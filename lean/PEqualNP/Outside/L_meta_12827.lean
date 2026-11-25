import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_12827.Model
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


end PEqualNP.Outside.L_meta_12827.Model

namespace PEqualNP.Outside.L_meta_12827
open PEqualNP.Outside.L_meta_12827.Model
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

end PEqualNP.Outside.L_meta_12827

namespace PEqualNP.Outside.L_meta_12827
open PEqualNP.Outside.L_meta_12827.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x280123815400125939a0e98a20369000c1a0001e00840004608a83321149f100059700600001e38e80008898022188014a0000450000430820c244bff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x41ff20083de40107f88020fd10041fd20083da40107e48020ffaa6217f54c43fca9885f95310df2a6213e54c43faa9885f55310deaa6213d54c43f8a9885f15310ffa9e217f53c43fca7885f94f10fea9e217d53c43f8a7885f14f10ffa1e21fe43c43fa87887f10f10ffa96217f52c43fca5885f94b10fea96217d52c43f8a5885f14b10ffa1621fe42c43fa85887f10b10ff99621fe32c43fa65887f0cb10ffa0e21fe41c43fa83887f10710ff98e21fe31c43fa63887f0c710ff90e21fe21c43fa43887f08710ffa0621fb40c43fc81886f90310fea0621fc40c437881887e10310dc20621ff30c43fc61887f4c310fe18621ff20c43fc41887f48310fe10621ff54842fea9087f95210bf2a421fd54842faa9087f15210be2a421ff53842fea7087f94e10bf29c21fd53842faa7087f14e10be29c21ff43843fc87087f50e10fe21c21ff52842fea5087f94a10bf29421fd52842faa5087f14a10be29421ff42843fc85087f50a10fe21421ff32843fc65087f4ca10fe194217d51843fe83087f90610fea0c21fc41843fe63087dcc610ff18c21fd31843f863087d0c610ff90c21f721843fc43087f48610fe10c21f421842fca1087fd0210ff20421be40843fa81087f10210de20421ff30843fc61087f4c210fe18421ff20843fc41087f48210fe10421ff10843ee21087ec4210ffaa2217f544437ea8884fd5110ff2a2217e54443faa8885f55110fe2a2217c5444378a8884f15110ffa9a217f53443bea68857d4d10ff29a217e53443faa6885f54d10fe29a217c53443b8a6885714d10ffa1a21fe43443fa86887f10d10ffa92217f52443dea4885bd4910ff292217e52443faa4885f54910fe292217c52443d8a4885b14910ffa1221fe42443fa84887f10910ff99221fe32443fa64887f0c910ffa0a21fe41443fa82887f10510ff98a21fe31443fa62887f0c510ff90a21fe21443fa42887f08510ffa0221fe404437c80887f50110fe20221bc40443fe60887f8c110fe98221fc30443fe40887f88110fe90221fc20443fe20887ec4110ff08221f610443fea8085fd5010ff2a0217e54043faa8085f55010fe2a0217c54043fea6085fd4c10ff298217e53043faa6085f54c10fe298217c53043fe86087f90c10fea1821fc43043fea4085fd4810ff290217e52043faa4085f54810fe290217c52043fe84087f90810fea1021fc42043fe64087f8c810fe99021fc32042fca2087fd0410ff20821fd41043f882087fcc410fb98821fe31043fa62087f0c410fa18821ff21043ee42087f88410fe90821fc21043e842085f94010ffa0021fb40043fc80086f90010fea0021fc400437880087e10010dc20021ff30043fc60087f4c010fe18021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0xd320c3f86418770c830ffa8861fe510c2fca2187f54430bea8861fc510c3fe82187f90430fea0861fc410c3fe62187f8c430ef18861fd310c3f86218770c430ff90861fe210c3fa42187f08430bf28061ff400c3fc80186f90030fea0061fc400c37880187fcc030ef98061fe300c3f460187f4c030ee98061f9300c3fea9905fd5320ff2a6417e54c837ca9904f95320feaa6417d54c837aa9904f55320fe2a6417c54c83fea7905fd4f20ff29e417e53c83faa7905f54f20fe29e417c53c83fe87907f90f20fea1e41fc43c83fe85907f90b20fea1641fc42c83fe65907f8cb20f719641fd32c83da65907f0cb20ffa8e41fe51c82fca3907f54720bea8e41fc51c83fe83907f90720fea0e41fc41c83fe63907f8c720fe98e41fc31c83fe43907f88720fe90e41fc21c83fe81907f90320df20641fd40c83f881906f10320ff98641fe30c83fa61907f0c320ffaa4417f54883fca9105f95220feaa4417d54883f8a9105f15220ffa9c417f53883fca7105f94e20fea9c417d53883f8a7105f14e20ffa1c41fe43883fa87107f10e20bea9441ff42883fc85107f50a20fe21441ff32883de65107f8ca20fe99441fc32883d865107fd4620ff28c417e51883faa3105f54620fe28c41ff41883fc83107f50620fe20c41ff31883fc63107f4c620fe18c41ff21883fc43107b88620fe90c41fc21883d843105f94220ffa0441fe408837c81107f50220fe20441bc40883fe61107f8c220fe98441fc30883fe41107bc8220fd90441ff54482fea8906fd51209faa241fe54482fca8907f55120beaa241fc54482f8a8906f151209e2a241ff53482fea69077d4d20afa9a41fe53482fca6907f54d20bea9a41fc53482f8a6907714d20ae29a41ff43483fc86907f50d20fe21a41ff42483fc84907f50920fe21241ff32483fc64907b8c920fe99241ed32483f864907fd4520bfa8a41f751482eea2907f94520fea8a41fc51482f8a2907d14520ba28a41ff41483fc82907f50520fe20a41ff31483fc62907f4c520fe18a41ff21483fc42907f48520fe10a41ff40483fc80906f90120fea0241fc404837880907fcc120ff18241fd30483f860907fc8120fd90241fe20483dc40907fd5020bfaa041fe54082fca8107f55020beaa041fc54082f8a8107fd4c20bfa9841fe53082fca6107794c20af29841fd53082faa6107754c20aea9841fc53082f8a6107fd0c20ff21841fd43083f886105f94820ffa1041fe42083fa84107f10820ff99041ef32083fc64107f4c820fe19041ec32083fea2107f94420bf28841fd51082faa2107f14420ffa0841fe41083fa82107f10420ff98841fe31083fa62107f0c420ff90841fe21083dc42107f48420fe10841ec21082fca0107fd0020ff20041be40083fa80107f10020de20041ff30083fc60107f4c020fe18
  | 2 => 0x2fca8207fd4c40ff298817e53103faa6205f54c40fe29881ff431037e86207f90c40df21881fd431037a86207f10c40de21881ff52103fca4205f94840fea90817d52103f8a4207fd0840dfa1081fe421037c84207f50840dea1081fc421037884207fcc840ff19081fd32103f864207fd4440ff288817e51103faa2205f54440fe28881ff411037e82207f90440df20881fd411037a82207f10440de20881ff31103fc62207f4c440fe18881ff21103fc42207f48440fe108817e50103fe80206fd0040ff20081fa40103fa80206f50040fca0081bf531037ca6206f54c40de29881bf521037ca4206f54840de29081bf321037c64206f4c840de19081bf511037ca2206f54440de28881bf311037c62206f4c440de18881bf211037c42206f48440de10881be501027ca0206e94040ffaa6617f54cc3fca9985f95330df2a6613e54cc3faa9985f55330deaa6613d54cc3f8a9985f15330ffa1e61fe43cc3fa87987f10f30ffa9661fe52cc2fca5987f54b30bea9661fc52cc3fe85987f90b30fea1661fc42cc3fe659877ccb30ff19661fd32cc3ba65987f0cb30ffa8e61fe51cc2fca3987f54730bea8e61fc51cc3fe83987f90730fea0e61fc41cc3fe63987f8c730fe98e61fc31cc3fe43987f88730fe90e61fc21cc3fe81987f90330df20661fd40cc3f881986f10330ffaa4617f548c3fca9185f95230feaa4617d548c3f8a9185f15230bea9c61ff438c3fc87187f50e30fe21c61ff528c3fca5185f94a30fea94617d528c3f8a5187fd0a30ff21461fd428c3f885187fcca30ff19461de328c3fa65187f0ca30ee19461ff518c3fca3185f94630fea8c617d518c3f8a3187fd0630ff20c61fd418c3f883187fcc630ff18c61de318c3fa63187f0c630ee18c61ff218c3fc43187f48630fe10c617e508c3fe81187f90230df20461fd408c3f881186f10230ff98461df308c3f661187fd5130bfaa261bf544c27ea8987f95130bf2a261fd544c2faa8987f15130be2a261bc544c278a8987fd0d30ff21a61fd434c3f886987fd4930bfa9261ef524c2dea4987f94930fea9261fc524c2f8a4987b14930b629261ff424c3fc84987f50930fe21261ff324c3be64987f8c930fe99261dd324c3f864987fd4530bfa8a61f7514c2eea2987f94530fea8a61fc514c2f8a2987d14530ba28a61ff414c3fc82987f50530fe20a61ff314c3fc62987f4c530fe18a61ff214c3fc42987f48530fe10a61ff404c3fc80986f90130fea0261fc404c37880987fcc130fd98261fe304c3bc60987fd5030bfaa061fe540c2fca8187f55030beaa061fc540c2f8a8185f94c30ffa1861fe430c3fa86187f10c30ffa9061fe520c2fca4187b94830b729061fd520c2faa4187b54830b6a9061fc520c3fe84187f90830fea1061fc420c3fe64187f8c830ef19061f
  | 3 => 0x8510ff10a21f621443ff32887fc6510fb8ca21fe99443ed32887f86510df94621ffa0c43fe41887fa8310ff10621ff98c43fe31887fa6310ff0c621ff90c43ef21887ee4310ffd4221ff284437e50887faa110df54221fe28443ff54486fea890ff95121bf2a243fd54486faa890ff15121be2a243ff53486fea690ff94d21bf29a43fd53486faa690ff14d21be29a43ff43487fc8690ff50d21fe21a43ff42487fc8490ff50921fe21243ff32487fc6490ff4c921fe19243ff41487fc8290ff50521fe20a43ff31487fc6290ff4c521fe18a43ff21487ee4290ff88521f710a43ff50486fea090ff94121fea8243fc50486f8a090ffd5021bfaa043fe54086fca810ef950219f2a043fd54086faa810ef550219eaa043fc54086f8a810ffd4c21bfa9843fe53086fca610ff54c21bea9843fc53086f8a610ffd0c21ff21843fd43087f88610df94821ffa1043ef42087fc8410ff50821fe21043ec42087fe6410ff8c821f719043fd32087da6410ff0c821bf28843ff41087fc8210ff50421fe20843ff31087fc6210ff4c421fe18843ff21087de4210ff88421fb10843fd21087da4210fd48421ffa8043fe50086fca010ff54021bea8043fc50087fea7a07f94f40bf29e81fd53d02faa7a07f14f40ffa1e81fe43d03fa87a07f10f40ffa9681fe52d02fca5a07f54b40bea9681fc52d03fe85a07f90b40fea1681fc42d03fe65a07f8cb40fe99681fc32d03fea3a07f94740bf28e81fd51d02faa3a07f14740ffa0e81fe41d03fa83a07f10740ff98e81fe31d03fa63a07f0c740ff90e81fe21d03fa43a07f08740beaa481ff53903fca7205f94e40fea9c817d53903f8a7207fd0e40dfa1c81fe439037c87207f50e40dea1c81fc439037887207fd4a40ff294817e52903faa5205f54a40fe29481ff429037e85207f90a40df21481fd429037a85207f10a40de21481ff32903fc65207f4ca40fe19481ff51903fca3205f94640fea8c817d51903f8a3207fd0640dfa0c81fe419037c83207f50640dea0c81fc419037883207fcc640ff18c81fd31903f863207fc8640ff10c81fd21903f843205f94240ffa0481bf40903f681206fd4e40df29c81bd5390378a7206fd4a40df29481bd5290378a5206fcca40df19481bd329037865206fd4640df28c81bd5190378a3206fcc640df18c81bd319037863206fc8640df10c81bd219037843204f94240ffa9a817f53503fca6a07f54d40fe29a817c53503fe86a07f90d40fea1a81fc43503fea4a05fd4940ff29281fd52503f8a4a05f14940ffa1281fe42503fa84a07f10940ff99281fe32503fa64a07f0c940ffa8a817f51503fca2a07f54540fe28a817c51503fe82a07f90540fea0a81fc41503fe62a07f8c540fe98a81fc31503fe42a07f88540fe90a81fc21503fe80a07ed0140ff20281be405
  | 4 => 0xff4c941fe19283ff41507ee82a0ff90541df20a83ff50506fea0a0fed4141bda8283fe50507faa0a0ff14141be28283f850506f0a0a0df95041ffa9883fe53106fca620ff54c41bea9883fc53107fe8620ff90c41fea1883fc43107fea420ff94841bf29083fd52106faa420ff14841ffa1083fe42107fa8420ff10841ff99083fe32107fa6420ff0c841bf28883ff411077e8220ff90441fb20883fd411077a8220fd50441ffa8083fe50106fca020ff54041bea8083fc50107fea998dfd5331ff2a6637e54cc7faa998df55331fe2a6637c54cc7fe8798ff90f31fea1e63fc43cc7fea598ff94b31bf29663ee52cc6dca598ff54b31bea9663ed52cc6daa598ff14b31ffa1663fe42cc7fa8598ff10b31ff99663fe32cc7fa6598ff0cb31ffa0e63fe41cc7fa8398ff10731ffa8663fe50cc6fca198ff54331bea8663fc50cc7fea918dfd5231ff2a4637e548c7faa918df55231fe2a4637c548c6faa718ffd0e31efa1c63fe438c7fa8718ff10e31ee21c63ff528c7fca518df94a31fea94637d528c7f8a518ffd0a31ff21463fd428c7f88518ffcca31ef99463fe328c7fa6518f74ca31fe194637e518c7fe8318ff90631fea0c63fc418c7fe6318f7cc631fb98c63ff508c7fca118df94231fea84637d508c7f8a118ffd5131bfaa263fe544c6fca898ff55131beaa263fc544c6f8a898ffd0d31ff21a63fd434c7f88698ffd4931bfa9263fe524c7faa498ff14931be29263ff424c7fc8498ff50931fe21263ff324c7fc6498ff4c931fe19263ff414c7fc8298ff50531fe20a63ff314c7ee6298ff8c531ef18a63ff504c6fea098ff94131fea8263fc504c6f8a098ffd5031bfaa063fe540c6fca818ef950319f2a063fd540c6faa818ef550319eaa063fc540c6f8a818df94c31ffa1863df430c7fc8618ff50c31fe21863dc430c7fea418ff94831bf29063fd520c6faa418ff14831ffa1063fe420c7fa8418ff10831ff99063df320c7fc6418ff4c831ee99063fc320c6fca218ffd0431ff20863fd410c7f88218ffcc431ef98863fe310c7ec6218ff4c431ee98863f5310c7fea018ff94031bf28063fd500c6faa018ff14031ffaa6437f54c87fca990df95321feaa6437d54c87f8a990df15321ffa9e437f53c87fca790df94f21ef29e435e53c87faa790df54f21eea9e435d53c87f8a790df14f21ffa1e43fe43c87fa8790ff10f21ffa1643fe42c87fa8590ff10b21ff99643fe32c87fa6590ff0cb21ffa0e43fe41c87fa8390ff10721ff98e43fe31c87fa6390ff0c721ffa8643fe50c86fca190ff54321bea8643fc50c87fea910dfd5221ff2a4437e54887faa910df55221fe2a4437c54887fea710dfd4e21ff29c437e53887faa710df54e21fe29c437c53887fe8710ff90e21fea1c43fc43886faa510ffd0a21f7a1443fe42887fa
  | 5 => 0xa42ffa8c85fe5190afca3217f54642bea8c85fc5190bfea1217f94242bf28485fd5090afaa1217f14242ffa9a857f5350bfca6a17f54d42fe29a857c5350bfe86a17f90d42fea1a85fc4350bfe84a17bd0942ff21285be4250bfea2a15fd4542ff28a85fd5150bf8a2a15f14542ffa82857f5050bfca0a17f54142fe282857c5050afca8217fd4c42ff298857e5310bfaa6215f54c42fe29885ff4310bfc86217f50c42fe218857e5210bfe84216fd0842ff21085ee4210bfa84216f50842f6a1085ff5110bfca2215f94442fea88857d5110bf8a2217fd4042ff280857e5010bfaa0215f54042fe28085ff54ccafea9997f95332bf2a665fd54ccafaa9997f15332be2a665ff43ccbfc87997f50f32fe21e65ff42ccbfc85997f50b32fe21665ff51ccbfca3995f94732fea8e657d51ccbf8a3997fd4332ff286657e50ccbfaa1995f54332fe28665ff548cafea9197f95232bf2a465fd548cafaa9197f15232be2a4657d538cbfe87197f90e32fea1c65fc438cafca5197fd0a32ff21465fd428cbf885197fcca32ef99465ef328cbfea3197f94632bf28c65fd518cafaa3197f14632ffa8465fe508cafca1197f54232bea8465fc508cbfea8995fd5132ff2a2657e544cbfaa8995f55132fe2a2657c544cbfe86997f90d32fea1a65fc434cbfe84997f90932fea1265fc424cbfe64997bcc932ff19265de324cbfea2995fd4532ff28a65fd514cbf8a2995f14532ffa82657f504cbfca0997f54132fe282657c504cbfea8195fd5032ff2a0657e540cbfaa8195f55032fe2a0657c540cafca6197fd0c32ff21865fd430cbf886195f94832ffa1065fe420cbfa84197f10832ff99065df320cbfc64197b8c832fe99065dd320cbda6419734c832ffa8865fe510cafca2197f54432bea8865fc510cbfea0197f94032bf28065fd500cafaa0197f14032ffa9e83fe53d06fca7a0ff54f41bea9e83fc53d07fe87a0efd0f41ff21e83fd43d077a87a0ff10f41ffa9683fe52d06fca5a0ff54b41bea9683fc52d07fe85a0efd0b41ff21683fd42d077a85a0ff10b41ff99683fe32d07fa65a0ff0cb41ffa8683fe50d06fca1a0ff54341bea8683fc50d06faa920ffd4e41ff29c837e53907faa720df54e41fe29c83ff43907fc8720ff50e41fe21c83ff52907fca520df94a41fea94837d52907f8a520ffd0a41ff21483fd42907f88520ffcca41ff19483fd32907f86520df94641ffa0c83bf41907ee8320ffd4241ff284837e50907faa120df54241fe28483ff53506fea6a0f7d4d41afa9a83fe53507faa6a0ff14d41be29a83dc53506b8a6a0ffd0d41dfa1a83fe43507fa86a0ef50d41fe21a83ff52506fea4a0fbd4941b7a9283fe52507faa4a0ff14941be29283ec52506d8a4a0ffd0941dfa1283fe42507fa84a0ef50941fe21283ff32507fc64a0
  | 6 => 0x1601200200000a00600601e01000003600a00201200000000800800000800000003000a05800a03602000000c00c00000000200000a00000600000200601a02600000802000801a01c00002001602200000200800200000c00001003001200000400001200000601c00000e00000e00800801000a00e01e01200200600e04a01800400400000601200600801000603c00000c00601e00000e00400a00000800200c00200000800e00000000a00800a01200200800001000400404601e00e01c00200000000800004000600400200200000601a00001000605200c00600a00000c00400800600001001e02000200600400202601000c00600002600600800400000002601000200002800200e00000400003c00200400600c04400002600e00400000000800400000000a00400201400600000000200800004000000001c00604800000e00000200202400002c00a01400400000800400800000202e00a00200c00200000000400600200a00601a01a01400000000200000600600400600a01c00001000000000000203600000200400201c01800c00a00200401400000000200400600400401002c00c00400801000000600201200800e01600601201e02602400200a00200000000400001e01400e01400e00000001a00000801000600200800600400200600202e00602802002800c00000000201400601a00000600000001402600400200400400600000201a00e00801e00800a01600600000000e00200201800001000200200000000600c02800000200200a04400001400001601e01000200000600000004c000004000002016002000005ff52d0ffca5a1df94b43fea96877d52d0ff8a5a1ffd4743ff28e877e51d0ffaa3a1df54743fe28e87ff50d0ffca1a1df94343fea86877d50d0ff8a1a1df55243bf29c87ff4390f7e8721f7d0e43ffa9487fe5290efca521ff54a43bea9487fc5290ffea321ff94643bf28c87fd5190efaa321ff14643ffa8487fe5090efca121ff54243bea8487fc5090ffe86a1f7d0d43ff21a87be4350ffea4a1dfd4943ff29287fd5250ff8a4a1df14943ffa8a877f5150ffca2a1ff54543fe28a877c5150ffea0a1dfd4143ff28287fd5050ff8a0a1df14143bf2a0877e5310ffe8621efd0c43ff21887de4310ffa8621ef50c43eea1887ff5210ffca421df94843fea90877d5210ff8a421ffd4443ff288877e5110ffaa221df54443fe28887ff5010ffca021df94043fea80877d5010ff8a021ffd4f42ff29e857e53d0bfaa7a15f54f42fe29e85ff43d0bfc87a17f50f42fe21e85ff51d0bfca3a15f94742fea8e857d51d0bf8a3a17fd4342ff286857e50d0bfaa1a15f54342fe286857d5490bfea7217f94e42bf29c85fd5390afaa7217f14e42ffa1c85fe4390bfa87217f10e42bf29485ff4290b7e85217bd0
  | 7 => 0x30638001464fa404c000a38b64c65d247207301e02d1581140624fe82d57d9310d15b840008d0e2507c000ebcc441dc000bc1e1ce99b65a2800000029c99d415441840000445a24f615c0dac3a1c95bfc3594d52b512c0002a4000ee9bb89f8248cf9b18000000001b10b418c5b3875960c0000006080019e5b8dd80000001780000e64000001285ab42300018956bdd180006bdc5148c0003e08a4d25264db0c84b100bd36c00031c000001a0856864c0006f86440003b40007fdad0da53c000185954d93cb18001860000690000000e085c48b9aa98044c03bc000001d54eb56e4000684000ef86ad9980000013f43100000007180008692f19b8000000a08184500000250ac5d84f58894eb8000f0d2e9819a99674954610001de4a404cdbec0000b1419ba0d6d2349e80014d90e549c4d4c08000000000000a740106d5448198000f9417c000000fa15dc26032d74cdfd458d84eecb99b5c1f10a1c45d3009008c4141a8d0dc9d61cd458b114830549187cec9e11c70f3ca3db008dd9152a0000210000e6c4287c00008a1be0be8915239668000f010a4108001180000e909d1bcd4440342e05bc2e400045000000000082001486c0195e09b8000d7db8066d83c000ca47e16f5bc5b6c18d294001ac85553a9b60669e089d8b8d6c4e680010b8000000000409881645698000000000001a50294dd1ca559928dc1925c275d6c000278c60000000c7d7c56dd014000549d7cb51e49d70001a48000000e8001cc9400000000143c3ec0000f80019a400000110d3ac001111c8914c208f080495f8fb5b89c5c64134557dc58a00f405440e889ccb09f4000000000001c6400003c099a3c000b3c72c3a400027d739a60dbc1957240012991ec8d8424c18ccc0a9dc45d1ab953400600c00c03400801000200200000c00000000400a00c00001401200201200000600a00000a00000001600006400200800600001c00600201a00001602801001200001200400000800202e00001200000c02000400000800000000200600000200e00000001e00001200400200000000000203a00c00000a00000000000000a00400400802200000601400800800000600402c00200200600400600000000c00402c00000000600001000000c00801600200c01600a00600000000400000000000000000202200604201200000400000000801201a01802000002e00000000a00001602600000600400000000000602200a01200a00001e00a01200000002000400200000200400601c01600400200400002800200800a00000400800000004400000000a00c00200200c00400600000600000e00400000401000401600000400000600200e02601400000a00000000200400000c00a01000000200000801601600000001c02a00a002014000002018008004002000002006
  | 8 => 0x80000019f046169c000b30528000561c3400022d4700003d5658b00a8978c00014c59c001291c213340018e4675398b4c0000000010283cdd2cb248b18303e907800146ddc82c826d6ec3642cc900dc44981ec000000581ae8d19531af1038b5c0e0e29934ea1be4e9c0f11051dd4b83f937c334480000d60000000000c000004f1cb1080000978128000fed7e00016cdcbc0006792d13c888ca9c0009cc9a44ad340084735ac0508cbd23d7d4000001368000000b384e000000121c658345d20e207f4fc00003dd2118b9dcc47c000000d748f56009590c0519020adcd550ad525bd15ad6b12888298459e17a00000000000000002d9b95e5d064001268d90ab12cdc39b2189c0015bc000000800da80010891780009e177ce41115e15bf5505508ca120c971799864bc44fc0008080000000000000004480015f19019697e46dca1c8cc174aa15a8d693e91b00b89290a9060fdc5c8b44110000bb53b036c768e840b4d347cd9ecda1384f4d11d7600003e56fd701e20001aa40013901c800142db50000f6ccddc280000006a0000434001aa0001e44facae096c30d814309b41a8056cd48a54a4c001358bccf14224e491ad671740000000fe5328e10d307bc87c000001d5c3893c400062938153d0bc0001255b966c1f80015a0d70504cc80000cc000001aed5898094cdcf0a841ccdf8ef0028000241c79e64058c0dafcb94d044119bd6207740003551d555400000000103c000b915105d58b5888b496b8b6cc208c800196040d220000c3000134cc05160000ac948400146951c8700008fd7e99097514a00000000005f4d09a688e4a59260000a502880000e40012495c4d000018480011598680016a0b7412d08c76150da7c550835611d50e055510cda59d44368a2c0647dd350001acc06854c000000239de980071443dca8000eccdc8001734a04000000c15c3ce88001bac465b2c0018a87f8dc17bc3391500003c8000000a0c1509ec848ced5fc794399b140014d0ba57b80002bc2b80000000019a00006999f8b79394e5999dd1cf9c0002b46b57891f0521128ee54880000000013213393bd41c000cc4a6c578910d410fd9b1cfdb4c49ca658fd720c998200001ad2b9c2c0000008e10499ddb3d8d5c1d71db7000190c4847984b80608d4000b2c0000000000000000012fc5a0001a400001152c83d0c1c000a916c00017580000008040000014b0000889950158990001be89680007b0001a958cc0ec83de19694df1474001905a9c000dcd5217740000000000000300000003717900008612a41791b92ac6e536421891cfe0ea5abd7c1d59af90755604204ece2c0a4eb19549610d903460034083861407ce8c080000000000000000000a81cd4000994a694206ccd5d174f1ca719440456ac8bc63194c290c699d0ca80005f80011b51
  | 9 => 0x314cb9c55874000710001e4ca4800013464969065053959187000019d2580009d40c400000167955c61c9c4000c11451a65010b1c001cc5d78fb000000000000000126c3c0000ae8d946b15ec0013a1989ab01d88f048c001cecb9dae193821c0011c08a816014481dde19e939c3189345b57f93d92dce757ec6947644704180000000000006ed348000ded67ddb8a14cfc830001d080006d9314c8dda1e40904815a14790850001e2c0000004d9b4400000000090c000f75c4d63c001bdc5ac8417056d5b58ba11e182c1e5e34ee1bb4001101004000cd9d291bcc781480005254c5b34f8c78455841c000be4001108001851e61c98f24e3c45c02400000152c5e016cc4cdd98f8591528af420129c781c8112424db08000ec0aa4824d2d6854fc1a5041da57c9a7857c46c0017dd134001ded8240000019f465d2e11681b02353050f99a8f8428518800000036055d5440000a098c0000000000010f00000000006880000007480018bcc553f8000bd50b01a09f1455a707b5cdd24cde06f00008918e8000fd8e357298d800000011c84d9ac7000019117d102511802c2f400175d0ec00000063462d0f570d185db13cd4c979576c82caf82555f565d8283950d1b1d584000001a05628001240001274aa89800559858d0000000724ff95cc00000000000000000000140028c0014f11d000172ca2117c4a066173c264605171604b60001931d34000fc50c44b0944001ae41f4f50e316c8ec44783fc000001ca02ac9bc000bfdc48f35b54a35df91fd8a1838c40ce08ec4f54e53eca19121db59cdc40f81dd039dd88a446c943594905070c8f94382141640009307a068c588cc0c70f280011d97688786a8751cc1d68e4d3b4cf51cc00144cab5cc8874b2051c778d5101cad56254801b400000158ce607d195c001c8c3c4000001e39a30e44bdcd8c001b91dacbb1614000d999213d090931c20ca287e800000188d79c4957a4c740017a88e8e7074c4314091c84bc001e3c000000001d8d371630000001af41409a1c618e115ddbcd9c0000008c40000000000004a51554dcce80016400012309c15480004dda340000011a000000000000000094c001558e5584dc68974259d40accefd7095d9940ab8001ce8d4d09cf180010091c4f90474000ad927c000000000000000cd1c119c5899c7c06d4a41883848b5541d95879ddcfbd2f8ff11e56d8000a31730afdbf005cb68e0d19ce1c9480890e80000009adbf9d04001224001689e50d294300007c5428ed14b5a0c000000705c742c05b88180019d8f8800000000009d5c800181ccf00000013a4000000001090b7097c0000000002dd2094e0001e252555e8e5d9813004382b01207e45f08c1bb186d9185740c959c0015a45b077c0012d9d0d7f1b30c340002f000105ca8c1d00740007ac07
  | 10 => 0x10ed985492400185cf207381c0b58ed45a40014992a9651b9c00130d6803f43ac0001bd0d4000b809404e8001b24000000000919199bc8000400f68c6c000000001578a24000899cb80000000000000000d079da5d32c7c895000022938cf7c4d0001b69cd8000b55a2c000f5dbc12b19d47d45643307a8000f983f1958325e5410dba41e8e00515e6803800cce400092c80dc30858001c01b287b9ad426853d9fdc24001595270000000d88000e506e00001d4740b899b4d3d7fda205347ecc5cf481540ac000ffc001361891dd8db400088000000000192c298f713f17f4000510681a8d1957ac000ef4001a000f40000000000000014f9b7cc24000001a1c000000101bbd318001c08d1d0705d8d815180000017483000fc000000000001ac40009c8000de96f96f1354001664b0c348bec88597c60d2f437cedd64842c00171000000078d6a51645e4181e040000000000003a87d80000010188640017856b49380012ec270788000001dc0cd40000d85ecb853dda84a780018dc000001000000070454001924854000aec000404cad45cf780000004896e8c3c001324bc9c9191c00133c2f80009fd68dba8001cb40400018f044c0000000014a84c85c12e516c000964c495680018ec0000000000012510312040000002c400000114504400156d494bf422161858c5cc000c900000000000000000012140005400012bc000988c2db7500cb7c95c67105800000000093c984130e786f4458fb8570c50f04db8d20350379bd49b1279a395b1adcbe0b34a10fd0204e183d9069c85dfd190fc97b000162d810c28af0c89c05639d6402198cff46b8469d990b51f56d11f800075c0d415c001d90000badb78844000a953fc7700000003b14bc0019c00013e02806655753780000000000001909980014781fd04c729714a5c000000000e3800000176518d834169df0dd58f5331ce0bd00000013882459c9ad83284f87f175547c5300000016e061964c000000170001244000a98ea8000000000000001cf8f54000000000d64000001d9c0013090c8811a19138abd6080000004e45dc1040012c5404000bb835c6e8a60001201cf5a74599bd9a9102d9912d4e7cddc39069d8a5b48000000fd4001884000001500000000b08585971c0c5a97cc9210ddd3c23cead054f451a8000000000000001dd4001a6d6346d0001d157712c14f476c1c4de40015154c0000000c389e43809a80dc63cf64c580000018c00000513b84a8000001085b0c0007a4001b999780000006fc000ae411922cc9cc81281cd0ac11a5a885e8b288ad3758ac008004d38f2d40c0000c1d0067cb058c800122935d1e80013d42a8000001c15964cb4621a54aacd595655d5a455d1e0c73d099e581b9928bd90946546c1a4daac000f107095e400000049013c0001380014e89b4
  | 11 => 0x1da9d49b04fa8bf09dc50c744a7d3e42a17b433cbf871d461d7513dccdc6c52d4ec2ed571e2885d4259947544b5ce4ad196c095654d78001218000ba96a9744000000001e000002fda110e1d4d538bbdcac4c4d106c4fcd4ad77832025c38c34de315b5df5411d61660001719d3906ce94df4e143744403b8000f30b145945fd80cf386a59742e9d
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x440043b42110010af98040043ba6010010cf94040042f96510010de59440042796510010be99040043ba6410010ded5040043ba5410010de55040043b95410010eed0c40043ba4310010ee50c40043b84310010eed0840043ba4210010ee50840043b84210010fc98440042f96110010fc584400437a5110010eed0440043ba4110010ee50440043b84110010fccc440043f03110010fcc8440043f02110010ee994400433a6510010ee59440043396510010eed8c40043ba6310010ee58c40043b86310010eed4c40043ba5310010ee54c40043b85310010eed8840043ba6210010ee58840043b86210010eed4840043ba5210010ee54840043b85210010eecc840043ba3210010ee4c840043b83210010eed8440043ba6110010ec98440043b96110010ec58440043b86110010ce94440043bb3110010eccc440043ba3110010ee4c440043b83110010ec0c440043bb2110010ecc8440043ba2110010ee48440043b82110010ec084400427d65cc010af99330042bd64cc010ee103300427f658c0109f596300435e538c010d754e30042f6618c010bd58630043d4318c010ee102300427f654c010afd9130042bc644c010bbd8930042ec624c010bdd8530042f4614c010ee101300427f650c0109f994300427d650c0109f194300435e530c010d754c30042ee620c010bb58830042f6610c010bd58430043d4310c010ee100300427d65c8010af99320042bd64c8010ee103200427f65880109f596200436e5288010db54a20042f66188010bd58620043e42188010ee102200427f6548010afd9120042bc6448010b7d8d20042dc6348010bdd8520042f46148010ee101200427f65080109f994200427d65080109f19420042de6308010b758c200436e5208010db54820042f66108010bd58420043e42108010ee10020042be64c4010af59310043b840c4010dd59710043b664c4010ed59310042f663c4010bd18f10042f662c4010bd18b10043f340c4010ed90310043b440c4010fc10310043b040c4010bd58610043765184010ee90210043b84084010be596100437965840109e59610042fa6484010be19210042f96184010de94610043f25184010fccc610043f03184010fcc8610043f021840109fd9510042bf6444010af19110042df6344010b718d10042ef6244010bb18910043ba4044010ee10110042f76544010ddd9510042776544010edd9110043b46444010f5d8d10042f66344010bd18d10043d46344010b518d10043e76244010bd98910042f46244010f918910042e46244010bdd8110043765044010ed90110043b44044010bed95100437b65440109ed9510043bb6444010be99110042f86444010ee19110042b86444010f6d8d10043d86344010fad8910043e86244010bed8510043f36144010de94510043f25144010
  | 1 => 0x42f4614c810bed8132042f8604c8109fd94320427e650c8109f594320427c650c810f34c8320427e6494410cf992510423e64944109f592510433d64944108f592510427e63944109f58e510427e62944109f58a510427d65d0410cfd53410433c54d04109fd96410427d6590410cf952410433d5490410be98241042f960904109fd95410433f5450410cf15141042df6350410b718d41042ef6250410bb18941042fb60504109fd94410427d6510410cf950410433d5410410be98041042f960104109f59731042ee62cc410bb58b31042f565cc410dd597310437753cc410dd54f31042f662cc410f998b31042e662cc410f958b31042f560cc4109fd96310427d658c410d794e310435d538c410bd98631042fa608c410be582310427f654c4109fd94310427d650c410af99031042bd640c410d794c310435d530c410f54c431042fa600c410be5803104375650c4109d59431043b6640c410ed59031042f6630c410f598c3104377530c410f594c3104375530c410f554c31043d7430c410f510c31042f6620c410f5cc831043d5320c410fc98031042f5600c410fc580310427d65c8410b798f21042dd63c8410bd597210437565c8410bd98f21043d663c8410b598f21043d563c8410bd18f210437752c8410dd54b21042f560c84109fd96210427d6588410db94a210436d5288410bd98621042fa6088410be582210427f65484109fd94210427d6508410af99021042bd6408410db948210436d5208410f948421042fa6008410be580210437565084109d59421043b66408410ed59021042f66308410bd18c21042f66208410f998821043775208410f994821043755208410f954821043e74208410f910821043e63208410f94c821043f26008410bd58021043f160084109f992500427d64940109f98e500427d63940109f98a500427d62940109f58650043773194010dd0c650043772194010dd086500427d65d0010be597400437965d0010ded53400437954d0010be587400437a51d0010fccc740043f031d0010fcc8740043f021d00109fd96400427d6590010cf952400433d5490010bd98640042f56190010be982400433f6590010cf996400433d6590010cf196400433f5390010cf94e400433d5390010cf14e400433f5290010cf94a400433d5290010cf14a40043b66190010ed586400433e5190010edcc640043b43190010edc8640043b42190010af98240042ba6090010cf942400427f65500109fd94400427e65100109f594400427c6510010cf950400433d5410010bd98440042f56110010ee500400433f6510010cf994400433d6510010cf194400433f5310010cf94c400433d5310010cf14c400433f5210010cf948400433d5210010cf14840043b66110010ed584400433e5110010edcc440043b43110010edc8
  | 2 => 0x64550109fd8d540427c63550109fd89540427c62550109fd85540427d61550109fd81540427d6055010de181540433d5415010b798c54042dd6315010bb98854042ed62150109f990540433e64150109f98c540435e63150109798c540427d6315010d758c540425d63150109f988540436e62150109b988540427d6215010db588540426d62150109f984540437661150109f980540437a60150109f993530427d64d4c109f98b530427d62d4c109f987530437661d4c109f983530437a60d4c109f596530435f5394c109f992530427d6494c109f98a530427d6294c109fd91530427c6454c10d7d8d530427f6254c109f189530427f6154c109f58553043746154c109fd81530427d6054c10af99053042bd6414c10d754c53042ee6214c10bb588530427e6414c10cf990530423e6414c109f590530433d6414c108f590530427e6314c10d798c530427e6214c10db988530426e6214c109f588530436d6214c109b588530427e6114c10dd984530427e6014c10de980530427f65d0c109f997430427d65d0c109f197430433e54d0c10cf55343042f661d0c10bd587430427f6590c109f996430427d6590c109f196430435e5390c10d754e43042fa6090c10be582430427f6550c109f995430427d6550c109f195430433e5450c10cf551430435e5350c10d754d43042f76150c10bd18543042fb6050c10be181430427f6510c109f994430427d6510c109f194430427e64d48109f593520427e63d48109f58f520427e61d4810dd987520427e60d4810de983520427d6594810dbd4a520427e64948109f592520427e63948109f58e520427f64548109f191520427f63548109f18d520436f62548109fd85520427d6154810dd185520427f60548109f58152042be6414810af59052042de6314810b758c520436d52148109f990520433e64148108f990520427d6414810cf590520423d64148109f98c520435e63148109798c520427d6314810d758c520425d63148109f988520436e62148109f984520437661148109f980520437a60148109fd97420427e65d08109f597420427c65d0810cf953420433d54d0810bd98742042f561d08109fd96420427e65908109f596420427c6590810db94a420436d5290810be98242042f960908109fd95420427e65508109f595420427c6550810cf951420433d5450810db949420436d5250810bdd8542042f46150810bed8142042f860508109fd94420427e65108109f594420427c65108109fd97320427e65cc8109f597320427c65cc810d794f320435d53cc810bd98732042f561cc8109fd96320427e658c8109f596320427c658c810db94a320436d528c810bd98632042f5618c8109fd95320427e654c8109f595320427c654c810d794d320435d534c810db949320436d524c810bdd85320
  | 3 => 0x110d714f404436f52d0110db14b40442f661d0110bd587404427e6590110cfd52404433e5490110cf552404433c5490110d7d4e404435c5390110dbd4a404436c5290110af996404433e65901108f996404433f5390110e7d4e404431f5390110cf94e404433d5390110cf14e404439c5390110c714e404433f5290110ebd4a404432f5290110cf94a404433d5290110cf14a40443ac5290110cb14a40442be60901109fd95404427d65501109f195404433f5450110cf151404435f5350110d714d404436f5250110db14940442f76150110bd185404427e6510110cfd50404433e5410110cf550404433c5410110d7d4c404435c5310110dbd48404436c5210110af994404433e65101108f994404433f5310110e7d4c404431f5310110cf94c404433d5310110cf14c404439c5310110c714c404433f5210110ebd48404432f5210110cf948404433d5210110cf14840443ac5210110cb14840442be6010110ee980404427e65cc110af99330442bd64cc110cfd53304433c54cc110d7d4f304435c53cc110dbd4b304436c52cc110bd98730442f561cc1109f996304433f548c110cf152304435f538c110d714e304436f528c110db14a304427f654c1109f595304427c654c110afd9130442bc644c110cfd51304433c544c110d7d4d304435c534c110bbd8930442ec624c110dbd49304436c524c110bdd8530442f4614c1109f994304433f540c110cf150304435f530c110d714c30442ee620c110bb588304436f520c110db148304427e65c8110af99320442bd64c8110cfd53204433c54c8110d7d4f204435c53c8110dbd4b204436c52c8110bd98720442f561c81109f996204433f5488110cf152204435f5388110d714e204436f5288110db14a204427f65481109f595204427c6548110afd9120442bc6448110cfd51204433c5448110b7d8d20442dc6348110d7d4d204435c5348110dbd49204436c5248110bdd8520442f461481109f994204433f5408110cf15020442de6308110b758c204435f5308110d714c204436f5208110db14820442be64c4110af593104433f54c4110cf153104435f53c4110d714f104436f52c4110db14b10443ba40c4110ee10310443ba64c4110ee59310443bb54c4110de953104437854c4110ee153104433854c4110f6d4f10443d853c4110fad4b10443e852c4110cfd52104433c5484110d7d4e104435c5384110dbd4a104436c5284110edd5210443b45484110f5d4e10443765384110dd14e10443d45384110d514e10443e75284110dd94a10443745284110f914a10443645284110fcd4210443b64084110ed102104427e63d50109f58f540427e62d50109f58b540427e61d5010dd987540427e60d5010de983540427d6595010cfd52540427e63950109f58e540427e62950109f58a540433f
  | 4 => 0x314c524436f6414910db990524436d6414910db190524436f6314910db98c524436d6314910db18c524436f4314910db90c524436d4314910db10c524436f6114910db584524436f6014910db580524436d10149109fd97424427e65d09109f597424427c65d0910cfd53424433c54d0910d7d4f424435c53d0910dbd4b424436c52d09109fd96424427e65909109f596424427c6590910cfd52424433c5490910d7d4e424435c5390910dbd4a424436c52909109fd95424427e65509109f595424427c6550910cfd51424433c5450910d7d4d424435c5350910dbd49424436c52509109fd94424427e65109109f594424427c6510910cfd50424433c5410910d7d4c424435c5310910dbd48424436c5210910bd98442442f561109109fd97324427e65cc9109f597324427c65cc910cfd53324433c54cc910d7d4f324435c53cc910dbd4b324436c52cc9109fd96324427e658c9109f596324427c658c910cfd52324433c548c910d7d4e324435c538c910dbd4a324436c528c9109fd95324427e654c9109f595324427c654c910cfd51324433c544c910d7d4d324435c534c910dbd49324436c524c9109fd94324427e650c9109f594324427c650c910cfd50324433c540c910d7d4c324435c530c910dbd48324436c520c910f34c832442fa600c910be580324427e65d0510cfd53414433c54d0510d7d4f414435c53d0510dbd4b414436c52d0510be98341442f960d05109f996414433f5490510cf152414435f5390510d714e414436f5290510db14a414427c6550510cfd51414433c5450510b7d8d41442dc6350510d7d4d414435c5350510bbd8941442ec6250510dbd49414436c5250510bed8141442f860505109f994414433f5410510cf150414435f5310510d714c414436f5210510db14841443b541105109f997314433f54cc510cf153314435f53cc510d714f31442ee62cc510bb58b314436f52cc510db14b31442fa60cc510be583314427e658c510cfd52314433c548c510d7d4e314435c538c510dbd4a314436c528c5109f195314433f544c510cf151314435f534c510d714d314436f524c510db14931442fb604c510be181314427e650c510af99031442bd640c510cfd50314433c540c510d7d4c314435c530c510dbd48314436c520c5109f997214433f54c8510cf15321442de63c8510b758f214435f53c8510d714f214436f52c8510db14b21442fa60c8510be583214427e6588510cfd52214433c5488510d7d4e214435c5388510dbd4a214436c52885109f195214433f5448510cf151214435f5348510d714d214436f5248510db14921442fb6048510be181214427e6508510af99021442bd6408510cfd50214433c5408510d7d4c214435c5308510dbd48214436c52085109f997404433f54d0110cf153404435f53d0
  | 5 => 0x534427f6454d10cfd91534423f6454d109f191534433c6454d108f191534435f6354d109fd89534436f6254d109bd89534427c6254d10db189534426c6254d109fd8553443776154d109dd85534427f6054d10ded81534427e6514d10cfd50534433c5414d10d754c534427e6414d109f590534435e6314d109f988534427d6214d109f984534427c6114d109f980534427c6014d10b7994534435e6514d1097994534435f5414d10e7d50534431f5414d10d7950534435d5414d10d7150534439c5414d10c7150534435f6414d10d7990534435d6414d10d7190534435f6214d10d7988534435d6214d10d7188534435f6114d10d7584534435f6014d10d7580534435d1014d109fd97434427e65d0d109f597434427c65d0d10cfd53434433c54d0d10d7d4f434435c53d0d109fd96434427e6590d109f596434427c6590d10cfd52434433c5490d10d7d4e434435c5390d109fd95434427e6550d109f595434427c6550d10cfd51434433c5450d10d7d4d434435c5350d109fd94434427e6510d109f594434427c6510d10cfd50434433c5410d10d7d4c434435c5310d10bd98443442f56110d10cfd53524433c54d4910d7d4f524435c53d49109f993524427d64d49109f98f524427d63d4910dbd5352443af54d4910cbd53524436e54d4910db553524436c54d4910eb153524432c54d4910dbd4f52443cf53d4910d3d4f524436e53d4910db54f524436c53d4910f314f524434c53d4910dbd93524436e64d4910db593524436c64d4910dbd8f524436e63d4910db58f524436c63d4910dbd0f524436e43d4910db50f524436c43d4910dbd87524436d61d4910dbd83524436d60d4910af99252442bd6494910cfd52524433c5494910b798e52442dd6394910d7d4e524435c5394910dbd4a524427e6494910cf992524423e64949109f592524433d64949108f592524427e6394910d798e524425e63949109f58e524435d63949109758e524427e62949109b98a524427d6194910dd586524427d6094910de58252442bf6454910af191524433f5454910cf15152442df6354910b718d524435f5354910d714d524427f6454910cfd91524423f64549109f191524433c64549108f191524427f6354910d7d8d524425f63549109f18d524435c63549109718d524436f62549109fd85524437761549109dd85524427f6054910ded81524427e6514910cfd50524433c5414910d7d4c524435c5314910db548524427e64149109f590524427e63149109f58c524436e62149109f984524427c61149109f980524427c6014910bb994524436e65149109b994524436f5414910ebd50524432f5414910db950524436d5414910db15052443ac5414910cb150524436f5314910f3d4c524434f5314910db94c524436d5314910db14c52443cc5314910d
  | 6 => 0x33d5210210cf14840843b66110210ed58440843b73110210ed0c440843b72110210ed08440843ba6010210af99330842bd64cc210d794e308435d538c210bd98630842f5618c210f50c630842bf644c210af19130842ef624c210bb18930842f7614c210bd185308435e530c210d754c30842ee620c210bb58830842f6610c210bd58430843d4310c210af99320842bd64c8210db94a208436d5288210bd98620842f56188210f908620842bf6448210af19120842df6348210b718d20842f76148210bd18520842de6308210b758c208436e5208210db54820842f66108210bd58420843e42108210af99310842bd64c4210ee90310843b840c4210bd597108437565c4210ed99310843b564c4210bd98f10842f463c4210bd98b10842f462c4210ed90310843b440c4210be597108437965c4210ee99310843b964c4210de953108437854c42109f98f544427d63d51109f98b544427d62d5110cfd8f544433e63d5110cf58f544433c63d5110cfd8b544433e62d5110cf58b544433c62d5110cfd87544433d61d5110cfd83544433d60d5110cfd5254442de6395110b758e54442ee6295110bb58a544427e64951108f992544427e6395110d798e544425e63951109f58e544435d63951109758e544427e6295110db98a544426e62951109f58a544436d62951109b58a544427d6195110dd586544427d6095110de58254442df6355110b718d54442ef6255110bb189544433f64551109fd8d544435f635511097d8d544427c6355110d718d544425c63551109fd89544436f62551109bd89544427c6255110db189544426c62551109fd85544437761551109fd81544437b60551109ed81544427e6515110cf550544433e64151109f98c544427d63151109f988544427d62151109f984544427c61151109f980544427c6015110af994544433e65151108f994544433f6315110cf98c544433d6315110cf18c544433f6215110cf988544433d6215110cf188544433f6115110cf584544433f60151108f980544433d60151108f180544433d1015110cfd53534433c54d4d109f993534427d64d4d109f98b534427d62d4d10d7d53534439f54d4d10c7d53534435e54d4d10d7553534435c54d4d10e7153534431c54d4d10d7d93534435e64d4d10d7593534435c64d4d10d7d8b534435e62d4d10d758b534435c62d4d10d7d87534435d61d4d10d7d83534435d60d4d10af99253442bd6494d10cfd52534433c5494d10d7d4e53442ee6294d10bb58a534427e6494d10cf992534423e6494d109f592534433d6494d108f592534427e6394d109798e534427e6294d10db98a534426e6294d109f58a534436d6294d109b58a534427d6194d10dd586534427d6094d10de58253442bf6454d10af191534433f5454d10cf15153442ef6254d10bb189
  | 7 => 0x354a10dbd8952843776154a10b798c52842dd6314a10db548528427e6414a109f590528427e6314a10d798c528425e6314a109f58c528435d6314a109758c528436e6214a10dd584528437a6014a109fd97428427e65d0a109f597428427c65d0a10cfd53428433c54d0a10db94b428436d52d0a10bd98742842f561d0a109fd96428427e6590a109f596428427c6590a109fd95428427e6550a109f595428427c6550a10cfd51428433c5450a10bdd8542842f46150a109fd94428427e6510a109f594428427c6510a10db948428436d5210a109fd97328427e65cca109f597328427c65cca10d794f328435d53cca10bd98732842f561cca109fd96328427e658ca109f596328427c658ca10db94a328436d528ca10bd98632842f5618ca109fd95328427e654ca109f595328427c654ca10d794d328435d534ca10db949328436d524ca10bdd8532842f4614ca109fd94328427e650ca109f594328427c650ca10f34c832842fa600ca10be580328433e54d0610cf55341842fa60d0610be583418433f5490610cf152418433e5450610cf55141842df6350610b718d41842ef6250610bb18941842fb6050610be181418433f5410610cf150418435e53cc610d754f31842ee62cc610bb58b31842fa60cc610be583318437565cc610ddd4f31843d653cc610dd54f31843d553cc610bd98b31843e662cc610b998b31843e562cc610fc98331842f560cc610fc583318435f538c610d714e318435e534c610d754d31842fb604c610be18131842be640c610af590318435f530c610d714c31843d5310c610bd5943184375650c610ed99031843b5640c610f598c3184377530c610f5d4c3184375530c610f514c31843d7430c610f510c31842f6620c610f5cc831843d5320c610bd58031842de63c8610b758f218436e52c8610db54b21842fa60c8610be583218437565c8610bd98f21843d663c8610b598f21843d563c8610bd18f218437752c8610f994b218437552c8610f954b21843f260c8610bd58321843f160c8610dbd4a218436c5288610db949218436d5248610bed8121842f86048610af99021842bd6408610dbd48218436c5208610f948421842f56508610dd59421843b66408610ed59021842f66308610bd18c21843e66208610ddd4821843e75208610dd54821843e45208610f9d0821843e44208610f98c821843e53208610bd580218433e5490210cf55240842f66190210bd586408433e6590210cf596408433f5390210cf94e408433d5390210cf14e408433f5290210cf94a408433d5290210cf14a40843b66190210ed58640843b73190210ed0c640843b72190210ed086408433e5410210cf55040842f66110210bd584408433e6510210cf594408433f5310210cf94c408433d5310210cf14c408433f5210210cf9484084
  | 8 => 0x10ee58c40c43b86310310eed4c40c43ba5310310ee54c40c43b85310310eed8840c43ba6210310ee58840c43b86210310eed4840c43ba5210310ee54840c43b85210310eecc840c43ba3210310ee4c840c43b83210310eed8440c43ba6110310ee58440c43b86110310eecc440c43ba3110310ee4c440c43b83110310eec8440c43ba2110310ee48440c43b82110310af99330c42bd64cc310cf95330c433d54cc310d794f30c435d53cc310bd98730c42f561cc310ee10330c433e548c310cf55230c435f538c310d714e30c43b8408c310afd9130c42bc644c310cf95130c433d544c310d794d30c435d534c310bbd8930c42ec624c310bdd8530c42f4614c310ee10130c433e540c310cf55030c435f530c310d714c30c42ee620c310bb58830c43b8400c310af99320c42bd64c8310cf95320c433d54c8310db94b20c436d52c8310bd98720c42f561c8310ee10320c433e5488310cf55220c436f5288310db14a20c43b84088310afd9120c42bc6448310cf95120c433d5448310b7d8d20c42dc6348310db94920c436d5248310bdd8520c42f46148310ee10120c433e5408310cf55020c42de6308310b758c20c436f5208310db14820c43b84008310b798f54842dd63d5210bb98b54842ed62d52109f98f548435e63d52109798f548427d63d5210d758f548425d63d52109f98b548436e62d52109b98b548427d62d5210db58b548426d62d5210dd587548437a60d5210cfd52548427e63952109f58e548427e62952109f58a548433f64552109fd8d548427c63552109fd89548427c6255210cf550548433e64152109f98c548427d63152109f988548427d6215210dd584548437a60152109f993538427d64d4e109f98b538427d62d4e10dd587538437a60d4e10af99253842bd6494e10d7d4e538427e6494e10cf992538423e6494e109f592538433d6494e108f592538427e6294e109f58a538427f6454e109f191538435f6354e109fd89538427c6254e10ddd85538435d5314e10bb98853842ed6214e109f990538427d6414e10d798c538427e6214e10db988538426e6214e109f588538436d6214e109b58853843756114e10de980538427f65d0e109f997438427d65d0e109f197438433f54d0e10cf153438435e53d0e10d754f43842f661d0e10bd587438427f6590e109f996438427d6590e109f196438427f6550e109f995438427d6550e109f195438433f5450e10cf15143842f76150e10bd185438427f6510e109f994438427d6510e109f194438435e5310e10d754c438427e64d4a109f593528427e63d4a109f58f528437561d4a10de98352842be6494a10af592528436f5294a109f992528433e6494a108f992528427d6494a10cf592528423d6494a109f98e528427d6394a109fd91528427c6454a109fd8d528427c6
  | 9 => 0x99052c423e6414b109f59052c433d6414b108f59052c427e6314b109f58c52c436e6214b10dd98452c43796014b109fd9742c427e65d0b109f59742c427c65d0b10cf95342c433d54d0b109fd9642c427e6590b109f59642c427c6590b10cf95242c433d5490b10be98242c42f96090b109fd9542c427e6550b109f59542c427c6550b10cf95142c433d5450b10bed8142c42f86050b109fd9442c427e6510b109f59442c427c6510b10cf95042c433d5410b10bd98442c42f56110b109fd9732c427e65ccb109f59732c427c65ccb10cf95332c433d54ccb10d7d4f32c435c53ccb10db94b32c436d52ccb109fd9632c427e658cb109f59632c427c658cb10cf95232c433d548cb10d794e32c435d538cb10dbd4a32c436c528cb109fd9532c427e654cb109f59532c427c654cb10cf95132c433d544cb10d7d4d32c435c534cb10dbd4932c436c524cb10bed8132c42f8604cb109fd9432c427e650cb109f59432c427c650cb10cf95032c433d540cb10d794c32c435d530cb10db94832c436d520cb10f34c832c433e54d0710cf55341c433e5490710cf55241c42fa6090710be58241c433e5450710cf55141c42df6350710b718d41c42ef6250710bb18941c42f86050710cf95041c433d5410710ed50441c42fa6010710be58041c433e54cc710cf55331c42ee62cc710bb58b31c433e548c710cf55231c435e538c710d754e31c42fa608c710be58231c433e544c710cf55131c42be640c710af59031c433e540c710cf55031c435e530c710d754c31c42fa600c710be58031c433e54c8710cf55321c42de63c8710b758f21c433e5488710cf55221c436e5288710db54a21c42fa6088710be58221c433e5448710cf55121c42be6408710af59021c433e5408710cf55021c436e5208710db54821c42fa6008710be58021c433e54d0310cf55340c42f661d0310bd58740c42f965d0310de59740c437b54d0310ee95340c437954d0310ee55340c43f261d0310be58740c43f161d0310cfd5240c433e5490310cf55240c433c5490310af59640c433d6590310cfd4e40c433e5390310cf54e40c433c5390310cfd4a40c433e5290310cf54a40c433c5290310cf95140c433d5450310bdd8540c42f46150310cfd5040c433e5410310cf55040c433c5410310ee50040c42bd6510310cf59440c433f5310310cf94c40c433d5310310cf14c40c433f5210310cf94840c433d5210310cf14840c43ba6010310be59440c43796510310ee99040c437b5410310eed5040c43ba5410310de55040c43b95410310ce55040c43b85410310eed0c40c43ba4310310ee50c40c43b84310310eed0840c43ba4210310ee50840c43b84210310be58440c43bb4110310ee90440c43b94110310ee10440c43b96510310ae59440c43396510310eed8c40c43ba63103
  | 10 => 0x83cd5348020d354d20083e76148020bb18520083e46148020b918520082ef6048020db94120083eb4048020eb90120083ac4048020fa10120083a84048020bed95200837b65480209ed9520083bb6448020ee19120083db6348020f618d20083da5348020f654d20082fb6248020fad89200837a5248020fa94920083eb4248020fa10920083f36148020fc185200827e63d53109f58f54c427e62d53109f58b54c437661d5310de58354c433f54953109f98e54c427d63953109f98a54c427d6295310eed8254c433f6395310cf98e54c433d6395310cf18e54c433f6295310cf98a54c433d6295310cf18a54c433e6195310cf18654c433f6095310cf58254c433f64553109fd8d54c427c63553109fd8954c427c6255310ded8154c433f6555310eed8154c433f6355310cf98d54c433d6355310cf18d54c433f6255310cf98954c433d6255310cf18954c433e6155310cf18554c433f6055310ced8154c433d6055310cf55054c433e64153109f98c54c427d63153109f98854c427d6215310dd98454c43796015310af99353c42bd64d4f10cf95353c433d54d4f10bb98b53c42ed62d4f109f99353c433e64d4f108f99353c427d64d4f10cf59353c423d64d4f109f98b53c436e62d4f109b98b53c427d62d4f10db58b53c426d62d4f10dd98753c437960d4f10cf95253c433d5494f10d7d4e53c42ee6294f10bb58a53c427e6494f109f59253c427e6294f10db98a53c426e6294f109f58a53c436d6294f109b58a53c433e5454f10cf55153c427f6454f109f19153c435f6354f109fd8953c427c6254f10af99053c42bd6414f10cf95053c433d5414f10d754c53c427e6414f10cf99053c423e6414f109f59053c433d6414f108f59053c435e6314f109f98853c427d6214f10dd98453c43796014f109fd9743c427e65d0f109f59743c427c65d0f10cf95343c433d54d0f109fd9643c427e6590f109f59643c427c6590f10cf95243c433d5490f10be98243c42f96090f109fd9543c427e6550f109f59543c427c6550f10cf95143c433d5450f10bed8143c42f86050f109fd9443c427e6510f109f59443c427c6510f10cf95043c433d5410f10bd98443c42f56110f10af99352c42bd64d4b10cf95352c433d54d4b10b798f52c42dd63d4b109f99352c433e64d4b108f99352c427d64d4b10cf59352c423d64d4b109f98f52c435e63d4b109798f52c427d63d4b10d758f52c425d63d4b10dd98752c437960d4b10cf95252c433d5494b10b798e52c42dd6394b10dbd4a52c427e6494b109f59252c427e6394b10d798e52c425e6394b109f58e52c435d6394b109758e52c433e5454b10cf55152c427f6454b109f19152c427f6354b109f18d52c436f6254b10af99052c42bd6414b10cf95052c433d5414b10db54852c427e6414b10cf
  | 11 => 0x7d6588420d794e210835d5388420bb596210836d6588420db952210836c5488420bb98e21082ec6388420dbd4e21083ce5388420db54e21083cd5388420d354e21082ee6188420db54621082ed60884209fd95210835e5348420d754d21082be6408420af590210835e5308420d754c21083765108420dd54421083e52108420be98021082f96008420eb99021083ad6408420db950210836c5408420bb98c21082ec6308420dbd4c21083ce5308420db54c21083cd5308420d354c21082ee6108420f998421083e65108420db54421083e55108420fa98021082ed6008420fa580210827e64940209f592500827e63940209f58e500836f3294020db0ca500836e2194020db086500827d65d0020d794f400835d53d00209fd96400827d6590020cf952400833d5490020d794e400835d5390020bb98a40082ed6290020cfd96400833e6590020cf596400833c6590020cfd4e400833e5390020e794e400831e5390020cf54e400839d5390020c754e400833c5390020eb98a40083ad6290020cf94a40083af3290020eb0ca400833e5190020cf54640083ae2190020eb08640082be6090020cf942400827f6550020d794d400835d53500209fd94400827e65100209f594400827c6510020cf950400833d5410020d794c400835d5310020bb98840082ed6210020cfd94400833e6510020cf594400833c6510020cfd4c400833e5310020e794c400831e5310020cf54c400839d5310020c754c400833c5310020eb98840083ad6210020cf94840083af3210020eb0c8400833e5110020cf54440083ae2110020eb08440082be6010020ee980400833e50100209f59730082be64cc020af593300835e53cc020d754f30083cf32cc020ee103300827f658c0209f596300835e538c020d754e30082ee628c020bb58a30083cc328c0209fd9530082bf644c020af191300835e534c020d754d30082ef624c020bb18930083cf324c020bdd8530082f4614c0209fd94300827e650c0209f594300827c650c020d794c300835d530c020bb98830082ed620c020f30c830083b8400c020af99320082bd64c8020d794f200835d53c8020eb99320083ad64c8020bb98f20082ec63c8020dbd4f20083ce53c8020db54f20083cd53c8020d354f20082ee61c8020eb90320083ac40c8020d794e200835d5388020bb58a200836e5288020ee90220083b84088020f694e20083d95388020be58a200837a5288020fa94a20083eb3288020fa0ca20083ea2188020fa086200827f6548020afd9120082bc6448020b7d8d20082dc6348020d794d200835d5348020bdd8520082f46148020ee90120083b84048020bbd95200836f65480209bd9520083af6448020eb19120083cf6348020bb98d20082ec6348020f318d20082cc6348020dbd4d20083ce5348020db54d2
  | 12 => 0x14c20db988530826e6214c209f984530827d6114c209f980530837a6014c209fd97430827e65d0c209f597430827c65d0c20d794f430835d53d0c20bb98b43082ed62d0c209fd96430827e6590c209f596430827c6590c20d794e430835d5390c209fd95430827e6550c209f595430827c6550c20d794d430835d5350c20bbd8943082ec6250c20bed8143082f86050c209fd94430827e6510c209f594430827c6510c20d794c430835d5310c209f992520833e64948208f992520827d6494820cf592520823d64948209f98e520827d63948209f597420833f54d0820cf153420835e53d0820d754f420827f65908209f596420833e5490820cf552420835e5390820d754e42082fa6090820be582420827f6550820cfd51420833c5450820d794d420835d53508209fd94420827d6510820cf950420833d5410820d794c420835d5310820be98042082f960108209f597320835e53cc820d754f32082ed65cc820db597320826d65cc820dbd4f32083ce53cc820db54f32083cd53cc820d354f32082ee61cc820bb583320827f658c8209f596320835e538c820d754e32082ee628c820db94a32082fa608c820be582320827f654c820d794d320835d534c820db949320827f650c8209f594320835e530c820d754c32083cd320c820be98032082f9600c820db594320826d650c820bb98c32083ce630c820dbd4c32083ce530c820db54c32083cd530c820d354c32082ee610c820fa98032082ed600c820fa58032082de63d4420b758f510835e53d4420d754f510835e5394420d754e510837751944209f992510827d64944209f98e510827d6394420d794d510835d53544209fd91510827c64544209fd8d510827c6354420af99051082bd6414420b798c51082dd6314420d794c510835d5314420dd544510827f65d04209f997410827d65d0420cf953410833d54d0420d794f410835d53d0420bb98b41082ed62d04209fd96410827e65904209f596410835e5390420d754e41083765190420dd546410827f65504209f595410827c6550420cf951410833d5450420b7d8d41082dc6350420d794d410835d5350420bbd8941082ec6250420dd94541083755150420bed8141082f860504209fd94410827e65104209f594410835e5310420d754c410827f65cc4209f997310827d65cc420d794f310835d53cc420bb98b31082ed62cc4209fd96310827e658c4209f596310835e538c420d754e31082ee628c420bb58a31083cf328c4209fd95310827d654c4209f195310835e534c420d754d31082ef624c420bb18931082fb604c420be181310827f650c4209f994310827d650c420af99031082bd640c420d794c310835d530c420f3cc831082de63c8420b758f210835e53c8420d754f210837651c8420dd54721082fa60c8420be58321082
  | 13 => 0xcfd4440483b75110120cdd44404833c5110120ed14440483345110120af98040483ba60101209f99730482be64cc120af593304833f54cc120cf153304835f53cc120d714f30482ee62cc120bb58b30483cd32cc120ddd47304837451cc1209f996304833f548c120cf152304835f538c120d714e30483ce328c120ddd463048374518c120ee102304827f654c1209f595304827c654c120afd9130482bc644c120cfd51304833c544c120d7d4d304835c534c120bbd8930482ec624c120f34c930482f7614c120bd1853048377514c120dd14530483b8404c1209f994304833f540c120cf150304835f530c120d714c30482ee620c120bb58830483ce320c120ddd443048374510c120af99320482bd64c8120cfd53204833c54c8120d7d4f204835c53c8120ddd47204837451c8120ee90320483b840c8120ee99320483b964c8120eed5320483b854c8120f6d4f20483d853c8120fa8cb20483e932c8120fcd4720483f051c8120cfd52204833c5488120d7d4e204835c5388120ddd4620483745188120ebd5220483ac5488120bbd8e20482ed6388120f3d4e204836e5388120db14e20483cc5388120d314e20483e75188120db14620483e45188120d914620483eb5088120eb90220483ac4088120b798f54082dd63d50209f98f540835e63d50209798f540827d63d5020d758f540825d63d50209f98b540836e62d50209f987540827d61d50209f983540837a60d50209f596540833f54950209f98e540827d63950209f986540827d6195020cfd91540827f63550209f18d540827f62550209f589540827f61550209f185540833d5415020b798c54082dd6315020bd98454082f561150209f990540833e64150209f98c540835e63150209798c540827d6315020d758c540825d63150209f988540836e62150209f984540837661150209d984540827d6115020dd584540827561150209f980540837a60150209f993530827d64d4c209f98b530836e62d4c209f987530827d61d4c209f983530837a60d4c209f596530835f5394c209f992530827d6494c209f986530827d6194c2097596530835f5494c20d7952530835d5494c20d715253083cc6294c20d7d92530835e6494c20d7592530835c6494c20d798a530835c6294c20d7d86530835e6194c20d7586530835c6194c20d7982530835c6094c209fd91530827c6454c20d7d8d530827f6254c209f589530836c6254c209fd85530827c6154c20d7d95530835f5454c20d7951530835d5454c20d715153083cc6254c20d7d91530835e6454c20d7591530835c6454c20d7989530835c6254c20d3189530835f6154c20d7985530835d6154c20d7185530835e6054c20d7181530835c2054c20b798c530835d5314c209f990530827d6414c209f98c530835e6314c209798c530827e62
  | 14 => 0x9051483776314520dd98c51483756314520dd18c51483774314520dd90c51483754314520dd10c51483776214520ddd0851483764214520dd50851483744214520ddcc851483763214520d98c851483753214520d94c851483743214520ddd8051483756014520dd480514827e65d05209f597414827c65d0520cfd53414833c54d0520d7d4f414835c53d0520ddd47414837451d05209f996414827d65905209f196414833f5490520cf152414835f5390520d714e41483775190520dd146414827f65505209f995414827c6550520cfd51414833c5450520b7d8d41482dc6350520d7d4d414835c5350520bbd8941482ec6250520ddd4541483745150520bed8141482f860505209f994414827d65105209f194414833f5410520cf150414835f5310520d714c41482ee6210520bb58841483775110520dd144414827e65cc5209f597314827c65cc520cfd53314833c54cc520d7d4f314835c53cc520bb98b31482ed62cc520ddd47314837451cc5209f996314827d658c5209f196314833f548c520cf152314835f538c520d714e31483cd328c520ddd463148374518c5209fd95314827e654c5209f195314833f544c520cf151314835f534c520d714d3148377514c520dd145314827e650c5209f594314827c650c520af99031482bd640c520cfd50314833c540c520d7d4c314835c530c520bb98831482ed620c520f34c83148377510c520dd14431482fa600c520be580314827e65c8520cfd53214833c54c8520b798f21482dd63c8520d7d4f214835c53c8520dd147214833f5488520cf152214835f5388520d714e21483775188520dd14621482fa6088520be582214833f5448520cf151214835f5348520d714d21483775148520dd14521482fb6048520be181214827e6508520af99021482bd6408520cfd50214833c5408520d7d4c214835c5308520ddd44214827e65d0120cfd53404833c54d0120d7d4f404835c53d0120bb98b40482ed62d0120ddd47404837451d01209f996404833f5490120cf952404833d5490120cf152404835f5390120d714e40483775190120dd14640482be6590120cf996404823e6590120cfd4e404839f5390120c7d4e404833e5390120cf54e404833c5390120e714e404831c5390120eb8ca40483ad3290120cfd4640483b75190120cdd46404833c5190120ed14640483345190120af982404827f65501209f595404827c6550120cfd51404833c5450120d7d4d404835c5350120bbd8940482ec6250120ddd45404837451501209f994404833f5410120cf950404833d5410120cf150404835f5310120d714c40483775110120dd14440482be6510120cf994404823e6510120cfd4c404839f5310120c7d4c404833e5310120cf54c404833c5310120e714c404831c5310120eb8c840483ad321012
  | 15 => 0x4835d6014d20d7480534827f65d0d209f997434827d65d0d209f197434833f54d0d20cf153434835f53d0d20d714f434827f6590d209f996434827d6590d209f196434833f5490d20cf152434835f5390d20d714e43482ee6290d20bb58a43482fa6090d20be582434827f6550d209f995434827d6550d209f195434833f5450d20cf151434835f5350d20d714d434827f6510d209f994434827d6510d209f194434833f5410d20cf150434835f5310d20d714c43482ee6210d20bb588434827e65d0920cfd53424833c54d0920d7d4f424835c53d0920be98342482f960d09209f996424833f5490920cf152424835f5390920d714e424827c6550920cfd51424833c5450920d7d4d424835c5350920bed8142482f860509209f994424833f5410920cf150424835f5310920d714c424827e65cc920cfd53324833c54cc920d7d4f324835c53cc920be98332482f960cc9209f996324833f548c920cf152324835f538c920d714e32482ee658c920db996324826e658c920ebd5232483ac548c920bb58e32483cf538c920db94e324836c538c920f314e324834c538c920bb982324827c654c920cfd51324833c544c920d7d4d324835c534c920bed8132482f8604c920db195324826c654c920ebd5132483ac544c920f3d8d32483cf534c920db94d324836c534c920f314d324834c534c920fad8132482ec604c920fa181324827e650c920cfd50324833c540c920d7d4c324835c530c920bb98832483cd320c920cfd53514833c54d4520d7d4f514835c53d45209f993514827d64d45209f98f514827d63d4520ddd5351483b754d4520cdd53514837654d4520dd553514837454d4520ed153514833454d4520ddd4f51483d753d4520d5d4f514837653d4520dd54f514837453d4520f514f514835453d4520f98cb51483e532d4520ddd93514837664d4520dd593514837464d4520ddd8f514837663d4520dd58f514837463d4520ddd0f514837643d4520dd50f514837443d4520ddd8b514837742d4520dd90b514837542d4520dd10b514837732d4520dd8cb514837532d4520dd0cb514837760d4520dd58351482be6494520af592514833f5494520cf15251482de6394520b758e514835f5394520d714e51483775194520afd9151482bc6454520cfd51514833c5454520b7d8d51482dc6354520d7d4d514835c5354520cfd50514833c5414520d7d4c514835c5314520dd544514827e64145209f590514827e63145209f58c514836e3214520db4c851482f66514520dd99451483775414520edd5051483375414520dd95051483755414520dd15051483b45414520cd15051483775314520f5d4c51483575314520dd94c51483755314520dd14c51483d45314520d514c51483e63214520f94c851483776414520dd99051483756414520dd1
  | 16 => 0xe64c8220af59320883ba40c8220ee10320882ed65c8220db59720883ae64c8220eb59320882ee63c8220bb18f208836f53c8220db54f20882ee61c8220eb90320883ac40c8220be597208837965c8220ee99320883b964c82209f98f544827d63d51209f987544827d61d5120cfd8f544833e63d5120cf58f544833c63d5120cfd8b544833d62d5120cfd87544833e61d5120cf587544833c61d5120cfd83544833d60d5120cfd5254482de6395120b758e54482f66195120bd586544827e64951208f992544827e6395120d798e544825e63951209f58e544835d63951209758e544827d6295120db58a544827e6195120dd986544827661951209f586544837561951209d586544827d6095120de58254482df6355120b718d54482f76155120bd185544833f64551209fd8d544835f635512097d8d544827c6355120d718d544825c63551209fd89544836f62551209fd85544837761551209dd85544827c6155120dd185544827461551209fd81544837b60551209f994544833d5415120cf990544827e63151209f58c544827e62151209f188544827e61151209f58454482be6515120cf994544823e6515120cfd8c544833e6315120cf58c544833c6315120cfd88544833d6215120cfd84544833e6115120cf584544833c6115120cfd80544833d6015120cf480544833f54d4d20cf153534827e64d4d209f593534827e61d4d209f587534835f54d4d20e7d53534831f54d4d20d7953534835d54d4d20d7153534839c54d4d20c715353483cf62d4d20d7d93534835e64d4d20d7593534835c64d4d20d7d8b534835d62d4d20d7d87534835e61d4d20d7587534835c61d4d20d7d83534835d60d4d20af99253482bd6494d20cfd52534833c5494d20d7d4e53482f66194d20bd586534827e6494d20cf992534823e6494d209f592534833d6494d208f592534827e6394d209798e534827d6294d20db58a534827e6194d20dd98653482766194d209f58653483756194d209d586534827d6094d20de58253482bf6454d20af191534833f5454d20cf15153482f76154d20bd185534827f6454d20cfd91534823f6454d209f191534833c6454d208f191534835f6354d209fd89534836f6254d209bd89534827f6154d20ddd8553482776154d209f18553483746154d209d185534827f6054d20ded81534827e6514d20cfd50534833c5414d20d754c534827e6414d209f590534835e6314d209f988534836d6214d209f188534827e6114d209f58453482de6514d20d7994534825e6514d20d7d50534839f5414d20c7d50534835e5414d20d7550534835c5414d20e7150534831c5414d20f3588534835f6414d20d7990534835d6414d20d7190534835f6214d20d7588534834d6214d20d7d84534835e6114d20d7584534835c6114d20d7d8053
  | 17 => 0xa20cf951428833d5450a20bed8142882f86050a20cfd50428833c5410a20d794f328835d53cca20be98332882f960cca20db597328836f53cca20f394f328836d53cca20f354f32882ee61cca20fa98332882ed60cca20fa583328835f538ca20d714e328835e534ca20d754d32882fb604ca20be181328835f530ca20d714c32883cd320ca20bb594328836d650ca20f398c328836f530ca20f3d4c328834f530ca20db54c32883cc530ca20bb98432882ed600ca20af99251882bd6494620ddd46518827e6494620cf992518823e64946209f592518833d64946208f592518827e63946209f58e51882df6354620b718d518827f64546209f191518827f6354620d7d8d518825f63546209f18d518835c63546209718d518837551146209fd97418827e65d06209f597418833f54d0620cf15341882ee62d0620bb58b418827f65906209f996418827d65906209fd95418827d65506209f195418833f5450620cf15141882df6350620b718d41882ef6250620bb18941882fb6050620be181418827f65106209f994418827d65106209fd97318827e65cc6209f59731882ee62cc620bb58b318827f658c6209f996318827d658c620d7d4e318835c538c620bb98a31882ed628c620f3cca318827f654c6209f595318827c654c620bbd8931882ec624c6209fd94318827e650c6209f59431882be640c620af590318835f530c620d714c31883cf320c620be98031882f9600c620b798f21882dd63c8620dd94621883755188620be98221882f96088620db952218836c5488620bb98e21882ec6388620dbd4e218836d5388620f9946218836d5188620f954621883ea6088620bb58221883e96088620dd94521883755148620bed8121882f86048620af99021882bd6408620f948421882ed6508620db59421883ae6408620eb590218836e5408620db15021882ee6308620bb18c218836f5308620db54c21883e66108620f9d44218836d5108620f914421882ed6008620cf952408833d5490220bb98a40882ed6290220cf996408833d6590220cfd4e408833e5390220cf54e408833c5390220eb98a40883ad6290220ebcca40883ac3290220cf946408833d5190220eb88640883ac2190220cf950408833d5410220bb98840882ed6210220cf994408833d6510220cfd4c408833e5310220cf54c408833c5310220eb98840883ad6210220ebcc840883ac3210220cf944408833d5110220eb88440883ac2110220ee98040882be64cc220af593308835f53cc220d714f30883cf32cc220d794e308835d538c220bb98a30882ed628c220f30ca30883b8408c220afd9130882bc644c220d7d4d308835c534c220bbd8930882ec624c220f3cc930882f7614c220bd18530883b8404c220d794c308835d530c220bb98830882ed620c220f30c830882b
  | 18 => 0xbb18941c82fb6050720be18141c827f65107209f99441c827d6510720cf95041c833d5410720bb98841c82ed62107209fd9731c827e65cc7209f59731c833e54cc720cf55331c82ee62cc720bb58b31c837651cc720dd54731c827f658c7209f99631c827d658c720cf95231c833d548c720d794e31c835d538c720f34ca31c827f654c7209f59531c827c654c720cf95131c833d544c720bed8131c82f8604c7209fd9431c827e650c7209f59431c82be640c720af59031c833e540c720cf55031c835e530c720d754c31c82ee620c720bb58831c83cd320c720dd94431c8375510c720cf95321c833d54c8720b798f21c82dd63c8720dd94721c837551c8720be98321c82f960c8720cf95221c833d5488720cf95121c833d5448720af99021c82bd6408720cf95021c833d5408720dd94421c83755108720be98021c82f96008720cf95340c833d54d0320bb98b40c82ed62d0320cfd5240c833e5490320cf55240c833c5490320af59640c833d6590320cfd4e40c833e5390320cf54e40c833c5390320eb8ca40c83ad3290320cf94640c833d5190320cf95140c833d5450320bbd8940c82ec6250320cfd5040c833e5410320cf55040c833c5410320af59440c833d6510320cfd4c40c833e5310320cf54c40c833c5310320eb8c840c83ad3210320cf94440c833d5110320ee98040c82be64cc320af59330c833e54cc320cf55330c835e53cc320d754f30c82ee62cc320bb58b30c83cd32cc320ee10330c833e548c320cf55230c835f538c320d714e30c83ce328c320afd9130c82bc644c320cf95130c833d544c320d794d30c835d534c320bbd8930c82ec624c320f34c930c82f7614c320bd18530c833e540c320cf55030c835f530c320d714c30c82ee620c320bb58830c83ce320c320ee10030c827e63d52209f58f548836d62d52209f987548827d61d5220de983548833f54952209f98e548827d63952209f986548827d6195220cfd91548827f63552209f18d548827f61552209f185548833d5415220cf990548827e63152209f58c548836d62152209f984548827d6115220de980548827e64d4e209f593538836d62d4e209f987538827d61d4e20de983538835f5394e209f992538827d6494e209f986538827d6194e209fd91538827c6454e20d7d8d538836f6254e209fd85538827c6154e20d754c538827e6414e209f590538835e6314e20db588538827e6114e209f584538837a6014e209fd97438827e65d0e209f597438827c65d0e20bb98b43882ed62d0e209fd96438827e6590e209f596438827c6590e20be98243882f96090e209fd95438827e6550e209f595438827c6550e20bbd8943882ec6250e209fd94438827e6510e209f594438827c6510e20cf953428833d54d0a20be98342882f960d0a20cfd52428833c549
  | 19 => 0xe54c833d6395320cf18e54c833e6295320cf18a54c833f6195320cf98654c833d6195320cf18654c833f6095320cf58254c833f64553209fd8d54c827c63553209fd8554c827c6155320cfd9554c833f6355320cf98d54c833d6355320cf18d54c833e6255320cf18954c833f6155320cf98554c833d6155320cf18554c833f6055320cf58154c833d5415320cf99054c827e63153209f58c54c836e62153209f98454c827d6115320de58054c82be64d4f20af59353c833e54d4f20cf55353c82f661d4f20bd58753c827e64d4f20cf99353c823e64d4f209f59353c833d64d4f208f59353c836e62d4f209f98753c837661d4f209d98753c827d61d4f20dd58753c827561d4f20de58353c833e5494f20cf55253c835f5394f209f99253c827d6494f20db98a53c827e6194f209f58653c833e5454f20cf55153c827f6454f209f19153c835f6354f209fd8553c827c6154f20af99053c82bd6414f20cf95053c833d5414f20d754c53c827e6414f20cf99053c823e6414f209f59053c833d6414f208f59053c835e6314f20db98853c827e6114f209f58453c83796014f209fd9743c827e65d0f209f59743c827c65d0f20cf95343c833d54d0f209fd9643c827e6590f209f59643c827c6590f20cf95243c833d5490f20bb98a43c82ed6290f209fd9543c827e6550f209f59543c827c6550f20cf95143c833d5450f20bed8143c82f86050f209fd9443c827e6510f209f59443c827c6510f20cf95043c833d5410f20bb98843c82ed6210f20cf95342c833d54d0b20cf95242c833d5490b20be98242c82f96090b20cf95142c833d5450b20cf95042c833d5410b20be98042c82f96010b20cf95332c833d54ccb20d7d4f32c835c53ccb20cf95232c833d548cb20d794e32c835d538cb20be98232c82f9608cb20db59632c83ae548cb20eb55232c836e538cb20f394e32c83cd538cb20db14e32c82ee608cb20fa98232c83e9608cb20cf95132c833d544cb20d7d4d32c835c534cb20bbd9532c836f654cb20eb95132c83ad544cb20f3d8d32c83cf534cb20db94d32c836c534cb20f314d32c834c534cb20bb18132c833e540cb20cf55032c835e530cb20d754c32c83cd320cb20be98032c82f9600cb20af99351c82bd64d4720cf95351c833d54d4720b798f51c82dd63d4720cf95251c833d5494720ddd4651c827e64947209f59251c827e63947209f58e51c836e3294720db4ca51c833e5454720cf55151c827f64547209f19151c827f63547209f18d51c82be6414720af59051c833e5414720cf55051c837551147209fd9741c827e65d07209f59741c833e54d0720cf55341c827f65907209f99641c827d6590720cf95241c833d54907209fd9541c827d65507209f19541c833e5450720cf55141c82df6350720b718d41c82ef6250720
  | 20 => 0xc35e540c430d7150310c2de620c430f3948310c35d520c430f3548310c34d520c430b7984310c3d6610c430f5944310c35d510c430f5544310c3da600c430b7580310c3d9600c4309fd97210c27e65c84309f597210c2de63c8430b758f210c36e52c8430db54b210c27f65884309f996210c27d6588430b798e210c2dd6388430db94a210c36d5288430f38ca210c27f65484309f595210c27c6548430b7d8d210c2dc6348430db949210c36d5248430bed81210c2f860484309fd94210c27e65084309f594210c2be6408430af590210c2df6308430b718c210c36e5208430db548210c3ce32084309f992500c27d6494030d78ca500c35c3294030d78c6500c35c31940309f597400c36e52d0030db54b400c27f65900309f596400c33e5490030cf552400c2de6390030b758e400c36e5290030db54a400c33f6590030cf996400c33d6590030cf196400c39e6390030e758e400c33e5390030cf94a400c3ae5290030cb94a400c33d5290030eb54a400c32d5290030e78ca400c39c3290030cf946400c33d5190030e78c6400c39c3190030af982400c33e50900309fd95400c36e5250030db549400c27f65100309f994400c27d65100309f194400c33e5410030cf550400c2de6310030b758c400c36e5210030db548400c33f6510030cf994400c33d6510030cf194400c39e6310030e758c400c33e5310030cf948400c3ae5210030cb948400c33d5210030eb548400c32d5210030e78c8400c39c3210030cf944400c33d5110030e78c4400c39c3110030af980400c3ba6010030cf940400c2be64cc030af593300c36e52cc030db54b300c39e64cc030e7593300c2de62cc030f394b300c35d52cc030f354b300c34d52cc030b7987300c39e40cc030e7103300c2dd638c030d794e300c36e528c030db54a300c3ba408c030ee102300c2f9638c030de94e300c3da538c030fa94a300c3e9528c030f68ca300c3d8328c030f68c6300c3d8318c0309fd95300c2bf644c030af191300c2ef624c030bb189300c36e524c030db549300c2f7614c030bd185300c3ba404c030ee101300c2df654c030d7d95300c25f654c030e7d91300c39c644c030f3d89300c2dc624c030f3189300c2cc624c030f3949300c35d524c030f3549300c34d524c030f5d85300c2dc614c030f5185300c2d4614c030b7d81300c35e504c030f6d01300c39e404c030e7101300c3d8404c030e6101300c2fb654c030ded95300c27b654c030eed91300c3b8644c030bed8d300c3db634c030de94d300c3da534c030f6d0d300c3d8434c030fad89300c3e8624c030fa949300c3e9524c030fcd85300c3f0614c0309f98f54c827d63d5320db98b54c827e61d53209f58754c837960d5320cfd5254c827e63953209f58e54c827e61953209f58654c833f6395320cf98
  | 21 => 0x6510c30cf950430c33d5410c30be980430c2f96010c30dbd4a520c27e64948309f592520c27e61948309f586520c36f5494830db952520c36d5494830db152520c3cc6394830dbd92520c36e6494830db592520c36c6494830db18e520c36f4394830db90e520c36d4394830db10e520c36f6194830db986520c36d6194830db186520c36e6094830db182520c27f64548309f191520c27f61548309f185520c36f6554830dbd51520c36e5454830db551520c36c5454830f318d520c36f6454830db991520c36d6454830db191520c36e6354830dbd0d520c36e4354830db50d520c36c4354830dbd85520c36e6154830db585520c36c6154830db981520c36c6054830db0c1520c2ee6214830db548520c27f65d08309f997420c27d65d0830b798f420c2dd63d0830db94b420c36d52d08309fd96420c27e65908309f596420c36e5290830db54a420c27f65508309f595420c27c6550830b7d8d420c2dc6350830db949420c36d5250830bed81420c2f860508309fd94420c27e65108309f594420c36e5210830db548420c35e53cc830db94b320c36d52cc830be983320c2f960cc8309f596320c36d528c830b7596320c35d658c83097596320c2de628c830f394a320c35d528c830f354a320c34d528c830b7986320c2dd608c8309fd95320c35e534c830db949320c36e520c830db548320c3cd320c830be980320c2f9600c830b7988320c3ce620c830f3948320c35d520c830f3548320c34d520c830b7984320c3da600c830b7580320c3d9600c830bb98b510c2ed62d4430db94b510c36d52d4430db94a510c36d5294430ddd46510c27e64944309f592510c27e62944309f58a510c36e5254430db549510c27f64544309f191510c27f62544309f189510c2be6414430af590510c2ee6214430bb588510c36e5214430db548510c37551144309fd97410c27e65d04309f597410c33e54d0430cf553410c2de63d0430b758f410c36e52d0430db54b410c27f65904309f996410c27d6590430db94a410c36d5290430dd946410c37551904309fd95410c27d65504309f195410c33e5450430cf551410c2df6350430b718d410c2ef6250430bb189410c36e5250430db549410c3765150430dd545410c2fb6050430be181410c27f65104309f994410c27d6510430db948410c36d5210430bb98b310c2ed62cc430db94b310c36d52cc430dd947310c37551cc430be983310c2f960cc4309f596310c36e528c430db54a310c2dd658c430d7596310c35e548c430d7152310c2de628c430f394a310c35d528c430f354a310c34d528c430b7986310c35d518c430b7582310c27f654c430db949310c36d524c430af990310c2bd640c430db948310c36d520c430dd944310c375510c430f54c4310c2fa600c430be580310c39e640c430e7590310
  | 22 => 0x530cf152214c36f5288530db14a214c3cd3288530ddd46214c37451885309fd95214c27e65485309f195214c33f5448530cf151214c36f5248530db149214c3775148530dd145214c27e65085309f594214c27c6508530af990214c2bd6408530cfd50214c33c5408530b798c214c2dd6308530dbd48214c36c5208530f34c8214c3775108530dd144214c2fa6008530be580214c27e65d0130cfd53404c33c54d0130b798f404c2dd63d0130dbd4b404c36c52d0130ddd47404c37451d01309f996404c33f5490130cf952404c33d5490130cf152404c36f5290130db14a404c3775190130dd146404c2be6590130cf996404c23e6590130cfd4a404c3af5290130cbd4a404c33c5290130eb14a404c32c5290130e7cca404c39d3290130cfd46404c3b75190130cdd46404c33c5190130ed146404c3345190130af982404c27f65501309f595404c27c6550130cfd51404c33c5450130b7d8d404c2dc6350130dbd49404c36c5250130ddd45404c37451501309f994404c33f5410130cf950404c33d5410130cf150404c36f5210130db148404c3775110130dd144404c2be6510130cf994404c23e6510130cfd48404c3af5210130cbd48404c33c5210130eb148404c32c5210130e7cc8404c39d3210130cfd44404c3b75110130cdd44404c33c5110130ed144404c3345110130af980404c3ba6010130af993304c2bd64cc130cfd53304c33c54cc130dbd4b304c36c52cc130ddd47304c37451cc130ee903304c3b840cc130ee993304c3b964cc130eed53304c3b854cc130fad4b304c3e852cc130f6ccb304c3d932cc130fcd47304c3f051cc130cfd52304c33c548c130dbd4a304c36c528c130ddd46304c374518c130e7d52304c39c548c130b758a304c3cf528c130d714a304c3cc528c130d314a304c3d7518c130d7146304c3d4518c130d5146304c3db508c130e7902304c39c408c130bb98b540c2ed62d50309f98f540c35e63d50309f98b540c36e62d50309b98b540c27d62d5030db58b540c26d62d50309f987540c27d61d50309f983540c37a60d50309f596540c33f54950309f98a540c27d62950309f986540c27d6195030cfd91540c27f63550309f58d540c27f62550309f189540c27f61550309f185540c33d5415030bb988540c2ed6215030bd984540c2f561150309f990540c33e64150309f98c540c35e63150309f988540c36e62150309b988540c27d6215030db588540c26d62150309f984540c37661150309d984540c27d6115030dd584540c27561150309f980540c37a60150309f992530c33e6494c308f992530c27d6494c30cf592530c23d6494c309f597430c33f54d0c30cf153430c27f6590c309f596430c33e5490c30cf552430c2fa6090c30be582430c27f6550c30cfd51430c33c5450c309fd94430c27d
  | 23 => 0xbd48324c3cd320c930cfd53514c33c54d4530dbd4b514c36c52d45309f993514c27d64d45309f98b514c27d62d4530ddd53514c3b754d4530cdd53514c37654d4530dd553514c37454d4530ed153514c33454d4530ddd4b514c3e752d4530d9d4b514c37652d4530dd54b514c37452d4530f914b514c36452d4530f5ccb514c3d532d4530ddd93514c37664d4530dd593514c37464d4530ddd8f514c37743d4530dd90f514c37543d4530dd10f514c37762d4530dd98b514c37562d4530dd18b514c37742d4530dd90b514c37542d4530dd10b514c37732d4530dd8cb514c37532d4530dd0cb514c37760d4530dd583514c2be6494530af592514c33f5494530cf152514c2ee6294530bb58a514c36f5294530db14a514c3775194530afd91514c2bc6454530cfd51514c33c5454530bbd89514c2ec6254530dbd49514c36c5254530cfd50514c33c5414530dbd48514c36c5214530dd544514c27e64145309f590514c27e62145309f588514c35f3214530d74c8514c2f66514530dd994514c3775414530edd50514c3375414530dd950514c3755414530dd150514c3b45414530cd150514c3775214530f9d48514c3675214530dd948514c3755214530dd148514c3e45214530d9148514c3d73214530f54c8514c3776414530dd990514c3756414530dd190514c3776314530ddd0c514c3764314530dd50c514c3744314530ddd88514c3766214530dd588514c3746214530ddd08514c3764214530dd508514c3744214530ddcc8514c3573214530dd8c8514c3753214530d54c8514c3743214530ddd80514c3756014530dd4c0514c27e65d05309f597414c27c65d0530cfd53414c33c54d0530dbd4b414c36c52d0530ddd47414c37451d05309f996414c27d65905309f196414c33f5490530cf152414c36f5290530db14a414c3775190530dd146414c27f65505309f995414c27c6550530cfd51414c33c5450530b7d8d414c2dc6350530bbd89414c2ec6250530dbd49414c36c5250530ddd45414c3745150530bed81414c2f860505309f994414c27d65105309f194414c33f5410530cf150414c2de6310530b758c414c36f5210530db148414c3775110530dd144414c27e65cc530cfd53314c33c54cc530bb98b314c2ed62cc530dbd4b314c36c52cc530dd147314c33f548c530cf152314c36f528c530db14a314c377518c530dd146314c2fa608c530be582314c33f544c530cf151314c36f524c530db149314c377514c530dd145314c2fb604c530be181314c27e650c530af990314c2bd640c530cfd50314c33c540c530dbd48314c36c520c530ddd44314c27e65c85309f597214c27c65c8530cfd53214c33c54c8530b798f214c2dd63c8530dbd4b214c36c52c8530ddd47214c37451c85309f996214c27d65885309f196214c33f5488
  | 24 => 0x544c3796095130bbd89544c2ec6255130bdd85544c2f46155130cfd91544c27f6355130d7d8d544c27f6255130dbd89544c26f62551309f189544c36c62551309b189544c27f6155130ddd85544c27761551309f185544c37461551309d185544c27f6055130ded81544c27e6515130cf550544c33e64151309f98c544c27c63151309f988544c27d62151309f984544c27d6115130af994544c33e65151308f994544c33f6315130cf58c544c33f6215130cf988544c33d6215130cf188544c33f6115130cf984544c33d6115130cf184544c33f6015130cf580544c33d30151309f997434c33f54d0d30cf153434c2fa60d0d30be583434c27e6590d30cfd52434c33c5490d309f195434c33f5450d30cf151434c2fb6050d30be181434c27e6510d30cfd50434c33c5410d30cfd53524c33c54d49309f993524c27d64d49309f987524c27d61d4930dbd53524c3af54d4930cbd53524c36e54d4930db553524c36c54d4930eb153524c32c54d4930f3d8f524c36f64d4930db993524c36d64d4930db193524c36f63d4930dbd0f524c36e43d4930db50f524c36c43d4930dbd87524c36e61d4930db587524c36c61d4930dbd83524c36d60d4930af992524c2bd6494930cfd52524c33c5494930dbd4a524c2f66194930bd586524c2bf6454930af191524c33f5454930cf151524c2f76154930bd185524c33f5414930cf150524c36d52149309f990524c27d64149309f984524c27d6114930bb994524c36e6514930dbd50524c3af5414930cbd50524c36e5414930db550524c36c5414930eb150524c32c5414930f358c524c36f6414930db990524c36d6414930db190524c36f6314930dbd0c524c36e4314930db50c524c36c4314930dbd84524c36e6114930db584524c36c6114930dbd80524c36d6014930db4c0524c27e65d09309f597424c27c65d0930cfd53424c33c54d0930dbd4b424c36c52d09309f996424c27d65909309f196424c33f5490930cf152424c2de6390930b758e424c36f5290930db14a424c2fa6090930be582424c27f65509309f995424c27c6550930cfd51424c33c5450930dbd49424c36c52509309f994424c27d65109309f194424c33f5410930cf150424c2de6310930b758c424c36f5210930db148424c27e65cc930cfd53324c33c54cc930db14b324c2de65cc930d7997324c25e65cc930e7d53324c39c54cc930f3d4b324c35c52cc930f314b324c34c52cc930b7983324c33f548c930cf152324c2dd638c930dbd4a324c36c528c930be982324c2f9608c930cfd51324c33c544c930dbd49324c36c524c930bed81324c2f8604c930e7d51324c39c544c930f3d89324c3cf524c930d7149324c3cc524c930d3149324c3db604c930b7181324c3d8604c9309f994324c33f540c930cf150324c2de630c930d
  | 25 => 0x3ce528ca30d754a328c3cd528ca30b7986328c3da608ca30b7582328c3d9608ca30db949328c36d524ca30bed81328c2f8604ca30f34c8328c2dd650ca30d7594328c3ce620ca30f3d48328c35d520ca30f3148328c2de610ca30b7580328c2be6494630af592518c37751946309f992518c33e64946308f992518c27d6494630cf592518c23d64946309f98a518c27d6294630bbd89518c2ec62546309fd91518c27c64546309fd89518c36f62546309bd89518c27c6254630db189518c26c6254630dd544518c27f65d06309f997418c27d65d0630cfd53418c33c54d0630b798f418c2dd63d06309fd96418c27e65906309f596418c27f65506309f595418c27c6550630cfd51418c33c5450630b7d8d418c2dc6350630bbd89418c2ec6250630bed81418c2f860506309fd94418c27e65106309f594418c2ee62cc630bb58b318c376518c630dd546318c2fa608c630be582318c35e548c630d7152318c2de628c630d754a318c3d6518c630d7546318c3d5518c630f6982318c2dd608c630f6582318c376514c630dd545318c2fb604c630be181318c2be640c630af590318c3d5310c630b7594318c35d650c630e7990318c39d640c630d7950318c35c540c630b7988318c35d520c630f5984318c3d7510c630d7544318c3d4510c630b7580318c27f65c86309f997218c27d65c8630b798f218c2dd63c86309fd96218c27e65886309f596218c2de6388630b758e218c3ce32886309fd95218c27d65486309f195218c2df6348630b718d218c27f65086309f994218c27d6508630af990218c2bd6408630b7d8c218c2dc6308630f38c8218c2fa6008630be580218c33e5490230cf552408c2de6390230b758e408c33e6590230cf596408c39e6390230e758e408c33e5290230cf54a408c39e3290230e70ca408c33e5190230cf546408c39e3190230e70c6408c33e5410230cf550408c2de6310230b758c408c33e6510230cf594408c39e6310230e758c408c33e5210230cf548408c39e3210230e70c8408c33e5110230cf544408c39e3110230e70c4408c3ba6010230af993308c2bd64cc230ee903308c3b840cc230b7597308c35d65cc230e7993308c39d64cc230b798b308c35d52cc230b7987308c39e40cc230e7103308c2f965cc230de597308c3ba64cc230ee593308c27e62d51309f58b544c27e61d51309f587544c33f63d5130cf58f544c33f62d5130cf98b544c33d62d5130cf18b544c33f61d5130cf987544c33d61d5130cf187544c33f60d5130cf583544c33f5495130bb98a544c2ed6295130bd986544c2f561951309f992544c23e64951309f58e544c35d63951309f98a544c36e62951309b98a544c27d6295130db58a544c26d62951309f986544c37661951309d986544c27d6195130dd586544c27561951309f582
  | 26 => 0x20cb30be98032cc2f9600cb30af99351cc2bd64d4730cf95351cc33d54d4730bb98b51cc2ed62d4730cf95251cc33d5494730ddd4651cc27e64947309f59251cc27e62947309f58a51cc35f3294730d74ca51cc33e5454730cf55151cc27f64547309f19151cc27f62547309f18951cc2be6414730af59051cc33e5414730cf55051cc37551147309fd9741cc27e65d07309f59741cc33e54d0730cf55341cc27f65907309f99641cc27d6590730cf95241cc33d54907309fd9541cc27d65507309f19541cc33e5450730cf55141cc2df6350730b718d41cc2ef6250730bb18941cc2fb6050730be18141cc27f65107309f99441cc27d6510730cf95041cc33d5410730b798c41cc2dd6310730cf95331cc33d54cc730bb98b31cc2ed62cc730dd94731cc37551cc730be98331cc2f960cc730cf95231cc33d548c730cf95131cc33d544c730af99031cc2bd640c730cf95031cc33d540c730dd94431cc375510c730be98031cc2f9600c7309fd9721cc27e65c87309f59721cc33e54c8730cf55321cc2de63c8730b758f21cc37651c8730dd54721cc27f65887309f99621cc27d6588730cf95221cc33d5488730db94a21cc36d5288730f34ca21cc27f65487309f59521cc27c6548730cf95121cc33d5448730bed8121cc2f860487309fd9421cc27e65087309f59421cc2be6408730af59021cc33e5408730cf55021cc2de6308730b758c21cc36e5208730db54821cc3cd3208730dd94421cc3755108730cf95340cc33d54d0330b798f40cc2dd63d0330cfd5240cc33e5490330cf55240cc33c5490330af59640cc33d6590330cf94a40cc33d5290330e7cca40cc39d3290330cf94640cc33d5190330cf95140cc33d5450330b7d8d40cc2dc6350330cfd5040cc33e5410330cf55040cc33c5410330af59440cc33d6510330cf94840cc33d5210330e7cc840cc39d3210330cf94440cc33d5110330ee98040cc35d63d52309f98b548c27d62d52309f987548c27d61d5230de983548c33f54952309f98a548c27d62952309f986548c27d6195230cfd91548c27f62552309f189548c27f61552309f185548c33d5415230cf990548c35d63152309f988548c27d62152309f984548c27d6115230de980548c33e54d0e30cf553438c2fa60d0e30be583438c33f5490e30cf152438c33e5450e30cf551438c2fb6050e30be181438c33f5410e30cf150438c36f5294a309f992528c27d6494a309f986528c27d6194a309fd91528c27c6454a309fd85528c27c6154a30db548528c27f65d0a309f997428c27d65d0a30b798f428c2dd63d0a309fd96428c27e6590a309f596428c2fa6090a30be582428c27f6550a309f595428c27c6550a30b7d8d428c2dc6350a309fd94428c27e6510a309f594428c36e528ca30db54a328c2fa608ca30be582328c
  | 27 => 0x40eb48421103b52108440af98021102bd6008440af98e50102bd6394040cf94e501033d5394040af98a50102bd6294040cf94a501033d5294040af98650102bd6194040cf946501033d5194040cf98e501033d6394040cf98a501033d6294040cfcca501033e3294040cf4ca501033c3294040cf986501033d6194040cfcc6501033e3194040cf4c6501033c3194040cfc86501033e2194040cf486501033c2194040ce98250103b96594040eed8e50103ba6394040ee58e50103b86394040eed4e50103ba5394040ee54e50103b85394040eed8a50103ba6294040ee58a50103b86294040eed4a50103ba5294040ee54a50103b85294040eecca50103ba3294040ee4ca50103b83294040eed8650103ba6194040ae98650103b96194040ee18650103bb5194040ee94650103b95194040ee14650103bb3194040ee8c650103b93194040ee0c650103bb2194040ee88650103b92194040ee086501035e63d53309f98b54cc27d62d53309f98754cc27d61d5330de58354cc33f54953309f98a54cc27d62953309f98654cc27d6195330cf98e54cc33c6395330cfd8a54cc33e6295330cf58a54cc33c6295330cfd8654cc33e6195330cf58654cc33c6195330cfd8254cc33d6095330cfd9154cc27f62553309f18954cc27f61553309f18554cc33f6555330cf98d54cc33c6355330cfd8954cc33e6255330cf58954cc33c6255330cfd8554cc33e6155330cf58554cc33c6155330cfd8154cc33d6055330cf55054cc33e6415330d798c54cc27e62153309f58854cc27e61153309f58454cc3796015330cf95343cc33d54d0f30cf95243cc33d5490f30be98243cc2f96090f30cf95143cc33d5450f30cf95043cc33d5410f30be98043cc2f96010f30af99352cc2bd64d4b30cf95352cc33d54d4b30bd98752cc2f561d4b30cf95252cc33d5494b30dbd4a52cc27e6494b309f59252cc27e6194b309f58652cc33e5454b30cf55152cc27f6454b309f19152cc27f6154b309f18552cc2be6414b30af59052cc33e5414b30cf55052cc36d5214b309fd9742cc27e65d0b309f59742cc33e54d0b30cf55342cc27f6590b309f99642cc27d6590b30cf95242cc33d5490b30b798e42cc2dd6390b309fd9542cc27d6550b309f19542cc33e5450b30cf55142cc2fb6050b30be18142cc27f6510b309f99442cc27d6510b30cf95042cc33d5410b30b798c42cc2dd6310b30cf95332cc33d54ccb30db94b32cc36d52ccb30be98332cc2f960ccb30e795332cc39d54ccb30d794b32cc3ce52ccb30f354b32cc2de60ccb30f698332cc3d960ccb30cf95232cc33d548cb30cf95132cc33d544cb30b7d9532cc35f654cb30e795132cc39d544cb30f3d8932cc3cf524cb30d794932cc3cc524cb30b718132cc33e540cb30cf55032cc36e520cb30db54832cc3cd3
  | 28 => 0x58032102be63d4440af58f511033f53d4440cf54f51102be62d4440af58b511033f52d4440cf54b51102be60d4440ee98351102ba60d4440af59651102be6394440af58e51102be6294440af58a511033f5194440edd4651103b86094440afd8d511039f6354440a7d8d51102bc6354440e718d511029c6354440cfd4d511033d5354440afd8951103af6254440abd8951102bc6254440eb18951102ac6254440cfd49511033d5254440edd45511033e5154440ee18151102be6314440e798c511029e6314440af58c511039d6314440a758c51102be6214440eb98851102ae6214440af58851103ad6214440ab58851102be6114440cfd4451103b65114440cf54451103b55114440cd54451102be6014440ee98051102ba6014440afd9731102be65cc440af59731102bc65cc440e794f311039d53cc440af98b31103ae62cc440ab98b31102bd62cc440eb58b31102ad62cc440af98331103ba60cc440ae98331102bd60cc440ee58331102b960cc440afd9631102be658c440af59631102bc658c440af58e311039f538c440e714e31102be628c440af58a311039f328c440e74ca31102be618c440ed94631103b5518c440e7cc631103b7318c440af98231102bd608c440afd9531102be654c440af59531102bc654c440e794d311039d534c440afd8931102bc624c440ed94531103b5514c440edcc5311039e314c440afd8131103bb604c440aed8131102bc604c440ee18131102b8604c440afd9431102be650c440cf994311023e650c440af594311033d650c4408f59431102bc650c440af98c311039f530c440e714c31102be620c440af588311039f320c440e74c831102be610c440e7cc431103b6310c440e74c431103b5310c440af98031102bd600c440afd9721102be65c8440af59721102bc65c8440afd8f21102be63c8440e798f211029e63c8440af58f211039d63c8440a758f21102bc63c8440eb94b21103ad52c8440af98321103ba60c8440ae98321102bd60c8440ee58321102b960c8440afd9621102be6588440af59621102bc6588440afd8e21102be6388440af58e21102bc6388440af58a21103af5288440eb14a21103ae3288440eb4ca21102be6188440ed94621103b55188440ebc8621103b72188440af98221102bd6088440afd9521102be6548440af59521102bc6548440afd8d21102be6348440af58d21102bc6348440eb94921103ad5248440ed94521103b55148440edc8521103ae2148440afd8121103bb6048440aed8121102bc6048440ee18121102b86048440afd9421102be6508440cf994211023e6508440af594211033d65084408f59421102bc6508440afd8c21102be6308440af58c21102bc6308440af98821103af5208440eb14821103ae3208440eb4c821102be6108440ebc8421103b621084
  | 29 => 0x1102bd6448440af191211036e5248440db54921103765148440dd54521102fb6048440be181211027f65084409f994211027d6508440afd9021102be6408440af59021102bc6408440ebd0821103ac4208440cfd0e501033e4394040cf50e501033c4394040cfd0a501033e4294040cf50a501033c4294040cfd06501033e4194040cf506501033c4194040af98f40102bd63d0040af98b40102bd62d0040af98740102bd61d0040af592401033e5490040be592401037a5490040ee95240103bb4390040ee90e40103b94390040ee10e40103bb4290040ee90a40103b94290040ee10a40102fa6190040eed0640103ba4190040ee50640103b841900409fd9540102bf6550040cfd95401023f6550040afd8d40102bc6350040afd8940102bc6250040afd8540102bc6150040afd81401033e5050040bed95401037b65500409ed9540102fb6450040eed91401037a5450040ee95140102f86150040ee90540103b84150040af98b53102bd62d4c40af98753102bd61d4c40af98353103ba60d4c40ae98353102bd6594c40cfd4e531039f5394c40af98a53102bd6294c40af98653102bd6194c40e7d4d531033e5354c40afd8953102bc6254c40afd8553102bc6154c40af98c531033f5314c40e794c531033d5314c40e754c53102be6214c40eb98853102ae6214c40af58853103ad6214c40ab58853102be6114c40ed98453102b66114c40af58453103b56114c40ad58453102be6014c40ee98053102ba6014c40af98f52102bd63d4840af98752102bd61d4840af98352103ba60d4840ae98352102bd6594840af98e52102bd6394840cfd4a52103af5294840af98652102bd6194840afd8d52102bc6354840ebd49521033e5254840afd8552102bc6154840af98c521039e6314840a798c52102bd6314840e758c521029d6314840af988521033f5214840eb948521033d5214840eb54852102be6114840ed98452102b66114840af58452103b56114840ad58452102be6014840ee98052102ba6014840afd9732102be65cc840af59732102bc65cc840e794f321039d53cc840af98732102bd61cc840af98332102bd60cc840afd9632102be658c840af59632102bc658c840af58e32102be628c840eb94a32103ad528c840e7cca32103af328c840af98632102bd618c840af98232102bd608c840afd9532102be654c840af59532102bc654c840e794d321039d534c840eb94932103ad524c840ebcc9321039e324c840afd8532102bc614c840afd8132103bb604c840aed8132102bc604c840ee18132102b8604c840afd9432102be650c840af59432102bc650c840af98c32102be620c840e7cc832103ae320c840e74c832103ad320c840e34c832102be610c840af58432102be600c840ee98032102ba600c840af58032103b9600c840ae
  | 30 => 0x5e53cc840d754f321027f658c8409f996321027d658c840afd9232102be648c840af59232102bc648c840db94a321036d528c8409fd95321027d654c8409f19532102bf644c840af99132102bd644c840af191321035e534c840d754d321036e524c840db54932102fb604c840be181321027f650c8409f994321027d650c840afd9032102be640c840af59032102bc640c840f34c832102fa600c840be580321037751944409f98e511027d63944409f98a511027d6294440b7d8d51102dc6354440bbd8951102ec62544409fd8d511035f635444097d8d511027c6354440d718d511025c6354440cfd0d511033d43544409fd89511036f62544409bd89511027c6254440db189511026c6254440cfd09511033d4254440de18151102de6314440b758c51102ee6214440bb58851103755114440dd947411037551d0440be98341102f960d0440af98f41102bd63d0440cf54f41102be62d0440af58b411033d52d0440cf94741103b651d0440ed54741103ba60d0440af58341103b960d0440ae583411027d6590440af59241102bd6590440cf59641102be6390440af58e41102be6290440af58a41102be6190440cf54641103bb6090440af58241103b860904409fd9541102df6350440b718d41102ef6250440bb18941102fb6050440afd95411033f6550440afd8d411039f6350440a7d8d41102bc6350440e718d411029c6350440cf54d41102bf6250440ebd8941102af6250440af18941103ac6250440ab189411033d5250440edd85411033e5150440afd8141103bb6050440aed8141103b86050440af99041103765110440dd54441102fa6010440be58041102be6310440af58c41102be6210440af58841102be6110440ed98441103b65110440cf54441103b55110440cd54441103ba6010440af58041103b960104409fd97311027e65cc4409f59731102bf64cc440af99331102bd64cc440af193311035e53cc440d754f31102ee62cc440bb58b31102fa60cc440be583311027f658c4409f996311027d658c440afd9231102be648c440af59231102bc648c440e7d0e311039c438c440dd9463110375518c4409fd95311027d654c4409f19531102bf644c440af99131102bd644c440af191311035e534c440d754d3110376514c440dd54531102fb604c440be181311027f650c4409f994311027d650c440afd9031102be640c440af59031102bc640c440e7d0c311039c430c4409fd97211027e65c84409f59721102bf64c8440af99321102bd64c8440af19321102de63c8440b758f211036e52c8440db54b21102fa60c8440be583211027f65884409f996211027d6588440afd9221102be6488440af59221102bc6488440ebd0a21103ac4288440dd946211037551884409fd95211027d65484409f19521102bf6448440af9912
  | 31 => 0x54540dd544515027e63145409f58c515027e62145409f588515027e65d0540ddd4641503745190540be98241502f96090540b7d8d41502dc6350540bbd8941502ec6250540ddd4541503745150540bed8141502f860505409f99441503b541105409f997315027d65cc5409f19731502ee62cc540bb58b315037751cc540dd147315027e658c5409f596315027c658c540d7d4e315035c538c5409fd95315027e654c5409f195315027e650c5409f594315027c650c540af99031502bd640c540d7d4c315035c530c540ddd443150374510c5409f997215027d65c85409f19721502de63c8540b758f215037751c8540dd147215027e65885409f596215027c6588540dbd4a215036c52885409fd95215027e65485409f195215027e65085409f594215027c6508540af99021502bd6408540dbd48215036c5208540ddd4421503745108540de147405033f5390140cf14e405033f5290140cf14a405033f5190140cf14640503bb5090140d7d4e531027e6294c409f58a531027e6194c409f586531027f6254c409f189531027f6154c409f185531035d5314c40bb98853102ed6214c40bd98453102f56114c40d794f431035d53d0c40be98343102f960d0c40cf94f431039e53d0c40e754f43102be62d0c40af58b43102be61d0c40af58743103ba60d0c40af58343103b960d0c409f59643102bd6490c40af596431033d6590c40af98e431033d5390c40af98a43102bd6290c40af98643102bd6190c40af582431027f6550c40afd95431033f6550c40e7d8d431033e5350c40afd8943102bc6250c40afd8543102bc6150c40afd8143102be6410c40d794c431035d5310c40be98043102f96010c40af98c431039e6310c40e794c431033d5310c40e754c43102be6210c40af58843102be6110c40af58443103ba6010c40af58043103b96010c40dbd4a521027e63948409f58e521027e61948409f586521027f63548409f18d521027f61548409f18552102de6314840b758c521036d5214840bd98452102f56114840db94b421036d52d0840be98342102f960d0840af98f42102bd63d0840cf94b42103ae52d0840eb54b42102be61d0840af58742103ba60d0840af58342103b960d08409f59642102bd6490840af596421033d6590840af98e42102bd6390840af98a421033d5290840af98642102bd6190840af582421027f6550840afd95421033f6550840afd8d42102bc6350840ebd89421033e5250840afd8542102bc6150840afd8142102be6410840db948421036d5210840be98042102f96010840af98c42102bd6310840af98842103ae6210840eb948421033d5210840eb54842102be6110840af58442103ba6010840af58042103b960108409fd97321027e65cc8409f59732102bf64cc840af99332102bd64cc840af19332103
  | 32 => 0xcf54d51902bf6254640af189519033f5254640cf54951903b75154640cf94551902be6314640af58c51902be6214640af588519033f5114640ed944519033d5114640ed54451902be6014640ee98051902ba6014640afd9731902be65cc640af59731902bc65cc640af98b31903ae62cc640ab98b31902bd62cc640eb58b31902ad62cc640af98331902bd60cc640afd9631902be658c640af59631902bc658c640e794e319039d538c640af98a31902bd628c640e7cca319039d328c640e7cc631903b7318c640af98231902bd608c640afd9531902be654c640af59531902bc654c640afd8931902bc624c640edcc5319039e314c640afd8131902bc604c640afd9431902be650c640cf994319023e650c640af594319033d650c6408f59431902bc650c640e794c319039d530c640af98831902bd620c640e7cc8319039d320c640e7cc431903b6310c640e74c431903b5310c640af98031902bd600c640afd9721902be65c8640af59721902bc65c8640afd8f21902be63c8640e798f219029e63c8640af58f219039d63c8640a758f21902bc63c8640af98321902bd60c8640afd9621902be6588640af59621902bc6588640afd8e21902be6388640af58e21902bc6388640eb94a21903ad5288640eb8ca21903ad3288640ebc8621903b72188640af98221902bd6088640afd9521902be6548640af59521902bc6548640afd8d21902be6348640af58d21902bc6348640edc8521903ae2148640afd8121902bc6048640afd9421902be6508640cf994219023e6508640af594219033d65086408f59421902bc6508640afd8c21902be6308640af58c21902bc6308640eb94821903ad5208640eb8c821903ad3208640ebc8421903b62108640eb48421903b52108640af98021902bd60086409f98b535027d62d4d409f987535027d61d4d40d7d4e53502ef6254d40bb18953502f76154d40bd185535035d5314d409f988535027d6214d409f984535027d6114d409f997435035f5390d40d714e43502fa6090d40be582435035f5350d40d714d43502fb6050d40be181435027e6510d409f98f525027d63d49409f987525027d61d4940dbd4a52502df6354940b718d52502f76154940bd185525036d52149409f98c525027d63149409f984525027d61149409f997425036f5290940db14a42502fa6090940be582425036f5250940db14942502fb6050940be181425027e65109409f997325027d65cc9409f197325036f52cc940db14b325027e658c9409f596325027c658c940d7d4e325035c538c9409fd95325027e654c9409f195325027e650c9409f594325027c650c940d7d4c325035c530c940dbd48325036c520c940f34c8325027e63d45409f58f515027e62d45409f58b51503775194540b7d8d51502dc6354540bbd8951502ec62
  | 33 => 0x4e319039f438c640e710e319027f654c6409f595319027c654c640afd9131902be644c640af59131902bc644c6409fd94319027e650c6409f59431902bf640c640af99031902bd640c640af190319035e530c640d754c319039f430c640e710c319027f65c86409f997219027d65c8640afd9321902be64c8640af59321902bc64c8640b798f21902dd63c86409fd96219027e65886409f59621902bf6488640af99221902bd6488640af192219036e5288640db54a21903af4288640eb10a219027f65486409f595219027c6548640afd9121902be6448640af59121902bc64486409fd94219027e65086409f59421902bf6408640af99021902bd6408640af190219036e5208640db54821903af4208640eb10821902bd65d0240cf59740902be63d0240af58f40902be62d0240af58b40902be61d0240af58740902f965d0240de597409037a51d0240af98b53902bd62d4e40af98753902bd61d4e40af98353903ba60d4e40ae983539033f5394e40e7d4e53902be6294e40af58a53902be6194e40af586539039f5354e40cf94d53902bf6254e40af18953902bf6154e40af185539033f5314e40e794c539033d5314e40e754c53902be6214e40eb98853902ae6214e40af58853903ad6214e40ab58853902be6114e40af58453902be6014e40ee98053902ba6014e40af98f52902bd63d4a40af98752902bd61d4a40af98352903ba60d4a40ae98352902be6394a40af58e529033f5294a40ebd4a52902be6194a40af58652902bf6354a40af18d52903af5254a40cf94952902bf6154a40af18552902be6314a40e798c529029e6314a40af58c529039d6314a40a758c529033f5214a40eb948529033d5214a40eb54852902be6114a40af58452902be6014a40ee98052902ba6014a40afd9732902be65cca40af59732902bc65cca40e794f329039d53cca40af98732902bd61cca40af98332902bd60cca40afd9632902be658ca40af59632902bc658ca40eb94a32903ad528ca40e7cca32903af328ca40af98632902bd618ca40af98232902bd608ca40afd9532902be654ca40af59532902bc654ca40e794d329039d534ca40eb94932903ad524ca40ebcc9329039e324ca40afd8532902bc614ca40afd8132902bc604ca40afd9432902be650ca40af59432902bc650ca40e7cc832903ae320ca40e74c832903ad320ca40e34c832902be610ca40af58432902be600ca40af58032902be63d4640e798f519029e63d4640af58f519039d63d4640a758f519033f53d4640cf54f51902be62d4640eb98b51902ae62d4640af58b51903ad62d4640ab58b519033f52d4640cf54b51902be60d4640ee98351902ba60d4640af98e51902bd6394640af98a51902bd6294640cfd4651903b75194640cdd4651902bf6354640af18d519033f535464
  | 34 => 0x902fb6050e40be181439039f6350e40cf94d439039e5350e40e754d43902bf6250e40af18943902bf6150e40af18543902bf6050e40eed8143903b86050e40af594439033d6510e40e798c439033d5310e40af98843902bd6210e40af98443902bd6110e40af580439036f5294a409f98e529027d6394a409f986529027d6194a409fd8d529027c6354a409fd85529027c6154a40b798c52902dd6314a40db54852902bd65d0a40cf59742902be63d0a40af58f429033e52d0a40af98742902bd61d0a40af583429036e5290a40db54a42902fa6090a40be58242902be6390a40af58e42903ae5290a40cf54a42903ad5290a40af98642902bd6190a40ee98242902bd6090a40ee582429036e5250a40db54942902fb6050a40be18142902bf6350a40af18d42903af6250a40cf94942903ae5250a40eb54942902bf6150a40af18542902bf6050a40eed8142903b86050a40af594429033d6510a40af98c42902bd6310a40eb988429033d5210a40af98442902bd6110a40af580429027f65cca409f997329027d65cca40afd9332902be64cca40af59332902bc64cca40d794f329035d53cca409fd96329027e658ca409f59632902bf648ca40af99232902bd648ca40af192329036e528ca40db54a329027f654ca409f595329027c654ca40afd9132902be644ca40af59132902bc644ca40d794d329035d534ca40db949329036d524ca409fd94329027e650ca409f59432902bf640ca40af99032902bd640ca40af19032903cd320ca40b798f51902dd63d4640bb98b51902ed62d4640ddd46519027e63946409f58e519027e62946409f58a519027f63546409f18d519033f4354640cf50d519027f62546409f189519033f4254640cf50951903755114640af597419033d65d0640af98f41902bd63d0640cf54f41902be62d0640af58b419033d52d0640cf94741902bd60d0640dd94641903755190640be98241902f96090640af98e41902bd6390640af98a41902bd6290640ed946419033d5190640ed54641903ba6090640af58241903b96090640b7d8d41902dc6350640bbd8941902ec6250640dd94541903755150640bed8141902f86050640afd8d419039f6350640a7d8d41902bc6350640e718d419029c6350640cf54d41902bf6250640ebd8941902af6250640af18941903ac6250640ab189419033d5250640edd85419033e5150640ed94541903365150640ed54541902bf6050640eed8141903b86050640af594419033d6510640af98c41902bd6310640af98841902bd6210640ed984419033d5110640af580419027f65cc6409f997319027d65cc640afd9331902be64cc640af59331902bc64cc640bb98b31902ed62cc6409fd96319027e658c6409f59631902bf648c640af99231902bd648c640af192319035e538c640d75
  | 35 => 0xc6454021cf951500873d5454021b7d8d50086dc63540219fd91500873f64540218fd91500867c6454021cf191500863c64540219fd8d500875f635402197d8d500867c6354021d718d500865c6354021db8c9500876d3254021af99050086bd6414021cf950500873d5414021b798c50086dd6314021de54050086ee62d4f40bb58b53d02f661d4f40bd58753d035f5394f409f98a53d027d6294f409f98653d027d6194f409fd8953d027c6254f409fd8553d027c6154f40d754c53d035e53d0f40d754f43d02fa60d0f40be58343d035e5310f40d754c43d02fa6010f40be58043d02de63d4b40b758f52d02f661d4b40bd58752d036f5294b409f98e52d027d6394b409f98652d027d6194b409fd8d52d027c6354b409fd8552d027c6154b40db54852d036e52d0b40db54b42d02fa60d0b40be58342d036e5210b40db54842d02fa6010b40be58042d027f65ccb409f99732d027d65ccb40db94b32d036d52ccb409fd9632d027e658cb409f59632d035e538cb40d754e32d027f654cb409f59532d027c654cb40bed8132d02f8604cb409fd9432d027e650cb409f59432d035e530cb40d754c32d036e520cb40db54832d03cd320cb40be98032d02f9600cb40b798f51d02dd63d4740bb98b51d02ed62d4740ddd4651d027e63947409f58e51d027e62947409f58a51d027f63547409f18d51d027f62547409f18951d037b6054740dd54451d037651d0740dd54741d02fa60d0740be58341d02df6350740b718d41d02ef6250740bb18941d02f86050740dd94441d03755110740ed50441d02fa6010740be58041d027f65cc7409f99731d027d65cc740bb98b31d02ed62cc740dd94731d037551cc740be98331d02f960cc7409fd9631d027e658c7409f59631d035e538c740d754e31d027f654c7409f59531d027c654c740bed8131d02f8604c7409fd9431d027e650c7409f59431d02be640c740af59031d035e530c740d754c31d0376510c740dd54431d027f65c87409f99721d027d65c8740b798f21d02dd63c8740dd94721d037551c8740be98321d02f960c87409fd9621d027e65887409f59621d036e5288740db54a21d027f65487409f59521d027c6548740bed8121d02f860487409fd9421d027e65087409f59421d02be6408740af59021d036e5208740db54821d03765108740dd54421d035f5394e409f98a539027d6294e409f986539027d6194e409fd89539027c6254e409fd85539027c6154e40d754c53902ee6214e40bb58853902bd65d0e40cf597439033e53d0e40af98b43902bd62d0e40af98743902bd61d0e40af583439035e5390e40d754e43902fa6090e40be582439039e5390e40cf54e439039d5390e40af98a43902bd6290e40af98643902bd6190e40ee98243902bd6090e40ee582439035e5350e40d754d43
  | 36 => 0x821db594420866d6510821bb99042087ae6410821dbd5042087ae5410821db55042087ad5410821bb58c42087e66110821bb58442087e56110821b958442086ee60108219f597320873e54cc821cf553320875f53cc821d714f320867f658c8219f596320873e548c821cf552320875e538c821d754e32086f6618c821bd586320876d658c8219b59632086ee648c821bb19232087ae548c821eb55232086ed638c821db94e32087ce538c821f354e320876c538c821f998632086ed618c821f958632086e5618c821bb982320867f654c821cf951320873d544c821d7d4d320875c534c821bbd95320876f654c821bb99132086ec644c821eb95132087ad544c821f3d8d32087cf534c821db94d320876c534c821f314d320874c534c821bbd8532086ec604c8219fd94320867d650c821cf950320873d540c821d794c320875d530c821bb98832087cd320c821bd98432086f5610c8219f992510867d64944219f98e510867d6394421dbd0a510876c4294421db8ca510876d32944219f597410873e54d0421cf55341087af42d04219fd96410867d6590421cf952410873d5490421bb98a41086ed62904219fd95410873e5450421cf55141086df6350421b718d41086ef6250421bb18941087af4250421bed8141086f860504219fd94410867e65104219f594410867c6510421cf950410873d5410421bb98841086ed6210421ed504410867d65cc421cf953310873d54cc421bb98b31086ed62cc4219fd96310867d658c421cf952310873d548c421d794e310875d538c421bb98a31086ed628c421f34ca310867f654c421cf951310873d544c4219fd94310867e650c4219f594310867c650c421af99031086bd640c421cf950310873d540c421d794c310875d530c421bb98831086ed620c421f34c831087d5310c421cf953210873d54c8421b798f21086dd63c8421bb99321086ec64c8421eb95321087ad54c8421bbd8f21087ce63c8421bb58f21087cd63c8421b358f21086ee60c8421cf952210873d5488421bb58a210876e5288421ed95221087b55488421bd58a21087765288421f994a21087e74288421f910a21087e63288421f94ca21086f660884219fd95210873e5448421cf55121086ef6548421dbd95210866f6548421bb99121086ec6448421eb95121087ad5448421bbd8d21086ed6348421bbd85210876e5148421f990521087e54148421f9cc521087e43148421bb18121086f76548421ddd9521086776548421ed95121087b55448421bdd8921087e76248421dd94921087e65248421f990921087e54248421f9cc921087e43248421bd18121086be64d4021af593500873e54d4021cf553500873e5494021cf552500877b5094021cfd92500867e64940219f592500873c64940219f98e500867d6394021afd9150086b
  | 37 => 0xaf593504867e64d4121cf993504863e64d41219f593504873d64d41218f593504867e63d41219f58f504877b5094121afd9150486bc6454121b7d8d50486dc6354121de540504867e64141219f590504867e63141219f58c50487772114121db884504867e63d50219f58f540867e62d5021db98b540867e61d5021dd987540867e60d50219f583540867d6595021cfd52540867e63950219f58e540867e60950219f582540863d6595021eb18a54086be6095021cfd8e540873e6395021cf58e540873c6395021cf98a540873c6295021cf986540873c6195021cfd82540873e60950218f982540873d6095021cf182540873f64550219fd8d540867c6355021db189540867f60550219f181540873f6555021eb18954086bc6055021cfd8d540873e6355021cf58d540873c6355021cf989540873c6255021cb189540873e6155021cf185540873c2155021cfd81540873e6055021cf581540873c60550218f18154086be6415021cf550540867e6415021cf990540863e64150219f98c540867d63150219f988540876e62150219f984540877661150219f980540867d6015021af99353086bd64d4c21cf953530873d54d4c219f993530873e64d4c218f993530867d64d4c21cf593530863d64d4c219f98b530876e62d4c219f987530877661d4c219f983530867d60d4c219f596530873e5494c21cf552530875f5394c219f992530867d6494c21db98a530867e6094c219f582530873e5454c21cf551530867f6454c219f191530875f6354c219fd81530867c6054c21af99053086bd6414c21cf950530873d5414c21d754c53086fa6014c21be580530867e6414c21cf990530863e6414c219f590530873d6414c218f590530867e6314c21d798c530867e6214c21db988530867e6114c21dd984530867e6014c21de980530867a6014c219f58053087796014c219e580530867f65d0c219f997430867d65d0c219f197430873e54d0c21cf553430867f6590c219f996430867d6590c219f196430873e5490c21cf55243086ee6290c21bb58a430867f6550c219f995430867d6550c219f195430873e5450c21cf55143086ef6250c21bb18943086f76150c21bd185430867f6510c219f994430867d6510c219f194430873e5410c21cf55043086ee6210c21bb58843086f66110c21bd584430867e64948219f592520867e6394821d798e520865e63948219f58e520875d63948219758e520867d65d0821cf953420873d54d0821bb597420876d65d0821dbd5342087ae54d0821db55342087ad54d0821cb55342086ed63d0821bb58742086ee60d08219fd96420867d6590821cf952420873d5490821bb98a42086f66190821bd586420867f6550821cf951420873d54508219fd94420867d6510821cf950420873d5410821bd98442086f5611
  | 38 => 0xf21886ee60c8621bd597218877565c8621f598f21887d563c8621af99350886bd64d4221b798f50886dd63d4221ded42508867e64942219f592508867e63942219f58e50887772194221afd9150886bc64542219fd91508873f64542218fd91508867c6454221cf191508863c64542219fd8d508867c6354221db8c9508876d3254221de540508867e63d51219f58f544867e60d51219f583544873f54951219f992544867e63951219f58e544867d6295121db58a544867d6195121dd586544867e60951219f58254486df6355121b718d54486fb6055121be181544873f64551219fd8d544875f635512197d8d544867c6355121d718d544865c63551219fd89544876f62551219bd89544867f6155121ddd85544867f6055121ded81544867b60551219f181544877860551219e181544867e6515121cf550544873e64151219f98c544867d63151219f980544867d60151219f993534867d64d4d219f983534867d60d4d21d7d4e534867e6494d219f592534867e6394d219f58a534876d6294d219b58a534867d6194d21dd586534867e6094d219f58253486bf6454d21af19153486fb6054d21be181534867f6454d21cfd91534863f6454d219f191534873c6454d218f191534875f6354d219fd89534876f6254d219fd8553487776154d219fd81534877b6054d219ed81534867c6054d21de18153486786054d219f994534875d5314d219f990534867d6414d21d798c534867e6014d219f580534867f65d0d219f997434867d65d0d219f197434875f53d0d21d714f43486ee62d0d21bb58b43486f661d0d21bd587434867f6590d219f996434867d6590d219f196434873f5490d21cf152434867f6550d219f995434867d6550d219f195434867f6510d219f994434867d6510d219f194434873f5410d21cf150434875f5310d21d714c434867e65d0921cfd53424873c54d0921bd98742486f561d09219f996424867c6550921cfd51424873c5450921bdd8542486f461509219f994424867e65cc921d7d4f324875c53cc921bd98732486f561cc9219f996324867c654c921d7d4d324875c534c921bdd8532486f4614c9219f99432487cd320c9219f997414873f54d0521cf15341486ee62d0521bb58b414867e65905219fd95414867d65505219f195414873f5450521cf15141486df6350521b718d41486ef6250521bb18941486fb6050521be181414867e65105219f997314875f53cc521d714f31486ee62cc521bb58b314867e658c521d794e314875d538c5219fd95314867d654c5219f195314875f534c521d714d31486ef624c521bb189314867e650c521af99031486bd640c521d794c314875d530c521b798f21486dd63c8521f598f21487d563c8521db952214876c5488521dbd4e214876d5388521f9d4621486be64d4121
  | 39 => 0x867e64943219f59250c867e63943219f58e50c86bf6454321af19150c875e5354321d754d50c867f6454321cfd9150c863f64543219f19150c873c64543218f19150c867f63543219f18d50c86de6314321b758c50c875e5314321d754c50c877950143219f98f548867d63d5221db58b548877661d52219f983548867d60d5221cfd52548867e63952219f58e548867e60952219f582548873f64552219fd8d548867c6355221dbd89548867f60552219f181548873d5415221b798c54886dd6315221cf990548867e6315221d798c548865e63152219f58c548875d63152219758c548876d6215221dd984548867e60152219f580548867e64d4e219f593538876d62d4e21dd987538867e60d4e219f583538875f5394e219f992538867d6494e21db58a538867e6094e219f582538867f6454e219f191538875f6354e219fd81538867c6054e21af99053886bd6414e21d754c538867e6414e21cf990538863e6414e219f590538873d6414e218f590538875e6314e21db58853887766114e219f980538867d6014e219fd97438867e65d0e219f597438867c65d0e21cf953438873d54d0e21bd98743886f561d0e219fd96438867e6590e219f596438867c6590e21d794e438875d5390e21bb98a43886ed6290e219fd95438867e6550e219f595438867c6550e21cf951438873d5450e21d794d438875d5350e21bbd8943886ec6250e219fd94438867e6510e219f594438867c6510e21bb98843886ed6210e21cf953428873d54d0a21bd98742886f561d0a21db597428876f54d0a21eb953428876d54d0a21eb55342886ed63d0a21f998742886ed61d0a21f958742886ee60d0a21cf951428873d5450a21bdd8542886f46150a21bb594428876d6510a21eb990428876f5410a21db55042886ed6310a21bb58442886ee6010a21d794f328875d53cca21bd98732886f561cca21bb596328876d658ca21bb99232886ec648ca21db94e328876c538ca21bb58632886ee608ca21d794d328875d534ca21bdd8532886f4614ca21dbd9532886ee644ca21bb19132887cf634ca21db94d32887ce534ca21d394d32887cd534ca21db14d32886ef614ca21f9d8532887e4614ca21bb18132887cd320ca21cfd53418873c54d0621ebd0b418873e5490621cf55241886ee6290621bb58a418873f5450621cf15141886df6350621b718d41886ef6250621bb18941887af4250621bed8141886f86050621cf950418873d5410621bb98841886ed6210621bb98b31886ed62cc621d794e318875d538c621bb98a31886ed628c621f34ca31886be640c621af590318875e530c621d754c31886ee620c621bb58831887cd320c621b798f21886dd63c8621bb597218876d65c8621bb99321886ec64c8621bbd8f21887ce63c8621bb58f21887cd63c8621b358
  | 40 => 0x3254031d74c9500c6be6414031af590500c73e5414031cf550500c6ee6214031bb588500c7795014031b798f54c86dd63d5321be98354c86f960d53219f98f54c875e63d53219798f54c867d63d5321d758f54c865d63d5321db98b54c877561d53219f98354c877a60d53219e98354c867d60d5321de58354c867960d5321cfd5254c867e63953219f58e54c867e60953219f58254c873f64553219fd8d54c867c63553219fd8154c867c6055321cf55054c86de6315321b758c54c873e64153219f98c54c875e63153219798c54c867d6315321d758c54c865d6315321db98854c877561153219f98054c867d60153219f99353c867d64d4f21db98b53c877561d4f219f98353c867d60d4f21d7d4e53c867e6494f219f59253c867e6094f219f58253c875f5494f21d795253c875d5494f21d715253c875f6494f21d799253c875d6494f21d719253c875e6294f21d718a53c875f6194f21d758653c875f6094f21d798253c875d6094f21d718253c867f6454f219f19153c875f6354f219fd8153c867c6054f21d7d9553c875f5454f21d795153c875d5454f21d715153c875f6454f21d799153c875d6454f21d719153c875e6254f21d718953c875f6154f21d758553c875f6054f21d798153c875d6054f21d718153c875d5314f219f99053c867d6414f21d798c53c876e6214f21dd58453c867e6014f219f58053c867f65d0f219f99743c867d65d0f219f19743c875e53d0f21d754f43c86ee62d0f21bb58b43c867f6590f219f99643c867d6590f219f19643c875e5390f21d754e43c867f6550f219f99543c867d6550f219f19543c875e5350f21d754d43c86f76150f21bd18543c867f6510f219f99443c867d6510f219f19443c875e5310f21d754c43c86f66110f21bd58443c873f54d0b21cf15342c875e53d0b21d754f42c873e5490b21cf55242c875e5390b21d754e42c86f66190b21bd58642c873f5450b21cf15142c875e5350b21d754d42c873e5410b21cf55042c875e5310b21d754c42c86f66110b21bd58442c875e53ccb21d754f32c875e538cb21d754e32c86f6618cb21bd58632c875e534cb21d754d32c875e530cb21d754c32c87cd320cb21bd98432c86f5610cb21cf95341c873d54d0721d794f41c875d53d0721bb98b41c86ed62d0721d794e41c875d5390721cf95141c873d5450721b7d8d41c86dc6350721d794d41c875d5350721bbd8941c86ec6250721bed8141c86f86050721d794c41c875d5310721ed50441c875e53cc721d754f31c86ee62cc721bb58b31c875e538c721d754e31c875e534c721d754d31c86ef624c721bb18931c86be640c721af59031c875e530c721d754c31c87d5310c721af99350c86bd64d4321b798f50c86dd63d4321d794f50c875d53d4321d794e50c875d5394321ded4250c
  | 41 => 0x8319f992520c67d64948319f982520c67d6094831cf951520c73d54548319fd91520c67c64548319fd81520c67c6054831af990520c6bd6414831cf950520c73d5414831db548520c6fa6014831be580520c67f65d08319f997420c67d65d0831cf953420c73d54d08319fd96420c67e65908319f596420c73e5490831cf552420c6de6390831b758e420c67f65508319f595420c67c6550831cf951420c73d5450831b7d8d420c6dc6350831bdd85420c6f461508319fd94420c67e65108319f594420c73e5410831cf550420c6de6310831b758c420c6f66110831bd584420c73e54cc831cf553320c76e52cc831db54b320c6f661cc831bd587320c6de64cc831b7193320c79e54cc831e7553320c75e52cc831f394b320c7cd52cc831f5987320c6dd61cc831f5587320c6d561cc831b7983320c67d658c831cf952320c73d548c831b758e320c67f654c831cf951320c73d544c831b7d95320c75f654c831b7991320c6dc644c831e7951320c79d544c831f3d89320c7cf524c831d7949320c7cc524c831b7d85320c6dc604c831cf950320c73d540c831b798c320c76e520c831db548320c7cd320c831bd984320c6f5610c8319f992510c67d6494431d7d0e510c75c4394431d7cca510c75d32944319f597410c73e54d0431cf553410c79f43d04319fd96410c67d6590431cf952410c73d5490431b798e410c6dd63904319fd95410c73e5450431cf551410c6df6350431b718d410c79f4350431bbd89410c6ec6250431bed81410c6f860504319fd94410c67e65104319f594410c67c6510431cf950410c73d5410431b798c410c6dd6310431ed504410c73e54cc431cf553310c6ee62cc431bb58b310c6de64cc431b7193310c79e54cc431e7553310c7ce62cc431b758b310c7cd62cc431b358b310c6de60cc431cf952310c73d548c431b758e310c75e538c431ed952310c7b5548c431bd58e310c776538c431f594e310c7d7438c431f510e310c7d7328c431f54ca310c6f6608c4319fd95310c73e544c431cf551310c6df654c431d7d95310c65f654c431b7991310c6dc644c431e7951310c79d544c431b7d89310c6df614c431d7945310c7d6414c431f5505310c6dc604c431bdd95310c777654c4319dd95310c7b6544c431ed551310c6f7634c431f5d8d310c776534c431f594d310c7d6434c431f550d310c7d6324c431f50c9310c6f4604c431af993500c6bd64d4031cf953500c73d54d4031cf952500c73d5494031ded42500c73f64940319f992500c67d6494031cf192500c67e62940319f58a500c6bf6454031af191500c73e5454031cf551500c6ef6254031bb189500c67f6454031cfd91500c63f64540319f191500c73c64540318f191500c67f6254031dbd89500c66f62540319f189500c76c62540319b189500c75f
  | 42 => 0xf983524c67d60d4931dbd4a524c6bf6454931af191524c6fb6054931be181524c76d52149319f990524c67d64149319f980524c67d60149319f997424c67d65d09319f197424c6de63d0931b758f424c76f52d0931db14b424c6f661d0931bd587424c67e65909319f596424c67c6590931cfd52424c73c54909319fd95424c67e65509319f195424c67e65109319f594424c67c6510931cfd50424c73c5410931dbd48424c76c52109319f997324c76f528c931db14a324c6f6618c931bd586324c76f524c931db149324c6f7614c931bd185324c67e650c931f34c8324c67e65d0531cfd53414c73c54d0531b798f414c6dd63d05319f996414c67f65505319f595414c67c6550531cfd51414c73c5450531b7d8d414c6dc6350531bbd89414c6ec6250531bed81414c6f860505319f994414c6ee62cc531bb58b314c7e662cc531f958b314c75e548c531d7152314c75f528c531f5d46314c6be64d4131af593504c67e64d4131cf993504c63e64d41319f593504c73d64d41318f593504c67e62d41319f58b504c77b5094131afd91504c6bc6454131bbd89504c6ec6254131de540504c67e64141319f590504c67e62141319f588504c7773114131d78c4504c67e63d5031d798f540c67e62d50319f58b540c67e61d5031dd987540c67e60d50319f583540c67d6595031cfd52540c67e62950319f58a540c67e60950319f582540c63d6595031e718e540c6be6095031cf98e540c73c6395031cfd8a540c73e6295031cf58a540c73c6295031cf986540c73c6195031cfd82540c73e60950318f982540c73d6095031cf182540c73f6455031d718d540c67f62550319f189540c67f60550319f181540c73f6555031e718d540c6bc6055031cf98d540c73c6355031c718d540c73f6255031cf989540c73d6255031cf189540c73e6155031cf185540c73c3155031cfd81540c73e6055031cf581540c73c60550318f181540c6be6415031cf550540c67e6415031cf990540c63e64150319f98c540c75e63150319f988540c67d62150319f984540c77661150319f980540c67d60150319f992530c67d6494c31db98a530c76d6294c319f597430c73e54d0c31cf553430c6dd65d0c31d7597430c75f54d0c31e7953430c75d54d0c31e7553430c71d54d0c31b758b430c6dd61d0c31b7983430c67f6590c319f596430c73e5490c31cf552430c6de6390c31bd986430c6f56190c319fd95430c73e5450c31cf551430c67f6510c319f594430c73e5410c31cf550430c6f66110c31bd584430c75d6510c3197594430c6de6410c31e7990430c75f5410c31e7950430c75d5410c31e7550430c6dd6210c31f5984430c6dd6110c31f5584430c6d56110c31b7980430c6be64d4831af593520c73e54d4831cf553520c73e5494831cf552520c76f5294
  | 43 => 0x548c66e62152319f588548c76d62152319b588548c77661152319f980548c67d6015231cf953438c73d54d0e31bd987438c6f561d0e31d7597438c75f54d0e31e7953438c75d54d0e31e7553438c6dd62d0e31f5987438c6dd61d0e31f5587438c6de60d0e31cf951438c73d5450e31bdd85438c6f46150e31b7594438c75d6510e31e7990438c75f5410e31d7550438c6dd6210e31b7584438c6de6010e31dbd4a528c67e6494a319f592528c67e6094a319f582528c67f6454a319f191528c67f6054a319f181528c6be6414a31af590528c76d5214a319fd97428c67e65d0a319f597428c73e54d0a31cf553428c6f661d0a31bd587428c67f6590a319f996428c67d6590a31b798e428c6dd6390a31db94a428c76d5290a319fd95428c67d6550a319f195428c73e5450a31cf551428c6df6350a31b718d428c76e5250a31db549428c67f6510a319f994428c67d6510a31b798c428c6dd6310a31b7597328c75d65cca31b7993328c6dc64cca31d794b328c6dd61cca31b7983328c76e528ca31db54a328c6f6618ca31bd586328c76e524ca31db549328c6f7614ca31bd185328c6de644ca31b7191328c7cf624ca31d7949328c7ce524ca31d3949328c7cd524ca31b7d85328c7d7614ca31f5185328c6dc604ca31f34c8328c73f54d0631cf153418c79f43d0631cf952418c73d5490631b798e418c6dd6390631cfd51418c73c5450631b7d8d418c6dc6350631e7d0d418c6ef6250631bb189418c6fb6050631be181418c73e5410631cf550418c6de6310631b758c418c6ee62cc631bb58b318c6dd65cc631d7597318c6de64cc631b7193318c7ce62cc631b758b318c7cd62cc631b358b318c6de60cc631bd597318c77565cc631f998b318c7e562cc631af993508c6bd64d4231bb98b508c6ed62d4231ded42508c67e64942319f592508c67e62942319f58a508c7773194231afd91508c6bc64542319fd91508c73f64542318fd91508c67c6454231cf191508c63c64542319fd89508c67c6254231d7cc9508c75d3254231de540508c67e62d51319f58b544c67e60d51319f583544c73f54951319f992544c67d6395131d758e544c67e62951319f58a544c67d6195131dd586544c67e60951319f582544c6ef6255131bb189544c6fb6055131be181544c73f64551319fd8d544c75f635513197d8d544c67f6255131dbd89544c66f62551319f189544c76c62551319b189544c67f6155131ddd85544c67f6055131ded81544c67b60551319f181544c77860551319e181544c67e6515131cf550544c73e64151319f988544c67d62151319f980544c67d60151319f997434c73f54d0d31cf153434c6f661d0d31bd587434c67e6590d319f195434c73f5450d31cf151434c6f76150d31bd185434c67e6510d319f993524c67d64d49319
  | 44 => 0x7795014041bb98b54cc6ed62d5331be98354cc6f960d5331d798f54cc67e62d5331db98b54cc66e62d53319f58b54cc76d62d53319b58b54cc77561d53319f98354cc77a60d53319e98354cc67d60d5331de58354cc67960d5331cfd5254cc67e62953319f58a54cc67e60953319f58254cc73f64553319fd8954cc67c62553319fd8154cc67c6055331cf55054cc6ee6215331bb58854cc73e6415331d798c54cc67e6215331db98854cc66e62153319f58854cc76d62153319b58854cc77561153319f98054cc67d6015331cfd5343cc73c54d0f31cf95243cc73d5490f31bd98643cc6f56190f31cfd5143cc73c5450f31cf95043cc73d5410f31bd98443cc6f56110f31dbd4a52cc67e6494b319f59252cc67e6094b319f58252cc76f5494b31db95252cc76d5494b31db15252cc76f6494b31db99252cc76d6494b31db19252cc76c6394b31dbd0e52cc76e4394b31db50e52cc76c4394b31dbd8652cc76d6194b31dbd8252cc76e6094b31db58252cc76c6094b319fd9152cc67c6454b319fd8152cc67c6054b31dbd9552cc76f5454b31db95152cc76d5454b31db15152cc76f6454b31db99152cc76d6454b31db19152cc76e6354b31dbd0d52cc76e4354b31db50d52cc76c4354b31dbd8552cc76d6154b31dbd8152cc76e6054b31db58152cc76c6054b31db54852cc67f65d0b319f99742cc67d65d0b31b798f42cc6dd63d0b31db94b42cc76d52d0b319fd9642cc67e6590b319f59642cc76e5290b31db54a42cc67f6550b319f59542cc67c6550b31db94942cc76d5250b31bdd8542cc6f46150b319fd9442cc67e6510b319f59442cc76e5210b31db54842cc6f66110b31bd58442cc76e52ccb31db54b32cc6f661ccb31bd58732cc76d528cb31db94932cc76e520cb31db54832cc7cd320cb31bd98432cc6f5610cb31cf95341cc73d54d0731b798f41cc6dd63d0731db94b41cc76d52d0731db94a41cc76d5290731cf95141cc73d5450731b7d8d41cc6dc6350731bbd8941cc6ec6250731db94941cc76d5250731bed8141cc6f86050731db94841cc76d5210731ed50441cc6be64d4331af59350cc6ee62d4331bb58b50cc76e52d4331db54b50cc76e5294331db54a50cc77b50943319f99250cc67d64943319f98a50cc67d6294331afd9150cc6bc6454331db94950cc76d52543319fd9150cc73f64543318fd9150cc67c6454331cf19150cc63c64543319fd8950cc67c6254331bb98850cc6ed6214331db94850cc76d5214331de54050cc75d63d52319f98b548c67d62d5231dd987548c67e60d52319f583548c73f54952319f98a548c67d62952319f982548c67d6095231cfd91548c75f63552319fd89548c67c62552319fd81548c67c6055231cf550548c6ee6215231bb588548c73e6415231d758c548c67e6215231db988
  | 45 => 0x94141b7d8d50506dc6354141d7d4d505075c5354141bbd8950506ec6254141dbd49505076c5254141d7d4c505075c5314141dbd48505076c5214141de540505073f64141419f98c505067d6314141cfd0c505073d43141419f988505067d6214141cfd08505073d4214141cf90450506fa6514141de99450507bb6414141ded4c50507db5314141d6d4c505077a5314141de54c50507785314141f614c50507585314141eed0c50507b94314141ded4850507eb5214141dad48505077a5214141de54850507785214141fa14850507685214141eed0850507b94214141fcd0450507ba4114141ded90505073b6414141ded8c505077a6314141de58c50507786314141ded0c505073b4314141de90c50507794314141ce50c50507784314141ded88505077a6214141de58850507786214141ded08505073b4214141de90850507794214141ce50850507784214141decc8505077a3214141de4c850507783214141ded84505077b4114141de904505073a4114141de50450506ee62d4c41bb58b531075f5394c419f98a531067d6294c419f982531067d6094c419fd89531067c6254c419fd81531067c6054c41d754c531073e54d0c41d794f431075d53d0c41bd98743106f561d0c419f596431067f6550c41cf951431075e5310c41d754c43106f66110c41bd58443106de63d4841b758f521076f52948419f98e521067d63948419f982521067d60948419fd8d521067c63548419fd81521067c6054841db548521073e54d0841db94b421076d52d0841bd98742106f561d08419f596421067f6550841cf951421076e5210841db54842106f66110841bd584421067f65cc8419f997321067d65cc841db94b321076d52cc8419fd96321067e658c8419f596321075e538c841d754e321067f654c8419f595321067c654c841afd9132106bc644c841bdd8532106f4614c8419fd94321067e650c8419f594321075e530c841d754c321076e520c841db54832107cd320c841cf54f411073d52d0441af98341106bd6490441cf95241106f56490441dd95241107b654904419fd9541106df6350441b718d41106ef6250441bb18941106fb6050441be18141106bf6550441cfd95411063f6550441e7d8d411079c6350441cf54d41107af6250441eb189411073d5250441afd85411073e5150441eed8141106bc6050441ee18141106b86050441bdd95411077765504419dd9541106f76450441edd9141107765450441ed95141107d76350441f518d41107b64350441ed10d41107e76250441f918941107b64250441ed10941107f36050441fc181411077b5094041cf192501067e63940419f58e501067e62940419f58a501073f4194041cf506501067f63540419f18d501067f62540419f18950106de6314041b758c50106ee6214041bb5885010
  | 46 => 0x41b7d8d52506dc6354941d7d4d525075c5354941bed8152506f86054941d7d4c525075c5314941db548525067e63149419f58c525067e60149419f58052506ee6514941db99452507ad6414941dbd4c52507cf5314941d3d4c525076e5314941db54c525076c5314941f314c525074c5314941ebd0c52507ad4314941dbd90525076f6314941db98c525076d6314941db18c525076f4314941db90c525076d4314941db10c525076f6114941db584525076d4114941dbd80525076e6014941db580525076c60149419f997425075f53d0941d714f425076c52d0941af997425073e65d0941af58f425079f53d0941e714f42507af52d0941cf14b42507ac52d0941cb14b42506be61d0941af98342506bd6490941d7d4e425075c5390941dbd4a425076c5290941bd98642506f56190941d7d4d425075c5350941dbd49425076c5250941bdd8542506f46150941afd8d425079f5350941e714d42507af6250941ebd49425073c5250941eb14942507b76150941af18542507b46150941ad18542506bc60509419f99442506be6410941d7d4c425075c5310941dbd48425067e65cc9419f597325067c65cc941af99332506bd64cc941d7d4f325075c53cc941dbd4b325076c52cc941bd98732506f561cc9419f996325067d658c9419f19632506be648c941af592325075f538c941d714e325076f528c941db14a32506f6618c941bd586325067f654c9419f995325067c654c941af99132506bd644c941d7d4d325075c534c941dbd49325076c524c9419f994325067d650c9419f19432506be640c941af590325075f530c941d714c325076f520c941db14832507cd320c941d7d4f415075c53d0541dbd4b415076c52d0541f5d4f41507d453d0541edd0f41507b543d0541f9d4b41507e452d0541edd0b41507b542d0541d7d4e415075c5390541dbd4a415076c5290541af58e415079f5390541e714e41506bd6290541ebd4a41507ac5290541edd4641506be6090541d7d4f505075c53d4141dbd4b505076c52d41419f98f505067d63d41419f98b505067d62d4141ee593505077b53d4141f6d4f505075b53d4141de94f505077953d4141de14f50507d853d4141d614f50507bb43d4141ee50f505077b52d4141fad4b505076b52d4141de94b505077952d4141de14b50507e852d4141da14b50507bb42d4141ee50b50507f341d4141ee907505077b64d4141ded8f505077a63d4141de58f505077863d4141ded0f505077a43d4141de50f505077843d4141ded8b505077a62d4141de58b505077862d4141ded0b505077a42d4141de50b505077842d4141deccb505077a32d4141de4cb505077832d4141ded87505077b41d4141de90750506de6394141b758e505075f5394141d714e50506ee6294141bb58a505076f5294141db14a505077b5
  | 47 => 0xd9432d067e650cb419f59432d06be640cb41af59032d07cd320cb41b798f50d06dd63d4341bb98b50d06ed62d4341ded4250d073c64943419f98e50d067d6394341cfd0e50d073d43943419f98a50d067d6294341cfd0a50d073d42943419fd8d50d067c63543419fd8950d067c6254341de54050d075f5394e419f98a539067d6294e419f982539067d6094e419fd89539067c6254e419fd81539067c6054e41d754c539075e5390e41d754e43906f66190e41bd586439075e5350e41d754d43906f76150e41bd185439076f5294a419f98e529067d6394a419f982529067d6094a419fd8d529067c6354a419fd81529067c6054a41db548529076e5290a41db54a42906f66190a41bd586429076e5250a41db54942906f76150a41bd185429067f65cca419f997329067d65cca41bd98732906f561cca419fd96329067e658ca419f59632906f6618ca41bd586329067f654ca419f595329067c654ca41afd9132906bc644ca419fd94329067e650ca419f59432907cd320ca41af597419073d65d0641cf54f419073d52d0641af98341906f565d0641dd597419077b5094241cfd92509067e63942419f58e509067e62942419f58a509073f41942419fd8d509067c63542419fd89509067c6254241de540509067e62d4d419f58b535067e60d4d419f583535079f64d4d41d7d93535075f62d4d41d798b535075d62d4d41d718b535075f61d4d41d7587535075f60d4d41d7983535075d60d4d41d7183535075f5394d41bb98a53506ed6294d41be98253506f96094d41bbd8953506ec6254d41bed8153506f86054d41d754c535067e6214d419f588535067e6014d419f58053506de6514d41d7994535079d6414d41d7d90535075f6214d41d7988535075d6214d41d7188535075f6114d41d7584535075d4114d41d7d80535075e6014d41d7580535075c6014d419f997435075c53d0d41af997435073e65d0d41e7d4f435073c53d0d41e714f435071c53d0d41af58b43506be61d0d41af98343506bd6490d41d7d4e435075c5390d41bd98643506f56190d41d7d4d435075c5350d41bdd8543506f46150d41e7d8d435079f5350d41cf14d435079c5350d41afd8943507b76150d41af18543507b46150d41ad18543506bc6050d419f99443506be6410d41d7d4c435075f53d4941d714f525067e63d49419f58f525067e60d49419f58352507af64d4941dbd4f52507cf53d4941d3d4f525076e53d4941db54f525076c53d4941f314f525074c53d4941ebd0f52507ad43d4941dbd93525076f63d4941db98f525076d63d4941db18f525076f43d4941db90f525076d43d4941db10f525076f61d4941db587525076f60d4941db983525076d60d4941db18352506de6394941b758e525075f5394941d714e525076f5294941be98252506f960949
  | 48 => 0x20cb3d5490832b798e420cadd63908329fd95420ca7f65108329f994420ca7d65108329f194420cb3e5410832cf550420cade6310832b758c420cbad4210832b7983320cadd638c832d794e320caed638c832b358e320cb6e538c832f394e320caee608c8329fd95320cadf654c832d7d95320ca5f654c832b7d89320cb5e524c832f3d09320cbce424c832f3509320cbcc424c832b7181320caef654c832dbd95320ca6f654c832bbd8d320cbcf634c832db94d320cbce534c832f3d0d320cbce434c832f350d320cbcc434c832bb181320cbcf654c832b3d95320cb4f654c832f3d91320cbce644c832f3591320cbcc644c832f3d51320cbce544c832f3551320cbcc544c832f3d85320cbce614c832f3585320cbcc614c832f3d81320cbce604c832f3581320cbcc604c832b3181320cbcd32d4432f34ca510cb7751944329f992510ca7d6494432d7cca510cb6e3294432d74ca510cb6d3294432d34ca510ca7e60944329f582510cbcd32544329fd91510ca7c64544329fd81510ca7c6054432af990510cabd6414432f34c8510cb755114432be980510caf96014432af993500cabd64d4032f34cb500cbcd3294032ded42500ca7e64940329f592500ca7e61940329f586500cabf6454032af191500cbcd3254032bdd85500caf461540329fd91500cb3f64540328fd91500ca7c6454032cf191500ca3c6454032d7cc9500cb6e3254032d74c9500cb6d3254032d34c9500ca7f6154032ddd85500ca7761540329f185500cb7461540329d185500cbcd3214032de540500cb5f5394f419f98a53d067d6294f419f98253d067d6094f419fd8953d067c6254f419fd8153d067c6054f41d754c53d06ee6214f41bb58853d075e53d0f41d754f43d06f661d0f41bd58743d073e53d0f41e794f43d079d53d0f41af58b43d06be61d0f41ed98743d07b561d0f41af98343d06bf6550f41cfd9543d079f6350f41cf94d43d06bf6250f41af18543d06bc6050f41d794c43d075d5310f41bd98443d06f56110f41dbd4a52d067e6394b419f58e52d067e6094b419f58252d067f6354b419f18d52d067f6054b419f18152d06de6314b41b758c52d076d5214b41db94b42d076d52d0b41bd98742d06f561d0b41af58f42d073e52d0b41eb94b42d07ad52d0b41af98742d07b661d0b41ed58742d06be60d0b41afd9542d073f6550b41afd8d42d07af6250b41cf94942d06bc6150b41af18142d076e5210b41db54842d06f66110b41bd58442d067f65ccb419f99732d067d65ccb41af99332d06bd64ccb41d794f32d075d53ccb419fd9632d067e658cb419f59632d06be648cb41af59232d076e528cb41db54a32d067f654cb419f59532d067c654cb41af99132d06bd644cb41d794d32d075d534cb41db94932d076d524cb41bdd8532d06f4614cb419f
  | 49 => 0xdd65cca32d7597328cade60cca32bb597328cb6d65cca32bb987328caed60cca32ddd46518ca7e64946329f592518cb5f32946329f982518ca7d60946329fd91518ca7c64546329fd81518ca7c6054632af990518cabd6414632dd544518cabe64d4232af593508caf661d4232bd587508cb7b50942329f992508ca7d6494232dbcca508ca7e61942329f586508cabf6454232af191508ca7f6454232cfd91508ca3f64542329f191508cb3c64542328f191508cb5f32542329fd85508ca7c6154232de540508ca7e61d51329f587544ca7e60d51329f583544cb3f54951329f992544ca7d6395132d758e544ca7d6295132db58a544ca7e61951329f586544ca7e60951329f582544caf76155132bd185544cafb6055132be181544cb3f64551329fd8d544cb5f63551329fd89544cb6f62551329fd85544cb7761551329dd85544ca7c6155132dd185544ca7461551329fd81544cb7b60551329ed81544ca7c6055132de181544ca7860551329f994544cb3d5415132cf990544ca7e61151329f584544ca7e60151329f580544ca7e65d0d32cfd53434cb3c54d0d32bb98b434caed62d0d329f996434ca7c6550d32cfd51434cb3c5450d32bbd89434caec6250d329f994434ca7e65d0932cfd53424cb3c54d0932b798f424cadd63d09329f996424ca7f65509329f595424ca7c6550932cfd51424cb3c5450932b7d8d424cadc63509329f994424caee61cc932bb583324cbcf528c932b7986324cadd608c9329f993514ca7d64d45329f983514ca7d60d4532ddd46514cabf6454532af191514cafb6054532be181514cabe6414532af590514cb7551145329f990514cb3e64145328f990514ca7d6414532cf590514ca3d64145329f980514ca7d6014532af993504cabd64d41329f993504cb3e64d41328f993504ca7d64d4132cf593504ca3d64d41329f987504ca7d61d4132ded42504cabf6454132af191504caf76154132bd185504cb7950141329f990504ca7d6414132dbcc8504cb5e32141329f984504ca7d6114132be983540caf960d50329f98f540cb5e63d50329f98b540cb6e62d50329f987540ca7d61d50329f983540cb7a60d50329e983540ca7d60d5032de583540ca7960d50329f596540cb3f54950329f986540ca7d61950329f982540ca7d6095032cfd91540ca7f61550329f185540ca7f60550329f181540cb3d54150329f990540cb3e64150329f98c540cb5e63150329f988540cb6e62150329f984540ca7d61150329f980540ca7d60150329f992530ca7d6494c329f597430ca7f6590c329f596430cb3e5490c32cf552430caee6290c32bb58a430ca7f6550c329fd94430ca7d6510c32cf950430cb3d5410c32e750c430caee6210c32bb588430ca7e64948329f592520ca7d65d08329fd96420ca7d6590832cf9524
  | 50 => 0x94142b7d8d5050adc6354142bdd855050af46154142de5405050b3f64141429f98c5050a7d6314142cf9085050a7e61141429f5845050af661d4c42bd5875310b5f5394c429f9865310a7d6194c429f9825310a7d6094c429fd855310a7c6154c429fd815310a7c6054c42d754c5310b5e53d0c42d754f4310aee62d0c42bb58b4310a7d6590c429fd954310b5e5310c42d754c4310b9d4310c42bb9884310aed6210c42af9834210abd6490842cf9524210aed6490842db9524210bae5490842bb9864210a7f6550842afd954210b3f65508428fd954210abf6250842cf9494210abc6050842bbd954210b6f65508429bd954210aef6450842ebd914210b6e5450842eb9514210bae4350842eb10d4210aec6150842b798f5110add63d4442ddd465110a7e63944429f58e5110a7e60944429f5825110a7f63544429f18d5110b3f4254442cf5095110a7f60544429f1815110b755114442ded425010b3c64940429f98e5010a7d6394042cfd0a5010b3d42940429f9865010a7d61940429fd8d5010a7c63540429fd855010a7c6154042b798c5010add6314042bd9845010af56114042de5405010b5e63d5332db58b54cca7e61d53329f58754cca7e60d53329f58354ccb3f54953329f98654cca7d61953329f98254cca7d6095332cfd9154cca7f61553329f18554cca7f60553329f18154ccb3d5415332bd98454ccaf56115332cf99054ccb5e6315332db58854cca7e6115332dd98454cca7661153329f58454ccb7561153329d58454cca7e60153329f58054ccb3e5490f32cf55243ccaee6290f32bb58a43ccb3e5410f32cf55043ccaee6210f32bb58843ccb3e54d0b32cf55342ccade63d0b32b758f42ccb3e5450b32cf55142ccadf6350b32b718d42ccbad4210b32ddd4651cca7e64947329f59251cca7e60947329f58251cca7f64547329f19151cca7f60547329f18151ccabe6414732af59051ccb755114732af99350ccabd64d4332bd98750ccaf561d4332ded4250cca7e64943329f59250cca7e61943329f58650ccabf6454332af19150cca7f6454332cfd9150cca3f64543329f19150ccb3c64543328f19150cca7f61543329f18550ccb795014332d758f548cb6e62d52329f987548ca7d61d52329f983548ca7d60d5232cfd52548ca7e61952329f586548ca7e60952329f582548cb3f64552329fd85548ca7c61552329fd81548ca7c6055232cf550548caf66115232bd584548cb3e6415232d758c548cb6e62152329f984548cb7661152329d984548ca7d6115232dd584548ca7561152329f980548ca7d6015232cf953438cb3d54d0e32bb98b438caed62d0e32cf951438cb3d5450e32bbd89438caec6250e32e750c438cb3e5490a32cf552428cade6390a32b758e428cb3e5410a32cf550428cade6310a32b758c428ca
  | 51 => 0x3e79524310ede6190c439fd954310ebf6550c43cfd954310e3f6550c43afd8d4310f3e5350c43af1814310edf6550c43d7d954310e5f6550c43b7d914310f9f6450c43d79514310f9e5450c43b71854310ef661d4843bd5875210f6f52948439f9865210e7d61948439f9825210e7d60948439fd855210e7c61548439fd815210e7c6054843db5485210eee62d4443bb58b5110f7751944439f98a5110e7d62944439f9825110e7d6094443cfd0d5110f3d43544439fd895110e7c62544439fd815110e7c6054443dd5445110f7b5094043cf1925010f3f4394043cf50e5010e7e62940439f58a5010e7e61940439f5865010e7f62540439f1895010e7f61540439f1855010eee6214043bb5885010ef66114043bd5845010f795014043d7d4e53d0a7e6194f429f58653d0a7e6094f429f58253d0a7f6154f429f18553d0a7f6054f429f18153d0b5d5314f42bd98453d0af56114f42d794f43d0b5d53d0f42bb98b43d0aed62d0f42d794c43d0b5d5310f42bb98843d0aed6210f42ddd4651d0a7e63947429f58e51d0a7e60947429f58251d0adf6354742b718d51d0a7f6354742d7d8d51d0a5f63547429f18d51d0b5c63547429718d51d0a7f60547429f18151d0ade6314742b758c51d0b755114742b798f50d0add63d4342bd98750d0af561d4342ded4250d0b3c64943429f98e50d0a7d63943429f98650d0a7d61943429fd8d50d0a7c63543429fd8550d0a7c6154342de54050d0b5f5394e429f9865390a7d6194e429f9825390a7d6094e429fd855390a7c6154e429fd815390a7c6054e42d754c5390afa6014e42be5805390b5e5390e42d754e4390aee6290e42bb58a4390b5e5350e42d754d4390aef6250e42bb1894390b9d4310e42af5974290b3d65d0a42af9834290aed65d0a42db5974290ade63d4642b758f5190afa60d4642be5835190b7751946429f98e5190a7d6394642dbd0a5190a7e60946429f5825190a7f63546429f18d5190b3f42546429fd815190a7c6054642dd5445190b7b5094242cfd925090a7e63942429f58e5090b3f42942429f9865090a7d61942429fd8d5090a7c63542429fd855090a7c6154242b798c5090add6314242de5405090a7e61d4d429f5875350a7e60d4d429f5835350b5f5394d42bdd855350af46154d42bed815350af86054d42d754c5350a7e6114d429f5845350a7e6014d429f5805350a7e65d0d42d7d4e4350b5c5390d42bb98a4350aed6290d42d7d4d4350b5c5350d42bbd894350aec6250d429f9944350baf5290942af5864250abe60909429f98f5150a7d63d45429f9835150a7d60d4542ddd465150adf6354542b718d5150afb6054542be1815150b7551145429f98c5150a7d6314542dbd085150a7e60145429f5805150a7e63d41429f58f5050a7e61d41429f5875050b7b50
  | 52 => 0x10000001800280010002001400000150008000000480010016000000100010012001c0070007000a000400d8005000000080010001000000000038008000c002400300050000000000100060000000c000000100020000000000800200010000800600020000001000000000018002800b000000480010008000e000c0028001000000080098000000000000040002001c00100038001000000080000003000a00000008003000a00100008001000a000c002801a0000000000180000018004000480010004000800080000002000000000000006000400d8003000000040090001000000080018008000000040100004000000000020000000a00240008007000400280000000000a00480110000000000200008003000c00080058003001000080008000000e000000280160002000c003000d000400000000000001400480090001000200400028001000c00036f5294b439f98652d0e7d6194b439f98252d0e7d6094b439fd8552d0e7c6154b439fd8152d0e7c6054b43db54852d0ef66114b43bd58452d0f7751947439f98a51d0e7d62947439f98251d0e7d6094743bbd8951d0eec62547439fd8951d0f6f62547439bd8951d0e7c6254743db18951d0e6c62547439fd8151d0e7c6054743bb98851d0eed6214743dd54451d0eee62d4343bb58b50d0ef661d4343bd58750d0f7b5094343cf19250d0e7e62943439f58a50d0e7e61943439f58650d0e7f62543439f18950d0e7f61543439f18550d0f795014343af5974390f3d65d0e43af9834390edd65d0e43d75974390f6f5294a439f9865290e7d6194a439f9825290e7d6094a439fd855290e7c6154a439fd815290e7c6054a43db5485290efa6014a43be5805290eee62d4643bb58b5190efa60d4643be5835190f775194643d7d0e5190e7e62946439f58a5190e7e60946439f5825190f3f43546439fd895190e7c62546439fd815190e7c6054643dd5445190f7b5094243cfd925090f3f43942439f98a5090e7d62942439f9865090e7d61942439fd895090e7c62542439fd855090e7c6154243bb9885090eed6214243de5405090f9f5390d43af5864350ebe6090d439f9875250e7d61d49439f9835250e7d60d4943dbd4a5250ef76154943bd1855250efb6054943be1815250f6d52149439f9845250e7d61149439f9805250e7d60149439f98b5150e7d62d45439f9835150e7d60d4543ddd465150eef6254543bb1895150efb6054543be1815150f755114543d7d0c5150e7e62145439f5885150e7e60145439f5805150e7e62d41439f58b5050e7e61d41439f5875050f7b5094143bbd895050eec6254143bdd855050ef46154143de5405050f3f6414143cf90c5050e7e62141439f5885050e7e61141439f5845050ebe60d0c43af5924310f3e5490c43b75924310f5e5490c4
  | 53 => 0x6000000180020000001c00200080000001000080010002000c00d0001000200200038001000c00180020002000400080010001000000040008000000200100050004001c00b000000070016004c000000000000008003000000120004002800b00300000000000000180004002000000040000000000100000010000800500000018000000100060014003800800100014002800200040004000000100080004000800400060010000800000000074001000900080000001000000160008002800100080028001000500180004001000600160010000801000080004004000e0018001000800130004001400080040004001401c80000006000000080090000000000c8003000200080008003000e00280050003001200040000001000000ac00580000002000400100040002001c000000100080000000800800000004001800e001200080030002003000180008003000000000000001000a001c001000300120040000800c000e00000118002000200180000001000c00000018007000000000000001001c00100030001000200340000011002c0008008000a001a000000100000000000000680000018001c00080000000001800000140000000800180020022003800180000002007400000150000000400180000050000400280000010000800000000016002800000100014000000580010010001400280030010000000700000002001c0008002001c0000006000000180000003800d0018000400100050008000000000000000000000000000028000000000080006001000d800000080000001000000040000000001000020000000000000000004001800700300000009000400020024000000400040008002800000000018000801a007200000098001000a00080000001000c0004001800f0000001c0030002000600000010007000a00000038003000000000008000000600340068009000800140000003000e00000040001000000000078000000000000010007004200340000001001c0024002800000060000000000000000018000800300040020001800100000010000000200060034003000000400000003000b0000003800100000012000400080120026000000b000d003400000000000000000000018004000e000400080010004001000180020006000000380000002004800280020000003c0028008000c001800000010000000000180030000001800000000000000000000000000000000300000004000400000040000001800180060000000c00080150006001c0000008001000040028000000000000010004000e003c0000009000a00180090002001400000000001000000140008010000800440000006000000040058009001c000c00200080000002000a800900020000000000400060008000000000120054000
  | 54 => 0x14000c0008003001000300038000001400180000002000a0014000000000000004000001800000010000000100040004003800a0004004c0000001001000000000000000800000028000000000040000000000800000000002000000000060002000800000020012001400000060002000000000008006000000480000000000000040018002000000040058000000000140030002001a001000a000000060008000000200060054001800100060000000800400040000000000000180004000000000040028000000400080004014800200000014000800200000004000000f0008004000180000002000c00400000000000c00080010062003000480000002001c0000005000000140000000000000000040009000000000000003000c00000038000000c000c003801000220004000000d00000008001800f0000003800a80020004003c00080020000000c001000500000010000000b000000c4001000f0000000c00e80010006004000100070006005800380000004000000080010006001000000000008001800d0003000000040020000000600180010001000200080008024000400000020006000c00100038004000000080008003000000140010002000800000000000000200000000000000400000020001000400300008009002c00000008004000400580000004001a00080040000001e00000008001000a00400028000001000000018004000600040000001000000100080003000000100028002003200040010000000c003000100090002002c0010000000c002000000000002000000100230040000800600030000002000700040004002c00080000008000c00100010006000400000030008002c00000020000001000000050004000000180000006000000f0001001c00980038000000000040000005003800080040002001e0008000000000040000000000400060008000000000040028004800a000400500000000000e0004006800e0000000000100090000005800000090004001c0000000000e00140040000000200080000005000200080000003000000140000013003800240000003000a00000018000000000000020007000400000000000000a000c00100010000000000380000000000400000010000000000180010002000c000000b000400080020019000a00040018002000c00280038001000a0000006800a0002001400000020010000000000000004000000500020000000c002000e0000000000200010000001000000010000002c00000000018005c000001300000004001000100000000000000a000000040058000001e00000000001000600040098000001e0008003000200040008001800300040010000000100040000001000b0000000000100000004001000480000000000c0000009000
  | 55 => 0x800180028004001000000000002000e000400d801c0000000000080000016000000480000000002400b0019000200400090002000800000008000000000000000001000a0004000000000000008000000600020000001000300000000000800a0002002800000000000000000080010010001c004800c00060000002800400040000000001b00040008003800100120000003800100180000000800a00040010000000f002e000400300020004001c002800100200004000800900040004002000400000004000000000000000003800700400000002000f001000100008007003e002000100000016000000300020012000000280020022001000100000018000400100110002000400300040000000000000070000001400a00040004000c0000008000e003400f0004000200000000000000200000010004000c00040088001000400080000000000e00040018002000e003c01080000000000000780000004000c0030009000000000010003002000000000000000200600000002001a000000000070008000c0030000000000040090000000e00000020015000000000008003001000580050000000a003000200000000000000900030000004c00a00000006007c00180000000000800400010000003800d00000044000400100240004000c00000000000000c001000000040000002000000040004000000000000008002000200040000000000000060040002800000040000000000f00000014000800b0002000c0010004000400000000000000a00000000000000200980040005000200080040002000c000000580000010000c00d800100060004000000600100000001000200020060003800b00020008003000b000e0000003000a0014001c0000000000400000018019000800000018007000000480008003001a000000680000000000000000000002000400000000036004000300010008000800000000006003c0000002000a00040000007000000240000007000600040020000000600000028000004000180008003000a00100008000000400000018000000e001c003000a00060028000000400020000003000000020004001000500000014007800200020028002000400080054000801a001800080010000000600400030000003800000008001001e003c00a8001004800040008001001e000000000010006000800a000c0004001c0048000000600100000000000200040000000000600040000001000200240008008000000180000021000c0020000000d00120010002800100020028003800100000000001000d002a00080040006000400140000001000e0010000800d0012001000080000000004c0028001000e000c0008000000000000008003001800300018000000e00100078001000a0004000000b001a000800
  | 56 => 0x180100006005000000050002000400080000000001c003801000000030012000000020000000000700160000002000900140000000001000000000000800000000008000001c000000000008000000a00240010001000000000010000000e0000000800500260008000000b0002000000800050002000800380040000001000080000026004000280040026000000980000004000c010800900340000003000600020010002800100000004000000800000004000000400000000001800200120000000000100060014001800000120034000801e0000000800200030000001c000000100000000001800000040010000000200060008001000400000000000000400000000000001e002a000000000000000004800300010000004800080010000000400280000008000000c000b001200200018000001000040018000000c00040000000000a001c0018000000000100008000000800100000000000800000000001000200700108000000a000400180090004001400000000000000000200010002000c00000000000001c00000010004000400200020002000000100030004000c00000000000000000080030004000000000040004000c00000110002001c002000100000018000800a000800080000000001e000400000040000005800180010000004c0000001000c001000380000000002400180000004000c0010004000200080000000000c00000018002000e00000070008000400000018000001400040010006000000280028000002e000000080110002000c002000000080030001000000060000004000100060004004800500100004004802d0002004000c801f0002001400000030004001800200040004000000700010002000000200020002003000100000000001400000020012001400300020004000c0010008000200140008001000a00540000007000200200038000000200080008001000800080000001000200040008000000200000018002000000080010002000800000000007001000000000002000600000008002000a00080000005000600000018005001e000800080040000000c003000000100004000000200240014003800000120004003000e003c002000000140006000400080000004000400300040000000c00000020000000000000020000001000000090000000c0040002000200080008000000a00240008000003000080000002001800080008001000000000000001000400400020004000c0040000800600020004001800200000034000800c000000040000009000200000000006002e001400000000002000c0028000001a0004000000d000e00100020035000c00ac0050000000c000c00000000002001000100000000000c000800200260000000000400000008007000100060000001000000
  | 57 => 0x600240068000001800000008000000200080000005000a001400b80040018000c01e0000000a0040004800400000004000000300000000001800c0000003c00080030000001000280000000000000d000200000008004000e001200000028008000000180008007000c001400080010010003c00000000002000000080000006000c00380050004008800000010034000c00780020000000000080010002001000000020008001000000000000002400400070008000c0018002001800080040003000600200008000000a0014003000f00040000001800d000c000c00100070004001c002001c000c00040030000000600680020001001400040008000000800000020000000400000000009000c0000000800100000004001001b0010003000080000004001c0010001000a0018000800000100018000000000000010002000b000400080000000000400040008002000600040000001000a000800000000004003c0008000001400240000003001e000000200040004004000e800600020008000000600020000002800c0000000400000000006000000080020006001c0038000000a001400b800300140018000000a0000000800000050004005c00a80020000000000300030002000c00000010000002c00100000002000000200020006000000100060024000000000030000000400100090000002800300000008000c00480000000000000280000022002c000000000000004001000f000200140018000000e0000002800000460008000000b0000000c005800200040008001800000040008000000300280004005000000080004001800100080000000000200020000003000500020030002800b0004000000a0006001000000000000000400340008005000200000038001000800100048000001e0028008000b0000001400080000002000c0038003000000240010000000000180010012000600040000004000c000000000000002002000d80000002000000000030002000000680020002000800680030000000000780070000000000a000100040004003800000020048000000600000024003800a00020028000000300180010000000b0008004000680000000000000300000000000800000000008001800000000000000800b000200000024000800200000000004000400060004000000600020008001000000020008000800500140018009000d0000001400080000000000400200000000000800000000000001000180000000000000500040002000400000010000000000880050000000000180030000002000500030000000c0078000000a001000000020004002800880040004003000180050016001c0090006000600140000002000200200018000000000200008009000a000000080000002000000000050000000c0
  | 58 => 0x8001400580000000000c0028002000000040000006000a00040000051001c002c00a000600060004001800000000010001000000000008001000000040000000800b000200000000001001200000008002000a003800080000004000c000801e0000000000000060006000000380000000000800000000000000400280000002000c00000010000002800280040004000800400020008000800080000004002c0000002005e00080038013001800000008003000200100020001000200180010005003800040068006000000340008005001800000058000000400180010001000400040050001000e0000001800000040018003000a000e000400000080000002c00200000004000c00000050000000400180000002000800300000000006800300000032001c00580070012000400000000000001400c800500000010002000300040008001000000100000000800000200000000000100300040006000700000004000800000000008003800000000024000000000080000002000400060004000800900120000000000100000010000000d0008000000080010026000800280130008000c00100000022000c0008010000c001000280010006000800080000008000c0010000000000100140016001a000400200040010000000f00090000001000300020010001800000020000000800000000000000400380000004002400280000000001c000000f00140028000800100000004000000600000010000000600000000002000e0008001400080040000002000580080000002000000020006000000a0003001400000008003000000040028004000c000400780000000000800000020000000000e00000002002800000000020001c004801500000020002000200020030002800000060000000000000100008001000000020000001000900080008000000a0004000000080110006000000000020014002c002000100000030000000000000004001000b00140008007000000180010000000300060018000000100020004002001300060008004800e000a0010000000c0006004800000000002004000100020018000800180030014000000400090018000c000800100000014003000000000000001800d000200000000005000a001c0000008000a002c014800100000000000000c0000000c00880040012000800180080008000c003800e0002000c00000060000000000000020002000c001000200020000001800100b40000000800d0058000400000030000003c0028002002c003000100000000000400d0002000000000000003000400000008000000a000400100000028002c00000050002003c001000000020000000800d001a0000000000a001a000c00400020000000000200010010000000080040004000c00080120
  | 59 => 0x7f2871f03ba17100000370213e2c746f285699854024c478c218a09d1d1a5b808cb291630b42705247a7060a5a000000008f1000000011f39b1f012800000000d6a000040306ed000013a00000f831e44521883440000000000006552aa2694131a45000002a833f0c00006be8000059260a4980a1ba4e6e585825a2ad72436a55002f80002d6c00012210956000053709f7990f1136167948f88dc363682ed038a30c000000010fc000018f4000000000000000852c0000000490ca3e4a0780000000000000000000000a97c0000426000073d80000000000014a926d25680000919c000000000000e9481c000040a412b80000000000000012db01750000399c6b9070e00002680000175c55668d9534e85612c7aad7400018ba119875580000000245a000115095341d0cabc9425892420ca00f8a4b8522029284055318945535c4e5c7ed2aff00000000bdb19cf05ac92910cc142100000000000000000006fe00000fdb062c15c44970ae20000000061100004a1a0c9800000002a06383852620cb3b0e3260cbe0000203e588487e060c44cab050000400080070002004800380000018000400000150000001400180070008003800000000000000c0138006000400240020001000000000008000000800140078002000a0094001800000000000000000000040004001802900040028007000300100008003000000000048002000100040000002800200000000001800a0006008400400000012000000000110002000c000000000000000001800200180000007800c0006004400280020004004400080000000000000000000002000400000010002001400000070008000c00b00070008001400200030010000000000020000000c00000040000001000080000000000400b800000000014000801a0002003c00000010006000000000070000002c00000010014001400200080018000400080000004004000d000e0004000000000000020003000080000016003c00000210002002c00000030010005c0078001000e00080000006002e0000000000000020004000000000000000003800e0000000000100010002002400200000000000c0008000001400180010001000c00340008003001c000c0030003000c001c002800300240010000800e001000380020001000600300060000003200000000007000200080020002000000040000003000000200030003000a00100010000000200000030001001a0008001802000020004002000a0020000000400060012002000200000006001400380030000000c00000010002000400180010008000000200010000000400680020004000000080000000000000200060000000000480000000001c002000100000064000000300000020000001000020014000800000060004009800f00000000
  | 60 => 0xaa28189c000000017f2000000000000000000000002992035260a0000a7f80003f5e00010e7901b00008228fa5a5c70000a3ace2ea2104b9aa358000237c53548b545790d2b3c529d28bb292fa16f6151cc20a5ca129e00000bd000043a076cc25d9cbf000005c0000000003fa93895b79c0b2f045eb145582b847d612a44fc0000085aaafcf45000000003e15047110d00005ff45c205f70f5600007c3294400000000000152f552686414b580001ee800000000000000000005e280001b5840180d398df00000fc0000000007320000000000000005c483c8a44143faa22031614604cb05b94fcb81e619084a190f01c4d51de37e4d971b0c32ee00000000000350c286c00000000088a05000025be49f057d000002d8559c7f64125a0f009fa0000000071c250e00000001d7a00000000275856f000078fcfd4a049533252c5464800015c247a43781f44464c145d3c0a675401c5fdd54c925e215a344000000004efa4394000023e44c2000103e1d5d53ccaad4b24170d00000000db3859d4f2a63792baab9828a06f915c2223324f69d9cf6d9a8055d47280bc6a8b653c06ff8d93800005126e641d88000518c000000003d90000356c30587b64e500000e73890704e69c8401c80000000897c000000000008a586a0283a04d280f5328007a4b4c000138800004df40000d65800000000000698000011e6451c0580000000000002f3800000006f6c00000000000b08c00010d6401a2d9066f00004c6e92ec000000047c200006ff24570000000000000000000000085a0b5a1d143b34f6b9bfb1f50000068d800014bc7cc8bc900002c2e6074fd729f00000834059a163c000030312a18a714140905000012421dd0052c8d28000564817654b686ca294e30f87e200001c64000000000000a20a9f531400000000af000002b35000000009d699aa11e400000001dbf00000000d7f94250000057856000001f22108c29c151c4ee40000af88000297c79d0639874949b66c6501da75000001d940001520000044a8000000000b83ebccc70000000000000000000000000000000000580000008780000123a1efc2da91603cda00000000000088c296012f0000250871840001af3000016100001eca376200000001b7500008c8400002190e5275b49baab1f000000003dc1bff000000000000efb551e0000e372abd25c012bd026a15f30e0776d5429ae33118428071d2aaf574c0000bad80000bae00000000999510693a467a800006741470472191733e24014f111704519603e957980000000a0b400000000000b0250ed000000000000000016c575e3a380000000152c0000d1d00003692000000015920000000112880000000535c00028862ef05ea1503000021e83cd42c780000000932800013fa000080e40240d273aa8a838ce3035a291a
  | 61 => 0x413049d60000000000000000000000000008740000584a102ca26917529aa2af88ffa7990d826d18fc593920818218c500205b0be09ac511416492e4e99f4ee89f5b56a40b4ceda13151fa418d143c000000001a287a886b93bf800007bd289c40063028726a7df37dc0000000106800004a593c52bfe18fc96a86cf1c333394993c4aa180a0000000000018a800007cb8b64800047a40000de41d9f2a36629c1b0000046c43b5466501393452692482f8dfb16267ff51b38ad9471a7a3c0001ce40000000000000f800005458501800009a09e8c7138b0b53a68d7c000281a0000698800023db000000000738ef4156a00012e59dd30f8e3dcc1048000000000000000212000017bd4c125df1758581c0001fe00000768400000000000791d57b95aa0682b10cfe2149e505e00000000000262c000000007ea367c000128180004126a170b628cb011520000000255f216600009a999bd50b092fcec10000292600007a98000127656fcdd7ab4247420000dfc956013c29644fbd186a0000037d0d380000000a1b400006e73aca000013618573aa23aa400000004be01ea49ab800000002ebd3d2042f00000000000000048644d3043f8000337200004f18000086c258c00000001d660001474000000009fa4d97aaf1561c0000058800046141a847a08000012e24a4000012700000fdc0001e9c037e93ccb7380002fca528d2e09e0615520000f1527d517b0680547312ce03548ccd3481d4318be193c21017a91ea88ef84d0a9f711f68bd8f668ab61d545034367a6aa1690addc4d2817458b000013531e0008000f714eb9c3a12f870a800024cb410c000051e90a52c06266800000000000288400010da00000000f0f8f2f000000000000000000011e06748000208852e02dd92f1000081d90af146d00006a7ced6154849a8619d3398d15462284313b78d01000000000002bc20000000000026600000009c0000000000000001632ae12c1a4fec6208000000000014c9a8804a6e18d4f2e1ef125e875e0ed80bfe32f6ad9514f8ce7557c215c4648fae116c2ef8c3d1d6613be53e93308f7e4132000000009e62f94000000023c50000000139e91b2069e00001719aa6044200013f91b1152bc88000002adf0000a5d83af01d2140a0001619878f078c8c2d29f11c1550e438050f16b71d8c51780001a3c0504000106702ca23206f10e8f01834fecaf540001a94400e13cca5c800034ea76dc9bf9df94ee027b800008d74ccc00015d806330f24af9879e258b17c61bbcece821044d02be4ce9a4c7000000000001d1739f231a800011be0aa014a40001a3606c4a80800000000e86268c5fd26f1000048a872b8000000000000000000000012f40002a6d35ea5a6c84a00003562000115e1ec4450e549c00000001c6e2f045b5890b457e80a1285
  | 62 => 0x30ed706d845946caa26b54206780000168603e44a0ca7618974574994cff106541b0e53415e5235725800000836057c587a79d91478d51263c4da4000199a00004168253800032120000000000040e86d940000000000000003dd9dbe0000000000000000000000046f9d8d3e9e3fdc1971c39149431e0b27a22f504481a42ed143a0eee6190f7d888000003e60b1b00002f680000bd01fb8000030bcbd0a87235d240b8d558b292cb014749618e3b4316108880b9b4b1be61ee46b020b14008a21411b967800003ee8000000000000000a3f80000000745800000002df60000577a3c00000acb0eb4120b3ae8043898f834a33c459080000a13500a89f4ceb02a037be318ca4380004770a0d80002bcb00005fe40000950000011e8efd8000000000006670000000001780000523000000008970000000019112838556000000000002654000006ac00013f650be4bbc000053c2b9e000000000003bec8214e16261b00006088a3e85bd54182418f108ff35584737d4051e6234bc227cff2a2c00c3e67f40000000552e71e860b89b854221205545000000000000000000046340fa8abc84991dce5e1433d0bc6000048d518984ac18861188c488c3f00003e0084300000000000000016f0042662cd6050c234818965d5399fb419be26e80778000000000000c30d4f3832000000025b2384a0000000048d575011c000026170000732cd4b17bc0138abb800004832fd8550105700000a22a36800008253224000000024f1000045e430b01ca52460000000121330a600000000e555732000027180000000000000022882bee2ffca7981200000a19026d1d8f5432789cb9920b3000000000fa00000cc678b07db800009b800000002c170000000051380000000b05400013674e540000000269c367200000000000426220408f78000000024f8a7417e43a62851878824b114da59651fc0b8e52627c6d2a9a525323e5a71096125019f06330039000005188760000000000009b94000028d00000000000249f4f3c00004bc0b6f3fcc0000d8e17c70000565c97f800000000001516268449f6645529300850ce80000ec99e4237b8579c0000000000000012409f9a0000905c6f41e58079a883000005701db833b524e9f18000053600000000256c000000000dc11deb0e0287186c10d200013fd83553ef05b900000000000021780000000167e0000b078000000018ac9aa8ca90000a5611f2000015280000f1d270e0c2292140001b063e1e495c988aa8d24745b9857580003daa881c5232c054ddc5c4d2ce8bb8066c2f340000000000022e04370a8a354695b438429b155ea46c50f7a9bf4b284d40000141d10901d345f91f1a06e029a45839df000000bf4000065e1d0aa83cc4427cc099029ad1bf86862c9898f88251e334c4a5eec530a0df172
  | 63 => 0x151851180005342af9052200002f18152944d859b130a328d17a0428078618600b002c24ef48ba80de947b51466fd485e83212c8c37953a3913917a2000094487392c86a6d80000fea0000000053810d80000000000000003dfc00006449eaa00000000e318c9f015e2914424800034f29b84f7c192a0482988400005ba1f7875fc000187f146e00000002823000000011050c8e000007940000cfb20660000b9600000000626c00000004440a77ca4f80c203a230940a79ac40c8204445180968000070e04868000300e3a043a81aae4e622fe01db9254000057f40001300000000011d90000000019a400026140000861c00012df4e0a0a4d18900004adcb06818d2aa00000000056e165010b650105b4855f4d92093c000052700006bec413a9b30d1c49b4491a63614fe300413e054b471420a87c480000a300000da60e721e800a44000000032e480c08d780000000000000029a9000000012c02970000089f8000000000002ed000026080000000035817c81262000046f0000000039f8d77000000008ab4000278c128e9c04000237800008fa00710000261c98b4c7b2bd25024000000000001ff6000107b85e500005bfca0f0f65544806e84c5ac5400001f4d2dd000000000000000000020740000000000015665a8400000005388601025096b206d656cc0ec13d23b1644cc00028b30000000000010f30c5a0000ddc16054c3e00312e60bde166c19dc00018ed559e38f000023300000820cc620c6b000073584de9466000000009ee8cc200004c4800000000000a0783a2266c0000af74cff018822e090284af9ede0000a34c350000021381e60dc6a36c00000000b589351580661dc4458479449e50acf628c5e44ac953000023cf3b9eaa54b9980002fbc8b3c5b002f70490000017107e300000000a980000550439990fb20cd561059d941822132ae693581871d2d3ac4662000005532ac27fa09d50f6113ae000000000003d108be87418000447a561d2d70000000000005cba0eb0d800758bb22b9f000072740002a6f31a407e14f623d732f4024462aaa2d02daa62c3ed9027300094c52311f674eb81108ad6150749a00c8015b86751fa07c5481b1ab91a1873e8be79c0c219c3efc0e01e0125324034b45061d4db43fbc310a19717cc50e400f8000000000007fd154c539a3950a5080003ebc0140950a54113a21d641cc2a9f2fd66d8ce04112945cc203060fa45e37787e7cde59a260000803c000000000005a3800001fb000062bc0000000000000000000c3300008de94959a14141e00002b1161041925c1816ba42c512a46f524c8000360290dd29119e816b071cd3659c02467aa8e441f00000e167c40aba000032bc08d468a093c33aa554827f11df2b00adf8c72049a00002d000002b3c42e2721c28
  | 64 => 0xd900001fe800054e30fe025fa49e85a8122833ca3650000183c278415dc0002c013bf40001609800000007fbc00000000000000155726651fd68ed48ff1d0a243e02801e5821b584486ec985150213b60a0d5ec045d151015940c7a1320da6ac501c19e5748fe3b784759ca9414a76a12e29dd445640d14e20107620e09c5469d09fc2762391cb8017661bb60a60d4409442d446470c2c06e135bc85c94e19a4604188658927800054c4920c000290e00001130b598106000085300000000000000000df1c012268474d31e919b09ce0000a0d80595580545504c0000246c000080a0aa60e6c000000000001274a3c945d9fd61b920000000106713ec0000ff0800000000000cb98000000000012cd26ed3ee0a31d0e6a7783c5c14909e3039748a21854a4c82f02ad86eb8d98882932060f88c42879d1918aae0344899000002e58105a57b14f60000ba221fb0dea661800007e641b65048d9b0b734226838c000140a4bd889c8000100f07fa000000004bf1b386234000000012c8000093480000000000020494fe469007b888ea1d200005808deb1eb31464460c15780003cd8460020f0000000037bc4eb000000000000000000000004fe40000000000000000000efe2966000039a993c06108ea5079000000004ae540380000000000075080005088000000000002eb422dc000000000005558000032532de0298000097f266e00008a3184c01669398000000000000d7800014c300000000000000055524ed02fc223900000000857993024ee59d00450f7f47a00000000000000002a90f0800004f24ab2c00000000000000000000004d7299b8687800000000000218296a0d4c0000be9000028f22a1408f982600000000b83870f37d684dca2b00003c1245cc000018b00000320000298d27e4724103c2b3d021877a42ad8df75392188c0002b483e823ff0ea2a38402326ee400015d607205c7800011d432ec5348d4d0daa4df235d0d43a1c83e6000000002bf2375a32652a29c452d0e1260a610000532c469902a00005468a3d506b12314c4403290eb93650000ad4069494d34c5e64c426b9c5e4ec20cd40002b7301003b0c1fb09c228d444240001b8910deaed400026490000000107b28602f12172d3798c38050e859c7b524553a4600001d8284353900dbccd205db0cb80834b4f814e0000ad883189fcf2c468e7916710811226032509800000000976c7a611c818926430ff611ba437e438ca1d96791964473c0f600a83b1c99211fa1ebe461c4c906fa8c6c267824fc83181f9448240b01df1fcd4bfa2c74ccc1e4b30ac0aa4d17000054d4ac1800020a8000071d92bc800025ec46fcc3a80002cc46b6400006aa430c2b2843c883d00001b8800023f000003cc5486839602ac3d5521aa04f0000373850500000d2a0e3100ca9bb00
  | 65 => 0x50543c0919f29120000000052f1a5c7d600000e360000000000000000fec00000000000460a51a0000236b00000000000201751c21560bc99699190c0ea460c00000f803e40aa9957248b6687865fa89214786cd509aa8b1186e0000c5088b54e160000255a9875412635c0b19a254ade3400f332c0c0000a588cb522842fc679349c628e300000e14000043a0ad2895108f933800000000982000009e815fcd3627bc0e049fc561e0dae0000ac4042a9e9f454618a91d7a7ac003a1384ba00c4842b85c40de0882b3a6488088dca64d07ce57d539c08ae236c702800000003e062afcd32ab950000459908a9d115696144d4ca0ec128960001263071b5822a960f9890b101b68b70b3a94ac1a2658a07f221b91aba0000ddf91f500005635575905530425740c4e12fc00000c146a125c900000000000299b50400000b2b8000010e7fd929e879c000000007bd8000000000006200000000072b12e3038b0000000010d15d80000127053627940314abd003719591b661f80f7780004ec80000ba12a2e29900000000112f2e0200000001d0300001e1c000000000000000000075112da66b400005a9000000007da000000002a388508000181c061400007452798658c0000d531fac0cb0957a41f220e00002568e8b20b800000001ea2000024703ed27b026322c3cb4880000216aecd14bac2129200000941000000008cb0ad480000000000000001a23e6660d452e000023f671f8aef87a340ac1be48b40f9a4782599c3f20b9d000000006a4941a4934893800006dc00001e7c0001b23144a70846d00000315a9c30d3d880100009ecd12380a9370635a10a2000000005afd384138b337070bc76c06220c80aea86c49078092a2b5c0d4119257ec32849689a6a16fe598d2c400e82aba585441820ef0e946204e70800041c006b83a5800048d414e82362b1b524454743a797d7279a6db8d7c925c2d8455b93c8a3023f909dc43d6a6bd0a1aa3fcdcd820318b6261c638000000002c80000103d00007d5c0000440000000000000d5700004ac4de622e30e280de40000d9200000000000116d0000000000000000000537ce5580004f56591000019b100000000e420d701c92105824900e0332666bc027060d4d5e429ce898000000000009ea80003b526f6086c801b39282d6c000000000006b6c00000001ff00000c630000000000000000646142490f8001298a09ee7a301ab883f00002399021000000001b7c0000000000034211ada56a00009f4800000dd333e0001090a474000000000002be10bba00002dc22c2000000000002964327650b82c10b142f6285a939d88bc310096cc96ea94e143299e90480a2d12b05108e8c276e4b1c17180a40e24516a5df94e629d038d806700f4987112d6454c000000009260000d271c3d38be8ef03
  | 66 => 0xb52a65b0b2687dce4e000000006fc81e5000037567b3c8959ab804e84454000106a397c73d529990014a604bc91668dd701ae01f4811a218018a034c0000000000000000000000526a358c50580000000887c000206000009ea52142676248044c031f18724118a1fce9e88c600e89d20d17881d3bd0410d5e498193ea24bb08b08000000039d800015a3450aa641157a76a075c2b6c9c711dd46642e2cbff09084d660174c168a8c0e5c381c8c125494a200534b4908bb245c1ffc71421ce4aa41294567975d1352000000000000f660000769943e22b8000000000002aa80000eb5800034da00008710daf097c623cd57864b238a234c20400e340743db410c08600ba094444d883bd4cb82ef076625690eb0341d2b5a3a724122e911d002a70000992c00000002bc44e1d3e7984f00007db0000000017f697a000000004766a044b7711ca243a95700000000000080dd1ea1378331a07381ca00002d8056155d4800043be0000000296802fa7c10f7180000000000000000000d360000d9a06e31fae16d1502035d3d96a7c908197d416cc943c00009fe3f54787000025851040945c729a56c0a6e00000fa91261b8e650c000000000000000265243f458e0f5c5ae0000000074b031e00be29f2000122a0000178400000002a3106160000000000008fc7bccee612d3149e00001238000000026180002600000058440000f3f10d6425d159800000005fc1280a90400000000a522866273c000081800002470ac05583917727265d2d1240b170000960cf3f9ee60d62761833c1dd0062847e47c7aafb2e7445a8c66a37141340000c941b151940ac3513f8c961c8ab110aa89b8b3f380000f0a10220b5450643e710410000000000000002b623840000000051ec00010168ae30000000000000000000b1642ca80001520008c7cf8000317a00011bf26132502000150f85d340d683a0000000000004dec000000008b26ce805e29b83ff40000ff9293031ac8e88aa780002d26000000000002f28000000006804112a464fb79e6e0000000000003db02262d280a10000463e0000000232f515a000000018604158a494000232a0000000000000001af012d4e498b2a00003f18cbc1cf70bd4000028f9c560e66912120693b213f473cd42d22864c1a5898000000000827f4c0002a54244aa52d52d152e47044708dd0a3550d9689c10811a0600005718e3b9df44e7e5e10acf94204080166851c975f4c54a2c8daf00071722a5455b20000277ead58277945322b461983742bc35216121800000004d263ed400000000000a37c18a920f05820000000225821aa00000000000192280e00352a7534161b5804d1590561600011d69211005a3f052ea00000ce4004136880002a460000946000000008c740000000000085d000000000164165c00024f00
  | 67 => 0x35e28aa92d39770477410d51651cd109aa00015ac0cb7160c59f91a101e44f3e4f000ef25bd000000004c510640244555c3bf000025f60068000135900006cdcb7616731d00000000000000000000058092731a8831940002b2f127000000000000000000001bb800043c458909b800000000000000000004128000031c25fa051e4514ed6978f000024d0535193857b6a5f4d46aaf931e2aed0ce70000000042a84cfaa012d889148d949c625724aca12f9ab6e2c4e0000eea8e7b35cc0001354a85242a80aac2df80002b92106c00022f013e232cc9971de745c8713901190bb000000001a99ed43ce481a8f2f20aa00002f3800022f204a41bac0e680003c1a31149070a6518ec5e940002a640000455c6e2000000008a2800029380000500146d8aae000000007c6800000003dd951e1f9d29000000000100317c26a9c6a28000000000000002be300007c8c00000000000000000000000000000000007992b6e0d34f280c1c000000009d2000000009000a2a00002c5c30b518480004c9c00015fd00004bfe39d54bf800000000694000129e4a680000c658000344e58ac0da87b52a2200002b212c60000a1c499900004da0456479b202f01f83d603420201000023e0000042b3ed040c48531c673d3216c086f9eed4bdc0000f1b880200000000179000029683ce800018a526ba603135b80000000855c4d22062165a00009d3800041da00012eb2275476c7b4c3bda6830000ac715629892000033bc39800000e98a44800004e5028a000000001c222f67d9800000000000000000027562c6a8e7c0002ba3170a07d80000f4d15404614a62aa5e40683b155e217752b9094903c402cf05dc76f137f933116e49e14fc7000004fa385c000000014508b74a0c00004b18444063e14324e4479c045383a73be48a08000042c4e66260069100e50000618d27a048b14746514000000000004aa000000001c0a0000000000000000000000052c2494000079483ce331847f000008383c9c04740000e984e5800011c480004d0aa2900001dd700000000d04800000000240e80800000000001181800045b400008398000416a00002d3000000007068463a2cb000093610f429ca4b6e111c767000000007e4000026c446f643151e8800025746018f301f0e272a0000e5b000019886ed00000000000021d484e8000000000001e02a0b0000000000028d149a6952c000162f562e66f80000000112ca594ce016f3462a0001356a2e51bdc1be0e6317111d3249590ff1d3b43547d5476ea59c028e6278721000043fe70247d58e1c0000933c000025936825ba91d6115e00005f74b7c800020e28e14a0711690478000003319d04ff4000015b0b5443687524c96800010f87b0d00329851172834c1fe14f151b20000cae8000092840444e019f7000012e4
  | 68 => 0xdcd1bc742a4000001588aa3ab666ac6138f87000000009d1000024380000000190a0d6e0eb45ed00000a8a000000b1e73135c00000001b9400003720000201e0000119800015be4a1c0001201113d0f8205b855e0302553aaf81393800000520000283800024521a9c000000052823ce000000001806b02c0000c6106148d405c7887600000c1d41a0cfd047e6f8d5ec82a6000025b936010911536a33560e206d00000000e7e00000000a0010bea82941027880b4594370000633c706246d3ed4ac011e620b244e200000f78dd304a89364a95094b07267af12a21d95000049113062ad03b9434a832c9fb6254600011210bf328ca0ca46e600003c4800000000000000000000002b44312c00009f597e80000000000019f60ef0000000000004b8088ac0000000031c00000000b450000123800003bb235c444c00023583378ad251e3865b368e0001488000027c000009470a40000000000000000420e7ecc000006500000000f92a707258435602658000000075a93a023f321f083203d8000008dc00010710a9f3836140c6cd23ea0ace5ec0145000000006268cba800053f28a4c00013bd55da0000d23a0b019a65324e5822a839860000000000000000000000170327700000000211b00000000000224354b66860ba89451000045d000000001b42000037280003efe59f4000000000007154d0a800030240000000002f00000000000161d0ec67e0ce72a61e2854944c00022443998ae29115263827be9b90a7580001cd64d890c7a99f4c486a0c482292d0c9c35acb4a9f2b4640099c5cca63149ee3a9944b97ce392a971142325201504898c584906f3bda9338f251cb424a6a4ec87880000000723400019a100004cf8000000036ba000000000000000000000010b2369e00003389f65212c37d85f79c060000a970fec0db9447495d02f5849600000000a1f8000000054780000000000030ad35d9df838400000491000031623cdd4808ab92b083d589b68000579c000000003892712444511e2407039e7e9056f22770b564bcc33519c11ecc78b43cb8006196a4d9803d80b800007e580002b85088886dd5818b3d2888b1491400000000000000001b20000000008632032000085e4000000000000000e2d0000000044943c7000000001d58dafa477395e1d5474e0000396400009c7a2f300000bec00000000000ab50000000022b00000000000032fa0000587037e46d200000ea985923283f741f3127d278a0000bcb01b2000000007f480000000904c66a00004fc601d40000926000098e9427000046ec2c88fd305c41f0601fc6c124b00ba2479c4848ae620ee99d09a524f5330a0001023ab2e2af8a7487282b3b025a57bc0c9a11600000000000000000005a413b027d1000000013051f2c00002aa11ae0d4d00000000c5c9379
  | 69 => 0x33b80000000000000000000f3a8000260400000000000377a0000000000000005e200000000000079590f70000456ca5f8000062438b0000061900003bcc21e80000b26208a3af046b19c8267600000001c3000000d49472942d4afe21c5182000000000000000000000000000cf60000000075c000000a7125476b921a180d0000716d20c848f57008ed136b20ee350a00002f61317392200000bb000000000000000000000008654456000000005ebd5e9999400006d606ee9b332052960446a21f426a85de4a4c1e251a4000000002a1a551c245c000000000003354f89aba50000859000018f400000000a110da53cc600000000000000039040000000374a35645f3800000007815193800000000000e55000057eead7c6930000000043f404b05e2078e00001118c20000005f087480003934000056a000000001fc0ea2000017b8000108000005716000052823280000449c00018204dae600ca088000000057950370000194814d825b88b2000027c8000101226dc0000e2181184384265c430ab960cde8e580000b44380029bc8f880002282169153d13611738004d0e899c73f8c0000f8903590af23390c73a0150000000000009cf0000705151520f1356c93a95560953485496bc212000047d83adce401de32bd8841101f189f46620cc06c600001d24302cdf2a3a5460200005ea8a0149d80efc07b04d81e505568000105600000000000257300001edc00002ed2d280ec80000000000000015d092620000ad5400000000000784ca019da00000000000024ac20143d9c0002a8807de0000c4c266f000000000000000000000000000000000032a80002bfd00000364000000013987410c9d11cc47862d949cd93e92edab0206468c3a2c449c7555503b9000053040001a48000000006f300000000a4b8bbd00004f040000000108d0be60000000000042860000a31000000000000944124c589a33cc00000000000333c8e900375330aedd366095a53d48894e391fea00000000fbc85ae4ed03b8cdc117db53c20000a67084625b495f137da4ba068648bc44b9ea6106c9040920a9ba1a044d6cf17a816476025209b990212a5662fcb76a5720a40a874c7ca223280a87d4aea10470000000000003d500000000000251f00009259233000025447f7800003a00000677cd6998520410000154880003ade55c40002bec000000000000000087c7f9c070a28b360400000000c300000000020a8000247a3e10395132f1764a6900001e07000000003bd25e1000058642fd0ce82ed40000cb080003e289c700001307000050c00001c7d406c7d4c7cf1ace57dc0000000202a1b14266d07280000c0ab1249b593fc19cc00000000f4f203a00000000000000000000001f9b00000000000000011967d90ca208083e68000000012c15868000
  | 70 => 0xd48000371c9c50b4480000000000160c94880cdc00000000b2e1920a8e8de6985c0acc7b440ed998f4ba200000000fd9495a00001722c3e18422a6892a8b040000000134ca1290116000000015c72f826494c6d94a80000000028200001f7c0988de893853c22085d0dc1e7803d48094000103f2998ab4d0d7a5e924e4aae89879f193c3c2ba80000000158229e878700004c4c3a4c0001f3f000073ad28e00002b980000551957000009c3c17c9c4a0fa800d413900002e784f98000053125ae634c000000000005954c2a80cb0336000000000000000000127413f70000a758618866d427a000112c912018b266253e0a3ef55dea3f40000000349a0000800000000000000000000033049d047908d550d10185c722000035380000d5416312738322cdb982a3000036f00001c3f2e824944000137d36a471a0000000000003664f9d800030c2000107d9cc004645ca085403da570c5e292960000000000007ab9b12561e92340000000566869b8000218a00002260dda8000027000007289d500000926000020820000070cacb000000009c4800000000000000038f800012e6833c0001de200003801407a1ac22d86a3c0002b8307440001139aa070000000000000001516000035f1fe453f800000002896000000000000000000000013da11d628e8576d08295a5254e61b51169eac246800000000000000000000000000000099915eb000028dc9018ed90afe569c461c3f5819f371e31d043327dc38a80df43d105ff51507414641823d0ada979086e80003ab0a4dd3fc09954d9486714189d7c4790572c41880000b12ab60ef203884c9453786d18fa610680000000000022a256ac00019cc0000000003b0000000000015cd21ca54961c24d16a77f000013c93e517fa28b0681021a00001eb61064c858000000063513a9158b0000abf800026d300000000b2a00000000660000013cf00000000f4380000000000000000004276324c00000000000000000000000000342800000001f022d38ffa983951043528b7a0000295288d4bc802c30000000116d904900000000000000013d654e041119ba19c21f58000000019b86edc3cd0a5908de8b1090d10a928020000000209f00007774d90a344222e414d44e98ac3ee6000102e800058300000000000000000000b9a0d3d000060fc000000000008420c0d000034d69384000019912640aa93eb9fe9020810680000000000091d82ba88994d22899800000002ed600010ce800000000bc40000000306c000154800000000a6984ae000020bc000000007900000302448800004cf693d8f3e218c02f28cecc0a90f53b92adb526689aa3740731c1320e22015a4a4c000000015da000000000002cc88da01bb00001b301e080001a0d00fc000066180000000358835605fc3efc85ad351800
  | 71 => 0x90530c7e300001a2b55ac000000000000000264400000000000000000000003af2000000018a00000796d22290591c3200004569a3d568093accd6000000009ff95bd0b8900008478a94800000000000d02800000007a6c00028e72258853c00028aa1824a380ca3a83e174cab8d5139c78000060c0000000022c4000000000000000597916b13d01bfa2ca09ba2aa71d728b8122583b30000ab2514a81252ece9d0d2da8000515e0af49939bb31bd86b294f70337522e26d8395906e2db49b142ae8ed21064552d461800006480000a5d896013d8a85840a940b06e212d840d200c11ee2f20000000011247dc820985d508c00000000000000001ba40000000587617384598000000074846d80c6e000000002801a2134629a284c60e182b18a19d28f24fe58506bbd23aa4b8000018a029f000000003f9400009c4308e6710d9e80000000000007823e647760000000075d2d86a15816f9844447032880001ec740f64828825867f1dec00fcc9a00003cb4a1ac0920a6239029930a4108a32a646d70c83015f00009a3400006cd00006b944ac93e23e860894000033e4b080b754f78000000000003e621be146aa91c0000d342d6a0d84f22a9e554527294cd301520000808800000000000a02c10a000044c4000000029c700000000ce92110000095c0000071703da0000cf780004eec4da934d000021a200001dc07013486000098180001cac000000000000000000018c00001e4000000000000486c0000094800000000000000000000005680000083c00000000b5600004fc800000000000384c72c4000000028ea208d47da1ad3c80153c00014bf000067342b7095d0842777d2990b000470000156318ae1e2460f40000000000000000000000108e78d1097a4711bc096b0f5788944246000006a800000004a001b980003aa60f503148000589c080065390eb4a909cd0d4cabc50000000000015c3294492a8000179f23d088c495e1b3200006d290d99d800366000000000002846909077a8fe2000000014e799c300000000ceb8fdf0602653838c291808d4a9f000029a25544122800000000000250c000000004c200007d00000279c14855c480000000000000000004d3c000000ba44f11aa000028415a61760000092909f516105a30ac4a35604b0812cdee8000143e16207b708ff10d089b4f948ad02a6200012ad877200004c4d1800000244c5218dbd90ca26b405ed01f9edd40580000e2e1b8841f8000159320dc0000000000013522ace2280194083709c043080f0800000000000baaa7d80a82000160f800000005f58e0292712a14000027c8000387c192837a0000476e0000000000045be1c6400000000000000098d9b4538503bfc1572acd0c40560884480d100000000a7c11a32da68a81436257e4d4200001b4a3862bbc00
  | 72 => 0xce909287e93ec0271c70b262c000000014a4000000007795614a77e000038ac0000703000057cc0000000120a7ae85c9963002886a2cc8ca1173b9c9d8c17c1f61000000011c0903500009d88b2017da00006a7400028ae00000e8541616a4302621f49ed0b833e2e00000001b3f4cfc000000006765180834800023a3547a68448561320352a1524000000000000000000000045b0351ce9f8eb22a1e43b000025460fe651f8849239b000000010c9800052e8065ca83221e186c0001204868515544439111262754d0628c163833b50dc973c7a40b4635e80000b9aa65117da03d12ff0e9d439682209c4073e0000000146e800008e864680001e931b8c00000001c65039016d83f8a9e423567a79087aaf03c160000d7686f157da143d178829f2ad6000075c000021824460bb111f71894996858280004ed6000000000000000000117d800000000d60000210a0000a9f88de000032d00000869a95c00000000000166100000001202a310000000011ad0cf700008a24a4d21a4276a2de0000000012c2a2e400008f5000000000000000000000012ee8000326c540400000000f40891811722c6000000007e597c954ee000036f04772d460000eec9d7e0000b0403b817dc2bdc986522200000000ad50849800057bc7c8400008350000515c0002ac820eaa5bc9e39cfe0000321d5ea20da00001f24be6a6e231de2d64259a58f00009c6cfdd96ca3ad88594af81769141205005da8d253a1e90f0597a4471cba193100e29212c0c16848b5a6cf37c03180f2ea8680bf619942ec00782068531d32a8b3e056650d00000f0046562170a358dd84bf65c755e394d447f49248ae506ad000044c8a7300000000887417400000ac06d08000000031ea00000001913223e000000014fd00008c1c05700000000000000008fa3e0a000066419eb446400010c28000000088651faaa8c3b7016f06dc255620f6000125a005b3d1c357800007074e0443511949ec60a32602554da78d2a7c000000000002fa2000125390571a86223d5c687ec066228353348240399031080000000492e4cf468e23dc49922d34c0a052615588a747230bbf274c7ce417f000000006ba80000f2a000009f8ad2000000004540000268800003d780001f6b0000000153917d351081f44acd1d9813b04d38a4080004baa5eccad680000000204d4c20202436c3e6c000297c0000000000000002e4c3c440000c0f3f7e0000b28800000001f2c013000000005f0c00016ab105000000002bea0000a1e945f80003e4429080001be815c8752c00000000a682ac40000000000003ac000294a00000000bdd13f357365ca54298000000097b52a68000000051845620000400a91c0eaf800000000000000000000006f140000000000000000000a801aee00010bb10b7464a1fd138f06
  | 73 => 0xddc44284668c86a45000009d2c00019ee0f509b794f380004b903134000000008d06900f940167408a852506a16040000000149a00001344ab9c15f0e13063e0000db0aab7429a66d400005090b1c0000a5693b32d7c10480000816336499653759b2b2da8552461a060416f48dcd0b788f621c897c8e730b8052f40000000234d2e48000132080001f28233c0001bde000049840000e4e000000013bc838f53343638af9030009d2469ca2aa216362600000000000000035ed0cf80000000314800004f6000000011200d192bec8474406a55d44dc704c7369d4f53b60000b65a1e12492120000027d60000000000026d800000000000000014680000d0b225d0000830c00025712d5e7820000249b296e9a3ced313fd2ad032b4fd081ad108216a107e810509d80570a34a84102b2000000003e132dc339400000000c06a98493e1fbd2acc28980000000248e6dbc54882c5242e6484c1a23b1217200006c000003750754876c911a00007984cca8a3e0cd67f4822280000000000005a80001ed283e40000af61910569d5a8ab3839b600013778000109627c00c8000000006cc0c650000563a97d40002b7f3472206c0000a831cf403fc14a9efa00009e4c67f80001792000000013de00004ce43b58f4b172a0001202000034ce73605e024dd3aee7aa4c370c5748946070baf24b3517c30b00000da455b857846120d1a4dec0000a7b01212c2809749452b0939e06ed888e00a440e42a54d8d188b3e8014a155d917f03c687b0526a4c200005948dc08e77267e6af09d782d14b447adc000187400004ac8f4c106600000ac400019b6401418f4bfa999200009cc8e3789c53dd0997c90226f230f6272423492c5524c7230000000015dc1ef48a40e0118007718d52000017ba3b887b1a51940a009e4d31a2ab1d92357cb4402a106ce00000001dec07da000000029a30000000102f8000131e00014b1a43b4dd4684c0000000182c21140001268000000014c6000000ce00004a007af0000018800015585252178400000002b820000fa50773000042ac0000000359a7bb916297e00000129009812e800007c200001f7c34366008000229a56e42374fdd0af8000081bc41609550000769ce5226570000000123c9443568c0000000000000008e480001b6c3c3094680002c2a25360000d5f81340b942cb0000238c193c86484109a7845ce3dacecb1e19343a25d417f92301ae68d8450200de164a8adc8600682000000000301e162db69588828966028e2879cff9961e049865495b18cf000009a300000eac00008d280000000484c9a48bb011e11bc600f0eb702ec3f584df8946800031841d38599a12e09f66968813060255f45670d16094e02ee404d18c9fab23d65ac0b070a5f50d426206b2a76c07ea8f4c1181ee02a8a26c84448b3c2cba7
  | 74 => 0x54900000fd51dde000000023bd215c0000000036e000073bc000028118da239c0000000000000000000bcf235064f8f708e4c000026043d894f400009c5cb428ae0062622287d99970512200001cf000000000000b1b800000003a5c000016b4b863cb4e9b9cb92e7a067496c1910000050d858b1a5520980000000026d000000000000ada35588f8100980000a9800008f280000fe4000148311c71b5a000035f84550000ae5c0000356000098ac000000031d09a047a10000022a92d80001d603ef699dc7d5216619ae6d68e38800000000000481000048f06b30892000000003a780b0a8ec0000000000000000000b0d80000000256a000118b80004c845388a0f80003648000000011ce1ac846d45a7834e000000001298000000083652e9ab4d194a582400000004c7e9fa000000000000410000000003f6e36ed4690b5d0000000093719a0555a45bca9f908e51c8013c23989510000000123f251215ac00000001714440a0000bf4800000005d500000886000000008a6187d000028a4d22288f0486000091f000000005e2d039a0972e388798000027f00004e5000022f907981898000087000002148000000000000000b6323df00007418de983231258000103f00003b8627703b500003396000015a01574f624ba4000085d000097e05f700000000a4540ea000005ce700c0000000000000000000c47288000000000dc2000030f561008a144ae9eb463305d40bbc402400000001efa0f14db123372146433cdfe80252a2ea2c0be01d28341cac48772ab22000000004438000000078c80768ebb2a824e449be2c3043e2a1080000000370e5a9cb5e9ea533c891a45c80d040b808de400019ff17a845380690f05232244ecd84a88e314c9c4400c800000000000f5ca8d7409c1300313800000002e34f1ea33c294a7694d6f9e5108142c614800000000000015508000000000000000000000000007e0000000003118000147708e40000b840000410e000120f000048fa42f00001b80000040ad13b00000ee8a65504588fd55c85e1cb148229320400000000000000000000002c1b00000000aff0000389e48dcee209ca1bfe720c000000004ae00000000000360e76f4bb9800011d0978cb3d035f264a94a8cf9069615a4000097ba227351200010fe000001d2892931a205a0db2431d5268652484054a06bf082f210a9e89419800005c21a600000e392d5200000000e690e000000c7d2a45011a9d440001ca200000000000040f0000000156ea05131708fc8000188418b8675127d1c2e465c1974000000000000000000000032b6269d10700000d6604d848c04484224945400000002cac0000f1ca86900000000000000000001d0857e85010da42fd400000000000937cedd00000a2a75cc0001fad00009f111769763000028b082a1
  | 75 => 0x800000004d081b2a1d55726000000025961a228da838a959808ea772c30d00b634243a7ca241cff08084c194da2bff415200012fb049f018052c0e6e8c3b007604fc92d9afa2cb80038000000000000000b980000505040bc91ca4c300000f8d5b5800000000340000000027205b1c8ad884317f2aed81a4986930f2814ceb9205c3f0a688c90a27a0000039f41c726b40b40b0353b6800000008cd4004974e0000000095700004fda00006d88f6400000000000117c23b87a2ccf99fd0531ea55834b941600000000d4c000000007ad14ffa4bd0000a43c00005d2404e000099312a00000657cf7c80005112402ce38000000008ce039180000000787480f00000000af953a200000000200034e80000000add4000131800004de84289d9121909d7400000000000980c0002c4b00008ea87030ba839aa7cf4000164b243008101a10ccd000094b9148000000004d78000140800004edc95ba29917880fccbdf000043341db0db5000011501abc6992b7835ae03a8a3390022aec6f0c132893011b012a1413037c00429378e479a1711681d5d2a01200087a01b09a401fa2c1438205b5071e2ed83cc04021d830eea5f60ddf1e9539361fbc2fc815318500604986944e2b1e472404d8824266848ac3c32a433c185be808118eb3e5a0078c8b167b259806c40001f0d4382000124a0000141cae8907500003ca6330448029080f7c9654a19a6dd0cd00af128c1b513b329b8cdcc029e1cd41178055a6432b9a1628b4f062f1ca45aa837f81c6479c186cdbf853348660e745b096f738843ad876800004af000007e78c0600000000fe628a7131c53900001a3400004ee8787800018d2819011c80000c4a0000c141969052475ec000212a2cd4292d31487e53a0e6665103031c40869b0477923722a2025308682bad1e1a7838f590a93000050a15dd931005b80000d841bef296422c15850fe703a03bdd5431b7a1674a8fd15c8192269e8a5134a94ae418897d0ced92d225940000000000027ac0000333800050a88004000073a00000000ef5945c00007cf8470000022060000078800039460000e568000066400006700000108074cc7a390ee30b6045075025472956a5485f2995609185b550489c4b147034f86bc9aeb0000a57d2d4955f100a00000001b9600a21bb453a013d183c000118a00000690409400000000000a7446cd86cc000000000000000000012c4352146f541002d108699dd12d2acc400000004e480000830911657f86570d2524593e2c55706f221f31e8c17d8eff0c9d4f1e01553f00ebf00006a4c0001b8650e643d8738000035d800000002aab3a56000067c891634c2000000021611ef2af44000000000000000a858000025086a419a0fee3a367e004b88000316ea3550a800000000000000009ef155a014c5cd2b370236
  | 76 => 0xc6fd00002a35425600004b32169520400001e800000000000005100004f3400009ae143800009c68fa4800000003970000000000001f1400004c20bc05c8400017b5264679a405e800047b00000471000000000000df48000022456bc5e60c9c0000667000000000000000105c00000e7a00015d586b430020000160013a00000000000000038620000c450d0b08b44780f2a25082f5404c810293304e9c75009111b55006c9538000000027ae000127e000000009280542126c10843c0450b81df0eec64bc6b694312f9622acc771f761d5ea7d800000000000849cc95a8760cfa19200000251031830d400009e85152a26400010fe41485be069b0b323c6070713458000009237a93c5a84d045a0000000198b22cea75400006fa00000000a82a5230000031cabf800000000000f4e983a164e0c780cf04c401868f28b8492e63aea542081c9a7322fa5510955272e0ce68664cd38463137652595949a0f323c7f0c1210f3900001280c1ba45637ee7c286b080000000a240fda98d025a809409f21d0b43f442547d08000000000008a78000477260f8cf380000000000113da4c500007ff15ba069e000000004b2918800005344000000043c80338afc22e20ad0421000000000ff40ebca820c9431320000e0b800000000000657800000004e80c2027fc00000b8078380005568785c000000008e26b9c2138ec42a6a0000f7e27e6274a1e14458829a3c080000b8622d119729da4000174a3fbe0000e982029529872615090f4e404819146558ff50e6e079c7d3a9880ea8000000002a823a2000058e2120222846605cf14bc45a800007fe8000000073ecd2b8ebe000000015cf0aab0000aa00e788de22c168b0505e000042800e54ac300001e364d7c7f41d3e578c00005b62905461e066832f8d7a000007713ef14062f5a0000db92c4807be98612f0000037600000000184b2ff600010cd8f5f0000000000000002d7600000000000000000014cf0e4f000000000000000530000005f5800000000000db880000000000000000000000922400028e200da3be88a113ed000098c8add80000064000054f09af00001990d2e0f8c253e0000c0c11210000492c0000000257e0000690844f25708fe4c6897c21372000130800000bd262895541a333b54a5d40000db4000072e8dd3a719434a00005291e6716a2000000016e142683a946b6079613b237586fd1ac05880000000020a300000000e3d94d9290a00000001efd4dc000004cf000045fc00000000dd10000021800000000f542ff119f80005656a1785d01b284c160000a500844537c5cfc8c48fa456fa0b34fc48000000000000000000000018e54d802b000004dc400000004586b03ce3323e21a960e08e5b800015e2012c53e0000471082b400000000000000098e00000e581af0df6
  | 77 => 0x70fc300e06bc872c057b0e0a32140088d330b1647b416d29a54b2658b4b8514af0000020c00000004a04000091f865544f86f5073a0441000000012519eb614ae00013ba0f2b2f648000000000050fc136c000000048d800005a18000220800009e58000119a621800000003e0200002ac800002ba3fc80000000000000000001c1127866d0c0001d2556d09918d6e095e3a54000000015630000b154000175809fe8604000000000000000000000000009ea800000000000000069c932a00005f404b3800040820000084946c00005e99175800007920fc92170000569491746c31b3c0ede9d24daa12c9229aa6f46ae00004cc400000001cc11b2c9354eb1a4641a8267650b12b594bd64cd8631157b00001d980002aa50000ac945061a8a0000000147ba3de000098ec52a831716a40000c83994a0000547c9c18c921a0c0000470800008fa9b98bff9e3c288cb1154da967100000000a7e1b8a00008ea000021a657585a80000292a000000005b800003d7a00000002a4041ce68dcf71277750100de12b08a971b809b7060680002644ac788460e5e000000000000000394e92e51a9800000002430706a835390c65602038491240a7c9c90900000000000000000003590000000021840ae87a80000000054ae23b8457800038a053192510dbe00008424cd800000000a9fc7c1287b13ce23b162b8000392400013ac00001c4a0d50d181c221a1a50bc0b8845302f019e40000000038e44004ef2a6c299413b9242000000000000791a851532e000078f20f8107202053dc800000620000de0000000007ec07c722602bf808a868f1f5a15120d70d928ba2343e0c48030a7c30414533d20595b500000000000000000003eb000000000000000100ea3394e8c3374ebb280e00000ccc9b7a36429183cb043106ee0000000146f000042d800000000a7600004a400000000000000009a200004c7294741b68000000095f4000000010da1800403000039aea3709751fc01aac6b80bf7a4610b3256e948e10a20000000078504b0503000014e580004bb8807c0000000000000000001d67482c7bc80000fb810980000000000001dc19454a6956f312a29c800016ce00000000000009d000025d835daa4a0b1800004c2000000002c791108c5300000000caa000029c686c803210d2495037a4ee413a32858b158d931ccf47fa000049ea9eb479600003c1800000007334000010000000000e5d8f1952e200010f6803a4168000070925b019360000000211412140609590848958083c91151229100000000d5d12e10000a11417791b8000000004ab996d2f7200000000c14334457754f1206601fa42d8052a12657f05b040000000153a00002f88045000004ac0ec9a350ab4101463a992928b600000002490000000006db1bf04c0c755400000000e4
  | 78 => 0x649883ca39a0e141819524000000006de4000091a158e0000000184656d89f1d1b80000000000012b38d2d0000000000020960000aa8d4651f95288235495e6171a1e128c201eb18c00000000000029c154f223287568cc900003ef40000e9b01743a44000059f143a77793c300f7356e03cc53e80004956806c3be1f5055a42bd42661d380000b0fd2ec15d73ca40000cbc804a2a6c6fa8c718231000004288d0081458825f10537000041d85ddc000180500001d200001ab300003a2000012190000000037e80001ffc00000000000007000000002b5a3cfc00004e6848200001038c6e8752418a1f194fd972a0db655913f28cfa00009914fd1864d19a0818400c00933d76000014da656041e000000000000000000000000001ec49c58866000027ea9ca4fe48e6300000000a5b18aa0206a0300002582386a81a127013d31a1c000000028bc35086fcd5e6851a0ca0ad4c36d0278043a780cb8b2281363c82fcb1614100d32411835187403b7668403d61b7c0000000000000002e5694e915723f148e46b60f7520571c2202b12802142028c90887118000000014d400028701fd8b0d40000ed4470e000000029420000000000014ed16c693e400016723066ad0d57e8000105c1f854ec8abd309c0000e3a1d8833f4000153a15b0000081dd4200f9d000000005d380000000a3c4f09212400000000b38027a31564990c9e80004e9e472c5740000125a000000000000000471889f0000000058011181afe3dc85d8412d000007bc64892dda01047b2609c00018a40e340000bec8bb600004e74967a94530fc251897224bc4fa0b0394671afc2e304804c9ba0d83d4213c14fc071d2ff05f1458529ce1ace5871443871000009d6835b20e9000000000001b4e000000000000fb10000294502c00000000000000000000000a63806d20cc52f2a424000000000003cecca88ab8217e84cceff80000ad8000073e234500005fa800018e52fe65d48de82b5708700090c18a111000041893580563094ca604000092b286a0000000295d00000684f75a62e56f20598768999100002cac0000000051c072cf1b1c3c45985c8041d0000000000002891a5134b06d10b1506d419fc000000024be4062000000002cc20542670c0da90a1396ac30e4f9c4658a6256cdb40000501a35bd5000000025400000001d410bfc4370000000000001d7d3b989ac16da9ef496aa0480000aba15998000000014f52d224e700000ae95c88dd2000000000000364535e5e889d81d90568ea18471a000000008be10bd803d030000005ab9f8d00003d144df000031d431742cb0ea72700aeb918e159907368ff1083033d20506f84b6f15fa4bb43808503a2f730a280b84900c5633f06f391d311ac29226af4225800027a8185075d07fd000066401c51d1223447fd141
  | 79 => 0x774a60e011c1ed022b8000219650f02e7981f11d2788d0ba8c644d0c0c650ab23bf0000631412a925800006c58000129557902be85760ecf40785c5c1130000000000007a9259e3fdc8cf8ef0220d000000002151377293a00014cea17e26424290b8f9e38304a1018c4380000000000078f800034d0526d03f8000000000008a500000000a0540000939000000012ab85be01a86930d8a251b000000012662682000000004d3000009927df400000004cf0a1d4bc18000000084e40001e6500000000000000000000001276909f3a123110ec50a475358b0e529e09c33c62150c12f800003e6000092c8000075853c81ad8b234b3e20640878000000000000000000000000002428c8a00006678266800000003b2c553919d2e327d8d43e1d943bb488540000bbb192e000000026db123c0000e7513ec0000000000029c5000092a400023c92c106b8400000002c242fd845e800000000a94b678000048a0000dd4800007f61f080000000000000007a220204bc43c8800004d111da376456f800008a400002f70f0c3dea000145b8ef10fce0000b1f2723000000000000392000000005f4800050aa96fc000000000002d4c28a241d4a123a1d4b610fb440600000000b02000065b106e84673bee1cc4b1d87c81c3a1a1d05b1476000044dc4ea80000000000000000002792aef143b8f9c3ed22bc0000240834d25ab8c61a4c00b6226580000280380800000001e6a00008060b469ad541bc1d8153d9b9e31f632f8d50011621ceaa10fed09c81a907c74e45079400003d40b9722d300d27bc0000170f00d6264c00008652c8a3ccc573a52d352487189c08bdf498297492cc00003b9a0681269110a0000000154d02de000038b89ec821e24668dd40000000528600000000cbc097032b92b316df000087ad146234e000031a0000285d567c000000000001eb87b940000e5a0a60364cbe300000000000095d8000000000000000ba117a4059126200000000000000000000000496808380000000000000027130000373cd6a23c608020000b85900729d4000000000000000aa60ae10000577416140000eee0000af4000000004a28000015f87463a20000000013430000000067e0000000042f800000001d5c5b30f4b18dc45900260b0d85a7549e24503681f91210e000000024303eee000150b80003e8e292135f27a13e5401192c90000005c49ac6278000000000002b900001ec05e38432000034fa17142ce16e24e5e178c00000000590026427a8c79317823f117794f74d56afd0b1f83bc24f2001482eabb1241a5dbc9cb2b19042267a80000b7c05083b08deca555299aad6c00027cb155eaa98e0727e13670390c0398000000000000002a224ea6000116904393c560000efe8000000000009fc000000000000000000000
  | 80 => 0x154ae8000019550000a6ac0001af6000011b49f29882490400006828d4c000000014b48000518800005659b1738ea632400026d900005da052b0000133073240aa8540000009390639347447e0000000000000008e015b509d251d248f000000000000300931800fb4e7400012578000101245583a98a6818ce4dd80ee8000032200008af800044d26108ca496d80cc0334419c99f52316652cf7a0a601e34003d4c8a7f515f60dd560b08f428e42eb8f3598381e2a170c4a528fa0000497c00012a4251e225556190741c5a8a78000072102660000ecb8fde036eacb556d0bba552c00000001b043c8619f950c0a160fbe790547f00000000817834a000000000000000000050ae9fb0f8f00004ecc20cc0000000449a00007c506ce0c2019ecc8ea81f06a200000000000000090b544a22922c9c8d8103399ed363a8e3955800000000217c0000a06370894e1232aa2f25385cd937c000000002f5cd2a23934cba1c895448efd507296d0a4185c10ae6363ca86242b33d22ad056c0310000011409dda79738483e9452d9acf3d24ab28887800057d0ac8021f8b813830436c3c4a6203b0800007a5107a0372100c38913f001820000000169600000000aff95e9433c35410d0a1ea2d9a000118c000000001b9072c82fa26e400000000022000000000002bbd53fa7e60000122c3c360000000297210e87368f8621e5442204c44f000000f2a9fc0fc41ff154846f240000b980000000122029e800007bd8000145a3b24a8ecfe085483a3836a4000177603ae00007b7a41c00007604000000012821d04af58ac500009fbc0000eea065a0fac00009624d441ff881e0000284834c43e900002d30ab80a700e2c17545b65533800000000001154a2d954260b382c30000034861400490000549c545084d07e213e628b800026714b84081d1f4aab2316833c4ddd0c7b00000001589a3340000023c0001625273e0000fc5104f0000a0640000000000086c4f88a88b495c9e952e70fca1794a8293a1000005d433180002c070000000027412c41d48a3b400001871476000000002b90000688936380000000000094e90580000089cdc805050000a28400000001e100000d2929614312000000021362f2e0000000237439c00e6934f8a6600002a70000053b000004b14bc000012e009a934dab7131d2a998f4080001bb80b5000000cd3bc200000000000000000013b2987624fe0a2c00025b80d847bdc1db03c8000000011a59b003cf2000000001e000000b64000216e42900000000000000000000d391ca616729c10000214738f84e3440180000448000098a13462ee89ae80000233000099c058d000042c684b4345800001b06bc09a6800018524b2c3548000107649d80000aa111802e1c26180000d5c3de1511a493114c09c04671f023a9a09a00
  | 81 => 0xfb10000000027383541ba41cc8000000000001404000000026fc000054e5285283d00001da55b3000000001f340000000508e4ca111a23942e1c2da0abe8bd954dc0bac66c029d072237b4bcf0e3f0cc20c4485d280107485024e4b91ea07020000c1da08f4d4e0ffcaca18494232885d20d233a1f2e5a5c6fe278029b6954537a800043a812107360ac34576000000023f627e8771558290cd2b508284628a8214c0a82106080b6743ac0000df8855725c4000074a0000373e99a0000000018e463e0c972bdf2ada04202aa0000156e7b3855d00003abc9c00d47000000000000c3e03c43892abd94b7000000008d048f1063b0000a92400000000f8606d8dac847b00000000b910000000000000000000000000010aa949200000da0f6497020fd00318ecf00001422a0e09f180001a7013e80001739585e00000000000494266dc28d8000142a9e0c23289ff54f000000000cb800007b40b0080000d70639924aa91407f207891e6a82734e289e92471fc73ffc78ec0000c04000019695df0d121be853a4894069c0000367c1621bac21041849519000023528d18608abd70e269decdf31dea3dac126d1eb1f4d000000008b18e7904c0296950e261d000068a8000027502d07e0400000000cf84a48f1300001ce21c455e799270c14292544d1ec02a7632c4000166b2da0518c559000000001ce08d229a700001cec000041446860000d27800036fa214c000231e0000a05d00907710000703d538a31b11042b300000f7523b068ec403800000003ec80000000000002ec653211a1e301e0000007ca000000000000000000000000000c39446e000044f0000000800000000db75898000158a9f3635f0369c4d69f2f52f6a940bdea73600000b54f14177c000088b0fae17710000000082804323b360000000097401f2000140d8000000000000000000000000010c68000000005f80000eb10000a2d1333800023fa62400000544126c72a0cec22674eae0000ca1195a013c8db86150db5167609b8fc984df14a833685dc91312ba4000010a96693fba830130d129816e893446c08fd4000047d0b4086361cca35f0000037b000000008a1972d4d4a5bc41c39cf2000000015621da256d20000b10000053bc88f8000000025f02168dbb926a3d506a40b268000025c4d60f6f8e9556bc1eb92218d16583cb09883e97bf2674969400012e33f288e0c1879abe25902d2c00000003b82000000000000ccc7ce00420c07585600013ad95e60000000000000000cac00016250000440200000000000000000000808015000000011a60000000000011fd80000000998cc84179d3ff29cc00000f9200004ac0000290311d46044e470972231e00010e60000361c755c6131653265a7c000000000000000007d800004416000097ca5e606443c10b1901960
  | 82 => 0x546c000000000001e7a0000a421f9e3a4081100001da425ea73487e6a41200009f5081b80000000000000016d14306a074c120000000000014e009190000b09000000000000896c00000000000a7b54ce18c12c8e4070de30dca1dc25b8cd2f9cb329e000004de038d00002244026ac02279400011b7917800ee9e6c93a00000438000000000000000ac58000133538c881308cca0be4294000117a8244255aafc4a868d88518a871007320c12cd871309e889b00f26290c00002e63e8c0000d48800016ec5710ca9a2fc3e407a44ead22094f6c0000d56a874337e020811b16b93d121b0c00027a8000002544be8d542a8c29dc11580001466a6dd51818fd42743fb400021770000000080400000000914d5100000070800003cf1019000017912ec80004f8c16e4e57174c45dc0000691847f00006868d37800054baaba400000002b0200013a62940509221a808d25b915ca38c000009334c385e90a27a8ea145e0000ac506ab44080ba478b00000faa16508440000000008580a6000030e67ee49cd1e9a000000011b1a2ec2f00a2342bb00001eb4000000024601bbc03b000026f03ad2825400000002b7a07a00000000092000000000000000068fd1eea6ec236079190130b9424c6a80c8ec8b3000003f24c1180000000491890a95b848f491710fc840d4b3276312bb8a20238633acb790c7154887d20e1a0ae9294c7b70c809588223256b862a141322fc69d080c01da1c544ef14dcab45111889e026395e02da46f9cbf7171546fa1a7cfd90f033dd862d48c708540c849b1815908d03cee0000d0e00000dfc564c20f800007f4adc127f84173ce26540fff8817400400006d900005158877000023520000a04000000000000000000012fe000063b0000282b07f00000e2ca879001a9e10f2ca8035090000048716660000afcd5d200001f5221dc684887200000000aa11feb38821184273061c0b0e0000b6e93ee41f400000000000563000001da9f4219dc0000a5d0fc500008c8c000000000000020b098d97282874bc8e680000000480d07984cf4daaa29400000004e1400000001562000000000dd800000000000000000042d00000000000031e0a3e0b3b80004d9a6d0141e17572a242b08e6c84d2450621380000e1432e8229000000000000249c0002a70510200013cea491231a9df0b19908052b419b0c41ab4c50267808a0e0000000000000000b033fa87760db4992407a68bf400000000000a89913786b53482000000023c441fe3e4c0001a812556a1641d5800057b42ec400000001acc000000000000000000000014d6318e0000000000055821f64ca00000000075183eeac323b342a653900000004039bc00029fe4c2aa090f6c27fd47c60a905e8000030de1cd00000000000000000000418000000002c6800000003ad4
  | 83 => 0x841a755506e2d08f53800040aaa09400000001a3e7d30b411b9320fe8328c4714bd136a00007048000496e000123400003a9c0000f838ed600000000000192c205a2e940000000000076ac481800000000000000000000000000cc3a0d743e4056cc359c10000000000001cca1430b144ea12b8c523600000001c2d000000000000000453622883c200004aca000000000000fb835d4a450ba924ca203c00001eb01886b08e7c153a0000a75028f0000000090a47d127bf337685e800012784fd400002e6800022f4369897685c9401286f00000dba2d5a0c3524f03ee000000000000158000062a4af400001c702768b5a155b00004d2462c0000257c0d3017a80001366ad7000026fe0e7e2fc0000047c11340f9487c8df800007d7c76d800054b200d0000194d000000015760000000053ec00000000000000000000001f9c8ad000009420000a2e02629b6044bc2790abd25365466448c625a5a849ae5f9c8f81d0e00000000da80c1500001cf00001ce32a86160000000002b4400014f4a5060000000000000004e307ab8a45800013e80000aed000000006708edc98ce00002de40000b2121e449986e08000000071acd548000566ca41c0001ebf40f20660ced03864c8035a44a495f94f9a00008e20a3100002a0400003060000980800000005248a7740002698000058d15a08ec0000028acf8e174355b2452cd2b055c4a94000076f96eb45d098f0226a34902fe661113a0f5d06800000994995751909a38009061931b07528295a3fe46bc2c7c0001cec340613e0d0609f9247649c022d9024000065943c519e1000051753ff956a32fea7e80ca12f0518471482bc1d3900000000447000000000000f55800048920000d04000000004181392832f0000000000021e9421c1408829000037547990000000009ba35c40001e55132825f8b7497370000000000000000000000000009920000a4c8aa717e22fec34dccb328f0000000005510000000073a400007a4316c068cd0023362dac93c8cce91764f1c454914e0b7102d40000c3c000045302fa8ddd9935429c3be04b5218000000000c90145f41380000000000000000888776000000000000e710000202c074c78b9c7f0000a51caf5000000008868e238cba00000000da69d7d402c9ec80000e4000000000000000006e800005fe86920bda26dc26a08fe0a7e000000016fd570e423d5d3891100006cb4b9da4014fdc00014a79abb0b903cd11f6831d000000000000dcd41e8560c12e20bd291c65acfeb864943b6a9542a716fc43220000fb895220f4a29d51ea8cb4000046cce8123661e8670754ac82a230c49c34d1203e93094501c37b95e30f180d4096c981e0d221cc80000000527885808cf020e14c89591036000000004f6c0002a921a7600005438000000000000000000
  | 84 => 0x588485455ee1e7a014674b83bf8000000028fc2eb000026d000004f2982b4278b0b89d70b5e000000000002128000027505e98000000055545d680000b84476839680001188000115390c90000720800026112b2210a48358d4643c62d0492680000eb652714d69e5f2ba27624000000026569a00000106d00002ef425905a242b47f089118a7800006dd882d9ba21f7295605d59c2747486c2c6e800000000a44d1b692e70e480000000000002828ffc000000000000000f9200004e060000000000000006e300a89fbc000062c860d00000000862045d000000000000aca80000000000000000001fccab4409aaa600000000116480000fae0000000000000009f6c2c90000123600000000000000000000000fbb00003c7458691c00000544c6ea2b820dba437800000000000575420880005862000123580001e2838280000deb117e0cf067a00000000000136198f3523c7670a3e00000a1497dc0000000076800002550f270000000000599962e6200003de0df11a7e7a347720ad1552800000000e48098c1db4c080552133a56382a68110588c00005bf0d6e0000000030f00000000743000006084cda0000a5525b102b42bd071980002a4216b07782c5a50980da800008590000000048086c534045b200000000169220600000000457000009ee0000517a6dac00004a32dec0a215951b781ee02d7d4329c6d000000014ec0f8b48620000000000000006f5c00029c2544a0f48a2502f300000000a9e2a9e09da0001135204a484a9ab0000088310f015e8cb2288a00004ea10a08d8442a69618d7e8525000041f0c5f00004c2c9d781e122bd301e33153cb057d4ce413388fb0e1a4c4698d546a144c26d80000c2f888d29882028d6e811c4c0881f40000d8b00001a300000000329099a889c0b620f1a27f496b0000421600010ee8fa300006b58000000000000000fd418e20000229466582770000a4f40002acc0000953c331000000007db8427955e00000000000023a0000a86d5f10000000051cc51205b20000688129dab110000851400000004b42000059aa8f34f5e000048f81430e1a73111fba118109400007fb25f900003bac0001a9b0b6e961ce348e1e496a000076507fb1dda0000b54000000000000dd1aa9c12f211704bd068342f0385400000000000000000000000000a16cd3807de16aa78f8148217322e4894d09100003c6a903d16b965f111077c44408d2c1aec440444200bf1a5e0c249218000000000013e98000000000008c20fad00005124000000038a20000d14291a000000000000169052e0000000000036cc4ee4e80215905f8962400005394f7659bc000000049fa000136100003f447708000103e0000000000021a207fc00009d59a0a0000451002c00000000a4bc0000000122a000000026960000166
  | 85 => 0xe0845800039bc000000000000000694d4021b530000a33d3c4852e4d702b3414292450000a78c000000036587cf00000000391682895939ee7000093953fb800007b01c9c1861904518286a00000000000024d49db045f0eb4000137b80000000000000020a70000000000000000ece0000eb087a12fe89ba41a389c633bc00005c1000000008ba4000293e2a007a90feda7b838769b7d384a9a82ab29c7c0a5130c0e8e1fdcd95171b4cbc7340748167c25664e108f62809475681e8f37a23b50649130bab1db105ec4b79046a8501878379c31f843305a035fc38b256351302c48c992560547c00005f41e830000000124013a9000000008f224ee000027a8b4000000000397c0000c504560a2880000000000054f527195dc232e39fc47c93e737f828895fc800006cc000013b06072e4a000000016d7000099ac00000000000981c0000fd1000000000000000000033b135f8000000063dc0000000000054680000000000000012c6800000000000eac8b7d284e2b388f991d500004c2ce301d4c2ad20000000000003e00000000217000004fa82c0904200007a180000ec800005e6c0000c6f3a4c0000e5aa1a300000000000000007c80000eeb0000000000014ee000000000000d3300000e180b48000000048f661955df8137000000000001911011074f08f700000000173014b000051e800000002487000031f40002a4c17e20000f640dab00002344000000041ea7590000000000000000f748e78000040ec00000002c3e000000011bb0fda00006408e6843280000f05131a00006a88000215d284c000000019972d78062560e863750de00011968e890000a44457b800021f44ad000014472bf672853f981a6000000011079b0d26c60fd000e1fbe19986fb077c838023683e645271ec155bc734c66b0000347020b529a80b712505114ff800f25770715ccd421ab2f221f3c0001459084a30140001cfd346447405ab0c193b6c0ad41031918229227b4abf1f872d060168c8a04ea487a28711c8a9f3414c61350e29a422c18863812d913c3a342f88a770456000000003cd80004f4e97f15dc9c9609a677d43d329da14c68af959fa6b60000000000013a1445200013ee80004dfa523cd8799a33c2a0000a7a8a8f305828680000000000049f81d400003a44646cd58000000000fa000027350978000000006c453e8505c000000000009c9800000000000ae400001b05000049209770ba3000000000000000514c000000025d0227e8f9463f99f400003d651ed22b53a48403807f118100000000f5c000000008fb83dd00003ae20000000000000000000a0602ad1736a83400000002db81074a01018d00004d1400013e810f60000c041c1200004f10eae113a3d467cdcb3414cb00003dc496388c257280000000055e00009578201000
  | 86 => 0x600ed000010ef05a3461a6f888caa4c8328c00010b684434cf247982e3aa7644c809353520000305e570028580000000000000000002aea0000000252b2522525400004d9507e00005f0081100008278bcc269700002fdcdeaa7be21701b615991b701fc200011248000000000000001e82000000000000c1b21ee1f1000000000dd4726492e800029c250f53968a101cc010f0016166e00de90e84b625422af00000000000010b0061100a0089023c00000002ae50000055120c08da4f5c00000002559035836fc00019a513124310000279031e4826c000000012f69b20487a0ba4b40793c000000013c48ab13fc9b9c48dcafc0000081e00008608d0387a700a85250020000000000000000002a1bc200000001c9e335c91188c9812f38a616b539c93641d467ad53239e4c109a32a009e154d41aaa49d5f38f1c0e407d64d528f6c3b800000c7014e7000085f0a9690ff2d7400004608000151a00010ec86e60000000000000000000000024f0000089c73d0000196000005edce8fa63304d672f010fa9f5027c966cdfd0000446c0000c4a1d4756608e3cf8fa88c178e1358000000000000000bc0896f370a46a88b7204600007e112f52224386c7c986d1252908a20f0400000001898000079280000000000000000000000000000000001f10000000000522e0a0000000000000000000e93834b0c60000095eaa1510160e7c1378000000000000001ce800000000bcc800000007a402438000311286f40001ead41247d740678000000030b858880000000000068191db000000000000000000095406f900000be466295b0827100000e8c00000000000708ca3d000054a4000149f84de0000000089a80000b66882085818fe000041355d9057e0c026c0d0f80dd53ea404340000b152130612133e000051dc06f0000200b4dce74200000000000000013e2915d117c0000f3d80000ff8230d192000000006ba00000000000000012f2abef126e000000000000000000014e22de1bbe8e740000647358c000106100cc0000a524da41e9400005928cd980000000442000000000000000022c0885000090e000000003dfe0000eda8000000000000000000000038f48eba5161d18678cbbd86a509c80000a29159b468e551c96d80000ef207fc36b80000000000156aa759436006bc000030440ca26080000000491839b883480001fe24c7497286c9249c00012bd292c1a9c979c000242349649ee921c8aff21de3cf875a0000000096acffd969a230c195c5a39ecc00008d3c091844a25344820368a50507a2380cd0c951905e808b0359000032460000000000000000000ace8000462c2e2800003e000006fd87858f0200000000000281c22180000000000049104c209429c880000389800013980656360c0001d48000073b800000002dd047
  | 87 => 0xdf80001105000000013ed13d837b40000000000000000000000198324180000d50aa370000098d52087f832e2224cd7215ed40b269f0930000000000001293973e000070c95bda0e44b140000ff18000265867249081d1941cc000105c961a3e9c8084000201131aa0000000000000001a680001c48202a1fe4d1f0da83f9c34a0671a4a6556248c87188f6829b46c404a68658000000004c182bb000000000000000327e000000008d9074c0710bbf8ec72e5e98480001b913a52909ce610e0f13564ff929f975302de3a3c05c8e212bb2a4d800022d05250a18c00022260000a624d85039c2a12653c779800057ea00000000abb3f4a9f0132228d056348d4406b08f003fc5528000000000000000050aae6000047e8000060900d0345c000000000003af400025040000a8500000000416e0b6ca5a886c29de0000000000050045d24000000000000000000000000000000845247332725ee075586a24f4ca3600002158101c4264d3d0ad5135067ed12e1c15569e5d6509f9e683d2e707939f00000000918d0e9800031c2a9a4000000008ec5e18db2000048423df0c171eda46b200005f6107e0bbe00011529e48000056e43f7059154a213f124e1ab51c163e5400016f500009a240000000000000000000000540a4d2cb3f8000454c65054a81b7456c04b70bf32bfb0028336c37e0eda51f80000913837f063609253c415bc242c1bd9286190e0000574c9998000000000000002aa42236000000000000000aaf067b25f1336800005989360259a000000007d003f8a56cdd3138a000000000000000000000000002b7c46ee3348ef78000000069d80000cf22f3400000001d350000000000025210000000000000000bb8000000021b535a20000984800031fe00005b71ae22d0804ed2270e6237a47ac03498b8c0bcc6b48433920703821a34ba803cf46802494dd9275f3970870d1258000329838a47540a2a06886178dc912ac55c400011e10000000000290558613415e1f61582000000000000d61800000001288bf09843000000000000000000000005d98000000000014a300000000aad8b9187f54548000000000000000000000026bc00009b5000003aa1d44000023217fc02e41c180001df308a85d1ce6e06c621da0ab03b0889c578210708d6ac4f4c0200000002a650000000000022450c8689b09010000000000010400000213600011c5a25247309e1c663a9334e9a5715208ab9d46ba3fe401980001c944e080001e1a2cca4068e158f2600002f6c0000cbd0000000112625ad0000a27d3541ff71ffe2dd48db8000513c0a500001c89000071100001f820000605c72d81b01d0470dc000217f1dcc8eb8208225a44364a504629dd218ee1d714de2c12442400000001c1f000095d867529201b7a3a58000000000002f2cd8c29
  | 88 => 0x59005960159019807c4bae10dc00000301c6a00012179d36000000000001fc50000000000008db2c8207c53a29933216ab0b0ba780002faa000000008730000983c00000000000a64908e0b10320a9f9cdad88c803700d8c62d1a4b2782a8e0adb25de04687fe15f59e841eee69154d005f433f2602d2d190ea103e2fd14499e0f2aca93707cb0ff00ca69a802a8800000003f30000000000000000c4e8dc5372e000052ea7c80000045c00008263b0a84e093a800043406974000155000001e2c000000000006d58000000000000000000248a1a6a97bc000000000006db44a91b9d1618b09c00004e205ca9cac00011f20000381000000004ca4000137a135627906400ff692a940ea058917f93f100007b643979d1400006ad000000000000aa0400019fc0a8480ac0000fc20000a958c1922505272000000180635702917c0000f32156011ad56380002a4c69fd3da957700007034953000000000000000000019b251c03be9ad0489a0d182170000148200000000cbb571c00000000728053200000001cc5000018e8fba000000006714e0b0dc314ce24bca99868f03684630ba683f14392499c4bb9429166e00009f08a730000000000000004cfe56c94310cac2120abf13570000122400008b880000000000036a92d0244000000000fd8316000000001b3b000000000000000000000000001d0d00000000bbe800026807cd40e600002a6e00000000000000000001230000443800013e101500c6483180000cc000007e3c000000000008d502c19f9200000000a72959e2b6849bccf300001fc6a1f44481638505417d40000000092e0000a870ac6560400010e01020013e94bc3b7128b01c84e653ec9dc70ec80000b2d0e4b000038802d2800000002ce0000000011a43460c150000252e00000001f4500006bdc000060f3e1674540001f564d6441c87970d2400000000000000000000000bb71a5900000a18000000021cc000000003034eea6d5cf6110d7064e2850cb399a947327dd54bb8e842e8a60385c306c85672000122c27b70000000000005552f98000038209212bc8011c90305e81fb85bf88968042178600000001738000000012940000557251e04f498c8223c6a7864024a552cc1bb0000056a4f9c4590a928be41f9077b813309d31dc071a8f588fd32244015c2789ac5103896408ef16ef150c5e8c1951ced58a03f1c60e977213ba00002fe9d3434ee7ec4fee00000000568400021c70000a5555f4800000000000340851642b639cc0000000451a00000000449000032d8cbf279c33e01ae80001962379e6991201800019c49fd08d085af48de00014032c0633020231304a539000008a071797f10c5c5eb8579a40e0df600000000fb61b221838000000010fc0000000113600000000fea80003f4000000001816243c6
  | 89 => 0x166d13ee000000023900000088148e9010000000008aa80000ec4455123e0000209c27ec52993ff000000000000bd61df87b48000239715926b68b1c8b241e9226d0d6096182f5600000002adb4d6a29e400012242314905400000002cb6488500d284f00005e9c64100002090ae714f8a0080000000028600000000000000020e128c80000000000000007db46ad033f2224a59c0001c7948360001591833800000000d551004000010ec379000000006e553f580000000000000022e10000095800000f500006b255c7837234a07f4487080000000573800013be000000007b906c7000023940000000000005953e480001a780000000297335045e70647a83b4d0e6ac91471f991b0a28d959d273c390a74e8fe59f092d1ea8ac8618000220c000000001c53cfa0000885800052740000000298300000000e6718d9548c61140000000193400000000488154aa2e800003ec1b96347464aa55a1cc25300819000000000000000000000000000f400670000026fc000000000000000d461daf4fc43c190d70a921d341274000239500005f7c0001a6053642edc0000079169828215b3800057102ddc01417ed0000add86c6800000000000000000031f800013cc199b4d9c000053f000000009b48000000000e2302012528a01636624d1ce000010ac2e7c000000015ba00013740000113a6a5cb5c2c47000000013aa072500000000471800000000000117a4ef3ea8367513ca5bc52a601300b984ba03ee0f74d639e495442000000000002f2a4bace14800026820001038230604f60000f428000000000000000afc380e3ac05642a6b0000922d031986800003640379800000006c887898000445c8c88a962c2d270c8954000284a0000387c0000000000000000000000000000000e4a4e4543cb0e8000000055f000000000000000000001bd2c3700006f08ed1a45a0000304c00000000000a94c0002957000046711588a982204000084f000055162c6435e8e1b33a237c095280000000546000000000000000107f000000006368000000034fc000000000000000000146617483a3a00004281fa71024010c00014dd397a0000e6a00000ad65a9811d98bb00000000b4e985d00005d18d2d8
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x8791530c440042d93906220021e4cc83110010f2264188800853975c8440042cd39e4220021665cf2110010b66ed90880085b176c8440042d8bae4220021cc5d72110010b64e7908800879273c8440042c939e4220021e45cf2110010b60e790880087a262c8440043d0b1642200216c9c62110010a76ea90880084ba76084400425cbb04220021e84842110010b66ec10880086b27608440042d8bb04220021ac5d82110010b64e610880085b07308440042d93904220021e89c82110010f46c410880087a06208440043d12904220021e85482110010f446410880087a1320844004272392c318021555d4318c010c72ca20460086b2611023004358b088118021e40c4408c0108eee3b2a60086ab6210130043543108098021acd84404c010d60c2202600846e72d943004236b96ca180210f9d0650c01087ae8328600846e721943004236b90ca180219394d620c010c9aa6b106008555750c43004362b1062180218e594400c010e32a620060086aa621003004354b108018021ac984400c010f206220060084d47358620042b2ba843100218e5944088010d64c220440086b16110220043d010881100211ddc76548010d36c62024008698631012004359b088090021ac18440480108bce7b28400845d73d94200421f3a0ca100210f5d065080108bce6328400845d731942004326b1ca4100219358d5208010acaea10840086c563084200431cb288010021a698c4008010d32c620040087295210020043593088010021e80844008010c6acb3262008635655931004273394c7880211d5d463c40109ace731620084757518b10042d8bb08188021ac5d840c4010e62ca20620086b26310310043583188188021ac98840c4010d60c4206200847576946100431dba2cb080218e1d165840108f2ea32420084797694610042f13966308021749cf2184010970e032220084ba76901100431db2c80880218ed944044010d36c62022008698631011004355b108088021aa1884044010c6ecbb22200863765191100432bb2ec6880211d5d663440109ace731a20084e67298d100432bb28c688021a5d906344010d28c831a200866765d89100436231ec4880211d5d662440109ace731220084e6729891004333b28c488021a9d906244010d48c831220086c7631891004362318c4880219518e5044010cc8c528220084b676901100431bb2c8088021a518e4044010d48c520220084b676101100431bb288088021a518c4044010d48c420220086b360101100431db2ec8880211e5d66444010974e9322200863b65191100432db2ec688021a61936344010cb6ca31a20086986418d1004335b2ec488021aa1936244010cd6ca31220086a8641891004364318c488021b418f6144010dc0c5b0a200847a76945100431c324a288021ac1925144010
  | 1 => 0x400428eb98ca200214b9c86510010a5ae4328800853a70194400421f3b0a6200210f5d85310010a5ce4298800852d7214c400421f3b0a4200210f5d85210010a3ce6290800851d73148400431a32ac220021651cd6110010b48e4b08800843d7694440042d339662200216c5c3311001096aec1888008535750c440042cb39e42200216c5c3211001096aec108800853575084400429cbacc0200218e59660100108f6ecaa0800863965d0c40042d938e86200216c5c74310010c72caa1880085b37150c40042d838a86200218e5974210010b64e3a1080085b171d08400431cb2a84200216cdc54210010b60e2a10800847b7558440042e839ac220021781c96110010a72e9288800853975d04400431cb2c82200214edd54110010b36e6a0880085987350440042d5b9282200216a1c94110010c72ca20880085e272cc440043c9a186220021e410c3110010ba4e790880087a34208440043d021042200216c9c66510010a74e3328800873271994400431dbb2ca200214e9d76310010a72ebb18800863965d8c40042d938ec6200216c5c76310010c72cab1880085b37158c40042d838ac6200214e9d46310010a72ea31880085aa7218c40042d4b90c6200216c9c46310010b62e231880084b97614c400438ca98a6200216a9c85310010b52e4298800853a75d88400429cbaec4200218e5976210010b64e3b1080085b171d88400431cb2ac4200216cdc56210010b60e2b10800853a75188400429cba8c420021669cc6210010b32e631080085b27118840042d8b88c4200212e5d85210010b34e62908008599731484004394a90a4200216c9c73210010b62e399080085b2718c840042d8b8c64200214edd53210010a70ea99080085b3714c840042d838a64200214e9d43210010a72ea1908008789320c8400429cbaec2200218e5966110010b62ed30880086b3659844004358b2cc2200216c9ce6110010b64e5308800853b7558440042cdb9ac220021661cd6110010b56e4b0880085a8725844004359bb2c2200216cdd56110010e66eab0880087937358440042d839ac220021e41cd6110010b20e6b0880087a37258440042d8392c220021e81c96110010b40e4b08800853a75184400431cb28c220021669cc6110010b32e630880085aa7218440042d4b90c2200216c9c46110010a72ed288800863976944400429cbae62200216a9cb3110010b52e598880085b376cc440042d8bb662200216c5d73110010e62eb988800879263cc440043c8b1e62200216c9cb3110010f44e598880085a272cc440043d0b9662200216c9c63110010a76ea98880084ba760c4400425cbb06220021e44c43110010b66ec18880086b2760c440042d8bb06220021ac5d83110010b64e61888008792730c440043c9b186220021e418c3110010f24a618880
  | 2 => 0xc0a9021171cd60548108deeca90a40862d645485204326b1aa429021879926314810c3ac9318a40861e6458c520430eb22c6290218b5926214810c9ac7310a40863564984520432cb1cc029021179cc65d08108bae632e840847575987420426a39ac3a1021179cc65908108bae632c840847975982420422fb9acaa1021171cd65508108bce632a840845d73195420423aba8c2a10218d55061508108f2ea302840866952181420422f398ca21021175cc65108108ece2328840843e74197320421eba0cb990211d5d661cc81087ce832c640843d74196320423abacc3190210fdd1654c810878e8b2a640843e74195320421eba0ca99021531c9534c810a98e6a92640847575185320432aa98c29902199548614c810974e9b02640847975181320421f3a0ca190210f5d0650c8108f4e0328640864f654c83204326b2a6419021721c1320c810c76e0b24a20846e7298e5104236b94c728821179ce62944108bae7314a20851d731534104296b90a9a08214d9c7545041087cec2a2820851d731514104296b90a8a08210fdd9541041087ce9b2c620843d74d963104237396cb188211b5cb658c410970e8b04620843e74d94310421eba6ca1882187592530c410c3ac8a9862084b874580310431ab2cc8188218d595640c410b60e0b2062085c57298c310423bbb2a618821555d4430c410aaaeb990620865565cc8310432ab2a6418821741c1320c4108eeeab0062084e47258031042d83a2c0188210f9d3658841087ae9b2c420845e73d96210422eb9ecb108212e1d1608841087ce9b28420843d74d942104316b24a4108218b5915208410970e8b00420863565990210431ab2ac8108216c1c164084108eaea31842084d67398821042e2b9cc4108211ddd95208410acaea21042084e5768c821042b2bac6410821995963208410ccaca99042086c4634c821042f038264108211ddd560084109a8e6b0042085b074580210421f3a4c7280210f5d2639401087ce9314a00843d7498a500421fba2c3280210f1d161940108bee6b0ca00845c735865004237b92c3280211b1c96194010acce598ca00855673c86500423cbb4a3a0021789cb31d0010ba4e790e800845e73d96400422eb9ecb200211b9cb65900108dae5b2c800863554986400428f39ecb20021475cf6590010a5ce5b2c800852d72d96400428f39ccb20021475ce6590010a5ce532c800852d72996400429d380cb200210f9d8539001087aec29c800852e7214e4004296b90a7200210f9d8529001087aec294800851e7314a400428eb98a5200218dd96619001087aed28c80085a672cc6400425abb063200214d5d43190010b2ce790c80084b576086400429aba84320021179cc65100108bae6328800846e721944004236b90ca20021351cd61100109c8e4b08800851e73194
  | 3 => 0xd854c811087aec2a6408861e64d4f204430eb26a7902218799053c8110c3ac829e408862e64d4b2044316b26a5902218b99052c8110c5ac82964088654539872044332294c3902219514d61c8110cc8a4b0e408843e74d95204421eba6ca90221179cf65481108bae7b2a408843f74595204421e3a2ca9022117dcd65481108b8e6b2a408843e75d91204421f3a8c8902210f9db5448110878edaa2408843e76151204421e3b0a890221179d76348110c3ea9b1a408861c54d8d204422f3a8c69022187d506348110c38a831a408845e76d4d204422e3b6a69022187d935348110c38c9a9a408845e7614d204422e3b0a69022187d905348110c38c829a408862f64d492044316326a49022193d8f5248110c98c7a92408862f641492044316320a49022193d8c5248110c98c6292408863754d85204431a2a6c29022195d4f6148110ca8a7b0a408866452d85204431baa0c2902218d1506148110caea630a4088654531852044333a90c290221991486148110c3ea9318408861c5498c204430faa2c6102218715163081108beeda98408845d76d4c204422fbb0a610221175d85308110c9cc7a90408864d63d482044327318a4102219358c5208110c3cc9a9e208861d64d4f104430f320a7882218759053c4110c5cc9a96208862d64d4b1044317320a5882218b59052c4110e36a62062088718531031044395a908188221ca14840c4110e30a9a9e20887185414f10443942a6a588221ca15052c4110e90a629620885667294e104438baa0a708221c51505384110e88a7a9420885567394a1044393aa0a508221c91505284110e8ea629420887445314a104429b3ac8108221c514e4084110e48a5204208853675102104438a2988108221c914840841108bee6b0aa80845c735855404237b92c2aa0211b1c9615501087eecaa0a80861d5458c5404316aa2c42a021879916315010c9cc7310a80864d639885404317322c42a0219398d6215010c9ac6b10a808655639845404332b14c22a0210f9d261d4c1087ae930ea60846e72d855304236b96c2a98210f9d36054c1087ae9b02a60843f74581530421e3a2c0a98211bdc96054c108d8e4b02a60845f7654c530430eb22a6298219354d6214c10c3ac9318a60862e649885304316b24c4298218b9916214c10c5ac8b10a60864e63588530431ab24c2298219a58a6014c108dce432e860846d72197430423abacc3a1821391c961d0c108dce432c860846d72196430423cbacc1218211bdc96550c108d8e4b2a860846e721954304236b90caa18211d5d46150c10c6aa830a860847975181430432ca98c0a18211b9c86510c108dae4328860847671194430421f3a4c3a90210f5d261d48108bce7b0aa40845d73d85520421f3a6c0a90210f5d3605481087ee8b02a40843c74581520422fb9a
  | 4 => 0x3ccba9c808843d7694e4044297394a7202214b5ca539011087eeca9c808852f7254e4044296392a7202214ddc55390110c3cca29c808862e65d4a4044387a9ea520221c314f529011087aed294808851e7394a404428eb9ca5202210fdd95290110a3ee6a94808851c7354a404429bb8aa5202218b9945290110e1ea6294808870c5314a404422f39ecaa0221175cf65501108dce5b2a808846d72d95404422fb9acaa0221171cd65501108dee4b2a808846c72595404421f3b0a8a02219514f6150110cc8a5b0a808863754185404432a298c2a0221991486150110a3ce72a0808851d739504044297394a8202214b5ca5410110a72e12a0808843f76550404428fb9aa820221471cd5410110a5ee4aa0808852c72550404429db82a8202214e1c26510110c3ccba98808843d7694c404428f39ca6202214b9ca5310110a5ae529880885397094c404421fbb2a6202214bdc95310110a58e4a9880885377154c404429db82a620221479d45310110c3cca298808862e65d484044387a9ea420221c314f521011087aed290808851e73948404428eb9ca4202214b9ca5210110a72e1290808843f76548404428fb9aa420221471cd5210110a6ee2a90808853b7054840442973a8a4202218b9945210110e1ea6290808870c53148404430fa9cc0202218714e6010110c5ea5300808862c52980404438da9cc020221c614e6010110e56a5300808872852980404421f3acc9982210f1d564cc11087eedaa6608843d76d53304421fbb0a9982210f5d854cc110c3cc9a9e608861d64d4f304430f320a7982218759053cc110c5cc9a96608862d64d4b3044317320a5982218b59052cc110ca8a730e608866452987304432a29ac3982219914961cc11087ce9b2a608843d74d953044237396ca982211b5cb654c11087ee8b2a608843c745953044237b92ca982211b1c9654c11087cebb22608843e75191304421f3b6a8982210f1db544c11087cec2a2608843c76151304430fb26a69822187193534c110c3ec829a608861c6414d30442373aec4982218bd53624c110c58a9b12608864f53d89304432629ec4982211b9d4624c110c5ea8312608862c541893044327a98c4982219314c624c1108dceda92608846c76d493044317b26a4982218b193524c1108dcec292608846c761493044317b20a4982218b190524c110c6ea9b0a608863454d85304432a29ec29822199d4b614c110cc8a5b0a608863754185304431a2a0c29822195d4c614c110ca8a630a6088667521853044332290c2982218bd52620c110c58a9310608864f53988304432629cc4182218bd51620c110c58a8b10608864f53588304432629ac4182211bddb520c1108daeda90608846f761483044236bb0a4182210f9d664c8110878eab26408843f76d53204421ebb6a9902210fd
  | 5 => 0x8654539844244332294c2212211d1d56110910ca8a6b08848866452584424421f3a6cb992210f5d365cc9108eae3b2e648843f74597324421e3a2cb992210f9d3658c91087ae9b2c648847571d96324421fba2cb192210f1d1658c91087ce9b2a648843d74d95324421fba2ca992210f1d1654c9108eee2b2a648847b7059532442a7396a699221539cf524c91087ce9b28648843d74d94324421fba2ca192210f1d1650c9108eee2b28648854d7214c32442a6b98a419221539d5320c910a98ea990648864e654c8324432632a6419221c3d51320c910e18a8990648863854980324432c29cc0192219a14a600c9108f0eab006488638545803244364992c0192218e15260d0510c70a8b06828845e75d8d414430faa6c6a0a218715363505108bcea31a828861f5418d414430e2a0c6a0a21179db53505108b8eda9a828845e7614d414422e3b0a6a0a211b9d76250510c5ea9b12828862c54d894144327a9ec4a0a219314f62505108dcea312828862f5418941443162a0c4a0a2193d4c6250510c98a6312828846e76d4941442363b6a4a0a2193d8f5250510c98c7a92828846e7614941442363b0a4a0a2193d8c5250510c98c6292828863854d81414432da9ec0a0a219614f6050510cd6a5b02828866852d81414431daa0c0a0a218e1506050510cb6a63028288658531814144335a90c0a0a219a1486050510a68eaa0882887145350441443922928220a211b9d662cc510c5ea9316628862c5498b3144327a9cc598a219314e62cc5108d8eab16628862f5458b31443162a2c598a2193d4d62cc510c98a6b16628846f76d4b3144236bb6a598a211bdd852cc5108daec296628863854983314432c29cc198a218e15160cc510c70a9b02628866852d81314431c2a0c098a2196d4c604c510cd0a4302628843f76d50314421ebb6a818a210fdd8540c51087aec2a0628861e64d4c314430eb26a618a2187990530c510c3ac8298628862e64d483144316b26a418a218b990520c510c5ac8290628845e7598f214430faa4c790a218715263c85108b8eab1e428861f5458f214430e2a2c790a2117ddb53c85108baeda9e428845f7614f214422ebb0a790a219398f52c8510c9ac7a96428864e6314b2144326b18a590a218e15260c8510cd0a5306428863854583214431c2a6c090a219614f6048510c70a83024288658531812144335a90c090a210fddb540851087aedaa0428843f76150214421ebb0a810a21879935308510c3ac9a98428861e6414c214430eb20a610a218b9935208510c5ac9a90428862e641482144316b20a410a218d15261d0110ca8a730e808866452987404432a29ac3a02219914961d0110a3ce72a4808851d739524044297394a9202214b5ca5490110a3ee6aa4808851c735524044297b92a9202214b1c95490110c
  | 6 => 0x3442a6392c029a2147dd11014d10a38e8880a68846e72d974344236b96cba1a211d5c765d0d108dee4b2e868846c725974344237396cb21a211b5cb6590d108f2e1b2c868846f725964344236392cb21a211b9cb6550d108dae5b2a868846f725954344236392caa1a211ddc56550d108f6e0b2a868846e72d944344236b96ca21a211bdc96510d108d8e4b28868863454984434432a29cc221a211d1d56110d10ca8a6b08868854e7395352442a6b9ca9a922153dcd54d4910a98e6aa6a48870f54d4f52443862a6a7a92214b9d253d4910a5ae929ea48852f7454f52442963a2a7a9221c3d5053d4910e18a829ea48864f6398f52442a7b9ac3a9221531cd61d4910a5ce9b06a48852d74d8352442a739ec1a9221535cf60d4910a5ee8b06a48852c74583524430faa4c729221871526394910c3ea8b1ca48861c5458e524430f326a729221875935394910c3cc829ca48861d6414e5244317326a5292218b5935294910c9cc7a94a48864d63d4a524430f324c729221875926394910c3cc8b1ca48861d6458e524432b31ac3292210fdd16094910878e8b04a48863a64582524421f3b6a8a92210f9d85454910c3ea9b1aa48861c54d8d524430faa0c6a92218715063549108bceda9aa48861f64d4d524430e326a6a9221179d85354910c3ec829aa48861c6414d524430fb26c6a9221871936354910c3ec831aa48861c6418d5244317b26c4a92218b1936254910c9ec7b12a48864c63d89524431bb26c2a92218d1936154910caec7b0aa48865463d85524421f3a6c0a92210f5d36054910c70c9b02a48865863d815244237bb2a4292214bdd15214910a58e8a90a48854f7354852442a639aa4292214b9d26214910a5ae9310a48854e7398852442a6b9cc4292210f9d0611491087ae8308a48845e73180524422eb98c0292218b99754149108daed2a0a48854e7395052442a6b9ca8292211bdd95414910a9ee6aa0a48854c735505244317328a829221939975314910e1ea9a98a48870c54d4c5244236bb4a6292214b9d25314910a5ae9298a48846f7654c5244297ba2a6292214b1d15314910c9cca298a48870f5414c52443862a0a629221595c46414910c9ac6318a4885697018c52442b33888629221595c44314910a9ce7b08a48854d73d8452442973a6c0292214b5d36014910a5ee8b00a48852c7458052442a7b9ac029221531cd6014910a5ee8880a48852c7444052442a7b9a2029221531cd10149108bce7b2e848845d73d97424423ab8ecba122117dcd65d09108b8e6b2e848845e73d96424422eb9ecb212211e5c365909108bee6b2c848845c73596424422f39ecaa1221175cf65509108bee6b2a848845c73595424423bb8acaa12211edc165509108bce7b28848845d73d94424422fb9aca21221171cd6510910c68a9308848
  | 7 => 0x7204214b9c85390210a5ae429c810843d7694a408428f398a520421475cc5290210b4ce598c81084b5760c640842cb39e43204212d5d82190210c6ca8b0881084d4735844084272392c220421479ce6510210a3ae7328810852e729944084296b94ca204210f5da5310210a5ce4298810852d7214c408421ebb4a420421479cc5210210a3ae629081085947358440842d2392c220421699cb311021096aec188810859673c84408425abb04220421391c9618c210c9ca6b10610864d535883084362b106218421351cd6188210c9ac7290410864d635482084362b1842104218d59664c4210c6acab2621084e67298f108426b39cc5884218e59664c4210c72cab26210851e73d87544428eb9ec3aa2214b9cb61d5110a5ae5b0ea88861f5498e544430faa2c72a2218bd526295110c5ea8b14a88864e6398a5444326b1cc52a2219398d6295110c9ac6b14a888656635865444333312c32a22187d936355110c3ec831aa88862f64d895444327b1ec4aa2219318f6255110c5ec8312a88864f631895444326318c4aa2219518f6155110cc8c5b0aa88865b63d81544432c31ec0aa2219ad8b6055110cd0c5b02a88843f76550544428fb9aa82a221471cd5415110a5ee4aa0a88852c72550544428f39cc82a221475ce6415110a5ce5320a88852d72990544429ab88c62a2214d5c46215110a3ee6b08a88851c735845444297b92c22a2214b1c96115110a9ce52a6a68854d7295353442a7b92a9a9a21531c954d4d10c9ec5316a68854f7258753442a6392c3a9a21479d360d4d10a3ae9b06a68854e72d8353442a6b96c1a9a2147dd160d4d10a38e8b06a68861e64d4e534430eb26a729a218bd526294d10c58a9314a68864f5398a5344317aa2c529a218b1516294d10c9ea6b14a68862e6498a5344316b24c529a218b9916294d10c5ac8b14a68866662586534421fba2c129a210f1d16094d10c74c8b04a68843e76d51534421f3b0a8a9a218bd536254d10c58a9b12a68862f5418953443162a0c4a9a2187d936354d10c38c9b1aa68862f64d895344316326c4a9a2193d8f6254d10c5ec8312a68862c641895344327b18c4a9a218dd936154d10c68c9b0aa68866762d855344332316c2a9a210f9d36054d1087ae9b02a68863864d815344334316c0a9a2117dd95314d10a3ee8a98a68851c7454c53442a7b92a629a21531c95314d10a3ce9318a68851d7498c53442a7394c629a21535ca6314d1087ce8308a68843d741845344237390c029a211b5c86014d10c3ccbaa0a68845d7695053442a7394a829a21535ca5414d108beecaa0a68854f7255053442a6392a829a21879945414d10aaae2320a68864d6218853442acb80c429a21539cb6114d10a9ae5b08a68851e74d80534428eba6c029a2147dd16014d10a38e8b00a68854f725805
  | 8 => 0x3614c310c6ca830a61886355418530c432b298c2986219554c614c310e34a620261886ab6210130c43543108098621ac184404c3108baeda98618854e72d4c30c43172a4c4186218b552620c310c5ca8b10618862d5458830c4327a9ac4186219314d620c310e36a620061886aa6210030c4354b1080186210f5d664c831087eeab26418843d7695320c421fbb2a990621535ce52c8310d64c2206418854e73d4a20c421ebaec8906210f5d4644831087ced2a2418843c7655120c430f2a6c690621875536348310c3ca831a418861d5418d20c42373b4a490621535ce5248310c98c7292418864c6354920c431b2a6c2906218d5536148310c6ca830a41886355418520c4333290c290621995486148310d36c620241886986310120c43952908090621ac1844048310c3ca9318418861d5498c20c430f2a2c6106218755163083108daeda90418854e73d4820c4326b1ea4106219358c5208310d34c620041886996310020c4395a9080106219398e62d5210c9ac7316a90864e6358b5484326b1ac5aa4219698e60d5210cb2c7306a90866a629835484334b14c1aa4210fdd95415210c38e6b24a70845f7654c5384326a9ac429c219398d6214e108dce5b2e870846d72d974384237394cba1c211b5ca65d0e10a3ce7aa6870851d7494f4384272392c3a1c211b9c86590e108dae432c870846e729954384236b94caa1c218dd506150e108dce4328870846d721944384316392c9294211bdd95214a10c9ac6a90a50864d63988528422f39ecba1421175cf65d0a108bce732e850845d739974284297396a9a14214b5d252d0a109a8e6b0e850845e73196428422eb98cb21421179ce6550a108bae732a850863754185428422f398ca21421175cc6510a1087ce9b2e650843d74d97328432b29ac3994210f9d3658ca1087ae9b2c650866652586328421f3a6ca994210f5d3654ca1087ce932a650843d7499532842a6392a699421531cd524ca1087ce9b28650843d74d943284327b2a641942193595320ca10d9264b0065084f071580328421f3b4a8a0c218e9506050610c72a8302830843d76d50418432729ac598c219354d62cc610ccacb31663086656558b3184371314c198c21535c8538c6108bced29a630845d76d4c31842a6b90a618c218d595640c610b8ae5318630847576d4c318426abb6a618c21749c3530c610b8ae429863085d27014c31842ab3a88618c21559d7320c6109c8e4b00630864d6394b2184326b1aa590c219559663c8610caacab1e43086d26398321842a6b98a510c211b9da52486108daeda90430854d73148218431ab2ac810c213c5c06308610b8ae7310430847576d482184272bb6a410c21789c35208610b8ae629043085e27014821842b33a88410c21599d63208610d88c699043084d473580218421ebb4a
  | 9 => 0xce8328658843d7419432c42a6b94a61962117dd9530cb10a9ae7290658846f7654832c42a7baa6419621535d5320cb10c9cca990658864c654c832c43872a26419621c3551320cb10b90e099065886395498241c430f2a6c6a0e21875536350710c3ca831a838861d5418d41c43172a6c4a0e218b5536250710c5ca8312838862d5418941c431d2a0c0a0e218e5506050710b60e0a08838863a5498041c43172a4c598e218b55262cc710c5ca8b16638862d5458b31c42a6b94a718e212e1d1608c71087aeb320638843f7559031c425c382c818e210f5da540c71087eecaa0638854d7294c31c425c3a2c018e218795263c8710c3aa931e438861e5458f21c430eaa2c790e21535ce5288710970e8b04438843d7599021c421fbaac810e212e1c1640871087aed2a0438843f7655021c42a6b9ca410e212e1d16008710c6ca8b0e81886396595340c421ebb6a7206214b9cb5390310a5ae5a9c818852e7294e40c4296b94a7206210f5d8539031087aeda94818851e73d4a40c428eb9ea520621479ce5290310a3ae7294818843d7614a40c421f3b4a8a06218d553615031087aedaa0818843d76d4c40c4297396a6206214b5cb5310310a5ce5298818852d7294c40c421ebb0a6206210f5db5210310a3ce7a90818851d73d4840c428f39ca420621475ce521031087aec290818847976d5040c425cbb6a8206216c9c75410310c72cb2a081885b27115040c429cbae86206214e5d44310310b64e2218818853975d0840c429cba884206216c9c44210310b36e6a0881885987350440c42d5b9282206216a1c94110310d62c2208818853975d8c40c429cba8c6206216a9c86310310b52e431881885b27118c40c42d8b88c6206212e5db5310310b54e5a9881885a972d4c40c438da9ca6206216a9ca5310310b52e529881884b97614c40c429cbaec4206214e5d46210310b34e631081885997318840c42d9388c4206216c5c46210310972eda90818859a73d4840c42ccb9ea420621669ce5210310b32e7290818872b5294840c425cbb0a4206214edd53210310a70ea990818853a750c840c429cba86420621e24c83210310c72cb308818859b7358440c42cc39ac2206216adc96110310b50e4b0881886396518440c42cd398c220621665cc6110310b54e430881885a97218440c4358b08c2206216a9cb3110310b52e598881884ba760c440c425cbb06220621669cf2110310b32e790881884ba7608440c425cbb042206210f5d664cc31087eeab26618843d7695330c421fbb2a998621535ca53cc310d64c2206618854e72d4e30c421ebaec8986210f5d4644c31087ced2a2618843c7655130c422f3b4a698621535ca534c310c5ca9b12618862d54d8930c43172a0c4986218b550624c310c9ca6312618864d5318930c431b2a6c2986218d55
  | 10 => 0x6a46190120082d538480900412b9d84048020c5eca202401068c631012008386a988090041a91844048020d90c6202401074953101200837030880900416a9d84048020d54ec20240106ab651012008395b288090041e2d8c4048020d54c620240106a86310120083c43188090041a218c4048020e56a6202401078a531012008394a988090041e254c4048020e12a620240107a36110120083543088090041e81844048020d40c2202401065b73d95200832c39eca900418ed976448020c76ca322401065b65d8d200832db28c690041a61906348020cb6cb29a401065b6554d200836431ec4900416a9d25248020e92a7292401067365d852008339b28c290041ac1906148020da0c630a40106e3621852008297390c72a6214b5c86395310a6ce231ca98851e7318a54c428eb98c52a6214d9c46295310a3ce630ca98851d7318654c4297390c32a6214b5c86195310a3ce7b04a98851d73d8254c4297396c12a6214b5cb6095310a5ce531aa98852d7298d54c429cb84c6aa6214edc16355310a3ce7312a98851d7398954c429cb84c4aa6214edc16255310a3ee6b02a98851c7358154c4297b92c0aa6214b1c9605531087eecaa0a98862e5498b53c4316aa4c5a9e218b95162d4f10c5aa8b16a78862e6498b53c4316b24c5a9e218b99162d4f10c5ac8b16a7886366498753c431ab24c3a9e219998a61d4f10ccac530ea78854e72d4e53c43172a4c529e218b5526294f10c5ca8b14a78862d5458a53c4327a9ac529e21539cb6354f1087aed2a0a78843f7655053c422fbb2a629e21535ca6314f108dce432e878846d7219743c4237396cb21e211b5cb6590f10c72a9304878846e7299543c4236b94caa1e218e5506050f108dce5b28878846d72d9443c431b2a2c221e218795263d4b10c3aa931ea58861e5458f52c430eaa2c7a96218799263d4b10c3ac931ea58864d7298f52c430f322c7a96218759163d4b10c6cc930ea5886356498752c432b31cc3a96219558e61d4b10c3ca931ca58861d5498e52c430f2a2c729621875516394b10a9ce7a94a58864d63d4a52c4326392c729621539cf6254b1087aed2a0a58843f7655052c4237bb2a429621535ce6214b108bce632e858845d7319742c422f39ecb21621175cf6590b10c72a9304858845e7399542c422eb9ccaa16218e5506050b108bce7b28858845d73d9442c431b2a2c2216210f9d265ccb1087ae932e658843e7419732c421eba0cb99621539cb53ccb10a9ae7296658843e7499632c421eba4cb196210f9d0658cb1087ae832c658854d7294e32c42a739ea5196210f9d2654cb1087ae932a658843e7419532c421eba0ca99621539cb534cb108bcec29a658854e73d4932c42373b0a4996212e9d3604cb10c74a9b02658863a5418132c421f3a4ca196210f5d2650cb1087
  | 11 => 0x8296ba86520041c354c3290020e1aa710c80104ad760864008386a984320041179ce65100208bae7328801045e73194400822eb98ca200419354e6210020c9aa6b10801051e73994400828eb9cca20041479cc6510020a3ae6328801053671194400829ab88ca200414e9c06510020a3aeb298801070c7254c400838c382a620041479cc5310020a5ce4298801053a7014c4008386a9cc420041c354d621002087aed290801052d75cc84008386a9e64200414b5d43210020e1aa619080105a9700c84008386a9c42200412b5d82110020e1aa610880105a970084400830f29cc0200418754e6010020a72eb300801063965980400838d29cc020041c654e6010020b52e5300801061e6494f300830eb24a7980418799153cc020c3ac8a9e601054d75ccb3008326b2e65980418e59440cc020e32a6206601078b321033008326a9cc5180411bdd5628c020c9aa6b14601054d750ca3008327b28651804187d92534c020c38c929a601061f6454d300830e322a6980419394f624c020c9aa7b12601064e531893008326a98c498041339db324c020a9aeb992601064f65cc9300832b29ec2980419554f614c020caca630a6010655531853008363990c2980419354e620c020c9ca6b10601064d5358830082a6ba8641804193594320c020c72ca2006010719531003008354b108018041e20c8400c020c3cc929e401061d6494f200830f322a7900418759153c80208deeca9e401064e6354f2008327bb2a790041931d953c8020e1cc8a9e401070d6454f2008326a9cc390041c354e40c8020e1aa6206401046d7694a200838ca9881100411e5da52880208bced29a401045c7694d200830fb24a6900418719253480208bceca9a401045c7654d200830fb22a690041871915348020caca7b0a401065553d85200832b298c2900419554c6148020c76cb202401063b65101200834c3188090041c654c4048020d60c2202401064f73d95200832639eca900418bd976448020c5eca322401064f65d8d2008236bacc690041339ce63480209cce331a401064f6518d2008347b20c690041a31906348020c9aea31a401046e76d4d200832631ea690041331da5348020a9aeb29a401064f6594d20082363b2a6900419318d5348020998eca9a401064f6554d2008327bb2a690041539d95348020a98eca9a401064c7654d20082263b2a690041c3d915348020e18c8a9a401066765d85200836231ec290041d154f6148020c9aa630a4010667651852008353b20c290041a91906148020d8ec630a40106c46318520083a2a98c29004199d4c6148020d8ca630a4010665531852008362a98c2900419154c6148020c9aa7b02401064c63941200836431e8090041d254f4048020dc0c3a0240104ae769012008317b2c8090041a318e4048020e1aa72024010
  | 12 => 0x218411ddc56550c208e8e2b2a861064d53d894308236ba8c4a18419354c6250c20cb2a7b02861047975181430832ca98c0a18411b9c86510c208ece2328861047571194430829ab88a9a10419654e6090820cb2a6b04841043e76151420829ab88a8a10410fdd95410820c9ce6b2e641064d6594f3208326a9cc3990419354d60cc82087ce9b2c641043d74d96320832ca9ac1190410f9d3650c82087ae9b28641054d7254c3208327b2a641904193595320c820cb4a6b00641054d7598c3208326b2cc619041535d6530c8208deeca98641064e6354c32082a7bb2a61904193dd9530c820c9aa7308641046f755803208326a9ac019041391c5600c8208bee6b24a21045c73592510822ebb4a628841879925314420c3ac9298a21045f7654c510830f322a6288418759153144208eeeca88a21063564544510822f39ccba0841175ce65d0420c9aa7316821064d5358b410822f39ccb20841175ce65904208bee6b2a821045c73595410822f398caa0841175cc65504208baebb1a821045d7518d410822f3b4a6a0841171da53504208bceca9a821045c7654d410832729ec4a08419354f6250420c5ca8312821064e531894108326a98c4a08419918a5150420cb4a7b02821065953d81410831d2a0c0a08418e5506050420cb4a63028210659531814108339288c0a0841179ce65104208bae7328821064d5398b310832729ac5988419354d62cc420c9aa7314621064d5358a31082a6bae65188410fdd1654c420878e8b2a62105547154d3108326a9ec4988419354c624c420cb2a7b02621043e74d94310821eba6ca188412e1c1640c420c3cc9298621061d6494c31082aab8ca61884187991530c420c3ac8a98621054d75cc83108326b2e6418841175d663c84208beeab1e421045d7694f210822fbb2a7908411b5d85488420a9ae62a44210565711522108236ba8c7108411bdd95388420c9cc6a9c421064d6554e2108327bb2a710841931d95388420e8ee2a9c42107447154e2108326a9ac110841879925308420c3ac9298421061e6454c210830eb22a6108418d5925108420c6ac8a88421074653484210832ca9cc0108419654d6008420a9ae62a04210565711502108236bacc6108413a5c06308420acae3a98421054d7594c210832731aa6108419318d5308420c9eeca98421064c7654c2108387322a610841c35915308420c9aa730842107455398421083a2a9ca210841d194d5108420e92a730042104cc735802108326a9ac010841aa9916008420e92a6b00421046d760ca5008326a9cc5200419354d6290020a3ce732c801051d73996400829b38ccb200414d5c66590020a3ce632c801051d73196400829d380cb20041c31c95390020a5ce429c801070d5398a4008386a9ac5200410f5da5290020a5aeb994801070d53cca40
  | 13 => 0x51cc120c6ac828e6090666621473048332b10a398241d14c851cc120a9ceb194609064e658ca30483a3190a3182418e994408c120e30a6204609078a32102304839828881182410f9d3654c12087ae9b2a609043f74595304821e3a2ca982410f9d7644c12087cea322609043e76d51304821e3b6a8982410f9d8544c120878ec2a2609061f64d4d304830e326a69824187d90534c120c38c829a609062f54d8930483162a6c4982419314f624c120c5ea8312609062c541893048327a98c4982419314c624c120a98ea992609064c654c9304823b3aec2982418dd53614c120c68a9b0a609065753d85304832a29ec2982411d9d4614c120c6ea830a609063454185304832ba98c2982419514c614c120d8a6430a609047676d45304831bb26a2982418d193514c120ccec5a8a609066462d45304823b3b0a2982418dd90514c120c68c828a6090667621453048332310a298241d14c8514c120c70ca20260907185310130483543108098241e24c8404c120d60c22026090730511013048317aa4c4182418b152620c120c9ea7310609064c539883048317aa2c4182418b151620c120c9ea6b10609064c535883048266bb46418241539d6320c120c9ccb190609066662d443048332b16a21824199988510c120ccac4288609074632144304830f326a7902418759353c8120c3cc829e409061d6414f204831b326a3902418d59351c8120c6cc828e409063564147204838c2988190241cc14440c8120e30a829e40907305414720483a8298a390241599c65388120c9ac629c409070f5414e20483862a0a710241939d85388120c9aec29c409074453d462048393aa0a310241c91505188120e8ea628c4090744531462048333b18a3102419958c5188120a5ceb204409070c53902204839228c81102414b9d44088120e18a62044090724511022048326b1cc5aa0419658e60d50208bee6b0ca81045c73586540821fbb2a82a0418d5516115020c9ac7310a81065663984540832ab1cc22a0418d9916115020cacc6b08a810655635845408333312c22a041991c96115020aace22a4a61055571152530828f3a0c529841475d06294c20a9ce5b0ca61051e74186530828eba0c329841955846194c2087ce830aa61043d74185530822f3b6a8a9841179d85454c20aace22a2a6105557115153082a7394c8a9841531c96454c20aaee2b22a6105547159153082ac382c8a9841479d26254c20a3ae9312a6105567198953082aab8cc4a9841539c46254c20a9ce5b0aa61054e72985530828fba2c2a9841471d16154c20a98e4b0aa61055870585530828f3a0c2a9841475d06154c20caac230aa61064c629815308326310c0a984117dd95314c208ece232e8610475711974308236bacc5a18419354e62d0c20c9aa6b16861046e72196430823d380cb
  | 14 => 0x6428c629043e74d95314821eba6ca98a410fdd1650c520878e8b28629043e74194314821eba0ca18a410f9d6640c520878eab20629043f76d50314821ebb6a818a410fdd8540c52087aec2a0629061e64d4c314830eb26a618a4187990530c520c3ac8298629046e75988314832629cc418a419314d620c520a98ea990629064c654c8314831b326a218a418d593510c520c6cc82886290635641443148333310a218a4199588510c520e8a64288629065853980314833828cc018a41b24c9600c520c3ea931e429061c5498f214830faa2c790a418715163c85208beeda9e429045d76d4f214822fbb0a790a41175d853c8520cacc628e429065563147214833828cc110a418e1536048520cb0a7b02429063854181214832c298c090a419cd446048520970e0b20429043f76d50214821ebb6a810a410fdd8540852087aec2a0429061e64d4c214830eb26a610a41879905308520c3ac8298429063664d44214831ab26a210a418b15262d0120c98a7316809064c5358b4048333310a3a02419958851d0120a3ce72a4809051d73952404829b38ca9202414d5c65490120a3ee6aa4809051c73552404829bb8aa9202414d1c55490120c3ccba9c809043d7694e404829b38ca7202414d5c6539012087eeca9c809052f7254e404829bb8aa7202414d1c55390120c3cca29c809070d7214e40482973ac65202418b9963290120e18a7194809052c754ca404831732a6520241c314d3290120c6ccba8c809071753d46404838a29ea3202418d9945190120e2ea628c8090714531464048393190a320241c94c851901208bce7b2a809045d73d95404822fb9acaa0241171cd655012087cec2a2809064c53d894048317aa0c4a02419314c6250120ccec428a809066462145404828f39ca820241475ce5410120a6ce32a0809053571950404821fbb2a82024147dcd5410120a38e6aa0809053771550404829a38aa82024187997531012087aed298809051e7394c404829b38ca6202414d5c6531012087eeca98809052f7254c404829bb8aa6202414d1c55310120a76e0a98809051e7514c404830f328a620241c35c85310120e32e0298809052e758c8404831732c6420241c314e3210120a58ea990809062e654c8404838629a64202416a1c13210120c6ccba88809071753d44404838a29ea220241cc5c35110120c6cca288809071753144404838a298a220241c98c85110120e4a64288809073370144404830fa9cc0202418714e6010120e36a73008090718539804048399a8cc020241cc146601012087ceb326609043c75593304821fbb6a9982410f5db54cc12087eec2a6609043d76153304830f326a7982418759353cc120c3cc829e609061d6414f304832629cc5982419314d62cc120a98ea996609063664d47304831ab26a3982418d990
  | 15 => 0x1f5498e514830e2a4c728a4187d516394520c38a8b1ca29061e64d4e514830eb26a728a41879905394520c3ac829ca29063664d46514831ab26a328a419598f5194520caac7a8ca29043e76d51514821f3b0a8a8a4187d536354520c38a9b1aa29061f5418d514830e2a0c6a8a41179db5354520c3ec9a9aa29061c64d4d514822f3b0a6a8a4187d905354520c38c829aa29047776544514829bba2a228a414d1d15114520aaee6a88a29055473544514822fb9ac828a41171cd6414520c6ccbaa0a2904757695051482ab39ca828a41555ce54145208eeecaa0a2905577355051482aa39aa828a418d9945414520caccba98a29071754d4c514838a2a6a628a41d1dcb53145208eaed298a2905367494c514829aba4a628a411ddd95314520a6ee8a98a2905347454c514832b328a628a41c5d505314520e28a8298a2907457214c51482b33ac6428a41c9d523214520e48a9190a290747538c851483a229c6428a41c9d513214520e48a8990a290747534c851483a229a6428a4155dcd6414520aa8e6b20a2905677259051482b9b82c828a41595c86414520acae5318a2905367418c514829aba0c628a41595c86314520ae2e0318a2905667290c51482b2b948628a415c9c24314520ae2e1218a2905667210c51482b2b908628a415cdc14214520ae0e0a10a290566708c851482b9b826428a415c1c13214520e8ee6990a290747634c851483a231a6428a41d8dc13214520ac8e0990a290760704c851483a29906428a414d9d36014520a6ae9b00a29053774580514829a3a2c028a4155dcd6014520aa8e6b00a29053774480514829a3a24028a4155dcd2014520aa8e6900a29045f73597414822e39acba0a4117dcd65905208b8e6b2c829045e73d95414822eb9ecaa0a41179ce65505208bae732a829045e75d8d414830faa6c6a0a418715363505208bcea31a829061f5418d414830e2a0c6a0a41179db53505208b8eda9a829045e7614d414822e3b0a6a0a418bd536250520c58a9b12829064f53d89414832629ec4a0a418bd506250520c58a8312829064f531894148326298c4a0a4195d8f5150520ca8c7a8a829066462d45414832bb18a2a0a419518c5150520ccec428a829066462145414831c2a6c0a0a4196d4f6050520cb0a7b02829067051d81414831daa0c0a0a418e1506050520cb6a63028290658531814148339a88c0a0a419c14460505208bee6b28829045c7359441483162a4c420a419314e6210520c98a6b108290666621444148332b10a220a410fdd165cc520878e8b2e629062f5498b31483162a4c598a4193d4e62cc520c98a7316629062f5458b31483162a2c598a4193d4d62cc520c98a6b16629066662d473148333310a398a419958851cc52087ee8b2c629043c7459631482a63aa6518a4193995328c520e8a
  | 16 => 0x831a2a4c329a4195d4e6194d20c6ea8b0ca69063454586534832ba9ac329a418d9926194d20c6ac930ca69066562986534831b322c329a418d5916194d2087ee8b04a69043c74582534821f3b6a8a9a410f9d85454d20c6ea9b0aa69063454d85534831baa0c2a9a418d1506154d20c3ec9b1aa69061c64d8d5348317b26c4a9a418b1936254d20c6ec9b0aa69063464d85534832bb1ec2a9a4199d8b6154d20c6ec830aa69063464185534832bb18c2a9a4199d886154d2087ce9b02a69043d74d81534831c326c0a9a419c1876054d208beeca98a69051f7454c534828e3a2a629a4155dc55314d20aa8e2a98a69051e7498c534828eba4c629a41559c66314d20aaae3318a69061e65d50534822ebb4a829a41559c65414d20aaae32a0a69045f7655053482abb8aa829a41551c55414d20c3cca2a0a69070f5458853483862a2c429a41535cb6414d20ab2e1b20a69054d7219053482a6b96c229a419358a6114d20a3ce8308a69051d7418453482a6b90c229a41935886114d20ab2e0308a69051e74d80534828eba6c029a419358b6014d20a3ee8b00a69051c745805348326b12c029a4155dc56014d20aa8e2b00a69051f74480534828e3a24029a411b5cb65d0d208ece3b2e869047571d97434823bb8acba1a411d1c565d0d208ece3b2c869047571d96434823bb8acb21a411d1c56590d20c5ea9314869064c5398a43482363aac521a419314d6290d20c76a9304869065853982434823c3aac121a419614d6090d208ece3b2a869047571d954348237b92caa1a411ddc56550d208e8e2b2a869047b70595434823b38eca21a411d5c76510d208eee2b2886904747159443483162a4c421a419314e6210d208d8eab10869064c53588434831c2a4c1a12419614f6050920c76a8302849065853181424832c29cc19924193dce658c920c5ccbaa4649062e65152324832732ea719241599c6538c920e1ea829c649070c5414e324832629cc1192418e153604c920c70a8302649065b5318132482a73aec69924193197634c920a9ce729a64905667194d32482373b0a699241c3d50534c920e18a829a649054e7614d32483273b0a699241539c4534c920c98a6302649064c5398832482a63aa6419241c3d51320c920e18a8990649043e7498f514821eba4c7a8a41559ce54d4520aaae72a6a2905577355351482aa39aa9a8a41c5d5353d4520e28a9a9ea2905367494f514829aba4a7a8a414ddd153d4520a68e8a9ea2907175414f514838a2a0a7a8a41d15c853d4520acceb196a290744538cb51483a229a65a8a41559cf64d4520aaae7b26a29056572d9351482b8b86c9a8a414d9d263d4520a6ae931ea2905657218f51483a299065a8a414d9d360d4520a6ae9b06a29055673d8351482aab9ec1a8a414ddd160d4520a68e8b06a2906
  | 17 => 0x8641c6d4c400c320d52c4200619078a3210030c8334b14c1aa4410fdd954152208bee6b08a91045c73584548821f3a4c3a9c410f5d261d4e208beeca98a71047671d97438823ab8ecba1c411d9c66550e208eae332a871047671194438823ab88ca21c410f9da5450a2087aedaa0851045e7694d328822ebb6a6194411b5db530ca2099aeda9865105ca70d4c32882a6bb6a619441935db530ca20e94e1a9865105ca7014c3288327a9cc21944193d4d600ca209c8e2b006510538705925188317b92c928c418b1c96494620c76e0b24a31063870592518823bbb2a228c41179cf65d06208bae7b2e831045f73595418822e39acaa0c414d9c75450620c58a8312831063b54181418821f3a6cb18c410f5d3658c620c9ea7314631043e74d94318821eba6ca18c41555c4530c6209d0e4b0063106cb325803188236bacc710c419398f5388620a9ee6a8c43104b870590218826639aca10c4153dcd6508620c5acab2043105a87059021882b2b8ca810c411b5d854086209d2e0318431064c63d4c2188237bb2a610c4159dc553086209caeda8843105e270d4421882a7b9aa210c41789c05108620998e6b00431070f530ca408821ebb4a32044147dcd5190220a38e6a8c81104ad760864088387a9864204416a5c0321022087aed288811051f73544408828e39aa2204412b5d82110220f1064204611045e7614d3088326298c498441339db324c220caea630a6110654531853088363990c298441c614c404c220d50c4202611078b321013088358308809844117dd9530c220c9ca6b10611064d53588308826639acb9044153dcd65c8220c5acb326411062d65593208832631ea7904411bdd953c8220c9cc6a9e411063965993208831cb2ac9904414b5c863d5120a72e031ea89051e73d87544828eb9ec3aa2414b5cb61d5120a72e1b0ea89061f5498e544830faa2c72a2418dd526195120c6ea8b0ca89064e6358a544832b31cc32a2419558e6195120ccac530ca89065663586544832ab1ac32a24187d936355120c3ec831aa89064c63d89544831bb26c2aa24195d8f6155120ca8c7b0aa89063764185544832bb18c2aa2419518c6155120ccec430aa89065863d81544833830ec0aa2410fdd95415120a3ee6aa0a89051c73550544829bb8aa82a2414d1c55415120a3ce7320a89051d73990544829b38cc82a2414d5c664151208bee6b08a89045c735845448296b90c62a24147dcd6115120a38e6b08a89052f72584544829db82c22a2414b5c8611512087ce930ea69043d7498753482ab38ca9a9a41555c654d4d20aaee2aa6a69055471553534828f3a4c3a9a41475d261d4d20a9ee4b0ea69051e74d83534828eba6c1a9a41559c760d4d20aaae3b06a69051f74583534828e3a2c1a9a41879935394d20c3ac9a9ca69063754986534
  | 18 => 0x1d4f20c6aa8b0ea79062e6498b53c8316b24c5a9e418d99261d4f20c6ac930ea7906666298753c831b322c3a9e418d59161d4f20cccc4b0ea79055671d4e53c82ab38ec6a9e410f9d06154f2087ae830aa79043d7695053c821fbb2a829e4117dd95314f20c74c8b00a7904767119743c823ab88cba1e418b5516290f208ece332a87904757199543c831caa0c0a1e411d9c76510f208eae3b28879062e5458843c831caa4c1216418e9526010b20aace3a9e659055671d4d32c822f3b0a6996418bd96544cb20c5ecaaa265905c671d4d32c82e4b86a6996411b9d8534cb2099cec29a659070e5414d32c8386aa0a699641539d8534cb20c9cec29a659070e7414d32c8386ba0a699641539c4534cb20e92e029a659064c5318132c822fbb2a619641c3951320cb20e1aa8990659063a5498032c831d2a2c019641b24c9600cb20c3ca931ea39061d5498f51c830f2a2c7a8e418755163d4720aace7a8ca39064e634ca51c821f3a0c6a8e410f5d0635472087aed2a0a39043f7655051c823bbb2a228e4117dcd65507208b8e6b2a83905347155141c830f2a6c6a0e41875536350720c3ca831a839061d5418d41c83172a6c4a0e418b5536250720c5ca8312839062d5418941c831d2a6c0a0e418e9506050720c72a8302839045e73d9441c822eb9eca20e414d5c65410720c5ca8b10839043e7499731c821eba4cb98e418b95262cc720c5aa9316639062e5458b31c8316aa2c598e419998a51cc720cccc4a8e639043e7499631c821eba4cb18e4193995328c72087ce832a639043d7419531c831d2a6c098e418e950604c72087ce9b28639043d74d9431c821f3a4ca18e410f5d2650c72087aeb320639043f7559031c825c382c818e410fdda540c72087aed2a0639043f7655031c821ebb2a818e41d14ca510c720c3ca931e439061d5498f21c830f2a2c790e418755163c8720cacc728e43906566354721c831d2a4c190e418e95160c872087aeb320439043f7559021c821ebb4a810e410fdd95408720c5ca8b16819043d76d4e40c829b38ea7206414d5c7539032087aec29c819070c534ca40c821f3b4a8a06418b553625032087aedaa0819043d76d4c40c829b38ea6206414d5c7531032087aec298819070c534c840c82d438264206410f5d664cc32087eeab26619043d7695330c821fbb2a998641e24c840cc320aace3a9c619043d75d9130c821eba8c8986410f9da544c320878ecaa2619045e7694d30c83172a6c4986418b553624c320c5ca8312619062d5418930c8327298c4986419354c624c320c6ca9b0a619063554d8530c831b2a0c2986418d550614c320caca630a61906555318530c8362990c298641175db530c320aace3a98619062e5498830c8316aa4c4186418b951620c320c5aa8b10619064f5358830c8266bb4641
  | 19 => 0x6a90801870d63548400c394382a420061475d63210030e1aa5190801870d520c8400c2ccb806420061c354a311003093aec188801870d520c4400c2ccb8062200614e5d66010030c72cb300801859973980400c395294c020061ca54a6010030c5cc9296601862d6494b300c317322a5980618b59152cc0308beeca96601864e6254b300c327bb2a598061c399152cc030e1ac8a96601864d52987300c386a948198061c354840cc0308baed29c601872952102300c23cbb4a7180611b1da524c030c5ec9292601862c64949300c2373b2a4980618bd91524c030c58c8a92601866652d85300c332a96c29806199948614c030ccaa430a601863b65901300c31db288098061aa188404c030e52a420260186b061101300c327b96ca98061931cb654c030c3ecbb22601861f65191300c327b2ec49806193d94624c030d1ec8312601868c64189300c326ba8c498061331da524c030c9ecb292601864c62549300c2663b2a49806193d95524c030a9ceca92601854c76549300c3263b2a498061c3d91524c030e18c8a92601865765d85300c362316c298061d154b614c030c9aa430a601865765185300c34bb20c298061a5190614c030d8ec430a60186c462185300c3a2a90c298061b1948614c030caaa430a60186c552185300c322a90c298061b218b404c030e92a5a0260186d061d01300c24f3b4809806187d96404c030d18c5202601870d52901300c34a30c8098061669c2404c03093cec202601861f65101300c3463108098061c3548404c030d28c220260186c862101300c3a4a908098061b4184404c030b34ec202601869a76101300c34db288098061c6d94404c030f16c4202601869862101300c3c43108098061a2188404c030f14a4202601871952101300c3c4a908098061c2548404c030f26c2202601869861101300c3c83088098061a4184404c030cd6e5b2a601866872d95300c31db2ec8980618ed94644c030b34e929a601866b65d89300c335b28c498061aa190624c030d96c6312601866b65949300c335b2aa498061d294d524c030ce6cbb0a601867365185300c358320c298061b4d8c614c030dc0c430a601866a6258354c822fb9ac32a641171cd6195320a5ce431ca9905367118e54c829ab88c72a641479cc6295320a3ae6314a9905367118a54c829ab88c52a64147dcd6195320a38e6b0ca99052c7258654c829db82c32a641479cc6195320a3ae630ca99052e7218654c831ab08c32a641479cf6095320a3ae7b04a99053671d8254c829ab8ec12a6414b9ca6355320a76e0b1aa99051e7398954c828eb9cc4aa64147dcd6155320a38e6b0aa99052c7258554c829db82c2aa6418d5846155320a3ee6b02a99051c7358154c829bb8ac0aa6414d1c5605532087eecaa0a9906365498753c831aaa4c3a9e418d9516
  | 20 => 0xd7498d520c2b338cc6a9061595c66354830ad4e121aa4185697090d520c2a739ec2a9061539ce6154830a5ee8b0aa41852c74585520c2a639ac2a90615a1c16154830a5ce830aa41852d74185520c332b08c2a90611bdd95214830c9cc6a96841864d6354b420c23bb8acaa10611d1c56550830c9ec6a92841864c63549420c334a96c0a10619a5486050830cd2a4b06641864e72596320c326b2ca5190619354a618c830c9aa4b04641866a52580320c2a6bacc41906153dd9520c830c9eeca90641864d52984320c26a38ac0190611bdc964944308d8e4b24a21846d76948510c317324a4288618b59252144308deeca90a21862e64548510c316b22a4288611ddd95114430c6ac8a88a21846e72997410c236b94cba08619398d52d0430c9ac6a96821846e72996410c236b94cb208611bdc965504308d8e4b2a821846e72195410c236b90caa08618795063504308daebb12821846d75189410c2373b4a4a08611b1da5250430c9ec7292821864c63949410c2373b2a4a08611b1d95250430c9ec6a92821864c63549410c32a31ca2a08619a94b6050430cd2a5b02821863a54181410c31caa0c0a08619a9486050430cd2a4302821867251181410c237394ca208611b5ca65104308daeb316621846f7558b310c236bb4a5988611bdd952cc4308baec2a4621854d72152310c2aab88a91886193989528c430c9acaa94621864f7654a310c3a3b8aa518861d11c5528c430c9aa4b04621862e64948310c316b24a4188618b991520c430c5ac8a90621863564944310c31ab22a218861d1949310c430cd2a5300621866952580310c2a6b90a818861555c4540c4308baeb310621864e62548310c327bb2a418861c3991520c430e1ac8a90621874552984310c3a2a94a218861d1949510c430e92a530062184cc72580310c326a92c018861a6991600c430e92a4b00621864d6394b210c32731aa5908619358d52c8430c9cc6a94421864d6354a210c2a6bac65108610fdd16548430878e8b2a421864f63549210c32631aa490861591c55248430cd2a5b02421843e74d94210c21eba6ca108612e1c164084308baebb1842184d97018c210c317324a4108618b5925208430acae3290421862e64548210c316b22a41086193d8d5208430c98c6a90421854d758c8210c326b2c6410861175d83294030c9cc6a94801864d6354a400c297394cb200614b5ca6590030a6ce332c801853571996400c297390cb200614b5c86590030a74e032c801843d7694e400c38731aa520061c358d5290030a3aeb194801870d528ca400c386a906520061c354a319003093aec18c801870d520c6400c32731aa4200619358d5210030a5ce5328801852d72994400c297390ca200614b5c86510030a6ce2328801853571194400c29d380ca200610f5da5310030e1cc
  | 21 => 0x21fba2cb10a610f1d16588530c9cca994429874532146214c21f3a6ca90a610f5d3654853087ee8b28429843c74594214c21f3a0ca10a610f5d0650853087ceb320429843c75590214c21fbb6a810a610f5db540853087eec2a0429843d76150214c22f3acc610a618b9935208530c5ac9a90429862e64148214c316b20a410a619398c5208530c9ac6290429864c654c8214c31b326a210a618d5935108530c6cc8288429863564144214c32b318a210a619558c5108530e8a64288429866852980214c33828cc010a61b24c96008530c38a931e809864e6314b404c326b18a5a02619598c51d0130caac628e809852e72952404c296b94a9202614d9c65490130a6ae32a4809852f72552404c296392a9202614ddc55490130a68e2aa4809862e65d4a404c317328a520261479d73290130c3ccb994809870c52cca404c30f32a6520261c31493290130c6ccba8c809872752d46404c392296a3202618d9945190130e4ea428c809872452146404c38b990a320261c54c8519013087cec2a2809861f5418d404c327b18a4a02619318c5250130caec628a809865463145404c297394a8202614b5ca5410130a6ce32a0809853571950404c21fbb2a8202614bdc95410130a58e4aa0809853771550404c29a38aa8202618b9975210130c5cca290809872970148404c28f3ae6420261879973210130e18a5990809861e654c8404c3862926420261661c13210130c6ccba88809872752d44404c392296a220261cc5c35110130c6cca288809872752144404c392290a220261c5cc85110130e2a64288809873370144404c395a94c020261ca14a6010130e66a3300809873051980404c317326a5982618b59352cc130c5cc8296609862d6414b304c31b326a3982618d59351cc130c6cc828e609863564147304c3942908198261cc14440cc130e50a8296609873054147304c3b0290a39826193588528c130e1ea8294609870c5414a304c326bb0a518261d114b518c130e2ea828c609871454146304c3a3a90a318261d1148518c130caac428c609851e75902304c3862948118261c5146408c130a3cea204609870c52102304c38a28881182619398d62d5030cd2c5306a81846f72586540c236392c32a0610fdd95415030c6aa8b08a81864e63588540c333314c22a0619958a6115030c6cc8b08a81865663584540c333312c22a061995896115030ca8e6b08a81853571153430c21f3b0a8a18614d5c45450c3087eecaa0861856671152520c2b2b88a9290614b9d06394830a5ae831ca41854e73d86520c2973a0c3290614b5d06194830ccac230ca41843e74185520c21eba0c2a90611b9db54548308dcec2a2a41856671151520c2b2b88a8a9061539ce6454830a98e6b22a41856771591520c2b238ac8a90615a1c16454830a5ce931aa41852
  | 22 => 0xa611b9d85254530c5ec8292a29862c64149514c23bbb2a228a614ddd15114530a68e8a88a29856772544514c2b2392a228a611bdc964145308d8e4b20a29863665d50514c23abb4a828a61599ca5414530acae52a0a29847776550514c2b3b92a828a61591c95414530c6cca2a0a29866665d48514c393aa6a428a61c91535214530e8ee7a90a29847576948514c29b3a4a428a614d5d252145308eeeca90a29853774548514c29a3a2a428a61999945214530e4ea8290a29872454148514c3a2b98a428a61559d73214530e2ea9990a29871454cc8514c3a3a966428a61d114b3214530e2ea8990a298714544c8514c3a3a926428a61d11493214530aaee6b20a29856772590514c2b2392c828a615cdc16414530aaae6320a2985737050c514c2b83828628a61555ce6214530a6ce8310a29853574188514c2aab98c428a615c5c06214530aace7210a29855573908514c2b93848428a615c5c24214530aace6210a29855573108514c2ab3866428a615cdc13214530ae0e0990a298747724c8514c3a3b126428a61d11893214530ea6e0990a298554704c8514c3a83826428a61d14c83214530a6ce9b00a29853574d80514c29bba2c028a614d1d16014530acee4b00a29856472580514c29bba26028a614d1d13014530acee4980a298564724c0514c237b92cba0a611b1c965d05308dee4b2c829846c72596414c237396caa0a611b5cb65505308dce532a829846d72995414c30faa6c6a0a61871536350530c3ea831a829861c5418d414c2373aec4a0a618bd536250530c58a9b12829846e75189414c317aa0c4a0a618b15062505308dceda92829846c76d49414c327b1ea4a0a619318f52505308dcec292829846c76149414c327b18a4a0a619318c5250530ca8c7a8a829866762d45414c332316a2a0a6195d8c5150530ca8c628a829866762145414c332310a2a0a618e1536050530cd6a5b02829866852d81414c33828ec0a0a618ed506050530c70a8302829866b52181414c334290c0a0a619cd446050530ce0a2302829846f72594414c236392ca20a61871526310530c9cc6290829864d63148414c32b318a220a619558c5110530c5ea9316629862c5498b314c317aa2c598a618b15162cc5308deeda96629846f7614b314c333310a398a619958851cc530ce0a3304629863854d81314c334296c098a618e150604c530cd0a4302629867351181314c25c382c818a610fddb540c53087aedaa0629843f76150314c21ebb0a818a618b993520c530c5ac9a90629862e64148314c316b20a418a618d993510c530c6ac9a88629843f74597214c21e3a2cb90a6187d5263c8530c38a931e429861f5458f214c30e2a2c790a619398f52c8530c9ac7a96429864e6314b214c326b18a590a619598f51c8530cacc628e429865563147214c
  | 23 => 0x15130a6ee2aa0a89853471550544c297394c82a2614b5ca6415130a6ce3320a89853571990544c237b92c22a2611b1c96115130a3ae6310a89851f73584544c297b92c22a2614b1c96115130a76e0b08a89851d73184544c31c2a4c1a1a618ed506050d3087ce930ea49843d74987524c2b338ca9a9261595c654d4930acee2aa6a49856471553524c2973a4c3a92614b5d261d4930a9ee6b0ea49852e74d83524c296ba6c1a9261599c760d4930acae3b06a49852f74583524c2963a2c1a92618b9935294930c5ac9a94a49863754986524c31a2a4c32926199d4a6194930c6ea8b0ca49863454586524c333a92c3292610f9db545493087cec2a2a49863754d85524c31a2a6c2a92618dd506154930c68a830aa49846f76548524c297ba2a4292614b1d15214930acee2a90a49856471548524c31732ea8292611b5da5414930acce32a0a49856571950524c237bb2a82926159dc55414930ac8e2aa0a49862e65150524c387aa2c629261c31516314930a9ae7b20a49856970d90524c2a6b98c8292615adc14314930ad0e0a18a49854d73d84524c2973a0c2292614b5d06114930a9ae6308a49856970184524c2973a6c0292614b5d36014930a5ee8b00a49852c74580524c2b3b8ac029261591c56014930a5ee8980a49852c744c0524c23bb8acba12611d1c565d09308eee2b2c849847471596424c30faa4c7212619398c5290930c9ac6294849863b54982424c334294c1212619a14960909308ece3b2a849847571d95424c23bb8aca212611d1c56510930c38a9318849864e63148424c326b18a42126193dca65cc930c3ccbaa6649861e65153324c32732ea599261c3d5052cc930e18a8296649864c52983324c334294c1192618e153604c930c70a8302649866b52181324c2a73aec499261c3d50524c930e18a8292649854e76149324c3273b0a499261539c4524c930e1ea8990649870c544c8324c21f3a4c5a8a610f5d262d4530acce52a6a29856572953514c2b3b92a9a8a61591c954d4530e4ea9a96a29872454d4b514c29b3a4a5a8a614d5d252d4530a6ee8a96a2985347454b514c393aa0a5a8a61c915052d4530e8ae6296a29855675ccb514c3a229665a8a61d114932d4530aaae7b26a29856672d93514c2b2b96c9a8a615c5c364d4530a6ce9316a2985357498b514c2aab98c5a8a61d14c832d4530a6ce9b06a29853574d83514c2b3396c1a8a61595cb60d4530a6ee8b06a29853474583514c317aa4c528a618b1526294530c5ea8b14a29862c5458a514c317326a528a618b5935294530c5cc8294a29862d6414a514c31b326a328a618d5935194530cccc5a8ca29866562d46514c21f3b6a8a8a610f9d85454530c5ea9b12a29862c54d89514c317aa0c4a8a618b15062545308dceda92a29862f64d49514c316326a4a8
  | 24 => 0x316a39862d5498b51cc3172a2c5a8e618b55162d4730acce5a8ca39864e624ca51cc21f3a0c4a8e610f5d0625473087aed2a0a39843f7655051cc23bbb2a228e611bdc965507308d8e4b2a83985347155141cc30f2a6c6a0e61875536350730c3ca831a839861d5418d41cc3172a6c4a0e618b5536250730c5ca8312839862d5418941cc31d2a6c0a0e618e9506050730c72a8302839846e72d9441cc236b96ca20e614d5c65410730c3ca8b18839862e5498b31cc316aa4c598e618b95162cc730c5aa8b1663986666294731cc333312a398e618e95260cc730c74a8b06639843d7599031cc21fbaac818e610f5da540c73087eecaa0639843e7499721cc21eba4cb90e618795263c8730c3aa931e439861e5458f21cc30eaa2c790e619598e51c8730cacc6a8e439843e7499621cc21eba4cb10e6193995328873087ce832a439843d7419521cc31d2a6c090e618e950604873087ce9b28439843d74d9421cc21f3a4ca10e610f5d2650873087aeb320439843f7559021cc25c382c810e610fdda540873087aed2a0439843f7655021cc21ebb2a810e61d14ca5108730c3ca8b1e819843e7695140cc30eaa6c6a06610f5db5410330b30e0990819865963983548c21fbb2a82a4611bdc961152308d8e4b08a91843e76951438c21ebb6a821c611bdd95214a308ece3b2e851847571d97428c266bb6a419461729c3520ca30b94e029065184d471580328c29c382c928c6187dcd6494630c38e6b24a31863b70592518c31c382c928c611ddd951146308dce5b2e831846d72d97418c237b92caa0c611b1c96550630a6ce3aa2831861c5418d418c31daa0c0a0c61175d6628c630a9ee4a8c63184b870590318c266392ca18c6153dc9650c630c3acab20631859870590318c2aab8ca818c61175d8540c630aaee2a9063184d576d44318c2e9386a218c6153dc9510c630ba4e028863184cc72580318c21f3a6cb10c610f5d3658863087ce9b28431843d74d94218c26cb80c610c61361cd6008630d9464b00431843d76946408c297b92a3204614b1c9519023093aec18c8118599700c8408c21ebb4a2204614bdc95110230a58e4a88811849d760c4408c266392cb9846153dc965cc230c3acb326611861d65593308c327312a5984618e59664cc230c72cab26611851d7318b544c29cb80c5aa261475cf61d5130a5ce5b0ea89852d72d87544c29cb86c3aa2618bd526295130c5ea8b14a89863754986544c31baa2c32a2619358e6295130caac730ca89866662986544c332b14c32a261999896195130ccac4b0ca89862f64d89544c317b20c4aa26193d8c6255130c6ec9b0aa89866762d85544c332316c2aa2618dd906155130caec630aa89866762185544c332310c2aa2619a18b6055130ce0c3b02a89843f76550544c297b92a82a2614b1c954
  | 25 => 0x211812110355108c0908812e9c2650844087aed328422063a709942110316392ca10881279cc650844093ae632842204ba70194211021f3aec6108810f5d76308440976e0b1842204b87058c211021f3a8c6108810f5d46308440974e031842204b97018c211024f39cc410881275ce620844095aeda90422062d65d4821102d5386a4108812b5d85208440c5aca290422058d7314821102d2b88a4108816a9c0520844095aed190422062d658c821102d2b8c64108818b5953208440d18c699042205a8704c82110316b2e4210881635cf2108440b54e19084220635658842110257bb242108818b5952108440b50e090842204b776484211031ab2a42108816c1c1210844093ee6b00422049c73580211028fb9aa328081471cd5194040a5ee4a8ca02052c72546501031b30aa328081c34c83294040a5ce598ca02052d72cc6501021ebb06328081479cf2194040a3ae790ca02043d76086501034cb18c7280816a9c86394040b52e431ca0205aa7214e50102d4b90a7280816c9c45394040b62e229ca02059a7318a50102ccb98c528081aa5886294040b34e6294a0205997314a50102d9388a5280816c5c45294040976ec994a0204b8764ca501025d3b065280812e5d83294040f1264194a02059a73d8650102ccb9ec3280816a9cb6194040b52e5b0ca0206b26194650102cdb9aa328081661cd5194040b56e4a8ca0205a872546501035930aa328081669cc5194040b32e628ca0205aa7214650102d4b90a3280812e9db3194040972ed98ca0205aa72cc650102d4b9663280812edd93194040970ec98ca0204ba76c86501025cbb64328081669cf2194040b32e790ca0204bb76486501025c3b243280819698d60d53308dee4b0ca99846c7258654cc297390c72a6614b5c86395330a6ce231ca9985357118e54cc28f398c52a6614d9c46295330a6ae2314a99851c7358654cc297b92c32a6614b1c96195330a76e0b0ca99851e7318654cc297390c32a6614b5c86195330c6ac230ca99852e72d8254cc296b96c12a6614d9c76095330a6ae3b04a99852e7298d54cc296b94c6aa661479ce6255330a76e0b12a99851c7358554cc297b92c2aa6614b1c96155330a76e0b0aa9986356118554cc297b92c0aa6614b1c96055330a6ee2b02a9985347158154cc21fbb2a82a6618e5526090f30c74a930087986365498752cc31aaa4c3a96618d95161d4b30c6aa8b0ea59856671d4a52cc21f3a0c2a96610f5d06154b3087aed2a0a59843f7655052cc237bb2a429661875516390b30c72a8302859847671d9442cc23ab8eca21661879516310b30c3ecb2a2659861f6555132cc2e338ea499661725c3524cb3099cec292659870e5414932cc386aa0a499661c3951320cb30e1aa8990659863a5498032cc31d2a2c019661b24c9600cb30c5ca9
  | 26 => 0x93b92a228881c91c95114440e4cc4a88a220635625445110392b12a228881895895114440e60e0a88a22063551980511034d31cc028881a658e6014440d54c5300a2206a9629805110398a8cc028881ac9466014440d62a3300a2204ae72d973110256b96cb988812e9c265cc44095ce432e62204ad72197311025d380cb98881a394d62cc440d1aa6b1662206aa629833110354b14c1988812e5d660cc440d34a73066220699539833110355312c198881aa58960cc440976eab06622063b75583311025d384cb188812b9c8658c44095ae432c62204ba7019631102cd386a718881635c8538c440b2ae229c622059a7014e311025d384c5188812e5c2628c440d1cc49946220598704ca311031a32aa318881651cd518c440e2ea6a8c622058d72cc631102cd38663188812e9c2654c44093ee6b2a62204af725953110256392ca988812b9c8654c44095ae432a62204ba70195311024f3b4a6988818d195514c440e2aa6a8a62204b975d81311031cbaec0988812e5d4604c440d34a63026220699531813110359288c098881ac544604c440d6662302622069a31181311025d384ca188810f5da650c440c74e1328622061c735943110257390ca188812b5c8650c440974e0328622049d76d4c311030eb2ea618881669c3530c44093aec298622061d6514c31102c6b90a618881655c4530c440b34e029862204bb70588311025c382c41888187597320c440b2ae3990622061d654c831102cc382641888187597310c440b1ae5988622059a70cc4311031ab2c621888127dd9310c440c3aca9886220598704c4311025bbb262188818d595310c440b60e098862204af725803110256392c018881279cf65c844093ae7b2e42204ba70997211024f398cb90881275cc65c8440974e032e42204ba70d8f211025cb86c7908812e9c063c8440972e031e422068d6394b2110346b1aa590881a698e60c8440d32c730642204b9759832110355294c190881aa54a60c8440d34c6b06422069963583211025dbaac1908818edd560c8440974e132c422049e73196211024eb98cb108812e9c06588440974e1b1c42204b970d8e211025d384c7108812e5c2638844087cea31c422043d7518e21102d5386a510881635cc5288440b4ae229442205aa7014a211034731a65108816a1c13288440c68caa8c42205a4725462110393a92a310881635cf2188440b54e190c42204ba70995211024fb9aca90881271cd654844095ee4b2a422049e73195211024eb98ca908812e9c0654844095ae531a42204ba7098d211025cb84c6908810fdd56348440878eab1a42204bb7058d211025c382c6908812b9da5248440c68caa8a422072552545211025cbaec0908818e5d76048440972ea30242206aa521812110354a90c090881ac9446048440d62a230242206b3
  | 27 => 0x81ac1c26114c40d4cc4b08a6206a562584531031ba9ac229881a594d6114c40c6aa6b08a620695535845310358382c229881aa98a6014c40d52c5300a6206b2619805310358b0cc029881a694e6014c40d32a7300a6204ba71980531024fb9ac3a9081271cd61d4840974e3306a4204b87058e52102d5386a5290812e1c16194840974e031aa4205aa70d49521025d386c2a9081a358e521484087eeca90a4204af765485210346b1aa429081a598e6114840d2ac7308a4206b070984521034b31ac229081a558d6114840c6ea4b08a4206a652584521031aa92c229081a95496114840d60e0b08a42069a63980521034cb1cc029081ac9866014840d62c3300a4206aa529805210354a94c0290812e9c66014840974e132e64204b671197321025ab88cb990812e9c065cc840976e0b0e64204b870587321025d384cb190812d9c4658c84096ae232c64204ba70196321025db82c3190812e1c1618c840974e132a64204b771595321025a38aca990812d9c4654c84096ae232a64204ba70195321030e32aa699081631c9534c840c58caa92642058c73549321025d386c2990812e5c3614c84087cea30a642043d75185321025cbaec0990818e5d7604c840974e3b0264204b975181321034d298c099081a654c604c840d54a430264206a9521813210355990c099081a68c8604c840974e230264204ba70994321025b388ca190812d5c4650c840974e0328642058d738c8321024fbb26419081661c1320c84095eec99064205a8704c832102c7bb26419081a3dd9320c840d1eca990642068d654c832103c5b826419081631c1320c840f10e09906420588704c83210346994c2190812edc1610c840970e0b08642078932980321025cbacc0190812e9c6600c840d1a64b0064204b771580321025a38ac019081e24c9600c840b60e2b0064204bb75580321031dbaac019081a6cc9600c840d5464b006420699325803210354992c019081a24c9600c840d66e2b0064204b871580321035838ac0190812c1c5600c84095ce531ca2204ad7298e511025d384c7288812e1c1639444093ce7314a22049d7398a511025d384c5288812e1c16294440b64e1a8ca2206957118d511030e31ea6a88814d1c55354440d1ec7b12a22068c63d895110347b18c4a8881a318c6254440d4ae2312a22062c62d49511029a38aa4a88816c9c35154440d36c6302a220698631815110355b10c0a8881aa1886054440d1cc7310a22068d63988511034731ac428881a358d6214440c3ac7a88a22062d62d44511034ab1ca228881a958a511444087eeca88a22061d635445110316b12a2288812ddd95114440d2ac6a88a2206a562544511029bbb2a2288818ddd95114440e2ee6a88a22071473544511038b31aa2288818d58d5114440e2ac6a88a2206156354451103
  | 28 => 0xc84096ae2324642047771595321023a38aca990811d9c4654c8408eae232a64204b970991321025bb8ac8990812d1c5644c840976e0b22642061c6454d32102a6392a6990818b191524c840a98e6a9264204b974d81321025cb86c8190812e5c0640c840c9eca990642064d654c832102e438264190812edd1600c840d9264b0064204f0715803210237394c7288811b5ca63944408bce7314a22045d7398a511030f3a0c6a8881875d06354440c38c7a1aa2205347150d5110327b1ec4a88819318f6254440c9ec6312a22064c6318951103173a0c4a88818b5d06254440c58c5a12a22053471509511032db18c0a88819618c6054440cd6c4302a22066862181511023bbb2a2288819558d5114440ccac4a88a2204bb75583411031dbaac1a08814e5d76090440c3aea31a82205347154d4110347b1ec4a0881a318f6250440d1ec6312822068c631894110316ba8c4a08814d1c55250440d36c7b02822069863d814110355b16c0a0881aa18b6050440c76ca302822069b63181411034c318c0a0881aad886050440d50c4302822053575984411029bbb2a2208818ddd95110440e2ee6a88822071473544411031ab1aa220881c9dc95110440e48e4a888220635625444110398382a2208811b9cb65cc4408dae5b2e62204ae72d933110256b96c9988812e5c364cc44095ce432662204ad72193311025cb80c9988819394d62cc440c9aa6b1662204bb745833110257390c9188812b5c8648c440c68c8a8c622055473546311038ba1aa3188811bdc9654c4408d8e4b2a622046e721953110236b90ca988812e5c2644c44093ee6b2262204af725913110256392c8988812edc1644c440c68c8a8a62204b974d81311021ebaec81888187597430c44093aec218622061d6510c31102cab888618881179cf65c84408bae7b2e422049e73d93211024eb9ec9908812e5c364c844093ce6326422049d73193211025cb80c9908819358e52c8440c9ac6a9642204bb74583211024f398c910881275cc6488440c68c8a8c4220564725462110393a12a31088117dcd65484408b8e6b2a422045e73195211022eb98ca908812e5c2644844093ee6b22422049c735912110257b92c8908812edc16448440c68c8a8a42204b974d81211021ebaec8108818b597420844095aec210422062d6510821102d2b88841088147dcd4194040a38e6a0ca02052f72506501029639283280810f5da54900408f2ed2a480206b26190640102cdb9a8320081661cd4190040b56e4a0c80205a872506401035830c82a00812e9d8415004095ee4b0ea6204ac72587531025d38cc1a9881669c35394c40970e0b14a6204b87058653102cd386a6a98812e9c06254c40974e1b0aa62043f7654c531024fbb2a629881a394d6214c40d1aa6b10a6206a6629845310352b14c2298
  | 29 => 0x6a3204ae7298e5190256b94c728c81279ce629464093ae7314a32053a70d4651902d9386a328c814d5db5194640c6aeda8ca32071673d46519038ab9ea328c81c99cb5194640e4ae5a8ca32053670d465190399386a328c814c9c35194640b64e1a8aa32043f76544519025bbb2a228c81ac9466014640d62a3300a3204ae72d973190256b96cb98c812e9c265cc64095ce432e63204ad72197319025d380cb98c812b9cb658c64095ae5b2c63204ae729963190256b94cb18c812e9c2658c640974e032c632068e624ca31902c6b966318c812b9ca654c64095ae532a63204ba70995319025d380ca98c812e9c2650c640c3ce7328632063a709943190257390ca18c812b5c8650c640974e0328632061e6594c31902cab8ca618c8187995530c640c3acb990632059571cc8319030eb2a6418c81635cb310c64093eec98863204b7764c43190257b92c018c812b1c9600c64093ce7b2e432049d73d97219025d384cb90c81279cc65c864093ae632e43204ba70197219024f39ecb10c81275cf658864093ce732c432049d73996219025d384cb10c812e9c0658864087cea31c432043d7518e219034731a6510c81635cf218864093ce732a432049d73995219025d384ca90c812e9c0654864087eeab1a432043c7558d219025db82c690c812e1c16348640974e1328432062e72994219031d384ca10c81279cc650864093ae632843204ba70194219021f3aec610c810f5d7630864087cea318432043d7518c219025d380c610c812e5c06308640c5ccb29043205a571948219031732aa410c818b5963208640b4ae3190432062d654c8219034631a6410c81635cf210864095eec90843204b776484219024fb9ac010c81271cd60086408dee4b0ea6a046c72587535022fbb2a629a81531c95314d40aa8e2a98a6a045f73587525022e39ac3a92811bdd95214940a98e6a90a4a056471548525023bb8aca192811d1c5650c940a9ae429864a054d7314832502a73aa6419281531d5320c9408eeeca88a2a05547354451502b2392a228a819518f5150540cc8c5a8a82a0654631454150332310a2a0a819c1476050540c6ccaa0882a046e721973150236b90cb98a819998b51cc540cccc428e62a046f725943150236392ca18a810f9d6640c540c3ac9a9862a063564d44315022f398cb90a81175cc65c8540cacc7a8e42a065663147215022fb9aca10a81171cd650854087ceb32042a062d64d48215031ab26a210a8117dd95314c40c9aa6b10a620655535845310257b92c3a18812b1c961d0c40976e0b0e86204bb70586431025cb86c2a18812edc16110c408deeca90a42064d635485210332a92c22908127dcd61d0840938e6b0e84204bb70587421025db82c3210812e5c36150840976e0b0884204b671193321025ab88c9990812d9c4648
  | 30 => 0x3d9721d032b31ca390e819598d51c87408bce732843a045d7399421d0317322a410e818d99151087408dce5b0aa72046d72d85539022fbb2a629c819354d6214e4095ee4b0e87204ac72587439022f39ec2a9481175cf6154a408deeca90a52064d63548529024fb9ac3a1481271cd61d0a408ece3b2e652047571d97329025b388c9994812d5c464cca40c3ac929e652047671d96329023ab8ecb194812d9c4648ca4096ae2324652062d6494a329025bb8ac8994812d1c5644ca40a98e4a9a652054c735493290327b2a641948193595320ca408dce531ca32046d7298e519022f39cc528c81175ce62946408eeeca88a32067251181419030f3a8c6a0c81875d46350640c38c6a9a832068f63d89419034631ec4a0c81a3d8c6250640d18c6312832062e751894190316ba8c4a0c818b1895250640a6ced28a832063676945419038bb1ca2a0c81c518e5150640e4ec528a832072462945419039928ec0a0c81a6d8c6050640d30c630283206ab621814190354310c0a0c81cc94460506408dce5b2e632046d72d973190257396c998c812b5cb64cc64095ce432663204ad721933190237396cb18c811b5cb658c6408dce532c632046d729963190257390c918c812b5c8648c64095ee4b2263204ac72591319030eb24a618c81555c6530c640c3ac8a9863205957110c319022f39ecb90c81175cf65c864093ce7b26432049d73d93219024f398c990c81275cc64c86408bce7b2c432045d73d96219022f39ccb10c81175ce658864093ce6324432049d73192219024fb9ac890c81271cd6448640c5ac92904320565719482190316b22a410c81695c44208640b34e1a9ca72059a70d4d5390257396c2a9c812b5cb6154e4087eeca98a72049f7654c539034729ac429c81a354d6214e40d54c5300a7206a962980539034d29cc029c81a654e6014e40b54e1a94a5205aa70d49529024f39ec2a9481275cf6154a40d1ac7290a52043f765485290257bb2a429481a358d5214a40d34c7300a520699639805290355294c029481aa54a6014a4096ce3b2e65204b571d97329025d384cb994812e9c065cca40c3ccb29e65204b671d96329025ab8ecb194812e9c2658ca40974e032c652062e6594a329025b38cca994812d5c6654ca40974e132a65204ba7019532902c6392a699481631cd524ca4087cea30a652043d75185329025d384ca194812e9c0650ca4093eec99065204af764c832902c7bb26419481a3dd9320ca40d1eca990652068d654c832902c63826419481a34ca610ca40d1a64b0065204b771580329025a38ac0194814d9c753d4640c3cc6a9ea32068e6398b5190346b1cc5a8c81a398d62d4640d1ac6b16a32053671d4b5190317312a5a8c81a698e60d4640d32c7306a3206aa629835190354b14c1a8c818e54e60d4640c72a53
  | 31 => 0x3baac319043a9951618c821d4aa8b0c6410ce47058632086a7396a699043179d8534c821ab2e029a6410c6d759913208672b88c8990438bd95544c821b8ce3a9a6410c6e7614d32086b4b80a699043339d8534c821e1ca829a6410f0d5414d32086e4b80a699043539d8534c821c9cec29a6410f0e7414d3208786ba0a699043539c4534c821e8ce229a6410f4a7014d32086a6b80a699043d25c0534c821a92e029a6410e4c53181320862fbb2a619043c3951320c821e1aa89906410ec532984320872731a65288438b59742d0421c5aa8b148210e1e54d8d410870eaa6c6a0843879506350421c3aa831a8210e2e54d894108716aa6c4a08438b9506250421c5aa83128210e2f65d09410871d2a6c0a08438e5536050421c74a83028210e39541814108755a10c0a0843179cf65104218bae7b288210e2e54588410871ab2a8220843a95894110421b60e0a088210e2e5498b3108716aa4c5988438b95162cc421c5aa8b166210e2d5498a3108726a9cc5188438b551628c42187ce9b286210c3d74d94310861f3a4ca188430f5d2650c42187ce83286210c3d74194310861ebacc8188430fdd5640c42187eed2a06210c3d76950310861fbb2a8188430f5d9540c421c98ca9906210f15544c4310870f2a4c7908438755263c8421c3ca8b1e4210e1d5458f2108666b98c990843a395163c8421d1aa8b1e4210c6d7694a21086a6b9ca5108431d5da5288421b8ae72944210c6d759912108717b2ca8908438bd9554484218deeab1a4210cac7458d2108674382c690843335cf61484219c8eca0a4210ea46450521086e239a8290843781c141484219cced98a4210da5740c52108762b1862908438dd965448421c6ecaaa24210dc67394921086733b48490843399d83248421a74e1b24a010d3a70192500861f3a4c7280430f5d2639402187ee8b1ca010c3c7458e500869d384a8a80434e1c15454021c3ca9b1aa010e1d54d8d500870f2a0c6a8043875506354021c3ec9b1aa010e1c64d8d500870fb20c6a8043871906354021c9ce431aa010e4d7218d500872cb80c6a80431b9da3254021c98c7192a010e4c634c9500861ebb4a8280430fdd95414021c3ca9318a010e1d5498c500870f2a2c6280438755163140218f6eca80a010e596354050086a7396a729e81559c75394f408dce5b0aa7a046d72d8553d022fbb2a629e81539cf5294b40acce3a94a5a045e73d8552d022eb9ec2a96811bdd95214b408ece332865a04757199432d02a6b94a619681535ce520cb40a9eea99065a054d754c832d02e43826419681b24c9600cb409e0e2b0065a055673d4651d02b3396a328e811ddd951147408dce5b2e63a046d72d9731d0333314a398e819998951cc7408dce532863a046d7299431d030f322a618e818d991510c7408bce7b2e43a045d7
  | 32 => 0x38e1906054d21cb6c6302a690e6b621815348739b08c0a9a438edd06054d21c70e8302a690c5f7654c534868e3a2a629a43561c15314d2187ee8b00a690c3c74580534863d386cba1a431e5c365d0d218dee4b2e8690c6e7598b43486363aac5a1a431d1d561d0d218dae5b2c8690c7a70d96434863cb86cb21a431bdc96550d218eee2b2a8690c7b70595434863c382caa1a431b5cb6510d218eae3b288690c7b70594434863c382ca21a438d15161d0921ca8a6b0e6490e4e654c8324862fb9acaa0a43171cd6550521c3ea831a8290e1c5418d41487162a6c4a0a438ed506050521c70a83028290e4f5358b314872629ac598a43535ca538c521a38e8a9c6290d587054e314861fba2ca98a430f1d1654c5218bcec29a6290d4d7294c31486aab8ca618a4317dd9530c521a38e8a986290d587054c31486963a2a710a435a1c15388521c76e0b26a090c7b76540504869c3a2a028243561cd501412187ee8b18a090c3c7458c50486c6b98c52a0434b9c86395021a6ce231ca810d1e7318a540868eb98c52a043479cc6195021a3ae630ca810d1e73d82540868eb9ec12a0434b9cb6095021a6ce3b04a810d2e7298d5408696392c6aa0434d1c56355021a76e0b1aa810d387058d540868f39cc4aa043475ce6255021a74e1312a810d39709895408697394c0aa04347dcd6055021a38e6b02a810d2c72581540869a38ac0aa0438b188605502187eecaa0a810c3e70993530861e382c9a98438b59262d4c21c6ac930ea610c3f74583530861e3a2c1a98430fdd16094c21878e8b04a610c3e74d81530861eba6c0a98430f5da5414c2187eecaa0a610c5f7654c530871d2a4c0298438e5526014c21c74a8b00a610e3954580530872ca9ac0298430f9c26414c21878e0b20a610e3a64980530871cb24c0298438edd26014c21c70e9300a610c3f74580530861e3a2c0298438e9916014c21c72c8b00a610e5a635805308735312c0298438edd16014c21c70e8b00a610e6872580530873838ac0298431b9c865d0c218ece232e8610c7a70196430863cb80cb218431b5d66290c219cae33148610e2d5458a430863db82caa18431e1c16550c21c5aa9b128610c6d751894308716aa0c4a18438d5536150c218eaea30a8610e3554185430863d380ca218431e5c06510c218daeb3108610e2e54588430863abacc2218438d9516110c21c5acb2a68410ce77158f4208667b9ac3a1043179cf65908218bae7b2c8410e3554586420862f39eca21043175cf6510821c6ca8b088410e2d659904208637bb2a8210438b99154108218deeab088410ce7755844208733baac221043a99516110821d4aa8b088410ce47058442086acb80a7990438d552618c821c6aa8b0c6410c6d751923208672b88c9190435a5c0538c8218deeab0c6410ce775586320873
  | 33 => 0xf218bcec2a2a790d4e7299153c86abb8ac8a9e43479d26254f21a3ae9312a790d1f7458553c868e3a2c2a9e4356dc16154f21ab0e0b0aa790d1e74d8153c868eba6c0a9e4347dd16054f21a38e8b02a790d4c7258153c86abb8ac0a9e43539c86054f218beeca98a790c3f7458053c861e3a2c029e439354e62d0f21c9aa6b168790c7a7019643c863cb80cb21e431e9c26550f218f2e132a8790e555318543c872b29cc221e439594d6110f21a74e1aa68590d3a70d5142c861f3b0a8a16430fdd95410b21caca73088590e565358442c872aa9cc3196439594e610cb21c9aa73168390e4d5358b41c862ebaec6a0e43175d463507218bced29a8390c5c7654d41c872729ec4a0e439354f6250721c5ca83128390e4e5318941c8726a98c4a0e439694f6050721cb2a7b028390e3a5418141c871caa0c0a0e439694c6050721cb2a63028390f165350441c86d83828220e439354e62cc721c9ca6b166390e4d5358b31c8726a9ec498e439354c624c721c3cc92986390e1d6494c31c870f322a618e4387591530c721c3cc929ea190e1d6494f50c870f322a7a86438759153d4321a74e9a84a190e1f6494d50c870e324a6a864387d915354321c38c8a9aa190e3970d9150c862ebb4a62864317dd953143218f6eca80a190c3f76550548870eaa2c62a443879916315221c9cc6b10a910e55639845488732b14c22a4439958a61d4e2187ee8b06a710c3c74583538861fba2c129c430f1d16094e2187ce9b02a710c3d74d81538862fbb2a629c43875915314e2187ce1320a710c3c70590538870eb24c629c438d5926114e2187ee8b00a710c3c745805388672392c3a1c431e9c36590e218f2e1b2c8710e4e5358a438863d384caa1c431e5c26550e2199ee6b0e8510e35541854288636bb6a821443395c4648ca21caaa630a6510c6e7694d32886a73b4a699443939da534ca21a9ae129a6510e4e53181328868eb98a9a0c430f9d85450621a3ae62a28310e3b54181418871c2a0c0a0c43aad08605062187eecaa08310e1d6494c318870eb22a618c439394d620c62199ae63264310e4d6598f2188726b2ac790c439559663c8621caacab1e4310c3e7498e508861eba4c7284431b1d932542218f6eca80a110c5f73586544862e39ac32a24387d906355121c9ec7b12a890e4c63d89544872a31ec2aa24396d8f6055121cb0c7b02a890e6b62d81544871db20c0aa24396d8c6055121cb0c6302a890e6b621815448739b08c0aa2438edd0605512187eecaa0a890d1c73550544869c382a82a2430fdd160d4d21878e8b06a690c3f74582534861e3a2c129a430f9c36454d2187ce0322a690e1c64d8d5348716326c4a9a438d1936154d2187ce9b02a690c3d74d81534871db26c0a9a438e1936054d21c74e9b02a690e3974d81534871db20c0a9a4
  | 34 => 0x2a818c3f76550540c70eb2ca9a186335dc562d0c3199ee4b0e8618e3554586430c71b2a2c221863875966410c318beecaa08618e1e64550430c62fbaac22186335dd56110c31caeeab088618e9654584430c74aaa2c221863351c16110c3187ee8b04a418c3c74582520c61f3a6c0a90630f5d3605483187aed2a0a418c3f76550520c637bb2a4290638e9526014831c72a9300a418e3a54580520c71caa2c0290639a54960148319aae331c8418e1d5458e420c63db82caa10631e1c16550831c3aa9b1a8418e1d5418d420c71aaa6c2a10638d5506150831c3ca8b188418e3654584420c71aaa4c3990638d55161cc8319aae23266418cd775587320c72bbaac399063a595161cc831d2aa8b0e6418cd470587320c62ebacc899063355c4644c831c3ecaaa26418dc671d49320c6673b0a499063c3950524c831e1aa82926418dc970149320c7872a26419063c3551320c831d8a653086418e1d65d0f410c70eaa2c720863879536350431c3aa9b1a8218e1e5418d410c70eaa0c6a086387d974350431c5ca9b128218e2d54d89410c7172a0c4a08638b5506250431c74a9b028218e3954d81410c71d2a0c0a08638e5506050431d36863028218e1e5458c410c71ab2a8220863a558d4110431b60e0a088218e2e5498b310c716aa4c5988638b95162cc431c5aa8b166218ccd72193310c7472a2c598863a355162cc4318baed29c6218c757694e310c6e2b94a718863175d6644c431c3ecb2a26218e1f65551310c66a3b28298863a5191414c431b88e4a0a6218dd070505310c71bb2ca8988638dd95544c431b8ce529a6218cd67690d310c66b3b064988634e9c36494031a74e0324a018c3e7498a500c61eba4c5280630fdd16294031878e8b14a018d3a70951500c69c382a8a80638b9536254031c5aa9b12a018e2e54189500c716aa0c4a80638bd936254031c58c9b12a018e2f64189500c716320c4a8063939cc6254031c9ae6312a018c5e76cc9500c72631664a806393189325403187aed2a0a018c3f76550500c7172a4c4280638b5526214031c5ca8b10a018e2d54588500c63dbb2a0280639a5895014031c9cc7316a990e4d6398b54c872d31cc1aa6439658e60d5321cd4c5306a990e3b7498354c872d31ac1aa6439658d60d5321cd4c4b06a990d3a70d5254c869d386c8aa6430fdd95415321c9ac7310a990e566358454c8733312c22a6439998961d4f2187ee8b06a790c3c7458353c861fba2c129e430f1d16094f21ab4e1aa4a790d5970d5253c86aab88c929e43479d06294f21a3ae8314a790d5a7018a53c86acb80c529e43479d36094f21a3ae9b04a790d5571d8253c868fba2c129e43471d16094f21a98e4b04a790d577158253c86a7390c129e430f9d36054f2187ae9b02a790c5e76d5153c86ad386a8a9e43565c35454
  | 35 => 0x58252cc6a7398c1296630f9d36054b3187ae9b02a598c6e76d5152cc6b5386a8a96635a5c35454b318dcec2a2a598d4e7399152cc6b3b8ac8a96634b9d26354b31a5ae931aa598d2f7458552cc6963a2c2a96635adc16154b31ad0e0b0aa598d2e74d8152cc696ba6c0a96634bdd16054b31a58e8b02a598d4c7358152cc6b3b8ac0a9663539cc6054b318deeca90a598e4e6354b42cc726b1aa5a1663995486150b31ccca53088598e665258442cc732a94c3996639994a610cb31c9cc6a968398e4d6354b41cc70f2a0c6a0e631b5d762507318daea3128398c6e7694941cc727b1ca4a0e639318e52507318d8eca928398e4f6354941cc72631aa4a0e639a94b6050731cd2a5b028398e3a5418141cc71caa0c0a0e639a9486050731cd2a43028398f265250441cc6d83828220e638b99252d4331c5ac9296a198e2e6454b50cc716b22a5a86634e9d35094331c5ec9292a198e2c6494950cc717b22a4a86638b1915254331c72e1b22a198c6d7694850cc637bb2a4286631edd9501433187eecaa0a918e2d54588548c726b1cc42a4638b9916215231caac7308a918e6562984548c667b92c3a1c638d5506150e318baedaa08718c3f74582528c61e3a2c1294630f9d36054a3187ae9b02a518c6f76548528c716b22a429463351cd61d0a318f4e1b2c8518c7970d96428c726b1ca521463355c464cca31a9ced2926518e4e76949328c6a6b84a49946393948604ca31a5ae42a68318c3e76151418c696b90a8a0c638ed506050631c70a83028318e9b43181418c61fbb2a820c63335c864cc631c9acb3166318e4d6558b318c732b2cc598c639959562cc63187ce9314a118c3d7498a508c62e3b264a84631edd95014231c9ec7b12a898e2f64189544c727b18c4aa2639918b6155131cb6c7b02a898e6b62d81544c734316c0aa2638ed906055131cb6c6302a898e6b62181544c734310c0aa2639cd846055131c76e8302a898c3f76550544c696392a82a2634e1c15415131c68a8b0e8698c3f74583524c61e3a2c1a92631bdd95214931a58e8a90a498d6870548524c61fba2c0292630f1d160149318bceb31e8498c7b70594424c63c382ca2126393995320c931c38a9b1a8298e2f54189414c7162a0c4a0a638ed506050531c70a83028298e3b70593504c63dbb2a0282634e1d15014131ad0e4a80a098c3f74588504c61e3a2c428263635c86395031a5ce431ca818d2d7218e540c68f398c52a0634d9c46295031a5ce430ca818d2d72186540c68f39ec12a0634b9cb6095031a5ae5b04a818d3671d82540c697394c6aa0634b5ca6355031a74e131aa818d397098d540c68f39cc4aa063471cd6255031a68e2b12a818d3b70589540c69c382c4aa063479ce6055031a38e6b02a818d2f72581540c696392c0aa0634d1c56055031c38c630
  | 36 => 0xa968428283ca14b4214141e36a6a10a0a0f18535085050795a928428283ca1494214141b60e2a10a0a0f5053d0450507b02968228283c6d4e4114141e30a7208a0a0f2b52904505079429482282834e5cf6414141a72e5b20a0a0f3271d90505069cba4c6282834edd16314141ad6e4b18a0a0d687258c50506b9b8ac6282834e5d06314141ad4e4318a0a0d697218c50506b8b88c6282834e9db4314141a72e5a18a0a0d3a71d0c50506b9b8a86282835c1c54314141a74eca18a0a0d387650c505078db9a86282834edc94314141e66e2a18a0a0d387150c505079838a86282834c1c54314141a72e9310a0a0d3b7458850506adb9ac428283561cd6214141ae6e2b10a0a0d397418850506ad398c428283565cc6214141ae2e2310a0a0d3a76d08505069cb9e84282834e9c74214141ae6e2a10a0a0d7071508505069d3b284282834e1d94214141a76e6a10a0a0f2b725085050799b8a84282834e1c54214141e60e2a10a0a0d3071508505069d3a664282834e5d33214141ae4e3990a0a0d7171cc8505069d3a464282834e5d23214141ae4e3190a0a0d71718c8505069d3a264282834e5d13214141a74e8190a0a0d39740c850507a499064282834e5ce4114141a72e5208a0a0d5b7350450506ac39a82282835adc94114141ad0e4a08a0a0d4e72d4e5310637390c0a98831b5c86054c418beeca98a620d4e73d4a521062f398c0a9083175cc60548418deeca90a420c7b70595321063c382ca990830f5d7644c841a9ae52986420d4d7394832106a7baa6419083535d5320c84187aed2a48220c7576952411061f386caa088387d976350441c3eca31a8220e2f65d894110717b28c4a0883a318c6250441c76cbb028220e3b65181411074db18c0a0883a618c6050441d56c43028220ea862181411071dba8c0a08838e54c6050441c72a43028220e5765d8d411072bb28c6a08834d5d64350441ccecbb128220e67651894110762318c4a08834d5d64250441ce6cbb028220e73651814110759b20c0a0883b418c6050441dc0c43028220c6f7258e5010636392c72808317dcd62940418b8e6b14a020d3a70d06501061e3b283280834e1c141940418f6eca80a020e4e6398b54cc72731ac5aa6639698e60d5331cd4c5306a998e696298354cc71dba4c1aa6639698d60d5331cd4c4b06a998e696258354cc69d386a92a6634e9c3645533187eecaa0a998e4e6358854cc72b31ac22a663999896115331a74e1aa68798d3a70d5143cc61f3b0a8a1e630fdd95410f3187ee8b04a598c3c7458252cc6b5386a9296635a5c35494b31acae2324a598d2e7418e52cc696ba0c7296635a9c06394b31ad2e031ca598d667110e52cc6b2b8887296634b9d36094b31a5ae9b04a598d6571d8252cc697ba2c1296634b1d16094b31a98e6b04a598d6771
  | 37 => 0x8d9d46150941d2ea630a84a0e94531854250753a90c2a1283a914861509418f6e0b2e64a0c7870597325070f320a7992838759053cc941c5cc9a9664a0e54539873250733a94c3992839514d61cc9418f6e0b2c64a0c7870596325070f326a7192838b990528c941c5ac829464a0e57539863250732294c31928399149618c9418f4e1b2a64a0c7970d95325061f3acc8992832d1c5644c941970e0b2264a0d4e72d4d32506a739ea4992831edc1650c9418f0e0b2864a0cb471590325070f320a619283535c8530c941c5cc829064a0d4d7314832506a73aa6419283531d5320c941c9cca99064a0e4c654c832507a2298a5a0a83c314c52905418dce531ea0a0c6d7298f505062f39cc5a8283175ce62d4141e32c9a9ea0a0d6a7294f50506b4b94a7a82835adc953d4141ad0e4a9ea0a0f197414f505078cb20a7a8283c614f43d4141b60e2a1ea0a0f4b53d4b50507a429ea5a8283ca59352d4141ab4e7296a0a0d597394b50506adb9aa5a8283561cd52d4141e96a6296a0a0f485314b5050794ba0a5a8283ca59052d4141e50a5a16a0a0db07150b505069cba6c7a82835a9cb63d4141ad2e5b1ea0a0d7171d8f50506b5394c7a82835a5ca63d4141a72e831ea0a0d3974d8b50506ad39ec5a8283565cf62d4141ae2e3b16a0a0d5a7398b50506acb9cc5a82834e5d062d4141e9264196a0a0d5a73d8750506acb9ec3a82835a9cb61d4141ad2e5b0ea0a0e4f5398a505072629cc52828393d4d6294141c98a6b14a0a0e4e63d4a5050726b1ea5282839398c5294141c9ac6294a0a0e5a63d42505072cb1ea1282839a98b5094141cd2c5a84a0a0c5e76d4d505062f3b0a6a828393d4f6254141c98a7b12a0a0e4f531895050726298c4a82831b9db5254141c9ec7a92a0a0e4c63d4950506373b0a4a828393d8c5254141c98c6292a0a0c7b7654050506adb9aa028283561cd5014141ad6e4a80a0a0d68725405050637b92c6282831b1c96314141a74e1a18a0a0d347150c505069c382862828317dcd62141418b8e6b10a0a0d3a70d08505069a38a84282834e1c14214141a74e1208a0a0e5a65d4c505078dba6a628283c6d9353141418f2ed298a0a0d6a7294c50506b4b94a6282831edd95314141ad6e4a98a0a0d687254c505072d328a628283c65d05314141e36c8298a0a0d3a75d0c505078da9e8628283c614f4314141e36a6a18a0a0f185350c50506d838a86282839a9975214141e96a7a90a0a0f4853d485050795ba6a428283cad935214141e5687a90a0a0f2943d48505063cbb4a428283569ce5214141ab2e7290a0a0c7b7654850506adb9aa428283561cd5214141cd4ca290a0a0f4b5314850507a4298a428283ca5d05214141e56c8290a0a0f2b431485050794a18a4282834e9d74214141e36a7a10a0a0f1853d085050795
  | 38 => 0x418beeca98a7a0e4d5358853d062fb9ac129683171cd6094b418deeca90a5a0e4d6354852d065a38ac8996832e1c1644cb41a98e4a9a65a0d4c7354932d065aba0c2996831e9c3650cb418f2e1b2865a0e4f654c832d0726b2a6419683475cc6494341a5ae4324a1a0d387050e50d069c38285286831b9c863543418dae431aa1a0c5e7318950d062eb98c4a86831edd950143418beeca98a720c6f76548529069d38683284831edd950142418dce5306a6a0c6d729835350727b14c5a9a83475d062d4d41aaae2316a6a0d4f7258753506a6392c3a9a83475d360d4d41a9ce5b06a6a0d4d72d8353506aab8ec1a9a83539ca60d4d41a9ae5306a6a0d1f745835350727a9cc529a8393d4d6294d41cb6a7304a6a0e5b53582535062fbb2a629a8353dc95314d41a98e4a98a6a0d5b7054c53506ac382a629a831bdc96014d418d8e4b00a6a0d1d74d8853506aab8ec429a83475d06214d41c9ac4310a6a0d4e72d8453506a6b96c229a83475d36014d41a3ee8b00a6a0d4f7258053506a6392c029a8355dc56014d41a3ae8300a6a0d4e7218053506a6b90c029a83555c46014d41c3ccba9e86a0cb47158b435070e29cc1a1a832d9c660d0d41ca8a730c86a0e5753185435065b3a8c2a1a838d9d46150d41d2ea630a86a0e9453185435062f39cc1a9283175ce60d4941ad4e129ea4a0d697094f52506b5b82a7a92835a1c153d4941e1ae829ea4a0f0c53d0f52506d238a87a928393d8e63d4941a5ae831ea4a0d657118f52506a7b9ac3a9283531cd61d4941a5ae9b06a4a0d4e73d8352506a6b9ec1a9283595c760d4941a9ce7306a4a0d4d739835250697ba2c1a92839398f5294941c9ac7a94a4a0e5b53982525072c29cc1292839ad4a6094941cb6a6b04a4a0e58535825250735a92c129283179db53549418bcec29aa4a0e5b53d81525072c29ec0a928396d4c6054941cb0a6302a4a0c6f7654852506a7b9aa429283531cd5214941ad6e0a90a4a0d6870548525062fb9ac029283171cd6014941c9ccba98a4a0f0d64d4c5250636bb4a6292835a9c25314941ad2e1298a4a0c6f7654c52506b5b82a6292835a1c15314941c9cca298a4a0f0d7414c5250786b20a6292834b9d74314941e18a7a18a4a0f0c5350c52506d238a86292834b5d36314941acae3b18a4a0d2d7418c5250726b18c62928359dc54314941ac8e2a18a4a0d4e73d8452506a6b9ec22928353dcd4114941a98e6a08a4a0d2d74d805250697ba2c02928353dcd6014941a98e6b00a4a0d67715805250696ba0c029283539cc6014941a9ae6300a4a0d6571180525065a38ac7a12838799453d0941c5ccba9684a0f0f5314b4250786298a5a12838b14a60d094196ce330684a0e6452986425072a29ec2a12839514c6150941ccea430a84a0f0c53149425065b3a8c2a1283
  | 39 => 0xa91965563984548cb1b322c22a465999896115232cc8e4b08a91962d54189438ca1fba2c128c650f1d1609463287ce9b02a31943d74d81518ca3bbb2a228c658d5915114632ad2e1994a11943e74986508ca1eba4c328465569c332542328f6eca80a11963764185544cb2bb18c2aa26599d886155132ce6c3b02a89967061d81544cb1db20c0aa26596d8c6055132cd6c4302a89967361181544cb38308c0aa2658edd0605513287eecaa0a89953471550544ca9c382a82a2651edc161151328f0e0b08a89962c5458b434cb0e2a2c7a12650fdd160d4532878e8b06a2994b870590514ca3bbb2a228a654d1d15114532ae0e0a88a29943e70990514ca3db82c828a651e1c16414532a70e0b20a29961f73590514cb0e39ac828a658bdc96414532c58e4b20a29963471590514cb1db82c828a650f1c16414532c70e0b20a29943870590514ca1fba2c028a650f1d16014532c76e0b26a09947b76540504ca9c3a2a0282655c1c55014132ad2e1990a099559708c8504ca1fba2c2282650f1d16114132c76e9306a81965a63583540cb35312c1aa0654e9c35495032a74e1b22a81943f76550540ca2ebb4a7190651b5da538c832c9aebb2a64194ce70d95320cb273b6ca99065539c7654c832a9ae1b2a641954d75991320caa7baac89906571dc5644c832b88e2b2264195cb70591320cae4382c899065a3590644c83299cedaa264195ca70d51320cae4b86a899065339d8544c832a9aeb30a641954f75585320cac7ba2c299065631d1614c832b96e0b0a64195c870585320cac73a0c299065635d0614c832d8ac230a641958e74d81320cac6ba6c099065535d6604c832a9eeab02641958f74581320cac63a2c09906571dc5604c832b88e2b02641964d75181320ca67bb265a88651edc164944328f0e0b24a21964f764ca510cb263b26528865d1dc53294432e88e2994a21954c704ca510ca1fba2c1288650f1d16094432c9a64b04a21943e74d81510ca1eba6c0a886533dd93214432d1cc8990a21968d644c8510ca3bbb2a228865b24ca6014432d9264b00a2194cf764cb500cb4732265a8065a359132d4032998ec994a0195c8704ca500ca9d3a6a1280650f9d2619403287ae930ca0194cc764c9500cb47b2264a8065a31913254032b90e0992a0196c532d85500cb62990c2a80658e5c36454032ab4e1992a01956a708c9500caac38264a80655a1c13254032c9eec992a01954c764c9500cb263b264a8065c3d913254032e18c8992a01974b704c9500caa638264a8065d21c13254032c6ec9b0aa01963464d85500cba2996c2a8065934c86154032c6ec830aa01963464185500cba2990c2a806595cc86154032ccc6430aa01965532185500cb32990c2a8065914c8615403299eec990a01947b76540500ca37b92c129e831b1c96094f
  | 40 => 0xa0038000000000000000000000004000800000000000008000000000000180000010008000000a00080180000000003000c00080080070000001000000000000000000000801e000001200080000038000000000000300140000000003800200080060000006001801c0000008001800e0000000000000200280000008016000000000080020030000002002c00100000000008000001400100020000002001000200b0014000000800500000048000008000800500040000000003000200000160000000000000400280280010006000800000000000008006006800800080160028002000800c0000000001000a001c777158252d0e3a38ac1296871bdd95214b43ccaa4b08a5a1c6f7258251d0e36392c128e878b9d06254743c5ae8312a3a1c777654451d0f32b12a228e874d5c464943438f6eca80a1a1c6f765485290f34a92c0294871ddd95114643a74e1a1ca121c6f725865090e36392c3284871edd95014243cd2c4a80a121c6f765485250eb238aa4292875a1c152149438eee2b00a4a1c74715805250e3bbb2a228a87591c95114543ae0e0a88a2a1c6f725805150e36392c028a871edd95014143ad0e4a80a0a1d70715405050e9d38486282871ddc562141438e8e2b10a0a1c6f725845050e36392c2282870f5da5490c438baed2a48621c3e70d954310eb338ea5290871bdd95214843acce5a8ca221c77765445110e9d38687280870f1d94394043a70e0a1ca021c777158a5010e3a38ac5280871bdc961940438d8e4b0ca021c7b765405010e3bb8ac129e851d1c56094f428beeca98a7a16555358453d0a2fb9ac128e85171cd6094742c3ce831aa3a161d7418d51d0a3bbb2a228e859558d5114742a6ae2324a1a147b7654050d0a2fbb2a629c859654d6014e428eeeca88a32153a70d0a5090a2fb9ac328485171cd61942428f6eca80a121659635405090a2fbb2a629a85551c55314d42ab0e0a98a6a1477715805350a3a38ac029a851ddd95114542aa8e6a88a2a1570705445150a2fb9ac028a85171cd60145428f6eca80a0a1558735405050ab838aa0282851ddc563141428e8e2b18a0a153a709085050a2fb9ac228285171cd6114142aace3a9ca62145f7654c5310a1ebb4a9210851b5da549084287ce1b2a842155673d465110a3bbb2a2288851ddc563940428e8e2b1ca02153a70d0a5010a1e3b285280854e1c142940428bee6b0ca02145c735865010a3dbb2a0280859398d62d533287eecaa0a9996355458454ccb2731ac42a6659958a6115332c6cc8b08a9996566358454ccb2a39ac22a665875506350b3287ee8b04a39943c7458251cca1f3a6c0a8e650f5d360547328eeeca88a3996356454451cca1f3a4c3286650f5d261943328f6eca80a19964d6398b548ca1fbb2a82a4658d5516115232c9ac7310
  | 41 => 0xc00180020080014000800600e000a002000c00080020008000000000e00180060000000000000e00680160000000003001a00080080018010003000000000140010000000000400000000040002000001a000000200000020018000009000e0098012003801600080040010002001000000000000040000004000400180020060000000000a0008000001001c009800e0008000000800e003002c000000800000020010004000800a000800600100040000002000800000080000000006001800600080080000012001800600180000030004000002c002801400000000018000003800200300020030000001001600000040000002002000c000000000280040000002000001400280000028004002000200180080008000001800000400160000008000000000200060020010000000000080000008006002000000080100000004000800600000040010000000000000000060048000000000e003000a0000008000000c00180080000002007801a001000200100060000000000000e0000014000800a000800000500080008000002002200580000030014005800000000000000000001000600400000050010001800200000060018004001000200100020010002001800c000000000000000008002005000600000020008004000000c000800a000000c0000000000001000280000000004002000a000000200000000058004000800800200000000000001801a00000000058014000001600680060090002004000800080020000002000000000000000010002002000600000100038002000800c0070000000000c00580060000000000801600000000000006001800400000000068000000001c002000200a8016006000200500040000008001800000180020008000000800e0018008000002c0028006001800400580060058012000800400000100088000000000200080040058002001000a00000040008000001000a00000000048000000800200280040030000001000000000040060000000000c0008008002000200000000010000000800a0000008000000600000060008002000002400080020048002000000a00000000000004000000c00d8004000800000000160018000004000e00000000000012000001000000020000010002000000080020000002000000800100040000000001800000000060038000000001c0020002001800200380000058000000000a000000000080000008000002001600080000038002001000200000140008002001800a000000000700060060000001000a000800200000020008014000000000000100000000001000201f800200100000018004000800000200080040006002800800000120000006008000800080140020004002800400200000000004001800400000000000004002000000
  | 42 => 0x5000a00180020010000003800400100000038008003000400600000008000002000000700060008002000000000080040028004000001400380000000000002000600000020018008001000a003000400b801e00780000030000000000000000000000006000800e00100000008000000000800c8000000001200280000000012000000801080020008000001000200080040040008000800000480000008008004800a00180000000002002800200180000000000000000c00700100000000000000000000000000000002800a00200020008000000800200080060000004000000200800000000002000800c002800400300000000006001800400000080000000000800000180060018008000800400000020000004002000800080000000002001000000080040010004000801e0000000013000c003800a000000a0000010000000000380000018000006801000100000000000003000000080060020000000800400000000040012005000e00180060030002000001200080040020000005000200380040000002000000800600000000002000000400000020008000000000200300060000000000800c0000002000000a000800000080040000002004800400180000048000001800800700000020004000000e00180000010000000800e0098002002000e000000000300040000002001801400200040030008001000a00480020000000001000200000080018018001000000180020008000000800000280040030002000000a00000140048006000000a0008002000000a0008000005800800000000038000000000000000000008000000800000100020020002006001800380040000002000000000a000200000100000000002000000080100010008000000600000040000000000000000000000000002000000c000000400180020000004004800c0010004002800e00280000008000003001600080000010002003000200100080000000003800a009000e001000a0080010002002600100000000002000000a003001000000000008006000000000500020000000000000800100020008008000000800d0004000000c001000000080000010024003000000100000000000000001800100040010000005002a00100000000016003800200200000000000001000a000000200000180028008000800000100120010012006000c00000000010012001800000080020000000002002a00180000000000000000000080000028002002800000280020060000001800000000060020006000000000000000000012000000e0010002003002000300000000014000800000000000008000002800a0000000000000400000000008000000001e001803600100000008002002800200100040000008000800800080080008000001800200400
  | 43 => 0xc00000080000000003800800000080030004002001800280120010000000000e0000000000000000180000000004003000200080000000000000000200080040098004001800800000060000002000801000580040000000000000000200040000004001000c00080000000004000000e002801000000020028008003000a00680040008004005800000300000000006000000a003001800680180000000008000000580000008008000000000780100050004001800a0010008001000000380160010010000800200b80000020000005801400000060000000001000400000000010004000001a001800000700020020000000800000f00000020008001800200080020010000001000200100020000000000800400400060000016002800000100020000002005000c00000020000004001000200000040008000003800e00000080050000001000e003000000180040048006000000000200000000020000000c009000c0030000004000200080000010002002000200100020020006002800c001801e00100040028000000800600200000050008000000600000000000002000000000480060000002003001400080020018004000800000000000010026000001a0000002002000a00100060018006002800200000060078000004001000000020090004000800800000060000000007000c00180080010000003000600080000000006002000600080080000006000000000000060000000000000000180020000010000800000000000010000000000200100060018038000000a00400020038000000000000000000010000001800c00080160028000000000c0000002001000000080000060000002000400280040038000000000e00000060010000000803800580060018004000000a00300160040000001000400680000030012001800800080000000000002000000000040000002000003000100020000006001003400780000000000002000000300000028000001000800000060020004000000000080280020000000000000300020000000004000200300160008000003000000000120000000000000000b80020020002001000e00200000018000002000400480000018000000000600000000018000000000e0000002000800a00600000000002001800000000020000006000000c000800e000800000000020000000007000e001000200180040000004000800c001801000080000000000002800200100160010002000800600100020010002001001a0000000001000600100000000004005800a000800200480060030006000000e00800000000004000000c000800000000140008002000000c003000200180020000000001800e00100060038006001800200000000048012000000000580040000000000000000200000
  | 44 => 0xf2357043114180004e905c500008040000000000000064ac000000000002b0000648944b634c0000000b874924000000126d4b8955454056f50000858231d52b0115a1119a1885054d0513948b610f9c00000000003f1d81045bc4631fa852d00002dc671430c276466f0358370618d59c30f8000000000000000005650af40d9c763132c00000e841800000c5000000000010d03871114602c000000072d2a8000000000002d70000000000000004fb3be0e073ae0c355ef80005f2400057644af000175f0000f7f000100901a110e3fc8000099c00004047022e9c00029546cb1234b7e5898f4f1ed80003da4a0900009483e919b3163920136599de00003910db8000000038d1eb11e7000000010dd341122420f5378d4a5254c4100000003809a36000000000005b80de800000000000000000000032130c8000000000028b8fc44e9d9990cac74e55300570000000000000022b0000000000002ec51e1615424270c6904dec00017a400080000008002001000600000060010008000000800080000000004003000000000080040006001800200080100008002003801a00080000000012000001400100060020008003800600000000038002000000a000000000000040008000000800000180000000002000800200280100008012000000600180000010008000001a003800200200000000006000000000100020000000000001c002800400100000120008000800000080020018006000000000080020000000001800000080040000002000000a00000240008020001800400200020000002000001e00e8000000000200000000000000002000800300000020012001000400000020020014001000c00280080008000001800e01180000008000006000a00200000040002000000600600180008004006800e0000004000000200000080000012004800c00100060000000008000200280020038000002800a00000160058000000000800100000028042000800000000000060000000800000100000008000001000400600100020006000000e00000020000002000800e0000008000801000100020008010000000800b8002000800000a00060008000000800000080040070000000000000000000010000002000a001800e0000000000000600000040018000002000000000040000004000001000280000000000000000a002000c006800200380000008000000800200080000018020006000e001000000000000010004002000000180040010000001000000580340028006000000e000000200300000010000001000a000800a0018030000000c0010002000000200000000000006000001000100080000000000001c00000080000002000000a000000a000801200080040010002001000000000020018002000000000000080028
  | 45 => 0x60831483e249790670cc48992ec941943d85d31e6563c000157108b4b383b487c83db8c2700006290000000000152c000083e215d974000018c000000000006663f88112000132a07c0b8e2b1c53618180001fe8b2c0000b6f14607f200017cc0000000000000000009c20000e2f00015d200000002ffcff1000192d103cd1500010b3593c182000005000000003134c5f0000000296cb1b000000004ac00000000000000000000000023f92ac19f8000000000060b84750000000000000048a1492628902e68417df2cd95fb29715ec397558e58442be0000aa8599d05c000000000004e2000000000000c95b8c99326c80004d300003df40005515a572da19504c34000403400053a400000002d40000000000152f000046c000040309400000000646199c000000080815e59e92ab924500000005e100061425a1e66ec000000115300000000001789000000000000000000e70094c00054c8751000000000008d800015670000dee03e400000000005c88d02000000000000001554000493cf94415513852e803f29f16d50000b8900017770000cda52ec000483800000000000000000000000000000005884b4300006cc00009b11ff00002ff492700000000000b2924400004c6143f0ce02f24be855f0000000000051d000000000015ad000184f0000fdc000034a00000000ee157b0000a49000031114fc00063343d50000ee6000000000000000001421000142b0000e310000000000113f000000039b00004048410682c00033dc1b6494d27e00003130000a3d0fa81070bf48d40000d51078000000000001a0562b22d84a61f5d0980001879000000064e80000000dcc290d9023540e0b5edc63423e14331348e04000136b00813310000000090c9ff000000059d549d35d4af32f1800000008df102c000051431a0d34e2c000071500011db1d24c0d12940001f955da52401404e043af3dd400000010d300018d01574a0b19dd08f0864f540000d5f50a00002b040c247a88d600000005c0cfbe000109d000000000000000000fa7000000055e96840ec00000000000000087b59080000298f982430e95365c000000039e0000cfe0000000595100a20c53ff000136c19f00170000000605000012b4c6861f40006564b1c00017ec2b9c3c00e9971600000001774e4307943de19d102a1c5010547c138b50096ac0000000000112a0000e2800500000000000304c00000000006628bb1000014200000001f982a00000000000000020a00004cfd85e3ad40004604b4128d17b025951b4000000000005863a9400048949166a4400000000002ea8248593400000000000000ad82e5000016f483600000003964000000188000015ff00000000000000000000010257551e7400038401743848d9300002ea00019fb121c00047c80000001
  | 46 => 0xcb9e00000000be44c928280000bd00001c440003444000000115c1fec6170000000082864200000000000b3067e400052fd6e04f58cc100882b0546402500017e12ce800000014540000333430148400008970fe188e22e5a8000000001dc17dc00006aa165c8601a60000231400038fd3e81890e2a000000000019ff0000000000000000006414b2536552b00000000000312800041594891abc00000000000000000456101729ec00040dd63200000005f9082520512aa5eccc74045c02861a059928b544d37a82cd00000000000000000173d568d22c096800033240000000000000000000000000000726000000000000002f7cc3b566c0000000e790000000000000000000000000000171d281641d825561131400018fe000000026d8000000000024d8000000000000000000001730000000000014561170caa4ce91565b586056590e8632d17a20e8094667f8e673d040004b9c0006065371179c45d3dc11c338f000045e80000f2124c64009a21d6801851c185b0000dd00b3813b0000000000015d332800066443b30000000000000069f937e00016e765317741b147c53a5cb0a06fd8bb45cc0001b28faf61380eb67000000000c4513100000001002650cb6649697aa00000000000000669d5dd2db8b8828bc0000d8543a000169f2bd400049397413874e8000019ea15149401ccc24a00009ae38c091d564c3bf1490000000000000009c558ed9134fc407331680000000cdf1c190c865980005f18000000000069c400017840002a1140c673927827954794f20d7b4b012624a5090f3aac902000000027800b407c92ef3534000000000039f9725000000033e000023313f8544d0cd20d433e0c9869c57a989c000000008ec000000000000014e3190c0000c540001588abe17d800033e40000000bf90001350509531559651300b752ba1c3029e000000000006bd0000568204480207e80000f80000000141f375c51654a44ab11b893a2a307100000af000017213ad15e811c4000000000000000002a14000000000027a400062d8ba92b98000039c00025dc00000000001df000048ed6d20001700000125f6804000342502510cc8e755e4bd65d2967d2cc4c6c501d6bb000103a269800000011793644000324095d19158770001a7f0001988388d93b0000fb03c7427b00011685f000005840c7233fc0000524b4c09a987f08407a518b000005905310000b7f000000000000004e440005c2cb3d0000000610167e0000000652942a6981a5509c8ae44ff400000000003024e6d2210cb206e800063140000000ce0106400022d00005d6c000000000000000005388a5a4af4c3600012ab0000000348c000000074001dc0000c8800000003ad1080acb34e00000a480000000d490e6000015816ce000000000008462f0800055d4511
  | 47 => 0x96344e2766c453c00000002c506f517e40004d280002ca86204591a5f0000535000000000000000000000000000000008431d592e03ed877e242c0000000c5800000003adcb9a4f8800000000001360dab000000038280002bf142353397d26258000537d25c0000000000017600000a1000000000000005f0c000505861f00000002b84a1200000000000b1f232c000000000054400001255176000000000000000001663620800000000005a3400000012181824000000140f00000005d8d2432aa40000000ea400000000000000000128811c00001bfc00000009ac0000f792afc6a637a41d32c1c6e3000000020ad2f80b5c0002d3d53100008d1519079802fda290b4800000000000000dae0000000000049c64900604c1c0000000000000000000018a300013cb5ae58233f99a9a6998563547800041c0a32000000000000000000000000000000017a1000000000015f94a100002230b86467c0001f1cd5e00000004dbc0002a5c00000002041984000501400000000004b2000068d000024951bc098042234c46c800000002e88b6b000097b000061407bc5945ec95e10fe8000000053e3be96ae37fcda020580005e180000000bf24dcd1230000f365b5c6401e4400000001f7509d0725049a8629bd275213872046652c344140003b5000067300001a5000000000000000000624977b301c0006474000000131061a80000000000495d5c7144922602119b65acc14a5e712b7000000042547216974e404ef158d2df0fd669c961e47f039a28e07e3285037b113d9034cb41c74c440000000c912c000000000000285d1c257bc0000000445000093f00010ba5e4000022ac0000000fca00000003ea5596000114f18d43b92599804025cf9d586c67069c07640000000000000034a4446000010c0001493000000045fc000000000000000003ec80002f30294229576e62319c257992902b6546b273c0000d409210000e6a0d5c00000000002a941783538413000000037195e30001455441000017c40005cb1103000032c1728bee4150eae49408874e1c0001afcce73ac901051b01080000b76046400010ec0002070000588157721e589a1540000000127c09380000000000013c40700008db0b800003a14c484da800029d00000000000000000000009421d98c6e00017f606140005de05fa000077f61110cc4598490038478262b40002530c1640980000028279000094f60750a255fd0740f6000000854d632b90694f44c9c63116c11314d2c0658f6236ec97833b044b0f655d653f47d82cf88fa00006e55e056065620b0c274cb0868fc78b1cf182f00013fe000000000000000000a1d000071f00015730000000000146f000000042152fc0000000000000000000000000000000147800002765264e61000000008980004118a6b5fb
  | 48 => 0x68f9a610580be010394b12f600da18b80d2000145200005b668500002ff194d1bb9392000055347680000000ab626943995318f7400009aa000129954b80000f2c8950d6c00000000000000000539000000003b567b11b9000000000000000000000000146700007905fe8000340c000267c00000010b95f28f2e53bc000000000012fc00000000002ba4000000000015e000000003dd000000027d07bc4bb95a73e400005f3800042ec00000004de00000005ce400000000ff0e754cf6918f63000000000000000000000275400000000000000000352d9096a240000000d5a4ba0000475c7a20a6009100017d4539c0003868c0104d831f000000000000005bc0000091c000000017a39fc0005754000000000060dc2c757f0000621c0000000844000c00050d400000000005e0939500015810000f8b0424a0545c097253e000066102881d9cb805f08ed364bc1e901286162c4c000019413426fc42417542e4002038c00015f5257963a140897a21740005c1c22c67dce1e28c4000665cebf03511a84e6d12958d51eb4d9d1ad0001149312cc590000000000056e0000b5e60a44f85cfd356054163f0000bb5340061e000002900019cf5c38bdc24992b9000000048c185649547475fece7162352de28640b556ed22e000000000001c026700000ad85b527bc58700000000000f303f790140000ccd00003643c0451342c014e1e0122b5b40944096c00000002f3607c000301400000006d607cc000000000013c5a231e28e73593819424c16d4032800000013de23a03f5000000000f054f2c5c00064619813c0d98214ad8475000b6a0e916c91a141da23c8000000104d00000000000000355c02b29940004430f99114800068640003d7543d446c8bd24ec05627d536d19415611770000073000056011c11d7c1c956c4000114ccc0445400028e42270001692000058f00000000000f73000197915a400000009941b780005fac00049592a5598000013a4e4b31c150660c575900000000000000000052800002f10000f2d60080154ac876c12000005fc01de1a54c3800000006a156296558772241d9421be8000000197b000000000013ea64fc86234c000030858c35dad97e000063e00005672e3cdd408c4e2e1e1ca4761d45f20000c151441a545cb54bc00000004d70000000142e2b745570e7cdb5000000028a14754d64cba41cc3b700009e100000000b5519e2444000385047c0b84000415d4b5000000000009bd5fd400059c00001c20e440000000000000000000b65d811900a7549135ada176a0504055b87e04a7cf39000041700000000000000000000000000000001322589c000000000047402a749c97fc24bc00000000000000000000190f0000000238c00000000002c6400060fcbe300011e458d8de72a5824
  | 49 => 0x2859b00005e4c98204894a309b17ba000083b000056d44858d705a40002cdc9da53ed458000162f66011183fa57cb32ad5cd000000014b0df1424587e151c9ea47983ac4f6cbaf15f8ce863e802f3e4c00000f40003fa00001261494668c00005b090300018a52ae800045d13e700012d101fc00000000000000c03000000000000005cdc0003c1406b0000dd66678000321435846d97e762b932f57195db0000211000158700009cc59ec81a4f503e86028ceb684cbd025b0000620c1d51fd483f35495ca00000002370000000107b00000000000a9b00009583174317000000000000003990cef0000e88000000000000d016c07ab19e185a328c0190a884114229734501000000011e1651cfc900000000000de800006df067c05b00000000000a18000161800000000000000000000061d81b800015d72d100001934a7600014b3464899a5af4f3862a5a8a3ba886d00016df0000ad4535c4b755f00980254aff0000000000000000014ed0000e0c5bec65e0001a6b0000c1d641146200000000dd0f8707b8e32472c3c915c00c6000118805d452729fc00000000000000e6000000001c4d87158a80000000f2b0e5c000186086b0a853fb639d1940b9400000016aa2a481d2325400045c5788023c000000128f212000067489620d7926f5c10c71672930c1120ec33b5c00045a44aa0b3090100011f9000000033214c00000000000060100015a5000029f0000000000000000004d01508000605400036955663fd93724c008b50000fc53fe80f65a701b70804000010d4ca0000000000111c1578000000000000000002d5400000000006a60000555c2c01178000634951800000003ac45721034197000174b60e94680000d8020317434d5c00000012e421fc0000000dce000021500006f30000000649c000000150d00015c200000000000000000000000000000000be81791a9d00008400000000000051a00009540000e0016352ff00000000000000000193663fc00000000002eb15ab463c94b3295305000000000007c600006c00000000000000000000001c68000000042a37f400050b418900000540b6c00000000510000000000000032200000000cde000085f2da400000000000000ecc463061b4a5c7ce0ffc43e5b780004e4d34e30b000051c40000001a282fe909f699d20f0000b03000005e51f16da000000000000003aa91860b4cc8b000043f3fb07e20000000032c89000000000000372000000000011c000003ee21d060e036c7b814bca9d0e0428f6788d4569a4797069c01259a000047ec00054d09dc03f8ea92f9510900000002c1000000000004160e2005cd0f837ecc11098927f3d9c8aa07406e1039864f000000000000005e8c0006720000367411c0001348000000000010411cd000029b00000a8d541295c00000
  | 50 => 0x22595ae0001538422c00000000000000f2c000000000000000000000000000058704f45abd9be50c834200012775109a43506000000000000000fae00005cf00000000000000321d96722440000000c2f48198eb397857b277d3be07340001fdcbd742240001f34000465928c2bc46b239e09fa456400000000004f24000000119a3d18000648cb5123f5269437da6e5704479420c00039312230000000160800000000005609520428c000000000031b400006840005a012f4081596c000000050241b000015fd388503926005434045500321181207181ad2a4448a4ae02c35d9d152630000000019574c2cc8d3998000000000000000001f84d3b000148c0000c7800cd1070000705195cc9400008a944b81c43798b1d4d4ce9961482ab000083000009e46359895402174c28f923f140ca2152c800065a8f5b0001a1b0001444000000000000000001a48426c0002c9161d619000000012d057c00002ec0e451a759250000da906404f90000ada5e1c00036c000057c55b000000000000d6c51000001c61a954e601b209347d543bda1c26801c504810c203e06273a111b80838000000060200006f63d716a52bb0b394494f264e00bed2928ec10a419ad00016b411d826118ac53b00000001fa00000000a3f4fa4e5858b50f42e740006698c60204193d199169b0000c2e0000000000113a3a8cf72654c91c000166204f400002f40000001910000000000019d355491ca00011a929c42ff5c3180341988d2269ce1b00004b44ee472236fcb5d5069a742d68867477503d024d1d300eca27193156212653f54820a4b2f88c1c1dd050a099562556dcfa5394d4aa49f42f8137d5472ac0302153859f4e3d0bc2378ebb1fe400047e0b79516811e67b9134547c86f000057328a800000000005ef000027f40000000cd542940002d358af38580002e8d3e430280003bf4000000072c1e5134b307800034f00000000f373bccdd300011460000d343a4903b43040be53ad47f49a8e7400000004c9122a4814000287061568287b350800001b4c19347200002bb80000a5800e02a1766370434b05556f850ed295632599505e4c9a44815bf055898f0820ad159e8cd104a588b4ee000058c0af2473d1ee0000000000000000006d138183855c8110f000000015bcf0934c948b56c995a1a8d9e341843c251d16b654b40000001336208139c22c196d5da90fe0a10447001165d2e940002748dbc26210ea660c0000b885d900001b10000be74d7820b44dc138000017d00017480000fe3479447b000049e633c000000000026644eb07fc9f716a450d14e87a6003c000424d04b00000260001a0926d508d495000000008ae000179a28eca6017250050000b83324d1bf582cd64000000052700004c4cdaf4c241a80001a6a1ba4cb00bb57
  | 51 => 0x32d26bd1e32d1c0461ca0bb81aa000031240000000ba0000015a056400000011272ecd48a1dc4000022c000000114d0000ca70a988c60000cc2030c91400009905c680005a5ca7e4e940000000fa00000f8d0001a44168095931e5a5c4a1931b28580002fa91b500000003e0c00000002ad248c3fd43900002ad00000cd8000606d53e4c793ec687d5f60c70000000052a371c00046b014b269000019885fc56152df000000064d03070000e330000000000081f0000ef4000000068ccf58000117c00000000000000000000069b40000000d3322bd06061b827713b96fe3d152fb28a44a900006a76a38000000063c105800000015b400007d12d5000000000002880000000185f0ae40002581124000000001e8ce45e64000055000022b59545a2c12d00000005ce02550db4fc647152f507e40005a0898e00b00003b9151c000199062c400240c47273ee559d41950cb3898d0730894d800000006520000000000059e565b05c57503df8b0b22712b3000042b3d34000000134550d1084335050e0fed33c2b34dcd3714f9b5901a76311800010b06534ea080e227cd7c4ea82830110d764b3c86a2e280000000f6d00000001d40000061c21f0000aea310000000000004580000000188a000062f1078ab1000000019f4f4b401cab200014d304fcae0088c0780000000000000014700005a4000060d400000f90b819d48b25f78000068000044cc88b1e488710000edc0c41676000000000000001464000000000063c475452bd43900000000e0cd2e13f8000000093e00000002804dc445d416d06f54c357214f02d3844465bc000492c0000000ca8000000000003c61d28000000000000000004738000000000000000000000c105c09a2b583400000000004f48abd2bdc5254440000000000017008bf468c0000000000000153a2a1881d3dac0000ea0b0f3d00a1a046171f609d5034aa10fc00006d500000005408000689014700000005df00006648c6f040c65107b4000000194f3c48000525946a00000003db0345387c00000017f21e110755ccc00000000000000d013f54000000000000017d100000000000000000153500013b06a649cb6364ebc000103c000000000002024514000209d1b255683bd0000000000180866bc0001810fe000000000000000436400031d8e4d205c0000000000000000000000005f5d37a1a840005b0cdb10000000000000000004500e4000000000004f9494e2b3c00061c937d000000036204c1019c66361446f01d04148000185323dcf2114e05b9402d9ed19a513b022078c31980003288e2900000005f2066c00003783a340006a109082920ea62cec2e341bca525794c64000006900012310d7400000000002a3cb9806612642d0891f00013e1000121c00013ba4df10f9000000011bc0000
  | 52 => 0x5a60dec13700003188000226000000017080001795000087d0000639000000026e400000000000000ed10d040004230000000000000005f340798dc2f842703f6da5a53655a2000096f0000494016597c1df40001948000523800062f12a400000004fdcd9f1ba80000000b713c200003348f53180cfd2557c000256cb5801d800046712d7481da16101812f1a3431200005fe000010400007c0677c000386020900000fc4e648c334d5a5800000003b000002f3800052008b724902035518c2538acaf6000000059797fd66dcc8968357e064a816210e0db85d5027f3a58c5b2424f920964233313ca6734f956d184c000572cd674fe556f36d800008e8000000124433a400067d4000000043900011ab0000efe00000000000000000000000000000000000000169500000000001a4c0000fb700014ea51b800003d431826440002cf00004c98402000104400007e911ad7f723b400008e4f3b509880f0000000000000000004ec0000c6b00010e70000c7514a56ca0000ea857e8cc750bce3e0b194cb5f4c939657117e51380005d587fe000083948740003c2c000354c00029c00fb12c92ea24658fb1b240000238000396990623fc9b020b400000011511c740004d1c1a24218da45e018b80dd800000003e30001558000022049e4000642c00000009511550c860000000162c074075cdbd55f97f122780004594d0f037ccee00000000e4cb1200017ee00000000000000000000000000000000aaf00009e22e710f3000084b0000234553d9bd026c06264815de0b680004a7106b689400061991c400019c4000196500000002dc0334570199f13740004d180001c6400000017940000000000000062c96715e38bd3000178559b40001b34000000122f3bc4c6a10bc85644d80005efd49a086c3be48540000830b2d204d2ce66700006224f002f0d01a4f34430018401f3e1807c13381c200010c5431da395c4c1d10f7c4ca66e14f946282ec3374b3527b10990000fed515d1e81d9504c1a243d0486c0633ac189e00012274de4000596000000000003a802de36844ba000000037d835132f800000018be00000000000000425c00030615b60000000554494132584320e55a0c00001264d680000000000000000000000000000000000070937692030001463445d548115cd2f0001514000000000008f54a60a8d1280000511cfe72ed00003450dc023ed12200005b300000001dad6884b1c099058cb0934312320000ec6000158a19940002308000418800000000000000cce0000000238000051c80003ed071736dcd4365acadf5cc4f9e69147cb0000e9b000139a0000a7729e178f3f840003a7d2fd0000d81118425163c8eee000012c5af8000686800000001a55bfc0001c4829907f550700008cf5854000000000000000005d600000000
  | 53 => 0x93d300015d1462c4a726acf505fa12e6184000000019b9610d14b000145f6691035027d4a25ed523607887c1138ca4f40c0a695b019d1652d2b403a0f9a20e11b008dd56525557a0239800000000000001260000030e000057f692c7350000000228000000000005814000000000008d4000000171c00015ed00000003c680004af000000000005cb800000002c90001a6413d45a7691cdf00fdc000084c9d60f3807d000000023200000000de5000000000012c6525c41465540005f6059e16d054d56f00001f4986f23344422124e7632d40004498000079cf1158587eb0000d1635c41d940651c900000271d10d6150503eb2e5461d4ea44400ff0443287d58f64c8b4b35b858c56b036667e0bf32f280000000ff336b52342fd018a01a96cf4b580e96624ff40000e010001a6525c4c3019c44410b7cc421b058091a2c355091000000000000000a2b1a00000000156b0000000063c00000000004b943965bccc334fd000034a03f34c9c748218493563080003acc4b300000000001637000028c000010f0000d1f00000001a58000411468700003c70000000000048c3fad6690001a272ad400000000001d1962c00000001a9074c458c3b2000000004f0a610000343439469748440e0281cd8c00000422cc94494164000093c000139c0000000ced0001779000050c141c4c30000000000000000000001fd960e62d40000000e65000063a0000000000164500009c7000076a1bf80000000e1730000000000000000072e2a1c00000001eb369ce9d000000000000004b651f41d6000000000006404f9100000000000da80001a7300003a91b98ef20001672000000026113a312880001d8000000015090000e6965497e51fd197860342f715944cf2f79087000075741b03c360ec0005d88d224328000000164600000005a9834868a816605ad41c5340000000000000002af00000004e8430600000005180d845ff80000000e460aed8ba1db4000406c0c7000101c14e548d00017490000000202c9c01dbd6b70000584008cfdf1de800022a00005bac000000131c00000000611a20081c00000005de000197d00013885d780000000e7a0000ee000013ca2628000000000031f40000bb83d40000000000000030104d7037400000006b61221a4e05c8df765c410e00016640b2d0ff00014c74458000000062300000000294000272112c00000524a5800060ac9bb000000052f4ddb00003dc44bc4d43c1c000000000000000000000000000026912101ce1c383cc578010d0000000279c9f10000b220000000000022a1a680000000000000107a3d2045a00000000000000000184816b800009500ef0000b1a23880001f7445b000000000000000000000219587b61c0ae304e800000003270270bd40e004814a9c000000095000000ed47653ab
  | 54 => 0xa31eceed18e0000012c00056305750e8967f65a4e8b38d15a6013896a000197754f0ec800000001924af859d000000000000000000000066a0000000000047d0000fee00000005994000000000000015400000000000000000016383f5000000000002fc000000010360000000000000000008f4000000000018550000000000000000010e9000000000000001f08000000174f4e895ba00012a600012512a711f1319c00000007ae00000003a4135d0cbc86e1c2d61342a0a7a0a002ae14519f625340001fb800000003523ea882f000000000005d6000000000000003b24000000000000008e421640000001533056c00000009c16524000053c0001b5c91267199a050757682468f0d1a28000000000000000004abcc7f442c0001a94000131d43c0000928000020600002d9451037902806dc00011d66398000000000030640000ac99511b60a1011a0e6e607900f276d34d00002bd5d08c57645800012f40004c0c8474a6800000002f0000000061812d851cd776095d47e582400000000005bc4e3900002aa000183c0000000331000049cda313f95052000005800000000000000167400000018fd469c00066948195c7586200000002ca0000435c3c1116065a00014b85ed00000000aaa41280003c64072000000025cc0000000459000000063d5317361837e04e40004830000097c1585a9d9c1695800025f0000000137700016ef1ca4cc5594c32500006484c7c6110000000416800011cc92000007550001a7d18fc00000000000ae000069002860000000000191f629c00000000000000000000000000000005b90ac921140162becd055e94c8a17bc7931bbd91b16b061941fd2002f0022e5be4c503eb09d123551ec45c8000000000000000002ddc00000001f500019d6000000000a8986672c000000000000000003d8169d33404ff2df53d700005f00000e351ec40000001283000160226cc00022e86555bb44e62525543000000000012f61cac000142c0000000cd700000ad0000000000000000016124c8492c000000000000003dd8000000068f28d8d7a3d28bae2e418882e480ce00000000000c0600008a6000000000005d0000000000000000000000000000000018e350280002b780005f640000000e9121e17101b393391f0c0002215846000054c4f310eb0000f1c45a80000d19a35624000000000000000000000000000340001e140002b5800000010a0000000000010af679c16a61b000011fc000123caa208012e3000000008f400000000001b90d20496d39f305000000008414b6da4250c47610000d8357888370000dbe088800000000000000000148844a4c2980e42a46883cfc000000000000000003d99378038d34f55245d8383d5c9438066e4f8d3f6000107700000002800833000097d00000003c54000668
  | 55 => 0xe000000011544b10000000095766d0dd200000050a387a9095893c6504000000000000000001cbc0001ed40003bd4000000064e29a80000000000000172903309f93510000422000050c0000000000016ece4e0ca0961025975755804043de171e56792160b28ff0000127002bc0362be800017e177f576016f4eb199d303d4612e117f84dd4000000176534a8aad0b40047223825d2b5c5a12a01807000011b55a855a47358866438000000000060f87030000b96125d97200000003ee89c957506fc69404b51694146000000035556c548e88693d1d2dc000000052d00b050e00661e34731207857c231039c0000000248978b1dcc3d700000005b648a126a10f7000000000010b4346400017ececf0001a822514cf054894c851d96cc4ed8c28491d4be45b10231d740001518491549000000001d84d60a6825fce6f68c159f1fb401b5b0800008fc0301ec04e02efcb5600011060000094000151b00005e52374000000133d00013a00000000338800031cc000465c00000000000000acc0000b4500001b500000001075617000000000010200000000386538a0000a40000181a5b85976341159100014e0000089a3d64000000000000000000000000000000000000002f24000000000000002413b280000000000558c1af5d39053000000002294a55fa91c61498a722b094fe0000000627400000002121e207b9000000000000001334e6b59580004ced939268400048880003d550f000e50221870000000172700000004d992d2670d0e33e140000000000290400000006ec4c499c72ff9a8b5e9c451658ce08353c68c2604137159850455f40003eacbf764dd73b33a98c828c00002e4d13d00005ed0000ab300019fd33ec21602186db3ce8ebe4b4c2385dc0fa2159051f00011775044707000083254540003a9cb053fa94f7469800052d8000000035c59983035e59a2f32810dc02e997333955af27c916b61a5986042c6f73c294a466145b71c6c00000012b610f0000294000032ec6e7490400000000000001744000083a2b4800011901303b7d05e10294a912b971715446b400000825e44d2413a0b1545f443d000049a3c5c9920000ed5442150f49b1a3808916c74f6005300006dd266c00020185a6372092d4004a903b593195eb575d38880002d247790d4c0004258dc900001350000000000000007740000000f2f37654d400008bb0000000202400000002280001147320800000009f859cc00009180000000000000000051796a042dc0000e94f24570d0920f687bd3bc032a4b1465f05c00006510efc28f01514138aac000000000000003e71912168d2385055a022a05a220001a415e75899000041b5414d6624157c465793421bed1f30e2cb5203c134312e4d5b47310be2dc86ab2f1426b1e8cdde60054cd0224b203428e8
  | 56 => 0xd62f1c0002b15a12000071c3b8c95c41c400064e00000a4d87840b00920001049551059a0000f2850d96244a788245f04b7b00000000000540000059806440003ad800000017b8000000025900000000f7a3359081244c0001ea8de3229cdc2288c00000018df0000000000112b00b80004d8085441f400069bd61f00000000000f4e30f000000007ca5984000000093148f40005b1800004c93760000000542d9310000c474e1400058002780000127000119b2dd036047b56782a645d7000000011a57f333980001e1926842d8f5f00000000000000000000000000005e990dd07a800000001e3000000017d40001e589d83a500004b2c00016c4f8a11b40ee0000d3f16042892a78adc37280005b2c00009b4c4359400000458000000000053e81b469dc20d183120b0664000477000000000000000000000000064b114e5d4c00026f828a5fe530e0000872000000000010d459306b1000036846dcd870000000000000027cc000000000054480005d440004f6547d00000004d900001b0c000109c000000000009157bd000000000000e200005a4000000000000000530e63000000000011f758687f800017cf10040005cac09000019330474000000140e00018cc00000000000000000000011880004c697cd4efce3d2adc000222837100000d96388d100000f3c00002fa00003b619ecb78256800017a80004479726378500622c40000000d1d00006470c6d06300012660000a02591136e000012a24f400000000000000000000048b588d7b6554cad529348f03f404663decbd1000088f47613081215182631c0000001958076c63b00004fa3179a7b54386c749d80005b94769148d6f73f6568e045438e1828000000000021d586500008be2d8c000345c5be000000043100005e340000000000484c00000008771f700001238000000000000011310000000450d44c0000000000000000000000eac12346158a647d4000171800000013d50000000556ca8e4ebc00061600002f35504000000062c0000000000039d40000c1580000000004030048000124d000000006e4d98000000038e81ca59f000047d835663a40002ed800019c801e4241a030e8c7ec04950c6500400059241bc61e80000000000000105f4e5c000434537f1edcd6a00000001acd189502d36300000004a35441000178a1c28868367034e46bc8944038df2158400025580005534000000082e000000000002ef09f48bc0000b3300018b90da8000487c0002d20040087805d2be4968173078300005740000ad03f3467900014ec5be8fc8000000036344c6109800000012b10000000675000046340000000000000073600000000000000000000058100005b34d945889a7500006ad000000000018f30000d6d3b1c0000a340006791267464415754305ee183c0002f
  | 57 => 0x1d906e5cf80000a709853c58ede0e1cfbb2ef854a40bd49f1c8da535f6d26b1f114b03e580ec088445434e896e3b411e20dfc36f6114e0309bc43535650480948472077117b00016871154000000000024d05900fbc626529981c63380e559540001cfcec4000165230dd4b75ea4113000064a000019b0001a623bbc00000005340000000000000000016b20000f5130810333494ac00860f330d7c812455d0795ba07422fc567700019bf2c980000001a2e24280000000a8900004b809f15d33fbc000000135b063800000017b90000000216c00060f5824000133834346a035c901600000b24360d3900000004ab400037b43392b19a945f88000574000000000005b4c7680eed2ec01c03542dcd4c10000dd80b096ee290809d0c200105528000000000032cc75300001be000000000009ad1ff40000000c65604ceeb0000d5d34207d426614f400000005aac5c100003ae069000000000000001559318da9721555f80278a9313dd3f200000000f9093800000001b6887a429090027780000df09fb55919d700000000000000000000000000000d3c00017fc00067bd0e600015ee2d7d9a80104314000067603d15dc1c1140332057012854b8d2e08fa116ad81732c50ad615ce8f46f98ac613108059692420450f4400014f200000005554000436d1ff5f147764e5856c6420805456c0005690087103000000000000001261000181600000000418ffc00003b120b1209000000000012bf00007af4ed00002e3000025b5003000000062acefb48084b03688781000000049b80001f4d3e6184979e3e7caa6693d1190000425000000012f000000000000000db363789ba1aa491500001c3234000032d8f77636066d291098b0af05a2366400036498d43d242b309904ed3a600004a1d6e6000000022240000ea88c90000ff80124363000189f6818b503c958a8000085000007a7000041f23649eb0000bb7000000000011de0000e491c7800045b4f3414b80d8000000034380003e11a5b13f0161000124a2d9d4dc18d940600000000000f1800008515a4d1c70000000000000000002811b182eb4a6c3d3000000063bd214000135500015950000d3d5eb8000000000056f4ead557497400000004c580000000e2d00000000000ab90000000238545b0750000552d8330000f2a67c0576196422556a95922e052214d245b26794a4c46544f2645d3900000a8a000000000000005ea00000000d4100019b20000000000001c2c340004aec03252154b963dc0000000000000000000000000000e36665800037cc00000000000000000000000014f40000000d7f296177301f8f1b41b417c4358ccf2f658590000d9a108d0ce2b3800046b882200000000000000000078913006b80000000000086618a000018945373110d1b09a1987296400007a07
  | 58 => 0x92100017523ffc0000000000000151d62d16d80e501e158f8d8243b87b42a7c00032a4f57000000014c000023e4dd164c00004a48afd366c00011dd9f1000171140a077700000005d1c00037745e607040000001530000135154fc2bf00000000f593e000000000e840d55f1c04c0001a0e4408000000173532f000000000003efcff714140003d91a213c0800048797d50000000566985d15e9772286c0005285263000021d2204000623c00066a4000000000040d000023b155049e800066342b5000080008a54435d0090e4e998f829744e525c0436398800007c43fe00014590000000000000020840004880ea201d400061718dd12c40004578dcf62a885a0000d90000132b000174d0000ab85cd80000000000178024b67cc000000000000018bd00000000000000000062d3ca495200015a10000000497521015dca754540000000084d1d1400049200001bad5f417a0e7d20280005c3400000000000000d6000000002128000000000000014ee05b800000002ba00014085fb400003dce5100017694d7d0ec29880315ead6f64fbd18350400000000000514d41753840b100000006250f4335181a9258c49b0000000606000056cc000000000000000000000fe433c40000c8c4d66a21193000000047f80000001330000129161240003eb4f9700003f400005bc23c551100000000c28e834c8c386000033018cca221d656fd00018c60000064407cfd3000098700007f000000001eec00000000000a0800040843f0119c0b32c04fcb58053fa00000001fcd02d0c64d060000000268c00000000000000e37000000000000000000000000081b15710b51ec86f40a5c00000004ef00006f8459c00000000000000000000000048f9437000000055780000001235562462a000000010b4c0e00007df0001162000194e36540004cb0000181d5560a948801f245410f299cd00013690000e485a8c7cc0000000427134054993bb18c938932e05964eb4f2043c529d0679a3d624c5883a689d02b297054bcc0004cdcd123530000000118e37f0aa1000088810a47a80db0a9506a879e226c5d211353c41950bba12081bb0000000519400000000003f5c36b257cbdb0000000619c7431ae84b603c45eb0000000000130f218c0000000465000000000002d6419000009cc000000080d0000000000000032992370ef0000469448600001215f40bfb00019eb000038a3c8d64859bd23964a00001c340000000000000000000000001e90000612910d0000d7e07eca6327981410cfd4510444795230046a4a394f13df0ec2632c0a20000ed8059d9e600019a10000000224982100000010000c26000018100009750000fa300019d934d8000377000032dc00000009531cf4b60251cc02069844e000085223ccfc13c196b1409d55c304800000000004
  | 59 => 0x1970324548c8da0cf18ca246cef9077cd6f42790aa3950ccc67e8fd8000000000009b80000000000000035206b9397093200001c800012eb000033b0000c833ab03470000183000000066d4d1a000019c000074d48cd05b2fd864432300002d6c0003364a33372c0000a5422b1404a8b136c000457c00000000002fad9193a4c00008500000000e4a178c00063a8b18519800031f81335c9000057311a11c3d224344d1ef073c0000000000000015200009e80000ae520a800053fd9f42394b2b1f7886c36a8aa45e7ccbf000178c48496412d5d15d5b74a08687598b55380002a0c0000000000000000005fc87c657c4a834980000000000000000000000003c8827e44443f120602f61c04a881768b9b000160c47556c4283c0002710d8a0000ee22c8511a4c94842262400064f030d69e91e00000db20aa152107b00003171082000049600000000000eda46cc0005cbc39b160ce5635600004e1904f09c4000066818000000000dcc0002bad05d0000000164c00000018b300000004d1005a1b3c4f61ced828000000000006302aac87e542000000000004fcc88227b80000000ffe028d448406127b265cb4029513c52c785df0570c770fb457d0e3d90a3d683370000c8f56a0000281869b21cc0004e356b00b3c00018f40002bb57ff00003e51adc0000000bab302c0ea41f89761d2cf5e00e041c35f5a4d1c5914268b42fc00006a2000000006493040000000529c000000000000000000000f8900000000c3c0003a78000294400000000000e492be146c00000000000001a51663800000000000000bb921714dd0f84a5e000112d4a092fe234c301608800030fd1d41af8000000150a698c00000001f416bc4da3f300000000000297cecd128c72a000000000018344a2400065a00000000000000000059aca2c000000c00000002d2800000010000000000062da904da119842c90a768e800005f86825f74f1f2654000000000024a8000000000054680005e5c0fd499400041a120d1884a35000000000015df307d41b03cd14100015c462818203f74ddf4cd00000ba0d8f000000008c0000000141e4474d424f40c990000ba861ccf564a8c7ef1a385201db85c20000000585000034b418803e90b10bd4dc36140d7332e5746000000000010f538158e510a19602b114a06450d85347000000005590000c7c0e9d03e00006ae23bcec5000047a0000000485c96b636d77d0429826000000000000001d88000000000000000000000595228c5fd000000000017090000000001c00065750ae4cf8c2901b0000000000034dd4d200005cb3abd8320d89a6c5d6800036e88ca2f74000000000040acedb4a1469e000000056d40005ba800017345c300009ed01c56bf40c94ad4cd5481196cd4020f03ba00000000000000213c2c51181384362d
  | 60 => 0x482628dd0a10000d6365e80000cc8000000029a58e454b000176f0000000000193560a87394ca1542000000059b906a404c17b000034001b800000000004c7597f66c11402734c3a33d13b1068c0000000d6817500004e78c9727c13eb48b400023a40004e754f6000158b0440b9f1f64fda4bdcf0e00003355c495ce3c500f20e240000001527000000000012a11cc0aa3512909a30a862200000000b980ab000000000000002c8c0000000e0e00001cb3b2ccc300000005a3c0002f9941300009a9000000065d460b00009ce1b516b800016a10001302000002d00000000000000334c00000000004f7000000010040000c8e526c00061d19fc283808500006e2000000000013620000fbc00010293c10fa616b57f400000795d900003c300000000f5230e453355b053257aceb969a00001efd6894348e5700000003e00c2d000198f3e30f101ffc000545c78f3bdd32e3894000531400000012e13a3818d3da09d46030d78000092e000173264719290000000000000054d95cf33cc0000000000308c00066b94da000168a000000000000005170a13192c000000000040742321bc589700015e4000000029b40004b294e80000f325a900000000d2158a00001c0036500000000f3d482000061a5b208f6293969a21c13ee2f9000b0000d184a4c0001e700003f38fc30000dd51e800005fa482344000005c64f31486400000001ac0000000009000041084e4252963113a800000000000000000220c0001648e8c0000000000000000000003fecebd143c0000000000591da3260b59c900000001de000057dc0000000cd800005ec12ecc9f37818fc3ecc0000618b75155989b303164300018610000000000075b000164b000005c63b40004a80ba62d880000b20000160172a36b14db1284bcb63a00000001994447c84c08693ed641400000019db00000000000def0001723000000000015160000000000165c0ad0000000179b31452f2000168c3da8382000147a09d4e150df4f3e053493343ec00000014c20000000000000024dc4cc00000005a0c5212bbd37048291130f107e70000000000047464f868366e867a2c3875e00d1811000096900000001aec3d124ada9b46100005ba4d0b5ae96193e094a85a8957451b40000000000228897e267400000000003c3c0000000000156000000002b7000163430f40000000000000000038e19ab00008eb00000000fc8000000000016719456430000000192600000000ed00004528a984e0cbc154e40b9440450046007d00320b59306cffd6204b060000c5500004d3000006f136559926d17e340fd4c94fc000024119d54b31962685523c6924691612c00035e40374f3800054f46c20c7414300000005ab40004edd6db034c0002e2cbbc520cc1a41f00006a70c8032b400033e96dc3ee015f
  | 61 => 0x3ba52464a2c27a1eb4afe00000b8681d5b925e4b1610546e851a4bd5513c41a2c4421c50342660001696000000055c0000000110a61ac00000009f63550da600000001d49a9200014f315496b500018f6000000018c5993000179267855981975178000099e3a1ca3a1454011000000000000000000000000114c3e54b7a000099635d0abc444879a000000033c80d160d8ff90001715579c000037032000000005af0df80000ba40001a8700013dd000000000000004948c17000184200011480000fb11a109d745b94290f491df035c0002ef426e0b9d0ab00017a421d9a042418bcf2fa570a05a0e504bc14220c589172f20000000000000009432fd4000151000001ec00060183db280d4502cfcb971354b85626038800d41953c9d9aa5f6873234789bc17398f93bd800053d45080fe4f4200003c50000000000000043a00000ca400026dc692000000056e00002e640000a158e0233800033d80000000000000000000000001e842b137d05710000000000069f0b04fd1000000033180000a6c0003bb00003e380004dd0000469000058280000000000000157258b800052b89e300008d70001998603d128289000029f40005a64000085c0001f3c0000000000468000000019e8000035a5bf06b563b80cf0001657201c0000000349057919d2191798243483d000047800000000000000059400016280a7000042166300de2c0964a00012b5145cc7a6a0c6864b54000336d3c751186b00978000000000012480003f3c000079991548100000000f3547e8d620ce809a58203091b800000000834410c0000000000284498d1980f3d29197d60001a8d0000000000000012b00000000b5300005491ef8000104811a2b4d53b60e0ee749c4bbb0204000000000000000006a5965f079040500000000000000000121a55d800060b01f84f3cb34658440855e0000349d3ae01b52da23a8abb096000000000002f100a4098d0c910e8cdc4a290bd13c18841801583332ce9c46893200000b64000066b19fd5be438553747f40001290a0c00012d4000000000000aa00000000000000000000000000000001a2c0000e82120c00010d199a15a8b650390f613130cbd390832e61f05ba6a305c44250000666d2ae00000000000000000000061044560000000000000045840005cf10d53594000166c000260c0001124cfc1bc811f5df913e1744fc2000170f39c80000000967000000000004d160e4e2431513c000016ec3ef45db0000000314c00054a97bb0000000000000007d830b1644000246000000000000ddc000000000000000002b6d38e3b754860001139000023c00000000000000117c000000000068ec63700000000000000000000053956a94f0480300010a65221a4a00013b30000000000000042b06d90000fc01fc58e40aa
  | 62 => 0x1b411ba3c4d5c544d4000000008c4e3173a17214e600008b300008fc2cbd0de27184004f081fc461cd47000000065c19e01b106bc0000000000169e69f13b251154ab56a473e4f196f413cc10060c12cd3e058f046a800042fc00000000001a4c42e68018c165019110000a7917d18d504f824c020cece6a4cca42cb8ca126310da1c945aa075800000006ac2ba022f2eb5603000000040e03ec000000040558bf37901ab000000000019f200000004e509ca59a915a3b846fd0000f8f12f984d5d840000000000000025c0000d9e0000853000000000010fa000000000000000000eff37e40001ce8000224c00021784c200000000000000000000002b9597000000048a405f5a5058900000000a1d45d4554a2538ec00004097ac4960000393ca9400000002d18000000088d6964e5f51dc5bf0b605f765b8deb3b940004aa4e555e0c000000000030d14fc27f036930c4a826770e5b35c030015acc560c117e6000163d68f13616a3d333000000006b87e42c401310a2c31e000000000000000bf80000074000327875c000000000012e90fa4e13229168500010500000a6e0cf51322fbcf88535400000003750000000000000037d4000682000035a400019cccac39f000000016f23558e685db00005ec40000000f7100012c10e107ba521c01a37f80002c9434c3c782e93fd4c6101542402a9d6331a652ed4c046ed433c000000168600000000d650fd338400000000000000000000169100000002b200001d3c815383417700007380000c2403014cc030571b57c80000000c4e2c9c000378800066f00000000fb500000003ba12f10490cf557ccb9139ec4c80000e81000000000011d20000000000000067693546741a7835dd5285c6142c20a480146c42ac2db11bd22e17af697935200007750000c080000c9b4ff0000127d71442380004388000000000004a00006a793c327f80000000d2b62dc1b3000001300003f6523c4e1124c000113088650f80001b491e951ed6810000000411cac34a000000001a7900012b0000000022759dd00008ee30ac47e4ca4e095d1400000014c4000000063b02a42a68f6f0000ba101351bb00000000000000000000000000000000a5300000000000a04390400000000001decf65299800041e17711f6c0002834d891f680a937e97751cdd3326384000000191e020160f000000036e4db468dd1d100018a44b080000311a5252780006244e470000000000186d00000006814c980b1000027740005b4591a5c187243638a730000000000000002f0cfd000000000000003d313da291400055a00005de800018345a84e083e6127400000000000000da3000176d000000000000005b88ed900015690000bec6435a18628400959440000000bd2000078e0001a0f051023e0000000636800031a400
  | 63 => 0xb7656c3443ea10ed1e6c000000000000000000674eba09d00004a88caf00000004c1800000000000b440000000e890000000338c0004ef400000002910000000000160700010c300000001be400000002364b749290000a6456815252f680000000c924ed48c1152000000000000000000000000060140004f7c00000000000000000000159000000000000ae21e7c55b00000002db400028782fb090800000000000f356a84be400000019d807f8000289800000014980000000409008d57a400053445e23a84a5663d1946000125966b192e6898000000012e13f465657f924032746582478000033558649d175c44f185400000003844e7700
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xf6148020a468654c6148020a448654c6148020e076454c6148020e046454c6148020a488654f4048020e41531874048020a0c8654e4048020c0e7654e4048020e05531864048020a0c8654c4048020c0e7654c4048020e05531844048020a488654c4048020e41531844048020a8a8398c4048020aa28198c4048020e098518c4048020e0863d4c4048020a888694c4048020b098594c4048020a288654c4048020a888654c4048020e0b8654c4048020b0a8654c4048020b088654c4048020e088654c4048020a088654c4048020d0a7654c4048020e0a7654c4048020e8063d844048020f0153d844048020e09531844048020e23651844048020e83631844048020e80631844048020f01531844048020e23531844048020e82531844048020e21531844048020e81531844048020e01531844048020d0a7454e524802084e87995320cb10d0a541c1320cb10b0a82d4e5310310d0b535ca5310310b0a83d4a5210310d0973d4a5210310b0b854c83210310d0a754c83210310c91735846110310ca1725846110310a458294c614c310b098294c404c310e0a53188404c310e1253184404c310b0a82d4c400c310e0b53588400c31084d8718e5248310a45839486148310b09839484048310e08639484048310e2252184404831084f8758f5208310b0a83d484008310e0963d484008310cc1321c5600ca10ac18018d3208610c49625c06214d10c49635c06314910a48854c9600c910c48754c9600c910e08544c9600c910c31651c1640c410c31651c16408410a458518d3208410cc0631c13208410a15831956110010a258219561100109a0825c74310010c31651c54310010990835c74210010c31651c54210010a3281dd965100109a0825c76310010c31651c56310010c197654c5310010d09535c85310010990835c76210010c31651c56210010c29765485210010d09735485210010839861d53210010d09754c832100109a2829ce6110010992839ca6110010d8073dc96110010d83731c96110010d80731c96110010c19655cc6110010c29655c861100109a282ddb3110010c91769cc3110010b81829cc311001099187d8c31100109918718c3110010c917618c3110010b118518c3110010b818218c311001099283ddb21100108b1861cc2110010931851cc2110010992839c82110010ca1769c82110010b81839c821100109a187d8821100109a1871882110010ca1761882110010b21851882110010b818318821100109a1878c82110010d80734c82110010aa082584408c010c4575588310c010e0953588400c010991870c4400c010b11850c4400c010e81620c4400c010a90835844088010c457558c2108010e096354840080109a1870844008010b21850844008010e81630844008010aa28298c40c4010a928398840c4010
  | 1 => 0xc88631c13208440c0d655cf2108440c29659c32108440c29651c12108440c31651c12108440c89635c86394040c89735886294040c89764c83294040c25725846195330e0a544c9600cb30a30815506050730c1b731c16494630a3281d506050630c19651c1640c6308ca878c96008630990815c03210230b41801893214530a2880590520c530b20815c05210130b10804c85110130928805d06154830a24845846154830a60805846154830e0a64549600c430a28805915208430c0d765483190030990815c03210030c0d765483110030988825c03110030d09525c03110030d097354a6010030e2152184404c030c0c76d91524c030c0c76191524c030a448654b614c030a4686548614c030a4486548614c030e0764548614c030e0464548614c030e4152187404c030c0e7654a404c030e0552186404c030c0e76548404c030e0552184404c030e4152184404c030e0985188404c030a8886948404c030a8886548404c030b0a86548404c030b0886548404c030e0886548404c030d0a76548404c030e0a76548404c030e8062d84404c030f0152d84404c030e0952184404c030e1365184404c030e8362184404c030e8062184404c030f0152184404c030e8252184404c030e1152184404c030e8152184404c030e0152184404c030b0a8494d524c030c15735846195320d0a745c0534cb20e0a544c9600cb20a30815506050720a0d8614d3290320a0d8614d3210320d08531c13210320a4681d4d620c320b1281d4c400c320e0b53588400c320a89868c8400c320c47531c5600ca20c2b721c16494620a3281d5060506208ca87cc9600c620c29651c16408620a498018f5308620d0b535c032102209a0815c03210220e0853188404c220a8a86cc8404c220e1053184404c220e8332184404c220c49625c06114d20c45621c56014d20b418018d3214520a18805905308520d09725c05310120b10815c05310120d08531c13210120b20804c85110120b0a858c8408c120e0a658c8408c120f0232144408c120e0853188404c120b08854c8404c120e08654c8404c120e1053184404c120e8132184404c120e2062144404c120f0132144404c120a45868c8510c120918805d06154c20a14845846154c20a50805846154c20c45531c5600c820a1880591530c420a49801d9530842084c8754d6008420e0a6454d6008420c0d7654c2190020d08721c15310020d09535c032100209a0815c03210020c0d7654c2110020988835c02110020d09535c02110020d09535ca6010020b0985cc840cc020e0965cc840cc02084f87d97324c020a4585cc8614c020e0953588400c020b09850c8400c020e09650c8400c020a188654c4048020e11531844048020a4681dd9534802084e869d95348020c0c76d915348020c0c761915348020a448654
  | 2 => 0xc54314141d10531c54314141b208150f5214141b208150c5214141d13531c54214141d10531c54214141d23521c54214141d20521c54214141932819db4314141930815cb4314141932819db4214141930815cf4214141930815d13214141930815d03214141948805d5320c841d22521c14110731a298215060506318d0805c4644c831d0a545c0524c831d09545c0524c831c91631c14110431c84641c9414c431c90641c1414c431a28805506254031d12531c14110721a19831506050621c30741c56014c218e0805c4644c821d0a545c0534c821d09545c0534c821d0a745c0534c821d09745c0534c821c48865c0534c821d0b845c0534c821d08845c0534c821d40815c0534c821ca1621c14110421c84641cd4148421ca0641c14148421a848458c3148421ac08058c3148421a18805506354021a4b854c9600cb40cc1321c5600cb40e046318a5150640e13639446050640e10639446050640e23629446050640e20629446050640a88804c9600ca40c85321c5600ca40d06739cb5194640d12739c35194640d11739c35194640d22729c35194640d21729c35194640a1a80995530c640a2a809955208640a0d8518d3208640a898018d3208640c49651c1320c840cc1321c5600c840d04731c95110440d10731c15110440d20721c15110440a2582191518c440c15655c4430c440a15831915188440c25655c44208440a1581195534c840a2581195524c840a888254c604c840a8883548604c840c89861c1320c840c8b651c1320c840c89651c1320c840a88804ca610c840988874ca600c840c85321c5600c840988874c9600c840d81321c5600c840c8b874c9600c840a88874c9600c840c88874c9600c840c8b754c9600c840e0b754c9600c840e8132dc5600c840c89321c5600c840e81321c5600c840c93321c5600c840ca2321c5600c840c91321c5600c840ca1321c5600c840c81321c5600c840a90805c46354440aa0805c46254440a168758d5114440a148758d5114440e0563dc95114440d04731c95114440e05631c95114440e05639895114440e06635895114440e05635895114440a26875895114440a24875895114440e07735895114440e04735895114440c33761c15114440d10731c15114440e11631c15114440d20721c15114440e21621c15114440a8980989328c440c8a621c1328c440a2582195518c440a2582195514c440e1153544604c440c0d655c8530c440c15655c4530c440c15655c7320c440990805c7320c440c0d655cb310c440c19659c3310c440c19651c1310c440c31651c1310c440a898098d3288440c8a631c13288440a15831955188440a15831955148440e21525446048440c0d655cc5208440c25655c45208440c25655c632084409a0805c63208440a0d8518d3208440a898018d320844
  | 3 => 0x8d1780ca000721c708cc00000b4000002562311e7725a100baba8b0251523d8001a0de0024e1f000ac27858244002125f23e79a100aa1ea40ee7f820000000033275a6c0018a3f0001529eb0800c1986d8000000006511c1428e8b000000004012c0006e0027600220000aa608002d000222e2002c000000088fe00000d1ac46f04e0000a00252000002085aaf0008618036b0e003287b0e28135cce88e30286571588aa0eb31ce15964599b09e9760030c5b0ecc9b168216e64b20452d6da988002840020a4f2600018c04000d51a8249f85a9fc7a9b4931ccc2800b51044610e14adec6870b913ac7aee67308b2a3844b50030a84d13e52060aa0808e9b89cb3026280c62da74af217aa66f92889b48c08360480039b14000f40023606048c12469a9200000077800cb8c85533432a42990d800000afb22001a4ac800000002e1c86bb688a000280006d8f8000843a95ad49f60033ebf8fa469ca8f22255962118003a1403807a1d002348c68900097aa0b18f2358a2ad00086800d7aba0e12abe1d8000966992400000951c0350006eb3666946b38008c8002f8000c0009f9e0a62ae243380018ecf1224d844a48042f14e00266d094a000ae17300d9b4a4c808b80000d10a97024960c41c9a2aaa48002e82729cc92142903ea3190000769c000000008300000206219c67c0665cadc13150768169a108b4a307a02cd109aab1d02ca1640a743381ed60789b82e1f9f23c000bc09ebdaa4018e453196cb126902943092eae00006af409aec0004a0e942510003710c6a800d899e5c2621601457ac8808d06100e9296829ad8a0b566c998a586c75062788ac71106beafc5ea50ca8282db405fb4c7922ec703cc4930a21ac020230541904c050080c008000000304c010300b008050040b0140002808000130100003c050280001c19024090000f014000c0040000f01800010000b4000040203c0100801114010400000001008010340100c1d02c030042400c02068050081f0d0120000d0300202c0001805000000440b0000a0000100c000100e028000001b01c05010390f800000110041c004000000601400008050080b0181800806090050502001802018210080a04c1d000080040d01401c1b731c16414532c18731c16414532c2b721c16414532c28721c16414532c30711c16414532a8481590644c832a8880590644c832988805d0614c832a8484584614c832ac080584614c832c88641c13254032ac0804c86154032a4681dd93254032c0c76d913254032c0c761913254032b0a84dc13254032a44864cb6154032a44864c86154032e07644c86154032e04644c86154032a50804c86154032a60804c86154032e43804c86154032a44804c86154032e40804c86154032a4980d95320cb41d04531c54314941e04531486150941d13531
  | 4 => 0x192a2a2a7c4e1fa10ae6d908ac429a5d116d6b4e44000ad86a681f47b8
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x180ac52000080a086044c75693502c39006a8d1f4a84e17408802b305470d2400a192cb801b4e78509463d22f00c0011082000224804a270048288ac580a53804c86154032c0443108b80a699043840862057014d320872010840ae029a6410d10e55321c5600cb40a404826438ac01948148291e1d32580321029012e996e2b00642052025d321c5600c840a024bac6392a228881804871cd62544511028212eb18e0a88a22070058c721c15114440a104bac4382a228881c00735887054451103022ca402e39906220608594805c63208440a04ca8c638264108816009654b61101300c2c052ca90c2202601858025952184404c030a04cb0a6382642064160291d4d6210030c83206a640ae019081106405c8815c05310120c80a9902b8064200411089854d7008440082c0523c32a62024010482a5a8654c4048020b004b2a7b0880900416029654c6110120082c012ca98c22024010442a62754c83210310b00c94a630880986212099818e5210120c42c0327290c22024188482e6163d484008310c40bb305398622002181176614630c440043102ecc10c618880086205d9839c82110010c10bb30a31042200218817660c62084400429032c39a641088008540654734c82110010c40c3ac41888018021a018558831100300431030eb18422004008680615630844008010
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 42
  | 6 => 1947
  | 5 => 11355
  | 4 => 6815
  | 3 => 438
  | 2 => 49
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
  | 5 => packedAt gbK5 (488265+((h/3785+packedAt gbK5 (431490+(h % 3785)*15) 15) % 16487)*15) 15
  | 4 => packedAt gbK4 (365729+((h/2271+packedAt gbK4 (333935+(h % 2271)*14) 14) % 10884)*14) 14
  | 3 => packedAt gbK3 (27740+((h/146+packedAt gbK3 (26280+(h % 146)*10) 10) % 526)*10) 10
  | 2 => packedAt gbK2 (3575+((h/16+packedAt gbK2 (3479+(h % 16)*6) 6) % 59)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffffffff80ffffc0ffffffffff80ffc7ffe3f
  | 1 => 0xc07f01fffffffffff03f03f03fffffff911fff
  | 2 => 0x7ffe03fff01fffffc003ffc1fff07fe1e3c7
  | 3 => 0xff800003ffffe03ffffffc0001ffff83fe03f8
  | 4 => 0xfffffffc0000003ffffffffffe000003fffc00
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x4309142808e2448402cb14b1425884a4266e1b
  | 1 => 0x95224c5191248918b015415434ab19499114ed
  | 2 => 0x2a4c289aa241d22d5540926d9135a472e1a346
  | 3 => 0xc68b163448903b669a6d80921c6ce237a03b0
  | 4 => 0x3070c183870e1c3b8e38e38e38070843ddd800
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xeaa8c880eaa8c880eaa8c880eaa8c880eaa8c880eaa8c880eaa8c880eaa8c880eaa8c880eaa8c880eaa8c880eaa8c880eaa8c880eaa8c880eaa8c880eaa8c880, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_12827
namespace PEqualNP.Outside.L_meta_12827
open PEqualNP.Outside.L_meta_12827.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 49 := block_range (n:=49) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 49 := bgb_2_0
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
theorem bgb_3_384 : Interval gbAtlas 3 384 54 := block_range (n:=54) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 438 := (concat (concat bgb_3_0 bgb_3_96) (concat bgb_3_192 (concat bgb_3_288 bgb_3_384)))
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
theorem bgb_4_6720 : Interval gbAtlas 4 6720 95 := block_range (n:=95) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 6815 := (concat (concat (concat (concat (concat (concat bgb_4_0 bgb_4_96) (concat bgb_4_192 bgb_4_288)) (concat (concat bgb_4_384 bgb_4_480) (concat bgb_4_576 bgb_4_672))) (concat (concat (concat bgb_4_768 bgb_4_864) (concat bgb_4_960 bgb_4_1056)) (concat (concat bgb_4_1152 bgb_4_1248) (concat bgb_4_1344 (concat bgb_4_1440 bgb_4_1536))))) (concat (concat (concat (concat bgb_4_1632 bgb_4_1728) (concat bgb_4_1824 bgb_4_1920)) (concat (concat bgb_4_2016 bgb_4_2112) (concat bgb_4_2208 (concat bgb_4_2304 bgb_4_2400)))) (concat (concat (concat bgb_4_2496 bgb_4_2592) (concat bgb_4_2688 bgb_4_2784)) (concat (concat bgb_4_2880 bgb_4_2976) (concat bgb_4_3072 (concat bgb_4_3168 bgb_4_3264)))))) (concat (concat (concat (concat (concat bgb_4_3360 bgb_4_3456) (concat bgb_4_3552 bgb_4_3648)) (concat (concat bgb_4_3744 bgb_4_3840) (concat bgb_4_3936 (concat bgb_4_4032 bgb_4_4128)))) (concat (concat (concat bgb_4_4224 bgb_4_4320) (concat bgb_4_4416 bgb_4_4512)) (concat (concat bgb_4_4608 bgb_4_4704) (concat bgb_4_4800 (concat bgb_4_4896 bgb_4_4992))))) (concat (concat (concat (concat bgb_4_5088 bgb_4_5184) (concat bgb_4_5280 bgb_4_5376)) (concat (concat bgb_4_5472 bgb_4_5568) (concat bgb_4_5664 (concat bgb_4_5760 bgb_4_5856)))) (concat (concat (concat bgb_4_5952 bgb_4_6048) (concat bgb_4_6144 bgb_4_6240)) (concat (concat bgb_4_6336 bgb_4_6432) (concat bgb_4_6528 (concat bgb_4_6624 bgb_4_6720)))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 5 zero,inputs.getD 3 zero,inputs.getD 4 zero]
def fullWord : Sig := 0xeaa8c880a8a88080eaa8c880a8a88080eaa8c880a8a88080eaa8c880a8a88080eaa8c880a8a88080eaa8c880a8a88080eaa8c880a8a88080eaa8c880a8a88080
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 0 32) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,11,43)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,11,43)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (3936921768 * 2 ^ 32 + 3363864704) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_12827.Model.Repr at out
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

def mono : List Gate := [⟨.and,[3,4]⟩,⟨.and,[1,5]⟩,⟨.or,[6,7]⟩,⟨.and,[1,2]⟩,⟨.or,[5,9]⟩,⟨.and,[6,9]⟩,⟨.or,[0,11]⟩,⟨.or,[1,10]⟩,⟨.or,[2,8]⟩,⟨.and,[12,14]⟩,⟨.and,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3936921768 * 2 ^ 32 + 3363864704) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3936921768 * 2 ^ 32 + 3363864704) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_12827

open PEqualNP.Outside.L_meta_12827 in
theorem PEqualNP.Outside.L_meta_12827 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3936921768 * 2 ^ 32 + 3363864704) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3936921768 * 2 ^ 32 + 3363864704) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
