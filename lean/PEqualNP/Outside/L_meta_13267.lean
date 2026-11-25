import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_13267.Model
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


end PEqualNP.Outside.L_meta_13267.Model

namespace PEqualNP.Outside.L_meta_13267
open PEqualNP.Outside.L_meta_13267.Model
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

def SBf (j : Nat) : Nat := [2, 2, 3, 5, 6, 7].getD j 0

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

end PEqualNP.Outside.L_meta_13267

namespace PEqualNP.Outside.L_meta_13267
open PEqualNP.Outside.L_meta_13267.Model
def s0K1 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 1 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 1 => packedAt s0K1 (i*3) 3
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 1 => packedAt s0K1 (4+((h/1+packedAt s0K1 (3+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffffffffffffff
  | 3 => 0xffffffffffffffffffffffffffffffffffffff
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffff8b
  | 2 => 0xffffffffffffffffffffffffffffffffffff95
  | 3 => 0x26
  | _ => 0
def s0Atlas : Atlas := ⟨1,rawDecor 14 s0Pos s0Neg, 0xc000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_13267
namespace PEqualNP.Outside.L_meta_13267
open PEqualNP.Outside.L_meta_13267.Model
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
  | 2 => 0xffffffffffffffffffffffffffffffffffffff
  | 4 => 0xffffffffffffffffffffffffffffffffffffff
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffff8b
  | 2 => 0xffffffffffffffffffffffffffffffffffff95
  | 4 => 0x26
  | _ => 0
def s1Atlas : Atlas := ⟨1,rawDecor 21 s1Pos s1Neg, 0xa0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_13267
namespace PEqualNP.Outside.L_meta_13267
open PEqualNP.Outside.L_meta_13267.Model
def s2K2 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s2K2 (i*4) 4
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s2K2 (5+((h/1+packedAt s2K2 (4+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 3 => 0xffffffffffffffffffffffffffffdf0ffc1fc7
  | 5 => 0x6ff0ffe0f8
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffff81222d295b
  | 1 => 0xffffffffffffffffffffffffffff82445652ad
  | 3 => 0x24e89b1cc6
  | 5 => 0x188ee398f0
  | _ => 0
def s2Atlas : Atlas := ⟨2,rawDecor 43 s2Pos s2Neg, 0x88888888880088008888888888008800888888888800880088888888880088008888888888008800888888888800880088888888880088008888888888008800, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_13267
namespace PEqualNP.Outside.L_meta_13267
open PEqualNP.Outside.L_meta_13267.Model
def s3K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (i*5) 5
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (6+((h/1+packedAt s3K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0x7fff00ffffffffc03fff80fffffff807f8ffc7
  | 2 => 0xffffff00ff807fffffffff01fc03ffffff18ff
  | 4 => 0x83ffffff00007fffc03ffffe0003fff80fe0f8
  | 5 => 0x3ffffffffff8000003ffffffffc00000fff00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x104b092124851444848a8b162d545b4a936b5b
  | 1 => 0xa095d84a4d4a28a3a915c0ab569aa8c5a8b5c5
  | 2 => 0x412652e88a534d293227558198c335974d18ae
  | 4 => 0x76389c8cec6c723223b9e6cd0313c6e18ee0f0
  | 5 => 0x7bc0e0f0f0707c3c3c3e78f1e3e207060fde00
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xa8a88888a0a08080a8a88888a0a08080a8a88888a0a08080a8a88888a0a08080a8a88888a0a08080a8a88888a0a08080a8a88888a0a08080a8a88888a0a08080, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_13267
namespace PEqualNP.Outside.L_meta_13267
open PEqualNP.Outside.L_meta_13267.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xc0c30040001a7081402212502c008061bf43bd43bf42bd42be41bc41de31dc31ee21ec21be40bc40fb10f810
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x28000008219000025aa5a1c754f428ea98812d52103a062087808410
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 6
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
  | 4 => packedAt s4K4 (244+((h/4+packedAt s4K4 (224+(h % 4)*5) 5) % 22)*5) 5
  | 3 => packedAt s4K3 (170+((h/2+packedAt s4K3 (162+(h % 2)*4) 4) % 13)*4) 4
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfe03fffffffe01fffff80fffffff01fff1fe3f
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xfffc03fc03fffe01fffff01fc07ffe07fe63c7
  | 3 => 0xfffffc0003fffffe01ffffe0007ffff81f83f8
  | 5 => 0xfffffffffc00000001ffffffff8000001ffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x97a0a4a628a31d25245c0972d4cb10cb30ae1b
  | 1 => 0x2a0509085144244848a0b2a5691563144754ed
  | 2 => 0x4caba2329a69491d913d58198c66b4479a6346
  | 3 => 0x713233a3639191911dce6cd03078d9e11d83b0
  | 5 => 0x81c3c3c383e1e1e1e1f78f1e3e40e1861ff800
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xc888c888c880c880c888c888c880c880c888c888c880c880c888c888c880c880c888c888c880c880c888c888c880c880c888c888c880c880c888c888c880c880, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_13267
namespace PEqualNP.Outside.L_meta_13267
open PEqualNP.Outside.L_meta_13267.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x12012953450b0c3c84006403d12b580411c307cda9229d20d2e8c71900417805400580101c00a004ce925a9970506114000024410d00b6800000001810c0ff43fe43fd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31de31fd31fc31dc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xfc202e3409c2487009e8346234864964e2fa040e00001d8d4002601836613e208ca4527800b800001b8fe7500060008301960561529000b437001dcba2f000143a8526910860d391f83813208b10042181bcd600001ec002400024000015000f0792b98c9004190806216360ec8e363203ca200200440002430001846380e0fa670580000002517868171e8786654301d0b62d3888c3e28280a4443e1a9b4000e2c8210800299544c251e0e8720a10850ac7324998000c010018040100012e1d00060007000104010916080401000f110103010000040305000f0102000a0804012613bb28e877551d0e7ca5214f546429f284853e5210b5ca4214f544429f280853e54cca7aa9994fd51329e2a26577514cae8a2995ed4132bc282655e53d06baa7a0e794f41cea9e833e52d067ca1a0cf55241afa9a835c53506dea4a0db14941bda828378505073ea6a0e714d41d7a92833c5250758a4a0cb14941dba8a83bb5050678a0a0ee141419c282833e541076a8398cf952319eaa4639e548c73aa918e790a31ce214635e518c73e8318e7506319f2a0633d540c76a8218e795031ceaa0639e420c7388418d794431eb288639f410c7ac8218e750431eaa086395410c67ea990cf15321af29e435d53c87a86390cf952219eaa443ac428867ea890cf15121afa9a435c53486f6a090de141219f2a0433d54087588410f50c4219f294813d519033c6320670c6409f284813e521027aa220678c440ce188813e5010374a0204f953309eaa6613f544c278a8985bd4930b62926177514c2e8a2984f953209eaa6413e548827aa9104fd51209e2a2415f53482b8a6905dd4520ba28a413f5408278a8105794c20aea9841e9200827ca9884f55310dc206213f5484278a9085794e10aea9c21d4318427ea8884f15110afa9a215c53442dea4885b149109f2a0213d54043a862086e10010
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x65000700ac813549c00e00996803c1058038c47a14a80f89006400a2a34d180a446015c00d86520002444c0916588ce9710080285e1401030020440550406800cb8e1815110b0f5314941c314c525069663d4541ca14b505071b5314141c614c505072b5214141ca14850506a46250731ac18141cc68c6250631a6181418c6a46250431ac181410c6956110831a5592510c61d65d0431a5592410c61f6550431a3189410c6986050431b1189410c6d06050431a5d95410c7176550431e1d89410c6946250431e1189410c6846250431e4d81410c6946050431e4181410c69060504318e98354c8717540c7218b5944208715540c421e1108310862c6254440c5544311023561150209518553082c86348020b8185200822e62d5210c5d503184315540c4108e59440043903110010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x114000000330507200201241c16110831d00c5b028218e8362181410c740310c0a0863449c3540c721a0aea2106210d04725443110283396a818c21845943110010
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 136
  | 3 => 50
  | 2 => 9
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
  | 5 => packedAt s5K5 (864+((h/16+packedAt s5K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s5K4 (4032+((h/45+packedAt s5K4 (3672+(h % 45)*8) 8) % 164)*9) 9
  | 3 => packedAt s5K3 (1996+((h/16+packedAt s5K3 (1900+(h % 16)*6) 6) % 61)*7) 7
  | 2 => packedAt s5K2 (453+((h/3+packedAt s5K2 (441+(h % 3)*4) 4) % 14)*5) 5
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x7ffffffffe03ffffc0ffffffff01fff1ffe3f
  | 1 => 0xf80fffe03ffffffffff03ffc03ffffffe3e3ff
  | 2 => 0xfff01fffffffc07fffffc0ffffffe03ffc7fc7
  | 3 => 0xffffe0003fffff80ffffff0003ffffc0ff83f8
  | 4 => 0xffffffffc0000000fffffffffc000000fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x411125228a2389122c02cb2d54b10e590dae1b
  | 1 => 0xf0448499644922458b01554c15634b262e0ed
  | 2 => 0x522d1185248907489555409a9a6b422cb45746
  | 3 => 0x64499d163912240ee669a603138d9b08df03b0
  | 4 => 0x878e1e183e1c3870fb8e38e3e00e1c30fbf800
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xe8a0c880e8a0c880e8a0c880e8a0c880e8a0c880e8a0c880e8a0c880e8a0c880e8a0c880e8a0c880e8a0c880e8a0c880e8a0c880e8a0c880e8a0c880e8a0c880, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_13267
namespace PEqualNP.Outside.L_meta_13267
open PEqualNP.Outside.L_meta_13267.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x421154b032c44003d0e00261a0d45112d00090000002e0000470038130c3c480014120b0030003717423332240020233941402b1946220a3f2a291d053e1800361f1000061e004a430f3a493b1c350008012831271b16073425022f0206100960088905043c0081434104004040e0000030017fd5003fe54017f55003fc54017fd4c057f53017f94c05fd53005f54c05fc5300ffd0c01fe43007f50c03fc43017fd48057f52017f94805fd52005f54805fc5200ffd0801fe42006f90801fd4200ff10801bc42007fcc801fe32007f4c801fc32017fd4405fe51005f94405fd51017f144057c5100ffd0401bf41007f90401fd41006f50403fc41007fcc401fe3100778c401fd31007f0c401dc31007fc8401fe21007f48401fc21017fd4005fe50005f94005fd50017f140057c5000ffd0001fe40006f90001fd4000ff10001bc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x84000df94420056f8a210003bf4108001dea084000f78c420007b86210003ee2108001f6108400bbf98020006fca01002b7c5008001df2004000ef10020007de4010003fa2008001f69004000fe48020035fecb8800afe65c400dbf32e20029f99710035facb880037d65c40013eb2e2002bf19710005fec988006fe64c4001df3262001af99310005fac988003bd64c40015eb262001bf19310005fec78801efe63c40017eb1e2007bf18f10036fea7880037d53c40017fb162000bf98b10005fac588002fc62c400dbfa962000df54b100077c8588003bc42c4001bf28e2006df147100077e8388003bd41c4001ef18e2000f70c710006fca18801b7c50c4013fda062000ef90310007788188027f840c4001dc2062000fec8310007f04188016ff65840057f32c2005df99610014fccb08016fd6584001beb2c20009f59610015f8cb08002ff6484001dfb242000afd921000dfcc908002fd64840037e3242000ef1921000d78c908002ff638400f7f31c2000f798e10005bcc708002fd6384001eeb1c2000b758e1003df8c7080177f5384001bea9c2000bfd8a10005fcc508002fd62840017e3142005dfd4a10006faa508003be4284001de2142008bf58610006fca3080177c5184001dfa0c2000ef50610007ee6308003de3184001ee18c2000fd0c610007a86308003f72184001fa10c2004bf98210006fca1080177c5084001df2042000ef10210007ee2108003fb10840117fb2a2000dfd9510004feca8800afe65440117eb2a2002bf19510046f8ca8800a7c65440017fb222000efd91100057ec888006fe64440017eb222001bf1911000778c888006bc64440017fb1a2000f7d8d10005bec68801efe63440017eb1a2007bf18d10007b8c688002dc6344011bfa9a2000df54d10005fec488003ef624400177b122000bf98910005fac488002fc6244001f63122000bb18910046fea4880037d5244001df2122000ef10910006fca2880237c5144001dfa0a2000ef50510007bc6288003dc3144001bf2822008df141100077c8088003bc4044001fd8822000fd84110025feca080037f65040013fb282002bf99410025faca0800afc6504009be32820029f19410005fec808006fe6404001df3202001af99010005fac808003bd64040015eb202001bf19010005fec60801efe63040017eb182007bf18c10026fea6080037d53040017fb102000bf98810005fac408002fc6204009bfa902000df548100077c8408003bc420400d7f3082000df94410026f8a208003bf4104001dea082000fdcc410007bc6208003dc3104001fa1882000f50c410007ee4208003f4210400b7f3002000df94010026f8a00800ffb4004001df2002000ef1001001ff08008003b84004001fd9002000fe08010007ee2008003fa1004001fa8802000fe44010
  | 1 => 0x2fc614c001fa30a6000bd18530006fca2980437c514c001dfa0a6000ef50530007bc6298003dc314c001bf2826010df141300077c8098003bc404c00ffd9826000f78c13003dfeca1800afe650c00fbf32860029f99430075faca1801f7d650c0013eb286007bf1943003dfec818006fe640c0017eb206007bf1903003dfcc61801f7f530c00fbea986000bf98830005fac41803b7f520c001bea906000ef90830007788418003de320c00fee1906000bf98430005fac2180037e510c01dbe2886000efd04300077a8218003de310c00fee188600fbf98030006fca01803b7c500c001df2006000ef1003003fbe601801ffa300c001ee9806007fe4c030065fecb9000afe65c8019bf32e40029f99720065facb900037d65c80013eb2e4002bf19720005fec990006fe64c8001df3264001af99320005fac990003bd64c80015eb264001bf19320005fec79001efe63c80017eb1e4007bf18f20066fea7900037d53c8019bfa964000df54b200077c8590003bc42c80017f30e4000bf58720006fca3900337c51c8001dfa0e4000ef50720007bc6390003dc31c8001bf286400cdf143200077c8190003bc40c80177fb2c4000dfd9620004fecb1000afe65880177eb2c4002bf1962005ef8cb1000a7c65880017fb244001bf992200077cc910006be64880017eb244000ef592200057ac910006fc64880017fb1c4007bf98e20005fac71001efc6388017bfa9c4000df54e2006dfac51002f7f5288001bea944000ef90a20007788510003ef3288001f61944000bf98620005fac3100037e5188017be28c4000efd06200077a8310003de3188001ee18c4000fb88620007d8431002afe6088001bf284400bdf142200077c8110003bc4088001f79044000fec822006dfeca900037f65480013fb2a4002bf9952006dfaca9000afc654801bbe32a40029f19520005fec890003bf64480015fb224001bf99120005fac890006fc6448001de3224001af19120005fec690003df63480016fb1a4007bf98d20005fac69001efc6348001ee31a4000b718d2006efea6900037d534801bbfa924000df549200077c8490003bc42480017fb0a4000fdd8520005eec290002fc6148001fa30a4000bd18520006fca2900377c5148001dfa0a4000ef50520007bc6290003dc3148001bf282400ddf141200077c8090003bc4048001fd9024000fb88120055feca1000afe6508015bf32840029f99420055faca100037d65080013eb284002bf19420005fec810003bf64080015fb204001bf99020005fac810006fc6408001de3204001af19020005fec61001efe6308001ef3184000b798c20005fac610003dd63080016eb184007bf18c20056fea6100037d53080197f310400adfd4820006faa410003be4208001de2104000fbcc820007d86410002fe61080017eb
  | 2 => 0x400077863200039c3190001df90c8000ef886400077a4320003bc21900035f3048013efd424009f7ca1200033e5090027dea848013ef1424009e78a120052ff6550001bfb2a80009fd9540015fccaa0052fd65500057e32a8014df19540014f8caa0006ff64500017fb1a8007bf18d400a6fea6a00037d53500017fb128000bf189400a6fea4a00037d5250001df2128001ef10940005fec2a0002fc6150001bf28a8014df1454000f7e82a0003bd4150001ef18a8000f70c54000dfec0a00037e5050029be2828001fed01400077c80a0007bc4050003fc2028001efd944000f7cca20007bd6510003de3288001efd8c4000f7cc620007bd6310003de3188012efd4c400967ea62004bbe5310025dea988000cf54c4009778a620007bf6210003df3108000af9884000f7ac420007bc6210025dfa908012cfd48400977ca42004bbd52100019ea908012ef148400077e6420003be3210001de9908000ef0c84000f7ec220007be6110003deb088000af5844000f78c22004bbf5110025df2888000cf944400977aa22004bbc51100259e2888000efcc4400077c62200039e3110001de9888000ef0c440007386220003bf2110001df1088000ef48440007784220007be60100275f3008001ee980400977ea02004bbe50100019f2808012ef5404009778a02004b3c501000f7fb2e6002bf9973003efccb9800a7e65cc0237eb2e6007df59730004facb9801efc65cc00f7fb266001bf9933003f7cc998006be64cc0017eb266007ef593300057ac99801efc64cc00fbfa9e6007f794f3003efaa798047dd53cc001aea9e6000bf98b30005fac5980477f52cc001bea966000ef90b3000778859801fdf32cc001ee9966000bf98730005fac3980037e51cc023be28e6000efd07300077a8398003de31cc00fee18e6000df9433008ef8a198003be40cc001de206600fbfd9630006fecb180027f658c0057f32c600fbf59630015f8cb1803f7c658c0053e32c6000bfd923000dfcc918002fd648c0037e3246010bf58e3007efea7180037d538c0017f3146000bf58a3007efea5180037d528c001df2146000ef10a30007bc6518003dc328c0017f30c6000bf58630006fca31803f7c518c001dfa0c6000ef50630007bc6318003dc318c00f7f3046000df9423007ef8a118003be408c001de2046000f7cc23003ff66118042ff654c001bfb2a60009fd9530015fcca98042fd654c0057e32a6010df19530014f8ca98002ff644c001dfb226000afd913000dfcc898002fd644c0037e3226000ef1913000d78c8980437f534c021ef29a6000df54d30087baa6980035d534c0017fb126000fbd8930005dec498002fc624c001f63126000bb18930086fea4980037d524c001df2126000ef10930007be6498003dd324c0017fb0a6000fdd8530005eec29800
  | 3 => 0xe32a42029f19521005fec890803bf64484015fb224201bf99121005fac890806fc6448401de3224201af19121005fec690803df63484016fb1a4207bf98d21005fac69081efc6348401ee31a4200b718d210d6fea6908037d5348435bfa924200df549210077c8490803bc4248401bf28a421adf145210077e8290803bd4148401ef18a4200f70c521007ee4290803ee21484017fb024200fed8121005f6c090802fc6048401fc3024200be181210d6f8a09085aff65084057f3284216df99421014fcca1085afd6508401beb2842009f59421015f8ca10802ff64084037f3204200ef9902100d7cc810802fd6408401deb204200af5902100df8c810802ff630840f7f3184200bf58c2103df8c61085b7f5308401bea984219bf988210b6fea4108037d5208431f7a104200ef90821007788410863ec4208401d62104217bf98421006fca21085b7c5108401dfa084200ef50421007bc6210803dc3108401f79084200fd88421007da4210803f521084017f3004200bf580210b6f8a0108037f649402bbf324a000df592500aef8c9280037f6394001bf31ca000df58e50004fac7280037c639402bbfa1ca000df90e50006fa87280577c4394001bfb14a000df98a50006fac5280027d6294001be314a015dfd0a50006fc85280033e4294001bea14a015df10a500067885280037f3294001bf194a000df4ca50006f865280037f6194001bf30ca0009f98650006fac3280037c619402bbfa0ca000cfd0650006fc83280037d41940019ea0ca015df10650006fe63280037e3194001af18ca000df4c650006f863280035c3194001bf90ca000df88650006fa43280037c2194005bf304a0029f98250016f4c1280577f409402bbe204a013bfd9640015fccb2004efd65900057e32c8001bf5924009f7ea920007be5490027deaa48001ef1524003dfcc720002fd6390027bfa9c8000df54e4000f7e8720003be4390001dea1c8001ef10e40005fcc520002fd6290027bfa948000df54a4000f7e8520003be4290001dea148001ef10a40005fcc320002fd6190001bf28c8013df1464000f7e8320003be4190001dea0c8001ef10640007bc6320003dc31900037f3048000df9424009ef8a120007bf4090003fda048001fe1024009f7ecb2004fbe6590027deb2c8013ef196400077ec720003be6390001deb1c8000ef18e4009f7ea72004f3f5390027df29c8013ef54e400067aa72004fbc5390001dfb148000ef98a400057cc520003bd6290001de3148013efd4a4009e7ea52004fbe5290027dea948000cf54a4009f78a520003bf3290001df1948000ef4ca40007786520003bf6190001df30c8000ef586400057ac320003bc6190027dfa8c8013ef946400067ca32004fbd5190027de28c8013cf146400077e6320003be3190001cf18c8000ef4c6
  | 4 => 0x87efd654c4057e32a621fdf19531014f8ca98802ff644c4037f3226200bf5913100df8c89887f7f534c401bea9a6200bfd8931005f8c49887f7f524c401bea926200ef909310077884988037e514c43fbe28a6200efd05310077a829881ff7314c401ef18a6200bfd8131005f8c09887f7c504c40f7fb286202bf9943103efcca1880a7e650c43b7eb286207df59431004faca1881efc650c40f7fb206201bf9903103f7cc818806be640c4017eb206207ef590310057ac81881efc640c40f7f3186207dfd4c310efbea6188775f530c40fef2986207df54c310efbaa6188035d530c40fee298621cf7d0c3103fbc8618803dd430c40fee2186200bf98831005fac4188777f520c401bea906200ef9083100778841881fdf320c401ef1906200f74c83103fb8641887afe610c401bf288621ddf144310077e8218803bd410c40fef9886207fd8c431007ba621881ff5310c4017f3006200bf580310eef8a01881fdf650c43bef328621dd7994310efbaca188035d650c40fee3286207f7d90310e7bcc8188039e640c401eeb206200e75903103fb8c818877df540c439ef2a0621df7550310e7b8a81881fdf620c401ef3106200f75883103fb8c418877df520c43bafa90621df7948310efbaa4188035d520c43bee290621cf7d0831007bc84188039e420c401eea10621cf710831007388418803de610c43d6f3086200f5984310efbea218877de510c401af288621df7544310efb8a2188775c510c439efa086200e7d0431007bc8218803dd410c401cea08621cf71043103fbec018803de600c401eeb006207f7180310efbea018877de500c43beea80621df7140310eeb8a018873df400c439ee2006219bfd9721015fccb908677e65c84053f32e4219bf59721006facb908027d65c84057e32e4200bfd93210077ec990802bf64c84037f3264200bf5932100df8c990803bc64c84035e3264200bfd8f2103dfcc790803de63c84016f31e4200bf58f21007bac790802dd63c840f7e31e4219dfd4f21006faa7908677f52c8401bea964200ef90b210077885908037e51c8433be28e4200efd07210077a8390803de31c8401ee18e4200bf98321005fac1908677c50c842f7fb2c4200dfd9621004fecb1080afe658842f7eb2c4202bf196210bef8cb1080a7c65884017fb244201bf992210077cc910806be64884017eb244200ef592210057ac910806fc64884017fb1c4207bf98e21005fac71081efc638842fbfa9c4200df54e210d5fac51085f7f5288401bea94421bfbd0a210077c8510803bc4288437f62144200eb10a210b5fcc3108037e518842fbe28c4200efd06210077a8310803de3188401ee18c4200fbc8621007ee4310802fe60884017eb044217df142210d5feca908037f65484013fb2a4202bf995210d5faca9080afc6548435b
  | 5 => 0x8941007dec4a0802ef62504017e3128200fb18941005d8c4a088b7f5250401bea928201efd09410077c84a0803bd4250403de2128201bfd8541006fca2a088b7c5150403fba0a8200ef9054100f7882a0807f441504017fb028200fed8141005f6c0a0802fc6050401fc3028200be18141116f8a0a0807bf4050403de2028222efd95410067ecaa088bbe6550445deb2a8222ef1954111678caa0803bf6350401cfb1a8200ef98d410077ac6a0803bc6350401ce31a8222efd4d411167ea6a088bbe5350445dea9a8200cf54d4111778a6a0803bf6250401d7b128200ef989410077ac4a0803bc62504015e3128200eb1894100558c4a088bbf52504459fa928222ef949411177aa4a08033d5250445de2928200efcc9410077c64a0803bd3250401de1928201efd854100d7ec2a0807b76150445dfa8a8222ef945410067ca2a088bbd5150445de28a8222cf145410077ec0a0803bb6050401df3028200ef5814100778c0a0802bc6050401dc3028200ae181411177ea0a088bbe5050445dea828222ef1414111678a0a081eff65cc4057f32e6207df99731014fccb98886fd65cc40fbeb2e62009f5973103df8cb9881eff64cc4037f3266200bf5933103df8c99881f7f53cc40fbea9e6200bf98b31005fac5988877f52cc401bea966200ef90b310077885988037e51cc443be28e6200efd07310077a8398802fe60cc4017eb066221df143310f5fecb188037f658c4013fb2c6202bf996310f5facb1880afc658c43dbe32c62029f19631005fec918806fe648c401df3246201af99231005fac918803bd648c4015eb246201bf192310fdfac71887b7f538c43defa9c621ed7d4e310f7bca7188037d538c43deea9c6200d754e310f7b8a718883df438c401ef21c6200f750e31107b88718802fe628c4017eb14621edfd4a31006faa518803be428c401de2146200f7cca31007bc6518803dd328c401ee1946207bf98631006fca31887b7c518c401dfa0c6200ef50631007be631881ff7318c4017f3046200bf582310f6f8a11887bdf658c401afb2c621ef7996310f7bacb1887bdc658c43dae32c6200f7d9231107bcc9188039e648c401eeb246200e759231107b8c91887bdf548c441ef2a4621ef755231107b8a918803df628c401ef3146200f758a31007b8c51887bdf528c43dafa94621ef794a310f7baa5188035d528c43dee2946220f7d0a31007bc85188039e428c401eea146220f710a31007388518876de618c43defa8c621ef794631006bca31887bdd518c43dee28c621ed714631107be83188039f418c401ef20c6200f7506310073a8318883dc418c401efb046200f798231007bac118803dc608c43defa84621ef7942310f7baa11887bdc508c43dae2846220f7d0231107b8811887eff654c401bfb2a62009fd9531015fcca98
  | 6 => 0x1bea9c6427f754e32006baa71901efe628c84fbfa946400df54a320077c8519003bc428c801ef9946407fbcca32005fcc319002fd618c84fbe28c6400bf98232005fac11909f7c508c8517fb2a6402bf99532146fcca9900a7e654c8517eb2a6400df59532004faca9900afc654c8017fb226400efd91320057ec899006fe644c8017eb226401bf1913200778c899006bc644c851bfa9a6400df54d32146fea4990037d524c801df2126400ef1093203fde6499003de324c8017fb0a6400bf18532146f8a299002ff604c8017e3026428df1413203dfeca1900afe650c80fbf32864029f99432135faca1901f7d650c8013eb286407bf1943203dfec819006fe640c8017eb206407bf1903203dfcc61901f7f530c80fef2986407df54c32137baa6190035d530c84f7f3106426dfd4832006faa419003be420c801de2106407f7cc83203fdc6419003dd320c80ff69906400bf98432005fac21909b7c510c8017f3006400bf58032136f8a0190037f649444bbf324a200cf99251006fac9288033d649444bbe324a200dfd8e51006fcc7288037d63944013eb1ca200df18e5112efe87288037e4394401bea1ca225df10e51006fec5288037e6294401beb14a2009f58a51006f8c5288977f4294401bf214a200cf90a51006fa85288977c42944019e214a200dfcca51006fc65288037d3294401be194a202df98651014fcc32880b76619444bbfa0ca225df10651006fec1288037e60944013f304a200df58251006f8c1288977f409444bbe204a201efd974100f7ccba08073e65d0403deb2e8201cf5974100f78cba0807bf63d0403df31e8201e798f4100f7ac7a08079d63d0403de31e8224efd4f411267ea7a0893be53d0449dea9e8200cf54f4112778a7a0807bf62d0403df3168200af98b4100f7ac5a0807bc62d0449dfa968224cfd4b411277ca5a0893bd52d04019ea968224ef14b410077e65a0803be32d0401de9968200ef0cb411277ea3a0893be51d04019f28e8224ef5474112778a3a08933c51d0403dfb068201ef983410057cc1a0807bd60d0403de3068224efd43411277ca1a0893bd50d0449de2868224cf1434111dfecb2080afe65904477eb2c8202bf1964100dfac92088abd649040f7f31c8200bf58e4111efea7208037d53904017f3148200bf58a4111efea5208037d5290401df2148201ef10a4100dfcc3208037e5190447be28c8201efd064100fee8320807f441904017f3048200bf5824111ef8a120807bc40904457fb2a8200dfd9541004fecaa080afe65504457eb2a8202bf19541116f8caa080a7c65504037fb228222efd514100f7ca8a088bbd5450403de2a28200bfd8d41007bec6a0802df635040f7e31a8200f718d41005b8c6a088b7f5350401bea9a8201efd0d410077c86a0803bd4350403de21a8200bfd
  | 7 => 0xa90033c6454801bfb1aa4009fd8d52006fcc6a90037d6354801be31aa42ddfd0d52006fc86a90037d435485bbe21aa402dfd8952014fec4a900b6f625485bbfa12a42ddf10952006fec2a90037e6154801beb0aa400df18552004f8c2a90b77f415485bbe20aa400dfd8152006fcc0a90037d6054801be302a4009f1815216efe80a90b77c40548577fb2c8402bf9964215efccb2100a7e65908577eb2c8400df59642004facb2100afc65908037eb24842befd524200f7ca9210afbd5490803de2a48407bf98e42005fac7210af7f5390801bea9c8401efd0e420077c8721003bd4390803de21c8401bf98a4215efea5210037d5290803dfa148401fbd0a4200fd88521002fe61908017eb0c842bdf1464200f7e8321007bc41908017f3048400bf5824215ef8a121007bf4090803de204842befd964215f7ccb210af3e6590857deb2c8400cf5964215f78cb21003bf6390801df31c8400ef58e4200778c7210afbf53908579fa9c842bef94e4215f7aa7210033d5390857de29c8401af98a4215f7ea5210af3f5290857df294842bef54a420067aa5210afbc5290801dfb0c8400ef986420077ac321002bd6190801de30c842befd464215f7ca3210afbd5190857de28c842bcf146420077ec121003be60908015f3048400ef5824200778c1210afbf5090857df284842bef5424215f78a1210af3c50908597fb2a8402bf99542165facaa100afc65508037fb228400bfd8d4203df8c6a10b37f5350801bea9a8401bfd8942166fea4a10037d5250803f7a128400ef9094200f7884a1007ec42508017fb0a8400bf18542166f8a2a1007bf41508017fb028400bf18142166f8a0a1007bc4050803dfb288401ef9944200e7cca21007bd65108039eb288401ef1944200f7ec621007be6310803deb188401ef18c421577ea6210ab3f5310855df298842aef54c420067aa6210abbc5310803df310842baf9884200f5cc4210abbf52108559fa90842aef948421577aa4210033d5210855de2908401efd844200f7cc221007bd61108015eb088401ef184421577ea2210abbe5110855dea88842aef1444215678a221007bf6010803df3008400af9804200f7ac021007bc6010855dfa80842aef940421577aa0210abbc50108559e2808407bfd9732015fccb9901f7e65cc8053f32e6429bf5973203efacb990027d65cc80f7e32e6407bfd933200dfcc99901fbe64cc8035f3266400bf5933203f7ac999002bd64cc80f7e3266407dfd4f3203efaa7990a77f52cc801bea966400ef90b32007788599002fe61cc8017eb0e6429df14732005fcc199002fd60cc853be2866427bfd9632015fccb1909f7e658c8053f32c6427bf59632006facb190027d658c8057e32c6400bfd923200dfcc919002fd648c8037e3246428bf58e3213efea71909fde538c80
  | 8 => 0x200000000800200000001600200400200c00600000400800200000600000200800000000000000c00200600000800e01601200000a00000000400000000000201600000000000200a02200400200800600000200600800600400800a00000400800c00000200200e00200000800800000000800600a00800000600000a00000201000000400200000400400000000000800000600000200000400e00000000000400200400200200001000400a00000200000a00000200800400000400c00000c00200200400a00800400001e00000000e00000000600600000000a00000200200000000000400200000400000400001e00000600e00200800000000a00400000600400200000800e00000003000401402400200000402c00c03800000000000003000001601200c00000400200200000400200400000200a00000000000400000400600000600c00000001400000000200000e01400800e01c00001400200000000000800c02200000200002800200a00400400000003000a00000000400000800400a00000200000000000202000001800a00200000002201400000000000000201000000600c00000000000800402c00000200000200200400200000200000200800400200000000e00400000200000000600600000600000400400400000001200400e01600000e00000002000000200000c00400000200000600000000000400000200000000000000a00400400000000400000003600600000000200200000000000a01200200000e00400400801000000e00400402e00400c00c00200000400000400000400801000000001a00600800400000000400200401200200000001600600800200400201a00000200000000000dfd9153186fcc8a98037d6454c61be322a602dfd8d53014fec6a980b5f6354c61bfa1aa607df10d53006fec4a98027f6254c01bf312a600df58953006f8c4a98c37f4254c61be212a600dfd8553006fcc2a98037d6154c01be30aa6009f18553186fe82a98c37c4154c01bfb02a600df98153006fac0a98037c6054c013e302a630dfd0153186f880a981eff6590c057f32c8607df99643014fccb218befd6590c0fbeb2c86009f5964303df8cb21806fd6490c0f7f31c8607dfd4e4303efaa72181fbf4390c03efa1c8607f710e43005fcc521802fd6290c5fbfa948601ef10a43005fcc321802fd6190c5fbe28c8601efd0643005fcc121802fd6090c5fbe2848601ef10243175fecaa180afe6550c5d7eb2a8602bf1954303dfec8a1806ff6350c5dbfa9a8600df54d4300fbe86a181fbe4350c0fde21a8601f710d43005fec4a1802fc6250c5dbfa928601ef10943005fec2a1802fc6150c5dbe28a8601efd0543005fec0a1802fc6050c5dbe2828601ef10143006fec8a90033f645485bbf322a400df5915216ef8c8
  | 9 => 0x4a0000000000968000000001cf00018553f8000000000b2dcc0001818eec0000000009d4000000000000000d1000000000102000000033c0000000009896b1970fc0000000001a4d594001b950d153d99d7999a87e0000000000588001cc4d3c718d6c0000005b441cbb40000348f9a2d1880006f075869129d7600000008100000008280000000000000000011e8000090001ccc00188c4e00000003b8658e0000000000101181ce8000000028c000000000000000001bbc0000000005d4000000bec00000120c48d75dc0c03c0000015057c00018e00005740000000000015e14c99d936ce21af4dac0957691d96206bcbe000019ce499307e4ce40009a8d8c1800799881b4d08c4000000000059c0011b0a180000000000013800000000000018900000000000000007c00000000000000000002c1c0806816593dbec0010f81203500012dd8c09598f4000df4ce00014f526cffd9e9c9dc90468000000000000000000dfc000b78b38000000000000000000698000000001c648a09e94e014000141c0000000004a800000141430da1d179a60001b28000000000000000ff40000000019ec0000000000012d94680000000000000000007c40000012d494c00151c06c5c9a50e29624001271aadabcea0b7da08000cb4308c8c000c204cd6f99b8000c7ca54578cf000001c001b340000018a41600000000018840000000000000000000003bd7d93a9c71720000194001b98000000b713140000000019502590ec62d3fd585850bd80010141280000005c0000001a441d0474000001244000000000000000000000000f34000000d1c5e4001531af91040f109479ce2d7dd97c1045b089400000000053937149804c330ed473119cce9a851dc1a4d69651174000000000000000214c9ca3400000c0005f4000000000899535ca00006a00000014440007b8000000001034000000c742e400000000000000000000000139cee94b816ca996f4000f94f0587c84800102c00400a00000000800800000202c00a00800c00400000e00a00e00400000c00200001400200200000200000400400600000600200000600600000000202000401600400600400000e01c00600200000000000600400a00000200000a00000200200e00600000600600800600200200000400600400400c00000000a00001e00000000000800000200000600200200200000a00400200200600000000c00000600000000200000800600200200000400000000e00200400000600600600600200200400000000600c00200001800000202402000201200200000600800000001601000000600600a00000801600000200000000000000000001800000000000800400400600200000000e00000a00202200800200200400601200c00000600e01a00200400000600400200400200
  | 10 => 0x2c1e9964df000008ce113d930400000000000000000000000166d6400000000095b018c00010da34000168a90f08000230bb00000017593b1bd875c000f5400000071c88000000131c000000305cec0001cd604c38000a1c000000000000b74a2c49dc353cd5446c910c001b70000000001aa55adb5070c37468c0001d40008dc000000000000488000000000278001441a70000000000728000200000001868f500012156e8e440014d591c1517f4000001600000544d580000000000000000002840000002700002ecb0c000b9000107c001320000dd44f4e510900018580018a8000f6ceb40000000013d00000015b5110000000001ad8000be4cd85c4fd80000e8ae9c452e000155c001cb8dbdad4ae0af10a80000018d86dd97400072515c0016dc001a389f000190c0000001300001ec000000000001a0c0012ada30000a0029c3f0b680000000013ed0807f8ea58f0499b144e40017a050524c14c0011f9b3d700e3c4ac0000005a0001548001a945dd3b84847a0519744314ec9c1513ced80dd3c1a81074118a780545496c8e249b9515a2145d3dd6603ad37c55d64465c4a50f51d0f9c0819f400000000000000101d589474c687f503c000000000000000764a21944000000000001460000000ac8000000001c0000021c001a040017a464ca315791b4401610000000000b547706b8e681558b8a4d978404001400000f456cc4f80000000001b1070000001cbceb98d536872c0018640009640000017e0e0c000000740000000000660fa80014d8000000e6d1388713f40000000016c0000001ae1c2c000000f00001695275861539a590a1c21bb5bfc0390cc0011a0001528000cf8385b09630aac00000000092000000058400070970400000117135400087c0016b40007b0aec00126880c1fc001725bf06514382c800192c9900cc2482b00000000012e80000000000006a4001911bc4000000000001c18001501590001bd0000000001c100019e571800000000133c638b504c96a0a8ce1c3f9278005398c713400000008e8001b8cca09d18b4808389559b9d145b4c001b195198391e400031c0004fc000000e840000012000000018fc654000000d90e782a17293f00000000000000010c80000011f4001a247684489bce5c0000000019587fc5cc000b982c4490000a2856c00000194884c32dc04de0000e7c5081f0a48000001b9161c0005159d49c0b58ec5614000000000000001984000e607d0000000d888447780000000000000000011ac000b109ec8c14655fc7103600018dc00186db85cf8a100002f84940000000000000019f1a40da9ab9938000b1800044c098000000000000001264085a65bb14dc2b461c000481038001918598850479a5d7bc0000011a55c19b10d5bac000000001c1d41000000121053c0140ec000
  | 11 => 0x378000000e8c000000000000000000001478bf40004e8e880012980012217b4985aa0000001a00754688000ea9454b80efc0c8000dd0ad45ec000244000000e90fdc000000000630000000000001141418000000000aa88f1a8800000128d099ca9ca5561254000c95ba41c14906106780ad1bcc3000000000000000108d23c0015c56c521c9704599299a534400130cb158c80000000019ddb20348000368000bac00086c0000000010fc0000004356e00004c54a42b9064001ba00014349256d80016fdbcd5d0000000000000cedad00014a017116c000000000cd4f117700015bc0000019ac6ec000d70000000000000000000000f803107883e53b51c8c3c0242649e0cc02e0db4bc86f4ab4b1cb3c000000a404651805d85f0fec000001b012b8500000000000000000000000000000000138001309c8039c4b5150b080002bc000000000000bb9bc00018f96ed3a0001748001a9c000425784f40fa48b84108d5a18f29835024289c585a4d6160c0000000000006fc0000014f081c0000000015f48319cc0009e58b0998d84e940f4000000001844000000a5000000137800000024d3c80000000009a4b84928000000000000000d4800000000000000000000146cdd800000000000000063c001ac40000000012e40000019411200003fc2f000189db885a95e425c1782a48a8fb4d0cf6534c25400000000109c0014ac6b097c45c56498c0009755c93e5b6000000169c000fd54840018d00003386b4874d754f8000000000001ce80000003f4b9c000044000d30ee49c5be855000000165c000001b6c5357f95d8cfdac0fa0cb8000000000000234000001580000d45cfd6d417d7792f5a54e75008000000000000000000001b5c0005ac6c47d86800000000003ec90c0880002d4000000001cad23157c0000001bc000000000e700000012500000013ac000000c7800106c000fe40000012603b03640000011580000004bd8743540015dc000d54001b44000000000000000000000000000fad1493c583c0008bd4b4ca80280005f8001998108c601dd6980000011e08e1c28bfd43d3a5adcc54000000cdc000430000000000000000000000000000000da5b400003a0e4058cba4000000000b355f8884438324000dc80000015a4000001ab16e4001004000000f38000000000000a5c60400124000000015c7a478c00185d8a00a99c802c0000580f95e8684c6512c4d4000d515a1b48460d80420ef4bd48b0adc94147c23ccbcf1c980000b4940d470ef16a452c11c0d922c82c0000018bc0013e8000f30000001284000c58000000001c69cf5908000000000c2d3bcbc00a4000000000001218000001790b000000014b00000000000000000000018ac000000001889a900006d8e6539000000100c0d52fc27c0007dd6594
  | 12 => 0x122589805c0007140000000000004083d87d496d5ecc4568ca6d155a48c49a78955395b25849afc580d2c5948140016d11c577d609168b60a60000000000001330000000000d640000000000019b4000000b5d67c868000000000000040000878afc0019e0ccd9957c40001a0888000000000798ac4000000f4d954db1b2c00004800066ca84fbd0c4f7445022d8409456907b4f21b540000003a80007cc000000e14318001bf40745716b8000001b800008551d40000000000009141254040005bc000000000e4c000bf918c000000000fcc0012b40000000007949f51b8938000001b0c000000734000000000000bdc000000000000000358000000a7000047c000001b7dbc80007480000001102a8000000a0ccd0558001830000e04000000000000a3cf5d1c07acaa026c000a252880600018c4000c80001a8dc8c85d1ece396740000000000000000000016498200000000000009c8000568000540000000001c980002f46258100010280bc0014ec93daa945135ca58f590b82d0000000000000000000188001205229905048000000000000abc0000001153349dc4d8000000000000000000fe9408b941c95717944c11ccd34000000a040b40011250accac4b0001828000000000000d40e19cc8ba80003e97740015080000018940d023892c228000000000000000000acc0009d80000012c4000c5cc00c11c89980000700784198000000a897e802000000000047170c1f4a080b00a11609480008cca7cde8000000a69488000000000000000000000d393e161962c6f8000344000000001cb47ec0fc59198c0000000000000c50400016bc000000000000000000000a9cc8800000154c000a457cdac851c000001301c40000001550b0531000067c615cdc000000a740007c8000704000c90000000070000000001b590e910073ca14dc41f8560000000f688e40c17b00015a8000000274001430000000000000d140012c0c18208000528fd01480014a83d00000001745e000000164d130000d4c0004b8c855cc50c000ebc00083c00106880400007c00067400000108800040da7dc75aecb31364001554000000000190000ad80010f0000001338ac0000184000000818e34000000d240000000012f80000000000003d46cc000000001128000000000000000000000000d040001d9735af17519c400103148d5b9bd40000000000005300000000010e50bc000d9c1ac001510000000bc4510000da0000281044000ab0ec159cc340017815d400009c0017f0000bcc6e43b40018cc0000000005558eca808010b00002252a8001ae5295195428000c0950c8adb680000003a439800000000062800064000000174d079a9932d99111c74cf3c000f70000000000000aa4001c48000cf4001740001be40000000000001580000000015f000
  | 13 => 0x221a3c000c6c2406e171190000000000114d248000001ab4001ba800178c0006c0000000000ba1360c986d5318001acc6e8000b20781ce5494a65c545200001b80001e4cc8000eccee000000105d5240016280000000000000000000000011086ad208b4d814644000000f780000016a8001ce02e8000001c5061995ce9c0002903c9c78760d954c0440f492f1051000bf15200004148c54fc000751715c3089dc2496072152d5403c40000013500000008200000015740000000000017ac0017e400000149c738000000000cb09789ac000000000000000635060218000ef8001765bb8f24001134000320000994e580005fc00000144895d7b980ca940017fc6687bcfe0fc46a8000b88000000d200004d0890670901259a684f0000210eb0000394e98000dc0db9c3d634d01c7d45836db64000000001b388f587000156c001c600000017552356880003e08b4010000000000000101708260608000001be00000000018798e4000f914bd0d8001a10001190000000000c24000ff8de4918000000000000000000000000f0c0012ec648000f98000000f853240019a0af4c1563c001800b4035c000ab8000000001c9437d34911400052457d2800012a00017eced0ff0000000001424d99598390000001b7504d2d0000000000000001bdc001388000000000000f7d58c001ae8c2800076dd019f973090442812c0000003017399680000002d80000002fc00000196000000000001883400077c88cb288c9c6c9350c00000017d08a49a166800000000135917c001808000000000000000694b6400125c0000000006d00000002503357889f8000000000000775c383706201e1b048ecf610b429576c328000000f2c000000418000000951290860b6d084fc8791679b1d1f16859154e4825cb17c80e4455a74134030d28d5d79d2cd164d19a6d198c05680c500017a8000f140000012c80009b0858000000864001c840014cc0b9480001238000000001cd0b45cd8000000000000df8000000000edd8045d029854c2ac268b8c43d6ac0000019bc6658e80510e16f0fb8000f19924000000e30d78000000000000dec0004451fc000ad0000b257d4000001a2800042c8fcf88000000ddc0009116700014d01c49b49ccbd04ec000001cd43404dc5b83cd2b0e54eac000838745c4cdcd2a4ca40000000010a505446d88060d0dd71c001a140009300000000000000000014c40010180000012bc13caf85e99fd82582c2dd9c090993573d56594cbbcd7ca3800196c000000cc40001a80014e800000000118400000000000127c38138c91c0008d99d000000000038c0e0000001b791a87f069c000000000ae48416380009fc3c00000000000010580000003dc00166544c00172c20c000001374000c0c001bf80007a8000
  | 14 => 0x1328000000000000be899c0013840008d0000204000000fb1c5c00000000156834c001119b100006000001456542ccc4d3d4e087e984c001b30001420000064000000c1c000f8d9200
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xf65590100063c65590100063f75590100063c75590100063f5359010004bc72590100063f525901000cbf715901000cbd71590100063c515901001ebb7059010006b870590100063c50590100147c75d8c1000cbe74d8c10004bd74d8c100047f7558c100147c7558c100047e7654c100047c7654c101863e6454c100063d6454c1003e5e6354c100065d6354c10005747154c100147c75d881000cbe74d8810004bd74d88100147e75988100047d75988100047f75588100147c7558810004bf745881000cbc7458810004df735881003cdc73588100147e75188100047d751881000cbe7418810004bd741881003cde7318810004dd73188100047e76548100047c765481016e3e64548100063d64548100066e62548100066d6254810005747154810005787054810004bf7690810004bd76908100063f659081015e3c6590810005ba709081000cbf7610810004bd76108100063f65108101563c651081012e3e64944100063d64944100057a7094410004bd76d04100063f65d04101263c65d0410004bf76504100063f65504101163c6550410005ac72504100065f658c4100f65c658c4101069e648c4100069d648c4101add6718c4100065f650c4100ee5c650c4100e69e640c4100069d640c41000756510c41019f54510c41000797410c41000795410c410004f5760c41019f57530c41000755530c410006d6760c410006d5760c41019f56750c41000755750c41000757650c41019f54650c41000796740c41000795740c41000796640c41000795640c41019f57520c41000755520c41000796420c41000794420c410007d2700c410007d1700c4101a6d6600c41019f54500c410197d3400c410197d0400c410005d673c8410004f57608410007a442084100147e76940100247c76940100ae3e64940100063d6494010005767194010007543194010004bf769001000cbd76900100063f659001009e3c6590010005b5719001000794319001001dba709001000cbf7610010004bd76100100063f65100100963c6510010005b571100100079431100100073a501001018f38501001001eba7610010005b9761001001eb97610010004b976100100073b651001018f38651001018f3b5310010007395310010005ba721001018f3b521001000739521001001fb27110010005b9711001001fb1711001004eba61100100073a511001018f385110010007b331100100079a3110010007983110010007b03110010007903110010007b32110010007b0211001001dba74c8010007d031c8010004f9760801001db87408010007d03108010007e02108010007b040c401003cf9768401001db87484010007d03184010004f77644010005d47344010005e47244010007725044010004fb764401001db87444010005e87244010007725144010
  | 1 => 0x8d100065c6518d100069f6418d100069c6418d1003e5e7518d1003e5d7518d100065f5218d10104de7118d1003cdc7118d100065c5118d100065c5018d100047e7654d100047c7654d100063f6454d101863c6454d100065f6354d1003e5c6354d100147c75d891000cbe74d8910004bd74d89100066f52d89100066f65d89100066c65d8910006af64d8910006ac64d8910006cf63d8910006cc63d89100066f75d89100066c75d8910006ae74d8910006ad74d89100066f53d89100066d53d89100066c51d89100066c50d89100147e75989100047d759891000cbe7498910004bd749891003cde7398910004dd7398910004ee72989100047f75589100147c7558910004bf745891000cbc7458910004df735891003cdc7358910004f77158910004fb70589100147e75189100047d75189100066f5218910004ee76189100066f65189100066c6518910006af6418910006ac6418910006cf6318910006cc63189100066e75189100066d7518910006af7418910006ac74189100066f53189100066d53189100066c51189100066c50189100047e76549100047c76549100063f645491016e3c64549100065f63549100065c63549100066f62549100066c6254910004be7690910004bc76909100063f659091015e3c65909100069f63909100069c6390910006af6290910006ac6290910004be761091000cbc76109100063f65109101563c65109100069f63109100069c6310910006af6210910006ac6210910005b5711091002c7e76945100063f649451012e3c64945100065f63945100065c63945100066f62945100066c6294510004be76d05100063f65d05101263c65d05100069f63d05100069c63d0510006af62d0510006ac62d0510005ba70d051000cbc76505100063f65505101163c65505100069f63505100069c6350510005ac7250510006af6250510006ac6250510005b87050510004de768c5100065f658c5100f65c658c5100069f648c5101069c648c510006cf628c510006cc628c510004de760c5100065f650c5100ee5c650c5100069f640c5100e69c640c510006cf620c510006cc620c5100347e76941100063f64941100ae3c64941100065f63941100065c63941100066f62941100066c6294110004be76901100063f659011009e3c65901100069f63901100069c6390110006af6290110006ac6290110004be76101100063f65101100963c65101100069f63101100069c6310110006af6210110006ac621011004eb864c4110006e862c4110006d46384110006e462841100063e74d94100063d74d94100047d73d94100047d72d94100347e71d94100067671d941002c7e70d94100067a70d9410004bd76990100063f65990100063c65990100047f75590100147c755901001cf8705901000cbf76590100063
  | 2 => 0x69f6458e100069c6458e100065e7558e100065d7558e100069f7458e100069c7458e100065f5258e10006d77158e100065c5158e100065c5058e100047f7654e100047d7654e100063f6454e101863c6454e1003e5e6354e100065d6354e10005747154e100147e75d8a100047d75d8a1000cbe74d8a10004bd74d8a1003cde73d8a10004dd73d8a100147e7598a100047d7598a1000cbe7498a10004bd7498a100147e7558a10004bf7458a1000cbc7458a100147e7518a100047d7518a1003cde7318a10004dd7318a100047f7654a100047d7654a100063f6454a1016e3c6454a100065e6354a100065d6354a10005747154a10004be7690a10004bc7690a1015e3e6590a100063d6590a100069e6390a100069d6390a10004be7610a1000cbc7610a101563e6510a100063d6510a100069e6310a100069d6310a10006ae6210a10006ad6210a100447d76946100063f649461012e3c64946100065e63946100065d63946101263e65d06100063d65d06100069e63d06100069d63d0610005ba70d06101163e65506100063d65506100069e63506100069d6350610005ac7250610005b870506100f65e658c6100065d658c6100069f648c6101069c648c6100ee5e650c6100065d650c6100069f640c6100e69c640c61000756510c6101a754510c61000797410c61000795410c610006d5630c6101a757530c61000755530c610005d5760c610006d5760c6101a756750c61000755750c6101a756650c61000755650c61000796740c61000795740c61000797640c61000794640c6101a757520c61000755520c61000796420c61000794420c6101a754500c610005d673c8610007a442086100147d76942100063f64942100ae3c64942100065e63942100065d639421000576719421000754319421009e3e65902100063d65902100069e63902100069d6390210005b571902100079431902100963e65102100063d65102100069e63102100069d6310210005b5711021000794311021004eb864c42100147e76d95100047d73d95100047d72d95100147e71d95100147c71d95100147e70d95100147c70d951000cbe76d91100063f65d91100063c65d91100063f53d9110004be72d91100063f52d91100063c51d911000cbe70d911000cbc70d91100063c50d91100047f75591100147c7559110004df735911003cdc7359110004ef7259110004ec725911004cfb7059110004be76191100063f65191100063c65191100147c75d8d100065f53d8d1003cde76d8d100065f65d8d100065c65d8d100069f64d8d100069c64d8d100065f75d8d100065c75d8d100065f52d8d100065c51d8d100065c50d8d100047f7558d100147c7558d10004bf7458d1000cbc7458d10004ef7258d10004ec7258d10004f77158d10004de7618d100065f651
  | 3 => 0xe65100200063d65100200069e63100200069d6310020005ae7210020004ef7648020005cc7348020005e471480201bf685048020007aa4048020004fb76480201bf6b5248020007aa4248020005f071480200147f76597100047f73597100047f72597100147e75d93100047d75d9310004bd76993100063e65993100063d659931000cbf76593100063e65593100063d65593100063f5359310004bc72593100063f52593100063c5159310006bb705931004eb870593100063c50593100147e75d8f100047d75d8f1000cbe74d8f10004bd74d8f10004ee72d8f10004ed72d8f100147e7558f100047f7654f100047d7654f101863e6454f100063d6454f100065f6354f1003e5c6354f100147e75d8b100047d75d8b1000cbe74d8b10004bd74d8b1003cde73d8b10004dd73d8b100147e7598b100047d7598b1003cde7398b10004dd7398b100147e7558b10004bf7458b1000cbc7458b100147e7518b100047d7518b1000cbe7418b10004bd7418b100047f7654b100047d7654b1016e3e6454b100063d6454b10005787054b10004bf7690b10004bd7690b1015e3e6590b100063d6590b10005ba7090b1000cbf7610b10004bd7610b101563e6510b100063d6510b10005b57110b100147d769471012e3e64947100063d64947100057a70947101263e65d07100063d65d07101163e65507100063d6550710005ac7250710005b870507100f65e658c7100065d658c7101069e648c7100069d648c7100ee5e650c7100065d650c7100e69e640c7100069d640c7100447d76943100ae3e64943100063d649431009e3e65903100063d65903100963e65103100063d65103100073a50103101b7385010310005b9761031004eb976103101b73a65103100073965103101b73b5310310007395310310005ba72103101b73b5210310007395210310005b971103100073a51103101b73851103100079a311031000798311031004dba74c831004db874083100147f76596100063f74596100063c74596100047f73596100047f72596100147e75d92100047d75d921003cde73d9210004dd73d9210004ee72d9210004ed72d92100063e65d92100063d65d9210005ae72d92100063e75d92100063d75d92100069e73d92100069d73d92100063f53d9210004be72d9210006ae72d9210004ae72d9210006ad72d92100063f52d9210006b571d92100063c51d9210006ba70d92100063c50d92100063e65192100063d65192100147e75d8e100047d75d8e10004dd7698e100065e6598e100065d6598e100069f6498e100069c6498e1003e5e7598e1003e5d7598e1003e9e7498e1003e9d7498e100065f5298e100065c5198e100065c5098e100147e7558e10004bf7458e1000cbc7458e100065f5358e1003cdf7658e100065e6558e100065d6558e10
  | 4 => 0x41200065f63941200065c6394120006776194120006746194120004be76901200063f659012009e3c65901200069f63901200069c6390120006b76190120006b46190120004be76101200063f65101200963c65101200069f63101200069c6310120006b76110120006b46110120006f061c8120006cc6388120006e461881200147f76594200063f74594200063c74594200047f73594200147f72594200147d72594200047c71594200547c70594200147e75d90200047d75d902003cde73d9020004dd73d90200063e65d90200063d65d90200063e75d90200063d75d90200069e73d90200069d73d90200063f53d9020004be72d9020006ae72d90200063f52d9020004bd71d90200063c51d9020004be70d9020006ba70d90200063c50d90200063e65190200063d6519020005b571190200147e75d8c200047d75d8c20004dd7698c200065e6598c200065d6598c200069f6498c200069c6498c2003e5e7598c2003e5d7598c2003e9e7498c2003e9d7498c200065f5298c20004de7198c200065c5198c200065c5098c200147e7558c20004bf7458c2000cbc7458c200065f5358c2003cdf7658c200065e6558c200065d6558c200069f6458c200069c6458c200065e7558c200065d7558c200069f7458c200069c7458c20006cc7258c200065f5258c20004dc7158c200065c5158c200065c5058c200047f7654c200047d7654c200063f6454c201863c6454c2003e5e6354c200065d6354c200056f7254c20005787054c200647f76548200063f645482016e3c64548200065e63548200065d635482015e3e65908200063d65908200069e63908200069d6390820005ba70908201563e65108200063d65108200069e63108200069d6310820005ba7010820006cd63cc820004ed760c8200074d530c820005e9700c8200147c759842000cbe7498420004bd74984200047f75584200147c7558420004bf745842000cbc7458420004df735842003cdc73584200047f76944200047d76944200063f649442012e3c64944200065e63944200065d6394420004be76d04201263e65d04200063d65d04200069e63d04200069d63d0420005ae72d0420005ba70d0420004bc76504201163e65504200063d65504200069e63504200069d6350420005ac7250420006b66150420006b56150420005b87050420004df768c420004dd768c4200f65e658c4200065d658c4200069f648c4201069c648c42003cdf760c420004dd760c4200ee5e650c4200065d650c4200069f640c4200e69c640c4200deac64884200c6ac640842005c7f76940200147d76940200063f64940200ae3c64940200065e63940200065d63940200056d729402009e3e65900200063d65900200069e63900200069d6390020005ae7290020004be761002000cbc76100200963
  | 5 => 0x963c6510220005ae72102200147e76d95200047d73d952006c7d72d95200047e71d952000cbe76d91200063f65d91200063c65d91200063f53d912000cbe72d912000cbc72d91200063f52d9120004bd71d91200063c51d91200063c50d91200047f75591200147c7559120004df735912003cdc7359120004f77159120004f47159120004be76191200063f65191200063c65191200147c75d8d200065f53d8d2003cde76d8d200065f65d8d200065c65d8d200069f64d8d200069c64d8d200065f75d8d200065c75d8d200065f52d8d20004de71d8d200065c51d8d200065c50d8d200047f7558d200147c7558d20004bf7458d2000cbc7458d20004ef7258d20004f77158d20004f47158d20004de7618d200065f6518d200065c6518d200069f6418d200069c6418d2003e5e7518d2003e5d7518d200065f5218d20004de7118d200065c5118d200065c5018d200047e7654d200047c7654d200063f6454d201863c6454d200065f6354d2003e5c6354d200147c76549200063f645492016e3c64549200065f63549200065c6354920005787054920004be76909200063f659092015e3c65909200069f63909200069c6390920004be76109200063f65109201563c65109200069f63109200069c63109200072d52109200147e75d85200047d75d852003cde73d8520004dd73d85200067451d85200067765d85200067465d8520006b764d8520006b464d8520006d763d8520006d463d85200067675d85200067575d8520006b774d8520006b474d8520006d673d8520006d573d85200067753d85200067553d85200067752d85200067552d8520006b642d8520006b442d85200067450d85200147c751852000cbe7418520004bd7418520006745118520006776518520006746518520006b76418520006b46418520006d76318520006d46318520006777518520006747518520006b67418520006b57418520006d77318520006d47318520006775318520006755318520006775218520006755218520006b64218520006b442185200067450185200047e76945200047c76945200063f649452012e3c64945200065f63945200065c6394520006776194520006746194520004be76d052000cbc76d05200063f65d05201263c65d05200069f63d05200069c63d0520006b761d0520006b461d0520004be7650520004bc76505200063f65505201163c65505200069f63505200069c6350520005ac7250520006b76150520006b46150520005b87050520004de768c520004dc768c5200065f658c5200f65c658c5200069f648c5201069c648c520006d7618c520006d4618c520004de760c52003cdc760c5200065f650c5200ee5c650c5200069f640c5200e69c640c520006d7610c520006d4610c5200647e76941200063f64941200ae3c649
  | 6 => 0xd739403009e3e65900300063d65900300963e65100300063d6510030004df764c0300065d654c030005cc724c030005d4714c0300147f76597200047f73597200047c71597200147e75d93200047d75d9320004bd76993200063e65993200063d659932000cbf76593200063e65593200063d65593200063f53593200063f5259320004bf71593200063c51593200063c50593200147e75d8f200047d75d8f2000cbe74d8f20004bd74d8f20004f671d8f20004f571d8f200147e7558f200047f7654f200047d7654f201863e6454f200063d6454f200065f6354f2003e5c6354f20005787054f200547f7654b2016e3e6454b200063d6454b2000cbd7690b2015e3e6590b200063d6590b20005ba7090b201563e6510b200063d6510b200072d5210b20005ba7010b200147c759872000cbe7498720004bd74987200047f75587200147c7558720004df735872003cdc73587200047f76947200047d769472012e3e64947200063d649472000cbf76d0720004bd76d07201263e65d07200063d65d0720005ba70d0720004bf7650720004bd76507201163e65507200063d6550720005ac7250720005b870507200f65e658c7200065d658c7201069e648c7200069d648c7200ee5e650c7200065d650c7200e69e640c7200069d640c720006d6610c720006d5610c72006c7d76943200ae3e64943200063d649432009e3e65903200063d65903200963e65103200063d65103200063e74d96200063d74d96200047d73d96200066d72d96200047e71d96200067a70d9620004bd76992200063f65992200063c65992200047f75592200147c755922000cbf76592200063f65592200063c65592200063f75592200063c75592200063f53592200063f5259220004bf71592200063c51592200063c50592200147c75d8e2000cbe74d8e20004bd74d8e200047f7558e200147c7558e200047e7654e200047c7654e201863e6454e200063d6454e2003e5e6354e200065d6354e200056f7254e2016e3e6454a200063d6454a20005787054a200063f6590a2015e3c6590a200063f6510a201563c6510a200074d530ca200147e75986200047d759862000cbe7498620004bd74986200047f75586200147c7558620004df735862003cdc73586200047e769462012e3e64946200063d649462000cbf76d0620004bd76d06200063f65d06201263c65d0620005ae72d0620004bf7650620004bd76506200063f65506201163c6550620005ac7250620005b870506200065f658c6200f65c658c6201069e648c6200069d648c6200065f650c6200ee5c650c6200e69e640c6200069d640c6200deae64886200c6ae64086200147e76942200ae3e64942200063d64942200056d729422000cbd76902200063f659022009e3c6590220005ae72902200063f6510220
  | 7 => 0x930006af6210930006ac6210930004de76cc9300055d75cc930006cc62cc9300055d754c930006cc624c9300147e75d85300047d75d85300067451d85300067765d85300067465d8530006b764d8530006b464d85300075553d8530006e762d8530006e462d85300067675d85300067575d8530006b774d8530006b474d85300067753d85300067553d85300067752d85300067552d8530006b642d8530006b442d85300067450d85300147c751853000cbe7418530004bd74185300065d5318530006745118530006776518530006746518530006b76418530006b46418530007555318530006e76218530006e46218530006777518530006747518530006b67418530006b57418530006d77318530006775318530006d65318530006755318530006d55318530006555318530006775218530006755218530006b64218530006b44218530006d73218530006d532185300067450185300047e76945300047c76945300063f649453012e3c64945300066f62945300066c6294530006776194530006746194530004be76d053000cbc76d05300063f65d05301263c65d05300071d53d0530006af62d0530006ac62d0530006b761d0530006b461d0530004be7650530004bc76505300063f65505301163c65505300071d5350530005ac7250530006af6250530006ac6250530006b76150530006b46150530005b870505300055f758c5300065f658c5300f65c658c5300069f648c5301069c648c530006cf628c530006cc628c530006d4618c5300055d750c5300065f650c5300ee5c650c5300069f640c5300e69c640c530006cf620c530006cc620c530006d7610c53008c7e76941300063f64941300ae3c64941300066f62941300066c6294130006776194130006746194130004be76901300063f659013009e3c65901300071d5390130006af6290130006ac6290130006b76190130006b46190130004be76101300063f65101300963c65101300071d5310130006af6210130006ac6210130006b76110130006b461101300055f758c130006cc628c130006d4618c13003c7f735943003c7d73594300047f725943003e5c32594300047c715943003e5c31594300747c705943003e5f30594300147e75988300047d75988300147e7558830004bf745883000cbc74588300047f76548300047d76548300055f735483000578705483015e3e65908300063d65908301563e65108300063d6510830006ae6210830006ad6210830004dd768c8300065d658c8300147c759843000cbe7498430004bd749843003ed431984300047f75584300147c75584300047f76944300047d76944301263e65d04300063d65d04301163e65504300063d6550430005ac7250430005b870504300f65e658c4300065d658c43007c7f76940300147d76940300055
  | 8 => 0xcbf76d0730004bd76d07301263e65d07300063d65d07300071d53d0730004bf7650730004bd76507301163e65507300063d65507300071d5350730005ac7250730005b870507300055f758c7300f65e658c7300065d658c7301069e648c7300069d648c7300847d76943300ae3e64943300063d649433009e3e65903300063d65903300071d53903300963e65103300063d65103300071d53103300065d73d96300047d72d96300047e71d96300067a70d96300047f75592300147c75592300865d6354e30005787054e3003f5b3054e300147e7598a300047d7598a300047f7558a300147c7558a30004bf7458a3000cbc7458a300047c7654a300055f7354a300063f6590a3015e3c6590a30005ba7090a300063f6510a301563c6510a300065f658ca300065f650ca300147e75986300047d759863000cbe7498630004bd74986300047f75586300147c75586300047e76946300063f65d06301263c65d06300063f65506301163c6550630005ac7250630005b870506300065f658c6300f65c658c630006d6618c6300065f650c6300ee5c650c6300147e76942300055d73942300063f659023009e3c65902300063f65102300963c65102300065f65cc2300075a50cc2300147e76d95300847d73d95300047d72d95300047e71d953000cbe76d91300063f65d91300063c65d91300063f53d9130004be72d91300063f52d9130004bd71d91300063c51d91300063c50d91300047f75591300147c7559130004ef7259130004ec7259130004f77159130004f47159130004be76191300063f65191300063c65191300147c7654d300063f6454d301863c6454d30005787054d300165f7654d300855c7654d300165c7654d300145c7654d300071f6454d300071c6454d300055f7254d300055c7154d300075b7054d300055c7054d30007587054d3003e5f6054d3003f5b6054d300147c75d893000cbe74d8930004bd74d89300066f52d89300066f65d89300066c65d8930006af64d8930006ac64d89300074d53d89300066f75d89300066c75d8930006ae74d8930006ad74d89300066f53d89300066d53d89300066c51d89300066c50d89300147e75189300047d75189300065d53189300066f52189300066f65189300066c6518930006af6418930006ac64189300074d53189300066e75189300066d7518930006af7418930006ac74189300066f5318930006ce53189300066d5318930006cd53189300064d53189300066c51189300066c50189300047e76549300047c76549300063f645493016e3c64549300066f62549300066c6254930004be7690930004bc76909300063f659093015e3c65909300071d5390930006af6290930006ac6290930005ba7090930004be761093000cbc76109300063f65109301563c65109300071d531
  | 9 => 0xe754c8400053d754c8400953e750c8400053d750c8400071d530c840005ba700c840005b9700c8400063f75584400063c75584400069f73584400069c73584400063f53584400063d5358440006af7258440004bc7258440006ac7258440004ac72584400063f52584400063d525844000eb771584400063c5158440006b870584400063c505844012e3e76944400063d76944400053d73944400053d72944400063e62944401ed3e71944400973671944400063d61944400053e709444009e3e609444012f3a60944400953e75cc4400053d75cc440005ba70cc440005b970cc44000cbe768c440004bd768c4400053f758c4400953c758c4401df1f538c4400071d538c4401069e768c4400069d768c4400071f758c4401df1c758c4400069e628c4401df1f528c4400071d528c4400e59e718c4400069d618c4400071e518c4401df1c518c4401e69e608c4401079a608c4401df1c508c4400053f754c4400953c754c440005bb704c440005b8704c44000cbe760c440004bd760c4400953e750c4400053d750c4401cf1f530c4400071d530c4400e69e760c4400069d760c4401cf1e750c4400071d750c4400069e620c4401cf1f520c4400071d520c4401059e710c44000796710c4400069d610c4400071e510c4401cf1c510c4401d69e600c4400e79a600c4401cf1c500c440004bf76c84400953e75c84400053d75c84400059e73c84400059d73c8440005ba70c8440005b970c844000cbe7688440004bd76884400053f75884400953c7588440006b56188440004bf764844000cbc76484400053f75484400953c75484400059f73484400059c7348440006b56148440005bb7048440005b8704844000cbe7608440004bd76084400953e75084400053d75084400053d73940400053d72940400063e62940400053e71940400063d61940400071e31940400071c31940401c53e70940400973a709404009e3e60940400af3a60940400047f72597300047c715973003e5c315973003e3f535933003e3d5359330004bc72593300063f5259330004bf71593300063c515933003e9c31593300063c505933003d5f7654f300765f7654f3003f1e6454f3003f1d6454f300055f7254f300055c7154f300055c7054f300147e7598b300047d7598b300065d5398b300147e7558b30004bf7458b3000cbc7458b300047f7654b300047d7654b3016e3e6454b300063d6454b30005787054b30004bf7690b30004bd7690b3015e3e6590b300063d6590b300071d5390b3000cbf7610b30004bd7610b301563e6510b300063d6510b300071d5310b300055d754cb300147c759873000cbe7498730004bd74987300065d539873003ed431987300047f75587300147c755873003ed431587300047f76947300047d769473012e3e64947300063d6494730
  | 10 => 0x86400063f75586400063c75586400069f73586400069c73586400063f53586400063d5358640004bc72586400063f52586400063d52586400063c51586400063c5058640005ba70186400063e76946400063d76946400053d73946400053d72946400063e629464009d3e719464009f3671946400063d61946400053e709464012e3e609464009d3e75cc6400053d75cc640004be768c640004bd768c6400053f758c64009d3c758c6401e71f538c6400071d538c6400069e768c6400069d768c6400071f758c6401e71c758c6400069e628c6401e71f528c6400071d528c6400069d618c6400071e518c6401e71c518c6401e71c508c6400053f754c64009d3c754c640004be760c640004bd760c64009d3e750c6400053d750c6401d71f530c6400071d530c6400069e760c6400069d760c6401d71e750c6400071d750c6400069e620c6401d71f520c6400071d520c64000796710c6400069d610c6400071e510c6401d71c510c6401d71c500c640004bf76c864009d3e75c86400053d75c86400059e73c86400059d73c8640004be7688640004bd76886400053f758864009d3c7588640006ae6288640004bf7648640004bc76486400053f754864009d3c75486400059f73486400059c7348640005bb7048640005b87048640004be7608640004bd760864009d3e75086400053d7508640006ae62086400053d73942400053d72942400063e62942400053e71942400063d61942400071e31942400071c319424009d3e709424009f3a70942400ae3e60942400147e76d95400047d73d95400047d72d95400ae3c42d95400047e71d95400ae3f41d95400ae3c40d95400147c75d8d400047e7654d400047c7654d400147c75d89400147e75189400047d75189400047e76549400047c76549400063f659094015e3c6590940006ac62909400147e75d85400047d75d854003cde73d8540004dd73d85400147c75185400047e76945400047c76945400063f65505401163c6550540005ac7250540006b76150540005b870505400065f658c5400f65c658c5400065f650c5400ee5c650c540006d7610c540006d4610c5401c47e76941400063f659014009e3c65901401fd3f7354c400971f7354c401871e6354c401871d6354c400053f7254c400053c7154c400053c7054c4009e3e6054c401873a6054c400063e75988400063d75988400063f53988400063d539884000eae72988400063f5298840004bd71988400063c51988400063c50988400063f765484016e3c76548400053f73548401f53f72548400972f72548400063e62548400053c71548400053c705484009e3e605484016f3a605484000cbe76cc840004bd76cc8400953e75cc8400053d75cc8400953e758c8400053d758c8400071d538c840004bf764c84000cbc764c8400953
  | 11 => 0x63d62506500ad3f71506500af3771506500063e61506500073b70506500053c70506500073870506500053870506501163e60506501173a60506500047e76cc6500047d76cc6500047f768c6500ad3e748c6500053d748c6500065d638c6500065f768c6500065c768c6500071e748c6500071d748c6500065d628c6500071e428c6500071c428c6500ed5e718c6500065e618c6500071f418c6500071d418c6500f65e608c6500f75a608c6500047f764c6500047c764c6500047e760c6500047d760c6500ad3e740c6500053d740c6500065d630c6500065e760c6500065d760c6500071e740c6500071d740c6500065d620c6500071e420c6500071c420c6500f55e710c65000756710c6500065e610c6500071f410c6500071d410c6500ee5e600c6500ef5a600c6500047e76c86500047d76c86500053f74c86500ad3c74c86500055e73c86500055d73c86500047f76886500ad3e74886500053d74886500072c42886500047f76486500047c76486500053f74486500ad3c74486500055f73486500055c73486500057b70486500057870486500047e76086500047d76086500ad3e74086500053d74086500072c420865003e5e6354e400065d6354e4009d3e7590e400053d7590e4003cbf7650e400147e7598a400047d7598a400066e6254a400066d6254a4009d3e7590a400053d7590a40006ae6290a400047f75586400147c7558640004df735864003cdc73586400053f755064009d3c75506400059f73506400059c7350640005af7250640005ac7250640006b561506400af3b4094240005ba70d8e4009d3e7598e400053d7598e4009d3e7518e400053d7518e40005ae7218e40005ad7218e40005ba7018e4009d3f7354e4009f1f7354e400071e6354e400071d6354e400053f7254e400053c7154e400053c7054e401863e6054e40005ba70d8a4009d3e7598a400053d7598a400063e7598a400063d7598a400063f5398a400063d5398a400063f5298a40006ae5298a40006ad5298a40004bd7198a400063c5198a400063c5098a4009d3e7518a400053d7518a400059e7318a400059d7318a40005ba7018a400063f7654a400063c7654a400053f7354a4009d3f7254a4009f2f7254a400063e6254a400072e6254a400062e6254a400072d6254a400053c7154a400053c7054a4016e3e6054a40004be76cca40004bd76cca4009d3e75cca400053d75cca4009d3e758ca400053d758ca400071d538ca40006ae628ca40004bf764ca40004bc764ca4009d3e754ca400053d754ca40006ae624ca4009d3e750ca400053d750ca400071d530ca4009d3e75d86400053d75d86400059e73d86400059d73d8640005ae72d8640005ad72d8640005ba70d864004eba60986400053f755864009d3c75586400059f73586400059c735
  | 12 => 0xd65908210c5ae7290821005b5719082100cbf7610821004bd76108211563e65108210063d651082120f2f52108210072d5210821005b571108210c6ae76108210c6ad7610821004ad76108210c72e75108210c72d751082120f2e65108210072d651082120f2f53108210072d53108210c7a67110821005ad71108210c7a571108210deae611082120f2c5110821005ae701082120f2c50108210bc7f76944210147d769442112e3e64944210063d64944210056d72944210072c4294421004bd76d04211263e65d04210063d65d0421004bf76504211163e65504210063d6550421005ac7250421005b870504210f65e658c4210065d658c4211069e648c4210069d648c4210078c428c4210ee5e650c4210065d650c4210e69e640c4210069d640c4210078c420c42120754510c4210c5ac74c8421007a44288421004ef76484210c5ac7448421005e87048421004f77648421005f070484210147c75980210047f75580210147c7558021004bf745802100cbc7458021004df735802103cdc73580210957a70d92500ae3c64592500757a70d8e500065f6398e500047f7258e500047c7158e500065d6318e5007d7a7018e500047e7690e500047d7690e500ad3e74d8a500053d74d8a500557a70d8a500053f7458a500ad3c7458a500055f7358a500055c7358a500063f7458a500063c7458a500047f7358a500065f7358a500045f7358a500065c7358a500047c7158a500055e7318a500055d7318a5005d7a7018a500047e7690a500047d7690a500063e7690a500063d7690a500063d6390a500ad3e7290a500063d6290a500053d7190a500053e7090a5015e3e6090a5015f3a6090a500ae3e7610a500ae3d7610a500063d6310a5015d3e7210a500af2e7210a500063d6210a500053d7110a500053e7010a501c63e6010a501573a6010a500047e76cca500047d76cca500ad3e74cca500053d74cca500065d63cca500047e768ca500047d768ca500047d764ca500053f744ca500ad3c744ca500065d634ca500047e760ca500047d760ca500055e73d86500055d73d86500257a70d86500ad3e74986500053d74986500063e74986500063d74986500047d73986500047d72986500063e42986500063c42986500055f73586500055c73586500ad3e74186500053d741865002d7a70186500ae3e76d06500ae3d76d06500af1e73d06500af1d73d06500063d63d06500053e72d06500063d62d06500063e61d06500053e70d06501c63e60d06501273a60d06501153d74906500047f76506500047c76506500055f73506500055c73506500056f72506500056c72506500057b70506500057870506500063f76506500063c76506500071f73506500071c73506500063d63506500072f72506500053c72506500072c72506500052c7250650
  | 13 => 0x8d210065f53d8d2103cde76d8d210065f65d8d210065c65d8d210069f64d8d210069c64d8d210065f75d8d210065c75d8d210065f52d8d210065c51d8d210065c50d8d210047f7558d210147c7558d21004bf7458d2100cbc7458d21004fb7058d21004f87058d21004de7618d210065f6518d210065c6518d210069f6418d210069c6418d2103e5e7518d2103e5d7518d210065f5218d210065c5118d210065c5018d210047e7654d210047c7654d210063f6454d211863c6454d210065f6354d2103e5c6354d210147c76549210063f645492116e3c64549210065f63549210065c6354921005747154921004be76909210063f659092115e3c65909210069f63909210069c6390921004be76109210063f65109211563c65109210069f63109210069c63109210cc7e76945210063f649452112e3c64945210065f63945210065c6394521004be76d05210063f65d05211263c65d05210069f63d05210069c63d0521005ae72d052100cbc76505210063f65505211163c65505210069f63505210069c6350521005ac7250521005b87050521004de768c5210065f658c5210f65c658c5210069f648c5211069c648c521004de760c5210065f650c5210ee5c650c5210069f640c5210e69c640c52100795410c5210deac64885210147e75d81210047d75d812100cbe74d8121004bd74d81210067850d81210067b65d81210067865d8121006bb64d8121006b864d8121006db63d8121006d863d81210067a75d81210067975d8121006ba74d8121006b974d81210067b53d81210067953d81210067b52d81210067952d8121006ba42d8121006b842d81210067a51d81210067851d8121006bb41d8121006b941d8121006da31d8121006d831d81210147c75181210067850181210067b6518121006786518121006bb6418121006b86418121006db6318121006d863181210067b7518121006787518121006bb7418121006b874181210067b53181210067953181210067b5218121006795218121006ba4218121006b842181210067a5118121006785118121006bb4118121006b94118121006da3118121006d83118121006f32118121006ea21181210147f76594210047f73594210b47c71594210047c70594210147e75d90210047d75d9021004bd76990210063e65990210063d65990210c4ec725902100cbf76590210063e65590210063d65590210063f53590210c6af7259021006ac72590210063f52590210063c5159021004bc70590210063c50590210147e75d8c210047d75d8c2100cbe74d8c21004bd74d8c210147e7558c210047f7654c210047d7654c211863e6454c210063d6454c210065f6354c2103e5c6354c21005747154c210cc7f765482116e3e64548210063d6454821004bf769082100cbd769082115e3e65908210063
  | 14 => 0x69c6458f210065e7558f210065d7558f210069f7458f210069c7458f210065f5258f210065c5158f210065c5058f210047f7654f210047d7654f210063f6454f211863c6454f2103e5e6354f210065d6354f21005747154f210b47f7654b210063f6454b2116e3c6454b210065e6354b210065d6354b2115e3e6590b210063d6590b210069e6390b210069d6390b21005b57190b211563e6510b210063d6510b210069e6310b210069d6310b21005b57110b210d47d76947210063f649472112e3c64947210065e63947210065d63947211263e65d07210063d65d07210069e63d07210069d63d0721005ae72d07211163e65507210063d65507210069e63507210069d6350721005ac7250721005b870507210f65e658c7210065d658c7210069f648c7211069c648c7210ee5e650c7210065d650c7210069f640c7210e69c640c72121f54510c7210147c759832100cbe7498321004bd74983210047f75583210147c7558321004bf745832100cbc74583210063e74d96210063d74d96210047d73d96210066d72d96210067671d96210047e70d9621004bd76992210063f65992210063c65992210047f75592210147c755922100cbf76592210063f65592210063c65592210063f75592210063c75592210063f5359221006af72592210deac72592210063f52592210063c5159221004bc70592210063c50592210147c75d8e2100cbe74d8e21004bd74d8e210047f7558e210147c7558e210047e7654e210047c7654e211863e6454e210063d6454e2103e5e6354e210065d6354e2116e3e6454a210063d6454a21005747154a210063f6590a2115e3c6590a210063f6510a211563c6510a212172f5210a210072d5210a21005ad7610a210dead7610a210df2e7510a210df2d7510a210072f6510a212172c6510a212172f5310a210072d5310a21005ad7110a212172c5110a21005ae7010a212172c5010a210147e769462112e3e64946210063d64946210056d72946210072c42946210063f65d06211263c65d06210063f65506211163c6550621005ac7250621005b870506210065f658c6210f65c658c6211069e648c6210069d648c6210078c428c6210065f650c6210ee5c650c6210e69e640c6210069d640c6210078c420c62100795410c6210ddac74c86210147e75982210047d759822103cde7398221004dd73982210047f75582210147c7558221004bf745822100cbc74582210147e76d95210047d73d95210d47d72d95210047e70d952100cbe76d91210063f65d91210063c65d91210063f53d91210063f52d91210063c51d9121004be70d91210063c50d91210047f75591210147c7559121004df735912103cdc73591210dcef7259121004fb7059121004f87059121004be76191210063f65191210063c65191210147c75d
  | 15 => 0xe61908312671c51908310059e70908312671c50908310e59f76108310059d76108310e71e75108310e71d75108312571e65108310071d651083125d9e72108310e78e72108312571f52108310071d52108310e79671108310059d71108310e79571108310059571108311069e61108312571c51108310059e70108312571c50108310ed5c75984310f65e65984310065d65984310e59e74984310059d74984311069e64984310069d649843124f54519843100757759843124f54759843103f56659843103f55659843100796749843100795749843103f96649843103f95649843124f575298431007555298431007964298431007944298431005d6709843124f5450984310055f76944310ed5d76944310071e74944310071d74944310071e64944310071d64944310055d72944310071e42944310071c42944310ed5e71944310ef5671944310f65e61944310075661944310055e70944310059d76d04310e69d76d04310049d76d04310e71e75d04310e71d75d04312471e65d04310071d65d04310059e72d04312471f52d04310071d52d04311069e61d04310079661d04310071e51d04312471c51d04310059e70d04312471c50d043123d9d7490431237545190431104df76504310055f75504310ed5c7550431005cf7250431005cc7250431227545150431005db7050431005d870504310059f76504310069f76504310049f76504310071f75504312271c75504312271e65504310071d65504310078f72504310059c72504310078c72504310058c72504312271f52504310071d52504310e59f71504310e797715043122e9e61504310079661504312279751504310071e51504312271c51504312279451504312271451504310079b70504310059c70504310079870504310059870504312271c50504310ed5c75980310055f75580310ed5c75580310065d65580310059f74580310e59c7458031005cf7258031005cc72580310147f76597210063f74597210063c74597210047f73597210047c70597210147e75d93210047d75d932103cde73d9321004dd73d9321004fa70d9321004f970d93210063e65d93210063d65d9321005ba70d93210063e75d93210063d75d93210069e73d93210069d73d93210063f53d9321006ae72d93210063f52d9321006b571d93210063c51d9321004be70d9321006ba70d9321004ba70d9321006b970d93210063c50d93210063e65193210063d65193210147e75d8f210047d75d8f21004dd7698f210065e6598f210065d6598f210069f6498f210069c6498f2103e5e7598f2103e5d7598f2103e9e7498f2103e9d7498f210065f5298f210065c5198f210065c5098f210147e7558f21004bf7458f2100cbc7458f210065f5358f2103cdf7658f210065e6558f210065d6558f210069f6458f21
  | 16 => 0x89310047d75189310047e76549310047c76549310063f659093115e3c65909310063f65109311563c6510931006af6210931006ac621093110c7e76945310063f65d05311263c65d05310063f65505311163c6550531005ac7250531005b870505310065f658c5310f65c658c5310147e75d81310047d75d813100cbe74d8131004bd74d81310147c75181310ee5f735943103e5c73594310047f725943103e5c32594310ec7c715943103e5c31594310047c705943103e5f305943103cdc73590310e69f735903103e9c735903103e3f535903103e3d5359031004bc72590310063f52590310063c5159031004bc70590310063c505903103d5f7654c3110e5f7654c3103f1e6454c3103f1d6454c310055f7254c310f65e6154c3103f566154c310055c7054c3100e9e6450c310147e75988310047d75988310065d53988310147e7558831004bf745883100cbc745883103ecc32588310047f76548310047d765483116e3e64548310063d64548310055f7354831005747154831004bf7690831004bd769083115e3e65908310063d65908312671f53908310071d539083100cbf7610831004bd76108311563e65108310063d65108312571f53108310071d5310831005b571108310ed5e758c8310055d758c8310065d658c8310ed5e754c8310055d754c8310059f744c8310e59c744c8310f47f76944310147d769443112e3e64944310063d64944310055d7394431004bd76d04311263e65d04310063d65d04312471f53d04310071d53d0431004bf76504311163e65504310063d65504312271f53504310071d5350431005ac7250431227345150431005b87050431004df764c4310055f754c4310ed5c754c43100795414c4310147c75980310047f75580310147c7558031004bf745803100cbc74580310065d5358031004ef7258031004ec725803103d5f76594310ee5f76594310055f725943103e5c62594310ed5c71594310055c705943103e5f605943103d9d769903103f1e659903103f1d65990310059e72990310071f52990310071c51990310059e70990310071c509903103d9f76590310e69f765903103f1e655903103f1d65590310059c72590310071f52590310071c51590310059c70590310071c50590310ed5e75988310055d75988310065d65988310ed5e75588310059f74588310e59c745883103ecc62588310055f76548310055d76548310071f74548310071c74548310071e64548310071d64548310ed5f72548310ef4f72548310075771548310055c71548310075471548310055471548310f65e61548310055c70548310ed5e75908310055d75908310059f76908310059d76908312671e75908310071d75908312671e65908310071d65908310e59e72908312671f52908310071d52908310059d719083126e9
  | 17 => 0x55671d96310055e70d9631005d671d92310059d76992311071e75992311071d75992310071f65992310071c65992310059e72992310071f52992310071c51992310059e70992310071c50992310055f75592310f55c75592311059f76592311069f76592310071f75592310071c75592310071f65592310071c65592310059c72592310071f52592310071c51592310059c70592310071c50592310f55c75d8a311059e74d8a310059d74d8a31005d671d8a310f55e7598a310055d7598a310065f6598a31006cf6298a310055f7558a310f55c7558a310059f7458a311059c7458a310f55e7518a310055d7518a310065f6518a311059e7418a310059d7418a31005d67118a310055e7654a310055c7654a310071f7454a310071c7454a310071e6454a310071d6454a310f55f7254a310f74f7254a310074e6254a310074d6254a310055c7154a310ee5e6154a310055c7054a310f55e7590a310055d7590a310059f7690a310059d7690a3126f1e7590a310071d7590a310071f6590a3126f1c6590a3126f1f5290a310071d5290a310059d7190a3126f1c5190a310059e7090a3126f1c5090a311059f7610a310059d7610a311071e7510a311071d7510a310071f6510a3127f1c6510a311078e7210a3127f1f5210a310071d5210a310059d7110a3127f1c5110a310059e7010a3127f1c5010a310f55e76946310f55c76946310071e74946310071d74946310071e64946310071d64946310055d72946310071e42946310071c42946310f55e71946310f75671946310ee5e61946310055e70946310059d76d06311069d76d06311071e75d06311071d75d06310071f65d06312771c65d06310059e72d06312771f52d06310071d52d06310071e51d06312771c51d06310059e70d06312771c50d06310e4df76506310055f75506310f55c7550631005cf7250631005cc7250631005db7050631005d870506310059f76506310069f76506310071f755063122f1c75506310071f655063122f1c65506310078f72506310059c72506310078c72506310058c725063122f1f52506310071d52506311079771506310071e515063122f1c51506310079b70506310059c705063100798705063100598705063122f1c50506310f55e75d82310055d75d82310065f65d82311059e74d82310059d74d8231005ce72d8231005cd72d82310f55e75982310055d75982310055f75582310f55c75582310065f65582310059f74582311059c74582310f55c75182311059e74182310059d74182310147e76d95310fc7d73d95310047d72d95310047e70d95310047f75591310147c7559131104df7359131004ef7259131004ec7259131004fb7059131004f870591310147c7654d31005747154d310147c75d893100cbe74d8931004bd74d89310147e751
  | 18 => 0xb5318141006ba5318141006b95318141006395318141006b85318141006bb7218141006ba7218141006b97218141006b87218141006bb52181410063b5218141006ba5218141006b95218141006395218141006b85218141006bb3218141006ba3218141006b93218141006b8321814101ebb7118141006bb5118141006ba51181410063a5118141006b95118141006b851181410063851181410047f725973103e5c31597310047c70597310147e7598b310047d7598b310147e7558b31004bf7458b3100cbc7458b310047f7654b310047d7654b31005747154b3115e3e6590b310063d6590b311563e6510b310063d6510b31006ae6210b31006ad6210b31005b57110b310fc7d76947311263e65d07310063d65d07311163e65507310063d6550731005ac7250731287345150731005b870507310147c75983310047f75583310147c7558331004bf745833100cbc74583310063e74d96310063d74d96310065d73d96310047d72d96310067671d96310047e70d9631004bd76992310063f65992310063c65992310071f53992310047f75592310147c755923100cbf76592310063f65592310063c65592310071f53592310063f75592310063c75592310069f73592311069c73592310063f5359231004bc72592310063f52592310063c5159231004bc70592310063c50592311863e6454e310063d6454e310f55f7354e31005747154e3103f573154e310165f7654e310165c7654e310071e6454e310071d6454e310055f7254e31007577154e31007547154e3103e5e6154e310055c7054e310f55e7590e310055d7590e3100e9e6490e3100cdf7650e310147e7598a310047d7598a310065d5398a310047f7558a310147c7558a31004bf7458a3100cbc7458a310047c7654a3116e3e6454a310063d6454a310055f7354a310066e6254a310066d6254a31004bf7690a31004bd7690a310063f6590a3115e3c6590a3126f1f5390a310071d5390a3100cbf7610a31004bd7610a310063f6510a311563c6510a3127f1f5310a310071d5310a310f55e75cca310055d75cca311059e74cca310059d74cca310f55e758ca310055d758ca310065f658ca310f55e754ca310055d754ca310059f744ca311059c744ca31006ce624ca310f55e750ca310055d750ca310065f650ca310147e769463112e3e64946310063d64946310055d73946310063f65d06311263c65d06312771f53d06310071d53d06310063f65506311163c655063122f1f53506310071d5350631005ac7250631005b870506310f55e75cc6310055d75cc6310075651cc6310147e75982310047d75982310047f75582310147c7558231004bf745823100cbc74582310065d53582310f65e76d96310071e74d96310071d74d96310055d72d96310055e71d96310075671d9631
  | 19 => 0x8941006ac50189410062c50189410063f76549410053e76549410053c76549410063c76549410043c76549410053f73549410071f63549410071c63549411153f72549411172f72549410072f62549410063c62549410072c62549410062c62549410053c715494116e3f615494116f3761549410053c7054941004be76cc941004bd76cc9411153e75cc9410053d75cc941006ac62cc9411153e758c9410053d758c9410071d538c941006ac628c941005b6718c941005b5718c941004bf764c941004bc764c9411153e754c9410053d754c941006ac624c9411153e750c9410053d750c9410071d530c941006ac620c9410053e76945411263e76945411243e76945410053d73945410071f63945410071c63945410053d72945410072f62945410063c62945410072c62945410062c62945411153e719454111736719454112e3f619454112f3761945410053e70945411153e75d81410053d75d8141006ac62d81410073850d81410073a75d81410073975d81410073b65d81410073865d81410079b63d81410079863d81410073b53d81410073953d8141007ab62d8141006ba62d8141006b862d8141007a862d8141006a862d81410073b52d81410073952d814104ebb61d814104fb361d81410073a51d81410073851d81411153e75981410053d75981410063f65981410063c65981410059e73981410059d73981410069f63981410069c6398141005ae7298141005ad7298141006af6298141006ac6298141005ba70981410053f75581411153c75581410059f73581410059c7358141005af7258141005ac7258141006ac62581411153c75181410063f65181410063c65181410069f63181410069c6318141006af6218141006ac6218141006b960181410073850181410063f75181410063c75181410063f53181410063d5318141004be72181410063f52181410063d52181410063e51181410063c5118141006bb5018141006ba5018141006b950181410063c5018141006b85018141006385018141005ba7618141006ba76181410073b7518141007387518141006bb65181410073b65181410063b6518141006ba6518141006b96518141006b86518141007386518141006386518141006bb63181410079b63181410069b6318141006ba6318141006b96318141006b863181410079863181410069863181410073b5318141007395318141006bb6218141007ab6218141006ab6218141006ba6218141006b96218141006b86218141007a86218141006a862181410073b521814100739521814101ebb611814101fb361181410073a5118141007385118141006bb75181410063b7518141006ba7518141006b97518141006b87518141006387518141006bb7318141006ba7318141006b97318141006b87318141006bb53181410063
  | 20 => 0x1163e76d95410053d73d95410053d72d95411153c71d954112e3f61d954112f3761d95410053e70d95411153c75d8d410071f53d8d410071f75d8d410071c75d8d410071f65d8d410071c65d8d410071f52d8d411069f61d8d411079761d8d410071c51d8d410071c50d8d411153e7598d410053d7598d410059e7398d41005ae7298d41005ad7298d41005b57198d41005ba7098d41005b97098d410053f7558d411153c7558d41005af7258d41005ac7258d41005b77158d41005bb7058d41005b87058d411153e7518d410053d7518d410071f5318d410059e7618d410069e7618d410071e7518d410071d7518d410071f6518d410071c6518d410071f5218d410e69f6118d410e7976118d410071c5118d410071c5018d410053e7654d410053c7654d411153f7354d411171f7354d410071f6354d410071c6354d410053f7254d41007377154d410053c7154d41007347154d41005347154d411863f6154d41187376154d410053c7054d411153c75d89410072f52d89410072f75d89410072c75d89410072f65d89410072c65d89410078f63d89410078c63d89410072f53d89410072d53d89410deaf61d89410dfa761d89410072c51d89410072c50d89411153e75989410053d75989410063f65989410063c65989410059e73989410059d73989410069f63989410069c6398941005ae7298941005b57198941005ba7098941005b970989410053f75589411153c75589410059f73589410059c7358941005b77158941005bb7058941005b870589411153e75189410053d75189410063f65189410063c65189410069f63189410069c6318941006ad62189410072f52189410063e75189410063d75189410063f53189410063d53189410063f5218941006af52189410062f5218941006ae5218941006ad5218941006ac52189410063c5118941004be70189410063c5018941005ae7618941006ae76189410072e75189410072d7518941006af65189410072f65189410062f6518941006ae6518941006ad6518941006ac65189410072c65189410062c6518941006af63189410078f63189410068f6318941006ae6318941006ad6318941006ac63189410078c63189410068c63189410072f53189410072d53189410c6af61189410c7a761189410072c51189410072c5018941006af7518941006ae75189410062e7518941006ad75189410062d7518941006ac7518941006af7318941006ae7318941006ad7318941006ac7318941006af53189410062f5318941006ae5318941006ad53189410062d5318941006ac53189410c6af7118941006ad7118941006af5118941006ae5118941006ad5118941006ac51189410062c5118941006af7018941006ae7018941006ad7018941006ac7018941006af5018941006ae5018941006ad501
  | 21 => 0xc75983410063f53983410063d5398341004be72983410063f52983410063d52983410063e51983410063c519834100eba70983410063c50983411163d6454e41005747154e410147e7598a410047d7598a411163d6454a41006ae6290a4112f3741946410047f75582410147c75582410147e76d954112e3e74d95411163d74d95410047d73d95410047d72d954112e3c42d95411163d41d95410047e70d954112e3c40d95410147c75d8d410065f53d8d410065f65d8d410065c65d8d410065f75d8d410065c75d8d411069e74d8d410065f52d8d411069c42d8d410065c51d8d410065c50d8d411069c40d8d410065f6518d410065c6518d4103e5e7518d4103e5d7518d4103e9e7418d410065f5218d410e69c4218d410065c5118d410065c5018d410e69c4018d410047e7654d410047c7654d410065f6354d4103e5c6354d41005747154d411153e7590d410053d7590d4103cbc7650d410147c75d89410066f52d89410066f65d89410066c65d8941006cf63d8941006cc63d89410066f75d89410066c75d89410deae74d89410066f53d89410066d53d89410066c51d89410066c50d89410deac40d89410147e75189410047d75189410066f52189410066f65189410066c6518941006cf6318941006cc63189410066e75189410066d7518941006af74189410c6ae7418941006af54189410c6ae5418941006ad54189410c6ac54189410066f53189410066d53189410c6af4318941006ae4318941006ad43189410c6ac43189410066c51189410c6ac41189410066c50189410c6af40189410c6ac40189410047e76549410047c76549410065f63549410065c63549410066f62549410066c62549411153e75909410053d75909410063f659094115e3c65909410069f63909410069c6390941006ac6290941006ac62509411ec7e76945410065f63945410065c63945410066f62945410066c6294541006ac62905410147e75d81410047d75d81410067850d81410067b65d81410067865d8141006db63d8141006d863d8141006eb62d8141006e862d81410067a75d81410067975d814104eba74d81410067b53d81410067953d81410067b52d81410067952d8141006ba42d814104eb842d81410067a51d81410067851d81410147c75181410067850181410067b6518141006786518141006db6318141006d86318141006eb6218141006e862181410067b7518141006787518141006bb741814101eba7418141006bb541814101eba5418141006b9541814101eb854181410067b531814100679531814101ebb4318141006ba4318141006b9431814101eb843181410067b521814100679521814101ebb4218141006ba4218141006b9421814101eb842181410067a5118141006785118141006ba411814101eb841181411153e76d9541
  | 22 => 0x80320065d5358032004f77158032004f4715803228d7671d92511153d76992510053e72992511ee3e61992511273661992510053e709925112e3c645925112d3f765925112e3f76592510053c72592511163e61592511173661592510053c705925112d3e74d8e510053d74d8e510063e64d8e510063d64d8e510ed7671d8e510063e6458e510063d6458e510047f7258e510047c7058e5112d3e7418e510053d7418e510065d6318e510f5767118e510047e7690e510047d7690e5112d3e74d8a510053d74d8a510063e64d8a510063d64d8a510b57671d8a510053f7458a5112d3c7458a510063e6458a510063d6458a510055f7358a510055c7358a510063f7458a510063c7458a510047f7358a510065f7358a510045f7358a510065c7358a510047c7058a5112d3e7418a510053d7418a510bd767118a510047e7690a510047d7690a510053f7690a510063e7690a510053d7690a510063d7690a510043d7690a510063d6390a5112d3e7290a510063d6290a510053d7190a5115e3e6190a5115f366190a510053e7090a5112d3f7610a5112e3e7610a510053d7610a5112e3d7610a510043d7610a510063d6310a5115d3e7210a5112f2e7210a510063d6210a510053d7110a511ee3e6110a51157366110a510053e7010a510047e76cca510047d76cca5112d3e74cca510053d74cca510047e768ca510047d768ca510047d764ca510053f744ca5112d3c744ca510047e760ca510047d760ca5112d3e74d82510053d74d82510257671d82510063e64982510063d64982510055e73982510055d73982510063f74982510063c74982510065e73982510047d73982510065d73982510045d73982510047d72982510063e42982510063c42982510053f745825112d3c745825112d3e74182510053d74182510063e64182510063d64182510357671182511853f7654f411853d7654f411fd3f7354f411271f7354f411871e6354f411871d6354f410053f7254f410053c7154f410053c7054f410063e7598b410063d7598b410063f5398b410063d5398b4100eae7298b410063f5298b410063c5198b41004be7098b410063c5098b4116d3f7654b410063f7654b410043f7654b4116d3d7654b4116e3c7654b410053f7354b4116f1e6354b4116f1d6354b411f53f7254b411272f7254b410063e6254b410053c7154b410053c7054b4100cbe76ccb41004bd76ccb411253e75ccb410053d75ccb411253e758cb410053d758cb410071d538cb41004bf764cb4100cbc764cb411253e754cb410053d754cb411253e750cb410053d750cb410071d530cb4112d3d76947411163d76947411143d76947410053d739474112f1e639474112f1d63947410053d72947410063e62947411ed3e71947411273671947410053e70947410063f75983410063
  | 23 => 0x63c509804203e5c32597320047c715973203e5c31597320047c705973203e5f305973203e3f535933203e3d53593320063f5259332004bf71593320063c515933203e9c3159332004bc70593320063c50593320147f7654b3216e3e6454b320063d6454b320055f7354b3215e3e6590b320063d6590b321563e6510b320063d6510b320072d5210b320147c759873200cbe7498732004bd749873203ed431987320047f75587320147c75587320147c75983320047f75583320147c7558332004bf745833200cbc74583320147f76596320047c71596320047c70596320147e75d92320047d75d92320147f7654e320056f7254e3203f4f3254e3213d5f7654e320165f7654e320145f7654e320165c7654e320055f7254e320074f7254e320074c7254e3203e5e6254e320055c7154e320055c7054e321347f7654a3215e3e6590a320063d6590a320071d5390a321563e6510a320063d6510a320071d5310a320055d75cca320074d52cca320147c759863200cbe7498632004bd74986320065d53986320047f75586320147c75586320147c75982320047f75582320147c7558232004bf745823200cbc74582320065d53582320057471595320057870595320063f74595320063c745953213c7f73595320065f735953214c7f72595320066f72595320067771595320047c71595320067471595320047471595320067b70595320047c70595320067870595320047870595320147e75d91320047d75d913200cbe76d91320063e65d91320063d65d91320063e75d91320063d75d91320063f53d91320063f52d9132004bd71d91320063c51d9132004be70d91320063c50d9132004be76191320063e65191320063d65191320063f6454d321863c6454d320056f7254d3203f4c3254d320147f76549321447d76549320063f645493216e3c64549320055f7354932004be769093215e3e65909320063d6590932004be76109321563e65109320063d65109320065d658c9320147e75d85320047d75d85320067451d85320147e75185320047d751853200cbe7418532004bd74185320067451185320147e75d81320047d75d813200cbe74d8132004bd74d81320067850d81320147e75181320047d75181320067850181320047c715943203e5c31594320047c705943203d5f7654c3214e5f7654c320055f7254c3213e5e6254c3203f4e6254c320055c7154c320055c7054c3213c7f765483215e3e65908320063d65908320071d53908321563e65108320063d65108320071d53108320072d5210832004df764c8320055d754c8320074d524c8320078c424c8320147c759843200cbe7498432004bd74984320065d539843203ed431984320047f75584320147c75584320147c75980320047f75580320147c7558032004bf745803200cbc745
  | 24 => 0xd73181520063f74181520063c74181520065e73181520047d73181520065d73181520045d73181520047e71181520147f765964215e3f745964216e3c74596420047f735964215e3e42596420047c715964216e3f41596420047c705964216e3c40596420147e7558e420047f7654e420047d7654e4215d3e7590e420053d7590e4203cbf7650e421f47f7654a4216f2f4254a420147c75986420047f75586420147c7558642004df735864203cdc73586420147c75982420047f75582420147c755824215d3f765964215e3f76596420053f735964216e3e625964216f2e62596420053c71596420053c705964215d3e75d8e420053d75d8e42005ae72d8e4215d3e7598e420053d7598e4215d3e7558e4215d3e7518e420053d7518e42005ae7218e42005ba7018e42005b97018e420053f7654e420053d7654e4215d3f7354e4215f1f7354e420053f7254e421863e6254e420053c7154e420053c7054e420053f7654a421563f7654a421543f7654a420053f7354a4215d3f7254a4215f2f7254a4216e3e6254a420053c7154a420053c7054a4215d3e75d86420053d75d86420063e65d86420063d65d86420059e73d86420059d73d8642005ba70d8642005b970d864215d3c75986420deae62986420053f755864215d3c75586420063e65586420063d65586420059f73586420059c73586420063f75586420063c75586420069f73586420069c73586420063f53586420063d53586420063f52586420063d52586420063c5158642004bc70586420063c505864215d3e75186420053d751864215d3e75d82420053d75d824215d3c75982420063e65982420063d65982420063f75982420063c75982420063f53982420063d53982420063f52982420063d5298242004bd71982420063c51982420063c50982420053f755824215d3c755824215d3e75182420053d75182420063e65182420063d65182420059e73182420059d73182420065f6354d4203e5c6354d4216f2c42549420147e75d85420047d75d854203cde73d8542004dd73d85420147e75d81420047d75d81421853f7654c421853d7654c421fd3f7354c421571f7354c420053f7254c4215e3e6254c421872e6254c420053c7154c420053c7054c4216d3f765484215e3f765484215c3f76548420053f73548421f53f72548421572f725484215e3e625484216f2e62548420053c71548420053c70548420063f75584420063c75584420069f73584420069c73584420063f53584420063d53584420063f52584420063d525844200eb771584420063c5158442006bb7058442004bc7058442006b87058442004b870584420063c50584420063f75980420063c75980420063f53980420063d53980420063f52980420063d5298042004bd71980420063c519804200eba7098042
  | 25 => 0x600340010010002000400000080000000002000000000000020010000000c0010014000000c0040008006000000000000030004002000000100040000000003001c000000000000000040000000001800000240090014002000400000080000000001000400000000030004000000800200100010000003001000c000000600080030008000001c00000040050000000000400200000000008000000000100040000018002000c0021863e64d915329d5f73591531853e74d89530053d74d89530063e74d89530063d74d895314e5d73d89530047e71d89530047e70d89531455d73989530053f74589531853c745895313d5f73589530057771589530057471589530057b70589530057870589531853e74985530053d74985530fd5d73985530f65f63985530f55f73585531853e74185530053d74185530ee5f63185530063e74185530063d74185530ee5f73185530047d72185530047e70185531853e74d81530053d74d81530855d73981530053f74581531853c745815307d5f73581530056f72581530056c72581530057771581530057471581530765d73181530047d72181530047e71181530047f72596431863c42596430047c71596431863f415964303e5c31596430047c70596431863c40596430147e7598a430047d7598a430147e7558a430147c759864303ed431986430047f75586430147c755864303cdc73586430147c75982430047f75582430147c755824303f1c4354d430147e75189430047d75189430147e75d85430047d75d85430147e75d81430047d75d814316e3e64d915216d3e76d915215e3f62d915215f2f62d91520053d71d91520053e70d91522956f725915215d3e761915216e3e76191521f63f62191521572f62191520053d71191520053e70191520063f64d8d520063c64d8d520047e71d8d520047e70d8d5216d3e7498d520053d7498d520065f6398d521456d7298d520053f7458d5216d3c7458d520063f6458d520063c6458d5214d6f7258d52005777158d52005747158d520057b7058d52005787058d520065d6318d520047e7690d520047d7690d520056f7250d520056c7250d520055e73d85520055d73d855216d3e74985520053d74985520063f64985520063c64985520d56d72985520053f745855216d3c74585520055f73585520055c73585520bd6f72585520057b705855200578705855216d3e74185520053d74185520063f64185520063c64185520063e74185520063d74185520047d73185520047e701855216d3e74d81520053d74d815216d3e74981520053d74981520063f64981520063c649815206d6d72981520053f745815216d3c74581520055f73581520055c735815205d6f72581520057771581520057471581520063f64181520063c64181520055e73181520055
  | 26 => 0x280010000000000000000040050004000000c0010000000000400100000000004002000800200000000008001001000100080020000004001400000000000010001000000100040010004000000000000040000008000000000400040000010000000000000000010004000000000000000000000001000c000000400100000040000000000c0030000002001800500000020000000001c0040000000000800000000020004000000400100000020004002001400000000000008000000400100000000014003000400000000060004002000000300040020000007000c00000400000004007000000100080090010001000000000000000000000000000000000020000002000000a00000000004000000800000000010014006000000000080010000000001c0040000001000000000000020008004000c0020000000000400000000090010001000000100000030004000000000000040030004000000800400080010000001000000000000000000002000c01d000400000000000008001001c002000400000080000000003000000200040020004001000000100140000000000000c0000000000000000000040010000000000000300040000000002000000000040010008000000800000000000014001000c000000400000000030000000000000000180000000002000000000000000018000000000200000000008000000000300000000008002000000100040010014003000000200000000000002000800800040000004003000800000000000000000000000200080020000002003c0000000002000000300080020000000000c000000001a00100020004000000800000040030000003000000200000030000000001000200000050004002000c00000080000000004000000000040000004001000000100000010014001000000100140010000001000400200040010010000000000000000010000003000000000080020018000000400100140000024003000000100040020000000000000000000020004001000c00000080000000000000400200000020000000000400000040000000001000c00000080040004001000000200100000004000000000100040030000008000800000040000010003000400500040000000000000c00a0000002000400200000000014001000400100000000000000000400100000010000000000c000000000500000000000005001c00300040000018001000400100000020008005001c00500000000000001000c00000000000014003000c0010018000000000600180040008002000800b0004002000c003000800100080000004000003800600040010000000000400200080050000004000000100000000004000000c00000180000018006000c000000c000000400200000010000005000
  | 27 => 0x1000000040030000004000800900140020004000000c000001c00200040020000000001c004000800500100030008000000000100080000004001000000100080000000000001c0000000008000000100100000000001000800700000000000002000c00100080000000000000000100040000010010000000000040000000000000000200040000000000001000600000000014000000000000040010004000000000600000000000001000800600000020000001000c0000020002000400b001000000100010000004000400800000000000000000400200080010004000000400000000010014000001000100000000004003000000100000000008002000c0010000005001000000040000010001000000700040000000000000000200140000000003000000200380000000005000c00100140000020000000000100080040008000000000900080020008003001800000000000000000000800000000010000002001000100000000008000000800000080000004000000400000000030000000000000100040040000000000000e00000000010000000000000000010004000000400200040040004000000000000040040010000000000a0014000002000000080000000008000c0010000000000400200000010000002000400b000400300040010010001000000100000030000001000400400040030004000000c0000010000000000000040030000000000800600080000014000000400000080000000005002800300000080000000000400100000000018001000800400000000000001000c00600080010000000002c003000000800000000000000000c00300000010008002000c00000000040014003000800000180030000002000800100000060008003000400100000020020001002c00200040000000000000400100000000000000000000000000040000004000000000000010000000000000000000000004000000000000040000004001000000100000020004000000400000080000000002000c000000c00100200000000000000800700000010000000000000300000010000002000000000000040034000000c0000064001000400300300000004000000000400000030000002000000200040010000000002800000180040008000000c0000010000000800200080010000000000001300000000000000000000100000000000000000400200000080008000000000300080030008000000000000180000004000000000000000000000003000000500140090008001000400000000000008003000000200040000004001000c0000000001001c00400000000000002001c000001400000100000008001000000500000030000000001000000040000004000002800600000000004001000800000000060004000000800
  | 28 => 0x7ad2210073000000000008869bc600011b226b9c563060eec80585a0000000078615a2000000000011fe6d988d61a8000000000000000000000207060d80004f900004f48000000081a000000067f000017b80000c10d7c63003ca0001910000000000001460001eba000000000018bc1f71aae0d79b084741dee0000000635009084d80000000fe63a519ee0000fe45050000000000045e00004348000000000000000000000000000000053500000fd9fb200019620ab1e80000000000016bc0000000000163859a1488613127600010a80001f485c51e5805400000b11f4a516994a85d220c3ea8000768800000010a63ba98a86de1e702779af8754000000005980000b86000000056c03d845c800076280001370e845771a0c0000000000000022a04ee2ff00007ec00000000976641a1240000000000000000002e400013f000019dc00019280000e4800000004f29cc600000000001bcc0000000000000000000000000fbc495894c1a987e40000000000000076d8000000000000000005d0018813a800000000000000000000000000004b267200000000000000000000000000000cec736000000000000001fbc00006ea000061c2dd8d3e6e480000000000000144428d00000001c4200018e40000b44000000031a157825a2094157035a000227061000002180a1a00000000001ea400000000000000000000007e9d4200000000000fce000000000000000000000000000048e942800002380000000000000044a8000000000000000000000000000000012a8dea1d200000000a22000000000b85e842c122838c213c00000000000000272004635f96dc661028e5b696006cb1838789223208f8000000000000003d40000000000000000000003b500007ca000000019e421d00000000000879000037600000228e968388001000000100000000008001001c000001c00000000000000002000c00000000030018001000000000000080008001000000000080000000003004000100140040000001000000000000010000000000c00200000000000001000800400040020000000000400000200000014000000800100000000004000000c0020004000000400000080020000002000400100040010000000000000300000000000000000000200000000008002000000000000040004000000000000240000004001000000500000000000000000400100000000008000000c00100140030000000001400400000020000008000400000000000000002001800000040000000002001800000400000008000000c006001000300000020004000001800100000030000004001000000000000000004000800200040010000009000400200180000018001000000000040050018000000000f0010001001000000140060000007000000100
  | 29 => 0xbb8c0873006aa39802820000fea0a8950e00000003258a8467a0000507031487400005e98000000193e000000044000007b707ae6c28cbe2228000409989c00015080000000000000000000003678000000000041780000000000151000052680001169d7a000000086c087c3dd00000001fc015d00000aa037c000210c89321100000eb60000000000000000005f820f82bc0000aa000018e200000000001fac27e000000017ee74680000000b5846b80004440dbe09514d80000000060000000002de00000008240d080000000000154a23b20460000000000000065e051e00000000000000000000016b977400009bc6ac80000000000000144c000108400020844ba8f7a2cd0000000000026c8000000000052d00007d9a1a000001a802d8000000206c7280000000000040b80007718000119000040e0000000000000000000000000000000000000005bc800000013ae00009062d68000000211a000198a6f80a2e2ac903289b00007b283a40001f9e000035433200002988000000000059d927e000143e73c8000000062600000000000000780800000013420000000000000000000006340000000000000000000001d3800021e68778c94104965c0001aa00000f9422a8000251000067b00000000000000000049a07d21bf179800000000001752355800061d955a00021f012600000000000000000000002ea00017165199eb63d5000068899d846a800030f1792848a0aa7080836000000003186a20000000000000003101383c20000000000061b000000000005441f1a83b8a7e28e8e400531d5c02390806cf0c8e000000000000006320d2200000003f88000000067400000005cb000000000000cd800000021b600000000b893240e71c8e7a221e822580b261480000000000000000000011980002162382939666382be7fd1ff289800007ed800000011f23b900000001dfe000162c0000000000000071380000000000000001e00000000001e5a700800063691e049d1970000180421180002160a9200000000000a4c2e0844c35700000000fa062180000000bde0001d5e00017b000000000db000068c80005430c602ed00007da00003c800006cc84400000490000000005b859e4da1250308800000018f65e587c20308c9c7588ed000000000000000000000000013cc79b1c364eb0d8600000001a68b2e0000000767800068c000000011f4000000000000000000ff000000000001fd02549ee80000da025c000000000000000e9e00000000000000271859200014fc000062834e800000013be00004743f4184a5a8a0d200006306b400000000e160001c641df00000000000000141e00000000000000000000000000000001ce2000000077d09ce0000000000000000000000001fda7a580005fd8bca1bd00000001dea2b100
  | 30 => 0xa800000000000001678b80000000ce2000043a000000000013660001a0654f0d781c79a7c0000000247000000000001790ee857d000031891567441d4400000002301532818000000000001db804a0001bf80001d307ac00000e800000000256000180661800004d78b02310800000000000001f0e12213aa0000000424800000014a800006a80000000000018a00000000000000000000000007960000920000000074b170851c9b10272800000000000000be8000078a0001b7400000000000000000000015c89d679395226b700000f312083640c8a85b800000000000001f08000000000012625a6a14e863215e00000005bd0214000000042b00000dd000000000000000000673030000021a45ca8000000000021500000001f3815b00006a9066c52b000000018cc52f801a501800000000005e88e8000000000001f50000000000011ca000099287e80005df800043791a400022425c7086800000004350d980000c4453c17d673380002568000000000000009160000f8e12080003b08bfa6438000000000000000000000000000120a15e90fa0000000000122c56a11ba000000000000006491c1683084e45b7800000007e0000000030e80000000000000000082d00000000000000000037c800079d80007ce800000000004a005540000000000000000000005a7800068a800000000006dd8000377000000015a6000000000000000000000000173a000000002b000033a05ac32c80000001fd6000133e6db800000000003408000000000000019da309131823c1ab60969d880001a9e2fd0000000090288f92d61340e0411c1e3000000000e88bc021e9da605c0dc400006fa0d30000000000000002f6000206800013c8000069086b000072080000001f7a00019ba000042a00022220f180000000000000067220296ac4748a2c0da9c6000000000001cd60fc944a59880000000d5e20380001e300000000000221800060400000000000465800050f0000000000009b9b9000016cc0000524870000000000000000000000000016d09a207580000000000000000088e0c34000000000000001980000552000028780000220000159800000000000000000000000014500000000c7c000000000000003b380006071ac46e29f320001b3443590ca00000000000236000117400000000000000000186822480001288b24000000000000006bf14b264d800082e93ee000000000012f6622800000000000000000000000063100000a31672000132027600005fc0000000000049320007560d46000000000000000001c780001a0a11780005960806000000000016ea1a202061f89f2a5db8000000000000000000000000000000031e8000000215a000000000010d83a1895475b800000001bc6fb80000001504000000000005d218c80003
  | 31 => 0xd0800000000004f98000000143a0471a6a2c58000000000000013020000000000036e0000648058148c00011e86580000000000005500004de817863786b40000410620209e58700005d68000000000000018aa64b000076a80002fc8000803040a7f600006989af23068ca235095520000000000000000003c0000223a594800000000001db0000000000000000000e5800000000000001f6c3d4800046386ce2dba1080001d72090000000000004a2800005d000000000000000f4a00016a04aa8e680001312000102a0000df6000105c37f16e44ab0000000049c0000000000000087c84b420a0b9000008dc7bf1be86ee10c627e87bc0000708000000018600000000cd40001410000000000016fc27c1acc8610b6884a800000000000000000000000000000002938000000000002f8e0849700006ec1aa262c9e341c312640000a5419711d6747800000001100000000000146e000000000000000000de000000000000fc4534800000020d60000cc042895aa4c9852e0001ed44c20000000000000000004d48000000000000018b66170ac200011cc00000cc36280000001d18000037800000000001a00000093a000000000000000000000000131c05b20144d800000001ff80000a640000e4c44f89d0680800040900008581f160b5135400000000000000000000000001f67240d260000fe873f800000000000000580433079c4e500000001646000195a7cb000000013e285a95021d2a02e57694960000000456800026402b400000000000000000000000000000000000000000000015de00000007700000000000000006ec000040400006b03c305c060d045466a1ba600012a800000000000b5660a81860000000305a2126ce996a40885825500da40001f4c000000000000003dd800044904568901950000000000019406578d665480e5c0000e88149800087f00000000000000000000021705ee800000000004918000000000000000000000000000157c0000c260001e4429b191a81c9eea0001bea00000007ef80004198f6c5a2800027f984e075000041300005b49f8833f927c0000000029000070f00007cd000000014123280000000082a3f30bd60001602000173484c0000000000000000000bf0000000050c3ae13fa000000058200004bf8000000000000000000000000000000000000000000d340000000000000000000000000678000000000000002b20000000000000000000001abc00000000000000000000000015ae000000066d800000005f47448844000000000003980000000000000051e8dd263080000ef000000000000000000000000000000000000ad6301800043f000860f00002041dde000000000000000000000000000044c80000000000000159622d197c5a410f0000000000000002cb00007a30
  | 32 => 0xecc000000000000007771f1032e225a6028000000166c77b000055b800000000002ce80000000000000000027680005748000000000000000000001a4c00017fc000065400000001540b6c619050063280007ab80000001b22000000083c80000000000000161216684d844311080000000725800000002664d900001b60000633800000016484e3000086c9d360001d902f100000000000000049e8428000000025e00012f857b800007000002c194fe5571d9811a800000000004d8800080f997200000001d7000000000000001d8c3c6000000000000000000000000000000000000a180000000130800036a92d200000000000000000000061093ea000000000009e2000000030720f40001934000000000020b243f91a064600004b2800089a03e278a1186485830c0fb87c8000012e23f000e6b5000000000000000000191000000010b600009ec145800a000057800016200000000000000000000003d39dbe0000f32000000056d1dc40001d6a0000de40000000000000000000005c280000000000000000045f217800008e25e10c8c00000000001586000000000000000001c6a0000000000000000006623038f806df0c6645c0000000000006600000001f98000000000000006ba1138000000000000001ff112e50a858800000006d78000000000000000001780000000000000000006520000000143067800000000000000075600000000000a3039d800044b0f36897000027000000001a28000000000000000000000103a248000175678520ec017a1648891a361821eaa3b1800000000000000000000000055380000000efa737000037e8ab80409bda34e05da4528bec34c1d7600014e883693f821c02d2714876400019a01b280000001c9a000000000008ba142826883300000dd9f905158000000000000016ae788800069b80000000000000000047b80000000b121c8985006e80000000000000151a03d800000000007a388fa00002f40001c5e00000000000084000000000000006b900003e3000000000002061c667cc000000000000001bd4000000000000000000000199003e0000000000000000008ac5c09afa0000b1c3878000000043e00000006b380003f80000000208c0000000000000000020a677684246c582a6620800000000000000000000000000000000000000639800000006681470000000000000000000000000000000005c9f62000176637c129c39e04c847080000000000000124200002b2000000000001e40001b0060990aa000000042607cc74f000000000000000000000136a1af80002f700000000000000000000000001b08000000000000007ee279000003a80005642034774873e3f59b3000000003ca80007df11e46d6069c30f9e0a000000007180002580000329994c0000000
  | 33 => 0x43048f1a00000ce78000004df00002629b7062d177a3a494084f8000047684d43630000175a1906f61b0c00000000001cb6259979c0001c184cb9e3a42e0ede0000b4636003d261b819200022500000000000000000000000000000000000000000002b38000182800000000003be0000138000000000000000d8e0000000000000042700000000f867c00000000000054a9a7a6bd8f2432b00002aa171041f9a985218000014807c2e0090c00015128199f8a65f800000000000000000000000000017261859eb830b00007d502480001d9c481010c8518000754800000000005741b6200000000000f480000000050115e45600000be0ee2049968e69b1e1c549885c00000000000d18423879038f800000000000000000000087800019222a887c043a881c3928284000000000006d22c41bbe85000000001bfa0001f4662488306f2000000000000001c8c7391720000000053a884832182ba0000db07af80000000aca00000000000000000000000000000000000000000000000000001ed80000000000000000000005d4213a00000004538000000000083f899869780341e621d65b2800012f9a9411f847281f80000cc000000000f200000000000000000000000017a4112005800009a60000000000000000008fe00000000000000020000040f16b6000000000000006eb80000001d2663e0da67ff00000001e7e00000e0000000000000005b01f023e087e86991c2465d14760f811e200021b86fd062e6358b605c1830e06e1ec03a4220a4e000000000ef0000000031c1b2e00000000000000000000000000000000ef40001f1429c155e3ad179e5cb862a19d800000017fa0000000000000000000000001e163b9920000001be7de00000000d1000013f627100000c980008708000113800000000007a783be2a78caa7f5152e74100000000000000000000001de0001e7800002a44e3a0ce0000d9a53005c66bb9e920001c120001f2200000000001e2c0001f5e2318baa8550000604800000000fc799800068805bc00000fa29e07de23a0000000169c00000000001dba0aa90424b602ca000000009c80000000bee88b191400000000fb00001e4800000000003ed00000001966000070600004de838072066c056422f004c000000000004ca000000021c800088601820001be27f780005f0000000000007820000000143200000001dc18ec81d829a0001f7059120287291ec600010bc6ce00002620dcc09a8c8257c99445da9cac5058000000000000000000000000000146c716834000004762ada03a000000075e0000000009a7b3964a1ee800000000000001dce30c1ae600000980ed8000496066e5d78000000000000000000002026578167e00000000000000491000000005b600000002af8af02cc000038900000000000000
  | 34 => 0x122e23e1c760000a3200000000001930000000000000007ee099e41b000000000000000000284000000005384b80000225091200000001e91de00ae00da00d80001fa94d60000000059086e6ea1e268459c1c61c0b7e000200400003ce7be8000000000000000000b593e800000004d40000000160c03c1ef02798dec0000ca400000006e100005b095422f605d04439144000032e0000000000000000002040000000000039245b800048081a465b800087800002eb8aba00000007b6870e8400604466800000000006e39da400000000001dd0623800000000000000c9000005580001782000204a000024200020300000acc3cf04c600000003af8000000174e50d18ac24100006268f5e0001164321123676d1232657012214603487598000778800058d00000000e9c1b800006ab000024780003260afa0000a580001f767381ede0000000776035600000000000000000000000000000001a180f69a40131204423280006a41c2c702000012000001300000000000000000000000000165000000018f203780000001ed2000000028a80dc57980000000766000000000000000000000000060c470000079580006710f4475f80002610000000070400000003370000000095000016f684d00000000aa67f2000004d16b20000000000134e6890000000108a2d2800000000000001e042191210000000049381a665a000000018b04c2800000000000000000000194e00000000000d947220d6434180002ab80008988000165800023c80000000000000000010b0000000092a000000000000ca0000000000189600000000000000000000000000000000000000115400000003000000000000022100002bb838e55d00000000000000088c29aa08a5c6178c0000c640000000000127a000000051e06367141df80eb8000000000028214e214c9b486c100000000fc2000000000000000000000477800000000000000000000005a04c03ac69c8b046da00000000000000063e000000076a00000001b2042c8000000000000022160001b560001d3a000000000019640000000000094a00000006af8000000000000019b4000000000000000000cf40000ef61849a2684b8ab47a898ae01d01684bc00003620c74000000000019e20000ad400000006088f9e00000000e508b63979cbc00011a27f700001ea9a100001e0e000163e3b480003a821e223d83b4000000000000000001fc20001eb26c51ee03028000517000087380007e800000000000585000039e9f6e000000000012e200000000002182000000012b025c0001bbc0000000000109e5a114da0000000000000000010f8000085a00003161fc872a00000000000b32717000001597d4000000000000000001c4051880000000000000000000000007b11e2a00000000000f0e398878
  | 35 => 0x7285b000000000000000b74692899c00b000012180003709076000000000000001a5800000000001ed00008639a42000000037f80000cb0000000000082800005e800000000c20248997a11a16fe4af03322b410866708000000000000000002c28000000000000000000001a1c8748c4a0fd1e361b1a1b4000000057300000c80000000000000007384bc86581fb114800000000000ce611280004e8800083e8000506000000005aa15c0f2c00003fe00000002b78000000178019292d00001c6e00019f85b3898e0000eb271f8000866800000000008620000000030254f80000000fd45ca03123e71f4e12500005f60000000000060c00000001c3212a0fd855c000000000003e20000801800000000000001b5c000081e000000047c08d806380000001e4019e8000000000000021c822099d44b18000000000000007ac00000001bb800041c800000009cc0001556000086a0fe000000000001f500001ae11a800018fc3308f306001d804030000270800000014a446f1f7200000000000450000000000002180000000093000012f078e6a580007fe800000000005758ea400000000000000000133a3410be05a0810417d8000000000000000003dc800000008e637b86200000000000000000000000b20a426a100000000e4200016240000f46000000002b8000000199c41c085640c09ac67d000024b863c2c219e67d69c101b880000000000570038c2330000184000000000000000000000065240700002bf046e4ff1e1000014b86f480002770f381ed80000091d32000000000000ee5d80000051000048480002bc9c8a0000000000000069500000000000000000000000001ff854c00000004890ad22c6145e547000083e1664815908c1b9981e0002258660000000000005280000000000000007880001ca8000102c00015884e8000000000005d200003848fbe0c290c818082dc3a3000036d8942000000000004b800020f6000065000000000000000000174c4c30a9a00000000000ff231200000e1000026680001ef938219000008561a825f68000005103e00014cc00000000000000000000000006d60000000770800032b92605fc80000f58fde0a51cae1e80fda41495ce30a0af81bc17b24308ce003d0a0059c1b3e189128817b13883759a5082fa24e000096c000000000000003b5800000011fa1368600000000000000003589b860b40000000000000011c8454000012b80005f7984400000000000006076800000000006458e7e61c911c40480024b51e463c989961b697aa38807024500dda19c10e647a9666288007856c841e569044201d89d470a8ca836e0964000000076b8000281800000000002859bca63c0000000053a2d080000000000000000000000004e48b200001f820000000000000071c84440001dbc00
  | 36 => 0x15bc0000000000127015a9bf658600000001f18000187e0002062000000000000000000de207a00000001452000045200000005339b12000000069383fc000000000000000001436000000000000007fa0cca0001b280720000000000000000004e98000000010a3c10e588080a281e080000001a3c0001160000000000000000000000000224441a904877200002b896c6000144676b03ba52f00000000ae00000000000000000000000000000000217e00000000000d580000c5400009260000000000000033d8000000000000001c40000364000000000000000000000487800001f800072d17462830d0c7d600006e01c7000000000000b62234000003f928c428100e000003a00000005fa1d40056a1f46f080000000a36000000016307b000000003d70000000000085a0000000000000001e0000000000000000b1800005d800042e800000000000a200007e9000000016d40120c1e3dba1500000000000000000000004cf00006e314700000000582800000012ce68e800000000000000258000205e00000000b30ae8000000079280000000000000000073500002efa0de00015344339eec2f300000000000000058a1f39240000101e00016ec0001a5c1501bfe26a0000000184622b978a000182c0001dcc0c4115c00017ac16c8b3e21300007cf8000000000023800000000000000106400000000000000000034e5370000000000017c80005f080000000000000000000020b83fb8000600800000000000000e1a00005fe0598000000100600000000000000000000000005620001e4c0000000000000000000007b5886600000000002202000000034c954c00000000000000000000028f195668e1046615000088d9f9c3c18e5a3fd087e000000039c84660000000000000076c910a000000000000002348000559893088b800000014e00000000000000000000004db0000000000000007f000000000000000000000000002f20bf81f45c900006bf800024e0bfe1dd9a2c1a78b000000d0000010180000aaa00004f0000000009f80000000000000000000012a201000000000000000000000010dc3b61ad20001bf211e800083922062ac12ae1259c6866f981a2b99c921e1933638b8000602111605f800014400006689da00002104819089013314680000876317000000000000000000000026410700000000ad833f0000000000000000000000cbc35e8cba00000000001dd6000021e000000000010880000e000f71cba718800053787d6000000000000006d38f3e880000047f000000008de0000000000000000000000000000664800017f000000003707b3013a0001d2000003f0000000000000001c48fa41c99a8a00000d8000000000000000000000000000087a928e806800083a082c1358000091075225b87
  | 37 => 0xbfc000103600004ce1d78e985df1aea4c413141280000000000000000005f20b847a4000000005225f49b9a7ed00004cc00001b70000000000000000000001ef80000cde000000070b9fae0688000000000003a1234000126c389820c08a089c82397f400014043bf800000000005f28000000036225e911a1a180007af0c0485c80000001ed08839cb81d68000000000000000000001be400000000fe9e62000104400020e6400000000000000000000000000021b000000000000000000000139e80a9d284f60000000000000000000001442000000048f0420000000000007fa00000001af0d7400018e80000000000000000000000000d4e00008a071f191e70000d62dc80005c3000000000005760000000000014d98be3f28000000000087fa00e86516e812680000000000000000000016220579054193083a00000004bb1a120548000000000003e1d0e045000000006a4000022478f8b5435480004cc80000000e4e0000000000000000000004b780004a6930e000000000000000000000752800042d2132000134600000000000000000000000020fc3da0a483d31e7c0000000820000000003c2243800000000000001d2e00010745d501ae41e00003688000000000000000003ea00005b88e3a7bf92b06d08000000000000000000030000000000000004f6000000000000000001f36000000043d8000000000033b80000000000593997600000000001b5a14215ea000010e0000000000000000001ee0001996813800058d80001da21ee0000000000000074d07c4000000000000000000000183a0d400017ec5f70a52000019c00000002f3800000000002088716836089a5008038000100a27a1c0e0000000000000000015ac0001e6469120d080780007310b1408c16781a0800000000000000a76246800027b800000000a63fe89d20000c3600000000000924000000055a0000000155036a0000705000000013b2000000000000000000000000000000001940000000000000029e800000005ca3ab0148000224a6a3a20808716fa66900000000af400021a2000000000000005da00002b01fe200004140001e7400000003f493c20001de4406947c0000000000000000006f600013287750b521de000000000001d896887fb80007e880000000000000000000c12060000000000000000000002e300000000000000225e0000bf00e410ec3c4071c000022639b985859d00000001b52000000000019fa00000003480000000000000012cc0000000000000000014e6000000000000000001192000000055e80007830c8055f84fa2ee8552316800053e000058b868a5f8948410d800052b800057d80000000000894800000000003df800073f00000001c1a55d80bc000000067585c252a91c40000b5e00009e0388800002e80000
  | 38 => 0x9c00005c40000000460a14a0868e440000000000000046b00000001d48102000057e80000001ef20b8000012e800033920c06370000000097e00000000001f1e15d8000699800045d8f643720a9c01416b00001ab401c00000000000000000000000000001c0a0000000121203838d0fb00000700451a0c40000000000000000000000000418000000002d203c61d1a7808400002bd80003468000000203249ba098000055e2290b70000000039a800000000003d59e8a5838a740d2a01887100004fb000000020b0303000000000000000cce0000000000000034b00000000a120000000000000000000000000000000125a0000ada7c90fa215f80000fa000000015b600001324bd000017a8a8864000005eb800000000007e1800000000000001f9600000005b8000000000005db000000000005ad12e400018fa000000000000000000000000000000000005639b246e0907a4ed8a9451d00000000000000000015380005458000000000000000000001bc000000000000032000000069200000000000000031807b000000610f2000000000000000000000000000067180004b00974000000000000000000000000000009f21967e10000100000000000000000f604460520045800059e800032c09865ee00000000000000000058789b80000000000000038400005ea0406000033c0000646000000082480000001cde2f1801200008b80770d5a0398e6c7b900004ba219214a80000000000000162800000004d3204257e16b805e80000000f8a64980002b90000000000016e80007c48000213883200014f22c3000000000000000000000125e000000037500000000d8400006221ee00005279e500000000000035851a948a000170400000008499a601f600000001a1400000000001af0000006c0000000000000000000000000f703fe00002ca00000000000000147e0000000628853082711c600000000001d9a00000000000000572000000000005ed8b365320f5a5cd8000000000000000000000000660800000000000000000074848a11800000000000561000016fa1200000000000000000005a60000b8a0000106000190c00000000000de852d80000000000000000000000000001e125c69c4a0000b9826801b61a00000000005c1e51ca644d800000000000000000000026c000016a000000032219aa4c100000d1000000000000001654000000000000000000000000000044e80000000000000000000000000000000000190800019ac2850000019000009480000000000000000000000006058ea847503b8008037288c0dd04b10fec0000000605000000002760000000822103a5f38a8a6bd16d609400a20000d70000000000000008670d600000cb60000000000146400000000d700000001c980001
  | 39 => 0x15280000000503000040500002608000000000000000004100000000000000000005a3207a0c88c524e7000004d8736000000010b97be5c01d0072f96866df8c4e5451f7442413841fd06ba85e80000000000000000085480000ad806813d00007011d6c000000000019f02ec000000000000000000000000065b06c01ce85c850001ac5841d2a1c403a62ec81ce84e118a000189000003600218000000000000015548100c7886780002ef085014a16560000000000000024d000083a93785fe0000000000044a1aa809d00007d7000062e80005fa800037e0b4c6e500005261d8676e000000018d200000003ac1cd2233979a3ee0b8e7f1a00838b123e60f8f62000137000007da000167c416986200005127d00000000000086282e600000000000000000000009e9a8008207146ed9a0e00007804b983080001c06000000000010be000211857a000000004e822996d87a106f235a8a9602a8abc6120c582c9800000001420000000000000000011be47e029e23a8a400a0134a000118c0001b4400000007d802ec36d06b23e400006ea8a50000000069a00002ed84fc3eb8000000210e00000000000000000000000000005bc00000000e0c00000002911fea29599947b0824e33199046d9001c34f000000000000000000000085e711052c2fa96be65500000d99560000000000000002d0000071e80000001986000000000000002f2000000000001e8800054b0000000056e87600000000000000000046d8000019a204000000000980000001ee235b0000315962a00000005d8864e10c9cfa4a092b200000006a7199a40a000000020dc00000000000be2000000000000007878c5000000006a481f088d000001110ee000000030c8d1e000000000000008750000000038607f1e68000000000000940001a9a00000008730df400019f20000840000000036480000000e82000095e1231a88860125427a8e7c0001e326b08d2e4c000002810000098000034a1e9852404388131aba72708da02a0000000068c5dc07425f8138a0231ba00000000000000000000d238a80000000000000000025384ec20500004a619120000000000000000017e411e09b600000006630000000042864c800074300000000000518163081219ce6d29f645cf00003511e9432480001d300002da8000141811e77998a44d2015800013b82a1961614d1f924ee93ce3c5119c26f8972015000000001561cb054200019ea0aba0520588000000166e000174a0000aea00000000000000000000000000000001cf0441019020980220001338547a0a240100001619a8613c9aaa06810c0000000000000000000000000000000000000c6937265480000000b5c00021283358000251800000000000d400000a800004ae00000000000000000000000000000000
  | 40 => 0x400016a83ee800000000006e600000000000621140a6260b9205f0f00551000000000000000e2800014d05091cf86700000377800017789ba000000005700000000d4845a81b00001fa829980001030000000000000000e40000000797800060380000000f1e0000000000000000000006d500000000000000159400018325dc8000808883c6b88ffc7328a8e4f680000000f6a4480000000000000017cc0000b2a000121800013161f417421c61cec7f300000001b6033e88c236f1fd26868d16887000000011b0000000041609282ce00000001ec800000000000000000000058f019e00020ac5750000492800081500000000000000221e78680000000000000158000000002081bdc353169800000004180a46000208200000000000e1c300a0744549454000000000008346b1800000000004d0000000000b800000000000000000000038500000001a0800000000000000000154600000000000c6e24d92a454e135c66b94580000fdc6f3800089a99880001c580000ec8000000000000007729ef63100000000061e00000000001f8c24c80006b0043c54d800048880000000000000014e000000000000004e180000000000000211c74218e0084800000000000000000628000057f0e182d380004641180000000031f800000013341d40568000000000000000fa800027d0000200800000000000001b18116169400000002bf800030515ca5a98000000158c4738962000207800000000001c300000200000000000014222a300000000f5870780007610000000000000007a83a9800000000002109c26018000004b00001798f9a1468a7c04a8000000000000006c4000000068f80000000000438000000000004bb8000000000000021da6748f220001f0a00013b4000177600015c456e80006d01f20000094800000003c5800061a80000000b0e00017d04ad800000000007fc0f404c6800007a98c65f99d4e29710500c90728391800000000000000000000000000000000001d680000000000088e000178643d000077e893c1dd0ee04340000000000000004a4000000088f20c8687981800000000000000000129209c000064f00006f7800000005480000c5e00000007e5022e4418f7c000000070f800000000000f98000000148200008000001fe00001cc2000000056680003b000c829c800004f190220495643fd80000001680000000000009a447600000bc0000347137e0000000000000034d800047b00001959bb20001e8600017307c1000033c1b0e0000000000000042500000001db000000000000000000000048e000015f05b01851fe419080000001142000188c0001e38742800000000006b280006c9800000018f40001fce00001122d40ccc00000000000000000000061580008951cd0000000082680000188000000
  | 41 => 0x6829813882160b6000023200c07ee800041b80006e9143800018a60000a8200000001d18fb600000002c782c20000000000141a54180000001eac4f40000163800063b8cf852c0a680cd156c408093e0000dc64e413747f9814a0000c7218d02b0871891000006d40001a34250113c00000000000bf6000206a1c680000000ffe00004221770b644838000000000000000007a980000001f560001e4800000000e021bc745800000000000000000000022c0000000000000000013f40d19ab05d7037a00000003118bc20001cf663f985e0001b72134800052380007da8000000000000000003310000000000000000000001b9c000000000011220000000000000000000001818000000000067415e400000000000ba838d80000929ad81da945067280000000666000000000000001fd87c60000000000000077f0000000091800012900001bba0c780000000000227a0f01d10eba2311f8e0000cd24db8000667800081f01ca00000005898f0a000000044d000038080007331d4c000000000000004f78ebc0000000000029c001226e4a580000000000283800064e0808000000026a8000000000084b150a60b800000000000ec8a020001c800000dca64a8e3c0001a5829b8000000000037390824679b6a00000000001bb400000000000f2887715580001e0641a1d960000000000000000000006bb182000000000000c2e07600001ab00000000000483000000000000b39c3a39d000085f000000021a666e14a20000c6a000000014394ca4451bd60000cea1e68000000000035297945e3800069c06cc00000002d98000000000000000006d30278000000000000006b587340f114a600000b000000007bd074e00000002de9c7419f107c00000000000000000000073200004478000531213e000000000000000001df20001de800021be0f7800000000000000bd020300006250bac0000000000191c0e68b7c12980002260804000050400010e400000000f90262571953011b0f7881400006ca800059a820e66985a20001788000000011f0000000000048a8000000010000007ca694800000012ba5f1912679c80002570ea236b9e7a00014ba68b9a0418690da0000000000144e27c80000001e5c00000006b68dac00000001e9a0b62b7000000000005ef088879a8bda48800006640000000000000021427c99f7e53d807263a81f80000000000000000012c227f00000000000000000016100008168000000186600000000df8c9e14096c400000001968aac69d00008558e56394189e0000b9e56780004c792860001b060e08c2a0000a3e5b2000000000000000000000000056816960468852118884a3b700001559c5408f00001bfa22a15180000001b6c2bb000086613061d80000000202c000000052700000881e4206a8a5a5120d1
  | 42 => 0xe60b01642000000000000000000000000121a158153a0000e063e1090a4f001b40001d748478000000069808a80000808000000000000000004999e6e000000020b95b80001aa67a694207948000000045c00000000e2917e1058eaa2f980000000000000000069f839e593000000013980000000000200a000000000000000000000000000053b9d644129632000077a00007f80001d1c000000000400000001f2e00000003cb82340001888000000000000000001b7a5bb800017897fe10c0ba65cf8000342800047d9492000000000021ae000000000000000000000000000000000000000000020a1f67e987320a28d68891800000000000000000000000086a00006779b9600008b018b000000001fe0000a5e000000000000000000bf8000123000000000001eee39980000000000239041a00000000001bd02929b88000000034900000001e3c58100004be8000438800070880003e48000000009e000000000000003f20000736840200000005c488be36c9c9e7ff8000000000000000000000000000000024b00000001ce80000000000097800018d858e800000000000ce80000000000000000000000000000000616800080400000001cea000072e0000000000054a35400005ce1df63ec86d05b980000000000000000070a00004408000000000000000004c88c766cd833e0a5800000000000bb8000000137616400000f200006e892520002114000000000000002f48b2200021f82a900000000b7800000005c88000000000000000004a78000000000000000000c700000000a38000000000000000001ab875800003bf0e528319278000000000002461a116d043a00000000000000000000011940000000000000016a00004448042000000049a80003c71a16167000000006e800000000000000000215c0001f06000156273d00000ec000000a0c9a17e800003b1f425d612726481faa6c715000000000703000000016f8000000053e80000000000000165a000000060a000087280000002148000000000021120001c4800000000000000000000000000001d6000022c80000000c6c00000000001b50000000000000000000000000000000006ae000000000006de000000000013bc399105619f80000000c4c000012471308246a300003c480000000e700001caa00000000000d2a4138000000000069d80000000000425906200015e200000007fb0cd80000d9c000174400012941a38000000000078800008008a987b9983a79822263ab97323d08000000000052000000631010000000000014f40000000000000000000000000000000000013992be0000d82000000000000000000000000063a000000038e10080000000000000000000000000000000000000019bc00000004ff80006f9800000000000001c8644c00003a
  | 43 => 0x5184f8000000000f000000000000000000899100267d80008171598000000000011e60000d96000000023d00000000000000000049205a404803a80000000816000000000000001d8e3b68e32426971e000000000000000000000000192e00020ae00000000000000282916c240121c1738000000000000000007418000000000000012c800000000001d940002086242000050b8000000000025f000000001e25308e544ea2166000000025592842870cd0000000000000000000724000000000000000000bb840580000000000695843406693440001d7c00000001a5000000000e2000000054600a06eb000008c9c944f70f6600012da00000008049e820000fa600016a4000000000013d60000000000000077c00000000000711a0bc000000000000000001f9a00007e662e226675500000000000000000000001b280d9a5a1c28c106b791680e20b88000000088a14263bc80006f100003b100006c7828619a952400000000000000000000000000000000000000000000000000000000000000072887304cb18780000b486662096888000000000000da0a2674084926e780000000000000000000015ec336800000000003cd0000000000081b8eca12c0d7200013b0000019600011b4000164026c0000000135622000000001bec35d800073992dc000004e69195c2748995800000000000000000000035b99462560b960001ff600016ba36e8000000000026d1162035006e000000052511b800000005608000567118447700000000000000000000008ee0000000000000000000921ad800070e117a00000003e580000001cee000000000000007c300000000000000096a0000cb400000004e68000000000030e00000000b9a00015722a400000ca92a060300005f10000156942c0258000745000008e993a71b098c27d90a44f18b9c000103400001e62f91d820420fac53197b42f50994000000000000004620f3a3c08000000000000000005e400000000000000000000014e4000000072c800000008167a800000a4000016e0000109990a000000000000003501b4600000000ea80004f51692000201c00021aa00000000001f1c00001d061f0000088800056280000000000000000000011a6597800000000004d6000000006e4000000087b16601979ac82e89d3e67f869242b80004ca83062cf000000000008850000000114c0000a240001ea8000000000000000000a60000000012d800000000000be800000005d414f2106000000000000000000d540000000000000082a2186000000000000003a3961a000000076480004ad187a0002102609140e0828000000000075c0000000000000000000000000000000013f9d248958e8a14f8f5004fa0ca000135a0001bf000002e8000000000016aa1cf00002c69f5200021761e78d
  | 44 => 0x1f3c0000000000000000000002e500000000000000000000000003e607404bf00000000ac6485000000014ec00000002288000000000000000000000000564800000000000000ba400a800000000000000000000000003405d84a99d562188ba086e800000000000001f440000000000176400000000001c3400007543f1a14c000011865082924e901c25941e9c0000d0e66c877e72100006c0800000015fe00006f8000000072c0000000000020e13f200000000000000000000000000000f400001239b1a000000004a000000000000000000000044600010c4756800000003283701778000000079500002350000000000082906c800000007f10cf27e0000018e007a173091434481f2000170e55a922658195f00000fc00000000000000001a800017c13c41ec800051000000000000383800085100000000352459800000000000ce01840b680002601fca0000000000000000000000000000000000056f80000000000000000000000008091ae07
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xa8e82d903184001c28a3b20630811385995410c610005c24128218c200099587d903184001c2ccbb206308002e1a0b640c610005c9406c818c200099587190318400172500320630800295e19520c6100054b4308418c2000a2e82d92508400134904b88810800217e0d72d95100050ec1ea5b222000a1d8314364440010bd0fa96c68800217a1c50d8d100042ec3ea431a200085d87140634400149b07a96c4880029360c75d891000526c18a1b122000a4d83d48624400149b073a8c488002a9604741891000526c18a031220018b4865c44244001928c6b88848800329189711091000654314e1a0a20008ae861c9414400185eca39282880030b194725051000647b18e4a0a2000c8c631c9414403115d0fb1282880622b21c62505100061db28e0a0a2000c38651c14144001936c638282880032618c705051000655b10e0a0a2000ca8621c141440010bf06b96ca080028760c659901000516c10cb320200083e87d95640400107d0e32ac8080028760c655901000516c10cab20200083e87d49640400143b07a92c8080020fa1c51590100061dba8e0b202000c38751c1640400143b06282c8080021b6087654c100142e43ac6a982000c35641c553040010bb063b2a4080020f21d64548100143643ac4a902000c69621c1520400107b0fb2c84080022e61a709081001c5c402ec210200083d87d94420404907f0eb24a2080020f61f65d04100041f43ecaa082000c2f651c94104001858ca392820800385145640c4102270a32a821882000b848250431040018aaeca986208003155d9750c410005a9406ca1882000b90805d03104001c28cab20620800295219520c410005a8402a41882000b9280908310400152b0c2106208003545d5700c410195c8422e01882000bc0825c0310400115d05bb4800800e2ea0376900100061c282ec20020009a4825c440040abe20a018880080030e5da501001000698b8ca02002000f10319404004001870cabb080080030ee1576100100061c42aec2002000c3b535d84004001876a4bb080080030e14576100100061cbb6ca2002000b3281d944004001872eca988008002cc20553100100061cbb2a42002000b308154840040131770cb8880080026a20971100100061cbb4a22002000d31719444004001932ed188800815ae4a063110010006c8b8c622002000c99760c44004001e24a21888008157c41443110010004d8c38622002055f13530c44004001e22a618880080cb64a1c3110010006c8c38622002000d91760c440040abe250a1888008003c4614311001000789b28622002055f10650c44004001b24e41888008157c4d48311001000788a90622002000b9283c844004065b24e818e40080cb641d031080102a6d03a0421002032d90740c61004001ac0e52822008003581ca5144010
  | 1 => 0xae7396c8100020f61f52d90200050ec1ea5b20400083d871476408001932e7386c8100028760c50d90200041ec3cca320400083f87594640800186ccab88c8100030d59571190200054ac08c9318400085d87d4a63080010bb0e284c61000227a1f6458c200044f438c8b184000a9581191630800149b053aac610002952057558c200052c402eab184000c4d751c963080010bb0fa92c610003151c45158c200042ec38a0b184000874815d9530800189ac7b92a6100021e6187054c200041f43ec8a904000a2e82d91520807d07f0eb2c84100032658e70908200041fc3aca2104000c4d7654c320800169100a9864100035254d700c820004f040ae0190400083d87d92510800107f0eb2e82100022761e63d04200044fc3ac7a08400083c87595410800113d0f31a82100022721d635042000617328e4a084000c2d651c9410800191cc639282100032358c725042000652394c2a084000c3a651c14108001872ca38282100032698c70504200064cb18e0a084000cb2611c1410800113b0fb24621000295205650c4200044ec3ec81884000c2d659ca400800191ac73948010003521407348020006b0280e29004000da0719012008001ac6a438a40100036890871480200042ec1ee4b2e2000a1d8399664c400143b0732ac9880028760f52593100050ec18a0b26200285e87d8d53c400149d05b1aa7880021760f7654b1000516412c8a9620009b0805c442c400185cca39283880030b59472507100061d328e0a0e2000c39651c141c400135104b8881880021760f72596100061732ce5b242000c2d659cb648400185ceb396c9080030b5d672d92100064739ce5b242000c8d739cb648400185d0b396c9080030b61672d921000617a9ce5b24200083d87d4b648400143b07a96c9080030b9cb52d92100041ec38a3b242000c2e721476484001874eb386c9080030e5d670d92100064d39ce1b242000c99739c36484001954e5386c9080032a5ca70d92100050ec18a1b242000c2e72143648400107b0f328c9080020fe1d651921000547416c931c200085d87d4a63840010bb0e284c70800227a1f6458e1000547416c8b1c200089e87191638400149b053aac70800295a067558e100042ec3ea4b1c200085d87141638400145d05b22a7080030dd907154e100062ab18e2a9c200083e87d91528400145d05b22a5080031598c7154a100041fc3acb214200083f87594428400107b0fb24a3080028ba0b64946100041fc3acba0c200089d8798f418400113f0eb1e83080f60f21d65506101044f43cc6a0c201c89c8758d418400185cca39283080030b594725061000647318e4a0c2000c8d631c94184001874ca38283080030e59470506100064d318e0a0c2000c99631c1418400113b0fb246308002a3a0b648c6100044ec3ec818c2000
  | 2 => 0xc751853000552412e830a6000a568754c614c0014a90ea98c298003859d153185300070aba2a630a6000a578254c614c0014a900a98c2980029560f52185300070aa9c8430a6000ab280908614c001c2aa6210c2980029561732185300052ac2a6430a6000a5583140614c0494390ca9e8298003079d953d053000706a98c5a0a6000e1553187414c00115d053b2829808a8721953505300060e3b2a6a0a6000b148154d414c00115d0c39282980030bd94725053000616328e4a0a6000d0d531c9414c00115d0fb1282980022b21c625053000706a98c4a0a6000ca472d85414c001c2aa630a8298003291c861505300061db28e0a0a6000c38651c1414c001a32a638282980032ad88705053000654310e0a0a6000cb3611c1414c001960c2382829800256a03758c53000627ba8c518a6000c5775186314c03b0b90cba86298003135d4620c53009d0e432a72026000c1e7654e404c001c1aa631480980038554c61901300950e432a62026000c1e7654c404c00163100a9880980038354c62101300070aa98c2202600285e86dd6304c00189eea314609800315dd4618c1300142ec1ee4b286000874815d9520c0010bb0db9aa4180022b209749843000617328e4a086000c2d651c9410c001874ca38282180030e59470504300042fc32e72806000c4d651c9300c0018aaca38a60180028760e65993200050ec1ccab264000a1d83d4964c800143b06282c99000a17a1f6354f200052b40ec6a9e4000d29529c042c80010bf06bb4a3900030b994725072000616b28e4a0e4000c3a651c141c8001872ca382839015f1a5ca70d96200050ec18cb3244000a2d82196648800107d0fb2ac9100020fa1c65592200050ec18cab24400083e87d49648800143b07a92c9100020fa1c51592200050ec18a0b244000876819d953880050b90eb1aa7100aa0f21d6454a200041ec3ecb214400083d87d9442880010bb073b4a3100020fe1d64946200041ec3ecba0c400083e87d95418800185eca39283100030b19472506200061db28e0a0c4000c38651c141880014ad03b2863100030bd9672902200050ec1ea5b224000a1d8314364480010bd0fa96c69000217a1c50d8d200042ec3ea431a4000a4d8214463480010bb0e280c6900031618c705492015516432a42124000e0c63548424800165100a9084900029560f52d85200052ac18a1b0a4000a658214461480014cb043a8c2900029560f521852000539406a430a4000a70805486148001c4aa4210c2900029560c50185200c456410eca0a4000c2f651c94148001858ca392829000323d8c725052000646318e4a0a4000ca472d854148001948e430a82900030ed9470505200061c328e0a0a4000c9b631c14148001930c638282900032cd84705052000658308e0a0a4000c2d759cb640800191
  | 3 => 0xa18c8000a95819883190001c1cc4a906320002c5205520c64000617bacc510c8000c2d75988219000123f06b94a12000217e0d72d954000617b28e4a0a8000c2c651c94150001948e5b0a82a00030ed9470505400061c328e0a0a8000a1d839d6621005b07b0fa94c4200028760f52988400041ec38a33108000a2d82146621000143b06284c4200fa0fa1e62548400048ec18e0a90801291f8754e321000126902baa64200024e201754c8400068ca9ae019080009b0815c0321000146902a9ac2200030bdd47258440006163a8e4b088000c8f731c96110001918e6392c2200030ba14725844000616c28e4b088000c2f531c9611000185aa6392c2200632960472584400041f43ea4b088000a1d83d496110001858e5a92c2200020f21d525844000616392a4b08802583e871456110001858e428ac2200030edd470584400061c3a8e0b088000c9b731c16110001930e6382c2200032adc8705844000654390e0b088000a1d831416110001858e4282c22000247e0d72944400041ec3cc5288803d83f87586511000145904b0ca2200024760e70944400060ebb2a71888000c1d76dd6311000162d03bac622007227e1d618c44000546412c31888000c1d7654c311000183aecba86220002c5205520c4401044fc3ac21888000a8c825843110001c28a2b086220002a9209618844000658b08e0908800091f835ca501000145904b0ca0200028760f52593300050ec18a0b266000a2c8259152cc0012b306382a59800255205754cb30004ac402ea9966000a548154e61cc00183aeca9e83980022b20976507300060fbb2a6a0e6000b148154d41cc00185cca39283980030b594725073000686a98e4a0e6000c3a651c141cc001872ca38283980034654c70507300042ec3eca1946000a3681d95418c00185eca39283180030b19472506300061db28e0a0c6000c38651c1418c0014ad03b2c63180028760f52d91300060e3b6c8a9a6000c1c76191534c0010bd0db92a6980029360f52d893000526c18ebb126000a4d83143624c00149f04a98c4980029360f521893000707b22a63126000e0c6454c624c00149b073a8c4980029a201531893000527c3aa63126000e0f7454c624c001c18e8a98c49800293205531893000725c02a63126000a4c8054c624c001c9100a98c4980029360c511893000526c18a0312602ba1c8654e424c001c1aa631484980034654e709093000654314e1212602aa1c8654c424c001c1aa63108498003135d462cc930004aa40aea9926000958805d5324c00189aea31264980039154c62d853000553416e9b0a6000a5583d4b614c0014ab06286c2980022b20974185300ec2e43aa630a6000a548154c614c0014ab06288c29800385d9153185300070a322a630a6000e4553d88614c001c8aa6310c2980029560
  | 4 => 0x484014b307a96c09080e2ee1d41d81210055441283b024200a598314060484014d304280c0908029660c751812100534c10ea3024200ab1811d060484014d305a98c0908029660f52181210053940ea43024200a7081548604840155505a08c090802aa209411812100748a0862302420085d831c1650840143b0732cc8108028760e65590210050ec1ea4b204200a1d8314164084050bd0fb1aa6108021d6187154c210061ab20e2a984200c57631c5530840185ea4bb084108030b5d9521082100692a92e221042009b0805c4420840185d0abb084108030b615761082100617a9aec2104200c2c515d8420840185aeca988410802c920553108210dc57c32e221042009a8805c4420840125b0e214a2108028b618429442100592c08852884200c2e651c9410840185aca39282108030e99470504210061cb28e0a084200a8d8610a310840170b02214621090295205650c4210070a28ac81884200a8d8610831084b3e08a2210621080217e1d6318e500060fba6e6b14a000c1c74dcd62940010bd03b9ac52800287e0d6290a5000517c12c6214a000a1f83588429400127100b88852804a4e20174986502c51c402e930ca00083d8790a619400107b0e214c3280028d60442986500041fc3ac5a0ca000a1f8358b419400185eec39283280030b1d8725065000687b98e4a0ca000d0c731c9419400185d0c39283280030b618725065000616b18e4a0ca000c2e601c94194001a54c039283280020f21d62506500050fc1ac4a0ca000c2c725894194001858e530a83280034a1cb70506500061dbb0e0a0ca000d1b731c14194001a30e638283280034adc8705065000694390e0a0ca000c39631c14194001872c438283280030e984705065000436c16ed18ca000a4d82dda31940014ad03bb463280021721d628c650005864128318ca000b188050631940010bf0eb106328002c5604420c6500048ec3e8218ca00091f87504319400161904a08632800385985410c6500058c4028218ca00093a80dd321940010bb07bb4432800217e0d760865000496c388410ca000c2d7598a429000143b073acc5200028b60b5398a400050ec1ea5314800083d87146629000145b0428cc5200028760c5098a4000516c10a13148000a2e87989529000185d0f312a5200030bdce6254a4000617310e2a94800091d831c1529000185cc4382a52004e47e1d538ca4000616bacc51948000e0d5398a329000126902baa65200024e201754ca4000616bacc4994800083e87d49619000143b07a92c3200020f21d52586400050ec18a0b0c8000a2e829da519000123f06b94a3200020f61e62946400048ec1ce128c80008ae829da319000183aeca9c6320002a3a0a768c6400060ebb6eb18c8000b1681dd63190001c1cc4a946320003075d9530c6400060ebb2e
  | 5 => 0x880346dd470504310068c3a8e0a086200d8b721c1410c401b10e4382821895b64dc4705043100788288e0a086200d1b851c1410c401a310a38282188034699470504310068cb28e0a086200d1b521c1410c401a32a4382821895b64e047050431006c9308e0a086200d93511c1410c401a34a23828218803461447050431006c8288e0a086200d10511c1410c43b0b90eb2ac01880296201655803100626b28e4b00620085d831c165c8401874cb386c9908030e59670d9321006173ace5b264200c2d759cb64c840191ce7396c990803235ce72d93210041ec3ea5b264200a1d83d4b64c840107b0e28ec9908030e9d670d93210061cbace1b264200c9a739c364c8401932e7386c9908032a9ca70d93210061dc2ce1b264200c38859c364c8401876a7386c9908030ed4a70d93210061c28ce1b264200caa725c364c840143b06286c9908030e9c050d93210041ec3cca326420083f8759464c840153501b24c7908021761f5298f210042ec38a131e420089e87d9163c840153501b22c79080227a1c6458f2100526c14eab1e420085d87d4963c84010bb0e282c7908028ea036454f210061bb20e2a9e4200c55631c553c840107d0fb22a5908028ea036454b211f41fc3acb216420083f8759442c840192cc6b8885908026c2017110b210041ec3ec928e4200a3a80d9251c840107f0eb2e83908022761e63d07210044fc3ac7a0e423d83c8759541c844113d0f31a83908722721d635072100617328e4a0e4200c2d651c941c840191cc639283908032358c72507210061d328e0a0e4200c39651c141c8401934c638283908032658c70507210044ec3ec918e4200a9a80d9231c840113b0fb20639080385147640c7210054d406c818e420085d839c3658840143b0632cc9108020fa1f65592210041f438cab244200a1d83195648840107d0fa92c9108028760f52592210041f438a2b244200a1d8314164884010f5013b2a71080a1721d6354e211541e43ac8a94420083d87d96428840107b0fb2885108024b61f6510a210059340eca21442009a8805c4428844907f0eb24a3108024b61c42946210041ec3ecba0c420083e87d95418840185eca39283108030b19472506210061db28e0a0c4200c38651c1418840170b02210631091385195410c621005c24128218c4200b908050431884010bb07386ca908028760f52d91210050ec18a1b224200a4d82d4f634840149b043aec69080217a1f52d8d210042f438a1b1a420085d87d4863484010bb0e280c6908031518c715492100617b28e4a0a4200c2c651c9414840191ec639282908032318c72505210045d430e0a0a4200c3b651c14148401870ca382829080326d8c70505210064c318e0a0a421ca94865043148489c28caa086290802e4201410c5210052cc18a1b024200a59839d76
  | 6 => 0x43c402eca906200a2c82591520c401a2ea6b8884188034554d7110831004d8402e2210621d85f87596320c4012b100baa641880307d4d76d04310060ebb2a7a086200c1f53dd9410c48946902b2a821880307dd9535043100617328e4a086200c2d651c9410c401a1ea639282188034354c725043100692288e4a086200c3a651c1410c401872ca382821880346d4c70504310068ca98e0a086200d30511c1410c489a28eaa0a6218802e4201414c4310052c402a6b006200c4d531c9600c40143b0da94c8188028761850990310050ec36a4b206200a1d86141640c4012a902bacc41887617e1d6598831004ac402eca906200b0c82591520c401a2ee838aa418803451d07154831004aac30e2a906200d16841c5520c401a2b0838aa4188034599071548310068ab20e2a906200956801c5520c4010bb0c382a4188025520575908310058a40aeb210625b91f8754a420c40162902a94841892e47e1d52108310058a40aa4210622089f865c4420c401a28a2b888418802662017110831004cbc32e22106220c97865c4420c401a2f0ab8884188034521571108310068b32ae22106200d15655c4420c401a2ea4b888418803455497110831006c9c02e22106200994805c4420c401b2100b8884188026420171108310068a282e22106249a5481596610c44113f0cba4c2188034514574984310e44fc3ac93086200d14755d2610c4012a90ea94c2188026561c42984312268b38ae9288620085f865ca510c40123b0f214a2188024761c42944310058ac0885288621ec5576986510c4010bb0d384a2188030799576d04310060f42aeda086200c1d855db410c40183ea4bb682188030714576d04310060e282eda086200c1d76597410c40123f0ea968218803075d952d04310058a40aa5a08624791d87947410c40183aed28e8218803511447250431006a8288e0a086200c1e65dd9410c401a28a3bb28218803071d776504310070a28eeca086200c1f85dd9410c4018390bbb2821880307d4b76504310060e28eeca086200c1c50dd9410c40183eedbaa821880307dd965504312258a40acaa086200c8f76dc9410c401e08a3b92821880343d4872504310068a288e4a086200c8f761c9410c401a1eea3928218803431d4725043100782288e4a086200d0e851c9410c401a1b0a392821880343994725043100686b28e4a086200d85811c9410c401b0ea23928218803431447250431006c2288e4a086200d04511c9410c401a18a039282188024721d52504310060fbb2a4a086200d0c72549410c40162902a928218912c52166150431006c2394c2a08625a91e87945410c40183eed28a8218803431ca51504312258b40ca2a086200c9b76dc1410c401b10e5b828218803c414770504310068a288e0a086200d18501c1410c401936ec382821
  | 7 => 0x3983944605040147305288c0a0802a6e0d51181410054c41aa23028200a3a87144605040147306288c0a08028e608511814100719408a23028200ca6625c442cc40136100b8885988030b994725073100616b28e4a0e6200d24511c941cc401874ca38283988030e594705073100698288e0a0e6200c35749c7658c40145b0432cc9188020fa1f65592310041f438cab246200a2d82195648c40107d0fa92c9188028760f52592310041f438a2b246200a1d83141648c40186ac838aa7188020f21d6454a310143643ac4a9462008ba80dda428c40107b0fb2c85188020f61f6510a31004ac402ea9946200c4d75989328c44907f0eb24a3188020f61f65d06310041f43ecaa0c6200c2f651c9418c401858ca392831880343d4c725063100686a98e4a0c6200c3b651c1418c401870ca382831880346d4c70506310068ca98e0a0c6200d16749c7658c401a2ae938ecb1880345a1271d96310068ac24e3b2c6200b1681d96648c40161b0432cc918802c5a0465992310048ec3ea53246200a1e86d4a648c40123b0e28cc91880287a1850992310048f43ecab246200b1681d95648c40123d0e32ac918802c360865592310058b408cab24620091e87d49648c40143d0da92c91880247a1c51592310050f430a0b246200a5681d96628c4012ad033b2a51880256a027654a31004ab408eca94620091e87991528c4012390eb22a518803139da6254a310f4a643ac4a94620085e861c1528c40133501bb485188024761f6590a310058b40ecb214625f91f8754a428c40123b0fb288518802c5a076510a312f48fc3aa4214621c89f865c4428c40133100b8885189764761e64946312e48fc3ac928c621e85c865ca518c40123b0f214a3188024761c42946310060e32aeda0c620091d87d97418c40183aedb2e8318802c5a0765d06310048fc3aa5a0c625d91d87947418c401838cbbb28318803071d776506310060fbb6eaa0c620091e87d95418c40183eedb2a8318802c5a07655063100647bb6e4a0c6200d0f521c9418c40191eec392831880343dd47250631006863a8e4a0c6200d0e851c9418c401a1b0a392831880343d94725063100686328e4a0c6200d0c511c9418c401a18a039283188024721d525063100686392a4a0c625c91e87945418c401a18e528a831880326ddb7050631006c4396e0a0c6200d18501c1418c401936ec382831880346dd470506310068c3a8e0a0c6200d8b721c1418c401b10e4382831880346e1470506310068c428e0a0c6200d1b651c1418c401a30ca382831880346d4870506310068ca90e0a0c6200d1a511c1418c401a30a2382831887a1761f65d82310052d406cbb046200c4f659cb608c40185eca39282988030b19472505310061db28e0a0a6200c38651c1414c40143b07a92c8188028760c50590310
  | 8 => 0x2a98c0a08038ad9762181410071432ec43028200e8b63d886050401d10c7b10c0a08038ae1762181410071442ec43028200e2b75d886050401c50ebb10c0a08038ad4f621814100714a9ec43028200a3a8598860504014730b310c0a0802a6a0e62181410054cc1cc43028200aaa8298860504011770eb10c0a08028ee1562181410051c42ac43028200a9b83588605040153106b10c0a0802ace0562181410051d428c43028200a398518860504015550c310c0a08032a9d8621814100715b28c43028200e28651886050401d16c6310c0a0803a218c62181412a751b08c43028200e2a851886050401c530a310c0a08038add46218141007143a8c43028200e2b531886050401c52a6310c0a08028ea1b52181410051c436a43028200b1983d486050401c36c7a90c0a08038618f521814100715b16a43028200e2862d4860504014750ca90c0a08028e21952181410070db1aa43028200e18635486050401c56c4a90c0a08038a18952181410051d434a23028200e1b639446050401c30c7288c0a08038ad8a511814100714314a23028200a3a861446050401c36c6288c0a08038618c511814100715b10a23028200e2862144605040147307ba8c0a08028e60b75181410054d418ea3028200a99831d460504018750e3a8c0a080386a0c75181410051cc18ea3028200e19831d46050401433063a8c0a08028e60875181410051d408ea3028200a3a859cc60504014730b398c0a08028ee1573181410051c42ae63028200aab825cc605040155104b98c0a0802ace0573181410051d428e63028200a39851cc60504014750fa98c0a08028e21f53181410051cc16a63028200a3a81d4c6050401c36a7298c0a0802ace0553181410055840aa63028200a3a8754c60504014710ea98c0a080386e0d53181410070d39aa63028200e197354c605040147704a98c0a08038ce0553181410051c40aa63028200e308154c605040146102a98c0a08028ea1672181410051cc2ce43028200a3b855c860504014710ab90c0a0802a6e0d72181410054c41ae43028200ab3815c860504014750a390c0a08028e61472181410054d418e43028200a99831c8605040756302390c0a0802a6a0f52181410054cc1ea43028200a3a87d4860504014710fa90c0a080386a0f52181410051cc1ea43028200e1983d48605040143307a90c0a08028ea0752181410051d43aa43028200a3887548605040147706a90c0a08038ae0952181410051c40aa43028200a3a85cc860504014730b990c0a08028ea1632181410051cc2c643028200e19538c8605040156503190c0a0802ac60632181410051d42a643028200a39854c860504014750a190c0a08028e61432181410070ca98643028200a9a83d44605040153307a88c0a08038cd4651181410051d43ca23028200a
  | 9 => 0x63945410060f3b0c728a820091f835ca515040185cedb14a2a08020f61c629454100616b90c528a8200c2e7618a5150401c1ec6314a2a08038318c629454100616c38c528a8200c2d7318a5150401c4ce2314a2a08024760e709454100616314e128a8200c2e7518b605040185aea316c0a0802c660c50d814100714310a1b028200b19839d7605040166102a9ec0a08038ad9462d814100714328c5b028200e8b6318b6050401d10c6316c0a08038aa1462d814100714c28c5b028200e2a7518b6050401c52ea316c0a08038ad4c62d814100714a98c5b028200a3a86d4b605040163307a96c0a08038a18b52d81410051c432a5b028200e286254b60504014750d28ec0a08038a18a51d81410051d430a3b028200e2862147605040185ecb394c0a08030b196729814100647b1ce53028200c8c639ca605040185cea314c0a08030b5d4629814100647398c53028200c8d7318a605040115d0e312c0a08030bdd46258141006163a8c4b028200c8f731896050401918e6312c0a08030b1d462181410051dc2ac03028200a3885580605040153706b00c0a0802a620d601814100555c12c03028200aa882580605040163306280c0a080386d8c50181410070c318a03028200e2b621406050401c50c4280c0a08028ea0375181410050ec18ea3028200a3a801d4605040147501a98c0a08028d20553181410051c402a6302820083e87d48605040143b07a90c0a08028ea0352181410041e43aa43028200a3880548605040107d0f288c0a08028ea0251181410041f438a23028200a3a80144605040143b06280c0a0802a6a0c50181410054cc18a03028200e1a83140605040147306280c0a08038660c50181410050cc18a03028200a398214060504014750b3b0c0a08028e61676181410051d430ea3028200b19831d4605040147307b28c0a08028e60b65181410051d42cca3028200a9a83994605040153307328c0a0802aaa0a651814100554c14ca3028200a9b83594605040153106b28c0a0802aae09651814100554412ca3028200a3a86194605040147306328c0a08028e60865181410070db2ec63028200e1865d8c6050401c370bb18c0a08038621763181410070dbaec63028200e1875d8c60504014750b318c0a08028e61663181410054d41cc63028200aaa8298c605040155305318c0a08028ee1563181410051c42ac63028200aab8258c605040155104b18c0a0802ace0563181410051d428c63028200a398518c60504015350c318c0a080386d9463181410070c328c63028232e936118c6050401c350a318c0a08038661463181410070dba8c63028200e187518c60504014750da98c0a08028e21b53181410070db1ea63028200e1863d4c60504014750ca98c0a08028e21953181410070db1aa63028200e186354c6050401661
  | 10 => 0x3128200aaa8098c625040155301318c4a08028be1563189410051642ac63128200aab8058c625040155100b18c4a08028ba14631894100516c28c63128200a8e8618c6250401c1eca318c4a080383194631894100707428c63128200e0d8518c6250401c1cea318c4a0803835d4631894100517436a63128200a2c86d4c6250401c1ec7a98c4a08038318f531894100517432a63128200a2c8654c6250401c1ec6a98c4a08038318d53189410059240aa63128200a2e861446250401c1ec6288c4a08038318c511894100517430a03128200b0d831406250401c1ec6280c4a08038318c50189410054741cea3128200a8d839d46250401c1d073a8c4a08028b60e751894100706c1cea3128200a0d839d4625040145d033a8c4a08028ba02751894100617c3aea3128200a2f835d4625040145900ba8c4a08028ba17731894100516c2ee63128218aa581dcc625040145d0b398c4a08028b616731894100517428e63128200a2d851cc625040145f0fa98c4a08028b61f53189410051740ea63128200a2e80d4c6250401c1ea7298c4a0802a9e0553189410055240aa63128200a2f8754c625040145b0ea98c4a080383e0d531894100707b9aa63128200e0c7354c6250401c4f02a98c4a08028b20553189410071240aa63128200a248154c625040145900a98c4a08028be1571189410051642ae23128200a8f835c4625040151906b88c4a0802aae01711894100554402e23128200a8e83d44625040151b07a88c4a0802a3e0d51189410054641aa23128200a2d87144625040145b06288c4a08028ba0051189410051742ee03128200a2d85dc0625040145f0ab80c4a08028b215701894100547c1ae03128200a8c835c0625040154f02b80c4a08028ba14701894100516c28e03128200a8e831c0625040151b06380c4a0862a9604701894100547418a03128200a8d83140625040145f0e280c4a08028b61c501894100707418a03128200a2d831406250401c1b06280c4a08028360c501894100517408a03128200a3a80dd9525040107d0d3b2a4a08030bdc8765494100617c10eca92820083e801d95250401838edb1aa4a0803071d86354941006163b6c4a928200c2e761895250401858ec312a4a080383d8c625494100706318c4a928200a2e87189525040185d0e312a4a08030bdcc625494100616310e2a92820091d831c15250401858c4382a4a08022e20176cc941006173a8c59928200c2d7518b325044523f0ea9c64a0802c5205538c941006173a8c51928200c2d7518a3250401c1aa631464a08034554e718c94100652314e319282008ba80dd932504010790cbaa64a08024d205754c9410049c402ea9928200c2e75189325040185aea31264a0802c5205530c941006173a8c41928200c2d751883250401c1aa631064a0803079db
  | 11 => 0xd044923f0ea9c65a08020fe19754cb410049a40aea9968200938805d532d040123f06b94a3a08020f61e629474100616b94c528e820091d839c251d047147501bacc1a08028760c759834100516c10eb3068215a3a801d660d040107d0fa94c1a08028760f52983410051d406a5306820083c8754a60d040185ce4a94c1a08028e20152983410041f43ca33068200a3a8094660d040107d0e28cc1a08028ea0051983410050ec18a1306820085f835cb65504010bb07386caa080217a1f52d8d410042f438a1b1a820085d87d4863504010bb0e280c6a080315d8c7154d4100526c1ea5b128200a4d831d7625040149b06286c4a08029360f521894100526c1cea3128200a2e85dd0625040145b0bba0c4a08029920553189410051742c863128200a2d8590c625040149b06280c4a08030b9d4629094100616ba8c52128200a598314360504014b3073aec0a08029660f52d81410052cc18a03028200a59831d460504014e102a98c0a08028ea1643181410051cc2c863028200a5983d4860504014750b210c0a08028e61642181410048fc1ae5b2a820091d839c3655040143d0c3aec6a080247a1f52d8d410050f436a5b1a8200a1e86147635040123d0e286c6a08024761f5218d410050f436a431a8200a1e86144635040123b0e280c6a0803071db6354d410041f436e4a9a8247d17731c5535040126d0c38aa6a08030da187154d4123e8bc18e2a9a8200d17631c55350401a28c638aa6a0802c360f52d894100517430ebb128200b0d831d7625040164902a9ec4a08028ba1851d894100586c18a1b128200c3b659c26250401870cb384c4a080326d8e70989410064c31ce1312822283d87d94625040145b05b28c4a08028b608651894100517c2ac43128200a2c85588625040151f06b10c4a0802a320d621894100555c02c43128200aa880588625040161b07a90c4a080383d8f52189410070631ea43128200a1d839d4625040145b05a98c4a08028be0953189410051a40aa63128200a1d83d48625040151d07a90c4a0802a360f521894100516c3ea43128200c2d87d486250401c1d07a90c4a08028b60f521894100706c1ea43128200a0d83d48625040145d01a90c4a08020f61c511894100516c10a23128200a1d83140625040145b04280c4a0802c360e751894100516c3eca3128200a2d83d94625040145d01b28c4a08028ba1665189410054741cca3128200a8d83994625040155501328c4a0802aa602651894100547c1aca3128200a8c83594625040155700b28c4a0802aa201651894100517430ca3128200a2f87194625040145b06328c4a08028ba00651894100707b2ec63128200e0c65d8c6250401c1f0bb18c4a0803832176318941007073aec63128200e0d75d8c625040145d0b318c4a08028b61663189410054741cc6
  | 12 => 0x28e20152982420041f438a33048400a1d83142609080107b0c38aa6210024b6087054c420048ec18e0a908400a2d82d4d611080146d03a9ac2210028d20553584420050ec1ea4b088400a3681d49611080146902a92c2210960fa1c51584420061dba8e0b088400c38751c16110801936e6382c221003261cc70584420061dc28e0b088400c38851c16110801876a6382c2210030e54c70584420061da90e0b088400c39521c1611080796302382c2210030e14470584420050ec18a0b088400a2d82141611080146d02282c2210030e1c050584421c51d406eb3008400a1d831d6601082b475003acc0210028b60b53980420041f43ea53008400a1d83d4a601080147501a94c0210020f21d52980420051c402a5300840083e87146601080143b06284c0210028b60850980420050ec1ea4b266400a1d8314164cc85545f0ca908599002176187054e3215d0fc32a7214642aa1f8654c428c80186ee838aca990030d1d071595320062bb98e2b2a6400c36841c5654c80186b0838aca9900315e0c71595320063838ee0b2a6400c3b741c1654c801870e8382ca9900316dcc705953200635b90e0b2a6400c73711c1654c8018e0e2382ca990030ee1070595320061c420e0b2a6400c59831c1654c80146902b2ec8990028e20165d91320041ec3ea5b226400a1d83d4b644c80107b0e28ec8990028760c50d91320041ec3cca3226400a1d83994644c80145b05328c8990020fe1d65191320051a40aca3226400a3880594644c85507d0fb22a4990020fe1d65909320051a40acb2126400a3880596424c80107f0eb2884990028d20565109320051c402ca2126400a5481596324c8014b100b2c64990029660c50d8132004a6c10e2a98640085f865d5320c8012a902baa641900256201754c83200627bb2a49906400d0d75109320c80117100ba4c2190029520553984320062aa98e2b006444c3671593639440145d05322c5288960f21d6458a510060f326e6b14a200c1d64dcd629440183ee9b9ac528803071d37358a510ec2f40ee6b14a20083d879da429440107900bb4852880287e0d6290a510041e402ec214a200a2f8258c429440143f06b1085288f60fe197110a510049c402e2214a20083d86dd1329440183cc8b9cc1288030759173982510ecaa40ae7304a200a2e82dd2609440147501ba4c1288028ea0074982510060fba2e7304a200c1c745ce60944c14a902b9cc12880307e1173982510060e422e7304a200c57815ce60944018a902b9cc1288020fa1e42982510060eb9c85304a20083e8710a609440183ae6214c1288030b5c842982510041ec36e4a9e8200a1d839d662d045b07b0fa94c5a08028760f5298b410041ec38a33168200a2d8214662d040143b06284c5a08020fa037654b411f41f43cc4a96820091d831c152
  | 13 => 0x902500000300400000f00101700500400100100b00001400300600701000200201300400100001500400500000a03a00100702800d00300000001900500400000a00800000801d05f07200a00d00600200600600b00000b00000601c00200b00000200200800000300502d00001200900300e00200d00300000300600300000a00000c00000200500101f00000600300500800000300400000200702000b01200300103801100200303d00101701d00b00f01600000101900100b00303e00003600200301d00000000600000000600500300300206700300400000902b00000500601e00000000900000000f00000400000f00100300000201100b00d02000500201e00000400400000000600600400000901100000000100800400001d03200001f00400000200100300300b00200000800204e00100500500701000200b00500000d01401500000900002900800300207202300300001c00a00b00202601901000e01501600200500800300500f03600000400500100000601a00000000900000000000300100202100200300600e00003800100100406f00c00101e00100000100b00100000000700102600300e00001800000000000000000104700a00000100001100001300f00001a00602900100301300100300001800500000200100000300300100200002600000301200400000100000001100100000300000100200500501800100100100200000000e00000100000901400802f00100700001200400500200900000200e00100100301c00400d00400201100300400100a00000100000100000402c00200000600500100100200100000200300200000600300000300000400002b00300300900400400103801300f00300103200000000f01700a00800500b0150060eb9ce9b12a600c1d735d36254c010f100b90c2a98021d20572181530049c402e2322a400c37641c56354801868c838ac6a90030ed907058d520061c320e0b1aa40085f8758c63548014a902b18c6a9002962016318d5216c1ec3ec830aa400c1f645cc6054801838c8b98c0a90025520573181520051d406e8302a400a3a801d060548010e902b98c0a900307dd173181520060e3a2e6302a400a54815cc605480183f08b98c0a900307211731815200627c12e6302a400c4c825cc60548018af02b98c0a90021720573181520062a40ae6302a400854815cc60548010bb06382cb210021d2057654e420048ec18e0b2c8400934815d9539080107b0c38aa7210024760c7054a420061d32ce1b0c8400c39659c3619080146d0332ac3210ae0f21d65586420050ec1ea4b0c8400a3681d49619080146902a92c3210028760c50586420051d406eb3048400a1d831d66090801475003acc1210020fa1f52982420050ec1ea53048400a3a80d4a60908010790ea94c121
  | 14 => 0xc028cd9a9eead6386e4e90429a40a52848abe2aea7ba98e66a1ba924ae867c50656678ca942ea2b656eb9a5fc13c674976b4e6aa1380a4834bf8b7ce024b65eab2e14e1fa3d2bf037cd646dea6cdfe94cb9e53035eb6cb8657223eba6026942c866140c8508722da6bb60009a853c29c04255e6669ba5320349644f23a288401422a1083280006eca10000260714bfc1ac08821c87426a0f80001c04f4000a509d674a2e46d01a20008945c48580000005dea54304ba435261215a236000938000460000800c94574000000000c1cd4276cc6a8ee00091a1c671295e6ee50e07e33e0003bc0007189bed2a8cc1ea8b80925e8b229485be7ce00079c000d88252500ae498a804de60aea6600079688a818000816000de03cc000000000a3ea7c4e604e826070000000de8e6e2ce34c00010ae483e2000cdc0006b00000185ac978d4cdea466000000d9601cc347ee8fe4581406b80bec8ab4079a0e040041280a4eed0e4a8000be0a72b327ea0000ce88800003600000024a710000cc85c228a4c800047a19e2dc6481164e29cebf257a2e818c0003d6dbe57e0d607600038a05a3dc3846f056c5f2dfa9c899cd66536ab8b7e0001b84fe00064242c000780c10000106d1c12661c790bd8ad207a0004aac50000d2e67a0001940ba3c2cfc8d6000000a1ab1053a5981ce912afc00000062808c3aa2da0005a8764bace4600039870457800009e000000000c0a3eca125a216400063600019a32e4de000ca0000000000000c6e42024662c0522d4240310494000000a4c5dc000000d249628da6da000b5a71e000028988a8ae1e00011870c9b4c64abc4b8c0e3ea2d60007984e447400043c48e770000de22683d080e2b4e560000000003140d4a0800069c900e0031e2ee0daaa085251a8f8ce802e86e820000b70000bbe0fe5f070036cc9034857c9347f262e68e00098c1be17417cb6e6fe3660006268ba55c9e45765b272e1307fc2dee669cc00000092c6920000a6ddcbe6074c0464442680cca429ece0870e40c20120772e6400101600f00301400200600b00402300a02700100d01204800400100100700000000100500b00200800100100003d00100900000d00d00500603b00000a00004100e03b00101c00100201f00100000300100000800900300000100300a00600700c01200800100900100000400004200104100a02900a00100400e00c01a00000f00002000000400000000800100100000100e00b00000300001e00200000101100000100000900100100300500500000401100100300f00300400300000401600800a00700700600a00100100000000600202b02e00200400a02000400800100000300702800400100900200300100000400800200000000001300c00700500200700902900f00f09700200001d00000605b000005004
  | 15 => 0x62fc284baacc69b2a806f63f483259027e498186c56e78ab0ab6ab25242708821e24d81ca1809a41a6b1c3ce17640875825ad860006229ac0a88c21cc49e000bc0e32000680a02478344892e620c4958a5e81eb62320dca62005c7c676075edd241c84c00092600092a000d44dce00074e000aecb36cf60005aa00038c4a2122ad0b26000000d16000000000d48cf23f02d2bbc0000000ccda06763b200045eb5c3c666004c160b3e544a32dd02f00dc9e07e8000000000000000b4684450a230a8c6900009aa0002c000000076291e000000000d58066d344644d63e611cc1a53459e0fa5e42e27d2276e6a202330b580006f249a0005d25381de000d047becea9505d0750d320008722facc21c893a1b6dee2140006a4332600a9261a0004e800000000000097a09a70e000ac8e760004f8000d3c7e090e000ae2000aac1840003a487c5fe542686d2c16e5fa2889f075a00a000604d9408e000c4c000afa0000000006ac51ca9c000cb4000dc206a70a0006c2b8c7d800000000000000000034e0000000008f67d40006bc4143b4000000e6c000994010a00a344b400000063a45a5e2b1203cbae0009f811a000df0b1400061821e2326e6358664000c7497e000902a26418cc0a161f0512bb2af8de4ae0792c5a470996ccc7ccc4e0f003030032439e15e43488ea04000360a82bfe6301a45bcd6ec7cb2a380178b4c20c2f4b885a00082cc30268aaa2784956b48d9210c000a7474c3403567ecd1254c6d41e6a5c0725b0000a22d8a0008be438ba22ba52691c7866aed463a67b8e7cc78090154d367ae7bc94406260ec3044abd444255645c258d0cd9081ca186a68ae22206c4da5e02a8e2c7a6e0e896000bba0f6da89c00008e2b6a318aaab7416c4cccba0004f0b304ea00088cd541f87d68f2000292670378d100e26c6d2637e82c6ba5b46a255a2b043a56030e8fc0007a2b9c0000000ac8680009e6000c7208667ea68ad8a78c7a0c2cb294e1d444c1dc00064ecae2b8d30aae0b20226fc1d65ae1484809a6d565eea0e9fabfa000552898d18296136aee58c000d7c5f6ce4e440b6d4a0d0a64bb06782d0db89167368f4428af0264b2011e6b619099ac8e56a1029289de6e212ad5c15c63c0001a01ec52e000432000094a2414ad3e6101448ca04a9bc9661c44306a84a6000000b2c9dc5a48d4bda0007a800000000045200023ce1625622c9fe0f4392cfa2249a2d8031264c4d04c4c422fe2e0000196e5227c1242ae3ba0602345ec00027a5d4e3a2c431acda8220000005c8d0a36ab0c694a14c80bb87de8b20001322aa30c28e0000001d23549f20000004caa2a76a0d865887e0002d800000002a000000454a9a000be800093c0007c8c36206906e4c2e6dd85163e4b7aa5a5c6080e06a7ea569c2c826bee74b54b1e48cd6c754b90a
  | 16 => 0x182cec5820005620006e8000a982a0c58000000b68350920000a4a84a1885044507323a8bf40007b6a28dec7fa1500005864fc876da280202cc700004a416a4906ce000000bde0008109c68c800032c580adeb44990970ad40fc212cace5a634bf6bc8570d5083e7aca628d00008b6000a46b8a3220006e412871a77c56886c9100008c423800004041a000aa44d2dcc000000056000828000d5a8a64829f6da4000210c40472000000850000ace9d000e0002f6000000000c220008c6000c54000d8e688000000dbc734a3c0000000007740e47e4168000b76000c7e4dc654192b1a34a0c6c2ec16204782152b280000000002a60000009300460000001b2000a1ea9e6b2c06000a3aac60008c09fc60829401e9d222e280c8444e1420003d451425c0001eea48602c76d385c0cb8c3843edc800000076e6b492e33a06497cb9295c218448d06000cd0abe7feb384623b6854100a44c66000d284b2bd0e7221a8fa35a1709a01586460008641e0000cbed8232ad8c2ca000000000d3a20e000b640009c49149404d452ce10df60000003160004f6dc00580003080000001f4bd2000d707e200046e1e8c48000814000cfeba06a01feb84e0a3fe7560681b0daa1fc7f6b80228d20a3885ebdc476936606bc68122f80de46a364278b2420a5a69ea0b84e06723728b0b3a2269f48b4954702c4a146cf4b5ec127942c6e2ee7e836c88db28f0d083ac0c0c3218a0f2726b08ba8866162e5455896e0ec502b1866242e368286e384a0b346dc1aed60984db08a8216db4a588465ba59c78ec5c446ac47c4a900009d4b52982012000c020000003885102669926d878800003e00000083a0003f6bd6c3a0966c065c1c2862424cc43ca25400082edf20003740506d2b4a00054aa7a95a290ac27c0cb03a00ca61e00050cc263e0746c46000000848e5e82a5b6b067288bc00041e554020caa46ce2ae70250000e12682d98af40aa4b0b72000c9e1a83ae00094aaba2000007b4744dde73a000c3c518ae6000638c6840c342000e34e087aa8a4640000af6b986fa000dc60006525d83d84ac024c9c96800056435cbc27ca9b6748220000208bcc9aeada5cabb4d62e60cbcbe472caf2840b78a60d9c00055024400018ee58000110d226f4a2000000054696a2f2bee406e28172592000000000dd4b563eecf036ed1aa301d8376d783f8d00ce217e6324ba73cceea0630a3c04bc1bc49c5b8a6a00080677eb503fc60ce306ea63e306000c983c8e500008e42bc8de6c47201120d283c87815666e084650044282cd41f28d823a522c1869e5943902a4bce3b8c2ad6adba51e65e33c38e65a24824e0a29e8444e4a038d74cf895289079e7789d8706b94880b664cedc4a4ec2496cb16b00aca24c13475c0987b2d7a5f40b0b02a6e37a436000ca66845e600008a32
  | 17 => 0xa7684e5961e46e00000009b80000000ea922d14000986000b967303964c0b0eb8e00090a000b04b0a000a1c0008248aa696a2c64a6243bea8eaccc6052a000d7600099e0ee000a8627217a000c3e00000060acd84c609c0008dc00c7b0e248602422bee1405e000886002e1c370a2ec008086682a2000c28000000e3cd7272a000000ce6742b8293ecdee181d0382776b3c2b2df4db6404d68dac19c93212e12c000aa6032000752cd658a6f8a0c8e6afe422adc000456000000ca21dae04c446988ea842cca14cbeae367667a069aaa825e7f0b60830d9e54071c416e20d4ed1e26ec6cc1ee3e62a488ab4e262aca70e4236285ca404ec0b4d84c14e7a9604c25d67f80483c413e07c298c929809747a49980e63386163da53ee1a1147087f407854ed5226278a2c21b4dfc3dec52520a9613aa52104006ddad7e72448468c06e9726c87389180bc03a3f24aebca01ae5c3469ec4925847c2274dae0e83e83947da3340a0486656d027689e201642aa42ca8716856d5e3367dcc5ee22bc47408ec19810e9caa844fabec46816686a89acd28385da8e0496d40000c083b0df80002c858e4be9b08d2000000000a3600081a41087a8ac000e0c0000008e80004408a26cc0001f6000000c0c3fa0000046d6b425ccdd690ca0a000000000c625ce0000827e689c26c54847ca88402000000cb6e6873e000000588c8c9da40e39c94659a5f88ce90885ac2c89e1aa66c39a054c9a77a8a06ca47e2ec000ccec960007d031c000
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x40140d9319472506210050664c651c1418840138090604420c62100681194825043188401a1065201410c621006841948050431484012149160f52590210048524583141640840140d93d49761082100648548805c4420840140d93a1576108210044965c8154c4208401825762055310821004c82418110a510840140d9399472504210050664e651c1410840138090604428c4210068114586108310840123090604429865000503e4d861c9419400121691e0d625065000603e0c72589419400141b935887050650004c4241811083194001a0482985410c6500068498480504319400140d93a1e6254a4000445245831c1529000180d839887054a4000509245759893290001428905d6624ca40006819888154831900011149160c70548400064454c815c0321000140d93a14725844000509245531c961100012149160f52584400060360c72d4961100012149160c50584400060360c72141611000181576a07758c4400068120851584311000181776205535073000541245531c941cc0015109154c705073000509a47651c9418c00143291d9470506300070254c629c2424c001444915d4624c9300060521d7454c614c001604925d153185300068454e80908614c001250906153218530006051d88154d414c00140c9654c725053000541245531c9414c00180c8754c62505300058124553189414c0892149854c61505300070154c72185414c0015109154c70505300070254c621c1414c001c1153184705053000512a437518a314c00145290dd4618c5300058224153188404c0016109054c61101300050364e651c941c80014199399470507200050364c651c9418800141993194705062000492241821446348001a0863201521092000498241821d4614800162090548421852000511245751c96308001448905d47258c200041524587d49630800194153205700c82000452660501cd20080015419314071480200055064f521c5200800140d9399472507100050664e651c141c400140d93a1672d92100048524583d4b648400180d839cb52d92100048524583143648400180d839c850d921000509a4b641c55384001a0682147640c61000681994825043184001a0665a0b640c6100068499680d9031840012149160f52590100040b660651c9410400140d9319472504100068119482504310400141597195640c4100058164865590310400105597219520c410194a424186108310400194175209700c4100050664c505d84004001520925c650100100050664c655d840040014299219576100100050664c855d8400400141993d4976100100060c5d88154c4004001520925c651100102b464e61718c44004001580925c6311001000704145760c440040019118754c311001000704195760c44004001911876143110010
  | 1 => 0x10048625983d4860504013109160f521814100486e6363d4860504012199818f52181410068260f62d486050401a098318b521814100486e4d82dd460504012909160c75181410048c245831d460504016109160c751814100684e45831d460504012189160c751814100684245831d460504012109160c7518141005822497354c6050401a1383205531814100684e4c8154c6050401a12732055318141006845cc8154c605040121993a167218141004a424583d4860504012199321f52181410048c24583d4860504016109160f521814100684e4583d4860504012189160f52181410068424583d4860504012109160f52181410048664c8754860504016109154e32181410068454e818c860504010389761532181410048c245854c860504016109154c32181410048664e87944605040121b9360a511814100628988805c442cc401448905d6624ca310040b660651c9418c40142992194705063100485a4686d49648c40121691a18505923100511a4676989528c40144a909da6254a3100503648655db418c40140d92197765063100503a5a851c9418c40150691d94725063100443660651c9418c40150691194725063100503a58501c9418c40141a96214705063100544a47651c1418c40150992194705063100544a44651c1418c40141a96d48705063100512a43659cb608c40150592d4d711083100644d4c805c4420c4019115320171108310054464c511c1410c40191075201414c43100512241531c9600c40150492590715483100644144805c4420c4015059299571108310050565b525c4420c40191385201711083100644214805c4420c40191395201711083100644254805c4420c40191265201711083100644594805c4420c40191352201711083100644548805c4420c40141596141711083100541648505c4420c40191080141711083100541648755d2610c4013109060442944310050364a855db410c40101d98d4976d043100407a6352dd9410c40181481dd965504310050365b521c9410c4011159814472504310050365a851c9410c40150495604725043100560241811c9410c40150598144725043100541658511c9410c40150690144725043100503658501c9410c4019047220552504310064121472985410c401d0072147705043100544a40511c1410c40141996140705043100544a5c511c1410c401d03721447050431007401c8511c1410c4014199621470504310050665b521c1410c40151091548705043100544a60511c1410c40151396144705043100544658511c1410c40151192144705043100512241651c9600c4012149160f52d93210050664c859c364c840141993d4a70d9321004852458314364c8401819839c050d93210050ca43641c553c8401892632017110b210068414680d9031c8
  | 2 => 0x80143291d4c70584420050c245531c1611080141993d4870584420050ca47521c1611080143091548705844200485245831416110801819831c050584420060a608701416110801832811c050584420050c241841c5654c8014509160c705953200452241821c5530c801504915d4424c8320054224175109320c88981481591739825100503a4b745ce609440181481dd1739825100605e10815ce609440101f9660c7054b4100445245831c152d040101f9660e709474100491245839d462504012449160c501894100494245831d460504012509160f5218141004c1245831d762504013049160c50d894100483e4d82d94625040120d9818f52189410048524583d4862504016049160f521894100681e4583d486250401a049160f52189410048524583140625040120c9660e7518941004c1245839d4625040120d93a0365189410048364f87194625040120e989d76318941004836627518c6250401a076320553189410068118c8154c625040120c9660c5018941004c124583140625040120f98d8c5018941004836606314062504012849160e751894100489245839d462504016049160e751894100681e45839d4625040120c9160e751894100681245839d462504012049160e75189410048364c805d462504012289061d531894100681e0c8154c6250401a0793205531894100681dcc8154c6250401a047320553189410048364e85dc062504012849160c50189410048364f8714062504012249160c501894100581245831406250401a079160c501894100483245831406250401a049160c50189410048124583140625040140d93a1c625494100407259831c152504011149160c70549410060360c621c152504016049154c628c9410070154c629c63250401424915d4624c9410050a2417518932504016049154c620c94122445a47835ca515040140f935c8629454100503e4d8718a515040101c9660e70945410060360c629c2515040140d939d462d81410068260c6214360504013109160e75d81410058264e8518b6050401609939d462d8141005882455318b60504013109160f52d81410068260c62d4b605040140d931d4621814100486660631406050401a0983d8850181410068260c62140605040121993a0375181410048524583d4860504012199320152181410048664e8094460504012149160c501814100584245831406050401a139160c50181410068424583140605040121993a167618141004c4245831d4605040121b9360b651814100486a6075d8c6050401219981d4631814100684d8c8154c6050401a106320553181410058264c85d886050401609931d762181410058824553d88605040121993a1462181410058264e851886050401609931d46218141005882455318860504012199321b521814
  | 3 => 0xfc5280055d462bc660002f0550140c0c0011e584790396f38cac11d220101042cb8028c7440323f800420a45c800000000012c034125c42a000da3e0811e16844ce400000448003b4000d05646468508000016d3354c5584500000000004252e381050a15b000004700018c9b3b8081e920580d9459580006125d3c294252589d050512b45a1381c128002d9323a8db4cc7f1211550d6a1c13a3c90d3549553c372f4ba4fd550e95016400000bc46c7e0f4000015c0a4004100005c4b19c223bd623cc3c2b88e000002649f51c000001e000820000059125000df00000234d30011d3d07459ca20c00024c91000002a8410008600000504003251f16c004b40048400000005ac0017906598003a00f000e71000022c00304cf375185b01852c2d21c05174b2090060d8d200149000f03380029c520046e5b800000003e80000053314e20b8001940057c6945d0c36000000000f931160921192708c00551232cc002407b080001310e578d03184d43c1f2109e000000007600000000eb5140000159000005c000251240000041cc83e4e61a8001b000358bf4980028000000070003b23d63000c2384771acff28cb00002b2dd0213d393313d18071298001bd3502d303d4e91507c20c851c8003dca142948008cb3d8fd40152300190588a37049344b5574ec5a4004d88c00c0027038394112ac000cc750006d53400084000241b000890b0b40c4264d09815427310a8000c300000000f154c002212f1cd3717c5c000ca00114569443793807457141281903f4ed1a2a4423ec7d00000000000009a4ac005953e5001a2c4be350134a8bb1894e20039545292e51135c000d40000043110050100000010000000060003000090282c0e01000040a0001000060d0902402000188802060300c0407008000204028140402020540204018102201000001203000000a000400004000000404010a048040000028000b018581401008080203030080000010640400008686c05000000603038140e0300004060a0383c0603040041c010980000120000c0181764205731815200605190815cc6054801817742057318152006051d0815cc605480181784205731815200605210815cc605480184482205731815200605a50815cc605480181594205731815200415245831c165908011149160c705964200445245831c1529080121993a0375982420048664c8054a6090801124916087054c4200445245831c152108012149160f52584420050664c851c161108014299221470584420050a64b531c1611
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x1285c7af3e795183428e80620060000000000000582402001536b0009000082600000002cc14005c4402b5a00ca10a012074a9c700000c000260000000011230c0149c1a48205000004006021800700103010004014025132840ae6302a400a0428194205731815200442142c9d01bacc121002210a164c8054a609080120850b27a90e0b088400a04285831c0505844200600d2440ee8b9cc128802806a7e4c8154c625040140250b06310e0a928200980285939d462d814100540142c18c5a96c0a0802600a164c75d88605040130050b263a8c43028200a8028583d8b521814100540142c18c5a90c0a0802a02a2e4c8154c6050401500512e640aa630282008842859321d521814100520345a9900b888418802811a6254805c4420c401480d112a402e22106200a4068a6520171108310050234da9100b88841880301196200505c4420c401880c9100282e221062008416a4851ca6150431004a0345cb0a23828218802410a164f529c364c840140850b07380a1b26420090128593994725042100500d43c18e4b128328002412a1e4d621c1419400120250b2743cc4a948000a01285839887054a4000500942c18e5a92c220002804a160c72141611000180243924ba2a630a6000c0121c9154c625053000580142a98c43828298002404a164e651c941c800120850b27328e0a0e400090128593194725062000482142c98ca3828310002804a160e72d4b648400140250b07390a1b2420008816a465209410c41000500b4e32904a086208002410a164f525d84004001408d40cabb0622002000b00688655d83110010
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x5
  | 2 => 0x6
  | 3 => 0x4d
  | 4 => 0x4e
  | 5 => 0x124e
  | 6 => 0x138e
  | 7 => 0x4
  | 8 => 0x94e
  | 9 => 0x138d
  | 10 => 0x8e
  | 11 => 0x128e
  | 12 => 0x150e
  | 13 => 0x98e
  | 14 => 0xce
  | 15 => 0x12ce
  | 16 => 0x9ce
  | 17 => 0x168e
  | 18 => 0x10e
  | 19 => 0x130e
  | 20 => 0xa0e
  | 21 => 0x134d
  | 22 => 0x20e
  | 23 => 0x140e
  | 24 => 0x20d
  | 25 => 0x154e
  | 26 => 0xb0e
  | 27 => 0x140d
  | 28 => 0x24d
  | 29 => 0x24e
  | 30 => 0x144e
  | 31 => 0xb4e
  | 32 => 0x144d
  | 33 => 0x16ce
  | 34 => 0xb8e
  | 35 => 0x148e
  | 36 => 0x184e
  | 37 => 0x14cd
  | 38 => 0x3ce
  | 39 => 0x15ce
  | 40 => 0xcce
  | 41 => 0x170e
  | 42 => 0x40e
  | 43 => 0x160e
  | 44 => 0xd0e
  | 45 => 0xd4d
  | 46 => 0xe8e
  | 47 => 0x178e
  | 48 => 0xecd
  | 49 => 0x10056
  | 50 => 0x24055
  | 51 => 0x24056
  | 52 => 0x25256
  | 53 => 0x4256
  | 54 => 0x11396
  | 55 => 0x98096
  | 56 => 0x14d
  | 57 => 0x24116
  | 58 => 0x25316
  | 59 => 0x144116
  | 60 => 0x145316
  | 61 => 0x2cd
  | 62 => 0x1a0d
  | 63 => 0x1a4d
  | 64 => 0x24216
  | 65 => 0x40216
  | 66 => 0x41416
  | 67 => 0x25556
  | 68 => 0xb8256
  | 69 => 0xb9456
  | 70 => 0x148256
  | 71 => 0x24b96
  | 72 => 0x184256
  | 73 => 0x144256
  | 74 => 0x40256
  | 75 => 0x25616
  | 76 => 0x160256
  | 77 => 0x161456
  | 78 => 0x185456
  | 79 => 0x41456
  | 80 => 0xb96d6
  | 81 => 0x28e
  | 82 => 0x188e
  | 83 => 0x18ce
  | 84 => 0x20055
  | 85 => 0x241005e
  | 86 => 0x4255
  | 87 => 0x8996
  | 88 => 0x138116
  | 89 => 0x402421e
  | 90 => 0x25856
  | 91 => 0x24416
  | 92 => 0x145856
  | 93 => 0x144b96
  | 94 => 0x145616
  | 95 => 0x144416
  | 96 => 0x124256
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 76
  | 6 => 1857
  | 5 => 4409
  | 4 => 1856
  | 3 => 371
  | 2 => 50
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
  | 6 => packedAt gbK6 (76137+((h/619+packedAt gbK6 (68709+(h % 619)*12) 12) % 3261)*12) 12
  | 5 => packedAt gbK5 (232198+((h/1469+packedAt gbK5 (211632+(h % 1469)*14) 14) % 9372)*14) 14
  | 4 => packedAt gbK4 (116920+((h/618+packedAt gbK4 (109504+(h % 618)*12) 12) % 2228)*12) 12
  | 3 => packedAt gbK3 (27077+((h/123+packedAt gbK3 (25970+(h % 123)*9) 9) % 490)*10) 10
  | 2 => packedAt gbK2 (4162+((h/16+packedAt gbK2 (4050+(h % 16)*7) 7) % 80)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffffff007fffffffffe007fffc7ffc7f1ffe3f
  | 1 => 0xffffffff803fff800fffffffff8e3fffe3e3ff
  | 2 => 0xff003fffffc03ffffffff803fff3c798fc7fc7
  | 3 => 0x3fffffffc0000ffffffc03fc07e0ff83f8
  | 4 => 0x3ffffffffffff000000003fff800fffc00
  | 5 => 0xffffc000000000000000000003ffffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x4b554b0032d2c5b5596042e56434dc2b0dae1b
  | 1 => 0x95a9966580256a8302ad8d4ac98a29d562e0ed
  | 2 => 0xe60c25aad540335a6cd6d023b2d34698b45746
  | 3 => 0x403039d379b9800c4f1b67b0237c0760df03b0
  | 4 => 0x80c13efc6e3e3c6f800381c0c3efb800fbf800
  | 5 => 0xf8fe00e070302070081c060303fff7fe000000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xe8a8c888e8a0c880e8a8c888e8a0c880e8a8c888e8a0c880e8a8c888e8a0c880e8a8c888e8a0c880e8a8c888e8a0c880e8a8c888e8a0c880e8a8c888e8a0c880, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_13267
namespace PEqualNP.Outside.L_meta_13267
open PEqualNP.Outside.L_meta_13267.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_1_0 : Interval s0Atlas 1 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_1 : Interval s0Atlas 1 0 1 := bs0_1_0
theorem alls0 : ∀ k ≤ 1, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_1 i (by omega) hi
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
theorem bs2_2_0 : Interval s2Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 1 := bs2_2_0
theorem alls2 : ∀ k ≤ 2, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 1 := bs3_4_0
theorem alls3 : ∀ k ≤ 4, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 6 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 14 := bs4_4_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 9 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 50 := block_range (n:=50) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 50 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_96 : Interval s5Atlas 4 96 40 := block_range (n:=40) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 136 := (concat bs5_4_0 bs5_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 48 := block_range (n:=48) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 48 := bs5_5_0
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
theorem bgb_2_0 : Interval gbAtlas 2 0 50 := block_range (n:=50) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 50 := bgb_2_0
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
theorem bgb_3_288 : Interval gbAtlas 3 288 83 := block_range (n:=83) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 371 := (concat (concat bgb_3_0 bgb_3_96) (concat bgb_3_192 bgb_3_288))
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
theorem bgb_4_1824 : Interval gbAtlas 4 1824 32 := block_range (n:=32) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 1856 := (concat (concat (concat (concat bgb_4_0 bgb_4_96) (concat bgb_4_192 (concat bgb_4_288 bgb_4_384))) (concat (concat bgb_4_480 bgb_4_576) (concat bgb_4_672 (concat bgb_4_768 bgb_4_864)))) (concat (concat (concat bgb_4_960 bgb_4_1056) (concat bgb_4_1152 (concat bgb_4_1248 bgb_4_1344))) (concat (concat bgb_4_1440 bgb_4_1536) (concat bgb_4_1632 (concat bgb_4_1728 bgb_4_1824)))))
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
theorem bgb_5_4320 : Interval gbAtlas 5 4320 89 := block_range (n:=89) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 4409 := (concat (concat (concat (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 (concat bgb_5_288 bgb_5_384))) (concat (concat bgb_5_480 (concat bgb_5_576 bgb_5_672)) (concat bgb_5_768 (concat bgb_5_864 bgb_5_960)))) (concat (concat (concat bgb_5_1056 (concat bgb_5_1152 bgb_5_1248)) (concat bgb_5_1344 (concat bgb_5_1440 bgb_5_1536))) (concat (concat bgb_5_1632 (concat bgb_5_1728 bgb_5_1824)) (concat bgb_5_1920 (concat bgb_5_2016 bgb_5_2112))))) (concat (concat (concat (concat bgb_5_2208 bgb_5_2304) (concat bgb_5_2400 (concat bgb_5_2496 bgb_5_2592))) (concat (concat bgb_5_2688 (concat bgb_5_2784 bgb_5_2880)) (concat bgb_5_2976 (concat bgb_5_3072 bgb_5_3168)))) (concat (concat (concat bgb_5_3264 (concat bgb_5_3360 bgb_5_3456)) (concat bgb_5_3552 (concat bgb_5_3648 bgb_5_3744))) (concat (concat bgb_5_3840 (concat bgb_5_3936 bgb_5_4032)) (concat bgb_5_4128 (concat bgb_5_4224 bgb_5_4320))))))
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
theorem bgb_6_1824 : Interval gbAtlas 6 1824 33 := block_range (n:=33) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1857 := (concat (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 (concat bgb_6_288 bgb_6_384))) (concat (concat bgb_6_480 bgb_6_576) (concat bgb_6_672 (concat bgb_6_768 bgb_6_864)))) (concat (concat (concat bgb_6_960 bgb_6_1056) (concat bgb_6_1152 (concat bgb_6_1248 bgb_6_1344))) (concat (concat bgb_6_1440 bgb_6_1536) (concat bgb_6_1632 (concat bgb_6_1728 bgb_6_1824)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 76 := block_range (n:=76) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 76 := bgb_7_0
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 2 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 2 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 20, 21),(inputs.getD 2 zero, 17, 21),(inputs.getD 4 zero, 5, 21)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 3 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 3, 11),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 5, 21)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xe8a8c888e8a0c880e8a8c888e8a0c880e8a8c888e8a0c880e8a8c888e8a0c880e8a8c888e8a0c880e8a8c888e8a0c880e8a8c888e8a0c880e8a8c888e8a0c880
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 9 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 49 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 42 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) (SBf 2) :=
    slice_correct (ms:=fixRows 20 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (3903375496 * 2 ^ 32 + 3902851200) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_13267.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,4]⟩,⟨.and,[2,3]⟩,⟨.and,[0,6]⟩,⟨.or,[3,5]⟩,⟨.and,[1,7]⟩,⟨.or,[2,9]⟩,⟨.and,[1,11]⟩,⟨.or,[2,12]⟩,⟨.and,[8,13]⟩,⟨.or,[10,14]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,15⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 9) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3903375496 * 2 ^ 32 + 3902851200) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3903375496 * 2 ^ 32 + 3902851200) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_13267

open PEqualNP.Outside.L_meta_13267 in
theorem PEqualNP.Outside.L_meta_13267 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3903375496 * 2 ^ 32 + 3902851200) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3903375496 * 2 ^ 32 + 3902851200) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
