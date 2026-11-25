import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_13323.Model
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


end PEqualNP.Outside.L_meta_13323.Model

namespace PEqualNP.Outside.L_meta_13323
open PEqualNP.Outside.L_meta_13323.Model
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

def SBf (j : Nat) : Nat := [2, 2, 5, 5, 5, 6].getD j 0

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

end PEqualNP.Outside.L_meta_13323

namespace PEqualNP.Outside.L_meta_13323
open PEqualNP.Outside.L_meta_13323.Model
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
end PEqualNP.Outside.L_meta_13323
namespace PEqualNP.Outside.L_meta_13323
open PEqualNP.Outside.L_meta_13323.Model
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
  | 4 => 0xffffffffffffffffffffffffffffffffffffff
  | 5 => 0xffffffffffffffffffffffffffffffffffffff
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffff8b
  | 4 => 0xffffffffffffffffffffffffffffffffffff95
  | 5 => 0x26
  | _ => 0
def s1Atlas : Atlas := ⟨1,rawDecor 49 s1Pos s1Neg, 0xaaaa000000000000aaaa000000000000aaaa000000000000aaaa000000000000aaaa000000000000aaaa000000000000aaaa000000000000aaaa000000000000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_13323
namespace PEqualNP.Outside.L_meta_13323
open PEqualNP.Outside.L_meta_13323.Model
def s2K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (i*5) 5
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (6+((h/1+packedAt s2K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0xffff00ff807fffffffff80fe01fffffff8c7ff
  | 3 => 0x3fffff00007fffc03fffff0001fff80fff07c7
  | 4 => 0xc3ffffffff807fffc03ffffffe03fff00ff8f8
  | 5 => 0x3ffffffffff8000003ffffffffc00000fff00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x4b212483048c4484868b166a2c5a96935b5b
  | 1 => 0x1095e849552934a9291b40aaa156af2b28c5ad
  | 3 => 0x61264aec6a4e5923b22dd581499b318dcf06c6
  | 4 => 0x36388c8e4c6c623223b1e6cd8d03c5c18da8f0
  | 5 => 0xbbc0f0f070707c3c3c3e78f1f1e2060e0ef700
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xaaaa880088888800aaaa880088888800aaaa880088888800aaaa880088888800aaaa880088888800aaaa880088888800aaaa880088888800aaaa880088888800, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_13323
namespace PEqualNP.Outside.L_meta_13323
open PEqualNP.Outside.L_meta_13323.Model
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
  | 1 => 0xffff00ff807fffffffff80fe01fffffff8c7ff
  | 2 => 0x3fffff00007fffc03fffff0001fff80fff07c7
  | 4 => 0xc3ffffffff807fffc03ffffffe03fff00ff8f8
  | 5 => 0x3ffffffffff8000003ffffffffc00000fff00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x4b212483048c4484868b166a2c5a96935b5b
  | 1 => 0x1095e849552934a9291b40aaa156af2b28c5ad
  | 2 => 0x61264aec6a4e5923b22dd581499b318dcf06c6
  | 4 => 0x36388c8e4c6c623223b1e6cd8d03c5c18da8f0
  | 5 => 0xbbc0f0f070707c3c3c3e78f1f1e2060e0ef700
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xaaaa808088888080aaaa808088888080aaaa808088888080aaaa808088888080aaaa808088888080aaaa808088888080aaaa808088888080aaaa808088888080, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_13323
namespace PEqualNP.Outside.L_meta_13323
open PEqualNP.Outside.L_meta_13323.Model
def s4K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x10a01800280ef18dc31dc43b087d887810
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x8800310c421d031043808410
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (i*4) 4
  | 3 => packedAt s4K3 (i*15) 15
  | 2 => packedAt s4K2 (i*26) 26
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (5+((h/1+packedAt s4K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s4K3 (98+((h/2+packedAt s4K3 (90+(h % 2)*4) 4) % 9)*4) 4
  | 2 => packedAt s4K2 (81+((h/1+packedAt s4K2 (78+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffbf0fffc3fe3f
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffdff0fffc3fc7
  | 3 => 0xefff0fffc3f8
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffff41e222e2661b
  | 1 => 0xffffffffffffffffffffffffff0224454488ed
  | 2 => 0x244e89aa3346
  | 3 => 0x1888ee3323b0
  | _ => 0
def s4Atlas : Atlas := ⟨4,rawDecor 15 s4Pos s4Neg, 0xc880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_13323
namespace PEqualNP.Outside.L_meta_13323
open PEqualNP.Outside.L_meta_13323.Model
def s5K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x50d4900302d8a01406008e0004abf43bd43bf42bd42be41bc41de31dc31ee21ec21be40bc40fb10f810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x28008192000825aa5a1c754f428ea98812d52103a062087808410
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 6
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (i*5) 5
  | 4 => packedAt s5K4 (i*16) 16
  | 3 => packedAt s5K3 (i*27) 27
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (6+((h/1+packedAt s5K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s5K4 (244+((h/4+packedAt s5K4 (224+(h % 4)*5) 5) % 18)*5) 5
  | 3 => packedAt s5K3 (170+((h/2+packedAt s5K3 (162+(h % 2)*4) 4) % 10)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfe03fffffffe01fffff80fffffff01fff1fe3f
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xfffc03fc03fffe01fffff01fc07ffe07fe63c7
  | 3 => 0xfffffc0003fffffe01ffffe0007ffff81f83f8
  | 4 => 0xfffffffffc00000001ffffffff8000001ffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x97a0a4a628a31d25245c0972d4cb10cb30ae1b
  | 1 => 0x2a0509085144244848a0b2a5691563144754ed
  | 2 => 0x4caba2329a69491d913d58198c66b4479a6346
  | 3 => 0x713233a3639191911dce6cd03078d9e11d83b0
  | 4 => 0x81c3c3c383e1e1e1e1f78f1e3e40e1861ff800
  | _ => 0
def s5Atlas : Atlas := ⟨5,rawDecor 31 s5Pos s5Neg, 0xc888c880c888c880c888c880c888c880c888c880c888c880c888c880c888c880c888c880c888c880c888c880c888c880c888c880c888c880c888c880c888c880, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_13323
namespace PEqualNP.Outside.L_meta_13323
open PEqualNP.Outside.L_meta_13323.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x645838421c00008e5a00000a00527a000000005402005022004c820c0070787e000014004e005c88003a00347400005e006a002818763e2e480020048a620000008c006e004a0000008044300000001272000068000000406000000000103646006c0066567c0e1606002a843c321e00002c0086240000000826001a0002084002610002000c08200001820a00103000808000ffd5001fe54005f95001fd5400ff150017c5400ffd4c01fe53007f54c03fc53007fd0c01fe43007f50c01fc4300ffd4801fe52007f54803fc52007fd0801fe42007f50801fc42007fcc801fe32007f4c801fc3200ffd44017f51007f94401fd51005f54403fc51007fd0401fe41007f50401fc41007fcc401fe3100778c401fd31007f0c401dc31007fc8401fe21007b88401fd21007f08401ec2100ffd4001fe50005f94001fd5000ff140017c50007fd0001fe40006f90001fd40007f10001bc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x204005bf99020005fac81000efc6408001bf2a04000df1502001dfec610012fe6308007ef3184000b798c20005fac61000fdd63080016eb184003bf18c2001dfcc410003ef3208007f61904000bf98420005fac2100037f5108001bea884000f78c420007b86210003ee2108007f61084000bf98020006fca0100037c5008001df2004000ef1002001fde401000ffa2008001f69004003fe48020005fecb88006fe65c4001bf32e20019f99710005facb880037d65c40013eb2e2001bf19710005fec988016fe64c4001df3262000af99310005fac988003bd64c40015eb262005bf19310006fca9880037c54c40017fb1e2004bf98f10005fac788012fc63c40017fb162003bf98b10005fac58800efc62c4001bfa8e2000df54710007bc6388003dc31c4001f710e2000fb08710037f6a1880037e50c4001be2862006fe14310006f0a188003fb40c4001df2062000ef10310007f08188003b840c40017fb2c2000dfd9610004fecb08006fe65840017eb2c2001bf19610006f8cb080067c65840017fb242005bf99210005fac908016fc6484001bf2a42000df15210005fec708012fe6384001ef31c2000b798e10005fac708003dd63840016eb1c2004bf18e10005fec50800efe6284001f73142000bb98a10005fac508003ed628400176b142003bf18a10005fac3080037f5184001bea8c2000fdcc610007bc6308003dc3184001fa18c2000f50c610007ee4308003ee2184001f610c2000fd08610007c84308002fe6084001bf2842000df142100077c8108003bc4084001fb8842000fec4210005feca880037f65440013fb2a2001bf99510005faca88006fc6544001be32a20019f19510005fec888003bf64440015fb222005bf99110005fac888016fc6444001de3222000af19110006fca8880037c54440017fb1a2000f7d8d10005bec688012fe63440017eb1a2004bf18d10007b8c688002dc63440017fb122000fbd8910005dec48800efe62440017eb122003bf18910007d8c488002ec6244001bfa8a2000df54510007bc6288003dc3144001f710a2000fb08510006fca0880037c5044001df2022000ef10110007f62088003f610440017fb282001bf99410006fcca080067e65040017eb282000df59410004faca08006fc65040017fb202005bf99010005fac808016fc6404001bf2a02000df15010005fec608012fe63040017eb182004bf18c10005fec40800efe62040017eb102003bf18810005fcc2080037f5104001bea882000fdcc410007bc6208003dc3104001fa1882000f50c410007ee4208003ee2104001f61082000fd08410007c84208002fe6004005fda802000df94010006f8a00800bf85004001bc2802000fed00100077c8008003bc4004001fc2002000ee10010007ee2008003fa1004001fa8802000fe44010
  | 1 => 0x3de328c001ee1946000bf98630005fac3180037f518c001bea8c6000f78c630007b86318003ee218c001f610c6004bf98230006fca1180037c508c001df2046000ef10230007be6118013fb308c0017fb2a6000dfd9530004feca98006fe654c0017eb2a6001bf19530006f8ca980067c654c0017fb226000efd91300057ec898016fe644c0017eb226005bf1913000778c898002bc644c001bf2a26000df15130007bc8698003dd434c0017fb126000fbd8930005dec49800efc624c001f63126000bb18930007be6498003dd324c0017fb0a6000fdd8530005eec298002fc614c001fa30a6000bd18530006fea2980037d514c001ef18a6000f70c530007dc4298003ec214c001bf2826000df141300077c8098003bc404c009fd9826000f78c130025feca18006fe650c0017eb286004bf19430025fec818016fe640c0017eb206004bf19030006fca8180037c540c0097f3186003bf98830027dcc418002ee620c0017eb106004fb58830005dac418003de320c009ee1906000bf98430005fac2180037f510c001bea886000f78c430027b86218003ee210c001f61086000bf98030006fca0180037c500c001df2006000ef10030027be6018013fa300c001ee9806004fe4c03001dfecb90006fe65c8007bf32e40019f99720005facb9000f7d65c80013eb2e4003bf1972001dfec990016fe64c8007df3264000af99320005fac99000fbd64c80015eb264003bf19320006fca9900037c54c80077fb1e4004bf98f20005fac79000efc63c8007f72164000fb50b2001fdc6590003ed32c80017f30e4000bf58720006fea3900037d51c8001ef18e4000f70c720007dc439000fec21c8001bf2864000df143200077c8190003bc40c80017fb2c4001bf99620005facb10006fc65880017fb244005bf99220005fac910016fc6488001bf2a44000df15220005fec710012fe63880017eb1c4004bf18e20005fac510003ef3288001f61944000bf98620005fac3100037f5188001bea8c4000f78c620007b86310003ee2188001f610c4003bf98220006fca1100037c5088001df2044000ef10220007de411000ffb20880017fb2a4000dfd9520004feca90006fe65480017eb2a4001bf19520006f8ca900067c65480017fb224000efd91200057ec890016fe64480017eb224005bf1912000778c890002bc6448001bf2a24000df15120005fec690003df63480016fb1a4004bf98d20005fac690012fc6348001ee31a4000b718d20007dc8490003ed4248001f71924000fb4c920005fec290003f761480017bb0a4000bf18520007e8c290002f46148001bfa8a4000df54520007bc6290003dc3148001f710a4000fb08520006fca0900037c5048001df2024000ef1012001ff64090003ee20480077fb284001bf99420005faca1000efc65080077fb
  | 2 => 0x400077ec320003be6190001deb0c8000ef186400477ea3200033f5190001df28c8000ef546400067aa320023bc5190001df98c8000ef8c6400073c6320003bd3190001de18c8000e70c6400077e4320003be2190001d710c8000ef48640007784320003ac21900015f3048008efd42400077ca1200033e5090001dea848008ef1424000678a120002ff6550001bfb2a80009fd954000dfccaa0002fd65500037e32a8000df1954000cf8caa00177e545000bbe2a28000bfd8d40025f8c6a0002ff62500077e3128000bfd8540005f8c2a00037f5150001bea8a8000f78c540007b862a0003ee2150001f610a8000df94140006f8a0a0017fb4050001df2028005bfd944002efeca200167f65100037f3288000bf5944002df8ca200177c651000b3e3288005bf9904003f7ea8200177e541000bdf2a08005cf950400077aa8200177c541000bde2a08005cf15040025fcc620017de63100016f3188000bf58c4002fbac620002dd631000bdfa188000ef90c400077a8620017bc43100077f3108005fb98840005dcc420002fd621000bf6b108000bb5884002f7e8420003be4210001dea108005ef10840005fcc220002fd6110001bfa888000df5444002f7e8220003be4110001dea088005ef10440007bc6220003dc3110001f71088000fb08440005fcc0200037e5010001be2808005efd004002ff48020003bd401000bfca008005efd944002e7eca2001fbe6510001deb288005ef1944002e78ca20017bf6310001df3188000e798c400077ac6200039d631000bde3188007efd4c400077ca620003bd531000fde2988005efd88400077cc420003ae6210001deb108000eb5884002f78c42001fbf5210001df2908000ef5484003f78a420003bf3210001df1908000ef4c840007786420017bf6110001df3088000ef5844002f78c22001fbf51100019fa888000ef944400077aa2200033d511000fde2888000efcc4400077c62200039e3110001de9888000ef0c440007386220003bf2110001df1088000eb884400077a4220003bc2110001d61088000ef980400057cc020003ba601000fdfa808000ef940400067ca020003bd501000fde2808000cf14040025fecb98006fe65cc009bf32e60019f99730005facb980137d65cc0013eb2e6004bf19730025fec998016fe64cc009df3266000af99330005fac998013bd64cc0015eb266004bf19330006fca9980037c54cc009ef21e6000f750f3001dfcc598002fd62cc009ef9966000f74cb30005fcc398002fd61cc001bfa8e6000df54730007bc6398013dc31cc001f710e6000fb08730006fca1980037c50cc001df2066000ef10330005fecb18006fe658c0017eb2c6001bf19630005fec918016fe648c0017eb246005bf19230006fca9180037c548c0017eb1c6003bf98a30005fac51800
  | 3 => 0xf304a001dfd425000ff6a128007f85094001bfb24a000df9925002cfcc9280037d6494001be324a000dfd8e50006fcc7280037d6394001be31ca000dfd0e50006fc87280037d4394001be21ca000dfd8a50006fcc5280037d6294001be314a000dfd0a50006fc85280037d4294001be214a000dfcca50006fc65280037d3294001be194a000dfd8650006fcc3280037d61940013eb0ca000df18650006fe83280037e4194001bea0ca000df10650006fe63280037e3194001af18ca000df4c650006f863280035c3194001bf90ca000df88650006dc43280037d2194001be10ca000db0865000cfcc128006ff65540017fb22a000efd91500057ec8a8016fc6454001de322a000af19150006fca8a80077c54540017fb1aa004bf18d50005fec4a800efc62540017fb0aa000bf1855000efea2a80037d5154001ef18aa000f70c550007dc42a8003ec21540037fb02a001fed4150006fca0a80077c5054003fc282a001dfd905000efcc8280167e6414003beb20a001df1905000efec6280077e6314003beb18a001df18c50006fe86280037e4314001bea18a000df10c5000efec4280077e6214003beb10a001df18850006fe84280037e4214001bea10a000df10850006fe64280037e3214001be990a000df0c85000efec2280077e6114003beb08a0009f5845000ef8c2280037f4114001bf208a000df50450006f882280037f3114001bf188a000d78c450006fa62280037c3114001ae188a000dfc8450006fc42280036e2114001be908a000df08450006d842280077e60140013f300a001de9805002dfecba0006fe65d000bbf32e80019f99740005facba00177d65d00013eb2e8005bf1974002efca9a00177c54d00097f31e8000bf58f4001dfcc5a0002fd62d00017f30e8000bf58740006fea3a00037d51d0001ef18e8000f70c740007dc43a0003ec21d0001bf2868000df14340005fecb20006fe6590001bf32c80019f99640005facb200037d65900013eb2c8001bf19640005fac920023bf549000bbf2a48000ef952400067ca920003bd549000bbe2a48008ef1524000678a920012fe63900017eb1c8000efd0e400077c8720003bd4390001de21c8003bf98a40005fac520003bf4290001df2148000ef50a40007788520002fe61900017eb0c8000dfd4640006faa320003bf4190001df20c8000ef50640007788320003de3190001ee18c8000fb88640007d84320016fe6090001bf2848000df142400077e8120017fb4090001dfb2c8008ef996400067ccb20003bd65900019eb2c8008ef196400077ec720003be6390001deb1c8000ef18e400477ea720003be5390001dea9c8008ef14e400077ec520003be6290001deb148000ef18a400477ea520003be5290001dea948008ef14a400077e6520003be3290001de9948000ef0ca
  | 4 => 0x803ec4288401f79944200fb8ca21007da6510803ec32884077f30c4200dfd4621006faa310803de3188401ee18c4200fbc862101fee4310802fe60884017eb044200fbd9621057dccb108036e6588401f6b2c4200db59621057d8cb10803ef6488401f73244200fb59221007d8c91082bef5488401f72a44200db95221007daa91082bec5488401b62a44200fbd8e21007dcc710803ed6388401f631c420afbd4e21007dca710803ed5388415f629c4200fbd0e21007dc8710803ed4388401f621c4200bb98621057dea3108036f5188401f728c4200fb54621006daa31082bec5188401f7a0c4200fb90621007da8310803ec4188401f798c4200fb8c6210079c6310803ed3188401f618c4200f30c621007dec110803ee6088401f6b044200fb18221057dea11082bec50884017fb2a4201bf99521005faca90806fc65484017fb224205bf99121005fac890816fc6448401bf2a24200df15121005fec690803df63484016fb1a4204bf98d21005fac690812fc6348401ee31a4200b718d21006fea2908037d5148401ef18a4200f70c52101fee4290803ee21484017fb024200bf1812101dfeca10806fe6508407bf32842019f99421005faca1080f7d65084013eb284203bf1942101dfec810816fe6408407df3204200af99021005fac81080fbd64084015eb204203bf19021006fca8108037c54084077fb184204bf98c21005fac61080efc63084077f3104209fbd482101fdca410803ed5208407f62904200fbd082101fdc8410803ed4208407f62104200fbcc82101fdc6410803ed3208407f61904200bf98421006fea2108037d5108401ef1884200f70c42101fde421080ff62108401f69084203fd48421005fcc010802fd6008407f7b284209fb99421006dcca10803ed6508401b6b284203fb1942101fdec810803ee6408401d73204200fb590210075ac81080fec6408413f7aa04200fb95021006dca810803ed5408413f62a04200db1502101fdec610803ee6308401f6b184203fb18c2104fdea610803ee5308401f6a984209fb14c21007de8610803ee4308401f6a184200fb10c21007dcc210802ee6108401f33084209fbd4421006dea210803ee5108401f6a884200db5442104fd8a210803ef4108401f72084200fb50421007d88210803ef3108401f71884200f38c421007da6210803ec3108401e61884203fbd8021007dcc010803ed6008407f63004209fbd402104fd8a010806fd659400b7f324a000bf5925000efea9280037e5494001beaa4a001df15250025fcc728002fd6394003bfa9ca000df94e50006faa7280077c53940077f314a000bf58a5000efea5280037e5294001bea94a001df14a50005fcc328002fd6194003bfa8ca000df94650006faa3280077c5194001ef18ca000f70c650007dc4328003ec21940037
  | 5 => 0xe3101dfcc518802fd628c401ef9946200f78ca31007ba6518803dc328c4097f30c6200dfd4631006faa318803df318c409fb98c6200bf98231005fac118803df658c419ef32c6200d799631007bacb188035d658c419ee32c6200f7d9231007bcc918803dd648c401ee324620cf7d5231007bca9188035e548c401eeaa4620cf715231006b8a918803df628c401ef3146200f758a31007b8c518833df528c401ef2946200f754a31067b8a518803df428c401ef2146200f750a31007b88518802de618c419efa8c6200d7d4631007bca318803dd518c401aea8c620cf714631007be8318803de418c401eea0c6200f710631007bec118803de608c401eeb046200f718231067bea118833dc508c4017fb2a6201bf99531005faca98806fc654c4017fb226205bf99131005fac898816fc644c401bf2a26200df15131005fec498803ef624c40177b126203bf18931007d8c498802ec624c401bfa8a6200df54531027ee6298803de314c4017fb026200bf18131025feca18806fe650c409bf32862019f99431005faca188137d650c4013eb286204bf19431025fec818816fe640c409df3206200af99031005fac818813bd640c4015eb206204bf19031006fca8188037c540c4097f318620bf7d4c31027bca618803dd530c409ee2986200f7d0c31027bc8618803dd430c409ee2186203bf98831005fac418813df320c401ef1906200f74c831027b86418802fe610c401bfa886200df54431027be6218813f6310c401ee9886204fd4c431005fcc018802fd600c409efb28620bf799431006bcca18803dd650c401aeb286204f719431027bec818803de640c401cf3206200f7590310073ac818813dc640c417efaa06200f795031006bca818803dd540c417ee2a06200d715031027bec418803de620c401eeb106204f71883105fbea418803de520c401eea90620bf714831007be8418803de420c401eea106200f710831007bcc218802de610c401eb308620bf7d4431006bea218803de510c401eea886200d75443105fb8a218803df410c401ef2086200f750431007b88218813df600c401ef3006200f758031027b8c01882fdf500c417ee2806203bfd972100dfccb90802fd65c84077e32e4203bfd932102dfcc990802fd64c84077e3264200df95321006f8a99080eff63c84097f31e4203f798f21005bcc790802fd63c8407eeb1e4200b758f2101df8c7908037f51c8401bea8e4200f78c721007b86390802fe60c84017eb064200bfd962100dfccb108037e65884033f32c4200bf59621006facb108027d65884037e32c4200bfd922102dfcc910802fd648840b7e3244200df95221006f8a910802ff63884097f31c4200bf58e21025f8c710802fd6288415f7a944200fb94a21007daa51082bec5288401f7a144200fb90a21007da8510
  | 6 => 0x176312a201dfd4951006fca4a88037d5254403be292a201bfd855100feea2a88037e5154403be28aa201fd14551005fec0a8803fb60544017db02a200bf18151007f0c0a8802f86054403bfa82a201df14151006fec8a88033f6454401bf322a200df59151006f8c8a88167c64544019e322a2008f19151006fec6a88035f6354401bf31aa200df58d51006f8c6a88035c6354401bfa1aa200df90d51006fa86a88037c4354401bfb12a200dbd8951006fcc4a88037d6254401be312a200db18951006fe84a88037e4254401bea12a200df10951006fe64a88037e3254401be992a200df0c95100efec2a88067f6154403bbb0aa200dfd8151006f6c0a88037e6054401beb02a200df18151004f8c0a88037860544013c302a205bfd974102efecba08167f65d04037f32e8200bf5974102df8cba08177c65d040b3e32e8205df9534102ef8a9a0812fe63d040bef31e8200b798f41005fac7a0817dd63d04016eb1e8205efd0f410077a87a080efe62d040bf73168200bb98b41005fac5a0817ed62d040176b168205efd0b410077a85a08037f51d0401bea8e8200bf98341005fac1a0802ff65904037f32c8200df9964100cfccb20802fd6590401beb2c82009f5964100df8cb20802fd649041ddfaa48205df9524102ef8a92083bbc54904019e2a48204bf98e41005fac72080efe62904017eb148205bf98641006fea3208037d5190401dfa0c8205fdd0641005fcc120802fd60904017fb2a8200dfd9541004fecaa0806fe65504017eb2a8201bf19541006f8caa08067c655040bbf2a28205df15141005fec6a0803df63504016fb1a8204bf18d41007b8c6a0802dc6350401dfa1a8200ef50d41005fec4a0803ef625040177b128203bf18941007d8c4a0802ec6250401dfa128200ef50941006fea2a08037d515040bfba0a8200ef90541005fec0a0803fb60504017db028200bf18141007f0c0a0802f8605040b7fb288201bf9944102efcca208067e65104017eb288205df59441004faca20816fc651040b7f320820defd504102efca8208177c541040bde2a08205cf15041025fcc620802fd63104077f3108200bf58841005fcc2208037f5110401bea888205efd044102fec8220803bd411040bfaa088200bf98041005fac020812ff65cc4037f32e6200bf59731025f8cb98812ff64cc40b7f3266200bf59331025f8c9988037e54cc401be2a66203bf98b31027dcc598802ee62cc4017eb166204fb58b31005dac5988037f51cc401bea8e6200bf98331005fac198802ff658c4037f32c6200df9963100cfccb18802fd658c401beb2c62009f5963100df8cb18802ff648c40b7f3246200bf5923102df8c9188037e548c401be2a46200bf58e31067bea718803de538c401eea9c620cf714e31007be8718803de438c401eea1c6200f71
  | 7 => 0xa1002de63d08017eb1e8405f758f42005bac7a1002fe61d08017eb0e8400bf98342005fac1a100eff65908037f32c8403df9964200cfccb21002fd6590807beb2c84009f5964201df8cb21002fd649080bbf2a48405df15242025fcc721002fd63908077f3148403efd0a4202fde8521002fe61908017eb0c8400bf98242005fac121002ff6550801bfb2a84009fd954200dfccaa1002fd65508037e32a8400df1954200cf8caa103fbf545080bbf2a28405df1514207f78a8a10033c54508017fb1a8404bf18d4202fde84a100fbe42508017fb0a8400bf18542005fec0a1002fc60508077fb288401bf99442005faca2100efc651080b7f3208405df9504202ef8a821012fe63108017eb188403bf9884201f7e842100fee4210807dea108405fb50842005fcc221002fd61108017f3008400bf58042025fecb99006fe65cc8017eb2e6404bf19732025fec999016fe64cc8017eb266404bf19332006fca9990037c54cc801f72166400fb50b32005fcc399002fd61cc8017f3066400bf5833201dfecb19006fe658c8017eb2c6403bf1963201dfec919016fe648c8017eb246403bf19232006fca9190037c548c8017eb1c6400f790e32007ba871900efe628c807ef9946404fbcca32005fcc319002fd618c8017f3046400bf58232005feca99006fe654c8017eb2a6401bf19532005fec899016fe644c8017eb226405bf19132006fca8990037c544c809f79926403f78c932005fec299002fc614c8017fb026400bf1813201dfeca19006fe650c8017eb286403bf1943201dfec819016fe640c8017eb206403bf19032006fca8190037c540c8097f3186404f790c32007ba861900efe620c807f72106400fb5083201fbe641900fee320c807ee9906404fb4c8320079a6419002fe610c8017eb086400bf98032005fac0190077f64d4403bf326a2059f9935100efac9a88077c64d4403bfb1ea201df98f5100ebcc7a88077d63d4403aeb1ea201df18f51006fe87a88037e43d4401bea1ea200df10f5100efec5a88077e62d4403b7316a201df58b5100edac5a88077c62d4401bfa16a200df90b51006fa85a88037c42d4401bf996a200df8cb51006fa65a88037c32d4403bfb06a201df98351004fcc1a88077d60d4403be306a201bf59651004facb28816fe64944017eb24a200df9525100ef8a928812fe63944017eb1ca203bf98a51005fac528806fe6194403bfa8ca201fdd465100fe8a328802fe60944017eb04a201df1425100dfecaa8802ff6454401dfb22a200afd915102df8c8a8803bc64544015e322a201dfd5151006fca8a88037d5454403be2a2a200bfd8d51007bec6a8802df63544097e31aa200f718d51005b8c6a88077f5354401bf29aa200df54d5100ef8a6a8802ff6254401f7b12a200bbd895101df8c4a8803ec625440
  | 8 => 0xfd8e5402efcc72a0177d639500bbe31ca805dfd8a5402efcc52a0177d629500bbe314a805dfd865402efcc32a0177d61950013eb0ca805df1865402efec12a0177e60950013f304a805df5825402ef8c12a016ff65550037fb22a801efd515402efca8aa0177c5455003de2a2a800bfd8d54025f8c6aa002ff62550077e312a800bfd8554005f8c2aa0077f51550017fb02a800bf1815400ef8a0aa0177e641500b3f320a805cf9905402efec62a0177e631500bbeb18a805df18c5402efec42a0177e621500bbeb10a805df1885402efec22a0177e611500bbeb08a8009f5845402ef8c22a0177f601500bbf300a8009f9805402efac02a0177c60150037eb2ca605bf992530277cc929802be6494c017eb24a604ef592530057ac9298037e5494c03be2a4a604bf98e53026fea729807df5394c09ee29ca603bf98a53005fac529802fe6194c017eb0ca601dfd4653005fcc129802fd6094c03be284a604bfd9553005fec8a9816fc6454c01bf2a2a601df1515300dfec6a9807df5354c09bf29aa604df14d5300fb8a6a9802ff6254c077e312a600bfd8553005f8c2a98077f5154c017fb02a600bf1815300ef8a0a9816ff65d0c037f32e8600bf5974302df8cba184bbf54d0c0bbf2a68605df1534302f78a9a18173c54d0c077f3168605fb98b43005dcc5a1802fd62d0c0bf6b168600bb58b43005fcc3a1802fd61d0c017f3068600bf58343025fecb21806fe6590c09bf32c86019f99643005facb218137d6590c013eb2c8604bf19643005fac9218177e5490c0bbe2a48604bf98e430277e8721817df4390c077f3148600bf58a43005fcc321802fd6190c017f3048600bf58243005fecaa18037f6550c013fb2a8601bf99543005facaa1806fc6550c01be32a86019f1954308f7ea8a18177e5450c0bbe2a28611ef1514300678a8a1817df4350c09df21a8600bfd894301df8c4a1802ff6150c017e30a8600bfd8143005f8c0a1812ff6510c037f3288600bf59443025f8ca21816fe6410c0bbf2a08605df15043025fcc621813bf4310c09ef2188604ef50c4302fba862180efe6210c017eb108600bf98443005fac221802fe6010c017eb008601bf5965202dfcc92900fbe64948015f324a400bf5925201f7ac929002bd6494801bf2a4a401df15252025fcc729002fd63948077f314a403dfd4a5200fdea52900fec52948017f30ca400bf5865200efea329002fe60948017eb04a401df1425201dfecaa9002ff645480b7e322a400df9515200ef8a8a9002ff63548097e31aa401bfd895200fdea4a900f7e5254807be292a401fb14952005fec2a9002fc6154803bfa8aa400bfd8152005f8c0a90077c505480b7fb2e8401bf99742005facba1016fc65d0821dfaa68405df9534202ef8a9a1017bc54d080b9e2a68404bf98f4202fbcc7
  | 9 => 0x600300000600300103300900000700000b00000301600200302001100f00100100100000d00200901100100000300103200401200100000000001001401b00c02300300a02000b00300200600c00102600a00800800000300000600f00500200000100000100200600f00000000000500200802000400100900200500300000c00000e00000000c00701501c00502f01704900000600300000300b00101f00100400000002800700500600400000600100900000000200d00000200200000000200600200000600000100401c00100100700e00100101600201700900100c00d00e00401100000500200001a00101500600401a00000000200900400401c00500102701e00002100b00a02c00d00c00003800000000100f00001200401400000000001600000900900101200000700000800500000600100200400200500000000600200500000000000703e00500903100000901600800801100100000300000000300100103a05800b00700a00100000d00b00e05a06100000000000100000b00600200f00b00000002900b00700200f00000202200100000700000800500100107301d00100300b00101400000300801800600100100200d00200100700000500f01f00301701a00300400300001902000600a01a00700000000300300200200000200000500500100901700600003700301300900800300d01100200000500b00100f00200000000000300700000100100600400300700000000a00100000801300000000700201800d00200801a00200501e01100a00000201d00000400200201c00b01b01c00100100100400700400700004800200900500200200d00b00000b00100b02600200500300000200002100100100800100001400001500000100300901600000e01800200100100000600800200100000901f00f00000603f00100900701900100500000601001500002100500101e00700200300002b02b00600100000000002500500200001001701b01c04100200000100a00c00300000401b02c01100400002d01f02600002600200000604b00000500d00400600b00000900100e00200000000200700000000202b01701100100200800c00000000200001100600000900000c00100c00400101300100002600000300300300201100000100300801300002e00300003901200b00000800c00000000000700700500000c00700600e00300200100001800000300000a00101c01600000200000000200300403201400003700000100a00100b07c00100dfacb2a016fe649500bbfaa4a801efd525400e7ea92a017bc54950097f31ca800bf58e5400efea72a0077c53950077f314a800bf58a5400efea52a0077c52950017f30ca800bf5865400efea32a0077c51950017f304a800bf5825400efea12a0077c509500b3f324a805d
  | 10 => 0x8000f6e26079612071ebd00002e20009ea828d72da000045000050e33ad140008d0cc20920e27a23a8b5076e5ec07abda4d046c000694f08d909a60d0b54226ab86e600058800040cbf2000f9e10c826000dd200027e30ce06e7600074a192000000bcc57c7f49b40002ca0008b800098c00081c90a80888a000e98d5479eadef7e9a20001e689602a26257614c76ab287220fedfaf4e93c000a30216342616c02bc07b4424fa6b9e0000005eeee8c9271685e5a833e1f21e4cf2cce744114058b34d6c83883aa8cae82d61d8136fa85ae06a4b65583b05a29c889a0d845a00096a2a459e36a5e247473e2d0e9cc54b5e3d80004e000000000000038c0c44900008da000f90baa79c1be0527123d451caf8d3e10a000a3e000f5ae66e46eca41cf6a8feca020c492b84778d08f806f2886070496b6e22e73000034e1346662749c21b2df6e8433262cd740ac84a1800327706b62fcc3a00000042e5b22e6000cdcec0e1ef0c62e43cb566041703101e85ce2b889e3c2a0c476020000000ac0e44d2c000d6824c9948f6bf69f2552ceadbeaeab2aa6eb06620b32928b60478000000746c72c8ebf4d88e64000c12000de4a84944b8ed84ad00006e43f225468e13e82205e3946e88c0cbcdb66109daf8620268437e28627c2385bc0e83fa35868cf621c8becad4c60b98f9aa58962c14ce67f2824dcede6e340c2ea64fa2aa010542be8000d5eb525486825d6854b1252c638a820280ee67e710e364f4f8e000eee0000fa2229d05d883669ccfa28ecdaa4669e91a56609c278264000000e4c04a2e8000000000000c1c9eee8c00c1feecef4c000000d30000d0065cb78e324a27607d41126481164c644c5f857e7e8f482dce82ccc1b4f547fa000f7adbc18821a1300005c4036f0e4bec588fc51e000340000000486cf0000a201768b093e000fa46f800000044e41e7e46dc000a6c8ccf5e000b0e03e0009465e8000000000000000000a4c2d8af0000472000c1e000000b1cddc00055c000e08e240e0bac6b4748d0eafa40a54400000000065a000388efc42098e7545a4000564208350984c62000000ecc602878bc23d62566deaba2fa04e8e20942046ac09abe08b485c0dc0068fada6c88cd09900001a0000d163aaef418e3123b2b488ea00a050e686ccc8acc6668a060000008183085f497a000cca4b2ef85aab6a008ae4674e1ca56de897c3e86e299aee0e183cc2c6000c38aa00401acaf6e1a5a6000000000f8a9b6c7c774000e4a000000ac272a2d23149c6a5c3d05dc00093000000069a000e420003a200106300402600a00002900100000d01300001b00000000800500002300000f00203500600900400100500000200000000000000300100b00200100400200b01100001801300601c00201300000001600001400000200b0070000010
  | 11 => 0x95600016ad4c9180be900eba7c2faedd012cda2eb039c9e69d64260767c6ec600043a000438d3af98e9496e00006441a82cc2adb4f3400015657aa26d1ea9e32e88e526c82b829862b0a92be6060958252adaa404886c4914658228c9c128d6498ab140002f424000031ea36dec0b4000f2042c00086e00001eb40e28556a34eb20e4e8a000c9e000000000eaa000d4aa004ce742dee000000cae000000750f1a000f1c026d32dd853e7a0f16c742acc3065630e70c3e2d9c46219419a64c0e61785b02cc2b21f43f0d0ac0c870618f96568090a74bfeef00129ccf6cd5c2b4f92812a38f2e1b69b0bba1445c2106004e3a4ea714000316a86000596c840008329bc3ee53600000077cdfc43625c4f692a0ea8ec7c0898f26bb28a8a98952bcea7a1ee370000f140c6b3a2f80001524b4598a788aac5c9ca7801daf0a36caa415e000042662400a24d823fe4460f4000182a6812675e2fe87c89c282b7400275ce2688200077e80200015a5f6dea2ba0f8b4e124bf80002ceb765cac8ca7c7b0f060d259ad44000000b080000007ea708000000bd683e39a27654000058676cc221c60340a260028400078abde000304b0a6f0b4a9a000000018a000000c688bc37662a000000000158aaec1a82a4082c286485235a514a0271ab9461450c344be47240001ca58e000cf6000df0000ae261c000652f10418b262140000567b2d50c16da4aa6c6c998000eda60e756584236e7e4b0f8c04c80449eb44c244ecb802a22ecdaee88b6845c1d03624ccdd4ace32a1185d4294816ab006c266736e58df2b8c1503de3d211ea2a00000e0007921e200000065000008c0001725a05e69c0b6213ce9af9498234c2a01f0a9cd5a8e80008f4000aee0000003da000c6e000000e74000d3c6be000108000000000ec848e0000006c0c280ba00026c0008f08743520000000a8636538ba8022768ec472cd460004660006963300000ec1b0b30772d0c5b6590a2c23ee0c3ac83058031888c3fc48217490c0003a62e47f80000006b252453a3a40004280000000000a605cdba0000383be396d66dc20b0000000a12a4ad280006a2e2a7ba92e3ba67a000e2e000c64fbec4aaf4422eae290054244a96044a14aca31a148996b6490e2a80006eed86d10b3ce30cecbdc3808be9d837c74e200976bb66ca000d984b80000000007bcc460da6c8e3e0006e056ccfe964f4aebc5e0c428e4e2c502a543b8080b10146654000000c08ef2ad2efe4e68dc00096c0001f628c000d7e9ceef639e9b80000006d69fa68ac860008604344c8000c06ee68005c03aec18b6c49aebeab6048d60000e48ce4346ba41aec5e000b8861ee8607e924cba4f259c7ec4d656e8c8be2d6a13aa60520234cc8086fb4fa043e1c4504a44ac4a520008a08800007da980000970bbe1ea5d0ab2378bd
  | 12 => 0x6e9f44e2384d2ef384c01fce6a93230244263a40ecc46ec386d9e1047ccc2e224ac654e94269806264a8d23ce570d6e0a4bee2be84cd2660814a7668d830aa3a47052e8aea6422a916c100f00a037419633c5d28666babeab0cdc666c7fe404b2cca867ca5ab72dd696012a1aa0deb46534e10c90b1eeaca66a48fb8a50ab4fa24d83c4bb0bc6b7c3c08b6a94f2a67829af001ce32269035e162dcabc4a90074bfc814e00dcc1907d08f201a78e0000003c8b040006349500009484da0002320000002c8a7ee4e138978806d387ae66ad48e62198968500bb87d66aa50a54cf30ba001c9de4a6cd2f66a0e7e2e04d92508b92670f3e7d226a220210686afced6f6016caac018ed44ac8c6f5c80ce1291edf8444cf80846ae3a0e54718f3ccaa1d64a89c4b7a894c5ac20000d2072836832638e1a2000ed837a000876000000000f522e07c800051a44a31c2308485181dcc56d58c7ebd481e00024edc449400000079ab5800070048a3600005e41ba000ed016e2f08906d2cc0bae49c8a6e70cb6cac27202ed78e90e5e764de0daa9d4db2954cb8a281ecf467f044010047c1b8702d8073a11c8ca73c47eca4f7c842aa866099e2504d2612e6ca324de0007a47a883c000f58a42c9a3bc154a705c85223f8e7a2469922c0d70d1c00032c000f047eefaa9baf82ee225ec96da8f420b6cd6ca62800f2416000a165320000009f00000000000003b6b1a338a0890280eb2210e39046a00086ab5aae6c6afb233407248cc401c08ee6c219e56aba641474c7ac7c4eb45ba872d7a0ccd24a18ce80007940000000004fc014000fbc0000000006fe55e15ce528104ba92063cf1e28a07ca76eb8ce24c46b0a8a000aa24f8000c4c680d02000f180008d44dce16000000562bb44bcbf0000844594a2220a0460c8f12300b02c0ec48c7ae22f504e46268bab38f84688a72b86df463e2f67cef765743ca0665506f64544483ece964e8abe000410000000726184f56a88b18000e20c7652a784000516f682f2692e3c0009a4e38e789ae00078200000000075a64000094c6bc2bc000d34546000000edc0000000000006a6000ea86a0fba4ae3281a4000000000a1ec2c78c738cbe62853c3c6c66000000348b4c000934fb6000ba2ca200065e11045e2ea4645fece0c365ea0cea04e5c3f694e10235c868cf42581cc85a00029641223a9666061c28e0d8eb9aa5e0000001409100d65c605a2923822ae000de2bbcf783e69747be21854ab7ebca1e080a06e2a6a10ea09fe1644309acb3ef740001de00036e452c78936786a8e71c1f89a83e0e5a64e160eb6e0a0000007cadc00006d40002683240009f8f32000644b9c09861a5da016122000f36e72846850cb40aec70168bfa0f68c2788000000484f407fcd227986f4336a4e75281a0aaa2e97e000762e6e9f6
  | 13 => 0xb24000354a3cafe00000058c08284082e84e00008e2b697258a000884000000e92888892460c440fc0000008d6078aec000f28d4e7765541661d4e8e366000c987206723ea9ec0bcc4ec3eeec1fa90870442a35629cd6240600000062451214e030a9a372a62d1ac5222cd9a1329e8b2e8f829803c7b63f419c530d8a47acfce02b36d40aaa8a2d767908b2f709aa4d427003a862d960000000007b8c0a392cd8e4002c94a7a6940b900b2a80578000000acc00045646eb425f2734000468000000fb0000e9e2de5b872e5f0646d94b966fc856cb087a3e4ad6af2000f645925fcf7270eea27d87aa6c6f029e47dc1bca1adc84f06ea5fad7c4c20d439809627a858000938740212000e56642ec258221e820f2c5be000ee400009e000cde068b7020e000b8ac34ede4aa92c3064a418c08ae147e693abc8efa92617ac3295e506758000632f9c29e4a0000ed22c40006da60c60a1a8e60664b5c3200006a4000c26db89be0000000000008ce000a6a8a448012e25a5286a8000906000b005cc34a2ee87e0c02884cadb0c04088e0eb16dacd52000bd217e21c0006fa000402ac8dfed36dde0001d20005b4000cb25ac0000008340009d20b899c38a364572dda24855a17c7deabc0000000007069e0000000f88000000c5020600000000000000051000095c000d18ae0000cd4f447f600000000024ad12adc000d56d06000cee62200026e0003b49fcb2077a90400000000095a9dcd42000000f228c42da000000000024000c007e0000988a0a000c946760000001a66d086c6d86ce23c4fe70a732000000f3a0001420005605de3dc922face50000e7cc804980000004324586b891c0caeea4eed2af24630912ea49b22d4242ad8e80186d04c3c8de8e6d8cb668ac9e211aa1c6
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe75d90100047d75d90100047f755901000c7c755901002c7f76950100047d76950100057a709501002c7f76150100047d76150100063f641501002e3c641501000c7e75d8c100047d75d8c10004ef7258c1001cec7258c1000c7e75d88100047d75d8810004df7358810024dc735881000c7e75984100047d759841002cbe7498410004bd74984100047d76d44100047f76544100053c7454410005e672cc4100665e658c4100065d658c410005d6718c41005e5e650c4100065d650c41000757510c41000755510c410004f5760c410006d6760c410006d5760c41000756750c41000755750c41000756650c41000755650c41000796740c41000795740c41000756540c41000754540c410007d2700c410007d1700c4100afd3500c4100afd0500c410005d673c84100566e65884100066d6588410005e67188410007c4318841004e6e65084100066d6508410007675108410007655108410007c63108410007c43108410004f57608410006e67608410006e57608410007667508410007657508410007666508410007656508410007a67408410007a57408410007665408410007645408410007e27008410007e170084100a7e350084100a7e05008410024de7398010004dd739801001cee7298010004ed7298010006d43198010006e421980100047f769401000c7d76940100057571940100075431940100076421940100157a709401000c7f76140100047d76140100057571140100075431140100076421140100167a761401000579761401001679761401000479761401009d7a74140100177271140100057971140100177171140100367a61140100077331140100075a31140100075831140100077031140100075031140100077321140100076a21140100076821140100077021140100076021140100157a75d0010007d031d0010007e021d00100463e65900100063d6590010007943190010007a42190010005ba709001000738509001003e3e65100100063d6510010007943110010007a421100100073a5010010007385010010004f9761001009d78751001009f3a541001009f385410010007d03110010007e02110010006ba7610010006b9761001009f3b751001009f3875100100073a65100100073965100100079a7310010007997310010007aa7210010007a97210010007b27110010007b17110010006ba61100100073b5110010007395110010007b331100100079a3110010007983110010007b03110010007903110010007b32110010007aa2110010007a82110010007b02110010007a021100100077050c4010007b040c401001cf97684010015787584010007d03184010007e02184010004f77644010005d47344010005e47244010004fb7644010015787544010005b87444010007d03144010007e02144010
  | 1 => 0x91100047d75d911002cbe76d91100063f65d91100063c65d91100063e75d91100063d75d91100047f755911000c7c7559110004df7359110024dc7359110004ef725911001cec7259110004fb7059110004be76191100063f65191100063c651911002e3f751911002e3c7519110044be701911002cbc70191100047e769511002c7c76951100063f649511002e3c64951100047e761511002c7c76151100063f641511002e3c6415110005757115110024de76d8d100065f65d8d100065c65d8d100069f64d8d100069c64d8d100065e54d8d100065c54d8d100047f7558d1000c7c7558d10004bf7458d1002cbc7458d10004ef7258d1001cec7258d10004f77158d10004de7618d100065f6518d100065c6518d100069f6418d100069c6418d100065e5418d100065c5418d10064de7118d10024dc7118d1001cee76d89100066f65d89100066c65d8910006af64d8910006ac64d8910006cf63d8910006cc63d89100066e54d89100066c54d89100047f755891000c7c7558910004bf745891002cbc7458910004df7358910024dc7358910004f77158910004ee76189100066f65189100066c6518910006af6418910006ac6418910006cf6318910006cc63189100066e54189100066c5418910054ee711891001cec71189100047e76d45100063f64d45100063c64d45100065f63d45100065c63d45100066f62d45100066c62d45100057a70d451000c7c76545100053c74545100063f64545100063c64545100065f63545100065c63545100066f62545100066c6254510005787054510004de768c5100065f658c5100665c658c5100069f648c5100069c648c510006cf628c510006cc628c510004de760c5100065f650c51005e5c650c5100069f640c5100069c640c510006cf620c510006cc620c510004ee76885100066f65885100566c6588510006af6488510006ac6488510006cf6388510006cc6388510004ee76085100066f650851004e6c6508510006af6408510006ac6408510006cf6308510006cc63085100047e76941100063f64941100063c64941100065f63941100065c63941100066f62941100066c62941100047e76141100063f64141100063c64141100065f63141100065c63141100066f62141100066c6214110004be76901100063f65901100463c65901100069f63901100069c6390110006af6290110006ac6290110004be76101100063f651011003e3c65101100069f63101100069c6310110006af6210110006ac62101100367865c4110006b864c4110006d46384110006e462841100047d7699410004bf745941002cbc7459410014f8705941000c7f76594100053c74594100063f745941002c7c74594100063c745941002c3c745941000c7f715941000c7d71594100167b705941000678705941000c7
  | 2 => 0x63e74d961002c3e74d96100063d74d96100065e73d96100065d73d96100066e72d96100066d72d96100067571d96100067a70d961000c7e75d92100047d75d9210024de73d9210004dd73d921001cee72d9210004ed72d92100047f755921000c7c75592100047e769521002c7c76952100047e761521002c7c761521002e3e64152100063d641521001cee72d8e10004ed72d8e100065f6598e100065c6598e100265e7598e100265d7598e100269e7498e100269d7498e100065e5498e100065c5498e100047f7558e1000c7c7558e100065f6558e100065c6558e100065f7558e100065c7558e100065e5458e100065c5458e10006d77158e10024de73d8a10004dd73d8a100066f6598a100066c6598a10006ce6398a10006cd6398a1001e6e7598a1001e6d7598a1001eae7498a1001ead7498a100066e5498a100066c5498a100047f7558a1000c7c7558a100066f6558a100066c6558a10006ce6358a10006cd6358a100066f7558a100066c7558a100066e5458a100066c5458a10006e77158a100065e63d46100065d63d46100066e62d46100066d62d46100057a70d46100053c74546100065e63546100065d63546100066e62546100066d6254610005787054610005e672cc6100065f658c6100665c658c610006ce628c610006cd628c6100065f650c61005e5c650c610006ce620c610006cd620c61000757510c61000755510c610006d5630c610005d5760c610006d5760c61000756750c61000755750c61000757650c61000754650c61000796740c61000795740c61000756540c61000754540c610007c6620c610007c5620c610005d673c86100066f65886100566c6588610006ce6388610006cd6388610007c431886100066f650861004e6c6508610006ce6308610006cd6308610007675108610007655108610007c63108610007c43108610006e56208610005e57608610006e57608610007667508610007657508610007676508610007646508610007a67408610007a57408610007665408610007645408610007c66308610007c563086100065e63942100065d63942100066e62942100066d62942100057571942100075431942100076421942100065e63142100065d63142100066e62142100066d62142100057571142100075431142100076421142100063f65902100463c65902100069e63902100069d6390210006ae6290210006ad6290210007943190210007a421902100063f651021003e3c65102100069e63102100069d6310210006ae6210210006ad6210210007943110210007a421102100367865c421000c7e76d951002c7e74d951000c7e70d951000c7c70d9510004bf745951002cbc7459510004df7359510024dc7359510004ef725951001cec7259510034fb70595100047e761951000c7e75d
  | 3 => 0xf63101200069c6310120006b76110120006b46110120006cc6388120006e461881200047f755902000c7c755902002e3e64150200063d64150200065e5498c200065c5498c20004de7198c2001ecc2198c2001cec7258c2001ecc3258c200065e5458c200065c5458c2001ecc7258c20004dc7158c2001ecc2158c2001ecf2058c20004ed76cc820006cd63cc82000c7e75984200047d759842001ee42198420004df7358420024dc73584200065e63d44200065d63d44200053c74544200065e63544200065d6354420005787054420004df768c420004dd768c420024df760c420004dd760c420006ce6388420006cd63884200065e63940200065d63940200065e63140200065d63140200069e63900200069d63900200069e63100200069d6310020004ef7648020005cc7348020006cd6348020005e471480200076a5048020007a8404802002cbe74d9710004bd74d971002c7c74597100067b705971003678705971000c7e75d93100047d75d93100063e65993100063d659931002e3f759931002e3c759931002e9e739931002e9d739931002eae729931002ead72993100047f755931000c7c75593100063e65593100063d65593100063f75593100063c7559310006bb705931002c7f76953100047d769531002e3e64953100063d64953100057a709531002c7f76153100047d761531002e3e64153100063d641531000575711531000c7e75d8f100047d75d8f1002cbe74d8f10004bd74d8f1001cee72d8f10004ed72d8f1000c7e75d8b100047d75d8b1002cbe74d8b10004bd74d8b10024de73d8b10004dd73d8b100063e64d47100063d64d47100053c74547100063e64547100063d64547100057870547100665e658c7100065d658c7100069e648c7100069d648c71005e5e650c7100065d650c7100069e640c7100069d640c7100566e65887100066d6588710006ae6488710006ad648871004e6e65087100066d6508710006ae6408710006ad64087100063e64943100063d64943100063e64143100063d64143100057976143100367976143100b57a74143100073a64143100073964143100057971143100075a31143100075831143100076a21143100076821143100357a75d03100463e65903100063d659031000738509031003e3e65103100063d65103100073a50103100073850103100b5787510310006b964103100b73a54103100b7385410310005b97610310006b976103100b73b75103100b73875103100073a65103100073965103100079a7310310007997310310007aa7210310007a972103100073b51103100073951103100079a3110310007983110310007aa2110310007a8211031002cbe74d9610004bd74d9610024de73d9610004dd73d961001cee72d9610004ed72d96100053e74d961002c7e74d9610
  | 4 => 0x9520004f77159520004f471595200047e761952000c7e75d91200047d75d912002cbe76d91200063f65d91200063c65d91200063e75d91200063d75d91200047f755912000c7c7559120004df7359120024dc7359120004f77159120004f47159120004be76191200063f65191200063c651912002e3f751912002e3c751912002ead72191200047e769512002c7c76951200063f649512002e3c64951200047e761512002c7c76151200063f641512002e3c6415120024de76d8d200065f65d8d200065c65d8d200069f64d8d200069c64d8d200065e54d8d200065c54d8d20004de71d8d200047f7558d2000c7c7558d20004bf7458d2002cbc7458d20004ef7258d20004f77158d20004f47158d20004de7618d200065f6518d200065c6518d200069f6418d200069c6418d200065e5418d200065c5418d20026cd7218d20004de7118d2002eac6490920006cc639092002cec76509200072c5450920006cc6350920005e87050920004ee768c920026cc638c920024ec764c920026cc634c920024de73d8520004dd73d85200067765d85200067465d8520006b764d8520006b464d8520006d763d8520006d463d85200067775d85200067475d85200067654d85200067454d8520006d673d8520006d573d852000c7e75185200047d7518520006776518520006746518520006b76418520006b46418520006d76318520006d46318520006767518520006757518520006765418520006745418520006d77318520006d47318520006e77218520006e64218520006e54218520006e63218520006e532185200047e76d452000c7c76d45200063f64d45200063c64d45200065f63d45200065c63d45200067761d45200067461d45200047e76545200047c76545200053c74545200063f64545200063c64545200065f63545200065c6354520006776154520006746154520005787054520004de768c520004dc768c5200065f658c5200665c658c5200069f648c5200069c648c520006d7618c520006d4618c520004de760c520024dc760c5200065f650c52005e5c650c5200069f640c5200069c640c520006d7610c520006d4610c5200066f65885200566c6588520006af6488520006ac6488520006cf6388520006cc6388520006e461885200066f650852004e6c6508520005ad7408520006af6408520006ac6408520006cf6308520006cc6308520006e761085200047e76941200063f64941200063c64941200065f63941200065c63941200067761941200067461941200047e76141200063f64141200063c64141200065f63141200065c6314120006776114120006746114120004be76901200063f65901200463c65901200069f63901200069c6390120006b76190120006b46190120004be76101200063f651012003e3c65101200069
  | 5 => 0x66f650853004e6c6508530006af6408530006ac6408530006e76108530006e461085300047e76941300063f64941300063c64941300066f62941300066c62941300067761941300067461941300047e76141300063f64141300063c64141300066f62141300066c6214130006776114130006746114130004be76901300063f65901300463c6590130006af6290130006ac6290130006b76190130006b46190130004be76101300063f651013003e3c6510130006af6210130006ac6210130006b76110130006b46110130006cc628c130006d4618c1300047f755903000c7c755903002e3e64150300063d64150300066e54988300066c5498830004ee7198830026cc3198830026cc32588300066e54588300066c5458830004ec7158830026cc3158830026cf3058830004dd768c830006cd628c83000c7e75984300047d7598430026d43198430004ef725843001cec72584300066e62d44300066d62d44300053c74544300066e62544300066d6254430005787054430006ce628c430006cd628c430004ef7688430004ed768843001cef7608430004ed76084300066e62940300066d62940300066e62140300066d6214030006ae6290030006ad6290030006ae6210030006ad6210030004df764c030005cc724c030006cd624c030005d4714c0300075a504c03000798404c03002c7c74597200047f715972001e6c215972002e3f759932002e3c759932002e9e739932002e9d739932001eae729932001eac21993200047f755932000c7c75593200063f75593200063c755932001eac215932002c7f76953200047d769532002e3e64953200063d649532002c7f76153200047d761532002e3e64153200063d641532002eae6450b200072c5450b2001ecc634cb2000c7e75987200047d759872001ee42198720004df7358720024dc735872001ee4215872000c7f76d47200047d76d47200063e64d47200063d64d47200047f76547200047d76547200053c74547200063e64547200063d64547200057870547200665e658c7200065d658c7200069e648c7200069d648c72005e5e650c7200065d650c7200069e640c7200069d640c720006d6610c720006d5610c7200566e65887200066d6588720006ae6488720006ad64887200063e64943200063d64943200063e64143200063d64143200463e65903200063d659032003e3e65103200063d6510320004bf745962002cbc745962000c7e75d92200047d75d92200047f755922000c7c75592200063f641522002e3c6415220006cf630ca2000c7e75986200047d759862002cbe7498620004bd7498620004df7358620024dc73586200053c7454620005787054620006e6618862000c7e76d952002c7e74d95200047d71d9520004bf745952002cbc7459520004df7359520024dc735
  | 6 => 0xd6588730006ae6488730006ad648873004e6e65087300066d6508730006ae6408730006ad6408730006e66108730006e561087300063e64943300063d64943300063e64143300063d64143300463e65903300063d659033003e3e65103300063d6510330004bf745963002cbc745963000c7e75d92300047d75d92300047f755923000c7c75592300063f641523002e3c641523000c7e75986300047d759863002cbe7498630004bd7498630004ef725863001cec72586300053c7454630005787054630006d6618c63000c7e76d953002c7e74d95300047d71d9530004bf745953002cbc7459530004ef725953001cec7259530004f77159530004f471595300047e761953000c7e75d91300047d75d913002cbe76d91300063f65d91300063c65d91300063e75d91300063d75d91300047f755913000c7c7559130004ef725913001cec7259130004f77159130004f47159130004be76191300063f65191300063c651913002e3f751913002e3c751913002e9d73191300047e769513002c7c76951300063f649513002e3c64951300047e761513002c7c76151300063f641513002e3c641513002e9c6490d3002cdc7650d300071c5450d30005d87050d300066f65d89300066c65d8930006af64d8930006ac64d89300066e54d89300066c54d8930004ee71d89300066f65189300066c6518930006af6418930006ac64189300066e54189300066c5418930006ce4318930006cd4318930004ee7118930004de76cc93001ecc62cc93001cdc764c93001ecc624c93001cee72d8530004ed72d85300067765d85300067465d8530006b764d8530006b464d8530006e762d8530006e462d85300067775d85300067475d85300067654d85300067454d8530006e672d8530006e572d853000c7e75185300047d7518530006776518530006746518530006b76418530006b46418530006e76218530006e46218530006767518530006757518530006765418530006745418530006d77318530006d64318530006d54318530006e77218530006e47218530006d73218530006d532185300047e76d453000c7c76d45300063f64d45300063c64d45300066f62d45300066c62d45300067761d45300067461d45300047e76545300047c76545300053c74545300063f64545300063c64545300066f62545300066c62545300067761545300067461545300057870545300065f658c5300665c658c5300069f648c5300069c648c530006cf628c530006cc628c530006d4618c5300065f650c53005e5c650c5300059d740c5300069f640c5300069c640c530006cf620c530006cc620c530006d7610c530004ee7688530004ec76885300066f65885300566c6588530006af6488530006ac6488530006e76188530006e46188530004ee760853001cec7608530
  | 7 => 0xc440005bb704c440005b8704c44002cbe760c440004bd760c44003d3e750c4400053d750c4400059f760c4400069e760c4400059d760c4400069d760c4400049d760c4400071e750c4400071d750c4400cf1f650c4400cf1c650c4400078e620c4400078d620c4400059e710c44000796710c4400071f510c4400071d510c4400059e73c84400059d73c8440005ba70c8440005b970c844003d3e75884400053d7588440005af7688440005ad76884400072e75884400072d75884400c72f65884400c72c65884400078e63884400078d6388440005ae71884400072f51884400072d51884400078e31884400078c31884400059f73484400059c7348440005bb7048440005b8704844002cbe7608440004bd760844003d3e75084400053d7508440005af7608440006ae7608440005ad7608440006ad7608440004ad76084400072e75084400072d75084400bf2f65084400bf2c65084400078e63084400078d6308440005ae7108440007a671084400072f51084400072d51084400078e31084400078c310844003d3e75980400053d759804002e3f659804002e3c65980400069e63980400069d6398040006ae6298040006ad62980400463e75980400063d75980400463f51980400063d51980400069e31980400069c3198040006ae2198040006ac219804002eba70980400073a759804000739759804002f3b659804002f38659804002f9a639804002f99639804002faa629804002fa96298040005ba71980400073b51980400073951980400079a3198040007983198040007aa2198040007a821980400071e63940400071d63940400072e62940400072d62940400053d71940400071e31940400071c31940400072e21940400072c219404003d3e70940400063e60940400073a6094040044bf765404002d3e761404002d3c76140400071e63140400071d63140400072e62140400072d62140400053d71140400071e31140400071c31140400072e21140400072c21140400053e701404003f3a70140400463e60140400073a601404002c7c74597300047f71597300265c315973002e3f759933002e3c75993300269e739933002eae729933002ead72993300269c31993300047f755933000c7c75593300063f75593300063c75593300269c315933002c7f76953300047d769533002e3e64953300063d649533002c7f76153300047d761533002e3e64153300063d641533002e9e6450f300071c5450f3000c7e75987300047d7598730026d43198730004ef725873001cec7258730026d4315873000c7f76d47300047d76d47300063e64d47300063d64d47300047f76547300047d76547300053c74547300063e64547300063d64547300057870547300665e658c7300065d658c7300069e648c7300069d648c7300566e65887300066
  | 8 => 0xcf1c540c440006ce620c440006cd620c440004ef7688440004ed76884400c66f65884400c66c65884400c72e54884400c72c5488440006ce6388440006cd638844001cef7608440004ed76084400be6f65084400be6c65084400bf2e54084400bf2c5408440006ce6308440006cd630844000c7e75980400047d759804002e3e549804002e3c549804002d3e74940400065e63940400065d63940400066e62940400066d629404002c7e761404002c7c761404002d3e74140400065e63140400065d63140400066e62140400066d6214040004bf76500400053f755004003d3c755004003d3e7598c400053d7598c4002d9d7698c400071e7598c400071d7598c4002f1f6598c4002f1c6598c400059e7198c400053f7558c4003d3c7558c4002e3c6558c4002e9c6358c4002d9f7658c400069f7658c400071f7558c400071c7558c4002f1f6558c400069e6558c4002e9c6558c4002f1c6558c4002e1c6558c400059c7158c4002e9f6158c4002cbe7694c40004bd7694c4003d3e75988400053d759884002dad76988400072e75988400072d759884002f2f659884002f2c659884002f8e639884002f8d6398840005ae71988400053f755884003d3c755884002e3c655884002eac625884002daf7658840006af76588400072f75588400072c755884002f2f6558840006ae655884002eac655884002f2c655884002e2c655884002f8e635884002f8d6358840005ac715884002eaf615884002cbe7694840004bd7694840005bb704c840005b8704c8400078d320c840005ba700c840005b9700c84003d3e75984400053d759844002e3c65984400053f755844003d3c75584400059f73584400059c73584400069d6358440005af7258440005ac7258440006ad625844002d3e76d444002d3c76d444003f1e73d444003f1d73d44400071e63d44400071d63d444003f2e72d444003f2d72d44400072e62d44400072d62d44400053e70d444003f3a70d44400053a70d444003f3970d44400053d7594440004bf765444002cbc76544400059f73544400059c7354440005af7254440005ac7254440005bb7054440005b870544400063f765444002d3e765444002d3c76544400063c765444002c3c76544400071f73544400071c73544400071e63544400071d63544400072f72544400072c72544400072e62544400072d625444003d3f715444003f3771544400073661544400073561544400073b70544400053c7054440007387054440005387054440005ae72cc440005ad72cc440005ba70cc440005b970cc44003d3e758c4400053d758c4400059f768c4400059d768c4400071e758c4400071d758c4400d71f658c4400d71c658c4400078e628c4400078d628c4400059e718c4400071f518c4400071d518c440005af724c440005ac724
  | 9 => 0xc31886400059f73486400059c7348640004be7608640004bd76086400453e75086400053d7508640006ae7608640006ad76086400072e75086400072d75086400072e65086400072d6508640007a671086400072f51086400072d51086400078e31086400078c31086400473b50942400053d76942400053d71942400071e31942400071c31942400072e21942400072c219424003cbf76542400053d76142400053d71142400071e31142400071c31142400072e21142400072c21142400473a701424000c7e76d954002c7e74d954002c7c74d95400047d71d9540044bf74595400047e7619540024de73d8540004dd73d854001cee72d8540004ed72d854000c7e75185400047d75185400047e76d454000c7c76d45400047e76545400047c765454002d3c74545400057870545400065f658c5400665c658c5400065f650c54005e5c650c540006d7610c540006d4610c5400066f65885400566c65885400066f650854004e6c6508540006e76108540006e461085400047e76941400047e76141400063f65901400463c659014002cbc745944002d3f75550400265e7598c400265d7598c4002e5e5498c4002e5c5498c40004de7198c400047f7558c4000c7c7558c4002e3c5458c4002e9c4358c400065f7558c400065c7558c400069f5458c4002e5e5458c4002e5c5458c4002e9c5458c4002e1c5458c40004dc7158c4002e9f4158c4003d3e7590c400053d7590c400069d6390c400053f7550c4003d3c7550c4002e3c6550c400269e6350c4001e6e759884001e6d759884002e6e549884002e6c5498840004ee71988400047f755884000c7c755884002e3c545884002eac42588400066f75588400066c7558840006af545884002e6e545884002e6c545884002eac545884002e2c5458840004ec715884002eaf415884003d3e75908400053d7590840006ad62908400053f755084003d3c755084002e3c655084001eae625084000c7e75984400047d759844002e3c54984400047f755844000c7c7558440004df7358440024dc7358440004ef725844001cec725844002c7e76d444002d3e74d444002d3c74d44400065e63d44400065d63d44400066e62d44400066d62d44400057a70d444002c7c765444002d3e745444002d3c74544400065e63544400065d63544400066e62544400066d625444000676615444000675615444000578705444003d3e75904400053d759044002e3c65904400053f755044003d3c75504400059f73504400059c73504400069d6350440005af7250440005ac7250440006ad6250440005bb7050440004df768c440004dd768c4400d65f658c4400d65c658c4400d71e548c4400d71c548c440006ce628c440006cd628c440024df760c440004dd760c4400ce5f650c4400ce5c650c4400cf1e540c440
  | 10 => 0x8640004ef725864001cec725864000c7f76d46400047d76d464002d3e74d46400047f76546400047d765464002d3c745464000578705464002d3f75d064002d3c75d06400059e73d06400059d73d0640005ae72d0640005ad72d06400453e75906400053d75906400763e65906400053f75506400453c75506400059f73506400059c7350640005af7250640005ac7250640005bb70506400453e75106400053d751064006e3e65106400665e658c6400065d658c6400071e548c6400071c548c64005e5e650c6400065d650c6400071e540c6400071c540c6400566e65886400066d65886400072e54886400072c548864004e6e65086400066d65086400072e54086400072c540864002c7d769424002d3e749424002c7d761424002d3e74142400453e75d02400053d75d02400073a50d0240005ba70d96400053d71996400463c65596400463f76596400053f71596400453e75d8e400053d75d8e400063e65d8e40005ba70d8e400069f6398e400063e6558e40005af7258e40005ac7258e400453e7518e400053d7518e40005ae7218e40005ad7218e40005ba7018e40004be7694e40004bd7694e400453e75d8a400053d75d8a400063e65d8a40005ba70d8a40006af6298a400063e6558a400059f7358a400059c7358a400453e7518a400053d7518a400059e7318a400059d7318a40005ba7018a40004be7694a40004bd7694a400078d320ca400453e75d86400053d75d86400059e73d86400059d73d8640005ae72d8640005ad72d8640005ba70d86400453e75986400053d75986400063e65986400059f73586400059c7358640005af7258640005ac72586400453e75186400053d75186400063e6518640005ba70186400453f76d46400053d76d46400471e73d46400471d73d46400472e72d46400472d72d46400053e70d4640004bf7654640004bc76546400059f73546400059c7354640005af7254640005ac7254640005bb7054640005b870546400053f76546400063f76546400043f76546400053d76546400063c76546400071f73546400071c73546400072f72546400072c72546400473771546400073b70546400053c7054640007387054640005387054640005ae72cc640005ad72cc6400453e758c6400053d758c6400071e758c6400071d758c6400071e658c6400071d658c6400071f518c6400071d518c640005af724c640005ac724c640004be760c640004bd760c6400453e750c6400053d750c6400069e760c6400069d760c6400071e750c6400071d750c6400071e650c6400071d650c64000796710c6400071f510c6400071d510c6400059e73c86400059d73c86400453e75886400053d75886400072e75886400072d75886400072e65886400072d65886400072f51886400072d51886400078e31886400078
  | 11 => 0x2c3c74584500065f73584500065c73584500066f72584500066c725845000e77715845000678705845002c7f76d04500055e73d04500055d73d04500056e72d04500056d72d04500057a70d04500057970d045000c7e76904500047d76904500067561904500047f765045000c7c76504500055f73504500055c73504500056f72504500056c72504500067561504500057b705045000578705045000c7e76104500047d761045002e3c64104500056e72cc4500056d72cc4500057a70cc4500057970cc45000c7e768c4500047d768c4500665e768c4500065d768c4500d65e648c45005d5e718c4500065d618c4500675a608c4500056f724c4500056c724c4500057b704c45000578704c45000c7e760c4500047d760c4500053e740c4500053d740c45005e5e760c4500065d760c4500071e740c4500071d740c4500ce5e640c4500655e710c45000756710c4500065d610c45005f5a600c4500055e73c84500055d73c84500057a70c84500057970c845000c7e76884500047d76884500566e76884500066d76884500c66e648845004d6e71884500066d61884500074e31884500074c31884500576a60884500055f73484500055c73484500057b704845000578704845000c7e76084500047d76084500053e74084500053d740845004e6e76084500066d76084500072e74084500072d74084500be6e64084500556e71084500076671084500066d61084500074e31084500074c310845004f6a60084500065e31980500065c31980500066e21980500066c219805000e7a709805002c7c74597400047f715974002e3c405974000c7e75987400047d7598740004df7358740024dc7358740004ef725874001cec725874000c7f76d47400047d76d47400057a70d47400047f76547400047d765474002d3c74547400057870547400665e658c7400065d658c74005e5e650c7400065d650c740006d6610c740006d5610c7400566e65887400066d658874004e6e65087400066d6508740006e66108740006e561087400463f54596400063f74596400463c74596400047f715964000e3e659524000e3c65952400053d769524002e3d76952400053d719524002f3a609524000cbf76552400053d761524002e3d76152400053d711524002e3e601524002f3a60152400063c5458e40004ef7258e4001cec7258e400963e65d0e40005ae72d0e40005ad72d0e400453e7590e400053d7590e40024bf7650e400053f7550e400453c7550e4008e3e6550e400269e6350e400063c5458a40004df7358a40024dc7358a400863e65d0a400059e73d0a400059d73d0a400453e7590a400053d7590a4001cbf7650a400053f7550a400453c7550a4007e3e6550a4001eae6250a4000c7e75986400047d75986400063c5498640004df7358640024dc735
  | 12 => 0xe64192500063d64192500055e73192500055d73192500056e72192500056d72192500057a70192500057a70d8e500053e7418e500053d7418e500056e7218e500056d7218e500057a7018e5002e3e64d0e500056e72d0e500056d72d0e500047e7690e500047d7690e500047f7650e500047c7650e5002e3e6450e500057a70d8a500053e7418a500053d7418a500055e7318a500055d7318a500057a7018a5002e3e64d0a500055e73d0a500055d73d0a500047e7690a500047d7690a500047f7650a500047c7650a5002e3e6450a500074d320ca500053e74d86500053d74d86500055e73d86500055d73d86500056e72d86500056d72d86500057a70d86500367a60986500055f73586500055c73586500056f72586500056c725865002c7c74586500065f73586500065c73586500066f72586500066c72586500057a701865002c7f76d06500055e73d06500055d73d06500056e72d06500056d72d06500047e76906500047d769065002e3e64906500047f76506500047c76506500055f73506500055c73506500056f72506500056c72506500057b70506500057870506500047e76106500047d761065002e3e64106500056e72cc6500056d72cc6500047e768c6500047d768c6500065e768c6500065d768c6500d65e648c6500065d618c6500056f724c6500056c724c6500047e760c6500047d760c6500053e740c6500053d740c6500065e760c6500065d760c6500071e740c6500071d740c6500ce5e640c65000756710c6500065d610c6500055e73c86500055d73c86500047e76886500047d76886500066e76886500066d76886500c66e64886500066d61886500074e31886500074c31886500055f73486500055c73486500047e76086500047d76086500053e74086500053d74086500066e76086500066d76086500072e74086500072d74086500be6e64086500076671086500066d61086500074e31086500074c31086500463e75d91500463f51d91500463c50d915002e3f751915002e3c751915003e3f511915003e3c50191500063f649515002e3c6495150024de73d8550004dd73d855001cee72d8550004ed72d85500053c74545500063f64545500063c64545500067761545500057870545500069f648c5500069c648c5500069f640c5500069c640c550006d7610c550006d4610c550006af6488550006ac6488550006af6408550006ac6408550006e76108550006e461085500063f64941500063c649415002e3c64d0c500056e72d0c500056d72d0c5000c7e7690c500047d7690c500047f7650c5000c7c7650c5002e3c64d08500055e73d08500055d73d085000c7e76908500047d76908500047f765085000c7c76508500074d320c8500057a700c85000579700c8500063f745845002c7c74584500063c7458450
  | 13 => 0x50210056d71150210bf6571150210056571150210056e7015021006ad6498c2101ecc6358c21005ae7494c21005ad7494c2101cee76d0c21004ed76d0c210bf2c54d0c2104d6e7590c210056d7590c210056f7550c2104d6c7550c210072c5450c21005e77150c21005e47150c2104d6e75984210056d75984210566e65984210066d6598421006ae6498421006ad64984210566e75984210066d75984210c66e54984210c66c549842101ee6719842100766759842100765759842101f66659842101f65659842101fa6649842101fa56498421007665498421007645498421005e670984210056d76d442104e6d76d44210046d76d44210bd6e74d44210072e64d44210072d64d442104f4e73d442104f4d73d44210566e61d44210076661d44210056e70d44210056d7594421054ef7654421005af7454421005ac7454421005cf7354421005cc7354421005eb7054421005e870544210056f76544210066f76544210046f76544210072f74544210bd6c74544210072c74544210052c74544210072e64544210072d64544210074f73544210074c735442104d6f715442104f6771544210066e61544210076661544210076b70544210056c7054421007687054421005687054421004ed76d04210bd6f75d04210bd6c75d0421005ce73d0421005cd73d042104d6e75904210056d75904210072c5490421007655190421004ef76504210056f755042104d6c7550421005cf7350421005cc7350421007655150421005eb7050421005e8705042104d6e75104210056d75104210bf2c5410421004ed76cc4210076551cc42104d6e758c4210056d758c4210074e758c4210074d758c4210074e658c4210074d658c4210078e648c4210078d648c4210074e548c4210074c548c421005ce718c421006ce618c421007c6618c4210074f518c4210074d518c421004ef764c42104d6e750c4210056d750c421005ae740c421005ad740c42100765510c4210074e750c4210074d750c4210074e650c4210074d650c4210078e740c4210078d740c4210078e640c4210078d640c4210074e540c4210074c540c421005ce710c421007c6710c421006ce610c421007c6610c4210074f510c421007c6510c4210074d510c421007c5510c42100745510c421007c7410c421007c4410c4210056f755802104d6c7558021005af7458021005ac7458021006ad6458021005cf7358021005cc735802102e3e64952500063d649525000579709525002c7f76552500053e7494e500053d7494e500247f7654e500053e7494a500053d7494a5001c7f7654a50004df7358650024dc7358650004ef725865001cec72586500053f74546500053c74546500055f73546500055c73546500056f72546500056c72546500067561546500057b70546500057a70d925002e3
  | 14 => 0x74e540c6210074c540c621007c6710c6210074f510c6210074d510c6210556e75d82210056d75d8221005ae74d8221005ad74d8221005ce73d8221005cd73d8221005ce7398221005cd73982210056f75582210556c7558221005af7458221005ac74582210556e75182210056d7518221004bf745952102cbc7459521004df7359521024dc7359521054ef7259521004fb7059521004f8705952100c7e75d91210047d75d91210047f755912100c7c7559121004df7359121024dc7359121004ef7259121004fb7059121004f870591210063f641512102e3c6415121024de76d8d210065e54d8d210065c54d8d21004ef7258d21004de7618d210065e5418d210065c5418d210065f63d45210065c63d45210053c74545210065f63545210065c6354521005787054521004de768c521004de760c521006cf6388521006cc638852100c7e75d81210047d75d812102cbe74d8121004bd74d812101cec725942102c7c745942104e6f725942101e6c72594210047c705942102e3f759902102e3c759902102e9e739902102e9d739902101eae7299021004be70990210047f755902100c7c755902101cec72590210063f75590210063c755902101eac725902101eac3259021004bc705902101eaf205902102c7f76950210047d769502102e3e64950210063d649502102c7f76150210047d761502102e3e64150210063d641502100575711502101cec7258c2101ecc3258c2100e6e6554821006ad64d08210bf2c54d0821005ce73d0821005cd73d08210056f755082104d6c755082102eae64508210072c5450821006ad64cc82101ecc634c82100c7e75984210047d75984210047d76d44210063e64d44210063d64d44210047f76544210053c74544210063e64544210063d64544210057870544210665e658c4210065d658c4210069e648c4210069d648c42105e5e650c4210065d650c4210069e640c4210069d640c42100755510c421004ef7648421005cf7348421005cc73484210047f755802100c7c7558021004bf745802102cbc7458021004df7358021024dc735802101d6d76994210bd6e74994210056e709942101d6f765942104e6f76594210bd6c74594210056c7059421005ce7399021005cd739902101dad76990210bf2f75990210bf2c759902101f2e659902101f2d65990210078e73990210078d7399021005ae70990210056f755902104d6c755902101daf7659021006af76590210072f75590210072c755902101f2e655902101f2d655902101eac6359021005ac705902101eaf605902104f2f54950210bd6f76950210056d76950210bd6e74950210bf2e64950210072d64950210056d71950210056e70950210bd6f76150210056d76150210bd6e74150210bf2e74150210bf2e64150210072d64150210bf66711
  | 15 => 0x5510c7210047f755832100c7c7558321004bf745832102cbc7458321004bf745962102cbc74596210053c74596210063f745962102c7c74596210063c745962102c3c74596210066f72596210566c72596210047c705962100c7e75d92210047d75d92210047f755922100c7c755922102c7f76952210047d769522102c7f76152210047d76152210063f641522102e3c641522100c7e75d8e210047d75d8e2100e6e6594a21005ae7494a21005ad7494a2100cef7654a210c72c54d0a21005ce73d0a21005cd73d0a210556e7590a210056d7590a2102cef7650a210056f7550a210556c7550a210072c5450a21024ef764ca21026ce634ca21006cf630ca210053c74546210057870546210665e658c6210065d658c62105e5e650c6210065d650c621005ce73c8621005cd73c8621024de7398221004dd73982210047f755822100c7c7558221004bf745822102cbc7458221005e671d96210c56e74996210056e7099621005af7459621005ac74596210566f76596210072f74596210c56c74596210072c74596210052c74596210056c70596210556e75d92210056d75d9221005e671d92210056f75592210556c75592210556e75192210056d7519221005ce7319221005cd7319221005e671192210572f54952210c56f76952210056d76952210056d71952210056e70952210c56f76152210056d76152210c72e74152210072f64152210c72c64152210056d71152210056e70152210556e75d8e210056d75d8e21005e671d8e21006cf6398e210556e7518e210056d7518e21005ae7418e21005ad7418e21005e67118e21005ae7494e21005ad7494e21004ee76d0e21004ed76d0e210c72c54d0e210556e7590e210056d7590e210056f7550e210556c7550e210072c5450e210056d76d46210566d76d46210c56e74d46210574e73d46210574d73d46210056e70d462104cef7654621005af7454621005ac7454621005cf7354621005cc7354621005eb7054621005e870546210056f76546210066f76546210072f74546210c56c74546210072c74546210052c74546210074f73546210074c73546210576771546210076b70546210056c70546210076870546210056870546210c56f75d06210c56c75d0621005ce73d0621005cd73d06210556e75906210056d75906210072c54906210056f75506210556c7550621005cf7350621005cc7350621005eb7050621005e870506210556e75106210056d75106210c72c54106210556e758c6210056d758c6210074e758c6210074d758c6210074e658c6210074d658c6210074e548c6210074c548c6210074f518c6210074d518c6210556e750c6210056d750c621005ae740c621005ad740c6210074e750c6210074d750c6210074e650c6210074d650c6210078e740c6210078d740c621
  | 16 => 0xc431005cc724c4310047f755803100c7c7558031004bf745803102cbc7458031004ef725803101cec72580310255d76994310cd5e74994310055e70994310255f765943105e5f76594310cd5c74594310055c7059431005ce7299031005cd72990310259d76990310cf1f75990310cf1c75990310271e65990310271d65990310078e72990310078d72990310059e70990310055f755903105d5c75590310259f76590310069f76590310071f75590310071c75590310271e65590310271d65590310269c62590310059c70590310269f605903105f1f54950310cd5f76950310055d76950310cd5e74950310cf1e64950310071d64950310055d71950310055e70950310cd5f76150310055d76150310cd5e74150310cf1e74150310cf1e64150310071d64150310cf5671150310055d71150310cf5571150310055571150310055e70150310069d6498831026cc62588310059e74948310059d7494831024de76d0831004dd76d08310cf1c54d083105d5e75908310055d75908310055f755083105d5c75508310071c5450831005d77150831005d4715083105d5e75984310055d75984310665e65984310065d65984310069e64984310069d64984310665e75984310065d75984310d65e54984310d65c5498431026d67198431007567598431007557598431027566598431027556598431027966498431027956498431007565498431007545498431005d670984310055d76d443105e5d76d44310045d76d44310cd5e74d44310071e64d44310071d64d443105f4e72d443105f4d72d44310665e61d44310075661d44310055e70d44310055d7594431064df76544310059f74544310059c7454431005cf7254431005cc7254431005db7054431005d870544310055f76544310065f76544310045f76544310071f74544310cd5c74544310071c74544310051c74544310071e64544310071d64544310074f72544310074c725443105d5f715443105f5771544310065e61544310075661544310075b70544310055c7054431007587054431005587054431004dd76d04310cd5f75d04310cd5c75d0431005ce72d0431005cd72d043105d5e75904310055d75904310071c5490431007555190431004df76504310055f755043105d5c7550431005cf7250431005cc7250431007555150431005db7050431005d8705043105d5e75104310055d75104310cf1c54104310055f755803105d5c75580310059f74580310059c74580310069d6458031005cf7258031005cc72580310047f755932100c7c755932102e3e64153210063d64153210057571153210065e5498f210065c5498f2101ecc2198f210065e5458f210065c5458f2101ecc2158f210065e63d47210065d63d47210053c74547210065e63547210065d63547210057870547210075
  | 17 => 0x55d76952310055d71952310055e70952310d55f76152310055d76152310d71e74152310071f64152310d71c64152310055d71152310055e70152310655e75d8a310055d75d8a31005d671d8a31006cf6298a310655e7518a310055d7518a310059e7418a310059d7418a31005d67118a310059e7494a310059d7494a31004de76d0a31004dd76d0a310d71c54d0a310655e7590a310055d7590a310055f7550a310655c7550a310071c5450a310055d76d46310665d76d46310d55e74d46310674e72d46310674d72d46310055e70d463105cdf76546310059f74546310059c7454631005cf7254631005cc7254631005db7054631005d870546310055f76546310065f76546310071f74546310d55c74546310071c74546310051c74546310074f72546310074c72546310675771546310075b70546310055c70546310075870546310055870546310d55f75d06310d55c75d0631005ce72d0631005cd72d06310655e75906310055d75906310071c54906310055f75506310655c7550631005cf7250631005cc7250631005db7050631005d870506310655e75106310055d75106310d71c54106310655e75d82310055d75d82310059e74d82310059d74d8231005ce72d8231005cd72d8231005ce7298231005cd72982310055f75582310655c75582310059f74582310059c74582310655e75182310055d7518231004bf745953102cbc7459531064df7359531004ef725953101cec7259531004fb7059531004f8705953100c7e75d91310047d75d91310047f755913100c7c7559131004df7359131004ef725913101cec7259131004fb7059131004f870591310063f641513102e3c64151310066e54d89310066c54d89310066e54189310066c54189310066f62d45310066c62d45310053c74545310066f62545310066c6254531005787054531006cf628c531006cc628c53100c7e75d81310047d75d813102cbe74d8131004bd74d8131024dc735943102c7c745943105e5f73594310265c73594310047c705943102e3f759903102e3c75990310269e739903102eae729903102ead7299031004be70990310047f755903100c7c7559031024dc73590310063f75590310063c75590310269c73590310269c3259031004bc70590310269f305903102c7f76950310047d769503102e3e64950310063d649503102c7f76150310047d761503102e3e64150310063d641503100575711503100e5e6554c310069d64d0c310cf1c54d0c31005ce72d0c31005cd72d0c310055f7550c3105d5c7550c3102e9e6450c310071c5450c31026cc32588310069d648c83100c7e75984310047d75984310047d76d44310063e64d44310063d64d44310047f76544310053c74544310063e64544310063d6454431005787054431004df764c431005cf724
  | 18 => 0xc63189410be6e54189410be6c54189410863c65d09410059d73d094101eac62d094101cbc765094107e3c655094101eac625094102c7e76d454102c7c76d454102d3e74d45410065f63d45410065c63d45410066f62d45410066c62d454102c7c765454102d3c74545410065f63545410065c63545410066f62545410066c62545410057870545410763c659054100c7e75d81410047d75d81410067b65d81410067865d8141006db63d8141006d863d8141006eb62d8141006e862d81410067a75d81410067975d81410b67a54d81410b67854d81410067b51d81410067951d81410067b6518141006786518141006db6318141006d86318141006eb6218141006e862181410067b7518141006787518141006bb741814109e7a541814109e785418141006bb4318141006b94318141006bb4218141006b942181410067b5118141006795118141006ba411814102cbc745944106e3f745944102c7e745944102c7c745944102e3c745944102c3c74594410047c705944102e3c405944102e3c5458c4102e3c545884100c7e75984410047d759844102e3c54984410047d76d444102d3c74d44410047f765444102d3c7454441005787054441004bf765044106d3c7550441007355150441005b8705044102e3c549804102eb840980410047f755804100c7c75580410047f755933100c7c755933102e3e64153310063d64153310057571153310066e5498b310066c5498b31026cc3198b310066e5458b310066c5458b31026cc3158b310066e62d47310066d62d47310053c74547310066e62547310066d62547310057870547310047f755833100c7c7558331004bf745833102cbc7458331004bf745963102cbc74596310053c74596310063f745963102c7c74596310063c745963102c3c74596310065f73596310665c73596310047c705963100c7e75d92310047d75d92310047f755923100c7c755923102c7f76952310047d769523102c7f76152310047d76152310063f641523102e3c641523100e5e6594e310059e7494e310059d7494e3100cdf7654e310d71c54d0e31005ce72d0e31005cd72d0e310655e7590e310055d7590e3102cdf7650e310055f7550e310655c7550e310071c5450e3101cdf764ca3101ece624ca310053c7454631005787054631005ce72cc631005cd72cc63101cee7298231004ed72982310047f755823100c7c7558231004bf745823102cbc7458231005d671d96310d55e74996310055e70996310059f74596310059c74596310665f76596310071f74596310d55c74596310071c74596310051c74596310055c70596310655e75d92310055d75d9231005d671d92310055f75592310655c75592310655e75192310055d7519231005ce7219231005cd7219231005d671192310671f54952310d55f7695231
  | 19 => 0x81510065f63181510065c63181510066f62181510066c62181510067960181510063f741815102c7e74181510063c74181510057a76181510067a76181510073b74181510073874181510067b64181510073b64181510063b64181510067a64181510067964181510067864181510073864181510063864181510067b63181510075b63181510065b63181510067a63181510067963181510067863181510075863181510065863181510067b62181510076b62181510066b62181510067a62181510067962181510067862181510076862181510066862181510167b61181510177361181510067b74181510063b74181510067a74181510067974181510067874181510063874181510067b73181510067a73181510067973181510067873181510067b43181510067a43181510067943181510067843181510067b72181510067a72181510067972181510067872181510067b42181510067a42181510067942181510067842181510067b32181510067a32181510067932181510067832181510167b71181510265e7598f410265d7598f4102e5e5498f4102e5c5498f4102e9c4098f410047f7558f4100c7c7558f410065f7558f410065c7558f4102e5e5458f4102e5c5458f4102e9c4058f4102e3c6550f410269e6350f4101e6e7598b4101e6d7598b4102e6e5498b4102e6c5498b4102eac4098b410047f7558b4100c7c7558b410066f7558b410066c7558b4102e6e5458b4102e6c5458b4102eac4058b4102e3c6550b4101eae6250b4102d3e74d47410065e63d47410065d63d47410066e62d47410066d62d474102d3c74547410065e63547410065d63547410066e62547410066d625474100578705474100c7e75983410047d759834102eb840983410047f755834100c7c755834102eb840583410763f54596410063f74596410763c74596410047c70596410053d761524102e3d76152410053d711524102e3e611524102f3661152410053e70152410063c5458e41004ef7258e4101cec7258e410063c5458a41004df7358a41024dc7358a4102d3c745464100578705464102d3c75d06410073551d06410063c5498241024de7398241004dd739824101cee7298241004ed72982410047f755824100c7c755824100c7e76d95410047e70d9541074bf7459541004df7359541024dc7359541004ef725954101cec7259541004fb7059541004f870595410047e76195410065f65d8d410065c65d8d410d65e54d8d410d65c54d8d410065f6518d410065c6518d410ce5e5418d410ce5c5418d410963c65d0d410269c63d0d41005ad72d0d41024bc7650d4108e3c6550d410269c6350d410066f65d89410066c65d8941006cf63d8941006cc63d89410c66e54d89410c66c54d89410066f65189410066c6518941006cf6318941006c
  | 20 => 0x578705915102e3e64191510063d64191510053e76191510063e761915106e3f611915106f3761191510053e701915102e3f731915102e3e731915102e3d731915102e3c731915102e3f721915102e3e721915102e3d721915102e3c721915102e3f711915102e3d711915102e3f701915102e3e70191510043e701915102e3d701915102e3c70191510063c64d8d510071f64d8d510065e64d8d510065c64d8d510071c64d8d510061c64d8d510665f61d8d510675761d8d510053e7498d510053d7498d510063c6498d510055e7398d510065f6398d510056e7298d510056d7298d51005757198d510057a7098d51005797098d510053f7458d510053c7458d510063c6458d510056f7258d510056c7258d51005777158d510057b7058d51005787058d510063c6418d510065d6318d510055e7618d510065e7618d510071f6418d510065e6418d510065c6418d510071c6418d510061c6418d5105e5f6118d5105f576118d5102e3c64d0d510056e72d0d510056d72d0d510057671d0d510057571d0d510047e7690d510047d7690d5102e3c6490d510047f7650d510047c7650d5102e3c6450d5102e3c6410d510063c64d89510072f64d89510066e64d89510066c64d89510072c64d89510062c64d89510074f63d89510074c63d89510566f61d89510576761d89510053e74989510053d74989510063c64989510055e73989510055d73989510056e72989510066f62989510057571989510057a70989510057970989510053f74589510053c74589510063c64589510055f73589510055c73589510057771589510057b70589510057870589510063c64189510066d62189510056e76189510066e76189510072f64189510066e64189510066c64189510072c64189510062c64189510074f63189510074c631895104e6f611895104f67611895102e3c64d09510055e73d09510055d73d09510057671d09510057571d09510047e76909510047d769095102e3c64909510047f76509510047c765095102e3c645095102e3c64109510063c64cc9510063c648c9510063c644c95100577714c95100574714c9510063c640c9510074d320c9510053e74d81510053d74d81510063c64d81510073a74d81510073974d81510073b64d81510067a64d81510067864d81510073864d81510063864d81510075b63d81510075863d81510076b62d81510076862d81510367b61d81510377361d81510053e74981510053d74981510063f64981510063c64981510055e73981510055d73981510065f63981510065c63981510056e72981510056d72981510066f62981510066c62981510057a70981510067b60981510053f74581510053c74581510063c64581510055f73581510055c73581510056f72581510056c72581510063f64181510063c641
  | 21 => 0xe75d81320047d75d813202cbe74d8132004bd74d81320047f755903200c7c755903202e3e64150320063d64150320071c5450c320072c545083201dcf764c832006cf764c832005cf744c832005cd744c8320074e544c8320074c544c832005cc714c832005cc704c83200c7e75984320047d7598432006cd3298432026d4319843201ee421984320047f755803200c7c7558032004bf745803202cbc7458032006cd3258032004f77158032004f47158032026d8305803201ee8205803202e3c64d0f510056e72d0f510056d72d0f5100c7e7690f510047d7690f510047f7650f5100c7c7650f5102e3c64d0b510055e73d0b510055d73d0b5100c7e7690b510047d7690b510047f7650b5100c7c7650b510074d320cb5102c7e749835100e7a709835100e77715965102e3e64952510063d6495251005757195251004bf745825102cbc74582510763e75d9151004be70d91510763c50d915102e3f751915102e3e751915102e3c751915106e3f531915106e3c531915106e3f521915106e3c521915106e3c5119151004be701915106e3f501915106e3c50191510063f649515102e3c649515102c7c765515102e3c64551510069f64d8d510069c64d8d510665e75d8d510065e54d8d510665c54d8d510665c50d8d510069f6418d510069c6418d510265e7518d510065e5418d5105e5c5418d5105e5c5018d510053e7494d510053d7494d510063c6494d510065f6394d510247c7654d510063c6454d510265c6354d51006af64d8951006ac64d8951006cf63d8951006cc63d89510566e75d89510066e54d89510566c54d89510566c50d8951006af6418951006ac6418951006cf6318951006cc631895101e6e75189510066e541895104e6c541895104e6c50189510053e74949510053d74949510063c64949510066f629495101c7c76549510063c645495101e6c62549510063c649455102cbe74d8151004bd74d8151006bb64d8151006b864d8151006db63d8151006d863d8151006eb62d8151006e862d81510367a75d8151006ba74d8151006b974d81510067a54d81510367854d8151006bb6418151006b86418151006db6318151006d86318151006eb6218151006e862181510067b75181510167a7518151006bb7418151006b874181510167b54181510067a54181510067954181510167854181510167b53181510067a53181510067953181510167853181510167b52181510067a52181510067952181510167852181510067a51181510167851181510763f61d91510773761d91510053e70d91510053e74991510063f64991510055e73991510055d73991510056e72991510056d72991510057571991510057a70991510057970991510055f73591510055c73591510056f72591510056c72591510057771591510057b7059151
  | 22 => 0x51430063c54d894301cee72d8543004ed72d854300c7e75185430047d75185430063c541854300c7e75d81430047d75d81430063c541814301cee7218143004ed721814300c7e75984430047d7598443026d43198443004ef725844301cec725844302eb840980430047f755804300c7c755804302e3f759925202e3c759925201e3f529925201e3d52992520863f519925201eac2199252004be70992520863c509925207e3c755925207e3f515925201eac2159252004bc705925207e3c505925202e3e64952520063d64952520056d729525201ee42198652004df7358652024dc735865201cec7258652004bf745825202cbc745825201c7e76951520063f649515202e3c6495152024de73d8552004dd73d855202cbe74d8152004bd74d815201cbc745974202e5e5498f4202e5c5498f4202ece4298f4202ecd4298f42004de7198f4202e9c4098f4202e3c5458f420069f5458f4202e5e5458f4202e5c5458f4202e9c5458f4202e1c5458f42004dc7158f4202e9f4158f4202e9c4058f4200c7e75987420047d759874201cbe749874202e3c5498742004df7358742024dc735874202e3c549834202eb840983420047f755834200c7c755834201cbc74583420047f715964201e6c21596420047c705964201cec7258e4201ecc3258e4200c7e75986420047d759864201ee42198642004df7358642024dc735864201cec725864201cee72982420047f755824200c7c755824201cbd74d954207e3f54d954200c7e76d954207e3e74d95420063d74d95420047d71d95420047e70d95420047e761954202d3c74195420053e761514202e3e761514202e3f621514202f2f62151420053d71151420053e70151420063c54d8d42024de73d8542004dd73d854200c7e75185420047d75185420063c541854200c7e75d81420047d75d81420063c5418142024de7318142004dd731814200c7e75984420047d759844201ee42198442004df7358442024dc735844202eb840980420047f755804200c7c75580420047f755933200c7c755933202e3e64153320063d641533202cef7650b320072c5450b3200c7e75987320047d7598732026d4319873201cdc735873201cde73983320047f755833200c7c7558332004bf745833202cbc74583320047f755923200c7c755923202e3e64152320063d641523201ecc3258e3202cdf7650e320071c5450e3200c7e75986320047d759863201ee4219863201cec725863201cee72982320047f755823200c7c7558232004bf745823202cbc745823202cbe74d9532004bd74d953200c7e75d91320047d75d91320047f755913200c7c7559132004f77159132004f47159132004fb7059132004f8705913202e3e64151320063d641513200c7e75185320047d751853202cbe7418532004bd741853200c7
  | 23 => 0x1000400000900e80000060080028004008000003000801e00900300780000000000000002000000000c0060000060000004000000000802c000001801400400000000100000040000050002001000800400000000000040000000000000000000001801000c00200180140580020028000006000006001400e00d00000080080050000008000001000802802e001000006c0000030008000002005001000800c00002e3c5458e5402e3c5458a5402e3c5498654004df7358654024dc7358654004ef725865401cec72586540463f549825402e3c549825402eb8409825402cbc745825402c7c74586540065f73586540065c73586540066f72586540066c725865402e77715865402e77415865402e7441586540047c705865402e3c405865402c7e749825402e3c74982540047d719825402e7a709825402e7b409825402e3c409825402e78409825402e384098254024de73d8554004dd73d855401cee72d8554004ed72d85540065f73584540065c735845402e3f43584540066f72584540066c725845402e3f425845402e77715845402e77415845402e3c415845402e74415845402e3441584540067b70584540047c705845400678705845400478705845402e3c405845402e3c749805402e3f439805402e3f42980540047d719805402e3c419805402e7a709805402e7b409805402e3c409805402e78409805402e38409805402e3f759925302e3c75992530263f53992530263d53992530963f51992530269c3199253004be70992530963c509925308e3c755925308e3f51592530269c3159253004bc705925308e3c505925302e3e64952530063d64952530055d7395253026d43198653024dc7358653004ef725865301cec7258653004bf745825302cbc74582530247e76951530063f649515302e3c649515301cee72d8553004ed72d855302cbe74d8153004bd74d8153024bc745974302e6e5498b4302e6c5498b4302ece4398b4302ecd4398b43004ee7198b4302eac4098b4302e3c5458b43006af5458b4302e6e5458b4302e6c5458b4302eac5458b4302e2c5458b43004ec7158b4302eaf4158b4302eac4058b4300c7e75987430047d7598743024be749874302e3c5498743004ef725874301cec725874302e3c549834302eb840983430047f755834300c7c7558343024bc74583430047f71596430265c31596430047c7059643024dc7358a43026cc3258a4300c7e75986430047d7598643026d43198643024dc7358643004ef725864301cec7258643024de73982430047f755824300c7c7558243024bd74d954308e3f54d954300c7e76d954308e3e74d95430063d74d95430047d71d95430047e70d95430047e761954302d3c74195430053e761514302e3e761514302e3f631514302f1f63151430053d71151430053e701
  | 24 => 0x8000000000800e00100080040100050008014002003000000c0000050000014002002001802c000000000001c008012009800000000a007800c02e01f000800c026002000001c000001006801c002000000800c014012000000000000300000dc00c002003002c02400700400000000120088000012002002000000200000080180320040008054002000001800400600500000000020020008014008023000000800000800000100240020048008018000005802800600300000080100000028004006000002006800200400000140000000000004000000000002c00200c0000000006005000800400c003000800000e0000050078020001000000c00000000100080000050020000006005000000000200000080380000010040000002001000000400e0040008000008006004800000a0080018004000006003800002a000000800000400100180080000040000060002001000800002e00300000080000000000044002009000800402400600a001800a0000000000016004028002400200c0018000000017001800400600300280000000000058000008000008800400200100500140220000038000008002004800001200300000080020050060014008004001800801a0020010000002007000800400c001000002000a00200280000040000000000004000001000000800a0008000002000007800801e00c001001402a0050028008010002000000c00001100100100060000040020000000003002000000000a800400e0030010008002000001800c02c003002800000200000400080000030080030000002000000c0160000008008004002000800800c015000008001c00800200040000040030004000006003001400200200700000060070038010000005005004000000100000000000020028040000000000809800c0030018008002004001000c0460000008040000004000801c008000000804400000100780180060050008020002010003800000e0000008028006000000801c00600400300080040040008000026000001801c080000000800800c00000000200060290010018000018002801000e001003800c006009000000c01c00000080600280000000004002003000801c002000000000000800900000000020000000000004002000000801e001000000001000100080080000000008020040006000800000c002000000000c000000800000a0010000008002004004800001200900000000000040000014008001000801000a0040008004006005000000000600c002802c00600000080000020020050000004000000002800200000080280180060020014004000001800400200100400300040070008028000002004000800a000002000401200900300180000010060020008001000000000000000a00040020040
  | 25 => 0x1b580007b00000000000014001800c0080000010008000003000000800600200000300000000000004008007005800800a0020018000000001000000c004002002000000a0080000014018005002000000c000000000000e006002000002200000180000000030078000016000002801401400000100000040000008028002006001000c00200b003800403601400000340000020010008020000000000000a0030000010004002000005c012003000001c000000000000c00200a0058000018000006800c02800400100040020000010054000000000001c000000003800401000700000000000230050038002000001001000a005003800800a0010008020010003001800000800e00100000020000130020000002006001800200c0008018000001002001800000000780080000020030000000007000004400e000003800001c00100c800400000f0010018002003000004800600500000100060050008020002009007800003000b000005c0020060058000036000000001400000300000180020050010000004000000000001000100000240000000008000002002000800000000000680240000000010000008007001001400c00600000040000000010074000005004803803c01800180080100070018018018005000002c00800400100100040000008008004001000000000000000280000300000010000010007001000800000d002800c0060020000008000000000000400600a003000c008004008801c00000000700080020000010004000000000000800800a000000400000700200000000020000000000000002001400200400480240080030018018002002001002800800d00880000060010020058004003000800c00200d00380080040000018024012000001000001200000000140000030008010004003000800000c01a004800000600b000800401c020001000c000005000800001e00000280a00060010020000002002001800800c000000800000a0010020000002004004801c00c002005800c03800100000040000010008008002000001000800c000001801400a00300000000040010000034006001001000800e00300000080160130048000000000000000000000c000000800200000000000000010000020000002007000001203b002800001e016000002000000400080000060010020058000016004000c03200400000000040000000018008005000001c002004002000401400300280040040030010014006000000002000200100080280020080000008002002000002c00a006000000000a0090040008000001000000001000000000300020030008000000007000800400000100080200040000008000008004000000c010002001800400000d00480000060000038004000008000804801e0000000004
  | 26 => 0xb3c1586f960000c081f00004de3161e564ca0690001be665624328b8d5ec38000155526a47a22b80000000002a2ba95b980002149c90aa863f4ea0ce155299e755a99cdb233c3ca3d3c752355097100548a6c14ea891000073b1473f2dda8586000061c0002726e3b30cbac29577ba8c181058d3e826104a21d5256bc29b3c6407520575bde0006f639d41240006e2336c4d2205104a1540008821538000cc2e8732e800027e5a40003bade5200000000013e4d145530001396cd23bb0ce800000013bb3c56da00008e00000000000001dd4cda0000002dc48eeda143e0000000abd0001658ccc2110003894a001910001ab80008b8000000000c000291000084c0000002b440ba3a2085b89c5e8718000291dbf049228a8e1577eeb108a351400075969815780000003ef80006489c55262b2dee2c6a0000001b0e2d053a0f756fa00038f03c81228bf53dbac14c2bf407ea3a00009a54ca2d040000007d800000000000000000000000744000000000054a0000164cf2000000000000000019c4dc8000000239d61e00052fbc5c000ba478c3aa15806261cb33e5bb87f1000000000069b0001b3d9224c80000001930b3275e00014883c34ee00010dea4a0000f2842c000000290478a95b05b8001ee4c37163917984498622100005528c17969d48000a845868001e5000056f8fc87960000c33b1c0004360001c309bed2d43d823c68e2185b50535f1e64b000000087294f5e113b942a91330c0865e8858730a0001ae09d80001024000000000276598c5350000da16f81b57199f6400071a44b00cc8e6b8d5bb800000048f0000001ab08df11a9e8d24a3155f414ed85e2ce7e40000b800003ab8c24a629df6aa800000000018529b40000000000000000a0224a975045007700000017be0001e702b0606000000058494c0352b10000d00f107d42a4057427948000019520006541ed9f38e7d00000005b40000001af8000000360098c20e7880002965d8c00033a1e607aa0000002dd883400000027310822c17dd00000000005f82d88bba00000000000000000002c1c00000069789e8ae4d4600490540cc0000003a056100002f22c19a84f477bf0000000b490a203ed1160af000246069265412f9a7dd740007b31c5cb86d2b11b2330000bb900039440007cf2562dd1e9000068f00003524ea26da29c000aad05a14a400000060a0000ab64f82ca80018cc85400000000002260002de125c30d6899920ca66126a70000a98c9f499a7b83f053600000000009fb60aad947b2b5507b8c0535020821b80012ae0000621bd58425fe4afb590eeece8417261ce4e9be7780c300000002a881e80009c26d80000000ae719ba78c17832524d8001c9a6830000001b520000001769d5833b71e8000cca8da0003980586e8d58f8d04d3cd4b000325092e
  | 27 => 0x200000021459bc00073f88780000006d01d1508c4580619a5534efab16fa058000ec100025500840000000000000f9d23dac90e820002ff80004cae732090000000e070002cb0b4ade800005e56146002303994898000359a2f17140000003d140005044e215280c837e0003afc00042a0c009c55ea0000d62e7c0ca16a412281c00001900030480000003cd3a5cc72f4d0788000d965734a200015d800061a8001fae8810e13f81bb042461d000160203a0450000aee0005400000f8e75300013dd2ecb3c00000017f200014b8000000f2c4cebc85706e8c7188001db426d7b7a8ac0006d47072f55920e7902e09f099200067c03bc6860004518001be4d8300000000002fa4848565866d530002074000d850000bbc00000000000017986fb00000000000002e9000000099f40792600000000000000e9e12500012cdb1aa8310900009b24cf62cae78bb000027480000000000000000000000225000000000000000011343520000000000beb224000185400012e9cfc2109a90001630cf2d84122afb06dc1037aa99f82121663b680f8d600880000000c660000000000000b3b5b01c14afe00069d32180000005f91450f60000000000118c00000000008be7dc46c38a00000002488000972b7a00012749c092141e800159492c00019a00000000002a3c28ed742c70001106c4200000016dc00067100000000003ed94b9da0000075b4d00b6b721d59bb0000c7800033dd862503000000036e9640000000258000236a3880006bc4c40d854d424008800003ec0000001838000b5e000000000000054d122da368d15998001bbc4e7000031c000ce30c5813463e00029f0000f0ad4c0003989b2ee3716c800000000000018a99fce4b1a3051850800011000000000134488784b7800067686293da00000000000007690000001a3e6c40d92cc17cc7cb3562d35d2aefb6e4ade5b8a1814e50000a1ae715e793791660000003f3859ef060463181b70e067a58001e48c0a626a14051aacf21f3535d524ed0001c4d16c24c265813c492d783171840000000000397cd409fa01e8000d2e63554f35a9a1800025e12f96a80551b6381496ab187899f7800000000003050707951c0b23976c54b00000000000000000e4c000000000053800083200018c400000000000000000007ab08e4e8ca064bc96859e80003eeb6712446f800014652ce000212abd81504e147014849e0b001b39d6cb3e9e27eb1820c0e00a3b892d085013819a8b48deefdf04b36d0954d492a111d0a5400000000000000000000000000bde206bae400076000026d8b9a3826f2800165c1b0000009d7401ff0002c9c0000002a780000000005a9800137a000000171dce800059180017b0000019000000000013080000005b7241032c7789155538a440b2d990b83e00fb0c5e44c
  | 28 => 0xb00015028060002f2d544f252e32095c94d250000001510f4e15bbee43d034509880019dede70000000b9e64d09921799fe0df000235857c0000002d3858441c5230790d680005babf696863e25a006ada621986078a595c8add000107dc4c6eb14981280000000002e5c000fc13df80000001f200000000000000611e2474e6490003c24000b980002600c700006009928280a1600036b400037f7db0000000cad048367441a0a51c4a950f78bca49a000197863b34680000007ef25d0001c30000000169800000000017ed1f605e3d0a74c0000002af9a505ae00000037a4000000000000000073e0000001292bc10000ed00000003a88000000bff309800010c000000000000000000033ed9f80a40640001e40b1022ea9480004bd0d8b9185da00058caec42ae00079f11240004a759c31e80000004babd6d7163d033709f90906fe17a994584a24b7d282806b40ea1830148a0a57963da0ec000d805928d38500d400b280019a6c9b2b71cd57b2008596b50c00000075a8000f684f60001bfde1e00039b000000000035c23754b40da0001f95e64c7d6f8850dc5a14c57a07e97909f50742bf0a1ec3f11f9afc92c36f664063040cfa10d3a4f43be6ed3f5bd7501c1903aabc7c000f9b00021a5766b8001c0000a401155f0878104c4ce1122b6800041d4d8800000000000023240000001562891e1802b0000001abe86c4a300000003de4f30d98000d195d78001dac8300001b0cc9800059b96d00000005c93a000000004a1958c0004fb000167963600000013056d0827030000126c9ac734b881984b1c6e080000000004fb92c18680003bf21e800092a7f20c5dea4452000254400061e4dd1e08f801d620b8e00dce1a02001c70e1a2f0157306da343be5248000f260000298590a7e0001210000000678000277407e3c27ae25b40000ce079adb0296000000263c00060c000309800000065a8d8d40013700027a19065e93fe8355f7e52d05f28d975014f762242155c00000000000005ea6558f68d0c39147c3ea5e06000000164c8107d60003bf44788d92b5b1c00005de34d1e6412a7d300002b837e00042c8f000000000308001cf40005048000bca000000000000000059a87bc3dcac85610938a909aa6cfb88c0006c90003361b260000003e1960689d4d7300129a7f272d3aeddba9cd00024349140000c9824c000ba369eb68c4c8c1912306b8000c0c4759664878b160348001ed2eb83b28001c3a1a6709ab81c700001890000000fd53fa00000001af46f1e1d79abd12d9800168c32e7ef00005fa1c947baa6c000e6c2d4b630fccbfc73400010e0c4c02b8000d7a3ad1750588ebc10e24402e40009f31301c24560b7300000008583830001f900007cc00029746fac5a0001a39a421ec388a1e5ab21d9432b5dd2a015678932d190
  | 29 => 0x705dc23c00000000000000f94aec7260001e980008ae0000000c2cbc32c199ac4b006736632c84e800016600010b40ff66680011963e300020d00000003b3090c00000000000000007ba6bdac980006440000000000c5578f21101562fb21a800000080c50fb49dc7884b7e18d706be2fc06e800127848502d1d0cb9216c5462fc4d6a00000000015d6a9550d934d0c6dd1691a7946544445ae88ac93e4643e200016c6c4979fb94c88ef7c1d29bf416a0003b18104d548e62341594942ad95a90315c080a721f800142400070823a5b64ce9000000068000076e0f6c00073746900011d44c27e9b9a8732ed56f1910c0006d2000310498c00e0a50000bc400045b8000000e1b0001e8000000000017b8a4c00074a32e11c2eaf2312e056085a215280009b86bb38c843c0000003f5000000000000000000e800012cbd65d6c7e359fa404ede1676eb13ac504b317000c5918086819c94e0bd82ff00c32c0b5800074c0001f8e0006238de800000056c00010aec674f080003cc06d6ebb41083662d00039e020a000044800100a0000000001d969a439ca5c4000321000011cf54000000200c6447c82bf18f43f270456600000000004438000cf80000001e8800000050c800000000000000000007b500000008d6000000000109c000000312d0fe56a52120800000007ad3b6123642f17301b00005e00d685816cc00069508853767154f4800055a0025d824e13d88950000000000000000179c0004ab5e380000000002ac0e312c0aed47a0000e62f7510d99c0bd600000011140001494ac8ff17b41a54aa9cc92cc0000003f8c000d76000000000000023500008300fa0599f5470e2a647a84d5a2cad542c1f504763a856f05c804675f000294d2f64a4502b215d9c56971607440000002e11b559a8bad762bf100005bd00035f800001f4be8e851defb23350ba42b40000709b5c000000000000000000079880005320000003bc53d46153ab1c3d0787ae00000010b829a11280018dc0001e60ad55f4e835cc80000000000002748ae8000411372d47e4611788df000000000039080002bc00000014a0f913120435b90f460b4a71909200029404ed9441fb0c4994000056114800005885c114f0fc0820d087c431e571eab87cf2fb8cce90300002fd974b2f0000fdcb0058244622b410e9917aa32ed4a27a71d7b201c2489441a87a94e65a3608927983412d0761159dbcb5c1360dc1316ca03109b98adef2e6de3f500004e20b737748a0da62500d4dc76d0b63922a17f40000000000000ded3b91b7d1fa6f600013c49700000000a2834200023fb1280000004a13190b9c000000298c00000061180000000003479a6537ee90759af5dedc9c824ca8047a8e5250bbd30000d693d7b05c000d0f2d01621cda97315a1aad5560004788d41ce00006d
  | 30 => 0x5103187c1e563aa80c06800000027c40000000c6bbf15f00007b12ba8f760000000000664f413631570e36d4f560800121812a15d8000de408d77a3498000a5607e16140009b452f2531232ba11f616253603b25ac00000000006df3c98000e080000fcdf40b6730080000000000000d51b804316831f18e160003681234000e0f00025c837c00046e000000000000000010ecfca5388000000c6179b8c9cc6400000012a400098106800014f00003e2bf444dc00079e01ac7303cf69d9d080000000000000e68174000035c73884c2e28001a944d822c80015a00000000000000f14429800013c000000058c00017b4268000000a7000013493bcc13274000000000060f1ee42e20003b503302a60004218bc800074871a0f85856ed900000000005376bd2fedc74c45000034c0004670a40318afa0002270000dc00000003ced36e00000000000000000e53559c82a7c5a588d0000faa000072c0000006e90000dc45e37ec00000000e4410b8591a0a4f7201d2c9caf7d7f0a01d90451b28480012d2bc679ab6051a84da209a049ba625e1b688300008fa79d0000bae0005bf1ccc00000045ca5c01b08d53bc80011380004e810583ba13470d22e8000000000000000000050619e90fa3b35cd3e380000004fea220a26195197a00941ae762480000000d36784265dc727070002935a8e74970a185c0002e400016617a45f67cc80009ded3e4890001410df60000000fb4ab226180009ba00008d80000000005598000000f0003c0eb800000026380007d2e5500002edf98b88210a874000c95276000160400027e0d6000000017c310dba80000000e91d80ecf00000009c8d0555f2a8038abb866b3a38000f5829ea31c192ee000000017ba00000030c8db400c56e07cd516b213cf2ff4a30e590f13b9000000060293cd2fc00040f000000000000000015d0b8c00017bd95c0002f80850a24e4e0000000000000657aa602a0e61342b6393340004f799f40006ca00038344209821d53bfd5a81f501228f5eece772a0b4395ee2cb18f0ed9c2200014e0ec0e8022d6240e480002670000d440000000000000000aee00011c5e2ae9b000104400000000001c807200049c863c89600074e00000000003d40001cf69146b924e80000002020dcc0006460001bc0828c6f5903ab48449e71738000000afe670b1b141e0001baaf582daa140000001f6a6d357f9bd1f9e4a800022114d00003310e1000026640b80000000000000000000000000198c0000000003c2c000a107688dc43c6c296b580000000006311824b140006e72ac40004a518cba440007d7000000131aaa517100004a600036e2af1d421da0001c4000017702c0001daef6c6902e541385b9496b62815a0000000000214cb9159b8fc2fc6281a58000000b960000efc00000009e0000e
  | 31 => 0x97e39700038d574c8ac47f0000d18f1c666309d33239b29e15ecef80002379c7c03a0001878b440000004ad0001d160004e8b7197c86935d3a6ac6ac9d64b700685dcecd00029d5550bba6528d94d3057a61d9d903289af340b41c8045c82ae9e70baa0b000002616c2151314a51d2960e934ea84cae00003950ccd8d20000fe0d08e5290462223b110ad9844832fc1b21110cdb6213180e3714ab1db160000002c140003df00014281003d631ba8bc5b890701832f8ee6deb58882d923e0003aa0f5c74cb4518398094f29320cb0478c6891057d8ec40000001198239370f8c27a9518d6e0000003734c32cfd0e98000000c3c00000001ec0003b08d6c000bb200002a967a95600000014ca65b0002fa40002aa4af2ff800059d6b000003807963421e393664bb0003bb400000065ebe9c244a2727f07043480000001bcd7d40000000000000000031a4140000f56c91e286d20001af3f89cd6276672abc000032c3fb0000000c160003d9000028c502000019af933bead646080006b1bbe5aae23e72396ad51c87206a0001d3aa8d1cfb03484026f00000018ec3fe2d400000008af72e134400052500027d93f2df030699700000000003de0000c5111780000008b1731bb8dbdcb690003db40004327868378e941175da80012d800021980009cc23100032740004380000000000000002800089e000000000000000060e8000dac00000000000000001a780000007160003070000804552228827400000029e8b2e3ea569a3c132a81f66002e134c2073fb84f9f0a97a317aad4000d821a5202033c1c811c000090200047e21cc02c7741cf2ad88160000cf80000000000001de80000a945f0001d6eca100010380007624f014cc00047968b8dc9b0cd5b00004613fc810694002c0000000000344000be061027fc4f011918c0001a82985179866814c3744358c4d81ce921871ec43d689f3c0160464cafd6ad2a1d22cae548780000008aa1948000f9434c2c8073c2040007cb800107c27b75000017ca5670003aa8df209461ebbb80000000000000000c061150000000e1571b3d45e72a2a2abbe280000002c89a2cd042153528cd1e80f330002aa9728f607c59288000da73128ddc256d1279a000077036404d8940fd8af25788c2d0026920b7b21000000054114e8594d01000000000000000021a8774e0200019080003fa1f034f000000043b800105428f375331c0000006e50001f5a2d856b2ca975647d0000e411e400066a9eb09460000000124000c8b2fb8001bc06de3908000d4c1ed450a0e58ac9900bb01f40005b53870084bf0cf354b83c199e9cf0000371beeacd00005f40002e8195988026cddb3688de177ad1c3112ad01045e10ba93d0e1418e7ec8d20cc859c0090001708a7700018717546a75f98001ebecc43
  | 32 => 0x5c8b911050000395949d672862238187476e3eb4bc00013f06b96cb28f8000f530000474000ec879136400000007bd2899f2a2031dc8560000a7e6d28000a9c0007113d9400000024491980008cf0003e910dcba2791b521b720002400838000ac90000000e248b500000000000004d111c810a2d60002d5c0000b1000282c00000000000000000005893a4c000fdc1b133b871e59b0000000620c6d33ab5719660005da000081ecec139800096e2133708328000a5c00000000000005578e80dd07c3006ab89c16000000000173a7a951280000004cd0e389f40006ce737b1d000000008b3dc000052c00020600008370001b1469aef3000148d2a66e900000016287d161b1be8000000243875da6a00073f28700009e40f387c000000048307605ba76700006a11dc0000000aa0000ac44e3a548000e5401d9ef8174ee737e1fb8d64eca093a739ba0f9403534e51ae6053a3951d0145170cc9c003702fe75e8e8c7cec9c52038a922215b6eabe04000000307a2340001de16a2481c56a206cd8001ac40007430aaca860e03968ffd4680007eea2d0b941b975a0001f8a000045800048265744f0000e5c0000002c2de6c5db0003d280000000002260bf8000550b9f10ac0000000001656a236011d352e8237493095c3469a30409e307887254b5885c000000257300cc9c0000001dfc304af3196a0b4ca4121672093cbe80002d70800000dac23f365198a0006c78001d860000000001be86365fc00000008147280001f66000313800067ee5b3e90a18b966e55b80000218000000000000000004d33a9f7aa21323b1add320002840000000a663b41a41c1423a0000000000e6600000000009ad65180000008c24ed0d74998bd31a219c8d907924be385df080004592e4c0004d013a9019e1c00000000000000001bb3ac8000000000000163400032d06486380e5000093400041936c202df9a00066e00c4f020004c9800000059a4ac135189c0000000001eae3cd000000000000049f000196288e497bcbd43420b6d5272402e3e872e85adfa0d0965b025dacc79d091b3999a019d0a0b42800091d7241f803a8ea20000bb000012478cbba16fe0000001b75c92a7f188b8254226b174281f128acce694b99df780a258f3979ce403c76fa42d3248bb12b1648000dfb0c295488a24d616daa744b6c30363b46084e2625a3abe4c780005ad0000edc0000000000000b560000001bb4000288000002ad0d00030b9f8c0003450550bb2e216ecaef91cad6e0bc000000050e25b0001ed40000001029aa07830000000000b155c3800000090a16f162c2fec1f3023440926a2851615015c2962000258dbf80000000ed5a2250b7ed8e385360990001598cee80976996bc00000000036ac0003c73a238b8d2c00066d15f15388ab0388ca11120001bc98c0
  | 33 => 0x7dc2b8db741ce00000000be75c05e85f000074e000263923c8663e095800007307e1123991ad2c4bb8a749069277df2ea4000d0020f00780022020001ce943c0002f42a4d29400000000000000004229fe8f9abc97ba31191c838d3912c4c9c6c405f124a1bfa26a00000009620000003da00000000000000000000217070cffe39a279000034400021195c4000000093000054200000000010328c513832980009417b3ba7813eab701bb645c9ef04722800063a18364d0001df01dc000000000080d0003eb8cfe184000000000072333980005c213322d16fc4d010427c9bb95743fd70e117114ab6f425116dda477b21a01102341426cd3959abcdea0d52ac0e5edbf7cd38780000000000001f767e20000000af0000000027400027f5ed8b95160ecc5db8c20e3a0076b7a14800028148b98682000007c12a58e109fc3d5be0d0c27f80000001ae246c21d00000e000021e8920eb40000001b8c5306585448001f202232b23290000d2258700000001e900019640000000000000000b5b594a0c450af3800000000000001e88000000e8a40a812c7587f507304bc1e828b10224907a41fd0001f38b74d890000fb8000bd432aa48de608715c33be8d6ce8900000003a0e961fa8fc4b70f3d70f9b342a455a00000012b8c2c000000108e00000000005aa00046d80000003e40000fe0000000000206800024a000000000000000000000000001b53e6000000000000000005fd5d70c1400000000000005240000001fec00000002000000000004f8000000011f0003ca8a72000772a888ab205449814c0000e2f1448001e8606851e2d100005aa00028a47b898342da4c41dc00011ea8d4ea06431b0197c8c6edb48e101ddd226b74233244a4d5159f009800000000000000000000001491a66f2700000000003200003ab800000000006d00ece8f1f31354b1e584000153406c75d6b08000000ace2370000000000000000151486d7a829ad92e00078d0000be27a500016d9aca0005863c6c000ef20ce3b88e980000000000000db10000000782c5b52417b400051f00014ad698897000000000000000000000000000003f487a60005a40c5056261b447b4c800000000019800000002df00000000000001cb0d74e1957300002e600069700004a80005e8000000000051b80012040001dd8000000000631a0d87de17a445188de0a000000000000000000000018309401700e2c09800010fa0bc3a43f60000000000a760000000f2e00000020ac000000000000000088039e3d080001975f1a955f920006020000c166a407cb01ceb020a3f400002400004088000e4000024d0000f3e13000000010c800000003b400000007f25bcb62000000169d26e511737226c0005df0003ddd0fc9c10003b9839ac7c7320b4d46400000006f0bccda2
  | 34 => 0xf00031a10bea1800035d4000000039bbd804a0000000001ada7a43bc00005d6a4e0000000000a6431d34e10384fa32099ecbf4d546142c89bfeec92808000f20a0e665bc044023866ae9ab4052534246359c0fc18843c2574f0cbdc000266defe02a594238c0281062833a98cec4403f9883ca64b646caa3cd8724af6deb7e58beebe462110519007f2231ecc5441680000000000b5f0001eb40000000fb80000005d300000006000005a880000000000000001f12b9b00034dd3b67f000008c800083a00006d80000004000000090d3f47f8ae4000000000262858033038197300000007c68000000ceb198adac36666c6d436ecd5031a350800089a00056bba7c0000005c4bd240004c00000001466000000000148650c00000003741f4000089c000a39466aba408a28300022194d2000000000000000000010ec00000000000000004c57da2e39b9eef50af80006ae1396121a88db6a0a00004f547462b4b43dacc0c01b6bc80019320000002e15046bf511105796f6c872158001b860000003025a880002593edd8aec88000000000081b301a3b438893b6beb93073acf56faa9880861131e4aab045caa374d2fd80001016da800093856c0000001b5ede65303194b5a00049580000c400070088c0d466c271236907900002028001bc49c03448040000aef00000000000001238000000c7f3fc8001c064845e2997907ea920000001572d6c6b996ec7f60004d0814400606f3f0800000000000000000005c400000012c2a2d66e8000ad000028b0000000b4a5de1ef40009c343032580008924650000000000000229000000000000011520000001c080002c53e104a450e0005f780000008c372b9e2c000eea67b2f9df62c8a4c49a4400021a0230000000476000000053e00043a028c00000072c3bf94dcd7c0001510f36a3861684a1ec22a362900000009eb639a4393aecc143a8a818a62887bd8000000b341c53d780000000002a4400000000000b4000706000377c000a580001e3d49600056d8730d52ee111480001b600022ab23c05c0001f696c1066c770280e54ba0f794cc32dcc3ebbb60825fce504c46dba3e5afed02427839c0ac82c1fa0001026cd74ce000055e96a017b40cc2204e22980001428a60001a7175800f2f900002b855018d9e448ca4544dcb1c4038a867810449f5e1f1378b27800051c23480005701c615f8bddd84b9039e8f197ee51a54c8001e3a1550000ac97dab1d0001dc0ddea5751880006b2abb2b68000000d680160001d4e0000000001126b3a0002e70000dae2e8b1718fcdb33348000000fa3000141c0005940002d409aec5d00024a40000283c23791bc20000000ef4bf23f9067b8300009b53dc00014de0005c106ec00076c14a0b8d9c00040002e9400064500017d41acf630001f9c85a000000000
  | 35 => 0x7fc53937f932c00052db4900000000370001bf4dc20000001f240000000000000e3e6562cd90ba0000001524000bc400020a4000000569000129c9f400028ec00000003c8971a2a68800000008ea000000000002262c68e80005920c03438000000bc023e332800000064480006f60005633a089fe000201800067a07553e99bc4389655428000000cdf469a468c7c5f33f6bc5957ea9f2ab08740f65b23b5b02ca5e64f27e9edc040255380954c646b1700023380002a40ff2c2467c00012d00000000005a1076d2908420000001ddef9f0110000928fa67218e50f645026498ad810838866cbc1d340840166bbb13640000000000000f112ba8be5f580834503dcc00000028f000057a00000000019cec8c62790c028a00000000011ec78d7d1315179c000000000194ec503f48b20000f870de8bd99a251d00033e9d46714649000117aac54338000000000000000045800019b03894d80007180001954e320000b18ffc00000000000000000000001f800003e4b54969e93
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xc3b741c16504001870e8382ca080161e61a709501002c1e422ec2a02013878805d8540400b07908baec6080160f21175d881002c1e422eda88201aa1c84596310403343908b286208002c5211510c410005a8402ea1882000b1484594310400192aecba06208002e4201740c410005a9404a81882000a5586150310402b6a10ab806208002e4211700c4100c516422cb1082017a2c84594210400164908a884208003915943108410005b0402ea1082000b2484594210400194aecba04208002e82017408410005b1404a81082000a658615021040296c10ab804208002e8211700841002c1f426ed280200287a80dda500400187708bb0a0080030e21176140100343dc32e22802013938845c450040016c505988a008003165da31140100f5a940c622802000c59760c45004001aa2e2188a00805754a1c3114010006a8c38622802000d51760c45004001e2508188a008003c461031140100e6a93a0622802000b5283c8450040018d2ed108a008076d8a062114010007a018c422802000c69760845004001ac2e2108a008003d08c42114010007a0188422802014d62870845004001ac30e108a008003585d8211401000791420422802000f21840845004037ac4e8108a008057549d431d00100a6b13a843a00200083f8759640040014730c2848008002cc604509001000788188a12002000f2021142400400b0790eb2880080026561c3110010004d2c38422002007a39869404004001e20632808008003c808650100100051cc30a02002000f10311404004001e40422808008073541d431100100e7892a062200201cf10540c44004037ac0ea108800806fc895021100100df902a0422002000c99765cc4004027a30eab988008002e4205731001000654bb2e42002013d28755c8400400174102b90800804f4c1d67110010005c841ae22002000ba0825c440040014730da88800804e4e21d51100100051dc32a22002000ba282cc440040017250318880080026661c311001000789a88622002000f11510c440040017270e188800800364a1c3110010005c8c38622002000d91870c44004001e250a1888008003c461431100100e789ba862200201cf10750c44004001e24ca1888008003c45943110010007c1390622002000f81720c44004001725079088008002e8a062110010007c018c4220020009a9870844004001e46a21088008003c85442110010007c1188422002000f803108440040017470e108800800368a1c2110010005d0c38422002000da1870844004001e450a1088008003c861421100100df91ba842200201bf20750844004001e44ca1088008003c85942110010007c1398422002000f8173084400402baa0ea18c2008053581d421840100aea83a8628802000d90740c51004029ac0ea10a2008003681d02144010
  | 1 => 0xd09baec2900160f21175185200051a422ea30a4000e245450861480015c100a10c2900160fa1276545200041f430e8a8a400083e87d91514800b0790e322a290003071d363545200060e3a0c6a8a4000c3474d855148001868e830aa2900030ed9070545200061c320e0a8a4000c5b631c151480018b0c6382a2900031cd84705452000638308e0a8a40009a8805d0214800115b0e3204290003235d0630852002c1e422eb3084000c1c7498d5108001838e8b1aa2100029520563544200062d318e0a884000c59631c1510800158902b1c42100023321d634802000662b18e29004000d88731012008001d12c62024010003681c440480200b61c202ed2a62005c3a649c254c402d87080bb0a9880170d9917115310004b8402e22a62016d30405c454c40010790eb22a3880030e99070547100061cb20e0a8e200089d8799031c400115b0f320438805a4e21171143100b68c3aae62062016d28755c840c402d2710ea8881880026661c3110310004d4c38422062000c1e749cf658400183ce8b9ecb080030b9d272d9610006173a2e5b2c2000c3a749c36584001872e9386cb08003169ce70d96100062cb9ce1b2c2000c6a729c365840018d2e5386cb0800287a136598e1002c1f426eab1c200085e87d95638400143d09b2ac70800217a1c6558e100050f426eab1c2000a2e84d96628400b07d09baac5080021ba1f6558a1000517426cab14200086e87195628400145d09baac5080021761e63d46100042fc3ac7a8c200086d8798b51840010df0eb16a30803217a1e63546100060e3a4c6a8c200b85c8758d5184001838e8b1aa30802a1ba1e6254610006163a4c4a8c200986c875895184001858e8b12a3080031698c70546100062cb18e0a8c2000c6a621c151840018d2c4382a3080021761f658c6100d50f426cb18c200085d87d94318403343d09b286308002c5211510c61000723312a218c200095587d94318400162d09b286308002d4a03650c610004aac38ca18c2000b528019431840014ad0c2a0630800391d96620c61000436c3ecb10c2018a2e84d9621840010db0fb28430805e8ba13650861000592422a210c2000e46635442184001c8eca18843080025961f650861000593426ca10c2000b6280d9421840012cb0e3284308002d8a00650861000533430a810c2000e476598c218400b07b0fb2c81080022761e631021000456c3cc42042000995870c4408400134b0e10881080161d219711511002e1a322e22a22000a558115063440014cb022a0c4880030e19270d45100041f430e8a8a200d83e87d91514400b0790e322a288003071d363545100060e3a0c6a8a2000c2c74d895144001858e8312a2880030ed9070545100061c320e0a8a2000c5b631c151440018b0c6382a2880031ad88705451000634310e0a8a2000
  | 2 => 0x870544400068db98e0a888000d18731c15110001a56e4382a2200034a1c870544400068d318e0a888000d19631c15110001a54c4382a2200034a588705444000699308e0a888000d31611c1511000b0790cbac622006b07197768c4400d50e432eb1888000c8d7658a3110035c18cab146220002c6a03518c4400d50e432a31888000b1880546311000113b0f3b0622006707d95760c4400ce0e32aec1888000c1f855d831100018390abb06220003075da750c4400060ebb2ea1888000c8d76988311000191aecb10622006783195620c440005c240ac4188800091d87d44311000183aeda886220002c6a03510c4400048fc3aa21888019a1c86544311000183aeca886220002c6201510c44002c1e432eb1088018c2c65dda21100314590cbac4220003235d963884400c70632ac71088000b2a80d4621100314590ca8c4220002ca201518844000546c306310880008ad879d8211002f85ecabb0422005f0b195760844000617c2aec1088000c2c855d8211000185aed3a842200030b5d9750844000646bb4c61088000c8d7658c211002fc18cab184220002e1205630844000496c3ea21088000c2d76d44211000165501a8842200024be1d51084400bd16432a21088000c2d76544211000165100a884220003235da310844000546c30621088000c8d760c42110001e0aa21884220003079d56398040006173aac5300800083f8754660100012730fa8cc0200024ee1d519804002d1c432a33008000a1d860c6501000145b0c10ca0200164e61e609404002e0e3b2c62808005c2c76588501000143b0c188a0200028b618211404002c9cc3cc0280800583c845d661cc00b07908bb2a3980020f618745473002c1e43cc8a8e600083c8759151cc001874c8382a3980030e590705473000456c3cc810e6005c1c76151434c001a30a8382869800383151431893000564402863126000a3684dd7614c00b07908ba8c2980028d21175185300070a2a28630a6000ad08050c614c00b07d093b2a2980020fa1874545300041f43ec8a8a600583c87191514c001858e9b12a2980030b1d062545300061a3a6c2a8a6000c3474185514c001876c8382a2980030e190705453000635b10e0a8a6000c68621c1514c0018e6c2382a2980031c1847054530004cc402e818a600089d87190314c00191ae831062980160f2117598430006163a4c4a886000c2c74589510c0014c902b12a2180031a988705443000634b10e0a886000ac48158a310c00198ac438a6018003621c8404c03000744b10809806000d9071101300c00b07908bacc3900160f21176547200041ec30e8a8e400583c8799151c80010790eb22a3900030e99070547200061cb20e0a8e400089d8799031c800b858ec2a28490003831506350920006942a0e0a124000cc8631c1424800146
  | 3 => 0x3188a000c1d765d031140190bf0eb08622806687211610c45002c1e422ed108a018a2c845da21140130df0eb0c42280628b211618845000616bb2e8108a00a86f87584211402f45908b084228003915843108450006162a6e4b1c8000c2e655cb4390001838a9b9ac5200030799573d0a400051ac08a930c800d83f865d4419000162b022a06320002c960454086400049c402e332c8000c2e65dc9639000183ccbb9ac5200024e20175986400051ac0ccb30c8000c3880dd9519000183eedb9aa32000307dd8735464000617bb6e4a8c8000c2f761c95190001876edb82a3200030edd870546400068db98e0a8c8000d18731c15190001a56e4382a3200034a1c8705464002c9cc30e0a8c800083f865d6319000143f0cbac632000287e19518c6400058c402a318c8000b1581994319000123b0fa88632000247e1d510c6400050fc32a218c8000b1880544319000107f0cbac43200028be19758864000517c32a310c8000b2880546219000164b0332843200024b61f510864000497c3aa210c8000a2f86544219000165100a884320003c154431086400041fc32e2284800583c841d9515000b43d09baac620016872107558c400ce0e2a0e2b188000c1e7558e431000b45d09baac4200168b21075588400be162a0e2b108000c2e7558a42100010bb0f31ea22000217e1d63d444002e0e3a2c7a88800086d8798b51100010df0eb16a2200170b1d162d44400042f43cc6a888005c1c7498d51100010b90eb1aa220017071d163544400043743cc4a888005c2c7498951100010d90eb12a2200170b1d1625444002e1a3a4c2a888000c5a631c151100018b2c6382a2200031a988705444000634b10e0a888000c72611c15110001838eab1a82200030b1d562504400d60e2a6ed188801ae0c5458a311003383ca8bb0622006707151760c4400cf062a2c41888000ac4815883110031858a9bb442200638315163884400be172a2ec1088017c2c545d8211002fc18a8b184220002b1205630844002e0f3a2c72808005c2e7458a501000143d0bbb2c620067071947158c400051742eecb108017c2c651c56210001711009906420003624c9700c840004d840ae01908000938805d66110001838eab1ac2200030b1d562584400048ec3cc7a88800091f8758f511000b838ecb1ea2200024b61e62d444000497c3ac5a888005c2c7658b5110001a34c7386a2200034658e70d444000695314e1a888000d29629c35110001838edb9aa220003071d873544400048f43cc6a888005c1c7698d51100012390eb1aa220017071d96354440006163b6e4a888000c2c761c9511000125d0f312a2200170b1da62544400049643ac4a888005c2c76589511000b868ed30aa2200164d21d61544400070ab1ac2a888000e25625855110001870edb82a2200030edd
  | 4 => 0x408401a8f06b88a8108035120d71150210be93a1ae22a04200d63805c454084012c900b88a810803582017115021004b0402e22a04217d24405c4540842fa5081380a81085f0b15176d0c2100592c08a8a184200d24541c5430842f25908bacc2108628b211759842100592422eb308420096587152610840185aed326a2108030b5d964d442105437c32eb2884200c2f84dd9510840185909bb2a2108030bddb745442100617bb0e8a884217d25811d1510840125d003a2a21085e4b21e645442100617bb4c8a88420092c87591510840185eecb22a21080313ddb7354421006863a6e6a884200c4f761cd5108401a18e839aa2108261ba1e61544210c6163a4c2a884200d247498551084018d6edb82a2108034a1d3705442100635bb0e0a884200d2b741c15108401a50e8382a21080352dcc7054421006a4398e0a88421dd63711c15108401a5708382a2108034a210705442100695320e0a884200d29641c1510843bac702382a21080358984705442100592c08a92084217b248454641084016c100a8c821085e5921d5150421006a239aa2a084200b60805454108401ac2a2382821085e4b211751042100592422a39884200b6080547310842f25908bac6210802c3211758c421005a2c08a91884200a4d86d46310840149f0ca8c6210802c3211518c421005a4402a318842008ad869d0310840164908a886210803495d1510c421005b0402a21884200a8d869d0310840131b0f3206210802d1604540c421005a2c2ce21884200b4585984310840129b0fa8862108029361b510c421005a2c2ca2188420094f87544310840149f0ca886210802c3211510c421005a4402a21884200b8484544310840178100a886210802d1e1d510c421006a3c3aa21884200b47865443108401c8f0ca886210803c1e11510c4210fda2422a21884200f0484544310840160908a886210803c19d1510c42100782ba2a21884200f06645443108401e0ac8a886210803d0e01510c421005a2402a21884200f4080544310840168100a88621087ed1e17410c421005a2c2882188421ff0454104310840155100b22c01080323590735802102e0f322e6324a005c2e645c8649400b85cc8b9687280170799173d0a5002c1f424ed18ca01aa1e849da319400183aecba063280160fa1276886500c517424ed10ca000c2d765d0219400107d0c3a2a2a80020fa1f64545500061db20e0a8aa000c38641c1515400b858c8b9686280170719173d0850006a4992e0190a000970815c03214001838e9b9ac228003071d07358450006163a6e4b08a000c2c741c96114001876e8382c2280030e1d070584500062db98e0b08a000c58731c161140018d6e4382c2280031a1c8705845002d1a422c3208a00583c845da311403543908bb4622802e17e1d618c4500d50e422c
  | 5 => 0x8802c52117598431004aac38a93086200c1d76993510c40183aecb26a21883217e1975944310060fc26eca886200c1c84dd9510c40183eedba2a21880307dd874544310ce8ac08e8a88620091e801d1510c4332390f322a21880307dda64544310048e43ac8a886200c1f76591510c40189eedb92a218803431d3725443100627bb0e4a886200d0c741c9510c4170bd0f30aa21886b071d261544310068a3a4c2a886200c5b76dc1510c401a30e9b82a21880316dd870544310068dba0e0a886200d18741c1510c401a96e4382a218803521c870544310f6a9b88e0a886200d1b841c1510c401a3108382a2188034699070544310068cb20e0a88621ed53811c1510c401aa4c2382a218802c560454904310cd8a422a32086200b5080546410c4332a90ea8a8218803511c95150431005a8402a2a086200d51511c1410c43323908ba88218802a6201645803100646b20e4b006205c36645c454c84012e100b88a990802956045498f210060e3a4c6a8e4200c1c7458d51c84018b4c6382a3908031658c70547210058a422a218e4200b508054431c8401858e9b92cb108630bd09761522102c1e422ebb1c4218d0c545cf428843543908b2c631086687211650c62100497400e8b2c4218d0c545cc6488431a48a9388c91085e1be1971952210c694204e12a44218c2c645d8548840164d03b20a91085e1be1971152210c69220ae22a44200968805c45488431a5081380a9108624b21175d8e210c6162a4eda1c421892c845db518840185eedba2a3108030bdd8745462100497400e8a8c4200c4f76dcd5188401a18e9b9aa31080313dd87354621006863a0e6a8c4200c6b76dc15188401a50e9b82a3108031add8705462100695ba0e0a8c4200d28741c15188401a96e6382a310803521cc705462100695c20e0a8c4200d28841c1518843125908bac6310802c3211758c62100586422cb18c4200b0c84546318840169100a8c6310802c3211650c621005a2c08a818c420094d87d44318840129f0ea886310802c3211510c621005a4402a218c421892c845d46088401838e9b1aa290803071d063545210062db18e0a8a4200c58631c1514842f85e84bb0a8108170d99171150210be93a12e22a04200970805c4540840191ac939e841085f4315173d082100592c08a8a10420583c845d6610840b0790f322a2108020f21d64544210061d320e0a884200c39641c1510840113b0f3206210802c5211510c4210070ab22a21884200b5080544310842fa18a8b9cc8108027120573990210be863aae73204200b84815ce640840151d07bb2c81085f0b99176950210c437c32e32a04217d28409c2540842f85cc8bb0a8108621be1971150210be9220ae22a04200968805c454084012cf0cb88a81086319e1971150210be93322e22a04200d25645c45
  | 6 => 0x52d41e84302a200a5983d0860544014e503a10c0a88029c607421815100539c0a64302a200a70814c86054401c9264190c0a881687a137558f4102d17426eab16820085d8798f51d04010bf0eb1ea3a08021b61e62d474100437c3ac5a8e820c85e8798d51d040b838e931aa3a082e1721d635474102e0e3a2c6a8e820a86e8798951d040b858e9312a3a08261b21d625474102e163a2c4a8e8200c5a631c151d04018b2c6382a3a08031a988705474100634b10e0a8e8205c36615d8549040127100b88a9208030b1537258e410060e2a6e6b148200a3a801526090401838a8b9cc1208030b15172982410061632ae5a1a8200c1c655cf4250435838e9b1aa2a0867071d063545410c6163a6c4a8a8217c2c74189515042d0f50c382a2a080316d8c70545410062c318e0a8a8200c6b621c151504018d0c4382a2a080a1ee1d51d81410b51c422a3b028213a71811d4605040155305a18c0a0802a660f421814109d1d426a23028213a3884544605040b2690ea8a82208030ddd9515044102e1b322e22a66200970805c454cc4014cb022a4c5988030b1d26254731006163a2c4a8e6200c6a621c151cc4018d2c4382a398803071d373596310d60fa1aec2a4621ad0c545cb438c40123d003a2cb1886b4315172192310d68a2a4e2324621985f865c6548c435a3081384a91886b0719176152310058b40ec82a4621985f865c4548c435a2882b88a9188025620171152310d68c204e02a4621a91c845d7628c435838a93b6851886a4721176d46310060fbb6e8a8c6200c1f761d1518c40123d003a2a31880313ddb7254631006863a6e4a8c6200c4f761c9518c401a18e8392a31880316ddb70546310068c3a6e0a8c6200c5b761c1518c401a36e8382a318803461d07054631006a5b90e0a8c6200d48721c1518c401a3708382a3188034621070546310d48e422ea3046200c2c74d89514c401858e8312a2988031ad88705453100634310e0a8a6219c1f435d8540c40b86cc8b88a81886745d0d7115031004b8402e22a06200c8d649cb430c433a18a8b968618802c56045450c3102c1e422eb308620583c87991510c4010790eb22a2188030e99070544310061cb20e0a886219d0c545ca640c40138902b94c818867431d57299031005c240ae53206200a8e82dd9640c43383cc8bb4a81886a17e1971950310ce8c204e12a06219c1e645d8540c4350bf0cb88a818867451057115031004ac402e22a06200957865c4540c4358af0cb88a8188674599171150310068ab22e22a06200d47825c4540c401a8904b88a81886745d097115031006a9c02e22a06200954805c4540c401aa100b88a8188025420171150310ce8a202e22a06219d18409c0540c433838a8bb68418802c560454508310068a2a0e2a10621991c845d6610c43543908bacc21
  | 7 => 0x38641c162544010df0eb10c4a88028b211621895100534402c4312a200a2e8499062544014d501320c4a88030b9d8641895100517400c8312a200e0c64d8c6254401c18c8318c4a88170719273d095102e0e322e7a12a205c34649c742544010f100bb484a88021ea0376509510061a326e2992a200c34641c53254401c18c899064a8802d1205320c9510051d400c9b02a200e1864d8f6054401c30c831ec0a88038a19362d815100714320c5b02a200c1c649ce6054401838c8b9cc0a8803079d363981510060f3a0c7302a200c2c649ca6054401858c8b94c0a88030b9d36298151006173a0c5302a200c3a74d82605440107d0e322c0a88030719373581510060e320e6b02a200c2c64dc96054401858c8392c0a88021ee1d60181510051dc22c0302a200a388458060544014b706b00c0a88029620d601815100535c12c0302a200a6882580605440147501ba0c0a88028ea0074181510051d424ec302a200a39849d8605440147509320c0a880296a0e64181510052cc1cc8302a200a6a8299060544014d305320c0a88021ee1d64181510052dc1ac8302a200a588359060544014d704b20c0a88029a20964181510051d430c8302a200c3a761906054401c36c9b18c0a88038619363181510070dba6c6302a200e1874d8c605440147509318c0a88028e61263181510052d41cc6302a200a6a8298c60544014d305318c0a88028ee1163181510051c422c6302a200a6b8258c60544014d104b18c0a88029ce0563181510052d430c6302a200e1b6418c6054401c30c8318c0a885794d8463181510070dba0c6302a200e187418c6054401c56c9b10c0a88038a193621815100725b1ec4302a200e4863d886054401c56e9b10c0a88038a1d362181510051d424c4302a200a398498860544014b507310c0a88029660e621815100535414c4302a200a3b84588605440147108b10c0a880296e0d62181510052c41ac4302a200a738158860544014d50c310c0a88038ad90621815100714320c4302a200e4b631886054401c90c6310c0a885398d84621815100715ba0c4302a200e287418860544014b5063a0c0a88029660c741815100535410e8302a200a69821d060544054e3023a0c0a88030ea1c74181510070d418e8302a200e19831d06054401c55043a0c0a88038a608741815100719408e8302a200e31811d0605440147509398c0a88028e61273181510051dc22e6302a200a38845cc60544014d704b98c0a88029a209731815100539c0ae6302a200a6a821cc60544014d304398c0a88029aa0b431815100534c1686302a200a7281d0c60544014e303a18c0a88028ea1272181510051cc24e4302a200a3b845c8605440147108b90c0a880296e0d72181510052c41ae4302a200a73815c860544014b506390c0a88029660c72181510
  | 8 => 0x2c03801002028038080020040280000c0000180b02a004010100140080000a00001c0300100000800802004004048030060000500000000c0100400800001000004014020010120000480a0020000e01a00a00400804000018070060080080000600e00402008016004008040160040400600e00c000030000280880e000014028010020000000200000400004000000010010000000004f0e10070586540d60e3a6e6b08a81ae1441dcd6115033838e839ac22a0678510473584540c6163a6e4b08a818e2441dc9611502f858e8392c22a05f8910472584540b61c3a6e0b08a816e3041dc1611502787080382c22a04f0e1d070584540062db98e0b08a800c58731c161150018d6e4382c22a0031a1c8705845409f18208e0b08a800c3b841c1611502787108382c22a04f0ed0c705845409e1da10e0b08a813c71811c1611502787082382c22a0170799173952530be162a0e2b168605c1f639d85450c0127100b88a8a18028d60454185430051d400a83028600c2c545c86050c011c902b90c0a18170b99172952520ce0e2a0e2b1e8405c2f629d8545080127100b88a8a10028d60454185420051d400a83028400c1c545cc60508011a902b98c0a10170bdd85450b3202c1e422eb30e6405c1f76151438c80b07908bacc3190028d20564151320051c402c82a264008b8805d0614c80138902ba2641900272201744c83200686ba0a8990640098d841c5320c80b07908bacc2190021e20175984320056240a653086400ac8804c9600c80198a6438ac0190170b19172d0f5102e0e322e7a16a20083c865d2535440183ce9b1ca6a88020f2197494951006173a6c5292a200a3a8494c605440147309298c0a88028ea1252181510051cc24a4302a205c1c649ce645440b838c8b9cc8a88170b192729915102e16322e5322a200c3b649c2645440b870c9384c8a88170e19170991510041fc3ac8322a200a1f83590645440143906b20c8a88028be09641915100516412c8322a200a3b80590645440147100b20c8a88170ea0270191510052d404c9b1aa200a1e80193635440183ce9b1cc6a88030b1927298d5100616322e531aa200c38649c263544018b6c7384c6a88030e1917098d5100616326e4b1aa200c2c641c96354401870c9b82c6a88030e1907058d510042fc3ac631aa200a1c8458c63544014b100b18c6a880287a126418d510052d404c831aa200c1e76190635440143d00320c6a88170b19272d0d5102e16322e5a1aa205c34649c743544010f100bb486a88021ea037650d5100535404c9b12a200a2e801936254401c18c9b1ec4a88038319063d89510060e324e7312a200c1c645ce625440185ce9b14c4a88030e192709895100635b14e1312a200c38645c26254401838c9b9ac4a88030719073589510061c326e0b12a200c
  | 9 => 0x20b8fa80013796b80018f8000001be1cf8000d305c9c6800140a608000800000b600000000000000000000007206517580005990609d0e00e50dc9411f09a986690f1221701a31a598e0f81a49969bf22089108412a9cb0000000000000c704e830a3c80008621c99796900e9538d89ce06c83e9f101d9bb0000830000001518688001b88000001150000a8118125800038a4c0000001480000208000361c01238000920f29ae02d14fa1d00020b09694793f1cd8000001108e786d10b246a4a000136a1009da1b87e92c13112b03e060a4791780024712293087d2281fa80000025c8b381088b85e8318f8a2703b99380011d0000c79f90ee862955a071a509e9ff0bb9c400000024389705f91e1b30390f91342021e410280c0000b52108631129fc0e8a32a2c8350f7177a399b803725716c05e1d80bd15796b1e11741d48328838dc0a50ab19a0fe9fb1171d22461e6a128fd25083d93f8a01998000001bc9828000000000f08000779cc8a623ea5b8000000258001b90000d7a638000000cf00000000015604085c2238c50002548791392568f68578c405a0dd9110000e48000000000000ea9e380002d8000000000002630000002420001c31571360d490ca2a9010c98000cca259ee1769d3a31a0381180023d0a59e50000001d10001fa00000000012499f8000ff08b0000000b08000002220000000000000000001121d793200000000000018d18d800144800073800131a3901993d8000000000000001300000440000001f020693d0068002180d80000000000cd0001688000e20000b580006c088a5982a0000002428000000b40881be8001fc98100000015200019480a00400c01009002000030090020180040000200000c0080200600800008000000000010020180000200201003800000004010020000000580200400000800006000008010040080780304006c0000000a01400002000000000060000000000100200800804006000000020440000c8000020040480300000c03001000010078030000000000100a01c0101100006400800004000000000080b4020120020100380001e01c02000008000060030000200280001e008018090120000280000403002000004000000020040040000700000000009012030050010000100080200004c0180000601400004016008020050020100180202c004030030040180080201200003802000010030020000000480005400000003004000038180000080000002c0040080900e0000200201800c0300500c01c0000000402c0000204801801002010000010040000000180001605001802000000028010000040480100200c01001028004008020000400000000c0000200000c000008000100080080000200000010002040000070000080080800200400010002000040000
  | 10 => 0x6480004a92e1160848001c09c60000001ae8ed8610000000818000000000b90ff8000eb25b1f698584f8001ab22780f80000421e058a2280018523591a0a48001510958000001620000c100010a028926800094103a0a00000008fa581e29c980001006180022d0000000a680024a85f0750a280002b8001c88000c80b20000918d019c8270000000641dc0000001428810000000000000000000000330de00000001d1b70001ce9499328000089138000db95985d82c80b0001b60000000f61fd0f400000385800003aa3e0ce8281118f11d88fe1ea84da36a4b8000ed0a31750ac1c201f0c60979882660020e30001719ea0000001981c180017d80001c8fa0d38901878c380009b192a0090700000020c9868000000278000980000000000001351a009f98c80d8479e880000000001f8000000000b68001790090000001d518a80016800007c8e80000349b119b80023a0310d1a2b11e89c2372190001b693c0e91ba8991bd0d5a578a20d6a1595a8001931b784f1b591880002180004c8001ca9002198000000001ca1a70000e112e92a0a89aa0db2160001e790904895a04b0002341279c913313b0000459ec0000002262000000590000001d29de02293700014e1e58120000000000000000c30000001919f58b322e8000000000001030168ae0000af800184a0a80007893e8000000d99ac00003400e00000014c80014b8f980021da338b28000bc0000001951058000001eb97a8510000000898001e90002402290000410ca1fd96701a00000019f1b3a0e91d94606b00005600005d10b8000708000000111d609f0001ac9ff8160da0b10000000001d69ed9a6a2f1e218f19595d0b81569720bd9f987d87f0421580f382418e80b9831fe14d9419b40951018e29591c513b96184d040094a210ca80490982a9d31191650a192f86e93a08ea1b0000939d081c00002f0499aa8002060002248ac93990d9d91a880295c8001c79f807804680024e00002000023125501e2250000000ae9ef20500000016e82e80017b1e48761898b78c21bba3793824e8ea0000001b48001de89a00016a1db22d97800000000000011f0000000001f621402c10d1e70fc1471198509b00368b98000002521659d700015880000000000007f8690bb22a00000011580022896a8000000000660de8000000001788b00730000000bfa588000f58000569148000000001dd00022e1ef9748da9cb8d20000c19c58000000571838868000000000378000cc0000000000638930000000001a28698002320600001b517d0cb0e380000021f17724097c86b90fa1a05585324193583b1dda0f075907a1680014d00018b0300000269da80006e0b48a7a481b180024d0b88001e19710c010523f19d00015e9a78c4a138cf8e09709e810c0fc94a80013894596c8e98ad000
  | 11 => 0x2178b192117e1c395e00018b80000000005b1c815315c0538710000000001b20338cb88f18a11400000000011326223b00000000000000000c9088af1c11dba5a04a09c9441f8a268649cd00091b8998a909a8d607b87b0470e600000000011a80a92997e9d99338748010df10424912603f0d081482f954a511529a423800009e0000df80000000018887c15091f92d04b8d299e8740e699d9989a09c49290000001698170000ba00016083d16f87187a08a00016d80002604186f8ab9020381d00001f214c1a916e15b0000001738152488cd8dd16780019e01900a0000000002658001f180015fa1f9f3a4f14900014309626492f0ee00519c0000e7166a5d04e1e00071420002078500700000000eb80012022f9f49940620490c698424b2309a392512da13000180234a1c20182e0462652080678541209a182322b84c1ec8ba9fe82126413a825252a3b80015b8be00006a80000000005b80000014ea08a350d711c1bf99101897f0f52411439232058001af83597307e07980000020f8000769d58000001550001df00016410e19a83f80000007720c1500480681631bd80010e8430f78e58000001e0a3f9b986f1541628000000000aa20e01412800000000000022417b8002600aaa218850000002532458a40002619960bf0098000000000000a3a1880000005a88203201591ca1125aa151ad83c8bc88c16d000238a5d80000000025e908190a55a029e6039916a49a441ba00011000008c87a8018001ad15f13c80000000026108d013a541c28000000000428728000670000ce1871820000002449610fb00008920d8002299860001971f780001b0078518000002119920059e9a3d92c8001a600000000000000012880010080014a0a102200000000000000000014b0000000001cf0001a20001f289ba2313480000009897a0001e30d11798000000060fb8550b71068131f41760128001b080010aa3a86a0000d524f80021480000012704500f1ee81b80d0f300000000003c0000000000c0800000000000000000000000250043a30029052a5e0a98000000000001bc2010001f717c25c0000a08f180010480016602380001e817a5908a9a82330000001cc21a8001af12b8448f48929eb00023617f88e0002430299488878ada0999b1240001ed0000be9901df8870001401b28ef8ef0000000248002170000001729600ec11b00020480000002b13e21ea2c0000000001fb80000014f0c58c286d8000fd98080000000000000018c0c895da51963a2000000014680000001a8000d919900024c80000025600023c08580018198900308d8f003a0f20000829dc8002041218001d40ec80820d0001da0908548000002451d18a716f2090001f30e405225f865a1224da5f0000000000000e18808000180001451a11f52539ab9
  | 12 => 0x1c70c90d426280000000020300000
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x43f90475205739902110e48104805c4540843f9048420d711502110e48100805c4540844392084201711502100650e0c805c4540840194083201711502100648e50805c4540844392094201711502110e48990805c4540840192164201711502110e48d0c805c45408401320906045450c210050a658841c15108401320906045490421006501cc80545410840134090604548c4210044926174544310840192174201510c421004d024181150310843f30494616710c4210fcc125185984310840130690211510c4210fcc1262745443108401605969d1510c421004c126174544310843f30498991510c4210054165e64544310840130498591510c421006c021380544310840194387201510c42100690e18805443108401b0384201510c421006c0210805443108401b0394201510c421006c0250805443108401b0274201510c421006c05d0805443108401b0264201510c421006c059080544310843f30494614410c42100522241641cd600840194132205700c8500fd81251610c42114001230906066598640004c424181994319000132090606650864000581e59510c421900017009054431086401068115081588311003fa04542056308440006604c8815c0321000b8148758d615444002e0921d62585511003341591215760c4401068119481588311000181976a03510c4400cc0726176544311000181976201510c4400bd09644855d8211003fa046520563084400060a5da80d44211002f02c985d951084400060a5d880544211003f60496544310844000681619510c42110001c05765443108440005c0241510c42110001a08542014318930006841508050c614c001488905d0620c530006091d081589510c0014609158870544300072058871101300c001c085418c705092000688150805086148001488905d06308520006051d08158d51080014509158c70544200052225d631012008001c81631c440480200068121262544318400160694d96620c61000590a43659883184001a048498d51086100fd81a53650c4218400160694d96630861000590a436598c218400189176201740c4100e49424186150310403f604945943108410006285d8805d021040372609061854084100e544251710c450040019118761031140100dd48251710845004001c41760c421140100064861d8408450040011339760450900100054465c3194040040015219708650100100e6441d4815cc40040379207520572100100064461d510c440040399137561c31100100064461d850c440040395109759431100100066061e720c44004039d00755c831100100064861d510844004001581970c421100100066061c3108440040379237561c21100100064861d8508440040375209759421100100066061e730844004037d00755cc2110010
  | 1 => 0x989b1f9cc000000000000000000003d2c99c4c60000a868000d800406302191027b49251040000000008800218de8e00000004242000d2004b00056222d828f021049b4349c20a1d1a00259708883038c45897098dc16583f979145437044ba8b48114281638854862e2a9183a3e4d0d8a4270f8e8b46a31078cc323915c9a2d01938ee6b2f814320829958700024890508f28a1500010e0cc00980c000004f25030f479382440c7c329d4a023361a12a123f0953261001d81e104985c1c3517a2404001811c1a483e900003c148e53a74460ec0009000103041f040c00000301141c0405050d240d00020c1103010100062202010214200a0211000000001909040a0506300622270e704104731c16115037c20411c870584540048c241811506150c018245420572181430048c2418115061508018145420573181420054124574151320c801508905d0544c83200462241841c5320c801a0464205320c9510068460d811d06054401a2182604741815100590245320c86054401260906045498b3111644d0c805c4540c401310906045450c3110641150815ca640c44190475205729903111644104805c4540c44190484209711503111644100805c4540c44591084201711503100650e08805c4540c40194082201711503100644e50805c4540c44591094201711503111644990805c4540c40191164201711503111644d08805c4540c40131090604545083100506658841c1510c401310906045490431006501c880545410c401488905907258031004942418115263c840134090604540c62110e48d08805c4540840132090604545082100485261645443108401a1164201510c4210fe41150815ce6408
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0xd00018000014b4880021c00004a00c010fc40950cb4e8a886210882104a865e645443108401480d3928402a21884200a8069894201510c4210054034d3a100a886210802901a799080544310844110254b0ca8862108801f9012a57654431084400064030c482a2188422000340176241510c4211004508854b0ea886220020218482a5875442110010
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x6
  | 2 => 0x4e
  | 3 => 0x3
  | 4 => 0x4
  | 5 => 0x5
  | 6 => 0x138e
  | 7 => 0x10e
  | 8 => 0x130e
  | 9 => 0x20e
  | 10 => 0x140e
  | 11 => 0x24e
  | 12 => 0x144e
  | 13 => 0x28e
  | 14 => 0x148e
  | 15 => 0xd0e
  | 16 => 0x188e
  | 17 => 0xe8e
  | 18 => 0x18ce
  | 19 => 0x4d
  | 20 => 0x20056
  | 21 => 0x24056
  | 22 => 0x138d
  | 23 => 0x20d
  | 24 => 0x140d
  | 25 => 0x24d
  | 26 => 0x144d
  | 27 => 0x20055
  | 28 => 0x24055
  | 29 => 0x4216
  | 30 => 0x4256
  | 31 => 0x24215
  | 32 => 0x20255
  | 33 => 0x4215
  | 34 => 0x4255
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 72
  | 6 => 2016
  | 5 => 4069
  | 4 => 1229
  | 3 => 158
  | 2 => 12
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
  | 7 => packedAt gbK7 (2040+((h/24+packedAt gbK7 (1872+(h % 24)*7) 7) % 125)*8) 8
  | 6 => packedAt gbK6 (82656+((h/672+packedAt gbK6 (74592+(h % 672)*12) 12) % 2420)*12) 12
  | 5 => packedAt gbK5 (212940+((h/1356+packedAt gbK5 (195312+(h % 1356)*13) 13) % 5908)*13) 13
  | 4 => packedAt gbK4 (77010+((h/409+packedAt gbK4 (72511+(h % 409)*11) 11) % 1784)*12) 12
  | 3 => packedAt gbK3 (11476+((h/52+packedAt gbK3 (11060+(h % 52)*8) 8) % 190)*9) 9
  | 2 => packedAt gbK2 (992+((h/4+packedAt gbK2 (972+(h % 4)*5) 5) % 22)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x7ffffe007fffffffc00ffffc7fffc7f1fe3f
  | 1 => 0xffffffffffffffffffffffffff888c7fffffff
  | 2 => 0xff807fffff807f803ffff007fff0f078fe63c7
  | 3 => 0xffff807fffff80003ffffff803ff007f1f83f8
  | 4 => 0x7fffffffffc000000003ffff801ffc00
  | 5 => 0xffffff80000000000000000003ffffffe00000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x2025a5962025a5aa72c086cb643335c370ae1b
  | 1 => 0xc5cacaa8c5cacaf4855b1b1589888c1da754ed
  | 2 => 0x6aa0734f6aa0730639ada046f2f0f068da6346
  | 3 => 0xb3732073b37320183e36cde0237f00761d83b0
  | 4 => 0xc040407dfc7c7c5f10070180c3ddda801ff800
  | 5 => 0xfc7c7c01c040406020380e0703eeef7fe00000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xeaaac880c888c880eaaac880c888c880eaaac880c888c880eaaac880c888c880eaaac880c888c880eaaac880c888c880eaaac880c888c880eaaac880c888c880, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_13323
namespace PEqualNP.Outside.L_meta_13323
open PEqualNP.Outside.L_meta_13323.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs2_4_0 : Interval s2Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 1 := bs2_4_0
theorem alls2 : ∀ k ≤ 4, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_4 i (by omega) hi
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
theorem bs4_2_0 : Interval s4Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 3 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 6 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 1 := bs4_4_0
theorem alls4 : ∀ k ≤ 4, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 6 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 14 := bs5_4_0
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
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 12 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_96 : Interval gbAtlas 3 96 62 := block_range (n:=62) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 158 := (concat bgb_3_0 bgb_3_96)
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
theorem bgb_4_1152 : Interval gbAtlas 4 1152 77 := block_range (n:=77) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 1229 := (concat (concat (concat bgb_4_0 (concat bgb_4_96 bgb_4_192)) (concat bgb_4_288 (concat bgb_4_384 bgb_4_480))) (concat (concat bgb_4_576 (concat bgb_4_672 bgb_4_768)) (concat (concat bgb_4_864 bgb_4_960) (concat bgb_4_1056 bgb_4_1152))))
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
theorem bgb_5_4032 : Interval gbAtlas 5 4032 37 := block_range (n:=37) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 4069 := (concat (concat (concat (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 (concat bgb_5_288 bgb_5_384))) (concat (concat bgb_5_480 bgb_5_576) (concat bgb_5_672 (concat bgb_5_768 bgb_5_864)))) (concat (concat (concat bgb_5_960 bgb_5_1056) (concat bgb_5_1152 (concat bgb_5_1248 bgb_5_1344))) (concat (concat bgb_5_1440 (concat bgb_5_1536 bgb_5_1632)) (concat bgb_5_1728 (concat bgb_5_1824 bgb_5_1920))))) (concat (concat (concat (concat bgb_5_2016 bgb_5_2112) (concat bgb_5_2208 (concat bgb_5_2304 bgb_5_2400))) (concat (concat bgb_5_2496 (concat bgb_5_2592 bgb_5_2688)) (concat bgb_5_2784 (concat bgb_5_2880 bgb_5_2976)))) (concat (concat (concat bgb_5_3072 bgb_5_3168) (concat bgb_5_3264 (concat bgb_5_3360 bgb_5_3456))) (concat (concat bgb_5_3552 (concat bgb_5_3648 bgb_5_3744)) (concat bgb_5_3840 (concat bgb_5_3936 bgb_5_4032))))))
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
theorem bgb_6_1920 : Interval gbAtlas 6 1920 96 := block_range (n:=96) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2016 := (concat (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 (concat bgb_6_288 bgb_6_384))) (concat (concat bgb_6_480 bgb_6_576) (concat bgb_6_672 (concat bgb_6_768 bgb_6_864)))) (concat (concat (concat bgb_6_960 bgb_6_1056) (concat bgb_6_1152 (concat bgb_6_1248 bgb_6_1344))) (concat (concat bgb_6_1440 (concat bgb_6_1536 bgb_6_1632)) (concat bgb_6_1728 (concat bgb_6_1824 bgb_6_1920)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 72 := block_range (n:=72) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 72 := bgb_7_0
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 48, 49),(inputs.getD 4 zero, 33, 49),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 5 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 3, 11)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 6 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeaaac880c888c880eaaac880c888c880eaaac880c888c880eaaac880c888c880eaaac880c888c880eaaac880c888c880eaaac880c888c880eaaac880c888c880
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 9 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 49 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 14 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) (SBf 2) :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have s3 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 3 zero)) (SBf 3) :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
  have s4 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 4 zero)) (SBf 4) :=
    slice_correct (ms:=fixRows 48 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (3937060992 * 2 ^ 32 + 3364407424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_13323.Model.Repr at out
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

def mono : List Gate := [⟨.and,[0,1]⟩,⟨.and,[1,2]⟩,⟨.or,[0,3]⟩,⟨.and,[3,6]⟩,⟨.and,[0,5]⟩,⟨.or,[6,10]⟩,⟨.and,[7,8]⟩,⟨.or,[4,9]⟩,⟨.and,[11,13]⟩,⟨.or,[12,14]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,15⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 9) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3937060992 * 2 ^ 32 + 3364407424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3937060992 * 2 ^ 32 + 3364407424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_13323

open PEqualNP.Outside.L_meta_13323 in
theorem PEqualNP.Outside.L_meta_13323 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3937060992 * 2 ^ 32 + 3364407424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3937060992 * 2 ^ 32 + 3364407424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
