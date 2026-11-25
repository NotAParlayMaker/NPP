import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_13705.Model
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


end PEqualNP.Outside.L_meta_13705.Model

namespace PEqualNP.Outside.L_meta_13705
open PEqualNP.Outside.L_meta_13705.Model
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

def SBf (j : Nat) : Nat := [5, 5, 5, 5, 5, 7].getD j 0

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

end PEqualNP.Outside.L_meta_13705

namespace PEqualNP.Outside.L_meta_13705
open PEqualNP.Outside.L_meta_13705.Model
def s0K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x40628a042f195c32bc6370c6f985d30
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0xd1000096418ca390a318c424c2510530
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (i*4) 4
  | 3 => packedAt s0K3 (i*15) 15
  | 2 => packedAt s0K2 (i*26) 26
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (5+((h/1+packedAt s0K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s0K3 (96+((h/2+packedAt s0K3 (90+(h % 2)*3) 3) % 8)*4) 4
  | 2 => packedAt s0K2 (107+((h/1+packedAt s0K2 (104+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffdff3ffff1ffff1ff
  | 2 => 0xffffffffffffffffffffffedfc7f3fe3f0fe73
  | 3 => 0x76ff8fcffc7f0f9c
  | 4 => 0x78fff00fff800fe0
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffa0180202049440a5
  | 2 => 0x122324452122a652
  | 3 => 0x9416819484a2b18
  | 4 => 0x78a4eae920ccde0
  | _ => 0
def s0Atlas : Atlas := ⟨4,rawDecor 30 s0Pos s0Neg, 0xfcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_13705
namespace PEqualNP.Outside.L_meta_13705
open PEqualNP.Outside.L_meta_13705.Model
def s1K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xe421
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
  | 0 => 0xfffffffc0fffffc0ffffffffff80ffff1ffe3f
  | 2 => 0xf03f01fff03f03ff0f07c0fc0fff07c0eb33cc
  | 3 => 0xffc001ffffc003fff007ff000ffff800f3c3f0
  | 4 => 0x1fffffffffffff800000ffffffffc03ff
  | 5 => 0xfffffe00000003fffffffffff0000000fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x10820804608210401108c51461842946015615
  | 2 => 0x258c6ac8a39455cb074354d8a6b5258a6b32cc
  | 3 => 0x4316ad51450e9ad57085b6514b56b114b3c370
  | 4 => 0xa28d1a20a28c326aad020820c68c638dc01aa
  | 5 => 0x8c30e1c38c30e3b8cce638e380708420fea800
  | _ => 0
def s1Atlas : Atlas := ⟨4,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaafaaa0000faaaaaaafaaa0000faaaaaaafaaa0000faaaaaaafaaa0000faaaaaaafaaa0000faaaaaaafaaa0000faaaaaaafaaa0000faaaaaaafaaa0000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_13705
namespace PEqualNP.Outside.L_meta_13705
open PEqualNP.Outside.L_meta_13705.Model
def s2K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x9d43
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (i*5) 5
  | 3 => packedAt s2K3 (i*16) 16
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (6+((h/1+packedAt s2K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s2K3 (17+((h/1+packedAt s2K3 (16+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x7ffff83ffff83f07fff07fff83fffc0f39f3f3
  | 1 => 0x87c1ffc3e0fffff8707f8783fc3c1fffd64c9f
  | 3 => 0xf801fffc00ffc3ff807ff803ffc01ff0e78f1c
  | 4 => 0x1ffffff0003ffff800003ffffe000f80fe0
  | 5 => 0xfffe0000000003fffffffffc00000000fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x800880400040008090088880444422009131
  | 1 => 0x2112910909522128342485112428894c524486
  | 3 => 0x12a52290d2a406538859502aca8152a2a58b18
  | 4 => 0x5539c42a9836ab9d5d0c4443733380c4f80ec0
  | 5 => 0x663187331cc733e66e6e667062220308ff6000
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xeeaaeeaaeeaacc88eeaaeeaaeeaacc88eeaaeeaaeeaacc88eeaaeeaaeeaacc88eeaaeeaaeeaacc88eeaaeeaaeeaacc88eeaaeeaaeeaacc88eeaaeeaaeeaacc88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_13705
namespace PEqualNP.Outside.L_meta_13705
open PEqualNP.Outside.L_meta_13705.Model
def s3K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x9d43
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (i*5) 5
  | 3 => packedAt s3K3 (i*16) 16
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (6+((h/1+packedAt s3K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s3K3 (17+((h/1+packedAt s3K3 (16+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x7ffff83ffff83f07fff07fff83fffc0f39f3f3
  | 1 => 0x87c1ffc3e0fffff8707f8783fc3c1fffd64c9f
  | 2 => 0xf801fffc00ffc3ff807ff803ffc01ff0e78f1c
  | 4 => 0x1ffffff0003ffff800003ffffe000f80fe0
  | 5 => 0xfffe0000000003fffffffffc00000000fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x800880400040008090088880444422009131
  | 1 => 0x2112910909522128342485112428894c524486
  | 2 => 0x12a52290d2a406538859502aca8152a2a58b18
  | 4 => 0x5539c42a9836ab9d5d0c4443733380c4f80ec0
  | 5 => 0x663187331cc733e66e6e667062220308ff6000
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xeaeaeaeaeaeac8c8eaeaeaeaeaeac8c8eaeaeaeaeaeac8c8eaeaeaeaeaeac8c8eaeaeaeaeaeac8c8eaeaeaeaeaeac8c8eaeaeaeaeaeac8c8eaeaeaeaeaeac8c8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_13705
namespace PEqualNP.Outside.L_meta_13705
open PEqualNP.Outside.L_meta_13705.Model
def s4K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0xcd32
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 1
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (i*5) 5
  | 3 => packedAt s4K3 (i*16) 16
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (6+((h/1+packedAt s4K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s4K3 (17+((h/1+packedAt s4K3 (16+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfffff03e0f83f0ff0ff0ffff83c1e0f667e93
  | 1 => 0xf07c1ffffffffff07f07f0703fffffff9993ff
  | 2 => 0xff801ffc00ffc3ff8007ff803fc01ff0e1e31c
  | 3 => 0x1fffff0003fffff800003fffe000fe03e0
  | 5 => 0xffffe000000003ffffffffffc0000000fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x2119011845115101902902919a245226222691
  | 1 => 0x4002221004000202102102200490488089026
  | 2 => 0x622b5448d6a5175688a5ab04aea09962e16318
  | 3 => 0xcb53989294359b9b5ab08a093732d044f603c0
  | 5 => 0x8c6210e318c622ec6cc6cc4e04030188ddd800
  | _ => 0
def s4Atlas : Atlas := ⟨4,rawDecor 47 s4Pos s4Neg, 0xeeeaeeeaccc8ccc8eeeaeeeaccc8ccc8eeeaeeeaccc8ccc8eeeaeeeaccc8ccc8eeeaeeeaccc8ccc8eeeaeeeaccc8ccc8eeeaeeeaccc8ccc8eeeaeeeaccc8ccc8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_13705
namespace PEqualNP.Outside.L_meta_13705
open PEqualNP.Outside.L_meta_13705.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x400000952142180008d0e1e40019009912a161d2060094003245cfa700700965aacf1414b0008424c88d2a74da8008c6090886820122001ca0011c8ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30df30fe30fd30dd30fc30ff20ef20fe20fd20ed20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x3480021546b002e4d4f00000b0010291f0c53456e5832723100513e016236747156005e5b466d3a2261494000076f000d002c6a006c133b685d670900432b1e395f17652364001b1926285a3d475218350f00001a083f701611730069420e4b50002000001c00000a604e0238304c000024335944144a1d3466044155632f2a5c5725271206150000052d3c3700038081800a80000581000106010380030a048a0602080782a881800d80019b04800001830701db94a43b6a94877a5090ef2a121d794e42aea9c857a5090af2a121734c832bd2806579500ca7aa920d7d4d41ae29a836f52506d8a4a0ded4141bc282839f5350738a6a0ebd4941d629283b75150776a0a0ee141419f2a0833e548c67aa918dbd4931b6292633e540c67aa818db94831b6a90637a500c6f2a018cf952219eaa4435f53486b8a690cf950219eaa0435e53086baa610de94021bca80435e53902baa7205b94a40b6a94815e53102baa6205b94840b6a90817651102eaa22067d0730cea0e615d538c2dca5185b54a309faa2613c544c33ea8986715130cfa0a619d414c3b6a09876d0130ec202615e530c2dca4185b54830d7a0e41ad41c839e6190734c320af29c415d53882daa510764c2209faa2413c54483b260906bd5120d62a241af414835a82907ad4120f5a0241e8404839e60907a8c120e698241e9304839260905794c20aea98416e520827ca9884f55310daa0e215e53842baa7085b94a10b6a9421d930843d241086d50510ec98221e9204427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x892200002e0003005002aa69cb0000060098e01211e5a80a0180010001202180003d24c9500cb185314141ca1485050669601493196580534861c6550530b2588404c2d16110130c6151304822c6550520b258c40482e16110120b258e30482a8644c120e2d913048388644c120e2d513048388544c120e2d053048389414c120d254930843495348210e450530443a14148110
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x100190a14ebb22609048a76d5130482443b28298241421d5414c120
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
  | 5 => packedAt s5K5 (826+((h/15+packedAt s5K5 (736+(h % 15)*6) 6) % 56)*7) 7
  | 4 => packedAt s5K4 (3471+((h/39+packedAt s5K4 (3159+(h % 39)*8) 8) % 141)*8) 8
  | 3 => packedAt s5K3 (960+((h/8+packedAt s5K3 (912+(h % 8)*6) 6) % 37)*6) 6
  | 2 => packedAt s5K2 (199+((h/1+packedAt s5K2 (196+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf87fffe07c3e1f0f871fc7fff8783c1f067e93
  | 1 => 0xff83e1fffffffff007e1f8703ffffffe1993ff
  | 2 => 0xfffc01ff803fe1fff801ff803f803fe1e1e31c
  | 3 => 0x1ffffc001fffffe00003fffc001fe03e0
  | 4 => 0xfffffe00000001ffffffffffc0000001fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x4908d0230944a901a10a42919c48a44d022691
  | 1 => 0x10200244201000200220882200920910089026
  | 2 => 0x6311548919a88b56a8095304ad4132c5616318
  | 3 => 0x465a9912510ccd9b354c02093665a089b603c0
  | 4 => 0x8463001c623110ec4691a44e00060310ddd800
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfeeaccc8feeaccc8feeaccc8feeaccc8feeaccc8feeaccc8feeaccc8feeaccc8feeaccc8feeaccc8feeaccc8feeaccc8feeaccc8feeaccc8feeaccc8feeaccc8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_13705
namespace PEqualNP.Outside.L_meta_13705
open PEqualNP.Outside.L_meta_13705.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x858643822005a8e000c1652007a0000005400785000022682000e00707e4a0000001c865c1a004e00887400000036006a5e0000007644003c2432623a00044000008a00106e2c480080000000000000001800720000006068007c4c000000001442006c660a0656121e3e00002e00340084283000000000002a8c462006083800004100000010000107030004000040408200ffd50037f5400ff95003fd54005f55003fc5400ffd4c03fe5300ff54c03fc53007fd0c01fe43007f50c01fc4300ffd4803fe5200ff54803fc52007fd0801fe42007f50801fc42007fcc801fe32007f4c801fc3200ffd44037f5100ff94403fd51005f54403fc51007fd0401bf41007f90401fd41006f50401fc41007fcc401fe31007f4c401fc31007fc8401fe21007f48401fc2100ffd4003fe50005f94003fd5000ff140037c50007fd0001fe40007f50001fc40007fcc001df30007f8c001fd3000774c001fc30007fc8001ef20007f88001fd20007b48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x28400bbf5942001df8ca1000eff640800f7f3204000bf5902001df8c81002f7f5408001beaa04003bfd8c2002dfcc61000fde63080016f3184000bf58c2001fbac610002dd63080077e3184004bf98820065dcc41000afe61080017eb08400bdfd4420006faa210003bf4108001dea084003bf9802001efca01000f7c5008007ef9804003f74c02001fde401000ffa2008007f69004004fe48020015fecb88006fe65c4005bf32e20019f99710055facb8800b7d65c40013eb2e2002bf19710015fec98801efe64c4005df3262000af99310005fac98800bbd64c40015eb262002bf19310056fea9880037d54c40057fb1e2005bf98f10005fac78800afc63c40057fb162004bf98b10005fac58800afc62c4005bfa8e2002fd94710016faa38802bf551c4001baa8e2002efd0710017ec838800bbd41c4001faa0e2000ed5071001efca18800f7c50c4001ef9862000f74c310007de4188003ed20c40077fb2c2003dfd961001cfecb08006fe65840137eb2c2003bf1961001ef8cb0800e7c65840077fb242007bf99210005fac90800efc6484013bfaa42000df5521001dfec708016fe6384007ef31c2000b798e10005fac70800fdd63840016eb1c2003bf18e1001dfec508012fe6284007f73142000bb98a10005fac50800fed628400176b142003bf18a10045fac3080277f5184001bea8c2000efd06100077a830800efe6084007bf2842003df1421001fbe610800ffa3084007ee9842000fe4c210007b2610800fef2084007fd1042003fb48210007f24108003e92084007fb8842002fec4210045feca880037f65440013fb2a2001bf99510045faca88006fc6544011be32a20019f19510005fec88801efe64440017eb222007bf19110046fea8880037d54440017fb1a2005bf98d10005fac688016fc63440017fb122004bf98910005fac488012fc6244011bfa8a2008fd94510006faa288023f55144001baa8a2000efd0510007ec8288003bd4144001faa0a2000ed5051001efca08800f7c5044001ef9822000fe8c110007ba6088003f93044001ec9822000fbc8110007f44088003ed2044001fc9022000fa48110017f6208800ff610440077fb282001bf9941001efcca080067e650400d7eb282003df59410004faca0800efc65040077fb202007bf9901001f7cc808002be64040017eb202003ef590100057ac80800efc640400dbfaa02000df5501001dfec608016fe6304007ef3182000b798c10005fac60800fdd63040016eb182003bf18c1001dfec408012fe6204007f73102000bb98810005fac40800fed620400176b102003bf18810015fcc20800b7f5104005bea882002efd04100177a820800efe6004007bf2802003df1401001fbe600800fdd3004007f79002003fb4801001fee200800ffa1004007fa8802002fe44010
  | 1 => 0x3ec21c8007bf2864003df14320007be6190003dd30c8009f7b2e400cfb99720066dccb90033ed65c8001b6b2e4004fb19720027dec990003ee64c8001f6b264004fb19320067dea9900336f54c8019f72a6400cfb55320006daa990033ec54c8009f7b1e4000fb98f20007dac790013ec63c8019f7a9e400cfb94f20067daa790033ec53c8001f7a1e4000fb90f20007da8790003ec43c8009f7b0e4000fb98720007dac390013ec61c8019f7a8e400cdbd4720067dca390033ed51c8001b6a8e400cfb14720007de8390003af41c8001f720e4000fb507200075a8390003ec41c8001f798e4000fb8c720007da6390003ec31c8019f7a864003fb9432001edca190033ed50c8007f62864003db14320007de819000fee40c8001f6a064003fb10320007de6190003cf30c8007f71864000fb4c3200079a619000fec30c80077fb2c4001bf99620075facb1000efc65880077fb244007bf99220005fac91000efc648801dbfaa44000df5522001dfec710016fe6388007ef31c4000b798e20005fac71000fdd63880016eb1c4003bf18e2006dfac510036ed62880057f30c4000bf58620076fea3100037d5188001dfa0c4000ef5062001dfcc11000f7e5088007be2844003f7cc22001fba611000fef2088009fd904400dbfd9520006feca900027f65480037f32a400dbf5952000df8ca900377c65480033e32a4000bfd91200077ec890002bf644800f7f3224000bf5912003df8c890003bc64480015e322400ddfd5120006faa890002ff634800b7f31a4000bf58d2002df8c690037ef524801bf7292400dfb5492006fd8a490003ef4248001f72124000fb50920007d88490003ef3248001f71924000fb4c920007d86490002ff61480057e30a400ddfd4520006faa290003bf4148001dea0a4000fbc8520007dc4290003ed2148001f610a4003df9412001ef8a090003df3048001ee9824004fec812001fdc4090037ef6548001b7b2a400dfb9952006fdaca90037ec654801bb632a4000fbd91200075ec890003ee6448001f6b224000fb1912000758c890037ef544801bb7aa2400dfb9512006fdaa8900036d544801bf62a24000fbd8d20007dcc690003ed6348001f631a400dfbd4d2006fdca690037ed534801bf629a4000fbd0d20007dc8690003ed4348001f621a4000fbd8520007dcc290003ed6148001f630a400dfbd452006edea290037ee514801bf6a8a4000db5452006fd8a290003ef4148001d7a0a4000fb90520007da8290003ad4148001f620a4000fbcc520007dc6290003ed3148001f618a4000fbd8120007d6c090037ef5048007f72824003db9412006fdaa09000fec5048007b62824000fbd012001fdc8090003ed4048007f62024000fbcc1200079e609000fee3048001f69824000f34c12001fd8609000eff65080037f3
  | 2 => 0x30007be4398003de21cc001ee90e6000f708730087bea19800fde50cc007af2866010f75433001fb8a19800f5c50cc001efa066003f790330007ba819800fdc40cc0077fb2c6001bf99630095facb1800efc658c0077fb246007bf99230005fac91800efc648c025bfaa46000df5523008dfac718046dd638c0097f3146003fb98a30005dcc518002fd628c007f6b146000bb58a30015fcc318002fd618c025bfa8c6000df546300077e8318003bd418c0077f3046003df9423001ef8a11800fdf308c00bfd9846011bfd9530006feca980027f654c0037f32a6011bf5953000df8ca980477c654c0033e32a6000bfd91300077ec898002bf644c00f7f3226000bf5913003df8c898003bc644c0015e3226011dfd5130006faa898047df534c023ef29a6011f754d3008fb8a698003df434c001ef21a6000f750d30007b88698002ff624c0097e3126000f7cc930007bc6498003dd324c001ee1926000bfd8530015f8c2980477f514c001bea8a6000efd05300077a8298003df314c001ef18a6000f74c530007b8629800f7e504c007be2826005fecc13001fbc6098047df654c001afb2a6011f79953008fbaca98047dc654c023ae32a6000f7d91300073ec898003de644c001eeb226000f71913000738c898047df544c023afaa26011f79513008fbaa8980035d544c023ee2a26000f7d8930007bcc498003dd624c001ee3126011f7d493008fbca498047dd524c023ee2926000f7d0930007bc8498003dd424c001ee2126000f7d8530007bcc298003dd614c001ee30a6011f7d453008ebea298047de514c023eea8a6000d75453008fb8a298003df414c001cfa0a6000f790530007ba82980039d414c001ee20a6000f7c8530007bc4298003dd214c001ee10a6000f7d8130007b6c098047df504c007ef2826003d79413008fbaa09800fdc504c007ae2826000f7d013001fbc8098003dd404c007ee2026003bfd943000dfcca1803efd650c0077e3286003bfd903003dfcc818002fd640c0077e320600fdfd5030006faa818016fe630c0216f3186004bf9883001fdcc418002ee620c0017eb106003fb58830005dac41800afe610c0017eb08600fdfd4430006faa218003bf410c001dea086003bf9803001efca01800f7c500c007ef9806003fe8c03001fba6018017f9300c0097fb2e4001bf99720026fccb900067e65c80197eb2e4004df59720004facb90012fc65c80097fb264007bf99320005fac990012fc64c8019bfaa64000df55320025fec790016fe63c80017eb1e4004bf18f20067dea590013ee52c8019f6a964004fb14b20007de8590013ee42c8001f6a164004fb10b20007de6590013ee32c8001f69964004fb0cb20015fcc390002fd61c8019bfa8e4000df547200077e8390003bd41c8009f790e4000fb88720007da439001
  | 3 => 0xe10ca003df9825001cfcc12800f7a609400f7fb2e8001bf9974003efccba00067e65d002d7eb2e8007df59740004facba001efc65d000fbfaa68007ef9534003efaa9a005bbd54d00019eaa68005bf98f40005fac7a0012fe62d00017eb168002bf98740005fac3a005b7f51d0001bea8e8007efd07400077a83a000f7e50d0007be2868003bfd964001efecb2000e7f65900037f32c8015bf5964001df8cb2000f7c65900073e32c8014bf592400aefea9200037d549000b7f31c8003f798e40005bcc720002fd6390007eeb1c8000b758e400077c8720003bc43900097f3148003fb98a40005dcc520002fd6290007f6b148000bb58a400077c8520003bc42900057f30c8000bf586400aefea3200037d5190001dfa0c8000ef5064001dfcc12000f7e5090007be2848003efd024003ff68120052ff6550001bfb2a80009fd954000dfccaa0052fd65500037e32a8014df1954000cf8caa00537f5450029df2a28000df551400a77aa8a00033d54500017fb1a8005bf18d40005fec4a0012fc62500017fb0a8002bf185400a6fea2a00037d5150001dfa0a8000ef5054001efca0a000f7c505000ffda028003ef9014001dfeca20006fe6510007bf32880019f9944009dfaca2000f7d65100013eb288003bf1944003dfcc82001f7f541000fbeaa08005bf98c4001fbcc620002de63100017eb188003f758c40005bac620003be431000fde2188004bf9884001fdcc420002ee62100017eb108003fb58840005dac420003be421000fde2108002bf9844001fecc220002f661100017eb088003fd58440005eac22004f7f5110001bea888007efd04400077a822000efe6010007bf2808003df1404001f7e802000ffa4010007dea008007fe5004002dfecb98006fe65cc00bbf32e60019f99730085facb980177d65cc0013eb2e6005bf1973002dfec99801efe64cc0017eb266005bf19330086fea9980037d54cc021efa9e6005f794f30087baa798017dc53cc001efa1e6005f790f30007ba8798017dc43cc0097f3166000bf58b3002fbe6598003de32cc001ee9966005f70cb30015fcc398002fd61cc021bfa8e6000df547300077e8398003bd41cc00bef98e6000f78c730007ba6398017dc31cc007bf2866003df1433002fbecb98043de65cc021af32e6010f759730006bacb98017dc65cc00befb266000f799330007bac998017dc64cc021efaa66010d7d5330087bca998043dd54cc001aeaa66010f71533002fbec598003de62cc001eeb166005f718b30087bea598043de52cc021eea966010f714b30007be8598003de42cc001eea166000f710b3002fbec398003de61cc001eeb0e6005f718730087bea3980435f51cc021ef28e6010f754730006baa398043dc51cc001efa0e6000e7d0730007bc8398003dd41cc001cea0e6000f7107
  | 4 => 0x80afc650c4057fb206207bf990310177cc818802be640c4017eb206202ef590310057ac81880afc640c437bfaa06200df5503102dfcc618803df430c40bee2186204bf98831017dcc418802ee620c4017eb106202fb58831005dac418803de320c40bee1906202bf98431016fea21880b7d510c405dfa086202ef50431017be621880bf6310c405ee9886205fd4c43101dfcc01880bfa600c4017d3006200bf58031017f2c018802f9600c437be2806204bfd972100dfccb9086afd65c84097e32e4204bfd932103dfcc990802fd64c84097e326421adfd5321006faa990812ff63c840b7f31e4200bf58f21025f8c790813ee32c8401f6996421adfd4721006faa390803bf41c8401dea0e4203bf98321005fac19086b7c50c84057fb2c4201bf99621016fccb108067e65884337eb2c4202df59621004facb1080afc65884057fb244207bf992210177cc910802be64884017eb244202ef592210057ac91080afc6488433bfaa44200df55221015fec710816fe63884017eb1c4202bf18e210c5fac510803ef4288401f62144200fbcca21007d8651080afe6188405bfa8c4202df546210177e831080bbd4188405f790c4204fdc862101dfcc110802fd6088433be2844218bfd952100dfcca90862fd65484037e32a4200bfd912103dfcc890802fd644840f7e3224218dfd5121006faa890802ff6348401efb1a4200b7d8d2102dfcc690802fd634840b7e31a4200f718d21005b8c690803ee3248401f69924218dfd4521006faa290803bf4148401dea0a4204fdc8521017dc4290802ff60484077e3024218df14121015feca10806fe6508405bf32842019f994210bdfaca1080b7d65084013eb284202bf19421015fec81081efe6408405df3204200af99021005fac81080bbd64084015eb204202bf190210befea8108037d54084057fb184205bf98c21017bcc610802de63084017eb184202f758c21005bac61080afc63084097f3104200fbd0821027d88410803ef3208409f61904202bf98421016fea21080b7d5108405dfa084202ef50421017de421080bf62108405f69084204fd4842101dfcc01080bfa60084017d3004200bf58021017f2c010802f9600842fbe2804203dfd925001efcc92800f7d64940013eb24a003df1925001efec72800f7e6394007af31ca003df58e5001ebac72800f7c6394001bfa1ca000df90e50006fa87280037c4394007bfb14a003df98a5001edcc52800f7d6294007b6b14a003df18a50006fe85280037e4294001bea14a000df10a50006fe65280037e3294001be994a000df0ca5001efec32800f7e6194007beb0ca0009f5865001ef8c3280037f41940019fa0ca000df90650006fa83280033d4194001be20ca000dfcc650006fc63280037d3194001be18ca000dfc8650006fc43280037d2194001b
  | 5 => 0x924110d7ac92088b7f5490401beaa48205bf98e41005fac720812fe62904017eb148202bf98641016fea32080b7d5190405dfa0c8207fdd064101dfcc120802fd6090445be2848221bfd954100dfccaa08877e65504033f32a8221bf59541006facaa08027d65504037e32a8221dfd514110f7ea8a08873f5450443df2a28200df5514110f7aa8a08033d5450443de2a28200bfd8d41007bec6a0802df635040b7e31a8200f718d41005b8c6a0803bf4350401df21a8200ef50d410077886a0802ff6250401f7b128200bbd8941025f8c4a0803ec6250401763128200efd09410077c84a0803bd4250401de2128221dfd4541006faa2a081ff74150405df20a8200bfd814101df8c0a08877c5050443dfb2a8221ef9954110e7ccaa0887bd65504019eb2a8221ef195410077ec6a08039f6350401df31a8200ef58d4100778c6a08039c6350443dfa9a8221ef94d4110f7aa6a0887bc5350401dfb128200ebd89410077cc4a0803bd6250401de3128200eb1894110f7ea4a0887be5250443dea928221ef149410077e64a0803be3250401de9928200ef0c9410077ec2a0803b76150443dfa8a8221cfd45410177ca2a0887bd51504019ea8a8202ef145410077ec0a0803be6050401deb028200ef1814110f7ea0a0887be5050443dea828221ef1414110e78a0a080aff65104037f3288202df9944100cfcca2087efd6510405beb2882009f59441015f8ca2081efe64104415f3208207dfd504103efaa820816fe63104017eb188204bf98841005fac42080afe6110405bfa888202df544410177e822080bf64110405dea088207fd5044101dfcc020802fd601043fbe2808205bfd973100dfccb9887afd65cc40b7e32e6205bfd933103dfcc998802fd64cc40b7e326621edfd5331006faa998812fe62cc4017eb166205f7ccb31007ba659887b7f51cc401bea8e6200efd07310077a839880efe60cc4017eb06621edf14331015fecb18806fe658c405bf32c62019f996310edfacb1880b7d658c4013eb2c6202bf19631015fec91881efe648c405df3246200af99231005fac91880bbd648c4015eb246202bf192310eefea9188037d548c4397eb1c6200f7d0e31007b88718812fe628c4017eb146200f78ca31007b8651880afe618c405bfa8c6202df546310177e831880bbd418c405ef98c6205fdcc63101dfcc118802fd608c43bbe284621cbfd953100dfcca98872fd654c4037e32a6200bfd913103dfcc898802fd644c40f7e322621cdfd5131006faa898802ff624c401f7b126200bbd8931025f8c498803ec624c401763126200f7cc931007ba64988737f514c401bea8a6200efd05310077a8298817f7314c405ef18a6200bfd813101df8c0988737c504c4057fb286201bf99431016fcca188067e650c4377eb286202df59431004faca18
  | 6 => 0x13eb288404bf1944203dfcc82101f7f541080fdf2a08407df5504213f7aa8210033d541080b7f3188400bf58c42025fcc421013bf4210809f72108404ef5084203fda842100afe61108017eb088427dfd444201dfcc021002fd601084fbe2808405bfd973200dfccb9909afd65cc80b7e32e6405bfd933203dfcc999002fd64cc80b7e3266426dfd5332006faa999003df43cc80bee21e6402bf98732005fac39909b7f51cc8077f3066400bf58332136f8a199012ff658c8037f32c6425bf59632025f8cb19012ff648c80f7f3246400bf59232025f8c9190977f548c801beaa46424bf58e32025fcc519003ef428c809f62146404f7cca3202fde651900afe618c8017eb0c6425dfd463201dfcc119002fd608c84bbe2846424bfd953200dfcca99092fd654c8037e32a6400bfd913203dfcc899002fd644c80f7e3226424dfd5132006faa899003df434c801ee21a6400fbd0932007d88499017ef324c809ef1926400bfd8532015f8c2990937f514c8017fb026403bf18132126f8a099012ff650c8037f3286423bf59432025f8ca19012ff640c80f7f3206400bf59032025f8c81908f7f540c801beaa06405bf98c32025fcc419013df320c809f71906404f74c83202fda6419003cd320c8057f3086400bf5843211efea21900efe600c8017eb006423df14032006fec8a88027f6454401bf322a200df59151006f8c8a88037f6354401bf31aa200df58d51006f8c6a88037f4354401bf21aa200df50d51006f886a88037f6254401bf312a200df58951006f8c4a88037f4254401bf212a200df50951006f884a88037f3254401bf192a200df4c951006f864a88077f61544033fb0aa201ddd8551006fec0a88037e6054401beb02a200df1815101cf8c0a881eff65d04037f32e8207df9974100cfccba0882fd65d040fbeb2e82009f5974103df8cba081f7f54d0441dfaa68220cfd534103f7ca9a081f7d54d0441deaa68200cf5534103f78a9a0816fe63d04017eb1e8207efd0f410077c87a0803bd43d040fde21e8204bf98b41005fac5a081fbf42d0401df2168200ef50b4103f7885a08837f51d0401bea8e8203bf98341005fac1a08837c50d040fdfb2e8220ef997411067ccba0883bd65d04019eb2e8207ef1974103f7ec7a0803be63d0401deb1e8207ef18f411077ea7a0883be53d0441dea9e8220ef14f4103f7ec5a0803be62d0401deb168207ef18b411077ea5a0883be52d0441dea968220ef14b410077e65a0803be32d0401de9968200ef0cb411077ea3a08833f51d0405df28e8220ef547410067aa3a080bbc51d040fdfb068200ef983410077ac1a081fbc60d0441dfa868220ef943411077aa1a0883bc50d04419e2868202bfd964100dfccb2080b7e65904033f32c8222bf59641016facb208027d65904057e32c8221bf5
  | 7 => 0x801000000c00002800003c01407800804000802800400001000000000000000001000c00000c01402000c00800800c00800400c00001401801801800c03c00000003400c01400003400c00400000400400801800003000004003800c01400c00000000000801007401000402000001001000c00c00402c00800800000003400003803000401002000400c06000400c00801400800c02801c00400400000800000000400000001c00800800002400800000c00400800c00801c00400003000000c03c00400800c01800400000002400002000001000c00c05800801403000001403bfb22a8019fd915400e7ec8aa0037f6355001bf31aa800df58d54006f8c6aa0037f6255001bf312a800df58954006f8c4aa0037f61550013fb0aa800df98554006fac2aa0037c6155001bfb02a800df98154006fac0aa0037c60550073e302a807bfd974300dfccba181f7e65d0c033f32e862ebf5974303efacba18027d65d0c0f7e32e8607dfd534303efaa9a1812fe62d0c017eb168602bf98743005fac3a18bb7f51d0c077f3068600bf58343176f8a1a1816ff6590c037f32c862dbf5964302df8cb218b2fd6490c5bbfaa4862def95243006faa9218b7bd5490c019eaa48605bf98e4302f7e872181fdf4390c097f3148605fb98a43005dcc521802fd6290c0bf6b148600bb58a43015fcc321802fd6190c5bbfa8c8603bf98243005fac1218b77c5090c597fb2a8601bf99543165facaa1806fc6550c59bfaa28600df5514303fbe86a1817be4350c017fb128604bf18943005fec2a180afc6150c59bfa8a8600bfd814301df8c0a18b37c5050c0b7fb288601bf9944302efcca218067e6510c577eb288605df59443004faca21816fc6510c0f7f3208607dfd504303f7ca82181f7d5410c57deaa08600cf5504302dfcc621817bf4310c0bef2188605ef50c4303fba8621812fe6210c017eb108602bf98443005fac2218af7f5110c077f3008600bf5804315ef8a02181eff65d08037f32e8407df9974200cfccba10aafd65d080fbeb2e84009f5974203df8cba101f7f54d080fbeaa68405bf98f42005fac7a100afe61d08017eb0e842adfd474201dfcc1a1002fd60d0855be2868404bfd964200dfccb210a6fd65908097e32c8428bf5924214efea9210a7be5490801beaa48429ef552420067aa921016fe6390809ef31c8400b798e42005fac721013dd63908016eb1c8404bf98a420277e852101fef42908057f30c8400bf5864214efea32100efe60908017eb048429df14242145fecaa1006fe65508517eb2a8401bf19542146fea8a10037d54508017fb1a8405bf18d4203fde84a1013be42508017fb0a8402bf18542146fea2a1002ff60508077e3028428df14142025feca21006fe6510809bf32884019f9944213dfaca210137d651080
  | 8 => 0x9e1c1a59a620fd89a26f3440fa800347224138aaa8000002842783292822e9b3688794c9cb8e3b1aa2388016fa0a8f48f386113607691228382919e9cb1991488f6357951063ae71e98141f7163a0585d848a4d9b08452720d096d30514697f0401a700000010baf11be24f0440129e00ceb3b3190000002bb3260ea8091c38000000000b200200030f0000000002d18001e22dd00000000000000033f00000eb4787c00024a83f29f97c0000001718000e580010e80000000000013f20a00017a0000000000b680018a80000c8002e280000000012e0000000002e50001d5820a1c9090710002ed90da4f9040c815c8003258328eb13012235891e29019202580017496f00034f80012b902245acf89ea6c000034161ad381499f9c415b85a80001aab480027a97fa0c00030427d071abd80002208286f865b0d08329822e00000000000000028fa659ca0001d78b00000ea24d06c8a72f900007a0c5aa21d41f4ae78a627a1fd2df8c199c8ff8a39bf8c38ca27e29a17ca9d28d17e8609579a81d18001ff800000000004002001400402401400401800800000002401400400001402c06401000000000000000800000000001800800401001402801402406c00400001008400005801402c00403009c08c00c00c00000000800400000008800001c00403001800001002000400001400000800001800402000c00400000402c01c00000001800400801002800801400001c00406800c00401400800001800401401000801801000400402000404800c02400000000003000c00c00005c00001400002000000c00800004000800401801800000000009000800800800002000005400000807800000401800402c01000000001800000000000002400400403c00401800002c00000000400000000000800002400403c02400000000400400407c03c0180ac01002000c02800c00000000800400001c02000400400c00400000001402000000800402800c00800800800801401000002800000400c00000000001400000000002c00c04000c01801000408001800400c01003800001000400001400400400800800000803800003800400c00400800c00c00000400800400400c00402400001400c00000000000000000000002c00403c00400404400003c01402000001c00000000400000400400000400000001400000c00804000c00400400800c00002401400005400400000001c03402000003000401c00800400400000000800402800000c00000000800c01401000400000800400000800400005003c0b402000802000002001c01800000007400000403000400400402000800000401000c00000002c01400801000800000400001c01000401400c01001c03000000000c00c00400401000000c01800000000c00000403800000000c00400800c
  | 9 => 0x2c59931c880010e000207800348a2d93733100003100000010492606b05317780000000032680000000000000017733733380017211d891a698000001572e18c00edaa100027d800081a1ea7b0a887080005b8000000c88001eb8000e680022c80316b0f28e2ab616b80035c80017b99600000000d0001d282a8ca99e26680000025eb209d90191648cc13598a26480023710a0c21f21ea015b28a6186c1849e59ed98d1d51329aba5700028e08900018f21b1c0b0100b2761422a311f8000000002303548000000000000000000000000001ae19a2792aa000000005000000000002b390001979b5b42800000113a3800023900000006ab5000000000016700000003780015ea21036929a460002a99b183921f8080f180012a0000000c68000001d3a1e1a90001b62050000000000001dc8b900007f33c80000004b1230bc96800000004f80000031b00024011f04c2451e797300000000000023d00020c9bda3e8001bc2bca0e06e9fe0e734c1c20002b023a0001498000000900000000000000002140cd00000000000000033831c8bd0cd94d0000bb0000758002bb80002e000000144a12af39312aea71a8280007ca172c712eb420002c28c4ac394a01ba028000698000000000000000a00000000002f30a980000000001d00014a80005e190126a55b2db1a145b5222c2fd0630f7985b49a012261ff2a780000011a8002cd2592008320001531cf86e0000000002ba8001cc2c91821aa160284b3e20020684390525e03cb3e8001a280020f16e2d78000e1223359b1e8000001b10efb238480bb8001098000000aa0098671c52ea079b0480026d026a378963090b1a0f8000000000000000000000e20229068001b29de8000003068d619280031784a80000003d096995a299070001a60000940000138981a520210100000000029c0000c28000000001200000000002a60a596a00035a8120000001db8000001b98000000000c60000a30000000002dc2ee0002c20000b31c4a0ea6380a96992c8e18aa9870870003039d48000a08838dd248800a6eae0a689e522d188a5db2c0b0adf35ba6c800216230a8d9ac8dd9eb0001ae80031f0bea41841a082a0a4093418816eb5380004a25c0430002650fe23ca2480000026a9e480031f80016c82182fa958cb35831b99110f80009a8d22ad21a8d000003700000002980000f00000015580b95913c1d30002921d72ac0000002478000b40d1b3f8000000000913152600058000002ce8048000000072bd25b1fb8002550001b82c01a792805b1a02182580000000001f7800343a7c8002150498f400030fa93a9482c18694f29a8003111c00da0000560189f98000002fc13ab3312d0b8067b5a1381390749e728cb2ca0b83a92b0b783d98cac130da27a3f8002bf05d07e00
  | 10 => 0x2518868338000000388bda108003021faa9f0000001db1da02a2879dd2ce0000001b69a88a68ab91c0001828001aa91a0ec2e63492fa9b90e400025480617e34d1999fb0a428c0d51bb9fca0d84ea3ab5320b2198fc80000009da3e29181630c0000000000da8002910000000000001f19e1950b44a92a4a00027b8002941950000001149398ef2490000001520000001ef9f40260b72041919bea2b95f1172660001970ab1dc1440002588000002fb2f700025a83ea3b8b28bc2738000000000000002a73108000000002d88000680000000001c28001482af0000e98000018000002b09d0ab6a281a301a30e94e2b72530000f500000000031013d0000000002f20003248000000000001b404d80000000033d24e2b18001c990d2cc8d397128a00000000000000003b0000d111000006a0558990001a100000019b8000358000958000001e11f13210582f580000008eae880000033b9290302c69528000001e08001f3979b2421480017899408c80001717b2d500000003b846a80a25893b54000000103a3f00013b09780021f1642950458000c984090a94bb0187aaf02f8203283307a701b32da25b8231e2a1d9bc839a1c1969a588511c97680022aa320000000002a400000027f9850000001c700023b0003138d88001ceaf28210f92db00017901fa72824b1c0282c1b4e0b529ea5f034a09add8002d9ac63400778273510000000c1181ab8b172ae05534a0002dc80019d8c719c02f26b80030aa6900026419b1c12b318b9ba3088f224980000027f32330bac52ca9229c69d89d61898000ecb5b10800000000028880000018e9f80000002859d016c0000f81f28000000728821ed0330000000003389a4b1e18c0fb0042f7a44006a4700000027524bae583e00032e0000002870000002e900026100016900005f00000013d8598003162908001652061c6334b5c162878a93166a77180aab2bf89c9198c404c91bb4d893137af40deb508660000410001c30002fe00027e8f0a7c13a21581b1153319a221928b29b8001700dc8000000000df02d14182514fa360000e080000004e26793bb2292aa101b49471323340000650622be87380007d0000002d0852b27a3507512fa9887eb350f313facc2cb8f580015895689c00006b8000000ae00d968a4c0ad0001fa24e9278af800000088acb1cd9252a8923921159a3890034eb29a338002c32070000002ca22f09292894915185a2a5a2293c82b8000000003148ce0000002270000000460000000000001cd1740000000002d100021b9af8000000e8000072239aec8002ab80025d315a9b141000000289000000003a5c8000240001fdab80e3235ab20cb80000029633d89b90280000000010c0001b380000011300008a80000000000000000012707831894d8000002d20000002b5213
  | 11 => 0x8c00000006f2de92405f8952ec274800053b3c000073228a2b00034326d8000002f51c595d9a68000d680013e9332e4800330b4a98625f80016a9c80d4000112a4380000021201300015f9cf1d1000340800000178335b0e198885a608f734b97aa2e8002ba285257811a2a0000000000001ccb4b0a914b30808f0000578002feb059ee80000000c0002f88b580a000355000000355800136af08003142169890180003202fba8005c80004921d250aa000000008d1c7868b123250000002c88e623c0420b9a86b41a1121a01f00008080001c80032f8238002e800000014c0000150200000000000002eb80016daa2a6811d000000288275811346b1d800125ab2a8f2e30d919aab13119df80000000003a21199d00033624309b0002ea80026b107b0330a277ac8297a44976337817931b0b0000000000000002c492f2c4000134af9aef0002428862eb1dd80025380029daa91878000a504480000008400022fa6a0a2b0c9bf02e9bd2de3073273169428a206d1af000108800356aed2311ada732671a41fea03a631ad1f595e2e11e890585016214505700012c1c91b70f11662cd8000de00000009d090831ad480000000030600032e8a10000d70000000382fc8f682cac79ce0ed2560000001b88002480001a0b458e03280000002f68000dc32a963000155213ae407d8002c091580f9810000001f63519a18000000001ec23d8a82500c523180028b98300020d01eaee9758d98000cf9b7b328003398cc828800008ae200005c2252be0ac8690b10000518af0001248ba86d827800019a8a92083c0f98a1900b1294e80e1539462db83080014785400000015007b000154810a188761f007f9da9161351980791ca8000478740000ada540d288d80000032188495a0000000003562a80000001f9130a9708bb529219948010002468eb94313e27686280026f9118000618640591802222208000000002e3ad701d8002e68000001409750000be0002268000000002e02b7a290001a380000009f8000000002090880ff0b4b483302898000000000000db80000000028110c90190b0352a510333a95c1d6b2a3009541f308b3220fc0569e38c30fd1110000000000000000000000000000003572ad8e51f50971168103322369e62d408f993b0981c2522d300000020880000008a15d1df00024c80004700000000000026e3180000000000000002710001e300000000000028eada8000ac2968000eeaff97d8c78bf0000000c08f88001060002f60001ea8b88c91402c98000000e4a9900027980000000002b05ea9c89f0ba0000002a18000000000d32a68001189108000000002a480017085898b1842019ab1f68000db2b92628002d02a38d79e8172800133af4a8600000032f158016b4c889b3a15aad929e2528fb9608000520000000360
  | 12 => 0x3130bfa048e90cf2b41d82efaaca341e40001d99ba8b61ac000119221b59346220278ad61ec9bb12d967ab99e92819f09ee18e064866973943b02a329de15b18d97d18f9611f89d234f23485131d1181fc0002d683fb2d0000002708b38700000000002f1a420002fa0e880000010f32b8a79b00000000d827419f165b410002510000000ee0002330000998000fa00025a2fd9a9a178810d591e9908600a484f1e68079142998000002b39560000001838922568000001b52bc00000032b24b2af8770003003450df80011b0988d484d0000548f004b80000005087b8001b22410000000000000000fe80011781e2b58000000000000000001ef0000000002d8042ad2ad588e094b198000002cf0000000000e78ae80000002d8002ff00
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x1518c110007b1418c1100065f654c11008e5c654c11000755514c11000795414c11001f5a504c11001f58504c110014f8764c11000771514c110007b1414c11002edb764c110006d8764c1100075b754c11018f58754c1100075b654c11018f58654c1100079b744c11000798744c11018f5b544c11000759544c110007d3714c110007d0714c11001edb614c11001fd3614c11018f5b514c11018fd2514c11000759514c11018fd1514c11000751514c1100079b414c110007d2414c11000799414c110007d1414c11000791414c1100066f65c81100666c65c81100076551c8110007a541c8110007c930c8110005d97388110185e97288110007715188110007b141881100066f654811006e6c6548110007655148110007a5414811001f6a504811001f685048110007cb3048110007c93048110014f87648110007715148110007b14148110026eb7648110006e876481100076b754811017f6875481100076b654811017f686548110007ab7448110007a8744811017f6b5448110007695448110007e37148110007e0714811001eeb614811001fe3614811017f6b514811017fe2514811000769514811017fe15148110007615148110007ab4148110007e24148110007a94148110007e14148110007a141481100047f74594100147f71594100147d71594100163f41594100163d415941001c7e705941001c7c705941001e5f305941001e5d305941001e6f205941001e6d205941001e77105941001e75105941003e3e759901003e3d75990100163f51990100163d519901001e3e509901001e3c509901001e9f309901001e9d309901001eaf209901001ead209901000c7e75590100063f54590100063e75590100063d7559010014bf7159010014bd71590100163f51590100163d515901001e3e505901001e3c505901001e9f305901001e9d305901001eaf205901001ead205901001eb7105901001eb510590100047f76550100047d765501003e3e64550100063d645501001d7870550100065f5498c100065d5498c100165f5198c100165d5198c100169f4198c100169d4198c1001e5e5098c1001e5c5098c1001ecf2098c1001ecd2098c100065f5458c100065d5458c100165f5158c100165d5158c100169f4158c100169d4158c1001cdf7058c1001cdd7058c1001e5e5058c1001e5c5058c1001ecf2058c1001ecd2058c1001eda1058c10016d91058c100066f54988100066d54988100166f51988100166d5198810016af4198810016ad419881001e6e509881001e6c509881001ecf309881001ecd30988100066f54588100066d54588100166f51588100166d5158810016af4158810016ad415881001cef705881001ced705881001e6e505881001e6c505881001ecf305881001ecd305881001eea1058810016e91058810
  | 1 => 0x8e1001ecd2098e100047f7558e1000c7c7558e10004bf7458e1003cbc7458e100065f7558e100065c7558e100069f7458e100069c7458e100065f5458e100065d5458e100065f5158e1001e5e5058e1001e5c5058e1001ecf2058e1001ecd2058e100266e7598a100266d7598a100066f5498a100066d5498a100066f5198a1001eea7098a1001e6e5098a1001e6c5098a1001ecf3098a1001ecd3098a100047f7558a1000c7c7558a10004bf7458a1003cbc7458a100066f7558a100066c7558a10006af7458a10006ac7458a100066f5458a100066d5458a100066f5158a1001e6e5058a1001e6c5058a1001ecf3058a1001ecd3058a1001c7c76546100065e63546100065d63546100066e62546100066d625461004675615461001d7870546101c63f65d06101c63c65d06100069e63d06100069d63d0610006ae62d0610006ad62d061019e3f655061019e3c65506100069e63506100069d6350610006ae6250610006ad625061002eda634c21001ddb764c210006db764c2100075b754c2101bf58754c21001f5b654c21001f58654c2100079b744c21000798744c2101bf5b544c21000759544c21001fca624c21001fc9624c2101bf5b514c21000759514c2100079b414c21000799414c210026ea624821001deb7648210006eb76482100076b75482101b768754821001f6b654821001f686548210007ab7448210007a874482101b76b544821000769544821001fca634821001fc963482101b76b5148210007695148210007ab4148210007a9414821000c7e76d95100047d74d951001c7d71d951001c7e70d951001c7c70d951000c7c75d91100047f755911000c7c7559110004df735911002cdc7359110004ef7259110024ec72591100047e76551100047c765511003e3e64551100063d64551100047f7558d1000c7c7558d10004bf7458d1003cbc7458d10004ef7258d10024ec7258d100047f755891000c7c7558910004bf745891003cbc7458910004df735891002cdc735891001c7c765451001d78705451000e77765451001d74765451000e74765451001c74765451000577745451000773705451001d76705451001d7470545100077070545100167760545100177360545100063f65d05101063c65d05100073551d05100057575905101adb574905100063f655051010e3c65505101a737515051000735515051001cf476505100057575505101a737545051000735545051003eb77650510006b476505101a73675505100073575505100073765505101a7346550510007977350510007947350510007a77250510007a47250510007b37050510007b07050510016b76050510017b3605051019f36505051019f3450505100065f65cc1100865c65cc1100075551cc1100079541cc110195d9738c110005e9728c1100077
  | 2 => 0x1ef4f54cc1200074d54cc1201ef4f51cc1200074d51cc1200078f41cc1200078d41cc12001dcd70cc12001ecf60cc120007cb60cc12001f4e50cc12001f4c50cc12001fca10cc1200056f754c12006d6c754c120005af744c120005ac744c12001f68504c12001fc8304c1200074f754c1201e74c754c1200074f654c1201e74c654c1200078f744c1200078c744c1200078f644c1200078c644c1201e74f544c1200074d544c1201e74f514c1200074d514c1200078f414c1200078d414c12001dcf704c120007cb704c12001ecf604c120007cb604c1201e7cb504c12001f4e504c12001f4c504c12001fc8504c12001f48504c12001fca404c120007c9404c12001fca104c12003e3e64550200063d64550200666e62550200065f5498c200065d5498c200065f5198c2001e5e5098c2001e5c5098c2001ecf2098c2001ecd2098c200065f5458c200065d5458c200065f5158c2001e5e5058c2001e5c5058c2001ecf2058c2001ecd2058c200065e63544200065d63544200666e62544200167661544200067561544200069e63d04200069d63d04201deae62d04200069e63504200069d63504201d6ae6250420016b66150420006b561504200047f74597100163f41597100163d415971003e3e759931003e3d7599310016b671993100163f51993100163d51993101c63e50993101c63c509931000c7e75593100063f5459310004df735931002cdc7359310004ef7259310024ec72593100063e75593100063d75593100069f73593100069c7359310006af7259310006ac72593100163f51593100163d515931019e3e505931019e3c50593100047f76553100047d765531003e3e64553100063d645531001d787055310004ef7258f10024ec7258f10004df7358b1002cdc7358b1001577765471003677765471000577745471001736645471001735645471001d76705471001d74705471000575755071003eb664507101cf375450710007355450710015b77650710006b776507101cf367550710007357550710017366550710017356550710007977350710007947350710007a77250710007a4725071019f36505071019f3450507100865e65cc3100065d65cc3100069e64cc3100069d64cc3100075551cc3100079541cc31008e5e654c3100065d654c3100069e644c3100069d644c31000755514c31000795414c3100666e65c83100066d65c8310006ae64c8310006ad64c83100076551c8310007a541c831006e6e65483100066d6548310006ae6448310006ad6448310007655148310007a541483100047f755921000c7c755921001c7e765521001c7c765521003e3e64552100063d645521002e5e7598e1002e5d7598e100065f5498e100065d5498e100065f5198e1001eda7098e1001e5e5098e1001e5c5098e1001ecf209
  | 3 => 0xd71191200072f511912021f2e501912021f2c50191200056e76551200056c765512006d6f745512006f2f74551200072f64551200072c64551200056f71551200076b705512001d6e705512001d6c705512000768705512001d687055120006ac64d8d2006d6e7598d200056d7598d20005ae7498d20005ad7498d20005e97098d200056f7558d2006d6c7558d20005af7458d20005ac7458d20006ac6458d20005e77158d20005e47158d20005eb7058d20006cd6318d2006d6e75d0d200056d75d0d20004ee7690d20004ed7690d200072d5490d2006d6e7510d200056d7510d200072d5410d2001dea7010d20005e97010d2006d6c75d852006d6e75985200056d7598520005ae7498520005ad7498520006ac6498520005e970985200056f755852006d6c7558520005af7458520005ac7458520005cf7358520005cc7358520005eb705852006d6e75185200056d7518520005ae7418520005ad7418520006ac6418520005ce7318520005cd73185200056e76545200056c76545200056f74545200072f64545200072c645452006d6f715452006f67715452001d6e705452001d6c705452006d6e75d05200056d75d05202172f54d05200072d54d0520005ae76d0520005ac76d05202172e75d05200072d75d05200072f65d05202172c65d05202172f51d05200072d51d05201c72e50d05201c72c50d052006d6e75905200056d759052020dad749052001dea7090520005e97090520004ef7650520004ec765052006d6e75505200056d75505202072f54505200072d5450520005cf7350520005cc7350520006af7650520005ae7650520005ac7650520006ac7650520004ac76505202072e75505200072d75505200072f65505202072c65505200078f73505200078c7350520007a771505202072f51505200072d515052019f2e505052019f2c505052006d6e75105200056d75105201fdae741052001dea7010520005e9701052006d6e758c5200056d758c520005ae748c520005ad748c52001dea708c520005e9708c520004ef764c520004ec764c520004ee760c520004ed760c52006d6e750c5200056d750c520005ae740c520005ad740c52001dea700c520005e9700c52006d6e75d81200056d75d81200066f65d81200666c65d8120006af64d8120006ac64d812001f6a50d812001f6850d81200276a75d81200276975d81200076b65d81201f76865d8120007ab64d8120007a864d81201f76b54d81200076954d8120005e971d81201f76b51d81200076951d8120007ab41d8120007a941d812006d6e75d01200056d75d01200072d54d012001f6850d01200056f755012006d6c75501200072d545012006d6e75cc1200056d75cc1201ef4e75cc1200074d75cc1200074f65cc1201ef4c65cc1200078f64cc1200078c64cc120
  | 4 => 0x52200063d645522006e6d625522001d7870552200065f5498e200065d5498e200065f5198e2001e5e5098e2001e5c5098e2001ecf2098e2001ecd2098e200065f5458e200065d5458e200065f5158e2001e5e5058e2001e5c5058e2001ecf2058e2001ecd2058e2001eda1058e200065e63546200065d635462006e6d62546200167661546200067561546200069e63d06200069d63d06200069e63506200069d6350620016b66150620006b5615062000c7e76d95200047d74d952006e6e72d952006e6d72d95200047d71d952006e6d20d952000c7c75d91200063f54d912002cde73d9120004dd73d912003cbe76d91200063f65d91200063c65d91200063f75d91200063c75d91200069e73d91200069d73d9120006ad72d9120004bd71d91200063f51d91202263e50d91202263c50d91200047f755912000c7c7559120004be76191200063f65191200063c651912003e3e751912003e3d751912003ead7219120004bd71191200063f511912021e3e501912021e3c50191200047e76551200047c76551200063f645512003e3c645512001d7870551200047f7558d2000c7c7558d20004bf7458d2003cbc7458d20004f77158d20014f47158d2001cee76d092006d6e75d09200056d75d092003eac64909200072d5490920005ce7390920005cd739092001cec765092006d6e75109200056d7510920006af64109200072d541092001cee76cc92001dea70cc920006ac648c92001cec764c920006ac644c92002ecc634c920006cd630c92000c7c75d85200047e76545200047c76545200063f64545200063c6454520004be76d052003cbc76d05200063f65d05201063c65d0520004be7650520004bc76505200063f655052010e3c655052001cee768852006d6e75885200056d7588520005ae7488520005ad7488520006ac648852001dea708852001cec7648520005cf7348520005cc734852006d6e75085200056d7508520005ae7408520005ad7408520006ac6408520005ce7308520005cd730852001dea70085200065f65cc1200865c65cc1200069f64cc1200069c64cc1200065f654c12008e5c654c1200069f644c1200069c644c12001f58504c12001fc8204c12006d6e76d952006e6e76d95200056d74d95200056d71d952001d6e70d952001d6c70d952006d6c75d91200072f54d9120005ce73d9120005cd73d91200072f75d91200072c75d91200072f65d91200072c65d91200078e73d91200078d73d9120005ad71d91200072f51d91202272e50d91202272c50d912006d6e75991200056d7599120005ae7499120005e970991200056f755912006d6c7559120005eb705912006d6e75191200056d75191200072f5419120005ae7619120006ae76191200072e75191200072d75191200072f65191200072c6519120005a
  | 5 => 0x47f74597200666f72597200266c72597200047f71597200266f205972000c7e755932001cec72593200047f76553200047d765532023e3f645532003e3c645532023f2e425532023f2c425532001cec7258f20026cc3258f200656e75d0b200056d75d0b20026cc634cb2000c7e7558720004df735872002cdc735872001cec72587200047f76547200047d76547201063e65d07200063d65d072010e3e65507200063d65507200656e75887200056d7588720005ae7488720005ad7488720005cf7348720005cc73487200865e65cc3200065d65cc32008e5e654c3200065d654c3200256f76597200666f76597200056f74597200056f715972001d6e705972001d6c70597200656e75993200056d75993200656e75593200056f76553200056d76553200656f74553200672f745532023f2f645532023f2c64553200056f715532001d6e705532001d6c7055320026cc6358f200656e75d0f200056d75d0f20024ee7690f20004ed7690f200072d5490f200656e7510f200056d7510f200072d5410f200656e75987200056d7598720005ae7498720005ad74987200656e7558720005cf7358720005cc73587200056f76547200056d76547200056f74547200656f715472006767715472001d6e705472001d6c70547200656e75d07200056d75d07201df2f54d07200072d54d07201df2e75d07200072d75d07201df2e65d07200072d65d07201df2f51d07200072d51d07201c72e50d07201c72c50d07200656e75907200056d7590720004ef7650720024ec76507200656e75507200056d75507201d72f54507200072d5450720005cf7350720005cc7350720006af7650720006ac76507201d72e75507200072d75507201d72e65507200072d65507200078f73507200078c7350720007a771507201d72f51507200072d515072019f2e505072019f2c50507200656e75107200056d75107200656e758c7200056d758c720005ae748c720005ad748c720004ef764c720024ec764c720024ee760c720004ed760c7200656e750c7200056d750c720005ae740c720005ad740c72001dea700c720005e9700c7200656e75d03200056d75d03200072d54d03200056f75503200656c75503200072d54503200656e75cc3200056d75cc3202374e75cc3200074d75cc3202374e65cc3200074d65cc3202374f54cc3200074d54cc3202374f51cc3200074d51cc3200078f41cc3200078d41cc32001f4e50cc32001f4c50cc3200056f754c3200656c754c320005af744c320005ac744c3200074f754c32022f4c754c32022f4e654c3200074d654c3200078f744c3200078c744c32022f4f544c3200074d544c32022f4f514c3200074d514c3200078f414c3200078d414c320007cb704c32001f4e504c32001f4c504c32001fca104c32003e3e645
  | 6 => 0xf755893008d5c75589300059f74589300059c74589300069c6458930005d77158930005d47158930005db7058930006cd621893008d5e75d09300055d75d0930004de7690930004dd76909300071d549093008d5e75109300055d75109300071d541093001dda7010930005d9701093008d5c75d853008d5e75985300055d75985300059e74985300059d74985300069c6498530005d970985300055f755853008d5c75585300059f74585300059c7458530005cf7258530005cc7258530005db705853008d5e75185300055d75185300059e74185300059d74185300069c6418530005ce7218530005cd72185300055e76545300055c76545300055f74545300071f64545300071c645453008d5f715453008f57715453001d5e705453001d5c705453008d5e75d05300055d75d05302771f54d05300071d54d05300059e76d05300059c76d05302771e75d05300071d75d05300071f65d05302771c65d05302771f51d05300071d51d05301c71e50d05301c71c50d053008d5e75905300055d759053026d9d749053001dda7090530005d97090530004df7650530004dc765053008d5e75505300055d75505302671f54505300071d5450530005cf7250530005cc72505300069f76505300059e76505300059c76505300069c76505300049c76505302671e75505300071d75505300071f65505302671c65505300078f72505300078c72505300079771505302671f51505300071d515053019f1e505053019f1c505053008d5e75105300055d751053025d9e741053001dda7010530005d9701053008d5e75885300055d75885300059e74885300059d748853001dda7088530005d97088530004df7648530004dc7648530004de7608530004dd760853008d5e75085300055d75085300059e74085300059d740853001dda7008530005d9700853008d5e75d81300055d75d81300065f65d81300865c65d81300069f64d81300069c64d813001f5a50d813001f5850d813002f5a75d813002f5975d81300075b65d81302575865d81300079b64d81300079864d81302575b54d81300075954d8130005d971d81302575b51d81300075951d81300079b41d81300079941d813008d5e75d01300055d75d01300071d54d013001f5850d01300055f755013008d5c75501300071d545013003e3e64550300063d64550300865e63550300066f54988300066d54988300066f519883001e6e509883001e6c509883001ecf309883001ecd30988300066f54588300066d54588300066f515883001e6e505883001e6c505883001ecf305883001ecd30588300865e63544300066e62544300066d625443001676615443000675615443024e9e63d0430006ae62d0430006ad62d04302469e6350430006ae6250430006ad6250430016b66150430006b56150430
  | 7 => 0x8a300066f5198a3001e6e5098a3001e6c5098a3001ecf3098a3001ecd3098a300066f5458a300066d5458a300066f5158a3001e6e5058a3001e6c5058a3001ecf3058a3001ecd3058a3001eea1058a3008e5d63546300066e62546300066d6254630016766154630006756154630006ae62d0630006ad62d0630006ae6250630006ad6250630016b66150630006b5615063000c7e76d95300047d74d953008e5e73d953008e5d73d95300047d71d953008e5d30d953000c7c75d91300063f54d9130024ee72d9130004ed72d913003cbe76d91300063f65d91300063c65d91300063f75d91300063c75d91300069d73d9130006ae72d9130006ad72d9130004bd71d91300063f51d91302863e50d91302863c50d91300047f755913000c7c7559130004be76191300063f65191300063c651913003e3e751913003e3d751913003e9d7319130004bd71191300063f511913027e3e501913027e3c50191300047e76551300047c76551300063f645513003e3c645513001d78705513001cde76d0d3008d5e75d0d300055d75d0d3003e9c6490d300071d5490d30005ce7290d30005cd7290d3001cdc7650d3008d5e7510d300055d7510d300069f6410d300071d5410d300069c64cc93001cde768c93001dda708c93001cdc764c9300069c644c930026cc624c93000c7c75d85300047e76545300047c76545300063f64545300063c6454530004be76d053003cbc76d05300063f65d05301063c65d0530004be7650530004bc76505300063f655053010e3c655053001cde768c53008d5e758c5300055d758c5300059e748c5300059d748c5300069c648c53001dda708c53001cdc764c530005cf724c530005cc724c53008d5e750c5300055d750c5300059e740c5300059d740c5300069c640c530005ce720c530005cd720c53001dda700c53008d5e76d953008e5e76d95300055d74d95300055d71d953001d5e70d953001d5c70d953008d5c75d91300071f54d9130005ce72d9130005cd72d91300071f75d91300071c75d91300071f65d91300071c65d91300078e72d91300078d72d91300059d71d91300071f51d91302871e50d91302871c50d913008d5e75991300055d75991300059e7499130005d970991300055f755913008d5c7559130005db705913008d5e75191300055d75191300071f54191300059e76191300069e76191300071e75191300071d75191300071f65191300071c65191300059d71191300071f511913027f1e501913027f1c50191300055e76551300055c765513008d5f745513008f1f74551300071f64551300071c64551300055f71551300075b705513001d5e705513001d5c705513000758705513001d5870551300069c64d893008d5e75989300055d75989300059e74989300059d7498930005d970989300055
  | 8 => 0x675755844003eb6745844003e77545844003e755458440006b6435844003eb44358440006b6425844003eb4425844001e76505844001e74505844001eb7405844001eb5405844001ed7305844001ed5305844001ee7205844001ee520584400047f76544400047d76544400065e63544400065d63544400066e62544400066d625444001676615444000675615444001d78705444010e3e65504400063d65504400059c73504400069e63504400069d6350440005ac7250440006ae6250440006ad6250440016b661504400047f74597300865f735973002e5c73597300047f715973002e5f305973000c7e755933001cdc73593300047f76553300047d765533028e3f645533003e3c645533028f1e435533028f1c43553300855e75d0f300055d75d0f3001cdc7358b3002ecc3258b3000c7e755873001cdc7358730004ef7258730024ec72587300047f76547300047d76547301063e65d07300063d65d073010e3e65507300063d65507300855e758c7300055d758c7300059e748c7300059d748c730005cf724c730005cc724c73002d5f76597300865f76597300055f74597300055f715973001d5e705973001d5c70597300855e75993300055d75993300855e75593300055f76553300055d76553300855f74553300871f745533028f1f645533028f1c64553300055f715533001d5e705533001d5c705533002ecc6258b300855e75d0b300055d75d0b3002cde7690b30004dd7690b300071d5490b300855e7510b300055d7510b300071d5410b300855e75987300055d75987300059e74987300059d74987300855e7558730005cf7258730005cc72587300055f76547300055d76547300055f74547300855f715473008757715473001d5e705473001d5c70547300855e75d07300055d75d073024f1f54d07300071d54d073024f1e75d07300071d75d073024f1e65d07300071d65d073024f1f51d07300071d51d07301c71e50d07301c71c50d07300855e75907300055d7590730004df765073002cdc76507300855e75507300055d75507302471f54507300071d5450730005cf7250730005cc72507300069f76507300069c76507302471e75507300071d75507302471e65507300071d65507300078f72507300078c72507300079771507302471f51507300071d515073019f1e505073019f1c50507300855e75107300055d75107300855e75887300055d75887300059e74887300059d7488730004df764873002cdc764873002cde7608730004dd76087300855e75087300055d75087300059e74087300059d740873001dda7008730005d970087300855e75d03300055d75d03300071d54d03300055f75503300855c75503300071d545033003e3e64552300063d645523008e5d635523001d7870552300066f5498a300066d549
  | 9 => 0xb405524002e5e7598e4002e5d7598e400065f5498e400065d5498e400065f5198e4001e5e5098e4001e5c5098e4001ecf2098e4001ecd2098e400047f7558e4000c7c7558e400065f7558e400065c7558e400065f5458e400065d5458e400065f5158e4001e5e5058e4001e5c5058e4001ecf2058e4001ecd2058e402863f6590e40005ae7290e4027e3f6510e400069d6310e400266e7598a400266d7598a400066f5498a400066d5498a400066f5198a4001e6e5098a4001e6c5098a4001ecf3098a4001ecd3098a400047f7558a4000c7c7558a400066f7558a400066c7558a400066f5458a400066d5458a400066f5158a4001e6e5058a4001e6c5058a4001ecf3058a4001ecd3058a402263f6590a400059e7390a4021e3f6510a40006ad6210a400047f755864000c7c755864001c7c76546400065e63546400065d63546400066e62546400066d62546400167661546400067561546401c63f65d06401c63c65d06400069e63d06400069d63d0640006ae62d0640006ad62d0640014bf765064019e3f655064019e3c65506400059c73506400069e63506400069d6350640005ac7250640006ae6250640006ad6250640016b66150640006b5615064000c7e76d954001c7d74d95400047d71d954001c7c765514001d78705514000e3f765514001d3c765514000e3c765514001c3c765514028e3c635514023e3c62551400053f71551400073b705514001d3e705514001d3c705514000738705514003e3f605514003f3b605514000c7c75d85400063d54d85400047e76545400047c76545400053d75d05400063f65d05401063c65d054001cbc76505400053d75505400063f655054010e3c6550540006b7615054003c7f745944003c7d745944003e3c435944003e3c42594400047f715944003e3f415944001c7e705944001c7c705944001e3f405944001e3d405944001e5f305944001e5d305944001e6f205944001e6d205944003e5f5498c4003e5d5498c400065f5198c4003e9f4198c4001e5e5098c4001e5c5098c4001ecf2098c4001ecd2098c4003e5f5458c4003e5d5458c400065f5158c4003e9f4158c4001e5e5058c4001e5c5058c4001ecf2058c4001ecd2058c400063d6590c400069d6390c40005ae7290c4003e6f549884003e6d54988400066f519884003eaf419884001e6e509884001e6c509884001ecf309884001ecd309884003e6f545884003e6d54588400066f515884003eaf415884001e6e505884001e6c505884001ecf305884001ecd30588400063d65908400059e7390840006ad629084001676759844001675759844003e77549844003e75549844001e76509844001e74509844001ed7309844001ed5309844001ee7209844001ee5209844000c7e755844000677515844003eb74158440006767558440
  | 10 => 0x8c210165d5158c210169f4158c210169d4158c21016cf2158c21016cd2158c21004df7058c210065c5058c21026cf2058c21006ad64d0821006cd63d0821004ed76cc821006cd63cc82101e7b759802101e7875980210067b549802100679549802101eda739802101ed973980210167b5198021016795198021016bb4198021016b941980210047f755802100c7c7558021006785058021026eb20580210067b75580210067875580210067b5458021006795458021006da7358021006d97358021026ea7258021006eb4258021026e84258021006eb3258021026e832580210167b5158021016795158021016bb4158021016b94158021016eb2158021016e9215802101e3f74592500047f715925001c7c705925001e3e405925001e3c405925001e5f305925001e5d305925001e6f205925001e6d205925001c7e76d0e500047d76d0e500056e7290e500056d7290e5001c7e7610e500047d7610e5001c7e76d0a500047d76d0a500055e7390a500055d7390a5001c7e7610a500047d7610a500074d320ca500047f745865001e77715865001c7c705865001e5f305865001e5d305865001e6f205865001e6d205865001e76105865001e74105865001c7e76d06500047d76d06500063d64d06501c63e76d06500063d76d06501c71e63d06501c71d63d06501c72e62d06501c72d62d06500063d61d06501c63e60d06501c73a60d065001c7e76906500047d769065019d3d74906500067561906500047d76506500063d64506500055f73506500055c73506500056f72506500056c725065000675615065019e3e76506500063d76506500071f73506500071c735065019f1e635065019f1d63506500072f72506500072c725065019f2e625065019f2d625065000737715065019f3661506500063d615065019f35615065000635615065019e3e605065019f3a605065001c7e76106500047d76106501c53e741065001c7e768c6500047d768c6500053e748c6500053d748c6500056f724c6500056c724c65001c7e760c6500047d760c6500053e740c6500053d740c6500056e720c6500056d720c65001d7a700c65000579700c65001c7e76886500047d76886500053e74886500053d74886500055f73486500055c734865001c7e76086500047d76086500053e74086500053d74086500055e73086500055d730865001d7a70086500057970086500047f715974003e3f415974003d3f765534009e3f765534028e3e635534023e3e62553400053f715534001d3e705534001d3c705534000c7e75587400063d5458740004df735874002cdc7358740004ef7258740024ec725874003eb741587400047f76547400047d765474001d7870547400053d755074010e3e65507400063d655074001c7c76552400a63d645524001d78705524003f3
  | 11 => 0x66d54988310166f51988310166d5198831016af4198831016ad4198831004ed70988310066c509883102ecf309883102ecc32588310066f54588310066d5458831006cf435883102ecc43588310166f51588310166d5158831016af4158831016ad4158831016cf3158831016cd3158831004ef70588310066c505883102ecf3058831004dd768c831006cd628c83101e7b759803101e7875980310067b549803100679549803101eea729803101ee972980310167b5198031016795198031016bb4198031016b941980310047f755803100c7c755803100678505803102edb30580310067b75580310067875580310067b545803100679545803102eda7358031006db435803102ed84358031006ea7258031006e97258031006da325803102ed832580310167b5158031016795158031016bb4158031016b94158031016db3158031016d9315803123e3f645532103e3c6455321026cc634cb210176621547210047f755832100c7c7558321004bf745832103cbc7458321026eb20583210047f74596210163f41596210163d415962101c7c705962103e3e759922103e3d75992210163f51992210163d51992210063c509922100c7e75592210063f5459221004df735922102cdc73592210063e75592210063d75592210069f73592210069c7359221006af72592210163f51592210163d51592210063c50592210047f76552210047d765522103e3e64552210063d6455221006ad6410a210072d5410a21296cf630ca210047f755822100c7c7558221004df735912102cdc7359121004ef72591210063f645512103e3c645512102cde76d8d210065f54d8d210065d54d8d210065f51d8d21004dd70d8d210065c50d8d21004ef7258d21004de7618d210065f5418d210065d5418d2102ecd7218d210065f5118d21296ce2118d21296cc2118d21004dd7018d210065c5018d21004ee768c92102ecc638c921014ec764c92102ecc634c9210065f63545210065c63545210176421545210069f63d05210069c63d05210069f63505210069c6350521017a4215052100c7e75d81210047d75d81210047f74594210163f41594210163d415942101c7c70594210266f205942103e3e759902103e3d75990210163f51990210163d51990210063c5099021026af209902100c7e75590210063f5459021024ec72590210063e75590210063d7559021026ac72590210163f51590210163d51590210063c5059021026af20590210047f76550210047d765502103e3e64550210063d645502123f2c42550210065f5498c210065d5498c210165f5198c210165d5198c210169f4198c210169d4198c21004dd7098c210065c5098c21026cf2098c21024ec7258c21026cc3258c210065f5458c210065d5458c21026cc7258c21026cc4258c210165f515
  | 12 => 0xd65189410062d65189410078f63189410078c63189410072f5118941005ad70189410072c5018941005b7714c941015b4714c9410078d320c941015b6710c941005b5710c94110d3e75d85410053d75d85411063e65d85410063d65d85410069f63d85410069c63d8541006af62d8541006ac62d854129f3751d854103f3675d854103f3575d854129f3665d85410073565d85410079763d85410079463d8541007a762d8541007a462d8541005b570d854129f3450d854110d3f765454110d3d76545410071f63545410071c63545410072f62545410072c62545410153f715454110f3771545410163f615454100737615454119d3c705454101737105454110d3e75d81410053d75d81410063d65d81410073850d814119d3c75981410059e73981410059d73981410069c6398141005ae7298141005ad7298141006ac62981410053f755814110d3c75581410063d65581410059f73581410059c7358141005af7258141005ac725814110d3e75181410053d75181410059e73181410059d73181410069c6318141005ae7218141005ad7218141006ac621814119f3850181410163f41594410163d415944101c7c70594410047f755804100c7c755804128e3f645533103e3c64553310175631547310047f755833100c7c7558331004bf745833103cbc745833102edb30583310047f74596310163f41596310163d415963101c7c705963103e3e759923103e3d75992310163f51992310163d51992310063c509923100c7e75592310063f5459231004ef7259231024ec72592310063e75592310063d75592310069f7359231006af7259231006ac72592310163f51592310163d51592310063c50592310047f76552310047d765523103e3e64552310063d64552310069d6410e310071d5410e310047f755823100c7c7558231004df7359131004ef7259131024ec72591310063f645513103e3c64551310066f54d89310066d54d89310066f51d8931004ed70d89310066c50d89310066f54189310066d54189310066f5118931296ce3118931296cc3118931004ed70189310066c5018931004de76cc931026cc62cc931014dc764c931026cc624c9310066f62545310066c6254531017543154531006af62d0531006ac62d0531006af6250531006ac625053101794315053100c7e75d81310047d75d81310047f74594310163f41594310163d415943101c7c705943102e5f305943103e3e759903103e3d75990310163f51990310163d51990310063c509903102e9f309903100c7e75590310063f545903102cdc73590310063e75590310063d755903102e9c73590310163f51590310163d51590310063c505903102e9f30590310047f76550310047d765503103e3e64550310063d645503128f1c43550310069d64d0c310066f5498831
  | 13 => 0x514103e3f615514103f37615514119d3c705514100c7e75d8d410047d75d8d410065e65d8d410065d65d8d410071f54d8d410071d54d8d410065e75d8d410065d75d8d410065f54d8d410065d54d8d410065f51d8d41004dd70d8d410065c50d8d410065e6518d410065d6518d410071f5418d410071d5418d4102e5e7518d4102e5d7518d410065f5418d410069e5418d410065d5418d410069d5418d410061d5418d410065f5118d41004dd7018d410065c5018d4110d3e75d0d410053d75d0d4102e9c63d0d41014be7690d410063d6590d41005ae7290d41005ad7290d41014bc7650d4110d3e7510d410053d7510d410063d6510d410069f6310d4100c7e75d89410047d75d89410066e65d89410066d65d89410072f54d89410072d54d8941006cf63d8941006cc63d89410066e75d89410066d75d89410066f54d89410066d54d89410066f51d8941004ed70d89410066c50d89410066e65189410066d65189410072f54189410072d5418941006cf6318941006cc63189410266e75189410266d75189410066f5418941006ae54189410066d5418941006ad54189410062d54189410066f5118941004ed70189410066c501894110d3e75d09410053d75d0941026ac62d0941014be76909410063d65909410059e73909410059d7390941014bc765094110d3e75109410053d75109410063d6510941006af621094100c7f765454110c7d76545410053f74545410065f63545410065c63545410066f62545410066c625454101734415454100c7e75d81410047d75d81410063d54d81410067850d814110e3f76595410071f73595410071c73595410072f72595410072c72595410053f71595410073771595410053771595410073b705954119d3c705954100738705954100538705954110d3e75d8d410053d75d8d410071e75d8d410071d75d8d410071e65d8d410071d65d8d410071f51d8d410059d70d8d410071c50d8d410063d6598d410059e7398d41005ae7298d41005ad7298d41005b57198d41005af7258d41005ac7258d41005b77158d4110d3e7518d410053d7518d410063d6518d410059e7618d410069e7618d410071e7518d410071d7518d410069f6518d410071e6518d410069d6518d410071d6518d410061d6518d410071f5118d410059d7018d410071c5018d4110d3e75d89410053d75d89410072e75d89410072d75d89410072e65d89410072d65d89410078f63d89410078c63d89410072f51d8941005ad70d89410072c50d89410063d65989410059e73989410059d7398941005ae7298941005b571989410059f73589410059c7358941005b7715894110d3e75189410053d75189410063d6518941005ae7618941006ae76189410072e75189410072d7518941006af65189410072e6518941006ad65189410072
  | 14 => 0xc7c7558232026eb20582320063f645513203e3c6455132024de76d0d32025ce72d0d320071d5410d3202cee76d093202dce73d09320072d541093200c7e75d81320047d75d813223e3f645503203e3c6455032025cf764c832006cf764c8322aece644c832026cc644c8322a74f544c8320074d544c832295cc714c8322a74f514c832005cf704c8322a74c504c832006cd32584320047f755803200c7c7558032004bf745803203cbc7458032006cd325803200678505803202edb3058032026eb205803201c7e70d91510063f649915110d7571991510055f73591510055c73591510056f72591510056c72591511057771591510057b70591510057870591510053e74d8d510053d74d8d510065f6398d510e5757198d510056f7258d510056c7258d510f5777158d510047e76d0d510047d76d0d510056e7290d510056d7290d510047e7610d510047d7610d510053e74d89510053d74d89510c57571989510055f73589510055c73589510d57771589510047e76d09510047d76d09510055e73909510055d73909510047e76109510047d761095100577714c95101574714c9510074d320c9510055e73981510055d73981510056e72981510056d729815104575719815104d7771581510053e74181510053d74181510055e73181510055d73181510056e72181510056d721815101e7a60181511063f745974103e3c745974103e3c435974103e3c425974103e3f415974101c7c705974103e3f405974103d3f76553410fe3f765534128e3e635534123e3e62553411c53c7055341014bc7458f410063d6590f41005ae7290f41005ad7290f41014bc7458b410063d6590b410059e7390b410059d7390b4100c7f76547410053f74547410173641547410047f755834100c7c7558341014bc74583410063d545834103d3f76597411063f765974103e3c635974103e3c62597411053f71597411c53c705974103e3f60597410063d6598f41005ae7298f41005ad7298f410063d6598b410059e7398b410059d7398b410078d320cb411053f76547410153f71547411073771547410163d61547411c53c70547410173710547411c53c75983410059e73983410059d7398341005ae7298341005ad72983410053f75583411053c75583410063d65583410163f41596410163d415964101c7c705964101677105964100c7f765524110e3d645524100577715524103f3741552410047f755824100c7c75582410057870595411147f74595410063f74595410065f73595410065c73595410066f72595410066c72595411047f71595410067771595410067b705954101c7c705954100678705954101c78705954110d3f745514100577715514103f34415514100e3f765514100e3c765514128e3c635514123e3c625514100737715514100734715
  | 15 => 0xf64d85541063f74d855401c7e70d855410d3d74985541153f745855410e3f64585540055f73585540055c73585540056f72585540056c72585540057b70585540057870585540a53d74981540055e73981540055d73981540056e72981540056d72981540ad3f74581540055e73181540055d73181540056e72181540056d721815400576711815400575711815401e7a601815428e3e435974303e3c43597430047f715974303e3f415974301c7c705974300c7e755874303eb741587430047f755834300c7c755834303f1f435524300e3f765524300e3c76552430071f735524328f1c735524303e3e635524323e3e625524328f2e625524328f2d62552430053f71552432853c70552430066f5498a43006ae5498a430066d5498a43006ad5498a430062d5498a430066f5198a43004ed7098a430066c5098a4302ecf3098a430066f5458a430066d5458a432aecf4358a4302ecc4358a430066f5158a43004ef7058a430066c5058a4302ecf3058a430063d54586430047f755824300c7c75582430063d545824300678505824302edb305824303f1c435514300c7e75d81430047d75d81430047f715944303e3f415944301c7c705944302e5f305944303d3f76550431763f765504328e3e635504303f1e635504323e3e62550430053f715504327d3c705504300c7e75584430063d5458443004ef7258443024ec725844303eb7415844302ed431584430047f755804300c7c75580430063d545804302edb305804323e3e425974203e3c42597420047f715974203e3f415974201c7c705974200c7e755874203eb741587420047f755834200c7c755834203f2f425524200e3f765524200e3c765524228e3e635524223f1e635524223f1d63552420072f725524223f2c725524203e3e62552420053f71552422253c70552420065f5498e420069e5498e420065d5498e420069d5498e420061d5498e420065f5198e42004dd7098e420065c5098e42026cf2098e420065f5458e420065d5458e422aecf4258e42026cc4258e420065f5158e42004df7058e420065c5058e42026cf2058e420063d54586420047f755824200c7c75582420063d5458242006785058242026eb205824203f2c425514200c7e75d81420047d75d81420047f715944203e3f415944201c7c70594420266f205944203d3f76550421563f765504228e3e635504223e3e625504203f2e62550420053f715504221d3c705504200c7e75584420063d5458442004df735844202cdc735844203eb74158442026e421584420047f755804200c7c75580420063d5458042026eb2058042024dc735933203e3e64553320063d645533228f1c43553320047f755833200c7c755833202edb3058332024ec725923203e3e64552320063d645523223f2c42552320047f7558232
  | 16 => 0x200101200300202500700100000500800200500300102800b00300500000100200000100700100200300400102100600002e00b00601600200d00200500200100000600000000101101700000700100000702000500000401d00000200900400000600b00000000000300001300d00401501300701200000100000f01d00200800700200000600000300400200000300200000900200400000800000901000000000100600900000300d00000002501200400301b00300e00900000203301500100002400200000400000200500000400204002600400000300100300500600300100000a00300600800600300600801500001f00300100800503800200100700000000000000100300600400000300a00300400600200900200b00200200100200b00d00000000d00703400701100300000a04d00500100000001500000a00100201501300000000001501100200200300000100d00e00000100000000700b00202d00001700000000000300000100000900601300100400000000601f00200200800100000e00000600200000b00700501f00a00000e00202000001400900100000200000200100300d00001700100a00100000000000400b00200000100800b00500b00000100b00401900000000100100300200000200200300000000100000000e00000200200000a00700200800c00200000000900d00900400700200000200800000400101100700000300100200000600100000a00000000300a00a00100c01a00000000000400000000000000000400200000400d00401700000000000400100500200100301300100700200000100000500800500100700100300600500100901700300200600600000300000700000400300300000000d00000300000200200000100000000100200100001100000000500002a00700100100500400700600000200001200900000900100200200000600600800000000300000000100000100000301d02800700000100000600d00000000000500000100100700700c01a03200301400300b00600600100100e00000000b00500200600000000200400101302800200900000200000700000000300400300200b01000000100d00301000100700503800400600000500400000700000101100000701100a00303300400000001001700603800500b00801200100800300000000301000000700000200500400100301c00400001001100001700100000300000600000c00100100200100a00000303300600e03300b00001200400000000500d00100b0040040190030050100000000010000020000011653d7498d540065f6398d540056e7298d540056d7298d540057a7098d54005797098d5416d3f7458d541453d74989540055e73989540055d73989540057a709895400579709895414d3f74589541063
  | 17 => 0x29ca9e41b27501ea00000005253e60db41a66a846c8ce8262a92144a7bc00e5db3290fcc756aac4ed0c6800061c51c16f44e078203491c4dc25a12b7938951400022f0c208c28883e9800066c8d300009f92ce4195138a6cb48a1523280004de00046f1b580000004161860000000000014c5d60000091f48d5c5d9084a42c9f84ea02602f82c86c75351a693aaa4d000178881a15c4b7a2e000059f0001dcd3ee5cf19c8bc0a187a81271b680000031a60e9924881213680009088aa2610678b603042079fb91460a005512a48be0660110f08e642fb000000000012239082b40001f500007bd5000001ca8000d12000486257888691f2a8206420c68b000077c0008671dc00002b01a72cc9a880000003b8a5a113630f09b0000ffe0280b48440bf62751a903284c45524bf0000c7a0000000910c640001fc948cc3c00000027700003f224b0014490000225a424ed48824dc89fc070000000076854a87f2b690cc0004921f28000234a29303a028000751076225416469e40626a011c09000020d85920000001ab4ec42c11510000000000000031c0000002a40b4909419455781740007a413320781f243b32288f82702291d404ad54e9122b984e400000000000006445e5000000105c2cb3b81330f9e00004e0aac2906150bb8c7c5424dd00020d546493c47e88b838a65900000000002d10c11598f5835a49814188d60004571c2d2ee4d500000003200ef5599824a4c6fa29a80000009ad18b02981325d300013840005c050612e8096a751c7054c65a7ea08a9ef0bf800000008609b68b500d1db82cc0f1005a93c33677a0dc167814600d00600100700700200200000200000000700000a00000800301400602200000200200000200500200200002700000000100000100100b00502600000100500500000100100a05800000700300000100600900900300501000c00200000100200100500000500000700400a01c00000301b00a00000400000a00f00400000000100100100500500d00300b00100001402700300300600200b00800c00000400000000200a00000100300100c00000000400a00400000200000500200200200b00400100000300200000800100004200000d00000b00101d00200000200000101900400000200900200700100700100501000e00100600200100400000100a00100300100200300000200b00200000000300000200500000a00500300000402300100900500900000b00300500701500000200300500600401600a01900000300100201c00300500000300000200000000002500200200001100200000200000a00000300200004400000e00100001300100000700000500200600e00300000400000700b00500100600400000e00200300000400000200100400400800400400000100000000800200c00
  | 18 => 0xec55200000000185fe5c7303000112e65d4b100000008e412e210919c4480a38408fb04fe2642240af202b3e3199456c6ed27b0f241c266c38b80013ec1272a11334000000000000000000030116e00009bf2d90000000ab600021dc00065730b800000084b0000000c108e552280000000000000000a1290d43811448160654de0b90cde5961a5a9fc6ca2120002aad0fa1714e3a3500000001bf095ce60000091800136296b4c289e000078c00000010f843f00006a537079b0001e987ee97f0001ee132600011097800003561b480003a0000000227923200000000000000cf27980000002ad06925700000003a00000d424e64fea13552c00004da99050e1bc1fea18c00064338c80000001744279d7c000aa200023e82f06f00001fac2aa74b23b921d49299f212054064c65a000000117e0003c525b45ba9a500000dd45a0003fea24ca2000000016cc8740000000000bc281f3548000bda000000032cd567bb3552a20118a76000000076275939e000000059726d000115a9ce481800000000000000004b2000502000000000003b1f94aea2690001b4000073d0002074e3e5c30d015ed2ae85d000000003a39f0ce80012f24b844a25c0d08494297a1a44164bc10197408cc9353e00c1468c0082d528d05e400023395a1068000284131c0007a943f1e351c432a00000011da0004a287803e84a12649e704585a728d003884a8bb2119efd2ea2d34e923eca305e741c98011ae83a13406480c278511c8260a7c6e92ac17347aca7c4650ee40202530de999152800000000005a07142a7800046456b3778b9d01600041f00003620003868cdcbd05593131d24c80a562758d882245900668b7cb920b82c3270800011b416943800000045000000004b00000b0c0000ab0000000000a8b3c5aa040c622d3de8844d2455b00015c82886e8000112923437145297780000000000cb07b6a9800000000000000cf80000460001fd96bc5fa90000000000002c50000ae4c580000001b38ea604800000000000000001c0c0007d7000000010000000010c4e2213b00026380003503efa3dc000207128000000031e3851c3137a4e344015c08849b004e834027a10f000029ccd600043c000000048200013c03560001050fa851e00000000000009e944b2a6c4ca3644df27a8f8e0004438f8d412000119800095e7ef35319e05e20000000a30c6c0f61e500002740b90ad8000a0448000000000940003ec800000056a00026d4818a031b0892539a3680df9d98c349a02a0a70c1f46af35c0000a1e69901892ac36682b0000000fb8a1b2ba00008386512c9800126225800025a40000003960bb80003572f829b8de83d0403a83cefe3672ae1e412280000d907744ba9f83cf0e5c9968cb0001eb4ce01522fc0c1ccee53b1550c047d2a9032c237c16a00
  | 19 => 0x6a0ce0d38c56381000158c07400002f0a9841e8650001cc453c8332779104a520002901cd40007f35358000e7c7f019781d409c00034880008fa0003d900000000000000b3cbac90a0002ad000067b22caa9027e000000114cb164902040fb8d4800043625810be2b503f86d04f64d64f400003da88c396809ca2884102d10bd00a2244ce8000af8a4c3b2800051a8a8096a120bd487200007ac0000e600000000020000001b2072c03c0f99d9ca5888b26e0750f341be00000000000002540000000a9948c1054b76199468259028400048280000006f90000cc93f833c48a901039e09a000065d3446e341f85fc0000673ea15c4c9a534187000113a34f4291e112504460db80000000003a3855154c00000029448eca7e343a268ad8000388000043e00000004bc0007ab23512040001c438c0000b829d907020f04e62642b28000d8401302224210b800020b92c80006a04f00bbd32a85822818a12a841e3f60a38afe695352a9d0eb0279437268c6be50105e8000000000000278843c00000000000000001d2011c000000554a868fc87f8356000000024d25b9bf095c3ce341820ceda6e239514b410a3a902f9fdcd9e03e26222100000000000000000000024975000000052f2698ed23be0002068c420000002870f8800000007492023870c0113929a55d1f6800000094434c11fcb2a521000000000094b37b00000005bc0001454bfe94a3e4945c30e201000179945c3d338389ad50413024717e864aa354600414daa3e725aa094a3e6be31792245ec12000002a4c065000768efca9c4850000fe9220a102a39ae404041818897e412a619072036019827d3ba08008a45c249726207be47948980007e856900000008263863a500000003d80b6816452c61b274a3d008458a0ff907c0001cb00000013ce58f14a0888f842bc475125cc784c51c4035944a5f334a22146e00874041b78ed09960002284e567b92d1a670cbe3f5497a82005eab7347a9c495a35b0001d7549c0782ab1b7c6866b631c06452640350fba0a8fac18547793b4dee54317b91349a093615400001b83a548f22bc6389a4120a6843b06c0000127021c1bb51f96a0a0674f1a100000000d53a680001ee1ec21c1fa111e7fe1748000eb642e461a05800000000000000000002fb8bb4c1a37f3188a8000000000020dca26a1742ba90c6622c042605d857a1e9001060d4886763270688b1815a26c9a743e407a1980dcce8c15110e960c97265b30603680001c90b010b52e236055000100000004d4800000057705280000001f129723d80b00004b99c903b20b117188ac06894e36c137948e4323e42668e2676c0fc80f40002421b300012f00dd0bda0ed0207ae52a9014b685362fa832400010d5310e785943c83b7a8a0d6637b00005f452248b49c825c8ea0002c907
  | 20 => 0x87c3903db98a879e03f00000000006b70b5a66c50a28024f02dc0006232ca1bb811e46035e03d0c409074610ff8de651d12780000002af000000000000043da47052600051ca3480009db3bc00013c21a42739534000000407a6ac1283291be99e404c6420000000a7a79f2c10e2400068500025d00000000ab80003ac7f90001ad40005ba3b2086800000000018b80000000002560958439454a3d46769ba30716153a21e70e99bf936e299000289875c32e00010802dc235462a73c00036f00012953160f54180504eec49f00011ec0002b339d9e200006503091b0c00000000000000000622ce25b80c82bb2d006b80000004620ac110c6663e70c30b1a10700019b50e81c22cd25980321e602b0000000000394211000010b00000000002d900013d519800017c06a000034500019303860001cd00011aa00052b941400093730e80347bc46e153800000000000000003ca00043418514e6036407257c0005f215c00008564731ce0d780f800012a8f700000c22d323611061593582184000000000053c9365f63bf0be951837c3902a5cea83f015200000ee00011000013200000ee000018811952d194c1801d14830000fc06d14e42828f4662514a8000000a5218c81e5354000000052c20821c250191c00000004092c4ce66e551e201929800000000000004030001d8108e0000ed80008fc3ff02daa4c0000fc51600000000001de95b927a00000000000008210b8182c0004ff1c116b49a800018328d800091144922dc13e8641421a408b49591b18000eaeaa823208c02f895b4ab25a886c6e716f17b81245b917121813808042c2245c8aa8180b382d0394a6545e9514a548db0a190481785c539189150aa5be3be03a02c68ff1eca1d8c2ca6710110d5456a140000000e3472946d00000008cd45887f80fc9fb2bd1c7000093f000197951c0090671e0010c0000ba80000000002db80000005a200011e03c27fb00000b8aaa57d3471fd94904264bd9ccc6dc488129178c03e1b053d17600006cb2691c1431e25631aa11800023600000000000003c30ef01b60002c7034476a47c13900000000004f70b680006db3e68fa0000000000137c00000053e80000000004ff1ce00007e2294089421431404497111e26440da848423c0eb325000076e0c33d800009d8a6c0002984ce45d50c69ef93e20003e0a9409066bd1958698e8a49153300010f40002c480010b63130791ba867ca060f423200000001a5294d4c60000000000858000000237425405c0e40000f2839447480007ec00000019e80003334eb00000000004a4a77940e31d000000010400000000003e07af1ba000000031200005c849897600b8a7473a4c300008304e20bf479a5f40005d20000001274a1615f81489a62cd0c514352469020001bec0000964c68f000386
  | 21 => 0x2e505940000002e4000078c1243a221392f44c000000005aa669473987c000a911ed141d46233f2f612a85c000049300012520b34eb800000000054d043123a7023d9961c00000000016b8eac7981b626ed1e01a11188001006000050a26415c00028f000000000050296c50283100378588f023a122b8c8c00000000000000007632088000d8a7cb0e30f8032a00006a0000298282130839c41c0004f31804e2c1680fea4389ae9f50840eb543c4491d180000009403af20549f088e0391ed905e67c50f93c4fe84b6330aa8462e3c40168000d1a93803000005d800000022b00000001080e3caa812800017d0000a402e88de067000036094c09c8802000000014825f5591ac40000002ad047149682316228840005641a21fa40009424b184dc08c5a53c723705c200019402e84a217926880009dc00c5449c247741ee2bb09283d453c0001a5c6ea4c62939769102ab50f21b64a0800022c1e2471a42a43516fd0624a753402c00003f82701d08f740c14e2a6bc41a3aa3cb222913830900006306482ce000000130e04f29217906b801e4e527fc6a69894cc0c607a26244e31268dfe1c736486a8e10074000000004a000366962022647246780003160f34aa8c353582ba54292982023913d006b42941c02038000ace2dc37600000002c220000cd47a1cd00000614049270000f2cf942885121b710a63b00b0a69c45010019091148125df30522255380911c0000000000037e8a406f2234000167400067f4e091b54b23c346380000000000db000055897c3ae00000009ed0002198c9200028880000000004d70a693006e639ca2f869a0ff10ca3e4b9ca465009e48994a3b111a3181d26e005d85754447ed038a3e10d66c61bb1ad10261d54911cd8a9438c07f1a4ccce43403e89a94ba6341179b4c4bc40a2c0a4d0a2c7a252115788e85ab33e9a8c0729e41f221001bc4fd54a9a203f831b3fa9a0487877722e0fac7329213cc975c9d05ac00000000008ec099a65c0001af459a298f6a85946896d40004be311250c0580001e299d0ed6725123873874454601d93e4ce2a1246480010928451e68001208a200000000c8c000010a0a14f635939b80000820000000000c7c08428e195800048d22b11bd07027c25da6d032629709600000002134e6153091400034f8000fb40f000000011dc000000108429c0000000e10776000000284c000a7200026c81c600000013dc6927554c08b3025c9f928c9260ef623f4a410514664373d285193a62ea4c31e4c4087c517a1ea882c69c505a080fc2354458260ce823e24190dac5b008d22798153c61c1120000000015f0000000000469000092c0006820000000e1e0002238bcc4b6016393000023000043c94e80a22b735d9ae897e7a10001b9044e18407c1b490ea11602680012584f445b0
  | 22 => 0x80006a20502ab9f0cf2e0001492630000946000210d460000000000024a92d38f286431c0a83caa290d881fa49293ece0c000077003c3988e81bd264892a0fb00022e426821b1bb957cfa096c2f580000dc74c22000a85ae5a91d924cd0366a733191a0ca827a24c835c8365402cd8000cc02e609aa0244b48223f391b066850b000207068e18600000000002b236611312c22541300a0d21e48c00000010de29c0219dc931e7610000e6c00038b00028f80006b200013049ca6f83a70f48cd07001b922f04100005529fc84748511e38e9d02e73a00881000000e20000474cfc8274ec0001048704393811400000051197c4000a1d29128dc75800000000000002e50000e14b6c13c551a83800086d3139a00000a8d1f897bd3ca3dd1029730e7ea784a0800026430a0dc8220c7e6960000000e5ea3a25e80003ae00055880000004ce0000af94a800000009d07de3d7439800047046220d00012e400a00012cc844a9f30802bc67a0002a49bc800026c000000016c77928d87880000004e20000e24000018152c84e9502a20314690068299193c1147910b5245853e7342cc2574c6e63a4469e3c9680240cc1f545fc0002ff29293043270002188e363401d019b800045d4a384f901a9f452e0000000a6d11e2a740000000002834000a2a2ee0c544c6a4125126d92a289100a911044c63b08a297c25272226c00011c692027d08246d400000000003f048f0001a1800062942a066914409e298a59400000016d928c000953140a0004ec7e62f485bc000a6f319800055c9ec0888c8150e7db4eea8000005371d7a1c4f060003d883951c0355180000076caad0000288000000000000046e8014c88b513e635838ea96086024607e8694206aaa000000037400008f80000002c8049800090c580000000000017e18100000000c84cc8b1d4222064e8000000000002a22c913e073000133c0003d548da4ec00000000000005306f147590193d60000ab20447663834280a28000a8f1c99e9d3081400a6800081c5cb1e601b4c720003f8a9808f42b1151885cc964a449f00003bc00013b8000000000000296c00007b0001c04ea4a844c515f80007e30000000aa249342b20f4bfa0000001d0cdd646339700013927de02a837c00030b3be9a280d81964e5822c00000010b0000000000000000000015e28905b0000000331000000089800029dd1ac01b36b8ad000006b01923f828a0001a08f04000a861ae904000042910aa9c1174000000177400000034d9ff00002e850c10740000000fb184400000031803a8dea0000001970000000000181000000042f0ed0f0e000000239932868c3098bd4f3a0291c9000114e0004ad20a4aa69521f61ed11f83984d988a85ac3fc18194fd45e6bf000183c4767482b124a83120002e32384000648557005153c
  | 23 => 0x1580a562c645581c0e1c2861f0a7e824c1e329c16440d40ac3209c5533c42810a05e87cc0c653480000005611c500011e4000000116c00033500000013e040142d1954ff45334ea000000000013380000001812bc277c000000000000000000011e99d4a1492b00000000006dd0001b2800094f17e0000fba6d4000000104c14924e90f44862f902ba3051689f227906b051662d0d1845c310ab00b991515064703ad09b8fa24023ba
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xb48855013048001e12a8a0260900028d60675593100060eba8e6b262000c2d751c964c40a343906b22a98811e8b209645531019e1c382c8aa62003970805d541c400146f0caa283880cecc20154507100051bc32eaa0e2033b30805d541c4001a2aea39a8388003495d472507100044e43ac898620009948750530c40011590eb2241880026921d414831001c1e43ac8aa4200089c8758d41840011590eb12830800e96219544c210004cc43a829842003a688655120840013510ea0a41080060f21d645511028d0e41ac8aa22047a2c8259154440016a306382a288002d860870545101c51a432a3a0a2033a3581d9541440674690ca8a828800e1d219755051019d1a432eaa0a2033b30805d54144001928ec39a8288003455d47350510005c8c00e6a0a2000ca4761c94144001a4aea3928288002e8600725051000698baee0a0a2000b91831c1414400174304382828800e9521951cc110196a8b9aa31822000d61725463044001b42e4a0c608800e95219514c110004ca43a829822033f12505053044067e20a0a0a6088003261d8744c110005c8c08e89822000a588655130440016a30a38a6088002e4610714c110005a943aa29822000b508754530440076a50ca8a608800ed4219514c110005a9c22a29822000f13745453044001e20e8a8a6088003c4547414c110005a8c2c829822059b918490530440013310ea0a6088163c4d45414c11000788a8a829822000b518550530440b1e26a8a0a6088003c4551414c110006c9c3a829822000b928750530440017210ea0a60880036421d414c1102c78942a829822000f11855053044001e26eaa0a6088163c41d5414c11000789b2a829822058f10655053044001f0704a0a6088003e0209414c11001d32432a39022000f41514c32044001f02829864088003545cd5188110186b0b92a31022000d917350620440074c90ca8a40880026921d414811019f91282829022033f20505052044001e82a39824088003e050730481101e72432a609022000f41514c12044001f028298240880032a1d87448110005d0c08e89022000a688655120440016c30a38a4088002e86107148110005b143aa29022000b608754520440076c50ca8a408800ed82195148110005b1c22a29022000f23745452044001e40e8a8a4088003c85474148110005b0c2c829022057ba18490520440013510ea0a408815bc8d45414811000790a8a829022000b618550520440ade46a8a0a4088003c85514148110006d1c3a829022000ba28750520440017410ea0a40880036821d41481102b79142a829022000f21855052044001e46eaa0a408815bc81d5414811000791b2a829022056f20655052044001f0706a0a4088003e020d414811001d1c402eab202003878805d954040074b100aa2c60800e9a2015458810
  | 1 => 0x90cbaa829800e5620175505300060e3b2a8a0a6033b1880551414c001a1aa839282980027260072505300044f434eca0a6000c1c651d9414c00183cea3b2829800307a1476505300060ec28eca0a6000c1f511d9414c00183ca03b282980030714076505300050e432eaa0a6000c1c765d5414c00162f02baa82980cec620175505300060e3b6caa0a6000c8c76dc9414c001918ec3928298003435d47250530005c4c00e4a0a6000c1c76545414c0011390cba4429800e1721975d813001c2ec3ecbb02600095b87553604c00763100aa6809800e4721d545013000c1ec26ecaa6400083d84dd951c808f25b09bb2a99011f0b9d95490f20004e4c00e6b0e400092d84dd951c80010df0cbaa839000e5a201755072023e163b2a8a0e4000d0d541cd41c800145f0cbaa83900030b1d9755072000593c0aeaa0e4033b28805d541c800191eec39a8390003435d4735072001c9643aa8a064003b488055130c80013190ea0a619000e962015458e200060fbace7b224051a1e83d915448089870e1b22a8900028b219549092022594402a92124000d0d549ce42480ab918c8b9c849010eca20154109202956240ac619240008ad87190214800154b0232042900032319173085200044f43ec89824043e185019130480013930139ec8900028ba1875d912000687bace7b224000b89809cf644800151b073b0c8900028ba1b5119120006163b6c8aa24000b0e83d915448089a50e1b22a89010f4a1c0645512001cb543ee0aa24000b61811c15448001948c838ac690002b12056318d2001cb4402eba1a4000c2e7655243480a165100aa4869013eca2015410d2000694aa2e021a4000aa5811906148001918c8b98c2900030b1d8645452001cb4402eba0a4038b2880553414807165100bae82900030bd50765052000436432eaa0a4003968805d54148001858ecaa282900ceca201545052000686aa0e6a0a40009c9801cd414800115d0d3b282900030b1947650520006173a8eca0a4000c2e851d9414800185b0a3b282900030bd44765052000617280eca0a4000c2c501d941480014590cbaa82900030b1d9755052000593c0aeaa0a4033b28805d54148001858edb2a8290003231db7350520006463b0e6a0a4000d0d751cd41480017130039a82900030b1d9515052000456432e918a400386c865d760480070db0fb2ec0900025ae1d54d812001d94402a9a02400392c87551404800769100aa66090002a321941cc12000457436e8982404fd28501d1304800769501b2a6090002a3a1b744c12028784286e8982404ff08501d1304800131d0fb226090113c2143644c12021f84280c89824003b4880551304800769100a8a60900e3c2143414c120004c643a829824000a8c865053048067e10a0a0a60900f2d2a17704c1201e5a542ec0982403c
  | 2 => 0xc50590310051ac08a0b206251a1c83591540c40145b08284c41880299604509883128f0621aa8b106200a2d84141620c4014cb02282c4188028e61050580310051cc20eab006200a71811d5600c4a3c3086aa2c0188020f61c50992210051ac08a13244200a38805d5648840183aea39ac9108020f61c50592210051ac08a0b244203878805d954884a343906b22a9108028761050d8d210052ac08a1b1a4200a1d8414063484014ab02280c690803165c05018d2129722108c6a8a4252e842118d414840107b0e284c8108028d604509902123e16392eab20420083d87141640840146b02282c81091e8b20964550210050ec20a13184200a5581142630848fc1884aa2c610802876105058c210052ac08a0b184200a39841416008401473083aac0108029c604755802123f14212a8b00420085d86dcd41940010bb0c39a83280021b61b725065000436c30e4a0ca000a37815d9419400143b0db9a83280028761873506500060f3b0e6a0ca000a2d86dc9419400145b0c39283280030b9d872506500051ac36e2a0ca000e17735854194001c28e6b0a832800389dc9615065000712392c2a0ca033e17305854194067c2a60b0a83280cf89c81615065019f12902c2a0ca051c1c7355161d008f858e4aa2c3a00028de05545874001c9c402eaa0e8000a378159541d00074b100aa2c7200030bd967290e4001d34402a8b148000c1f659ce42900070e90eb0aa32000307d94735064000617b28e4a0c803883c8755361500410790cbae82a000e0f219755054000616b2ce52188000c1d659ce42100074e100baac220002a9a0a43584400054b41c84b088000c1d651cd411000185aca39282200060f61376553300041ec26eca8e605191d84dd954cc0a383cecaa485980027260072587300048ec26eca8e600085f865d541cc0072b100baa8398147071d9545073000686aa0e4a0e6000a1f865d541cc001838ecbaa8398002c5e05755073019d8c402eaa0e6000c8f761c941cc001a1aea392839800e4721d545033001d34402a8b146000c2f759cb644c08f45d05b22a8981430e1c364551300050e432a921a6050b1880552434c001a1aa93948698157231917290d3027d8c402a821a600089d87190314c00152b02320629800323191720c530004e4c04e5b226000a1e861d7644c001a1eeb396c898002e260272d913000546c14ec3226000a1e86d44644c001838edb22a898002c3a0b64551302868c386c8aa2604fd1870191544c0072b50fb82a898002d460470551300064a320e2b126000ac481588624c0072b100bae8498003079d954909302258c402a92126043b1880550424c001a32a8b808498002a5604641853000646322e430a6000c1c76191514c0072b100bae82980e2c620154d05301c58c402eba0a6000c1f541d9414c0010b
  | 3 => 0x1b128200a658114362504010db0f328c4a08021be1d651894100534402ca3128200e0d54d8c6250401c1aa8318c4a091e8be1d541894100516402a83128200a2d84d44625040185aa8b80c4a08021b61c501894100516c20a03128200a6581140625048f858c4bae84a09128e20165909410060eb2ce72128243a3880594425046747100aa6c0a08028e61050d814100538c08a1b028200d1773dc56550401a28e7b8acaa080349dcb715954100692396e2b2a8200d3371dc16550401a36e6382caa0803461cc705954100695b90e0b2a8200d28721c16550401a66e2382caa08cf0e618705954119e8d418e0b2a8233d19831c16550467a5504382caa08cf4a608705954119e98c08e0b2a8200b1581997635040162f02b2ec6a0802c620165d8d410048ec38a1b1a8200a1d86143635040162b02286c6a08028e2016598d4100616b2ce531a8200a3880594635040143b0b3b0c6a08024761e6518d410058ac0cca31a8200a9880594635040123f0eb28c6a0802c5e056518d410058c402ca31a8200a1f87594635040183f0eb28c6a080383e096518d4100706412ca31a8200a1f815946350401c2f02b28c6a080386e016518d410050e402ca31a8200e1880594635040143100b28c6a0803075957018d410048ec38a031a8200a1d86140635040162b02280c6a0802c960665d894100593c0acbb128200b28805976250401c1aca31ec4a08024b61c50d894100516c30a1b128200b2581143625040147100b2cc4a08030759673989410051c402ca3128200a2d859d8625040125b0f328c4a0802c9606651894100554402ca312820092f87594625040164f02b28c4a0802ca201651894100517c3aca3128200c2f875946250401c1f06b28c4a08038320d651894100517c0aca3128200e27815946250401c5700b28c4a08028b201651894100714402ca3128200a28805946250401c1acbb18c4a080383594631894100616b2ae0312820092d87140625040145b0c280c4a0802c96045018941295c240a641928200d85325c432504b526f02baec2a08e28e20165d85410060eba8c7b0a8200c2d7518b615040166100b2ec2a0803075d8635454100616bb0c4a8a822193687d85515046747100b2ec0a08028e61850d814100598c08a1b02823383c87595605040183aca39ac0a08030b594725814119c9c402ea3028200c1d7518c6050401c30a0318c0a08030b5d4621814100714280c4302820083d87142648c40146b02284c9188028e201755923100616ba8e4b24620083d87141648c40146b02282c91880e1e201765523123d16412c8aa46200a2d84143624c4014cb02286c4988028b610501893100532c08a03126200c6970140624c4a5c8862312a29894ba10c462505310041ec38a13206200a3581142640c4a3838e6baac8188020f61
  | 4 => 0x348000000007d2630000012608a214924b78000004f0ca80023806d2102e000704ba800000000920000000002e8c3000905380002be0009e800056720f69d41a6104398003c4130000004a40008c84f1ac3000b18401c52c00240000000789050ce2489017b1f88087f0002e0848ed8b90ee0000016a0000000000041e9cc589f32989e86280041c7d0758fb4be00000000000000e8012004030080901c0400403000010002101c0b00c02008080000c0000300c030100c000090680400001024100180000003074000001b01c1300009008040000c0180201000008000140300c1c008080000a00406024020000001800000120080a00408014070380601401000020000000004010260000402000000050dc010000a0080e0040000c0502c0501c020041c0000400406020000000c008000180b004030002e024010081100c0100c0001400054030000000002030020580c028090340400c0200001010000000000401010010140100005030050100500c000040c00004030000000102c1e000050280d00c0b000030300b0400100c0500813004000000c0000009405000078b0c0b9cc0aa00f1a181729815400517c0aa93148600a2c805526290ca3c1e60aa4c5218028b6135198a4300616aa2e13148600a2d841426290c014cb02284c5219478310d5458a4300516c20a0b148600a65811416290ca147100aa2c12194786cc154582430051cc20a0b048600a71811416090c8f858e4aa2c2218028de05545844328f0a18aa8b08864f83c875516010ca3c3660aa2c02180287e055498e420050e402a931c8447e0f20552639080143b09a8cc721003075517098e420050ec20a131c8400a5581142639088fc1884aa2c721002876105058e420052ac08a0b1c8444a3880551609088fc5640aa2c1210028e610505824200538c08a0b048451c1c73551611080146f02aa2c22111f89085545844221c1e43aa8b008447e2b20551601088f43906b22a99911e8b209645523223f06322a899064528cc874c9610c8a558902992c219157231d1325803200565c0264b006400a3984141600c801c9264282c0190029c6045058032295a240a64192a200c2d659ca43d040183acb39c85a08e20f21d545834100616b2ce531e8200c1d659ce62d04710790eb2ac1a080316dcc70595410062c398e0b2a8200c6b721c165504018d0e4382caa08029620165d8d410042ec38a1b1a8200a1d8414363504014ab02286c6a08021761e6518d410042fc3aca31a8200a588059463504a343f0eaa0c6a0802872015418d410050ec26a231a8200c1d545c063504010bb0e280c6a0802876105018d410052ac08a031a8251c1c635d743504a147100b2c86a08030b5967290d4127d1c402ca21a8200a68805976250401c1aa831ec4a08021b61c50d894100516c20a
  | 5 => 0x694ea8001dc6d871217174000002040cc95c0000020c324380801da0003202c16c3cd278a80b299c5da370c40551d0632fa435239633fe914f51b225612c6a9261c26c0728b20002b8e30be000080000000c09840020c1bc64c000aa0007d82b1bf000000938982d25005480614c6eccd1e108c0000013a1a2000000df3842944e8b043e150dca154488ad2c1510007dcb980040c02119000478001371ee15a29c8623537a96ce380049c000000260004d873034000000660e022c9581a9a72ca1c4a4000244934d98a126a6588a220108474002511407c84380002e1784b08c42c4a0bc8811901f0018a41de1fcfe250462670b68f02b67ac000002aa000001fb0a24600017c000390118974d24412d0dd4c08981e9324725911e9ca18e360560492080341390b06c9b0471780dc1e511818196310f80b31e447c002184f0999141c5000648741fe3888047516131c61c0019e0000011d8002880000004a000348168001fe5f8001584ca870000d7052764458a20202e11b1093124b12181f28a1d8bba7c3ce7f44494e1fa894e90a308e43d19a7945a000001da1200c8001660000f80c800000990fc875000758001de00057522038276001109f52d6000b612a00a000630304a6970aa0002e49bc718722024fc4e1023502f0000000546b00013842026c1e0001b482cf49ce0000e4d6a74432120b10933449ec00133000494cc0f50005d0001fa00002400000000000cba6b458000001111a067cd219d0001846c8580d800000000000000000ec05e000202680288bd089d7008308f798b0da2f40123e3560ccac9af40e5e8da1120006e80009a0009c536a6a2dc7912a0af39a8203d1310d414c0919b0ca61517222242518ae11a04803c671394bc1d03589944e04c038f6370278f00004aa875148cd3927002d1e31b86dca997f0000742a8b52b49d4d487b412504bb000000000c8167386000000002d0988000000008d0001a10005080500004a0000000021c62867943340170a90db3b0730f300b4fa73c001dd3ca7b0d18000b61104408d000650d8929000030000000000000024810c0000013447e6d4009cb206000df12300063460800104850000004269182f91b13e4bc0017149600000000000108a48220860009f13722e77c0f0d43a6214c180040a0dc7492e2009c8001133b88e07b800378478000f83d00005a19109a3280018600080c3e9810005403f1151e81e0c60000000440d1602bc070980281ce0001d1d117e0004898f0ae14055800310000969473000fd2ea1a00055c1d8000002dc22883304528a783121000000000460000000000008350506f4b29dcfc095400664a680020e0013b021000138001f1494000340003548791508f1f2698ab21b35c000000940a400000000000000
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xc9f000000318d8680002a888eaba3030000268018801c83800d0b801808000aaf9f802911a73097aa20ac0b091e93101b821290a780000c0025200028000024a980000016b2b00f8594228e320019b32f16002c801726220004c200000180008041c00000c00640014040414002c04001410000030cc340800480801225912015498a4300485644805526390801a09844c85058032006904c981141600c80101d972015418d410050a241659ca435040102d97201541894100506241659ce4250401428905967298d4100682e08805946350401a08822016518d410060665c805946350401a0a922016518d4100682648805946350401a11912016518d41005822416518f625040141890596739894100682e0c805946250401a088320165189410060a65c805946250401a0a9320165189410068264c805946250401a219120165189410058224165d8c625040160890594631894129461261325c432504012199814063181410048a660501886050401428905d472592310060a61170140624c401861815c0501893100506241751cd6488401819845c05018d210061460570140634840141a909d873506500050aa42761c94194001818801d9755073000503e59751c941cc001508905d4725073000542241549ca434c00148591191720c53000642dd5809cb644c00130990a0b6455130006421c282d91544c001818809d9549093021c46261545c0424c0014859119172185300060620076551414c00150890550725053000642551801c9414c00141591940765053000407660501d9414c00141591140765053000606200765d5414c00140c965d4725053000542241751c9414c001888766007250530006425d5801c9414c001828801d9755072000503e59751cd41c8001508905d4735072000542241549ce424800148591191730852000642dd5809cf644800130990a0f6455120006421c283d915448001828809d95490d2027c4a261545c043480014859119173185200060a20076551414800150890550735052000642551801cd41480014259194076505200040b660501d941480014259114076505200060a200765d5414800140c965d4735052000542241751cd4148001888766007350520006425d5801cd4148001a0850a1b744c1200064214287d9130480019085021d414c1200068214086505304800730898551404c12000544241751cd41c4001520905d4725071000505259751cd414400191175600735051000509259751c9414400192175600725051019d0c25975dc1414400189076604744c11001c9425985505304400151097615414c11019d84259855053044001b0185209414c11001d90259514c120440018a076604744811001c9825985505204400152097615414811019d88259855052044001b018520d4148110
  | 1 => 0x2b098025ae8a311b04001215a3a4060702a181801480002da899010f1e1aae07a11c001395001d2d00801d9104851a0
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x38002603600828c0b44a07068ae004c16400798a00032b2a01491a0001800081c10420060132ec9100b28c6a080301197644805946350401900c9322402ca31a8200c0265d9320165189410060432ec8900b28c4a080320193644805946250401280d0920aa4e521a6000a4068470a0b645513000502342404ecaa48498002109a8241541c9414c001404532eac00e4a0a60009406849055273909200052034238507b22a890002821a1202765524348001084d4120aa0e6a0a4000a02299756007350520004413522850dba26090002a01a114286dd13048001084d48a143ec89824000a4068450a1f644c120004213522810ea0a6090002901a1140875053048001104d48a0432829824000a8068450219414c1200052014ec2904a0a6088002a00a661482505304400148053b0a41a829022000a802998520d4148110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x6
  | 2 => 0x2
  | 3 => 0x1
  | 4 => 0x3
  | 5 => 0x4
  | 6 => 0x4e
  | 7 => 0x5
  | 8 => 0x94e
  | 9 => 0x124e
  | 10 => 0x138e
  | 11 => 0x8e
  | 12 => 0x150e
  | 13 => 0x98e
  | 14 => 0x128e
  | 15 => 0xce
  | 16 => 0x168e
  | 17 => 0x9ce
  | 18 => 0x12ce
  | 19 => 0x10e
  | 20 => 0xa0e
  | 21 => 0x130e
  | 22 => 0x180e
  | 23 => 0x20e
  | 24 => 0xb0e
  | 25 => 0x140e
  | 26 => 0x154e
  | 27 => 0x24e
  | 28 => 0xb4e
  | 29 => 0x144e
  | 30 => 0x16ce
  | 31 => 0x28e
  | 32 => 0x184e
  | 33 => 0xb8e
  | 34 => 0x148e
  | 35 => 0x3ce
  | 36 => 0xcce
  | 37 => 0x15ce
  | 38 => 0x170e
  | 39 => 0x40e
  | 40 => 0xd0e
  | 41 => 0x160e
  | 42 => 0x188e
  | 43 => 0x58e
  | 44 => 0xe8e
  | 45 => 0x178e
  | 46 => 0x18ce
  | 47 => 0x98956
  | 48 => 0x94996
  | 49 => 0x9c956
  | 50 => 0x949d6
  | 51 => 0xb89
  | 52 => 0xb8956
  | 53 => 0x94b96
  | 54 => 0x99256
  | 55 => 0x9d256
  | 56 => 0x1849
  | 57 => 0xb9396
  | 58 => 0xb9516
  | 59 => 0x185516
  | 60 => 0x9c996
  | 61 => 0x168996
  | 62 => 0x150996
  | 63 => 0x99856
  | 64 => 0xb8996
  | 65 => 0x98b96
  | 66 => 0x184996
  | 67 => 0x409
  | 68 => 0x1609
  | 69 => 0x9d516
  | 70 => 0x169516
  | 71 => 0x104b
  | 72 => 0xb9696
  | 73 => 0x185696
  | 74 => 0x1689d6
  | 75 => 0x9d856
  | 76 => 0xb89d6
  | 77 => 0x9cb96
  | 78 => 0x1849d6
  | 79 => 0x589
  | 80 => 0x1789
  | 81 => 0x104c
  | 82 => 0x3ca
  | 83 => 0x184b96
  | 84 => 0xcc3d6
  | 85 => 0xccd
  | 86 => 0xb89895e
  | 87 => 0x9894b9e
  | 88 => 0xb89c95e
  | 89 => 0x9c94b9e
  | 90 => 0xb9856
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 72
  | 6 => 1722
  | 5 => 2744
  | 4 => 638
  | 3 => 103
  | 2 => 28
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
  | 6 => packedAt gbK6 (70602+((h/574+packedAt gbK6 (63714+(h % 574)*12) 12) % 2500)*12) 12
  | 5 => packedAt gbK5 (142680+((h/914+packedAt gbK5 (131712+(h % 914)*12) 12) % 3622)*13) 13
  | 4 => packedAt gbK4 (39762+((h/212+packedAt gbK4 (37642+(h % 212)*10) 10) % 842)*11) 11
  | 3 => packedAt gbK3 (7482+((h/34+packedAt gbK3 (7210+(h % 34)*8) 8) % 136)*8) 8
  | 2 => packedAt gbK2 (2322+((h/9+packedAt gbK2 (2268+(h % 9)*6) 6) % 37)*6) 6
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffc3e0383fc1ffffc1e03c07c13b33f067e93
  | 1 => 0x3c07c003fc1fe0f01ffffffffc6d4cc81993ff
  | 2 => 0xc007fffc001fff001fe003ff838e70f1e1e31c
  | 3 => 0x7ffffffe000001ffffc0003f07f01fe03e0
  | 4 => 0x7ffffffffffffe000000003ff8001fffc00
  | 5 => 0xfff80000000000000000000003fffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x4434061080a40510cd120a4118001113022691
  | 1 => 0x28408001240920a10024a09460250448089026
  | 2 => 0x80955ad4009656025750132b098a70b1616318
  | 3 => 0x1266d5acac004049b995a0212d07b01b603c0
  | 4 => 0x2203b1a3731b98cf0000600c237f8000ddd800
  | 5 => 0x33c001c0620310880201803043ffeeec000000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xfeeaeeeafeeaccc8feeaeeeafeeaccc8feeaeeeafeeaccc8feeaeeeafeeaccc8feeaeeeafeeaccc8feeaeeeafeeaccc8feeaeeeafeeaccc8feeaeeeafeeaccc8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_13705
namespace PEqualNP.Outside.L_meta_13705
open PEqualNP.Outside.L_meta_13705.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 4 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 6 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 1 := bs0_4_0
theorem alls0 : ∀ k ≤ 4, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
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
theorem bs2_3_0 : Interval s2Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 1 := bs2_3_0
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
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 1 := bs3_3_0
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
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 1 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 1 := bs4_4_0
theorem alls4 : ∀ k ≤ 4, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
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
theorem bs5_4_0 : Interval s5Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_96 : Interval s5Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 117 := (concat bs5_4_0 bs5_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 46 := block_range (n:=46) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 46 := bs5_5_0
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
theorem bgb_2_0 : Interval gbAtlas 2 0 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 28 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_96 : Interval gbAtlas 3 96 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 103 := (concat bgb_3_0 bgb_3_96)
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
theorem bgb_4_576 : Interval gbAtlas 4 576 62 := block_range (n:=62) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 638 := (concat (concat bgb_4_0 (concat bgb_4_96 bgb_4_192)) (concat (concat bgb_4_288 bgb_4_384) (concat bgb_4_480 bgb_4_576)))
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
theorem bgb_5_2688 : Interval gbAtlas 5 2688 56 := block_range (n:=56) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2744 := (concat (concat (concat (concat bgb_5_0 (concat bgb_5_96 bgb_5_192)) (concat (concat bgb_5_288 bgb_5_384) (concat bgb_5_480 bgb_5_576))) (concat (concat bgb_5_672 (concat bgb_5_768 bgb_5_864)) (concat (concat bgb_5_960 bgb_5_1056) (concat bgb_5_1152 bgb_5_1248)))) (concat (concat (concat bgb_5_1344 (concat bgb_5_1440 bgb_5_1536)) (concat (concat bgb_5_1632 bgb_5_1728) (concat bgb_5_1824 bgb_5_1920))) (concat (concat (concat bgb_5_2016 bgb_5_2112) (concat bgb_5_2208 bgb_5_2304)) (concat (concat bgb_5_2400 bgb_5_2496) (concat bgb_5_2592 bgb_5_2688)))))
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
theorem bgb_6_1632 : Interval gbAtlas 6 1632 90 := block_range (n:=90) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1722 := (concat (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 bgb_6_288)) (concat (concat bgb_6_384 bgb_6_480) (concat bgb_6_576 (concat bgb_6_672 bgb_6_768)))) (concat (concat (concat bgb_6_864 bgb_6_960) (concat bgb_6_1056 bgb_6_1152)) (concat (concat bgb_6_1248 bgb_6_1344) (concat bgb_6_1440 (concat bgb_6_1536 bgb_6_1632)))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 5 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 12, 28)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 5 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 2 zero, 24, 28),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 5 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeeeafeeaccc8feeaeeeafeeaccc8feeaeeeafeeaccc8feeaeeeafeeaccc8feeaeeeafeeaccc8feeaeeeafeeaccc8feeaeeeafeeaccc8feeaeeeafeeaccc8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 9 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809450 * 2 ^ 32 + 4276800712) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_13705.Model.Repr at out
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

def mono : List Gate := [⟨.and,[1,3]⟩,⟨.or,[0,6]⟩,⟨.or,[4,5]⟩,⟨.or,[2,7]⟩,⟨.and,[3,4]⟩,⟨.or,[0,10]⟩,⟨.or,[0,11]⟩,⟨.and,[8,12]⟩,⟨.or,[1,13]⟩,⟨.and,[9,14]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,15⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 9) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276800712) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276800712) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_13705

open PEqualNP.Outside.L_meta_13705 in
theorem PEqualNP.Outside.L_meta_13705 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276800712) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276800712) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
