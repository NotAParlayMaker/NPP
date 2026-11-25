import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_12937.Model
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


end PEqualNP.Outside.L_meta_12937.Model

namespace PEqualNP.Outside.L_meta_12937
open PEqualNP.Outside.L_meta_12937.Model
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

end PEqualNP.Outside.L_meta_12937

namespace PEqualNP.Outside.L_meta_12937
open PEqualNP.Outside.L_meta_12937.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x841fc21082fca0107fd0020ff20041fd40083f880107fcc020ff18041fd30083f860107fc8020f790041fe20083f440107f48020f690041f920083fea9885fd5310ff2a6217e54c43faa9885f55310fe2a6217c54c43fea7885fd4f10ff29e217e53c43faa7885f54f10fe29e217c53c43fe87887f90f10fea1e21fc43c43fea5885fd4b10ff296217e52c43faa5885f54b10fe296217c52c43fe85887f90b10fea1621fc42c43fe65887f8cb10fe99621fc32c43fe83887f90710fb20e21fd41c43ea83887f10710ff98e21fe31c43ec63887f4c710fa98e21fc31c43fe43887f88710fb10e21fd21c43ea43887f08710ffa0621fe40c43fa81887f10310ff98621fe30c43fa61887f0c310ff90621fe20c43fa41887f08310ffaa4217f54843fca9085f95210feaa4217d54843f8a9085f15210ffa9c217f53843fca7085f94e10fea9c217d53843f8a7085f14e10ffa1c21fe43843fa87087f10e10ffa94217f52843fca5085f94a10fea94217d52843f8a5085f14a10ffa1421fe42843fa85087f10a10ff99421fe32843fa65087f0ca10bea8c21ff41843fc83087f50610fe20c21ff31843fc63087f4c610fe18c21ff21843fc43087f48610fe10c217e50843fe81087f90210fea0421fc40843fe61087f8c210fe98421fc30843fe41087f88210fd10421fd20843f241087f08210ff88421f710843f621087fd5110bfaa221fe54442fca8887f55110beaa221fc54442f8a8887fd4d10bfa9a21fe53442fca6887f54d10bea9a21fc53442f8a6887fd0d10ff21a21fd43443f886887fd4910bfa9221fe52442fca4887f54910bea9221fc52442f8a4887fd0910ff21221fd42443f884887fcc910ff19221fd32443f864887fd0510ff20a21f641443fa82887d50510fe20a21ff31443fc62887d8c510fe98a21f531443f862887fc8510ff10a21f621443fa42887d48510fe10a21ff40443fc80887f50110fe20221ff30443fc60887f4c110fe18221ff20443fc40887e88110fe90221f920443f840887fc4110fd88221fe10443ec20887fd5010bfaa021fe54042fca8086f950109f2a021fd54042faa8086f550109eaa021fc54042f8a8087fd4c10bfa9821fe53042fca6087794c10af29821fd53042faa6087754c10aea9821fc53042f8a6087fd0c10ff21821fd43043f886087fd4810bfa9021fe52042fca4087b94810b729021fd52042faa4087b54810b6a9021fc52042f8a4087fd0810ff21021fd42043f884087fcc810ff19021fd32043f864085f94410ffa0821fe41043fa82087f10410ff98821fe31043fa62087f0c410ff90821fe21043fa42087f08410bf28021ff40043fc80087f50010fe20021ff30043fc60087f4c010fe18021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0xd540c27aa8187f15030be2a0617e530c3fe861877d0c30ff21861fd430c3f886187710c30ffa9061fe520c2fca4187b94830b729061fd520c2faa4187b54830b6a9061fc520c3fe84187f90830fea1061fc420c3fe64187f8c830fe99061fc320c3fea2187f94430bf28861f6510c2eca2187f54430bea8861f5510c2eaa2187f14430ffa0861fe410c3fa82187f10430ff98861fe310c3fa62187f0c430ff90861fe210c3fa42187f08430bf28061ff400c3fc80187f50030fe20061ff300c3be60187f8c030fd18061fd300c3ba60187e4c030ffaa6417f54c83fca9905f95320feaa6417d54c83f8a9905f15320ffa9e417f53c83fca7905f94f20fea9e417d53c83f8a7905f14f20ffa1e41fe43c83fa87907f10f20ffa1641fe42c83dc85907f50b20f6a1641fc42c83fe65907f8cb20f719641fd32c83da65907f0cb20ffa8e41fe51c82fca3907f54720bea8e41fc51c83fe83907f90720fea0e41fc41c83fe63907f8c720fe98e41fc31c83fe43907bc8720ff10e41fd21c83da43907f08720ffa0641fe40c83fa81907f10320ff98641fe30c83fa61907f0c320ffaa4417f54883fca9105f95220feaa4417d54883f8a9105f15220ffa9c417f53883fca7105f94e20fea9c417d53883f8a7105f14e20ffa1c41fe43883fa87107f10e20bea9441ff42883fc85107f50a20fe21441ff32883fc65107f4ca20fe19441ff51883fca3105f94620fea8c417d51883f8a3107fd0620ff20c41fd41883f883107fcc620ff18c41fd31883f863107fc8620ff10c41fd21883f843105f94220ffa0441fe40883fa81107f10220ff98441fe30883fa61107f0c220ff90441ef20883f641107fd5120bfaa241fe54482fca8907f55120beaa241fc54482f8a8907fd4d20bfa9a41fe53482fca6907f54d20bea9a41fc53482f8a6907fd0d20ff21a41fd43483f886907fd0920ff21241ee42483fa84907b50920fe21241ff32483fc64907b8c920fe99241ed32483f864907fd4520bfa8a41fe51483faa2907f14520be28a41ff41483fc82907f50520fe20a41ff31483fc62907f4c520fe18a41ff21483de42907f88520fe90a41ed21483f842907fd0120ff20241fd40483f880907fcc120ff18241fd30483f860907fc8120fd90241fe20483dc40907fd5020bfaa041fe54082fca8106f950209f2a041fd54082faa8106f550209eaa041fc54082f8a8107fd4c20bfa9841fe53082fca6107794c20af29841fd53082faa6107754c20aea9841fc53082f8a6107fd0c20ff21841fd43083f886105f94820ffa1041fe42083fa84107f10820ff99041fe32083fa64107f0c820ffa8841fe51082fca2107d94420bb28841fd51082faa2107d54420baa8841fc51083fe82107f90420fea0841fc41083fe62107f8c420fe98841fc31083fe42107f88420fe90
  | 2 => 0x3fe81206fd0240fda0481ff53502fea6a077d4d40afa9a81fe53503faa6a07f14d40be29a81dc53502b8a6a07fd0d40dfa1a81fe43503fa86a06f50d40fe21a81ff52502fea4a07f94940fea9281fc52502f8a4a07fd0940dfa1281fe42503fa84a06f50940fe21281ff32503fc64a07f4c940fe19281ff51502fea2a07f94540fea8a81fc51502f8a2a07fd0540dfa0a81fe41503fa82a06f50540fe20a81ff31503fc62a07f4c540fe18a81ff21503fc42a07f48540fe10a81ff40503f680a07f90140df202817e54103fea6207f94c40bf29881de53102bca6207f54c40bea9881dd53102baa6207f14c40ffa1881fe431037c86207f50c40fe21881bc43103fea4207f94840bf29081ee52102dca4207f54840bea9081ed52102daa4207f14840ffa1081fe42103fa84207f10840ff99081fe32103fa64207f0c840ffa8881fe51102fca2207d94440bb28881fd51102faa2207d54440baa8881fc51103fe82207f90440fea0881fc41103fe62207f8c440fe98881fc31103fe42207f88440fe90881fc21102fca0207fd0040dfa0081fe40103f480207f50040dea0081f940103fea9985fd5330ff2a6617e54cc3faa9985f55330fe2a6617c54cc3fe87987f90f30ef21e61fd43cc3ba87987f10f30ffa9661fe52cc2fca5987f54b30bea9661fc52cc3fe85987f90b30fea1661fc42cc3fe659877ccb30ff19661fd32cc3ba65987f0cb30ffa8e61fe51cc2fca3987f54730bea8e61fc51cc3fe83987f90730fea0e61fc41cc3fe639877cc730ff18e61fd31cc3ba63987f0c730ff90e61fe21cc3fa43987f08730ffa0661fe40cc3fa81987f10330ffaa4617f548c3fca9185f95230feaa4617d548c3f8a9185f15230bea9c61ff438c3be87187f90e30fea1c61fc438c3b887187fd4a30ff294617e528c3faa5185f54a30fe29461ff428c3fc85187f50a30fe21461ff328c3fc65187f4ca30fe19461ff518c3fca3185f94630fea8c617d518c3f8a3187fd0630ff20c61fd418c3f883187fcc630ff18c61fd318c3f863187fc8630ff10c61fd218c3f843185f94230ffa0461fe408c3fa81187f10230ff98461df308c3f661187fd5130bfaa261bf544c27ea8987f95130bf2a261fd544c2faa8987f15130be2a261bc544c278a8987fd0d30ff21a61de434c3fa86987750d30fe21a61ff524c2fea4987f94930fea9261fc524c2f8a4987fd0930ff21261fd424c3f884987fcc930ef99261fe324c3fa6498774c930fe19261ff514c2fea2987f94530fea8a61fc514c2f8a2987fd0530ff20a61fd414c3f882987fcc530ef98a61fe314c3fa6298774c530fe18a61ff214c3fc42987f48530fe10a61ff404c3fc80987f50130fe20261ff304c3f660987f8c130ef18261ff540c2fea8187f95030bf2a061be540c27ca8187f55030beaa061b
  | 3 => 0x6218fd8c431fe98863dd310c7ea6218ffd4031ff280637e500c7faa018df54031fe28063ff54c86fea990ff95321bf2a643fd54c86faa990ff15321be2a643ff53c86fea790ff94f21bf29e43fd53c86faa790ff14f21be29e43ff43c87fc8790ff50f21fe21e43ff42c87fc8590ff50b21fe21643ff32c87fc6590ff4cb21fe19643ff41c87fc8390ff50721fe20e43ff31c87fc6390ff4c721fe18e43ff50c87fca190df94321fea86437d50c87f8a190ffd5221bfaa443fe54886fca910ff55221beaa443fc54886f8a910ffd4e21bfa9c43fe53886fca710ff54e21bea9c43fc53886f8a710ffd0e21ff21c43fd43887f88710df54a21ffa1443fe42887fa8510ff10a21ff99443fe32887fa6510ff0ca21bf28c43ff41887fc8310ff50621fe20c43ff31887fc6310ff4c621fe18c43ff21887de4310fdc8621ffa8443fe50886fca110ff54221bea8443fc50887fea890dfd5121ff2a2437e54487faa890df55121fe2a2437c54487fea690dfd4d21ff29a437e53487faa690df54d21fe29a437c53487fe8690ff90d21fea1a43fc43487fe8490ff90921fea1243fc42487fe6490ff8c921fe99243fc32487fe8290ff90521fea0a43fc41487fe6290ff8c521fe98a43fc31487fe4290fdc8521ff10a43ee21487fea090dfd4121ff28243fd50487f8a090df14121ffaa0437f54087fca810df95021df2a0433e54087faa810df55021deaa0433d54087f8a810df15021ffa98437f53087fca610df94c21ef298435e53087faa610df54c21eea98435d53087f8a610df14c21ffa1843fe43087fa8610ff10c21bf29043ff42087fc8410ff50821fe21043ff32087fc6410ff4c821fe190437e51087fe8210ff90421fea0843fc41087fe6210ff8c421fe98843fc31087fe4210fbc8421ff10843f621087fa4210fb48421fa90843e521087fea010ff94021bf28043fa50086f4a010ff54021bea8043f950086f2a010ff14021ffa9e81fe53d02fca7a07f54f40bea9e81fc53d03fe87a06fd0f40ff21e81fd43d037a87a07f10f40ffa9681fe52d02fca5a07f54b40bea9681fc52d03fe85a06fd0b40ff21681fd42d037a85a07f10b40ff99681fe32d03fa65a07f0cb40ffa8e81fe51d02fca3a07f54740bea8e81fc51d03fe83a06fd0740ff20e81fd41d037a83a07f10740ff98e81fe31d03fa63a07f0c740ff90e81fe21d03fa43a07f08740beaa481ff53903fca7205f94e40fea9c817d53903f8a7207fd0e40ff21c81be43903fa87207f10e40de21c81ff52903fca5205f94a40fea94817d52903f8a5207fd0a40ff21481fd42903f885207fcca40ff19481fd32903f865207fd4640ff28c817e51903faa3205f54640fe28c81ff41903fc83207f50640fe20c81ff31903fc63207f4c640fe18c81ff21903fc43207f48640fe10c817e509
  | 4 => 0xff10f41de21e83ff52d07fca5a0df94b41fea96837d52d07f8a5a0ffd0b41dfa1683fe42d07fa85a0ef50b41fe21683ff32d07fc65a0ff4cb41fe19683ff50d07fca1a0df94341fea86837d50d07f8a1a0df55241ffa9c83fe53906fca720f794e41af29c83fd53906faa720f754e41aea9c83fc53907fe8720ff90e41fea1c83fc43907fea520ff94a41bf29483fd52906faa520ff14a41ffa1483fe42907fa8520ff10a41ff99483fe32907fa6520ff0ca41bf28c83ff419077e8320fdd0641ffa8483fe50906fca120ff54241bea8483fc50907fea6a0dfd4d41ff29a83fd53507f8a6a0df14d41ffa1a83fe435077c86a0ff50d41fe21a83bc43507fea4a0dfd4941ff29283fd52507f8a4a0df14941ffa1283bf42507fc84a0ff50941dea1283fc42507fe64a0ff8c941fe99283fc32507fe82a0fdd0541ff20a83be41507fea0a0dfd4141ff28283fd50507f8a0a0df14141bf2a083ff53107fca620df94c41fea98837d53107f8a620ffd0c41ff21883fd43107f88620ffd4841ff290837e52107faa420df54841fe29083ff42107fc8420ff50841fe21083ff32107fc6420ff4c841fe190837e51107fe8220efd0441ff20883f641107fa8220ef50441faa0883ff50107fca020df94041fea80837d50107f8a020ffd5331bfaa663fe54cc6fca998ff55331beaa663fc54cc6f8a998ffd0f31efa1e63fe43cc7fa8798ff10f31ee21e63ff52cc7fca598df94b31fea96637d52cc7f8a598ffd0b31ff21663fd42cc7f88598ffccb31ef99663fe32cc7fa6598f74cb31fe19663ff41cc7fc8398ff50731fe20e63ff50cc7fca198df94331fea86637d50cc7f8a198ffd5231bfaa463fe548c6fca918ef952319f2a463fd548c6faa918ef552319eaa463fc548c6f8a918df54e31ffa1c63fe438c7fa8718ff10e31ffa9463fe528c6fca518ff54a31bea9463fc528c7fe8518ff90a31fea1463fc428c7fe6518ff8ca31fe99463fc328c6fca318ffd0631ff20c63fd418c7f88318ffcc631ef98c63f7318c7fea118ff94231bf28463fd508c6faa118ff14231ffaa2637f544c7fca898df95131feaa2637d544c7f8a898df15131ffa1a63df434c7fc8698ff50d31fe21a63dc434c7fea498dfd4931ff29263fd524c7f8a498df14931ffa1263fe424c7fa8498ff10931ff99263df324c7fc6498ff4c931ee99263fc324c7fe8298ff90531fea0a63fc414c7fe6298fdcc531ff18a63de314c7fea098dfd4131ff28263fd504c7f8a098df14131ffaa0637f540c7fca818df95031feaa0637d540c7f8a818df15031bf29863ff430c7fc8618ff50c31fe21863ff520c7fca418df94831fea90637d520c7f8a418ffd0831ff21063fd420c7f88418ffcc831ff19063fd320c7f86418df94431ffa0863fe410c7fa8218ff10431ff98863df310c7fc
  | 5 => 0x943be29287ff5150efea2a1ff94543fea8a87fc5150ef8a2a1ffd4143bfa8287fe5050ffaa0a1ff14143be282877e5410efca621ffd0c43dfa1887fe4310fbc8621ff50c43dea1887dd4310f3a8621ffd4843ff290877e5210ffaa421df54843fe29087ff5110ffca221df94443fea88877d5110ff8a221ffd4043ff280877e5010ffaa021df54043fe28087ff53d0bfca7a15f94f42fea9e857d53d0bf8a7a17fd0f42ff21e85be43d0bfa87a17f10f42de21e85ff51d0bfca3a15f94742fea8e857d51d0bf8a3a17fd4342ff286857e50d0bfaa1a15f54342fe286857d5490bfea7217f94e42bf29c85de5390abca7217f54e42bea9c85dd5390abaa7217f14e42ffa1c85fe4390bfa87217f10e42bf29485ff4290b7e85217bd0a42ffa8c85fe5190afca3217f54642bea8c85fc5190bfea1217f94242bf28485fd5090afaa1217f14242ffa9a857f5350bfca6a17f54d42fe29a857c5350bfe86a17f90d42df21a85fd4350bf886a16f10d42ffa1285ef4250bfc84a16f90942ffa8a857f5150bfca2a17f54542fe28a857c5150bfea0a15fd4142ff28285fd5050bf8a0a15f14142bf2a085ff5310bfca6215f94c42fea98857d5310bf8a6217fd0c42ff21885fd4310bf886215f94842ffa1085bf4210bfc84217b90842fea1085bd4210bda84217fd4442ff288857e5110bfaa2215f54442fe28885ff5010bfca0215f94042fea80857d5010bf8a0217fd5332bfaa665fe54ccafca9997f55332beaa665fc54ccaf8a9997fd0f32efa1e65fe43ccbfa87997f10f32ee21e65ff42ccbfc85997f50b32fe21665ff51ccbfca3995f94732fea8e657d51ccbf8a3997fd4332ff286657e50ccbfaa1995f54332fe28665ff548cafea9197f95232bf2a465be548ca7ca9197f55232beaa465bd548ca7aa9197f15232be2a4657d538cbfe87197f90e32fea1c65fc438cafca5197fd0a32ff21465fd428cbf885197fcca32ef99465ef328cbfea3197f94632bf28c65fd518cafaa3197f14632ffa8465fe508cafca1197f54232bea8465fc508cbfea8995fd5132ff2a2657e544cbfaa8995f55132fe2a2657c544cbfe869977d0d32ff21a65fd434cbf886997710d32ffa1265fe424cbfa84997f10932ff99265ef324cbfc6499778c932ffa8a657f514cbfca2997f54532fe28a657c514cbfea0995fd4132ff28265fd504cbf8a0995f14132ffaa0657f540cbfca8195f95032feaa0657d540cbf8a8195f15032bf29865ff430cbfc86197f50c32fe218657e520cbfe84197f90832fea1065fc420cbfe641977cc832ff19065ee320cbfa6419774c832f699065ff510cbfca2195f94432fea88657d510cbf8a2197fd4032ff280657e500cbfaa0195f54032fe28065ff53d07fca7a0df94f41fea9e837d53d07f8a7a0ffd0f41ff21e83be43d07fa87a0
  | 6 => 0x2401003c0c400001c00801401001400c00800401002800000400000001802c03c00400401800001802000001001005401000800001402804800001c0000180140080000000300200281140000040c401c02c00000c03800000804806400400c00001002800800005003c00000000000400405001000400009002400001401400000c00401001c01c02402c00000800003005802400400001400800001000000000000402001400001c04802401007c0600080080080080340000040100340180480040ec00400c01000400002002000000000401801001801400001c00804c00402404000800001000400000000400805c03407407000000802000000400000802c03800000807400001003000800400401802400001400c00400000400000006c00400c01404c00000c00005000c02800000803401c00403002004c01801401002000001002002407000000800000807c00400402001800000001809001001c00004800403800400400c05c01400000002800000002800c01005802800c00800800000400002c00002403400003c00002c00800c00800000401400000003803404c00400400000c00000000c00401400000400003000400801401401000800001402803800403800000002801c00405800400000c00801803800000401400003000404800800001c00000000400800000000c01803c01c02400003800400800000400400000401c01400400400001c01004800002c00401c02400c00000000000402803c00c00c00800c00002c02402400c02c0140040a403c01800000807800800400403800800404400003401802400000001800406c00000807000c0240080140000000080300080180080000280000a404000000000c00000000000000800800004000c04800000000800c05804804c02c02c00002c00000400405001807000000000001c01004800000001402c0000a000003800c03400c0000180380000040300080ac01800c00000800800000000001001c08000802000002800c04000400c00000400404003c00805c03803403800001401001402801000400007000801400800004c00004c01402c0240000040d002000000400800400001000402c02400401801803800402801001000400400400000001c00802801800001000000401c00402400801400c0140000a0018004008000094017fea5a1ff94b43bf29687fd52d0efaa5a1ff14b43ffa8e87fe51d0efca3a1ff54743bea8e87fc51d0ffea1a1ff94343bf28687fd50d0efaa1a1ff14343beaa4877e5390ffe8721efd0e43efa1c87ff5290ffca521df94a43fea94877d5290ff8a521ffd4643ff28c877e5190ffaa321df54643fe28c87ff5090ffca121df94243fea84877d5090ff8a121ffd0d43efa1a87fe4350f7c86a1ffd4943bfa9287fe5250ffaa4a1ff14
  | 7 => 0x8503f29a33a262061a898f7226b0280025110b833848800227ab99f89970de2f680012c05180000019b0158000de9aa00008697833c0000be8003228441350000001a600030b00000000000a8000000002110001862bd8510000000000242bbba49a115300033022c1888002aa000137a6191324c87e386b5900006a3980001a729e83b8002f0a753403260f10000f41bb15cb2b3810422a2330a6a37f274825b1011605e2331598000b400019c8002548002f10cb8502a897d0000000002bea81233b3534700000027f0d79b0938366b8209e37a8000000c5b461482ac2058a1007af58aaafe2d8a170001bba863752f31ab2c03838008028b5a651b10dab7006b9680002d4aae11689500000000026593201781cac50000002a30fc80000039797aa10ab88580003069d50201d9183b4c960356845906a9aa4000002980000000006405680000032eba08001730b2aa78e20000000001712210cf98235814d80fa950001ff9d08820db2e29c4908044865b50935b3400000039301b10a90d0ea00020e0002081fd9280f918480028d8000000000d010400026e000000000000113a0980025c13300026f00000005d1c08000000ec000380b4fb1d2670b100000000000000010c00000017ba2fad294690538b2f9b7f9e780c07280000023d1ad0000132fa00000022498c80019a1b70ca13e21b9cf0302c18d8219881a2331998a9511efa04ac901380025300000035f94a80000029ba830b99408000002308f692f00011ba521dc3108ed0001e80d3b7729b301acf9fb1a4ac48002dc00000000000012b00004a189a188000000001630000000000af0000001118001398a21ba80004cb6f14500018fab220d8051b41af2ef8d422022b155040b219d627292392735ea123a28e011eb4b08b0253559a198e29ca7e3250759458779a3aea0e88351180331afb93a3036c2d5a928199a92eb1a43992908d19bc000000000181acd1660632b72e81b1aa699622e80000000012400002680004b06d2820c02648da20f0000000001be0001ca8c08d20b200000002837c1db3478c50ac1f41e70dc8f2af60ba0e6276a2a199333a45235344b7b8c3a9c03ab0e28010993f000090375a4b853b48866b8423b07d395822a858001ec2f4af80e6b0495b0f219fb8e259317b1da6c16e8002740001b80000000062428000c415b8000003618001559d9b9235d01e00000000035329d0001abb6aa409d12fb9d70001c6000130893a5d80027a805a318000a01faaeea69800103000000358a9323880028b1e61788000000d58001a8b29b2fb68207903b8a26b010004801000000807402c01c00400403004400800401004400c00000c05803001000001400000c00000002401000001400c0f400000000000003000003400000003001402000002400003004c01000
  | 8 => 0x290580000000000022e2fc00000000020090c9d7aa70c680000009c9f1062b4b8002e3a010000002b396900000032b80000000029400020d0a70e90000002888001c3800000232b16273a288f196a0000f50140002b52608e400032dacc0002cc8000a193f9e000000025e35116098eb5f0d4872215a959bd11c052b119999eb26102fa1c8002de80036e80008380000880014e0a48002c100009938521d270000000000055a570002808002920003988001eb9ef3720002df2d10ce9b5b5424b00028e1a097014a23b8001cd8003a500002b0a516c0ffa7831880000039c80031a8b3929a36a0c946381a5039a26c91007cb232fea7d8fb89daef0ae0a080003a0cf3010e29470001f200008596a994900b0c8fc1908f580004312485635db3a8000000002af136a4497080ead40b480019136209200039b32a0ea889b878000002840811dd8661c2b539413498270091891b2b6b01a314914a52a47b0300f07706c820b311fc8e707fa710cda4e03d16c80033e31e803b43034b24a0a0fea640ec800251b381fe0b92d72f8ba1b0c2a10498003529f800024ea6dab6b5708011c8ce0000001d2aaa8002c685303d80037193d3388fd8d92ec0b0800214a438001b980000016e39f82304d3642bf06880000000000028780000002897fb04000154b5b00000038eb8322938d18d0ed93713d81680011f1a980000027b84e91a80000006fb740f8a3991b11502d088893391a5fb3708799f33f09f185aa510284a85b0c625d2ceaba1c8a6032f0ef2a5a541769f50001ca1aeb763a680000000b9d835c333092af00df0033891bcacb064b7e0d280036300000028380000139a8122baaf28002c20001833280e09ea2de1a798d9da360ada0609528d9a028aea1a0a41c5b2890e8748dfac819d8e30000000000000d300034220883218105e9bf000091258b451b00579f6b613369878002340fab9eb4e36a2c40000001d1aa92c317dad19310001720fb0c49109b600000028813927e85f015275ae700010f8e107080da2f3901fa1e0b5602e22d21e818a0614430f17e1ff0400000001f0117ba58001df00e299a7600022384bae33a32af87014e8002348b1ad3899a06922a82b0082d95f8000a68980ab94cae7a5a25b0002b1a469f28001f38000001650002690000000002e49e68002418508e78000001a20aa00037287f125091a4da219290a8069aca0f386f21b2dd3379e90dc28d03c977000368a1680000039719286702c93c8e51fc0b000013c00208c80008d80037c8000f6000341a2200001e8eb3002430ee8a3007115a6880032213a0001c522d91984789f80000019380030ba252410000000000000000001d49e591a00000000000023780a165a48148a4f88a8b7b0891f87820b12a0f81fb82198f0761ba19aa798429c10359502312a48
  | 9 => 0x1e3acf05c800359a372118000003290730b8800278b141c909600001fac597b00009c2978c20000000000002c380000020921c0309d236d80000000000030590198500026280000037b00012e80020400000032a8cc80000002c00000000039db768000000000018001540003889360000003a42852a630600000031b1f99940cd0001209508000000600000000c11c18000003638000890002242472bb18094790a00015e1c322c8171140cb15d1b78001268410001cb19036d08ba1faf1b3d800078a8ca4a17f18725f07b0001968002160000c8b4400015c1cb838967acaa70b20a4a90000031525a9dfa5b8d8873b9e03607c32c1e99a5b13b4a11d2dd8310399ee8000000000bd898a3d82a86e000000000134800000000000245982810a980a3b2e0ad8c985f8001a697e80000000015e8003501a300000020e997a8c3928000000000000a900015d80000018b80000033e869198a969588a60002a0000054000087000294a261621dd02488819d36920713ea272b2b649b4ab4ab316f2d9a538000bb2891ae01904f9bd8000002e61ac89d1628001e18002a0a848001e20000000000552ea8b61c7943b1f8002b58000002ee09aaf7941ae900025e9638002dab6e1e41c00001aa89b28f8000000ad39107e800076827ab13a39ce800000034222a4d12131900402a1f08f329d8000000002e000029038f38a83c1ee2d68f033631ba129f5af924405a1b6ab08612582cbba00efac635a06395f3a203f9c805493bb2c975ac0800286b6bb40a6aa9896f85a94f01f1762f3b05169977b42b169ea80690909e8e381da632be35184e0fa345b55297201ad827c36714d0940001de0b700034e88e9c418800000015600019b86d80004707980012fa020002492a43170000c280009700007a36c8220002ce2498002460372bc80037ea0f8000000e180d1f483780015180000018b2b90b6b39a1da2ba791da816000365b9c33d30230d964107307b23a59a770968000002bd2d08001342360000000001258000001011de80021e0c79a533ba1011db1231108c0002f200021780037100008d000374991897b090000000001120b529f01b912ae680005d85702904d86b1492870c81719790719d88002ad29e0112fab9f1cd00022ab4903e93b32588a30d02600029fb7d12017c82f000303a9639d299256161a6eb870ebb57a0334d14b8c91feaa980038baa81648740d711938da6638c07aa13831a67a052b61b300018c1922fc8be3a603812daf426f800000195a420002ab8002181798a98ca87b8bc1c9aad89488480036501823ea91ae103901d3328af9d338280028f1d3af50001b3ae221a9751428590dd908b34b070cc33f90d875373b9512baebac89749590598418003898000329f600031e2209931a01e488f1671579f3121ad22db36017
  | 10 => 0x2bc30fa57a8ba7b36620a9e130980005baa1b5223935ab782a396b012a3e21309a00000004c0002c28000002ff800004a912b79ac00000006eb410000bd0c70ee104b998a8b6780026d00018012882bb9435cad32638000001338003270000002c70000002193859112283211f19e28f9a7d2719d5ac990e1fd1060f78002e40000468000003279e8814ab008e0001951523960a795826b8f08000712dcae5944ba10002ac90793002e80001a96100cb792ff31f3628ac8a280b2db84800005c00016b80017c0d68002e880018a17a33c90f00037a38cb1c22980000000000000001c0000001230000bf1d42d900030e8002489020d60620000000000790001260ab0bfb2020380028e8000368490000002151ed80036994f91e00000000000000000000000014b0001f71cf800142140000377811a3f80015a000343800149809ad613aafb0e596d0001b20439be938b0ab6f95aa0c2d79742fd92d38827c9668000861dca508003468000002cd92aa558b333b00000000011880021f11704f00024c14c3731c207d80023580006780034828a08fb15b5e03b0001688b800028ab94a550002dfb4daec92c99e9ad8841d694312e00032d2e5335b801ec8001ce27a00033223ca731b89ed0ba9a28dd2381cc34ab0a0000a58dbb8f8522fd0e800000000000016d8002d500000000000010b0001539b91c6a3a0001319cc922266895b96b4c0000d519c2d00c32ab02399e1982bf9a80e98002e98000002b42a28000000000001569f7aed0d09db9d0293af7000046313000318058a680003848bb890ab83548003269b500037d80006c2142778828e49739bfb240bc8f4a0bb1ca7fa32390b9b9278000003708d100023a80035b8fd25cb860002ed984272000000045200331a819e5000000132ae08fe03e1c731a34f23c1571f92ae8083798ff1e32c788324f0c188086530800000006ab3909b868000225a3f2e1a56b12800186b78821
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x3400435e53d0010d754f400436e52d0010db54b400427f65900109f596400433e5490010cf552400435e5390010d754e400436e5290010db54a40042f66190010bd586400427f6550010cf951400433d5450010b7d8d40042dc6350010d794d400435d5350010db949400436d52500109fd94400427e65100109f594400427c6510010cf950400433d5410010b798c40042dd6310010d794c400435d5310010bb98840042ed6210010db948400436d5210010bd98440042f561100109f597300433e54cc010cf553300435e53cc010d754f300436e52cc010db54b300427f658c0109f596300433e548c010cf552300435e538c010d754e300436e528c010db54a30042f6618c010bd586300427f654c010afd9130042bc644c010cf951300433d544c010d794d300435d534c010db949300436d524c0109fd94300427e650c0109f594300427c650c010af99030042bd640c010cf950300433d540c010d794c300435d530c010bb98830042ed620c010db948300436d520c010bd98430042f5610c0109f597200433e54c8010cf553200435e53c8010d754f200436e52c8010db54b200427f65880109f596200433e5488010cf552200435e5388010d754e200436e5288010db54a20042f66188010bd586200437a50880109fd95200433e5448010cf551200435e5348010d754d200436e5248010db549200437a50480109fd94200427e65080109f594200427c6508010af99020042bd6408010cf950200433d5408010b798c20042dd6308010d794c200435d5308010db948200436d5208010bd98420042f56108010cf953100433d54c4010d794f100435d53c4010db94b100436d52c4010dd597100437754c4010ed953100437554c4010ed553100433554c4010ddd4f10043d653c4010dd54f10043d553c4010d554f100437752c4010f994b100437552c4010f954b100436552c4010cf952100433d5484010d794e100435d5384010db94a100436d5284010bd58610043765184010be596100437965840109e59610043ba5484010ee55210043da5384010f654e100437b5284010fa94a10043795284010fa54a10043695284010be586100437a5184010fc946100427f6544010cf951100433d5444010d794d100435d5344010db949100436d5244010bdd95100437765440109dd9510043775444010ed95110043755444010ed55110043355444010ddd4d10043d65344010dd54d10043d55344010d554d10043775244010f994910043755244010f954910043655244010bdd8110043765044010fc88110043f12044010bed95100437b65440109ed9510043ba5444010ee55110043da5344010f654d100437b5244010fa94910043795244010fa54910043695244010bed8510043f36144010de94510043f25144010fc88510043f12144010
  | 1 => 0x433d54d0810d794f420435d53d0810db94b420436d52d08109fd96420427e65908109f596420427c6590810cf952420433d5490810b798e42042dd6390810d794e420435d5390810db94a420436d52908109fd95420427e65508109f595420427c6550810cf951420433d5450810d794d420435d5350810db949420436d5250810bdd8542042f461508109fd94420427e65108109f594420427c6510810cf950420433d5410810d794c420435d5310810db948420436d52108109fd97320427e65cc8109f597320427c65cc810cf953320433d54cc810d794f320435d53cc810db94b320436d52cc8109fd96320427e658c8109f596320427c658c810af99232042bd648c810cf952320433d548c810d794e320435d538c810db94a320436d528c8109fd95320427e654c8109f595320427c654c810cf951320433d544c810d794d320435d534c810db949320436d524c810bdd8532042f4614c8109fd94320427e650c8109f594320427c650c810cf950320433d540c810d794c320435d530c810db948320436d520c8109f992510427d64944109f98e510427d63944109f98a510427d62944109f597410433e54d0410cf553410435e53d0410d754f410436e52d0410db54b410427f65904109f596410433e5490410cf55241042de6390410b758e410435e5390410d754e410436e5290410db54a41043765190410be98241042f960904109fd95410433e5450410cf551410435e5350410d754d410436e5250410db549410437651504109fd94410427d6510410cf950410433d5410410d794c410435d5310410db948410436d5210410be98041042f960104109f597310433e54cc410cf553310435e53cc410d754f310436e52cc410db54b310427f658c4109f59631042be648c410af592310433e548c410cf552310435e538c410d754e310436e528c410db54a3104376518c410be98231042f9608c4109fd95310433e544c410cf551310435e534c410d754d310436e524c410db5493104376514c4109fd94310427d650c410cf950310433d540c410d794c310435d530c410db948310436d520c410be98031042f9600c4109f597210433e54c8410cf553210435e53c8410d754f210436e52c8410db54b210427f65884109f596210433e5488410cf552210435e5388410d754e210436e5288410db54a21043765188410be98221042f960884109fd95210433e5448410cf551210435e5348410d754d210436e5248410db549210437651484109fd94210427d6508410af99021042bd6408410cf950210433d5408410b798c21042dd6308410d794c210435d5308410db948210436d5208410f948421042fa6008410be580210427e64940109f592500427e63940109f58e500427e62940109f58a500427d61940109f597400433e54d0010cf55
  | 2 => 0x6154c10d7185530435e6054c10d7181530435c1054c10af99053042bd6414c10cf950530433d5414c10b798c530435d5314c10bb98853042ed6214c109f990530433e6414c108f990530427d6414c10cf590530423d6414c109f98c530435e6314c109798c530427e6214c10db988530426e6214c109f588530436d6214c109b588530427e6114c10dd98453042766114c109f980530437a6014c109fd97430427e65d0c109f597430427c65d0c10cf953430433d54d0c10d794f430435d53d0c109fd96430427e6590c109f596430427c6590c10cf952430433d5490c10d794e430435d5390c109fd95430427e6550c109f595430427c6550c10cf951430433d5450c10d794d430435d5350c109fd94430427e6510c109f594430427c6510c10cf950430433d5410c10d794c430435d5310c10e750c43042be64d4810af593520433e54d4810cf55352042de63d4810b758f520435e53d4810d754f520427e64d4810cf993520423e64d48109f593520433d64d48108f593520427e63d4810d798f520425e63d48109f58f520435d63d48109758f520427e61d4810dd987520427e60d4810de983520427d6594810cf952520433d5494810d794e520435d5394810dbd4a520427e64948109f592520427e63948109f58e520426d6594810dbd52520436e5494810eb952520432e5494810db55252043ad5494810cb552520436c5494810dbd4e520436e5394810f394e520434e5394810db54e52043cd5394810d354e520436c5394810dbd92520436e6494810db592520436c6494810dbd8e520436e6394810db58e520436c6394810dbd0e520436e4394810db50e520436c4394810db986520436c6194810db982520436c6094810cf951520433d5454810d794d520435d53548109fd91520427c64548109fd8d520427c6354810dbd89520427f61548109f585520427f60548109f581520436f6554810dbd51520436e5454810eb951520432e5454810db55152043ad5454810cb551520436c5454810dbd4d520436e5354810f394d520434e5354810db54d52043cd5354810d354d520436c5354810dbd91520436e6454810db591520436c6454810dbd8d520436e6354810db58d520436c6354810dbd0d520436e4354810db50d520436c4354810db985520436c6154810db981520436c6054810db04152042be6414810af590520433e5414810cf55052042de6314810b758c520435e5314810d754c52042ee6214810db548520427e6414810cf990520423e64148109f590520433d64148108f590520427e6314810d798c520425e63148109f58c520435d63148109758c520427e6214810db988520426e62148109f984520437661148109d984520427e6014810de980520427a60148109fd97420427e65d08109f597420427c65d0810cf953420
  | 3 => 0x1109e19520443eb6248110fad49204437a5248110de14920443e85248110fa90920443e94248110fa8c920443e93248110fcd8520442f86148110fc18520443f24148110fc50520443f23148110fc4c520443eb2148110fc88520443e92148110fc48520443e121481109f99420442be6408110af59020442de6308110b758c20442f66108110bd58420442fa6008110fa48020442fb62c4110be58b10443f241c4110fc50710443f231c4110fc4c710443f221c4110fc48710442f76484110bd59210442f76384110bd58e10442f76284110bd58a10443f35084110fc88210443f12084110b798f54042dd63d5010bb98b54042ed62d50109f98f540435e63d50109798f540427d63d5010d758f540425d63d50109f98b540436e62d50109b98b540427d62d5010db58b540426d62d50109f987540437661d50109f983540437a60d50109f596540433f54950109f98e540427d63950109f98a540427d62950108f596540433f6395010cf98e540433d6395010cf18e540433f6295010cf98a540433d6295010cf18a540433e6195010cf186540433e6095010cf182540433f64550109fd8d540427c63550109fd89540427c62550109fd85540427d61550109fd81540427d6055010cfd95540433f6355010cf98d540433d6355010cf18d540433f6255010cf989540433d6255010cf189540433e6155010cf185540433e6055010cf181540433c1055010af990540433d5415010b798c54042dd6315010bb98854042ed62150109f990540433e64150108f990540427e6315010d798c540425e63150109f58c540435d63150109758c540427e6215010db988540426e62150109f588540436d62150109b588540427e6115010dd984540427661150109f980540437a6015010af99353042bd64d4c10cf953530433d54d4c10bb98b53042ed62d4c109f993530433e64d4c108f993530427d64d4c10cf593530423d64d4c109f98b530436e62d4c109b98b530427d62d4c10db58b530426d62d4c109f987530437661d4c109f983530437a60d4c109f596530433e5494c10cf552530435f5394c109f992530427d6494c109f98a530427d6294c1097596530435f5494c10d7952530439e5494c10c7952530435d5494c10e7552530431d5494c10d7152530435f6494c10d7992530435d6494c10d7192530435f6294c10d798a530435d6294c10d718a530435e6194c10d7186530435e6094c10d7182530433e5454c10cf551530427f6454c109f191530435f6354c109fd89530427c6254c109fd85530427d6154c109fd81530427d6054c10d7d95530435f5454c10d7951530439e5454c10c7951530435d5454c10e7551530431d5454c10d7151530435f6454c10d7991530435d6454c10d7191530435f6254c10d7989530435d6254c10d7189530435e
  | 4 => 0xd58432442fa600c910be580324427e65d0510cfd53414433c54d0510be98341442f960d05109f99641442de6390510b758e41442f66590510dd99641442f56490510dd95241443745490510f598e41442f56390510f558e41442d56390510bd58a41442f660905109f195414433f5450510cf15141442fb6050510be181414437465505109d19541443b76450510edd5141443765450510dd15141443b45450510bdd8d41443b64350510ed10d41442f76250510edd0941443b54250510fcd8141442f46050510fc181414427e6510510bd98441443b541105109f997314435f53cc510d714f31442fa60cc510be583314427e658c510af99231442bd648c510bd9963144376658c510bdd9231443b6648c510bd59231443b5648c510ad59231442f5638c510dd94e3144374538c510bd58a31442f6608c5109f195314435f534c510d714d31442fb604c510be1813144374654c5109d19531442f7644c510bd59131443d7634c510f5d4d3144376534c510dd14d31443d4534c510f5d0d31443d4434c510bdd8931443d7324c510f54c931443f3604c510bd18131443f0604c5109f99431442f6610c510f54c4314427e65c8510dbd4b214436c52c8510be98321442f960c85109f99621442f66588510dd99621442f76488510bd59221442f76388510bd58e21442f56288510dd94a21443745288510fcd8221442f66088510fc182214427c6548510dbd49214436c5248510bed8121442f86048510dd19521442746548510bdd9121442f56448510bdd8d21442f56348510f9d8921443e75248510dd94921443745248510f914921443645248510fcd8121442f46048510fc181214427e6508510af99021442bd6408510b798c21442dd6308510bd98421443e52108510be980214427e65d0110cfd53404433c54d0110bd98740442f561d0110ed507404427e65901109fd95404427d65501109f195404433f5450110cf15140442df6350110b718d40442f76150110bd18540443b541501109f99440442de6310110b758c40442ee6210110bb58840442f66110110bd584404427e65cc110d7d4f304435c53cc110bd98730442f561cc110f54c7304427e658c1109fd95304427d654c1109f19530442bf644c110af191304435f534c110d714d30442f7614c110bd18530443d5314c1109f99430442be640c110af59030442ee620c110bb58830442f6610c110bd584304427e65c8110dbd4b204436c52c8110bd98720442f561c8110f9487204427e6588110be996204437a6588110be58a204437a5288110de14a20443f36188110be98620443f06188110fc90620443f14188110fc8c620443f13188110fc88620443f121881109fd95204427d65481109f195204436f5248110db14920442f76148110bd18520443e52148110be19520443786548
  | 5 => 0x534427e62d4d109f58b534435f5394d109f992534427d6494d109f98e534427e6294d109f58a534427d6194d10dd586534427d6094d10de58253442bf6454d10af19153442ef6254d10bb189534427f6454d10cfd91534423f6454d109f191534433c6454d108f191534435f6354d109fd89534436f6254d109bd89534427c6254d10db189534426c6254d109fd8553443776154d109fd81534437b6054d109f994534435d5314d109f990534427d6414d10d798c534427e6214d109f588534427e6114d10dd584534427c6114d109f980534427c6014d109fd97434427e65d0d109f597434427c65d0d10d7d4f434435c53d0d10bd98743442f561d0d109fd96434427e6590d109f596434427c6590d10cfd52434433c5490d10bd98643442f56190d109fd95434427e6550d109f595434427c6550d109fd94434427e6510d109f594434427c6510d10cfd50434433c5410d10d7d4c434435c5310d10e750c43442f66110d10bd58443442fa6010d10be580434427e64d49109f593524427e63d49109f58f524436f52949109f992524427d64949109f98e524427d63949109f98a524427d6194910dd586524427d6094910de58252442bf6454910af19152442df6354910b718d524427f6454910cfd91524423f64549109f191524433c64549108f191524427f6354910d7d8d524425f63549109f18d524435c63549109718d524436f62549109fd85524437761549109fd81524437b60549109f99452442be6414910af59052442de6314910b758c524436d52149109f990524433e64149108f990524427d6414910cf590524423d64149109f98c524435e63149109798c524427d6314910d758c524425d6314910db988524427e6114910dd584524427c61149109f980524437960149109f180524427f65d09109f997424427d65d09109f197424433e54d0910cf553424436f52d0910db14b42442f661d0910bd587424427f65909109f996424427d65909109f196424433f5490910cf15242442de6390910b758e42442f66190910bd58642442fa6090910be582424427f65509109f995424427d65509109f195424433e5450910cf551424427f65109109f994424427d65109109f194424433f5410910cf150424436f5210910db14842442f66110910bd58442442fa6010910be580424427f65cc9109f997324427d65cc9109f197324435e53cc910d754f324436f52cc910db14b32442f661cc910bd587324427f658c9109f996324427d658c9109f19632442be648c910af592324435f538c910d714e32442f6618c910bd58632442fa608c910be582324427f654c9109f995324427d654c9109f195324435e534c910d754d324427f650c9109f994324427d650c9109f194324435f530c910d714c324436f520c910db14832442f6610c910b
  | 6 => 0x27c6550a10cf951428433d5450a10db949428436d5250a10bdd8542842f46150a109fd94428427e6510a109f594428427c6510a10be98042842f96010a109fd97328427e65cca109f597328427c65cca10d794f328435d53cca109fd96328427e658ca109f596328427c658ca10af99232842bd648ca10db94a328436d528ca10be98232842f9608ca109fd95328427e654ca109f595328427c654ca10d794d328435d534ca10db949328436d524ca10bdd8532842f4614ca109fd94328427e650ca109f594328427c650ca10be98032842f9600ca10cf953418433d54d0610be98341842f960d0610b798e41842dd6390610cf951418433d5450610bed8141842f86050610d794f318435d53cc610be98331842f960cc610af99231842bd648c610d794d318435d534c610bed8131842f8604c610db94b218436d52c8610be98321842f960c8610db949218436d5248610bed8121842f86048610af99021842bd6408610b798c21842dd6308610f948421842f96008610cfd53408433c54d0210cf952408433d5490210bd98640842f56190210cfd51408433c5450210b7d8d40842dc6350210cf950408433d5410210b798c40842dd6310210bb98840842ed6210210bd98440842f56110210d7d4f308435c53cc210d794e308435d538c210bd98630842f5618c210afd9130842bc644c210d7d4d308435c534c210af99030842bd640c210d794c308435d530c210bb98830842ed620c210bd98430842f5610c210dbd4b208436c52c8210db94a208436d5288210bd98620842f56188210be59620843796588210de94a20843ea5288210fa54a20843785288210be98620843f26188210fc586208436f5248210db14920842fb6548210ded9520843eb6248210fad49208437a5248210de14920843e85248210fa90920843e94248210fa8c920843e93248210be18520843eb2148210fa48520842be6408210af59020842de6308210b758c208436e5208210db54820842f66108210bd58420843e92008210bd597108437565c4210ddd53108437554c4210ddd4f108437553c4210ddd4b108437552c4210be597108437965c4210bed8b10842f962c42109f98f544427d63d51109f98b544427d62d5110cfd52544427e64951109f98e544427d63951109f98a544427d62951109f586544437561951109f58254443796095110b7d8d54442dc6355110bbd8954442ec6255110cfd91544427f6355110d7d8d544425f63551109f18d544435c63551109718d544427f6255110dbd89544426f62551109f189544436c62551109b189544427f6155110ddd85544427f6055110ded81544427e6515110cf550544433e64151109f98c544427d63151109f988544427d62151109f984544437561151109f184544427e60151109f180544427e64d4d109f593
  | 7 => 0x150310b798c40c42dd6310310bb98840c42ed6210310bd98440c42f56110310d794f30c435d53cc310bd98730c42f561cc310f54c730c42bf644c310af19130c435e534c310d754d30c42f7614c310bd18530c43d5314c310af99030c42bd640c310bb98830c42ed620c310bd98430c42f5610c310db94b20c436d52c8310bd98720c42f561c8310f948720c436e5248310db54920c42f76148310bd18520c43e52148310af99020c42bd6408310b798c20c42dd6308310bd98420c42f561083109f98f548427d63d52109f98b548427d62d5210dd587548437a60d5210cfd52548427e63952109f58e548427e62952109f58a54842df6355210b718d548433f64552109fd8d548435f635521097d8d548427c6355210d718d548425c63552109fd89548427c6255210cf55054842de6315210b758c54842ee6215210bb588548433e64152109f98c548435e63152109798c548427d6315210d758c548425d63152109f988548436e62152109b988548427d6215210db588548426d6215210dd584548437a60152109f993538427d64d4e109f98b538427d62d4e10dd587538437a60d4e10d7d4e538427e6494e109f592538427e6294e109f58a53842bf6454e10af191538427f6454e10cfd91538423f6454e109f191538433c6454e108f191538435f6354e109fd89538427c6254e10af99053842bd6414e10d754c53842ee6214e10bb588538427e6414e10cf990538423e6414e109f590538433d6414e108f590538435e6314e109f988538436e6214e109b988538427d6214e10db588538426d6214e10dd584538437a6014e109fd97438427e65d0e109f597438427c65d0e10cf953438433d54d0e10d7d4f438435c53d0e109fd96438427e6590e109f596438427c6590e10cfd52438433c5490e10d794e438435d5390e109fd95438427e6550e109f595438427c6550e10cf951438433d5450e10d794d438435d5350e109fd94438427e6510e109f594438427c6510e10cfd50438433c5410e10d7d4c438435c5310e10e750c43842fa6010e10be580438427e64d4a109f593528427e63d4a109f58f528437561d4a10de983528436f5294a109f992528427d6494a109f98e528427d6394a10de982528427f6454a109f191528427f6354a109f18d528436f6254a10af99052842bd6414a10b798c52842dd6314a10db548528427e6414a10cf990528423e6414a109f590528433d6414a108f590528427e6314a10d798c528425e6314a109f58c528435d6314a109758c528436e6214a10dd584528437a6014a109fd97428427e65d0a109f597428427c65d0a10cf953428433d54d0a109fd96428427e6590a109f596428427c6590a10b798e42842dd6390a10db94a428436d5290a10be98242842f96090a109fd95428427e6550a109f5954284
  | 8 => 0x10af99052c42bd6414b10b798c52c42dd6314b10db54852c427e6414b10cf99052c423e6414b109f59052c433d6414b108f59052c427e6314b10d798c52c425e6314b109f58c52c435d6314b109758c52c436e6214b10dd98452c43796014b109fd9742c427e65d0b109f59742c427c65d0b10cf95342c433d54d0b10bd98742c42f561d0b109fd9642c427e6590b109f59642c427c6590b10b798e42c42dd6390b10bd98642c42f56190b109fd9542c427e6550b109f59542c427c6550b10cf95142c433d5450b109fd9442c427e6510b109f59442c427c6510b10bd98442c42f56110b109fd9732c427e65ccb109f59732c427c65ccb10d794f32c435d53ccb10bd98732c42f561ccb109fd9632c427e658cb109f59632c427c658cb10af99232c42bd648cb10bd98632c42f5618cb109fd9532c427e654cb109f59532c427c654cb10d794d32c435d534cb109fd9432c427e650cb109f59432c427c650cb10bd98432c42f5610cb10cfd5341c433c54d0710cf95241c433d5490710b798e41c42dd6390710be98241c42f96090710dd59641c43765490710ed95241c43b55490710dd15241c43d66390710bd58e41c43d56390710b558e41c42f56290710bd98241c43f26090710fc58241c433f5450710cf15141c42f76550710ddd9541c43b76450710edd5141c43765450710dd15141c43b45450710bdd8d41c43b64350710ed10d41c42f76250710edd0941c43b54250710bd18141c433e5410710cf55041c43b54110710be98041c42f96010710d7d4f31c435c53cc710af99231c42bd648c710d794e31c435d538c710be98231c42f9608c710dd59631c42f7648c710ed99231c42f5648c710ed59231c42b5648c710dd94e31c43d6538c710f554e31c4374538c710bd58a31c42f6608c710fc98231c43f1608c710d7d4d31c435c534c710bdd9531c4377654c710bdd9131c42f5644c710f5d8d31c43d7534c710dd94d31c4374534c710f514d31c43d7434c710f510d31c42f7624c710f5cc931c43d5324c710bd18131c435e530c710d754c31c43d5310c710be98031c42f9600c710dbd4b21c436c52c8710db94a21c436d5288710be98221c42f96088710dd59621c42f76488710bd59221c42f76388710bd58e21c43765288710f994a21c43e55288710dd14a21c42f66088710fc98221c43f16088710dbd4921c436c5248710bdd9521c43776548710bdd9121c42f56448710bdd8d21c42f56348710f9d8921c43e75248710dd94921c43745248710f914921c43645248710bd18121c42be6408710af59021c42de6308710b758c21c436e5208710db54821c43e52108710be98021c42f96008710cf95340c433d54d0310bd98740c42f561d0310ed50740c433e5450310cf55140c42df6350310b718d40c42f76150310bd18540c43b54
  | 9 => 0xd9130082bc644c020cf951300833d544c020d794d300835d534c020dd9453008375514c0209fd94300827e650c0209f594300827c650c020af99030082bd640c020cf950300833d540c020d794c300835d530c020bb98830082ed620c020bd98430082f5610c020dd9443008375510c020cf953200833d54c8020d794f200835d53c8020dd947200837551c8020dbd5320083ae54c8020db55320083ad54c8020cb553200836f53c8020f394f200836d53c8020f354f200834d53c8020f9947200836d51c8020f9547200836551c8020cf952200833d5488020d794e200835d5388020bb58a200836e5288020dd94620083755188020ee95220083b95488020f694e20083d95388020be58a200837a5288020fa94a20083f25188020de54620083f15188020dc546200827f6548020cf951200833d5448020d794d200835d5348020dd94520083755148020bbd95200836f65480209bd95200836f5448020eb951200836d5448020eb551200832d5448020dbd4d20083ce5348020db54d20083cd5348020d354d20083e65148020db54520083e55148020d954520082ef6048020db94120082fb6548020ded95200827b6548020ee95120083b95448020f694d20083d95348020bed8920083eb6248020de94920083ea5248020fc94520083795148020fc54520083715148020fac8520083e92148020b798f54c42dd63d53109f98f54c435e63d53109798f54c427d63d5310d758f54c425d63d53109f98b54c427d62d5310dd98754c437960d5310cfd5254c427e63953109f58e54c427e62953109f58a54c43766195310cfd9154c427f63553109f18d54c427f62553109f18954c433d5415310cf99054c427e63153109f58c54c427e62153109f58854c43766115310de58054c42be64d4f10af59353c427e64d4f10cf99353c423e64d4f109f59353c433d64d4f108f59353c427e62d4f109f58b53c437661d4f10de58353c435f5394f109f99253c427d6494f109f98a53c427d6294f10dd98653c427f6454f109f19153c435f6354f109fd8953c427c6254f10d754c53c427e6414f109f59053c435e6314f109f98853c427d6214f10dd98453c43796014f109fd9743c427e65d0f109f59743c427c65d0f10d794f43c435d53d0f10bd98743c42f561d0f109fd9643c427e6590f109f59643c427c6590f10cf95243c433d5490f10bd98643c42f56190f109fd9543c427e6550f109f59543c427c6550f109fd9443c427e6510f109f59443c427c6510f10cf95043c433d5410f10d794c43c435d5310f10e750c43c42f66110f10bd58443c427e64d4b109f59352c427e63d4b109f58f52c437661d4b10de58352c436f5294b109f99252c427d6494b109f98e52c427d6394b10dd98652c427f6454b109f19152c427f6354b109f18d52c436f6254b
  | 10 => 0x1083555354420dd14d51083776454420dd99151083756454420dd19151083776354420dd98d51083756354420dd18d51083774354420dd90d51083754354420dd10d51083766254420ddd0951083764254420dd50951083744254420ddcc951083763254420dd4c951083743254420dd98151083746054420dd08151082be6414420af590510833e5414420cf55051082de6314420b758c510835e5314420d754c51082f66114420dd544510827f65d04209f997410827d65d0420cf953410833d54d0420d794f410835d53d0420dd947410837551d04209fd96410827e65904209f596410833e5490420cf55241082de6390420b758e410835e5390420d754e41083765190420dd546410827f65504209f595410827c6550420cf951410833d5450420d794d410835d5350420bbd8941082ec6250420dd945410837551504209fd94410827e65104209f594410833e5410420cf550410835e5310420d754c41083765110420dd544410827f65cc4209f997310827d65cc420cf953310833d54cc420d794f310835d53cc420dd947310837551cc4209fd96310827e658c4209f59631082be648c420af592310833e548c420cf552310835e538c420d754e3108376518c420dd546310827f654c4209f595310827c654c420cf951310833d544c420d794d310835d534c420bbd8931082ec624c420dd9453108375514c4209fd94310827e650c4209f594310833e540c420cf550310835e530c420d754c3108376510c420dd544310833e54c8420cf553210835e53c8420d754f210836e52c8420dd947210837551c8420be98321082f960c84209f596210833e5488420cf552210835e5388420d754e210837551884209fd95210833e5448420cf551210835e5348420d754d210836e5248420dd94521082be6408420af590210833e5408420cf55021082de6308420b758c210835e5308420d754c21083765108420dd54421083e52108420be98021082f960084209f992500827d64940209f98e500827d63940209f597400833e54d0020cf553400835e53d0020d754f400837651d0020dd547400827f65900209f596400833e5490020cf552400835e5390020d754e40082ee6290020bb58a40083765190020dd546400827f6550020cf951400833d5450020b7d8d40082dc6350020d794d400835d5350020dd945400837551500209fd94400827e65100209f594400827c6510020cf950400833d5410020b798c40082dd6310020d794c400835d5310020bb98840082ed6210020bd98440082f56110020dd944400837551100209f597300833e54cc020cf553300835e53cc020d754f300837651cc020dd547300827f658c0209f596300833e548c020cf552300835e538c020d754e30082ee628c020bb58a3008376518c020dd546300827f654c020af
  | 11 => 0x5e6454c20d7591530835c6454c20d7989530835c6254c20d7d85530835e6154c20d7585530835c6154c20d7981530835c6054c20d708153082be6414c20af590530833e5414c20cf55053082de6314c20d754c53082f66114c20bd584530827e6414c20cf990530823e6414c209f590530833d6414c208f590530827e6314c20d798c530825e6314c209f988530836e6214c209b988530827e6114c20dd98453082766114c209f58453083756114c209d584530827e6014c20de980530827f65d0c209f997430827d65d0c209f197430833e54d0c20cf553430835e53d0c20d754f430827f6590c209f996430827d6590c209f196430833e5490c20cf552430835e5390c20d754e430827f6550c209f995430827d6550c209f195430833e5450c20cf551430835e5350c20d754d430827f6510c209f994430827d6510c209f194430833e5410c20cf550430835e5310c20d754c430839d4310c209f992520827d64948209f98e520827d63948209f597420833e54d0820cf553420835e53d0820d754f420827f65908209f596420833e5490820cf55242082de6390820b758e420835e5390820d754e420836e5290820be98242082f960908209fd95420833e5450820cf551420835e5350820d754d420836e52508209fd94420827d6510820cf950420833d5410820d794c420835d5310820be98042082f960108209f597320833e54cc820cf553320835e53cc820d754f320827f658c8209f59632082be648c820af592320833e548c820cf552320835e538c820d754e320836e528c820be98232082f9608c8209fd95320833e544c820cf551320835e534c820d754d320836e524c8209fd94320827d650c820cf950320833d540c820d794c320835d530c820be98032082f9600c820af99351082bd64d4420cf953510833d54d4420b798f51082dd63d4420d794f510835d53d4420cf952510833d5494420d794e510835d5394420ddd46510827e64944209f592510827e63944209f58e51083775494420dd95251083b65494420cd95251083755494420ed55251083355494420dd15251083775394420dd94e51083d65394420d594e51083755394420f554e51083555394420dd14e51083776494420dd99251083756494420dd19251083776394420dd98e51083756394420dd18e51083774394420dd90e51083754394420dd10e51083746294420ddd0a51083764294420dd50a51083744294420ddcca51083763294420dd4ca51083743294420dd98251083746094420cf951510833d5454420d794d510835d53544209fd91510827c64544209fd8d510827c6354420ddd9551083775454420dd95151083b65454420cd95151083755454420ed55151083355454420dd15151083775354420dd94d51083d65354420d594d51083755354420f554d5
  | 12 => 0xd0120cf15340482ee62d0120bb58b40483ad42d01209f996404827f65501209f595404827c6550120cfd51404833c5450120b7d8d40482dc6350120bbd8940482ec6250120eb509404827e6510120b798c40482dd6310120bb98840482ed6210120bd98440482f561101209f997304835f53cc120d714f30482ee62cc120bb58b30483cd32cc1209f996304827f654c1209f595304827c654c120afd9130482bc644c120d7d4d304835c534c120bbd8930482ec624c120f34c9304827e650c120af99030482bd640c120bb98830482ed620c120bd98430482f5610c120fa90b20483e942c8120fa8cb20483e932c8120be58720483eb21c8120fa48720482ef6488120bb59220482ef6388120bb58e20482ed6188120fad4220482de63d5020b758f54082f661d5020bd587540827e63d5020d798f540825e63d50209f58f540835d63d50209758f540827e62d5020db98b540827e61d5020dd987540827661d50209f587540837561d50209d587540827e60d5020de983540827d6595020cfd52540827e63950209f58e540827e61950209f586540823d6595020cfd8e540833e6395020cf58e540833c6395020cf98a540833c6295020cfd86540833e6195020cf586540833c6195020cf982540833c6095020cfd91540827f63550209f18d540827f62550209f589540827f61550209f185540833f6555020cfd8d540833e6355020cf58d540833c6355020cf989540833c6255020cfd85540833e6155020cf585540833c6155020cf981540833c6055020cf08154082be6415020cf55054082de6315020b758c54082f66115020bd584540827e6415020cf990540823e64150209f98c540835e63150209798c540827d6315020d758c540825d63150209f988540836e62150209b988540827e6115020dd984540827661150209f584540837561150209d584540827e6015020de98054082be64d4c20af593530833e54d4c20cf55353082f661d4c20bd587530827e64d4c20cf993530823e64d4c209f593530833d64d4c208f593530827e62d4c20db98b530827e61d4c20dd987530827661d4c209f587530837561d4c209d587530827e60d4c20de983530827d6594c20cf952530833d5494c20d7d4e530827e6494c209f592530827e6194c209f586530825d6594c20d7d52530835e5494c20e7952530831e5494c20d7552530839d5494c20c7552530835c5494c20d7d92530835e6494c20d7592530835c6494c20d798a530835c6294c20d7d86530835e6194c20d7586530835c6194c20d7982530835c6094c20cf951530833d5454c209fd91530827c6454c20d7d8d530827f6254c209f589530827f6154c209f185530835f6554c20d7d51530835e5454c20e7951530831e5454c20d7551530839d5454c20c7551530835c5454c20d7d9153083
  | 13 => 0xf398e42482ed6390920f358e42482cd6390920bb58642482ee60909209f195424833f5450920cf15142482fb6050920be181424836c65509209b19542483af6450920ebd51424836e5450920db15142483ac5450920bbd8d42483ae4350920eb10d42482ef6150920fad8142482ec6050920fa181424827e6510920bb98842483ad42109209f997324835f53cc920d714f32482fa60cc920be583324827e658c920af99232482bd648c920bb996324836e658c920bbd9232483ae648c920bb59232483ad648c920ab59232482ed638c920db94e324836c538c920bb58632482ee608c9209f195324835f534c920d714d32482fb604c920be181324836c654c9209b19532482ef644c920bb59132483cf634c920f3d4d324836e534c920db14d32483cc534c920f3d0d32483cc434c920bbd8532483eb604c920bb18132483e8604c9209f99432482ee620c920f34c8324827e64d45209f593514827e63d45209f58f51483775194520afd9151482bc6454520b7d8d51482dc6354520af99051482bd6414520b798c51482dd6314520dd544514827e6414520cf990514823e64145209f590514833d64145208f590514827e6314520d798c514825e63145209f58c514835d63145209758c514837960145209f997414827d65d05209f197414833e54d0520cf55341482ee62d0520bb58b41483ad42d0520ddd47414837451d05209f996414827d65905209f196414833f5490520cf15241482de6390520b758e41482ee6290520bb58a41482fa6090520be582414827f65505209f995414827c6550520cf951414833d5450520eb509414827e65105209f594414827c6510520cfd50414833c5410520bb98841482ed6210520ddd4441483745110520be98041482f960105209f997314827d65cc5209f197314835e53cc520d754f31482ee62cc520bb58b31483cd32cc520ddd47314837451cc5209f996314827d658c5209f19631482be648c520af592314835f538c520d714e31482ee628c520bb58a31482fa608c520be582314827f654c5209f995314827c654c520d794d314835d534c520f34c9314827e650c5209f594314827c650c520d7d4c314835c530c520bb98831482ed620c520ddd443148374510c520be98031482f9600c5209f99721482ee65c8520db99721482ef64c8520bb59321482ef63c8520bb58f214836c51c8520fad8321482ee60c8520fa18321482ed6288520ddd4621483745188520be98221482f96088520ddd4521483745148520bed8121482f86048520bbd9121482ed6448520bbd8d21482ed6348520f9d8521483e75148520db14521483e45148520d914521483eb6048520bb18121483e860485209f99421482be6408520af59021482de6308520b758c21482ee6208520f948421482fa60085209f997404833f54
  | 14 => 0x9231882bd648c620dd9463188375518c620be98231882f9608c6209fd95318827d654c6209f195318835e534c620d754d31882ef624c620bb1893188376514c620dd545318827f650c6209f994318827d650c620be98031882f9600c620dd94621883755188620be98221882f96088620dd94521883755148620bed8121882f86048620af99021882bd6408620b798c21882dd6308620f948421882f96008620cfd53408833c54d0220cf952408833d5490220bb98a40882ed6290220cfd51408833c5450220b7d8d40882dc6350220cf950408833d5410220b798c40882dd6310220bb98840882ed6210220bd98440882f56110220d7d4f308835c53cc220d794e308835d538c220bb98a30882ed628c220afd9130882bc644c220d7d4d308835c534c220af99030882bd640c220d794c308835d530c220bb98830882ed620c220bd98430882f5610c220bb597208836d65c8220dbd53208836d54c8220dbd4f208836d53c8220db54720882f965c8220de59720882f961c82209f98f544827d63d51209f987544827d61d5120cfd52544827e64951209f98e544827d63951209f58a544836d62951209f986544827d61951209f58254483796095120b7d8d54482dc6355120bdd8554482f46155120cfd91544827f6355120d7d8d544825f63551209f18d544835c63551209718d544827f6255120dbd89544827f6155120ddd85544827761551209f185544837461551209d185544827f6055120ded81544827e6515120cf550544833e64151209f98c544827d63151209f988544836d62151209f188544827e61151209f584544827e64d4d209f593534827e61d4d209f587534835f5394d209f992534827d6494d209f98e534827d6294d20db58a534827e6194d209f586534827d6094d20de58253482bf6454d20af19153482f76154d20bd185534827f6454d20cfd91534823f6454d209f191534833c6454d208f191534835f6354d209fd89534836f6254d209fd8553483776154d209dd85534827c6154d20dd18553482746154d209fd81534837b6054d209f994534835d5314d209f990534827d6414d20d798c534827e6214d20db588534827c6214d209f984534827d6114d209fd97434827e65d0d209f597434827c65d0d20d7d4f434835c53d0d20bb98b43482ed62d0d209fd96434827e6590d209f596434827c6590d20cfd52434833c5490d20bb98a43482ed6290d209fd95434827e6550d209f595434827c6550d209fd94434827e6510d209f594434827c6510d20cfd50434833c5410d20d7d4c434835c5310d20e750c43482ee6210d20bb58843482fa6010d20be580434827e65d0920cfd53424833c54d0920be98342482f960d09209f99642482de6390920b758e42482ee6590920db99642482ed6490920db952424836c549092
  | 15 => 0xc83ad4250320b798c40c82dd6310320bb98840c82ed6210320bd98440c82f56110320d794f30c835d53cc320bb98b30c82ed62cc320f34cb30c82bf644c320af19130c835e534c320d754d30c82ef624c320bb18930c83cd324c320af99030c82bd640c320bb98830c82ed620c320bd98430c82f5610c3209f98f548827d63d5220db58b548827e61d52209f587548837a60d5220cfd52548827e63952209f58e548827e61952209f58654882df6355220b718d548833f64552209fd8d548835f635522097d8d548827c6355220d718d548825c63552209fd85548827c6155220cf55054882de6315220b758c54882f66115220bd584548833e64152209f98c548835e63152209798c548827d6315220d758c548825d6315220db588548827e6115220dd984548827661152209f584548837561152209d584548837a60152209f993538827d64d4e20db58b538827e61d4e209f587538837a60d4e20d7d4e538827e6494e209f592538827e6194e209f58653882bf6454e20af191538827f6454e20cfd91538823f6454e209f191538833c6454e208f191538835f6354e209fd85538827c6154e20af99053882bd6414e20d754c53882f66114e20bd584538827e6414e20cf990538823e6414e209f590538833d6414e208f590538835e6314e20db588538827e6114e20dd98453882766114e209f58453883756114e209d584538837a6014e209fd97438827e65d0e209f597438827c65d0e20cf953438833d54d0e20d7d4f438835c53d0e209fd96438827e6590e209f596438827c6590e20cfd52438833c5490e20d794e438835d5390e209fd95438827e6550e209f595438827c6550e20cf951438833d5450e20d794d438835d5350e209fd94438827e6510e209f594438827c6510e20cfd50438833c5410e20d7d4c438835c5310e20e750c43882fa6010e20be580438833e54d0a20cf55342882fa60d0a20be58342882de6390a20b758e428833e5450a20cf55142882fb6050a20be181428835e53cca20d754f32882fa60cca20be58332882be648ca20af592328835e534ca20d754d32882fb604ca20be181328837751946209f992518827d64946209f98e518827d6394620de982518827f64546209f191518827f63546209f18d51882be6414620af59051882de6314620b758c518837551146209fd97418827e65d06209f597418833e54d0620cf553418827f65906209f996418827d6590620b798e41882dd6390620dd94641883755190620be98241882f960906209fd95418827d65506209f195418833e5450620cf55141882ef6250620bb18941883765150620dd545418827f65106209f994418827d6510620be98041882f960106209fd97318827e65cc6209f597318835e53cc620d754f318827f658c6209f996318827d658c620af9
  | 16 => 0xf6590f209f99643c827d6590f209f19643c833e5490f20cf55243c82ee6290f20bb58a43c827f6550f209f99543c827d6550f209f19543c827f6510f209f99443c827d6510f209f19443c833e5410f20cf55043c835e5310f20d754c43c839d4310f20bb98843c82ed6210f20cfd5342c833c54d0b20cf95242c833d5490b20b798e42c82dd6390b20be98242c82f96090b20db59642c836e5490b20eb95242c83ad5490b20db15242c83ce6390b20bb58e42c83cd6390b20b358e42c82ed6190b20bb98242c83ea6090b20fa58242c833f5450b20cf15142c82ef6550b20dbd9542c83af6450b20ebd5142c836e5450b20db15142c83ac5450b20bbd8d42c83ae4350b20eb10d42c82ef6150b20bb18142c833e5410b20cf55042c83ad4210b20be98042c82f96010b20d7d4f32c835c53ccb20af99232c82bd648cb20d794e32c835d538cb20be98232c82f9608cb20db59632c82ef648cb20eb99232c82ed648cb20eb59232c82ad648cb20db94e32c83ce538cb20f354e32c836c538cb20bb58632c82ee608cb20fa98232c83e9608cb20d7d4d32c835c534cb20bbd9532c836f654cb20bbd9132c82ed644cb20f3d8d32c83cf534cb20db94d32c836c534cb20f314d32c83cf434cb20f310d32c82ef614cb20bb18132c835e530cb20d754c32c83cd320cb20be98032c82f9600cb20ddd4651c827e64947209f59251c827e63947209f58e51c827f64547209f19151c827f63547209f18d51c82be6414720af59051c82de6314720b758c51c837551147209fd9741c827e65d07209f59741c833e54d0720cf55341c82ee62d0720bb58b41c83ad42d07209fd9641c827e65907209f59641c82de6390720b758e41c82ee6290720bb58a41c827f65507209f59541c827c6550720cf95141c833d5450720eb50941c827f65107209f99441c827d6510720bb98841c82ed62107209fd9731c827e65cc7209f59731c835e53cc720d754f31c82ee62cc720bb58b31c83cd32cc7209fd9631c827e658c7209f59631c82be648c720af59231c82ee628c720bb58a31c827f654c7209f59531c827c654c720d794d31c835d534c720f34c931c827f650c7209f99431c827d650c720bb98831c82ed620c720dd94721c837551c8720be98321c82f960c8720bbd9321c82ed64c8720bbd8f21c82ed63c8720db94721c83e651c8720f954721c82ee60c8720fa98321c83e960c8720bbd9521c836f6548720bbd9121c82ed6448720bbd8d21c82ed6348720f9d8521c83e75148720db94521c83e45148720bb18121c82be6408720af59021c82de6308720b758c21c83765108720dd54421c83e52108720be98021c82f96008720cf95340c833d54d0320bb98b40c82ed62d0320eb50b40c833e5450320cf55140c82df6350320b718d40c82ef6250320bb18940
  | 17 => 0x8430b758c210c36e5208430db548210c3765108430dd544210c3e52108430be980210c2f960084309f992500c27d6494030d7d0e500c35c43940309f597400c33e54d0030cf553400c39f43d0030db94b400c36d52d0030dd947400c37551d00309fd96400c27d6590030cf952400c33d5490030b798e400c2dd6390030e710e400c36e5290030db54a400c3765190030dd546400c27f6550030cf951400c33d5450030b7d8d400c2dc6350030e7d0d400c36e5250030db549400c3765150030dd545400c27f65100309f994400c27d65100309f194400c33e5410030cf550400c2de6310030b758c400c39c4310030bb988400c2ed6210030db948400c36d5210030bd984400c2f56110030dd944400c3755110030cf953300c33d54cc030db94b300c36d52cc030dd947300c37551cc030b7993300c2dc64cc030d7d53300c39e54cc030d7553300c39d54cc030c7553300c3ce52cc030d754b300c3cd52cc030d354b300c3d651cc030d7547300c3d551cc030d5547300c33e548c030cf552300c2dd638c030d794e300c36e528c030db54a300c376518c030dd546300c3ba548c030ee552300c2f9638c030de94e300c3da538c030f6d0e300c3d8438c030fa94a300c3e9528c030fc946300c3f1518c0309fd95300c2bf644c030af191300c33e544c030cf551300c36e524c030db549300c376514c030dd545300c2df654c030d7d95300c25f654c030e7d91300c2de644c030b7191300c39c644c030a7191300c35f544c030e7951300c35d544c030e7551300c31d544c030f3949300c35d524c030f3549300c34d524c030f5945300c35d514c030f5545300c355514c030b7d81300c35e504c030bed95300c37b654c0309ed95300c3bb644c030ee191300c3ba544c030ee551300c2fb634c030f6d8d300c37a534c030f694d300c3ea524c030fa549300c3f2514c030fc545300c2de63d5320b758f54c827e63d5320d798f54c825e63d53209f58f54c835d63d53209758f54c836e62d53209f98754c827d61d5320de58354c833f54953209f98e54c827d6395320db98a54c827e61953209f58654c833f64553209fd8d54c827c63553209fd8554c827c6155320cf55054c833e64153209f98c54c827d6315320db98854c827e61153209f58454c83796015320af99353c82bd64d4f209f99353c833e64d4f208f99353c827d64d4f20cf59353c823d64d4f20db98b53c827e61d4f209f58753c837960d4f20d7d4e53c827e6494f209f59253c836e6294f209f98653c827d6194f209fd9153c827c6454f20d7d8d53c827f6154f209f18553c835d5314f209f99053c827d6414f20d798c53c836e6214f209f98453c827d6114f20de58053c827f65d0f209f99743c827d65d0f209f19743c835e53d0f20d754f43c82ee62d0f20bb58b43c827
  | 18 => 0xdd952510c3b65494430cd952510c3755494430ed552510c3355494430dd152510c3d74394430f510e510c3775294430dd94a510c3e65294430d994a510c3755294430f954a510c3655294430dd14a510c3776494430dd992510c3756494430dd192510c3746394430ddd0e510c3764394430dd50e510c3744394430ddd8a510c3766294430dd58a510c3746294430ddd0a510c3764294430dd50a510c3744294430ddcca510c3763294430dd4ca510c3743294430dd982510c3746094430cf951510c33d5454430db949510c36d52544309fd91510c27c6454430d7d0d510c35c43544309fd89510c27c6254430ddd95510c3775454430dd951510c3b65454430cd951510c3755454430ed551510c3355454430dd151510c3d74354430f510d510c3775254430dd949510c3e65254430d9949510c3755254430f9549510c3655254430dd149510c3776454430dd991510c3756454430dd191510c3766354430ddd0d510c3574354430dd90d510c3754354430dd10d510c3544354430ddd89510c3766254430dd589510c3746254430ddd09510c3764254430dd509510c3744254430ddcc9510c3763254430dd4c9510c3743254430dd981510c3746054430dd0c1510c2be6414430af590510c33e5414430cf550510c2ee6214430bb588510c36e5214430db548510c2f66114430dd544510c27f65d04309f997410c27d65d0430cf953410c33d54d0430e710f410c36e52d0430db54b410c37651d0430dd547410c27f65904309f996410c27d6590430cf952410c33d5490430b798e410c2dd6390430db94a410c36d5290430dd946410c37551904309fd95410c27d65504309f195410c33e5450430cf551410c2df6350430b718d410c39c4350430db949410c36d5250430dd945410c37551504309fd94410c27e65104309f594410c33e5410430cf550410c36e5210430db548410c3765110430dd544410c33e54cc430cf553310c35e53cc430db94b310c36d52cc430dd947310c37551cc430be983310c2f960cc4309f596310c2be648c430af592310c33e548c430cf552310c36e528c430db54a310c375518c4309fd95310c33e544c430cf551310c35e534c430db949310c36d524c430dd945310c33e540c430cf550310c36e520c430db548310c376510c430dd544310c2fa600c430be580310c27f65c84309f997210c27d65c8430cf953210c33d54c8430db94b210c36d52c8430dd947210c37551c84309fd96210c27e65884309f596210c33e5488430cf552210c36e5288430db54a210c3765188430dd546210c27f65484309f595210c27c6548430cf951210c33d5448430b7d8d210c2dc6348430db949210c36d5248430dd945210c37551484309fd94210c27e65084309f594210c2be6408430af590210c33e5408430cf550210c2de630
  | 19 => 0x8540c27d6215030db588540c26d62150309f984540c37661150309d984540c27d6115030dd584540c27561150309f980540c37a60150309f992530c27d6494c309f597430c33e54d0c30cf553430c2dd65d0c30d7597430c25d65d0c30d7d53430c39e54d0c30d7553430c39d54d0c30c7553430c2dd60d0c309fd96430c27d6590c30cf952430c33d5490c30b798e430c35e5390c30be982430c2f96090c309fd95430c33e5450c30cf551430c35e5350c309fd94430c27d6510c30cf950430c33d5410c30e750c430c2fa6010c30be580430c35d6510c3097594430c2de6410c30e7990430c35f5410c30e7950430c35d5410c30e7550430c31d5410c30f6980430c2dd6010c30f6580430c2be64d4830af593520c33e54d4830cf553520c2f661d4830bd587520c33e5494830cf552520c36f52948309f992520c27d64948309f986520c27d6194830dbd52520c36e5494830eb952520c32e5494830db552520c3ad5494830cb552520c36c5494830f3d0e520c3cc4394830dbd92520c36e6494830db592520c36c6494830db18e520c36f4394830db90e520c36d4394830db10e520c36f6194830db986520c36d6194830db186520c36e6094830db182520c33e5454830cf551520c27f64548309f191520c35f4354830d710d520c27f61548309f185520c36f6554830dbd51520c36e5454830eb951520c32e5454830db551520c3ad5454830cb551520c36c5454830f3d0d520c3cc4354830dbd91520c36e6454830db591520c36c6454830db98d520c36f4354830d3d0d520c36e4354830db50d520c36c4354830d310d520c36f6154830db985520c36d6154830db185520c36e6054830db181520c36c3054830af990520c2bd6414830cf950520c33d5414830bb988520c36d5214830bd984520c2f561148309fd97420c27e65d08309f597420c33e54d0830cf553420c39c43d0830db94b420c36d52d08309fd96420c27e65908309f596420c33e5490830cf552420c2de6390830b758e420c36e5290830db54a420c27f65508309f595420c27c6550830cf951420c33d5450830b7d8d420c2dc6350830e710d420c36e5250830db549420c27f65108309f994420c27d6510830cf950420c33d5410830db948420c36d5210830cf953320c33d54cc830d794f320c36e52cc830db54b320c2fa60cc830be583320c27d658c830af992320c2bd648c830cf952320c33d548c830db54a320c27f654c830cf951320c33d544c830d794d320c36e524c830cf950320c33d540c830db948320c36d520c830be980320c2f9600c830af993510c2bd64d4430cf953510c33d54d4430bb98b510c2ed62d4430db94b510c36d52d4430cf952510c33d5494430db94a510c36d5294430ddd46510c27e64944309f592510c27e62944309f58a510c3775494430
  | 20 => 0xc2dd64cc530e7d53314c35e54cc530d7153314c39c54cc530c7153314c2dd62cc530d7d4b314c35c51cc530b7983314c2be648c530af592314c33f548c530cf152314c2dd638c530ddd46314c374518c530be982314c2f9608c530cfd51314c33c544c530ddd45314c374514c530bed81314c2f8604c530b7d91314c2dd644c530e7d51314c35e544c530d7151314c39c544c530c7151314c2df624c530d7d49314c3d7614c530f5d45314c35c514c530f5145314c3db604c530b7181314c3d8604c5309f994314c33f540c530cf150314c2de630c530f54c4314c27e65c85309f597214c27c65c8530cfd53214c33c54c8530b798f214c2dd63c8530ddd47214c37451c85309f996214c27d65885309f196214c33f5488530cf152214c2de6388530b758e214c36f5288530db14a214c27f65485309f995214c27c6548530cfd51214c33c5448530b798d214c2dd63485309f994214c27d65085309f194214c2be6408530af590214c33f5408530cf150214c2de6308530b758c214c36f5208530db148214c3775108530dd144214c3e52108530be980214c2f960085309f997404c33f54d0130cf153404c2de63d0130b758f404c39d43d01309f996404c33f5490130cf152404c39e43901309fd95404c27d65501309f195404c33f5450130cf151404c2df6350130b718d404c39d43501309f994404c33f5410130cf150404c2de6310130b758c404c39e4310130bb988404c2ed6210130bd984404c2f56110130cfd53304c33c54cc130eed53304c3b854cc130f690f304c3d943cc130f6ccb304c3d932cc130f6cc7304c3d931cc130cfd52304c33c548c130b7d92304c2dd648c130e7d52304c35e548c130d7152304c39c548c130c7152304c2dd628c130b7586304c3db508c130bb98b540c2ed62d5030bd987540c2f561d50309f98f540c35e63d50309f98b540c36e62d50309b98b540c27d62d5030db58b540c26d62d50309f987540c37661d50309d987540c27d61d5030dd587540c27561d50309f983540c37a60d50309f596540c33f54950309f98a540c27d62950309f986540c27d61950308f596540c39c6395030cf98e540c33c6395030cfd8a540c33e6295030cf58a540c33c6295030cfd86540c33e6195030cf586540c33c6195030cf982540c33c6095030cfd91540c27f63550309f58d540c35c63550309fd89540c27c62550309fd85540c27c6155030cfd95540c39c6355030cf98d540c33c6355030c718d540c33f6255030cf989540c33d6255030cf189540c33f6155030cf985540c33d6155030cf185540c33e6055030cf181540c33c3055030af990540c33d5415030bb988540c2ed6215030bd984540c2f561150309f990540c33e64150308f990540c27e6315030d798c540c25e63150309f988540c36e62150309b98
  | 21 => 0x6115130cf984544c33d6115130cf184544c33f6015130cf580544c33d30151309f997434c33f54d0d30cf153434c2fa60d0d30be583434c27e6590d30cfd52434c33c5490d30b7996434c35e6590d3097996434c2dd6490d30e7d52434c35e5490d30d7152434c39c5490d30c7152434c2dd6290d30b7586434c2de6090d309f195434c33f5450d30cf151434c2fb6050d30be181434c35c6550d3097195434c39f6450d30e7d51434c35e5450d30d7151434c39c5450d30c7151434c2df6250d30b7d85434c3db6050d30b7181434c3d86050d309f994434c33f5410d30cf150434c2de6310d30e750c434c33f54d4930cf153524c27e64d49309f593524c27e61d49309f587524c2be6494930af592524c33f5494930cf152524c36f5294930afd91524c2bc6454930cfd51524c33c5454930bdd85524c2f46154930cfd50524c33c5414930db548524c27e64149309f590524c27e61149309f584524c27e65d09309f597424c27c65d0930cfd53424c33c54d0930b798f424c2dd63d0930e790f424c27e65909309f596424c27c6590930cfd52424c33c5490930b798e424c2dd63909309fd95424c27e65509309f195424c33f5450930cf151424c39e43509309f994424c27d65109309f194424c33f5410930cf150424c2de6310930b758c424c2fa6010930be580424c27e65cc930cfd53324c33c54cc930b7997324c35e65cc930b7d93324c2dd64cc930e7d53324c35e54cc930d7153324c39c54cc930c7153324c35c52cc930b7587324c2de60cc930af992324c2bd648c930cfd52324c33c548c930b758e324c36f528c930db14a324c2fa608c930be582324c33f544c930cf151324c36f524c930db149324c2fb604c930be181324c2df644c930b7591324c39f544c930d7951324c35c544c930e7151324c31c544c930f3d89324c3cf524c930d7149324c3cc524c930b7d85324c3db604c930b7181324c3d8604c9309f994324c33f540c930cf150324c2de630c930f34c8324c33f54d4530cf153514c27e64d45309f593514c27e62d45309f58b514c35f32d4530d74cb514c2be6494530af592514c33f5494530cf152514c3775194530afd91514c2bc6454530cfd51514c33c5454530bbd89514c2ec6254530cfd50514c33c5414530dd544514c27e64145309f590514c27e62145309f588514c27e65d05309f597414c27c65d0530cfd53414c33c54d0530b798f414c2dd63d0530e790f414c27e65905309f596414c27c6590530cfd52414c33c5490530b798e414c2dd63905309fd95414c27e65505309f195414c33f5450530cf151414c39e43505309f994414c27d65105309f194414c33f5410530cf150414c2de6310530b758c414c2fa6010530be580414c27e65cc530cfd53314c33c54cc530b7997314c35e65cc530b7d93314
  | 22 => 0xa30db548528c2f66114a30bd584528c27f65d0a309f997428c27d65d0a30cf953428c33d54d0a30e710f428c27f6590a309f996428c27d6590a30b798e428c2dd6390a30db94a428c36d5290a309fd95428c27d6550a309f195428c33e5450a30cf551428c2df6350a30b718d428c39c4350a30db949428c36d5250a309fd94428c27e6510a309f594428c2fa6010a30be580428c2be648ca30af592328c36e528ca30db54a328c2fa608ca30be582328c36e524ca30db549328c2fb604ca30be181328c37751946309f992518c27d64946309f98a518c27d62946309fd91518c27c6454630d7d0d518c35c43546309fd89518c27c6254630af990518c2bd6414630bb988518c2ed6214630dd544518c27f65d06309f997418c27d65d0630cf953418c33d54d0630e710f418c27f65906309f996418c27d6590630b798e418c2dd6390630dd946418c37551906309fd95418c27d65506309f195418c33e5450630cf551418c2df6350630b718d418c39c4350630dd945418c37551506309fd94418c27e65106309f594418c2fa6010630be580418c2be648c630af592318c376518c630dd546318c2fa608c630be582318c376514c630dd545318c2fb604c630be181318c27f65c86309f997218c27d65c8630db94b218c36d52c86309fd96218c27e65886309f596218c3765188630dd546218c27f65486309f595218c27c6548630b7d8d218c2dc6348630db949218c36d5248630dd945218c37551486309fd94218c27e65086309f594218c2be6408630af590218c2de6308630b758c218c3e52108630be980218c2f96008630cfd53408c33c54d0230e7d0f408c33e5490230cf552408c2de6390230b758e408c39c4390230cfd51408c33c5450230b7d8d408c2dc6350230e7d0d408c33e5410230cf550408c2de6310230b758c408c39c4310230bb988408c2ed6210230bd984408c2f56110230b7597308c35d65cc230b7993308c2dc64cc230d7d53308c35d54cc230d754b308c35d51cc230be597308c37965cc2309f98b544c27d62d51309f987544c27d61d5130e7d8f544c33f63d5130cf58f544c33f62d5130cf98b544c33d62d5130cf18b544c33f61d5130cf987544c33d61d5130cf187544c33f60d5130cf583544c33f54951309f992544c23e64951309f58e544c35d63951309f98a544c27d62951309f986544c27d61951309f582544c3796095130cfd91544c27f6355130d7d8d544c25f63551309fd89544c27c62551309fd85544c27c61551309fd81544c37b60551309f994544c33d5415130cf990544c27e6315130d758c544c27c63151309f988544c27d62151309f984544c27d6115130af994544c33e65151308f994544c39d6315130cfd8c544c33d6315130c758c544c33f6215130cf988544c33d6215130cf188544c33f
  | 23 => 0x3d8932cc3cf524cb30d794932cc3cc524cb30b7d8532cc2dc604cb30db94832cc36d520cb30f34c832cc2fa600cb30be58032cc2be6494730af59251cc37751947309f99251cc33e64947308f99251cc27d6494730cf59251cc23d64947309f98a51cc27d62947309fd9151cc27c64547309fd8951cc27c6254730d7cc951cc35d3254730dd54451cc27f65d07309f99741cc27d65d0730cfd5341cc33c54d0730b798f41cc2dd63d0730e790f41cc27f65907309f99641cc27d6590730b798e41cc2dd63907309fd9541cc27d65507309f19541cc33f5450730cf15141cc39e43507309fd9441cc27e65107309f59441cc2de6310730b758c41cc37651cc730dd54731cc2fa60cc730be58331cc2df64cc730b759331cc35e54cc730d715331cc2dd62cc730d754b31cc35e51cc730f594731cc3d551cc730b798331cc3da60cc730f658331cc2be648c730af59231cc2df654c730d7d9531cc2df644c730b759131cc35e544c730d715131cc2df624c730d754931cc3d7614c730f5d4531cc35e514c730f514531cc2dc604c730dd94431cc375510c730f54c431cc2fa600c730be58031cc27f65c87309f99721cc27d65c8730b798f21cc2dd63c87309fd9621cc27e65887309f59621cc2de6388730b758e21cc27f65487309f59521cc27c6548730b798d21cc2dd63487309fd9421cc27e65087309f59421cc2be6408730af59021cc2de6308730b758c21cc3e52108730be98021cc2f96008730cf95340cc33d54d0330b798f40cc2dd63d0330e750f40cc33f5490330cf15240cc39e4390330cf95140cc33d5450330b7d8d40cc2dc6350330e750d40cc33f5410330cf15040cc2de6310330b758c40cc39e4310330bb98840cc2ed6210330bd98440cc2f56110330d758f548c27e62d52309f58b548c27e61d52309f587548c37a60d5230cfd52548c27e62952309f58a548c27e61952309f586548c33f6455230d7d8d548c27f62552309f189548c27f61552309f185548c33d5415230bb988548c2ed6215230bd984548c2f56115230cf990548c35d63152309f988548c36e62152309b988548c27d6215230db588548c26d62152309f984548c37661152309d984548c27d6115230dd584548c2756115230de980548c33e54d0e30cf553438c2fa60d0e30be583438c35d65d0e30d7d53438c39e54d0e30d7553438c39d54d0e30f6983438c2dd60d0e30f6583438c33f5490e30cf152438c33e5450e30cf551438c2fb6050e30be181438c33f5410e30cf150438c39d4310e30b7594438c35d6510e30e7990438c35f5410e30e7d50438c31f5410e30d7550438c39c5410e30b7580438c36f5294a309f992528c27d6494a309f986528c27d6194a309fd91528c27c6454a30d7d0d528c35c4354a309fd85528c27c6154a30af990528c2bd6414
  | 24 => 0x211035d5308440db948211036d5208440dd94421103755108440f948421102fa6008440be580211033e4394040cf10e501035e53d0040d754f401036e52d0040db54b401037651d0040dd54740102be63d0040e794f401033d53d0040e754f401031d53d0040eb94b401033d52d0040eb54b401032d52d0040ed947401033d51d0040ed547401033551d0040af592401033e5490040d794e401035d5390040db94a401036d5290040dd94640103755190040be592401037a5490040ee95240103da5390040f654e40103ba4390040ee10e40103ea5290040fa54a40103f25190040fc546401027f6550040b7d8d40102dc6350040d794d401035d5350040db949401036d5250040dd94540103755150040afd95401033f65500408fd95401039f6350040af18d401039c6350040a718d401039e5350040cf54d401039d5350040c754d40103ae5250040cf54940103ad5250040cb54940103b65150040cf54540103b55150040cd54540102bf6050040cf94140102fb6550040ded95401027b6550040bed9140103bb6450040de95140103ba5450040f6d8d40103d86350040f694d40103d95350040fa94940103e95250040fc94540103f15150040d798f54cc27e62d53309f58b54cc27e61d53309f58754cc37960d5330cfd5254cc35e63953309f98a54cc27d62953309f98654cc27d6195330cfd9154cc27f62553309f18954cc27f61553309f18554cc33d5415330cf99054cc35e63153309f98854cc27d62153309f98454cc27d6115330de58054cc33f54d0f30cf15343cc33e5490f30cf55243cc2fa6090f30be58243cc35d6590f30d795243cc39e5490f30e755243cc35c5490f30b758a43cc2dd6190f30b798243cc3da6090f30f658243cc33f5450f30cf15143cc2df6550f30d7d9543cc39f6450f30e7d5143cc35e5450f30d715143cc39c5450f30c715143cc2df6250f30b7d8543cc2dc6050f30cf95043cc33d5410f30e750c43cc2fa6010f30be58043cc2be6494b30af59252cc36f5294b309f99252cc33e6494b308f99252cc27d6494b30cf59252cc23d6494b309f98652cc27d6194b309fd9152cc27c6454b309fd8552cc27c6154b30db54852cc27f65d0b309f99742cc27d65d0b30cfd5342cc33c54d0b30b798f42cc2dd63d0b30e790f42cc27f6590b309f99642cc27d6590b30b798e42cc2dd6390b309fd9542cc27d6550b309f19542cc33f5450b30cf15142cc39e4350b309fd9442cc27e6510b309f59442cc2de6310b30b758c42cc36e52ccb30db54b32cc2fa60ccb30be58332cc2df64ccb30b759332cc35e54ccb30d715332cc35e52ccb30f394b32cc3cd52ccb30b758732cc2de60ccb30f698332cc3d960ccb30af99232cc2bd648cb30b7d9532cc35f654cb30b7d9132cc2dd644cb30d795132cc35c544cb30f
  | 25 => 0x3765394440f594e51103565394440dd54e51103d55394440d554e51103745394440ed90e51103b44394440ddd4a51103765294440f994a51103665294440dd54a51103e55294440d954a51103745294440dd19251103776394440dd98e51103756394440dd18e51103774394440dd90e51103754394440dd10e51103776294440dd98a51103756294440dd18a51103774294440dd90a51103754294440dd10a51103773294440dd8ca51103753294440dd0ca51103766094440dd182511035e5354440d754d511036e5254440db549511027f63544409f18d511033e4354440cf10d511027f62544409f18951103776554440ddd4d51103765354440f594d51103565354440dd54d51103d55354440d554d51103745354440ed90d51103b44354440ddd4951103765254440f994951103665254440dd54951103e55254440d954951103745254440dd99151103776354440dd98d51103756354440dd18d51103774354440dd90d51103364354440dd50d51103744354440cd10d51103776254440dd98951103756254440dd18951103774254440dd90951103754254440dd10951103773254440dd8c951103753254440dd0c951103766054440dd18151103744054440b798c51102dd6314440d794c511035d5314440bb98851102ed6214440db948511036d5214440bd98451103755114440cf953411035e53d0440d754f411036e52d0440db54b411037651d0440dd54741102fa60d0440be583411027d6590440b798e41102dd6390440d794e411035d5390440db94a411036d5290440dd546411027f6550440cf951411035e5350440d754d411036e5250440db54941103765150440d794c411035d5310440db948411036d5210440dd94441103755110440be98041102f960104409fd97311027e65cc4409f597311035e53cc440d754f311039c43cc440db94b311036d52cc440dd947311037551cc4409fd96311027e658c4409f59631102be648c440af592311035e538c440d754e311036e528c440db54a3110376518c440dd546311027f654c4409f595311027c654c440afd9131102bc644c440d794d311035d534c440e710d311036e524c440db5493110376514c440dd545311027f650c4409f994311027d650c440d794c311035d530c440db948311036d520c440dd9443110375510c4409fd97211027e65c84409f597211035e53c8440d754f211036e52c8440db54b211037651c8440dd547211027f65884409f996211027d6588440d794e211035d5388440db94a211036d5288440dd946211037551884409fd95211027d65484409f19521102bf6448440af191211035e5348440d754d211036e5248440db54921103765148440dd545211027f65084409f994211027d6508440af99021102bd6408440b798c21102dd6308440d794c
  | 26 => 0x254c409f189531027f6154c409f185531035f6554c40e7191531035e6454c40d7d89531035e6254c40d7589531035c6254c40d7d85531035e6154c40d7585531035c6154c40d7981531035c6054c40d710153102de6314c40d754c53102ee6214c40bb58853102f66114c40bd584531033e54d0c40d794f431035d53d0c40be98343102f960d0c409f596431035d5390c40af596431033d6590c408f59643102be6390c40e794e431033d5390c40e754e431031d5390c40af582431027f6550c40cf951431035e5350c40d794c431035d5310c40e750c43102fa6010c40be58043102be6310c40e798c431039e5310c40cf54c431039d5310c40c754c43103ba6010c40af58043103b96010c40b798f52102dd63d4840d794f521035d53d4840bd98752102f561d4840d794e521035d5394840dbd4a521027e63948409f58e521027e61948409f586521036f5394840db94e52103ce5394840d394e521036d5394840f354e521034d5394840db14e52103ae4394840eb10e521036c6494840dbd8e521036e6394840db58e521036c6394840dbd0e521036e4394840db50e521036c4394840dbd86521036e6194840db586521036c6194840db982521036c6094840d794d521035d53548409fd8d521027c6354840cf90d521033c43548409fd85521027c6154840dbd95521036f5354840db94d52103ce5354840d394d521036d5354840f354d521034d5354840db14d52103ae4354840eb10d521036e6454840dbd8d521036e6354840db58d521036c6354840dbd0d521036e4354840cb90d521036d4354840db10d521032c4354840dbd85521036e6154840db585521036c6154840db981521036c6054840db10152102de6314840b758c521035e5314840d754c52102ee6214840db54852102f66114840bd584521033e54d0840d794f421035d53d0840db94b421036d52d0840be98342102f960d08409f59642102de6390840b758e421035e5390840d754e421036d52908409fd95421033e5450840d794d421035d5350840db949421035e5310840d754c421036e5210840db54842102fa6010840be580421027f65cc8409f997321027d65cc840d794f321035d53cc840e710f321036e52cc840db54b321027f658c8409f996321027d658c840af99232102bd648c840d794e321035d538c840db94a321036d528c8409fd95321027d654c8409f19532102bf644c840af191321035e534c840d754d321039c434c840db949321036d524c8409fd94321027e650c8409f594321035e530c840d754c321036e520c840db54832102de63d4440b758f511035e53d4440d754f51102ee62d4440bb58b511036e52d4440db54b511035e5394440d754e511036e5294440db54a511037751944409f98e511027d63944409f98a511027d6294440ddd4e5110
  | 27 => 0x40d7d4f325035c53cc940e7d0f325027e658c9409f596325027c658c940af99232502bd648c940d7d4e325035c538c9409fd95325027e654c9409f19532502be644c940af591325035f534c940d714d325039f434c9409f994325027d650c9409f19432502be640c940af590325035f530c940d714c32502fa600c940be580325035f53d4540d714f515027e63d45409f58f515027e62d45409f58b515033f42d4540cf50b51502de6394540b758e515035f5394540d714e51503775194540b7d8d51502dc6354540d7d4d515035c5354540bbd8951502ec6254540d7d4c515035c5314540dd544515027e63145409f58c515027e62145409f588515027e65d0540d7d4f415035c53d0540af997415033e65d0540af58f415039f53d0540cf14f415039c53d0540c714f41502bd62d0540cfd4b415033c51d0540af98341502bd6490540b798e41502dd6390540d7d4e415035c5390540ddd4641503745190540be98241502f96090540d7d4d415035c5350540ddd4541503745150540bed8141502f86050540afd8d415039f5350540cf14d415039c5350540c714d41502bf6250540cfd4941503b76150540edd45415033c5150540ed14541503bb6050540af18141503b860505409f99441502be6410540d7d4c415035c5310540ed504415027e65cc5409f597315027c65cc540af99331502bd64cc540d7d4f315035c53cc540e7d0f315027e658c5409f596315027c658c540af99231502bd648c540d7d4e315035c538c5409fd95315027e654c5409f19531502be644c540af591315035f534c540d714d315039f434c5409f994315027d650c5409f19431502be640c540af590315035f530c540d714c31502fa600c540be580315027e65c85409f597215027c65c8540af99321502bd64c8540d7d4f215035c53c8540ddd47215037451c85409f996215027d65885409f19621502be6488540af592215035f5388540d714e215036f5288540db14a215027f65485409f995215027c6548540af99121502bd6448540d7d4d215035c53485409f994215027d65085409f19421502be6408540af59021502de6308540b758c215035f5308540d714c215036f5208540db14821503775108540dd14421503e52108540be98021502f96008540d7d4f405035c53d0140f6d4f40503d853d0140eed0f40503b943d0140eed0b40503b942d0140eed0740503b941d0140d7d4e405035c5390140af58e405039f5390140cf14e405039c5390140c714e40502bd6290140af58640503bb5090140bb98b53102ed62d4c40bd98753102f561d4c40d7d4e531027e6294c409f58a531027e6194c409f586531039c6494c40d7192531035f6294c40d798a531035d6294c40d718a531035f6194c40d7986531035d6194c40d7186531035e6094c40d7182531027f6
  | 28 => 0x94541903755150640bed8141902f860506409fd97319027e65cc6409f597319035e53cc640d754f319039c43cc6409fd96319027e658c6409f59631902be648c640af5923190376518c640dd546319027f654c6409f595319027c654c640afd9131902bc644c640d794d319035d534c640e710d3190376514c640dd545319027f650c6409f994319027d650c640be98031902f9600c6409fd97219027e65c86409f597219036e52c8640db54b219027f65886409f996219027d6588640dd946219037551886409fd95219027d65486409f19521902bf6448640af191219036e5248640db54921903765148640dd545219027f65086409f994219027d6508640af99021902bd6408640b798c21902dd6308640f948421902fa6008640be58021902bd65d0240cf59740902be63d0240cf54f409033d52d0240cf54740902f965d0240de597409027e62d4d409f58b535027e61d4d409f587535039f64d4d40d7d93535035f62d4d40d798b535035d62d4d40d718b535035f61d4d40d7987535035d61d4d40d7187535035f60d4d40d7583535035f5394d40d754c535027e6214d409f588535027e6114d409f58453502de6514d40d7994535039d6414d40d7d90535035f6214d40d7988535035d6214d40d7188535035f6114d40d7984535035d6114d40d7184535035f6014d40d7580535035d4014d409f997435035c53d0d40af997435033e65d0d408f997435039f53d0d40cf14f435039c53d0d40c714f43502bd62d0d40af58743502be60d0d40af592435035f5390d40d714e43502fa6090d40be582435035f5350d40d714d43502fb6050d40be181435039f6350d40e7d4d435033c5350d40e714d435031c5350d40afd8943502bf6150d40eed8143502bc6050d40ee181435027e6510d40af990435035f5310d40e750c435035f53d4940d714f525027e63d49409f58f525027e61d49409f58752502de6394940b758e525035f5394940d714e525036f5294940b7d8d52502dc6354940d7d4d525035c5354940bdd8552502f46154940d7d4c525035c5314940db548525027e63149409f58c525027e61149409f584525027e65d0940d7d4f425035c53d0940af997425033e65d0940af58f425039f53d0940cf14f425039c53d0940c714f425033c52d0940af58742502be60d0940af59242502de6390940b758e425035f5390940d714e425036f5290940db14a42502fa6090940be582425035f5350940d714d425036f5250940db14942502fb6050940be18142502bf6350940e7d4d425033c5350940e714d425031c5350940ebd8942503af5250940cf14942503ac5250940afd8542503bb6050940af18142503b860509409f99442502be6410940d7d4c425035c5310940eb508425027e65cc9409f597325027c65cc940af99332502bd64cc9
  | 29 => 0x2d039f434cb409fd9432d027e650cb409f59432d02be640cb40af59032d02de6394740b758e51d037751947409f98e51d035e63947409798e51d027d6394740d758e51d025d63947409f98a51d027d62947409fd8d51d027c63547409fd8951d027c6254740cfd0951d033d4254740dd54451d037651d0740dd54741d02fa60d0740be58341d02bd63d0740cf94f41d02bd62d0740cf54b41d033e51d0740ed94741d03b551d0740af98341d03ba60d0740ee58341d02de6390740b758e41d02bf6550740cfd9541d02bf6350740cf94d41d02bf6250740cf54941d03b76150740edd4541d033e5150740ed14541d02bc6050740dd94441d03755110740ed50441d02fa6010740be58041d027f65cc7409f99731d027d65cc740af99331d02bd64cc740e7d0f31d027f658c7409f99631d027d658c740af99231d02bd648c7409fd9531d027d654c7409f19531d02be644c740af59131d039f434c7409fd9431d027e650c7409f59431d02be640c740af59031d027f65c87409f99721d027d65c8740af99321d02bd64c87409fd9621d027e65887409f59621d02be6488740af59221d027f65487409f59521d027c6548740af99121d02bd64487409fd9421d027e65087409f59421d02be6408740af59021d02de6308740b758c21d03e52108740be98021d02f96008740d7d4e539027e6294e409f58a539027e6194e409f586539027f6254e409f189539027f6154e409f185539035d5314e40bb98853902ed6214e40bd98453902f56114e40d794e439035d5390e40be98243902f96090e40e794e439033d5390e40e754e43903ba6090e40af58243903b96090e40d794d439035d5350e40bed8143902f86050e40e750c43902bd6510e40cf594439039e6310e40e7d4c439033d5310e40e714c43902bd6010e40dbd4a529027e6394a409f58e529027e6194a409f586529027f6354a409f18d529033e4354a40cf10d529027f6154a409f18552902de6314a40b758c529036d5214a40bd98452902f56114a40b798e42902dd6390a40db94a429036d5290a40be98242902f96090a40db949429036d5250a40bed8142902f86050a409fd97329027e65cca409f597329035e53cca40d754f329039c43cca409fd96329027e658ca409f59632902be648ca40af592329036e528ca40db54a329027f654ca409f595329027c654ca40afd9132902bc644ca40d794d329035d534ca40e710d329036e524ca40db549329027f650ca409f994329027d650ca40be98032902f9600ca40ddd46519027e63946409f58e519027e62946409f58a519027f63546409f18d519033e4354640cf10d519027f62546409f18951902de6314640b758c51902ee6214640bb58851903755114640b798e41902dd6390640dd94641903755190640be98241902f96090640dd
  | 30 => 0x7a6494021de59250087786494021ded8e500877a6394021de58e50087786394021ded0e500877a4394021de50e50087784394021de18a500877b4294021de90a50087794294021de10a500877b3294021de8ca50087793294021de0ca50087786194021ded06500877a4194021de50650087784194021decc6500877a3194021de4c650087783194021dec86500877a2194021de486500873e5454021cf551500875e5354021d754d50087e521540219fd91500867c64540219fd8d500867c6354021dbc8550087762154021db48550087752154021d9485500877b6554021ded51500877a5454021ee951500873a5454021de55150087b95454021ce55150087785454021ded4d500877a5354021f694d500875a5354021de54d50087d95354021d654d50087785354021fac8550087f22154021fa48550087f12154021f8485500877b6454021de99150087796454021de191500877b6354021de98d50087796354021de18d500877b4354021de90d50087794354021de10d500877a6254021ded09500877a4254021de50950087784254021decc9500877a3254021de4c950087783254021de985500877b4154021de90550087794154021de105500877b3154021de8c550087793154021de0c5500877b2154021dac85500877a2154021dc88550087792154021da48550087712154021d848550087782154021af99050086bd6414021cf950500873d5414021b798c50086dd6314021d794c500875d5314021f948450086fa6014021de540500875f5394f409f98a53d027d6294f409f98653d027d6194f409fd8953d027c6254f409fd8553d027c6154f40d754c53d035e53d0f40d754f43d02fa60d0f40be58343d033e53d0f40e794f43d039d53d0f40af58b43d02bd61d0f40af98343d03ba60d0f40ee58343d02bf6550f40cfd9543d039f6350f40e7d4d43d033e5350f40e714d43d02bf6250f40afd8543d02bc6050f40d794c43d035d5310f40e750c43d02fa6010f40be58043d02de6394b40b758e52d036f5294b409f98e52d035e6394b409798e52d027d6394b40d758e52d025d6394b409f98652d027d6194b409fd8d52d027c6354b409fd8552d027c6154b40db54852d036e52d0b40db54b42d02fa60d0b40be58342d02bd63d0b40cf94f42d033e52d0b40eb94b42d03ad52d0b40af58742d02be60d0b40ee98342d03b960d0b40b798e42d02dd6390b40afd9542d033f6550b40afd8d42d033e5350b40ebd8942d03af5250b40cf94942d03ac5250b40afd8542d02bc6050b40db94842d036d5210b40eb50842d02fa6010b40be58042d027f65ccb409f99732d027d65ccb40af99332d02bd64ccb40e7d0f32d027f658cb409f99632d027d658cb40af99232d02bd648cb409fd9532d027d654cb409f19532d02be644cb40af5913
  | 31 => 0x8c8219fd95320873e544c821cf551320875e534c821d754d320867f650c8219f594320873e540c821cf550320875e530c821d754c32087cd320c821bd98432086f5610c8219f992510867d64944219f98e510867d63944219f597410873e54d0421cf553410875e53d0421d754f410867f65904219f596410873e5490421cf55241086de6390421b758e410875e5390421d754e41086ee6290421bb58a410867f6550421cf951410873d5450421d794d410875d53504219fd94410867e65104219f594410867c6510421cf950410873d5410421d794c410875d5310421bb98841086ed6210421ed504410867d65cc421cf953310873d54cc421d794f310875d53cc4219fd96310867d658c421af99231086bd648c421cf952310873d548c421d794e310875d538c421bb98a31086ed628c4219fd95310873e544c421cf551310875e534c421d754d310867f650c4219f994310867d650c4219f194310873e540c421cf550310875e530c421d754c31086ee620c421bb58831087d5310c421cf953210873d54c8421d794f210875d53c8421eb95321087ad54c8421f394f21087cd53c8421cf952210873d5488421d794e210875d5388421bb58a210876e5288421ed95221087b55488421f594e21087d55388421bd58a21086e56288421dd94a21087e652884219fd95210873e5448421cf551210875e5348421d754d21086ef6548421dbd95210866f6548421eb95121087ad5448421f394d21087cd5348421bbd85210876e5148421f9d0521087e64148421f950521087e44148421f9cc521087e63148421f94c521087e43148421bdd95210877765484219dd9521087b65448421ed55121087d65348421f554d21086f76248421f9d8921087765248421f994921087e74248421f990921087e54248421f910921087e73248421f98c921087e53248421f90c921087e76548421b9d9521087676548421f9d9121087e66448421f959121087e46448421f9d5121087e65448421e995121087e55448421e955121087e45448421f9d8d21087e66348421f958d21087e46348421f9d4d21087e65348421f194d21087e55348421f154d21087e45348421f9d0d21087e64348421f950d21087e44348421f9d8121087e66048421f958121087e46048421af99350086bd64d4021cf953500873d54d4021b798f50086dd63d4021d794f500875d53d4021f9487500873e5494021cf552500875e5394021d754e50087e52194021ded42500867e64940219f592500867e63940219f58e500877b5494021de95250087ba5494021ce95250087795494021ee55250087395494021de152500877b5394021de94e50087da5394021d694e50087795394021f654e50087595394021de14e50087eb2194021fc88650087e92194021fc48650087e12194021ded9250087
  | 32 => 0x1be580540867e6415021cf990540863e64150219f98c540875e63150219798c540867d6315021d758c540865d63150219f988540876e62150219f984540877661150219f980540877a60150219e980540867d6015021de58054086796015021af99353086bd64d4c21cf953530873d54d4c21be98353086f960d4c219f993530873e64d4c218f993530867d64d4c21cf593530863d64d4c219f98b530876e62d4c219f987530877661d4c219f983530877a60d4c219e983530867d60d4c21de583530867960d4c219f596530873e5494c21cf552530875f5394c219f992530867d6494c219f982530867d6094c2197596530875f5494c21d7952530879e5494c21c7952530875d5494c21e7552530871d5494c21d7152530875f6494c21d7992530875d6494c21d7192530875e6294c21d718a530875e6194c21d7186530875f6094c21d7982530875d6094c21d7182530873e5454c21cf551530867f6454c219f191530875f6354c219fd81530867c6054c21d7d95530875f5454c21d7951530879e5454c21c7951530875d5454c21e7551530871d5454c21d7151530875f6454c21d7991530875d6454c21d7191530875e6254c21d7189530875e6154c21d7185530875c2154c21d7d81530875e6054c21d7581530875c6054c21af99053086bd6414c21cf950530873d5414c21b798c530875d5314c21be98053086f96014c219f990530873e6414c218f990530867d6414c21cf590530863d6414c219f98c530875e6314c219798c530867e6214c21db988530867e6114c21dd984530867e6014c21de980530867a6014c219f58053087796014c219e580530867f65d0c219f997430867d65d0c219f197430873e54d0c21cf553430875e53d0c21d754f43086ee62d0c21bb58b43086f661d0c21bd587430867f6590c219f996430867d6590c219f196430873e5490c21cf552430875e5390c21d754e43086ee6290c21bb58a43086f66190c21bd586430867f6550c219f995430867d6550c219f195430873e5450c21cf551430875e5350c21d754d430867f6510c219f994430867d6510c219f194430873e5410c21cf550430875e5310c21d754c430879d4310c219f992520867d64948219f98e520867d63948219f597420873e54d0821cf553420875e53d0821d754f420867f65908219f596420873e5490821cf55242086de6390821b758e420875e5390821d754e42086f66190821bd586420867f6550821cf951420873d5450821d794d420875d53508219fd94420867d6510821cf950420873d5410821d794c420875d5310821eb50842086f66110821bd584420867d65cc821cf953320873d54cc821d794f320875d53cc8219fd96320867d658c821af99232086bd648c821cf952320873d548c821d794e320875d538c821bd98632086f561
  | 33 => 0x92534867d6494d21cf592534863d6494d219f98e534867d6294d21db58a534867d6194d21dd586534867e6094d219f582534867f6454d219f191534875f6354d219fd89534876f6254d219fd8553487776154d219fd81534867c6054d219f994534875d5314d219f990534867d6414d21d798c534867e6014d219f580534867f65d0d219f997434867d65d0d219f197434873f54d0d21cf153434875e53d0d21d754f434867f6590d219f996434867d6590d219f196434873e5490d21cf552434875f5390d21d714e434867f6550d219f995434867d6550d219f195434873f5450d21cf151434875f5350d21d714d434867f6510d219f994434867d6510d219f194434873e5410d21cf550434875e5310d21d754c434879d4310d21bb98843486ed6210d21bd98443486f56110d219f997424873f54d0921cf15342486f661d0921bd587424867e6590921b798e42486dd63909219f195424873f5450921cf15142486f76150921bd185424867e65109219f997324875f53cc921d714f32486f661cc921bd587324867e658c921af99232486bd648c9219f195324875f534c921d714d32486f7614c921bd185324867e650c9219f997414873f54d0521cf15341486ee62d0521bb58b414867e6590521b798e41486dd63905219fd95414867d65505219f195414873f5450521cf15141486ef6250521bb189414867e65105219f997314875f53cc521d714f31486ee62cc521bb58b314867e658c521af99231486bd648c5219fd95314867d654c5219f195314875f534c521d714d31486ef624c521bb189314867e650c521bd58321487e75188521bb582214867e64d41219f593504867e63d41219f58f504877b5094121afd9150486bc6454121b7d8d50486dc6354121af99050486bd6414121b798c50486dd6314121de540504867e6414121cf990504863e64141219f590504873d64141218f590504867e6314121d798c504865e63141219f58c504875d63141219758c50486de63d5021b758f54086fa60d5021be583540867e63d5021d798f540865e63d50219f58f540875d63d50219758f540867e62d5021db98b540867e61d5021dd987540867e60d5021de983540867a60d50219f583540877960d50219e583540867d6595021cfd52540867e63950219f58e540867e60950219f582540863d6595021cfd8e540873e6395021cf58e540873c6395021cf98a540873c6295021cf986540873c6195021cfd82540873e6095021cf582540873c6095021cfd91540867f63550219f18d540867f60550219f181540873f6555021cfd8d540873e6355021cf58d540873c6355021cf989540873c6255021cf985540873c6155021cf085540873f6055021cf981540873d6055021cf18154086be6415021cf55054086de6315021b758c54086fa601502
  | 34 => 0x8875e63d52219798f548867d63d5221d758f548865d63d5221db58b548877661d52219f983548867d60d5221cfd52548867e63952219f58e548867e60952219f582548873f64552219fd8d548867c63552219fd81548867c6055221cf550548873e64152219f98c548867d6315221db588548877661152219f980548867d6015221af99353886bd64d4e219f993538873e64d4e218f993538867d64d4e21cf593538863d64d4e21db58b538877661d4e219f983538867d60d4e21d7d4e538867e6494e219f592538867e6094e219f582538867f6454e219f191538875f6354e219fd81538867c6054e21d754c538867e6414e219f590538875e6314e21db58853887766114e219f980538867d6014e219fd97438867e65d0e219f597438867c65d0e21d794f438875d53d0e21bb98b43886ed62d0e219fd96438867e6590e219f596438867c6590e21cf952438873d5490e21bb98a43886ed6290e219fd95438867e6550e219f595438867c6550e219fd94438867e6510e219f594438867c6510e21cf950438873d5410e21d794c438875d5310e21e750c43886f66110e21bd584438873e54d0a21cf55342886f661d0a21bd58742886de6390a21b758e428873e5450a21cf55142886f76150a21bd18542887ad4210a21d794f328875d53cca21bd98732886f561cca21af99232886bd648ca21d794d328875d534ca21bdd8532886f4614ca21f34c8328873f54d0621cf153418873e5490621cf55241886de6390621b758e41886ee6290621bb58a418873f5450621cf151418873e5410621cf55041886ee6210621bb588418875f53cc621d714f31886be648c621af592318875e538c621d754e31886ee628c621bb58a318875f534c621d714d318875e530c621d754c31886ee620c621bb58831886ed65c8621db59721886f565c8621dd59721886f560c8621ded42508867e64942219f592508867e63942219f58e508867f64542219f191508867f63542219f18d508876f2154221af99050886bd6414221b798c50886dd6314221de54050886de63d5121b758f544867e63d5121d798f544865e63d51219f58f544875d63d51219758f544867e60d51219f583544873f5495121b798e54486dd63951219f992544867e6395121d798e544865e63951219f58e544875d63951219758e544867d6295121db58a544867d6195121dd586544867e60951219f582544873f64551219fd8d544867c63551219fd89544876f62551219fd85544877761551219fd81544867c60551219f994544873d5415121cf990544867e63151219f58c544867e60151219f58054486be64d4d21af593534867e64d4d21cf993534863e64d4d219f593534873d64d4d218f593534867e60d4d219f58353486be6494d21af592534875f5394d219f992534873e6494d218f9
  | 35 => 0xd65104319f194410c73e5410431cf550410c6de6310431b758c410c75e54cc431d7153310c75d52cc431af992310c6bd648c431b758e310c75e538c431ed992310c7b5648c431bd58e310c776538c431f594e310c67f654c431b7d95310c75f654c43197d95310c75e544c431d7151310c75d524c431b7d85310c75e514c431f5905310c7d5414c431bdd95310c777654c4319dd95310c6f7634c431f5d8d310c776534c431f594d310c7d6434c431f550d310c7d6324c431f50c9310c77b50940319f992500c67d64940319f98a500c67d62940319fd91500c67c64540319fd89500c67c6254031d7cc5500c7763154031d74c5500c7753154031af990500c6bd6414031bb988500c6ed6214031de540500c6de63d5321b758f54c867e63d5321d798f54c865e63d53219f58f54c875d63d53219758f54c876e62d5321dd58754c867e60d53219f58354c873f54953219f98e54c867d63953219f98254c867d6095321cfd9154c867f63553219f18d54c867f60553219f18154c873d5415321cf99054c867e63153219f58c54c876e6215321dd58454c867e60153219f58054c86be64d4f21af59353c867e64d4f21cf99353c863e64d4f219f59353c873d64d4f218f59353c876e62d4f21dd58753c867e60d4f219f58353c875f5394f219f99253c867d6494f219f98253c867d6094f219fd9153c867c6454f21d7d8d53c867f6054f219f18153c875d5314f219f99053c867d6414f21d798c53c876e6214f21dd58453c867e6014f219f58053c867f65d0f219f99743c867d65d0f219f19743c875e53d0f21d754f43c86f661d0f21bd58743c867f6590f219f99643c867d6590f219f19643c873e5490f21cf55243c86f66190f21bd58643c867f6550f219f99543c867d6550f219f19543c867f6510f219f99443c867d6510f219f19443c873e5410f21cf55043c875e5310f21d754c43c879d4310f21bb98843c86ed6210f21cfd5342c873c54d0b21cf95242c873d5490b21b798e42c86dd6390b21bd98642c86f56190b21cfd5142c873c5450b21cf95042c873d5410b21bd98442c86f56110b21d7d4f32c875c53ccb21af99232c86bd648cb21d794e32c875d538cb21bd98632c86f5618cb21d7d4d32c875c534cb21d794c32c875d530cb21bd98432c86f5610cb21cf95341c873d54d0721bb98b41c86ed62d0721b798e41c86dd6390721cf95141c873d5450721bbd8941c86ec6250721ed50441c875e53cc721d754f31c86ee62cc721bb58b31c86be648c721af59231c875e534c721d754d31c86ef624c721bb18931c87d5310c721ded4250c867e64943219f59250c867e63943219f58e50c867f64543219f19150c867f63543219f18d50c86be6414321af59050c86de6314321b758c50c87795014321b798f54886dd63d52219f98f54
  | 36 => 0xc931d7951324c75c544c931f3d89324c7cf524c931d7149324c7cc524c931d3149324c7d7614c931b7185324c7d4614c931b5185324c6df604c9319f994324c6de630c9319f997414c73f54d0531cf153414c6de63d0531b758f414c79c43d05319f996414c6de6390531b758e414c67f65505319f595414c67c6550531cfd51414c73c5450531b7d8d414c6dc6350531e710d414c67e6510531ed504414c7d743cc531f510f314c7d732cc531f54cb314c6f560cc531af992314c6bd648c531b7992314c79e648c531a7992314c79d648c531b7192314c6dd628c531f5d46314c6dd608c5319f993504c67d64d41319f98b504c67d62d4131d7ccb504c75d32d4131ded42504c6bf6454131af191504c6ef6254131bb189504c6be6414131af590504c6ee6214131bb588504c77950141319f990504c73e64141318f990504c67d6414131cf590504c63d6414131d7d0c504c75c43141319f988504c76e62141319b988504c67d6214131db588504c66d62141319f98f540c75e63d50319798f540c67e62d50319f58b540c67e61d5031dd987540c67e60d50319f583540c67d6595031cfd52540c67e62950319f58a540c67e60950319f582540c73f64550319fd89540c67c62550319fd81540c67c6055031cf550540c6ee6215031bb588540c6fa6015031be580540c67e6415031cf990540c67e6315031d798c540c67e6215031db988540c66e62150319f588540c76d62150319b588540c67e6115031dd984540c67e6015031de980540c67a60150319f580540c77960150319e580540c67e6494c319f592530c67d65d0c31d794f430c67f6590c319f596430c73e5490c31cf552430c6f66190c31bd586430c67f6550c319fd94430c67d6510c31cf950430c73d5410c31d794c430c79d4310c31bd984430c6f56110c31dbd4a520c67e64948319f592520c67e60948319f582520c67f64548319f191520c67f60548319f181520c6be6414831af590520c76d5214831be980520c6f960148319fd97420c67e65d08319f597420c73e54d0831cf553420c6de63d0831b758f420c6f661d0831bd587420c67f65908319f996420c67d6590831b798e420c6dd6390831db94a420c76d52908319fd95420c67d65508319f195420c73e5450831cf551420c76e5250831db549420c67f65108319f994420c67d6510831d794f320c76e52cc831db54b320c6f661cc831bd587320c67d658c831af992320c6bd648c8319fd95320c75e534c831db948320c76d520c831f34c8320c6f6610c831bd584320c67e6494431cf992510c63e64944319f592510c73d64944318f592510c67d65d0431cfd53410c73c54d04319fd96410c67d6590431cf952410c73d5490431b798e410c6dd63904319fd95410c73f5450431cf151410c67f65104319f994410c67
  | 37 => 0xcf952328c73d548ca31db94a328c76d528ca31bd986328c6f5618ca31cf951328c73d544ca31db949328c76d524ca31bdd85328c6f4614ca31cf950328c73d540ca31f34c8328c73e54d0631cf553418c73e5490631cf552418c6de6390631b758e418c73e5450631cf551418c73e5410631cf550418c6de6310631b758c418c7b54110631cf953318c73d54cc631b7597318c75d65cc631d7953318c79e54cc631c7953318c79d54cc631d7153318c75d52cc631bd597318c77565cc631ed953318c7b554cc631bd583318c6be64d4231af593508c73e54d4231cf553508c73e5494231cf552508c77b50942319f992508c67d64942319f98a508c67d6294231cf951508c73d54542319fd91508c67c64542319fd89508c67c6254231d7cc5508c6be6414231af590508c73e5414231cf550508c6ee6214231bb588508c7795014231d758f544c67e62d51319f58b544c67e60d51319f583544c73f5495131bb98a544c6ed62951319f992544c67d6395131d758e544c67e6295131db98a544c66e62951319f58a544c76d62951319b58a544c67d6195131dd586544c67e60951319f582544c73f64551319fd8d544c75f63551319fd89544c67c62551319fd85544c77761551319fd81544c67c60551319f994544c73d5415131cf990544c67e62151319f588544c67e60151319f580544c67e65d0d31cfd53434c73c54d0d31bd987434c6f561d0d31d7997434c65e65d0d31d7d53434c79f54d0d31d7553434c79c54d0d31b758b434c6de61d0d31f5987434c6d661d0d31f5587434c6dd60d0d319f996434c73e5490d31cf552434c6de6390d319f195434c73f5450d31cf151434c6f76150d31bd185434c67e6510d31cf950434c73d5410d31e750c434c6de6510d31d7994434c6de6410d31e7990434c75f5410d31e7950434c75d5410d31e7550434c71d5410d31b7588434c6de6110d31b7580434c67e64d49319f593524c75f43d4931d710f524c67e60d49319f583524c6be6494931af592524c76f5294931db548524c67e64149319f590524c67e60149319f580524c67e65d09319f597424c67c65d0931cfd53424c73c54d0931e710f424c67e65909319f596424c67c6590931b798e424c6dd6390931dbd4a424c76c52909319fd95424c67e65509319f195424c73f5450931cf151424c6df6350931b718d424c79c4350931dbd49424c76c5250931bdd85424c6f461509319f994424c67d65109319f194424c6de6310931b758c424c6f66110931bd584424c67e65cc931b7997324c75e65cc931b7993324c6dc64cc931d7953324c75c54cc931d714b324c6de61cc931b7583324c6be648c931af592324c6dd638c931dbd4a324c76c528c931bd986324c6f5618c931dbd49324c76c524c931bdd85324c6f4614c931b7991324c6dc644
  | 38 => 0x152cc67c6054b31db54852cc67f65d0b319f99742cc67d65d0b31cfd5342cc73c54d0b31e710f42cc76e52d0b31db54b42cc6f661d0b31bd58742cc67f6590b319f99642cc67d6590b31cf95242cc73d5490b31b798e42cc6dd6390b319fd9542cc67d6550b319f19542cc73f5450b31cf15142cc6df6350b31b718d42cc79c4350b319fd9442cc67e6510b319f59442cc73e5410b31cf55042cc6de6310b31b758c42cc76e5210b31db54842cc76e52ccb31db54b32cc6f661ccb31bd58732cc6de64ccb31b719332cc75e54ccb31d715332cc75e52ccb31f394b32cc7cd52ccb31b798732cc7d661ccb31f558732cc6dd60ccb31af99232cc6bd648cb31b7d9532cc75f654cb31b799132cc6dc644cb31d795132cc75c544cb31f3d8932cc75e524cb31b718532cc6df604cb31db94832cc76d520cb31bd98432cc6f5610cb31cf95341cc73d54d0731b798f41cc6dd63d0731e710f41cc6de6390731b758e41cc73e5450731cf55141cc6df6350731b718d41cc79c4350731ded4250cc67e64943319f59250cc75f4394331d710e50cc67e62943319f58a50cc67f64543319f19150cc67f62543319f18950cc75f3254331d74c950cc6be6414331af59050cc6ee6214331bb58850cc7795014331d758f548c67e62d52319f58b548c77661d52319f983548c67d60d5231cfd52548c67e62952319f58a548c67e60952319f582548c73f6395231cf58e548c73f6295231cf98a548c73d6295231cf18a548c73e6195231cf186548c73f6095231cf982548c73d6095231cf182548c73f64552319fd89548c67c62552319fd81548c67c6055231cfd95548c73f6355231cf58d548c73f6255231cf989548c73d6255231cf189548c73e6155231cf185548c73f6055231cf981548c73d6055231cf181548c73d5415231cf990548c75d63152319f988548c67d6215231dd984548c67e60152319f580548c73e54d0e31cf553438c6f661d0e31bd587438c73e5490e31cf552438c73e5450e31cf551438c6f76150e31bd185438c73e5410e31cf550438c79d4310e31af993528c6bd64d4a31cf953528c73d54d4a31cf952528c73d5494a31dbd4a528c67e6494a319f592528c67e6094a319f582528c73e5454a31cf551528c67f6454a319f191528c67f6054a319f181528c6be6414a31af590528c73e5414a31cf550528c76d5214a31be980528c6f96014a319fd97428c67e65d0a319f597428c73e54d0a31cf553428c6de63d0a31b758f428c67f6590a319f996428c67d6590a31cf952428c73d5490a31b798e428c6dd6390a319fd95428c67d6550a319f195428c73e5450a31cf551428c6f76150a31bd185428c67f6510a319f994428c67d6510a31cf950428c73d5410a31bd984428c6f56110a31cf953328c73d54cca31af992328c6bd648ca31
  | 39 => 0x73c43141419f988505076e62141419b988505067d6214141db588505066d6214141d7d4e531067e6294c419f58a531067e6094c419f582531067f6254c419f189531067f6054c419f181531075d5314c41bb98853106ed6214c41be98053106f96014c41d794f431075d53d0c41bd98743106f561d0c419f596431073e5490c419fd95431073e5410c41d794c431075d5310c41e750c43106f66110c41bd584431076f52948419f98e521067d63948419f982521067d60948419fd8d521067c63548419fd81521067c6054841b798c52106dd6314841db54852106fa6014841be580521073e54d0841db94b421076d52d0841bd98742106f561d08419f59642106de6390841b758e421067f6550841cf951421076e5210841db54842107ad4210841bd98442106f561108419fd97321067e65cc8419f59732106be64cc841af593321075e53cc841d754f32106f661cc841bd587321067f658c8419f996321067d658c841af99232106bd648c841db94a321076d528c8419fd95321067d654c8419f195321075e534c841d754d321076e524c841db549321067f650c8419f994321067d650c841d798e511075d6394441cf94f411073d52d0441af592411073e5490441b798e41106dd6390441bd59241107765490441ed95241107d66390441f558e411067f6550441afd95411073f65504418fd95411073e5350441cf54941106bf6150441cf94541106f76550441ddd9541106776550441bdd9141107b76450441dd95141107b65450441edd0d41107b54350441ed90941107b44250441ded42501067e63940419f58e501067e62940419f58a501067f63540419f18d501067f62540419f189501073f4154041dd905501073d4154041dd50550106de6314041b758c50106ee6214041bb58850107795014041bb98b54cc6ed62d5331d798f54cc67e62d5331db98b54cc66e62d53319f58b54cc76d62d53319b58b54cc77561d53319f98354cc67d60d5331cfd5254cc67e62953319f58a54cc67e60953319f58254cc73f6455331d718d54cc67f62553319f18954cc67f60553319f18154cc73d5415331cf99054cc75e63153319f98854cc67d6215331dd58454cc67e60153319f58054cc6dd65d0f31d759743cc75f54d0f31d755343cc6dd62d0f31b798743cc6dd60d0f31cf95243cc73d5490f31bd98643cc6f56190f31cf95043cc73d5410f31e750c43cc6f66110f31bd58443cc75d6510f31e799043cc75f5410f31e795043cc75d5410f31e755043cc71d5410f31b758843cc6de6110f31f598443cc7d56110f31b758043cc6be64d4b31af59352cc6be6494b31af59252cc76f5294b319f99252cc73e6494b318f99252cc67d6494b31cf59252cc63d6494b319f98252cc67d6094b319fd9152cc67c6454b31d7d0d52cc75c4354b319fd8
  | 40 => 0x538ca41d754e329067f654ca419f595329067c654ca41d794d329075d534ca41bdd8532906f4614ca419fd94329067e650ca419f594329075e530ca41d754c32906f6610ca41bd584329075e53d0641d754f41906bd65d0641cf597419073e53d0641e794f419071e53d0641e754f419073d52d0641bd597419077565d0641f594f41907d553d0641bd58341906de63d4241b758f509075e53d4241d754f509075e5394241d754e509077b50942419f98e509067d63942419f98a509067d6294241d794d509075d53542419fd8d509067c63542419fd89509067c6254241cfd0550906de6314241b758c509075e5314241d754c50906ee6214241bb588509077950142419f98b535067d62d4d419f983535067d60d4d41d7d4e53506ee6294d41bb58a535075d5314d419f988535067d6214d419f980535067d6014d419f997435075f5390d41d714e43506f66190d41bd58643506be6390d41cfd4e435079f5390d41e714e43506bd6290d41af98643507b66190d41ad98643507b56190d41af582435075f5350d41d714d43506f76150d41bd185435067e6510d41e750c43506be6510d41cf99443506be6310d41e798c435073f5310d41e794c435079d5310d41af58843506be6110d41af580435067e63d49419f58f525073e43d4941cf10f525067e60d49419f58352506de6394941b758e525076f5294941db548525067e63149419f58c525067e60149419f580525067e65d0941af997425073e65d0941af98f425073c53d0941cf14b42506be61d0941af58342506bd6490941b798e42506dd6390941dbd4a425076c5290941bd98642506f56190941dbd49425076c5250941bdd8542506f46150941af18d425073c5350941ebd8942507af5250941cf14942507ac5250941cb14942507b76150941af18542507b46150941ad18542506bf60509419f99442506be64109419f997325067d65cc9419f19732506bf64cc941af193325075f53cc941d714f325079c43cc9419f996325067d658c9419f19632506be648c941af592325076f528c941db14a325067f654c9419f995325067c654c941afd9132506bc644c941d7d4d325075c534c941e710d325076f524c941db14932506f7614c941bd185325067e650c9419f594325067c650c941af99032506bd640c941bd98432506f5610c941ed90f41507b443d0541edd0b41507b542d0541bd58341506de6390541b758e41506be6390541e798e415069e6390541e758e41506bd6290541edd4641506bd60905419f98f505067d63d41419f98b505067d62d4141cfd0b505073d42d4141ded4250506df6354141b718d50506ef6254141bb18950506de6314141b758c50506ee6214141bb588505077950141419f98c505075e63141419798c505067d6314141d758c505065d6314141cf90c505
  | 41 => 0xf41cf54e43d06bd6290f41af98643d06bd6090f41d794c43d075d5310f41e750c43d06f66110f41bd58443d079e6310f41e794c43d073d5310f41e754c43d071d5310f41af58843d06be6110f41ed98443d07b56110f41af58043d06de63d4b41b758f52d06de6394b41b758e52d076f5294b419f98e52d075e6394b419798e52d067d6394b41d758e52d065d6394b419f98252d067d6094b419fd8d52d067c6354b41cf90d52d073c4354b419fd8152d067c6054b41db54852d076e52d0b41db54b42d06f661d0b41bd58742d06be63d0b41cf94f42d073e52d0b41eb94b42d07ad52d0b41af98742d07b661d0b41ed58742d06bd60d0b41b798e42d06dd6390b41afd9542d073f6550b41af18d42d073e5350b41ebd8942d073e5250b41af18542d06bf6050b41db94842d076d5210b41bd98442d06f56110b419fd9732d067e65ccb419f59732d06bf64ccb41af19332d079c43ccb41db94b32d076d52ccb41bd98732d06f561ccb419fd9632d067e658cb419f59632d06be648cb41af59232d075e538cb41d754e32d067f654cb419f59532d067c654cb41afd9132d06bc644cb41e710d32d067f650cb419f99432d067d650cb41af99032d06bd640cb41d794c32d075d530cb41db94832d076d520cb41ded4250d067e63943419f58e50d073e4394341cf10e50d067e62943419f58a50d067f63543419f18d50d067f62543419f18950d073f4254341cf50950d06de6314341b758c50d06ee6214341bb58850d07795014341d7d4e539067e6294e419f58a539067e6094e419f582539075f6494e41d7d8a539075e6294e41d758a539075c6294e41d7986539075c6194e41d7d82539075e6094e41d7582539075c6094e419fd89539067c6254e419fd81539067c6054e41d7d95539075d6454e41d7d89539075e6254e41d7589539075c6254e41d7985539075c6154e41d7d81539075e6054e41d7581539075c6054e41d754c539075e53d0e41d794e439075d5390e41bd98643906f56190e41d794d439075d5350e41bdd8543906f46150e41d754c439079d4310e41b798f52906dd63d4a41d794f529075d53d4a41d794e529075d5394a41dbd4a529067e6394a419f58e529067e6094a419f582529075e5354a41d754d529067f6354a419f18d529067f6054a419f18152906de6314a41b758c529075e5314a41d754c529076d5214a41be98052906f96014a41d794f429075d53d0a41b798e42906dd6390a41d794e429075d5390a41db94a429076d5290a41bd98642906f56190a41d794d429075d5350a41db949429076d5250a41bdd8542906f46150a41d794c429075d5310a41eb508429067f65cca419f997329067d65cca41af99332906bd64cca41d794f329075d53cca419fd96329067e658ca419f59632906be648ca41af592329075e
  | 42 => 0x7192324cbcf528c932b7586324cadd608c9329f993514ca7d64d4532d7d0f514cb5c43d45329f983514ca7d60d4532af992514cabd6494532ddd46514cb7551145329f990514ca7d64145329f980514ca7d60145329f993504ca7d64d41329f987504ca7d61d4132ded42504cabf6454132af191504caf76154132bd185504cabe6414132af590504caf66114132bd584504cb7950141329f990504cb3e64141328f990504ca7d6414132cf590504ca3d6414132d7d0c504cb5c43141329f984504cb7661141329d984504ca7d6114132dd584504ca7561141329f98f540cb5e63d50329798f540ca7e62d5032db98b540ca7e61d50329f587540ca7e60d50329f583540ca7d6595032cfd52540ca7e61950329f586540ca7e60950329f582540cb3f64550329fd85540ca7c61550329fd81540ca7c6055032cf550540caf66115032bd584540cafa6015032be580540ca7e6415032cf990540ca7e6315032d798c540ca7e6215032db988540ca7e6115032dd984540ca7661150329f584540cb7561150329d584540ca7e6015032de980540ca7a60150329f580540cb7960150329e580540ca7e6494c329f592530ca7d65d0c32d794f430ca7f6590c329f596430cb3e5490c32cf552430caee6290c32bb58a430ca7f6550c329fd94430ca7d6510c32cf950430cb3d5410c32d794c430cb9d4310c32bb988430caed6210c329f992520cb3e64948328f992520ca7d6494832cf592520ca3d64948329f597420cb3f54d0832cf153420ca7f65908329f596420cb3e5490832cf552420cade6390832b758e420ca7f6550832cfd51420cb3c54508329fd94420ca7e65108329f594420ca7c6510832cf950420cb3d5410832b798c420cadd6310832d7953320cb5c54cc832af992320cabd648c832b758e320cb5e538c832eb992320cbad648c832bb58e320cb6e538c832f394e320ca7f654c832b7d95320cb5f654c83297d95320cb5e544c832d7151320cadf624c832d7949320cbce424c832f3509320caef654c832dbd95320ca6f654c832bbd8d320cbcf634c832db94d320cbce534c832f390d320cbcd434c832ddd46510ca7e64944329f592510ca7e60944329f582510ca7f64544329f191510cb5f3254432d74c9510ca7f60544329f181510cabe6414432af590510cb755114432be980510caf96014432ded42500ca7e64940329f592500ca7e61940329f586500ca7f64540329f191500cb5f3254032db8c9500cb5d3254032db4c9500ca7f61540329f185500cabe6414032af590500caf66114032bd584500cb795014032bb98b53d06ed62d4f41d7d4e53d067e6294f419f58a53d067e6094f419f58253d067f6254f419f18953d067f6054f419f18153d075d5314f41d794f43d075d53d0f41bd98743d06f561d0f41af59643d073d6590
  | 43 => 0x548cb3e6255232cf189548cb3f6155232cf985548cb3d6155232cf185548cb3f6055232cf981548cb3d6055232cf181548cb3d5415232cf990548cb5d6315232db988548ca7e61152329f584548ca7e60152329f580548cb3e54d0e32cf553438caee62d0e32bb58b438cb3e5490e32cf552438cb3e5450e32cf551438caef6250e32bb189438cb3e5410e32cf550438cb9d4310e32cf953428cb3d54d0a32cf952428cb3d5490a32b798e428cadd6390a32cf951428cb3d5450a32cf950428cb3d5410a32b798c428cadd6310a32eb508428cb3e54cca32cf553328cadd65cca32d7597328cb5e54cca32e7953328cb1e54cca32e7553328cb5c54cca32bb597328cb6d65cca32eb953328cbad54cca32bb583328cabe64d4632af593518cb3e54d4632cf553518cb3e5494632cf552518cb7751946329f992518ca7d64946329f982518ca7d6094632cf951518cb3d54546329fd91518ca7c6454632d7cc9518ca7f60546329f181518cabe6414632af590518cb3e5414632cf550518cb755114632be980518caf96014632af993508cabd64d4232cf953508cb3d54d4232cf952508cb3d5494232ded42508ca7e64942329f592508ca7e61942329f586508cb3e5454232cf551508ca7f64542329f191508cb5f32542329fd85508ca7c6154232af990508cabd6414232cf950508cb3d5414232bd984508caf56114232de540508cb5d63d51329f987544ca7d61d51329f983544ca7d60d5132cfd52544caf66195132bd586544ca7e64951329f58e544cb5d63951329f58a544cb6d62951329f986544cb7661951329d986544ca7d6195132dd586544ca7561951329f982544ca7d6095132cfd91544ca7f6355132d7d8d544ca7f6255132dbd89544ca7f61551329f185544ca7f60551329f181544ca7e6515132cf550544cb3e64151329f984544ca7d61151329f980544ca7d60151329f997434cb3f54d0d32cf153434caee62d0d32bb58b434cb5e65d0d3297997434cb5f54d0d32e7d53434cb5d54d0d32e7153434cade62d0d32f398b434cace62d0d32f358b434cadd61d0d32b7583434ca7e6590d32cf952434cb3d5490d32b798e434ca7c6550d32cfd51434cb3c5450d32bbd89434caec6250d329f994434cb3e5410d32cf550434cb9d4310d32b7994434cb5e6510d32b7990434cb9e6410d32d7d50434cb9e5410d32d7550434cb9d5410d32c7550434cade6210d32b7584434cadd6010d329f997424cb3f54d0932cf153424cade63d0932b758f424cb9c43d09329f996424cade6390932b758e424ca7f65509329f595424ca7c6550932cfd51424cb3c5450932b7d8d424cadc6350932e710d424ca7e6510932eb508424cbcf43cc932f310f324caed60cc932af992324cabd648c932b7992324cb9e648c932a7992324cb9d648c932b
  | 44 => 0xaf56114c42be9805310af96014c42d794f4310b5d53d0c42bb98b4310aed62d0c429f5964310b3e5490c429fd954310b3e5410c42d794c4310b5d5310c42e750c4310aee6210c42bb5884310b5e6394842d758e5210b3e53d0842af5924210b3e5490842b798e4210add6390842bb5924210b6e5490842eb9524210bce6390842f358e4210a7f6550842afd954210b3f65508428fd954210b3e5350842afd894210b3e5250842bbd954210b6f65508429bd954210aef6450842ebd914210b6e5450842eb9514210baf4350842eb50d4210b7751944429f98e5110a7d63944429f9825110a7d60944429fd8d5110a7c6354442cfd095110b3d42544429fd815110a7c6054442b798c5110add6314442dd5445110afa6014442be5805110b7b50940429f98e5010a7d63940429f9865010a7d61940429fd8d5010a7c6354042cfd095010b6e4254042cf5095010b6d42540429fd855010a7c6154042b798c5010add6314042bd9845010af56114042de5405010af661d5332bd58754ccb5e63d5332db58b54cca7e61d5332dd98754cca7661d53329f58754ccb7561d53329d58754cca7e60d53329f58354ccb3f54953329f98654cca7d61953329f98254cca7d6095332cfd9154ccb5c63553329fd8554cca7c61553329fd8154cca7c6055332cf55054ccb3e6415332d798c54ccb6d62153329f98454cca7d61153329f98054cca7d6015332b759743ccb5d65d0f32d7d5343ccb5d54d0f32b798b43ccadd61d0f32b758343ccb3e5490f32cf55243ccaee6290f32bb58a43ccb3e5410f32cf55043ccb9d4310f32bb98843ccaed6210f32d759443ccb9e6410f32d7d5043ccb9e5410f32d755043ccb9d5410f32c755043ccade6210f32f398843ccbcd6210f32b758443ccadd6010f32cf95342ccb3d54d0b32b798f42ccadd63d0b32e710f42ccade6390b32b758e42ccb3e5450b32cf55142ccadf6350b32b718d42ccb9c4350b32af99351ccabd64d4732af99251ccabd6494732ddd4651cca7e6494732cf99251cca3e64947329f59251ccb3d64947328f59251cca7e60947329f58251cca7f64547329f19151ccb5f4354732d710d51cca7f60547329f18151ccb755114732ded4250cca7e64943329f59250ccb5f4394332d710e50cca7e61943329f58650cca7f64543329f19150cca7f61543329f18550ccabe6414332af59050ccaf66114332bd58450ccb795014332d758f548cb6e62d52329f987548ca7d61d52329f983548ca7d60d5232cfd52548ca7e61952329f586548ca7e60952329f582548cb3f6395232cf58e548cb3e6295232cf18a548cb3f6195232cf986548cb3d6195232cf186548cb3f6095232cf982548cb3d6095232cf182548cb3f64552329fd85548ca7c61552329fd81548ca7c6055232cfd95548cb3f6355232cf58d
  | 45 => 0x14342d7d4e5390a7e6194e429f5865390a7e6094e429f5825390b5f6494e42d798a5390b5c6294e42d7d865390b5e6194e42d75865390b5c6194e42d7d825390b5e6094e42d75825390b5c6094e429fd855390a7c6154e429fd815390a7c6054e42d7d955390b5d6454e42d79895390b5c6254e42d7d855390b5e6154e42d75855390b5c6154e42d7d815390b5e6054e42d75815390b5c6054e42d754c5390b5e53d0e42d794e4390b5d5390e42bb98a4390aed6290e42d794d4390b5d5350e42bbd894390aec6250e42d754c4390b9d4310e42d794f4290b5d53d0a42af5974290b3d65d0a42cf94f4290b9e53d0a42c794f4290b9d53d0a42bb5974290b6d65d0a42f394f4290bcd53d0a42bb5834290ade63d4642b758f5190b5e53d4642d754f5190b5e5394642d754e5190b7751946429f98e5190a7d63946429f9825190a7d6094642d794d5190b5d53546429fd8d5190a7c6354642cfd095190a7f60546429f1815190ade6314642b758c5190b5e5314642d754c5190b755114642be9805190af96014642b798f5090add63d4242d794f5090b5d53d4242d794e5090b5d5394242ded425090a7e63942429f58e5090a7e61942429f5865090b5e5354242d754d5090a7f63542429f18d5090b3f42542429fd855090a7c6154242b798c5090add6314242d794c5090b5d5314242bd9845090af56114242de5405090a7e61d4d429f5875350a7e60d4d429f5835350b5f5394d42bd9865350af56194d42d754c5350a7e6114d429f5845350a7e6014d429f5805350a7e65d0d42d7d4e4350b5c5390d42bb98a4350aed6290d42af98e4350b3f5390d42e7d4e4350b9c5390d42af98a4350bae6290d42ab98a4350bad6290d42af5864350abd6090d42d7d4d4350b5c5350d42bbd894350aec6250d429f9944350b9d4310d42af9944350b3e6510d42af98c4350b9e6310d42cfd4c4350b9e5310d42e754c4350abe6210d42af5844350abd6010d42eb90f4250bac43d0942bb5834250ade6390942b758e4250abe6390942e798e4250a9e6390942e758e4250baf5290942af5864250abd60909429f98f5150a7d63d4542cf90f5150b3c43d45429f9835150a7d60d4542b798e5150add6394542ddd465150b7551145429f98c5150a7d63145429f9805150a7d60145429f98f5050a7d63d41429f9875050a7d61d4142ded425050adf6354142b718d5050af76154142bd1855050ade6314142b758c5050af66114142bd5845050b7950141429f98c5050b5e63141429798c5050a7d6314142d758c5050a5d6314142cf90c5050b3c43141429f9845050b7661141429d9845050a7d6114142dd5845050a756114142d7d4e5310a7e6194c429f5865310a7e6094c429f5825310a7f6154c429f1855310a7f6054c429f1815310b5d5314c42bd9845310
  | 46 => 0x43cf90f5150e7e62d45439f58b5150e7e60d45439f5835150f775194543dd5445150e7e62145439f5885150e7e60145439f5805150e7e62d41439f58b5050e7e61d41439f5875050f7b5094143bb9885050eed6214143bd9845050ef56114143de5405050f5f4314143cf90c5050e7e6214143db9885050e6e62141439f5885050f6d62141439b5885050e7e6114143dd9845050e7661141439f5845050f7561141439d5845050ebd62d0c43af5874310ebe60d0c43af5924310f3e5490c43b75924310e9d6490c43d79524310f9e5490c43b758a4310edd6190c43b79824310e7f6550c43afd954310f3f6550c438fd954310ebf6350c43cf94d4310ebf6250c43afd854310ebc6050c43b7d954310f5f6550c4397d954310edf6450c43e7d914310f5e5450c43e79514310edf6250c43b7d854310edc6050c43e7d954310e9f6550c43c7d954310f9f6250c43a7d894310f9e6250c43e75894310f9c6250c43e7d854310e9f6150c43e79854310f9d6150c43e71854310f9f6050c43e79814310f9d6050c43e71814310e9c6050c43e750f5210f9d4394843dbd4a5210e7e61948439f5865210e7e60948439f5825210f9d43548439fd855210e7c61548439fd815210e7c6054843e750c5210f6d5214843bd9845210ef56114843be9805210ef96014843e750f5110f9d4394443ddd465110e7e62944439f58a5110e7e60944439f5825110f9d43544439fd895110e7c62544439fd815110e7c6054443e750c5110eee6214443bb5885110f755114443be9805110ef96014443e750f5010f9d4394043ded425010e7e62940439f58a5010e7e61940439f5865010f9d4354043cfd0d5010f5e4354043cf50d5010f5d4354043c750d5010e7f62540439f1895010e7f61540439f1855010f9d4314043bb9885010eed6214043bd9845010ef56114043de5405010ef661d4f42bd58753d0b5f5394f429f98653d0a7d6194f429f98253d0a7d6094f429fd8553d0a7c6154f429fd8153d0a7c6054f42d754c53d0b5e53d0f42d754f43d0aee62d0f42bb58b43d0abd6590f42cf59643d0b3d5390f42af98a43d0abd6190f42af58243d0b5e5310f42d754c43d0b9d4310f42bb98843d0aed6210f42e798c43d0b9e5310f42cf54c43d0b9d5310f42c754c43d0abe6210f42eb98843d0bad6210f42af58443d0abd6010f42b798f51d0add63d4742b798e51d0add6394742ddd4651d0a7e6394742d798e51d0a5e63947429f58e51d0b5d63947429758e51d0a7e60947429f58251d0a7f63547429f18d51d0b3e4354742cf10d51d0a7f60547429f18151d0b755114742ded4250d0a7e63943429f58e50d0b3e4394342cf10e50d0a7e61943429f58650d0a7f63543429f18d50d0a7f61543429f18550d0ade6314342b758c50d0af66114342bd58450d0b795
  | 47 => 0x38003002c0050000007000000100000000008009000800f00040030024008001c00000000010000001000400b00040040000000000c00900000000000000000000000000000004000000800000480010008003002000100000010004000000400a00180100008009003800e0000012000400400100010008000000000000080140000004000c0030028000001400600000090000001002000f00040000014003001c00000140020010005000801d000c0070000005001c000000c008000400600000000000005003000200080000018001008c0060000002000400f00140010020005001001700940040004009003400300200000000001005800b000000700040000004000000400000040000000007001000a000000600000000008006000000100000000000003001400c00240000004001000c00000180020000004001000000040050020001001c0030048007000400000080030004005000800400040000000004003400d000800000040020010008000000400040150024000000c00b000c00b001c0000004001001800400000060020005002c0090000001000400200140050000000000c000000c0090000001000800000180000034001000800000040010044001000001b00500030004003001c00000680000068001000401600000050000000002001e0000000002402a000800300000010014003000400200040010000000002400d0000005001c0060000001bd98752d0ef561d4b43dbd4a52d0e7e6194b439f58652d0e7e6094b439f58252d0e7f6154b439f18552d0e7f6054b439f18152d0f6d5214b43bb98b51d0eed62d4743ddd4651d0e7e62947439f58a51d0e7e60947439f58251d0e7f62547439f18951d0e7f60547439f18151d0f755114743ded4250d0e7e62943439f58a50d0e7e61943439f58650d0e7f62543439f18950d0e7f61543439f18550d0eee6214343bb58850d0ef66114343bd58450d0f795014343af5974390f3d65d0e43af58b4390ebd61d0e43af9834390edd65d0e43d75974390edd60d0e43bd9875290ef561d4a43dbd4a5290e7e6194a439f5865290e7e6094a439f5825290f5f4354a439fd855290e7c6154a439fd815290e7c6054a43db5485290eee62d4643bb58b5190f7751946439f98a5190e7d62946439f9825190e7d6094643d7d0d5190e7f62546439f1895190e7f60546439f1815190f755114643ded425090f5f43942439f98a5090e7d62942439f9865090e7d6194243cfd0d5090e7f62542439f1895090e7f61542439f1855090eee6214243bb5885090ef66114243bd5845090f795014243b75834350f9f5390d43af5824350f5f43d4943cf90f5250e7e61d49439f5875250e7e60d49439f5835250f6f5294943db5485250e7e61149439f5845250e7e60149439f5805250f5f43d45
  | 48 => 0x250000002000800500000100000004000000100180020008004001c001002800100000090024003000c00d0000000001c00e001c011000400f0028007000000400240030004001002c000000c001000400000040020000003000800a0004000000400200000000000000000000000080000000005000000100080090000003000c003001c0000008002000c00600180000004000000000f007c001001c005000000000000040000003000000000040020048000000c00a000c0010004000001c0010000000000000200180020008009000c00600140000004000002c014000000b000000200040000000000000000b001400100080040008001005c00500040000000000001401000100060000001000000400000000000000000000b0000025005800000100000000003000000000500040014018000000000240000000000004002200080040004012000400000040000014009001800200800000020012002000100040120000002000400b0048001002c001001400200000030044000001c012000000200b80020000005001800400080000000000002800000000010048002000800000000000000008000800200000000004000000000400000000004004003c00000000010014000000400900400090000000002401b0004001001c0070004002000800700240020004001000c000001400d002c001001c02300440010000007001c00300100030000000000c00100280050020003004c00000000000000001000000500040010000000000000200100040000001000c00800080050000001000000c0008003000400600000000000000000400e000c0340010005000400a00080110000006001000500280010008006000800c000400c0004000000000000240000000000001c00a000400f000c005002000200140030000006001800200100080000000000400100180000008000001800000000000018000003800300300030000001000800200180000004000000800000340000018002004c00000000130010008000000000000000004002000000000040030000005000c008004c00100000000018001000000100140000018000005000000080010020004000c00000000060024004006800100000010014000002c00600580090004007000000300580030000004001c000002400300000020008000000c006002c001002802900180000000000000c0000004006000000400040160004007000000600000000010000000000b0008001001c008000000c000000000380020000002000000000400020004000005000e000c00100000090018002000000100000010008000000400200480000004002000000000040100024008001c003002800000040020010002001400100140160008000000c00000180060000002000400d001400a00
  | 49 => 0x20008000400200080030000001000c000000000d00000070014001000c0000004001000c0050000007000000a0054002005400200000020024000001401d0000000001c00000040050000000000c000000c0020028000000000900000070020000000401100000000018018000800000000060020002000000000100030004004000c004002801a000400e00040020000008000c00200140000010002003000000100010004000000000500080050000000005000a003400000140020000001000800e000c003000000000040000028006001000000080050004005000c0030014004000c0100000000001000c00080030000003000c00700000010004007000800100000010000000000c0060008004000c00700000000018000000c00400000000000003001000700000000000001001000300000060004012000800000040050000000000c00200140000004007000000200240120000000003c016000800b00000000004004000000000380010008003000c0050004005000c000000400000080010024002000000d0000002000400800800010000002000000600240010000004001000000080000028000004000000080020000000000000100140030008005000001500000060008000000400000200030028017000800000340000028003005000b00080040028014001400400040000014000001c000000400000200010000000000000300080010004006002c005000400500000020010003000800300400020004000000800200280000000000000000800100000018002000c01600000010034005001c0090008005001c00200040070000000002000a001000000080090004006000000300000000020000003800000000010008004000000d000800200040130004001001c00900000000000002000800d00000020038000000400500200040004005000000a006400900000000004006004000000000000000009000000000000010004003000c004000c004000c000001c009004002e0008002007c00b0010007001800000000080000001000000100080000014001000400000600000004002003000100080090000006001400000000050004000000001200040020000005001c00200000000020001006c010002000100040070004001003800100000050000001001400000240030048003000401f0000000000c00300080020004000000000300000050034000005c001001c0120000005000000400000030000000000c001001c0000034012001c00000080070008002002000700580000000001000c005000400300180000000000000801a000000c000000d0008000002c0040000004000400000200000004011003800200100060004000000c00200000010000009006800e0000000003400100000010004000000000000040
  | 50 => 0xc0000000002000c002000800000080000000000000800f00080000000001001000200000010020000001800600000040008002002400c00040000024000000000100100010020016000001a000c00400040060054003000800f000c000000400e000800500000000008011000c0000000000000000900080000008002000400d00000050030001001800500140010008000002800900000070038000000c0010008016000000d000000200140010004005000c0000020000000000100080030020004000800300040170024011000000a00100010008005002c00400200000004001000000d000000b0000000000000e00080000040005001800d00000000014000007c0010000012000000000200000004000000800200000020000002000000e0008001000c001004400200040070000004000c003008800a000c001000c000000800a0000003002c00700080000004002001800400040000008000000c000002000b0008004001c002004000100100070000001000000f0028001002800d00000010010002001c000000c000000000100000040010008000000100040000004004000800000200030014000000000000b4007000400000500000000000001c0010020000000000c001c000000c012001c008000c000000400700000000008002004000d0000001000001200080050000000000000600340000020005000c002000000800000000010001000000000040000000003000400000000070004000000c001000401200100040004000000400e000c001002c0000010004002400f00040290000005003000000bc01100000080020000001800b0000002000000300140060008002000c002000000800080010008000000000000240030004000002000800000030000002000000600080020008002001c0010014001002000000080030018006002000f0004002008000e001c0110040001000400000080020000000000000300100030010000000000000040000014002000000c00000020044002002400a000000c00140080048003000c00300000020014001001800000040000000005000800500040040000008000000e0000000001000b000000000000020004001005c0030038000000c00f000000500180040008006003c000001c0000000004000400000040000008000000000000000070014004002000500300010020002000800100040000008013000400f0004006000800200000060000006000001a0000000004c0070010002000000100b8003000001200080010004000000401a000000000440000000000001800000500000004004000c00c00080000004005005c00300280080028001000001400200010004001000000a0000000000000300180010004001000c000000000100040000000008000c00000100110
  | 51 => 0x400000040020000004001c001000000000080030014005002400b00040000000004000c00300440000004005000000000000110000000000c00000300020010005001801100000010024000000000700080010020001000c000000400000040000018001000c019000400000140010014000001800a0000000000800200040000000007002800000000060004005001801b0010021002400b00000000004008000000100080030050034002000400000020000000001000100040000004000000000100140010004003002000c000000700100030008006000c006004000100000000004009002c00000000000000003000c000001c0070008001003000200040000000000000c002000400000000000000003000c000001400900040000024017000000700580000010001006000000180000004004001400100000040000008005c0000034000000000000000000004002001000900100000048000000400500000000000000000400000040050004001000000200100070018001000800a000c0000000006001000200080030008002002000600000010004006000000800000060048007000c000000800000180070000000000c00a00000000000003000800300040040090000003800100180050004000004800100080020008000000800700080020000008000400400040000008002005800200340000010001000400000080050008000000c00000000050004000000000c00180000008002001800200840060004002000c007000800400000020010001000800b001c000003400500000130004001000c00d0018004001400000000000038007000000c0000000000001300000020000006000400600000000008003001800000000050004005001400000080040000006000800200040000000008000000c003000000140290004002001400f0010000002000100000000000003000c003003400200100070018004001c009000000c000c001000c00300140030000000000400200000020000002000000b000000c0030006000000100000080010000003c00200000030034005002c001000400a000000900000070008006001000400000200018000001400100000030018017001800000000000000001000000000a0002000800000000050008004000000900b8000000000800000000000001000c00c00000020004004000400b002c0040008006001001700040000004000002400100000000018000002c01b00000000000006002c00100180140010002000c003002c0060018000000800d008400100100090000004001000000040050010003000c0020010002000c001000000000000080004001005c0000024000002c002000c0010008004001c000001800900000000000002000c005002c0010004001000000300040020000
  | 52 => 0x4004001c004000400000180020004005000400e0000008001c004000800000000000004000000000100080010000001000c000000000100140040010000000c0050080000000000000300000000000000800900040000008002001c0080000008000000c00000080008000001400000100070000001001800300000000008003000c0010000002000c00000300000024000000801400400030000000000000200080010024002001c0070000002001c01f00200000000000000c030002400000040010004002000000000100020004001002400200140000000003001000000100030010001000c0050014039000800d00000000014000000000800300000020006000400600000000004000003400100000030024007000c00400080010010008001c0270000010000000000080010008000000000000100020000028001000b001400100080010000003004800b003c0000024000000400000480050000000000000300440010018000002400100300010050001002000300040010010001000000500000020000000001400200000000014001001000d0028000001c00800040010004001002c00000000010028000003400d00040340010005000001a000000000040000000000000400000240000004000001c001000000000400010004001001c007001000000000000004000000c00000040000000000002400100040010000001001c00a0014004000c00c000000700040000004000001800000040000014003000c0020000000003c00200040060004019000800c0008001000400a002400c00280000000000000400000000310000000000001700040060000001007800000000100028000000400c0000003000401100500010008002001800100040090010000000000400040010050000001c00000000010000001001c0000000000000000000000030000002000400000100080000000002800000140040024001000c00500000140000003000000c0008001000c000000000100000030000010001800300000020058001000000000000040008008000000000000010004009000400500180110000006000400c002800100000020000000000000100240000010001000800400240030004003000c001001000800080010000004000000b00040020030000001c0020010005001400100000010000004000000200580020008007000c0060008000000000200080000018000000000d00200020020003000000300000040008004000c000000000000300010004000000800f00100020020005002400000ac00000000030000003001000000040090008002003800000000020004000000000200080000010004000400000100000000005000000100140110000002003c000000000a004400000040060004000000400200280040004000
  | 53 => 0x1075b9b0a35d033f04d08240158893353749f8315ce36e09832352095c269400a0048179a3514039800003b00000e95000000000000fcd920b1c4e000000021e5103000010e31ac200002a5cf5e19d8017e000000016be39fa3848ee58000063e35fc00000003926000000025ab000000000000000000000002438000085452b400000002c6e000000002d9133e14048e3800026d60000098000030be8c30b9698343924000125c1db60e5e0000d670f4e2e9c0000ce591aa3790000000026e60000170112924aa0000000000018480000000014e800010c027e0412a500273491c51dc00ad00000eb49d70000000071982e9a19831c6000000000000e5a0000000102200003718de900003bb438780001ecf050e5c9c0a8151600009f346fc80003b003f6c0000000000000006d686482fa80000c5693f042da511113a00004eb6000000000000e84453895d0000104200011fb0000000000000000000000046f8cc213e30cda3c881d887384412344826f21c224a86a280000000000000007f98000000000000000000115a00012958000121433d116e242a2c3e7d5400026ec35a60000f3080000000974c0001deb00000000123a62c0000000087d031c0000000000000000000000000015c6341467b0a3d98a500000000000086d43de000000000b3031c0000c0210ae0f888cec00000002db2000000006de00000001081874700fe00005e423ac4920000045a158500000000000129d21ea0000f591c6d361000010ad91ac4dfc6c706950179000000000000000187e00000000df436fc365c000165900006bf50bd000012c067e0c8581c700000000000110831dc0c28000126b00001fecbdc0000000081e41759c2e296e0000b8315ac3c229b4ce899a8f42dc05846c20a4c3e823aa8bc4153a4a26000060896f51ada500c0000000000034944c5800031321c840000000193e423c0000000230000000001a53061c000800000080250004000002000400040040008001000000000100040004000000800b0040000000000b000400500500010004001002c00800540010028000000400b0018001000c00000080010008006000001b000c01900000090008009000400000000010004000000000000280000008007001c00900000000008005001c000004400f000000500000000000000000402400240050020004000400000000020004000001c001001800400100020028005000401100280010004014003c003000000100040010000000000000500040000008006001c000000000b000400000000000000000000000000440000000008000c002000000e00000000000014000400000240000050004000c00f002c0050048000002000200300010004006004800800080040000005009000000040010008000000800000000010018004000
  | 54 => 0x1f7275ac0000000260273cce1c000048a80000462a02144047de038e05521f92843ce9d000021f037ecd639b9b21b613e0000074a386207240001063060a0dc4f64800000008a44668a56900000234af405b940580000000155c0000634411f97e5069c62749fb17cc49ee55400f6a2bb00008520f1e27cc20328c44dd1000000000001009194a22d600000e110e60000777800000003f4489b494c912b000055591cd846c150600013d28000459000000001f30000066940000000379a00003991ba800000000000142e00005fe45c300004da80000f81800000000000a5580f932b2000025f0000000083342fc800000003a88000150c108c8550a51800000007b10000000000000000ff3800026d4000068880000000000002e124500003f4c000000000008c38d280a984c149f6099b12391a5a744918c87614e2e394c00015244c44000000000000c9e000094180003a1c9cec00000002c7c000000000002d8a8ce8000000000005388a6f800000000000000000014e0000075e222349640ffc5ec245609c014e0cf58000270079c8c2e13bc4e7226513fc04203f8a50180000000226633180001a870c5848d021323b420680000b2c01cc1862000000010723820104125f89194fd66a4c22b800000006f10d2b8000123400000001a84158213b920ba54200008a041580d0a000058340000000000034d8000060800000000000258143884b9032e000000004184dc1169e00001fd400000000000000000000000000916800002951a285cc01ac9e41000000003570c5c000069502ba800000005604c47189b17766098ef30d6f000000013ee0000363231dcf579552000004b530e0000440e1460000000000009e1c000000000004628cf5209323fe0000000000000009e580001dd0110a9d60106a4741ee494c04b21ef92c9261b4bcb09443af81974ba18b561b8055fc000235c4c3221884440dee0000000000000003fc60000000000000009f20597a7df38226fe876d8000114293151519c2c0ce69d280002703000000000000b5d00000000034122a068600000001ee500000000146037a34449bb4e7b944b2eca12e84b69c5e324e8f044b7a49312d8010818990e0448634c92fd07d1490689282be00000832000118f000034ec54600000e2200000000ece8000000000012299ee94790528800000000000000059c271b0000111800000000000000011580001476458c10c961b173a0000e7580002e3c681d3a2930009f681048f012e041907988000000000001e192b58a0f000000000001266000000000001c180e56865c0000000000000005d01437433c8cf4ff602cc0cdc0000d651e5d000000003450000000000000000000000094d45199d3620a01f6cf76827e3e2226aca8a00002c5a26907f493820a580000000276b152495
  | 55 => 0x73489c04a64fda780856d8000000018610b50000191c000042489160000000000027251b36000000002e24bae0000000242600004ea4bbf00000000296c86689a93588400ce3724d4138c158c1630ae30e28843442b004e4a54387c2c300000000570c000125024085cc8b5ea43600000000726089c1344224cc9e211e4d245e4ce6190bf113a24147409c5902161438b181b78417204302b303c9348493cc2648fa73922550448320f5089277a13a31b07164077b81509aa220f80020e62a5e803a400008558f2544fe8ebcf55a08000000000fa7023c1e7a6b9527d887e0c8277a8a709d3300007a8825a80a400008180fb0000000009e8c2b7000000000944000208c19245dbd353000000008154280000018ba71e80001df4198a75f424f09cd1dae0000cdc80002ae6646135d1abe080e456cb2a80e32ca66dc823c0817387c1b80000000008803d1c000000000007f58c151318000000002ee00000faa6d5c00000000000000000014ef00000000c62000025380000192a23a00000000000000016f000004a29690000091d8a6c800000000000a3280152e3e297040000001ba40000000000024fe29d4000200626d80000000000000005b341d100001294000074a1a903c86655c9bd0000000085ec0001fcc398e00000001e2c454855848d7098620bc1c0c98e9e6a3cd60000000171416383778df712b70c748f2cf46235e4b8a6980a690aa42a8c00009659c090eda3edc50e25db0d765b2cfd212e900007880087800009c2000102b8000000093680000000127658881e38105000024b8000000022f871cc14b0000000029c4000000018ae000081e000000004d1c7a9946910406d60e16a2120000184035a80004ea82cf017900000ab68b84ac40000000079506ed000000000dad0c52067012e1a840000b67000000013938000057c00000001cd6445c07fc90196800000502410e979a3dd414250862449000099fc0000000000000000000000287000013840088000000010b205d03b1a11f0000188832c2611c6d70186373400000001c5b000091e000000004f6e63793dd8000135e0000de1a6a32df677380000bf400000d201e59db00000575c2a6207d0000000000010ed46909dd063f902d42cc30992e60f2000002fa0000069d158a7e1000001a0000046a401200000ae079a4e1a123026780000f158d76000000e827100000cca00000001d15000014b8d2180000a2e8b7882ea3aa3e560000000000000007de800000000a8057b41842236431e000000026f425369a3d14d000005e800006751f06329e982cfcf80000000000000013c90000557c00022cd3a2e00012608cf0000000009538aec07209f0cf2200cc0000000009e0000411e00001810000289e6290000022c291c000123080001868000000027040000000097980
  | 56 => 0x37d42920000000057900004014d4b8c4b0e5c00008851bd00000276c7200faf3cb62990000027d1dee5c60000211f34fa5ae4a0f9f3128261a410fba0de395821d8000194500006498048016a000000000000d8000005380e938e0e299e37149029a9d01a604a8000000000004d180001a1244c40000b10800000008904b121c9f00000000e0d0000455a000125c800038d4000000000000000777c000230a2c9842e500e8acc339e36a400024943cf400001c580840000000036106f137c42b381c20bcf42d26ca8bef19500cd400002491c481958000000000004bda637000025b7000011142b61b04000056a800000004b7a00000000000310e00000001b380000541c95fa4860000000119c0000097200008da80000774130000000000c5200005f89a4142a0000100b01ba00008bc505f000000d600007af00000000000000017eb000000010fc83f63ebe00009be18cc21c40000a49a10220b8464801e82e425d8496400000000000000000000000e7a00003c18000000041b8000000013400001128000044ce14d488ea1780000000000000000000000023080003f3a0000000000009fe0000b83932a4d960001362800036a000007ea800000000000b86133f0000814427180002b560000d461683000000003230ecb4f7e7a9cd9a00d60000306c109082200000000000053700006be10f3800038ce68451d414a4000000011110000473088cc11b800027f655bc78c946a2d86000010f8c600242000065e90461192636c00000003770572800000002ef846852a59b3d0e3e0000efc800029bc604ce2180001cdc00000000101180c7440d328fa4144400003fa00eb4434286cef0830f0000000000000003cb25870d720002082447ac2dc01931f881eb80001dc20000618800d90d636584ae03718dc90000000000000004110000000000003a92654828a9679241e6254242000000000000fbd99ed077e4d480000000000004000001b30000000012c200000000000000000aa46f057cc2ae8047318467c90768000000000002f80a4a298693780001405000093d49c3046e1bba00009450e473e4449b400000000cc866ac000271309b60000000000005fe546c000000033c40f70cd700001ac40000f381f5b2374000023180000000775923f08ce483e25887fe800026f2219c0000c4300006e180000000000021a1141800000000000050a4f24f9c0000cae03863ed2379c2ff80004a400a7c000000004b20000bc39e1c000000000000000000000000001dd13c928444000000000001af00000000137e12dc01926413d0e9dcc603837d13d2848c000198033ca0000000000007400000819988435620e44a0780003b4e8fe8000060f332c5b4137e0000312800012a7a1470000235d0f512e200000000000124d2b36000000000de16b04
  | 57 => 0x1c38bcc4db676e0d3819793e7e51bc975107716da000037e18b500009fdc4f8a6711df29ddc5b509ee12f6410061d1c1e2cea4168b25a6363ba8382c48805e100007978ce2095d00007858996000013f48d3418380002d76204418093b5000000012d800004146000027b000038c87ec4000000000006c90000000042988a5000016c70dba16ac5f08000451a6a68c2c80003fa038e40000000000000000000000301600000000000000000000f018cf1d16825c00000003f6e00012d992d1000044c800000004acc000039280002f9c5ccca3c257e0000298800000003932000000013760c6e2af00000000000000008aa1395200e8b5030f8a3f00000e3c00608f132dc60f40f1800044b075e456c8b99000070e400002f71b82143c000000000003c70479252c18b400000001a3c0b0a9a0937523c74bfc1d150849e71000028640ba9ea02dc08e0c37c10e945d699744cf00003f2888844020cf700000464748800047a671a00f4876426ce000028d08b13dd89e60c920fda08c04078000153b3e7a000016f24622b06166d1b38000347000000000864173e0f285c385f503504eec00019e12eea3fe000025be3d803570000000009ca000000021fe29b86d990488d850b580000a3a00003e0273310bf09fe118279bc0002062413053d800021a90d34000000019764aba1044000165600003434b3f80002a6c56e00000a9c0000546800015da1b4812a03090d5320707ca8af200000000000125a00000000000000025cf4a1423900188bad2104619caf88e2410809b30063177826ba4a8cc8500001b14535000019810a723a9487b000032841808a2324391a42000128c00002b620000000251035c276d0d2607e8000016a0cb288f649de81203920e70434a2ff0000023b47aa2b344f18000000092dc000000043100000000027917686b0c0e980002e46000000000001d2c0000635195306fc0000000090026aa9f1889116a52c5e000029d2793112e00008f7000000000168000000038081ad89cc004f00000000000251e00002acca1e82492f0c338c998049748b882c8000000028c839600000000000060582a6927d0af47a284fb1cfe0e0231ec000209a04bc767111480e12a9e36ac000142111d0000000000000e3692345e7035342804764a4507910000867000025cb209c0000e940000297e8c75093852700005ecd2af99a64f645d4037e8000000085d40fe101800002d89059a7f12a56215c6618691247651b907280000000662400007e10a7c21e83189edb2eae00008519b850b18000000007e300000000000209d1a1667f034d8000000029b0ffd887b000095b40fe8fdd49501c750a7194e264c75148c827ef1caa4ddd2c4122407a4085929c068836c28b28c820000000099ec5758e7100000000ccc257900000000a4b1
  | 58 => 0x462a0000f5aa3f50000000071d80002a7059740d3a627254276f8df304d0145e2dcd02100001a4e0f0800023134bc218ec19d9e330dd000000000000440a0000cee1aaf000000011e88109072477eca9520322b7a5914912a76c00008f8c5f2939b2d1a056c6a2000030fe8cfc238a16023b800001a90000164866a400004e63bda000122292a80e7c01e528b841400003b4c6330000000087d8f39857d00003d313f38000000078344ad80001aa86a8467d800041be558c2e783e92c320e9000000004d3834880001f743460000000018a2000096e87d9035600005e900eb075a3d480000c5a00004cc0000000006f024049d3000019d01be65fc000017ca0ccc4a540001823423a270ce1d94e5471a5bc42ce9f3210321ec03d2800006663ce40cc1e4e2040455d3480c7a2f920000ac70000113430cc0002157000038b02ea0000278235545d88000372c2dfc736953935040000a4c95c5000095545b400001a0c6cbc00011070000489c00002bc000035f48fb95d6217c00000000ac7000000002f3a00e1b4e0000aee80002bfc023c0000000000000000000000029e26443981d8f38100b5800006cf1620000022e00002a026c58d1785980c348a488ad00000e2200007a8800000000000000000002fa167c43b9e664b5091c09ac2374000095e023b000000000000000077b2d9264801b1000000000000b508000479c90fc000000013a677b0000064b333c000000000304e86351cce01c44351a5e408f082f6050c0000e030000164c00000290c49372a5b5c8d6984d3f4c000113d118f073a929023ea20e27e470a8000275d422e000005909b12e7e68c8fae2410197e0000037a78c31161dc472da79200000000ae48c5417362b400000000000000005f1a07200000000000000037ea6aa4327097d376a0000666a5dd000014b40a5a5b14dde000020f86543c0e8050fae984001288cc810a80002e10496cab5876e2b7c63546f58e1122d89018f92055445da00000001e36000054706b71369140260c4c3020702a0a4b0c32f23433e2879a00e8106a4f0a0000000000034f6595c00002d02f9e00000001ebe000008d00a91ede13909f512b01ba54fe625a08139aa41e92009cff700000000518c38318f815d045988cb9aaa000000000001b290000735400000004878161c0000b7c000087f009d1146000000007c91a1d09b089f84b8154931921608000000000000000f8206132828000000000001bee474c00380004d064f90e78042c105a0000000000000001dac077153f1d0e8090c3d0000000007040001baa4108000000018fb2bea25d8000242e084a63e4bda81c42548000005ba0ea213e05c911ba73610a0413000027f54f328da82ac8000000032900002141141c5fe829a1d1447dc684082a04670000000000000002994
  | 59 => 0xe163d1d99643219097180002038000000000000000087a27385d70b8b00006aec000000000000000000107332d072c800000001c0a360caa41f51300a000016283350182882cd471f4c00000999387000022a6248c000189e01960000000219b33fc84cc09d8667000029240000bd4414c04e4dc600000000000000023f30000000000006dc000063b041c949d3012358039d8812000048c4ed1a6f9087400009140099356e21686be268a34b00ac919e144314ec210cf561c3a41e26b4916f98e71730639131f005744789470c1f1783305e8e84c548a61353c6ac92008ec1337c203c00000001b6c6a9860e00000aac00012bf9f0e00006544000026545b2000000009572d4e577120184e70ffe82ed32c0790153a2a7c0fd00002c143504f029d0400000001207889600000000000000012b000003dda628203616c8c5c800027bc2cfc30e000039ea4d88cfa800021960000f83a0ba43b20000b0f000000000000000000000000000000000000000554c791e6046f400000001fb6350a92091098f163a4a118800027a2211c97cd3c41ad7107e0ea131c249e00a60000000000000000000c29800016a615dcdff9b8d2e687c2400022fd00008ee8eb012bc267a21308ae0d5e080a28a406700001d7619dc0000d3800007dbcb670298027c52c8f739b1107f20000c90a05d0dc89810000031926fc92049b09117278c8c84da5000041d20f00ee213ee1e2024847be92483f7c000049c8bc10000508867d149b1e4600009581bbc00000298525972f00006ec80d91bfc05dc000051e9ef72af84ef400015d2453a0000a9626b02ddc3a540ce81924c3e000000014073cc80000f09800000000000000082738ec279c00000004dc200007158000000012a923c9ce800003c841a525af1e7661081942700166411ccc6300d9160e5c80b800f7b0bcc00002210000489078e4000277631e2835c00000000fba0000000052100001c80000000032e45ab800000f5000054542740000000063f000000000000567cf53000000000000718264d0000695824620d648806efc2f6a4503cd87948a3d000025ee000041624d91ec058ac81823bb0a2087f479407002e925b88000030000004e4000000003da400004011c2f4f8a0000373863900009ad80000dd716960000e2480001f6600000000000435820ac718894e486a33b400008ee18903c38c3c9590022230d8bfa1c473ecc06b82e282313cca0000def00000cc200013a480000000000000000002a8a3f5c00010c322dc8f74ddd8163000039809db99280000000062f930d0cb072cc0000b590e8259b800000002b240000c3325e34c067e640000b0a40380000fc08afd42841cd0c1b1bb04d5e9b8c8f5045648d032791591f7604022824a14924e31569b550a5905f03d602e0c7f9d7b036a0000000
  | 60 => 0x8a1700ac0913800000000000836c66c07d90000000000000001bfa000000018dd00000ad02ce08dd1f3a00000001bf0000000011a100000000195931580000000611468f0ba5041c00000001f881d740000bc688de00000000a7a80000000861c0000b2a075891ed34f0000007657fcecd1b3c00004a04000049a0000894c00018e000008d6d3a595d93eb07b880000000129800011fe87b12f5c8d440af0c0d278000008f78fbb4334000000000004f8434100000f380be86301239a1fb0efe8b0d0761ab4028c9535026a38e2b466fd0a1b1bec3c545fa03ab910f3e2c97202d312e10b7e6790f8e00ac000022445b60bff203a2da4a29194d02f04f08cbd8000291e93713aa80001a7408780000000000087d0000170113023bb044a038038c46d7ca5b0aad49a2024800009d026f08fa4ae71d8129546128c5ea2b010e25840dad15bb00001c2c3659b350000000079200000c860000000121f220a10343b1013600000bbce6703d90afc32340c783a92abc9ebc29ea2a024ac8abc3360a5f0000263034b9bc931ea44e400000004d425d68d44994b17c48fc8da300000000000070519162e56290499d15740d3082a8e9822310ddc3cf00000a8f15d2705906e83e84f9621644d50c70448e64dd0f21fe800008b6d00d0000008c0000f7316610000000000000000000000000000000000000000023ea3d740e2490d002a0000244cee300002356433881308302676675c0e71cbf25940000edba45e074e9b780e89d5c246c0a650daa32a432267bc3c08000000000000000b3500000000aa50000000073682c09b1b4b3c82b0a35935a3c5c27d00ee100b22fc2d1134615c040cc0000d1380001fd029f800000000000000058c8e73000023451ce182039d40000000000015c8810c4f821512900000000000000000000000019d50994652000010560e1201800000000427821a82ff1f5e24f83ec47ba90090000000000004cb00000000b071fad44c600000001af002f68c4935c0b500000607800016b22fc030f92c18707095e31313078fcb00000600d151579246a6b80ead2496243849d000026bb00006758ecb9c03106e0000833000025c630243d00dcc04226b2006c0000012c59b400025d40b5e0000e97a7ac48664c44ea6a0fc29c800000f78000000036c420b245f4e56185c0000b61113200006658000213c00004bb8ca707686e40000000023847644daa00004bf675d0c848000000063a008b00004f3a1ddcdfc9a7948262fcd0349d8549980000f6c800000004561256800015bc6001372184e000064090f0a7d22c8e447897321b43f8234200001ff8328e3874b55800019700000699a5d522fa071804513034d9a00013b010c51ce8000039100001c66000000000000000000054f080700000000d8625b400000c8810792db1fc
  | 61 => 0x26ec000000012a09a600001af500000000000140a247c881000012120000000000018e544f663386a684c24fe858451231eaa48949a0074518b2358c9b24000021a131400005ed9e743dc26b007e39fc4082e72a4c219feb00000000e8c9b6902a840712b980001b9c84013e39559346245040f402e539ce01885690add081800002f7800048b2000000020110000171124d160c00000000841929a487c18f51a2095c3cea49f907f8c3924b42f0874f22880000000058a95d5000010884efa20f00005ba400000001af08e1807927bc344c3028a599c85161e51f411c8c76029c29f44030afa0ac40c54094800000003ee83b60b7200000000dff1b51000000000001704000036a0c4d0d292ba20000681a57443026f6000000000c2c000099085a40abc000000000bb1b4c00000001c220000714c000000046c4000000000000000000113813da4438464c000053f3fe2877822206e9000015a07d08671337851d525f186843069f781cf0d0f121c318c2a119750000839800001ab0000189878285e5000008a134ba1a61bac7f4492f000000009a50300976400002444000000000008c60a76000000000f54ab38997044483444211b43000092a4599a21d1c8299113d48000217000000000fff3784000096a0fe64a0259880000000240c6cfc5780000352400010a6a06109d60000924a2193a0e73c8240862a0000940d0099c6b327a0d080c600003fae00010709d2935ac5634d8f8000000033711e2800037022aa0dfe96af000016241ae8e5e009a683c451800038f20038c0f829100002d68bc4800000000000dc5a7fa410c8df807118ac12a448b4000000000002cf45a40000000000000961d060000801c0f2000000005178527000000000000000000000000000cc38177000000013cd99e70d2651f80000c2f4ef60000ec48ad500003daccc5892003e27398a588000000083e00000000000000000000e8600009be07c7800000006a8c4259dca4eb2000097b000000000000074800000004d051afa19015cc761000000001b746bb41c680000000257c000067222ee59f4000011c38ea4904e77999c068c99649288000414a00840002738000086d8cca81954ede10840000bef458e09c43381cd7000086a821a07a127c02a58a64a1fa4d66000038f269d4a325174eac97802cce2b2453380002da242c83d1000041800000000000021826070000110b000002a4af30b3e00009da000024991a9c5900f65a5f1000034ac0001f3424ce1e589948ef208900000000000005369b1053d02410a82000000000f81ac2000000006871c9200008d100000d4400000000000000000006ce1c0a4cec405400000004e422944000172c2112646905e9ce44e1a264c2a3a29800001be4efb0baa278809c8ecf9d6923d800000000000135c00008f
  | 62 => 0x52100f0d08872888c1486479200013be80002f2a0000000000036ac32640000d56000000000000000000083700000000000000006528a050000460444220cf33a80000000000000009b2075f8dc721a83cbcde5800009400000fde06d700002c240000000000000003d921f2000000000000ba10000000000013053f8630400000f980000828400000003e9000000000185000000000001758126800010d6915e3daa0b7cdba9240000007ec8810b85000000000000c71052e60185f2262544be4a149d99246000045a000000000bfa71340000aa200007f84d7d1b0607e2000000000000000000090f00000000971d1df0000145c000050e800000007e348b8238f1d262bdc00000000000000115d00004e7834380000bbc000000000001a1719f256dc19309793eda1eb4000000035c400009a10d67271453cc06d800000003854bd08e3406d24748a970000000000000001f9100000000739043329a00000f570fb4340a000000020c314c09e3cffb9e34185c22f000022fc1e1600dce51209e0000592084280001ef093b400000001bc28754f829cd2000091444d18e5202ac835467988bd000016a9263a0e7384c69d40000982476271a46d280001ba00000000000000002b080000b8c40d600000000c2200000de0000147c000071449ad9adc22a257dd39d0000417800000000ed10000904400002bf0000000000009892392264926c00004b5a8a986a8a590058874904e5000039d8000096ba07b42de000000000002a0c29cd035000000009c5401280000000000102820850000000000011132c4c403400006760510000000000000000272d1849c9e08de66c89c89320109a0000dea04b1000000011c20ceb231c000046c00003762001000004742de80019140000018de0000b4c96521c26000072a047915be83d0d99950f3c983a90f180bb33ca294bd1c09d991c9e747c43a82d5253c0b4c00000000eb24e14000000000008b8085600000000000000000000000457400022301b7a85843c38652006c000000025a500006c4c000000000002f540000000000045146428000105e000134d272d00000000e5700004fe00000000127a0000000024e034b000045bc00020e000003d3c12d9b42000038f5388839726de440d273876f4fa24d70000088e3d2688e40000dc800004f84e8d8a112e24000000000000ca6191c46aa7fb0000000096980000000000103700000000682505800000000000000000003adc95000000000000000000000d400cd20000000163820b00000c1486ed3a7297dc0000000037e9284b1d000000000000f8d0ecf00008634000181701a40000000000000000000e580000000094880000fef00001a504dd14dd462839f4cc5227c0fd61e5c4411bab000063f918680004bc0328096c0000000000002320a9100
  | 63 => 0x9163e709e88055059c69f8890a387425c0624ff90000072c91a829808fa4ac241c400007c2340662cc75300004c4877544ef266d000008404460000030e81f80a2021400006b3447d8000000038b8e5c26dc12dc000000019822fb60dc8afd800000000000e2b8f8032be6db826b916919c83f0c1848c91000024cc1d980e627be26e0d4e236e34a2274800020e422c29748775228f16ae60cd1a81cff0cfe000000000000c804ea8000000000000000661000023ec0000b6e9081110200010d78c53000000000001a52000039640000af6000066412b50c9d15124bbc29000fd0000600c00000000000414c5a492882a3a45cc95a15c2464400011bd9a5c00005dec18904c52f3800647468000331897d480105a31da45530b9724b104e0439068088b8155c4f38c99919148243a8c0431dc0000036a85ca820a01920001155800000005ec4d200c751f0e0000152258d018a4b74a21067d19e23164fc29f2726267dfc3e01aff33f425fc2000524241c0000000000000008924ba080000000000088c94b81964429c00000000000405c73d8364000037f012b00002c8c089c88a078c17061c2893c104900004f34c4f96d43e80000078d90c200002e8ce070a03000000000000000000000000000d571c86930c000000000000000bc7278a075e000004d8baf493a00000d80f9f03be442400000000000000109b02fd23ba994427a168a18ce00000000ded11d2555c49d00000000000077d85eb415e381017c000012627a3cc4819aa00006fc4e139e0606b475b400000003b0e94cd2e2000017a087c00000000210015140001886400400011c480001ea0474034f8000000058cc000000027967d0cd3b91013f9c0a386439f95214466505e3033d375800009f6839f0000029c0000000000008e0d99224027d03ac400025823c4c612c58d212441c45c4000000000000624c00021e92f729db8597000000000000f4f82fa4dea49d92f52228000067c06a82783000051c432a8624077018b49610000008800013c7058421fe0e0878a000000000000de5011400009300d23800000000000db78d681c304994f07a5f64d525b94e2587654db43b9c0680d1c0000224800001404610551054d0c82049c65d099c9269000000000f3a1d400004d147a6870d0a941bcc2d4800009907100000143b29ee00000001e4b2d985e48000000000006858b740bac0000650c55e8133460024609f89ef14554000134885be00000000f5c085f1ff631e4000000000008d90d1080001dac000059d80004b0084a01e400000000000000000004a8a400400011e2000000000000ab03b78000048580003a12569886780002b600000ffa800028ae4b78000000020528f94000199700005ad098a000017ec000032d80000d9400006ea000046202b444eb800009b234d4b
  | 64 => 0x430a3c42be4785069a00763cb861ecafe9f4900001ef82979f701bd29394bca0000416200000001a2900003e34000107f10d686b86c68000000018ac0000000000000000c800f005ba50a8000175d0a4c00005828000010e42411bc9e7d00007f60b31a46d2c849d7c10200000cbe3b54173a6aa00008700cdd00003088000090e88b03b7400009c480003b5c9d9c94623901f146aace4183b043627228d351ced36ca3a4018a0a84257272ecb86975913662fa4dc793cf4e8234f091600002f561e1006003fb000000007ca8c4a2eee0000000000000007a652dc95f81c023ef84da23b700001bac0019c9d18163bb81b3926810cc00003cc80003a145090c0a800000007e5c0000b0329b60000ffe2033048c00003aa01c00678000092ba2974f4e0000b7300000000630c13f9ccd4faa45fc48401c3346678c40000000481622cd2ad874e000067dc2560000000092d8f5f9a1c40a60000a4f90d041700158589276524109c153090b2819ec43f536002c1116c1ca458f949c4a5c59d008c260203bc6764eee0000166c0000d7e08444232000000009670000000000000000000166800025752f502f44ef1000025e43d6400014af00000000a1e034c000000008c300000000000036400003c32000129b970e349e41a4d8b90a100000000b50131b1188881849518d9000072f00000f154e620c1808398123b8e64212dc0d6308f454a4f168b8815526bcc9421c1d1ed002a03471c4e382a22e881e98c126e25a8c44da09540124dc81cc00ae43ac76c85a6090432c0000112600004c9073c525106354e2858c40619a6839908c687d3000000008e300001d90100600000d4966c4f6655681ad8a8203388d289cc978b00003bf50b2a12c23f061403899d01000000007831e7600002ca51e6000000000000000255913cc00008e18000000013c44fa800036ee33783c491f50944708c9c9a59a1978717c14d19032b7e0000f75a6d006ae0000df7a65e22b20000000005906406ef44418b9300003b88da4990601020000b3f18491ad68be000002aa19207d2c6ffa55400000000b8180000348000115e1df147d89050ac7800013301c6118180000a281aa0f2b849d00003328000161235d49d890dd896600005689319a339000000006c80000224e08944a1000041e47f74ad4a70b2db08cc0cc9174026648cf8b010aac22c06d4d3e495e319aa1f2c0000b30402a101087500001fd87714a2297dd000000010b180003d04775c17f119c477e9d7000000001f3200000000000000098007930000494600000000efe000053d13639a9525923b2800000004bf065dc00023043c34576019c87da3e8e71f508a241b0786849869f8000000000000000000323200007538000391c69f026184ce2fa20000fb700001e7c5fa4bcf1e1e11d860c125d046b0
  | 65 => 0x4403fc885a01f714185c6c0000eef200805b12d00d7400000e94ac520921bd862ec1db9e9438b0000021584fd2250671c5a080000000000021389f3000000000000000000000000000000000057ac6c380000000108c00000001d9c36c0000000000000000000138b045a9be80000d491f5c7fe50021a4e22e4425428f9fa8000000000001c771be08ef000014564ef83568f9400001c280000d0096eb3d6600008f204a400000000b4e077400003c200f0a08940f88a38546176947ce000065416a9000000000001d484d5a6a80d8788234f2a89c4000090f386a90080209a5f142e0000000204600000000000030d32a80000a8f272c00005bf40000fad30347d280002115039600000000ba900009d8c540896508ca17281dd814a0000000019b8c0c45188db4d5e800038ac5fb40cb800000001b6cc2d0000000021e5095051c49662e4473a8290334005152ef1fa514d4000000000002df80000050093d33e276080000000000040d85eb10f230c67df40da165115c23f711d8000049780000e8e80000000897857f80003f60000064326be3b6a000023f0000000000000000aaa2a60820c00014534d8c00007168000000000000f8093f0500542800012aa337e0000d161827313887b00001c28000000000919b15412c00006ec04720a90304d119000031cc9a340001547077c0000daa800000005d5000000004244691037da3940000435400009fc000027593d69c6f4c980000000000000001150a91125c331a0000d818000000050680001b920000998c8f80e36184000013a126d900002384f318c650040309412a9e09298e00009c1a6cf482a3a48b4706d115163004cf188f745ee00008fd87e63da23934000000021600000000000000009cdc00000003fe827109c080000000509400022d7000074583db11d6219207203e32464339400010691fd3437a000133200001038000135893502b502388bc101be0d0a4bd108d8795109e052000021c100006470000255614de59100000000103e0000e7480000000000000000000514874d3171431173c2c606549d2202145f58bba000036123e20b14800000003b20000000000008bf86ca93c5000086c906ca0fb000000000001e370b82000000015d415200acc000075000008bb000020a235ce0000000000008d0000045000000000000000000000000157c000253b469e00000000c7d2da400000cd8b0800000f742400cb400005b7116e879e25886ef81f18cad386e064537904fe07147e2d07f023530c2000000000001fee0000f528000120691b89e414b5025c000085b0000265c41e8c669f2e232a9a1104a215d4e7a5f48fc5060747b83ef4000000000000000f06000000004be0000085316f400003e0875d2dd47a000001a3440a800013e9800023fa0f149a017bf0a260454
  | 66 => 0x1325800000001c0811089ef326a14a913b000036745e8c00000000000000000000004fd20000000139d00003498baa8000369a0000dfc0000333e89ac0000f9b00008d3000000000000028ce7c847722380000000219d226072bcd3700000000657439c9fb22960000000000000000180c00011b40000519800000000000787d15892c50f720000fd380003f563d49094800020d01264dcf800000000000000000000000000000000000000000000138c00002174000000027a86ad800000002eb60000000000003d83f440000000000077e848a06e612f00aec5b805cd2ae26eb43459eb0396e404cccd8e2147145335121000023f4397400013d5000080fcb768816000000000cf80004c40000107191b81ee67b280001c4a000006e000000000094000000000000c42000000000000000000000027e84adc71b0a0815cc09a800003c9a121183468540000f2a4b162f98c5f00f12a805b3cda7826d07785bfc00004cc26e63cb85c692324ab452e825c0000000000000870000000000002a8259206548c14fc110a6453c92306cb0b433bb0460cba1000000003f60b9b91e52b2885c40171b2e0000189d1eb80001d7a000045485511e305ae87a0097333680000b4c0b750024168452f1f4421184520166965036760000de88000201800000d10000491600009480aed3b2a000082d9dd92de600003d50000054406a91da8b511d5a07f800000000000889cf69a063000037a004292a53ab65fcc49314d8176e4e80034a5d9314653ec20e258900008a253a88d18000056940001111434e8a181579600272c0ca529422ee2c820000302800000000000000000048f493f0f639dcd0000000000021d24a860000000223421626d00bda25e23dd042ec51b1c60339231b4d3d109b000080f40b1075c42380000e70800000008b0000000000000794093d80001918000130280000000754506502600d748f88000000011e0000070627b02564288418d1e53209e00000001d6601e87504fab199144f23fc4784959a4f3e000139190970c883dd806511df1b329b9d09b986a2db6000061e85d11af225c400000004aa60060ba389301e6c51543e70000000057d875727b600000000ef280000000000066d8000000000000000000091285b00001bda0000000000025e4408800000000c9732b046f00001f591f1c00000000000000044d0ba91ee40dee16e800000001d3e33f87230c0f1a7a00000000000000006b53b80e48148402f0000192e10c680c05dd00003df027646398ab1000000013690000000052353df21b72fde6ae80461962379e3b0c0ca19e0000000003872794208e740852b00000b5a374c5c10000000000011748354000009ec21c000000009db483c8bd929060000efc023213fa4e780000000000000007e713ec00000000a300000
  | 67 => 0xc000000001f7835c000076ac68e805b00000000000000000008ad80000000149a000000000000b681fb4fcb000000001d20000033e00006224d9b800007da0000bed0de500f6576c8250a2543be000043702d718dc4a8878b8000407281383e98619322095a0f7b17c300006350cde939719ca1efc000000016a405941019333456a00fc0000565000000000000000101400006698e663aca68e8225241c162c075d1300ca1062e0000a8588cc1afc8d1c00008cd359249a92e18000309867a4620120a2ce638f0ed483ec48e4000000000001ae63af8000000020de01a92c789b62e041348000000000008ca077a252547d6000139221a831ae3e5ce8f258700008a58000162000000bcc000232f073400012759523437044580000f5600000734000000000003678ce096f900008e9c06a8000000099dc59600000000000097e80000000000076696894f944554bd0057110e8728067e800000007d945280d8c0b6c11a4dea9402439e62a05f70ccc14c6792809aa2e3139e4db917c8f7106f22f7424a08d023301f3c145800009f48ad08551b6d0000000074197970b4023d487789543aee2708f49074f2c4e4a80e630887368a6cac0000000292e000078780002ccc46dc658000026447f340001da246ca7f900001dc10000000120389c500000000dd0000046d00be400010b500004e507808ee8215e3dd0747891e2c2a3c285e18000258000000000b8a3c3016289dc94501eee72949b28000291800011f819da248e000069b80711b665ce056e000026980000fe4000000006c885ae266c195c8768fe9079237143b785e903c625be8dc0e4d06f433be97253af0d810000000000017bc0000831c0001efd16be732800000000f48916c0001e554ba2004006410572b422350353150916685660b1195e200000000f8110430e9292ecab725bf39101f70eaaa17c3e3a0000b8b851132f4748c5f6a2d6000000000000000000082a41612466240e84f490480001b30000067a800013c4822c21d83de0736140cd7786ab19dc6f5c00000003d2081291ea1521000058681751bce08f617c5040800012560f1069200000000000127400002a4c0001207170b0000000000000000000024cc49112429cc00004099a6726bc00003ef0000000097ac000206d00000000000171c0000969c0001ee34d16000000024f8093015bcb32a75735323b506bd81021dbe000000001d43c4400000000000000072ad288a39537be00003d986780e3251fd0e5a67c055a4ffccc304ad45a00001287a027000021542de8b74410432ac88aa3db2bde424cae698240c644778e011f463700013060c044e0000000000000001aca4d0c3e4000000000000340800038a000000000782297c625cd5c024a1d04004d1b025b200006598f9c800013e4149400000000000041
  | 68 => 0x1c49903831b7223fcb49814c11da7ac413d22771c4a09a505689843a1684042d819b1276c00000001b7c000058d8d570f044fe43a0000000004846507400024bd3ef8000000009c7484a6ab0c69000b00005ac43c7003e40f01319210898f218c6fccd8a0000413895e86b621f3000089b8000000000005b9c00000002ebc3b18000118c2d0457a8cd20067000074d08729854000023980c40174000042dc5fc22fb0806723d281120c06180000d2f1e3e420865f0c3581e6059290353771d1c11ce8c9cd1b9672298c6878000141b00000000bb72393481840c4cef17e200002ec8104800039c40000c640e060000502c0000000269e1738e58a17615f20000ce30c4522e2780ce2a92142de0962800000000cc454a04ba17530d920000774800000009224000188f459c19140b214bb000064d918100000000996c812079830182288b32083b36001f34d409d8b31228d4c852000000008b0933a1d731efe7b34bc89d0800d88f093c49632277459a86c497d843744b65379854e4d32000043e80000b4a9e2cba212ce3a6e000071000000000000000011c5062c8c8c00006ce0000000000000000000000057d80001fd60000000196a40ec000047f071643781371236000a002e00000001c124c0260a0000000028ce45d85c017133de40dd00002529211000000000000000074f49a2139c495675886f90d8e383e0000000000028024588aca9929000000004b4973c02d235a40c59582145a8f293a2000003f20000f4289f72f58000000005fc0000000000008a607ee0001374165b0000791400004f745147ccc000017c20580000f1a9bb73ee21da1356000047246d4865a92dc0dd80000b3d9d4622e8000082a8f844cd47d490b41c7c00000000cb3839c44f08d2c0001c4f1a629f90e568000323e48590740abe011677fc0000cec1e682ea01960fb62bc25464bfe9f8629e254d04ab19224030951c089213932600468c3895cf2b0000000002515000000010e70cc01cd881b0742a443285072d4f2017162daa000072fa3994e903104b9e930f00000000d391c7b0000404854695cb00001928000209900004a7d1742695477235d50d2000024f25e30db513642c947a2cef49763348c1888e2e2546076a309c1fe8000324a3f1860907c7054e19bc000001e000057b03ea02132d8c5a14e2a123c28ec4274b17270742d609708178000044c19353a7264a0c7e2b0cf191f870504656c7b327720a86031ceab9a964c1a72849001b261e74905804e140034762d6c29187b52e5200013330a59166e722cdf3823e05c62c18b609e9d0a0457e91c107560000000000022d200004f6c3e80d8f257a2c08000000000007c3c0001cd300001d7922c16bc3d6800002a58000143e000082881203b48000000000003918000009900004e3c00001a894f
  | 69 => 0x7b3bc00714129959323ce1ac8a672780180a00f007b0ddf27ca7b5cbe31d42481089743a916c212f469a518b006e0000000077303e1264e8fe46df800000000000f670000172e0001192800032de2224cc71d2e440211752760000499600008f309d10000770c0b00c1700000000ac4800000000000216a4c6000057403fe1d6300000000dbd18ba1c7c8f60000000003aa0000e60800000000000000134908524fdcb2e1ae34fca2b004af106b33b696509c69f1743d68be8690198f01689fd8f3c81af000009d000012d63fe64f981b0279c0c360a78000000049f42d553282679387a9e68d0d00000000791800016132e7293292b38a6b000028f89fd000016026810e5a10dc000000006e6a693000056bd0ac0f652074859c000145b197c000065c89da000019e400000001db01d30c5c192f06606328000000042e655882ef87ac444a00013dc93d3469c0000000000000007694d9388ca405c0000fee00000000942109a0eb032fc1038aa119124a7e6b513c89b790f0017dc3c5936626ae7dcc85695a4430c09d400009ec4cde117c3b01ab315ca00000000f902f841ff4000000006d826980001a2816de46080161917000027b400000001de29ccc00000003ad4864c46e1f08072a2a01278a6073be6007cc16140d2e2239a487585e84bb00000e700000000000000000000226a2c8c68987353a989398dce13601cae1c9929903ea39ec37a8c9524a006f6398c000243b46e42cc414e0000067e307c33193ac08020000e9006c61e587f7c000000021c22858704166024566864f7000000cea8d8c00010701ae0370c9171ecc1ff43bcc5c70f5400c822004e022154cb818250d5843e02a28761012907603327960fa814ff06ec000104f8f322fdc57c000017dc0416473921e9f800d0449613c68ca22efa2240c8a0f6714780000000000000000000000000000000608d6a899c182800001b09f3c2b18000000001421ec299f471a8a3711d47f6c0000e9900002a94d90a0173c2e3e3000005a7496000000001a7f0a2c8e2c4ce97e600007790caa88c800000000c4b1f1b3e20958c5aa0e291ef81061001800026be7f1d31d00003a0a0000642000032d80000a899b1e00001a5800012f020884d28a0a90f4369c841c83aa1c5000061cd1b79d4a4b3a02d803f1a6f00006a502478000130a00005119143447e0000f6a000025660000134000034c27224ddb235839be28a906085db33261229162805d0b840d3c03a07d615140c2c251a7f936469298977175f335a1a3c47a1766450e62991060000244065300000000000027a10cf863401de23800001ae633fe74691db000000004f7470480003e148b18a1c80000000000021f9d56000000006e78000000032680000c51000000000001c980b2e28210009e013856164897d867e0a1a57
  | 70 => 0xead113128000008e2115486c024947ee42609cbe255874006a6000005240000000000000008f000000000000052788740000418800003af8ba71f700e4cfc6210a4e34706d0858c2900005244842058b262e3c30c3a926c00000000a5497e11ef247440488000000000009ec800000004b3c00027d60000597d15c8000000007c8000168c2c729504dd18000000000000002266076478e80002132000000011959490063c0fe8c8023561f28979800000004bd800000000db7000087d40000cc124208d00eb389460000000096404d300000000f440d9310526d70eff000000000000ad00000465c0000000000000000000c05075816365f0073fa475129620a8ec60000000085f47b790ca3d5063cccfd892d4cac8f64beb9bae4fb6008800018140000000045b860e24ee39287899bc10000000006691f24b0a6e207620000027a579c8a78000045401d4a1391bf45660000701860a08e00000000000045ea0000b1e24e30c7001003069d7e14269e40a7d1fba1e3c7df800019f918e8181017d89b91b226bf800000000804508cf7a0000351054d40000000000053108a68c2b16720000f681e8600000000000000000001ebcc0e800000000c6c77080002dc80000d0725d0397a99b80001c9c4d860000000107e485a000000013281b3400000000a392c101658000161d00002d947e2800000003da8000224d000063c0dcf00003a9e0ad49df1f5300000000543000000001ff8000000000000000a0400001e34946899c192b00000000cb493742f9656448d796923b5e10a084d11bb3b0c00000001b1a00f03c9c73784f50000000096680000000000000024e10000000000016b500005010000000000000000000000000008d9800000000000000048b998800003560191928700000000000000000000000b02a51600003e2c00000004e3e5ea4e681d0d0000000067c1cc23ec419ed25794581846765874e9b3600004ba0a0b21b33a7e00000001ddb11c600000000000478c7ed123f8df104dc33c8fb900431b946e605f903cc0fc400000ac000000009984d12935600006b7d1be03e50000000000027090000000000000002ed40000e988c7e00002840d35890d0af07a24bab0cc9000052f10e4087f34180000000043c25ea148915f80002512000017480000000000120ca47700003ec0000016e411c0dd43f718464abc17586308ea94f2e7a7818194173d0685592e11ef54f6a30f0e12236900a818f0f9602e8432a246c26b000000000000e7280001d8e7874a9992130000000098920f304de528526980003bea7130000000038a4000098399a8000088280000000081e00000000000000000000000a0400000000000000000000000000173b4dfe1b500000ef548aa47f86dd9b0b39f80000000211207106aa014489752da63c7c6d911
  | 71 => 0x24b3496219400000004dc47ff800000000dd4531491d0efa20f03f90b48a747448a33209a8a6651a7c95d813226eb306e1fc80de9ac50956803019d1da6000200000000a99152602ac00004c700000000000113a0000385800008bf1c743d0d064a41a00be30a8f50a3614ae461b108d02bd3afe7bcced98810106a6e5000003aa490e008c081993226087bbd37881f30000000099891a500000000000148931a0970041b02cf00000000ba28a661cd40c44000017f1954799c00000000d0c0000000000000008774000000000000000bd500003c1c2d006fd00000000567400000000f1a00001210ab71a347f68bbb00000000299400019b814a41aa874e277e37728b98434850a2cd251000001e4d000033a0d32000000000b507fc96df00000000bc5187e457a0000000000000000000aa8855700722aec44c16814d0a49c8000126012023464000000000000000000188125763a38000124f37d42ae0f408df6343e09140000bcb17e054000000000000000000000000000000012a923803936689000002a9203e438c0cf25a32096935902f0171016214d8bf60b9000004f4800011d51a721020000079f367c7cf800000000000101800000002054000000023a23902000000000004f420000bff8000000044c5098854919a000006108fa31f0c6a44b5ba3203b2835dcb079ba942c48c193298a4800003138b6b00ed020c0b6cadc9ba12e7c56d800019c81cce0ad85f39e2336f646203c415ee079e1f90bb11f1f400a76fd31da3fe4b2253c06f31e7b1f983368deea463113c00007a4000000001bf8483919900001368000080d0a3a000072d169d00000000f6c1edc3d72893cb1f80000eec6850c41a0ef3780000112d27e3274c2e90ed613fc368e6954c28880e07dc78a0755800000000000be816034eea000084917b2359681945a1272f4c543f8c7de1fa132225c6809b9b7417721ca0a979184057294f00000ce221b28b0402592622dbc000000000000496000000018984fb2000000000000000634cdc19db125ca04950f71b1d46d6000027900000db220f400022ac45080000766000034f0000041f01a14666486c00019834406346c0000000051a3b0061225062198211c45d9ae929fc0000000199a455c79e07f123d6207e0bc41e801f840c8929d07715870fee02f8000094d47ee165077f884a0000000030e8000133404785db1b5e3eee2a8c00018560000368416880003e18604000000000000429400020c22a1a00006ac80004e2c16dc000103e000000013f0000000009824000126e0d580000000000000003b691c2a4520000865000018e24d681760abb94c837748a9c282000034e6538c4e480000000778c73e23ff2a4a90c0f7820fa127034b00621aa52f0a1a243520bc545c831ac6c400980ab4126cab925340d668
  | 72 => 0xb7b9f8900000000000000000000000deda32c1f40688c0b5857b00000000ffd094721f89e7800025120000000121596b63c7a3a5c00000ea00000000fdf800049004fa8a840e4526e03eacd05887837ee40681fa80000000398848a95ae46ae6358e649d611fb267d102784fc023e0d10f7e0d0013503ad0000000000000d14d1f9ebb310444dcabb12b5081695201eb8cc72f8a4db4d5ca1e201fe8910e05a6c20b6a623084588052a4087e0c1594942e2a000032111a02ee07620000000049c09b2816422990000668c1ea00163860250083287b82c126c14000000027e63ab0662055c1ed28920cdd9cfa000000000000000000098450149ade000000000000a7c092602746458a0a0000000106c0ab92444000000018802e1e177800019633be07430000177f2d1e0000000000039b07a34358a045227c0cacf7f887c14f6231c52a800004b020e0400800036301d9d2968a27148a55f51778c94074626b0acca41d47c2400109585fb00000000ada800000009109034084116fa0f60afa142c0000963800020d4135a9ec4f948b0e0000882121000004d560000188000000000000bea8000000027ec83100001eaa0000de280003dbe0c91020259b2a22000047c812b0de45a987f8000023640aa00001fef00000000371000002449424f7d8000390c00000000000340c7c98000078a0000000000000004e52000101ba469348a1ea0cbf800000001f800000000054a195c07405d2000034bce678727123800000000f5f000000013bd11360dfe3808000000045983ea53d500000000164c00000000000000000000000b6231a472715042f605204000065148ca16b927e8d0200003e68ab2815d301e53a898d000008aa78fd11621161e009af4000102e000000006df24ee00000adc0000000054c000000000003aa6000095700001c3600000000000000000007eb154d2cee2a980000588000057046a7a3cf391a9b7ce480000365000008ab1dbb000065580000edc287e4ea00000000176a2c350af825049c800013da1d754e500000acba68600005d700000000000034a0836925200004cd4000240414ee808815c06a53e5a2c4454a000009c87b0d055800000002098d7b9f6c143486480001f3a0000736d35900000000949c000027c49385ca80c6a39a465a76780001fae000080f800002633b9e0000000000034040000bfd8eeb00003e4d2561a6c094e000027781133ed6000063e02940000293cdb823e61966378c6d79c65000000002ed12702d7022acb3e069e00005fdd2b294b900006ebd309927528388fec0001e56000000001f980b508649c3c64a96bf00000001367002929b447f0196a4d000fa049c3db80001f040000000000031be61b8000000000000000a4580002e9a0000a438000000068b914800002d3400000001
  | 73 => 0xb64396c0000a4d00000f0a473c00026a44e805edc98c8ba200008dcc3b18d94000001149c78e0d00006ce4000000000000000de6000028f20000000000000002fe4000000007a20000d0c23240b069cfcd4d98524df60cc43da08702b5a206824714a6499c451c00000001c382b3d03a9e8e13f29bdc00009ea00007350fcc03d600001198000204c491493a47259537421094e8000000000006174e0a1fe919ac4aac3b900000fe00000000000044e687b4c9d80001dca323c0001a3500004c300000000000000000001fbd228856581241b68000099512138000000000000000ec23e8a00000000000493e0000555800000007f2c5658edd2b7430202f00000000000000000000196274f87ac0d9f0000000027c8e6500006b6c00e80000000000041888c633420000000000000000bb00000347407400011340d30347a8dd800020bf0000000000000004e649d590f301db4a4600013200544000051391ef8fdf0000289800024e200000000640800000004bf88871c1944de000000013b048c080b4000000014da60051f69aec0000539c000000000000000477a44d029279f0248a1e8045c99c80000df80000000000016da00005d18d96a521000000013a992a90000088c00010080000000046d04302a5a25f8dc3a03b00005438ce71e152a067209173800000000000f0d9d40447c3b2400022100000000000015a7000047ccfdd80003b303f20e0624344f7475385f50f1122344410fb3a6bc33a63df8906933404880d9850697610a625d9d3e7869c154e0001223126f44d252f52160d4831969210fc900af2df030a0e5190233e4647a497c8000136471e093223b2172c86e416585f640b4485c000000000007c485e38000475a000000017d3000037bc00006bd0ae80001282a761046000000db999902d02c7477c26621f80020d19a0000000059e09470d723eea32ecabc000036b600000000000000013b00000000105c6df4981000000000cd847995b436028d501f1026a00002eacad916254cf4792012f9fc94d02793c000278139e82020d430d9d000000006d60f830ad2593c0000db4195e72a84ca8ddc2d2e0001185800000000000ce190c704d6811c00000003a580000e53168400000000db19fc600001eac0001cee443c5d3c4b50af5132c6bd0000000000002e6800000001f845c90000015900006fc800000002ed05254c8e81a300000000509000032367364e1b00002c68943100c840a4e682b2800006141c5e9a7d22384b20fd4000132b800014e466ccb4580004e449b60285a2f009d420e90ba07bc45a25ab47e0a15e00000000000000025f8992517f844c4e3a2c5c7d601e5023a4f9c92f9905000060e43a1a5f004d881dcd6d0f304bdc63bc000000000000000000000038e04e392d21dad0e741dd400000000438
  | 74 => 0x5bf83f780000000000000012ed35820000000226c00007be9005800000000000bf21f190000990ca6021a000002c5089f8f9e45880000f6121c944a20000000070406e6000075900002a0412580d297ba00f400000000000140096613ee854649ba6e103bf03f0257c00001a8246700009c0800022a500000eac5b8800000002efc00022a20000000111225f418c45ef420e9f9e250c0ab0ae99e124f482b68ee418f600007d900000000000070ccb93227500da000000011a734728548dd20000305a64b0bd28000277000011350db507e467980e78eaf4cbe4ac4be6800000008fbc41985290f46081cd2c95844fae0000000000000009c98ec726a000000000a420000000000000001e9b00000000000035e00004a2c25800004cce7aa4160104d01ba0000c58856b12aa3ff00000eed00000000b540c03000081c40001e9502ce0da856b2735273e55c00000a5804ce5598000141848500000000265a317853acdbfa41e443624b0000220037ca9818a490d8b1c6e000018e838c18c80000c3b17f11c2e970412926f03c081214a28907b44568c3d352859930de5a6c3829c7e3b148fc400020341e8c3fd000017361d6c768400025a64c6a39108ea0bde10284400aa58afe3bee7ff400000004c520ae8362272a013e3a309d2944a1b88335c92a9a5d000093fc000244c421c0000000000000004e9c000049f000000000000000000000012000000000000008bc0000227a8861130a57d41407a8c0000f034536000000000700e205e9800023410f74000097f9c320cd6146468a86da000033383be07f6425a351809c0f642d2850c00000000000029b8000255c430a8ca4ba50000419600000000ac800005db00000f6d0000459037a80001fec0860000000000000000000000014307e8000023312d1053311cf0000000075402cf173100006fb4eac0000000000013e0123f1a961f0c000103b2904322497d000000000d047e80000000097580001e7745ec0000000228542709c3000020b600003fd4b038000000000002268000419c2fdc0001d211f448fe0000000000007ab400027ab1fda3cc4aaa0000085c6f4d30d0dd9445e0000c5f8000025063a4d31034d071c2850728074b006a58a098a846a0608000008d80002d886d8096903e042b22a1c74c14e9192c5fd8faa11a34c6e000075c15644c7a00000000000000000000001faa1252261cbe3836f03ea8610b03000035308684a36a056103a9de0db210101d12000051d000009da8341205116d182a704c0cd25ae48829da44c4179f01b82c10a15983500009c64000181b125e17307f09acf42aa9d3c53ca40900000000000000000009728e128bbd36200b989a716b00000000030a8000472c76e502c9864058600000000b7714686d9c1f320f6202268805bb200f36d657a538e
  | 75 => 0x134b0000000005289e40000000000012cc1e5a000000000001656947c000047f33fa4b0416500004aa299f93c219b514d02794142267800002d8ca5a0000012a037c0001abf247a0000000119d1d6a0000cd10000000018180000000321800009088fca00000000000276a06927da898400001e6a00009d89be13d829fa80000000156a0001313000000003b8c0401d323e700fd000024d50b76000100f1c5a05b0000121c0c0025d6000000000000000967071c046d000018c000020fd2e6a60f000000001e046a7c9108ce9022e3e4499b95123ae44434df21b6c17d64668000000040545f6400000000000967cf050ddb0976000124924f400006934c5389bd0e104c70000000015b06f185fa948821a2000000000004114883530a8ee037b800000000000000000000000000230e7f8819a076600000440c089bfb00000000a99268e32bc00001bb9242000068340000b46137c2f4c35388d60000372c46d84cf2c2c04bd29c8b89304400000000000000000000001d5f3c5e39e8afe11db00003f488fc9e2534c63d749489e474ea03bd84ee0000307414cd37b21c329e47ed47b7023601840000000114906c600009ff000000002ff4e4a23454bce1b142f909dd12a20000d8902f5040076a0636000018880000000217f251a0fe060e89490000000000022171af426340001f182430797cb0ba1180c4a000022f119e00000000e1e00000000000000010f1000059c539f1fde47460000000000000003f5017e0000161699a40000e7928ee0000efe22820000000002c00e5163c0000000000000001abcb9400001c4662b8000062800001b0c9d7879406800000000112a3c4e0001262121500008ff03d491cc000000000000000287446c400002c74bf860212da8000347c0db400000b900000000000000000002f5c8a800fc4260457c5030e9b3f341fc4a3110591ed8915d02f95433b984b544ac96a20000337c0000b3a36e200009e5000023802d3c000007717880000deb00003b541d44ea2193e075c1e70346800000000000d7d800000009884c3a264e1a4625f00000928000000004059ad100007f549d68aee215200000000000315464b431998a114fe3ea000009023ed072e800014a000007eb00001a713516153cbc79da002100820f12179b063028c81de90c4437c84bc6400683000000007cb000004184374abd80002114740c000000008824e880470e100bc4508098505121de085180001c97000000000000000000094984571cde000000002860000415c000000002763f466c9400011670b92000000021b018845bb000013ef246e93a8de38e3f4f5094512bb9e10148060c821c9a66387e67d93c30f6240b625ac453a7a04fcc44b0d6620a832802a2057991060022759014096012bc062dc2ea8b7940107344832248f000
  | 76 => 0x8e00002279d2600000000947858d113e99acd53a3912ff013cccf7111b028283e535a9459412009846391b3140a48c04d001e4246b2700400011b0000000000001ba60000631d2ac0028064200005b00bdf328200000000000000000003d313c3357838a020991754d7e8aa1014048202be4f40bfa80000000000000001964b7800000000bca3d220000e6e8000147000000001229000000000001771000000006ad944130ae14a080b00004a36383c04f1ab51cac0000f86a1450e466ed0000000006be00000000b454874000136880000000000049e0afc218075b04c8145c000023649c41748000044a4000005e3e6e0000bd100000e6e63b4f90000001ae53f40000aba00689ab80001e7f00004bc4e4a8000000052b0a268d1046ea141c16e1b9732da3d2c4f0800044aa6280939800045a63e1449f000002fc54c4428a46b10a44018b0c00003ade000000014543948686c000016d0000368cc3480002296640522e9f8e48f82ad01fe124c115812d89f10b7e2f021d0071320b40f3a329937e931f2c9a9878abd16c836ec0000000210508b005346691e080dc22fe839996ca0d7c9618369088f449675492471944445a0000ce284310c7c3140ea58aea2d6600000159d680a6488810901435227600000d98000232842a000020cc0000000073b08df27e89adc0000000284c00001199555030878e00000561217888e0570000007023574000000000004e90a77156923b483c120c04e90000991c000094f028e46f465b07f923889c6000005fa00005aa88b291c61fbc8658a2386e50d2a3cac754026225a04fe4f979af91196000000023a900000000000065a000055a8b2709802d2c853c03080004fb40000000221600000001043a5a9185806980000475429400001ac110c4dae0a4c31190601abe0da0000000000000000000196410bc52940001d110262942c44a800003020000a69941200009091015926314d28000c7d000000000000cf40206464c137d09f97bb064e9ee0c7e93c724025de8e65a3e84dc02a1431b08b2498440a047e97513270000015180da000000010c60f12116a83ac000000000000000929851b3e9e82dcbb99c2131e86bc4e3f80000812403899292b610d804904611c0f371c47b44dba39f388437808e525a10ed28624f8986991462000089326a8000053091678000000000011de80000000270400018701b8469d0445a4f619cc2a84363a1cd00a2829c00008c3000030586b500000000120cbb6873600009b943f3996b264608bcb35a14307a64624000160b361c000000015c8335883dd17980000000206c848800039803b40000000000002e50ee9000000000000000000000001d5535c80003bde000020a9553245e000110a145a294e9e0812a1b73466c0d940000a281eae00001f39fd928be000000
  | 77 => 0x148000000098e43be9a491f541a8c3e5250e4c1c3608a191eda001a000000003c1427c3d081aa93103d6e9f1050f1eb64bbe5ff0bdb07bd25b40b853d3000029da1d3530ba5ef3a6a295cac59568000077248eba12533a464380000000000064e4fab800002ec000000000001864266c000096100001078000000019ba02f4000132411d6435c0f7179d4aae8c5cfe1000000000000000000000000000000000032e647a12d10000305c00009411f90000000010c104f044b8750c000000018045d801ff00263d08000084b1fff0000110c0000000000000000000000000000003280000000019641f21cdc0000000121780004bd200000001fca00000000bbc86d617b800000002712000000000000000000000000000c683eb4000000000000b9060840001a13000045e800010de000008e800008af18a40000bd390f31e6618006de235a045200000000000076c000133a80002f307b144de00000c3c368828f09ff0000000000000000112596895793a1229800002e1800000001fe0996a61b3bce991921902ae14165130c0c000000005d2c0000cb71d3496582eb8c5811800a3d0629ddd36881d6c3662010210c8568126000000008dfcb438000286600000002632431697fc000193a000000000000fee27ea2a383060ac64cd0000062a8000000033500000e51000000000000af10dde7d0800010454a9c449429585670fb00ac4fdc115203724fac6fa9b9d3aec1a812fe800000000000a9e888a01e60000000090c38e21590b4a84a9217a0000ec1a7ae4aa0114c0001035000023948b504bf443e000000021e03226000102480000000000049b9a0800004e1c95322d840de3c7400024b54d4e0001202955d00000001317a68722405030c91a3a513324da00000ed9037882d4c3299dd000067cc3b818ea4e2081707508eb308b61b0400014f9103c000000000000f1e0000e40002f00000000ede825d21ce1de1171177202f47d3473c27c1492260ec7b1a29508a465680dda4f035dc4b9c0d606f629ac1e6903f8b4e00004d640ae123800000000000274d30aa87705c0867a00005ce80000e6400004dec10d911f2ca8000000023d2000070700000753157e078800000002d800f38c4509124a1a98201781c61000017a460ca76642ee374400009b00000826d2f90b84016000010a995b348de46ccbcc873c32f000000002074000080c4ce10de44748844c35c0e6b00003f3c000142d3698172c00009d400004e8d11d9b412f8231187ff20a4261c95913381ba73d38000000024fe1e1a701400009d542f204987bd0000206400000b80d4300000000000146149f2000000000004a0e00006b8800000003bf00000d091c340000ade000002cc00000000de245aa0000a1f1d38126c9a240000000000015c861c21a200001640000000008
  | 78 => 0x18c4c2c00d24441cb843b926425dc3ec67034b1618c53456234c0a187a7000000011f016f226560000f8590fb19c088d40000da00afe0000000000043a2131035b80002bf27c013f70000000000000000000000058f45fd80003506718c000190f0f9298d00000af400005b8400000003604000134d80001a0e59bc0000a153fc0461400000001600326c682800003ba00012dd82d200006e4436800000000184501000002868000000017ad27b888f4c038746449c27603f2800027ac0000fe000000000000036f87ec4a7c1f5c7a0a31c026862c00000000000000008dc907d335e20540001d7a0d5a2be0000190d27989654000000009200000e9580000000000000000001a5c5c89397127112a60000c069bf6165a20240000cd9301c1a480000ce700000000f7f0000330a40e4626800000008b9513280000000645401c05c630ee78ec000171900000a0c000041b04b496b0b38098300009d9115c0000000000000001110000051a000012ad27b09de41dc8451000024240248000204200000001b5d0ed451cc33a007c309e00002f19112000072a0000039900001c68ef90c5612e4965c000251d39f000005860ad304e64a4d327a6d61e942e71316a30734da3d6849a800000002ef800000000000000025a0000164e532cf4d123320d80000e0ba03c181c874000000000000000000000002fc62910fea19343f1e98f0076273017804658b8ea33701441fcc00000002ab6216c33e00fa4288000000000003004000123e80004e14000000000004a7a22e53f08153110c426400004bc07be0000aba800010b800010399c450000000007b93bf00000000aef0000463e24751e184a5000029d0000170a1456985114e1a4a37c00014b020c4726ea52a07838a020000469826aa28b243243f8b0a000000007ea40001ff0186a7310930a4a52c76324cf9da29f486233fc510000001a2701c7c086bf000015b4bf90000336e912cdf59179185a2b50869096319c2868c0001f93269015d8820970900003b900000ab60000489825982e01d8a00011b621d72fce3079242800015de4d4c7a200ba4c202e991e69586000045085a68aa02f901790dc48573000061c83a206a947a095c0b150e6100000000aef8000248827ac5af2180117c16f000026312fd41880523810d285e00009bf816f000014205ff0e1900008bd0aa70d4a40148440a0c908d2ad895300390a5d06dc2db80001d47212895292c9a3da37b231e04911fb3438e333c5b5800000000000000132f000065f50130000124a213800017be00000000a93800000000000000191e1aa4000000025b6000000000000000000000000001c2931c200000000000231a07d00000495155e0001149a6730000973800009cc4af8567821b8000000000012a4a08d4dba834c2280c5e000000012
  | 79 => 0x10b880c45427c849eb9297457c34ed1ef222a0f988d1816d1014000000006c91c0014b44690fce0b211d0861f000018eb21f25bbc0001f6127f01cfc8338b66000062bc07380000556000064c1ec82316000029d9b4843fe641c49221e3036239f8ce684bd388c0df0a39130910a84d34b4f9392124e62348698a3035003ca48f18af2000085701970000000040ac703800046aa00000000000000020f0f3f000000000000d6c00fe44ae000000000000bd8497400000000aaa00007ada3e42c6a1fa4eaea623050a00012bd8c30146a556036688f8000092604228000463600000000f3f00000000a07234923b0000000000cf44b6000038903a1027e53a13e822f21f4a000020d07fa2f5e0000000153e35ba75e068b8000040478840000bec00006ecc54a80000ab0782d29b1b992d0c0000000263f2f08757835a060b186e00000e51d9240962780c2f13e92df4095c83a06d315c40000a4c05ee00002c8868b1fea07b600011d001d9206e06286ea837f44c83598ace02ed1f7e0000126848624468e5c5c784360000252000000003fda4368da590ba000000010ed800000000000719000031b40000000000015ae0000cce80000b2284d40000000091000008e580000cc0247ce4399cc2a200dc11d705a2140e23f0a6b8385148600000000c040bb286fce3900001cee18bcf0000003490055c94a133e18b600000000000000059d842c23f43d8c000000018f729a20000000000000000000000151f0000000067780000000507812193ab404600000000f45040a2e480001c8438400000000053c1694000126900000ef26fa500f974c02b48b2d227a5e52d589b04812879b074c7f98000000001c0000035c93634ad8000106d000045b400004a18000105080bce5c856a00009d688a0165e000000012679f3614a8089094c14c114a6738c00e00001cd099482ca900a3a761c30ce88872486e467d09d944830b60000fbc80000000990916485ea3d2e94112fc9c5d07d655f8e53887317706360a9e26181eb80ce13a90e2a04ee5124ec9824f19067a5932283cd38827f3ce8c023d01a800000f50000000068d87c49316001e9734000000000002a6c000172100001a008db000008b26bd8c5b10b3187644bc829086f4d2c32707f0237d4efe000000013b41d7200004190424492e87c4f368b25356044b8000148537c61f142eea6a2310a000000000002a2e160126da77100000a80eb89042000096651750000000000002e3842f00000000bef94ae2dc67b740001f1e0000000000008aa00009588000000016f68e98283072a00003a2108302784b5436184a094d50b1c37f93808033168e73ed19a83da4c2c32283bd249544e4743caf2882428d816cc8438000091a8e742f98cba1ee061604690d424b181284f2d193f35d65c1400011a84
  | 80 => 0x98e00c60000b929faf0c5c43b0cd3871517601f7cd6c85f8000060fd13e9411345a7b58a7c00662ac029e0eb81296194681e826e982535a000243b988340daa6c813dea13a3d7a4d5055908cf263c47d0efea2b70000000036c10d8213861e100d90df4d109954b34167a22463800ab699700a0a1f4819906493e4a7bb901a8fea02e6466cbff0000136a98c0334000000008958d7915c4000080d8c98a17200a0134438b870f000000006279b93089694c50e600003aa80cbc0000000000047040410fcd3e6a000112ca4882dec0000000000000002f813f119714422039000005532764696c9219dd30e582c4d02c0000000019300001d2d27fa43dc5ed0d64000000008e418410000863884c2422361a766c949183828e0000000000003fca8950016800032922569306000000003cdc00010a030fa10d4ca3000000002918000088d01f606d91bb800000004528000256f00006064cd80d0c134e935cdb110f000000000f8a80001fca00000000d1f0d180000000235d00005f110cc8000000000000001e980e623a80000000000000000d56a5da258e28904540000000071d000000000000937c000000037d013340000000499200000000000145874f13f608a4336c7258032a706000000013901b5922780000d2d176b0134116837d104800001ac09631e6e072822947211ff6000092b8000112d03ec94900ed2571000000006440bc946e200004240fb53c5280340c193844c3a926c
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x862e649483004316b24a4180211bdd9520c0108daeca90600862e645483004316b22a4180218d952610c010c6aa93086008655539843004333294c2180219954a610c010c6ca8b08600863554584300432b29ac2180219554d610c010ccca4b08600866552584300431aaa4c3100219554e6188010ccaa530c400847775586200431aaa2c3100219554d6188010ccaa4b0c400843e74d94200421eba6ca10021179cf65080108bae7b28400843e74994200421eba4ca10021179ce65080108bae7328400847571594200421f3a0ca100210f5d065080108bce6328400845d73194200421ebacc8100210fdd5640801087eed2a0400843d76950200421fbb2a8100210f5d954080108baeb318400861e5498c200430eaa4c61002117dd56308010c3ca8b18400861d5458c200422fbb4a610021175da5308010c3cc9298400861d6494c200422fbb2a610021175d95308010c3cc8a98400861d6454c2004317324a4100218b5925208010c9cc7290400864d639482004317322a4100218b5915208010c9cc6a90400864d63548200431b2a4c2100218d5526108010caca73084008655539842004332a94c2100218d9516108010c6aa8b08400865653584200432aa9ac210021999496108010ccaa4b08400847576d5310042aab9ea988021595cb54c40108eaeda9e200853574d4f10042b2b96a788021c555253c4010e2ca8a9e20087155454f100423abb6a5880214d5d352c4010aaae7a9620087255494b10043a2a9ca588021c995152c4010e4aa8a9620087465354b10043a2a9aa5880211d5da5184010c72cb2a4200863965552100432cb2ca708021965955384010e32a8a9c200847976d4a1004334b2ca5080219a5955284010e54a8a9420087295454a10043a529aa508021d254d52840108f2ed28c200847676d5110042aab9ea888021595cb5444010a6aeb2a2200863765951100431bb2aa8880211d9db5344010a6ae9a9a200856572d4d10042aabaca68802195d965344010e2aa929a20086576554d100438b2a2a688021c555153440108eceda92200853574d4910042aab9ea488021595d65244010ccecb29220087255494910043a2a9ca48802199d955244010e4ca8a9220087255454910043a329aa488021d154d5244010ec4e0a92200863554d81100432aa9ec0880219954b6044010e62a910220087515388110043b0a944088021cc5512044010ea2a6902200876152481100431db2ca8880218ed955444010cb6cb29a200865b6554d100438caa2a6880211e9db5244010ad2eb292200866b659491004335b2aa488021ca9515244010e52a8a92200874a5354910043a4a9aa488021d89c55244010cd2a5b0a200876152d85100423d3b4a288021cc5525144010ea2a728a20087615294510043b0a944288021d85492144010
  | 1 => 0x210422fbaac610821879516308410c3aa8b18420845f7694c210422ebb4a610821879925308410c3ac9298420845f7654c210422ebb2a610821879915308410c3ac8a98420862e649482104316b24a4108219398e5208410c9ac7290420862e645482104316b22a4108219398d5208410c9ac6a904208565715482104333b2a4210821995952108410e4ca890842087255448421043a329a4210821d154d2108410c74a9300420863954980210432d29cc0108219654e6008410cd2a5300420863a54580210431caa2c0108219694d6008410cb2a6b00420866a525802104334a92c010821b848560084108bee6b24a00845c73592500421fba2c7280210f1d16394010c6aa930c8008655539864004332a94c3200211ddd56190010c6aa8b0c8008655535864004332a92c320021879536350010c3aa9b1a800861e5418d400430eaa0c6a0021179da53500108b8ed29a800845e7654d400422e3b2a6a002193d8e5250010c98c7292800864f63549400432631aa4a0021179cf65100108bae7b28800846e72d944004236b96ca20021179ce65100108bae7328800846e729944004236b94ca200211d5c565100108bce6328800845d731944004237390ca200211b5c865100108baeb318800861e5498c400430eaa4c62002117dd56310010c3ca8b18800861d5458c400422fbb4a620021175da53100108beeca98800845d7654c4004236bacc4200218b9526210010c5aa9310800864e539884004326a9cc4200211bdd56210010c5ca8b10800862d54588400432729ac4200219354d62100108deed290800846d76948400432731ca4200219358e52100108deeca90800846d76548400432731aa4200219358d5210010c6aa9308800865653984400432aa9cc2200219994a6110010ccaa5308800863654584400431aaa2c2200219594d6110010caaa6b088008666525844004332a92c2200218d552618c010caaa730c600866552986300423bbaac3180218d551618c010caaa6b0c600866552586300421f3b4a8980210f1da544c01087cecaa2600843c76551300430fb24a69802187192534c010c3ec8a9a600861c6454d3004317b24a4980218b192524c010c5ec8a92600862c64549300421f3a6ca180210f5d3650c0108dce5b28600846d72d94300421f3a4ca180210f5d2650c0108dce5328600846d72994300423ab8aca180210f9d0650c01087ae8328600846e721943004236b90ca180210f5d6640c01087eeab20600843f76950300421ebb4a8180210fdd9540c01087aecaa0600861e6494c300430eb24a61802187991530c010c3ac8a98600846d7598830043172a4c4180218b552620c010c9ca7310600864d539883004237baac4180218b951620c010c5aa8b10600864e535883004326a9ac4180211bdda520c0108daed29060
  | 2 => 0xc4290218d9926114810c6ac9308a40865663984520432ab1cc2290218e9926014810c72c9300a40865a63980520432cb1cc029021179ce65d08108bae732e840845e73197420422eb98cba10211d9c465d08108bce7b2c840845d73d96420422f39ccb21021175ce65908108bce632c840845d73196420423b388cb210211e9c065908108baeb31c840861e5498e420430eaa4c72102117dd56390810c3ca8b1c840861d5458e420422fbb4a721021175da53908108beeca9c840845d7654e420432731ca5210219358e5290810c9cc6a94840864d6354a420422f39ccaa1021175ce65508108bce632a840845d73195420423b388caa10211d5d76150810c6aa9b0a840865553d854204332a96c2a10211d5d46150810c6aa830a8408655531854204332a90c2a1021179ce65108108bae7328840845e73194420422eb98ca210211d9c465108108f4e0328840843e74997320421eba4cb990210f9d065cc81087ae832e640847671197320421f3a6cb190210f5d3658c81087ce932c640843d74996320421f3a0cb190210f5d0658c8108ece232c640847a70196320421ebacc9190210fdd5648c81087eed2a4640843d76952320421fbb2a9190210f5d9548c810c3cc929c640861d6494e320430f322a71902187591538c810c5cc9294640862d6494a3204317322a5190218b591528c81087ce932a640843d74995320421f3a0ca990210f5d0654c8108ece232a640847575d85320431aaa6c2990219554f614c810ccaa5b0a640847575185320431aaa0c2990219554c614c810ccaa430a640843e74994320421eba4ca190210f9d0650c81087ae8328640847671194320423d380ca19021179cf65904108bae7b2c820845d7598e410430f2a4c7208218755263904108beeab1c820861e5458e410430eaa2c72082117dda53904108baed29c820845f7654e410422ebb2a7208219398e5290410c9ac7294820864e6354a4104326b1aa5208219558e5190410cd2a53048208639545824104334a92c1208219654e6010410cd2a5300820863a54580410432ca9ac0208219a549601041087ce9b2c620843d74d96310421ebacc9188210fdd5648c41087eed2a4620843d76952310421fbb2a9188210f5d9548c410c3cc929c620861d6494e310430f322a71882187591538c410c5cc9294620862d6494a3104317322a5188218b591528c410c6ac928c620866952982310432ca9ac1188219a549608c410c72a9300620866952980310431caa2c0188219694d600c410cd2a4b00620866952982210423dbaac1108219a549608841087ce9b28420843d74d94210422f39eca10821175cf65084108f2e0b28420843d75990210421fbaac8108210fdda540841087aed2a0420843f76550210421ebb2a810821175d66308410c3ca9318420861d5498c
  | 3 => 0x526314c108beeca98a60861e6454c530430eb22a6298218b9526214c10c5aa9310a60864d5398853043172a2c4298218b5516214c10c9aa6b10a60861e6498c530430eb24c6298218b9926214c10c5ac9310a60864e639885304317322c4298218b5916214c10c9cc6b10a60863664984530431ab24c2298219998a6114c10ccac5308a608639649805304334b14c0298211b9ca65d0c108dae532e860846e721974304236b90cba18211d9c465d0c108dce532c860846d729964304237390cb218211b5c86590c108ece232c860846e729954304236b94caa18211b9c86550c108dae432a860847671195430428e39aa8a1821471d15350c108dce5328860846d729944304237390ca218211b5c86510c108ece2328860847a70194430428eb9ca821821475d25310c10a3eeaa18860851d7550c430430fb2a8621821875954310c10c3ca931ea40861d5498f520430f2a2c7a90218755163d4810c3cc929ea40861d6494f520430f322a7a90218759153d4810c3cc931ea40861d6498f520430f322c7a90218759163d4810c6ac930ea4086556398752042973a6a5290214b5d35294810a9ce7a94a40854d73d4a52042a739ea929021535cf5494810a9ce62a4a40854d7315252042973a6a7290214b5d35394810e1ca929ca40870d5494e52043872a2a729021c35515394810a5ce829ca40852d7414e52042a739ec929021535cf6494810a5ce9b1ca40852d74d8e5204386a1887290214b9d06194810a5ae830ca40854e7318652042a6b98c3290214b9d06094810a5ae8304a40854e7318252042a6b98c129021179cf64548108bae7b22a40843e74d8d520421eba6c6a90214b9d36254810a5ae9b12a40854e73d8952042a6b9ec4a90211b9db5454810a9ce7aa2a40854d73d5152042373b0a8a9021539cc5454810a9ae62a2a40846e76d4d52042973a6a6a90214b5d35354810e1ca929aa40870d5494d52043872a2a6a9021c355153548108dcec29aa40852e7414d5204296ba0a6a9021539cf6454810a9ae7b22a4085647159152042973a6c6a90214b5d36354810ac8e2b1aa40870d4310d52042973a0c2a90214b5d06154810a9ce630aa40854d7318552042973a0c0a90214b5d06054810a9ce6302a40854d7318152042973a020a90214b5d01054810a9ce6082a40854d73041520421ebb4a8290210fdd95414810c3ca9318a40861d5498c520430f2a2c6290218755163148108baed298a40861e6494c520430eb24a62902117dd95314810c3cc8a98a40861d6454c52043172a4c4290218b5526214810c9ca7310a40864d539885204237bb2a4290218b9915214810c5ac8a90a40864e635485204326b1aa429021879926314810c3ac9318a40861e6458c520430eb22c6290218b9926214810c5ac9310a40864e639885204326b1c
  | 4 => 0xe0ea90c408876052486204421fba2ca902210f1d165481108bee6b2a408845c735952044296ba0a490221535cc524811096ae830a40884d57318520442b23aa42902219919521481108f4ec29240885a97414920442e4b98a490221725ce4248110bc2e321240885a9748c920442f0b8c64902216c5d06148110ba2e630a40885d17390520442f0b948290221e85094148110b62e918a40885e1728c520443e099262902219a1972148110ce0cb10a40885e172885204433432a42902215c1d52148110ce0ca90a40887607548520443b1b2a4290221b81952148110ec0ca90a40886606548520442f1ba24290221785d12148110bc6e690a40885e1734852044354b224010221b258d2008110dc2c290040885d17390710442d8ba46388221b858a21c4110dc6c490e20884d773592104425bba2c708221b858a2084110dc6c4904208864e6398b5404326b1cc5aa0219398d62d5010c9ac6b16a808655639875404332b14c3aa0219a58a60d5010a3ce7aa4a80851d73d525404297396a92a0214b5cb54950108bce7314a80845d7398a540430eb18c72a021479ce6295010a3ae7314a80851e73986540428eb9cc32a021479cc6095010a3ae6304a80852e721825404296b90c12a021479cf6455010a3ae7b22a80852e72d915404296b96c8aa02117dcd60550108b8e6b02a80861d6318d540428f39cc4aa021475ce6255010a68e2b12a80851e73985540428eb9cc2aa021479cc6055010a3ae6302a80852e721815404296b90c0aa0210fdd95415010c3aa9318a80861d5458c5404316aa4c42a0218b5516215010c3cc9318a80861e6458c5404317324c42a0219398e6215010c9ac7310a80862e64588540432731ac42a0219358d6215010cacc7308a808655639845404333314c22a0219958a6115010cb2c7300a8086696298054043172a4c5a98218b55262d4c10c5ca8b16a60862d5458b5304317324c5a98218b59262d4c10c5cc8b16a60862d6458b530431ab24c3a98219958a61d4c10cd2c5306a60851e74d4e530428eba6a729821539cb5394c10a9ae5a9ca60843e7498a530421eba4c529821539cb5494c10a9ae5aa4a60854e7215253042a6b90a929821875906494c10a3ce9314a60851d7498a530428f3a4c329821475d26194c10a3ce8304a60851d7418253042a7390c129821535c86094c10a3ce9b1aa60851d74d8d53042a7396c6a9821535cb6354c1087ee8b02a60843c74581530422f3b6a8a9821539cb5454c10a9ae5aa2a60845e7615153042a7390a8a9821535c85454c10c3ac8322a60851e74989530428eba4c4a9821551c56254c10a3ce930aa60851d74985530428f3a0c0a9821475d06054c10a9ce4302a60854d72181530428f3a020a9821475d01054c1087aed2a0a60843f76550530430f2a4c629821875
  | 5 => 0x854c735485244316392c829221879926314910c3ac9318a48861e6458c524430eb22c629221931c96314910c6cc8b08a48863564584524432b31ac2292219558d611491087ce8308a48843d74184524422f398c229221175cc6114910c74c8b00a48863964580524432d31ac0292219658d6014910ce2c2b00a48843e74180524421eba0c029221179cc60149108bae6300a48845e73d97424422eb9ecba1221471cd54d0910a58e4aa6848852d7414b424426ab9cc3a12211d1d561d09108bce7b2c848845d73d96424422f398cb21221175cc6590910c3ea931c848861c5498e424423a3aac3212211e1d560909108bee6b2a848845c73595424423bb8acaa12210f9da5450910878ecaa2848851c735514244296392a8a122117dcd65109108b8e6b28848843e74194424422f398ca21221175cc651091087aedaa08488474755844244332292c2212211e1d5601091087ce9b2e648843d74d97324428e3a2a799221531c953cc910a9ae629664884b574987324423a3aac3992210f9d3658c91087ae9b2c648843e74196324421eba0cb1922187993538c910c3cc829c648847475586324423c3aac1192210fdd1654c910878e8b2a648847771595324422f3b4a699221171d9534c910a38e8a9a648854c7254d324421fba2ca192210f1d1650c91087ce8328648843d74194324422f398ca19221175db530c9108e8eab08648866452584324423c3aac0192213a5c86050510b2ce7b22828847676151414429b3ac86a0a218d1964350510c68ca21a82885b17010d414429a3aa84a0a21355cc60505109cae430282885e1721814144274b90c098a211d1d5644c5109e0e0b22628859674d8d314423b3b0a698a21359db434c510aaceba1a628865465d0d314432a3288698a21a5590434c510ba2e021a6288554754c9314425aba0c098a21395c8604c510bc2e430262884b574984314423b3aec910a21355cf64885108ecebb1c42884b574d8e21442b93a8c110a21355cf64485108e8eab2242884b574d8d214423a3aac690a21599d76248510acce529242884767614921442b33b0a490a21999d85248510e4ce829242887257414921443a3398a490a21d15cc5248510ec2e029242884b574181214426ab98c090a21355ce61d0110a68eaa0e808845f73595404422e39acaa02211bdc965501108d8e4b2a808861f5418d404430e2a0c6a02214d1d54150110d28c6a0a80885b070505404425aba4c398221551d531cc11087ee8b2a608843c745953044237b92ca982211b1c9654c110c38c9a9a608861c6414d30442aa3aa6298221a5191314c110ba0e098a608852d7414b20442a6b98a5902219914961c8110ac8ea90e40885727518620442d8ba0c310221745cc6188110ba2e720c40885e37250620442d8ba4631022178dc93188110a
  | 6 => 0x28428e39aa9a1421179cf6590a108bae7b2c850845e73196428422eb98cb214219358e5290a10c9ac6a94850845f73595428422e39acaa1421179cc6550a108bae632a850851c73551428422f398ca21421175cc6510a1087ce832e650843d74197328428e3a2a7994210f9d3658ca1087ae9b2c650843e74196328421eba0cb194218b592528ca10c5ac8a94650843f74595328421e3a2ca994210f9d0654ca1087ae832a650851c7454d328421f3a0ca194210f5d0650ca10a38e6aa6830851c735514184274b90c0a0c21471d153cc610a38e8a9a63084e972181318437090ac010c21475cc54d0210a5ae42a6810851c73552408421f3b0a8a0421475cc5450210a5ae42a2810861f5418d408430e2a0c6a04210fdd95410210a38e6aa0810861e5458c408430eaa2c6204218b9516210210c5aa8b10810863654584408431aaa2c220421475d053cc210a9ae429e610851c7454e308430e326a698421179d8534c210a3ae829a610861c6414d30842a6b90a69842187592530c2108beeca98610851c7454c308430eb22a6184219394d620c210c9aa6b10610865653584308432aa9ac2184214b5d052c8210a9ae6296410846e761492084296ba0a490421535cc5248210bc2e3a92410847a7614920842753b0a4904216a5d05248210b92e629241085c97390920842f1b8a84904216a5d23248210bc6e299241086e0614852084316b24a4104219358e52082108deeca90410862d645482084326b1aa410421999496108210ccaa4b0841086a9644802084364b1a4010421b85852008210aaee6aa621085377454f108422f39cc52a221175ce6295110c3ec831aa88864f63d89544432631ec4aa2218bd906255110c9ec6312a88864c631895444332316c2aa2210fdd95415110a38e6aa0a88852c72550544422f39cc22a221175ce61151108bce6300a88845d731805444237390c02a2211b5c8601511087ce9314a68843d7498a534430e326c6a9a218bd936254d10c58c9b12a68862f641895344316320c4a9a2193d8c6254d10cc8c5b0aa68845f7654c534428e3a2a629a21531c95314d1087ce9308a68843d74984534421f3a0c029a210f5d06014d108dce4300a68846d721805344237396cba1a211b5cb65d0d108e8eab0e868846e72d964344236b96cb21a211d1d56190d108dee4b2a868846c725954344237b92ca21a211b1c96510d108dce4328868846d72194434428eb98a821a21475d05310d10a3ceaa18868851c7550c434423a3aac221a218d1516110d10ca8a6b08868847875580434434ca1ac021a2117dcd64d49108b8e6b26a48843f7458f524421e3a2c7a922187d936354910c38c9b1aa48861f6418d524430e320c6a92218b1936254910c98c7b12a48863464d85524432a31ec2a92211bdd95214910a58e8a90a48
  | 7 => 0xb996210f5d265ccb1096ae930e658843e74d9632c421eba6cb196210f9d0658cb1087ae832c658843e7499532c421eba4ca99621531c9534cb1087ce8328658843d7419432c428f39ea9a0e21879526390710c3aa931c83886556598e41c432ab2ac720e21b458d6090710a3ce7aa2838843e7615141c42cb39ec8a0e21659cf5450710b62e1aa283884767615141c425b3b0a8a0e214d9d64350710a68eaa1283884d57318141c4272b90c0a0e210fdd95410710d6282b00838851e74d4f31c430f324a718e2187991538c710c6acb32463886356559231c4358b22c118e21479d3534c7108bcec29a638859674d8d31c42cb3a6a698e21745c3534c7108ecec29a63884d67614d31c42ab3ae8698e21a5590434c710aa8ea99263884b57418131c4272b90c098e2117dd9530c710da262b0063884d573d9221c425aba6c710e211b9d852487109aae7b2243884b574d8d21c42f0b86a490e211d9d852487109ccec29243885667614921c43333b0a490e21c99d05248710e4ae829243887467314921c43a2b98a490e21d85c0524871096ae830243884d57318121c4237bb2a410e219a9496008710cd2a4b0043886e12158021c426ab9cc3a0621879506350310c3aa831a81886946350540c425aba4c39862187192534c310c38c8a9a6188694644c530c425aba0c290621355cc6148310ccaa430a418845e7398a548422eb9cc52a42187d90635521087eecaa0a90851c73550548430eaa2c62a4218b5516215210c3cc8b18a90864e639885484326b1cc42a4218b9916215210c9cc6b10a90864d63588548432b31ac22a4219558d6115210cccc4b08a90866562584548421f3a4c529c210f5d26294e10c3ae6322a70861c64d8d538422fbb2a629c21471d15314e10c3ac8a98a70864d53588538430e39ac829c21875926314e10c5cc9310a70862d649885384317322c429c218b5916214e10c9cc6b10a70863664584538431ab22c229c21999896114e10ccac4b08a70846e721974384236b90cba1c21471cd54d0e10a3ae829e870854d7214f4384237390cb21c211b5c86590e10a3ae62a4870852d72152438428e3a2a721c211b9c86550e108dae432a870843e76951438428e39aa8a1c21179da5350e10a38e8a9a870846e721944384236b90ca21c210f5db5410e10a3ae62a0870852d72150438422ebb6a621c21475d05310e10a9ae4298870851e7550c438428e3aa8621c2187d954310e10c3acaa18870869943580438422fb9ac9a9421171cd64d4a1087ee8b1ea50843c7458f5284237bb2a4294218b5915214a10c9ac6a90a50861e6498c528430eb24c629421879916314a10c3ac8b18a50862d649885284326b1cc4294218d9916114a10c6ac8b08a50865663584528432ab1ac2294219c5866014a108bce632e850845d731974
  | 8 => 0x9544c020c3ec929a601061c6494d300830fb22a69804187191534c020c6ec928a601063464945300831bb22a2980418d191514c02087ce9b28601043d74d94300821f3a4ca180410f5d2650c02087ce8328601043d74194300821ebacc8180410fdd5640c02087eed2a0601043d76950300821fbb2a8180410f5d9540c020c3cc9298601061d6494c300830f322a61804187591530c020c5ca9310601062d549883008326a9cc4180418b951620c020c5aa8b10601064e535883008326a9ac4180411d5d6610c020c6ca9308601063554984300832b29cc2180419554e610c0208eeeab08601063654584300831aaa2c2180419594d610c020caaa6b08601047576944300831b324a2180418d592510c020cccc5288601066562944300823bbb2a2180418d991510c020c6ac8a886010666625443008332b12a218041535cf54c8020acae3aa6401052d74d4f20082b2b8ea790041c355253c8020e1ca8a9e401070d5454f2008392aa4a390041d154e51c8020e4ca8a8e40107255454720083a329aa390041d154d51c80208daed29440107195454e200823cbb4a510041cc9515188020e62a8a8c40107525354620083a8a9aa3100411b9db5448020a9ae7aa2401056571d512008296baca8900418bd965448020c5ecaaa2401046e76d4d2008296ba6a690041595c75348020a9aeb29a401064f6594d2008386aa4a69004193d955348020e1ca8a9a401070d5454d2008333b2ca290041c95525148020e8aa728a40106676554520083932a2a290041c95515148020e8ca6a8a40107455354520083b1382a2900418b5536048020c9aa7b02401063b65951200831db2aa89004196d965348020cb6caa9a40107195454d2008394aa4a490041d254e5248020ce6cb28a40106736554520083992a2a290041cc5515148020ea4a6a8a40107515354520083b1292a290041d89c95148020ec6c4a8a401076151c85200828f39ea92a621179ce62953108bae7314a98851e73d9154c421fbb2a82a621479d35394f1087ce9314a78843d7498a53c428f3a6c6a9e2117dd95314f108dce5b2e878846d72d9743c432aa9cc3a1e211b9cb6590f108dae5b2c87886355498643c4237390ca21e211b5c86510f10a3ae72a0878851d7494c43c428fbaa8621e21475d54310f108bce7b22a58845d73d9152c421f3a6c6a96210f5d36354b108deeca90a58861e6498c52c430eb24c629621879916314b10c3ac8b18a58863a6458052c431cb22c0296219698d6014b10cb2c6b00a5886726158052c422f39ecba1621175cf65d0b108bce732e858845d7399742c426ab9cc3a1621179cf6590b108bae7b2c858845e7319642c422eb98cb21621179ce6550b108bae732a858852c7255142c422f398ca21621175cc6510b1087ce9b2e658843d74d9732c421f3a4c
  | 9 => 0xaa8b1c821045f7694e410822ebb4a72084117dd953904208baeca9c821065663946410832ab1ca3208419598d5190420caac6a8c821045e73195410822eb98caa08411b5d76250420c5aa9b12821064d53d894108316aa0c4a08419354c6250420ccec4a8a821066462545410822f39cca20841175ce651042087ce932e621043d74997310821f3a6cb188410f5d3658c42087ce932c621043d74996310821ebacc9188410fdd5648c42087eed2a4621043d76952310821fbb2a9188410f5d9548c420c3cc929c621061d6494e310830f322a71884187591538c420c6cc928c621063564946310831b322a3188418d591518c42087ce832a621043d741953108236baec4988418b553624c420c9aa7b12621062d541893108326a98c49884199d89514c420cc8c4a8a621043e74994310821eba4ca188419c54560c842087aeb320421043f75590210821ebb4a8108410fdd954084208baeb318421061e5498c210830eaa4c61084117dd56308420c3ca8b18421061d5458c210822ebb4a610841879925308420c3ac9298421045f7654c210830f322a610841875915308420c6cc9288421063564944210832b31ca2108419558e5108420c6cc8a88421063564544210832b31aa2108419558d5108420e4ca890842107255448421083a329a4210841d154d2108420c74a9300421063954980210832d29cc0108419654e6008420ce2a3300421063a54580210831caa2c0108419694d6008420cb2a6b00421067251580210837090ac01084117dcd64940208b8e6b24a01043f7458e500821e3a2c7280418b5526290020c9aa7314801046f7558a4008316aa2c5200419354d6290020cccc4a8c801066562546400830f2a6c6a0041875536350020c3ca831a801061d5418d400822f3b4a6a0041171da53500208bceca9a801045c7654d400832bb1ca2a00419518e5150020caec6a8a801065463545400822f39eca20041175cf65100208bce7328801045d73994400822f398ca20041175cc65100208baeb318801061e5498c400830eaa4c62004117dd56310020c3ca8b18801061d5458c400822fbb4a620041175da53100208beeca98801045d7654c4008316aa4c4200419394e6210020c9aa7310801062e545884008316aa2c4200419394d6210020c9aa6b10801047575984400831b2a4c2200418d5526110020caca7308801065553984400823bbaac2200418d9516110020c6aa8b08801065653584400832aa9ac2200411d5da5110020cacc72888010655639444008333314a2200419958a51100208eeeca88801065663544400832ab1aa220041999895110020ccac4a88801062d5498a3008326a9cc5180411bdd5628c020c5aa8b14601064d5358a3008333312a31804199589518c02087ced2a2601043c76951300821f3b2a8980410f1d
  | 10 => 0x51c7454d430823b38cca218411d5c66510c208dce4328861047671194430823ab88ca218411e9c06510c20a3ae72a0861051d7494c430828fbaa8621841475d54310c20c3ecaa18861061d6550c430822f39ecb21041175cf65908208baeb31c841061e5498e420830eaa4c72104117dd56390820c3ca8b1c841061d5458e420822fbb4a721041175da53908208beeca9c841045d7654e4208326b1ca5210418e5516090820cb2a7300841063a54580420832ca9ac0210410f9d3658c82087ae9b2c641043d75992320821fbaac9190410fdda548c82087aed2a4641043f76552320821ebb2a91904187992538c820c3ac929c641061e6454e320830eb22a7190418b592528c820cb2a6b04641063954980320831caa2c0190419694d600c820c3ca931ea21061d5498f510830f2a2c7a88418755163d4420c3cc929ea21061d6494f510830f322a7a88418759153d4420a6ce9a8ca21053574d4651082ab39ea328841555cf5194420aace7aa4a21055573d5251082ab398a928841555cc5494420a6ce9a9ca21053574d4e510838b2a4a728841c55525394420e2ca8a9ca2107155454e510829b3a0a7288414d5d05394420aace7b24a21055573d92510829b3a6c7288414d5d36394420e2a8621ca2105367418a510829aba0c528841559cc6294420aaae6314a2105567390a51082aab9c85288414d9d23294420a6ae9194a21053674182510829aba0c128841559cc6094420aaae6304a21045e73d91510822eb9ec8a88410f9d3635442087ae9b1aa21047676d5151082ab39ea8a8841555cf54544208ecec2a2a2105567315151082aab98a8a88411d9db5354420a6ce9a9aa21053574d4d510838b2a4a6a8841c55525354420e2ca8a9aa2107155454d510823b3b0a6a88414d9d05354420a6ae829aa21055673d9151082aab9ec8a8841591c96454420a6ce9b1aa21053574d8d51082b2392c6a8841c550c4354420aace7212a2105557390951082b938484a88415c5c24254420ae4e0212a21057170109510829b3a464a88414d5d23254420ae4e1192a210571708c951082b938064a88415c5c03254420a6ce8302a2105357418151082ab398c0a8841555cc6054420a6ce8102a2105357408151082ab39840a8841555cc205442087aed2a0a21043f76550510830f2a4c628841875526314420c3ca8b18a21061d5458c510822ebb4a628841879925314420c3ac9298a21045f7654c510830f322a628841875915314420c6ca9308a21063554984510832b29cc2288419554e61144208eeeca88a21063664544510831ab22a2288419598d5114420caac6a88a21045e73997410822eb9ccba0841179cf65904208bae7b2c821045e73996410822eb9ccb20841175d66390420c3ca931c821061d5498e410822fbaac720841879516390420c3
  | 11 => 0x482963aa84a0241a318d4250120b50e0a1280904ad7498b30482a63aa65982410fdd1654c120878e8b2a609061c64d4d304830e320a698241531d5324c120d18c899260905c8704c930482e4b9c85902416a5d232c8120dc2c390e40904cf735922048257ba2c7102419358e62d5020cacc730ea81065563987540832b31ac3aa0419558d61d5020cccc4b0ea81067161983540828f39ea92a041475cf5495020a6ce3aa4a81053571d52540822f39cc32a041175ce6195020c3ac631ca81051e7398a540828eb9cc52a041479ce6195020a3ae730ca81051e73182540828eb98c12a0414d9c46095020a6ae2304a81051e73d91540828eb9ec8aa0414d9c76455020a6ae3b22a81061d6318d540828f39cc4aa041475ce6255020a3ce730aa81051d739855408296392c2aa041479cc6055020a3ae6302a81053671181540829ab88c0aa0410fdd95415020c3aa9318a81061d5458c540831aaa4c22a0418d5516115020c3cc9318a81061e6458c540832731cc42a0419358e6215020c6cc9308a81065663984540832ab1cc22a0419998a6115020c6cc8b08a81065663584540832ab1ac22a041999896115020cb2c7300a81067161980540831b2a4c3a98418d55261d4c20c6ca8b0ea610635545875308316b24c5a98418d99261d4c20c6ac930ea61063664587530831ab22c3a98419998961d4c20ce2c3306a61051e74d4e530828eba6a729841559c75394c20aaae3a9ca61043e74986530821eba4c329841559c75494c20aaae3aa4a6105567115253082aab88a929841875906494c20a3ce9314a61051d7498a530828f3a4c329841475d26194c20a3ce8304a61051d7418253082ab388c129841555c46094c20a3ce9b1aa61051d74d8d53082ab38ec6a9841555c76354c208bcedaa2a61055671d5153082aab8ea8a9841179d85454c20aace22a2a61055571151530830eb20c8a9841479d26254c20a3ae9312a61051e74985530828eba4c2a9841531c96154c20a3ce8302a61051d7418153082ab388c0a9841555c46054c20a3ce8102a61051d74081530821ebb4a8298410fdd95414c20c3ca9318a61061d5498c530822fbb2a629841879915314c20c3ac8a98a61063654984530831aaa4c2298419554e6114c20c6ca8b08a61063554584530832aa9ac229841879926314c20c3ac9318a61062e649885308316b24c4298418d9926114c20c6ac9308a610656639845308333314c2298418d9916114c20c6ac8b08a610656635845308333312c2298418e5926014c20ce2c3300a61047671997430823ab8ccba18411b9c865d0c208ece232e861047571197430823b38ccb218411d5c66590c208dce432c861047671196430823ab88cb218411d9c66550c208eae332a861046e72195430823b388caa18411d5c46550c20a38e6aa28610
  | 12 => 0x98441555c453cc220a38e8a9c611061c64d4d308822f3b0a698441475d0534c220c38c829a61105557114d308830eb24a61844117dd9530c220a38e8a98611061d6454c308832729ac4184419354d620c220caca6b0861106555358430882a7b9aa9904414bdd153c82208bce730ca89045d73986544830fb20c6aa24195d8f6155120ca8c7b0aa89063764185544832bb18c2aa2419518c6155120ccec430aa89043f76550544828e39aa82a2414d1c554151208bce7310a89045d73988544821f3a4c329a410f5d26194d20c38c9b1aa69063764d85534831a326c2a9a418dd906154d20c68c830aa690657631855348333b10c2a9a4117dd95314d20a38e8a98a6905547154c534821f3a4c429a410f5d26214d208ece3b2e869047571d9743482363aac5a1a411d9c76590d208eae3b2c869046c7558a434823bb8acaa1a411d1c56550d208eee2b28869047471594434823b388ca21a411d5c46510d20a3ae62a0869051d7414c434828f3aa8621a41471d54310d208d8eab10869062c54588434832629ac421a411e1d56010d20d3286b0086904f17118142482c739ec8a12411b9d85450920a5ceb21a849062c6590d424831632886a12416a5c0435092099ae630284904e57118142482f0b88c0a12413c5c4604c9208d8eab2264904e87059132482c73a6c6992411b9d8534c92099ceda1a649054e75d0d324832632e869924193194434c920d1ac821a64905c97010d3248256ba0c099241395c4604c920bc2e230264904ad74988324822fb9ac9a8a41171cd64d452087ee8b1ea29043c7458f514823bbb2a228a414d1d15114520aa8e6a88a29063471590514830f324c628a41875926314520c3cc8b18a29061d6458c514832a38ac628a418e9916014520c72c8b00a29065a63580514832cb1ac028a41471cd54d0520a68e2aa682904cd7398b414829aba0a3a0a41179cc65905208bae632c829061f5498e414830e2a4c720a410f9da5450520a38e6aa2829053471551414831632a84a0a4117dcd65105208b8e6b28829045e73194414822eb98ca20a410f5db5410520ccac4288829051c7454f31482aa38aa798a412b5d262cc520aaae628e629043e74196314821eba0cb18a4187993538c520c3cc829c629045e7694d314828e3a2a698a41551c5534c520c98ca992629043f74594314821e3a2ca18a410f9d0650c52087ae8328629045d76d4c3148332b10a218a411b9d764c852099ae7b26429046e75d8f2148256ba6c790a415a9d460c852099ae7b2242904ad74d8d21482b33aec290a41599d85148520cccec28a4290726741452148392ba0a290a41d19cc5148520e8ae628a4290761701452148256ba0c090a41335cc604852099ae7316809052c7550b404822fb9acaa0241171cd6550120c3ea831a809061c5418d40
  | 13 => 0x648cb20d52c8b04659051e74d4d32c822f3b0a699641639d3634cb20b1ce9a9a65905c970d4d32c82373b0a699641339d8534cb20a9ceba1a659068d6410d32c8256ba0c099641395c4604cb208beeca9865906c93258032c822f39ec8a8e41175cf645472087ce9b1aa39043d74d8d51c823bbb2a228e41179cf65d07208bae7b2e839045e7399741c822eb9ccba0e41335ce62d07208bce7b2c839045d73d9641c829a38aa8a0e418b195425072087ce9b2e639043d74d9731c821f3a4cb98e410f5d265cc72095ae9316639043e74d9631c821eba6cb18e41551c5534c720c98ca99263904cd73d9321c8256ba6c790e41335cf644872095ae9b1a43905e170d4521c82733b0a290e412b5d0604872099ae630243906715158021c837090ac010e41335ce62d0320c3ca831a819061d5418d40c834631a84a06412b5d262cc320c38c929a619061c6454d30c83463226498641179ce61952208bae730ca91061f6418d548821fbb2a82a441471cd5415220c3aa8b18a91063554584548830f322c62a4419398d6215220c9ac6b10a91065663984548832ab1cc22a4419958a6115220c6cc8b08a91065663584548832ab1ac22a44199589611522087ce930ca71043d74986538830eb98c8a9c41871936354e208beeca98a71051c7454c538830eb22a629c419554d6114e20c38e6b20a71061d6498c5388317322c429c418b5916214e20c6cc9308a710635649845388332b14c229c418d9916114e20c6ac8b08a710656635845388332b12c229c411d9c465d0e208eae232e871051c73553438828eba0a7a1c41555c453d0e208ece232c871047571196438828eb98a921c414d5c45490e20a38e8a9c871047671195438823ab88caa1c410f9da5450e20a38e6aa2871045e7694d438828e3a2a6a1c411d9c46510e208eae2328871043d76d50438828eb98a821c414d5c45410e208baeda98871051d7414c43882aab88a621c41479d54310e20a38eaa18871061f6550c438830eb2a8621c41a650d6010e20a38e6aa6851051c735514288278b88c0a1441471d153cca20a38e8a9a65104f171181328823bbb2a228c418d5915114620caac6a88a31051c73553418822f39ecb20c41175cf6590620caac728c831065563546418822fb9acaa0c41171cd65506208bce632a831045d73195418828e39aa8a0c41471d153cc62087ce9b2c631043d74d96318831ab24a318c418d591518c62087ee8b2a631043c74595318821f3a0ca98c410f5d0654c620a38e8a9a63106e121580218828eb98a9a04414d5c454d0220a38e6aa4811043e76151408828eb98a8a04414d5c45450220c3ea831a811061c5418d408821fbb2a820441471cd5410220c3ca8b18811061d5458c40883172a2c4204418b5516210220c6ca8b08811063554584408828eba0a7
  | 14 => 0xa8b08801863554584400c34a21ac220061999496110030ccaa4b08801847576944400c32b31ca2200619558e5110030cccc5288801866562944400c23bbb2a2200619598d5110030caac6a88801871443544400c333312a220061995895110030a9ae5aa6601855571d53300c22fbb2a9980618799154cc030c3eecaa6601861c76553300c386aa4a598061c395152cc030e1aa8a96601864e6454b300c326322a598061c555251cc030e8aa528e601871654547300c38aaa2a398061d194951cc030e8aa4a8e601865664547300c32a322a398061175da538c0308f2ed29c60187295454a300c398aa2a318061d8549518c03087ced2a2601843c76951300c21f3b2a8980610f1d9544c030c5ec9292601862c64949300c317b22a4980618b191524c030c6ec928a601863464945300c31bb22a2980618d191514c030c3ee9b2a601861c74d95300c30fb2ec898061175d6644c03093ce9322601861f65191300c30eba8c898061179db544c030c38c9aa2601854d72d51300c2aab8ea898061271da544c030a3aeb2a2601861f65951300c22e3b2a89806187191544c030938ecaa2601861f65551300c30fbb2a898061479d9544c030a38ecaa2601861c76551300c20e3b2a89806193d96524c030d18c9292601870d54949300c30e322a49806193d95524c030d18c8a92601870e54549300c386aa2a498061c3d91524c030c9cc8a92601864c64549300c386322a49806183191524c030caecb28a601869464945300c38aaa4a298061d154a514c030c38c8a8a601865765545300c34a322a298061c5951514c030e2aa8a8a601874652545300c3a2a92a298061c5d91514c030cacc8a8a601865464545300c38a322a29806185191514c030c3aa9b02601861c64941300c31dba6ca980618e1d3654c030c76cbb22601863b65191300c31db2ca8980618ed95544c030d30c9b1a60187195494d300c335b2ca4980619ad95524c030e52a8a92601874a53549300c339b2ca2980619cd95514c030e62a8a8a601875253545300c3b0a92a298061479cf54953208bce730ca99045d7398654c828f39ec8aa6410fdd95415320a3ce9a9ca79043e7498653c821eba4c329e41479d36354f208beeca98a79047671d9743c823ab8ecba1e419354e62d0f208ece3b2c879047571d9643c8316aa4c521e411d9c46510f208eae2328879051d7395043c828eba4a621e4147dd54310f20a3aeaa18879051e73d5342c830f2a4c721641875526390b20c9acb31c859064d6558e42c8364b1ac121641479cf5450b2087cec2a2859058e73d9142c82c739ea8a16416a5c35450b208dcec2a285904ae7615142c82973ac86a1641335cc6050b209cae2302859043f7655042c8354a12c021641479d353ccb20c3cc929c659061e6454e32c8316b2cc9196418b595
  | 15 => 0x6d72996410c30f2a4c720861875526390430c3ca8b1c821861d5458e410c32731ca5208619358e5290430c9cc6a94821864d6354a410c32ab1ca3208619598d5190430caac6a8c821846e72195410c236b90caa0861175d76350430c3aa9b1a821861d5418d410c28eba886a0861875944350430c9ec6a92821864c63549410c38621aa4a086195d8d5150430ca8c6a8a821871443545410c237394ca208611b5ca6510430ce2a2b06621843f76952310c21ebb4a9188610fdd9548c43087aecaa4621862e6494a310c316b24a5188618b991528c430c5ac8a94621863664546310c31ab22a3188618e552600c430cd2a5300621863954580310c334a92c0188619c945600c43087ce932e421843d74997210c21f3a4cb108610f5d2658843087ce832a421843d74195210c22ebaec690861279d36348430c3aa9b1a421861d5418d210c327b1aa4908619318d5248430ac8e2a92421865763545210c32a31aa290861591c9514843087ce9b28421843d74d94210c21f3a4ca108610f5d2650843087aeb320421843f75590210c21fbb4a8108610f5da540843087eecaa0421843d76550210c30f2a4c610861875526308430c3ca8b18421861d5458c210c317324a4108618b5925208430c9cc7290421864d63948210c2b2b8ca4108618b9915208430c5ac8a90421864e63548210c326b1aa4108618d9925108430c6ac9288421865663944210c32ab1ca210861595ca5108430c6cc8a88421863564544210c32b31aa2108619558d5108430aceea908421856575484210c333b2a4210861995952108430e4ca8908421872554484210c31d2a4c0108618e5526008430cd2a5300421867151980210c31d2a2c0108618e5516008430cd4a4b00421866952580210c33928ac0108619c5456008430dc242b00421845d7610e500c28ebae87a00618759743d0030e1e86a96801871743547400c30eaa4c72006117dd56390030c3aa8b1c801851d7510e400c30fb2887200619398d5290030c9ac6a94801870c4354a400c32b31aa3200619558d5190030e2886a8c801861e54d8d400c30eaa6c6a0061879506350030c3aa831a801849e76d0d400c28ebae86a006187d974350030c9ec7292801864c63949400c327b1aa4a00619318d5250030e1e86a92801865763945400c32a31ca2a006195d8d5150030ca8c6a8a801871743545400c30eaa4c620061879516310030c3aa8b18801851d7510c400c30eb288620061665c043100308daeb310801862e54988400c316aa4c4200611bdd56210030c5ca8b10801862d54588400c34621ac4200611b5da5210030c9cc7290801864d63948400c237bb2a4200619398d5210030c9ac6a90801870c43548400c23abacc2200618d9526110030c6aa9308801866652984400c332a94c2200611ddd56110030c6c
  | 16 => 0xc30f2a4c721061875526390830c3ca8b1c841861d5458e420c326b1ca5210619398d5290830c9ac6a94841847671195420c23ab88caa1061175d76350830c3aa9b1a841861d5418d420c28eba886a1061875944350830c9ec6a92841864c63549420c38621aa4a10611d9c665108308eae3328841866952583320c21fbb4a9190610f5da548c83087eecaa4641843d76552320c317322a5190618b591528c830c72a9300641863954580320c335292c0190618b95262d4430c5aa9316a21862e5458b510c316aa2c5a88618b99252d4430c5ac9296a21862e6454b510c316b22a5a88614d9d35194430a6ae9a8ca21856672d46510c2b2b96a328861599cb5494430acae5aa4a21871473552510c2b3390a928861595c85494430aaaeba1ca21871554d0e510c38aaa087288614d9d35294430a6ae9a94a2187265494a510c392aa4a528861c99515294430e4aa8a94a2187474354a510c3a221aa5288614d9d05294430a6ae8294a21855673d92510c38aa1887288614d9d06294430a6ae8314a2185567318a510c332b10c5288615c9c06294430aace7214a2185557390a510c29b3a465288614d5d23294430a6ce8304a21853574182510c2b3390c128861595c8609443087ce8312a21843d74189510c23b3b6a8a8861599cb5454430acae5aa2a21871473951510c38a39aa8a88611d9d85454430acce42a2a21856572151510c2aabae86a8861c59534354430e2aa9a1aa2187165410d510c38aaa086a88611d9db5254430a6ce9a92a21853574d49510c3932a4a4a8861c95525254430e8e87292a21874443949510c3932a2a4a8861c95515254430e8e86a92a21874443549510c23b3b0a4a88614d9d05254430a6ae8292a21855673d91510c2aa39ac8a8861555c34354430e2a8621aa2185727010d510c2b8b8086a8861c59d04354430e2cc821aa2187156410d510c3a938086a8861555c04354430ea2e021aa21855473589510c29b3a0c4a88614d5d06254430aace6312a21866562189510c2b9380c4a8861c510f4254430aace7212a21855573909510c2abb9a84a8861551cd4254430e2886a12a218536748c9510c29aba464a88615c9c03254430ae2e0192a21853674181510c29aba0c0a8861599c86054430acae4302a218536740c1510c29aba060a8861599c83054430acae4182a21843d76950510c21fbb2a8288618b9526214430c5aa9310a21862e54588510c316aa2c4288611b5da5214430c5cc9290a21862d64948510c237bb2a4288618b9915214430c5ac8a90a21863654984510c31aaa4c2288619994a6114430ccaa5308a21847776544510c31b322a2288618d5915114430cccc4a88a21866562544510c237394cba08611b5ca65d0430a3aea21e821861d6510f410c38621aa5a0861c510d51d04308dce532c82184
  | 17 => 0x8261879d8548c130c3aec2a4609861c5458a304c30e2a2c3182619398d62d5030cccc530ea81866562987540c32b31ac3aa0619998961d5030ccac4b0ea81852e72d52540c296b96a92a0614d9c75495030a6ae3aa4a81851e7398a540c28f39cc32a0614b9c86095030a5ae4304a81853671182540c29ab88c12a0614b9cb6455030a5ae5b22a81853671d91540c29ab8ec8aa0618718f6255030a3ce7312a81851c73589540c30e31ac4aa0618718f6155030a3ce730aa81851c73585540c30e31ac2aa0618718e6055030c38c6302a81852e72181540c296b90c0aa0614d9c46055030a6ae2302a81843f76550540c316aa4c42a0618b5516215030c6aa9308a81863554584540c317324c42a0619398e6215030c5cc8b10a81864e63588540c31b324c22a0619598e6115030cccc5308a81866562984540c31b322c22a0619598d6115030cccc4b08a81866562584540c334b14c02a0619c5866015030c3ce8b2e861854d72d53430c2aab8ea9a18618759654d0c30c3aa8b06861863954582430c28eb9aa82186187d954310c30c3acaa18861863a54580430c28ebacc821861875966410c30a9ae5aa0861855571d50430c28ebaca82186117dd95410c30c3cc8aa0861851f76550430c30fbb2a82186147dc95410c30a3ee2aa0861845f75580430c30eaa2c021861a69916010c30c6ca930ea41863554987520c31b2a2c3a90618d55161d4830a5ce9a94a41852d74d4a520c2b338ea529061595c75294830acce3aa4a41856571d52520c38639aa929061599c45494830acae22a4a41854d75d0e520c386aa68729061c35504394830a9ce7b24a41870d4310e520c2973a0c3290614b5d06194830a9ce630ca41866561186520c2b5380c3290614b9d06094830a5ae8304a41856671182520c2b2b88c1290610f9d0615483087ae830aa41846e76d51520c2b338ea8a9061595c75454830e18e72a2a41870c73551520c2373b0a8a9061599c45454830acae22a2a41854d75d0d520c3872a686a9061c35534354830e1ca821aa41870d5410d520c2a739ec8a9061531cd6454830a9ae1a1aa41870d4310d520c2b538086a90615a5c04354830e1ce821aa41870e6410d520c386b2086a9061d29c04354830a9ae021aa4187497010d520c2a639ac2a90614b9d06154830a5ae830aa41854e73185520c332b08c2a90615a9c06154830a5ce8302a41852d74181520c2b3388c0a9061595c46054830a5ce8182a41852d740c1520c21ebb4a8290610fdd95414830c5ca9310a41862d54988520c237bb2a4290618b9915214830c5ac8a90a41863654984520c31aaa4c2290619954a6114830c6ca8b08a41863554584520c332a92c2290611d9c665d08308eae332e841851d7510f420c30eb2887a1061c310d52d08308ece332c841847571996420
  | 18 => 0x3509308ece2328849847571194424c296b90a821261871526310930c38a8b18849863854980424c22f3aec999261355c764cc9308baec2a6649861d64153324c30f328a999261879d854cc930c3aec2a6649870e72153324c386b90a9992618715161cc930c38a9306649843e75992324c21e3aac9192610f5db548c93087aec2a4649845e75d91324c28f3a4a899261539ca544c930c3ec82a2649861d64151324c30f3b0a899261875d8544c930e18a9b12649870c54d49324c387aa0a49926187153614c93093ae8302649861c54181324c26ab88c09926187152630c930e1ea8990649843e7498b514c21eba4c5a8a610f9db545453087cec2a2a29862f54d89514c3162a6c4a8a618bd506254530c58a8312a29847776544514c2b2392a228a618715263d0530c38a8b1e829851e7590f414c30faa4c720a61871526390530c38a8b1c829853671d51414c28f3ac86a0a618719643505308dce4328829846d72194414c29ab88a820a61871526310530c38a8b18829863854980414c22f3aec998a61335cb64cc5308baec2a6629861d64153314c30f328a998a61879d854cc530c3aec2a6629871671153314c38ab88a998a618715162cc530c38a9306629843e75992314c21e3aac918a610f5db548c53087aec2a4629845e75d91314c28f3a4a898a61559c6544c530c3ec82a2629861d64151314c30f3b0a898a61875d8544c530c38a9b12629871454d85314c38a2a6a298a61c5d50514c53093ae8302629861c54181314c266b90c098a6187152630c530e2ea8988629843f74597214c21e3a2cb90a618715263c8530c38a8b1e429843f74596214c21e3a2cb10a61871526388530c38a8b1c429843e74d95214c21eba6ca90a61179d6634853093ae931a429861c5498d214c30e2a2c690a610fdd16508530878e8b28429843e74194214c21eba0ca10a610f9d66408530878eab20429843f76d50214c21ebb6a810a610fdd8540853087aec2a0429861f5498c214c30e2a4c610a6187d516308530c38a8b18429864d63d48214c2b2b88a410a619558f5108530acae4288429856675484214c2b23aa4210a61c9d512108530e48a8908429863b54980214c31c2a4c010a618ed516008530c70a8b00429866b52580214c334292c010a619cd456008530ce0a2b0042986e121580214c30e2a4c7a02618715163d0130a38eaa1e809851e7590e404c30f32c8720261871536350130c3ea831a809861c5418d404c28e3aa86a0261871954350130b30e0a1a809861f5498c404c30e2a4c62026187d516310130c38a8b18809849d7690c404c28f3ac8620261879964310130c5ea9310809862c54988404c317aa2c4202618b1516210130d1c86b10809863754984404c31a2a4c2202618dd516110130c68a8b08809869643584404c30eb20a91
  | 19 => 0x8b10819868e4358840cc31baa2c2206618d1516110330d2c86b08819843f76550548c316aa2c42a4618d5516115230c9ac7310a91862e64588548c326b1ac42a4619558e6115230cccc5308a91866562984548c31b322c22a4619558d6115230cccc4b08a91866562584548c296b90a921c614d5c45490e3087ced2a2871843d76d50438c296b90a821c614d5c45410e308baedaa0871849d76d50438c2cd386a821c61475db5410e30c3aedaa0871851d72d50438c28eb8ea821c61c69c35410e30b1ae42a0871859571150438c2cd380a821c6187d516010e30c3ec821aa51843e74185528c21eba0c2a94611bdd95214a30c5ac8a90a51866552584528c30f32887a14619358e5290a30c9ac6a94851847771595428c23a38acaa14611d9c46550a308eae232a851870c43549428c316b24a5194618b591528ca30c3ec821aa31843e74189518c21eba0c4a8c611ddd95114630c6ac8a88a31866562544518c30f32887a0c619558e5190630caac6a8c831846f72595418c236392caa0c611b9c865506308dae432a831871443545418c31ab24a318c618d591518c63087ee8b2a431843c74595218c21f3a0ca90c610f5d0654863093ce9b1a431856471549218c2b2392a290c610f9d3650863087ae9b28431866765484218c332b2a4210c61b84856008630a5ae42a6811853571153408c21f3b0a8a04614b5c85450230a6ae22a2811861c5418d408c24f3b686a04610fdd95410230c3ca8b18811861d5458c408c3172a2c4204618b5516210230d1886b10811863654584408c31aaa2c220461a510d6110230938e8b2e611851f74597308c30e326a99846117dd954cc230c3cc8aa6611862f6298b544c28eb98c5aa2618dd8661d5130a3ae630ea89843f76550544c297396c62a2614b5cb6315130a6ce3b18a89853571d8c544c28fb92c62a26147dc56315130a3ae7b10a89851d73988544c28eb98c42a2618b5886215130a6ce2310a89853571188544c29cb80c42a261475cf6115130a3ae7308a89851d73184544c297390c22a2614b5c86115130c6ac2308a89853970184544c30eb1ec02a2618758d6015130c70a9306869861f74996434c30f32ea921a61871516290d30c38a8b0c869861c54982434c31daa0c0a1a61479d76450d30c38cbb22869851e74951434c22f3b0a8a1a61479d85450d30c3cec2a2869861c54d89434c30e2a6c2a1a61871506050d3099ae430286984d571181434c34db20c0a1a61871526310d30a38eaa18869843e74987524c21eba4c3a92610f9db545493087cec2a2a49863754d85524c31a2a6c2a92618dd506154930c68a830aa49846f76548524c2b238aa4292618715263d0930c38a8b1e849851e7590f424c30faa4c721261871526390930c38a8b1c849852e72d51424c28f3ac86a1261871964
  | 20 => 0x9535802110335292c0108819a5496008440ce4a2b00422067151580211037090ac0108810f5d8439404087eeca9e802061e6354f401030fbb2a7a0081c354e52d0040e1ca6a96802070d5354b401031731aa5a0081c554e51d0040e4aa528e802071653547401038aa9aa3a0081c994951d0040e4aa4a8e802063663547401021ebb4a9200811e5da5490040e92a6a9480207515354640103b0a92a320081171da53500408bceca9a802064f63949401032631ca4a008193d8d5250040c98c6a92802065763945401032a31ca2a008195d8d5150040ca8c6a8a802061f73d95401030e39ecaa008187d976350040c3eca31a802061d7518d401024e3b4a6a008187d965350040c38c6a9a802049c7654d401030fb2aa6a0081479d95350040a38eca9a802061c7654d4010317b2ca4a0081a318e5250040e1aa7292802061c635494010317b2aa4a0081a318d5250040e1ca6a92802070d535494010387b1aa4a00818b18d5250040e18c6a92802060c63549401031bb2ca2a0081a518e5150040e2aa728a802072552945401030e31aa2a00818dd955150040d28c6a8a802071653545401038aa9aa2a0081c99495150040e4aa4a8a802071763545401031a31aa2a0081c518d5150040c28c6a8a802065b73d95401032c39ecaa008196d976350040cb6ca31a802069b6418d401032db2ca6a008196d955350040e34a8a9a802066b659494010335b2aa4a0081ca9515250040e92a6a928020673659454010339b2aa2a0081cc9515150040ea2a6a8a802076152545401021fbb2a82a6610f9d85450f30b32e1aa2879845e7615143cc24f3b0a8a1e61479d85450f30c3cec2a287987197015143cc30e2a6c4a1e61871536150f30c38a830287984cd7218143cc26ab88c0a1e610fdd95410f30d3286b00879846f7654852cc23b38ecba16611d5c765d0b30c38a8b1e859852e72d5142cc26ab8ec99966117dd564ccb30c3ac82a6659851e7494b32cc24eba6ca99661479d3654cb308bced2a2659854e7295132cc30eb20a899661725c3524cb30a3ce929265984ce7614932cc24eba0c099661355c4604cb30d9264b00659864c624c951cc23bbb2a228e611b9cb65d07308dae5b2e839861c5458f41cc29b38ea8a0e61335cb64cc7308beeab26639861d6415331cc28f3a4a398e61275d3654c730a3ce9b2a639845e7695131cc2ab38ca898e6187590544c730aa8e2a9263985d170d4531cc28f3a4a298e61359d8514c73093ae830263984cd7218131cc36898ac018e610f9d365c873087ae9b2e439843e74d9621cc21eba6cb10e610f9d3654873087ae9b2a439849d7498d21cc21f3a6ca10e610f5d36508730dc242b00439843e7695140cc30f2a0c6a066187550635033087aedaa0819861f5458c40cc24ebb486206618bd516210330c58a
  | 21 => 0x39321aa4a8881c910d52544408ecec292a2205567314951102aab98a4a88814d9d36354440a68e8b1aa2205357090d511038aa1886a88815c9c04354440ae2e021aa2207167310d511038b31886a8881c558c4354440e64e021aa2205357010d5110398b8086a88814d1d16254440a6ce8312a2205567318951102aab98c4a8881995886254440ae4e0312a2205567390951102aab9c84a88815c9c04254440ae2e0212a22071443cc9511029b3a464a88814d5d23254440a6ee8992a220534744c9511038a21a64a8881559cc6054440aaae6302a2205667218151102b2b90c0a8881559cc4054440aaae6202a2205667210151102b2b9080a8881175da53144408beeca98a22064e539885110326a9cc4288819394d6214440c9aa6b10a22046d76948511032731ca4288819358e52144408deeca90a22064e635485110326b1aa4288819594e6114440caaa7308a220666529845110332a94c2288811ddd95114440cacc6a88a220655635445110333312a228881995895114440ce2a2b06822045f7694e411022ebb2a7208819398e5290440c9ac7294822064e6354a4110326b1aa5208819598d5190440caac6a8c8220659539804110334a94c0208819654d6010440cd2a4b008220672515804110237394cb988811b5ca65cc440c3aca21e622070c4354b311038a21aa3988811b9ca658c4408dae532c622061e6494e311030eb24a71888187991538c440c3ac8a9c622062e6494a3110316b24a5188818b991528c440c5ac8a94622063564946311031b322a3188818d591518c4408dce432a622046d72195311021ebaec89888187d91534c440c38c8a9a622061d6510d3110317b22a4988818b191524c440e1886a92622063764545311031a322a298881c510d514c4408dce5328622046d72994311022f39ccb90881175ce65c84408bce732c422045d73996211022f398ca90881175cc654844087aebb22422049e73d91211030fb22a690881871915348440c5ec8a92422062c6454921102b238aa4908818dd915148440c68c8a8a422056472545211022f39eca10881175cf65084408bce7328422045d73994211022ebacc61088117dd563084408beed298422045d7694c211030f324a6108818759253084408beeca98422045d7654c211030f322a610881875915308440c5cc9290422062d64948211032731ca4108819358e5208440acae3290422062e645482110316b22a4108819398d5208440c9ac6a90422063664944211031ab24a2108819598e5108440caac7288422056572944211031b322a2108818d5915108440cacc6a8842206556354421102b3baa4210881595d52108440cceca90842206656548421103a329a4210881d154d2108440cb4a73004220659539802110334a94c0108819c5466008440cb4a6b00422065
  | 22 => 0x814b5d64394840e1aa721ca42070d5310e52102973a6c729081c350c4394840a5ce830ca42054e7318652102a6b98c329081995846194840ad4e030ca42054e7318252102a6b98c129081599c46094840acae2304a42045e73185521022eb98c2a90811b9db5354840acce3a9aa42056571d4d52103863a4a6a9081c31d153548408dcec29aa4205667114d52102b2b88a6a90814b5d64354840e1ca721aa42070d5390d521038729886a9081c354c4354840a5ce9b1aa42052c7458d5210296b8486a9081c350c4354840ad4e021aa4205697010d521038739886a9081c398c4354840e1ac621aa42072a7010d5210296b8086a9081ca5c04354840a58e8b0aa42052e7418552102a7398c2a9081535cc6154840ccac230aa42056a7018552102a7398c0a9081535cc6054840acce2302a4205657118152102a739880a9081535cc40548408baed298a42045f7654c521032729cc4290819354e62148408deeca90a42064e635485210326b1aa4290819594e6114840caaa7308a42066552984521032b29ac2290819554d6114840ccaa4b08a42066952583421022fbb4a721081175d95390840c9cc6a94842064d6354a421032ca9cc0210819654d6010840cd4a4b00842047671997321023ab8ccb990818759443cc840e1886a96642047671996321023ab8ccb1908187992538c840c3ac929c642061e6454e321030eb22a7190818b592528c840c5cc8a94642062d6454a321023b388ca990811d5c4654c84087aebb22642061f6454d321030e322a69908187594434c840c5ec8a92642062c64549321038621aa4990811d9c6650c8408eae3328642064e5398b5110326a9cc5a88819394d62d4440c9aa6b16a22064e6394b5110326b1ca5a88819398d52d4440c9ac6a96a22055673d4651102aab9ea328881599cb5194440acae5a8ca22056672d4e51102b2b96a728881c51d15394440acce429ca2205657214e511029abac8728881c554e4394440e2aa621ca22055673d4a51102aab9ea528881d194e5294440e8aa7294a2207465354a51103a2a9aa528881c990d5294440e4886a94a2205567314a51102aab98a5288814d9d36394440e2a8621ca2205367418a51102ab398c528881555cc6294440ccac4314a2205727018a51102ab39c8528881555ce4294440a6ce9194a220535748ca51102ab398c128881555cc6094440acce4304a22056572182511022f398c4a8881175cc62544408eceda9aa22056672d4d51102b2b96a6a8881c51d25354440e28e8a9aa2204767614d51102b3390a6a8881595c85354440a6aeb21aa2207165390d511038aa9c86a8881c594c4354440e2aa621aa22047676d4951102ab39ea4a8881555cf5254440e8ca7292a22074553949511039321ca4a8881c910e5254440e8ca6a92a220745535495110
  | 23 => 0x50940e1ea6a1084a061e6414f325030eb20a799281479d743cc940c3cc9a9c64a061e6414e325030eb20a7192810f9d6644c94096ae332264a054e72d4d325030f320a69928187590534c940a3ceba1a64a061c65d0d325023b388ca192811d5c4650c940c3cc829864a061d6414c32502a6b90a6192819614e600c9408bce7316a2a045d7398b515022f3b6a6a8a81179d85354540c9ea7b12a2a064c53d895150327a98c4a8a819314c62545408eeeca88a2a056472544515030eb18a7a0a818799453d0540c3aec29e82a07167114f415038ab88a7a0a818714d62d0540c38a730682a045e7598e415022e3aac720a81175db53905408baec29c82a043e75d8d415030fb18a6a0a81879d85350540c38a7b1282a071453d85415038a29ea2a0a81c5d4c515054093ae630282a061c531814150256b90c0a0a81c5d4d4110540c3cc829e62a061d6414f315028f3ae8798a8187993538c540c3cc829c62a061d6414e315021f3acc898a812b5ca644c540aace3a9a62a061e6414d315030eb20a698a81479d7434c540c38cba1a62a046e721943150236b90ca18a8187990530c540c3ac829862a05557114c315032c29cc018a8117dcd65c85408b8e6b2e42a061e6414f215030eb20a790a8117dcd65885408b8e6b2c42a061e6414e215030eb20a710a81179cf65485408bae7b2a42a043e75991215024eb9cc890a81879905348540c3ac829a42a045f73594215022e39aca10a81179cc65085408bae632842a045e7598c215022e3aac610a8117ddb53085408baeda9842a061e64d4c215030eb26a610a8117dd853085408baec29842a061e6414c215030eb20a610a818b5935208540acae229042a063564d4421502b2b90a210a81599d52108540ac8ea90842a07475348421503a229a4210a8196d4e6008540cb0a730042a065b53580215032c29ac010a819ad496008540cd0a4b0042a067351580215033828ac010a81b84856008540c3ac629c80a061d7614e405030e29ac5202818714d6190140a9ce5a9ca62054d72d4e53102ab38ea729881555c75394c40a3ce9314a62051e7498653102a7390c129881535c86094c40aace2304a62055571182531028f3a4c4a9881471d16254c40a3ce930aa62051c7458553102a7390c0a9881535c86054c40aace2302a62055571181531022fbb2a6298819354e6214c40c9aa6b10a62065553984531032aa9ac2298819654d60d0c40c3ce6b2c862061d6594e431030ea9ac1218819694d6010c40a3aeb318862051f7654c431030fbb2a62188147dc95310c40a3ee2a98862069a63580431032b29cc3a90819554e61d4840caca6b0ea4206555358752102a739ea529081535cf5294840acce3a94a42056571d4a52102b338ea729081595c75394840e18e8a9ca4205667114e52102b2b88a729
  | 24 => 0x30287a06994358043d0237bb2a4296810fdd563d0b40a3ce729685a049d73d9542d028f39ecaa16814b9ca5350b40b52e1a9285a051e7394942d02573b0a4a1681275cc6050b4096ae230285a06a94258042d023b38ecb996811d5c765ccb4096ae332265a062c6250951d023bbb2a228e810fdd563d0740a3ce728e83a049d73d9541d028f39ecaa0e814d9c65350740a68e2a9283a05b170d4541d028f39ca2a0e812d9d8515074093ae630283a04ad7218141d0358a0ac020e811b9cb65cc7408dae5b2e63a04ad7299131d022f39ecb90e81175cf65c87408bce7b2c43a045d73d9621d022f39eca90e81175cf654874093ae732243a045e73d9421d022eb9eca10e81b848560087408beeca98a72064d53588539032aa9ac229c81275db5310e40b34e1a98872058d7214c43902cab88a621c81669c05310e40c3ec621aa52045e73185529022eb98c2a94811bdd95214a40c9ac6a90a520665525845290326b1ca5214819358d5290a40c3cca21e652062d6494a3290316b22a5194811ddc5654ca408e8e2b2a652047671195329023ab88ca99481c310d524ca40c3ec621aa32045e73189519022eb98c4a8c811ddd95114640caac6a88a32066562544519032ab1ca320c819558d5190640c3cca21e632063564946319031ab22a318c811bdc9654c6408d8e4b2a632046e721953190236b90ca98c81c510d514c6408bee6b2a432045c73595219022f398ca90c81175cc654864093ce7b2243205647154921902b2392a290c81179cf65086408bae7b284320667654842190332b2a4210c81b84856008640938e6b2e812051f73597409030f31aa7a048193d8a62d4d40a3ae8316a6a065761987535028eba0c3a9a8117dd95314d40a9ce5b20a6a054d72d9053502ab38ec829a81555c76414d40a3ae9b10a6a051d74988535028eba0c429a81935886214d40aace2310a6a05557118853502acb80c429a81475d36114d40a3ae9308a6a051d7418453502a7390c229a81535c86114d40caac2308a6a055970184535030fb9ccba1a818799753d0d40c38a6b1686a061c53587435030e29cc1a1a819614e6090d40cb6a630286a051e75d8d435028f3b0a6a1a81879d85350d40c38a7b1286a061c53d854350256b90c0a1a812d5c46050d40d36c630286a045e73987525022eb9cc3a9281179db53549408bcec29aa4a065753d85525032a29ec2a928195d4c6154940ca8a630aa4a046f7654852502b238aa4292818758c53d0940c3cca29e84a061d7614f4250387390a7a1281c35c853d0940c38a6b0e84a061c53983425022f3acc721281171d563909408baeda9c84a045d7614e425021f3aec6a128187d8c5350940c3cec29a84a070c53d89425038629ea4a1281c3d4c5250940c38a7b0a84a049d73181425030e298c0a12812d5c460
  | 25 => 0x548855008798aa442a8043d494e2154021ea2a710aa010d6b7548550087952a242a8043ca5512154021e94a690aa010f495348550086b9baa42a8043cc9512154021e62a890aa010f525348550087a8a9a42a804378dd52154021ec6ea90aa010f636548550087b1aa242a8043d89512154021f44a890aa010f225448550087b0aa242a8043e85512154021e42a890aa010f605448550087b1a9a42a8043d894d2154021f84a690aa010f425348550087b0a9a42a8043f054d2154021e82a690aa010f605348550086adb9ac8a8043561cd6454021ad0e4b22a010d707159150086ad398c8a8043565cc6454021ad4e4322a010d7271191500869dba2c6a80434e1d16354021ad0e4b1aa010d707158d500869d3a0c6a80434e5d06354021ad4e431aa010d727118d50086b539686a80435a5cb4354021ae4e3a1aa010d7171d0d50086b539486a80435a5ca4354021ae4e321aa010d717190d500878ca1886a8043569ce4254021ab2e7212a010d727190950086b8b8c84a8043ca5084254021ae4e2212a010d7171109500869d3a464a80434e5d23254021ae4e3192a010d71718c950087a499064a80435c9c43254021ae2e2192a010d5a7390550086acb9c82a80435a9ca4154021ad2e520aa010d6a7210550086b4b9082a8043cc5044154021a74e918aa010d39748c550086b539462a80435a5ca3154021ad4e418aa010d69720c550087a898862a8043d8dc52154021ec4c290aa010f634148550087b120a42a8043d85052154021ec08290aa010f633148550087b118a42a8043d84c52154021ec06290aa010f637248550087b131242a8043d8d092154021ec48490aa010f614248550087b021242a8043d8cc92154021ec46490aa010f613248550087b019242a8043d8dd92154021ec4ec90aa010f617648550087b03b242a8043d8dd12154021ec4e890aa010f617448550087b03a242a8043d8d912154021ec4c890aa010f616448550087b032242a8043d8dcd2154021ec4e690aa010f617348550087b039a42a8043d8d8d2154021ec4c690aa010f616348550087b031a42a8043d8d0d2154021ec48690aa010f614348550087b021a42a80434e9d02154021a72e810aa010d5a7308550086acb9842a8043d8484215402187aed2a0a010c3f76550500870f2a4c628043875526314021c3ca8b18a010e1d5458c500862ebb4a628043879925314021c3ac9298a010c5f7654c500870f322a6280438759153140219ceec908a010ea6644845008752b224228043b198d2114021d8ac6908a010e3a54980500871caa4c0280439694e6014021cb2a7300a010ee121980500863dbb2a0280438e9915014021c72c8a80a010e5a63540500872cb1aa028043d848550140218beeca98a7a059970d4d43d024f3b0a6a1e812b5c86050f4096ae2
  | 26 => 0x53b2ca890843c9d965448421e4eeaaa24210ea7655512108793b2aa890843399d85448421b4ce82a24210dc67315121086e2b98a890843789c05448421bc2e02a24210da674d8d21086d2ba6c690843595d66348421b4ce931a4210da57498d21086b3baac690843b158c63484219cceda9a4210da674d4d21086d2ba6a690843c95535348421bc4e1a9a4210de170d4d21086e2baca690843b1d965348421e8ecb29a4210f865494d21087c2aa4a690843c95515348421e8eeaa9a4210ec76554d21087a3b2aa690843d1d515348421f0ca8a9a4210f455454d21087c2aa2a690843c155153484219ccec29a4210da67414d21086d2ba0a690843719cc5348421bc4e029a4210de17014d21086733b68690843395db43484219cced21a4210ce57690d21086b33a88690843595d44348421f0a8621a4210d657598121086b3baac09084369dd16048421b48e8b024210dc77358121086e239ac090843699d06048421b4ae83024210dc67318121086e2b98c0908438795263d4021c3aa931ea010e1e5458f500870eaa2c7a80438799253d4021c3ac929ea010e1e6454f500870eb22a7a804339dd921d4021d4cc890ea010ea56448750087932a243a8043c955121d4021d8cc690ea010ec56348750087a329a43a8043d154d21d4021a74e9a84a010d3974d4250086ad39ea128043565cf50940218bee6b24a010c5c73592500861fba2c7280430f1d16394021ab4e7aa4a010d5973d5250086ad398a928043565cc5494021a74e9a9ca010d3974d4e500878d2a4a728043c65525394021e34a8a9ca010f195454e500869d3a0a7280434e5d05394021ad6ea90ca010d737548650086f1baa4328043d8dd52194021f44a890ca010fa15448650087e129a4328043f054d2194021ab6e6b24a010d587359250086ad398c928043565cc6494021ad4e4324a010d7271192500869dba2c7280434e1d16394021a74e831ca010d397418e50086b5390c7280435c9c46394021e328621ca010d3a7418a500869cba0c528043569cc6294021ab2e6314a010d5a7390a50086acb9c85280434e9d23294021a72e9194a010d3a74186500869cba0c328043569cc6194021ab2e630ca010d5a7390650086acb9c83280434e9d23194021a72e918ca010f26544855008792aa242a8043d194d2154021e8aa690aa010c5e73191500862eb98c8a80430f9d0635402187ae831aa010e677648550087323b242a8043d8dc12154021ec0e090aa010c7a76d5150086ad39ea8a8043565cf54540218f4ec2a2a010d5a7315150086acb98a8a80431e9db5354021a74e9a9aa010d3974d4d500878d2a4a6a8043c65525354021e34a8a9aa010f195454d500863d3b0a6a80434e9d05354021a72e829aa010f2a54c855008794aa642a8043d294f2154021e92a790aa010f32
  | 27 => 0x431e5c265d0c218f4e032e8610c79701974308636bacc5a18439354e62d0c219cae33168610e2e5458b4308726a9ac5a18431d5d661d0c21caaa730e8610ce572987430871b2a2c3a18439554d61d0c218f4e132c8610c7970996430863d380cb218431e5c06590c218daeb3148610e2d5498a4308672b8cc5218438b5516290c21c9ca6b148610c7575986430871aaa4c321843395ca6190c21c6aa8b0c8610e5653586430863d384caa18431e5c26550c218f4e032a8610c7970195430868e39aa8a1843471d15350c218f4e13288610c79709944308637390ca218431d9c46510c218f4e03288610c7970194430868eb9ca821843475d25310c21a3eeaa188610d1d7550c430870fb2a8621843875954310c218bce7b2c8410c5d73d96420862ebacc721043879526390821c3aa931c8410c5f7558e420870f2a2c7210438755163908218beed29c8410c5d7694e420862fbb2a721043175d95390821c6aa8b0c8410e2d655084208786a9a84210439554e6110821c6ca8b088410e55535844208752a12c2210430f9d3658c82187ae9b2c6410c3d75992320861fbaac9190430fdda548c82187aed2a46410c3f76552320861ebb2a91904387992538c821c3ac929c6410e1e6454e320870eb22a7190439554d618c821c9aca9906410f0d544c8320871aaa4c2190438d551610c821caca6b086410ec532584320862f39ecb20843175cf65904218baeb31c8210e1e5498e410870eaa4c72084317dd56390421c3ca8b1c8210e1d5458e410862fbb4a720843175da53904218beeca9c8210c5d7654e4108716aa2c520843179ce65104218bae73288210c5e73194410862eb98ca208439354e6210421c5ca8b108210e4d53588410871ab2a8220843c554d4110421d4ac4a088210c3e74d96310861eba6cb188430f5d6648c42187eeab246210c3f76952310861ebb4a9188430fdd9548c42187aecaa46210e1e6494e310870eb24a71884387991538c421c3ac8a9c6210e4d5358a310861f3a4ca188430f5d2650c42187ce83286210c3d741943108716aa4c4188438b551620c421c9ca6b106210e55654c4310878aaa26218843b1589310c421e1aa8a9e4210c6d7694a210878aaa2a7108431d5da5288421c5ecb2a24210e2f655512108727b2ca69084393d955348421e1aa8a9a4210dc67390521086e2b9c8290843699d23148421b4ae918a4210e3765951210871bb2aa89084395d965348421caecaa9a4210f155454d21086e339c8490843715ce4248421b4ce91924210da5748c92108732baeca90843999db6548421acae1b2a4210dc673d9121086e2b9ec890843595d66448421b8ce73224210dc57399121086b3baac890843a959064484219ccedaa24210dc673d5121086e2b9ea890843789c35448421bc2e1aa24210da57595121087
  | 28 => 0x5218bae7b2a8290d1e73d51414868f3a6a798a439314d62cc52187ce9b2a6290c3d74d95314868f3a6a698a43179ce64d41218bae7326a090c3e7498f504861eba4c7a82431edd95014121c3cc9318a090e1d6498c504870f322c628243875916314121cb4c7306a810e5963983540872d31ac1aa0439658d60d5021cd4c4b06a810e7261583540868f39ea92a043475cf5495021a74e1aa4a810d3970d52540862fb9ac12a043171cd6095021a5ce5b1ca810d3671d8e540870eb18c72a043479ce6295021a3ae7314a810d1e73986540868eb9cc32a04347dcd6095021a38e6b04a810d1e73182540868eb98c12a0434b9c86095021a6ce2304a810d1e73d91540868eb9ec8aa0434e9c36455021a72e1b22a810c5e73181540862eb98c0aa0434b9ca6355021a6ce331aa810e1d6318d540868f39cc4aa043475ce6255021a3ce730aa810d1d73985540868fb9ac0aa043471cd6055021a58e4b02a810d3471581540868f398c0aa043475cc6055021a5ce4302a810d3671181540861fbb2a82a043875526315021c3aa8b18a810e3954980540871caa2c02a043879926315021c3cc8b18a810e4d63988540872ab1cc22a0438e9926015021cb4c7300a810e5963980540871d322c02a0439698d6015021cb2c6b00a810e6a62580540873930ac02a0438e95260d4c21c72a9306a610e3a54583530871caa2c1a98438e99260d4c21c72c9306a610e3a64583530871cb22c1a98439a98960d4c21ce4c2b06a610d1e74d4e530868eba6a729843569c35394c21ab2e1a9ca610c3f74582530861e3a2c129843569c35494c21ab2e1aa4a610d5a7015253086acb80a929843539cb6494c21aace3b24a610e1d64192530868f3a4c529843475d26294c21a3ce930ca610d1d74986530868fba2c129843471d16094c21a3ce8304a610d1d7418253086a7390c129843559c46094c21a3ce9b1aa610d1d74d8d53086ad386c6a9843565c36354c2187ce8302a610c3d74181530862f3b6a8a9843569c35454c21ab2e1aa2a610c5e7615153086ad380a8a9843565c05454c21a9ce5322a610d5671991530870eb20c8a9843479d26254c21a3ae9312a610d1e74985530868eba4c2a9843479d02154c21a3ae810aa610d1f74581530868e3a2c0a9843531c96054c21aa8e2b02a610d1e74181530868eba0c0a9843539c86054c21aace2302a610c3d76950530861fbb2a829843879526314c21c3aa9318a610c5f7654c530870f322a629843875915314c21c74a9300a610e3954980530872ca9cc0298438e9516014c21c72a8b00a610e5953580530870f324c629843875926314c21c5ac9310a610e3564984530871d324c0298438e5926014c21cb4c7300a610e3a64580530871cb22c0298439698d6014c21cd4c4b00a610e7261580530863d384cba18
  | 29 => 0xa66218c5d7694e310c70f324a7188631d5da538c4318bcec2a26218d4d72151310c6acb80a898863479d2514c431aaaeb20a6218f1454505310c6caba6c69886355dd5434c431aaaeb1926218d95748c9310c637390c8a80631b5c8645403187ce8312a018c3d74189500c63dbb2a0280638e5915014031cd2c4a80a018e4d6398b54c8733312c3aa643479cf5495321a3ce7b22a990c5e7318154c862eb98c0aa6430fdd95415321cccc4b08a990e2d6498b53c8733312c3a9e43479d35394f21a3ce9b1aa790c3e7418153c861eba0c0a9e4317dd95314f21cccc4b08a790c7a7019443c863cb80ca21e43475ce5410f21a3ae92988790d1f7550c43c868ebaa8621e43479cf54d0b21c3ca931c8590e1d5498e42c868f39ea8a16430f9d85450b2187eecaa08590d1e74d4f32c870f324a71964387991538cb21a3ce9a9a6590c5e7614d32c862fbb2a6196438b5506250721c9aa63126390c5f7359250c862e39ac9286430fdd16394321878e8b1ca190c7b7654050c872ab1cc3aa4439958a61d5221a3ce7aa4a910d1e73d91548862f398c0aa443175cc605522187eecaa0a910e6562984548871ab24c3a9c439958a61d4e21a3ce9a9ca710d1e74d8d538861f3a0c0a9c430f5d06054e218beeca98a710e6562984538863d380ca21c431e5c06510e21a3ae72a08710d1d7494c438868fbaa8621c43475d54310e21c6aa830a8510e5553185328868f39ea9a0c43879526390621c3aa931c8310d1e73d51418861f3b0a8a0c430fdd95410621a3ce9a9e6310e1e6494e318870f322a718c43479d3534c6218bcec29a6310c5f7654c318862fb9ac928443171cd649422187ee8b1ca110c3c7458e508863dbb2a028443479cf5495121c3ea8b1ca890e4e6358a544872b31ac32a243479cf64551218bce6302a890c5d73181544861fbb2a82a243475ce64151218bee6b00a890c5c73580544870eb9cc9a9a43479d35394d21c3ac9a9ca690e1c735925348717322c529a438d9916194d21a3ce9b1aa690c3e74181534861eba0c0a9a4317dd95314d21a3ae9318a690c3f74580534861e3a2c029a431b5cb65d0d218eae3b2e8690d1e73d53434868eba4a7a1a431b5cb6590d218eae3b2c8690d1d73952434868f3a6a721a430f5d26550d218bae732a8690c7b70595434863c382caa1a43479cf5450d2187cec2a28690d1e74d4d434862f3b0a6a1a431e9c06510d218f2e03288690c3d76950434868eb9ca821a430fdd95410d218baed2988690d1d7494c434862fbb2a621a4347dd54310d21a3aeaa188690e1e6550c434870e32a8621a431b1d56210d219c8e2b108690c74755844348672392c221a43479cf54d0921c68a8b0e8490d1e73d51424868f3a6a7992439514d61cc921a3ce9a9a6490d1e73d5341487162a2c5a0a43179cf655
  | 30 => 0x6550548c72ab1cc22a4638d95161d0e31c6aa9b0a8718c3e74181528c61eba0c0a94630f5da5414a3187eecaa0a518c6f76548528c71d2a4c0294638e5526014a31c74a8b00a518e3954580528c734a92c0294638795263d0a31c3ca8b1e8518e1e5498e428c70eaa4c721463879516390a31c3aa8b1c8518d2c72551428c71aaa6c2a14638d5506150a31a5ae52a08518e3654584428c61ebacc9194630fdd5648ca3187aed2a46518c3f76552328c71aaa6c2994638d550614ca31e1aa89906518e1e5498e418c70eaa4c720c63879516390631c3ca93188318e1e5458c418c70eb2ca998c638759554cc631c6acb2a66318e3565553318c61f3a0c4a84630f5d0625423187aed2a0a118c3f76550508c7172a4c4284638b5526214231c5ca8b10a118e2d54588508c63dbb2a0284639a5895014231c5ea8b14a898e4d6398a544c726b9cc52a2639998961951318dce4302a898c6d72181544c61fbb2a82a2634b5ca64151319aceb30e8698e5675987434c66ab84c3a1a634b5ca5490d3187cec2a28698d1d73950434c696b94a821a630fdd95410d31b1ae52a08698d9571950434c62fbb2a821a6327dd95410d31b2ee2aa08698d1f76550434c70fbb2a821a6347dc95410d31a3ee2aa08698f1771550434c68e382a821a63351c56210d31c3aa8b008698e1d6410f524c716b26a5292631bdd95214931c3aca21e8498cd47158e424c726b1ea5212639358c5290931e1887a928498e9443d85424c63d380ca212631e5c065109319ace33266498c5e75193324c62ebb4a999263539ca54cc93193ce930e6498e2d64d4a324c716b20a519263359c6644c931a9ce52a26498d4e75d89324c6a73b0a499263939d8524c931a9ae02926498cd675185324c72b3a8c299263355c0614c931c38a8b1e8298e1d6510d414c74b326a318a631b9ca64d41318dae5326a098c3e7498b504c61eba4c5a82631edd95014131c3ee6b20a098e1c73590504c62ebb68628263875934314131c3ac8218a098e2e64988504c716b24c4282638b9916214131c5ac8b10a098e4f43588504c72621ac4282631b9c860550318dae4302a818c3f76550540c716aa2c42a0638e5516015031c5cc8b10a818e4e63588540c732b14c22a0639a98a6015031cd2c5300a818e3a64580540c72d31ac02a0639a9896015031cd2c4b00a818e7261580540c71aaa4c321863475d25310c31a3eeaa188618c3e74181520c61eba0c0a90631bdd95214831c5ac8a90a418e6952580520c62fbaac7a1063355c66390831c9cc6a948418c7a70195420c63cb80caa1063479cf54d0431a5ae42a68218d3970153410c70f2a4c720863875526390431a3ce7aa28218d3671d51410c61f3b0a8a08634b5c85450431a72e02a28218c3f76550410c62fbaac620863535c854cc431ab2e02
  | 31 => 0xaa9ec2994839554c614ca41a9ae52986520e5653584329070eb2ca7a0c838759553d0641caacb29e8320e556554f419062f398c4a8483175cc62542418baed298a120c5f7654c509072729cc4284839354e6214241c9ca6b10a120e4d53588509063dbb2a0284839a5895014241c9ea6b14a6a0c5f7654c535065b3acc321a838d9d66190d4196ae130c86a0d8d7294c43506cab8ca621a8327dd95310d41b2ee2a9886a0cb471588435070eb1887a92839358f52949418deeca90a4a0cb67198f425064f39cc3a12839358f5290941c9ac629484a0d2e75d8942506973b0a4a12838b9d85250941a5ae029284a0cb675185425071b3a8c2a12832d5c0615094196ce3b2664a0c3e75193325070eb2887992832d1c5648c941c5ac9a9464a0e2d6414a325078621ea499283a510f614c9418f4e032864a0c7970194325074b31ea320a831b9ca63d41418dae531ea0a0c5e7398b505062eb9cc5a82831edd95014141c3ee8b18a0a0e1c7458c505061ebb486282838758e4314141c3ac6218a0a0e4e639885050726b1cc4282839398d6214141c9ac6b10a0a0e2e43588505071621ac4282831b9c86054c418dae4302a620c5f7654c5310726a9ac4298839654d6014c41a3eeaa188620c5e73181521062eb98c0a90831bdd95214841c9ac6a90a420e6952580521061fbaac9990832d5c6648c841c5cc8a946420c7a70195321063cb80ca990830f5da54904418eaed2a48220d9573d91411069bbaa86a08834d5d64250441b2ae72128220c6e7218d5010636b90c6a8083179cc62540418bae6312a020c7b76540501072cb1aa0280839a5895014041c9cc6b16a998e666258754cc697396a92a6634b9cb64553318dce4302a998c6d7218154cc61fbb2a82a6639598d6115331a9ae5aa68798e365458443cc6a6b96a821e6317dd95410f31a3eecaa08798e1f7655043cc68fb92a821e63471c15410f31c3aa8b008798d2e74d4a52cc716392c9296630f9d06054b3187ae8302a598c6f7654852cc697396a9a16638759443d0b31a5ae92968598f0c4354b42cc66ab9cc3a1663a510d61d0b31c3ca931c8598e1d5498e42cc697396a8a16630f9d85450b31c3aca21a8598c3f7655042cc68f3a4a599663279d261ccb319ace33226598d4e7295132cc62f3b0a899663479d2524cb31c3aa831a8398c5d7610e50cc63dbb2a0286634b9cb6395231a5ae5b1ca918d1d73d8a548c68eb9cc52a4638b5886295231a6ce2314a918d2e72186548c696b90c32a4634e9c06195231a72e030ca918d1f73582548c68eb98c12a4634b9c86095231a5ae4304a918d3671182548c637390c0aa4631b5c86055231a3ae7312a918d3471589548c716b10c4aa4634d9c66055231a3ee6b02a918d1d73181548c697390c0aa4634b5c86055231a6ce2302a918c3f7
  | 32 => 0x563dc95410d32a3eecaa0869961f76550434ca8fb92a821a65c3dc95410d32a3ee2aa0869951c70550434ca66392c221a65875516010d32c38a8b1e849961d6510d424cb47326a5192658759043d4532c6ac9a8ca29947776544514ca3b38cc9a82651d5c664d413287ce930ea09943d74987504ca3dbb2a02826587dcd6414132c38e6b20a09945d76d0c504cb0eb268628265875904314132c6cc9308a09963564984504cb1b322c2282658d5916114132cae86b08a09965443584504ca3b388c0aa0651d5c4605503287eecaa0a81963554584540cb1caa2c02a0658d9916115032cacc6b08a81966662584540cb3930cc02a0659c5866015032c74c8b00a81965a63580540cb35312c02a0659c9856015032ce2c2b00a81962d5498a430ca8eba4a62186547dd54310c32a3ce7aa6841953571153420ca9cb80a9a1065879526390832c3aa931c841951e73d51420ca97396a8a10650f9d85450832a6ae22a2841953970151420ca1fbb2a82106517dd56310832aaae22a6641955970153320ca2ebb4a71906587992538c8328daed29c641945e76151320caaab88a899065565c0544c832a3ce9292641954d75909320cb862a28499065635d3634c832a9eeaa1a641943e74181510ca1eba0c0a88651ddd95114432c6ac8a88a21967151580510ca3b388c8a80651d5c4645403287ce830aa01943d74185500ca3dbb2a0280658e5915014032ce2c2a80a01954e72d4e53d0637390c0a9e831b5c86054f418beeca98a7a0d1f7654c43d070fbb2a621e8347dc95310f41a38e0a9887a0e1d5358043d06a739ea529683179cc6054b418bae6302a5a0c6f7654852d068f39ca5a1683279ce61d0b41a5ce529a85a0d1e7394942d065b38ec9996838759443ccb41a9ae729665a0f0c4354b32d065aba4c399683a510d61ccb41c3cc929c65a0e1e6454e32d070eb2886996830f5d843943418f6eca80a1a0d4e72d9253906a6b96c929c83475d36294e41a3ae9314a720e4d6218a53906ab388c529c83539c86194e41a9ae430ca720d5a7018653906acb80c329c8347dd16094e41a3ae8304a720d4e7218253906a6b90c129c83559c46094e418dce4302a720c6d72181539068eba4c4a9c83551c56254e41c9ac4312a720d5671981539068fba2c0a9c83475d06054e41a9ce4302a720d4d7218153906ab388c0a9c8317dd95314e41caca6b0c8720e5553d85439062f398c0a9483175cc6054a418baed298a520c5f7654c5290637bb2a4294839694e6014a41cb2a7300a520e5a53580529072ca9ac0294839a5496014a418baeb31c8520c5f7558e429062ebb4a72148317dd95390a41caaa7b0a8520e55531854290786a9a84214838799253cca41c3ac929e6520e1e6494e329070eb24a71948387991538ca41c3ac8a9c6520d4c7254d329072
  | 33 => 0x6428bce630aa12145d731855090a2ebb4a62848517dd95314242caca7308a121655539845090b2b29ac2284859554d61142428f6eca80a121671615405090b2ba9ac329a8517dd95314d4295ceb31486a162e7598a4350a56b84c521a85635ca5310d42b2ae329886a149f7654c4350ac7b92a621a852b1c96110d42d1cc7a9484a161d6310f5150b2ab1ea328a851ddd951145428ece331ea0a14757198f5050a2f39cc3a8285175ce61d41428f6eca80a0a161f7458c5050b0e3a2c6282850f5da4314142c3ac7218a0a161d6310c5050b2b31cc2282859558e6114142cacc6b08a0a1655635845050b1b21ac2282858d10d61141428ece2302a621475711815310a2fbb2a6298859554d6114c42cb2a6b00a62151f7550c4310a1ebb4a9210851b5da5490842b1ae7b22842152f7550d4210a2f398c0a8885175cc60544428eeeca88a221655635445110b38a8ac0288851d9c463540428eae231aa02145e731855010a2eb98c2a80851edd95014042cb2c6a80a021671615405010b32b14c3aa6659598d61d5332a6ce3aa4a99953671d9154cca3b388c0aa6651d5c4605533287eecaa0a99964e6358854ccaaab8ea9a1e658b9516210f32aaae3aa0879945f7655043cca8fbb2a821e6587dd95410f32a3ee2aa0879951c7055043ccb0eaa2c021e65639c843d0b32c3aa831a859953674d4651ccb1a38ac928e650f9d0605473287ae8302a3994777654451cca2ebb087286651edd95014332a6ce3b1ca91953571d8e548ca9b388c52a4654d5c46295232a74e0314a9195397018a548ca8eb9ec32a465475ce6195232a5ce430ca91963561186548ca8fb9ac12a465475cc6095232a5ce4304a91953671182548ca9ab88c12a4651d9c460552328eae2302a91951d73985548ca96392c2aa4658d5846155232a5ce5302a91951f73581548ca8eb98c0aa4654b9c86055232a6ce2302a91953571181548ca1fbb2a82a4659358e6215232c5ca8b16871962d54d89438cb0f2a4c721465875526390a32c3ca8b1c851961e5498c428cb0f2a2c6214658759654cca32c3acaaa6651962d65953328cb16b2aa9994650f9d0605463287ae8302a31943d76950518ca1fbb2a828c651ddd95114632c74a9300a31963954980518cb1d2a2c028c658e5516014632ce2a2b00a31943e74185508ca1eba0c2a84650f5da541423287eecaa0a11963654984508cb1aaa4c2284658d9516114232c6aa8b08a11947b76540508cb38b0aa0284658dd516195132caac730ca89966562986544cb2ab9cc32a2651d9c460551328eae2302a89943f76550544ca9ab8cc82a265339d662d0d32c9ceb31686994cd7098b434ca9ab8ca921a650f9d85450d32a3ae72a0869953571950434ca1fbb2a821a65635ca5410d32b2ae32a0869945f76550434ca4fbb2a821a6
  | 34 => 0x8a0a1e4f435885050f1721ac4282879998a6114143ccac5308a0a1e66625845050f32b12c22828795d0d6114143c6c86b08a0a1c3d769524310e2ebb4a9218872b5c86050c4396ae23028621ccd721814310e6ab88c0a1887875d76550c4393ae5b2a8621c9d71d954310e4f386caa1887879db6550c43a3ae1b2a8621c9d71d894310e4f386c4a1887475d66250c43a3eeab128621c9d72d854310e4f386c2a1887475d66150c43a3eeab0a8621d1d759814310e8fbaac0a1887639c86050c43b1ae43028621d96711814310ecab88c0a1887875d46050c43d1ce43028621c9d721814310f46b90c0a1887235c86050c43d2ce23028621c9d711814310f4ab88c0a1887255c46050c4393eeca1ea421c9f7650e5210ec7b92872908727dd94354843b1ee4a1aa421c7a701855210e3cb80c2a90871d9c460548438eae2302a421c9f7650c5210e37bb2a429087c350d5214843d2a87308a421e95435845210f32a92c229087a650e6014843d3286b00a421e69525805210e4fbb287a888727dd94394443b2ee2a1ca221c9f7650d5110ecbb8a86a88871e9c062544438f2e0312a221c6e721815110e36b90c0a888727dd94314443d1a87310a221e8d435885110e3bbb2a228887c550d5114443ccac4a88a221e99439805110f4ca1ac0288879c545601444393eeca1ea021c9c7650e5010ecc3828728087271d94354043b30e0a1aa021d3a70d0d5010ead38486a80874e1c14354043ab0e0a1aa021e1f7650d5010e8e3b286a8087871d94354043a3ee4a1aa021d1f7150d5010f8db8286a8087471c14354043e30e0a1aa021d187050d5010e3b388c4a80871d5c462540438dce430aa021c6d721855010e4fbb28628087a350e6214043d1a86b10a021e95439845010f4aa1ac2280871edd95014043cd2c4a80a021e71615405010eab38ea729e851d9c46054f428eae2302a7a145f7654c53d0a8fbb2a621e8587dd95310f42a3ee2a9887a151c7054c43d0b0ea9ac021e85559cf51947428bce6302a3a145d7318151d0a3bbb2a228e850f5d843943428f6eca80a1a155671d925390aaab8ec929c85559c46294e42aaae2314a72155a7018a5390aacb80c529c85475d36194e42a3ae930ca72154e721865390b2ab08c329c8547dd16094e42a3ae8304a72154e721825390aab388c129c85555c46094e428ece2302a721475711815390a8eba4c2a9c85531c96154e42caac230aa72154e729815390a8fba2c0a9c85475d06054e42a9ce4302a721556711815390aaab88c0a9c8517dd95314e42c9ca6b14872164d53d894390b0eb2ca7a14858759553d0a42c9acb29e852164d6554f4290a2f398c0a8c85175cc60546428baed298a32145f7654c5190a3bbb2a228c859694e6014642cb2a7300a32165a535805190b2ca9ac028c859c5456014
  | 35 => 0xa00800880000120030018020034000002008c00c007001002c00202200b001000000000000440040040000014002002001800800c000000802c00400a0030000000000003800400400800380380000000028044008012006800000200c00000000000000010004002001004801c002007017001802a00d0000008006000003800400c00b00200080060020100014006023006002c01000000000200100010010000048002000003c0060000000008000004007802006c000001800800000300000ac01c006000802000000000580140000070030000000004000001000000200500cc002001000000002c0010018004006007002800800600600a800c0140120000028000009000006c00e00000000080040000008044004000000000401600a006001800e001001800c064000005001800000c0040020010001000001c01000f000009400c000004802003c000005002000000000c8004004015002800c00200100080240000010000004000000000001c00000c009000c0080070068000008000002001801a00d0000000026010003802400000d000801000a007000002c000002008800400400000100100020040010000006005002800000000901d009401e006000800400001a00081c4000003009003400000000c00040120040028000000017003002000600100980280060250050004022005000002800c02a00d0000006002005806c0000020008030000002002802803e01b002000401e000001000000600000f000800e0000038000002000001803800200500c8008002000004002400600100000000020010000000000011000801000000c0038000004007000000001200d000000800c007001800400c00a003800c01800600280300000040020048006000001803c0120020088000000000004002801c01d001804400000b0008024000003007000000000a0010004004001003800401601200f000c004000002000000200c000000801a000004800000c0010008000004001003000c00000400400000000000038014000003001000c0160030098008000002004803000201800000000120000030024028000006800000a01100300200220000048018004000004000800000200400c0000022000800000e00100a000000400600500000020110130000000007003801801c00300a0018004001008000001400000000000380060000000004008acce3a94a5a1c767118152d0e3ab88c0a96871bdd95214b43acce5a8ca3a1c6e7218151d0e36b90c0a8e871ddd951147438f6eca80a1a1d6671d4a5290e3b388c0a94871d5c46054a438deeca90a521d6672d465190e37390c0a8c871b5c860546438eeeca88a321d5970d0e5090e9d38686a84871edd950142438deeca90a4a1c77765445150e3dbb2a028287565c34314143a72e121
  | 36 => 0x2001801c002003000c004014001002c0260020008000002007012000c004001003800800800100200180020200060010000021000000000c0030000004002001003000400a000000000002e00000c803400000100200b80000000000098002013004000400a004001800800000d000000002a0000000008006003002000001e004003000c00000c0000008000009001800c00000100000080100140040060012007000007c008000000800c002000001802800000100100c0006000000001800200000080fc004010014800800c001003000400601e002800400200100000240080090060004002000001000c016005000800c01200600500140020000060060006000006801001a00300080c400000900e0010016001004800000600f007000000800700f800800200e00200000020020060004006010002001c0000000038004008001004801c01400000b803000c0070088000002000000800c0000000000000004003003801800804b0000018030002000800401c012004800000600c001000400600e0028018086002000001000e004001802400600b000802c0020000010000002000000000c002001001800c000018000001403e005008803000e0010008000008003000000000600100180000200090000010008004005000000600300600080080000010038002001001000c00200200100040200020118010004000001000002e00e000001800000e004800000600100f8040008000003001c0000020098004034002000800000c00000580000000050050030014002003801401c000001000804000600180100320000018010004001001801400c003004000400c00200300000080070010000000018000804400c00100100000160000000008000002000001c01000100500040020020010000002000000002400e0020048010000021002801c006000006802400a002004806c0020000008020008001000802001800300080280060030000000002000005000c002018000000400c00500a00180080040058080000006000003800e0010000004006000000000800c0000000010004001007000c0000260008048002003004800400000400300200000030008048018008000801c0080040028000002001007800001e0000008000008001000800403e0000000014012001004800000000300000080020000018028002008005000000200100080040020000020000014001000005c00a003006801400400e00100040080010068018012001007001400000000000080020000000000000000005008c00400100a0004004006003800402400000080100020010008008008000001802401000f005000c0000170020008002002005000001e0010020008020021000000800c021000000000a006006001c00c001000800000200100b80680
  | 37 => 0x140000000048002001002000c00000700200000000090000000004000001001000e001001003401800600080100020150038024002000000000c0000030008008002004001000400000700200080020130018000000008012805c00a006004805c000004000000c0020000058008060004001800001600d001004000200000000240040020000018002000008800000a0010000000000000000000001e00100000280020010020000000001002003800a016012007800200000200080020000038000000000003802c006001000002001a002003800000000500f800c000000003002800c002000000800000500100040080000010008000001001001000a00700000080000060000000000002001000c000002000000c00000700000000420060038004000000002008000000100100080000000000000006000001000800e00000080100320030018000002004008013c00400500000000000050000000008004000001c008001008801c00000600400040200020000000002004000800802a0050020004002000000002400a000004005800e0000030030000003002801c000009001000000001000000040000530030028002005000000801a0000018000012001001000000000a00100080160040020000004000004000800200d0020000006006000801c008000000004c00a001002000c00200200380100000000088000022000000802800001700000040060040000004002002000002001200a00681840000110000004002009006000000000000780180000010040014000002000003c02a000007001001200000480900000000040000008000001000000000300e00000040020008000000000000000c00600a0010000002005004000000000a0018020020000001000000c002001000800201200000040040070008038008007002003c00200300400480080090048038000000001802000800300000100000020000000000021001800c00a0000090000000004004000801201a000800000a002001800403800d0070030000015003004000c002000000c00a0000000000000009002002c000003000000400200100080140260000048004006009000009c008001007000801e00a001002000e012009802000e007001000000000100d000000401c000800c00000b0000024000002000800400c0000030000000006007001800a000002802002e00c00b8010000005007802000e001006800807600000d000c066002002000c012005005800001600000880140000040000004004007000000c00600e001000000a03600080180000010010000026004000000000200300880040040000000000002000000000001c001002800001600d006000004800d0000040012000000003800a001004000000000b002001000400800380100000010
  | 38 => 0x194c508800010f9bba8f918f628f85f0734233a0002b7c00002ca9b8952e107973a627064e7279706354004e8fc25a00002302923acbca6c9d70048084274c8e9e263131a9112db2660074400000c2982899607492720c90000507981c000187a60d9f64b0b052e0581e0c2fe046c2392886297a5949252a564ef159a9178ddca3286f6746184aaa9120c04b00d27dd1d6479b2174494237a12319ca46d12460fa26bc9489072b3c851059328aa5400000a6002f29a12ab800000009e115f20c5800000000000001e34361abaaa28800013c03487a2ad9e30e0c5e00020da94d01dc50000007bb9178009808a4430cfa13d91aa0001e020000f2200013449552abe0002d040002afc8b7a01200000000002d2a536a85a0001f260002a06a1d0c9459215cc1fb8a6ea5d0000a130dba43117dc132295a7889ff400000000000000287800000011c600024183f88ce4832976838d992c87623ae7f29c64000000062b800005b0ae49a417be1f516d85e4953c81880000492dc800010800000f604121c005a885ae000257255d8ca20618cca19e254c40c9e2e00023a40001a1e7de00005de814a9aca10248a9adc1d6224c81ca82660824664170f76055000056a80000000b9a49f8e6aa41853416d8000a97800082aa7962ec82ea6d51978b091cf08e386ac000000028aac0000000000e0800017da94600000003eda688761ac469708044378000012002ec0000000000228a37b155819900001fe9b70a2900000002704a7500000000000000239800000005330ee0a6992582a99128000000000000b43cd000020425bc6fc126e0000d5cafd8482000230a0001fe4799199684b252c92a8000035865045a0b3c5b283da9048b483eaa9c0230177e39317ae0000662585abd82a5035c73380005c697c800018540931ef2b450000000231a0000000074198e753000094991fe000176626390021ef13a02d39c6c130915c80f1f564619a047dfa3f6b7700003399696253a1d0000275245627cc8b21d1600011081ee2b268578a669e515d22160adc8c6119088d07862f8023606c802a000000000003a0000038020000000000001001e00000200280100010000004010008000000c00400200300080020020038014008009000801800200f006800401600000200040040080120000012023001000c00a006036800800000900200140080020088074002002000000400400800180180000010028010000003000006400600100480140060000008000006004000003c0000000000010000007000001800200a000800000200d009000004e000002000002800100c0004054000004804400c005004809800e000001000004001d000800000200d001807c0240000030014006001007000800a00d000801800000600e0000004000000800801603400d8000
  | 39 => 0xe0aef84ba0002a3a0000de471081d60002a667e90c8686fa9d624b0b6047b2702ad88ffa6ec9fb8ac520d6a5d80000bc207c2d29fb058f98dcad9abaeb1e10620ad9db81af8d4c33f29560000cac2f794628ad2d303de000000005e635f94366890ade68300000000a12b5a89ce00024a465d0b5a799a0e4ae802ae00010b60000000000247c6610000000294e0dd1b08ae4000000016a609b19d00518b5239caae696c800000000000cc125e00021c2201a9e600015de13a87a000b8e9a000000072c8cbea2e98967a993e8000139800022d866d003a229ab4897580000220000913a27898f9a0619200008c9196047c141a00900cc63802462572be012c1a1492096de0002d8852f094a00023c6000141412908269e4973c73893d865a88c2aa280008dc8edc0000000b16991e0000e1234e8b66a9c13ae8df1546000000075f82981c90d063aaa894000044ca84000046c9d48616919a8db8000584a22668b86884a6152034680003a1800067306f42e3966e596a7d6337a52a05a240452fa77c53d80000001f0c000000083daa04a249f9400013645b10000000000000017343590174000000000011d069a9152a298000000157a49208560000f9a0001c6a35d80000000000000000049f26f871c81529140c6c1901776609ad80465276e6a016226f994dc528000051d9d12251aad836b8000000000001c224e0000000a48800096b000012500001241e6e95e2800000260c00017000001d3a5be8fe8284019818b0ad0691067491913180000ed40001fda2a30db80000fe600005fc75a2b080002caaa3e863000000006ea8000000000024408f400025360000470b558d8c575000001900001f702a8921a17cacaa64e54d0c0a1a79fa07942d7aac7800000021323820000349993486000004b00000753996c2068ea200000000000000864a84000014f20002a6806581e80000000000045849a98522251a0e1959af0496948439d0df00b3a0e08df9b26810a1a86b001b49fb00000001242882800062417ec7bf900a38c91962cb9c262660000af41b640a498b201f800000000004d600000a0082400019f885197700000000b34ad349dc22723c2a926813ad2888590368be000018598baa17174027900e4a708430b399b480001f9070f800023d89d6000000000019b800000b000000004d489f282c80007670f6a9ec800045d064a5d905ec197aadc00000004be8d086d5a4e206f83c447089542c902bc141821227413ac85825eea4510243b4ac0c34fa38a700833c376acdaab495829cf00842be000052c00009f50f905102b0c0a2a2ae0e580002ff89c402a8ee630c9c5a7f98eda5652a4c18f2bc819125fe0f50a905278000708075c9930000b439bf844f89ea70e91765dc81849e62c760000d4e83e2622000036889401484f40c4200
  | 40 => 0x7d9cde9a9a86c73b19329078e0e4a707620eb8632b5f13627ec9bce11800009cc924e2ac000041800003fb0f1c8e98000a4ca5a2119032eaf3a7e028c800091fa2ce6fb19a400b12e21cb8038a580358064800019b273069c00000000000489884e65418786f8a1e85a32c3a637acfc1dd871e4fb1928000042e9058f3c00027d2747ab7a494a70a020169e82d21e4006946411a0000000275e56c0cea91a935a782aae82c6806a8308f52322a844ac420be7b505909fa18b45038ba823e0936591a22271300002aa93da87180003ee00005f5a5fc8171eea33b07e4719810a000262c8d706b6000114a2d3116011200007209b5e86d800000000000000144111a2e6aaea78a57b0c5622725186cf96e400000000001642000000000005c00000c0200021f2824a8364f1ac567691d720002ba42ac80007511d906e922b845fa342643877274d80007961b7ab5b9fd69f4114687b80009ad8f2e3d58000000000012380003161ba00001cd43c6262442f00000f41f1a00019aa14f81cc28808ca8f686d45658000000000045c000031d80007659f16000159039f020a00003be000000049821e0457a4369bb17bc755ac884220b38b6603c256c8fceab92a127cd9b466b30c9258b83840d1874e61b21d666812180002364a3f071678a06083c19e3e0a38b8aa5f0266355242255226c88d31fb40002c74abb12e67f104409e81fa25538fe04339736828a6aa6ca207827000084a5227c1ac87c424a96f67b8a166656aac8b69962613713462771cb672907786322d5cb3a150e617905a86124727d10c20169852090905285aa1502abfa7240469902a238736530800040193480409528a31160825219520aaa12a9868e422b184e82c08000b441a22915000001587660000a9eaa18f4a4128e9297c8c3c61981f0337181a426a9ee0e9a89e480a104756a4620e884ee14380000000c624fc00000000afe24e94e00001c541d400007b6000000000001f4985632c04545f10000000091a000000003ca96a000000059fa17670586581c18e0c00018fa576000000006de000000088c21b21ed2ade571ab689d6294800001ba626975e1cf80001be1aec8c21bd6acf878a2dea89a24a16702ba2c263b5958600000000000a3a358a15021f800017400000000c1eb7083660372d0c6e48840000053a8d180003f425ec520000046a132e65101d43ae12d40fe80000000000b3d08726e3a1f6000006287e8bcc7771d7aae9a92c50aa66e74211ea735800029d8d5a7508caeb509d144ed9d8e4cf9180b7183f400002c80f71b78999abb827682c0a32010c10d9cd2b179d5081a27ce5aa8230806811e8ec8000a24000076a800051802e004a807a00024d6000083442b9f30000235472290f64d800008b90eb039522aa16aa14c45a8af094c9b0c488a3c200009
  | 41 => 0x30c00000000000000a4f1f1c186800000000000000c8267995620001e72000129043322f64958990404851aaba916c03e84e079a00008d3800060127220000000000000030e800000000006e68000309000097a800005c02de26d9a383e7800080421861ef8c9c831a50240b9432000000097d1b9699c9ec03af1a6400011022c00000000021400000000c8984800000008e3213e439800005e163a0ff2646225ac103891f4055f0e789d4101801492a48ff84d40eca63231f1f320000cda790000051f1a1a1a7188a32a9b2aa0885aca1518c2741000031e182461115649702236a40132a15aaaae0fe245a4b588ee8ef08783979fd03a5a9b486e9d8400021241bca936b7006340861b660ab109651200006759e240000800398a7e29ef9b8021d1af65d80000460a68696e087c29887329e9a328a070ad44590fd2297085a2719a5846b00008432d767de98642f3a56e00000000f4a3be2230eca24f93921531e9200027260002812000179a2078000000000080eaa7c1f2a2bc173000083b817c9ba954c000000022e970c702800020a184e07287825b20b128d79b7e0000ed0094179e079a0ea9c61288ad728482bc80000002aa0b2284842ca0000a5416560001c2c820000000000000000dd80002bc20dea6ba3899302000005a00000000001200000154079700000002a58aab08fa02780005460ece31c00002ef8000000274a00015da3bf828600000009f900c0000000000027b476d8e440d80000a2223c02cca8d4442800025d19389479eca9fe010e0002cc200002dc310173800000008ea239400010ca000190694c0e0200019a60000000b5880000c1913600000000000000153a8ee00000000002b2890c0830184219017808d44289eb699b02e8b2da7aab328ef23a725fa737090000000003798f1013c9e04000298600000000000000482ab8600012dc3b000001448000afe85860000234adc848a75e297e00025044f28000000199409880d02da1334128ab9a1140f7a000025c0002b6ca081b8a62c00fc51786e2365a1e275d2bb2a60996254895c01d0131e4810000b4b83ee466179c5d4005044ca9f057da29a0002dc4000186865f92de00017b88af858e48d0eea3fd0000000257e000187273920de4db80a64150dee9d52af2b652b12000000058080000002dbe53d10c05b9a99e982029c38b21b497980000000cd200000001508000000000000000000000fd407b2db631492c83afad0836f80000d8aafab0a800000000007011724a6297f4000130a13f8d32000158c00000005bc80000000e3400024785f40000000143c000166034a071452a97122e89b00816a6940000fb41caa592802120600028242dc157039f8eae3d60000461000081b24744e4000000015ce01e04d66d7000000000007e10000acb908496785e84
  | 42 => 0x4c88a287858b360a999ba56e0000000086200000000000b9800000000000000000000000000000002cee5c9923e46b80000002d2c3aa13fc0001a78a228b468949df00002b160000b960002a464ba13c08661b4408f9b4e00000009b90000000000000000009c509e200000000b696b02588000adfa0e200000000002d3e378ab6e0002de6a548a7e6cb27881a50acc4b184ca70180000c28b840000000000000025c9eb87a30ab43ac9e5e45380004b680000000000000210a0000000000000092ba0180130f30972118a0000e386beadaa000000084d85840002202ab6a7600001664000000000000004798f3600000008ee054a92b1014a87000000000007a6800033010dc00000000002310000000000000002708684388aa520719630a20241c00019ee62610280000b6c36aa710283839e6dc800078c00003ea272c0e30000950a14451d1f0638f800029f15e275600008631e26000000000001d800003807a80046a9f89fc0e18ca06029366634155a581821c6ce9ede25487de4b2939409ea2cc54e109464f8c6648f215423f9d2209d11fc8a1003418516f08771dd077b9c7ab4587207b9101e69c800000000008ec000094b80001898276646a34066d800000027f67ab80001a1aa360001d204d0217a965aab2863aad02281d462aa248a7171aae6a58000000159ca36976a0002878a859bcc90ea128b3b1cf800000009d000005098e709d7000030620d2121ad78000009c760ac2e00029540000000000116e36c800016c83ac73621224360bd85ae2d4cb6122a606c272e2039e7e6ed06a846f0000102000000019360000bec12f00000b600001fca8bc08e0b18520835e0b100000540000995a428000198200000005ca10228962d66644000000001e2a9ca9e0519813a000000000017e40000f5a000202a80190b0372000000009cc7a880005e089ca95e8000a9d09f40000000217a63a9d6958e4868098000097a000000000016747428308555055e000076877f9b32a0a8b6261800000000a44a9884dab1280bc10a858a00017d200002609971b6a4ac8000639800000000002e780005962238000000000000009a905780000568000000000013760002850a302b582680000590148874a800096aa7565bbaa400001a16a20aa42000000020e2d125e880002ed02be48380008ca88b4a078000000080850a2bec000000000014f80e6000000026000002b56108930453a288c37492664fda920b6880000000b90437ac30800133043a01ea8258f9c3e988800001dda1a29fd27aeadb86a31c0c8daa9ca60500005998b8c84c07ce8e714a678c825855a05b865199206030000000000000012a2000000000003b67128000000112e0000000b0600000002aa80000000722000037c89ae1fa25be3f0982e00005c200016904b9095e5d32
  | 43 => 0x1f0465988a4396a410125968a727000000000001b080000002a483a2a23e72b2c860e80b265579e0e000040e0f99882000150653aa17e923037c4a7a69c2f48e6636687ba6218fc04388aee000224824b9efc98500004ce0000b281e600000a7000022d60000b064261aca4820770000174600007642b8293400000008148000000165000000007398afc71a157e00000000001dc06c6076a4ae0000b19015e0000baca4597ea97c2a98b291402aa896ceaf28b401b2a4b800000000e2851ca1c80000000000000000062007d8792990462d80002479992a160000269890c645945a6e50000000079ca8d1d80445855a7e000006d880008989c44a9e15dc0001c964530000b6bac1a4c5999e7eba01ca981f9a12cab603d7000073b897600c800000013100000000000000087f2356000104c4779cda902155251100000001f660001d2c29c8bd620098f869d043a0001dbeaf7108600000000d902207c390c2b1f98d82ae881866b819a00027d84ab2a0a12811a00000000000000061fa84aa0129ea0241cf292d24c4a28188400898e4936103c19f23844a19148b1c27c679daa9283211501ba184200018f424e06ce9ca16c62e70356a7d199cb6b24b28e017e6000156057992f20000f647be2668000139c2cf88505e19b2e0b4000025910823ba1f969d0a44c7a00000000000000000008110aa20dc251000019e05b30a3441e8cba76b0eac1c689ec000188e7d51b683c2000000027eeb4080009372a1e0002bf0000290a0b98dce342800074a0a86ae0aa2c43ea11603810349789816010a8961398d809202c44000000030b00000002476000000059c95b426190a40002b98aa200f6b632c207212d9c81785dea8507ae00014500979b3464729da5861bdc9d2088e92104340000000000273457f9f626b2000062f144c078243800008760000ffe58e087a702220468000007aa1ec6b29a9582802be80df93506e180000c4a85662a06a4312202c9b583e086b9f9c869060a092237492f00009a086b47ed8c260001f201fa895624c9b12a2707f800007564a829fc730130e076980e7dc8a0602ea67473d89f6721882053486c80000a9c0000cc2069137c000066679eaa809879314b5c8dca5de00da12b8000000000000009a4b4894ae228972e04b87a20002664774a2640000f9400019423b0a3fc2368f96675060eacb224a2a21a42294017a51a95ba0472070b31967a8c0000053b09ba17502fe4c726ee76f215815d834c4be1784000033a4589e084b1107e6a415a6025151469e8f2400022e2000107c0588000000215621aa194aa39ebe7b9ac602af187c1098f3a9c5ab8c28891140ac1822781943831d02561a99306af989b222b07a8000165c49c0530a73093c79215d01510bd05c72dbcab100007c6292e76d28d6000126c2ee0414
  | 44 => 0x49a6243248507b293aa72a3411580757ad8e57598ac8baa7c04f700000000000000000000000006f0800000017147308000000141656a1f8a5150696aa6ab3c9be86981d82d9a1b40d160e916d26ada5827329d248c894d040f8742b4f11102fd87e27be93e0971844e29a800043226b4000296e34e0d6a03fade000000006b8870c0c99dd60000000000000000000000000c4a00028a843e229e00029d2981263c0002c346448000809000042e00004c9867e00014a429ea1380000000a3b00005dd015c00022c2a718a1609a9142015000014b0c8e25a0bf28210000787a0ac0f614983758e1821b8c22942ab8a17227c4ac187c000000000000ace000117a00021a61bb0af600028ea6ac0bc8924a106874801697680004af00003d799240001f4c0000270000000081dad26000000000026da0002094000050a000247a000000085c870000028b494510ee0002b2000015c20ea9dc20000000000242c000209c00001769730000000000000009500001f14b170e1672c19302b892f6706235212700002ae00006cc000021b230e19a00001aa9510ae495924569aa0000186206f28626f62280000088600000009f691e0ac380001ec29103448ac860e079a0d4852a0000000a8001fc5251e44661a6b84380d9228907ec00000005bf2c7266f0000b6c11cc0000000000000091700000001d30b6d285230bad4083d1cb8833a720299269a7b2176e6c593888fba1ea0faa9ec9de99a82b004fc35813a251e9c569c18000000045615f210e9790000521a6a221480f40001680028281a43480003c39e708310000000163458507744ba9dd82868040a332c32a430a0a5fea1cc422898091b2c04a82011220c895a910820c02d89de79d23a2234a27e83f292825f00009bd09942628000ad380008eeaa9e7c8a344326a39ea8e280884e9aaa9b110f090394c084b8a18820a6e6b1091f45289ebc3650e5677521f418606908c480002491e7c0000ac425b09586e985fab161ee033800009e9074a77c870e34b2cfe3702c1675f250ea52a2245c7a6f642c800004f97ee0001188b258000181abde00027ea13e11c031320603c10794b73a0982a2a5d21b624e6313a7b668f80003e81ef01d51ee808888eaaa1036e000172a000003e78729687d1a610419a3d46629fba0a682524059f2a4f0a04a4c82c665b8ad748f3aca8677ab320c603cca37800093413b872d2648af10d74aff017e48e1382431873c6a50b0e00000001592c080000d020a403c0846862050324c800002fc53c2a9481a80d445f00000000bc482e0000000000000018c6a8c009248e80002c58ba6777800000029e2533800000023d8344062e162000065d975845005f48e589fa764876e5a9255a1090ec400017ba371800020288b2729a9ce09b8e2800002d25df23cca83271e93a
  | 45 => 0xb93e27a58e827df00005e2a4f822e258e94315f073f259cb60a94c9a3a4c204a218a90aa62a5c080ec8ad96f87a0a3507f52c822f99ce853782720000b76000268c35e93806688db02fa1a2642b08aa18aace4062a35864526c23e1111eb5484d873f8108b74ad7e5570b789628d360002c9430720b007780005ab9f28a0c8000000063e5351b1ca3f8f4ea3988be2cea5880001b40262081607d8bae52b24f2798890893c0db624117de8c98b7411d0fdc00013b21451d660002d4649a0c50628946e7d39b4280b9b04000158a1248cf4a7a00600002378af91b9017111b65711df883e82688c197a000000005a1000054c800011a8780805975a00014202408000000219e43b00009581f8e00015be000000081205960000000648988c839962a00024e02b597d8333092062992ce87e0a781c88b5441b86ea2c413289b18a021571ce01c0834ab5b050c000225e0910000a2c28b253980009951a124272a286fa000089500000001df425c057a4688a6c92f80007620000000000000027c20360000000000036600000000600000000000013ba0000d6600004985610000151acf62c811724040000aa0a2a07cd1c6011e8fda592800074fa3a03e02cc831a8000000053c95487f61c723e0a138c2a417add490f29026fd97aaa8cac3698d9d52ad41bd474d01b83eea39a4369a3a9dd88c46e71e467731e9e6ba80004cb0e2a59e0b308cb0bd44cd956c57299ce6f815a465a0000448183e7c2912a00000000000000a6100005511ae400027085af816a00022281cb0000add845270b80001b48da41758da07ac80003d512545d50a40a6f018c642278c302184c31f8000204ad1ea2e0d20a680be4000083c680986a000192694face0b568b446b58e463a30c3687fa9ba5a1a996000099c9d1ab36850877a145998ca0c24fa586891600004e272a800025f800078d89d8a9b80000000000724a13c00000004a480000002810000137e3058000000029e67195f46b484a60dc82248b823769a7a5ba00008988dc19f27e614fc32304a8000113c1d69c746c880006821d628b6a9700000ff600008040001fde5879e945ab2d3a000268a46e80006ae866a25080005021940a64a66030380004e78f3e0fca0f02f02c84b5c2b407780f9237087c20d09000448801c020a3caa3d2dde8032942b0513cc6fcaab66ba014e87b00c8ab5a3c89912266a5980000001a9c65580002d702e493920ae5cb0202338a0bc3ec858c41a96da05320660001ffc41119881d19104250000000018581f6847c00004cc00009265fe17a6a4e8b566331752176ab227aa813417e00000a2138a10000000002dd0000156a184902000023d6694800033611920e72a3e82e80001582d240001a8e9aa14c8532ab4c95713a422d9f5c2df95e44a3800077a8f2801b08ec717839
  | 46 => 0xd40000000000125c00011663642d00296000067ea0640002c4e413800000000005148000881ab5435613fa42a2ca27fb03d69872864ab8ad18a7d924c8c809180000982890800029682823e0aa7a68da8e46e3208696d000021280003db913a541255e710027e000182c0001b0e0000000000274437d2c6c90983f66e7815621811e422ba2748a3aa18000000000025163868d3c00000006c6a270303000065ba9443d113b48fa94fe8a0a9f29c32b943fe25707409bbe83317d49351d4a41b1b244b404e45388602463222ca1a9f101c126d0368a99c0908b581ca13d6abd1900ac6a80c34c0000807a4700002a2a00000000172dca0001ad400000003f30000716000000014d6572000040e0b5e6a6a21e857195865f282e1e600002db89343ad800085000008e483ca000059a4d0a29c0001f9e9b52bb000000003bd907865c2b0a71b9588000256800023683fa80000ec246e00005528a50000542ab005f28e0a5d22806300066e326278008b0f0024c14fa00019e400000007432c0e00025b626a9ca0000100cafe0dd0a4e0000008185ca42286e68d14c455b8000131156610280000000000b2610b4000000062213e60000000980800000000008eaad1a20d83ba00091b000000000002ac0485a49a35480005062cdc00026702418e302b2aa2e000111200016dc00000000002292000000056b8b140002c9e531a022a990000879a0263438f1e0001df65e50f2a7551a760002cb0000000000018ea00013701c48000555918e000000049281c29b3000063a0db444c2d0a0a82d920599c281c2022e05920a87fa935e52c9a1c6b191d2b028aa0600a0c097a2dd800184be03a110e3a400000e680000000000000169c92c2040a969ef621c0a9686f1ada7dd92648bf01901060000a318da62ed8000000147200017a4000103031805220002aee0000e647a70f62af580000000ee20000000149800026780004e328682be81a00001578a3c8eba9c380007a9195c4cc9c309761806a38901c233989426e2a6a87c2c22048a618a6f8000a1f80006e8a6780000000a36282c7fb85b4244951c1e31f5291a1b144840f160001d8c3bb0ae663b82b2000000000018e25c5a9240001d8a476170e52d1d769fc2508333abd40001cba3608000a9b29c809f193c749867070687d6ad1896eb2c952a4551f480fb15ea7502af63c998aa0000000a3083905b000000001610000000035b9d6c473923098c069a8a18000000065c32f07e600000000e49e42000000000000000000300000000000000000000000000000000000000000000723800000000002c79ab200000004f7a4da0000000ab32da821222fa68824de48a18fe33520e893f84660001de82530000a8995fa000278e74f073aa791f8c92ea53ab3500009ec11e8a69000028e27789b4a94098
  | 47 => 0x35992a981800000027bc7c4a590714a1ca490000052280005fc80000daacc452ea6960002cba29d000016895300cd0240488211ca638000105a33600000000002a4e00000004da8fc66a88c4400022329b000000698a5288b80000001e1a194a09a1f1800000029123d9800065200a28bb800021185046e0800065e80486c19998000256c3df00000002ce2000000000002d4b2d208c044172000025a63508e1048c8000000031e1eb050006381824db00002051d0600015b600000000000d24b1200007f618706918dea4dc889a8f727ba57f26166a48000862000000000001c98b6a63695e000018b800000003052898428000000000009c0000025980000002bee0001b4a81f85dc8711cc8ad0a6e867a042c57e175c37fa2908f40d725e41524883878e70a90646af05e24faa09023c0dac2d917889bc93a8501256687222b021a07b6ab8170812d2b1865c9bb6b0e1fbe56f1620ada82063f219ac9029af2547a2a89c6aa0e5a0a6920d01cea1c28bb095292aa1bb85ba2e2000068627f200022002ca980886e0000b188e4a00009e65a500008340570446202832a000000002cc2b4964423227a8848000075b98fc2240010b4c96001300d880001c767d0800048b2ad4000000019e9c481b0000061d0ac25bb2a2269b0000b35800059a82083f10004000014296615726ee00006a906766e6000000000000001fbc5ff92ee393800000000006a19a88a7104d02489050007800026a29fe58d80002721bea380006e000031441189acb6297ac2928b7c8861a7e1ac0ea650babda00028f61ae06ae5f19dae000276241a2366af028660cf80007ffa1c022f00009cf8c7a00000000001d1c0000d143a1078836f2bea23f277229180005a3840600029b69f7ac1cb6e9c7c000000000000006bb9decab18ad833da4a0000226e0db00004a6800035b27ae77f0854aa9853203380004d71d385e392e039a0e3c99f153e211057e58b17c00002d4eb41a2140000f025b0a87c7c792c238b819c0000fbe972992ea4124fc4021e3c3e18f4671c1a8400020466642b78181134a1a4acf80be07528b025de3501bf4475135627f808651a0fe464623f400016627fc000072a2c540000dd483b00000000bf0a3a06604f20000274a5000000a084c205ce7f3a38692d83e22ee8000000085c00000000000ffc000000017605ee0cca7906d48000b5280007cb8f32629000000c1c805ed0000865990a351803c0a880000ad119c79480003b613a600009441f2000000028460001a32a5780008140000b3e80008bb2d900001ec4049a3e60001bfc853a03800a008c69b871095880005d38000362a80244d06fc00028d035c23ac6f001c80002c909db20fe99d8ecc7a10ef80001f3a8460b0c18700007439c94000214843f068202b8000000000000000009eb25
  | 48 => 0x9dcb5500000000000aea18c00000f7e000000079380000001bbc9500000614220800000002359b105139c9a0738a92000279a07c8a0c693822a9082af842e85bc5fa05e42751c1e95f0cb64af80000000000a03a9fa740068e9d92c8e97e000069f00005b5000060ca3e80001fac000000060a8018000220c000000000003e44a9a1143da00000000000000000000000000000000311823c000000059b241a7ea0af48ae800000000000000000000174a0000d4a4ea8000000000000000000001278000000000000004bf0000000295c92702965ff08e800024465541b601278a54a669ffa969216a32c8344000000065900000002b8850f80000002cce696a19a7b3880c08022a200013ee41d80000129e2a00016b2000015a9ff943a3c506247ea8dcc1e981feb4e131287525f6a1e80b89001bdaa2f806811b9c8c2c2940ab732bfe48900008ed981e1179d103a000e24a2800000005fe01999ec8db23e20002ccc0000000447231e79680003ce2a0200001807678000000000000006e0000000000029ac000236076c02c6954082c4bc0b9200028603ec15981c6105241006cc000000091289b49b7190c7a197b003c06fa2e9223a43525761009c220000000b0a05742380f402f2aa447d6109e0000000af880004240488a868ec80000fdea10a4f426f8000ae38226234296c2e0800019180000000000000075e29090580b880008448000095000088480005a4a030895a5dc9898a4c59f055471f80009c700000000e882a383781b6922e3fb800098a12a8ad7abf40f79508ae108662ab96b4158ac9a18e8d9e11293f270d91beace01407fe130096005be06521a202696888b121b09ff0d5e7e4a04c9b2ac3caa402c20450d34324209e6538ec692610aa7650e50167800000001ae0bd807c3f5a00a593840478018d40cb2abc6f28c2899e8b500b586a28cb824e3068d0c02b14906ae00000c680000000000000000047b9eec00000005950566545908cb0f865a0002a3c4b30de80000000b24800099481882dca8b6000214a36700000000000624a4960000000b56000099aa2dc00020747712bb68e4074c63588844b60a3cb1f0dfa2852014ab29ac47841a4a3eb000051e25c4000000027b8c1076ea7b88a617b609e01f47728e0684200003e2ac6e3872cbea95000000008b00000c5a05ba8ce8a2000023c80f86c2a83e47c876c98d1b4c000000026692d20002564633993a0000000000244000000003e3a2f20001bac6f48594394a056b1ea9989d3000097426fc836000000022e8000133a2faa28caaa84120001a8a47e021a237a99000008e60000ca680d2b301070000b2b112c6980000000000099780001b5a43e0000000a881a66aef000013b00000000888a0280007f30a303ef000000017f600000008b180007bd11a63bf20a63
  | 49 => 0x160e00000002c700000d3800000028f882923d200018764c300006df0628449035402c80000002ab008e80000000000000000044e0000632820e74b92120001de206a000000d800000022f00000000000000008581faa6526de0002c4c00000005831ed20000ede25aa77400000004bf80000002dda6fba98c00000003dc00000f2182835f07a40001156000082e9241092000000043c80000000000b4700ea7e09f5a0000000000153a002841001d95126dd000000000000000000000000030d0000000000000018f27f2171800000006b80e58ae899f41bf84de7b409920001eda00006e45d085821a300006cf049a80d945c71400000000e3aadc0000000285e75a97100000000897000026f1e54aa581189c4927a5c884767f01730a3c24d2208800026c2bba952017211e0b940a928763049d986bf8bfa00522a491204fa28b104227a173e67711dc8c5a6d866c80000001c3267024ce8880e2000020583210beea0ea2d20178da820722fe000102c7319be473d1bb017a800067f24a266f879053b82282a0a51a4a08e480002b046bd00000001698320253c37d91c409900002279bfe0001bd05e0200e50d1e903510b043d41ed62a91dc867899542228cfe000000000010f40002d3650c0000000000000018d2b618c96a4f86362a600005bd292a96685a4697165e0001e889d9a65062f800000014068b2a3ec15595a0b5413e4387ad6817c81ac49d07d00002638487246000025b08fe9f861b1258ca6b8d789d3989e3851de47db000007b84720001ac2000240228d8a0496ba1ac000000088f0000220a7380000cf000000003c31dfa0002814ad4800034a877ca6e29a880ca3f200026206c088a800003f092a000016c18188f11386327800000000002bb0000000194a000216200000002f1a3f89610000914a79c59a000013d0462000000089a80000001aa61cc000095627ca00017987118f1242f80a89030e768cc1c7827e1c3812e1a9803282040c71fe20001b3873300005529756401000027c24a61bc1e4c14e142486084ce14d86a088a96ea00028ae0ea1fe8ae00d18a47000048d8fa254301366769e8e93da35a347051e0dd8100a0a1632930111a4a5ada489b20b60841e3a47ea8381b725860000000000133c6aa249e8e0a91e1931624b2e297a25e07846b3a76810c9c4e6ebaa4aa0d16280001b1e00008c629a0eb48479abe9511846aa711c800000000002b9e3900ef415b8e944da119e93185a804119c800000000000000000000078b2b5a0001afc99fa2ac93b8abe4e5832a31c9e140000fd8822900e000000039b00001030dde7ad206e9fd1cc40c315425ea1f700001ba81f32b3400002944d315a2840000000000000000b34233047e1e7833800011065ba06424ff8fae0001a309ab163c4e380000001f689afa
  | 50 => 0x2ab461ba988a5c9f3c289a782983ab740002642527297833ca1685cca15a6e20a4e33400009222528a59216caa3149220a9db2a588ff0af1ab9c000199a9332b2466c035000000007b325e07681aac8b429a25fc1b846a7a7363a383c600010fe0000bc25b5a79e1d20cf8951a244000183c51287385ae9cbe00000007c912b6b7898a03dc800000020dc33a203ea742ac2a2122d40001324000152c0ee0f2c1170b2c0000c54000052400000000002b441ffabf2a8917ccaed0000041800097380002f68000000000000008643d09fa667c2d48000000000028e0000000069890ea000277e0001c24000000098480000002c9c00000006b6024aa7e0000000000055d000000000006001b360000000000000000020d4000059c48783bc898083a146000095382ba000000078625244f1059800005580002574000000051c0000b3a86723e201e44769262000211037e12ae000000000000005e585d224398ec40682b89e88d1e0049744887170a0001280429873451b04b699600000000058000000050b0000695938407100006db000000000000001ec239b80009471af82fd000002f80006708ab60000bbc000273ab232126b04879259d8cc413194580001c1200017da7e2000060d1b580002c02000000000000002b687f04758f6c2980e9852a041a4fd0f201879c3490518400a12da0b2012b4998a8707260000526a07a7f82362ae5a556b14a9d826881a21348cb87cf8bfc0c803285db2506164800076a25a840a9c106930c880000a9a45122764d3800085e03ce8281f38a43800040980003fc87f4000058000000000001b763401f6e1112bcc08c9a4033b80000000e0470708e20002c402a0000000028ac9f200009b80388096a0047c21eb0504a31c31ba240ac0a33c8bd13d21b9941c41c2d20a3484aa01d225a00012ba7f1a4560c082f4766800068f0efa3982a50000021e46e230400023147fc80003e905a00d693b001c9fdc5b40ee40000cb400000a4773a1528919cbc000000000000004ef9a5e18e000000000001eaa3386b421647cb00002f8843c87792b0932a2961501f02a4c2c1e19511e2546a6a0a9d93f86c80ca48768d8e0459a2a2e0205400023b4000000007e0000116891c4de877e72880000001c90746800067a80000ff99c4000013c8d280000001e384a118c40000dfc5230ea40000a2e2611f60000178c43417ce7848f4800023480cd884c7ab07e04238f989929d600000000a6a80ee0002c50110890a237000000000001b1a0027038000000083e1ae80004bb000086a800000000c600005026b9800079580000000b860002c68a46000012b283c68b000000019d841d1e6a00000000001b5049daaf04729fc20002cd88cd00e6000000015c81324bd038e0001c3c60c028c00027dc0001bc88cf97e00001da6
  | 51 => 0xa0606bcb57abac581139a89a16a03dd1a28768a13460ea08800302ee6921bc66d68508449aace779aa5c00000004f5019e40e84385392caeb1a856c77181aa9e196fe4de01b69480f1a2c8a16e30117e21e595ee94e0096a469456245276ab3010e45f09edc5238b4200016e05a68a560700000b34000000026ce2f7000033211a469523de0000000511800000004287572b4a0000420a6c1e204a300007d795e80000000000124417180001520d56a778000510860c0001c6251fab649a01bfa0000000868000067480000001e9800017045678aac000013800000000c4137400024581ff161c0002d443f280005adab1c39722b2000240667d8d688670d2e3e3002a4400d483488000415a6ae8738eee3710c680238c305eca08ea371f5099680000000000000000000000009bfa388b65ac06000000036108d80c1000031700008cc9b6e0002de49ac00000000c3e73e9a105d894b600018f000014964f39cae0000b085499f6a83c80000001e780000680301acde7c01f4a31903b40be941089e8550188abd2003ad6453615366042cf0000000067f80006a09bc400000006f78000172a640000256a3d3165269414b839ea816582800093b1a0a56b242e9f9a51285c000003100004d5030e2a11ab4acea210886a0203a81c1433190d629201589fe98123bc0ba0287000022496bc6578aea0002dd67fd8baab581a68000096090d1ade9bc00de04c
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x6215130c25725846115130c31615c06115130c0c545c86050d30c14545c46050d30a1a85d906050d30a15819d854cc93081d87150604c930c14545c4604c930a0d829d854cc53081d87150604c530c0c545c8604c53081d871526348530a25861512108530a61811496008530a61821456008530a62854856008530e23544856008530e20544856008530989821c14350130991811c14350130a0e8590d6210130a168590d6110130c0c635c86055030c14635c46055030a19859916010c30d0a745c04354830d12745c0435443081f875536348430a0e84d8d5248430a1684d8d5148430a61819496008430a61829456008430a63854856008430a61854856008430e22544856008430e2154485600843081f87d974350030a0e86d0d5250030a1686d0d5150030c19655c04310030a898010d6210030b098010d5210030a918010d6110030e04435496110030b118010d5110030e04435895110030c0c645cb544c030c14645c7544c03081e869d9544c030a0c86552524c030a0c86951524c030a0c86551524c030a1486552514c030e046454a514c030a1486951514c030a1486551514c030e0464949514c030e0464549514c030a14835516115220a148454d6114e20915811d54310e2081c875954310e20a188550d6010e20a15811506350220a0c835516210220a1483551611022081d87190534c220c14645c4534c22081c87591530c220a0c8454d620c220a148454d610c220a188550d6010d208e1811c1644c920a0c85590434c920a8880590434c920c89645c0434c920d05745cc5148520d22745c05148520d21745c05148520d42735c05148520d41735c05148520c0c7518d4250120989831c14250120c88631c142501209a1811c14250120c0c75191324c120989841c1324c120c88641c1324c1209c1811c1324c120e22544856008420e21544856008420e42534856008420e41534856008420d05745cc5248710d22745c05248710d21745c05248710d42735c05248710d41735c05248710a0c835516215210a0c8454d6214e1090d821d54310e1081c875954310e10a188550d6010e10a0d821506350210a0c835516210210a1483551611021081d87190534c210c0c645c8534c21081c87591530c210a0c8454d620c210a148454d610c210a188550d6010d108e1821c1644c510a1485590434c510a9080590434c510c91645c0434c510d05745cc5248510d22745c05248510d21745c05248510d42735c05248510d41735c05248510c147518d4150110991831c14150110c90631c141501109a1821c14150110c1475191314c110991841c1314c110c90641c1314c1109c1821c1314c1109c183dd121481109a184dcd2148110a61815496008410e22544856008410e21544856008410e42534856008410e41534856008410
  | 1 => 0x18e1801c96110d21e05535096110821e05544c9610c821e05535894110421e0554589310c421945859cf6448421925859d36348421d21545c35348421b4180d515348421b05859515348421961809d44348421d057550c4348421e055458d21d4021e056454d21d4021f015454d2194021b22841c12154021b21841c12154021b42831c12154021b41831c12154021b4283d512154021b4183d512154021d23755512154021962871512154021b42831512154021b41831512154021b2284d4d2154021b2184d4d2154021f025494d2154021f015494d2154021d437554d2154021f025454d2154021f015454d21540219628714d2154021b228414d2154021b218414d2154021961819cb4354021961829c74354021961819ca4354021961829c64354021d21425c44254021d41325c43254021d21725044154021d41724c43154021b42839052154021b41839052154021b22848c52154021b21848c52154021b42839092154021b41839092154021b22848c92154021b21848c92154021b23845d92154021b20845d92154021b43835d92154021b40835d92154021b22841d92154021b21841d92154021b42831d92154021b41831d92154021b4283dd12154021b4183dd12154021b42839d12154021b41839d12154021d21741d12154021960875912154021b43835912154021b40835912154021962871912154021b42831912154021b41831912154021b2284dcd2154021b2184dcd2154021b22849cd2154021b21849cd2154021d41731cd21540219608758d2154021b238458d2154021b208458d21540219628718d2154021b228418d2154021b218418d215402196287d0d215402196187d0d21540219628790d21540219618790d2154021f014310d2154021d22744842154021d21744842154021d42734842154021d41734842154021e22644855014021e21644855014021e42634855014021e41634855014021c45625c46214d40c49625c06214d40c45725846114d40c51615c06114d40a1a85d8c6050d40c14535c46050940a1581990534c940c0c535c86050540a0d82990534c540a458614d2108540a61811496008540a61821456008540a62854856008540e43534856008540e40534856008540a198598d6010c40d0a735c04354840d12735c04354440a0e83d915248440a1683d915148440a61819496008440a61829456008440a63854856008440a61854856008440e42534856008440e41534856008440a0c8654e5250040a0c8694d5250040a0c8654d5250040a148654e5150040e046354a5150040a148694d5150040a148654d5150040e04639495150040e04635495150040c1a765c05450f30c0c545c86050f30c14545c46050f30c19769c35410e30a0d821506350230a15811506350230c25625c46215130c29625c
  | 2 => 0xe8f950cca505043684617d1e2753732cd033d0d0000030400168004d8b626c001d0fb0bc00000763f47f25000020a7398022ac0000000294db4a0d23b4b94e89f3708718c060011f2600000072000652384d3180b33816270f30601a124b73b0572885d228bf1e8101cd3812083364002145443c64388ea31000000d6001474fd4d000d3178001854a001135100000114000c5045000ec310a8f10012314800525214306d23ccc198bd07d4019c6a2c0694ecb4425261807c0947d1d43f2e8131ed4e2f09025cf00f844350e4454c2048b847051050fe1280a4ace33d82812d39004a6108fc2bd070144e024004a47025400418ff4c8d10b0be4cca1268b146415460390000d0308600000001450ac003b94800000490c7374002a5311bd011601e10ce02581b0009e000003e11214c1742ca30009330c00000004f0c0100372912a480453d0004b0003c881000aa000190c1424c0e54752f51882468e72b0b23a0713bc5b08834444c84d0503854c1a06c2245c0d8d537c3d48916158260741c379250011b428d840c7e248470d423084623dc001e4000f0291e108000c93e82d1b86b220000002001c032d48c00080280b300c200b00808140000848000a028440e000383c0403000200a02008140c290c0285c0d0000000020000ce602050004a1100044006e01050000000800060c000484c02038202a01008000e1f020000401038402003080700e00018a00006010000200010043c39058140004000182e010106c680109008321d0c0080822c0d759c86050c43c0d755c86050c43c15759c46050c43c85729c46050c43c15755c46050c43c86725c46050c43c85725c46050c4389581dd94354843e05435496114843e0943549601484388d82dd94354443e05435895114443e1143545601444388d821d94394043895811d94394043989821c14394043991811c14394043989821c14354043991811c14354043929821c14354043931811c14354043949821c14354043951811c1435404390d821c14354043915811c14354043b09821c14354043b11811c1435404391a861c14354043c1a861c14354043d0a821c14354043919821c14354043d09821c14354043909821c14354043d12811c14354043919811c14354043d11811c14354043911811c14354043915811c15310f42a188054d6010f428a9801c96110d42915811c15410f32a18805516010f32c0f76dc95410d32915811c15410d328c9801c96110d32a18805516010d32b0581151424c832b0980151424c83290d821c15310f41a188054d6010f418b1801c56210d4190d821c15410f31a18805516010f3190d821c15410d318d1801c56210d31a18805516010d31b0582151414c431b1180151414c431918805d54310d2181e879954310d21a19801954310d218e1801c56210d2
  | 3 => 0xae0013d0000045ccd000e9234000112d4b90200033000d7000002a0ad130bb0b8993d4380c8911540003c413ad0509c844410e1647722c004d40000000039274f84f52c240
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x804f00000e54b4401120000061541d030029324d0005830800008418068190182a047050d5010f20504c08e0a1aa021e40609811c14354043908c8900a9ac021e85211912015458043cca42322402a8b0086994826488054d6010f41904c9100aa2c021e632099220154580434c6c032021aa4b088018580640435895110030908c890aa1ac021c41281912016410d324828112ab22e021a649062018d811c14250120844cc0c8382649824188064604704c9304824132442a86b0087084a064880590434c510a084aac8b808698a2188063608705054044212330320e098a6088620191821c1314c110
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 40
  | 6 => 1870
  | 5 => 10236
  | 4 => 5876
  | 3 => 335
  | 2 => 23
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
  | 6 => packedAt gbK6 (57966+((h/623+packedAt gbK6 (50490+(h % 623)*12) 12) % 2469)*12) 12
  | 5 => packedAt gbK5 (436736+((h/3412+packedAt gbK5 (388968+(h % 3412)*14) 14) % 14863)*15) 15
  | 4 => packedAt gbK4 (313378+((h/1958+packedAt gbK4 (287924+(h % 1958)*13) 13) % 7757)*14) 14
  | 3 => packedAt gbK3 (21099+((h/111+packedAt gbK3 (20100+(h % 111)*9) 9) % 403)*10) 10
  | 2 => packedAt gbK2 (1675+((h/7+packedAt gbK2 (1633+(h % 7)*6) 6) % 33)*6) 6
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xe3fe1fffc3fffc7e0e38f8fff1fff07e04f3cf
  | 1 => 0xfc1fe1e3fc3c7f8ff03f1f1c3e387f8e3b4d33
  | 2 => 0x1ffe03ffc07ff1ffc01fe03fc07ff1c38e3c
  | 3 => 0xffe00003ffff8001ffffe0003fff8001fc0fc0
  | 4 => 0xfffffffc00000001ffffffffc0000001fff000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x20020000400000800000202400481000001045
  | 1 => 0x414448448890a810501909089211250c194512
  | 2 => 0x1a88848911095002a640124124824a60c28a28
  | 3 => 0x88c1d55222a819253aaa4002392703256c0f80
  | 4 => 0x131119803b326249cd349c9380040c49b7e000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xfeeaeae8feeaeae8feeaeae8feeaeae8feeaeae8feeaeae8feeaeae8feeaeae8feeaeae8feeaeae8feeaeae8feeaeae8feeaeae8feeaeae8feeaeae8feeaeae8, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_12937
namespace PEqualNP.Outside.L_meta_12937
open PEqualNP.Outside.L_meta_12937.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 23 := block_range (n:=23) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 23 := bgb_2_0
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
theorem bgb_3_288 : Interval gbAtlas 3 288 47 := block_range (n:=47) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 335 := (concat (concat bgb_3_0 bgb_3_96) (concat bgb_3_192 bgb_3_288))
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
theorem bgb_4_5856 : Interval gbAtlas 4 5856 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 5876 := (concat (concat (concat (concat (concat bgb_4_0 (concat bgb_4_96 bgb_4_192)) (concat (concat bgb_4_288 bgb_4_384) (concat bgb_4_480 bgb_4_576))) (concat (concat (concat bgb_4_672 bgb_4_768) (concat bgb_4_864 bgb_4_960)) (concat (concat bgb_4_1056 bgb_4_1152) (concat bgb_4_1248 bgb_4_1344)))) (concat (concat (concat (concat bgb_4_1440 bgb_4_1536) (concat bgb_4_1632 bgb_4_1728)) (concat (concat bgb_4_1824 bgb_4_1920) (concat bgb_4_2016 bgb_4_2112))) (concat (concat (concat bgb_4_2208 bgb_4_2304) (concat bgb_4_2400 bgb_4_2496)) (concat (concat bgb_4_2592 bgb_4_2688) (concat bgb_4_2784 bgb_4_2880))))) (concat (concat (concat (concat bgb_4_2976 (concat bgb_4_3072 bgb_4_3168)) (concat (concat bgb_4_3264 bgb_4_3360) (concat bgb_4_3456 bgb_4_3552))) (concat (concat (concat bgb_4_3648 bgb_4_3744) (concat bgb_4_3840 bgb_4_3936)) (concat (concat bgb_4_4032 bgb_4_4128) (concat bgb_4_4224 bgb_4_4320)))) (concat (concat (concat (concat bgb_4_4416 bgb_4_4512) (concat bgb_4_4608 bgb_4_4704)) (concat (concat bgb_4_4800 bgb_4_4896) (concat bgb_4_4992 bgb_4_5088))) (concat (concat (concat bgb_4_5184 bgb_4_5280) (concat bgb_4_5376 bgb_4_5472)) (concat (concat bgb_4_5568 bgb_4_5664) (concat bgb_4_5760 bgb_4_5856))))))
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
theorem bgb_5_10176 : Interval gbAtlas 5 10176 60 := block_range (n:=60) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 10236 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_96 bgb_5_192)) (concat bgb_5_288 (concat bgb_5_384 bgb_5_480))) (concat (concat bgb_5_576 (concat bgb_5_672 bgb_5_768)) (concat (concat bgb_5_864 bgb_5_960) (concat bgb_5_1056 bgb_5_1152)))) (concat (concat (concat bgb_5_1248 (concat bgb_5_1344 bgb_5_1440)) (concat bgb_5_1536 (concat bgb_5_1632 bgb_5_1728))) (concat (concat bgb_5_1824 (concat bgb_5_1920 bgb_5_2016)) (concat (concat bgb_5_2112 bgb_5_2208) (concat bgb_5_2304 bgb_5_2400))))) (concat (concat (concat (concat bgb_5_2496 (concat bgb_5_2592 bgb_5_2688)) (concat bgb_5_2784 (concat bgb_5_2880 bgb_5_2976))) (concat (concat bgb_5_3072 (concat bgb_5_3168 bgb_5_3264)) (concat (concat bgb_5_3360 bgb_5_3456) (concat bgb_5_3552 bgb_5_3648)))) (concat (concat (concat bgb_5_3744 (concat bgb_5_3840 bgb_5_3936)) (concat (concat bgb_5_4032 bgb_5_4128) (concat bgb_5_4224 bgb_5_4320))) (concat (concat bgb_5_4416 (concat bgb_5_4512 bgb_5_4608)) (concat (concat bgb_5_4704 bgb_5_4800) (concat bgb_5_4896 bgb_5_4992)))))) (concat (concat (concat (concat (concat bgb_5_5088 (concat bgb_5_5184 bgb_5_5280)) (concat bgb_5_5376 (concat bgb_5_5472 bgb_5_5568))) (concat (concat bgb_5_5664 (concat bgb_5_5760 bgb_5_5856)) (concat (concat bgb_5_5952 bgb_5_6048) (concat bgb_5_6144 bgb_5_6240)))) (concat (concat (concat bgb_5_6336 (concat bgb_5_6432 bgb_5_6528)) (concat (concat bgb_5_6624 bgb_5_6720) (concat bgb_5_6816 bgb_5_6912))) (concat (concat bgb_5_7008 (concat bgb_5_7104 bgb_5_7200)) (concat (concat bgb_5_7296 bgb_5_7392) (concat bgb_5_7488 bgb_5_7584))))) (concat (concat (concat (concat bgb_5_7680 (concat bgb_5_7776 bgb_5_7872)) (concat bgb_5_7968 (concat bgb_5_8064 bgb_5_8160))) (concat (concat bgb_5_8256 (concat bgb_5_8352 bgb_5_8448)) (concat (concat bgb_5_8544 bgb_5_8640) (concat bgb_5_8736 bgb_5_8832)))) (concat (concat (concat bgb_5_8928 (concat bgb_5_9024 bgb_5_9120)) (concat (concat bgb_5_9216 bgb_5_9312) (concat bgb_5_9408 bgb_5_9504))) (concat (concat bgb_5_9600 (concat bgb_5_9696 bgb_5_9792)) (concat (concat bgb_5_9888 bgb_5_9984) (concat bgb_5_10080 bgb_5_10176)))))))
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
theorem bgb_6_1824 : Interval gbAtlas 6 1824 46 := block_range (n:=46) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1870 := (concat (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 (concat bgb_6_288 bgb_6_384))) (concat (concat bgb_6_480 bgb_6_576) (concat bgb_6_672 (concat bgb_6_768 bgb_6_864)))) (concat (concat (concat bgb_6_960 bgb_6_1056) (concat bgb_6_1152 (concat bgb_6_1248 bgb_6_1344))) (concat (concat bgb_6_1440 bgb_6_1536) (concat bgb_6_1632 (concat bgb_6_1728 bgb_6_1824)))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 5 zero,inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero]
def fullWord : Sig := 0xfffffffcfeeaeae8fffffffcfeeaeae8fffffffcfeeaeae8fffffffcfeeaeae8fffffffcfeeaeae8fffffffcfeeaeae8fffffffcfeeaeae8fffffffcfeeaeae8
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 32 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,2,34)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,2,34)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4294901486 * 2 ^ 32 + 4277075680) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_12937.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,1]⟩,⟨.and,[4,5]⟩,⟨.or,[2,3]⟩,⟨.or,[4,8]⟩,⟨.and,[6,9]⟩,⟨.and,[2,3]⟩,⟨.and,[7,8]⟩,⟨.and,[5,6]⟩,⟨.or,[11,12]⟩,⟨.or,[13,14]⟩,⟨.or,[10,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4294901486 * 2 ^ 32 + 4277075680) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4294901486 * 2 ^ 32 + 4277075680) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_12937

open PEqualNP.Outside.L_meta_12937 in
theorem PEqualNP.Outside.L_meta_12937 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4294901486 * 2 ^ 32 + 4277075680) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4294901486 * 2 ^ 32 + 4277075680) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
