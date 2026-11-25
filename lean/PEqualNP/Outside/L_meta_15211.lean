import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_15211.Model
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


end PEqualNP.Outside.L_meta_15211.Model

namespace PEqualNP.Outside.L_meta_15211
open PEqualNP.Outside.L_meta_15211.Model
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

def SBf (j : Nat) : Nat := [4, 4, 3, 5, 6, 6].getD j 0

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

end PEqualNP.Outside.L_meta_15211

namespace PEqualNP.Outside.L_meta_15211
open PEqualNP.Outside.L_meta_15211.Model
def s0K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (i*5) 5
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (6+((h/1+packedAt s0K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffffffffffffff
  | 3 => 0xffffffffffffffffffffffffffffffffffffff
  | 4 => 0xffffffffffffffffdf83fff801ffffe00fff0f
  | 5 => 0x6ffc1ffffe007ffff007f0
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xffffffffffffffff80884259325896ecb65b77
  | 2 => 0xffffffffffffffff811084aa54a92b755aadbb
  | 3 => 0xffffffffffffffff8221093469324dba6d36dd
  | 4 => 0x247a11c771c471dc0fc70e
  | 5 => 0x1843de0781f87e1f8e07e0
  | _ => 0
def s0Atlas : Atlas := ⟨3,rawDecor 62 s0Pos s0Neg, 0xc000c000c0000000c000c000c0000000c000c000c0000000c000c000c0000000c000c000c0000000c000c000c0000000c000c000c0000000c000c000c0000000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_15211
namespace PEqualNP.Outside.L_meta_15211
open PEqualNP.Outside.L_meta_15211.Model
def s1K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s1K3 (i*5) 5
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s1K3 (6+((h/1+packedAt s1K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffffffffffffff
  | 3 => 0x5be0ffc1ff801ffffc01ff00ffff0063f8
  | 4 => 0xffffefff07ffffffe00fffffffff00fffffc3f
  | 5 => 0x73fff801fffffff00001ffffff00007fc0
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xffff802210882592a492c5245b4b4b4b6aaddb
  | 2 => 0xffff804421104aa4c9254a48ad959595b356ed
  | 3 => 0x249e423a937691c9931d37c0e6e61a6378
  | 4 => 0x1108f4211c471d8e2391c6e6c0f8dc7836
  | 5 => 0xe1087bde0781e0fc3e1f8f8f8c0e07f80
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xa0a0a000a0a00000a0a0a000a0a00000a0a0a000a0a00000a0a0a000a0a00000a0a0a000a0a00000a0a0a000a0a00000a0a0a000a0a00000a0a0a000a0a00000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_15211
namespace PEqualNP.Outside.L_meta_15211
open PEqualNP.Outside.L_meta_15211.Model
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
  | 4 => 0xffffffffffffffffffffffffffffdf0ffc1fc7
  | 5 => 0x6ff0ffe0f8
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffff81222d295b
  | 1 => 0xffffffffffffffffffffffffffff82445652ad
  | 4 => 0x24e89b1cc6
  | 5 => 0x188ee398f0
  | _ => 0
def s2Atlas : Atlas := ⟨2,rawDecor 51 s2Pos s2Neg, 0x88888888888800008888888888880000888888888888000088888888888800008888888888880000888888888888000088888888888800008888888888880000, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_15211
namespace PEqualNP.Outside.L_meta_15211
open PEqualNP.Outside.L_meta_15211.Model
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
  | 2 => 0x83ffff007f807fffc03fff01fc03fff80f38f8
  | 4 => 0xffffffff80007ffffffffffe0003ffffffc0ff
  | 5 => 0x3ffffffffff8000003ffffffffc00000fff00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x104b052290851444848a8b162d545b2a535b5b
  | 1 => 0xa095d44b254a28a3a915c0ab569aa8a568adc5
  | 2 => 0x752656ea46534d2923a7d58198d335b14d38e8
  | 4 => 0x4238988c746c7232323966cd0303c6c78ec0b6
  | 5 => 0x7bc0e0f078707c3c3c3e78f1e3e207060ff600
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xa8a88888a8a80000a8a88888a8a80000a8a88888a8a80000a8a88888a8a80000a8a88888a8a80000a8a88888a8a80000a8a88888a8a80000a8a88888a8a80000, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_15211
namespace PEqualNP.Outside.L_meta_15211
open PEqualNP.Outside.L_meta_15211.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x602d09128e100d850008000e1df43dc43ef42ec42ef32de32dc32ec32cc32f741f441fb40f840
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0xa9000860280c02d0168c0711201869ca5a1d394f42a7294654e540ca98a819710cb41ca21883a442107886420f20cb40cc21881a8421039064206c10440
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x8100284640c841a219032103803210440
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 13
  | 3 => 14
  | 2 => 3
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (i*5) 5
  | 4 => packedAt s4K4 (i*16) 16
  | 3 => packedAt s4K3 (i*27) 27
  | 2 => packedAt s4K2 (i*38) 38
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (6+((h/1+packedAt s4K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s4K4 (228+((h/4+packedAt s4K4 (208+(h % 4)*5) 5) % 17)*5) 5
  | 3 => packedAt s4K3 (398+((h/4+packedAt s4K3 (378+(h % 4)*5) 5) % 19)*5) 5
  | 2 => packedAt s4K2 (117+((h/1+packedAt s4K2 (114+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfe0fffffffc01fffffffffff80fffffffe1fff
  | 1 => 0xfff07fffffffe00fffffffffff01ffffffe1ff
  | 2 => 0xbfff83e0fffffff003ff00fffffe03f803fe38
  | 3 => 0x3ffffc00fffffffffc0000fffffffc0003ffc0
  | 5 => 0xffffffffffffffffffffffffffffffffffffff
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x3e1084412f6815254992a2b88366cdab60edb
  | 1 => 0x42f10882542bb44992a34559b10b56d3ae16d
  | 2 => 0x4842791d4994ca6ed234669ead5a2271937638
  | 3 => 0xd08423de8e271388e3b8b8e74e9d384623bbc0
  | 5 => 0x21084210f0381c0f03c0c0f870e1c387c1ddb6
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xe888e88800000000e888e88800000000e888e88800000000e888e88800000000e888e88800000000e888e88800000000e888e88800000000e888e88800000000, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_15211
namespace PEqualNP.Outside.L_meta_15211
open PEqualNP.Outside.L_meta_15211.Model
def s5K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x1c0000c485142933004035600001df43dc43ef42ec42de32dc32f741f441de31dc31fb40f840df30dd30
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x2001c00100c0010001800540020d594632d2210834e528c73086206a10840d8208811c544c298a4985514530
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 9
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
  | 3 => packedAt s5K3 (258+((h/3+packedAt s5K3 (243+(h % 3)*5) 5) % 19)*5) 5
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfffffff807ffffffffffff80fffffffffc3fff
  | 1 => 0xff83fffff803ffff807fffff01fff807ffc7c7
  | 2 => 0xffc1ffffffc01ffff807ffffe03fff807f8f8
  | 3 => 0xf0001ffffffffe0000007ffffffc000007ff00
  | 4 => 0xffffffffffffffffffffffffffffffffffffff
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x2110825da0542a4c95151388366cda6a6c1b5b
  | 1 => 0x427504a8aed14c95331a2d9b10b5692575c5c5
  | 2 => 0xe423a931329b691a1a334ead5a22757126e8e8
  | 3 => 0x8f7bd1c5c4e271dc5c5c774e9d384646477f00
  | 4 => 0x8421e06070381e060607870e1c3878783b6b6
  | _ => 0
def s5Atlas : Atlas := ⟨5,rawDecor 31 s5Pos s5Neg, 0xe8a80000e8a80000e8a80000e8a80000e8a80000e8a80000e8a80000e8a80000e8a80000e8a80000e8a80000e8a80000e8a80000e8a80000e8a80000e8a80000, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_15211
namespace PEqualNP.Outside.L_meta_15211
open PEqualNP.Outside.L_meta_15211.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x323970018941bb00814805a78a000c9cb0000b0daa34140220441eb52474508003dd173e11bbf700190700354312a8531102f120068ad1b30071c8000018006c0178b002403e004cc0002001000100781012800b83040c1032200a82017fd50017f5400ff95001fd54005f55003fc54017fd4c01fe53007f54c05fc5300ffd0c01fe43007f50c03fc43017fd4801fe52007f54805fc5200ffd0801fe42007f50803fc42007fcc801fe3200778c801fd32007f0c801dc32017fd4401fe51007f54405fc5100ffd0401fe41007f50403fc41007fcc401fe31007f4c401fc31007fc8401fe21007f48401fc21017fd4001fe50007f54005fc5000ffd0001fe40007f50003fc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x244001bf99220005fac910006fc6488001bfaa44000df55220005fec71000efe6388001ef31c4000b798e20005fac710003dd63880016eb1c4003bf18e20005fac510003ef3288001ef1944000f70ca20007d86510003cc32880017f30c4000bf58620007dc4310003ec21880017f3044000fbc8220007f64110002ff6548001bfb2a40009fd9520015fcca90002fd65480057e32a4000df19520014f8ca90002ff6448001dfb224000afd912000dfcc890002fd64480037e3224000ef1912000d78c8900037f5448001beaa24000bfd8d20007bec690002df63480077f31a4000bf58d2001df8c690003dc63480016e31a4000f78c920007b86490002ff6148001fbb0a4000bdd8520005f8c290003f461480017a30a4000fbc8520007da4290003fb2048001f71024000bfd9420015fcca10002fd65080057e3284000bfd902000dfcc810002fd64080037e3204000dfd5020006faa810002ff63080077f3184000bf58c2001df8c610002fe6208001f79904000f78c820007b86410003ec3208001e61904000bf98420005fac210003ee2108001f61084000bf98020007de4010003fa2008001f69004000fe48020005fecb8800afe65c40017eb2e2002bf19710005fec988006fe64c40017eb262001bf19310006fea9880037d54c40017fb1e2003bf98f10005fac78800efc63c40017fb162000bf98b10005fac588002fc62c4001ef1962000f70cb10007f64188003f820c40017fb2c2002bf99610005facb0800afc65840017fb242001bf99210005fac908006fc6484001bfaa42000df55210005fec70800efe63840017eb1c2003bf18e10005fec508002fe62840017eb142000bf18a10007bc6508003dc32840017eb0c2000fdcc610007e86308003f72184001fa10c2000bf98210007ee2108003fb10840017fb2a2000dfd9510004feca8800afe65440017eb2a2002bf19510006f8ca8800a7c65440017fb222000efd91100057ec888006fe64440017eb222001bf1911000778c888006bc6444001bfaa22000df55110005fec688003df63440016fb1a2003bf98d10005fac68800efc6344001ee31a2000b718d10005fec488003ef624400177b122000bf98910005fac488002fc6244001f63122000bb18910007bc6488003dc3244001fd8822000fd84110005feca0800afe65040017eb282002bf19410005fec808006fe64040017eb202001bf19010006fea8080037d54040017fb182003bf98c10007bcc608002de63040017eb182000f758c10005bac60800efc63040017fb102000bf98810007dcc408002ee62040017eb102000fb58810005dac408002fc6204001ef1902000f70c810005fcc208003f73104001fa1882000fdc8410007e84208002fe6004001fd9002000fe08010007ee2008003fa1004001fa8802000fe44010
  | 1 => 0xefe6394001ef31ca000b798e50005fac728003dd63940016eb1ca000df94e50016f8a728002fe62940017eb14a000df94a50016f8a528003de3294001ee194a000bf98650005fac3280037e5194005be28ca002bf98250016fea12800bfb5094005fc284a002bfd9550005fec8a8006fe64540037e322a002dfd5150006faa8a8002ff63540077e31aa000bfd8950005f8c4a8003de3254001ee192a000bfd8550005f8c2a800aff6054005fda82a000df94150016f8a0a800bf850540017fb2c8002bf99640005facb2000afc65900037eb248001dfd524000f7ca9200077d5490001deaa48000cf5524001dfcc720002fd6390001df21c8001ef10e40005fcc520002fd6290001df2148001ef10a40007bc6520003dc32900017f30c8000bf586400077c8320007bc41900037f3048001efd024000ff68120007f840900017fb2a8002bf99540005facaa000afc65500037fb228001dfd514000efaa8a0002ff63500077e31a8000bfd8940005f8c4a0003de3250001ee1928000bfd8540005f8c2a0006ff6050003fda028000ef9014000f7880a0007f840500077fb2e6002bf99730005facb9800efc65cc0077fb266001bf99330005fac99800efc64cc001bfaa66000df5533002fbea79800fdc53cc007ef21e6000f750f30005fcc598002fd62cc001ef1966003f70cb30005fcc398002fd61cc007ef98e6000f74c730005fecb1800afe658c0017eb2c6002bf19630005fec918006fe648c0017eb246001bf19230006fea9180037d548c0017eb1c6000bf98a30005fac518003de328c001ee1946000bf98630005fac318003de318c001ee18c6003bf98230007be611800ffb308c0017fb2a6000dfd9530004feca9800afe654c0017eb2a6002bf19530006f8ca9800a7c654c0017fb226000efd91300057ec898006fe644c0017eb226001bf1913000778c898006bc644c001bfaa26000df55130027bea698013dc534c001ef21a6000f750d30005fec498003ef624c00177b126000bf18930007d8c498002ec624c001ef1926000f70c930005fec298003f7614c0017bb0a6000bf18530007e8c298002f4614c001ef98a6000f74c53001ff66098003de304c0077fb286002bf99430005faca1800efc650c0077fb206001bf99030005fac81800efc640c001bfaa06000df5503001dfcc618002fe620c0017eb106000f78c83001fb86418002fe610c0017eb086000f78c43001fb86218002fe600c007ef9806003fe8c030007ba601800ff9300c0017fb2e4002bf99720005facb9000afc65c80017fb264001bf99320005fac990006fc64c8001bfaa64000df55320005fec79000efe63c80017eb1e4003bf18f20007bc6590003dc32c80017f30e4000bf58720007de4390003ed21c80017fb2c4002bf99620005facb1000afc65880017fb
  | 2 => 0x41005fec6a080efc63504017fb128200bf18941007bc64a0803dc32504037fb0a8201fdd05410077c82a0807bc4150403fa20a8200bfd8141005f8c0a080eff65cc4057f32e6200bf5973101df8cb9880eff64cc4037f3266200bf5933101df8c9988037f54cc401beaa66200bf98b31005fac598803de32cc407ee1966200bf98331005fac198802ff658c4057f32c6200bf59631015f8cb18802ff648c4037f3246200bf5923100df8c9188037f548c401beaa46200bf58e3103fbea71881fdc538c401ef21c6200f750e31005fcc518803ee628c401773146200bf58a31007dac518802ed628c401ef1946200f70ca3101dfcc318803df318c407fb98c6200bf98231005fac118802ff654c401bfb2a62009fd9531015fcca98802fd654c4057e32a6200df19531014f8ca98802ff644c4037f3226200bf5913100df8c8988037f544c401beaa26200bfd8931005f8c498803de324c401ee1926203fdcc531007bc6298802ff604c4017e3026203bfd9431015fcca18802fd650c4077e3286203bfd903100dfcc818802fd640c4077e3206200dfd5031006faa81880efe630c40defa986203f714c3101fbc8618803dd430c4017f3106200bf58831007bc641880fdc320c4017f3086203f7cc43101fec6218803dd310c407fa9886200bf98031005fac018802ff65c84057f32e4200bf59721015f8cb90802ff64c84037f3264200bf5932100df8c9908037f54c8401beaa64200bfd8f2101dfcc790802fd63c84077e31e4200fbccb21007bc6590803dc32c8401f61964200f30cb21005fcc190802fd60c84017fb2c4202bf99621005facb1080afc65884017fb244201bf99221005fac910806fc6488401bfaa44200df55221005fec71080efe6388401ef31c4200b798e21005fac710803dd63884016eb1c4203bf18e21005fac510803de3288401ee1944200bf98621007de4310803f721884017f3044200bf58221005feca908037f65484013fb2a4202bf99521005faca9080afc6548401be32a42029f19521005fec890803bf64484015fb224201bf99121005fac890806fc6448401de3224201af19121006fea8908037d54484017fb1a4200f7d8d21005bec69080efe63484017eb1a4203bf18d21007b8c690802dc6348401f79924200f78c921007b86490803ec3248401e61924200fdc8521007dc4290802ff6048401fdb024200bed8121005f8c090803f860484017c3024200bfd9421015fcca10802fd65084057e3284200bfd902100dfcc810802fd64084037e3204200dfd5021006faa810802ff63084077f3184200bf58c2101df8c610802fe6208401ef1904200f70c821005fcc210803ef2108401fb1084200fb48421007ea4210802fe60084017eb004202bf5965000dfcc928002fd64940037e324a002dfd5250006faa92800
  | 3 => 0xeb1c640bf7d4e32007bca719003dd538c817ee29c640af7d0e32007bc8719003dd438c815ee21c6403bf98a32007be651900fef328c8017f30c6400bf58632005fcc119002fd608c801efb2c640bf799632007bacb1902fdc658c801efb24640af799232007bac91902bdc648c817efaa46400d7d5232057bca919003dd548c801aeaa4640af715232005bcc51902fdf528c801ef2946400f754a3205fb8a51902bdf428c801ef2146400f750a32057b88519003df618c801ef30c6400f758632007b8c31902fdf518c817ee28c640af7d0632057b88319003df608c801ef3046400f758232007b8c11902fdf508c817ee284640af7d0232057b88119002ff654c8057f32a6400bf59532015f8ca99002ff644c8037f3226400bf5913200df8c8990037f544c801beaa26403fbcc932007bc6499002ff614c8017e30a6400bfd8132005f8c09900eff650c8057f3286400bf5943201df8ca1900eff640c8037f3206400bf5903201df8c8190037f540c801beaa06403bf98c3204fbea61900fde530c801eea986403f714c32047be861900fde430c801eea186403f710c32005fcc419023ef420c811f62106403f7cc83201fdc6419003dd320c807f69906400bf98432005fac219002fe600c8017eb006403f7d943204fbcca19003dd650c807ee3286403f7d9032047bcc819003dd640c807ee3206409f7d5032006bea819023de540c801eeaa06400d755032047b8a819003de620c8016f3106400f39883204fbea419003de520c801eea906409f714832047be8419023cf420c801ef2106400f750832047b88419023cc420c807efb086400f798432007bac21900fdc610c813efa886409f714432047be8219023dc410c807efb006400f798032007bac01900fdc600c813efa806409f714032047be8019023dc400c8057eb2ca201bf99251005fac928806fc6494405bfaa4a200df5525101dfcc728802fd6394401bf29ca202df14e51005fcc528802fd6294401bf294a202df14a51007bc6528803dc32944057f30ca202dfd4651017eea32880bf451944017f304a200bf58251016f8a12880aff65544017fb22a201bf9915100df8c8a880b7f5454401beaa2a200bfd8d51007bec6a8802df63544077e31aa200f718d51005b8c6a8802ff62544017e312a200f78c951007b864a880aff6154405fba8aa200df94551016f8a2a880bf451544017fb02a200bf18151005fecb2080afe65904017eb2c8202bf1964100dfac9208077f5490403beaa48203bf98e41005fac720802fe62904017eb148200ef90a4100f788520803de3290401ee1948201bf9864100f7e8320807f74190403fa20c8200bf98241005fac120807bc40904017fb2a8202bf99541005facaa080afc65504037fb228201dfd514100f7ca8a08077d5450401deaa28200cf551
  | 4 => 0x37e6355001beb1aa800df18d54006b8c6aa0077f43550039fa1aa801df10d54006fec4aa0036f6255001bf312a800df58954006f8c4aa0036c6255003bfa12a801df1095400e7884aa0037f6155001bbb0aa800df98554006fac2aa0037c6155001ba30aa801dfd055400e7e82aa0077c4155001bfb02a800ded8154006fcc0aa0037d6055001be302a800de1815400efe80aa0077c40550039e202a802bf5965300dfcc929802fd6494c077e324a602dfd5253006faa92980efe6394c07bfa9ca602f7d4e5301fb8a729802fe6294c017eb14a600bf98653005fac32980b7c5194c017f304a600bf58253016f8a12980eff6554c017fb22a601bf9915300df8c8a980b7f5454c01beaa2a602bfd8d53017bea6a980f7e5354c07be29aa602f714d53005fec4a9802fc6254c017fb0aa600bf18553005fec0a9802fc6054c077fb2c8602bf99643005facb2180efc6590c037eb248601dfd524300efaa92180efe6390c07dfa1c8601f7d0e4301fb88721802fe6290c017eb148600bf98643005fac321802fe6090c017eb048601ef10243005fecaa180afe6550c017eb2a8602bf1954301dfec8a18077f5450c03df2a28601df551430077aa8a18033d5450c037fb1a8601f7d0d4301f7c86a180fbc4350c03ee21a8600bfd8943007dec4a1802ef6250c017e3128600fb18943005d8c4a1802ff6150c017e30a8600bfd8143005f8c0a180afd65948037f324a400bf5925200df8c92900b7f5494801beaa4a403bf98e52005fac72900afe6294805bfa94a402fbd4a52017d8a529002fe61948017eb0ca402df14652005fcc129002fd6094805be284a402bfd9552005fec8a9006fe64548037e322a402dfd5152006faa8a9002ff6354801efb1aa400b7d8d5201df8c6a9003dc63548016e31aa402bfd8952017dea4a90037e5254805be292a402fb14952005fec2a9002fc61548017fb02a400bf18152005fecb2100afe65908017eb2c8402bf1964200dfac9210077f5490803df2a48401df552420077aa9210033d54908077f31c8400bf58e4200dfcc521007bf4290803f7a148401fb10a42005fcc321002fd6190803de20c8400bf98242005fac121007bc40908017fb2a8402bf99542005facaa100afc65508037fb228401dfd514200efaa8a1002ff6350801efb1a8400b7d8d4201df8c6a1003dc63508016e31a8401bfd894200fde84a1003be4250803de2128401fb10942005fec2a1002fc61508017fb028400bf1814201dfecb9900afe65cc8017eb2e6403bf1973201dfec999006fe64cc8017eb266403bf19332006fea9990037d54cc819f7a16640cfb10b32005fcc399002fd61cc8017f3066400bf58332005fecb1900afe658c8017eb2c6402bf19632005fec919006fe648c8017eb246401bf19232006fea9190037d548c8017
  | 5 => 0x7b47f0000002c90000000002421eb17c0001ff0001e20000000000000003b21634540000002c713b1d41b912933a45d2ff2132741b528a16a3620000001c23372ab0990910000973b70000000000000000170000002764833270003aa0000670000008000000008000008020008000000000008000008028030020000008018028030000000008000010008000008018010008000050000010008000010008008000008000020020008020010000000000028000028048000000010018050000008000020008000010000000000000000000000000000008030000000000000000000000008018018008018008008008010000018000048010040010000008000090000000000010000000000010020008000000000000038000008010000000000008000010028028000028000000010000000000008008008000000038000018058010008000000008010000000018000010000038000038000010000008000010010010000000008000000000018000000000000000000010000000018000000020000020000008000000000000008000008028008028018000038010008010008000000008000030000008000010000000000010010000010000000000008008000000000008000000000010008000000000000000000000020000000000000010000000010010018000028028010000000000010008010008000018000000000060008008020000008000000030000028008018028010018010030000000000000018008068008020008010008000000000008000010028000000000000000020008030000000020010000058008020020030000008000000000000008018000008000038020000008018000000000000010008008000020000000000000040000050010000000000000018008000010008008000000010000008008010018000040058000000010000000018067d64d5005bfb1ea802df98f54016fac7aa00b7c63d5003bfa1ea801df10f54016fec5aa00b7e62d5005beb16a802df18b5400efe85aa0077c42d5005bfb0ea802df98754016fac3aa00b7c61d5003bfa0ea801df10754016fec1aa00b7e60d5005beb06a802df1835400efe81aa0077c40d50037fb2aa801bfd91540177ea8aa0077e5455003be2a2a801ef15154005fec6aa003df63550016fb1aa803bf18d54007b8c6aa002dc6355005bfa9aa802df14d5400f7e86aa002ff6255001f7b12a800bbd8954005f8c4aa003ec625500176312a802dfd4954016f8a4aa007bc42550017fb0aa800fdd8554005eec2aa002fc6155001fa30aa800bd18554016fea2aa00b7c5155003dfa0aa800bfd8154007f6c0aa002fb60550017e302a800fe18154005f0c0aa00b7f5055005be282a801ef1015400efec8aa0067f64550059fb22a800dfd8d54006bec6aa
  | 6 => 0x43c2a01cb0000003143cc00000000000000021d0003f100000041f00000000000000011c0000000000000000000000001c10000000001ef0000000000000000001cc0000000e10000000003af35000000003c00003e00043d0000000003c00000001930000000000000003000000001440000001db00012200015b00000000000000000009d42a29d00000004d10115100042932f1be0000004560000002380004044002de0000001d02910023a20000000c40000002e90000000003163ea2c00002d245827841934c00047d0003e100000000000000000038200006f27f09235a3ad0750000000000000000000000003e70000000000002960003810000550000000004640b40002b000000000015e00023417d1751b24420000003340002810000000000004900001780000000000002f80000000001e700000041b0002fa0000002570000001ea3090000000000002280001001d72871f30000ba2e200000534e01349700000000000043009f17a35349124000007642d0000000002792da00015000000000000000000044c0000000000000000ca00021b29c0780001e60000e21c60000000000000000000002bf0ac2440000001fb00000000000004600000046900009e11105700000000000023e0000000000000003050000000000000000000000000000ad0001b804100d00000000014500000000024e00000000000000000031700000000029e21f00009a0dd00017400000000000000007000000000000b12500000e00036e00000030a0004110000000002ed05b4060000ff14b3c300023918636400000021800000000012a0be0a80bd3650000000003dd00000043e0002fc0003870000000000000270000000000000003410110e700001b45f0001e10e000028c0000000004530000000001ac00000000004000044b2a50000000000003e40000000000000000000000000003890004080000000000000690564033bc0003452e300000000000017700031a0000000001bc00000000000000c00021126937443415c00002e0003a632e24d14f00000000000013a00000000000021e00040e0003513d00000000004664770000000bc0000000a145a3ae0c031d3350d000000000016c0cb00000000024130d1e80000000000000004790000000000000003f20a700033247200035622f0000000000001800000000000004120002200000000000002c40000000000002e80000e60000000000000000000004350001ba38f00000000000000000000000000000045b0000000002e100029700017b0001ec00039f1e000000026e2990000000003cd0000000001522150000001120000000001960004840000004270003750003230730000511870002030000000003d124300037d1583fe0000002eb0000000000000950074492f90000
  | 7 => 0x1f200000007d10200000000001f1980003702520000000004960000000003220002470000000630003243b000000000008622618f0000000000000000000000000002b900000034f00000000038b0003f64170000000000000003ed0000004150002591990000000000002301212a24630003eb0000b23f71af1dd3710000820000002bc2cb1310002680002aa00017e08835c0000000000000001a40001c73e80ed1d334820b3920000000000002e03a707e0000002f00000ef18813d2670000000000000000000003e306e2580000fe00000034304e04800000000000000000042f0381dc0000000000000003bf2f40002f200022a02b00025000000000007220118331f13200040b0000000000000000000000000000000000002be11f00000000000011b3b617644d00000028e0000003910002f73d42d80000000000000000000000000000001332a300000000000000000000000028d20a0002ce44337235800025c0df2864130002000a043332040100000012e0000000002a903a1de0000000000003072b500000018e00006b0000000f42ef3842770000000e300000000000000000037a00047a10a00000000000000000000000000000043b43a09300003300000000000027e0000003150000000000000000000f90000000000000003fb00037823338c02a00000000000000000000000f00000044700000008f45c0000003303120000000000000000000000000002d300044a00006d00016600000045243f39737700036d0001070000443d20000000c200000000000000000021225600000028b0002cf0000000000000000000000003b90002a82231702483213f33032c202c0c50902db27100000000000027b00000021c0000001460001a200000014c00000000042b09c0000bf2b40000000002b60000000000003960000740001a146f18b00000010800000000000000000000015400000048227d1d100032949947004a00000019f00000000013429f00040d00000000000000000000000000000000000000000000000000000048f0000a22bb18a0c10000003b100012f3553800d744100000000000006c1420001390000001472350003264622850000000b831c0000000000000000000000000000000002cd3b341e00027a0000001fc0000d900000000000000000000000000038e28f02000000000002500000000005224600000000000000044e0003f81571da0000161c039d2940000003dc1850ea00800000000016e0000f500000000048600000000000044400017107126d29000039a3ba0000980000000004980000000000000004673d300000000000022734223c10e0680183332d50000000fa3100000001d90004740000320000000003632d000025f2b10000f10000000002fe00040500000010600000000
  | 8 => 0x660000001721a50294452ba00000000000000000000000000000000000000037c23618d3d636b1950003a50000002753254870000000000000000470000000000774360002dc0d64730000000002920001370004940003ab0003fc3ac0000d84920000fc00013500000008a2981791fe03b3d507f36f00000046a01c00000000000000030625e3fa2224600004760001092cc1301ae2a400000028911d30820e00020632d00000000000022100014e1f64250000002f63980000000003a900000000000011800042045530c2f33cf2834610000000000a91fd33100036600036c33c00000000000000014800000000025d1730000000003c70a40000000002e40000000002c324b3df15611600008405e0000001f531800034a0000000000000003cb38d0000003de0d316b0000000000000000c94710000000000000eb26c0001f90310000000040001361ee0000000003e520d0000002d741c1f100000000000000000000000031e4220000000100000da48c4500000004460000002290003d70000000000000001ad1172490000000000000002050000000000000004213600001f847c0000003831ab3c108000000000049a0003e00000001cf0000000002c61f00000000000e90000003e200000000000000033e3bd04500000000035e00000000000037b00000000000000033600000026f1810ae2070850000003900000000000000000000000002f11b00000f800000000034000042800000000000000011e47846d00000046816832c0000260000000000790000000000003f000000000000002800000022d0003192d600009b40214d01400000000000029b00014a0003470000ab00008c0000010b62040003a004200000000000000000000000000000000029500000023f0000000000000000000000000000002c50000000000000000001590000000000000000001c500029a2530004930000000000000000000000000000000300000000001a72d91a30960000000000000000000000000002ca1920002ac0000000003b800000000047e0b92ea0000002ec00000008700041d38a0000000a60004164572e70000000002092653391d80002540000000540000000000000000000001d637916400000000000037326300000012400000000a0350000ee01d1650002a10000002c824c00024f0001f73d81ce0f308b2ee0000002b300000000000046500000000004f00000019a22e0001050003690003860000002af0000b000000000000000000000000300000000000021448120800000011a3db00017f0000003ee0000000001f430b16d00008d00048000000023b00000000000000034941000038813e3ff4073130001e90000000001d200000014125a32a0000dc0000000001bb00000013f06104c0000000002640000002102c102f
  | 9 => 0x2100000000000005d0000000000002610001aa19700000019e0000003bb1030001b133f0240fb3a40c30000530652730000002a709425519c00048810400000000046e0150000340c600000005900036800946b3d92e50002a635200048a23147b40c0aa21700000042e0000001fa0000000000000000000002ae4850000000000a520f30234426200033b12b0000000000000002d402d00006600000000000000000000000000021a0001261550000000a30000600cd1690b30000000000000000003f50003ec00000000000000000032818423206401e0000f71132510000000e83fd34636a27200013800004b0002b82bd48b2600002241a62252df0004263e900000042c3da23a00000010f0000000d50000000000003f40000002e600000000016106a0000e505a0000000001ed1c400000039c0000000000000b130f4313381a00001670000002f50000003943592fb0583ce19b1623991b71140000ec00000600045900000000018c0000f22d10003c90810193540000000af00000001200000005000011000040a42344827036142400005f4143ef3b527c1431ca0831e402210b0cc0000000000000003850000000000000001200000004090000000003be23d16000000000000000048d0000000004750f632b00000000000049500037e0361b42020000cf37f3b41821900e40d20000000f00000000000000000ce0de1b63c80003011c907a3a805c0371a802300000012c00008e00048e0002840000000000000000000001940000000002ad00010d00046c1270000000003a30000000000000000000000000003040000000000000000000000000d40fd0622b20000000003670000002fd0000000001233c60001d50000004184891a925b0001490c700008903f1e34510000000000393111cd0000000003a101a0000002190000000000000000000000000000002dd00000000000000015320c00003d00044030e0000000000bb00039e10c00012d00000000000035f0001bf3c440f00023700000000000000000039b3c24383761e512843726b00007c3570000000000b50c800000034b0001bd2931c80000000000000003c500000000000000024a0b700000000016f00000028000015d34d00000011526a0000001b30000000003f900041a0000d104335b00000000013c00000000000000000000000000000000000035d00022c00000019d0002b70001df22b21600000004939300000000000014000043200018900033d00044f0db0004391193950000003ca28815f45e31b19128215a0003e60000000000000001c32452
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe76191100063f65191100063c65191100047e76d51100147c76d51100063f64d511000e3c64d51100047e76551100047c76551100063f645511000e3c645511001cde76d8d100065f65d8d100065c65d8d100069f64d8d100069c64d8d100065f54d8d100065d54d8d10004de72d8d100047f7558d100147c7558d10004bf7458d1000cbc7458d10004ef7258d10004ec7258d10004f77158d10004de7618d100065f6518d100065c6518d100069f6418d100069c6418d100065f5418d100065d5418d10004de7218d1001cde73d8910004dd73d89100066f65d89100066c65d8910006af64d8910006ac64d8910006cf63d8910006cc63d89100066f54d89100066d54d8910006ce73d8910006cd73d89100147e75989100047d759891000cbe7498910004bd749891001cde7398910004dd7398910004ee72989100047f75589100147c7558910004bf745891000cbc7458910004df735891001cdc7358910004f77158910004fb7058910004ee76189100066f65189100066c6518910006af6418910006ac6418910006cf6318910006cc63189100066f54189100066d5418910006cf7318910006cc7318910004de768c910004dc768c9100065f658c91005e5c658c9100069f648c9100569c648c910006cf628c910006cc628c910004de760c91001cdc760c9100065f650c91004e5c650c9100069f640c9100469c640c910006cf620c910006cc620c910006e862c4110006d46384110006e4628411001cde73d9410004dd73d9410004ee72d9410004ed72d941001cde73d9010004dd73d9010004ee72d9010004ed72d901000e3e64550100063d6455010004ee72d8c10004ed72d8c10004dd7698c100065f5498c100065d5498c10004de7298c100047f7558c100147c7558c1001cdf7658c100065f7558c100065c7558c100065f5458c100065d5458c10004dc7258c10006d47158c1001cde73d8810004dd73d8810004ed7698810006ce6398810006cd63988100066f54988100066d5498810006cf7398810006cc73988100047f75588100147c7558810004bf745881000cbc7458810004df735881001cdc7358810006ce6358810006cd63588100066f75588100066c7558810006af7458810006ac74588100066f54588100066d5458810006cf7358810006cc7358810006e47158810006e8705881001cde7318810004dd7318810004ee7218810004df768c810004dd768c810006ce628c810006cd628c81001cdf760c810004dd760c810006ce620c810006cd620c810006d563cc410004f5760c410005f1700c410006e562c8410007c432c8410004f57608410006e962c8010007e321c8010004f97608010007c83208010007e0210801001cf97684010004f77644010005d47344010005e47244010004fb7644010005e87244010
  | 1 => 0x9120004f47159120004be76191200063f65191200063c65191200047e76d51200147c76d51200063f64d512000e3c64d51200047e76551200047c76551200063f645512000e3c645512001cde76d8d200065f65d8d200065c65d8d200069f64d8d200069c64d8d200065f54d8d200065d54d8d200047f7558d200147c7558d20004bf7458d2000cbc7458d20004ef7258d20004f77158d20004f47158d20004de7618d200065f6518d200065c6518d200069f6418d200069c6418d200065f5418d200065d5418d20054de7218d2001cdc7218d20004de768c9200065f658c92005e5c658c9200069f648c9200569c648c920004de760c9200065f650c92004e5c650c9200069f640c9200469c640c9200067765d85200067465d8520006b764d8520006b464d8520006d763d8520006d463d85200067754d85200067554d8520006d632d8520006d432d8520006776518520006746518520006b76418520006b46418520006d76318520006d46318520006775418520006755418520006d63218520006d43218520004ee76c8520006cc63c8520006e461c8520006cc6348520006e46148520005e87048520006f061c8120006cc6388120006e4618812001cde73d9420004dd73d9420004f671d9420004f571d94200063f645502000e3c6455020005ce728c820004ed760c820005e9700c820006ce760c820006cd760c820046ce640c820046cc640c8200074f540c8200074d540c820007ca700c820007c9700c8200047f75584200147c7558420004bf745842000cbc7458420004df735842001cdc7358420006cc3258420004ed7688420005ce738842001cde7398020004dd7398020006cc3298020007c83288020004ef7648020005cc7348020005e47148020004fb7648020007ca3248020005f07148020004df735971001cdc735971000e3e64553100063d64553100147e75d8f100047d75d8f1000cbe74d8f10004bd74d8f10004ee72d8f10004ed72d8f100147e75d8b100047d75d8b1000cbe74d8b10004bd74d8b1001cde73d8b10004dd73d8b10004df7358b1001cdc7358b10006ce620cb10006cd620cb10007c8320831001cde73d9610004dd73d96100063f645521000e3c64552100147e75d8e100047d75d8e10004ef7258e10004ec7258e100147e75d8a100047d75d8a1000cbe74d8a10004bd74d8a1001cde73d8a10004dd73d8a10004df7358a1001cdc7358a10006cf620ca10006cc620ca10007c432c86100147e76d95100047d74d9510004bf745951000cbc7459510004df735951001cdc7359510004ef7259510004ec72595100047e761951000cbe76d91100063f65d91100063c65d91100063f75d91100063c75d91100047f75591100147c7559110004df735911001cdc7359110004ef7259110004ec7259110004b
  | 2 => 0x1ecc3258b30004ee7298730004ed729873002d5c754c730004ee72d9230004ed72d92300063f645523000e3c6455230006ce628ca30005ce728c630024dd73d95300265f53d95300147e76d95300047d74d95300265e73d95300065d73d9530004bf745953000cbc7459530004ef7259530004ec7259530004f77159530004f471595300047e761953000cbe76d91300063f65d91300063c65d91300063f75d91300063c75d91300047f75591300147c7559130004ef7259130004ec7259130004f77159130004f47159130004be76191300063f65191300063c65191300047e76d51300147c76d51300063f64d513000e3c64d51300047e76551300047c76551300063f645513000e3c645513000e9c6490d3000cdc7650d3000e9c6450d300071d5450d30005cc7250d300066f65d89300066c65d8930006af64d8930006ac64d89300066f54d89300066d54d89300066f65189300066c6518930006af6418930006ac64189300066f54189300066d5418930006cf7318930006cf5318930006cc5318930006ce4318930006cd43189300065f658c93005e5c658c9300069f648c9300569c648c930006cc628c9300065f650c93004e5c650c9300069f640c9300469c640c930006cf620c9300067765d85300067465d8530006b764d8530006b464d8530006e762d8530006e462d85300067754d85300067554d8530006d632d8530006d432d8530006776518530006746518530006b76418530006b46418530006e76218530006e46218530006775418530006755418530006d75318530006d45318530006d64318530006d54318530006d63218530006d43218530004de76cc530006cc62cc530006d461cc5300255c754c530006cc624c530006d4614c530006cc628c130006d4618c13000e3e64550300063d645503001ecc32988300047f75584300147c7558430004dd768c430005ce728c430004df764c030005cc724c030005d4714c030004df735972001cdc735972000e3e64553200063d64553200147e75d8f200047d75d8f2000cbe74d8f20004bd74d8f20004f671d8f20004f571d8f2001cde7398720004dd7398720005e8704872001cde73d9620004dd73d962001cde73d9220004dd73d922000e3e64552200063d64552200065f5498e200065d5498e200065f5458e200065d5458e20006cf7258e20006cd630ca20005cd760ca20006cd760ca20046ce640ca20046cc640ca200074f540ca200074d540ca20006cc3258620005ce73886200147e76d95200047d74d9520004bf745952000cbc7459520004df735952001cdc7359520004f77159520004f471595200047e761952000cbe76d91200063f65d91200063c65d91200063f75d91200063c75d91200047f75591200147c7559120004df735912001cdc7359120004f7715
  | 3 => 0xf6518d210065c6518d210069f6418d210069c6418d210065f5418d210065d5418d21004ee76cc921066ac64cc921005e671cc921004de768c9210065f658c92105e5c658c9210069f648c9210569c648c921005ce728c921004de760c9210065f650c92104e5c650c9210069f640c9210469c640c921046ac640c921006cf630c921005ce760c921006ce760c9210074f650c9210074c650c9210078f640c921046ce640c921046cc640c9210078c640c9210468c640c9210074f540c9210074d540c921007c432c8521005ce73885210067b65d81210067865d8121006bb64d8121006b864d8121006db63d8121006d863d8121007c832d81210067b54d81210067954d8121006da32d8121006d832d8121006cc32181210067b6518121006786518121006bb6418121006b86418121006db6318121006d86318121007c832181210067b5418121006795418121006eb3218121006da3218121006d83218121006e83218121006c83218121006f32118121006ea2118121004df735942101cdc735942100e3e64550210063d6455021004ee72d8c21006ce620c82101cde7398421004dd7398421004ef7648421005e87048421004f77648421007c63248421005f070484210047f75580210147c7558021004bf745802100cbc7458021004df735802101cdc735802100c7f76552500063d64552500055c73552500056c725525000574715525002e5f5498e500065d5498e50004de7298e5002e5c5198e500265c7558e500265f5458e500065d5458e50004dc7258e50004bf7458a5000cbc7458a50004df7358a5001cdc7358a50004df768ca50004dd768ca5001cdf760ca50004dd760ca500065e639465000c7c75d915000c7c76551500063f645515000e3c645515000578705515001cde73d8950004dd73d8950006cf620c950006cc620c95001cde73d9640004dd73d9640004ee72d9640004ed72d9640004f671d9640004f571d9640074fa70d9640014bf76552400059c7355240005ac7255240005b471552400163f76552400163c76552400071f73552400071c73552400072f72552400072c72552400073771552400073471552400073b705524000738705524000e3e605524000f3a60552400047f7558e400147c7558e400063d5458e400063d5498a400047f7558a400147c7558a40004df7358a4001cdc7358a400071d548ca400071d540ca40006ce620ca40006cd620ca400478c420ca400047f75586400147c75586400063d5458640004df735864001cdc7358640004df735954001cdc7359540004ef7259540004ec7259540004f77159540004f4715954006cfb705954001cde73d8940004dd73d8940006cf620c940006cc620c94001cdc735973000e3e64553300063d64553300071d5450f30005cc7250f3001ecc3298b30
  | 4 => 0x82410147c7558241004df735954101cdc7359541004ef7259541004ec725954107cf77159541004fb7059541004f87059541014bc76551410163f76551410163c76551410071f73551410071c73551410072f72551410072c725514100737715514100734715514100e3f615514100f3761551410073b70551410073870551410063d54d8d4101cde73d8941004dd73d89410063d54189410071d548c9410071d540c941006cf620c941006cc620c9410063d541814101cde7318141004dd731814100e3e64553310063d645533101ecc3298b31004ee72d9631004ed72d9631004ee72d9231004ed72d923100e3e64552310063d645523100cdf7650e310071d5450e31005cc7250e310066f5498a310066d5498a31006cf7398a31006cf5398a31006cc5398a31006ce4398a31006cd4398a310066f5458a310066d5458a31006ce628ca31006cd620ca31006ce62cc6310147e76d95310047d74d953103cdf73595310047e76195310053d74195310047f75591310147c7559131004ef7259131004ec7259131004fb7059131004f870591310047e76d51310147c76d51310047e76551310047c765513100e3e64551310063d64551310065f658c93105e5c658c931006cc628c931005d6718c9310065f650c93104e5c650c93103e5c658c531005ce728c53101cdc735943100e3e64550310063d64550310071d5450c31005cc7250c3101ecc329883101ecc3258831004df764c4310355c754c4310047f75580310147c7558031004bf745803100cbc7458031004ef7258031004ec725803101cde73d9721004dd73d97210063f645532100e3c64553210147e75d8f210047d75d8f21006ce760cb21006cd760cb21046ce640cb21046cc640cb210074f540cb210074d540cb21007c6710cb21007c5710cb2101cde7398321004dd7398321006cc329832101cde73d9621004dd73d962101cde73d9221004dd73d922100e3e64552210063d64552210065f5498e210065d5498e210065f5458e210065d5458e21006ce63c86210147e76d95210047d74d9521004bf745952100cbc7459521004df735952101cdc7359521004fb7059521004f870595210047e761952100cbe76d91210063f65d91210063c65d91210063f75d91210063c75d91210047f75591210147c7559121004df735912101cdc7359121004fb7059121004f87059121004be76191210063f65191210063c65191210047e76d51210147c76d51210063f64d512100e3c64d51210047e76551210047c76551210063f645512100e3c645512101cde76d8d210065f65d8d210065c65d8d210069f64d8d210069c64d8d210065f54d8d210065d54d8d21006cd72d8d210047f7558d210147c7558d21004bf7458d2100cbc7458d21004fb7058d21004f87058d21004de7618d210065
  | 5 => 0xe3c64552320571f4355232014df7654e3200cdf7650e320071d5450e32005ce72d9632005d671d9632005d571d9632005ce72d9232004df7655232004dc7655232005cf7255232005cc7255232005d77155232005d47155232005db7055232005d870552320065f76552320065c765523205f1f74552320071f64552320571c64552320074f72552320074c72552320571c42552320075771552320075471552320571f41552320075b70552320075870552320571c405523204cdf7654a320071d5490a32044df7650a3205d5e75d86320055d75d8632006d7619863205d5e75d82320055d75d82320559e74d82320059d74d8232005d671d8232005d571d823205cdf7359532054df7359132064ef72591320063f645513200e3c645513201cdc735943201cdc7359032044ec725903200e3e64550320063d64550320471f43550320472c42550320071d5450c32005cf7250c32004df764c8320047f75584320147c755843201ed431584320047f75580320147c7558032004bf745803200cbc7458032004f77158032004f47158032045cc72590320478c42590320455d74d503204f4e72d503204f4d72d50320474f42d50320474c42d5032004df765503201cdc7655032005cf7255032005cc72550320478c4255032005d77155032005d47155032005db7055032005d870550320065f76550320065c76550320455f745503204f1f74550320471e64550320071d64550320074f72550320074c72550320474f42550320471c42550320474c42550320470c42550320075771550320075471550320471f41550320075b70550320075870550320471c40550320565f54988320565d549883201ece7298832045ce7498832045cc74988320074f54988320074d5498832005cd7198832005ce709883205cdf76548320071d5490832045ce7290832054df7650832045cf72508320055f755843204d5c755843201ed461584320055f755803204d5c75580320059f74580320459c7458032005d77158032005d4715803200c7f765525100e3e64552510063d64552510055c73552510056c7255251005787055251004bf7458a5100cbc7458a51004df7358a5101cdc7358a51006ce620ca51006cd620ca51004bf745825100cbc745825100c7c76551510063f645515103e5f54d8d510065d54d8d51004de72d8d510365f5418d510065d5418d51004de7218d510365c5118d5101cde73d8951004dd73d8951004de768c951004dc768c951004de760c95101cdc760c9510065c639455101cde73d9641004dd73d9641004ee72d9641004ed72d9641084f671d9641004fa70d9641004f970d96410047f7558e410147c7558e410047f7558a410147c7558a41004df7358a4101cdc7358a41006ce620ca41006cd620ca410478c420ca410047f755
  | 6 => 0xb62d81540076862d815406f3842d81540077361d81540077061d815406f3b41d81540055e73981540055d73981540065c63981540056e72981540056d72981540066c62981540057671981540057571981540067461981540757a70981540055f73581540055c73581540056f72581540056c72581540057771581540057471581540065c63181540066c621815400674611815400679601815406d7a76181540067a76181540a73b74181540773874181540767b64181540a73b64181540075b63181540067a63181540067863181540075863181540065863181540773b43181540076b62181540067a62181540067862181540076862181540066862181540773842181540077361181540067a61181540067861181540077061181540067061181540773b411815400c7f765525300e3e64552530063d645525300574715525300578705525301ecc3298a5301cdc7358a53004bf745825300cbc745825301c7c76551530063f645515301ecc3298a4301cdc7358a4301ecc3258a430047f75586430147c755864301cdc735864301cde73982430047f75582430147c755824309cdf7359543004ef7259543004ec7259543004f77159543004f47159543004fb7059543004f8705954301cbc76551430163f76551430163c76551430071f73551430071c735514300e3f635514300f1f63551430072f72551430072c72551430073771551430073471551430073b70551430073870551430072d54d89430666f54d89430666d54d8943066cd73d89430063d54189430072d54189430466f5418943046ae54189430466d5418943006ad54189430062d5418943046cf7318943046cf4318943046cc43189430063d54d85430063d541814300c7f76552520063d6455252005747155252005787055252004bf745825200cbc745825200c7c76551520063f645515200e3c645515205e5f54d8d520065d54d8d5204e5f5418d520065d5418d5201cde73d9642004dd73d9642094ee72d9642004f671d9642004f571d9642004fa70d9642004f970d9642014bf7655242005b47155242005b870552420163f76552420163c76552420071f73552420071c73552420072f72552420072c725524200e3e625524200f2e62552420073771552420073471552420073b70552420073870552420063d5458e420047f75586420147c75586420063d5458642004df735864201cdc73586420063d549824201cde7398242004dd73982420047f75582420147c7558242004df735954201cdc735954208cef7259542004f77159542004f47159542004fb7059542004f870595420565f54d8d420565d54d8d420465f5418d420465d5418d42046cf4218d42046cc4218d4200e3e64553320063d64553320672c4255332004f671d9632004f571d96320063f6455232
  | 7 => 0x8954006cf7318954006cc73189540c66c51189540c66c5018954096ac4018954006d763d8554006d463d8554006e762d8554006e462d85540be7675d855407e7575d8554006d76318554006d46318554006e76218554006e462185540b6767518554086757518554086b674185540b6b574185540b67453185540b6745218554086b442185540b6745018554086b44018554006db63d8154006d863d8154006eb62d8154006e862d8154006f361d8154006f061d81540ae7a75d815406e7975d815406eba74d81540aeb974d8154006db6318154006d86318154006eb6218154006e86218154006f36118154006f061181540a67a75181540767975181540a67853181540a6785218154076b842181540a67851181540e71f74d8d5409f1c74d8d5409e5f64d8d540e71f64d8d540055e72d8d5409f1c42d8d5409f1f41d8d5409f1c40d8d540d55e7398d540056e7298d540056d7298d54005767198d54005757198d540057a7098d54005797098d540056f7258d540056c7258d54005777158d54005747158d540057b7058d54005787058d5409d5e7618d540065e7618d540d71e7418d540071d7418d540d65f6418d540df1f6418d540055e7218d540d71c4218d540d71f4118d540d71c4018d540055e73d89540055d73d895408f2e74d89540072d74d895408e6f64d89540cf2f64d89540074e73d89540074d73d89540074f63d89540074c63d895408f2f43d895408f2f41d895408f2c40d89540055e73989540055d73989540956e72989540057671989540057571989540057a70989540057970989540055f73589540055c73589540057771589540057471589540057b705895400578705895408d6e76189540066e76189540c72f74189540972c74189540966f64189540c72f64189540074f73189540074c73189540074f63189540074c63189540972f43189540972f41189540972c40189540bf3774d855407f3474d855407e7764d85540bf3764d85540075763d85540075463d855407f3743d85540076762d85540076462d855407f3442d855407f3440d85540055e73985540055d73985540065c63985540056e72985540056d72985540066c62985540857671985540057a70985540057970985540055f73585540055c73585540056f72585540056c72585540057b70585540057870585540065c63185540066c621855407d7676185540067676185540873674185540073574185540867764185540b737641855400757631855400676631855400674631855400754631855400654631855408737431855400767621855400676621855400674621855400764621855400664621855408734421855408734401855406f3a74d81540073974d815406e7b64d81540af3b64d81540075b63d81540075863d815406f3b43d81540076
  | 8 => 0x4c5bcbc4ac51894d000064c0000005140000000000000009ec0b4000b8c00137c000b612346411b04149380b91cc990f845995b416d2e12dce8003c3105d009c038000000001448519278030d595549709009743e91a8c480010640000000000000000006c5519375098d94000e6089d0c065c6bc8247855b93892f8ed01992e5101170ee4ca4fc0b0c78c4042acc0827c4c4248bf0d512082702f9501284cd438c7d4e943142d037d0d10a0c10d886e8fb90bc770adcf88829364d6839d0ed0a4050b1cab42a067d2bcb515315993a1488230ced46c760a6462c0c8d00000b78664930c5c000ed4f6800407001038004008030000041380500c00000003034090000230060000000500000400800002054008580020140000001a0301003e000014000120040600280102001c0002001a00803801000000008050040000000000005808001012000018000000ec0081305600c0000800a0280082d0220000481d0100040400e0020040100001a000080050000000680200c070000150000200f81200600423006006054038050000200300200001000812000004070050160000000703e00008002000034000070080400000600600c1b00100a0180400001a0000500a000010040000180000700300001406809000014110040080c80400f00000c00005012018090010160740000d00e0140000001a024038020040ac0000000c02c1b00000005401813012004088080000000b0100140080e00201201803001004000018050040200e80107002c0300100201c028060120040d8130040240101201e008018180120480280f00c0140001100a0200101501a02c00001000004018000000140080700a0000600500000826005004004000020020042180b0020440b80100800c00800020004040020020000000004a03404800008000000000020100580c00206c000000000180000d0120000182000400402000000008018010020b0000030000800d80200001c010070040180300000c0400002a05807400000000004000000480000500703a01c01027006170000000080100c0000000240781000a008018030000080000004003c0000201e04000810000020010030060001900e0000440001f01601c0000300a0a4000030040200681104a05c0100a01a0200180e0040701100c02608800803004024000080040000180700a000070020200f00400101cde76d8d540e65e75d8d5409e5d75d8d54004de72d8d5401e5e7518d5401e5d7518d5401e9e7418d5401e9d7418d54004de7218d540de5c5118d540de5c5018d540d69c4018d5401cde73d8954004dd73d8954006cf63d8954006cc63d89540ce6e75d895408e6d75d895408eae74d89540cead74d8954006ce73d8954006cd73d8954006cf6318954006cc63189540c66e75189540966d751
  | 9 => 0x3487e0de156c8014f85480006011f0000ccc1408e401521c00034c0011fcffc3fc000000d209591b4000eb460c4ac818534f49458604ad00483b8d38a0ce094043d8000b7cc251c00009f4c4102d2c4ea8bcd0500000002d400000156400098c3500011940002e4af4000b08000000000ee00002f0f0800000108c000000f10000b48684924000aac000000b684ec7e43b00010e11754c0028490588fd06209bc0011e04793552d43912700d800055d3dcfdc578001238e510341846292e84c86e54782b0ead140928cac110228690454f4cf8ce4cdb10ac094d083387f0df940d54468c29891442d1289344754c8000d040006ecd2d00c8c8ac13453d8dc0a8400000000063475cd6cc00318a053411042e082ce4142c15445c4e4b545e44b87f5490f1c000e2ceb152cf35360504000d34430bc8e2543857494c000194a2c5cc1180ec0013e55204bcf214fcda4b284fc5f02210400008b4c1485c538540000f30654000a593348fc4d40000014244a0c0caa50580012410445613d01241787a084002c5dc00c000dd4e8d27c0003e4001094f18e5c3607511901d4c392c8ea0495115548b2451c7cc81505c54c05c3bd180a714312d8fe42946f818112c630cb00e425d5385a01c8b9048915850d09d10c5f8cd03ed4a95a8204700764bfc7800104985214b09cd4dc7ecbe90751bd3f89e0368008040b74b35224cb8a247b0214af0c30c043f072d414ecc48c13c61859c97c8f543ceec0ad1691c86d82c04f00988d0128ef0f2c4682a95b071555c0007406d026954d295358f948ad1ace74f711850483706a91ec4e90f04514849502fcd113ad0180706601e81e4e892b903d060ae933043c758754be4995008cdc0012c000042852c000e440001655284d82d8d74000dd84a42b46f000000000011c0e14e06b0000000708418bf51f53c0001384000001514241350000c8c00125c2a45a558854444012cbdc720a3cf985853e92a80004a808807d1f904c001470c94344a4d068001580000000d1488549c080308d98158510e9c01800026cbb8bbd33d4e4000d2800000000000076c0009d88982447c82c43c91d4000f542612b4000c20fa10fc0000000011a40000009543848081f4edd02000147400121800125090c0a12052ac844160e8558ccd800000046cd180007a4000a207a800053c67000139c32041c83d2f10a800046000000029c0000001e0000d48a7d5093103b4374d5c0001fc334000000000001258000000a9ca954d48e0000ba49a8f404704091dcca89e5308000000a181d04dce34f6c000001348c9c000000ce12d0dc4888464e7c6580000003e03011b87c4fe8b6c6886a4594ec53d41045fd4c40011249854a0ded3e05f50544e0068570d6464822c66895d2fc92c6447b4e54aec17cc4556837944c0f06dc80523d434c
  | 10 => 0x36532545c0541cc6e0c7469d4b49c85ed2209b0f2421d2a0e14e2000039884ce008c4550114c592b09b4fc5138eb80000008f0c6c1ec724e3c0002b87042bc4800a51a124c0a80000010f94cc7f941028cb3c6d4f9070d300e315a0085498d4d1e47693ecce80012905a8004b4cb386c8250000e700009dc531320b9c32d47d2000603dd025464bd0a8c978b955410040004f55a4d90280c34650fb0e10c547483049c083540017122c9800003a94b8fc90cc00000000106cd854e93b00009207890385588210e94ac40cad40d0d60d54dac000b2c000c7c73cba1210001130000000fa4d30acc000a0806c23400116c20120d378524ba8a88df54f0000a985c0000d1cd0c0013bc3acee94bc2cc0000005b4a5c2dd080fcd0280340ccb0444c868c5058c000000f78000f3922889477c84800023ccf9550000000df0108ca08b87988ec8e8bd4a78d24f812141a8ff8d9d3a47fd14c3892546fd4a51d919cae41b474531c790d3c998cc46f46cc000000905244de89d47d801c830d8c93cf4427402412040000018ca14afc3c52ed50d3b40440012cc1b0f0135cc28da90846a0dbcebc3ccb880f420c8f9120850b80da05d430c8707e90b81a0738a8056499cff07b8a6c8593c874ccbd17c000e790c433c9acb8559045930cab9160000000880001445150f7400134d268d70a3804c9685e863c224a1ca34a28efcb10ddc5c8b440000009490d47c0794135451090cc1380ea472936c00113452887951d3f0500fac000150ec07103c03248bc4441884d1441454b211792989109f0075198b30c908d473091c5c4590168bd8f3d1549b8e1cc70e995109605552751093cc284fd8c84718e38cf1524448b406249882c8c89314bb456d2895940fd1184c13913993a8c2d558cfd480ec831c508130ad87d08dd4083d4864ab0a50438b714d81f82590dd534b006c0bc00013c40005b0fbc000cb4f29014de50b0e189a0394058a6115c9f8000918bec0015ac340810000a3000079c00000148d000a9129c00008cbb03a4000e6953c001071560ae077836c2652300010f48d8dcccf40b00c541c874bf80d4000f60000000b64e2800111cc180015848a8cc8100000c613fc0000000000000000006ac000a000000011c4358000148000c652a4f50a68dfc8c13f463957847cd803288380001c4f580008b080d4204cc7dcbac49d010fa8238a406790300000008cc000965504000000fd400057cf64064000680be0f5c210ac82f435cc694944f8484f0c00000086cce4420000909110254f7d2f4c7819c1746b90e52641b907800000000000000014530400087c0003f8b18d4532ca485806b41c01ac5ad18c000dd1144000000000944218d40b580dc608fec6994ec7345b82900001bce9128d13c9e80000000004b4000f9c07871c138c1c2084b101c00
  | 11 => 0x9c4890c801d88a0674000000000c3c00066d1650c9370001280b5c0e959c0005e0b140008605685d87bd318380000e482780009d0854ef8f047ac000aa1368d7c288e04e0d4194281f000061c1a4000000000000db4434000a743d00003f5338000000db800138cc990d86948a42ec96c001260f143a0ff4331460e58b993949a5248e6415d4f400000126d1e93b810c00077435546907c24c0900011d00000c06142e800088c940dc90890b40000bcfe0424a100201dced8000e6c0f8ef4aa8d79148610af814c190fb40015749fca5557c00041081c001570000a44abd328
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xd18731c15450c01a50e4382a8a18034c1c4705514304707b1aa83128619c2f875506250c318590eaa0c4a180383e0d54189430070641aa83128608e0f735506250c01c4f02aa0c4a180389205541894300715c02a83128600e28805506250c3185eec392a921003451cc715524200692390e2aa48400d18731c15490801a50e4382a9210034c1c470552420060eaa6e6b0c8400c1d545ce609080161d05b22a91900313dd872552320062bbb0e2aa46400d44721c5548c8018b6ec382a919003521c87055232006a8388e0aa46400a5685d86618c81145904b22a8190032310b76550320fec2210e2aa0641dd88421c1540c801c1885bb2a81900383108765503204586412c8aa06400c4f761c9540c841e0885b8aa819003151d87155032006a2390e2aa0641ff04421c5540c83de1085b82a819003161d87055032006a4390e0aa0641df08421c1540c801aa0e2382a819023431d1549883204687392a92106408a8c845883294437838ec39aa8a08630b1d872551410be1a3b6e2aa28200d24721c55450429870ec382a8a0803461cc705514100694390e0aa28200d30711c15450401c1aa831064a080307551731814100466412e63028201c1f76551438c401a1aa8392871880293a177398a3100546c20a731462088cc8750e628c401c1aa8a1cc51881f07d8d74195310141e43ac8aa26200a2c82591544c40147100b22a89880315196718c9310062632ce518a6200d0d541c9430c411c18c8aa06590822a3a1b640c92100707b28c81924200e0c65190324840149d0daa0649082383193540c92100526432a81924208e0c645503248401d10c8196c090802b2a18321812100725b28643024200e48650c86048401d16c8190c090803a219032181210057140e643024200e4b540c86048401c92a8190c090803b00cb21181210056541c423024200dc2321c121084014a902aa4c728003451cc715524000692390e2aa48014c3b761c15490001a30e6382a9200034a1c8705524000698388e0aa48000e0d54988329000183aa9b9ac32000233a0b735864000686aa0e4a1e6000a2e82d91548c0014390caa28698007071d95450d3004646320e4a1a6000d0d541c9434c00151b08298c4980223321d431893000706aa2863126000a958414c614c001c2aa8a18c298002b12094318530006263a8c498a6000c5475185314c011c1cc8aa065100033218c7048520004f040ae01904008e0c64550320800178102b806410023231d03258420004e543c649004000dc2321c5200801151d09b106508002876107558c100042e43aa8b182000c54751c56304001858ea3a2c4080021b21d5458810006463a0e6b102000cc8731c162040019c0e2382c408022a3211620c810004f0412e01882000ac5860cb21040015930c1904008003325d83208010
  | 1 => 0x5c09b1994003395c1c3b128000e230025442be0b020085345b7174485299512c5030b0002468145843c3c1c538a8268016000000d8000035afc00000027804003f9d5920000000006320a8cb00053ac80000470010e4a5a21000492637900da61a6d220d6b30400005e8147ead25a996c3d510a4f80f0005400526c800002b4b941106a499c83e00360019aab33000be1d08a6000430000128000000198b800000fcb70da9002003083000db6c2bc80450007000bc3d11cb46d383207c00018c5a800000e02e000000050343d8280062000015474688000000000009e5d323540039000000042548d46400002e52c0048000aab57020d768100280ee2d0015000c41133cbc68059b962922322800186e9585c823ea3cf2b317800206942a30002a198806e8d04851964e13a7d5c5b6981205068380e0400004040101800080000064000001000000a0000c1001018400e090080016060d010061202018080a0380c140001800000e028080000088041417040341401068000201018040a01010100608020034310a72d8d5400586412e831aa800d0e749cf62550018b0c7384c2aa0031a18a70985541752b41cc630aa800a668298c61550014e501318c2aa0b785a1063185540070ac20c630aa82de167418c6155001c2ae8318c2aa00295a08631855416f0a210c630aa82de144018c6155001c88c7b10c2aa00295a0e621855416533414c430aa800a72809886155057c4ec8310c2aa00391d8c621855400722318c430aa82be27841886155055c4908310c2aa0ab899d0621855400712ba0c430aa800e47831886155001c8906310c2aa0ab89d0c621855415712200c430aa800e50631876055001cc0c430ec0aa0031518e719815400632314e3302a800c567318660550018cce430cc0aa0029620d601815400534412c0302a800a708158060550534b507318c0aa0029aa0a63181540053940cc6302a828e1b6418c605504fc3508318c0aa0038661063181541470dba0c6302a827e187418c60550014b504318c0aa09f86108631815413f0da08c6302a800e4863d8860550014b507310c0aa09a9aa0a62181540053940cc4302a825e2b641886055001c96c6310c0aa0039218c621815412f15c20c4302a824e2884188605504bc56e8310c0aa0938a1d0621815400725c18c4302a800e48831886055049c5686310c0aa0938ad0462181540072831ec2302a800e6062d8460550014b507308c0aa0029aa0a611815411d3940cc2302a822e33641846055001ca6c6308c0aa0039418c611815400731b10c2302a800e60621846055043c6508308c0aa0038c610611815411719ba0c2302a821e30741846055043c6686308c0aa0878c10861181540e60e3b6e6aa28600a2e86dc95450c2d868ec38aa8a1803491c871551430a61c3b0e0aa28600
  | 2 => 0xce601bc24604d000001a181cd8e761337d42192cb4888991d0793ad7432b00
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x9202803a65803004841aa60000000042822c7006947a20000800000400011c50001604926106318554005822498418c60550638248720554189431860a21c805506250c01a0883201541894300688204805506250c0121594a17619863200701108761c5540c801c08421d8705503217f40108711c1540c80101c98551731814100603550825cc605040120d94a177398a310460321d5450e628c40141594196718c93100503650659ca314c40180d54a0b735864000503259541c9434c01180c875514318930006815508250c614c00140d941d4624c5300050565075185314c001415941d47158c10
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x5
  | 2 => 0x6
  | 3 => 0x4
  | 4 => 0x9ce
  | 5 => 0x168e
  | 6 => 0x24e
  | 7 => 0x144e
  | 8 => 0x3cd
  | 9 => 0x3ce
  | 10 => 0x15cd
  | 11 => 0x15ce
  | 12 => 0x170d
  | 13 => 0x198d
  | 14 => 0x14d
  | 15 => 0x19cd
  | 16 => 0x2cd
  | 17 => 0x1a0d
  | 18 => 0x44d
  | 19 => 0x1a4d
  | 20 => 0x10e
  | 21 => 0x180e
  | 22 => 0x28e
  | 23 => 0x184e
  | 24 => 0x40e
  | 25 => 0x188e
  | 26 => 0x5cd
  | 27 => 0x58e
  | 28 => 0x18ce
  | 29 => 0x143d5
  | 30 => 0x1983d5
  | 31 => 0x2c3d5
  | 32 => 0x19c3d5
  | 33 => 0x2c155
  | 34 => 0x28116
  | 35 => 0x142d5
  | 36 => 0x44155
  | 37 => 0x40116
  | 38 => 0x14455
  | 39 => 0x5c155
  | 40 => 0x58116
  | 41 => 0x145d5
  | 42 => 0x442d5
  | 43 => 0x40296
  | 44 => 0x2c455
  | 45 => 0x5c2d5
  | 46 => 0x2c5d5
  | 47 => 0x2c143dd
  | 48 => 0x10416
  | 49 => 0x28416
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 64
  | 6 => 1179
  | 5 => 1391
  | 4 => 225
  | 3 => 23
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (i*15) 6
  | 7 => packedAt gbK7 (i*26) 17
  | 6 => packedAt gbK6 (i*37) 28
  | 5 => packedAt gbK5 (i*48) 39
  | 4 => packedAt gbK4 (i*59) 50
  | 3 => packedAt gbK3 (i*70) 61
  | _ => 0
def gbH (k i : Nat) : Nat :=
  match k with
  | 8 => gbHint (packedAt gbK8 (i*15+6) 9)
  | 7 => gbHint (packedAt gbK7 (i*26+17) 9)
  | 6 => gbHint (packedAt gbK6 (i*37+28) 9)
  | 5 => gbHint (packedAt gbK5 (i*48+39) 9)
  | 4 => gbHint (packedAt gbK4 (i*59+50) 9)
  | 3 => gbHint (packedAt gbK3 (i*70+61) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (16+((h/1+packedAt gbK8 (15+(h % 1)*1) 1) % 2)*1) 1
  | 7 => packedAt gbK7 (1811+((h/21+packedAt gbK7 (1664+(h % 21)*7) 7) % 84)*7) 7
  | 6 => packedAt gbK6 (48339+((h/393+packedAt gbK6 (43623+(h % 393)*12) 12) % 2754)*12) 12
  | 5 => packedAt gbK5 (71861+((h/463+packedAt gbK5 (66768+(h % 463)*11) 11) % 1670)*12) 12
  | 4 => packedAt gbK4 (13950+((h/75+packedAt gbK4 (13275+(h % 75)*9) 9) % 298)*9) 9
  | 3 => packedAt gbK3 (1652+((h/7+packedAt gbK3 (1610+(h % 7)*6) 6) % 36)*6) 6
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffffffffff801fffffffffffc7ff0fffc3fff
  | 1 => 0x7ffffffffffe00ffff800fff9c7f0fffc7c7
  | 2 => 0xff803fc007ffffff007ffff003e79ff1c7f8f8
  | 3 => 0xffffc00007ffffffff80000003f81ffe07ff00
  | 4 => 0x7ffffffffffffffffffe00007ffff
  | 5 => 0xfffffffff80000000000000003fffffff80000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x4da6c6d56938109b4d8db4d53429b076dc1b5b
  | 1 => 0x44b6b6a72db360896d6824ab994570b6dc5c5
  | 2 => 0x9682338324ed5b2d04675ae092c69bb1c6e8e8
  | 3 => 0xe773820c47769dcee7040c8323781dde077f00
  | 4 => 0xc06020300787e1f0f8786f0fc3ff600003b6b6
  | 5 => 0xf87c3c3f80070180c040700c03ffeeedb00000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xe8a8e888e8a80000e8a8e888e8a80000e8a8e888e8a80000e8a8e888e8a80000e8a8e888e8a80000e8a8e888e8a80000e8a8e888e8a80000e8a8e888e8a80000, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_15211
namespace PEqualNP.Outside.L_meta_15211
open PEqualNP.Outside.L_meta_15211.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 1 := bs0_3_0
theorem alls0 : ∀ k ≤ 3, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 1 := bs1_3_0
theorem alls1 : ∀ k ≤ 3, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
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
theorem bs4_2_0 : Interval s4Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 3 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 14 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 13 := bs4_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 1 := bs4_5_0
theorem alls4 : ∀ k ≤ 5, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 9 := bs5_3_0
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
theorem bgb_3_0 : Interval gbAtlas 3 0 23 := block_range (n:=23) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 23 := bgb_3_0
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
theorem bgb_4_224 : Interval gbAtlas 4 224 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 225 := (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 bgb_4_224)))
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
theorem bgb_5_1376 : Interval gbAtlas 5 1376 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1391 := (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 (concat bgb_5_192 bgb_5_224)) (concat bgb_5_256 (concat bgb_5_288 bgb_5_320)))) (concat (concat (concat bgb_5_352 bgb_5_384) (concat bgb_5_416 (concat bgb_5_448 bgb_5_480))) (concat (concat bgb_5_512 (concat bgb_5_544 bgb_5_576)) (concat bgb_5_608 (concat bgb_5_640 bgb_5_672))))) (concat (concat (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 (concat bgb_5_800 bgb_5_832))) (concat (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)) (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)))) (concat (concat (concat bgb_5_1056 bgb_5_1088) (concat bgb_5_1120 (concat bgb_5_1152 bgb_5_1184))) (concat (concat bgb_5_1216 (concat bgb_5_1248 bgb_5_1280)) (concat bgb_5_1312 (concat bgb_5_1344 bgb_5_1376))))))
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
theorem bgb_6_1152 : Interval gbAtlas 6 1152 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1179 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)))) (concat (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)) (concat (concat bgb_6_416 bgb_6_448) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))))) (concat (concat (concat (concat bgb_6_576 bgb_6_608) (concat bgb_6_640 bgb_6_672)) (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 (concat bgb_6_800 bgb_6_832)))) (concat (concat (concat bgb_6_864 bgb_6_896) (concat bgb_6_928 (concat bgb_6_960 bgb_6_992))) (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 (concat bgb_6_1120 bgb_6_1152))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_32 : Interval gbAtlas 7 32 32 := block_range (n:=32) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 64 := (concat bgb_7_0 bgb_7_32)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 4 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 28, 30),(inputs.getD 2 zero, 26, 30),(inputs.getD 3 zero, 22, 30),(inputs.getD 4 zero, 14, 30),(inputs.getD 5 zero, 14, 46)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 20, 21),(inputs.getD 2 zero, 17, 21),(inputs.getD 3 zero, 37, 45),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 13, 45)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 3 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19),(inputs.getD 1 zero, 17, 19),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19),(inputs.getD 1 zero, 17, 19),(inputs.getD 2 zero, 17, 21),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 34, 35),(inputs.getD 1 zero, 33, 35),(inputs.getD 2 zero, 41, 45),(inputs.getD 3 zero, 37, 45),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 6 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19),(inputs.getD 1 zero, 17, 19),(inputs.getD 2 zero, 17, 21),(inputs.getD 3 zero, 22, 30),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19),(inputs.getD 1 zero, 17, 19),(inputs.getD 2 zero, 17, 21),(inputs.getD 3 zero, 22, 30),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xe8a8e888e8a80000e8a8e888e8a80000e8a8e888e8a80000e8a8e888e8a80000e8a8e888e8a80000e8a8e888e8a80000e8a8e888e8a80000e8a8e888e8a80000
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 9 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) (SBf 2) :=
    slice_correct (ms:=fixRows 12 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (3903383688 * 2 ^ 32 + 3903324160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_15211.Model.Repr at out
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

def mono : List Gate := [⟨.or,[3,4]⟩,⟨.or,[4,5]⟩,⟨.and,[0,7]⟩,⟨.and,[2,6]⟩,⟨.and,[1,7]⟩,⟨.and,[3,10]⟩,⟨.and,[9,11]⟩,⟨.or,[9,10]⟩,⟨.and,[8,13]⟩,⟨.or,[12,14]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,15⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 9) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3903383688 * 2 ^ 32 + 3903324160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3903383688 * 2 ^ 32 + 3903324160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_15211

open PEqualNP.Outside.L_meta_15211 in
theorem PEqualNP.Outside.L_meta_15211 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3903383688 * 2 ^ 32 + 3903324160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3903383688 * 2 ^ 32 + 3903324160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
