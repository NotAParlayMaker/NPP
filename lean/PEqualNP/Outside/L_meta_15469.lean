import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_15469.Model
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


end PEqualNP.Outside.L_meta_15469.Model

namespace PEqualNP.Outside.L_meta_15469
open PEqualNP.Outside.L_meta_15469.Model
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

def SBf (j : Nat) : Nat := [3, 4, 3, 5, 7, 6].getD j 0

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

end PEqualNP.Outside.L_meta_15469

namespace PEqualNP.Outside.L_meta_15469
open PEqualNP.Outside.L_meta_15469.Model
def s0K2 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s0K2 (i*4) 4
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s0K2 (5+((h/1+packedAt s0K2 (4+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffffffffffffff
  | 3 => 0xffffffffffffffffffffffffffffdf0ffc1fc7
  | 5 => 0x6ff0ffe0f8
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffff81222d295b
  | 2 => 0xffffffffffffffffffffffffffff82445652ad
  | 3 => 0x24e89b1cc6
  | 5 => 0x188ee398f0
  | _ => 0
def s0Atlas : Atlas := ⟨2,rawDecor 46 s0Pos s0Neg, 0xc0c0c0c0c000c000c0c0c0c0c000c000c0c0c0c0c000c000c0c0c0c0c000c000c0c0c0c0c000c000c0c0c0c0c000c000c0c0c0c0c000c000c0c0c0c0c000c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_15469
namespace PEqualNP.Outside.L_meta_15469
open PEqualNP.Outside.L_meta_15469.Model
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
  | 2 => 0xfff87fe00ffffffffe01fe03fffffff0047ff8
  | 3 => 0xf0fffffff007fc03fffffffc07f007ffff8e3f
  | 4 => 0xfffffffff80003fffffffff80007fffff03f
  | 5 => 0xff007ffffffffffc0001fffffffff80007ffc0
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x2010096152292428a224562c58b568b6a9b6db
  | 2 => 0x442692bb44b26a51451caf02ad5a7551a45b78
  | 3 => 0x8d4224ca6ea4529a69493b560663266b368e2d
  | 4 => 0xee84471388c763639191cd9b340c478dc77036
  | 5 => 0x8f7781c0f078383e1e1f1e3c78f840e07ed80
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xaaa0a0a0aa000000aaa0a0a0aa000000aaa0a0a0aa000000aaa0a0a0aa000000aaa0a0a0aa000000aaa0a0a0aa000000aaa0a0a0aa000000aaa0a0a0aa000000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_15469
namespace PEqualNP.Outside.L_meta_15469
open PEqualNP.Outside.L_meta_15469.Model
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
  | 1 => 0xffffffffffffffffffffffffdfc7fff87ffe3f
  | 3 => 0x6bf878ff8783cc
  | 4 => 0x73ff80fff803f0
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffff8041102888a8d5
  | 1 => 0x20b2245455522a
  | 3 => 0x1517459d461b4c
  | 4 => 0xe2476e66463b0
  | _ => 0
def s2Atlas : Atlas := ⟨2,rawDecor 27 s2Pos s2Neg, 0xaa888888aa888888aa888888aa888888aa888888aa888888aa888888aa888888aa888888aa888888aa888888aa888888aa888888aa888888aa888888aa888888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_15469
namespace PEqualNP.Outside.L_meta_15469
open PEqualNP.Outside.L_meta_15469.Model
def s3K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x20000134006f32bc6570cb6194c32
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x2390a32
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
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
  | 3 => packedAt s3K3 (79+((h/1+packedAt s3K3 (75+(h % 1)*4) 4) % 9)*4) 4
  | 2 => packedAt s3K2 (27+((h/1+packedAt s3K2 (26+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffbfc7fffe3fff1ff
  | 1 => 0xfffffffffffffffffffffffdff8ffffc7ffe3f
  | 2 => 0xebff0f3ff8e0fcc
  | 5 => 0xf3fff03fff00ff0
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffff4070220a092a0d5
  | 1 => 0x20864414425462a
  | 2 => 0x1512e8669086b4c
  | 5 => 0xe248eb92418db0
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 39 s3Pos s3Neg, 0xe8e8e8e888888888e8e8e8e888888888e8e8e8e888888888e8e8e8e888888888e8e8e8e888888888e8e8e8e888888888e8e8e8e888888888e8e8e8e888888888, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_15469
namespace PEqualNP.Outside.L_meta_15469
open PEqualNP.Outside.L_meta_15469.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x600100002a00108003d30006b002e527122d1c791a56275380361c480000052a00506800a3098b00440004200d01400002b505ccb02c889100000f800061780000204993040050402200000c00000ff43fe43de43fd43dd43fc43ff42fe42be42fd42fc42bc42ff32fe32de32fd32fc32dc32ff41fe41fd41fc41ff31fe31de31fd31fc31dc31ff21fe21fd21fc21ff40fe40fd40fc40ff30df30fe30fd30dd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x3286000c4002400000000000000007d5080000004798c00000000000000000000000000000342683124004380000290a1fc840000000000000000006d160380000309e000000005c1e0022930000000000a0002a800004f001ed18882e845365142970d043388006c8a52000d40000074000000000cc1c0f858e80041800e47a3b800001a1e8f9082151000005700200000017840ac000000000000014d400000a78904a3e000040000244002200000000000000000000000c0000d8005c004c000bc0020000001532898a412259250200001ad269c3c89c9c443a8a8406f000000000000007e704a8012e5b458100000000000038001cc3c000000000001400046031919c123c000348e9900000722d1801cb2002f8d476373b1191c9f05000d84148150000009a59047e02800c4004d00000580028c000000000000000000000000000009d00000560b001680000001901000031a40094000007489469b866250c0000501804200100804000302828000501004000b0200c00000080802040180c2600058040000008080000000040a000081c00000080c0201010080400005755243af294875e5190ebaa121dbd4943b6292879f5450f9ea4a1d714943e6292874c5250eb8a2a1d7d4143af298875e53d0abaa7a16790e42cea1c859f5390b38a7214f94a42afa9a855c5350abca6215754c42cf218859d4310b3ca6216754c429f29085ae5210a7ca9994f55332d6216655f548cabaa9195794a32cf214659c428cabca31957542329faa2653c544cb58841957d5032aeaa0655e520cb9ca41973d0832cf210659c420cb9884196310832af288655d500cabca7a0d754f41cea1e835f53506b8a6a0e750d41b7a92836c52506f6a0a0de14141af298835d53106bea918d755231af294639e428c7388518d794631aea84633e540c67aa818d7d5031cf2a0635d540c73aa818c755031af290639e420c7388418d794431eb288635d500c6bca790d754f219f2a4433d54886bca710d754e21d6214433f5448678a890d7d4d21ae29a437b50486f0a090d7d4c21ae29843ac42086bca7a05754f40af29c815d539033a87205b94a40b6a94815e53102baa6206750c409f2a6613d54cc2bea9986795330aeaa6619d54cc23aa9985794b30cf216619c42cc2bca3985754e30afaa2615d544c2b8a4986790930ce212615c514c3b6a0985794c30afa9e415c53c835885904f952209eaa4415e53882baa7104fd51209e2a2415f53482b8a6906b10920bba8a417451482bca6105754c20afa9e215c53c42bca7085754e109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0xa01a242c55280003c0ac002001d0019ab916b802a5e0140074dd117006c01412ccd0a04709360001d8046000004eb40294c301910e0001032018981c7980400ac00d004c020008400000c800000e00003e04341030600005020400006140030020000c3d505250f0f6414943a398b5390a8e6214e42a65805390a1d649463287d91508ca5960d5032a398a420ca4d6510832c3994420cb0d6510832c310a510cb0c4254032a318943d068c6250d41c350c525071943141419398b548c70e5210a3187d91508c62c625503187596540c64c6255031a3189540c70f625503187189540c70c625503183189540c61f659083187594420c61d6494f21c394c428861d6414c2196580530870c5310821a3189439030d4394a40a3189431022c62553309318954cc28c6255330c3d8954cc21c6255330c318954cc20c625533087d9642cc21d6510b3093189544c2546155130c3148424c21d641453087592530c21d6414f20c314c42c830c5310920c9108514821d6494c208759053c421d6494e10
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x68014013100001c4900c0285386c829287425c26510832a10e4a18a0a0c0e72d91508c606bb0a621043425c05310821818e4b20a29840c725925308206392c829e21031c96494e10
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (i*5) 5
  | 5 => packedAt s4K5 (i*16) 16
  | 4 => packedAt s4K4 (i*27) 27
  | 3 => packedAt s4K3 (i*38) 38
  | 2 => packedAt s4K2 (i*49) 49
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (6+((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s4K5 (912+((h/16+packedAt s4K5 (800+(h % 16)*7) 7) % 80)*7) 7
  | 4 => packedAt s4K4 (4950+((h/55+packedAt s4K4 (4455+(h % 55)*9) 9) % 316)*9) 9
  | 3 => packedAt s4K3 (2420+((h/20+packedAt s4K3 (2280+(h % 20)*7) 7) % 96)*7) 7
  | 2 => packedAt s4K2 (502+((h/3+packedAt s4K2 (490+(h % 3)*4) 4) % 15)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf81ffffe07fffff81fffe0ffff03fffe7c7e3f
  | 1 => 0xffe07fffffffffffe07fff03ffffffff8f8fff
  | 2 => 0xffff80fff80fe07fff83fffc1ffc0f01f3f3cc
  | 3 => 0xfffff0007ffffc00001ffff001fc03f0
  | 5 => 0xffffff000000007fffffffffe0000001fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x4a420a2231224a180594a05525219954343615
  | 1 => 0x1089144442449021602949024a4622a88988ea
  | 2 => 0x6145268890e902caaa82729813a88c0d52d34c
  | 3 => 0x459658f12481db7cd34c18d31cf3c831fc03b0
  | 5 => 0x861860e1c70e1c771c739ce380c300c1ef6c00
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xe8e8e8e8c888c888e8e8e8e8c888c888e8e8e8e8c888c888e8e8e8e8c888c888e8e8e8e8c888c888e8e8e8e8c888c888e8e8e8e8c888c888e8e8e8e8c888c888, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_15469
namespace PEqualNP.Outside.L_meta_15469
open PEqualNP.Outside.L_meta_15469.Model
def s5K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xe31288900560000a0418010004be43bc43ef32ec32bf41bd41ee21ec21be40bc40ef20ed20
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0xc49814100a18c430ca38a6a0ce14141a729c431e5390298a6905914520
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 7
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
  | 4 => packedAt s5K4 (212+((h/4+packedAt s5K4 (192+(h % 4)*5) 5) % 17)*5) 5
  | 3 => packedAt s5K3 (197+((h/2+packedAt s5K3 (189+(h % 2)*4) 4) % 9)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfffffffe07fffffe07fffffffe03ffff1ffe3f
  | 1 => 0xe07ffffffffffffff81f01ffffffffffe23fff
  | 2 => 0x7f01fff80fe03fffe001f03ffc1f80fc33cc
  | 3 => 0xff8001fffff0003ffffffe003fffe000ffc3f0
  | 4 => 0xfffffe000000003fffffffffc0000000fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x210914223122450601652a524a212caa0cd615
  | 1 => 0x4a2228c442449818580a40ac94c651546228ea
  | 2 => 0x154c4d6890e90d6eaaa0a93627691e06bc334c
  | 3 => 0x8668b1912481d1b334d3cc0839b38418d743b0
  | 4 => 0x1870c1e1c70e1e3dc71cf1cf01c21860fbbc00
  | _ => 0
def s5Atlas : Atlas := ⟨5,rawDecor 31 s5Pos s5Neg, 0xea88c888ea88c888ea88c888ea88c888ea88c888ea88c888ea88c888ea88c888ea88c888ea88c888ea88c888ea88c888ea88c888ea88c888ea88c888ea88c888, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_15469
namespace PEqualNP.Outside.L_meta_15469
open PEqualNP.Outside.L_meta_15469.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0xe00003c7000001e5800006812000000620000000000360000000006000400007e4e000000004652002a160c00000000200000000000007c0200000026000000000000480800000000347a1828001c6c000072540000560a000080000000322400000000003e0000382c0000000022005e002e661a00306e74001060640014000000000078000000000000008200005c843a4c50004a00427600000000865a4000006a000000000000440102120300000001010000000101000100020100030000ffd5003fe5400ff55003fc54017fd4c01fe53007f54c05fc5300ffd0c03fe43006f90c03fd4300ff10c03bc43017fd4801fe52005f94801fd52017f148017c5200ffd0803fe4200ff50803fc42007fcc801fe32007f4c801fc32017fd4401fe51007f54405fc5100ffd0403bf4100ff90403fd41006f50403fc41007fcc401fe31007f4c401fc31007fc8401fe21007f48401fc21017fd4001fe50007f54005fc5000ffd0003fe40006f90003fd4000ff10003bc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x2a4000df19520014f8ca9002eff6448001dfb224000afd912000dfcc89002efd64480037e322400bef1912000d78c890002ff6348001efb1a4000b7d8d20035fcc690002fd634800d7e31a4000f718d20005b8c690003be4348017de21a400cfbd4920006fca4900037c5248019f62924000db14920005fec290003f761480017bb0a4000bf18520007e8c290002f46148017dfa0a4000ef50520007de4290003ed2148001df202400bef10120007f64090003ee20480017fb284002bf99420005faca1000afc65080117fb204001bf99020045fac810006fc64080017fb184006bf98c20005fac61001afc6308001df2184008ef10c20055fcc4100037e5208001be2904000bf98420005fac210023bf4108001dea084000fb88420007d84210026fe6008001df2004008ef10020007de4010003fa2008001f69004000fe48020005fecb8800afe65c40017eb2e2002bf1971002dfec988006fe64c400bdf3262001af9931002dfac988003bd64c40015eb262001bf19310005fec78801afe63c40017eb1e2006bf18f100077c8788017bc43c40017fb162000bf98b10005fac588002fc62c4001bf2962000df14b1002f7e8388003bd41c4001df2062005ef10310005fecb0800afe65840017eb2c2002bf19610025fec908003bf64840015fb242001bf99210025fac908006fc6484009de3242001af19210005fec70801afe63840017eb1c2006bf18e100077c8708013bc43840017fb142000bf98a10005fac508002fc6284001bf2942000df14a1003dfac308013bf4184001dea0c2000fdc8610007e8430800efe6084001df2042004ef10210007ee2108003fb10840017fb2a2000dfd9510004feca8800afe65440017eb2a2002bf19510006f8ca8800a7c654400f7fb222000efd91100057ec888006fe644400f7eb222001bf1911003f78c888006bc64440017fb1a2000f7d8d10005bec68801afe63440017eb1a2006bf18d10007b8c688002dc6344001df21a2007ef10d10005fec488003ef624400177b122000bf98910005fac488002fc6244001f63122000bb18910006fca4880037c524400fdfa0a2000ef505100077c808801fbc4044001fd8822000fd84110005feca0800afe6504001bf32820029f99410005faca080037d65040013eb282002bf1941001dfec808006fe6404007df3202001af9901001dfac808003bd64040015eb202001bf19010005fec60801afe6304001ef3182000b798c10005fac608003dd63040016eb182006bf18c100077c860800fbc43040017fb102000bf98810007dcc408002ee62040017eb102000fb58810005dac408002fc6204001bf2902000df1481002dfcc20800fbf4104001dea082000fdc8410007e84208012fe6004001df2002003ef10010007ee2008003fa1004001fa8802000fe44010
  | 1 => 0xbbf5190001df28c8000ef5464009778a320003bf3190001df18c8000ef4c640007786320003bf2190001df10c8000ef48640007784320007be60900035f3048001ee982400977ea120003be5090001dea848012ef14240035fecb9800afe65cc00dbf32e60029f99730005facb9801b7d65cc0013eb2e6006bf19730035fec998006fe64cc00ddf3266001af9933008dfac99801bbd64cc0015eb266006bf1933008fbe879801bbe43cc00dde21e6006f710f30037388798002fe62cc0017eb166000df94b30006f8a598002fe61cc0017eb0e6011efd07300077a839801bdf31cc001ee98e6000ef9033008f788198002ff658c0057f32c6000bf59630015f8cb1803eff648c0037f324600fef9923000d7cc91803efd648c001deb246000af5923000df8c918042fd638c001ef29c6000f754e300377c871801bbc438c0017f3146000bf58a30006fca5180037c528c001ef1946000f70ca30005fcc318002fd618c01fdfa0c6000ef50630007bc6318003dc318c00d7f3046000ef9023007f788118003df308c00dfd9846000bfd9530015fcca98002fd654c0057e32a6010bfd91300077ec898002bf644c0037f3226010bf5913000df8c898043bc644c0035e3226010f7d0d300377c869801bbc434c021ee21a6010e710d30005fec498002fc624c001bf2926000df14930005fec298002fc614c021dfa0a6000ef50530007be6298003dd314c001df2026010ef10130037f66098003de304c00d7fb286002bf99430005faca1801afc650c00d7fb206006efd90300357ec818006fe640c01d7eb206006bf1903003778c81801abc640c00d7f3186006f794c30007baa61801bbe430c00dde2186000bf98830005fac4180037e520c001be2906000f78c830037b86418002fe610c0017eb08600eefd04300077a8218003de310c00dee188600fbf980300077c801803bbc400c00def9806006fe8c030007ba601801bf9300c0017fb2e4002bf99720005facb9000afc65c80157fb264001bf993200577cc990006be64c80157eb264000ef593200057ac990006fc64c80017fb1e4006bf98f20005fac79001afc63c8001df21e400aef10f2006fdea5900037e52c8001be296400dfb14b20006d8a590002fe61c80017eb0e400aefd07200077a8390003ef21c8001f690e4000ef90320057788190002ff65880057f32c4000df99620014fccb10002fd6588001beb2c40009f59620015f8cb10026ff64880037f3244009bf5922000df8c910002ff638800d7f31c4000bf58e20035f8c710003be4388013de21c400bbf58a20006fca5100037c52880017f30c4000bf5862004f7e8310003bd4188001f710c4000fb08620045fcc110003be4088013de2044000fbc8220007f64110002ff6548001bfb2a40009fd9520015fcca90002fd65480057e3
  | 2 => 0x31007ba621881bf5310c4017f3006200bf580310df788018802ff65c84057f32e4200bf59721015f8cb90862ff64c84037f3264218bf5932100df8c990802ff63c840d7f31e4200bf58f21035f8c790803be43c8431de21e4200df94b21006f8a590863bf41c8401dea0e4200bf98321005fac190863bc40c84017fb2c4202bf99621006fccb1080a7e65884017eb2c4200df59621004facb1080afc658842d7fb244201bf992210b77cc910806be648842d7eb244200ef592210057ac910806fc64884017fb1c4206bf98e21007bcc710802de63884017eb1c4200f758e21005bac71081afc6388401df21c4216ef10e210cdfac51086bef5288401bf2944200df14a210d7d8a5108036c528842b7f30c4216efd06210077a8310803ef2188401fb90c4200bf98221005fac11085bbc40884017fb2a4200dfd9521004feca9080afe65484017eb2a4202bf19521006f8ca9080a7c65484337fb224201bf991210cdfac890806fc64484017fb1a4206bf98d21005fac69081afc6348401df21a4219ef10d21006fca4908037c5248433dfa0a4200ef50521007ee4290803ee21484017fb024200bf181210cf788090802ff65084057f3284200bf59421015f8ca10856ff64084037f3204215ef9902100d7cc810856fd6408401deb204200af5902100df8c810802ff630840d7f3184200bf58c21035f8c610803be430842bde2184218bf988210bfdea4108037e5208401be2904217fb14821006d8a41085afe610842bdfa084200ef50421007de4210803f62108401f69084200fd48421005fcc010802fd600842bde2004202bf596500a5fec928006fe64940297eb24a001bf19250035fcc728002fd6394005bfa9ca000df54e500077c8728053bc43940017f314a000fb98a50005dcc528002fd6294001f6b14a000bb58a50006fca52800b7c52940017f30ca000bf58650006fca32800b7c5194029dfa0ca000ef50650015fcc12800b7f5094005fda84a002fe142500a778812800aff65540277fb22a000efd91500057ec8a8006fe64540277eb22a001bf1915009f78c8a8006bc64540017fb1aa006bf18d500077c86a804fbc43540017fb12a000bf18950006fca4a800b7c52540017fb0aa000bf18550016fea2a80037d5154027dfa0aa000ef50550015fec0a800bfb5054001bf282a002df14150017f0a0a804fbc4054001dfb2c8012ef996400077acb2004bbc6590001dfb1c8000ef98e400357cc7200039e63900014f31c8000ef58e400073ac720003bc6390025dfa9c8000ef94e400077aa72004bbc5390001dfb148000ef98a400077ac520003bc6290025dfa948000ef94a400067ca520003bd5290025de2948000cf14a400077e6520003be3290001de9948000ef0ca400077ec320003be6190001deb0c8000af5864000778c32004
  | 3 => 0xf3086400bf584321177e8219002fe600c8017eb006422ef10032015facb28886ff64944037f324a221ef9925100d7cc928886fd6494401deb24a200af5925100df8c92881afe63944017eb1ca200ef90e5110f788728802fe62944017eb14a200df94a51016f8a52880afe6194405bfa8ca202fdd4651017e8a328887bf41944017f304a200bf58251016f8a128887bc40944057fb2aa220bfd915100dfcc8a8882fd64544037e322a200bfd8d51035f8c6a880b7f5354401bea9aa200ef90d511077886a8802ff6254401f7b12a200bbd8951005f8c4a8803ec625440176312a200df94951016f8a4a880aff6154405fba8aa200df94551016f8a2a880bf45154441dfa0aa200bfd8151005f8c0a880b7f5054441de202a200efd95410ff7ccaa0803bd655043fde32a8200efd8d410073ec6a0803be6350401deb1a8200ef18d4103578c6a08039c63504014e31a821fefd4d410077ca6a0803bd535043fde29a8200efd89410077cc4a0803bd6250401de312821fefd49410077ca4a08033e5250401dea92821fef1494100678a4a0803bf3250401df1928200ef4c9410077864a0807bf61504035fb0a8201edd85410ff7ea2a0803be5150401dea8a821fef145410077ec0a0803be6050401deb028200ef1814100578c0a087fbf505043fde2828206bfd9731015fccb98802fd65cc40d7e32e6206bfd93310377ec99881abf64cc4037f326621ebf59331035f8c99881bbc64cc40d5e3266206f794f31007baa79881bbe43cc40dde21e6200bf98b31005fac5988037e52cc401be2966200f78cb31037b8659887bbf41cc401dea0e6200bf98331005fac19887bbc40cc4017fb2c6202bf99631005facb1880afc658c4397fb246201bf992310e77cc918806be648c4397eb246200ef592310057ac918806fc648c43b7eb1c621cf7d0e310377c871881bbc438c439ee21c621ce710e31005fcc518802fd628c401bf2946200df14a31035fcc318873bf418c401dea0c6200f7cc631037ee6318802fe608c4017eb04621cef10231005feca9880afe654c4017eb2a6202bf195310edfec898803bf644c4015fb226201bf991310edfac898806fc644c43bde3226201af19131007bca698803dd534c40ddf21a6206ef10d31005fec498802fc624c401bf2926200df14931007bc6498803dc324c43bdfa0a6200ef50531037ee6298803de314c4017fb026200bf181310ef78809881aff650c4057f3286206df99431014fcca18802fd650c40dbeb2862009f59431035f8ca1881aff640c4037f3206206ef9903100d7cc81886efd640c40ddeb206200af59031035f8c81881afe630c437efa186206ef90c3103778861881bdc430c40dce2186200bf98831005fac4188037e520c401be290621cbf984310df7e8218803bd410c40def9886206fd8c4
  | 4 => 0xbec52948017f30ca400bf58652016fea32900b7c5194853dfa0ca400bf98252005fac12900b7f5094805be284a429ef1025214efec9290a77e6494853beb24a429df19252006fec7290037e6394801beb1ca400df18e5214efe87290a77e43948019f21ca429df50e5214ef887290a73c43948053f314a429dfd0a5214efc85290a77d4294853be214a400dfd8652006fcc3290037d6194801be30ca429dfd065214e7e83290a77e4194853bea0ca429df10652006fec1290037e6094801beb04a400df1825214efe81290a77e4094853bea04a429df1025214e78812900aff65548557fb22a401bf99152155fac8a9006fc64548017fb1aa406bf18d520077c86a90abbc43548057fb12a402fbd4952006fca4a900b7c5254805f6292a400bfd8552005f8c2a90abbf41548017fb02a400bf181521577880a900b7f6414805bf320a402cf99052016fac82900b3d6414805be320a402dfd8c52016fcc62900b5e6314805beb18a402d758c52016f8c6290a37f4314851bf218a400cf90c52146fa86290a37c43148519e218a402df9885214cfcc42900b6e6214851bfa10a428df90852146fa84290a37c4214805bfb08a402df98452016fac22900b7c6114851bfa08a428cfd0452146fc82290a37d4114851be208a402dfd8052016fcc02900b7d6014805be300a428dfd0052146fc80290a37d4014851be200a428cf10052035fecb9900afe65cc80dbf32e64029f99732005facb9901b7d65cc8013eb2e6406bf19732035fec999006fe64cc84d7eb266406bf19332037bca799003dd53cc80ddf21e6406ef10f3213fdea5990037e52cc801be2966427fb14b32006d8a599002fe61cc8017eb0e6426efd0732005fcc199002fd60cc84dde2066400bfd9632015fccb19002fd658c8057e32c6424bfd923200dfcc919093be648c8035f3246424bf592320077ac919002bd648c8037e3246425bf58e32127be871901bbe438c80dde21c6424f710e3212738871901afe628c801bf2946400df14a32007be651901bef328c8017f30c6400bf586321277e8319002fe608c8017eb046424ef10232005feca990037f654c8013fb2a6402bf99532005faca9900afc654c801be32a64029f1953212dfec899003bf644c8015fb226401bf9913212dfac899006fc644c84bde3226401af19132007bca699003dd534c80ddf21a6406ef10d32006fca4990037c524c80df79926400f78c932005fec299002fc614c84bdfa0a6400bfd8132005f8c099097bc404c80d7fb286402bf99432005faca1901afc650c80d7fb206401bf99032115fac81901afc640c80d7f3186422f7d0c320377c861901bbc430c80dee2186406e710c32125fcc41908fef520c801bf2906400df1483211fd8a4190036c520c80def9906406fb8c832007ba641901bed320c8017
  | 5 => 0x80300e010000000000080180001a008000010000340000101c000020000000040000100003801000004014008010080000000a01002c0600a00000800800000004008000080000100300c0040600900000c01008004000010010020240081a0020000080100200c0100401a0140080000200c020050060040000600400c0080900004402007000000008040000080000d00c00400007002008000000000000000000200000000000000000020000240000d00a00001004006000000040000000e00200000c0100100600c0401001c0080800200400002000000010008030000000180100003400000002000030050000040000501a00c03800016008000020060180100001c044008050000000100100400402002006010000000080000100200800002801000000030010020000000500a01c01014016010000010000100100000c0180000001200c0780000001000001000000010050080080000000000007800000004000080000300080701803c0000002601000000002000000010000000000000000001801014014020010020100000000200800001002004030010100040100000202803000000004000060120000080004a00000801008000010010000240080001a01c0000100402800008002018050030060000600301000002001004044028000020000200500000403001002024000000060100100100c0140000000600000808015facb2981aff6494c037f324a62dbf59253035f8c92981afe6394c0dbfa9ca602f7d4e53016bea72981bdc5394c5befa1ca606ef10e53037b8872981b9c4394c017f314a600bf58a53016f8a529802fe6194c017eb0ca62defd0653005fcc129802fd6094c5bde204a606bfd9553165fec8a9803bf6454c015fb22a601bf99153165fac8a9806fc6454c59de322a601af19153016fea8a98b37d5454c057fb1aa602f7d4d53036fca6a981b7c5354c05ee29aa62cf7d0d530377886a98b3dc4354c59ce21aa600bfd8953007dec4a9802ef6254c017e312a600fb18953005d8c4a980b7c5254c017fb0aa600bf18553016fea2a98b3bf4154c017fb02a600bf18153016f8a0a98b3bc4054c0ddfb2c8606ef996430377acb2181bbc6590c0ddf31c8606af98e430373cc72181bbf5390c0ddf29c8606ef54e4303778a72181bbf6290c0ddf3148606ef58a4303778c5218afbf5290c57de2948606efd86430377cc32181bbd6190c015eb0c8606ef1864315f7ea3218afbc5190c0ddfb048606ef982430057cc12181bbd6090c0dde304862befd424315f78a12180afd65948537fb24a401bf9925214dfac929006fc6494805bfaa4a429df9525214efaa92900b7c549480d7f31ca400bf58e52016fea7290037e5394801bea9ca402df14e520077c87290a7bc43948057f314a402dfd4a52017dea529
  | 6 => 0x1f949f2b400005515f00000016d0000000000001650a70000000000000000000000000000000002fa2d91360000002eb24c3990000000183462870004632ab1ea2813f600001e00000033d2c545007b00047d3c234149a3c903300b2ad3263b725f1c60003b40000f135f4783b80000e10000140000000004b84193140003ca41100030600009500012f42946b3083892700000000370080001230000003584170000000003311352be00026300014a0000000b300004e0000001dd00029f4692c402a40c3771330000000000003220494b427f0002e640d00001d2383ea3980de34f00442d4ab00000000009916142a13911d0593d61a135919200010d42700000003c00033b0004670000000002883c14bf0002ac32d1fe04a0e62db2360b808525d1ba0003da3c329143915940204c0003660060001e40001fa3a531315b30a00000008002700000e00031d0001270002de0000000ef0000003a73163f43a900000044f2e41b44b626e00004f0700000000000bf1c10001d02a60514b900000007200017721e0000000434211320003d00000002420004330000113df2d401b1e21a22c10fe2f10001420000000003e20ac30700008a1da3ad00000045a22e00034c4b031039737818f27e00000025a0002c31930cb0000460000f300044b48e1704471940000ab0004400631460001d21072a14664950002250001761d400038844d37312401a49646d29d20814d0000002b01ae1a82ea2a214724d0000640000001a62c90000002062a80000000000000003a80ec07e20d34b4230002ec2aa0000900003c500044c0002173f309232400033c0c54240000000910002160710004492f90002cd0000d416800000038a0003d900349e3320000000002cf0003372403de0000000001910000003c74ad3650000000000003bb01f0000000000002d83e11de26618b3a033300009e00000000002e00034202235b0f50000820001a004b37e4530003ac0744831620003560004bd31803634e21a1690004160004511730a20681b80001860000002b10000ce3d732a1db3050000e01982e54a829a2a922019e20919c00000000025c31f43632e0610503bc3041e934a28a2000003ee0003442ee0000003e80004082530000002b947e2c20074650f702847047309b0004430004a400000000000000000000038d0000004030000001992f500010300024a3bf09300000000045719b22b3ce02900013f0003fa37a0001cb3830001570001fd00014101c0001ad0000000000000002543540ee0000002760000003cd1013490000000a323f07c00000000000028e19d0004790001ff0000000000000bb2500000000001312472620342020001842f843c2df3210000040040d001018000000010000140000200801c00800002044118000040000300000000
  | 7 => 0x6e0053450000ad0000da3000000000002e200039e0003194050000000000001850001090004913ec07f3f943d16703045f0670b900048b0af00023100049328500d39515c00000000000000043e0761e60000ff00000000033e2d03393681f300000000000018300000000032c06600036a0000000c73404a14723ed03f24e24100005a0004440000000000004ae28f3db0000000a51660b60000000002ed1ed49b3922a71ef00032324910f3a20002461b531b00043a00000000000017814c18c3642600f60443ba43b0000d00fd00000016a1a348a48848401222d0b03521050001140001b200024f00036c3b00000002dd22100016329b0000000000002d51d64280003f02923850620002484554a50000004892013f10000000001ee2771b74a70002840000000c20000000000000000000000000000310000004603633b93ab3620000000002f62960004871ac0003121f20390000003d83290001c744e32810b3ef11123d1f40000000001380004260000000000000004093f500041e0000000000000000001800a12c708c00000000033505e0000000000000000000000870000000002bb00039b00036b15d0000000000e30351bd22700025b1a900001500000000036d4760f02cc41200008930c1102e74a61d90db14446230e47727a4741c20002e91ca30121d1b938446c2453d14412b21584801eb3eb32f00f31a4351df30321444605206c34d0830003f800017d0001cd3c613b3b541d28008611f44839037000000025228d3601dc00014800000019641400000000000000000000000000010a00007329c00026d0000fb00000026a00013e0b53dc00000047c0000002a40000002233a422a00024422800000007a2510eb49c00c40000024b1041d506b47f00038f00000041809420f40100000000000000000018d20b41c40600000000000019533812c4bc0000000c600035e00000000000000010210e4970cd2cb2fe00017907d43f39f0002a31003362bd39d0000000e22591202f331e1c90e42293873204ac3512372673fb2d33910003fd00009c00043206a0000004451f80000a020e3fe0812554940000000000001b000000000000047112d0000c00002b34543021161ec2f72560560412e014b3252dc2d100000000040445c2e100014f0972fd41b00021803a45200000046402b00018837b2433551bc3b328300000016e0cc0001822ca2c849913416400000939300037f0000002570b13343481cf0000002fc1af0000000002731b300000020c2ef0000003751901c41aa41334705d0c10002110404593e70bc0530001750001bb0000450000000fa41a0000002262902b80000000000000983f229e00030f00022f0000000000420000000001a70653c41120001b60001fc2070e80f23301cc0001f70003b146f084000000
  | 8 => 0x4b22c036748f16f45627200138204729823b0be00011312a4af3b223e15639600019a4b31970002743501220002780000000004100000000000b70002ba02d12847b0b242b30913d3be4984820003cc2580600253aa03d0002a53c000018700000000000000000000009f33a2d71530001d10000002790a90000000000004850004860cf00000030b0001e100000029321900000036f00005c0002653e445b25e3e30002030003e52120ea3614b71fb0f83c81c831704d1c042510c00000014938646800009a0963cb4aa0000002fb2f00004904a329519f22c0190002f212b14500000a0000000000a844240e00000027b0000d937d2bc0000000003ae0d300015100000000000000012e0003d332b17f0d500000031c0bd26400028c27526f1810691d30dd3533e90d227102042005700227c0001724613f736e11b1520ed2ce0000000000001d800046a4383a147a1bf03213028b00040f2d205418a2b63a300026b0881ce2bf11a1f10003740791be34300000016b23348c1e823511c2ff1f637621300000002139429915e00000009d40b4b10002da12117c0230001600a440a01300045832700006e29417e42c0000002d600030d2390483a63d51b118e20a0a62820df41f2240004750d13cf08b00048d0000000000c83dd0001f51ab0fc0000000000000000000000003bd00000037200000000003e26845e3e026100049d1e70d70000000000ba0002ae3710004310e538c21b0000e900000000000044a0000003791060003ff00014000035d42f00016c05b0f93b64b52f400017b45d06f08d4303d44222101430ae0c300012600000000017a08e00001723408f0aa1a40000000f400000021c2b700000000002f0002b53150000000000004a900000000000000000000038e27d1180c40000000000ca00031100042e4150000000001e50004bb00017100000000000000026c00014e11e00000000011700000000000000001003b12538b3af0581d735a11900001600000007500035c2300000dc0001291894810d60771374921c302c2af2321c51740003e64ba40713a05f00000023c2972c61151e00240c90001a53690002e30002a000000013c00039a0260b433f2694a04be0384340e73d238037c3fc35721f00000015a4a21540003811502860000781f04370000000000001552e800000022200000000000000000020528906d00023a1082042150000000d80000000000001e300039c4
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc40189100047e76949100047c76949100063f649491014e3c64949100065f63949100065c63949100066f62949100066c62949100047e76149100147c76149100063f64149101463c64149100065f63149100065c63149100066f62149100066c621491000cbc76505100063f65505100fe3c65505100059c73505100069f63505100069c6350510006af6250510006ac6250510005b8705051002cbe76901100063f65901100963c65901100059e73901100069f63901100069c6390110006af6290110006ac6290110006e4628411000cbe74d9410004bd74d9410034de73d9410004dd73d9410004ee72d9410004ed72d94100047d76994100063e64994100147f76594100063e64594100063c43594100047c72594100063f41594100063c405941000cbf76590100063e65590100063d6559010034bc735901000cbf715901000cbd715901001cbc70590100147e75d8c100047d75d8c1000cbe74d8c10004bd74d8c10004ee72d8c10004ed72d8c10004dd7698c100065e6598c100065d6598c100069e6498c100069d6498c100369f7498c100369c7498c100069f4198c100069c4098c10004bf7458c1000cbc7458c100069c4358c10034df7658c100065e6558c100065d6558c100069e6458c100069d6458c100069f7458c100069c7458c100069f4158c100069c4058c10034bf7690c10004bd7690c1015e3e6590c100063d6590c100369e6390c100069d6390c100147e75d88100047d75d881000cbe74d8810004bd74d8810034de73d8810004dd73d8810004ed76988100066e65988100066d6598810006ae6498810006ad6498810006ce6398810006cd63988100066f75988100066c7598810006ae4398810006ac4398810006af4198810006ac40988100047f75588100147c75588100066e65588100066d6558810006ae6458810006ad6458810006ce6358810006cd63588100066f75588100066c7558810006ae4358810006ac4358810006e47158810006af4158810006ac40588100147e75188100047d751881000cbe7418810004bd7418810034de7318810004dd7318810004ee72188100047f76948100047d769481014e3e64948100063d64948100065e63948100065d63948100066e62948100066d62948100147f76148100047d76148101463e64148100063d64148100065e63148100065d63148100066e62148100066d621481002cbf76504100fe3e65504100063d65504100059c73504100069e63504100069d6350410006ae6250410006ad6250410006e562c8410004f57608410007645208410024bf769001000cbd76900100963e65900100063d65900100059e73900100069e63900100069d6390010006ae6290010006ad6290010005b57190010034f97684010004f77644010005e47244010004fb7644010
  | 1 => 0x9710004bd74d9710004ef7259710004ec725971000cbf76593100059c73593100069f7359310034bc73593100069c73593100349c735931000cbe74d8f10004bd74d8f100069c43d8f10004bf7458f1000cbc7458f10034bf7690f10004bd7690f100147e75d8b100047d75d8b1000cbe74d8b10004bd74d8b10034de73d8b10004dd73d8b100047f7558b100147c7558b1000cbe7418b10004bd7418b1014e3e6494b100063d6494b101463e6414b100063d6414b100066f6214b100066c6214b1001cbf76507100059c735071003cbd76903100059e7390310004ee72d9610004ed72d9610004bf745961000cbc74596100059e73d9210034be73d92100069e73d92100349e73d92100069d73d9210006b571d9210006ba70d921000cbe74d8e10004bd74d8e10004bf7458e1000cbc7458e100069c4358e10004be7690e10034bc7690e100147e75d8a100047d75d8a1000cbe7498a10004bd7498a100047f7558a100147c7558a10004bf7458a1000cbc7458a10004df7358a10034dc7358a100063f6494a1014e3c6494a100063f6414a101463c6414a100066e6214a100066d6214a100059c7350610005b8705061000764520861000cbe76902100059e7390210005b571902100147e76d95100063c64d95100063c43d95100047e72d95100063f41d95100063c40d9510004bf745951000cbc7459510004df7359510034dc7359510004ef7259510004ec72595100047e76195100063c641951000cbe76d91100063f65d91100063c65d9110034be73d911003cbd71d911000cbe70d911000cbc70d911000cbe74d8d10004bd74d8d100069c43d8d10034de76d8d100065f65d8d100065c65d8d100069f64d8d100069c64d8d100069e74d8d100069d74d8d100069f41d8d100069c40d8d100047f7558d100147c7558d10004bf7458d1000cbc7458d10004ef7258d10004ec7258d10004de7618d100065f6518d100065c6518d100069f6418d100069c6418d100369f7418d100369c7418d100069f4118d100069c4018d10004be7690d10034bc7690d100063f6590d1015e3c6590d100069f6390d100369c6390d100147e75d89100047d75d89100066f65d89100066c65d8910006af64d8910006ac64d8910006cf63d8910006cc63d89100066e75d89100066d75d8910006ae43d8910006ac43d8910006af41d8910006ac40d89100147e75989100047d759891000cbe7498910004bd7498910034de7398910004dd7398910004ee72989100047f75589100147c7558910004bf745891000cbc7458910004df7358910034dc7358910004f77158910004ee76189100066f65189100066c6518910006af6418910006ac6418910006cf6318910006cc63189100066f75189100066c7518910006ae4318910006ac4318910006af4118910006a
  | 2 => 0x6e6e65c8220064ed72d95200666f52d95200147e76d95200063c64d95200063c43d95200147e72d95200666e72d95200066d72d95200147c72d95200063f41d95200063c40d9520004bf745952000cbc7459520004df7359520034dc7359520004f77159520004f471595200047e76195200063c641952000cbe76d91200063f65d91200063c65d9120034be73d9120004bd71d912000cbe74d8d20004bd74d8d200069c43d8d20034de76d8d200065f65d8d200065c65d8d200069f64d8d200069c64d8d200069e74d8d200069d74d8d200069f41d8d200069c40d8d200047f7558d200147c7558d20004bf7458d2000cbc7458d20004f77158d20004f47158d20004de7618d200065f6518d200065c6518d200069f6418d200069c6418d200369f7418d200369c7418d20006cf5218d20006cc5218d200069f4118d200069c4018d20004be7690d20034bc7690d200063f6590d2015e3c6590d200069f6390d200369c6390d200047e76949200063f649492014e3c64949200065f63949200065c63949200656e72949200047e76149200063f64149201463c64149200065f63149200065c63149200056e76149200666e76149200672e74149200672d74149200072f64149201772c64149200674e73149200674d73149200074f631492017e6e631492017e6c63149200074c63149200064c63149200072e43149201772c43149201772f41149201772c401492000cbc74d8520006b741d85200067765d85200067465d8520006b764d8520006b464d8520006d763d8520006d463d85200076452d8520006b774d8520006b474d8520006b643d8520006b443d85200067652d85200067452d8520006b440d852000cbe7418520004bd74185200066c5218520006b74118520006776518520006746518520006b76418520006b46418520006d76318520006d46318520007645218520006b67418520006b57418520006b64318520006b44318520006e75218520006765218520006745218520006e45218520006645218520006b44018520004be7650520004bc76505200063f65505200fe3c65505200059c73505200069f63505200069c63505200072c5250520006b76150520006b46150520004ee76c8520006e461c85200656c7548520006e46148520054be76901200063f65901200963c65901200059e73901200069f63901200069c63901200072c5290120006b76190120006b461901200076852c81200656e7588120006e4618812006cee72d942000cbe74d8c20004bd74d8c20004bf7458c2000cbc7458c200069c4358c2006e6e621482000cbe7498420004bd74984200047f75584200147c75584200059c7350420005b87050420004ed76884200059e7390020004ef7648020005e47148020004fb76480200076a524802000cbe74d
  | 3 => 0xe6214a300066d6214a301269e648ca301169e640ca300074c520ca3000cbe7498630004bd749863000cbe7458630004bf7650630004bd76506300359c73506300e69e648c6300055d750c6300de9e640c630034bd76902300359e73902300055d75cc23008e9e64cc2300069c43d9530004bf745953000cbc74595300069c4359530004ef7259530004ec7259530004f77159530004f4715953000cbe76d91300359e73d9130034be73d91300869e73d91300869d73d9130034bc73d9130004bd71d91300147e75d89300047d75d89300069c43189300063f649493014e3c649493019f1c43949300063f64149301463c64149301971c43149300066f62149300066c621493000cbc74d85300147e75185300047d751853000cbe7418530004bd74185300069c4318530004be7650530004bc76505300359c7350530004de76cc5300359c74cc5300859c744c530006d4614c530005d8704c53008cbe76901300359e73901300859e748c130004bf745943000cbc74594300369c6454c30005cc7254c3000cbe7498830004bd74988300047f75588300147c7558830004bf745883000cbc745883018e3f649483018e3c649483017e3f641483017e3c64148300066e62148300066d621483017f4c32148300369c648c83000cbe7498430004bd7498430004bf745843000cbc7458430034bc76504300359c7350430006b66150430006b56150430004dd768c4300369c648c430034be7690030034bc76900300359e7390030004df764c0300369c644c03000cbe74d9720004bd74d972000cbf76593200059c73593200069f7359320034bc73593200069c73593200349c7359320004bf715932000cbe74d8f20004bd74d8f200069c43d8f20004bf7458f2000cbc7458f20034bf7690f20004bd7690f2014e3e6494b200063d6494b201463e6414b200063d6414b2006e6e7614b2006e6d7614b2006f2e7414b2006f2d7414b201872e6414b200072d6414b2006f4e7314b2006f4d7314b2017e6e6314b2017e6c6314b200072e4314b201872c4314b201872f4114b2006f6a7014b2006f697014b201872c4014b200147e75987200047d759872000cbe7498720004bd7498720034de7398720004dd73987200066c529872000cbe7458720004bf7650720004bd76507200059c73507200072c5250720005b8705072006d6c754872005cbd76903200059e73903200072c52903200047d76996200147f76596200063c43596200063f41596200063c40596200147e75d8e200047d75d8e2000cbe74d8e20004bd74d8e20004bf7458e2000cbc7458e200069c4358e2015e3e6590e200063d6590e2000cbe7498620004bd74986200fe3e65506200063d65506200059c73506200d66e65886200be6e65086200963e65902200063d65902200059e7390220
  | 4 => 0x8a400053f7558a400953c7558a400069e6358a400059e7318a400059d7318a400069e6318a4004dba7018a400069e6394a4018e3e6394a400071e6394a400061e6394a400071d6394a401453e7294a4014e3e6094a4014f3a6094a400069e6354a400963e7614a400963d7614a400971e7314a400971d7314a4017e3e6314a400071e6314a400061e6314a400071d6314a4014d3e7214a400972e7214a400072e6214a400072d6214a401463e6014a401473a6014a400953e75cca400053d75cca400369e63cca400072c52cca40004be768ca40004bd768ca400369e638ca40004bf764ca40004bc764ca400053f754ca400953c754ca400369e634ca400369e630ca400072c520ca400059e73d86400059d73d86400069e63d86400069d63d864001dba70d86400069e63986400069e63586400069d6358640034bc73586400063e52586400063c52586400953e75186400053d75186400059e73186400059d73186400069e6318640005ae7218640005ad7218640025ba7018640004be7694640004bd76946400069e63946400069e6354640005af7254640005ac7254640034bf76cc6400369e63cc640004be768c640004bd768c6400369e638c640004bf764c640004bc764c6400369e634c640004be760c640004bd760c6400953e750c6400053d750c6400369e630c6400069e63c8640004be7688640004bd76886400953e75886400053d75886400059e73886400059d73886400069e63886400072c52886400053f75486400953c75486400069e6348640004be7608640004bd76086400069e63086400072c52086400069e6394240005ae7294240005ad72942400973b50942401a4bf76542400069e63542400369c4359730004ef7259730004ec72597300065f43597300363e43597300363c43597300365c43597300361c43597300066f72597300047c72597300066c72597300046c72597300063f41597300365f31597300063c40597300365c305973008e9f7359330034bc73593300369c73593300349c7359330004bf71593300369c4398b300047f7558b300147c7558b300047f7694b300047d7694b3014e3e6494b300063d6494b3018f1c4394b300147f7614b300047d7614b301463e6414b300063d6414b3017f1c4314b3000cbe7498730004bd74987300369c439873000cbe7458730004bf7650730004bd76507300fe3e65507300063d65507300359c73507300065d654c73008d9c744c730084bd76903300963e65903300063d65903300359e739033000cbe74d9630004bd74d9630004ee72d9630004ed72d963000cbf7659230004bf7159230034bc705923016e9e6494e30014df7654e301669e6454e30005cc7254e300047f7558a300147c7558a3014e3e6494a300063d6494a301463e6414a300063d6414a300066
  | 5 => 0xbcec725942100cbf76590210059c73590210069f7359021034bc73590210069c73590210349c7359021004bc705902100cbe74d8c21004bd74d8c210069c43d8c21004bf7458c2100cbc7458c21034bf7690c21004bd7690c2114e3e64948210063d64948210bd6e72948211463e64148210063d64148210be6e76148210be6d76148210bf2e74148210bf2d74148211bf2e64148210072d64148210bf4e73148210bf4d731482117e6e631482117e6c63148210072e43148211bf2c43148210bf6671148210bf6571148210d66e61148211bf2f41148211bf2c40148210b4bf76504210059c73504210072c5250421007645288421004ef76484210bd6c7548421004f7764842100766524842100cbc74980210047f75580210147c7558021004bf745802100cbc7458021004df7358021034dc73580210066c5258021004bf7458e5000cbc7458e500069c4358e500347f7654e501b71c4354e500056c7254e5000cbe7498a50004bd7498a500066f7598a50006ae7498a50006ad7498a5006e6f5398a500066d5398a50006ae4398a50006ac4398a5006e6c5198a50006af4198a5006e6f5098a50006ac4098a500666c7558a50006ae4358a50006ac4358a50006af4158a50006ac4058a500066e6294a5000cbe7498650004bd74986500066e62946500059c7350650006ae6250650006ad625065000cbe76d91500059e73d9150034be73d91500069e73d91500349e73d91500069d73d91500963c52d9150004bd71d915000cbe74d8d50004bd74d8d50004be7690d50034bc7690d500063f649495014e3c64949500066f62949500066c629495000cbc74d855000cbe7418550004bd7418550034de7318550004dd73185500056c7254550004be7650550004bc76505500059c73505500056e72941500059e73d96400059d73d9640005ae72d9640005ad72d96401adba70d96400963c6559640075ba70d8e400953e7598e400053d7598e400069f6398e400859d7698e400071e7598e400071d7598e400069f6598e400069e6598e400069d6598e400069c6598e4008e9e6098e4008f9a6098e400369f7598e400369e7598e400361e7598e400369d7598e400361d7598e400369c7598e400369f7298e400369e7298e400369d7298e400369c7298e400069f5298e400069c5298e400369f7198e400369e7198e400369d7198e400369c7198e400069f5198e400069c5198e400369e7098e400369c7098e400069f5098e400069c5098e400069f7658e400869e6058e400879a6058e4008d9e7318e400369e6318e4007dba7018e400369e6394e400971f5394e40004bf7654e40004bc7654e400369e6354e40005af7254e40005ac7254e400953e75d8a400053d75d8a400059e73d8a400059d73d8a400069e63d8a40045ba70d8a400069e639
  | 6 => 0xe43594310363c43594310365c43594310361c43594310066f72594310047c72594310066c72594310046c72594310063f41594310365f31594310063c40594310365c30594310de9f7359031034be7359031034bc73590310369c73590310349c7359031004bc70590310369c43988310047f75588310147c75588310047f76948310047d769483114e3e64948310063d649483118f1c43948310147f76148310047d76148311463e64148310063d641483117f1c43148310e4bf76504310fe3e65504310063d65504310359c7350431004df764c4310065d654c4310dd9c744c43100795414c43100cbc7498031004bf745803100cbc74580310369c435803100cbe74d8f21004bd74d8f21004bf7458f2100cbc7458f210069c4358f210059c73507210147e75983210047d7598321004bf745832100cbc745832100cbe74d9621004bd74d9621034de73d9621004dd73d96210047d76996210063e64996210d66f52596210147f76596210063e64596210063c43596210066f72596210d66c72596210063f41596210063c405962100cbf76592210063e65592210063d6559221034bc7359221004bc70592210147e75d8e210047d75d8e2100cbe74d8e21004bd74d8e21004dd7698e210065e6598e210065d6598e210069e6498e210069d6498e210369f7498e210369c7498e21006cf5298e21006cc5298e210069f4198e210069c4098e21004bf7458e2100cbc7458e210069c4358e21034df7658e210065e6558e210065d6558e210069e6458e210069d6458e210069f7458e210069c7458e210069f4158e210069c4058e21034bf7690e21004bd7690e2115e3e6590e210063d6590e210369e6390e210069d6390e2114e3e6494a210063d6494a210065e6394a210065d6394a211463e6414a210063d6414a210065e6314a210065d6314a210056d7614a210d66d7614a210d72e7414a210d72d7414a211c72e6414a210072d6414a210d74e7314a210d74d7314a2117e6e6314a210074e6314a210064e6314a210074d6314a2117e6c6314a210072e4314a211c72c4314a211c72f4114a211c72c4014a210acbf76506210fe3e65506210063d65506210059c73506210069e63506210069d63506210072c52506210076652c862100cbc7498221004bf745822100cbc74582210066c52582210147e76d95210063c43d95210063f41d95210063c40d95210d4ef72595210047e761952100cbe74d8d21004bd74d8d210069c43d8d210047f7558d210147c7558d21004bf7458d2100cbc7458d21004fb7058d21004f87058d210063f6590d2115e3c6590d210047e76949210047e76149210063f65505210fe3c65505210059c73505210d66c658852100cbe74d8121004bd74d8121006b840d8121006b8401812100cbe74d9421004bd74d9421
  | 7 => 0x89410069c63d89410059e73989410059d73989410069c63989410cdb571989410053f75589410fd3c75589410059f73589410059c73589410069c63589410c5b77158941005bb7058941005b870589410069c63189410069c63949410071f639494118e3c63949410071c63949410061c63949411453e729494114e3f619494114f3761949410069c63549410fe3e76149410fe3d76149410ff1e73149410ff1d73149410071f631494117e3c63149410071c63149410061c631494114d3e72149410ff2e72149410072f62149410072c62149411463f61149411473761149410fd3e75cc9410053d75cc9410369c63cc9410072c52cc941005b671cc941005b571cc941004be768c941004bd768c9410369c638c941004bf764c941004bc764c9410053f754c9410fd3c754c9410369c634c9410369c630c9410072c520c9411dcbe76945410069c63945410ff3751945410069c6354541005af7254541005ac72545410069c63d81410059e73981410059d73981410069f63981410069c639814103db571981410053f75581410fd3c75581410059f73581410059c73581410069c6358141005af7258141005ac7258141025b771581410069f63181410069c6318141006b96018141034be73181410063e52181410063c5218141006bb5018141006b85018141004bf745973100cbc74597310369c6454f31005cc7254f3100cbe7498b31004bd7498b310047f7558b310147c7558b31004bf7458b3100cbc7458b3118e3f6494b3118e3c6494b3117e3f6414b3117e3c6414b310066e6214b310066d6214b3117f4c3214b310369c648cb31034bc76507310359c735073100cbe7498331004bd7498331004bf745833100cbc745833100cbe74d9631004bd74d96310069c43d9631004ee72d9631004ed72d96310069c435963100cbf76592310359c73592310e69f73592310e69c7359231004bc70592310069c4398a310047f7558a310147c7558a3114e3e6494a310063d6494a311d71c4394a311463e6414a310063d6414a311cf1c4314a310066e6214a310066d6214a310dcbf76506310359c73506310359c74cc63100cbc74982310047f75582310147c7558231004bf745823100cbc74582310069c4358231004bf745953100cbc7459531004ef7259531004ec7259531004fb7059531004f8705953100cbe76d9131034bd71d9131004be70d913116e9c6494d31014dc7654d311669c6454d31005cc7254d310147e75d89310047d75d89310063f649493114e3c64949310063f64149311463c64149310066f62149310066c62149311269c648c9311169c640c9310074c520c931034bc76505310359c73505310e69c648c53100cbe74d8131004bd74d813100cbc74181310369c4359431004ef7259431004ec72594310065f43594310363
  | 8 => 0x63f41d95320063c40d9532004bf745953200cbc745953213cef72595320047e76195320063c641953217e6f621953200cbe76d91320063f65d91320063c65d9132004bd71d9132004be70d91320165c6594d3216e9c6494d32014dc7654d321669c6454d320047e76949320063f649493214e3c64949320047e76149320063f64149321463c64149321269c648c93200cbc74d853200cbe7418532004bd741853200cbe74d8132004bd74d813200cbc74181320369c435943211cec725943218f1c439483217d6e729483217f1c431483217e6e761483211e6d761483211f2e741483211f2d741483217f4e731483211f4d731483217e6e631483217f4e63148321f74f431483217f2e431483217f2c431483217f4c431483217f0c43148321f72f41148321f72c4014832004df764c8321159c744c83200cbe7498432004bd74984320369c43984320066c5298432004bf745803200cbc74580320369c43580320066c5258032036d8305803200cbf76592510059c73592510069f7359251034bc73592510069c73592510349c73592510fe3c5259251004bc7059251004bf7458e5100cbc7458e51034bf7690e51004bd7690e5114e3e6494a510063d6494a510066e6294a510066d6294a51005757194a5100cbc7498251004bf745825100cbc7458251004df7358251034dc735825100cbe74d8d51004bd74d8d510069c43d8d510347c7654d511ef1c4354d510056c7254d510d66e75d8951006ae43d8951006ac43d8951006af41d8951006ac40d895100cbe7418951004bd74189510066f7518951006ae7418951006ad74189510be6f53189510066d5318951006ae4318951006ac43189510be6c5118951006af41189510be6f5018951006ac40189510066c62949510066c629455100cbe74d8151004bd74d8151006b840d8151006b840181510fe3e65d95410059f73595410059c7359541005af7259541005ac72595411e5b77159541005bb7059541005b870595410e69f61d8d410e79761d8d410dd9e7398d410edb57198d410f5b77158d410fd3e7518d410053d7518d410369e6318d410069d6318d410e59e7618d410069e7618d410071e7518d410071d7518d410069f6518d410069e6518d410069d6518d410069c6518d410de9f6118d410df976118d410369f7518d410369e7518d410361e7518d410369d7518d410361d7518d410369c7518d410369f7218d410369e7218d410369d7218d410369c7218d410069f5218d410069c5218d410369f7118d410369d7118d410069f5118d410069c5118d410369f7018d410369e7018d410369d7018d410369c7018d410069f5018d410069c5018d410369c6394d410ff1f5394d41004bf7654d41004bc7654d410369c6354d41005af7254d41005ac7254d410fd3e75d89410053d75d
  | 9 => 0xc52d9153004bd71d9153004be70d9153006af64d8953006ac64d89530078c43d895313e6e75d895321eae43d895321eac43d8953006af41d8953006ac40d89530069c4318953006af6418953006ac64189530078c431895317e6f751895311e6f54189530066d541895311ecd731895317e6e531895317e6c5318953006cf431895317eae431895317eac4318953006cc43189530068c431895311e6f5118953006af411895311e6c5018953006ac401895300cbc74d855300cbe7418553004bd74185530069c431855300cbe74d8153004bd74d81530069c43d815300cbc7418153034bc7358643036b77158643036b73158643036b43158643004bc7058643034be7398243004bd7198243036ba7098243036bb3098243036b83098243004bf7458e5200cbc7458e520065d6394e5218f1c4394e520056d7294e520347f7654e520053f7454e5214d3c7454e522171c4354e5200cbe7498652004bd7498652034de7398652004dd7398652004bf745825200cbc7458252004df7358252034dc735825214d3e74d8e520053d74d8e520071c43d8e520056e72d8e5217e6e6298e520053f7458e5214d3c7458e520065d6318e5218f1c4318e520056e7218e5218d3e7390e5218f1e7390e5217e3e6290e520053d7190e520053e7090e5214d3e74986520053d74986520055e73986520055d73986520d66e629865214d3e74186520053d741865200675611865214d3e74d82520053d74d82520053f745825214d3c74582520055f73582520055c73582520666e625825200cbe74d8d52004bd74d8d520069c43d8d5200cbe7418552004bd741855200cbe74d8152004bd74d815217d3f7690c5215d3d7690c5217d3e7390c5217f1e7390c5217f1e6390c5215f1d6390c5218e3e6290c5215f2e6290c520053d7190c520053e7090c5213e6f52597320363e43597320363c43597320066f725973213e6c72597320063f41597320063c40597320165e6554f32005cc7254f3213f4c5254f3217d6d7614b3213e6d7614b3213f2e7414b3213f2d7414b3217f4e7314b3213f4d7314b3217f2e4314b3217f2c4314b3220f2f4114b3220f2c4014b3200cbe7498732004bd74987320066c5298732004bf745833200cbc74583320066c525833200cbe74d9632004bd74d96320069c43d96320069c435963200cbf76592320359c73592321269f73592321269c7359232004bf7159232004bc705923214e3e6494a320063d6494a322071c4394a321463e6414a320063d6414a321ff1c4314a320074e52cca320147e75986320047d759863200cbe7498632004bd74986320069c439863200cbe745863200cbc74982320047f75582320147c7558232004bf745823200cbc74582320069c43582320147e76d95320063c64d953218e3e43d953218e3c43d9532
  | 10 => 0x90cc4e00053c00072233a00007c0007e263a7d00000000004f60d0000000000000000d464e8000000000000cec0000000000002c80008b8d0000000000200700200500000000200100000000100100000000100000000200800000100300000000000000300100100300200000300000400000500100000000200501200800000000000300000300000000100100000200200000000000000000100000000000400400100500200100000100100000100000000400000100000000500300000000200000000000100000100000000100000300000500200200000300300400000000600000500300000000100000000300000000400100000600000500100100200300100000100000200600700100200b00000300300000000000300200101200000600100200100100100100700b00300100d00100000000000000000400100000000100100000300200200300000000000000200000300800a00300500300000000100200000800000500000000400400000c00000000000000000200500000100100000600100400100000000200000000100000000000400000000100000200300000000000000300100000200a00000000300200200200000d00100100200600100400000c00000000100000200000300000300100b00900000100200000500100000000000000000100100000400000100100000100300600000e00000000000100000000400300100700200400300100100000000800100000200100b00200000100000000000e00200400100300100000100000100000100200500900200000000000000000300500000200100700000500000100400200100100200000200800200a00000400600200000000100100500100000000000100100000000100100400700000200200000100000a00000100200000100000600200100301100400400100c00000000e00000f00100100200000000000100000100300000000200000100300100000000000000200100000500000600100000a00000100000000000000200300000000100300800000000400000400100300000100200000000300000300000300100000300000000600100300100100000100200000000300000200000100100100000800100000000100100000300000000100700200000000000500000000000000000600000200000500100000000000100000000000600200100000000300000000600100000200100000400100300000000000000100000000000600000000000000000700700000100500100000cbe7498a53004bd7498a53034de7398a530369c4398a5300cbe7498653004bd7498653034de73986530369c4398653004bf745825300cbc7458253034dc73582530369c435825300cbe76d91530359e73d91531669e73d91531669d73d915315e3
  | 11 => 0x9f8c7c00000000000078c0000000000000000000000007aa856b680005140000006f80000008cc7ec000000000932b864b8bc60001cc0006b80006846a60000000000009ca0009342860000dc0000168a2d12000aa60003ac0003265ce4506a800081e0007008a80002b06ae888000a28000000000418d14000d42aa866a6084b07daab0000520000000000000000000c1200081400046a00000000000000065ac5a0002685240006d8bcc00000000022800099c5c66467968f2b48a6450e000000000498000000000000000000000ba227400000000051a000000936434ce4d7409e81a86478054ab5a77c9300000000008a40001341c20000005b65941680000000000000c2000000482a9a000000a6239a86a000a8245400000000012e85e00000000000061200038c06834a80c278a7a0006d23b2000bea7d200057400000000000000092868c89a000082a0c0000000000004560000002148680000007680e45169720003e40004fa7589b071ccce29e230000b3400088e6266720000000000000000000002623bc0000000004e20000000000000007f600074200000000000053e89847c910000000000000bb235cd20b6e000d600000000001a699400000000044a0000003f646600000070605c0009a4bf6d023f47de0000000000000001760000008c87900000000ba000000b664a46de000000aa011232cd3c000000534582000000588000678a4a4ac000518c0c00035200000000001a2f6740578000d260000000000000000000000002a2464032000000a9c0000900005ac000000c58840b7a83e38800000000000000000078286e000000000000d5a510000cc8000000c707ea9520008ec30e2103f23d037a7c43285fc0000000000000002f27d400000000000080e0000000000000000000000008243f0902c00d680000000000000a2af80000000009d60000000000007020000000000000000000003fc0000000000000002f000000093c0006b40002cc000000000138c3c0001be0000004da28000000000000000074a000d300000005f200000000000000000000000060a000000a0a00075000000010017e0001c4afc00043eab20e2816af40ee10e736c6c0000000000002b2000cb440011a9040002e400a926a44000000000000334b4e23600000034c1a86882f4bb0c86000a6837215e00000018c1468040000006000de00000012637cd523701e85bed6463e18200008821e00045e000000000620ba82c0d6a0004f025c000000000730000000000000b900003240000642e2000a6c9b400000000000000000000015c0006e8000000b1aac2000000562b3ed3e1fc542002b60980cf48aa712ce887e44872c01e4e69f611638206c4908481585045b84a6c6400082c3b40000000005e4000cbe0000004529003b000000000000
  | 12 => 0x424014000038ca600094a000d0413c4681f6000000000000000b52d58cea0001d06a085800000014400095a0000001da4febd4000000000000000156d56000392a6a124000000c36462000a80d22000000bf4000884af0000c56000000000000486000aec0005d09707e60003683a6000000c149cc000000000000726606c1a402000000a0e77662a0005eab5494e374436000c8cba400000000000000000000026aa609b6d6e0003fa0000007a6580000000000c4c2ac0008d20000000006fc84c000948a3a0005b4b4a0000000000000000000005fe364322bf20000003180000000007cc00000000049e000a04000000000000000000000000642000a1cb02010000d40000a4e0000000a40000000001a00005e60005486ac7fc000000000c1849cd180002040002c6000ca000005e0004be6e4000c748340008120000000000000000006a402000091400000000000000033c000000c78084000000000bae5ee874000000000502bf800027a56c0423901420000620000002fe1ce02200000066c000000000000c88b980007bc2e0000446360a1017c00080867020c4dc2883ec74ca72aca13e3464c81f00ea0000006f000046c0e8b2840600000000059ab2e4f2a34c5c8fe00000000000024400038e000bd6b4c0000002a820ac240000000000000000e60007660fa2126326bc760a0800016017231e00049a00073a8c27b27ae2020009c81ca9d4ac6bca1b41489980008e2656036128c4a21a00000073e0005f4000000000d28c800000000000000008ee54c96abba0000aaaf20000000000000000000001fa00074800000000019a39e752c9cbaa00000000034e5f800000003400057a000c7295442a54e7840000000000000000000003ba00000037e67c82a0000ce27e00097653000061a39682e000cda8a63502f82ea8bac02000a2c71e9a0000000ab800000000058cb8e000ac87049620001a485a0ac3429aa00004004e9a809c9debb44083f80fcb5c58e0966229748289baa8400001c000c6e000ac01b0000000000744628c4800000067a000bd00007c000000084a6be3061780000004840069c4000000b2c00000e7fe000000aaa00050a000000000000d380000000000000002b40000008dea389ee9ecbb6234000000a1e3ee000000000a96000b94000000098c920000000000005c4b78ca400092a00000000000000000c1ae0003be82616225200000000041eb581e0000000000c8e3c8000922ae256000000000049200000014a0000006980001d200018412a0006c6000000000d34000c229e60000000000000000000009580003a4308000bc8cd68e00000009607c8000d0a0002ce0d24b49a222e1b833000000000000000055009a00055e000a3200098686015a2e618a3c612200000002a00000019c
  | 13 => 0xd5e0000000000000000000000009c0716a209dc00093e0004ce00099000000000000000000032eb2003000000042e4e40001d452e4cc788590000000cf8000000000000000000be46588f4000000404c7ec8a000c0ea5025e5a60008fa00000000000000000000000036c0000000000000009f40000000000000706c08546e0000d702a48440007ee8dcd7200000000074e0009826dc188818000222c9ea52cb80006b687c26e8eab14ba68ac0000c05088926188461f4cb27ac4c2000000d5c5c07dc0005589fa5864aa000170000000a6e15400000000000057e166000000be2000a0268e0008b6000a8a0a014e5e80000000009960000000000002540003de0003a23c200041a91a46e0002905a40000001ba4c065e89c4a8000000000000000000000b466d0004c2a000000a360004969d80000003a8000000000000000ab400000094c5c20000008b45ae32a8d00000000000001de0000460006860002008fc7a20b267ecd00002a60000000260000000000000e00000000008d6000bbe0007f81c800000000078a0000007fa0000000005b0000be80000004308966da0f8d0e0000000440006660000000800000000006160000005060000244fc29c0000000001ac694568250b10570000000832a2a000a6600097a7ba7f000000000000000000000000083c0007be00000039c9083e0000000c9026c000cd80000a8c6098a5f60000000000005e28bc598060386ce0aee000b9600051e73478e624c1e000000000000b6c000978000cae0000000000001ea294d366921c69da3ea282b0c62c3fe30064a00028a4f444eafabf0682000650724b2a0000002a003a000b2679e000000528ade0000000000008302be9f29f09ce95e0c6966540ccc4144eea16d1e43c87224053806eaaec76a765ca2b6762000000a5a000c5e1d802e5f0b6a6520007940008be0009680000006340001b2000000000192c6a0001bc0000d87c6a3ea5c9be944000c3e086bc4ada912000000174b046cc00088a0000124ec000000d16c26000000000c2800000000000000000022070cd2e0a6000bfe000000000000a480000c4000c2000005259e3e27c20540009d0a2664e00006a0000000000000000000000000003945b2000ad00005d697c55600000000000000059c36a0001b6000c0a0000000005dc24200000000007a00000047000000000000000000000000058a000592a926620000007280000000004720006c8ad8378a1879a45a000d4c00098cb846f45aa000c52cdc38a8f800000070e65c3da000000a427e400044c0000000000000ec55400060e000000000000c8223ab380780007e000000000000000000000011e7f2058000000000adc0006d69e24e09e093abc022a000358000000c080fe00027689400000000077800000000099a0000002b80
  | 14 => 0x29800088655c000000000000cc2050000a860006408b200010400000000000000000000072e00095c5ec6ec79829a806cde132000cca57c000000000c96b1623e0000000002dc0000009649240007640000000007744d84c492075a000000000b760002ee0000002380003b6000c16000000d4e00000091c000000000000000332000b92bee000000000000000b7e0006380009a6d441209884f813690e19ea56a74696850a303d494608c31a2d800070863c00000000000062e64cb700002bccd4572af682075412c40ac44cee00000003e72000085c00000048c000714602000000000000000ad6cfc00000000098e810c420002d467400000050c000000000b9e000000b24d54a40876852000000000b82d2c1a2000000000000000376000caa000000000000000c840008007185a8000cd22fc000a980002c40000002160000005a2890bc20006fe000ad22925bcbac000000000a9e0004a0000000000536000610000710aea82256ea2e4329fc000000000546b080006682da00000000033e76a9c275c000676000d2a000000d3a0d6000000b7200011400004a000000000000000b06a14b180000009840000002d0cc4b444a2772b7c73c0000000004745004de92c3e60000003c46f225a000000956000000000000000cb60000001ee000000b0a15200027c24600000000036e000a70000000a1a0b000000000016a6ca0000000000cc0000000005fa00000000097e5ba3aa20803c3666e6130000000000bec23c8c400000087a838c2c000a94992354c660000000b6b500000000008b05c869e07e4160000000000000001e40f600000000000000059602cbbc0000007460002ca000ae670a0000000003ce000a8ccf000055a7f44d0000000320000000654000802000878c3a00000010c870532000c4031200000069cd66018000000000b129fe0000000000000000000000000005767920003844760b400011008a000000786d323e80000727ce61c428d1cba0106b800000004ea00000040c2840000004b6b36ab6000a7c81c000abaa1291e47a3aecbc232ac49ea000a78362000000000000b0e0000000000000000000000000004bcd1a000d0875600000000000090ad1061eb8aae4000000000000000b568f07d684e6360002ec00000056a8c6164be600094034430a00004846000014c0ca410aa4d62c680280008f6ce60005da336c2e7b8d500000006447b083a1f8000000076000008bda00000000018e000000b22000b40000bfc000000c3800000045cb1c0008e400048e0000000000560bec54b3a0da0000000004801020006fa0000000000002d6000000000b1e000000906000000ca20000000000004d40000003040001c0abe3d2a5e000380000bd2094b003b89ac0000002fa000000000000a7e6600009b200099e00077a00
  | 15 => 0x52c73835aaa29186aaa4c0002de2baa2213a3ca5d46801dc0000007708d8bb8cc66c26a22d200034810875e19400044200000028c53a000000630000000000000000000478000000ae80005cc000000000a9000000020e000ce200000096c0002ae16e000b5e6b00002e89c6aac000a88000000b4231c00044016ccba0001aa000000000000566150b3c0d441c24e0000001ec00000000004c69a00000083600000000000000088200080a0003100000000ae0000000000000001e600024c28e000c320003d8000000000bdeb9c76c000000cfa5a0000000a248d4066d4a0000005441408a01960008e800000086cd48a000000000000002640000000003d6256b9a000a54c1000088068ac0400048a00011800051c0008da6c400000000000021800079c000b320000006140000002240000009426ea512cac000ae000024a000bce0000003407b4000000000270000000000000000000000186c305520000005d80000002580000000000000008ca0000007ca000000438000000000000000000356000cf277e9d2000c944443c00000004bac620000007a0000296000000acc71a88c00049400092e000000522564b620000006640006ce7e80002aa4ca0747a4000000b3066e4d296e000000000000000938000be0a4676e00040e2c2b883a0314b646ba206d0c1f20000000000000b80006d44200000f25de0000000004d60008ce000cb00008ae3dcabc000000648000b74000d249e410a0000000009e84884120f4000c1c00000000000000000000000021c0000000000009bc08e000000000000000732000000cf600060c000950000a3c7d80000006f61987a8000000000bd82660000000000000006040000000001800009b800000031600000047e000b8c00011c69000086600000072a0008c0302c9800000000017ac9a1d60bcad400035e000c46426a06862000cc04b23983380000000000000009ae6eec7a00000000089e000bfa0000008421fe190000afeacecfe4225e0000bdc00000022c000000000d6c0004ae00000009230c0009160000001e2000260000584d060000000000000000005d200005aca8000000a8e52a0006e20002263cc0f00000c8000458c34272000000000c066b243a42c2480004c67b6c50a580008e6000526
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xc1c7459531cc00149904b2a639801b079cd659033000516412cb2066000c8e641c9538c07dc1cc8290651800307991750c630004a6412ea18c6000c1e645d7308c00129904bae61180032310c72595300064a218e2b2a6000e0c43188524c0010d904ba8c298003075d443185300054ac088630a600689c831d9414c00d13d07ba2ca180bf231907254c300364a39cc2a0860068b487585410c00d13906ba6cb9001a27a1f735932018d0e41ac9296402fa1c8359052c800161906b20a5900bf139cc52987200344e41aeca0e4000c2f7614941c8001a18e629283900034a148705072017616bb0a52064000d0e7314a40c800d13906ba4c3100030799473506200060eb28e6a0c4000c1e659ce408800183acb39c81100be93a1b631492000707b20c62924000e0c6418c524805f49f0e318a4900029361c631492017f07c20c6292402fe0c8418c5248001c1ce8318a490003835d0631492000707a08c62924000e0c4018c524805fc18c7218a4900039118c52d85200054b41ee9b0a400689c835d06148001c48a5a08c29000299a18521852000713b20a430a4000e24641486148001c8ec6290c2900039118c52185200054a41ae830a4000e26841486148001c4b08290c290003899d0521852000712ba0a430a4000e46831486148001c8b06290c2900038990c521852000712218a430a4000e2452100614800d13d073b2829000227a1873505200060fb28e6a0a4000c1c651cd414800113d0fb1a829001a2721c6350520006163b0a4a0a4000d0c731494148001c18c62928290003251cf61505200064a398c2a0a4000e245218541480018c8ea30a429000307d9673901200060e32ce7202400089d87d8e404800d13f0e31c80900c30b9d8529012000687398a52024000e0c6314a404800192ce7b0c8090003259cc619012000712290c32024000c6675186204800d13906ba4c21001a2720d74d97100344f43ee6b26200689c835d062c406343906b24a5880be8720d6414b1017d2741ec4296200689e83dd1658400d13f0eb9ec90801a2720d7498a1018d0f41ec9294202fa1e83d90528405f49906b10a508002a960443189100044f430e6a0a2000c1f651cd4144001838ca39a828806e27a1f63505100344e438c6a0a2000c8c73d894144001918e631282880030e194705051000654310e0a0a2000c1f659ce4044001838cb39c80880022761f63901100344fc38c72022000c8e73d8a404400191ce63148088002a56044058c10006323a8e2b102000c1e651cd410400183aca39a820801a2721e63504100044e43ac6a082000c8c739894104001918e6b12820800299618520841000632bb0a4108200089d869ce400400183ccb39c80080030759673900100344fc3cc7200201189f8758e400400191ce73148008003239cd6290010
  | 1 => 0x886bb0a4188be1b209761483117d0e41ac82906206c1c73595410c40145904b2a8218803071d1654c43100526412ca988620699487505310c40d13d07ba2c190803839926314a2100706b24c6294422fa4f8798c528840149b0f318a5108bf83e126314a2117f06424c62944200e0e7498c5288401c1ae9318a51080383d066314a2100706204c6294422fa4f8658c528845fc1cc7218a5108030799473506210060eb28e6a0c420689c8798d41884011390eb1a83108df0bdd8525062100686398a4a0c4200e0e63149418840d13d07ba2c11080307d9473505210060e328e6a0a420689c835d3604840d13906ba6ca1081a27a1f735902118d0e41ac9290422fa1c83590520840161906b20a4108e30bdd8525042100686398a4a0842009668794921084018ceed29242108bf131cc525802100686218e4a9ca00689c835d2629400151906ba4c5280038354c4398a500344e41ae930ca000c8c739894194001918e6b1283280c687a0f64949500344f41ceca0aa006c1e635d6639000125904bacc720002c32097598e4000547416cb31c8000a8d82d96639000d13d0e294c7200022761c5298e400344f438a331c800089d87146639000d13d0fa84c7200022761f5098e4021e4731ee4a9c802fc8e631c9539000183ceb31ec520003075d663d8a400060fbacc6b148000c1c7598d629006383d0f31ca5200c70761e6394a400048ec3cc6294802fa1f8798c529005f83d0f318a5200028761e6314a4017e0ec3cc6294800081d8798c529005fc1f05318a5200bf8320a6314a4000707394c62948000e0e639885290001c1cc6b10a52001b0798d75cca4017f07318a59948031c1e63dd5329005fc1cc629065200022761e63186400060f3acc630c8000c1d7598c619000191cc7390c3200032398d72186400344f41ced28c8000c8e63dc9519000191cc6392a32001a27a0c764c6400360f31aea18c800092c825d4319000d13d073b4432000227e1973886400344fc3cc710c800089d8798e219000183ceb31c4320003075d6638864000616bb0a510c8000d0e7314a2190001c1cc6294432000307dd663486400060e3acc690c800689e839d8219000185aec29043200038398c52086400064731ce52848000c8e635ca509005f91886392cb9801a87a13435973021f0621ee4b2e602fc1c431c965cc05fc1886392cb980030ba10725973000616c20e4b2e602fc4e831c965cc00189b06392cb9800313d0c725973017e17218e4b2e602fc2c431c965cc05f89886392cb980bf0310c725973017e27988e4b2e602fc4c301c965cc00d43907a0acb980030b1cb41597300350e41880b2e6000c2c7210165cc06383887bb4a5980c68720d6494b3017e0e21aec296602f86c825d852cc05f43906b20a59801b071cd655073000516412caa0e6000
  | 2 => 0xf08a00000002d20000e2ba103c05889000001ec6c2da4d92c0000000252002f2080050040001004004010000101c050000000001000010040000002010050000000000008050000300001004090040002401000010000602005008000000003c0100004014010000500c0001800000000300100400000020000001810008050040401000000040000203005000070080000405030020000000005014000040000c02000020080400c0001007000000000001006000020140000c080080205401004000345fc1eca218c4a991383d50431895300706aa086312a62fe0e8510c6254c5fc1b0a218c4a98bf83dd4431895317f063a886312a600a8d8110c6254c89c1ea2218c4a9802a3a0043189532270628086312a600a958110c6154c01a1887396c7290c74310e7218e5217e27314e730ca43191c835d0619486323906ba6c1290bf1398873582520344e41ae830aa40689c835d3605485f91ce421ecb19003075d443986320054ac088730c6400c1f7510d608c85fc1886294c2190bf8310c525803217f24180a4b006431a1c835925294401a1886392a6a881a2720d74189510054641ae8312a200e0d5310c625440d13906ba6c0a881b0718d7518d4100496412ea31a8200b0c825d4635040151f04b28c6a0802a32096518d410054dc02ca31a8200a9880594635040d13d0e290c6a08022761c5218d410344f438a231a820089d87144635040d13d0fa80c6a08022761f5018d4121e4631ee4a9a822fc8c631c9535040183cea31ec4a0803075d463d89410060fba8c6b128200c1c7518d6250401930c7b82c4a08032618c705894118e0f438c72928231c1d8718e525040123b0e318a4a08be87e1c631494117e0f438c62928200a1d8718c525045f83b0e318a4a08020761c631494117f07c10c6292822fe0c8218c5250401c1ce4318a4a08038318f621494100706318c42928206c1c635d7325045fc18c629664a081b2518e71cc94100692294e39928231c1c63dd5325045fc18c629064a08032318f725454100646318e4a8a820089e8718d605040183eea31ac0a0803071d463581410064631ee4b028200c8c631c960504014710ab00c0a0802aa20960181410344f41ee8b2e622fc8c641c953cc40191887396cb188038310e6214a3100437416eab046200c1f7510d608c401918c8392a6988fb83190520c93117e46218e4b286206a1e84d0d650c487c1887b92ca188bf0710c725943117f06218e4b286200c2e841c9650c40185b08392ca188bf13a0c725943100626c18e4b286200c4f431c9650c45f85c86392ca188bf0b10c725943117e26218e4b28622fc0c431c9650c45f89e62392ca188bf130c072594310350e41e82b286200c2c72d05650c40d43906202ca188030b1c8405943118e0e21eed2906231a1c83592520c45f83
  | 3 => 0x2e42585259800000244f9d85922c0000043b0400000001169c12400000bea08b18006830a180001991a72930802e8829de9e18a110009db0800008000005aa6c000005a036a38005290cc1980000009d000002f47588eb20fea1adc21800388000026008800360000019a5bb02ac228521d000000938a2001b6790000011e7c0000000000000480009713c0000000112000001f8ce0003ca7a7a10054b2800b609c052f62d8007e84624a48a30002e00c00000bbad4531623a26454000000289f9b47d9b25d000641944b978002aa46000000000c2409109e5c80000000001b800000002ce002fc418004a2ae1c000798da8800000000002f8001e2c01dc00000bb000940005600050000720900000000000001ee0000000000810007f9be6e800548ca9185e608000001c1d2141302c00800000008588c0e232001bc002f078296489540780015800002e200000318c48b83a1395a002de3d2b237a904426e00000002ea8f800000001c878000000000000000ae9aeae000b10d400000000f6000000000090800001d492800a088430908b9a38a9800719a4738c88c258341a868a5e8a99e5b156ab1c0359602c22263082a117a02aa065a927c8982a2a2042a87f0000023c0020c00000001aa00262452cc3e800000003800020000002565c000470009c800000000a9cc1280000000002c284ad0000000005c18800b0000998002a800000000123600000268000000061800392a40024c49800001d21ba1c00000000007a00683a1e2f0008615e662802f800000cc8097c7a9aca28002e90aa69884d094058000017e4e2b4000000627c570f20b826a7000001f4001028e86800206001f80008800000000fcb5800001a604904510ee000003b234672fe1a94e0d00000100000003980000000001c41d9929a9daafa8814000950d24e8002b226000003a8001f03e0025a291462c81a120a600000000003e0c063a94a60001b2680000000000001423717670800b821a00064002b60007a000a0000420c932001842d0004a85aa
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xe5dac4ee928000b4c0354dc01b407000000000246c3943800848b04c00d040020000000003500000003cd081756480002c000010000000040049900000000a8d786287402e0000aa214cc607164d8801e7d48d6400102820020004021c101000c081060400317e0318c825d4635045f80f9261c631494117e032498718c525040140d9718f62149410050365c63188525045fc046314a71cc9410050365c43988528c40140e92dd4435823117d0324e841c9650c45f40c93610725943100503251831c9650c45f40e94d0c725943117e0320c72d05650c45f80c831c8405943117e031cc82595410c40180c74209654c4310060361d7498c528840110d981cc525062117d0325e63149418840101d9819473505210044365c83590520840110d981cc525042117e0398c825d6639005f80f9261e6314a4017e032498798c529000140d9798e6214a400050365e63588529005f80e63209750c640004836626314a219005f40f9798c5288640004076607598d219000120d9898c520864017d0324e841c965cc05f40c93610725973000503251831c965cc05f40e94d0c725973017e0320c72d0565cc05f80c831c8405973017e031cc8259541cc00180c74209654c73017e039cc8259640cc00180e64209750c63000603990825d7308c00140d9710c6214930005032497510c614c00110d9720d6414b20004436607314941c800110d989cc529032000407662651cd418800101d9899673902200060361d7418c5248001604935d05218520006816118314861480012259810c52185200044366073149414805f40c9718c5250520007011cc52185414800110d989cc529012017d03e5c6314a4048001c06731486190120
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x12460050030008be00fa666073149418845f007d3b31318a510c80008816a0935d0521852017c0194ccc0e62928290002405a91cc52185414805f00653331398a520240009016a6731486190120
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x5
  | 2 => 0x6
  | 3 => 0x4d
  | 4 => 0x124d
  | 5 => 0x138d
  | 6 => 0x4
  | 7 => 0x94d
  | 8 => 0x8d
  | 9 => 0x128d
  | 10 => 0x150d
  | 11 => 0x98d
  | 12 => 0x98e
  | 13 => 0x150e
  | 14 => 0xcd
  | 15 => 0x12cd
  | 16 => 0x9cd
  | 17 => 0x168d
  | 18 => 0x130e
  | 19 => 0xa4d
  | 20 => 0x134d
  | 21 => 0x20d
  | 22 => 0x140d
  | 23 => 0x20e
  | 24 => 0x154d
  | 25 => 0xb0d
  | 26 => 0x140e
  | 27 => 0x24d
  | 28 => 0x144d
  | 29 => 0xb4d
  | 30 => 0x16cd
  | 31 => 0xb8e
  | 32 => 0xbcd
  | 33 => 0x14cd
  | 34 => 0x3cd
  | 35 => 0x3ce
  | 36 => 0x15cd
  | 37 => 0xccd
  | 38 => 0x170d
  | 39 => 0x170e
  | 40 => 0x44d
  | 41 => 0x164d
  | 42 => 0xd4d
  | 43 => 0x178e
  | 44 => 0xecd
  | 45 => 0x17cd
  | 46 => 0x44995
  | 47 => 0x44c
  | 48 => 0x45515
  | 49 => 0x164c
  | 50 => 0x449d5
  | 51 => 0x1649d5
  | 52 => 0x198d
  | 53 => 0x14d
  | 54 => 0xed355
  | 55 => 0x44215
  | 56 => 0x45415
  | 57 => 0x45455
  | 58 => 0x165455
  | 59 => 0x2cd
  | 60 => 0x19cd
  | 61 => 0xecbd5
  | 62 => 0x443d5
  | 63 => 0x455d5
  | 64 => 0x1655d5
  | 65 => 0x45715
  | 66 => 0xed655
  | 67 => 0x1a0c
  | 68 => 0x583d6
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 68
  | 6 => 1216
  | 5 => 1723
  | 4 => 390
  | 3 => 60
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
  | 7 => packedAt gbK7 (1944+((h/22+packedAt gbK7 (1768+(h % 22)*8) 8) % 170)*8) 8
  | 6 => packedAt gbK6 (49447+((h/405+packedAt gbK6 (44992+(h % 405)*11) 11) % 1942)*12) 12
  | 5 => packedAt gbK5 (89592+((h/574+packedAt gbK5 (82704+(h % 574)*12) 12) % 3328)*12) 12
  | 4 => packedAt gbK4 (24310+((h/130+packedAt gbK4 (23010+(h % 130)*10) 10) % 622)*10) 10
  | 3 => packedAt gbK3 (4340+((h/20+packedAt gbK3 (4200+(h % 20)*7) 7) % 96)*7) 7
  | 2 => packedAt gbK2 (575+((h/2+packedAt gbK2 (567+(h % 2)*4) 4) % 12)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffffc03fffffffffe00fffffcf8f9f1f1ffe3f
  | 1 => 0x3ffffc07e007ffffffffffff471e3e3e23fff
  | 2 => 0xfc07ffff80007c03fff01f80387e7cfcfc33cc
  | 3 => 0x7ffffffff8003ffffe0003f807f00ffc3f0
  | 4 => 0x7fffffffffffc000000003fff8000fffc00
  | 5 => 0xfff8000000000000000000003fffffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0xb548c0058aca9524a0852caa81868d0d0cd615
  | 1 => 0x29312c054102ac94b1a5155143122626228ea
  | 2 => 0x3805e56a802a4c6275a11e01a85a54b4bc334c
  | 3 => 0x90c679b3677300839ecf84063e807f00d743b0
  | 4 => 0x2307be3c79bc73f0070218183f7f8000fbbc00
  | 5 => 0xc3e0302041c00300180c00603fedfbdb000000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xeae8e8e8ea88c888eae8e8e8ea88c888eae8e8e8ea88c888eae8e8e8ea88c888eae8e8e8ea88c888eae8e8e8ea88c888eae8e8e8ea88c888eae8e8e8ea88c888, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_15469
namespace PEqualNP.Outside.L_meta_15469
open PEqualNP.Outside.L_meta_15469.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 1 := bs0_2_0
theorem alls0 : ∀ k ≤ 2, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
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
theorem bs3_2_0 : Interval s3Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 1 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 5 := bs3_3_0
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
theorem bs4_2_0 : Interval s4Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 10 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_32 : Interval s4Atlas 3 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 60 := (concat bs4_3_0 bs4_3_32)
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
theorem bs4_4_128 : Interval s4Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_160 : Interval s4Atlas 4 160 5 := block_range (n:=5) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 165 := (concat (concat bs4_4_0 (concat bs4_4_32 bs4_4_64)) (concat bs4_4_96 (concat bs4_4_128 bs4_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 50 := (concat bs4_5_0 bs4_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 1 := bs4_6_0
theorem alls4 : ∀ k ≤ 6, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 7 := block_range (n:=7) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 7 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 12 := bs5_4_0
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
theorem bgb_2_0 : Interval gbAtlas 2 0 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 7 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 60 := (concat bgb_3_0 bgb_3_32)
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
theorem bgb_4_384 : Interval gbAtlas 4 384 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 390 := (concat (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat bgb_4_96 (concat bgb_4_128 bgb_4_160))) (concat (concat bgb_4_192 (concat bgb_4_224 bgb_4_256)) (concat (concat bgb_4_288 bgb_4_320) (concat bgb_4_352 bgb_4_384))))
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
theorem bgb_5_1696 : Interval gbAtlas 5 1696 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1723 := (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)))) (concat (concat (concat bgb_5_416 (concat bgb_5_448 bgb_5_480)) (concat (concat bgb_5_512 bgb_5_544) (concat bgb_5_576 bgb_5_608))) (concat (concat bgb_5_640 (concat bgb_5_672 bgb_5_704)) (concat (concat bgb_5_736 bgb_5_768) (concat bgb_5_800 bgb_5_832))))) (concat (concat (concat (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)) (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024))) (concat (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)) (concat (concat bgb_5_1152 bgb_5_1184) (concat bgb_5_1216 bgb_5_1248)))) (concat (concat (concat bgb_5_1280 (concat bgb_5_1312 bgb_5_1344)) (concat (concat bgb_5_1376 bgb_5_1408) (concat bgb_5_1440 bgb_5_1472))) (concat (concat bgb_5_1504 (concat bgb_5_1536 bgb_5_1568)) (concat (concat bgb_5_1600 bgb_5_1632) (concat bgb_5_1664 bgb_5_1696))))))
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
theorem allgb_6 : Interval gbAtlas 6 0 1216 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)))) (concat (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 (concat bgb_6_384 bgb_6_416))) (concat (concat bgb_6_448 bgb_6_480) (concat bgb_6_512 (concat bgb_6_544 bgb_6_576))))) (concat (concat (concat (concat bgb_6_608 bgb_6_640) (concat bgb_6_672 bgb_6_704)) (concat (concat bgb_6_736 bgb_6_768) (concat bgb_6_800 (concat bgb_6_832 bgb_6_864)))) (concat (concat (concat bgb_6_896 bgb_6_928) (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024))) (concat (concat bgb_6_1056 bgb_6_1088) (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_32 : Interval gbAtlas 7 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_64 : Interval gbAtlas 7 64 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 68 := (concat bgb_7_0 (concat bgb_7_32 bgb_7_64))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 3 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 24, 25),(inputs.getD 2 zero, 33, 37),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 3 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 33, 37),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 6 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 9, 25)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeae8e8e8ea88c888eae8e8e8ea88c888eae8e8e8ea88c888eae8e8e8ea88c888eae8e8e8ea88c888eae8e8e8ea88c888eae8e8e8ea88c888eae8e8e8ea88c888
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 9 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 17 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (3941132520 * 2 ^ 32 + 3934832776) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_15469.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,3]⟩,⟨.and,[2,6]⟩,⟨.and,[3,4]⟩,⟨.or,[0,7]⟩,⟨.or,[1,8]⟩,⟨.or,[0,1]⟩,⟨.and,[2,5]⟩,⟨.and,[9,10]⟩,⟨.or,[12,13]⟩,⟨.and,[11,14]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,15⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 9) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941132520 * 2 ^ 32 + 3934832776) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941132520 * 2 ^ 32 + 3934832776) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_15469

open PEqualNP.Outside.L_meta_15469 in
theorem PEqualNP.Outside.L_meta_15469 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941132520 * 2 ^ 32 + 3934832776) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941132520 * 2 ^ 32 + 3934832776) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
