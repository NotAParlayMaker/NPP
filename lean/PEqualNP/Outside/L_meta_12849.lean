import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_12849.Model
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


end PEqualNP.Outside.L_meta_12849.Model

namespace PEqualNP.Outside.L_meta_12849
open PEqualNP.Outside.L_meta_12849.Model
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

end PEqualNP.Outside.L_meta_12849

namespace PEqualNP.Outside.L_meta_12849
open PEqualNP.Outside.L_meta_12849.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x841fe31083fa62107f0c420ff90841fe21083dc42107f48420fe10841ec21082fca0107fd0020ff20041fd40083f880107fcc020ff18041fd30083f860107fc8020f790041fe20083f440107f48020f690041f920083fea9885fd5310ff2a6217e54c43faa9885f55310fe2a6217c54c43fea7885fd4f10ff29e217e53c43faa7885f54f10fe29e217c53c43fe87887f90f10fea1e21fc43c43fea5885fd4b10ff296217e52c43faa5885f54b10fe296217c52c43fe85887f90b10fea1621fc42c43fe65887f8cb10fe99621fc32c43fe83887f90710fea0e21fc41c43fe63887f8c710fe98e21fc31c43fe43887f88710fe90e21fc21c43fe81887f90310fea0621fc40c43fe61887ecc310ff18621fd30c43f861887e0c310ff90621fe20c43fa41887f08310ffaa4217f54843fca9085f95210feaa4217d54843f8a9085f15210ffa9c217f53843fca7085f94e10fea9c217d53843f8a7085f14e10ffa1c21fe43843fa87087f10e10ffa94217f52843fca5085f94a10fea94217d52843f8a5085f14a10ffa1421fe42843fa85087f10a10ff99421fe32843fa65087f0ca10bea8c21ff41843fc83087f50610fe20c21ff31843fc63087f4c610fe18c21ff21843ee43087f88610fe90c21fc21843e843085f94210ffa0421fe40843fa81087f10210ff98421fe30843fa61087f0c210ff90421fe20843fa41087f08210ff88421f710843f621087fd5110bfaa221bf544427ea8887f95110bf2a221fd54442faa8887f15110be2a221bc5444278a8887fd4d10bfa9a21df53442bea6887f94d10bf29a21fd53442faa6887f14d10be29a21dc53442b8a6887fd0d10ff21a21fd43443f886887fd4910bfa9221ef52442dea4887f94910bf29221fd52442faa4887f14910be29221ec52442d8a4887fd0910ff21221fd42443f884887fcc910ff19221fd32443f864887fd0510ff20a21fd41443f882887fcc510ff18a21fd31443f862887fc8510ff10a21fd21443f842887fd0110ff20221fd40443f880887fcc110ff18221fd30443f860887fc8110ff10221fd20443f840887fc4110fd88221fe10443ec20887fd5010bfaa021fe54042fca8087f55010beaa021fc54042f8a8087fd4c10bfa9821fe53042fca6087f54c10bea9821fc53042f8a6087fd0c10ff21821fd43043f886087fd4810bfa9021fe52042fca4087f54810bea9021fc52042f8a4087fd0810ff21021fd42043f884087fcc810ff19021fd32043f864085f94410ffa0821fe41043fa82087f10410ff98821fe31043fa62087f0c410ff90821f721043fc42087f48410fe10821f421042fca0087fd0010ff20021fd40043f880087fcc010fd98021fe30043fa60087f0c010fc18021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0xf404c3fc80987f50130fe20261ff304c3f660987f8c130ef18261ff540c2fea8187f95030bf2a061fd540c2faa8187f15030be2a0617e530c3fe86187f90c30ef21861fd430c3ba86187f10c30ffa9061fe520c2fca4187f54830bea9061fc520c3fe84187f90830fea1061fc420c3fe64187f8c830ef19061fd320c3f86418770c830ffa8861fe510c2fca2187f54430bea8861fc510c3fe82187f90430fea0861fc410c3fe62187f8c430ef18861fd310c3f86218770c430ff90861fe210c3fa42187f08430bf28061ff400c3fc80187f50030fe20061ff300c3be60187f8c030fd18061fd300c3ba60187e4c030ffaa6417f54c83fca9905f95320feaa6417d54c83f8a9905f15320ffa9e417f53c83fca7905f94f20fea9e417d53c83f8a7905f14f20ffa1e41fe43c83fa87907f10f20ffa1641fe42c83dc85907f50b20f6a1641fc42c83fe65907f8cb20fe99641fc32c83fea3907f94720bf28e41fd51c82faa3907f14720ffa0e41fe41c83fa83907f10720ff98e41fe31c83fa63907f0c720ff90e41fe21c83fa43907f08720ffa0641fe40c83fa81907f10320ff98641fe30c83fa61907f0c320ffaa4417f54883fca9105f95220feaa4417d54883f8a9105f15220ffa9c417f53883fca7105f94e20fea9c417d53883f8a7105f14e20ffa1c41fe43883fa87107f10e20bea9441ff42883fc85107f50a20fe21441ff32883fc65107f4ca20fe19441ff51883fca3105f94620fea8c417d51883f8a3107fd0620ff20c41fd41883f883107fcc620ff18c41fd31883f863107fc8620ff10c41ee21883fa43107f08620f610c417e50883fe81107f90220fea0441fc40883fe61107f8c220fe98441fc30883fe41107bc8220fd90441ff54482fea8906fd51209faa241fe54482fca8907f55120beaa241fc54482f8a8906f151209e2a241ff53482fea69077d4d20afa9a41fe53482fca6907f54d20bea9a41fc53482f8a6907714d20ae29a41ff43483fc86907f50d20fe21a41ff42483fc84907b90920fea1241ed42483f884907fcc920ff19241fd32483f864907fd4520bfa8a41f751482eea2907f94520fea8a41fc51482f8a2907d14520ba28a41ff41483fc82907f50520fe20a41ff31483fc62907f4c520fe18a41ff21483fc42907f48520fe10a41ff40483fc80907f50120fe20241ff30483fc60907f4c120fe18241ff20483f640907f88120f710241ff54082fea8107f95020bf2a041be540827ca8107f55020beaa041bd540827aa8107f15020be2a041ff53082fea6107f94c20bf29841fd53082faa6107f14c20be29841ff43083fc86107f50c20fe218417e52083fe84107f90820fea1041fc42083fe64107f8c820fe99041fc32083fea2107f94420bf28841fd51082faa2107f14420ffa0841fe41083fa82107f10420ff98
  | 2 => 0x3fca5205f94a40fea94817d52903f8a5207fd0a40ff21481be42903fa85207f10a40de21481ff32903fc65207f4ca40fe19481ff51903fca3205f94640fea8c817d51903f8a3207fd0640ff20c81be41903fa83207f10640de20c81ff31903fc63207f4c640fe18c81ff21903fc43207f48640fe10c817e50903fe81206fd0240fda0481ff53502fea6a07f94d40fea9a81fc53502f8a6a07fd0d40ff21a81fd43503f886a07fd4940bfa9281fe52503faa4a07f14940be29281ff425037e84a07f90940fea1281bd42503f884a07fcc940ff19281fd32503f864a07fd4540bfa8a81fe51503faa2a07f14540be28a81ff41503fc82a07f50540fe20a81ff31503fc62a07f4c540fe18a81ff21503fc42a07f48540fe10a81ff40503f680a07f90140df202817e54103fea6207f94c40bf29881fd53102faa6207f14c40ffa1881bf43103fc86207f50c40dea1881fc43103fea4207f94840bf29081ee52102dca4207f54840bea9081ed52102daa4207f14840ffa1081fe421037c84207f50840fe21081bc42103fe64207f8c840fe99081fc32103fea2207f94440bf28881fd51102faa2207f14440ffa0881fe411037c82207f50440fe20881bc41103fe62207f8c440fe98881fc31103fe42207f88440fe90881fc21102fca0207fd0040dfa0081fe40103f480207f50040dea0081f940103fea9985fd5330ff2a6617e54cc37ca9984f95330feaa6617d54cc37aa9984f55330fe2a6617c54cc3fe87987f90f30fea1e61fc43cc3fea5987f94b30bf29661fd52cc2faa5987f14b30ffa1661fe42cc3fa85987f10b30ff99661fe32cc3fa65987f0cb30ffa8e61fe51cc2fca3987f54730bea8e61fc51cc3fe83987f90730fea0e61fc41cc3fe63987f8c730fe98e61fc31cc3fe43987f88730fe90e61fc21cc3fe81987f90330fea0661fc40cc3fea9185fd5230ff2a4617e548c3faa9185f55230fe2a4617c548c2faa7187fd0e30ff21c61de438c3fa87187750e30fe21c61ff528c3fca5185f94a30fea94617d528c3f8a5187fd0a30ff21461fd428c3f885187fcca30ff19461de328c3fa65187f0ca30ee19461ff518c3fca3185f94630fea8c617d518c3f8a3187fd0630ff20c61fd418c3f883187fcc630ff18c61de318c3fa63187f0c630ee18c61ff218c3fc43187f48630fe10c617e508c3fe81187f90230fea0461fc408c3fe611877cc230fd98461ff544c2fea8987f95130bf2a261fd544c2faa8987f15130be2a261ff434c3fc86987f50d30fe21a61ff524c2fea4987f94930fea9261fc524c2f8a4987fd0930ff21261fd424c3f884987fcc930ff19261fd324c3f864987fd4530bfa8a61fe514c3faa2987f14530be28a61ff414c3fc82987f50530fe20a61ff314c3fc62987f4c530fe18a61ff214c3fc42987f48530fe10a61f
  | 3 => 0xa818ff55031beaa063bd540c67aa818ff15031be2a0637e530c7fe8618ff90c31fea1863fc430c7fea418ff94831bf29063fd520c6faa418ff14831ffa1063fe420c7fa8418ff10831ff99063fe320c7fa6418ff0c831bf28863ff410c7fc8218ff50431fe20863ff310c7be6218ff8c431fb18863fd310c7ba6218fd4c431ffa8063fe500c6fca018ff54031bea8063fc500c7fea990dfd5321ff2a6437e54c877ca990cf95321feaa6437d54c877aa990cf55321fe2a6437c54c87fea790dfd4f21ff29e437e53c87faa790df54f21fe29e437c53c87fe8790ff90f21fea1e43fc43c87fe8590ff90b21fea1643fc42c87fe6590ff8cb21fe99643fc32c87fe8390ff90721fea0e43fc41c87fe6390ff8c721fe98e43fc31c87fea190ff94321bf28643fd50c86faa190ff14321ffaa4437f54887fca910df95221feaa4437d54887f8a910df15221ffa9c437f53887fca710df94e21fea9c437d53887f8a710df14e21ffa1c43fe43887fa8710ff10e21bea9443ff42887fc8510fb90a21fea1443ed42887f88510ffcca21f799443fe32887fa6510ff0ca21f6194437e51887fe8310ff90621fea0c43fc41887fe6310ff8c621fe98c43fc31887fe4310fbc8621fb90c43ff50887fca110df94221fea84437d50887f8a110ffd5121bfaa243fe54486fca890ff55121beaa243fc54486f8a890ffd4d21bfa9a43fe53486fca690ff54d21bea9a43fc53486f8a690ffd0d21ff21a43fd43487f88690ffd0921ff21243fd42487f88490ffcc921ff19243fd32487f86490ffd0521ff20a43fd41487f88290ffcc521ff18a43fd31487f86290ffc8521fb90a43fe21487dc4290ffd4121bfa8243fe50487faa090ff14121be28243ff54086fea810ff95021bf2a043fd54086faa810ff15021be2a043ff53086fea610ff94c21bf29843fd53086faa610ff14c21be29843ff43087fc8610ff50c21fe218437e52087fe8410ff90821f721043fd42087da8410ff10821ff99043ef32087fc6410ff4c821fe19043ec32086fca210ffd0421ff20843fd41087f88210ffcc421ff18843fd31087f86210ffc8421f790843fe21087ec4210ff48421f690843f521087fea010ff94021bf28043fd50086faa010ff14021ffa9e81fe53d02fca7a07794f40af29e81fd53d02faa7a07754f40aea9e81fc53d03fe87a07f90f40fea1e81fc43d03fea5a07f94b40bf29681fd52d02faa5a07f14b40ffa1681bf42d03fc85a07f50b40dea1681fc42d03fe65a07f8cb40fe99681fc32d03fea3a07f94740bf28e81fd51d02faa3a07f14740ffa0e81fe41d03fa83a07f10740ff98e81fe31d03fa63a07f0c740ff90e81fe21d03fa43a07f08740beaa481ff53903fca7205f94e40fea9c817d53903f8a7207fd0e40dfa1c81fe43903fa87206f50e40fe21c81ff529
  | 4 => 0x7f14432ffa8065fe500cafca0197f54032bea8065fc500cbfea7a0ff94f41bf29e83fd53d06faa7a0ff14f41ffa1e83bf43d07fc87a0ff50f41dea1e83fc43d07fea5a0ff94b41bf29683ee52d06dca5a0ff54b41bea9683ed52d06daa5a0ff14b41ffa1683fe42d07fa85a0ff10b41ff99683fe32d07fa65a0ff0cb41ffa8683fe50d06fca1a0ff54341bea8683fc50d06faa920ffd4e41ff29c837e53907faa720df54e41fe29c83ff43907fc8720ef90e41fea1c83fc43907788720ffd4a41ff294837e52907faa520df54a41fe29483ff429077e8520ff90a41fea1483bd42907f88520ffcca41ff19483fd32907f86520df94641ffa0c83bf41907ee8320ffd4241ff284837e50907faa120df54241fe28483ff53506fea6a0ff94d41fea9a83fc53506f8a6a0ffd0d41dfa1a83fe43507fa86a0ef50d41fe21a83ff52506fea4a0ff94941fea9283fc52506f8a4a0ffd0941ff21283fd42507f884a0ffcc941ff19283fd32507f864a0ffd0541fba0a83fe415077c82a0ffd4141bfa8283fe50507faa0a0ff14141be282837e54107fea620ff94c41bf29883de53106bca620ff54c41bea9883dd53106baa620ff14c41ffa1883fe431077c8620ff50c41fe21883bc43107fea420ff94841bf29083fd52106faa420ff14841ffa1083bf42107fc8420ff50841dea1083fc42107fe6420ff8c841fe99083fc32106fca220ffd0441dfa0883fe41107ec8220ff50441dea0883f541107fea020ff94041bf28083fd50106faa020ff14041ffaa6637f54cc7fca998df95331feaa6637d54cc7f8a998df15331ffa1e63fe43cc7bc8798ff50f31eea1e63fc43cc7fea598ff94b31bf29663fd52cc6faa598ff14b31ffa1663fe42cc7fa8598ff10b31ff99663fe32cc7fa6598ff0cb31ffa0e63fe41cc7fa8398ff10731ffa8663fe50cc6fca198ff54331bea8663fc50cc7fea918dfd5231ff2a4637e548c7faa918df55231fe2a4637c548c6faa718ffd0e31ff21c63fd438c7f88718ffd4a31ff294637e528c7faa518df54a31fe29463ff428c7fc8518ff50a31fe21463ff328c7fc6518ff4ca31fe194637e518c7fe8318ff90631fea0c63fc418c7fe6318f7cc631fb98c63ff508c7fca118df94231fea84637d508c7f8a118ffd5131bfaa263bf544c67ea898ff95131bf2a263fd544c6faa898ff15131be2a263bc544c678a898ffd0d31ff21a63de434c7fa8698f750d31fe21a63ff524c6fea498fbd4931b7a9263fe524c7faa498ff14931be29263ec524c6d8a498ffd0931ff21263fd424c7f88498ffcc931ff19263fd324c7f86498ffd0531ff20a63fd414c7f88298ffcc531fb98a63fe314c7bc6298ffd4131bfa8263fb504c6f6a098ff94131fea8263fc504c6f8a098fe14131bc28263ff540c6fea818ff95031bf2a063be540c67c
  | 5 => 0xa43ff294877e5290ffaa521df54a43fe29487ff5190ffca321df94643fea8c877d5190ff8a321ffd4243ff284877e5090ffaa121df54243fe28487ff4350fbe86a1ff90d43df21a87ff5250efea4a1ff94943fea9287fc5250ef8a4a1ffd4543bfa8a87fe5150ffaa2a1ff14543be28a87ff5050efea0a1ff94143fea8287fc5050ef8a0a1df95043bf29887ff4310f7e8621ff90c43ef21887fd4310f7a8621f750c43ffa9087fe5210efca421ff54843bea9087fc5210ffea221ff94443bf28887fd5110efaa221ff14443ffa8087fe5010efca021ff54043bea8087fc5010ffea7a17f94f42bf29e85fd53d0afaa7a17f14f42ffa1e85bf43d0bfc87a17f50f42dea1e85fc43d0bfea3a17f94742bf28e85fd51d0afaa3a17f14742ffa8685fe50d0afca1a17f54342bea8685fc50d0afaa9217fd4e42ff29c857e5390bfaa7215f54e42fe29c85ff4390bfc87217f50e42fe21c857e5290bfe85216fd0a42f7a1485ff5190bfca3215f94642fea8c857d5190bf8a3217fd4242ff284857e5090bfaa1215f54242fe28485ff5350afea6a17f94d42fea9a85fc5350af8a6a17fd0d42dfa1a85fe4350bfa86a16f50d42fe21a85ff4250bde84a17f90942df21285ff5150afea2a17f94542fea8a85fc5150af8a2a17fd4142bfa8285fe5050bfaa0a17f14142be282857e5410bfea6217f94c42bf29885fd5310afaa6217f14c42ffa1885fe4310bfa86217f10c42bf29085ff4210b7e84217f90842f721085fd4210b7a84217b50842ffa8885fe5110afca2217f54442bea8885fc5110bfea0217f94042bf28085fd5010afaa0217f14042ffaa6657f54ccbfca9995f95332feaa6657d54ccbf8a9995f15332ffa1e65fe43ccbfa87997f10f32ffa1665fe42ccbfa85997f10b32ffa8e65fe51ccafca3997f54732bea8e65fc51ccbfea1997f94332bf28665fd50ccafaa1997f14332ffaa4657f548cbfca9195f95232feaa4657d548cbf8a9195f15232bea9c65ff438cbfc87197f50e32fe21c657e528cbfe85197f90a32fea1465fc428cbfe651977cca32f799465ff518cbfca3195f94632fea8c657d518cbf8a3197fd4232ff284657e508cbfaa1195f54232fe28465ff544cafea8997f95132bf2a265fd544cafaa8997f15132be2a265ff434cbfc86997f50d32fe21a65ff424cbfc84997f50932fe21265ff324cbde64997f8c932ef19265ff514cafea2997f94532fea8a65fc514caf8a2997fd4132bfa8265fe504cbfaa0997f14132be28265ff540cafea8197f95032bf2a065be540ca7ca8197f55032beaa065bd540ca7aa8197f15032be2a0657e530cbfe86197f90c32fea1865fc430cafca4197fd0832ff21065fd420cbf884197fcc832ef99065fe320cbdc64197f4c832ee99065ed320cbfea2197f94432bf28865fd510cafaa219
  | 6 => 0x90522c908d00006de05216e4fa19e914b5a000000d8ce1c00200000100200000000100800000000400400100000100000100100400400400100000601200500000f00500100500000001b01000500500000000101e00300000201e00000000300300000500500600000000300500102800f00f00a00100400100400000700000200c00a00100000f00000c00700100600000100000501100000900000100000000a00000100e05000000300300000000900000100000100200300000301001600107e00000001f02102d00102800101200900200001800900100300500300000100000100301100100100300e01000300100004400200000504200000200200200e00000000500000702b02500000000400c00600000102000900000300e00c00000200800101d00200300000100000100100b00801a00000400300a00600201401501000700400000a00701901100d00300000100300000000000b00401900102200c00601c00000000100500101e00000c01000200300200300100700100000100000200000000000400900a00100600700200000701000800600300000100c00002100100800000900204900600100100200200600000400000100300400100000100300504400001100000001303c00200000b00100400000501600500000800100200002001001800000000401400000600200c00201200200300200300000400f00400300100000100000300300b00100000700000200600000000000100000200800600100000400600300000200000000700000300200a00200000000500a00300001100300000200200400100000200701100600200300000500000001000100000900000500100000100800500000300400a00500000000300000000002400000501100000500100400100000700d00400001000000000101900500600100100400100300200200800000100101d00800000201900200200100f00600200000000c00300900000100200900000200100700b00000000e00000101e00100800000700001000000b00300001700100100700300000000500f00f00300700400100000100300002101800200000800700100500200200600000700200100201701001500100401300201a01400000900203200001800600100000100600300000300000100a00f00100001400100700800b00501c00100200300500200002a01a00001600500200200000400400500000100100b02200000601300000300000f00b00400200101000200e00700b00400100000500000c00500800702400000000100000000f004001005000000ffa9687fe52d0efca5a1ff54b43bea9687fc52d0ffea3a1ff94743bf28e87fd51d0efaa3a1ff14743ffa8687fe50d0efca1a1ff54343bea8687fc50d0efaa921df94e43ffa1c87bf4390fbe8721ffd4
  | 7 => 0xa45cbc01ba6940cacae00000000000000000000a000354000000bb00003204785da000304baa590b1431207e3f60002640006f842a0000009da2d027a0007f2000940138a2a8880000004fed840000000007ee0005ae000000000000e180005c0a52000d70000000d9623200061e000a76474a680407e2b36d2e926bb26b27d27a06029b40ec382c34de277ce3821c0007a804e576de863e00c93e00019a6aa000528000c262d4672d9ac581d40000005ac5182ac5f8b66c2e5fa008620d6c94cd8e41e2860005800007ea0004300001000006fec02ca83c80f6ce698e000734000a3a156000b58a50d540b40007b004c2b8810cbc862cea89405c59ea06bf2c0ea5c814db800094a0e21dabde1249920009c08a4b7e86e52c20c36057e0006b4000db4bce2e4d7643e5d2dbe15c0004d030c000d3800097c0001a8000c10332bd064000042e6b005ed7cb26be097600054e65000074a5440b8c62350a04000a3c9c4a5a7c02c869829acdee5ca9400000051e0e07da8b65c2d0a116724ac6d12b54dac8b2a32a12d6e5404ce1d8a842f091c6922622bc32209eb6e8726fc0223d0e3e6e6506a827304e6dba60ccc21c015a3b41bc8405cc7484766d83acd8a7c46769aac64000d04560e1a5f2cf00ee42013aaca7600c81ca2be000000000366000000a100000005c833e832000000b500000003c4e5e95a260000146000000dd4cd0000000a264484e4882ccab2a1b06dc0d86120002780000002e60ac7520002705ca00002cbac80a8fad8257400075eb86000000000ddce440005f0130000000d880a0000000b0e00089c43800000001000000000041088667a79c178000000cac8ecbf45ee35886c00039e8cee30276000000000bbe0000000002684f82d60020fca983d40a2102000af8dd6b6c8cabd69f49d642481c610cc038e7a6cdc4d8a222ea0006f0aea5861a0aba02e000d9800049c9be0000000004b676c6002dc01c0000007e6c5c000000000c8064844c5ec1f0000664b98ae07b2000710da665ce5a6c0ab600000007c292670d80530000e3417400077a5b8dec0002b6000000bd80040003ccb229e4908812cfc7b800000040e8d67ae6342ae0007580006a29cc24291ed3ca46c420ba9bc3ee9884a2568aa25380000001fc000000000e3a3a0e0e2da8340320009ece203fc00000000064ce48afc36c44235ed5a2c049ab08874a6ac84982080b60588ad00000c0660a8c000000000cee0000007b6e322a80dc190c883b6bb62cc20692047cb709a8000e6600000000017c0000008700000008ee18aba6000e083ae9b8c70b3277200087acd8dc6d68aa4536ae6ab20002305d8dce72e4be680418c7a63c96edd89e8b4e0701e04544b0026364c12596c94b1ec482169281ea54a0eaaf00007383da2200008c877816200051696a0be3
  | 8 => 0x93cafa6360b29ac2f60004ace4043400000000048a000e10e2a0000003160a68d2000000996000238000000000ada444000690ab83920006260006c483cce40009f00007ac1f4bfc0000009fec243ecc7e0000002a41ee000000deabc252a03c5a6b726b8000000000e007f4d52542b9cbc617223aac2ca4e58cb6314d26d920008648f601a2cacc412a0009386668262a0dd046863adc8000000830d6a01e0b602800017ac40d20dfad106a8dc00004c660e000c16e2ea384503020008087408fc0006ca4a05a437ca020007f086ab8218400e7e44cc6d60000000000001c24045bc9105783264f4d08712000b42520d160002ee00039a0001a2582c4e0008e0be20003f213ec18b028ea2587d0e52acc7ecd28000b30000790746de0b4883a3b8c7455a480d1a08c090bb8a420000f8000638b180ae3340000000005ba4a600037600050c000bfa4e00006a400038cbee000000b3404800000000025e26e12678c02a1fe8a6da00d2656c9c6da2d86bcaaccb4b460000000004ca000000c6cbec324000456b9651000040a0008561e40008f4e62056974000ae80e4da87967446fa7fe93ac8e89243261a546168d1e428228b5ca80c98bb43984bc05a4b268acbe5627b4be8a2497a3a66a00003be9541922240006d0d5eaf4532ad880225c3e4340b2462a4949ee00017e58c000d2ca9e0003fa8240000003b0b3c06400023c7280000008c42e8c96000000d46bae30675a336a64118bd200080c2220bc000df600000084e56c346c9224800041c000000236460d068c0000708e0a00000000047a26c98cad40002085e28fed9c33abd4afe8760004d6bc4822b2ec8a06c6ba6d48de0007d47140000000f0912a00ccca3685aa2082e2981ae1ce18cd4855cbc81522c4e24966784408c722ec9dcce8000a1a14ecec0000007567f600062c37e1823740000005140440000008580005e03e8ddec4a050380000d664ee000c228dc92c2a60d442ca7800094e82c38400000094276a4907e809670c48c000b000000001d28e8000000d786e09d8d2ad9400040221a0008ac3ba000594000732788896dfc6966aed0e372396154000d0c51a0000000006880000009b2b10a542801046cc38a000e56a5e000ce01b4c30dee000daac06000000000d6011a9628e6df2000850aa80a800006a00065ac2c6143e2134a2c2fa000000a4e884e60994b94e260001e2194cd4b7a9fa388dc4500ce2686c52776b8096456a606766abe70a4462b2000492be6164c0800059885cd40ae477ea9045e000beacf4c82a087201f23b2b3869ee041c67c607a000a142120000003e000014274ca74b9200000055058a1760004d21660000000002020003f80004e81b6000000000016288000042000c445b0b1c1a680e60a98a1fa6ec7a41367627c24a8d8686869cbe466
  | 9 => 0x26bba25a0c6000618aa619846e46a318584c3a7700d00000008280000000000000000005d071a5a2000148000932dccd440004ec0008802badc2000b12a0c72c000da2d321086be838000000d7e7decb0abc56e8903685b4000000754308d24000678d3e00004ac68768616000000000d5c9f640c6f478e0007a23fe416000cf2076630d56e147228e23d25ce9481c44f20722529c6a489844da27e96c8605b20007d60004980f2ac00da1408aa0000005a00000000000000000009b62e062e000d020000008f2000b740004b4af237867ca6c44aa586ee00000000027243a328cc670478aa8e8a0000000000000a44c60970000436a403d650a5925700000004de0002de000000b520003940003a83560007bccb800099aa92000848000946034b8c90eb7806844e9de00053c50e652d4214a0004aa8981b206e240000a0e34a2feb9e00057abca00000068c030000000866000000000646d4c6629d2000d30d220001329680c471c66cba00002943e6000c36de481ae027ba71e0000008b80000004844e26ac34c1cc5f67ca47053a0920005480000005de2fc2b026aa7200035c75c9a6e4ad0087ea7c5560001be40610e9b000019629611e3ca14c0368204624880000000008bc46664a3ea7cc0c2c0a13c990000800db6000000774caa68e8420002746c24828d400008a08e7c80cec545c4098000000000128ba45dc49e012000c5a552798440e16000000c0c00087c6b6094338d3aa96000cf632ee128041d09804fc972db088c8da36aa2e3c0088000db2944b64046000000000b2881e6eaca6a34cba0cc4f6cd29182c690011200050200015000033c5129ced4a00049688eb56cfe0004c000000031ab0a058370c6a000780e3ce5499800002400000022c78600000008400088a73a000ade0000e6a9a604b7ca28ad6a70956000af6bf6dbc0006e801467ea568c61c80005d68d8000000d6451c21e28ac8c00000020a7029fc0000620000000000002500000000003d8ab4dd246c4c47f8144d1c18e4dc342a663aa6841ec000718000e64018000960c7c36e0aa5be0005a873e000000844000000000000d36000170000e28000dda7009d0c4c3de000e4234e452a0a0009a40000008c20000000000000006085ea5b600055425600035a9f800000000034820e0004d4a7abbcc286c632a10ac3e2ce00000045a46492a000bfeb6a000df0000564aaa76ea1c64274e0002c268219cd72214000c04a8a290000234cc80008364f0000000c5e1aa6222f29a24b87940387aa0005d4b8eca05e83dc5fe9aeb4ab76ac8674106806b62266c1a1d6da4b2c09cbf0d9065e66e5261586ce3c2a4c2aa0785fc0000000000000748a8c1eb0c8ae716c6611c03ecfab200000009367fa0003ceaee458d18902c1c3a40002d22828f091a2443bc000924000
  | 10 => 0xb9ac140fede60006f60000a49049d40668ccca224e84ad7ab4cb40b8831e1ac87895079ee36c3c41423e2b4d58a7e0b01806e433059a89e000000422df8000000aced34d620009f24c2dfeb5e0006c8e22930000a60adc060852122c86b3ec00e2c2046a6d9e352000a1e00073c09a11052eb4482a90a30a9c2e0c12092e658a9ca30188000b680000008ba000c204008b08b400031c99e9ca0001f69e20007dc00003a97e57cb840009785aaac42542186e29344120009ba000c46986e4e0de000c2a00000072a61c6447d800047e0008e41b8d4e504632000cda4ba6d29ea55e8bea1628eccecb224a0005c600034400058e000000750782726000a6e426dca000386000aa0922000b8ab066243a29524ea0001143c60869c80009a083e000aecbcc7921de0007640d6000e4c310e1e486b90ad270653484c4ae05428c00000024600081612c000a8695c1600000003f02e2d500e8c78bda186e06d14b1643c9e65e67366f289a65432c2105f4ae20820001dc00027c000000000000a3eb041a49160008547e0ab0200006300000000284000df400062869abf85721e815e99c2f485e906c509e01f8bdc00090cc9e0008180000008f812e0002a295e5247ce000a620004c850822e5e416c0fa3f4566d7437a020c767be00074279a53ec6e0f4aae70ec32472e46c38e504a439c000a88668cd654c55829e0001e600048e00036264eba800022ab3ab1a59c958c9ac5610c29cdaeba2a1830e7fca4a84624c2f88a216acf841a2
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x131042ef624c410bb18931042fb604c4109fd94310427d650c410af99031042bd640c410d794c310435d530c410be98031042f9600c4109f59721042be64c8410af59321042f565c8410dd59721043b664c8410ed593210437752c8410dd54b21042f560c84109fd96210427d6588410db94a210436d5288410bd98621042fa6088410be582210427f65484109fd94210427d6508410db948210436d5208410f948421042fa6008410be580210437565084109d59421042f66208410f998821043775208410f994821043755208410f954821043e64208410f950821043e73208410f90c821043f26008410bd58021043f160084109f992500427d64940109f98e500427d63940109f98a500427d62940109f58650043772194010dd086500427d65d0010b798f40042dd63d00109fd96400427d6590010cf952400433d5490010bd98640042f561900109fd95400427f65100109f994400427d65100109f194400433e5410010cf55040042ee6210010bb58840042f66110010bd584400427d65cc010af99330042bd64cc010be597300437965cc010ee99330043b964cc010ded4f300437953cc010be587300437a51cc010fcc8730043f021cc0109fd96300427d658c010d794e300435d538c010bd98630042f5618c010be982300427f654c0109fd94300427e650c0109f594300427c650c010d794c300435d530c010bd98430042f5610c010f64c030042f9650c010de5943004279650c010be98c30043da630c010ded4c30043da530c010de54c30043d9530c010f690c30043d9430c010f68c830043d8320c010fc98430042f9610c010fc584300437a510c010f68c430043d8310c010fcc8430043f0210c0109f597200427f65880109f596200436e5288010db54a20042f66188010bd58620043e421880109fd9520042bf6448010af19120042df6348010b718d20042f76148010bd185200427f65080109f994200427d65080109f19420042be6408010af590200436e5208010db54820042f66108010bd58420043e42108010dd59710042f662c4010bd18b10043f330c4010fc0c310042f56184010dd94610042f96584010de59610042796584010be98e10042f86384010be586100437a5184010fc94610043f32184010fc086100427f6544010afd9110042bc6444010b7d8d10042dc6344010bbd8910042ec6244010bdd95100437765440109dd9510043b76444010ed19110043d76344010f518d10043e76244010bd98910042f46244010f918910042e46244010bdd8110043765044010fcd0110043f04044010bed95100437b65440109ed9510043bb6444010ee19110043db6344010be98d10042f86344010f618d10042d86344010fad8910043e86244010bed8510043f36144010de94510043f25144010fcd0510043f04144010
  | 1 => 0x427e60d4c10de983530427d6594c10d7d4e530427e6494c109f592530427e6294c109f58a530427f6454c109f191530435f6354c109fd89530427c6254c109fd85530427d6154c109fd81530427d6054c10de18153042be6414c10af590530435d5314c10bb98853042ed6214c109f990530433e6414c108f990530427d6414c10cf590530423d6414c109f98c530435e6314c109f988530436e6214c109b988530427d6214c10db588530426d6214c109f98453043766114c109f980530437a6014c109fd97430427e65d0c109f597430427c65d0c10cf953430433d54d0c10be98343042f960d0c109fd96430427e6590c109f596430427c6590c10d794e430435d5390c109fd95430427e6550c109f595430427c6550c10cf951430433d5450c10d794d430435d5350c10bdd8543042f46150c10bed8143042f86050c109fd94430427e6510c109f594430427c6510c109f993520427d64d48109f98f520427d63d48109f987520437661d48109f983520437a60d48109f596520436f52948109f992520427d64948109f98e520427d63948109fd91520427c64548109fd8d520427c6354810dbd89520427f61548109f585520437461548109fd81520427d6054810af99052042bd6414810b798c52042dd6314810db548520427e6414810cf990520423e64148109f590520433d64148108f590520427e6314810d798c520425e63148109f58c520435d63148109758c520427e6214810db988520427e6114810dd984520427e6014810de980520427f65d08109f997420427d65d08109f197420433e54d0810cf55342042f661d0810bd587420427f65908109f996420427d65908109f196420436e5290810db54a420427f65508109f995420427d65508109f195420433e5450810cf551420436e5250810db54942042f76150810bd18542042fb6050810be181420427f65108109f994420427d65108109f194420427f65cc8109f997320427d65cc8109f197320435e53cc810d754f32042f661cc810bd587320427f658c8109f996320427d658c8109f196320436e528c810db54a32042fa608c810be582320427f654c8109f995320427d654c8109f195320435e534c810d754d320436e524c810db54932042f7614c810bd18532042fb604c810be181320427f650c8109f994320427d650c8109f19432042be640c810af590320427e64944109f592510427e63944109f58e510427e62944109f58a510427d65d0410bb98b41042ed62d04109fd96410427d6590410cf952410433d5490410be98241042f960904109fd95410427f65104109f594410433e5410410cf55041042de6310410b758c41042fa6010410be580410427d65cc4109fd96310427d658c410d794e310435d538c410be98231042f9608c4109fd9531042bf644c410af19
  | 2 => 0x5288510db14a214427c6548510cfd51214433c5448510d7d4d214435c5348510dbd49214436c5248510bed8121442f860485109f994214433f5408510cf150214435f5308510d714c214436f5208510db148214427e65d0110cfd53404433c54d0110b798f40442dd63d0110d7d4f404435c53d0110dbd4b404436c52d0110bd98740442f561d01109f996404433f5490110cf152404435f5390110d714e404436f5290110db14a404427f65501109f595404427c6550110cfd51404433c5450110d7d4d404435c5350110dbd49404436c5250110bdd8540442f461501109f994404433f5410110cf150404435f5310110d714c40442ee6210110bb588404436f5210110db148404427e65cc110af99330442bd64cc110cfd53304433c54cc110d7d4f304435c53cc110dbd4b304436c52cc110bd98730442f561cc1109f996304433f548c110cf152304435f538c110d714e304436f528c110db14a304427f654c1109f595304427c654c110cfd51304433c544c110d7d4d304435c534c110dbd49304436c524c110bdd8530442f4614c1109f994304433f540c110cf150304435f530c110d714c304436f520c110db148304427e65c8110cfd53204433c54c8110d7d4f204435c53c8110dbd4b204436c52c8110bd98720442f561c81109f996204433f5488110cf152204435f5388110d714e204436f5288110db14a204427f65481109f595204427c6548110afd9120442bc6448110cfd51204433c5448110b7d8d20442dc6348110d7d4d204435c5348110dbd49204436c5248110bdd8520442f461481109f99420442be6408110af590204433f5408110cf150204435f5308110d714c204436f5208110db14820443e92008110cfd53104433c54c4110d7d4f104435c53c4110dbd4b104436c52c4110eed5310443b854c4110f6d4f104437a53c4110de14f10443d853c4110d614f10443eb52c4110fa14b104433f5484110cf152104435f5384110d714e104436f5284110db14a10443b75484110ed15210443d75384110f514e10443e75284110dd94a10443745284110f914a10443645284110fcd42104427e63d50109f58f540427e62d50109f58b540427e61d5010dd987540427e60d5010de983540427d6595010cfd52540427e63950109f58e540427e62950109f58a540433f64550109fd8d540427c63550109fd89540427c62550109fd85540427d61550109fd81540427d6055010cf55054042de6315010b758c54042ee6215010bb588540427e6415010cf990540427e6315010d798c540425e63150109f58c540435d63150109758c540427e6215010db988540426e62150109f588540436d62150109b588540427e6115010dd984540427e6015010de980540427e64d4c109f593530427e62d4c109f58b530427e61d4c10dd987530
  | 3 => 0x910bb994524436e65149109b994524436f5414910ebd50524432f5414910db950524436d5414910db15052443ac5414910cb150524436f5314910f3d4c524434f5314910db94c524436d5314910db14c52443cc5314910d314c524436f6414910db990524436d6414910db190524436f6314910db98c524436d6314910db18c524436f4314910db90c524436d4314910db10c524436f6114910db584524436f6014910db580524436d10149109fd97424427e65d09109f597424427c65d0910cfd53424433c54d0910d7d4f424435c53d0910dbd4b424436c52d09109fd96424427e65909109f596424427c6590910cfd52424433c5490910d7d4e424435c5390910dbd4a424436c52909109fd95424427e65509109f595424427c6550910cfd51424433c5450910d7d4d424435c5350910dbd49424436c52509109fd94424427e65109109f594424427c6510910cfd50424433c5410910d7d4c424435c5310910dbd48424436c5210910be98042442f960109109fd97324427e65cc9109f597324427c65cc910cfd53324433c54cc910d7d4f324435c53cc910dbd4b324436c52cc9109fd96324427e658c9109f596324427c658c910cfd52324433c548c910d7d4e324435c538c910dbd4a324436c528c9109fd95324427e654c9109f595324427c654c910cfd51324433c544c910d7d4d324435c534c910dbd49324436c524c9109fd94324427e650c9109f594324427c650c910af99032442bd640c910cfd50324433c540c910d7d4c324435c530c910dbd48324436c520c910bd98432442f5610c910be98032442f9600c9109f997414433f54d0510cf153414435f53d0510d714f41442ee62d0510bb58b414436f52d0510db14b41442fa60d0510be583414427e6590510cfd52414433c5490510d7d4e414435c5390510dbd4a414436c52905109f195414433f5450510cf151414435f5350510d714d414436f5250510db14941442fb6050510be181414427e6510510cfd50414433c5410510b798c41442dd6310510d7d4c414435c5310510dbd48414436c52105109f997314433f54cc510cf153314435f53cc510d714f314436f52cc510db14b31442fa60cc510be583314427e658c510cfd52314433c548c510d7d4e314435c538c510dbd4a314436c528c5109f19531442bf644c510af191314433f544c510cf151314435f534c510d714d31442ef624c510bb189314436f524c510db14931442fb604c510be181314427e650c510af99031442bd640c510cfd50314433c540c510d7d4c314435c530c510dbd48314436c520c510f54c4314427e65c8510af99321442bd64c8510cfd53214433c54c8510d7d4f214435c53c8510dbd4b214436c52c8510be98321442f960c85109f996214433f5488510cf152214435f5388510d714e214436f
  | 4 => 0xf592534427e6394d109798e534427e6294d10db98a534426e6294d109f58a534436d6294d109b58a534427d6194d10dd586534427d6094d10de58253442bf6454d10af191534433f5454d10cf15153442ef6254d10bb189534427f6454d10cfd91534423f6454d109f191534433c6454d108f191534435f6354d109fd89534436f6254d109bd89534427c6254d10db189534426c6254d109fd8553443776154d109fd81534437b6054d109ed81534427e6514d10cfd50534433c5414d10d754c534427e6414d109f590534435e6314d109f988534427d6214d109f984534427c6114d109f980534427c6014d10b7994534435e6514d1097994534435f5414d10e7d50534431f5414d10d7950534435d5414d10d7150534439c5414d10c7150534435f6414d10d7990534435d6414d10d7190534435f6214d10d7988534435d6214d10d7188534435f6114d10d7584534435f6014d10d7580534435d1014d109fd97434427e65d0d109f597434427c65d0d10cfd53434433c54d0d10d7d4f434435c53d0d109fd96434427e6590d109f596434427c6590d10cfd52434433c5490d10d7d4e434435c5390d109fd95434427e6550d109f595434427c6550d10cfd51434433c5450d10d7d4d434435c5350d109fd94434427e6510d109f594434427c6510d10cfd50434433c5410d10d7d4c434435c5310d10bd98443442f56110d10cfd53524433c54d4910d7d4f524435c53d49109f993524427d64d49109f98f524427d63d4910dbd5352443af54d4910cbd53524436e54d4910db553524436c54d4910eb153524432c54d4910dbd4f52443cf53d4910d3d4f524436e53d4910db54f524436c53d4910f314f524434c53d4910dbd93524436e64d4910db593524436c64d4910dbd8f524436e63d4910db58f524436c63d4910dbd0f524436e43d4910db50f524436c43d4910dbd87524436d61d4910dbd83524436d60d4910af99252442bd6494910cfd52524433c5494910b798e52442dd6394910d7d4e524435c5394910dbd4a524427e6494910cf992524423e64949109f592524433d64949108f592524427e6394910d798e524425e63949109f58e524435d63949109758e524427e62949109b98a524427d6194910dd586524427d6094910de58252442bf6454910af191524433f5454910cf15152442df6354910b718d524435f5354910d714d524427f6454910cfd91524423f64549109f191524433c64549108f191524427f6354910d7d8d524425f63549109f18d524435c63549109718d524436f62549109fd85524437761549109dd85524427f6054910ded81524427e6514910cfd50524433c5414910d7d4c524435c5314910db548524427e64149109f590524427e63149109f58c524436e62149109f984524427c61149109f980524427c6014
  | 5 => 0x31842be640c610af590318435f530c610d714c31842be64c8610af593218436e52c8610db54b21842fa60c8610be583218437565c8610ed99321843b564c8610ddd4b21843e652c8610dd54b21843e552c8610fc98321842f560c8610fc583218436f5288610db14a218436e5248610db54921842fb6048610be181218436f5208610db14821843e52108610bd59421843756508610f998821843775208610f9d4821843755208610f914821843e64208610f950821843e73208610f90c821842f56008610b798f40842dd63d0210cf952408433d5490210bd98640842f56190210cf950408433d5410210bb98840842ed6210210bd98440842f56110210af99330842bd64cc210d794e308435d538c210bd98630842f5618c210d794c308435d530c210bd98430842f5610c210db94a208436d5288210bd98620842f56188210f908620842bf6448210af19120842df6348210b718d20842f76148210bd18520842be6408210af590208436e5208210db54820842f66108210bd58420843e42108210fa48020842f565c4210dd59710842f662c4210bd18b10842f965c4210de597108437a53c4210de14f108427e63d51109f58f544427e62d51109f58b544433f63d5110cf98f544433d63d5110cf18f544433f62d5110cf98b544433d62d5110cf18b544433f61d5110cf587544433f60d5110cf583544433f5495110b798e54442dd6395110bb98a54442ed62951109f992544423e64951109f98e544435e63951109798e544427d6395110d758e544425d63951109f98a544436e62951109b98a544427d6295110db58a544426d62951109f586544437561951109f58254443796095110b7d8d54442dc6355110bbd8954442ec6255110cfd91544427f6355110d7d8d544425f63551109f18d544435c63551109718d544427f6255110dbd89544426f62551109f189544436c62551109b189544427f6155110ddd85544427f6055110ded81544427e6515110cf550544433e64151109f98c544427d63151109f988544427d62151109f984544427c61151109f980544427c6015110af994544433e65151108f994544433f6315110cf98c544433d6315110cf18c544433f6215110cf988544433d6215110cf188544433f6115110cf584544433f6015110cf580544433d1015110cfd53534433c54d4d109f993534427d64d4d109f98b534427d62d4d10d7d53534439f54d4d10c7d53534435e54d4d10d7553534435c54d4d10e7153534431c54d4d10d7d93534435e64d4d10d7593534435c64d4d10d7d8b534435e62d4d10d758b534435c62d4d10d7d87534435d61d4d10d7d83534435d60d4d10af99253442bd6494d10cfd52534433c5494d10d7d4e53442ee6294d10bb58a534427e6494d10cf992534423e6494d109f592534433d6494d108
  | 6 => 0x25e63952109f58e548435d63952109758e548427e62952109f58a548433f64552109fd8d548427c63552109fd89548427c6255210cf55054842ee6215210bb588548433e64152109f98c548427d63152109f988548436e62152109b988548427d6215210db588548426d6215210dd584548437a6015210af99353842bd64d4e10bb98b53842ed62d4e109f993538433e64d4e108f993538427d64d4e10cf593538423d64d4e109f98b538436e62d4e109b98b538427d62d4e10db58b538426d62d4e10dd587538437a60d4e10af99253842bd6494e10d7d4e538427e6494e10cf992538423e6494e109f592538433d6494e108f592538427e6294e109f58a538427f6454e109f191538435f6354e109fd89538427c6254e10d754c538427e6414e109f590538435e6314e109f988538427d6214e10dd584538437a6014e109fd97438427e65d0e109f597438427c65d0e10cfd53438433c54d0e109fd96438427e6590e109f596438427c6590e10cf952438433d5490e10d7d4e438435c5390e109fd95438427e6550e109f595438427c6550e10cfd51438433c5450e10d7d4d438435c5350e10bdd8543842f46150e109fd94438427e6510e109f594438427c6510e10cf950438433d5410e109f993528427d64d4a109f98f528427d63d4a10dd587528437a60d4a10dbd4a528427e6494a109f592528427e6394a109f58e528427f6454a109f191528427f6354a109f18d528436f6254a10ddd8552842be6414a10af590528436d5214a109f990528433e6414a108f990528427d6414a10cf590528423d6414a109f98c528427d6314a10db98852843756114a10de980528427f65d0a109f997428427d65d0a109f197428433e54d0a10cf55342842f661d0a10bd587428427f6590a109f996428427d6590a109f196428436e5290a10db54a428427f6550a109f995428427d6550a109f195428433e5450a10cf551428436e5250a10db54942842f76150a10bd185428427f6510a109f994428427d6510a109f19442842fa6010a10be580428427f65cca109f997328427d65cca109f197328436e52cca10db54b32842f661cca10bd587328427f658ca109f996328427d658ca109f196328427f654ca109f995328427d654ca109f19532842f7614ca10bd185328427f650ca109f994328427d650ca109f19432842be640ca10af590328436e520ca10db54832842fa600ca10be580328433e54d0610cf55341842ee62d0610bb58b41842fa60d0610be583418433f5490610cf152418433e5450610cf55141842fb6050610be181418433f5410610cf15041842de6310610b758c418435e53cc610d754f31842fa60cc610be583318435f538c610d714e31842bf644c610af191318435e534c610d754d31842ef624c610bb18931842fb604c610be181
  | 7 => 0x4d4b10cf59352c423d64d4b109f98f52c435e63d4b109798f52c427d63d4b10d758f52c425d63d4b10dd98752c437960d4b10af99252c42bd6494b10dbd4a52c427e6494b10cf99252c423e6494b109f59252c433d6494b108f59252c427e6394b109f58e52c427f6454b109f19152c427f6354b109f18d52c436f6254b10db54852c427e6414b109f59052c427e6314b109f58c52c436e6214b10dd98452c43796014b109fd9742c427e65d0b109f59742c427c65d0b10cfd5342c433c54d0b109fd9642c427e6590b109f59642c427c6590b10cf95242c433d5490b10dbd4a42c436c5290b109fd9542c427e6550b109f59542c427c6550b10cfd5142c433c5450b10dbd4942c436c5250b10bed8142c42f86050b109fd9442c427e6510b109f59442c427c6510b10cf95042c433d5410b109fd9732c427e65ccb109f59732c427c65ccb109fd9632c427e658cb109f59632c427c658cb10d794e32c435d538cb10be98232c42f9608cb109fd9532c427e654cb109f59532c427c654cb10bed8132c42f8604cb109fd9432c427e650cb109f59432c427c650cb10af99032c42bd640cb10d794c32c435d530cb10bd98432c42f5610cb10bb98b41c42ed62d0710cf95241c433d5490710be98241c42f96090710cf95041c433d5410710b798c41c42dd6310710be98041c42f96010710d794e31c435d538c710be98231c42f9608c710afd9131c42bc644c710bbd8931c42ec624c710be18131c42be640c710af59031c435e530c710d754c31c43d5310c710be98031c42f9600c710af99321c42bd64c8710db94a21c436d5288710be98221c42f96088710db94821c436d5208710be98021c42f96008710cf95340c433d54d0310b798f40c42dd63d0310bd98740c42f561d0310cfd5240c433c5490310cf95140c433d5450310bdd8540c42f46150310cfd5040c433c5410310bb98840c42ed6210310af99330c42bd64cc310d794f30c435d53cc310bd98730c42f561cc310be59730c437965cc310ee99330c43b964cc310ded4f30c43da53cc310de54f30c43d953cc310fc98730c42f961cc310fc58730c435f538c310d714e30c435e534c310d754d30c42f7614c310bd18530c435f530c310d714c30c43d9300c310be59430c4379650c310f698c30c437b530c310f6d4c30c4379530c310f614c30c43da430c310f650c30c43da320c310f60c830c42f9610c310f68c430c43d8310c310db94b20c436d52c8310bd98720c42f561c8310dbd4a20c436c5288310afd9120c42bc6448310b7d8d20c42dc6348310db94920c436d5248310bdd8520c42f46148310af99020c42bd6408310dbd4820c436c52083109f98f548427d63d52109f98b548427d62d5210dd587548437a60d5210cfd5254842de6395210b758e548427e6395210d798e5484
  | 8 => 0x20cf55240082ee6290020bb58a400827f6550020cf951400833d54500209fd94400827e65100209f594400827c6510020cf950400833d5410020bb98840082ed62100209f59730082be64cc020af593300833e54cc020cf553300827f658c0209f596300833e548c020cf552300835e538c020d754e30082ee628c020bb58a300827f654c020cf951300833d544c0209fd94300827e650c0209f594300827c650c020cf950300833d540c020d794c300835d530c020bb98830082ed620c020cf953200833d54c8020dbd5320083ae54c8020db55320083ad54c8020cb55320082ee61c8020cf952200833d5488020bb58a200836e5288020ee95220083b95488020be58a200837a5288020fa94a20083ea2188020fa086200827f6548020afd9120082bc6448020cf951200833d5448020b7d8d20082dc6348020bdd8520082f46148020bbd95200836f65480209bd9520083af6448020eb191200836f5448020eb951200836d5448020eb551200832d5448020f3d8d20083cc6348020f9d8520082ec6148020f918520082e46148020bbd81200836e5048020fad0120083e84048020facc120083e83048020bed95200837b65480209ed9520083bb6448020ee19120083ba5448020ee55120083db6348020f618d20082fb6248020fad89200837a5248020fa94920083eb4248020fa10920083eb3248020fa0c920083f36148020fc18520083eb2148020fa485200827e63d53109f58f54c427e62d53109f58b54c437661d5310de58354c433f5495310bb98a54c42ed62953109f98e54c427d63953109f98a54c436e62953109b98a54c427d6295310db58a54c426d6295310cfd9154c427f63553109f18d54c427f62553109f18954c433d5415310b798c54c42dd6315310cf99054c427e6315310d798c54c425e63153109f58c54c435d63153109758c54c427e62153109f58854c43766115310de58054c427e64d4f109f59353c427e62d4f109f58b53c437661d4f10de58353c435f5394f109f99253c427d6494f109f98a53c427d6294f109fd9153c427c6454f10d7d8d53c427f6254f109f18953c437b6054f10af99053c42bd6414f10d754c53c427e6414f10cf99053c423e6414f109f59053c433d6414f108f59053c435e6314f109f98853c427d6214f10dd98453c43796014f109fd9743c427e65d0f109f59743c427c65d0f10cf95343c433d54d0f10be98343c42f960d0f109fd9643c427e6590f109f59643c427c6590f10d794e43c435d5390f109fd9543c427e6550f109f59543c427c6550f10cf95143c433d5450f10d794d43c435d5350f10bed8143c42f86050f109fd9443c427e6510f109f59443c427c6510f10bd98443c42f56110f10af99352c42bd64d4b10b798f52c42dd63d4b109f99352c433e64d4b108f99352c427d6
  | 9 => 0x995430827d6550c209f195430833e5450c20cf55143082ef6250c20bb18943082fb6050c20be181430827f6510c209f994430827d6510c209f194430833e5410c20cf550430827e64948209f592520827e63948209f58e520827d65d0820cf953420833d54d08209fd96420827d6590820cf952420833d5490820db94a42082fa6090820be582420827f6550820cf951420833d5450820db949420827f65108209f594420833e5410820cf55042082fa6010820be580420827d65cc820cf953320833d54cc8209fd96320827d658c820cf952320833d548c820d794e320835d538c820be98232082f9608c8209fd95320833e544c820cf551320827f650c8209f59432082be640c820af590320833e540c820cf550320835e530c820d754c32082fa600c820be58032082be64d4420af593510833e54d4420cf553510833e5494420cf552510837751944209f992510827d64944209f98e510827d6394420cf951510833d54544209fd91510827c64544209fd8d510827c6354420af99051082bd6414420cf950510833d5414420b798c51082dd6314420dd544510827f65d04209f997410827d65d0420cf953410833d54d0420bb98b41082ed62d04209fd96410827e65904209f596410833e5490420cf552410827f65504209f595410827c6550420cf951410833d5450420bbd8941082ec6250420bed8141082f860504209fd94410827e65104209f594410833e5410420cf55041082de6310420b758c410827f65cc4209f997310827d65cc420cf953310833d54cc420d794f310835d53cc420bb98b31082ed62cc4209fd96310827e658c4209f596310833e548c420cf5523108376518c420dd546310827f654c4209f595310827c654c420afd9131082bc644c420cf951310833d544c420d794d310835d534c420bbd8931082ec624c420dd9453108375514c420bed8131082f8604c4209fd94310827e650c4209f59431082be640c420af590310833e540c420cf55031082be64c8420af593210833e54c8420cf553210837651c8420dd54721082fa60c8420be583210827d6588420cf952210833d5488420bb596210836d6588420dbd5221083ae5488420db55221083ad5488420cb552210836e5388420db14e21082ee6188420db54621082ed60884209fd95210833e5448420cf551210833e5408420cf55021083765108420dd54421083e52108420be98021082f96008420dbd5021083ae5408420db55021083ad5408420cb550210836e5308420db14c21082ee6108420f998421083e65108420db54421083e55108420fa98021082ed6008420fa58021082e960084209f992500827d64940209f98e500827d6394020db886500836c21940209f597400833e54d0020cf55340082de63d0020b758f400827f65900209f596400833e54900
  | 10 => 0x482ec6250120eb50940483775150120dd145404827e6510120cfd50404833c5410120d7d4c404835c5310120bb98840482ed6210120eb90840483775110120dd144404827e65cc120af99330482bd64cc120cfd53304833c54cc120d7d4f304835c53cc120bb98b30482ed62cc120ddd47304837451cc1209f996304833f548c120cf152304835f538c120d714e3048377518c120dd146304827f654c1209f595304827c654c120cfd51304833c544c120d7d4d304835c534c120bbd8930482ec624c120ddd453048374514c1209f994304833f540c120cf150304835f530c120d714c3048377510c120dd14430483d9300c120cfd53204833c54c8120d7d4f204835c53c8120ddd47204837451c8120eed5320483b854c8120f6d4f20483d853c8120fa90b20483e942c8120fcd4720483f051c8120cfd52204833c5488120d7d4e204835c5388120ddd4620483745188120bbd9220482ed6488120ebd5220483ac5488120f3d4e20483cc5388120f9d46204836c5188120f914620483645188120fad42204827e63d50209f58f540827e62d5020db98b540827e61d50209f587540827e60d5020de983540827d6595020cfd52540827e63950209f58e540827e61950209f586540823d6595020cfd8e540833e6395020cf58e540833c6395020cf98a540833c6295020cfd86540833e6195020cf586540833c6195020cf982540833c6095020cfd91540827f63550209f18d540827f62550209f589540827f61550209f185540833f6555020cfd8d540833e6355020cf58d540833c6355020cf989540833c6255020cfd85540833e6155020cf585540833c6155020cf981540833c6055020cf08154082be6415020cf550540827e6415020cf990540823e64150209f98c540827d63150209f988540836e62150209b988540827e61150209f584540827e6015020de98054082be64d4c20af593530833e54d4c20cf553530827e64d4c20cf993530823e64d4c209f593530833d64d4c208f593530827e62d4c20db98b530827e61d4c209f587530827e60d4c20de983530827d6594c20cf952530833d5494c20d7d4e530827e6494c209f592530827e6194c209f586530833e5454c20cf551530827f6454c209f191530835f6354c209fd89530827d6254c209fd85530827c6154c20af99053082bd6414c20cf950530833d5414c20d754c53082f66114c20bd584530827e6414c20cf990530823e6414c209f590530833d6414c208f590530827e6314c20d798c530827e6214c20db988530827e6114c20dd98453082766114c209f58453083756114c209d584530827e6014c20de980530827f65d0c209f997430827d65d0c209f197430833e54d0c20cf553430827f6590c209f996430827d6590c209f196430833e5490c20cf552430827f6550c209f
  | 11 => 0xbc6454520cfd51514833c5454520b7d8d51482dc6354520d7d4d514835c5354520cfd50514833c5414520d7d4c514835c5314520dd544514827e64145209f590514827e63145209f58c514836e4214520db50851482f66514520dd99451483775414520edd5051483375414520dd95051483755414520dd15051483b45414520cd15051483775314520f5d4c51483575314520dd94c51483755314520dd14c51483d45314520d514c51483e64214520f950851483776414520dd99051483756414520dd19051483776314520dd98c51483756314520dd18c51483774314520dd90c51483754314520dd10c51483776214520ddd0851483764214520d990851483754214520d950851483744214520ddcc851483763214520dd4c851483743214520ddd8051483756014520dd480514827e65d05209f597414827c65d0520cfd53414833c54d0520d7d4f414835c53d0520bb98b41482ed62d0520ddd47414837451d05209f996414827d65905209f196414833f5490520cf152414835f5390520d714e41483ad4290520ddd46414837451905209fd95414827e65505209f195414833f5450520cf151414835f5350520d714d41483775150520dd145414827e65105209f594414827c6510520cfd50414833c5410520b798c41482dd6310520d7d4c414835c5310520bb98841482ed6210520eb50841483775110520dd14441482fa6010520be580414827e65cc5209f597314827c65cc520cfd53314833c54cc520d7d4f314835c53cc520ddd47314837451cc5209f996314827d658c5209f196314833f548c520cf152314835f538c520d714e3148377518c520dd146314827f654c5209f995314827c654c520afd9131482bc644c520cfd51314833c544c520d7d4d314835c534c520bbd8931482ec624c520ddd453148374514c520bed8131482f8604c5209f994314827d650c5209f19431482be640c520af590314833f540c520cf150314835f530c520d714c31482ee620c520bb5883148377510c520dd14431482fa600c520be580314827e65c8520af99321482bd64c8520cfd53214833c54c8520d7d4f214835c53c8520dd147214833f5488520cf152214835f5388520d714e21483775188520dd14621482fa6088520be582214833f5448520cf151214835f5348520d714d21483775148520dd14521482fb6048520be181214827e6508520cfd50214833c5408520d7d4c214835c5308520ddd44214827e65d0120cfd53404833c54d0120b798f40482dd63d0120d7d4f404835c53d0120bb98b40482ed62d0120eb50b404837751d0120dd147404827e6590120cfd52404833c5490120d7d4e404835c5390120eb90a40483775190120dd146404827f65501209f595404827c6550120cfd51404833c5450120d7d4d404835c5350120bbd894
  | 12 => 0x54d209f18553483746154d209d185534827f6054d20ded81534827e6514d20cfd50534833c5414d20d754c534827e6414d209f590534835e6314d209f988534827c6214d209f984534827d6114d20b7994534835e6514d2097994534835f5414d20e7d50534831f5414d20d7950534835d5414d20d7150534839c5414d20c7150534835f6414d20d7990534835d6414d20d7190534835f6214d20d7588534835f6114d20d7984534835d6114d20d7184534835f6014d20d7580534835d2014d209fd97434827e65d0d209f597434827c65d0d20cfd53434833c54d0d20d7d4f434835c53d0d20bb98b43482ed62d0d20be98343482f960d0d209fd96434827e6590d209f596434827c6590d20cfd52434833c5490d20d7d4e434835c5390d209fd95434827e6550d209f595434827c6550d20cfd51434833c5450d20d7d4d434835c5350d209fd94434827e6510d209f594434827c6510d20cfd50434833c5410d20d7d4c434835c5310d20bb98843482ed6210d209f997424833f54d0920cf153424835f53d0920d714f42482fa60d0920be583424827e6590920cfd52424833c5490920d7d4e424835c5390920bb996424836e6590920bb59242483af5490920db952424836c5490920eb152424832c5490920f3d4e42483cc5390920bb982424827c6550920cfd51424833c5450920d7d4d424835c5350920bed8142482f86050920db195424826c6550920ebd9142483af5450920db951424836c5450920eb15142483cf5350920f314d42483af4350920eb50d42483eb6050920bb18142483e86050920ba181424827e6510920cfd50424833c5410920d7d4c424835c5310920bb98842483ad42109209f997324833f54cc920cf153324835f53cc920d714f32482fa60cc920be583324827e658c920cfd52324833c548c920d7d4e324835c538c9209f195324833f544c920cf151324835f534c920d714d32482fb604c920be181324827e650c920af99032482bd640c920cfd50324833c540c920d7d4c324835c530c920cfd53514833c54d4520d7d4f514835c53d45209f993514827d64d45209f98f514827d63d4520ddd5351483b754d4520cdd53514837654d4520dd553514837454d4520ed153514833454d4520ddd4f51483d753d4520d5d4f514837653d4520dd54f514837453d4520f514f514835453d4520f990b51483e542d4520ddd93514837664d4520dd593514837464d4520ddd8f514837663d4520dd58f514837463d4520ddd0f514837643d4520dd50f514837443d4520ddd8b514837742d4520dd90b514837542d4520dd10b514837732d4520dd8cb514837532d4520dd0cb514837760d4520dd58351482be6494520af592514833f5494520cf15251482de6394520b758e514835f5394520d714e51483775194520afd9151482
  | 13 => 0xdbd52218836d5488620db94e218836c5388620f9946218836d5188620f954621883ea6088620bb58221883e96088620dd94521883755148620bed8121882f86048620f948421882ed6508620db594218836f5408620db550218836e5308620db14c21883e66108620f9d44218836d5108620f914421882ed6008620cfd53408833c54d0220b798f40882dd63d0220cf952408833d5490220bb98a40882ed6290220cfd51408833c5450220cf950408833d5410220bb98840882ed6210220af99330882bd64cc220d794e308835d538c220bb98a30882ed628c220d794c308835d530c220bb98830882ed620c220f64c030882ed65c8220db597208836f54c8220db55320882ee61c8220be597208837965c82209f98f544827d63d51209f987544827d61d5120ebd8b544833f63d5120cf98f544833d63d5120cf18f544833f62d5120cf58b544833f61d5120cf987544833d61d5120cf187544833f60d5120cf583544833f5495120b798e54482dd6395120bd98654482f561951209f992544823e64951209f98e544835e63951209798e544827d6395120d758e544825d63951209f58a544836d62951209f986544837661951209d986544827d6195120dd586544827561951209f58254483796095120b7d8d54482dc6355120bdd8554482f46155120cfd91544827f6355120d7d8d544825f63551209f18d544835c63551209718d544827f6255120dbd89544827f6155120ddd85544827761551209f185544837461551209d185544827f6055120ded81544827e6515120cf550544833e64151209f98c544827d63151209f988544836d62151209f188544827e61151209f58454482be6515120cf994544823e6515120eb588544833f6315120cf98c544833d6315120cf18c544833f6215120cf588544832d6215120cfd84544833e6115120cf584544833c6115120cfd80544833d6015120cf480544833f54d4d20cf153534827e64d4d209f593534827e61d4d209f587534835f54d4d20e7d53534831f54d4d20d7953534835d54d4d20d7153534839c54d4d20c7153534835f64d4d20d7993534835d64d4d20d7193534835f62d4d20d758b534835f61d4d20d7987534835d61d4d20d7187534835f60d4d20d758353482be6494d20af592534833f5494d20cf152534835f5394d20bd98653482f56194d209f992534833e6494d208f992534827d6494d20cf592534823d6494d209f98e534825e6394d209f58a534836d6294d209f98653483766194d209d986534827d6194d20dd58653482756194d209f58253483796094d20afd9153482bc6454d20cfd51534833c5454d20bdd8553482f46154d209fd91534833f6454d208fd91534827c6454d20cf191534823c6454d20d7d8d534827f6254d20dbd89534827f6154d20ddd85534827761
  | 14 => 0x4721c837551c8720be98321c82f960c8720dd94421c83755108720be98021c82f96008720cf95340c833d54d0320b798f40c82dd63d0320bb98b40c82ed62d0320eb50b40c833f5490320cf15240c83ae4290320cf95140c833d5450320bbd8940c82ec6250320eb50940c833f5410320cf15040c82ee6210320bb58840c83ae4210320af99330c82bd64cc320d794f30c835d53cc320bb98b30c82ed62cc320d7d4e30c835c538c320d794d30c835d534c320bbd8930c82ec624c320d7d4c30c835c530c3209f98f548827d63d5220db58b548827e61d52209f587548837a60d5220cfd52548827e63952209f58e548827e61952209f586548833f64552209fd8d548827c63552209fd85548827c6155220cf550548833e64152209f98c548827d6315220db588548827e61152209f584548837a60152209f993538827d64d4e20db58b538827e61d4e209f587538837a60d4e20af99253882bd6494e20d7d4e538827e6494e20cf992538823e6494e209f592538833d6494e208f592538827e6194e209f586538827f6454e209f191538835f6354e209fd85538827c6154e20d754c538827e6414e209f590538835e6314e20db588538827e6114e209f584538837a6014e209fd97438827e65d0e209f597438827c65d0e20cfd53438833c54d0e20be98343882f960d0e209fd96438827e6590e209f596438827c6590e209fd95438827e6550e209f595438827c6550e20cfd51438833c5450e20bbd8943882ec6250e209fd94438827e6510e209f594438827c6510e20cf953428833d54d0a20be98342882f960d0a20cfd52428833c5490a20cf951428833d5450a20bed8142882f86050a20cfd50428833c5410a20d794f328835d53cca20be98332882f960cca20d7d4e328835c538ca20d794d328835d534ca20bed8132882f8604ca20af99032882bd640ca20d7d4c328835c530ca20ddd46518827e64946209f592518827e63946209f58e51882bf6454620af191518827f6454620cfd91518823f64546209f191518833c64546208f191518827f63546209f18d518837551146209fd97418827e65d06209f59741882ee62d0620bb58b418827f65906209f996418827d6590620cfd52418833c54906209fd95418827d65506209f19541882ef6250620bb189418827f65106209f994418827d6510620cfd50418833c5410620b798c41882dd6310620be98041882f960106209fd97318827e65cc6209f59731882ee62cc620bb58b318827f658c6209f996318827d658c6209fd95318827d654c6209f19531882bf644c620af19131882ef624c620bb18931882fb604c620be181318827f650c6209f994318827d650c620af99031882bd640c620be98031882f9600c620af99321882bd64c8620dd94621883755188620be98221882f9608862
  | 15 => 0xc37b654c0309ed95300c2fb634c030f6d8d300c37a534c030f694d300c3db434c030f610d300c3db324c030f64c9300c2f8614c030f68c5300c3d8314c0309f98f54c827d63d5320db98b54c827e61d53209f58754c837960d5320cfd5254c827e63953209f58e54c836e62953209f98654c827d6195320cfd9154c827f63553209f18d54c827f61553209f18554c833d5415320b798c54c82dd6315320cf99054c827e6315320d798c54c825e63153209f58c54c835d63153209758c54c836e62153209f98454c827d6115320de58054c827e64d4f209f59353c836e62d4f209f98753c827d61d4f20de58353c835f5394f209f99253c827d6494f209f98653c827d6194f209fd9153c827c6454f20d7d8d53c827f6154f209f18553c82be6414f20af59053c835d5314f209f99053c833e6414f208f99053c827d6414f20cf59053c823d6414f20d798c53c836e6214f209f98453c827d6114f20de58053c827f65d0f209f99743c827d65d0f209f19743c833e54d0f20cf55343c82ee62d0f20bb58b43c827f6590f209f99643c827d6590f209f19643c835e5390f20d754e43c827f6550f209f99543c827d6550f209f19543c833e5450f20cf55143c835e5350f20d754d43c82fb6050f20be18143c827f6510f209f99443c827d6510f209f19443c82ee6210f20bb58843c833f54d0b20cf15342c833e5490b20cf55242c82fa6090b20be58242c836d6590b20db95242c83ae5490b20eb55242c836c5490b20bb98242c83ea6090b20fa58242c833f5450b20cf15142c82ef6550b20dbd9542c83af6450b20ebd5142c836e5450b20db15142c83ac5450b20ebd0d42c83ad4350b20bb18142c833e5410b20cf55042c83ad4210b20be98042c82f96010b20d794e32c835d538cb20be98232c82f9608cb20af99032c82bd640cb20d794c32c835d530cb20be98032c82f9600cb20af99351c82bd64d4720b798f51c82dd63d4720ddd4651c827e64947209f59251c827e63947209f58e51c836e4294720db50a51c827f64547209f19151c827f63547209f18d51c837551147209fd9741c827e65d07209f59741c82ee62d0720bb58b41c827f65907209f99641c827d6590720cf95241c833d5490720eb50a41c827f65507209f59541c827c6550720bed8141c82f860507209fd9441c827e65107209f59441c833e5410720cf55041c82de6310720b758c41c82ee6210720bb58841c83ad42107209fd9731c827e65cc7209f59731c827f658c7209f99631c827d658c720d794e31c835d538c7209fd9531c827d654c7209f19531c82bf644c720af19131c82ef624c720bb18931c82fb604c720be18131c827f650c7209f99431c827d650c720af99031c82bd640c720d794c31c835d530c720bb98831c82ed620c720af99321c82bd64c8720dd9
  | 16 => 0xa600c830b7580320c3d9600c830b6580320c37751944309f992510c27d64944309f98a510c27d6294430afd91510c2bc6454430bbd89510c2ec62544309fd91510c33f64544308fd91510c27c6454430cf191510c23c6454430d790d510c35d43544309fd89510c36f62544309bd89510c27c6254430db189510c26c6254430de181510c2be6414430af590510c2ee6214430bb588510c37551144309fd97410c27e65d04309f597410c33e54d0430cf553410c2de63d0430b758f410c39d43d0430bb98b410c2ed62d0430be983410c2f960d04309fd96410c27e65904309f596410c33f5490430cf152410c39e4390430dd946410c37551904309fd95410c27d65504309f195410c33e5450430cf551410c2df6350430b718d410c39d4350430dd945410c3755150430bed81410c2f860504309fd94410c27e65104309f594410c33f5410430cf150410c2de6310430b758c410c39e4310430dd947310c37551cc430be983310c2f960cc4309f596310c2dd658c430d7596310c2df648c430b7592310c2de628c430b7986310c35d518c430f6d82310c2dd608c430f6182310c27f654c430afd91310c2bc644c430bbd89310c2ec624c430bed81310c2be640c430af590310c376510c430dd544310c2fa600c430be580310c2df640c430e7990310c2dd640c430e7590310c29d640c430b7988310c2de610c430f5984310c3d6510c430d7544310c3d5510c430d5544310c3da600c430b7580310c3d9600c4309fd97210c27e65c84309f597210c2be64c8430af593210c2de63c8430b758f210c36e52c8430db54b210c2fa60c8430be583210c27f65884309f996210c27d6588430b798e210c2dd6388430f30ca210c3765188430dd546210c27f65484309f595210c27c6548430b7d8d210c2dc6348430db949210c36d5248430dd945210c3755148430bed81210c2f860484309fd94210c27e65084309f594210c2df6308430b718c210c3cc32084309f992500c27d6494030d790e500c35d4394030d78ca500c35c3294030d78c6500c35c31940309f597400c2de63d0030b758f400c27f65900309f596400c33e5490030cf552400c2de6390030b758e400c39d43900309fd95400c27f65100309f994400c27d65100309f194400c33e5410030cf550400c2de6310030b758c400c39d4310030bb988400c2ed6210030ee500400c2be64cc030af593300c2df64cc030e7993300c2dd64cc030e7593300c29d64cc030b798b300c2de61cc030b758e300c35e538c030be58e300c37a538c030f694e300c3da438c030f650e300c3da328c030f60ca300c2fa618c030f68c6300c3d8318c0309fd95300c2df654c030d7d95300c25f654c030b7d91300c2dd644c030b7189300c2dc614c030b7d81300c35e504c030f6d01300c3d8404c030bed9530
  | 17 => 0x85309fd95214c27e65485309f195214c27e65085309f594214c27c6508530b798c214c2dd6308530dbd48214c36c5208530ddd44214c3745108530be980214c2f960085309f997404c33f54d0130cf153404c2de63d0130b758f404c27e6590130cf952404c33d54901309fd95404c27d65501309f195404c33f5450130cf151404c2df6350130b718d404c27e6510130cf950404c33d5410130bb988404c2ed6210130af993304c2bd64cc130ee993304c3b964cc130de147304c35f548c130d7552304c35c528c130d7146304c3db508c1309f98f540c35e63d50309f98b540c27d62d50309f987540c27d61d50309f983540c37a60d50309f596540c33f5495030d798e540c27e62950309f58a540c27e61950309f586540c33f64550309fd8d540c27d63550309fd89540c27c62550309fd85540c27c6155030cf550540c2ee6215030bb588540c2f66115030bd584540c27e6415030cf990540c27e6315030d798c540c27e6215030db988540c26e62150309f588540c36d62150309b588540c27e6115030dd984540c27661150309f584540c37561150309d584540c27e6015030de980540c27e6494c30cf992530c23e6494c309f592530c33d6494c308f592530c27d65d0c30cfd53430c33c54d0c309fd96430c27d6590c30cf952430c33d5490c30be982430c2f96090c30d7596430c25d6590c30b7592430c35e5490c30e7952430c39d5490c30d7152430c2de6290c30b7986430c3da6090c30b7582430c3d96090c30b6582430c27f6550c30cfd51430c33c5450c30b7d95430c35f6550c30e7d91430c39f5450c30d7951430c35c5450c30e7151430c2dc6250c30b7185430c2df6050c309fd94430c27d6510c30cf950430c33d5410c30b798c430c39d4310c30be980430c2f96010c30dbd4a520c27e64948309f592520c27e61948309f586520c27f64548309f191520c27f61548309f185520c2be6414830af590520c36d5214830bd984520c2f561148309fd97420c27e65d08309f597420c33e54d0830cf553420c2de63d0830b758f420c39d43d08309fd96420c27e65908309f596420c36e5290830db54a420c27f65508309f595420c27c6550830cf951420c33d5450830b7d8d420c2dc6350830e750d420c36e5250830db549420c2fb6050830be181420c27f65108309f994420c27d6510830b798c420c2dd6310830be980420c2f96010830db94b320c36d52cc830be983320c2f960cc8309f596320c2dd658c830d7596320c2df648c830b7592320c2de628c830d754a320c2de618c830b7582320c27f654c830af990320c2bd640c830db948320c36d520c830be980320c2f9600c830b7d90320c39e640c830b7590320c39d640c830a7590320c2de620c830f3988320c3ce520c830d7548320c3cd520c830b7984320c3d
  | 18 => 0xb718c218c36e5208630db548218c3cc3208630be980218c2f96008630b798f408c2dd63d0230cf952408c33d5490230b798e408c2dd6390230e750e408c33e5410230cf550408c2de6310230b758c408c39d4310230bb988408c2ed6210230af993308c2bd64cc230b7597308c35d65cc230b7d93308c39e64cc230b7593308c39d64cc230a7593308c2de62cc230b7987308c2f965cc230de597308c3ba64cc230ee593308c37a51cc2309f98b544c27d62d51309f987544c27d61d5130cfd52544c27e64951309f58e544c35d63951309758e544c27e62951309f58a544c27e61951309f586544c27d6095130de582544c2ef6255130bb189544c2f76155130bd185544c33f64551309fd8d544c35f63551309fd89544c36f62551309bd89544c27c6255130db189544c26c62551309fd85544c37761551309dd85544c27c6155130dd185544c27461551309fd81544c37b60551309f994544c33d5415130cf990544c27e63151309f18c544c27e62151309f588544c27e61151309f584544c27e65d0d30cfd53434c33c54d0d30be983434c2f960d0d309f996434c27c6550d30cfd51434c33c5450d30bed81434c2f86050d309f994434c27e64d49309f593524c27e61d49309f587524c36f5294930afd91524c2bc6454930bdd85524c2f46154930af990524c2bd6414930db548524c27e6414930cf990524c23e64149309f590524c33d64149308f590524c27e61149309f584524c27e65d09309f597424c27c65d0930cf953424c33d54d0930dbd4b424c36c52d09309f996424c27d65909309f196424c33f5490930cf152424c27f65509309f995424c27c6550930cf951424c33d54509309f994424c27d65109309f194424c33f5410930cf150424c36f5210930db148424c27e65cc930dbd4a324c36c528c930be982324c2f9608c930dbd49324c36c524c930bed81324c2f8604c9309f994324c2be640c930af590324c27e64d45309f593514c27e62d45309f58b514c3775194530afd91514c2bc6454530bbd89514c2ec6254530dd544514c27e64145309f590514c27e62145309f588514c27e65d05309f597414c27c65d0530bb98b414c2ed62d0530ddd47414c37451d05309f996414c27d65905309f196414c33f5490530cf152414c27f65505309f995414c27c65505309f994414c27d65105309f194414c33f5410530cf150414c2de6310530b758c414c3775110530dd144414c27e65cc530ddd46314c374518c530be982314c2f9608c530afd91314c2bc644c530bbd89314c2ec624c530ddd45314c374514c530bed81314c2f8604c5309f994314c2be640c530af590314c3d5310c5309f997214c27d65c85309f197214c2be64c8530af593214c37751c8530dd147214c27e65885309f596214c27c6588530dbd4a214c36c528
  | 19 => 0x9548c27f61552309f185548c33d5415230bb988548c2ed6215230cf990548c35d63152309f988548c36e62152309b988548c27d6215230db588548c26d62152309f984548c27d6115230de980548c33e54d0e30cf553438c2fa60d0e30be583438c2dd6590e30d7596438c35e5490e30d7152438c2de6290e30b7986438c2dd6090e30cf951438c33d5450e30bed81438c2f86050e30d7d95438c39f6450e30d7951438c39e5450e30e7551438c35c5450e30b7189438c2dc6150e30b7d81438c3db6050e30f6181438c39d4310e30dbd4a528c27e6494a309f592528c27e6194a309f586528c27f6454a309f191528c27f6154a309f185528c2be6414a30af590528c36d5214a309fd97428c27e65d0a309f597428c33e54d0a30cf553428c2de63d0a30b758f428c39d43d0a309fd96428c27e6590a309f596428c36e5290a30db54a428c27f6550a309f595428c27c6550a30cf951428c33d5450a30b7d8d428c2dc6350a30e750d428c36e5250a30db549428c27f6510a309f994428c27d6510a30b798c428c2dd6310a30db94a328c36d528ca30be982328c2f9608ca30b7d92328c2dd648ca30f394a328c35d528ca30f354a328c2de618ca30f6982328c2dd608ca30f6582328c36e524ca30db549328c2fb604ca30be181328c2be640ca30af590328c2dd650ca30d7594328c2df640ca30e7990328c2dd640ca30e7590328c29d640ca30f3988328c35d520ca30b7984328c2dd600ca30af993518c2bd64d4630bb98b518c2ed62d4630ddd46518c27e64946309f592518c27e62946309f58a518c27f64546309f191518c35e4354630d750d518c27f62546309f189518c37551146309fd97418c27e65d06309f597418c2de63d0630b758f418c39d43d0630bb98b418c2ed62d06309fd96418c27e65906309f596418c33e5490630cf552418c39e43906309fd95418c27d65506309f195418c2df6350630b718d418c39d43506309fd94418c27e65106309f594418c33e5410630cf550418c2de6310630b758c418c39e4310630dd946318c375518c630be982318c2f9608c630b7d92318c2dd648c630b798a318c3d6518c630d7546318c3d5518c630f6982318c2dd608c630f6582318c2bf644c630af191318c2ef624c630bb189318c376514c630dd545318c2fb604c630be181318c2be640c630af590318c2dd650c630d7594318c2df640c630e7990318c2dd640c630e7590318c29d640c630b7988318c3d6610c630d7544318c2dd600c6309fd97218c27e65c86309f597218c2be64c8630af593218c2de63c8630b758f218c27f65886309f996218c27d6588630b798e218c2dd6388630db94a218c36d5288630f30ca218c27f65486309f595218c27c6548630b7d8d218c2dc63486309fd94218c27e65086309f594218c2df6308630
  | 20 => 0xc2f96090f30cf95143cc33d5450f30cf95043cc33d5410f30be98043cc2f96010f30af99352cc2bd64d4b30cf95352cc33d54d4b30bd98752cc2f561d4b30cf95252cc33d5494b30dbd4a52cc27e6494b309f59252cc27e6194b309f58652cc33e5454b30cf55152cc27f6454b309f19152cc27f6154b309f18552cc2be6414b30af59052cc33e5414b30cf55052cc36d5214b309fd9742cc27e65d0b309f59742cc33e54d0b30cf55342cc27f6590b309f99642cc27d6590b30cf95242cc33d5490b309fd9542cc27d6550b309f19542cc33e5450b30cf55142cc2fb6050b30be18142cc27f6510b309f99442cc27d6510b30cf95042cc33d5410b30be98042cc2f96010b30cf95332cc33d54ccb30db94b32cc36d52ccb30be98332cc2f960ccb30cf95232cc33d548cb30cf95132cc33d544cb30af99032cc2bd640cb30cf95032cc33d540cb30db94832cc36d520cb30be98032cc2f9600cb30af99351cc2bd64d4730cf95351cc33d54d4730bb98b51cc2ed62d4730cf95251cc33d5494730ddd4651cc27e64947309f59251cc27e62947309f58a51cc33e5454730cf55151cc27f64547309f19151cc27f62547309f18951cc37b6054730af99051cc2bd6414730cf95051cc33d5414730dd54451cc27f65d07309f99741cc27d65d0730cf95341cc33d54d0730bb98b41cc2ed62d0730be98341cc2f960d07309fd9641cc27e65907309f59641cc33e5490730cf55241cc27f65507309f59541cc27c6550730cf95141cc33d5450730bed8141cc2f860507309fd9441cc27e65107309f59441cc33e5410730cf55041cc2de6310730b758c41cc33e54cc730cf55331cc37651cc730dd54731cc2fa60cc730be58331cc33e548c730cf55231cc2bf644c730af19131cc33e544c730cf55131cc2ef624c730bb18931cc2f8604c730af99031cc2bd640c730cf95031cc33d540c730dd94431cc375510c730f54c431cc2fa600c730be58031cc27f65c87309f99721cc27d65c8730af99321cc2bd64c8730cf95321cc33d54c8730dd94721cc37551c8730be98321cc2f960c87309fd9621cc27e65887309f59621cc33e5488730cf55221cc36e5288730db54a21cc27f65487309f59521cc27c6548730cf95121cc33d5448730bed8121cc2f860487309fd9421cc27e65087309f59421cc33e5408730cf55021cc2de6308730b758c21cc36e5208730db54821cc3765108730dd54421cc33e54d0330cf55340cc2de63d0330b758f40cc33e5490330cf55240cc33e5450330cf55140cc2df6350330b718d40cc33e5410330cf55040cc2ee6210330bb58840cc3b94010330d758f548c27e62d52309f58b548c27e61d52309f587548c37a60d5230cfd52548c35d63952309f98a548c27d62952309f986548c27d6195230cfd91548c27f62552309f18
  | 21 => 0x5250440b798c41102dd6310440db948411036d5210440dd94441103755110440be98041102f96010440e798c41102bd6310440e758c411029d6310440cf94c41102be6210440eb948411033d5210440eb548411032d5210440af98441103b66110440ed944411033d5110440ed54441103ba6010440af58041103b960104409fd97311027e65cc4409f59731102be64cc440af593311035e53cc440d754f311039d43cc440db94b311036d52cc4409fd96311027e658c4409f59631102bf648c440af192311036e528c440db54a3110376518c440dd546311027f654c4409f595311027c654c440afd9131102bc644c440d794d311035d534c440e750d31102ef624c440bb189311036e524c440db5493110376514c440dd54531102fb604c440be181311027f650c4409f994311027d650c440af99031102bd640c440db948311036d520c4409fd97211027e65c84409f59721102be64c8440af593211036e52c8440db54b211027f65884409f996211027d6588440af99221102bd6488440db94a211036d5288440eb90a211027f65484409f595211027c6548440afd9121102bc6448440db949211036d5248440bed8121102f860484409fd94211027e65084409f59421102bf6408440af190211036e5208440db54821103ae4208440cfd0e501033d4394040cf90a501033c4294040cf906501033c4194040b798f40102dd63d0040db94b401036d52d0040e798f40102bd63d0040e758f401029d63d0040af98b40103ae52d0040cf54b40103ad52d0040cb54b40102be61d0040af592401033e5490040db94a401036d5290040be592401037a5490040ee95240103bb4390040ee50e40103ea5290040fa54a40103ba4290040ee10a40103ba4190040ee106401027f6550040db949401036d5250040afd95401033f65500408fd9540102bf6350040af18940103ae5250040cf54940103ad5250040cb54940102bc6150040afd81401033e5050040bed95401037b65500409ed9540102fb6450040eed91401037a5450040ee95140103ba4350040ee10d40103ea5250040fa549401035e63d53309f98b54cc27d62d53309f98754cc27d61d5330de58354cc33f54953309f98a54cc27d62953309f98654cc27d6195330cf98e54cc33c6395330cfd8a54cc33e6295330cf58a54cc33c6295330cfd8654cc33e6195330cf58654cc33c6195330cfd8254cc33d6095330cfd9154cc27f62553309f18954cc27f61553309f18554cc33f6555330cf98d54cc33c6355330cfd8954cc33e6255330cf58954cc33c6255330cfd8554cc33e6155330cf58554cc33c6155330cfd8154cc33d6055330cf55054cc33e6415330d798c54cc27e62153309f58854cc27e61153309f58454cc3796015330cf95343cc33d54d0f30cf95243cc33d5490f30be98243c
  | 22 => 0xc409f185531035d5314c40bb98853102ed6214c40bd98453102f56114c40d794f431035d53d0c40be98343102f960d0c40cf94f431039e53d0c40e754f43102be62d0c40af98743103ba60d0c40af58343103b960d0c40ae583431027d6590c40af592431027f6550c40afd95431033f6550c40e7d8d431039f5350c40cf94d431039c5350c40af18943102bc6150c40afd8143102be6410c40d794c431035d5310c40e750c43102fa6010c40be580431036f52948409f98e521027d63948409f986521027d6194840eb192521036f5394840db94e521036d5394840db14e52103af4394840eb50e521036c6494840dbd8e521036e6394840db58e521036c6394840dbd0e521036e4394840db50e521036c4394840dbd86521036e6194840db586521036c6194840db982521036c60948409fd8d521027c6354840cfd0d521033d43548409fd85521027c6154840dbd9552103ac6454840dbd4d521036e5354840db54d521036c5354840ebd0d52103ad4354840db991521036f6354840db98d521036d6354840db18d521036f4354840cbd0d521036e4354840db50d521032d4354840db10d521036f6154840db985521036d6154840db185521036e6054840db181521036c4054840bb988521036d5214840cf953421036e52d0840db54b42102fa60d0840be583421027d6590840db54a42102bd6590840cf596421023d6590840af58e42102be6290840eb94a421033d5290840eb54a421032d5290840af98642102bd60908409fd95421033e5450840db949421036e5210840db54842102fa6010840be58042102bd6310840af98842103ae6210840eb948421033d5210840eb548421032d5210840af98442103ba6010840af58042103b960108409fd97321027e65cc8409f59732102be64cc840af593321036e52cc840db54b321027f658c8409f996321027d658c840afd9232102bc648c840db94a321036d528c8409fd95321027d654c8409f19532102bf644c840af191321036e524c840db54932102fb604c840be181321027f650c8409f994321027d650c840af99032102bd640c840db948321036d520c840bb98b51102ed62d4440db94b511036d52d4440db94a511036d5294440ddd46511027e63944409f58e511027e62944409f58a511036e5254440db549511027f63544409f18d511033f4354440cf50d511027f62544409f18951102de6314440b758c51102ee6214440bb588511036e5214440db54851103755114440bb98b41102ed62d0440db94b411036d52d0440dd947411037551d0440be98341102f960d04409f596411036e5290440db54a41102bd6590440cf59641102bd6390440cf94e41102be6290440eb94a411033d5290440eb54a411032d5290440af986411033d5190440af582411027f6550440db949411036d
  | 23 => 0xe58021902de63d0240b758f40902bd65d0240cf597409039e63d0240af58f409039d63d0240a758f40902be62d0240cf54b40902be61d0240be597409037965d0240f698f40903d963d02409f98b535027d62d4d409f987535027d61d4d40d7d4e53502ef6254d40bb18953502f76154d40bd185535035d5314d409f988535027d6214d409f984535027d6114d409f997435035f5390d40d714e43502fa6090d40be582435035f5350d40d714d43502fb6050d40be181435027e6510d409f98f525027d63d49409f987525027d61d4940dbd4a52502df6354940b718d52502f76154940bd185525036d52149409f98c525027d63149409f984525027d61149409f99742502be65d0940cf997425023e65d0940cfd4f425033c52d0940af98342502bd6490940dbd4a425036c5290940be98242502f96090940dbd49425036c5250940bed8142502f86050940cfd4d42503af6250940ebd49425033c5250940eb14942503bb6050940af18142503b860509409f99442502be6410940eb508425027e65cc9409f597325027c65cc940dbd4b325036c52cc9409f996325027d658c9409f19632502be648c940af592325035f538c940d714e32502fa608c940be582325027f654c9409f995325027c654c9409f994325027d650c9409f19432502be640c940af590325035f530c940d714c325036f520c940db148325027e63d45409f58f515027e62d45409f58b51503775194540b7d8d51502dc6354540bbd8951502ec6254540dd544515027e63145409f58c515027e62145409f588515033f4214540cf508515027e65d0540bb98b41502ed62d0540ddd4641503745190540be98241502f96090540ddd4541503745150540bed8141502f860505409f99441502de6310540b758c415027e65cc5409f597315027c65cc540ddd47315037451cc5409f996315027d658c5409f196315035f538c540d714e315027f654c5409f995315027c654c540afd9131502bc644c540bbd8931502ec624c540bed8131502f8604c5409f994315027d650c5409f19431502be640c540af590315035f530c540d714c3150377510c540dd144315027e65c85409f597215027c65c8540af99321502bd64c8540ddd47215037451c85409f996215027d65885409f196215036f5288540db14a21503ad42885409fd95215027e65485409f195215027e65085409f594215027c6508540af99021502bd6408540dbd48215036c5208540eb50821503775108540dd14421502fa6008540be58021502de63d0140b758f40503da63d0140f658f40503bb42d0140ee50b405033f5390140af58a405033c5290140cf14640503bb5090140d798e541035d6395040bb98b53102ed62d4c40d7d4e531027e6294c409f58a531027e6194c409f586531027f6254c409f189531027f6154
  | 24 => 0x21d035d5388740db94a21d036d5288740eb50a21d027f65487409f59521d027c6548740d794d21d035d5348740bed8121d02f860487409fd9421d027e65087409f59421d02be6408740af59021d035e5308740d754c21d036e5208740db54821d03ad4208740dd94421d03755108740d7d4e539027e6294e409f58a539027e6194e409f586539027f6254e409f189539027f6154e409f185539035d5314e40af597439033d65d0e40cf94f43902be62d0e40af98743902bd60d0e40d794e439035d5390e40be98243902f96090e40d794d439035d5350e40bed8143902f86050e40e7d8d439033e5350e40e794d439039d5350e40af18943902bc6150e40afd8143903bb6050e40ee181439039d4310e40dbd4a529027e6394a409f58e529027e6194a409f586529027f6354a409f18d529033f4354a40cf50d529027f6154a409f185529036d5214a40db94a429036d5290a40be98242902f96090a40af58e42903ae5290a40cf54a42903ad5290a40af98642903ba6090a40af58242903b96090a40db949429036d5250a40bed8142902f86050a40af594429033d6510a40af58c42903ae6210a40cf54842902be6110a40af580429027f65cca409f997329027d65cca40af99332902bd64cca409fd96329027e658ca409f59632902bf648ca40af19232902fa608ca40be582329027f654ca409f595329027c654ca40afd9132902bc644ca409fd94329027e650ca409f59432902be640ca40af590329037751946409f98e519027d63946409f98a519027d6294640bbd8951902ec62546409fd8d519027c6354640cfd0d519033d43546409fd89519036f62546409bd89519027c6254640db189519026c6254640dd54451902ee62d0640bb58b41903765190640dd54641902fa6090640be58241902bd6390640cf94e41902be6290640cf54a41903b65190640cf54641903b55190640ee98241902bd6090640ee58241903765150640dd54541902fb6050640be18141902de6310640b758c41902bd6510640cf594419039e6310640af58c419039d6310640a758c419033e5310640af988419033d5210640ed984419033d5110640af580419027f65cc6409f997319027d65cc640af99331902bd64cc640e750f319027f658c6409f996319027d658c640afd9231902bc648c6409fd95319027d654c6409f19531902bf644c640af191319039d434c640bbd8931902ec624c640bed8131902f8604c6409fd94319027e650c6409f59431902be640c640af590319027f65c86409f997219027d65c8640af99321902bd64c86409fd96219027e65886409f59621902be6488640af59221903ae42886409fd95219027d65486409f19521902bf6448640af191219027f65086409f994219027d6508640afd9021902bc6408640eb90821902fa6008640b
  | 25 => 0x27d6294f409f98653d027d6194f40d719253d035f6294f40d798a53d035d6294f40d718a53d035f6194f40d798653d035d6194f40d718653d035f6094f40d758253d027f6254f409f18953d027f6154f409f18553d035f6554f40d799153d035f6254f40d798953d035d6254f40d718953d035f6154f40d798553d035d6154f40d718553d035f6054f40d758153d035d5314f40d794f43d035d53d0f40be98343d02f960d0f40d754e43d035e5350f40d794c43d035d5310f40be98043d02f96010f40b798f52d02dd63d4b40d794f52d035d53d4b40bd98752d02f561d4b40d794e52d035d5394b40dbd4a52d027e6394b409f58e52d027e6194b409f58652d035e5354b40d754d52d027f6354b409f18d52d027f6154b409f18552d02de6314b40b758c52d035e5314b40d754c52d036d5214b40d794f42d035d53d0b40db94b42d036d52d0b40be98342d02f960d0b40e794f42d033d53d0b40e754f42d031d53d0b40cf94b42d03ae52d0b40eb54b42d02be60d0b40ee98342d03b960d0b40d794e42d035d5390b40d794d42d035d5350b40afd9542d033f6550b40e794d42d033d5350b40e754d42d031d5350b40ebd8942d03af5250b40cf94942d03ac5250b40af18142d035e5310b40d754c42d036e5210b40db54842d03ad4210b40be98042d02f96010b409fd9732d027e65ccb409f59732d035e53ccb40d754f32d027f658cb409f99632d027d658cb40af99232d02bd648cb40d794e32d035d538cb409fd9532d027d654cb409f19532d035e534cb40d754d32d02fb604cb40be18132d027f650cb409f99432d027d650cb40af99032d02bd640cb40d794c32d035d530cb40b798f51d02dd63d4740d794f51d035d53d4740bb98b51d02ed62d4740d794e51d035d5394740ddd4651d027e63947409f58e51d027e62947409f58a51d033f4294740cf50a51d035e5354740d754d51d027f63547409f18d51d027f62547409f18951d02de6314740b758c51d035e5314740d754c51d03755114740d794f41d035d53d0740bb98b41d02ed62d0740dd94741d037551d0740be98341d02f960d0740d794e41d035d5390740d794d41d035d5350740b798c41d02dd6310740d794c41d035d5310740dd94441d03755110740be98041d02f960107409fd9731d027e65cc7409f59731d035e53cc740d754f31d027f658c7409f99631d027d658c740d794e31d035d538c7409fd9531d027d654c7409f19531d02bf644c740af19131d035e534c740d754d31d02ef624c740bb18931d02fb604c740be18131d027f650c7409f99431d027d650c740af99031d02bd640c740d794c31d035d530c7409fd9721d027e65c87409f59721d02be64c8740af59321d035e53c8740d754f21d037651c8740dd54721d027f65887409f99621d027d6588740d794e
  | 26 => 0x490821cf55242086f66190821bd586420876d65908219b59642086ed6490821db95242087ae5490821eb552420876c5490821bb98e42087e66190821bb58642087e56190821b958642086ee60908219fd95420873f5450821cf15142086ef6550821dbd9542087af6450821ebd51420876e5450821db15142087ac5450821bb18d42087af4350821eb50d42086ef6150821bb181420867f65108219f594420873e5410821cf55042086ee6210821eb50842086f66110821bd584420867d65cc821bb597320876d65cc821bbd9332086ed64cc821dbd4f320876d53cc821bb58732086ee60cc8219fd96320867d658c821d794e320875d538c821bb98a32086f6618c821bd586320867f654c8219fd94320867d650c821af99032086bd640c821d794c320875d530c821bd98432086f5610c821db594320866d650c821bbd9032087ae640c821bb59032087ad640c821ab59032086ee630c821f398c320876f530c821f394c320876d530c821f354c32087e6610c821bb58432087e5610c821b958432086ee600c8219f992510867d64944219f98e510867d6394421db90a510876d4294421dbcca510876c32944219f59741086ee62d0421bb58b410867f65904219f596410873e5490421cf55241086ee6290421bb58a41087ad42904219fd95410867f65104219f994410867d65104219f194410873e5410421cf55041086de6310421b758c41086ee6210421bb58841087ad4210421ed504410867d65cc4219fd96310867d658c421d794e310875d538c421bb98a31086ed628c4219fd9531086bf644c421af19131086ef624c421bb18931086fb604c421be181310867f650c4219f994310867d650c4219f19431086be640c421af590310875e530c421d754c31086ee620c421bb58831087d5310c421af99321086bd64c8421bbd9321087ae64c8421bb59321087ad64c8421ab59321086ee63c8421bb18f21086ee60c8421bb58a210876e5288421bd58a21087765288421f994a21087e64288421f950a21087e73288421f90ca21086f660884219fd9521086ef6548421dbd95210866f6548421bbd9121086ed6448421bb98d21086ec6348421bbd85210876e5148421f9d0521087e44148421f98c521087e53148421bb18121086f76548421ddd9521086776548421bdd8921087e76248421dd94921087e65248421f9d0921087e44248421f98c921087e53248421bd181210877b50940219f992500867d64940219f98e500867d6394021afd9150086bc6454021b7d8d50086dc63540219fd91500873f64540218fd91500867c6454021cf191500863c64540219fd8d500875f635402197d8d500867c6354021d718d500865c6354021db909500876d4254021af99050086bd6414021b798c50086dd6314021de540500875f5394f409f98a53d0
  | 27 => 0x21bdd8542486f461509219f994424867e65cc921d7d4f324875c53cc921bd98732486f561cc9219f996324867c654c921d7d4d324875c534c921bdd8532486f4614c9219f99432486be640c921af590324867e65d0521cfd53414873c54d0521bb98b41486ed62d05219f996414873e5490521cf552414867f65505219f595414867c6550521cfd51414873c5450521bbd8941486ec62505219f994414873e5410521cf55041486de6310521b758c414867e65cc521d7d4f314875c53cc521bb98b31486ed62cc5219f996314867f654c5219f595314867c654c521afd9131486bc644c521d7d4d314875c534c521bbd8931486ec624c521bed8131486f8604c5219f99431486be640c521af59031486be64c8521af59321487b664c8521ed593214876f5488521db552214876e5388521db14e21487e751885219f993504867d64d41219f98f504867d63d4121ded4250486bf6454121af19150486df6354121b718d504877950141219f990504867d64141219f98c504867d6314121ddc84504876e21141219f98f540867d63d50219f98b540876e62d50219f987540877661d50219f983540867d60d50219f596540873f54950219f98e540867d6395021db98a540867e60950219f582540873f64550219fd8d540867c63550219fd81540867c6055021cf55054086de6315021b758c54086fa6015021be580540867e6415021cf990540867e6315021d798c540865e63150219f58c540875d63150219758c540867e6215021db988540867e6115021dd984540867e6015021de980540867a60150219f580540877960150219e580540867e64d4c219f593530867e62d4c21db98b530867e61d4c21dd987530867e60d4c219f583530867d6594c21d7d4e530867e6494c219f592530867e6094c219f582530867f6454c219f191530875f6354c21db189530867f6054c219f18153086be6414c21af590530875d5314c21be98053086f96014c219f990530873e6414c218f990530867d6414c21cf590530863d6414c219f98c530875e6314c219f988530876e6214c219f98453087766114c219f980530877a6014c219e980530867d6014c21de58053086796014c219fd97430867e65d0c219f597430867c65d0c21cf953430873d54d0c21bb98b43086ed62d0c219fd96430867e6590c219f596430867c6590c21d794e430875d5390c219fd95430867e6550c219f595430867c6550c21cf951430873d5450c21d794d430875d5350c21bbd8943086ec6250c21bdd8543086f46150c219fd94430867e6510c219f594430867c6510c21bb98843086ed6210c21bd98443086f56110c219f992520873e64948218f992520867d6494821cf592520863d64948219f98e520867d63948219f597420873f54d0821cf153420867f65908219f596420873e5
  | 28 => 0x54f32887cd53cca21f998732886ed61cca21f958732886ee60cca21d794d328875d534ca21bdd8532886f4614ca21af99032886bd640ca21bb594328876d650ca21bbd9032887ae640ca21bb59032887ad640ca21ab59032887ce630ca21dbd4c328876d530ca21bb58432886ee600ca21bb98b41886ed62d0621cf952418873d5490621bb98a41886ed6290621eb50a418873e5410621cf55041886de6310621b758c41886ee6210621bb58841887ad4210621d794e318875d538c621bb98a31886ed628c621afd9131886bc644c621bbd8931886ec624c621bed8131886f8604c621af99031886bd640c621d794c318875d530c621bb98831886ed620c621af99321886bd64c8621bb597218876d65c8621bbd9321887ae64c8621bb59321887ad64c8621ab59321886ee63c8621bb18f21886ee60c8621bd597218877565c8621ed99321887b564c8621af99350886bd64d4221b798f50886dd63d4221ded42508867e64942219f592508867e63942219f58e508877721942219fd91508867c64542219fd8d508867c6354221db909508876d4254221de540508867e63d51219f58f544867e60d51219f583544873f54951219f992544867e63951219f58e544867d6295121db58a544866d62951219f586544877561951219f982544867d6095121b7d8d54486dc6355121bed8154486f86055121cfd91544867f6355121d7d8d544865f63551219f18d544875c63551219718d544867f6255121dbd89544867f6155121ddd85544867f6055121ded81544867b60551219f181544877860551219e181544867e6515121cf550544873e64151219f98c544867d63151219f980544867d60151219f993534867d64d4d219f983534867d60d4d21d7d4e534867e6494d219f592534867e6394d219f58a534876d6294d219f58653487756194d219f982534867d6094d21afd9153486bc6454d21bed8153486f86054d219fd91534873f6454d218fd91534867c6454d21cf191534863c6454d21d7d8d534867f6254d21dbd89534866f6254d219fd8553487776154d219fd81534877b6054d219ed81534867c6054d21de18153486786054d219f99453486be6414d21af590534875d5314d219f990534873e6414d218f990534867d6414d21cf590534863d6414d21d798c534867e6014d219f580534867f65d0d219f997434867d65d0d219f197434873e54d0d21cf553434875f53d0d21d714f434867f6590d219f996434867d6590d219f196434873f5490d21cf152434867f6550d219f995434867d6550d219f195434873e5450d21cf551434867f6510d219f994434867d6510d219f194434873f5410d21cf150434875f5310d21d714c434867e65d0921cfd53424873c54d0921bd98742486f561d09219f996424867c6550921cfd51424873c54509
  | 29 => 0x2c873d5450b21cf95042c873d5410b21bd98442c86f56110b21cf95332c873d54ccb21cf95232c873d548cb21d794e32c875d538cb21bd98632c86f5618cb21cf95132c873d544cb21af99032c86bd640cb21cf95032c873d540cb21d794c32c875d530cb21bd98432c86f5610cb21cf95341c873d54d0721bb98b41c86ed62d0721cf95241c873d5490721cf95141c873d5450721bbd8941c86ec6250721cf95041c873d5410721b798c41c86dd6310721ed50441c873e54cc721cf55331c875e53cc721d754f31c86ee62cc721bb58b31c873e548c721cf55231c86bf644c721af19131c873e544c721cf55131c875e534c721d754d31c86ef624c721bb18931c86fb604c721be18131c86be640c721af59031c873e540c721cf55031c87d5310c721af99350c86bd64d4321cf95350c873d54d4321b798f50c86dd63d4321cf95250c873d5494321ded4250c867e64943219f59250c867e63943219f58e50c873e5454321cf55150c867f64543219f19150c867f63543219f18d50c86be6414321af59050c873e5414321cf55050c877950143219f98f548867d63d5221db58b548877661d52219f983548867d60d5221cfd52548867e63952219f58e548876d62952219f982548867d6095221cfd91548867f63552219f18d548867f60552219f181548873d5415221b798c54886dd6315221cf990548867e6315221d798c548865e63152219f58c548875d63152219758c548876d6215221dd984548867e60152219f580548867e64d4e219f593538876d62d4e21dd987538867e60d4e219f583538875f5394e219f992538867d6494e219f982538867d6094e219fd91538867c6454e21d7d8d538876f6254e219fd81538867c6054e21af99053886bd6414e21d754c538867e6414e21cf990538863e6414e219f590538873d6414e218f590538875e6314e21db58853887766114e219f980538867d6014e219fd97438867e65d0e219f597438867c65d0e21cf953438873d54d0e21bb98b43886ed62d0e219fd96438867e6590e219f596438867c6590e21d794e438875d5390e219fd95438867e6550e219f595438867c6550e21cf951438873d5450e21d794d438875d5350e21bbd8943886ec6250e219fd94438867e6510e219f594438867c6510e21bb98843886ed6210e21cf953428873d54d0a21bd98742886f561d0a21bb596428876d6590a21db952428876c5490a21bb98e42886ed6190a21bb982428873e5450a21cf55142886f76150a21bd185428876f6550a21ebd91428876e5450a21eb95142887ad5450a21db15142886ec6350a21ebd0d42887ad4350a21bbd8542887e76150a21f918542886ec6050a21eb508428875e53cca21d754f32886f661cca21bd587328876d65cca21bbd9332886ed64cca21dbd4f32887ce53cca21db
  | 30 => 0xde60cc431cf952310c73d548c431b758e310c75e538c431ed952310c7b5548c431bd58e310c776538c431f594e310c67f654c431afd91310c6bc644c431cf951310c73d544c431bbd89310c6ec624c431bed81310c6f8604c431b7d95310c75f654c43197d95310c79f644c431e7191310c75f544c431e7951310c75d544c431e7551310c71d544c431f3d89310c7cc624c431b7d85310c75e514c431f5d05310c7d4414c431f6d81310c6dc604c431f6181310c6d8604c431bdd95310c777654c4319dd95310c7b7644c431ed191310c7b6544c431ed551310c6f7634c431f5d8d310c776534c431f594d310c7d7434c431f510d310c7e7624c431f9189310c7d6324c431f50c9310c7f3604c431fc181310c6be64d4031af593500c73e54d4031cf553500c73e5494031cf552500c77b50940319f992500c67d64940319f98a500c67d6294031cf951500c73d54540319fd91500c67c64540319fd89500c67c6254031af990500c6bd6414031cf950500c73d5414031bb988500c6ed6214031de540500c67e63d53219f58f54c876e62d5321dd58754c867e60d53219f58354c873f54953219f98e54c867d63953219f98254c867d6095321cfd8e54c873e6395321cf58e54c873c6395321cf98a54c873c6295321cfd8654c873d6195321cfd8254c873e6095321cf58254c873c6095321cfd9154c867f63553219f18d54c867f60553219f18154c873f6555321cfd8d54c873e6355321cf58d54c873c6355321cf98954c873c6255321cfd8554c873d6155321cfd8154c873e6055321cf58154c873c6055321cf55054c873e64153219f98c54c867d6315321db98854c877561153219f98054c867d6015321af99353c86bd64d4f21cf95353c873d54d4f21be98353c86f960d4f219f99353c873e64d4f218f99353c867d64d4f21cf59353c863d64d4f21db98b53c877561d4f219f98353c877a60d4f219e98353c867d60d4f21de58353c867960d4f21cf95253c873d5494f21d7d4e53c867e6494f219f59253c867e6094f219f58253c873e5454f21cf55153c867f6454f219f19153c875f6354f219fd8153c867c6054f21af99053c86bd6414f21cf95053c873d5414f21d754c53c867e6414f21cf99053c863e6414f219f59053c873d6414f218f59053c875e6314f21db98853c87756114f219f98053c867d6014f219fd9743c867e65d0f219f59743c867c65d0f21cf95343c873d54d0f219fd9643c867e6590f219f59643c867c6590f21cf95243c873d5490f219fd9543c867e6550f219f59543c867c6550f21cf95143c873d5450f21bdd8543c86f46150f219fd9443c867e6510f219f59443c867c6510f21cf95043c873d5410f21bd98443c86f56110f21cf95342c873d54d0b21cf95242c873d5490b21bd98642c86f56190b21cf9514
  | 31 => 0x14131fccc4504c7da3114131ded90504c77a6414131de590504c7786414131ded8c504c77b4314131de90c504c75a4314131de50c504c7594314131de10c504c77b6214131de988504c7796214131de188504c77b4214131de908504c7794214131de108504c77b3214131de8c8504c7793214131de0c8504c77b6114131ded04504c77a4114131de504504c7784114131decc4504c77a3114131d68c4504c77931141319f98f540c75e63d50319f98b540c67d62d50319f987540c77661d50319f983540c67d60d50319f596540c73f54950319f98a540c67d62950319f982540c67d60950318f596540c73e6395031cf18e540c73f6295031cf98a540c73d6295031cf18a540c73e6195031cf186540c73f6095031cf982540c73d6095031cf182540c73f64550319fd89540c67c62550319fd81540c67c6055031cfd95540c73e6355031cf18d540c73f6255031cf989540c73d6255031cf189540c73e6155031cf185540c73c3155031cfd81540c73e6055031cf581540c73c6055031af990540c73d54150319f990540c73e64150318f990540c67e6315031d798c540c65e63150319f988540c67d62150319f984540c77661150319f980540c67d60150319f992530c67d6494c319f597430c73e54d0c31cf553430c67f6590c319f596430c73e5490c31cf552430c75e5390c31bd986430c6f56190c319fd95430c73e5450c31cf551430c75e5350c319fd94430c67d6510c31cf950430c73d5410c31bd984430c6f56110c31af993520c6bd64d4831cf953520c73d54d4831cf952520c73d5494831dbd4a520c67e64948319f592520c67e60948319f582520c73e5454831cf551520c67f64548319f191520c67f60548319f181520c6be6414831af590520c73e5414831cf550520c76d5214831be980520c6f960148319fd97420c67e65d08319f597420c73e54d0831cf553420c67f65908319f996420c67d6590831cf952420c73d54908319fd95420c67d65508319f195420c73e5450831cf551420c6df6350831b718d420c6f76150831bd185420c67f65108319f994420c67d6510831cf950420c73d5410831cf953320c73d54cc831db94b320c76d52cc831bd987320c6f561cc8319f596320c73e548c831cf552320c67f654c831cf951320c73d544c831af990320c6bd640c831cf950320c73d540c831db948320c76d520c831bd984320c6f5610c8319f992510c67d64944319f597410c73e54d0431cf553410c6ee62d0431bb58b410c67f65904319f596410c73e5490431cf552410c6de6390431b758e410c67f6550431cf951410c73d54504319fd94410c67e65104319f594410c67c6510431cf950410c73d5410431b798c410c6dd6310431cf953310c73d54cc431d7d53310c79e54cc431d7553310c79d54cc431c7553310c6
  | 32 => 0x19f197424c73f54d0931cf153424c6de63d0931b758f424c79d43d0931dbd4b424c76c52d0931bd987424c6f561d09319f996424c67d65909319f196424c73f5490931cf152424c76f5290931db14a424c67f65509319f995424c67c6550931cfd51424c73c5450931e750d424c76f5250931db149424c67e65109319f594424c67c6510931cfd50424c73c5410931b798c424c6dd6310931dbd48424c76c52109319f997324c73f54cc931cf153324c76c52cc931cfd52324c73c548c931dbd4a324c76c528c931bd986324c6f5618c931cfd51324c73c544c931dbd49324c76c524c931bdd85324c6f4614c9319f994324c6be640c931af590324c73f540c931cf150324c76f520c9319f997414c73f54d0531cf153414c6de63d0531b758f414c79d43d0531bb98b414c6ed62d0531dbd4b414c76c52d05319f996414c73f5490531cf152414c79e4390531dbd4a414c76c52905319fd95414c67d65505319f195414c73f5450531cf151414c6df6350531b718d414c79d4350531dbd49414c76c52505319f994414c73f5410531cf150414c6de6310531b758c414c79e4310531dbd48414c76c5210531cfd53314c73c54cc531dbd4b314c76c52cc531edd53314c7b454cc531f590f314c7d543cc531f9d4b314c7e452cc531cfd52314c73c548c531dbd4a314c76c528c531b7d92314c6dd648c531e7d52314c79c548c531f3d4a314c7cc528c531f5d46314c73f54d4131cf153504c76f52d4131db14b504c67e64d41319f593504c67e62d41319f58b504c77b54d4131eed53504c73b54d4131de953504c77954d4131de153504c7b854d4131ce153504c7da43d4131f650f504c77b52d4131fad4b504c76b52d4131de94b504c77952d4131de14b504c7e852d4131da14b504c7f331d4131f68c7504c77b64d4131de993504c77964d4131de193504c77b63d4131ded0f504c77a43d4131de50f504c77843d4131ded8b504c77a62d4131de58b504c77862d4131ded0b504c77a42d4131de50b504c77842d4131deccb504c77a32d4131de4cb504c77832d4131ded87504c77b41d4131de907504c77941d4131de107504c77b31d4131de8c7504c6be6494131af592504c73f5494131cf152504c6ee6294131bb58a504c76f5294131db14a504c77b5094131afd91504c6bc6454131cfd51504c73c5454131bbd89504c6ec6254131dbd49504c76c5254131cfd50504c73c5414131dbd48504c76c5214131de540504c67e64141319f590504c75e4314131d750c504c67e62141319f588504c75e3114131be994504c77a6514131ded50504c7bb5414131ced50504c77a5414131de550504c7785414131ee150504c7385414131f690c504c7d94314131ded48504c7eb5214131dad48504c77a5214131de548504c7785214131fa148504c76852
  | 33 => 0x91508c67f6454231cfd91508c63f64542319f191508c73c64542318f191508c67f62542319f189508c77950142319f98b544c67d62d51319f983544c67d60d5131e7d8f544c73f63d5131cf58f544c73f62d5131cf98b544c73d62d5131cf18b544c73f61d5131cf587544c73f60d5131cf983544c73d60d5131cf183544c73f5495131bb98a544c6ed6295131be982544c6f960951319f992544c63e64951319f58e544c75d63951319f98a544c76e62951319b98a544c67d6295131db58a544c66d62951319f586544c77561951319f982544c77a60951319e982544c67d6095131de582544c6796095131bbd89544c6ec6255131bed81544c6f86055131cfd91544c67f6355131d7d8d544c67f6255131dbd89544c66f62551319f189544c76c62551319b189544c67f6155131ddd85544c67f6055131ded81544c67b60551319f181544c77860551319e181544c67e6515131cf550544c73e6415131d758c544c67e62151319f588544c67e60151319f580544c6be6515131cf994544c63e6515131e758c544c73f6315131cf58c544c71d6315131cfd88544c73e6215131cf588544c73c6215131cfd84544c73d6115131cf4c4544c73f6015131cf980544c73d6015131cf180544c67e65d0d31cfd53434c73c54d0d31bd987434c6f561d0d319f996434c73f5490d31cf152434c6de6590d31d7996434c6dd6490d31e7d52434c75e5490d31d7152434c79c5490d31c7152434c6de6190d319f195434c73f5450d31cf151434c6f76150d31bd185434c75c6550d3197195434c79f6450d31e7d51434c75e5450d31d7151434c79c5450d31f5d85434c6dc6150d31f5185434c6d46150d319f994434c73f5410d31cf150434c6de6310d31e750c434c73f54d4931cf153524c67e64d49319f593524c67e60d49319f583524c76f54d4931ebd53524c72f54d4931db953524c76d54d4931db153524c7ac54d4931cb153524c7ce43d4931f350f524c76f64d4931db993524c76d64d4931db193524c76f63d4931dbd0f524c76e43d4931db50f524c76c43d4931dbd87524c76d61d4931dbd83524c76e60d4931db583524c76c60d4931af992524c6bd6494931cfd52524c73c5494931dbd4a524c6fa6094931be582524c6bf6454931af191524c73f5454931cf151524c6fb6054931be181524c73f5414931cf150524c76d52149319f990524c67d64149319f980524c67d6014931bb994524c76e6514931dbd50524c7af5414931cbd50524c76e5414931db550524c76c5414931eb150524c72c5414931f390c524c7cd4314931dbd90524c76e6414931db590524c76c6414931dbd8c524c76f4314931db90c524c76d4314931db10c524c76f6114931db584524c76d3114931dbd80524c76e6014931db580524c76c60149319f997424c67d65d093
  | 34 => 0xcc79d5490f31d715243cc6de6190f31f598643cc7d56190f31cfd5143cc73c5450f31b7d9543cc75f6550f31e7d9143cc79f5450f31d795143cc75c5450f31e715143cc6dc6150f31cf95043cc73d5410f31e750c43cc6f66110f31bd58443cc76f5294b319f99252cc67d6494b319f98252cc67d6094b319fd9152cc67c6454b319fd8152cc67c6054b31af99052cc6bd6414b31db54852cc67f65d0b319f99742cc67d65d0b31cf95342cc73d54d0b31b798f42cc6dd63d0b31e750f42cc67f6590b319f99642cc67d6590b31db94a42cc76d5290b319fd9542cc67d6550b319f19542cc73e5450b31cf55142cc79d4350b31db94942cc76d5250b31bdd8542cc6f46150b319fd9442cc67e6510b319f59442cc6de6310b31b758c42cc76e52ccb31db54b32cc6f661ccb31bd58732cc6be640cb31af59032cc76e520cb31db54832cc6f6610cb31bd58432cc73e54d0731cf55341cc6de63d0731b758f41cc79d43d0731bb98b41cc6ed62d0731cfd5241cc73c5490731e790e41cc73e5450731cf55141cc6df6350731b718d41cc79d4350731cfd5041cc73c5410731b798c41cc6dd6310731e790c41cc6be64d4331af59350cc6ee62d4331bb58b50cc77b50943319f99250cc67d6494331d790e50cc75d43943319f98a50cc67d62943319fd9150cc67c64543319fd8950cc67c6254331de54050cc75d63d52319f98b548c67d62d5231dd987548c67e60d52319f583548c73f54952319f98a548c67d62952319f982548c67d6095231cfd91548c67f62552319f189548c67f60552319f181548c73d5415231cf990548c75d63152319f988548c67d6215231dd984548c67e60152319f580548c73e54d0e31cf553438c6f661d0e31bd587438c73f5490e31cf152438c73e5450e31cf551438c6f76150e31bd185438c73f5410e31cf150438c6be6494a31af592528c76f5294a319f992528c73e6494a318f992528c67d6494a31cf592528c63d6494a319f982528c67d6094a319fd91528c67c6454a319fd81528c67c6054a31db548528c67f65d0a319f997428c67d65d0a31cfd53428c73c54d0a31bd987428c6f561d0a319fd96428c67e6590a319f596428c67f6550a319f595428c67c6550a31cfd51428c73c5450a31b7d8d428c6dc6350a319fd94428c67e6510a319f594428c76e528ca31db54a328c6f6618ca31bd586328c76e524ca31db549328c6f7614ca31bd185328c6be640ca31af590328c73f54d0631cf153418c6ee62d0631bb58b418c73e5490631cf552418c6de6390631b758e418c73f5450631cf151418c73e5410631cf550418c6de6310631b758c418c6dd65cc631d7597318c75f54cc631d7553318c6de60cc631bd597318c77565cc631ded42508c67e64942319f592508c67e62942319f58a508c6bf6454231af1
  | 35 => 0xd63948419f982521067d6094841d794d521075d53548419fd8d521067c63548419fd81521067c6054841b798c52106dd6314841d794c521075d5314841db54852106fa6014841be580521075e53d0841d754f421076e52d0841db54b42106f661d0841bd58742106be63d0841e794f421073d53d0841e754f421071d53d0841cf94b42107ae52d0841eb54b42107b661d0841af58742107b561d0841ad58742106be60d08419f59642106bd6490841d794e421075d53908419fd95421075e5350841d754d42106bf6550841cfd9542106bc6350841e794d421073d5350841e754d421071d5350841ebd8942107af5250841cf94942107ac5250841afd8542106bc6050841af990421075e5310841d754c421076e5210841db54842107ad4210841bd98442106f561108419fd97321067e65cc8419f59732106bf64cc841af193321075e53cc841d754f321067f658c8419f996321067d658c841af99232106bd648c841d794e321075d538c8419fd95321067d654c8419f19532106bf644c841af191321075e534c841d754d32106f7614c841bd185321067f650c8419f994321067d650c841af99032106bd640c841d794c321075d530c841cf90e511073c4394441cfd0a511073d4294441d794f411075d53d0441bb98b41106ed62d0441af98f411079e53d0441cf54f411079d53d0441c754f41107ae62d0441af58b41107ad62d0441ab58b41106be60d0441af592411073e5490441d794e411075d5390441bd59241107765490441ed95241107d65390441f554e41107b64390441ed10e41107b74290441ed50a411067f6550441d794d411075d5350441afd95411073f65504418fd9541106bc6350441e794d411073d5350441e754d411071d5350441afd8941106bf6150441cf94541106bc6050441bdd95411077765504419dd9541106f76450441edd9141107765450441ed95141107d65350441f554d41107b64250441ed10941106de63d4041b758f501075e53d4041d754f501075e5394041d754e501077b50940419f98e501067d63940419f98a501067d6294041d794d501075d53540419fd8d501067c63540419fd89501067c6254041cfd09501073d4254041b798c50106dd6314041d794c501075d5314041bb98850106ed6214041de540501075e63d53319f98b54cc67d62d5331dd58754cc67e60d53319f58354cc73f5495331d798e54cc67e62953319f58a54cc67e60953319f58254cc73f64553319fd8954cc67c62553319fd8154cc67c6055331cf55054cc6ee6215331bb58854cc73e6415331d798c54cc67e6215331db98854cc66e62153319f58854cc76d62153319b58854cc77561153319f98054cc67d6015331cfd5343cc73c54d0f31cf95243cc73d5490f31bd98643cc6f56190f31d759643cc75e5490f31e795243
  | 36 => 0x42419f58a50906df6354241b718d509067f6354241d7d8d509065f63542419f18d509075c63542419718d509067f62542419f189509073f4254241cf509509077950142419f98b535067d62d4d419f983535067d60d4d41d7d4e53506ef6254d41bb18953506fb6054d41be181535075d5314d419f988535067d6214d419f980535067d6014d419f99743506be65d0d41cf997435063e65d0d41cf14f43506be61d0d41af592435075f5390d41d714e43506f66190d41bd586435075f5350d41d714d43506f76150d41bd185435079f6350d41e7d4d435073c5350d41e714d43507b76150d41af18543507b46150d419f99443506be6410d41e750c435067e63d49419f58f525073f43d4941cf50f525067e60d49419f583525076f5294941b7d8d52506dc6354941bed8152506f86054941db548525067e63149419f58c525067e60149419f580525067e65d0941dbd4a425076c5290941bd98642506f56190941dbd49425076c5250941bdd8542506f461509419f994425067e65cc9419f597325067c65cc941af99332506bd64cc941dbd4b325076c52cc941bd98732506f561cc9419f996325067d658c9419f196325075f538c941d714e325067f654c9419f995325067c654c9419f994325067d650c9419f19432506be640c941af590325075f530c941d714c325076f520c941db14832506ee62d0541bb58b41507b743d0541ed50f41507e662d0541f958b41506bd6390541cf14e415073f5290541edd46415067e63d41419f58f505067e62d41419f58b505077b5094141b7d8d50506dc6354141bbd8950506ec6254141de540505067e63141419f58c505073f4314141cf50c505067e62141419f588505073e4114141db98a541076d6295041d7d4e531067e6294c419f58a531067e6094c419f582531079c6494c41d7192531075f6294c41d798a531075d6294c41d718a531075e6194c41d7186531075f6094c41d7982531075d6094c41d7182531067f6254c419f189531067f6054c419f181531075f6554c41e7191531075e6454c41d7d89531075e6254c41d7589531075c6254c41d7985531075c6154c41d7105531075f6054c41d7981531075d6054c41d718153106de6314c41d754c531073e54d0c41d794f431075d53d0c41bd98743106f561d0c419f596431075d5390c41af596431073d6590c418f59643106be6390c41e794e431073d5390c41e754e431071d5390c41af58a43106bd6190c41af982431067f6550c41cf951431075e5350c41d794c431075d5310c41bd98443106f56110c41af98c431079e6310c41e794c431073d5310c41e754c431071d5310c41af58843107b66110c41af58443107b56110c41af98043106de63d4841b758f521075e53d4841d754f521075e5394841d754e521076f52948419f98e521067
  | 37 => 0xdb98e52d076d6394b41db18e52d076f4394b41db90e52d076d4394b41db10e52d076f6194b41db58652d076f6094b41db98252d076d6094b41db18252d067f6354b419f18d52d073f4354b41cf50d52d067f6054b419f18152d076f6554b41dbd4d52d076e5354b41db54d52d076c5354b41ebd0d52d07ad4354b41db99152d076f6354b41db98d52d076d6354b41db18d52d076f4354b41cbd0d52d076e4354b41db50d52d072d4354b41db10d52d076f6154b41db58552d076f6054b41db98152d076d6054b41db18152d076d5214b41db94b42d076d52d0b41bd98742d06f561d0b41db54a42d076e5250b41db94842d076d5210b41bd98442d06f56110b419fd9732d067e65ccb419f59732d06be64ccb41af59332d076e52ccb41db54b32d067f658cb419f99632d067d658cb41db94a32d076d528cb419fd9532d067d654cb419f19532d076e524cb41db54932d06f7614cb41bd18532d067f650cb419f99432d067d650cb41af99032d06bd640cb41db94832d076d520cb41b798f50d06dd63d4341bb98b50d06ed62d4341db94b50d076d52d4341db94a50d076d5294341ded4250d067e63943419f58e50d073f4394341cf50e50d067e62943419f58a50d076e5254341db54950d067f63543419f18d50d067f62543419f18950d06ee6214341bb58850d076e5214341db54850d07795014341d7d4e539067e6294e419f58a539067e6094e419f582539067f6254e419f189539067f6054e419f181539075d5314e41d794e439075d5390e41bd98643906f56190e41e794e439073d5390e41e754e43906bd6290e41ed98643906bd6190e41ed58643906be6090e41d794d439075d5350e41bdd8543906f46150e41af594439073d6510e41e798c439073d5310e41af58843906bd6110e41af980439076f5294a419f98e529067d6394a419f982529067d6094a419fd8d529067c6354a419fd81529067c6054a41db54852906bd65d0a41cf59742906be63d0a41cf54f429073e52d0a41af58742906be60d0a41db94a429076d5290a41bd98642906f56190a41db949429076d5250a41bdd8542906f46150a41af18d429073d5350a41ebd89429073e5250a41eb94942907ad5250a41afd8542907b76150a41ed18542906bc6050a41eb508429067f65cca419f997329067d65cca41afd9332906bc64cca41bd98732906f561cca419fd96329067e658ca419f59632906be648ca41af592329067f654ca419f595329067c654ca41afd9132906bc644ca419fd94329067e650ca419f59432906be640ca41af59032906ee62d0641bb58b41906bd65d0641cf59741906be63d0641cf54f41907ae62d0641af58b41907ad62d0641ab58b41906be60d0641bd597419077565d0641f998b41907e562d0641ded42509067e63942419f58e509067e629
  | 38 => 0x2540cb3f64550329fd85540ca7c61550329fd81540ca7c6055032cfd95540cb3e6355032cf18d540cb3e6255032cf189540cb3c3255032cfd85540cb3e6155032cf585540cb3c6155032cfd81540cb3e6055032cf581540cb3c6055032af990540cb3d54150329f990540cb3e64150328f990540ca7e6315032d798c540ca7e6215032db988540ca7e61150329f584540ca7e60150329f580540ca7e6494c329f592530ca7d65d0c32cf953430cb3d54d0c329fd96430ca7d6590c32cf952430cb3d5490c32bb98a430caed6290c329fd95430cb3e5450c32cf551430ca7f6510c329f594430cb3e5410c32cf550430cb9d4310c32bb988430caed6210c329f992520ca7d64948329f597420cb3e54d0832cf553420ca7f65908329f596420cb3e5490832cf552420cade6390832b758e420ca7f6550832cf951420cb3d54508329fd94420ca7e65108329f594420ca7c6510832cf950420cb3d5410832b798c420cadd6310832eb508420cb3e54cc832cf553320cb9e54cc832e7553320cade60cc832cf952320cb3d548c832b758e320cb5e538c832eb952320cbad548c832bb58e320cb6e538c832f394e320caee618c8329fd95320cb3e544c832cf551320cadf654c832d7d95320ca5f654c832e7951320cb9d544c832b7d89320cb5e524c832f3d09320cbcc424c832b7181320caef654c832dbd95320ca6f654c832eb951320cbad544c832bbd8d320cbcf634c832db94d320cbce534c832f3d0d320cbcc434c832bb185320cabe64d4432af593510cb3e54d4432cf553510cb3e5494432cf552510cb7751944329f992510ca7d64944329f982510ca7d6094432cf951510cb3d54544329fd91510ca7c64544329fd81510ca7c6054432af990510cabd6414432cf950510cb3d5414432dd544510cafa6014432be580510cabe64d4032af593500cb3e54d4032cf553500cb3e5494032cf552500cb7b50940329f992500ca7d64940329f986500ca7d6194032cf951500cb3d54540329fd91500ca7c64540329fd85500ca7c6154032af990500cabd6414032cf950500cb3d5414032bd984500caf56114032de540500caee62d4f41bb58b53d06fa60d4f41be58353d075f5394f419f98a53d067d6294f419f98253d067d6094f419fd8953d067c6254f419fd8153d067c6054f41d754c53d06ee6214f41bb58853d075e53d0f41d754f43d06f661d0f41bd58743d073e53d0f41e794f43d079d53d0f41af98743d07b661d0f41ed58743d06bf6550f41cfd9543d079f6350f41e7d4d43d073e5350f41e714d43d06bc6150f41d794c43d075d5310f41e750c43d06f66110f41bd58443d076f5294b419f98e52d067d6394b419f98252d067d6094b41dbd4e52d076e5394b41db54e52d076c5394b41ebd0e52d07ad4394b41db19252d076f6394b41
  | 39 => 0xcb795014332d758f548cb6e62d52329f987548ca7d61d52329f983548ca7d60d5232cfd52548ca7e61952329f586548ca7e60952329f582548cb3f64552329fd85548ca7c61552329fd81548ca7c6055232cf550548cafa6015232be580548cb3e6415232d758c548cb6e62152329f984548ca7d61152329f980548cb7a60152329e980548ca7d6015232de580548ca796015232cf953438cb3d54d0e32bb98b438caed62d0e32cf951438cb3d5450e32bbd89438caec6250e32e750c438cb3f54d0a32cf153428cb3e5490a32cf552428cade6390a32b758e428cb3f5450a32cf151428cb3e5410a32cf550428cade6310a32b758c428cadd65cca32d7597328cade60cca32bb597328cb6d65cca32af993518cabd64d4632be983518caf960d4632ddd46518ca7e64946329f592518cb6f32946329f982518ca7d60946329fd91518ca7c64546329fd81518ca7c6054632dd544518cb7b50942329f992508ca7d64942329f986508ca7d6194232afd91508cabc64542329fd91508cb3f64542328fd91508ca7c6454232cf191508ca3c64542329fd85508ca7c6154232af990508cabd6414232de540508ca7e61d51329f587544ca7e60d51329f583544cb3f54951329f992544ca7d6395132d758e544ca7d6295132db58a544ca7e61951329f586544ca7e60951329f582544caf76155132bd185544cafb6055132be181544cb3f64551329fd8d544cb5f63551329fd89544cb6f62551329fd85544cb7761551329dd85544ca7c6155132dd185544ca7461551329fd81544cb7b60551329ed81544ca7c6055132de181544ca7860551329f994544cb3d5415132cf990544ca7e61151329f584544ca7e60151329f580544ca7e65d0d32cfd53434cb3c54d0d32bb98b434caed62d0d329f996434ca7c6550d32cfd51434cb3c5450d32bbd89434caec6250d329f994434ca7e65d0932cfd53424cb3c54d0932b798f424cadd63d09329f996424ca7f65509329f595424ca7c6550932cfd51424cb3c5450932b7d8d424cadc63509329f994424cbcf528c9329f993514ca7d64d45329f983514ca7d60d4532ddd46514cabf6454532af191514cafb6054532be181514cb7551145329f990514ca7d6414532dbcc8514ca7e60145329f580514ca7e64d41329f593504ca7e61d41329f587504cb7b5094132afd91504cabc6454132bdd85504caf46154132de540504ca7e64141329f590504cb5e32141329f984504ca7d61141329f98f540cb5e63d50329f98b540cb6e62d50329f987540ca7d61d50329f983540ca7d60d50329f596540cb3f54950329f986540ca7d61950329f982540ca7d60950328f596540cb3e6395032cf18e540cb3e6295032cf18a540cb3f6195032cf986540cb3d6195032cf186540cb3f6095032cf982540cb3d6095032cf18
  | 40 => 0x5350d42c714d4350baf6250d42af1894350bac6250d42ab1894350abc6150d42afd814350a7e6510d42af9904350baf43d0942eb50f4250aee61d0942bb5834250abd6390942ebd4a4250abe6190942af5824250a7e63d45429f58f5150b3f43d4542cf50f5150a7e60d45429f5835150b775194542b7d8d5150adc6354542bed815150af86054542dd5445150a7e63145429f58c5150a7e60145429f5805150a7e63d41429f58f5050a7e61d41429f5875050b7b5094142b7d8d5050adc6354142bdd855050af46154142de5405050a7e63141429f58c5050b3f4314142cf50c5050b3e42141429f9845050a7d6114142be9835310af960d4c42d7d4e5310a7e6194c429f5865310a7e6094c429f5825310a7f6154c429f1855310a7f6054c429f1815310b5d5314c42cf9534310b5e53d0c42d754f4310aee62d0c42bb58b4310a7d6590c429fd954310b3e5450c42d794c4310b5d5310c42e750c4310aee6210c42bb5884310b3d53d0842af9834210abd6490842cf9524210aed6490842db9524210bae54908429fd954210abf6550842cfd954210a3f6550842cf54d4210abf6250842cf9494210abc6050842bbd954210b6f65508429bd954210aef6450842ebd914210b6e5450842eb9514210bae4350842eb10d4210b7751944429f98e5110a7d6394442cfd0a5110b6e4294442cf50a5110b6d42944429f9825110a7d60944429fd8d5110a7c63544429fd815110a7c6054442b798c5110add6314442dd5445110afa6014442be5805110ade63d4042b758f5010b7b50940429f98e5010a7d63940429f9865010a7d61940429fd8d5010a7c6354042cfd095010b6e4254042cf5095010b6d42540429fd855010a7c6154042de5405010b5e63d5332db58b54cca7e61d53329f58754cca7e60d53329f58354ccb3f54953329f98654cca7d61953329f98254cca7d6095332cfd9154cca7f61553329f18554cca7f60553329f18154ccb3d5415332bd98454ccaf56115332cf99054ccb5e6315332db58854cca7e6115332dd98454cca7661153329f58454ccb7561153329d58454cca7e60153329f58054ccb3f54d0f32cf15343ccb3e5490f32cf55243ccaee6290f32bb58a43ccb3f5450f32cf15143ccb3e5410f32cf55043ccaee6210f32bb58843ccb3e54d0b32cf55342ccade63d0b32b758f42ccb3e5450b32cf55142ccadf6350b32b718d42ccbad4210b32ddd4651cca7e64947329f59251cca7e60947329f58251ccabf6454732af19151cca7f6454732cfd9151cca3f64547329f19151ccb3c64547328f19151cca7f60547329f18151ccabe6414732af59051ccb755114732af99350ccabd64d4332bd98750ccaf561d4332ded4250cca7e64943329f59250cca7e61943329f58650cca7f64543329f19150cca7f61543329f18550c
  | 41 => 0xc439fd954310ebf6550c43cfd954310e3f6550c43afd8d4310f3e5350c43af1854310edf6550c43d7d954310e5f6550c43b7d914310f9f6450c43d79514310f9e5450c43bd9875210ef561d4843dbd4a5210e7e61948439f5865210e7e60948439f5825210f3f4354843cf50d5210e7f61548439f1855210e7f60548439f1815210f6d5214843bb98b5110eed62d4443ddd465110e7e62944439f58a5110e7e60944439f5825110f3f4354443d790d5110f3d4354443d750d5110e7f62544439f1895110e7f60544439f1815110f755114443ded425010f3f4394043d790e5010f3d4394043d750e5010e7e62940439f58a5010e7e61940439f5865010e7f62540439f1895010e7f61540439f1855010eee6214043bb5885010ef66114043bd5845010f795014043d7d4e53d0a7e6194f429f58653d0a7e6094f429f58253d0a7f6154f429f18553d0a7f6054f429f18153d0b5d5314f42bd98453d0af56114f42d794f43d0b5d53d0f42bb98b43d0aed62d0f42cf94f43d0b9e53d0f42e754f43d0abe62d0f42eb98b43d0bad62d0f42af98743d0abd60d0f42afd9543d0b3f6550f42e7d8d43d0b3e5350f42af18943d0abc6150f42afd8143d0b5e5310f42d754c43d0aee6210f42bb58843d0b7751947429f98e51d0a7d63947429f98251d0a7d60947429fd8d51d0a7c6354742cfd0d51d0b3d43547429fd8151d0a7c6054742b798c51d0add6314742dd54451d0ade63d4342b758f50d0af661d4342bd58750d0b7b50943429f98e50d0a7d6394342cfd0e50d0b3d43943429f98650d0a7d61943429fd8d50d0a7c63543429fd8550d0a7c6154342de54050d0b5f5394e429f9865390a7d6194e429f9825390a7d6094e429fd855390a7c6154e429fd815390a7c6054e42d754c5390b5e5390e42d754e4390aee6290e42bb58a4390b5e5350e42d754d4390aef6250e42bb1894390b9d4310e42af5974290b3d65d0a42cf54f4290abe60d0a42bb5974290b6d65d0a42bb9874290aed60d0a42ddd465190a7e63946429f58e5190b3f42946429f9825190a7d60946429fd8d5190a7c63546429fd815190a7c6054642dd5445190b7b50942429f98e5090a7d63942429f9865090a7d6194242b7d8d5090adc63542429fd8d5090b5f635424297d8d5090a7c6354242d718d5090a5c6354242cfd095090a7f61542429f1855090b7950142429f9875350a7d61d4d429f9835350a7d60d4d42d7d4e5350af76154d42bd1855350afb6054d42be1815350b5d5314d429f9845350a7d6114d429f9805350a7d6014d429f9974350abe65d0d42cf9974350b3c53d0d42af98b4350abe61d0d42af5834350abd6490d42d7d4e4350b5c5390d42bb98a4350aed6290d42d7d4d4350b5c5350d42bbd894350aec6250d42e7d8d4350b9f5350d42cf14d4350b9c
  | 42 => 0x800000000080008000001c002000000100080010000003000000000040000000004000000000040010000000000800000000010000001002400200040020008001002c000000001200000000004005000c000001c0000004000000c002000c003002c006002c000000c00b0004000000400000140000020000000c000001800300240000000004000c00100200010000001000401c000000c000800200080000004003000000000280000000000000000600180020024001003000300040050008007003000100040000000001001c0040004005000000000240040000000000c006000800600200000010001003c0000038000000c0070018005000400700340010004000000400500000010000003000c0000010000002c00000000020000005002c000002000200000010030001000000000000010000000001c001001400100000000010001000000100040090070002000000600080010000000001c002000c00200000040024000000b6f5294b439f98652d0e7d6194b439f98252d0e7d6094b439fd8552d0e7c6154b439fd8152d0e7c6054b43db54852d0efa6014b43be58052d0eee62d4743bb58b51d0efa60d4743be58351d0f7751947439f98a51d0e7d62947439f98251d0e7d60947439fd8951d0e7c62547439fd8151d0e7c6054743dd54451d0f7b50943439f98a50d0e7d62943439f98650d0e7d61943439fd8950d0e7c62543439fd8550d0e7c6154343bb98850d0eed6214343de54050d0ebd65d0e43cf5974390ebe61d0e43b75974390f5d65d0e43b75874390ede60d0e43dbd4a5290e7e6194a439f5865290e7e6094a439f5825290f3f4354a439fd855290e7c6154a439fd815290e7c6054a43db5485290f7751946439f98a5190e7d62946439f9825190e7d6094643bbd895190eec6254643cfd0d5190e7f6254643dbd895190e6f62546439f1895190f6c62546439b1895190e7f60546439f1815190f755114643ded425090f3f43942439f98a5090e7d62942439f9865090e7d61942439fd895090e7c62542439fd855090e7c6154243de5405090edd61d0d43b79834350f9f5390d43af58a4350ebd6190d43af9824350e7e61d49439f5875250e7e60d49439f5835250f6f5294943bdd855250ef46154943bed815250ef86054943db5485250e7e61149439f5845250e7e60149439f5805250e7e62d45439f58b5150e7e60d45439f5835150f775194543bbd895150eec6254543bed815150ef86054543dd5445150f3e43145439f9885150e7d62145439f9805150e7d60145439f98b5050e7d62d41439f9875050e7d61d4143ded425050eef6254143bb1895050ef76154143bd1855050f7950141439f9885050e7d62141439f9845050e7d6114143af9874310ebd6490c43cf9524310edd6490c43d79524310f9e5490
  | 43 => 0x1e000000500000000010000002000400180000000008000800400080010000003000000300200020000002000c00100000070008004000c005000c000000c00a000400500000020000007000000700580000000000003c0080010005000400000040000008007002800000000000004002001c00200400060000008000800100000000000002002c00500000030000001000c0000000005002000200180000010001000c00400000020000001000000000000020000000000400100000010020000000000100000000020000000400100000010004002000800300500030020000001400100000030008006002400000880000004000000400e001000e00040010000003000000c000c0040000000001400200100000008003001000000000000000004000000100140020024000004000f0000001000000500000010014008000800100080000000003000c0010068003001000200040000000000000000300140010008003000000800180010000001000000a00040010014005001400500000040000003001000300080000000001002400600080000000000000800000000000040001004c0040000000001c003000000800180070004013000000200000040048002006800200080010004000000000c000800400340000000000000000a0018004000000300100010010000000000200140000024007001000200040000000000000800200200010000005002000a002c001000000200000000004000003000c0008002000c00200000030004001000000200040030000001000800500040000008002001c000000000000280010000000001000f001400600000000008004001400000080090000001000400000040000000009000c001000000100000080008000001c004000000000040000004006000800000100010000004000000d001000100000000004003000c00900040000064000000400800000070018010000000800000000020002000000100040000000001000400100040050034000001000000140030000006000c00400000040010001002c0000008003000c0060000000000800300100000020000000001400300010004001002c00200180050004000000400e00000070018003000400300000160010006000400d00000060008000000400a000000200000000004005000800200a800100640000004005001400100000000080000000000000000060008002000400500000000004000000000c004c00300040030030006002c001000800400080000000000001c00200000030004001000c00300300070000002000000100040070010001000400200000000014000001c001003c000000400000180010000003000800000000000004003001400000000080008001000000c000c004002c0010004000000001200000000
  | 44 => 0x200000000004000000000a000400000000000004000003c00100000020004000000400000000030024003000c001000800000000060004003002c0010024009005000100000050004000000000000080030018000000000000180000000003000c002000000000140010000002001c002000800100040030014000000c00000080000024002000000800000000000004000000600040000010001000000e000000000040080008000000001000400060004000001c000001c00000000010008005000000600180020000002000800000000030008000002800100000000018000000000000000000010000002400000000010000000001000200040010000000000000200140000020000000800b00080000008004000000200080000004004000400000000000000000001400600180030000002000800000000040008007000c01700040000000000001c00000000000000000000000200180000004006000000800000050010000000000a0030004000000d001400a0000012000c0030008007000800000000000000004001c00100200060010005000800000000050004000000000000000000004003001400000040000008003000c000001400100100000004002001400100000040004000000000200080040004001000000400180040000004000c0040000007004000300000000008001000c0000004005000000000000000000000000000300240000008005002400800040050028008001800300080030004000001400100180060000008004c0010000000001c0060004001000400000000010000001000400200040010024002000c0000010000000400000100050000005000c0030000000000c0000010006000000a00000010010000000400000080000010002000000800040020054007006000100000000008000000000100000000008004000000000000020000000000c002000400200180030000000004c0020000000001c00f0000005000000200080020008000000c0040004001000000000040010010000000c0080000008001000600080000004016000800d0000000001000000000110024001004000000000000000000000400100040030000000000c000001c004002800b000800100000000008000001400800100070014000002800300000020000000003c00000000010010000000c00e001000000080010008000001000100040000008000000c00e0004000002400700080000058000000c00000040030010000000c000000000200280020020000000000300000040010007000c0000020002000801e00180000000000001800a00ec001001800000480040000001001c00e00040060018009000401100080000000000002800300040080018000001400600200010000000003c00d000400600740020008
  | 45 => 0x80060014003000000300000010004021000401c00080000000001000800800000000000000000000000000000008002000400400040000018002000400b00740040004003002c0030018002001001900040000000000000c0010000004000400b000000000040010000003001400200540050000000001c00000040020008000000401100080040000000000c00000100060020000000c007000400100080000014006000000000040000014004001c00100100030000003003000000040000008006000000500000000000002000800100180000010002001800000000000000002000c000000400300380080014000000400c00000030000000005400100040060004003000000100000080034000000000800000000004002000400d0000009002800200100000000006000400600180000008004003000100000060000003003c0010008004002000100100080004000000400300000020008005000c009000401800100000000000000000d000c00100040020000004000000700000030000005000c00100880000000006000000800140000004005001000000080000000006001800200000010000000000c00100080040050000000c001000c002000000100540010000001000000000040000008001000800a002800b0030001000400200100090004001001400c000400200040040014002000000500040000004001000000d0000001001c000000c0020020005000c004000000000040000004001001000100140000004001007000900080000000005002800800040030000000001400900000000038000000800000500020010004001c000001800a0004001000c000001c0000000000000c0000004005000000000280000000001002c00100100020014005000c00d00000010000000002800600000000000000000000000000070000000000800200080000030000005c0000010015000400100080000010009000000b0008000000000c00000000018000000000400040050008000000400000100010028000002800000500000008000000402d00000010004002002c0000000000002400c0000004001000d00100000000001001000200300000004003004c00000040000000001000400700140010004001006c001000c00000040000024000000800500300000008002000000200040040000006001400d00000040010000000400300180000000003000000200140060000000001c00100000120020004000c0000004001000c003000000000040000008004000800300000040004000000400e0028002000000100000010000008000800700040030014002002c000000c00000080000024002000c001003c0020014002000000000000070000001000000100000010020006000800c00040000000002000000800000000000002
  | 46 => 0x10000000001c0050004001000000000000010000004000800a0000000000000000140100004003000000100000030004003000800000080040004000003400100400000004001000800300000010008000000000000080030000002000000100540030008000000c0000020000000400000100100000002000800000000000014005003400100000030000000000c006000400500040010004000000000300000010000002000400000080020018001000800000140060004000001400c000000200000010008000002c0040004001000400a0000000003800100140020000001000c004001c00000180020004002001c0000000000001000000140000000000000c00000080010000008000c00400040000004000001400700100000000001000400f0024003000000400180000000002000000300380010028000000000000000060008003000000200200000008007000c00000000000010004001000400140020000001001000300040020008001001c000000400100300000008001000c00000000050018001002c00200000020004001001c00600100040004000001c002000400100480090010000001000100280000008009001c00500040020000003001400400000070000005000000600200010000007000c0060000000000c000000400100440010008002000000200080020000000002c0020010000004800500040020000000000000a0000000000800000040030010001001800400240010014004000c000001c002000000000040070010000000000000040000000001000000200000050004000000800b000400000040000008004000800d001000600000010000000002c00000040000020003000c005000000400200020014001001400200040000004002000800000040030004006000000000000030000005000000100000030000003000000400000000000000000000000000000014008000800000000000010003000000100240030000004000c00600000000008002000c006000800600040000018008000c00000040060000001000400100180000014003000c00000240010024002000000100000040000002001800000200080004000000000f0028004000000100040030000003000800000040090008011002000000040000008001002c001000000000000080034000000800000080000044001001000000040000040000000c003000000f001400500000010000000001c005000000100000030014003000800000040000000001000400100000010008000001400200000020024000000000300080000000000001c00700080010014000003c009001000000000000018000003c000000000100040000000000000000d000000000000000010000003400200140070004001000000a00040000000000001000e000
  | 47 => 0x91443f00000000000017e0000010a8c3c8581b9e000000011ca000000005c94108000023988b98e6503191c9c52b48a397ed477278685c116e4319c84642ed2319384a3db0a2a8000000000006f3a10a16b46ee0bc80692000000009289326000032186a60000121600000000000000009ac31a000000002c04704800300040000038000000000300000000010000000000000080020000000000800000100000008001000000300040030004002000c002001800000000030010001000000400000000038000002000100000030014000000000000000110008005002c0010004001001000c000800b0000003000000c00040000000002000400100000080000003000800100000100004002000000000000010000001000c005000c003000400300500030004002000000100380000000008000800100040030004005000800000040010004005000000900000000008005000c00000000010000009000000000480000000001000400000000030008000000400000380020018000000c00000080000000001001001200000010008000000800100000000014002001000000000020000001000000200040020000000000800000040000018003000c0050000000000c007002c006000000200140040010007000801500000010000000000c000000000000380020000000000000300000000018006003800300180020010000000c005000000100080010060000000000600000000004001003000000240010004000000c007000c003000000400000090014002000000500040060000003001000000000010004000000000e000000000040000014002000400b002800000200000028000004c000000000100040070008000002c00300340040000002001000200040050000000002000000000010000000000000000000010008002000000000000020014003000000a001800100000040000008001400100280000004000000c0000000001001c00000280050000001000000f0010006000c001000c004000800100000040000004001800000080030004004000c00200040050010004000800000080000000001000c001000c0000000004000400d000000200080030038000002000000140010004000000000d0014003000c0080000005001000000000000008008000800c001000100000050004000000400000040020000005000c006005800100040000000002000c0040034000000000200140000000001000000000180010000001000800b00000000000003003c000000400f00000030004002000000400000000004003000000000040040004002002c00600140000004000000c003000400f002400600040000004007000c0000024004000c001000000000100010030001000c00600080070010001002c00b00000010004003001800
  | 48 => 0x358006345270f600000703c0000000000012a0d42000000007cd0000000035a262b4b258afa424889286dc8000282885b00000000425659c8000000000006bcc6a917973ec048440000414000074b86280638261c43c877d9c8c041e01e87f68a630000000000023ac00000000feb92690f04397c00000000f7600002f680000000000000009f2182600004a117db34666fbcb068000000000006a79fa02786000000000002fbc85240000000341812b8eae0000353035408848000000065440000000000004d888ca0972a240000311800010fa156c462114f09be000119e9dc5331086145ac20b3277c78c1022052722ce788ce8c862400006f1400000000000028000020b6453e36941df97a5300c82e81141d13320858fc7330211121a8268f0f9a1b00004e088b106cf2f64798518e80003cb6000057719993bca0000ddf065002ca00008f400001b9e7f190ab0000135a2b9c083a2a536b84d540000a13000000000001b890000000000000000000000030500000000284089f800000000a082160bf618c4529c00000003a563c8c33d21c9218a2f044b5194e00000000000155a00da73d4bae9cbe29068184526818823fc2b88000000041465c286f505f121925e39126043508a60000df28000478c0000b509e7300003ca90a600260000838872181520090089800000000006645c0001b970dda47880000000000075f40538000000030f474ca0080000000063516ca000008c89e0127d25902c250dea3e73c4c86c45d695e13b8200000001ecf431e6b8838e8763000001fcc0b8fa144ae0000e4e0c25428200005b0901f0746633009f2184000081b0c1f042905e66bd0c98800000000a0022400003e3a5cf8fb9838b3e500000ae3800000006d0800000002b8a05240001b002dd27ba476897c40e3c754443a000017a01d7c6b08000138466ec76301e8419826fc84e223a052e009000015833cac000000000003f527d7800000000000000000013020000564c000000000004f900cb00001c4804a408b8cf90df47a94429937336385cb0bea054f2ee23004e47069d00000000000190220400f8059e000000002ab46ed065919fc39b0aa50fda37046ecc17a8c3230f84dfc98e95420ad442f0e4a80000000879040d1461000000000000ae1190a54b40000214296a1c9879d00001fee40080001169000036e83f615161cc02d44000000003d40000000000038368d38ced000000000000f851f4800000000fde8000000000010eb0000183200000000000000000000000000000084d42f701b600006f0c13a23dd08e05640ab30acd31be10681d60b720e645294f7180002206432043395b80b3a09a40219df400000000000089c023a0fdcbd6800000aa56f800014970000021d139131513e826901bd9efd00000000000217700008
  | 49 => 0x1641e3400005aa034a0fc0000000001598000000020286ef80003d30000000000001b2c00007b581262dc2387c0001c881990392c6a08000039007d800013572d60000000000002062000000000003ed400010e605e009c800006668000357e000000004c300006dec000000015828488b7f882820ee00001e50000000000000000743340a313c0000000000071f400008810c6400010709812444269d01a580001f4600006ab89b71822000000021e900001604a7f2117146a00010881bd000000000000000000002b200000000000089d8da5800044ea8cc83341065000000000001890278200000001934000046ecde69cbf390685c47e8914b3c1e6a748ac217a35b6364d03708ad14308694743805f441e0000941800000003f2878f80000000118817300003e207a2000000002c9a000000022b207f03d1d1009c9f0a48000000016fe00007f3000010040e585fb8e0b9f551b640000be280001b845608000000015f6023043d9aee030a510c43884b937c21688d348fae0000740439f9f6827704ccce881d400000000000002e11ffc511427e81ab45ba0000b3e80002a2e00000000000000001a91e21d2406da0000f000fc500006fb485780000000000110b014704565980000158d000000000000000000000000000000293e00000000ee1408a1f9cbc39c58287600002089c281408000000012ea00000000250000031ea4bac01400000bb227dc00009dd04d800011cf8e6d0000000000000003d980000c410f522d140000112800000000000c8780003aaa5ae400001020a823ba400000004770790c0d8a32f000000000000ed70c964414646238e3bfe04b4d58209329ea78ec7968f293fb65704ad98b30253687b8bee212700005b2c91409c80000611c62c0417349439c0d231bb61e7e000075700003fa823e011c8ec43daa81209b39d8f04fe77f8aae1bfd360e83cd1548ae3406a00008b685ad36f287840000000000055f80001baf2ff4808900098c428c65a08d3602270000736101b100b30883be03f804bd462e68440a6957932c6485c0118c9a000000002a18f861b062c74dc080000000000000019060000839c0001853000018fc000000046a66fc101d88cd44f6000100e93ce000064d80000d74000013bc000202543c6498000016df00002a4519c130c3fde402000012c71d2256e838b8000253c000000000000000000014086e900000000000029e2e6243ecfd20e4c2d9c000000003ee36584c880001dbd1a7a0000f09949e3e1c0f6400000000000829c000000015f20000000064a202e2e0491f83d3359400004d49aa0004a523cccb88a9387a1d84c7a08b62fd202ccdb917b00d4c5ee82bd1f3a285226980d9000000003d4c0000000000000007b2800001c240d44150000019c0000e770000148800000000
  | 50 => 0x2e5006000011930bcf00004dc8315000010b60000cac96341c3a0000000037140685f205798c1a05b800002640e8a3e9800000000fe745fa8e983630a5d007c52e48cf84c532f64514d5794821be40000ad2000001540000000168100001c8c0bc0000451e869876f118a1e180000609000000006e882b08aaa32c207d000016113fa22e148a1061e220078e0372800011de7170aa280002a3a6ca8ec4800000005fa095283953efa457400007092b5827883f70ca20faa62d8000000000000000ca380001d20383400020b200003604000194a0a5c000000001150d484a88d32000028b60f2c000093f0000625c87f00003e60000000000000000000104c9fde00000000894017e22a8191400019582ee8572c82c0000455c092caee800000006c84e8280002eb25350c8b146f000030380001c483b101d140fc8000000056c06f98e0209060000365000000006a58e9400002a0c33d8000086b08fe375400000003cd660dcc7f226a01d086fcf47800043546e2c00012da17d47f0c647858a1fd00324bd4152215ca1400e5e9e20255e3c5c000000000001a006d3a070000079044f2000030c26af84ed10951dc60d4031e8000000000000000a030000000038a9cb5000019380001e5e2d56000000000000000093056e000042224f94e6f09e93cf436f0a7e1aac3618000000023721dfe154c20f01191d660000000000000008c70d4484cb00000000386819000001ee00000000000000010e000fd16a83a580000000000000000000000000078a82180000003c000000012df0000000034f0d2800008b04b33167936ae6eb800000000000000000000003e7800000000bbc225859a0000000035f8330855f1c851ff0000000011f6299e000000022dc32c400006c880001ece896c00000000000000000000000cf2000000019c7003e000093d0000395e000000003960000000025500000000000000000000000000000000001e06000043f9e9901d2303d03215dc34f224d512c80000000888c5ee0000007200004bd0af600008bb8bcb000000005dc0110000006d65f905a19975449c00006b18000351a738032081c2209242488928b1346ea0ad400000003f3000000000e2900000000e5b93250000000000000000000000000013a0387e5ba0000150d01c800001f38e3225ec3a151ea88a80f9200000000000000000009f42102000007e80000cba00008b5000002a5407800000000bf740ec0000dde000000000000000032b00cc470889b800000005af4000000021ca3db4def85c0352661751ae079e0ef62fbce859e7100002bb40000000000001800001f4600000000000000042460000000000000000000c849b6d06a60000798000021b200000000000000082d00000000000000000000edd0000000000004a6000025fcdb29d322a82
  | 51 => 0x12ad00001fc41451a473e3600004960b100000000071a800000000000bb180000000000059b80000000000043e1d7027ce69b8f371f7221a66d44bd300000400144038d05f9000000000000000464a00001388000337a64b40000000000027acbd48076000046889cc8a75325208287170fdb1bd2000021f96b400007e40000136e38ea00000000a720000336400000004428000039a8000000015180000000128e0000aaca28500001874000080306de6e18d32a39500004114375800002541f7800002d512880000ea500000000259800000002de000000001dd508f012dcc310e9e13c27cb01719c4d2d0e31e061185b200008c406be9944000000008271581000000000818000000062cc0000000000000000ff232d0000000054211710000710075e1d94295c775c6fe00002b78000085b8000000020049449735202a34f8e82194b281a00002651d930000000009700004448071c000000044d6000036e00003dd44c6c545a1533e6a000000011e6473a0060000000000002df8583800015108d2898a000027a48b2442700002a4c351068c0adb000000000e8800039300000de88aa92dda0000977000000001f8c000155b000022bc3470000297c36dc55300003a3463c00000dff40cc6984c388c4b00005bd400000000000000000021ce00000000b0e0000476400011b012fb453863240d413a40b7c27cc55d0b70385e5bc82bf93ab144200ac2bb9cce40f04b00b6b911222888af0bb915d51732126d1e112720ce800005d2a28a29866b6453084eb1eac59880000672000028a506e0000222a803c8b91c473bd2000110b80000ed8000000023d645ea5e4c72e0000092076d8be515cf0c520000000144d00000000ced9f7a00000000000000021041410d59023400000000fa5093d3a7c811cf80816d000a45b0a8f16d30000834504f837312743034091000029d60000000096400008280965120c3ee033f4000042d2f960000742000033f203fc696a15400ce56d000005910dbe0b3cc8e9d123900727487b00000000000000000003fe27b991be97a101d67e6400010c427e614f430113290000228400013f41ba66ea910411d0193601ed0d385692a74548411507083230000000000001a646644f728000458e60500000000000000000001ec2000016a80001dda000000011e18000000060cc0000dcc1776000058221cd00000000d418000000000006bf9845000048e51c791b9000000000000000000000000000000000003d0f2b80000bea00001ac80002e5e0000fb380002bde0000898800000000000d1f804c000000000000c440000000000002bd130c00002ce17eb02147db8c91990d2f8e037405a1c6c1b0a00004c18cb5361c00000001b771c2c134c39000001bcc00002889f810b42000000022a80000824888b
  | 52 => 0x1224000100002fd00000000b351fe600000000000230e2af671bc0000d5917843f2c0000ab900001ee4000127f000000008c584d100004f5c22f8ab62d000000000000000000000000000012a8459000000000000000000000002faa00000001d592c1826846ce13d90000248c000000000000cf8ea3003f2c142dd0b7a16ee1b2e40bc8dc1f6f20647258847a021375288bc000200d00000ab400022ef3aae615c000000000000000a8a189314dc01c8eb3800023460000000204f14d64e7400002ff339a486100e07d0148e43bc2b110f8090861f50f1000045c254a8e339939000068a80000000000000000001d5d41f08660380800033700000000024600003cd80000000000000003d580001886000089e880700000000b4717cd00006c6c0001c5e18100000000179200005ae82b598352c6a09143e2159e0ef457982ab19e944001364c60852330a8593c8fd117300002d1424e01fd000019bc7e38adf19c2000000021d21bdc8e804078eac0abe000000018ab000004840000f9d0000294c0001bb230c0000117d000000006e4c0000000000000000001241000031fc93221da00001a6c8bc040f00000000e011f6b000077b0000014c24103fc8971000000002c280000000394000011a4800000006c090199bc211d8320041ea1040ea85b9c000180045d26388000202c324e6e38aaf1d560f14243879c9de400008ce400019df0000000000000000000005c27018a7438807fcfd721ab2210068831d000000000000d9e082400005af066900001bec8b40219800038d00000e161f3b000030749f0865400001ccc000000000001efd01523e02f7e86dc00014473c8800000001f3800007c5421c0f403b30721c4b5800028ca7370a2a152700000000fca00000000000000000000000000000012d032e00000e6312d430928080cea800000008e1800016420000139c5721e4f125249410f802ed000009e80249eb8018e5538d75a28b00000000000021b0000599c8660000293a63582b7000042f06d7cce0045e06ee851c000030030100000000000014ca00000000bb100007f64a3b0ed221d80000e30a12a000000000000000000000000000b670f0651307c79569183600000000191000000001a1000000004d28fb080000000000000020ed23f66b1c0000cd8080820e482085b5033000000001e823bbc00000000000000000000000000292a3f5c000175816f680f40000000000000000000326000000000000a0123ba000000000001d985cccaf980003de668d400001cd3b98000077e800000008c180001d7c43bc00011a6940e1b3e031800000002af80000ae480003830010400002fe44240000b0e800000000638000159434164fec02f1b1d00004f2841b8dd223b26aa8000082245466b34157184108540000df61b96000
  | 53 => 0xc20d0755a25e00000000000092844120ba85ee819e431a79f452b9d48171a12d911986b50000878090f800000000000000000000007010d751b553ad27814edc05670e785da01a7861405b01d6849296b23d4647b82d6000011bc000000000004426000000000001ed40e382909303270288fc40e9adf19be7d0831123aa188c441813e182d00003ca000019ae30e459946db0000186e2f2c00021a905a0270c000000000000000fff1f3d455400001178000265a71fcfa81aa712281a14f5da1f900007a24c19037d036661c000000000000000072c800020a0347417412f442d00554d2f84151664815c33b85c911485894dbc235b1a6c6dccabe827200000000d69000012b210650071f9605581ef0386000000006b6000009af000011acc3c800000000000e8f81590000000105e143c0000000000021ca153c8e0405e8ef6000000000001d5b204200009341f4b350e80c8000000017a620ecca9800000002a40653800000007f1c0000000474800000000000095e000000000000000000000000000000000011685c30d7c00011898000000000000000b2a20380e880d287982222195c11d0000419c000000008c0176e3b2cd48000000001e34f268cc4173e62e00b9800026a409b887092c210f400000000000351c0000000154f00003c9c0000f89420a12ec000000032bc0000273000018504520f1e90a5395c1ab8d101a5d00000000000000000006cc8000000000000000f0a1f930000340052183da00000001020800022d6000028a86e026c60000bf90d3137c020b80001d52276818bc8f780000000000116d0bd830fc714800000000000000000000003bba000021402aa000050dc0002192056c4ca919b1a193b3205081ad95ad0000000000016170000000000000003fa61b64000000036722100feb0baa08b60000edf84cd1f261a60e9f927719548b2901f8fac0000000000000000000168115b000000006cc03b90ed83c9085fc000058800001e0000005992bd611e8afd8d9a00004a391dd0c770cb81110245000000002bf805113a1000085880000f8317900000000034400000000000000000000000c999c6b21304758e7c80000000000000012fc10de0000e3c8c3521e800000b81488000014a4182840100002d1c00018960b987e78038055800006e6000000003dc82240513923a24a61bc43310ad9092e632c0001b231c0255c400016cd38ba657c00007030c1000000000000421a1f5c9e88000000000000001e781e7041f000010d63710000000000001fe600f0073081f35c86278a209dd836321da86381a2c2de23900a2103db00000000000000000004388731000000007f74fb2975440a81b99018000000004ae800021c1436000000000000000058c440a06ab40a6630843914b0000000003d812cc0000517c00
  | 54 => 0x3e223d44c8f20670000000000003242f106c9c00011a842d65fc095c1f6d000089b0e3c0a3b0d7637e86b600003c84000085f0000196616f40000b2409e244bd10f0000117c40a8000207b2a020d7cba51b64112c0000cbc838c02c828086d1800003360000000000000008be0057154942bc5e040001ed9000000000000000000062b8000084b41c02044000044e00006aa0e51a34b0000000102703b2000041a06e4000000008e688b087691dd639d439821570c2a000103e091900004d70f4600000000000119b80002f3034f10db162e00000001195234416ec26e40000000000000000000b8a106a5d08b621d4f0d967918f3e09b4005800005a68000000000000000000215248c904f061800001b600989356197055bc173800027a63588e0523153cba24e4d36866a02ba000078311c800000000f9f80000000000000021ec000027380001f6c2796773832d800019c40000d080000441464500000000362271a804b829327bc8ef0cb780003896101c00000001dde0d349e69fab2e8213dd06c000020ce01c4e3897f800007af88b30d2f234e0000b6f20c739286da4c5f149c180400001161d2529ec000086da0b0163e8818000000000003778c6a18ee0fee426c0000000139e047d0a51d44280a0000c7398c8110e0ba434305d70000000023d800017706db0000018605ae0000c97a32000000f601368a1700008dbc000126a22444670a008dbf0e967b78821000000008c6800011a12fea1cacf4d8d8a0e0a60c000001430000287c000063b000068000000000000000000000000052a3a0488700003e9a1bbc0000000000000000000fb73a822ab0000000028c8000000017271fec0000b0c80001f4800006160000000000000000000045c0000de4800005d88970c9d0000000000003ce0275000000006ec000044a01a9400015a300005e6c58a15cc1fa01a411bd0000352a356854aa1a335346214cfe8cfc10ae000070183ef04de584057a80002fc6532400000003b4c318c000074a00002b4800009f944063cf8c288000215a0000000000010601d64eb295364206421cfb48000294c579ce5b00000c5800000000000000000000000555000000000000000000000004f50f1e00004b1074022473ade2f24b1580002d302a1800014072cb844e80000000000000002af14340000332ca1f169537ee1b68b1d901a31ba1e80000000045be1e501ad000000000000c89191918ac88dc0e297d12242271000000000000000000003f920ac289000014ce1a900000923076f000017ac0000882086c563838301bc05846ad02e21e5235103174cab80002eac01b90d6800009423470cdb04ac00000000321169e389e6d689108000206e6e545eb879d39540a1491b000024d6660c000069645f20000f050e6841
  | 55 => 0x27b90a58000207c1c28a2c1cfe0cec671400004310ce609a80000bf30000000013400000000570804f8000000029f8f6222ff148451b0000000016c60308d5591b31f60000076c8000000000004fb0dd9088050e022a0ada00000000b2a00000000000000000003a7a82a00001b03290a00006fc0000000017448c380002e260000052000006c6000000000000000659400012dc0000314cff112f1331854540000000000000006eb0000000077c488d000000000000000000043ea0001131000000004fc400000000000852102b0000000000008f9800003720000000000026004910000000000000000000000024b200007278b6f307800003fc800036e20ce8000000028000000000112a11fa000070600000000000000019840000000004b00002c7074ec2fd2356101a85348f887a20a32000000000000000411d11d8000421e1c647d4000026be55b40000b9c243a4058000000022c01134000219e3bea28cc0000dfe000008e06f20042224e88f4000000000007d6848e8000032e4c480000ba200006fc80000000000065a400000003b361d98000000000000000f080000000026cc000000000004d8800003b743f628b4ab09ad6000000000000000000000001881f782a9a54fc81c00001a445ddc5ad80000000000000000002c104c286531ef632e820140000000031e000000019f124be424c000000000006a98785000031422b400220e0a21623098aef180b2664865037c963e25ea35c50ba08da1b1000003290b7a133885f400000af03540000a7c060714466f48fef90f519e68ae000002a3164208d800000000fca7bd0307800000006cfc2d318af041054f4000000027b67888000183b0a16301c00000000e546b3c000000017a28ad0e9a019f420c20d8000000047440d480000000407c6f31060a1642d248f31068125b3cc05b210b905b027da0000000000000002bac0000000000074b494909ba00007fb800001c000000000000000000008aec0000bff36a43b00ebf9fb33dd80c9400010d510ee00000001932000063e01e48000156200000000dbb0000322000000000000000000010881af40000000000000002ab80001389285600004419d9f0000417c000040b000068c02a299e72ea420848230000115800000001ca5000000005ed8db800008d1c03c00002592000000003ff000000000000000347046649168000307a8ac08079efa0000000097480000dd428f0eb30cf50de00000000000000000000000150900000000a3e127c2ee670f801a09222676351c0000f053a1a000000007960000583c000107d32e20e440000c8e00007fc8000108000003bc8000008a300e6f683a38e1000006ca420b03ba1c1c0fb40000000328a00000e220a100000000ddd8fe300005ee4000042b213a00000000fdd00000cd80
  | 56 => 0x65e067b00002e4037b946647a6822054a1e4b00006bfc00000000f9410c800015d100001d9c0000ef906c0000117f0000000000000000000151c61b819496cf0e3668180001f863e28000087223931a060000a5900002dac61009d180003d5c0000f6802a236f867e888f168c1aa866a806c9b682a22000000004dc15e2000000000000000000000000003698575c0001a5900001694000000026c00000c438244378c0000b0080000000652465207c004900ac4837882c085c52a0b3ba215341a46f4f778abb26e01358a448a7900001a2400004f500000000e2d000000000000000000008ec418cf5914a4249e66280000000000000000000000413a007458c0e30000054d48b2800000000000dc2965e192c3d8ce2186fe3ce00000e34800000008d488c7a2073b7c35c0dc8000016c07e74b2984fc00000000000013f289274e0170219c000065fc73c80000000000000017c3051c000000003f608c843802fb0000000000009b5036100007c8cbf60000247066400001fa10000875d14387f801ea51a041f155029fa2db4000076d2a085db400005b3000000000000000293676c40001866000056bc0000d4600002aaca87833800004088050836a043e6c149f78000000023fca58800019b80000e21011000360000000000000000260709a24300007f8c11e0000000055ac0001a0a1f8400000000000000000008c91e3f0e3e0000c2d92811d9a42ec28b98f12f6c00003488000141e0f980000ce4327c000056196f83f6e7a38000000000005d30237800038a81ce03d69ea80000108800014dc31162de03a4000000000000f588000000000008ab000024200000000000014a80ca80001de043505c2054c931334bc00009ee850f44307bf8da7000000000000000023500000000e3800f2103600001b4021d234c0000000013c000000000000000349c00007321dc9466a51cc0869b2042860000b5a8b41000000010d9a05c0000182c684000004f600007f098cd03142604e2987b4056417c878591e02a6400044cf00000bc800001f216c1091a47e09ca93981b5c1fd40001769035247842900000000069f8e019085000079880000000030004e40000b0534b63ac4e5391a5007470301e88eec15d01bc8000062602482568495841d065023640000000000008dc6c48000240e000000000000d4405ac0000f1a000000000000000000041d00001c3b2bfc6f200000cc044f00dd40001e2400006bbc19a8000000081f400007c10000000096700003d7e00003e91609078000010760000371a7fe0588963d03c005d015808f30f8c64c0000000034ae439c00016bf000000000000000000041e4c7903f0000000000000000000000000000a6600000000000000000006bc0ff2883314362e84d4000000000000000011d8000002c000012e80
  | 57 => 0x4c60558ad42235329e6fa0c04a3b10820000106400003c780000000177e081457fd1db0000000054e4e6799b036ce533095616c324a48b101a8908a23960000e58068224f2774004998db39f80000c4e049208720000000000011a600000000ac6000063ecfe702d2000003c10b0800000000000000000000000000a5494c1000000007781b8018da0001118800001d839b90a108550d863ea8c3d8d1a0bc2499917680a6000010f0e819ff91aea0000863800041ec82d4e8c042f3352000016b037a23ae0000000201414b07580d82190c12be814091111680d3873d8000000000000000ccd814b000062044789edf0000422c19c99ff22204428fe297fc2e3c2e901238140000046f0000205a11d434580000aef1e5e8ba08bd0ffd183c12680a503a10a0c56dc4421dd22930316801010ac0cc60000000000000000000000000000000000000000000000001098122321b484b000010ed3d0e4ff467290eb174c699c7da9d6232da3eec0000000000000010301163000074e40000000012024544280fc4000069a904e19a30000000074102e2253e000020480003f0a00000001fa72c260000000008300003a940001ca6000012182b40000283a092448291400000000118580000000577c0001dbb000050804e90000000000004ae0a19036e00000000957000000000000000000000000000000142883982f500000000000074f8d2b00000000000000005420d2000000000000460400d0e19296e48cc718897000003fb800016c9475058003bf868b34cc0000101992b35fa612c6e0828c36c047a914b8000061e2bb000015bd1a4246a80da9553000000000001c1f06a80000000100a02fe7fd4b15000000006a2c1d71c57000083a40000bdf0944000043b1b7e227c540cd2b000034763928167008f13de33dc1d8800024682520f19000000000000000000000000000eea000019c00000b219fb23d7268d02d180000c1c4eb0dd4000000001c2c5c58000000000707a4021c06b857402e50000138e00000001e09000077ac00000002d2020acc4f800034985904f9b8a461c0e00009ce0000000000008348d1000002114ea28000000010d00000778000000000001d8a426e14a0e6022c63a6018010cb21d3075203110ea81050698708512099d221d233408da033700000000daf00002ad45ab02a89ad000000000000129500000000ffb0000419400000000b3e171e23e43d6000000000000000000034fe0c9c00000000000000014f80002762161047b15ab292008789cb836927ec0000000000000000000f6e8c9217d08efcc16015b443e864c3691f3131b06ec434408e029580000000017b2560771ce28800000002afcfdc9dee225c376c4461a9e37a6581c000000042a46f38497824a07ca0abcfd784a911c451642c100000b6c8618
  | 58 => 0x4660b40000060582c595d20000000000012bd08ee0184ead0000270a409c000043703ce322c22a92a8339e765514113ba000000001bb000036b20000aa21d5442d26154f3b800000000000000000000001ad00000000000000000000000076c00000000000209848180000000466000007739348000010384c780000000000000000002c726f28144160e40304ef0e52000000000000000159137b66a50bca8c17022421348cf051205a200010c515b91abc000000007d600000000bd0120228bc41a8b48830c1d5256fc8d812a93f2400007f892cb47b66470473946244a4000000000000c7230e87cb81d40b9a217824f000000004374da2124d473067f0f4220420000000000012743dd6000000000000000734c462a27d0702000021e961500000b64899136b000034dce9b888b39ba5acc8dd054a2c8a2fc44ed84b1000054bca4919d9000010ec7ee1a4115648d64209917611342f38eb90b562be40b4c7ad0000000088b40000ee617740000155959500000000000000045ae000000000000d3e00002b610de04f264140000a9712c2662c81d000041a6172035ea1fc00006244393800000003de8000173a244e65807e40f26202014c11e5a3b42ae00938ad887db243600009178f4500000000000000030520000000078900007b8000006d30000000000010ce00007f280000f8b0000000045f80001fc0361ce058d1b0000561478719463e061658a2510e3098061bc8d7000000004d2c31580002a1c00011c00000000000007d2a1b546f8000069f8a70374e505cf6a148b00000000e901444267c00000001054268674f000005d5000088f801d9c3808d409dc000000000003db800019f8321658984a0800000006f5400000000000408cc8a80001e26610c04e99a5000000000000000000078190f9000025c27a444188000000042b8000000000004d44b538f54256c3d2ce22927000000000000000021320000000000000007618dd20b5e1ef011580000000051200003ea0a6f42ba00004b909d81dac217cf0a80002a3644e0d1315a627fe2914f69961f11b843fc09d80003a0e80b4692000032f03d0c000000000002a30000000000002714fe000f700002fac0000000000000000001b6f0d661b00200238b13be6558a6293d60000473467d1d220ee010f82b780003b8651c8b50000009c605100001159066000a4000000000000000ec280001ab063f426110bf0000716478d9fcd09186c18f3d8000456a00003cc89a232a00b5000008b1238041b44e5223200000000f480b2947c8334cb53000000000a1c87e0ddd0578000000013b93d4832540001a551d482e380001925103038780001a713c5600000d00000000030891268000000014b07b1000032145924000226f19863330aa89c162b2c000066d8f883b5c7b0ca120000
  | 59 => 0x1cd25d0028a126e2926000091d877600000000d0a000000003a60000000003e479903f0883c00000000a01971237e8198000900003a74612831b229033cc0000591a1e716d41ae83371a70467665b05a99e49000015f87eb0000140c1fbc1b60c8d0000000000006fc464e69cd0909ae000000000000000042aa5fe4c5aa2ba00000000a168000109237ac0000000292c522800020b80000000000023c73650000000008610000000000000002eae00002dc00001cee661cf0f1766000016bd14203ec1f1a00010e780001c44145886c1ce82cb07a151d490c01fd41c407c6000002dc0000000000000005b6ca7293664212777c0629973185666006718b4800003c3c29a9452088229fc47a0cc6356671b4000000000000aa468c8aca27d42ec05df9ec8067600007c813283c8e264d1e40000402200006858dec350a2078000000000006ae00000000000000000001bff149e0000000000000001cd80da000040be000075a871c0a3000000000000000012380271a4808b435d8000000047362e54317073107680000d3d09563b380000000000000000000000000000004edc0e4a07e0000000000000003f0800011a1800028fe0000ce100003524000000200003e44000059295d8322657b40001c5f36203a6c0000a0a00000000000000000000000d3111513626000029f8000054e0000d9d8000000089986340617411e0000e9880001d5e039c39100000f7c1f1c0000000049a332836b88ab000061340001b1a00008f5d0b992ae30d6410ce4900003cf200009e800000000000082e9136000000000000ea70000000083c040200000000e5c0000068a24781ab80ab0000000000000000000000000020f40000000066b800046aa0b244900fe4416251388149838000018581c499dc0174250c00020ac35ea00000000000000057a413b018b2dcc372c6d88000000075d40000c14000000000000000000031a4000000000004de84470c4500000000d98800042b684b8acf800000005aec0000460000059b4c77815400de20b4eafa3ad452224285112095260c5c50e00158914c400011618df00e0e4fe8cec00000000000050e8b333f18297c1e2000000000000f689ffb183e36341c423462cd26890c5e8eb730c61b091a7a0a6000008841068c480000492c2c380001ec8600845b8000000035b83ed07aa174e09e10bf11261c380000d0e8000000072a400000000dfa133c1e08f1128a64c44bcf21d00000000000009671da80000000111427b02dfc000000027b81f2cb941fc4147000000b080002b086a7084710b617aa2db03a7136c266209442f4833d000021200001d5e25da67d005285dd00003bd000020b90000000002283f300004dd10900000223a00000000000000000001430c4100000649043800020221e3c0000000000033d
  | 60 => 0xa94800000000000b2d800000004af00000000285c5cb800000002e9c00000001ab946d82c0800014c035d00000ef31e66000001e4438000025b200dc56f151f270600001490000119c7d7484609770e6e00000001bad0ec45c54000220d00000000ebd000042de515c18ba3de31b800000000000177c826c59317aa0000000000000003e881d44000000009e020489cf8000000022cc2d387ea45f8000046b9ce53cca2ed012fa39600000000000119000000e504399c763f220000ecb800002c41de43af004d12601b6c8c29afe362a307000007bd000000003ec990843ca341c84206a000004c8c46900003a5e4a340001eff06ba00000000786088468ad0fe885229848b9c7fa8b3a07303180313a36d00000a40292899100005ef03450b691f344a105f396301772327c0001a400000000000000001dd0000045c11a92fb400000001bd43a0000002841bb52c4400008608000231c000000022c81fa60c846fd8000345a00000001bdd00001fac000059e2202000107200000000013c58a846d00007078899818737320000297805d00005aa40000bec00000f3c0000000037c000108598e80000000026a0a4c25320bc0e918f1d382482bc58600000000100c430000011e4400451f98d33c66369058c9db30000000099581a700004800fba8e712ea05c3cd930a3600000000df890860000000095da0b72454619cd25800009f60df0000044700000000a72000039f400005fc086a005400007000000000004ad1949f6341f455fd151000035ae7fb4ba5a08a000042c8431835500000000000000034440a900000000000000010f7926100000000b86000013ca3e791d981a330687f08380038d2788444c000000010c4000000000000e084cf492a9e0800001c5000013872f1e0ee4000000004ac77c00000900000000006ce800013fa8968000000000001618397000015663b6828d9ed60fc85b944878ee23a222f94a9996e200b600000000000244a77c80000000000000004860f7624327474cd68f5e2ca0552c000186a20c80000ab9041b3fd68abc0000000461842345620000239e7e3c1541f2d00000000bb38000000000001fa0cbb322016e47679b9b13d0631513800000000413c0000afc1ad20000c931b700000809cc018e33369a00002930000177a2a691ec896c1928036c03a8ebf0000749c00000002f5821b80001a9f0000122c4b480003ac23df4ba300002f0a00008358000000000009389d923fe60001099800009e64de01b2966b056e0128aae84930a04000000014e8341e0000000000000000000d1b00002b5270d014e8047000016e8b4492730b8a00004cf8000000000000000afd000051ecb51000006bc5668b8b957a46c2812880c8a2500000000000045c1434194c1098000000057dc4219d0e31527914c76800
  | 61 => 0xd400000000e1d0000000088acab21d7718005368a5a090744f808cc6c0233a07be8594000000000007fc03fe0a5e14f02390f010abd00000000d2491db0000000068300001c1600003fb000000002e787d380002bc80000000014e46f02ea06a680000000000113b905a0000000065f00000000000024409cb23180000000000000008400a6985bb1a28000073d0ad4374c8dc40000000000082f40001ad31b5e4f542a0030b14f63500e3018ca0000609c74a80000ae200000000088367a151c00000000c186444a57800000003dec00008972c0c00000000de31c340000000000000000000b3f80000000000000022d113122b389b418201a040000a63222a2e164344e4593380000000087801db000020bcc069fac0b6e874511e10c20000724c7d799ab0ea62ea40711c771aba231810399821a5c2cd00750000104c87640001da9354a5340c008d5605087204161851e000077cd03587a3051e62c079d84b000008a90000000000000000000000000000000f0d80000b3000005c61fbe0e4800000001b8f0516313910e8000075e00009ca1941000078e85171cad079000002fe10620000735914683901bc0749819e1a9b342c508c1820418000039a800002fa20e400000000000000036f8000138d0000000000000000000248400014c70edc0000bd98f22411c05f400000000000754cffd02591332519c414a1801dc8442c1029e9c200a1b74d109c7a0000050497c8b6232ee00001fd0291015200000000000279e00006450ff428ee604500101820000000000000001e9459b04a6145c1a3e4b4c000000031a20000fc100000d180000000068f000033b80000000000000000000b2f000000010780572000000000000000000000000000000000000003c08000078c0000ca180003df20000dba1057000026b800000000000000000009b100004dbc00001cf0000315400019b5000082089050000329a4b6cc500f310a645a6c0000fbe3ffe000032f0ef1426400010659c4429e4000096780004128536cc510cb03f0e6671150800034b4859862e220500007fa84be00003c2e66790050edf414a8960d920741058e45f0000000021026c7c23f141e30720000b3885922e5a66b0896810b2abe4b3400000000000077800013ad00000000000182800003fe40000000000000011371d5801c00ea8b8807d83e7c0000000090301ec1e1004000002ec200000001fec44ac000006795cd30e600003bf159b000000000000dc625301e9cd6aa06f1b3637f4212188404160000000000000000000000232c235830c060180000c12230cf550000000003580000000247c00000000000021000000001d730bcc00000001bc700000000000031a23d211f50120efc2b6c860800000003bda3a9800014de000000000001e27000000000002369000000
  | 62 => 0xb4861d0000033300000b7c000000037602c344ea87b7402422200f19c99048404dc000000000000000dee18f7000000001f583b82ab058bc40600000da00000f068000284a0c48685000000006654400000018d66fe808b233102c675d05be9ace0000000000000002f763cb8f00800000000000a10910c04b43fa505500002630871800001e44252000059a857d0e5a69dc0001f5200002bfc00008e9000000011c28000232e72cc55a923730d236384df17c1000000000c6182b24b809980ed1acb20dc5c10be6043a02360000a1a800000002e480000b3800002b1c00009e005ba6fd47bb800029c088a00000c1800008260e861c9000004c707849de23d28331439280003d9c3fc0d520c7235c227351ad01a10000672c1778000000000000000000250c00000000000000076acb2d000042b40c7085d000011c600000000487016c6b24cada12839de02a10ec000000000000000088d39a457a000003e1337200000000de10f900000000000000000000000000024ca0cfc2f180002b8660c466f0000000000000001f660000000000000003b5800010571e03464230c4000191f000000000eb8000000000000000f94000028800000000327a67c86100000000000000001f8a00000000000000043160001034000000003b040000000159e00000000fa200000000000000000003b380000a930ba45660a230000389c07600000000268e580cb39929a296c43dcae5208931d4302ce6a15c02c5852000000000391a20245b200002f6a205c2fa16fb10d068707e311493ee836d400023022716081019a04913408763855006ff3bee3ac077284232e022588fb203bb2e0a174cc41824f1b306d9800010d216240000ba3940a384c33e0c0c92de33348a805208f010cf82dcc41380000000613c05f000026b00000f2993340c604ff89a60a370430017000020f9037679d88ba91f5000019b413000b8021e7b887b0a01542c01ba008017090000512c000000000000000000000023867f84000000036fa099c07d874c02ea8b80fe414ca129e68a48060c492bb65360a1315f41c361d10fae07b2040c4335146007d405675e4d28187f37f235ac1991cb1207a113c241000000000000000000025c601880000f243c1600001d9a10e30b001f800001333a380000a0d800000007c800000f073fd00000a4c852d00005f584e8858f00007424000182e3976000111a000000000000000000000000000e558000078e000014a0e2d44e22fb414c1c310d702d98000110730d842d4ffb9b1415a200004360000000068f11820d51184e0001178800018ea00004b990522b6a064c000026500006b180001e0729c21759136800011ba0000000129c01288ae400003640000098800000002a766028e0a8000390800000000000000007380f6a0
  | 63 => 0x1e35028c04f8b8000435c00000000000000001a400000000a7c00000000000370800000001b12142262e825d000000005c5822e80004372000000003ad000053c07ef00002e2251d10fb0000192212911cf1f43119421602cf86de0000000000021263f703e082f7a00c3ca048491b99ef8000000000002176060c13c8e7f80002150000000000000000000000013301192345400000002ea60000a6b8000000014acd04237b14ce44c037b0000365e837800008021bc460600001c08189a00000001b763cb429900001e11042c041000000000fa28b1449f02c53d5e562000010a3463e22603f4205100005ec4000000000004fb09229b3608920000000000031f8000000021bc000000002a8206a0a1a0de0543800029c400008bc8697420e06fc7aa82da11406d18e710c360d6c84f859e9a4200000000f890e3d08b00000b41847427907e5428180000000000066a9014167e00000001dfa000000000000000059a8c8c00007a503082700f979ef71e2a638c000027d12200000000218800008178000000011a0000108d000000007d64f999f7644c28d9440a9a0714ec3ff000010710fcc000050682312e1a4c043288000000000000001dfb00006268000199d000026944730509084e2a903a68000000043a027c0000000000006bf02de312a0000764000017644928f1b915e0a340000c0f05fb00000000b5f00001c6c00007d494160bf00000a55147531766f98c02000013280000d5080003a8e00001fe800023ee83b8ec89c110000735c000160b0000000079082cb03604c2c00013e224c45ebc00000004386000000000003ad04d68e410000000021a400021db40ea00002b20ce6203667b400013bb00008c20a0d000000000000000000008e65e6400010030a1834811a103460ff451b8000000000007ec0000000000d80000000000016882c9d10580000000000000000000000000000000002076000034c9a28000000007c080002fae0000dab013239825174000000000008040e318000000000000000000000040240001beb00003c649c414060000000000019b335cc847c9af000034127e8cb4d015f00005cfcd8c000000005398bf8800000001b8483d8c2d3d668f8c0000000000075b40000000223856185e203e81c4c2bdc000000026fa000000015460000000005892670000569c00007b608e20000000177b066200000000000088a41f80000b2241ea281c00000001ade000028700000000000032e800000000000c519629310c000089d800000005a3c759001146cc89748f90000000000005d193f50000000000008f0265e8b4c69c0c5211264650000176a0000359cc91049d000005e47bf8000344e39bc886a1df23a4388cb62a07322fe0000e8d8053000040b0132008e1daa6db80000ea1437000007e69327432e0
  | 64 => 0x2f7908c0b9b0dc808f4bec800032aa00000000000000000000000000000000000000000000000000000000000000000000f8a00008d040000d2700003d5c7ec000031280000724222e0000894415d05420000000000000000000000000006ee00000000e6c8000415264688a080000a2600000000d4a03ac8e20000000044960000cc30000205a000000022d827cc0000bff87a43020000023400003efc7fa45c8874200000000faa0000000056700000000017643e800000000000118c4fe1235401282b40001ba11e28000106b8000000000000000000452a00000000f123afc0000000174300000000000136100000000a1b17d2000000cc90f0b8700000000b5b0bfe2880772c26600000000000065417e200000000bda00001c2410180000000109400008f80ad6000025e000000000f6200001ab0000000000000000000000073e0f2e0e882c243910ec39cb433686e688e0851d00000000d6e8000000077bca17a36a2fb0000000007f31ba000011bf80003ec4000002b929638546300c690fb918800000018867029440000b16975b26724e688df0000000000000000000000000000000000000000002ab80000000565cac5000030441dcc5d60cd60c400000000000011be00007e080000000319400000000000847800000000000034055181dc10c80000b4b19481b5000007d580000000331c82d8ef7000064841fd89de06f200009a80e9d311c304062f95c4431287dc32696a33e8200004b6941f00000000e7500000000000110d800000000000000000000000000000000000007a2c000166400000000e62005235bc63d8cf280003bec0ef8000000000004f1cac9054944aa0000560171a22780b280000000000026f11a282bb000000003e28209134e00000001a393ba26b94a2401a40000000000000001222000000000003b600000000000000000000f921a2e10164399171000000006bdc477000000005be4d279f4040720000000057b0274607c0000000000054b0e17000000000000eb6138f28040000000000007ae48504a997b7305e0000b8e9c3541162c3863212a60fba000000008ba272c22c8bfa00000000227518c239c168c3b6cc129e9d08a400000002013000000005eb164a2e4202e4166105914aa1ecc000070f000000004129293130e00000000a52057258580000000000000000001e74000036d0ad700000000000074a00003d0600005f7000000000000000231100006658d0d12491400000000016d000000000000100d0000000064c9d1e000000006889e401f6c466856985dc1a1e0480d1902960bb677a0b2384de471200000001b2e0000696054921080fc43de42b19fbb18f200007e713443e10000035900000000000000000004600668003b95800c0c8acccc90f0d4532350cea8034139784e6caf29
  | 65 => 0xa3683cea8e1c000130f28e2598471e000000007928000030200001ea4afe80003c6a4178630900000006bd907b80002aac22c0982800020aa32f4000140b00000000042000000002fec00011432ce8385000000002e7200d4000000000000000b0f131f00000000000000024da6f00000044b281e0000000000033a000000001e2f00002cb84030000275223200000000287a2da000000002e6c0000000196a4404447c0af1fe0231053d0dd6093624ba000000000a30a88000000002be00007f3c06e0d4b1af83750a3592b70000000095a13b628247ae8914962425100560039852a3fce3ae4ba8942a2ed64e79199971f121000f400000000000000026c19240212000098d060534025c60367081635d232bd15304d70000000097f11af00004d90aed066b43760000c24000000000000d48800011720000000074000005268000000000001ea10f30bf000004284a9a00000000708c000158b1ee272e4000000000008d7c828800044e6817430d00002d6274180001e122aec460cfed06e742f24ac808e00003ad6059c25c177500006b700001daf2cc65d806648de5000022b8dda0000000024c91728f2525ee000000000003048844c52c800034043c402c986473f003e64000053413000000c0d8b4b20ec66bc37604d20bfe078806a800014ac674ce0e9ea1000071c8f5623b700008d900c198bc45e88adccfb853c44ca0000fd11f043f7400003d7221c2d100730a7987ce381a3b403ab000023d81fb4000000000008a2036b000000000000b3803bc1faa13102ca1db415f0317861d80001c0c0000921207406dc0000c4d800000007dc40001018000011280001f18122c5eb87f28000000003000000fcf000000000000713000000000001a8c000000011678913000001900000000242a0000dec9b451c6e0000000000031685fa800008d841aa13680b88e8633ba5d3c2b818d50000257463700002e60622475e9dd300007088d71895811a24950b9e000000001f3c0002031355a090c93b00001294222412ba1d400005440000151818e66fa4000078c000019602280e8e000000005179a4d1f66310871416f700000000000000000000000000000000000668c2f0000000000000000dc40000588c000056000005f3800000003b4800001c7800039fa5a700000fe2000026400000e6b08e4000000007c234c0000000013cc2d8c2b6000000004746000099e058e0bfc4ecc451122400000000d9c000044344739102000000000ae0000000000001954000000000000000000065a00000000a6f8000000064a80dc0000000000008b709f0114e0000e1800000000000000000000da27c7d02a800023f213845259e311bd00001158800000000000000000008ce28f80001be321e200000001a0e2908187c2360f581c820e28d968c093e4c
  | 66 => 0x7b8000176213d861b418a1034000038e4cd300001b5870dd02918e01512256c580206300005db8190238c000006b00001e9700006c940000f494500836cd318755000009705aa8ea800002cb40001537053600008ee187613cc0000000000018cc0f38470800000000000e1c80000e2c2a9d1c1226746ae877000016a4000000000001bf60000000103d00002d16000076e0e421aa64a40b7d07af2cb225f4000193f00001cd05bc879208cc46746950a9603e019a4c5200000000000082689ab00001e1400003a500000000000099b35740000000000000002f1400000c82f12215800000000000275800000000c800000dd2800000000c78b4300004340819468720c900007ea08a7189d000051f81cf800018f64094a7f800000000c44b1993d40be07ff4092800044c800000001d8c22a6000031a83cc197e186d0179748000000002988000265c603c00022f622f68b91113800004aa57b89a012f22312872c49d8844000000006a4800000000000000167c00000000a2783430f261254b3794fb2e8a05681868fb42db20000f4a800000007af0c7580000000000087706c800000000b90041f29783bf85ae80002f000478000000000005974000000001dc8eac0001c2719a800011e083841e64737c000025200000000000067e309c00009779b9200001abc3e18000419a00000000000096a00000000000000000004658000000006bc00000000000016844a8000035a27d46d988383236000000000000000000082203a42adc7b6c8030af41b28094c7a7201700000000000000000000000bbf800000001488000000019e2000000011462304022c00000003c1c0a7098b983621344d1875c118d4202892119f22ec000040905159b910d3452310ff92e0000037d44c200002ef846ac1c9174400000c6ccae00f103026d8496c1097000000000000000000000000001fd80d8200007ca800023da00001c10d3b403225009bba3a73d4c8364000232806805490a86000000000000bf380000000000000001f100000000e798d60000014e0000198e098c7024000208146e815709728000154203f8c2607181fa41394000105c1e0000000000000249c8654fc5a1120000401c507000028307e690789da83dea867514da3b031b46c208fe000000000000000091b2406391ccbb061200001fa4848829a379600000001c2033ea246000000002862000101309b219080000c462286204c5f00bd38a2c2ca43ad00001ccc149457650be154021d4315cf4b1f5300000000000000000000000000000000007f900000000000028c0fab8b57010400000ce96d13164394484481ef00106910cd11ceb00001aa04608000114654e11318950478a0000dc39d21302a0514d3900000000593800000002e5240d8bcd0a8500004408e8b80001d8a6dac4e9
  | 67 => 0xd948e0000303000000000338797d0d080002cbe03b4e6691c6342a806d1a40a9b29f48d4486a21c83fe854c0a288bc30e74000081c851c0c922a60f8387750000000034aa29306101d901898c2e2b328a04e760000453000002d59cda19da00000001ed8402c8dac000000020566f8800019d700007314c63073d3590000000000001ddc0000724825b070c00009c909a000000000000000000005070e3a208d373e26740f0800000007c240001e19266a000071781a60000000000000000000000000000000606435c000000000001e2c00013a60b9c5e10000227e1b240000ac780000c6616a000022cd3db47c00799839c000049ec8e38000078a726ca840ee009000000509058c00000c5400014a300000001039142c40fe46c45e394f127002f8800022ad01f4000012c152519b420806e500000000000018e8e2c04ba412c739800022ae4978000198f0000769c0000000350c4dd4524000001e68564c290a5c00000000000121c1082000000013f200000000eee0000074c542c0000000000000009a69c1300000000202800000000000000000000000000f2a917700000444d3d80000000861c0000cef22fc00000001b1727ee0000000000035a800000001864000010980000601000000000001618169200005a6092a3d245fec0000a8200008b64ab61ced0646204c7f78000000085c0a430d26192e29f40001f4f063e000000000000d062d3828f800000001dac4f89f390000000024fa1ba000067900000000000039d80000b963cd448f000006d4366e28c8c8183cd000000000001cf11bde27044c100001f4c65c800000003e648c244c5800000005e70a1408e80fc00000b6e150536946edc000061004a000005ac8b750000043092b9030176a000000019b70000000000000000f74296c674809e000000000000000102000009840000170873a51828000001c000000004ce0f2a0e4c80e800004c200000000a2a01322bc902c80000c26000000000003f3e0000bc5004034fa67187a0a175475e00004fda3df278a00000001a03000066c400000003378539ce45173800005a74a8015c62eec0f8c3c8042139f672a0000000000008b482d71755344a66f8007891f18fc30582c49a123f1a4b4412a0d90062c03305398b832cfc750c48e22bf2120000000005363ca2000000020c039a253740001d820000000000000000000000000023d824fc7d60ea580d204bc6adc17d80001d18251400000000c8c4778000000037f000010d9000000000000d91000005320000000000026e27068cb3063c028c00000001bbd11f800006981e9a000000000001eca000000000000f6800000000d510000000000005e307913a101adc00000002e6e00002df91c500000000729070200001598000000044d0356c2fb988000004e4c0001a17000
  | 68 => 0x500000000170632980000cc4a0fe25f43d70b918b0f00005e1803286bf08ea0000000140c326a64b11958000219600000000000269c0000b57839d3774000000015130000667ca5596c00c9881e4000000017f23ba8bc8a2442ae863a46cf216e12ca3bcc0000000327050540001fcb38380404b4b97a303b2851479006e3060e8bc8c3c1354000000000000000472e6d8ccf000000000786000000001ebe79a51d713a5000058f0cb713791c560000e2513e022fa71182648e3a07ba5064696000000000c884b78fd400004eb80000000423a1ac09d3920b132e35dc617800000001834a1c800000006bc80000d0400000ff01b1021500000000000123d00000000000195d46ce00003ae10cf0fe85e3008d0000401600007f5a2bd0a98070c000200741f83be8dba800046fc578cc6397c62a56000072a86c40000857c8ea000000000c2452800003200000000000003582044c000000029660000e949a6827140000274000000007e5cedd1f061a020000a5083e246e027185d99e2842388b38abc18883b0600009b699c33bfa00003cf89ff0000122400019bf282624c40000c47000000000e8000000000000000000006ce36180778acc193061d4000092e26fc7a78f7e1e67444c0000e039b7f38ac7b34000000030180001026800029aa0000000227f00007dfc92c236e3e5c871c42a000000004e1113c92ff1168808c6e881c145e61a0400007b5214c2cac02c9c7c3a8456ed0c6000000005280c8380000000000066795b2000000000000000000000000000000000000000001d35000011b8492000009dc00000000f9c15683ec8e708000000000000ee800018e20000b81000000002118b0100000000000026a810e0b00586c00020fd35867d4400016da0a0e7bec0001dc81b8600009d8000000008fa0000000046a8386000000000000000109280000000000058d1b3a000078a46448e8b250a3fb07b9089e2dec7c34e8b10b41fcc00005730e8f170c000067811e444808200000006b00002adc0000000373a83ac00003de15e00748a5c1a451e040bdc29ba3761f00000000000000d468690000133f00001e1cf5a928f0000607031f0000000000b800000000000000000015ce000067d8afe0000435e00000f6000043f0555000006fb0000000000000000ae63cf4000044600000000f27000037f86d040000000000026a000023d200000c286758e4502de000000018f9120200005361c0124408f5047f0000346e00640000000120836ac39496ea3d005de502000003326000000000000000000106212a4000050fc0000000000000008da800001f000000000000000000001ee214600007c300001ae7176c78845629a311d54623417219a10c0609c0d11800023aa0000000000045bc2b08c0d19f0217080a04020ca53adc1b88d7
  | 69 => 0x77a29d2da875a88a8023e0d5865f4d1f0a3400000000000000028200000000000042881ce40000fba3d0247106bc800011364cd8676000000000000000000000003f0cebd800000002c590559bde236e0000000000000008c0d0cd17220000000110618ac000014282f4175a3ca84ae4b6914913cfe13d025f9d8d05804f7c0001fb500001810eb18000276a25d06b2800032024b7400000e5112400004a69f2131fe0000f1f013d12e200000000a401be28258cbd1d90019432047c8978323e87194ce405010e240900b568661000031f4f06106025460d1c7fd137b01be0000ed68000202446d8000000045841164ece80001d120000a6c951c0000197c3661af1146275d8000000001f200000000be9277e1548000150a0000000000023e13cb06d2500300000f2e0000c79a2eb000055dc00003bd31b25d34000212d1694000000016f32cf4000000009cc19826ad48b80585119e12b400023ce0000626000009c9000000000001fa600000000000000000004dd8000000015ae152c98388c70000000000006aa00004804000000038787ddc54e1ef0129271cce4d09fe250000000000aa5069c0000d5e80000fb81b1445304a70f36496800000003d6e44908f58e3e0000595472d10530000761089a176f00000000000000000007f70000057830be1df10c895aa3e0a28e422898262f04591881f8000253a385c00006a946bc000087e85d800000000000000000003df85349f7b01c66d6c046897b292807d516d9386433200003a48000000088e00002083352e66c8000107f000013740000000179a3a68a76000000004b05098948d000006507b784e90000000056aa0bb30ca8a58000000000002ff400013f80000296816d8000314c000073c000003cc8bec0001ab63f6819d505100063cde0000ac600001d768500f639f7c00000000f658628000000000000000196415e400020a400000000083000042a20000114800032804d9400014cd25aa0000cd41cf2241e2c7800015d300000000000000000001ac4fe08000218c00004d80000048253444d60000374024990a7800042b0000000002ee33e624b400003ea00004e3073d800020d8000000007113b8835a0a7489d900005f08cf617651af63c20e16a0c2180c26ecd3c06f500b00a0cb8c99e30a740000fe81a5400000000000000000008d30da002b43864000000009aa2e480000b020ea025e00000000128200000000013929701b07bb8059056517b414148ef803632c826d8e47988a00003ef0fc48d3900001214906800000007668000000039cc00000001edc0cfe00000000000326e6f602a721be37148bdc00000003bc60d24f93823f3284000090b00000000000000017c93bc2348c0001c0500000000e4f000000006aa4cc08000092c0f0888793c21d8e00003ff0e5007
  | 70 => 0x3e1400000002a900000f6000002cf61bd000001140000445ce0a000019680000a71861128e087a86fc88fb000070ad0b3800013c66ac4cff000025564370d76859a3b5400009318bd417c2000000000002078491c702094600000000f5485d436d43854000000016dc0df8000104a00000000f788e6303966cd4000000027c61b24e2d80004636508858b80003a980000043061900005204000183f00005b5400012bf35f2002823e0000000037d079a0000057e12f914d1ac5460e365485500000f9a5bbc0000000101000000001abb0e7c0000000020e000039d000000000ce200009de800000003a5ce249ec631f400000001b4743368ddc0bb00000000548c000000029de0000000000003f63918545063716a01f4c4d18000072e104850598aa14d400011278000000000002f980000000437c39780000aa855481f88e111ffe76d4a0480000000000055400001b5a0000000000042f65bb08a50000166c2b80dc180000000246884b02c12e1c29c41ac06c71c4067a900200001a1213046aa86f343586b08ab4192e18a84a800000b712208399432223790000000048b80003328000072f0000405c2e4c0001805000000001eb000017986f106198000155e7a9c2e1000046280000bca0000257c8864000201e41220830c4c8f372f4400001f480001d5a69d4f929f9c2642000000000001d74000000016b71dea22a817c000000007874bcf9dd928f235987a784ab34a651805be1c55000000006c6000008f2012ce4485c71bae5554204093c1e9a84d01c3a230196e000119f80003f5a56880000000000029240000000343c000000000002bf20000bc592f30000515888c102e1b8a6cf86480000000000000000000000000011e5000032b400005c49a6f000015345ae00001ab80f50000151900005ca80000000000000009048c152674891868f000038dc0000ccc013002e4128d178238300001af00000000000064a0b7e05fd35f43e6d03680002a5c0000000000000000bc800000001eb600009159b483da450cc000000000000000c5b8e5700000000000219f3eac3dd4917193c1a68687d06f800000000000000012721f263901e8098e318671ec00001e500000000000181d214e000000000001a9c00000001ec524f000007b49eab12c6000000012a100004a1d031187734a269ac017800000007bc8c5f920e12c078b4b95898516720000e32068d1a243dc000003b00016420ccbe119500000000d85177d0c9087b4ab101d32bd81ab474e000016624610504971b000069d846a000000000b10040800000007efc00009b5165000003ac014f00005a6506e8ec9000000007dc1dc60000032c05614f9098e00000000e0825ac5f8000019ca1c7000008d68cea4668328c47d229e000000009be00000b8c1da00000000000002d50
  | 71 => 0xa7680162bd470640000f180daa52fca5e80000000110c5e0002d0d08514000020c644e80000e71844c000000008ba11da00005b80a02222c452877e0bef8cb940960000976187a2f4873246b90000000026345028a6d000000000000000275e0000ace965646c67ad01f909f808ca25540001db93dce73c09f493a2000000000000385000016f0bd5800030427a4c000213c451282fccd20000000000000000c9c47760000d9a1e8a1e58000000006b9000000002528000000083a0fd8a1e821446c2c3ff80001c420be4000012800008d40fe900000b2a46fcdf98000461a6de8da800002c9835b4000107a00000598ad080001af006647fd94300aec000059000003af06784f879e7e00000000b2b8000000066e8be813eb00008b300000000000000000001319169e673000000003f784f1873e8cff19580000000198d0df0846c0000c762ac00000bb603663bd40fd4cfd8c7c00008e94cf41a4300000000a9f000011ea39fc000134f1c4e00011c694871e6a4d091298000096600010c70f423b423d1115f000000000000000000000000000000034a2e06541c42d00001d46000010b80002554000072c1e6d00000000cc29547213e8881024821233a251a89a28dc90000062474921832ba8211d07d800037dc34301ba12d7000051f47be0000000000000001d153c383d405ca0a7a390c768c000000000005a100000000384800003c70000180a8e2800000000000000005680003faa189486199eb000028f4000223941d4179cec00000000061187cfa085000025d51211cc342c6884075f00000000000004d800000004fe4af8000000006cac45e1cdb065c718871f9cb2000062e509f83ab000000002f60a5122d400000001ca133dc0868c58968d00000000000000000006be04cc0b5f42d4368880980002764000081400de0ec057e0112000000000cb4000000000005b8c0000000361a0000000210c417c00010da177a10980000c6f03a7025e0000000000000004ea88cb0d292cdc00000000b88132a00000000000000083c800008d500001ff400001770eb6675042e9f16000026485961ce700000000f5b22a709d858846cc8952000009f80000000282234340001cc7000000009a98000355c03f0000106633820000a040c7a04322144e1b0b651a66320c000000000000000000000031a0000039d8000000059008798cf2262c3bb4e9b0bae0000226401100002f7c67886de9f7947a2000024a2190000000000001e390cca6d741ea9b8c0000000000018a50000000000005e527926af05c00000000000000000000206622ec000055a000000000001d14101c0000f60800000005e34c34124839aa55308f2859700000000ab980003eb605a44729f5f0000000000008b53958048c5f18788107e1e980000a74110a77f112f859b0
  | 72 => 0x42740728000000000008cb88ad924c0a908f8800018590000000059d8f963c6c00007619df91f4059440000e8d00000000baf161415ba00004f38fc93e560000ab380001b8e87ac66721f3117a07187e6042016840304bdc1aec1b520000f76a01f248660a844a19ef2d4a00000000d8f0e8c00009960000258a000000000680cac3ec400000003c9884bcdd196eb36b000005e503010000000050a838325225bf40000000000087c400a000000000e6800018e545580000000229221560000e81146d38cc3e6000004f91cfc0000000155719a2136cdeb894b000025782409da500000000b9e8fbf000007cc00000002aca362cd66000046c400000001d642528659c93aa2221d440000ce7000010643508000000000000000000000000000000b498000000031bc65480000000000005e207100008894000000000000000028000042720000caa18233f100000000053b109e0f482f1170700000000afb0baf000000000001d7139448068865000000004fb91cc837f163859e079e000034260000000086d00000000000000031c255d46d814d62bf4000002a00000cd81d3ca90000000005d700000acb000000003b8a05b07862f488c000002fee0a9809a92b300008ef4c09914c000000000000000037a70cc00000000c9e73d09b49e5947420804096098c381c4d243cd1bbf12f276c8068935d1b4247fc4811135000033ec0000ded239400004211d8b000000004bb1fa5362c35cd1719a8f195c00002ae88190d0e000072e88f722be0000649a2ea00000000000000000003e1c00000000000000080711c90ee84c10ac3a3122c34588101d11a02e6853a82c183183a666c240001dcd34b82b24a98a3403f923d300ab807c411839f0f8c97f300006c0400000c33a140000d6205751e566140baf857c133400004b71ea2000000000002038000078b0707800018a2394c00000003dae5ff40000cb6451c7ca8a5d000041ca00000000000000081a409a000000000000c2e0000000014e4d0c0000151e8980f39000001a8768000004f600000000b4f94c800000000000000037ce0000bf323d000000000986800000000000739075000000000f341ead380c28e80000000223619f4f12823b193a28980001bfe000000000001f36000036a806d213d2c743a4c27f19203e927c684c512f80c5a65491df00002bc42ddc4c40e54000018c400000000000000116022ab012a8130000000000000000000121330ac00000000000000030840000000476a00080ca997e41a4000083800000000000000014bb00c61fc8000000021720000000000037c828309d4230a02d4895099b9c1047ca00009458f46160623b40001a52157081dd1c88000419e4554a658000000000008398b97195600002681ada11220dc0000000000004c24000028d00005f74
  | 73 => 0x80000aa21740000000000910d4e0bc454e96cc1e385f4c00008d60000000054f8c2a392287086b514692640054425e0bab00004e40ce2218100005b1c00000002e4c000000009ed00260000000000000006108433000000000000000000000000000d5180002364000000008a5002a39591c81d960000000089c81601878000000001683d4025f8e2620e31370000113484252b407e380000d6442700000ec0800041ac00004a8800002a6000000000000000000000000000000000024c0000129c00004611dcf065e4618b1900000000309092b0000000000000ea800000a200001cca3cf0000633c00000002d0a84d8000003200002fd43908a6822b81a4ce960a16013828705f2000000005814e4b800014504b980000000000000000001700000000000000000111e0000e6809fa1b9c00000000be0000013e804d0c38225200004cb00000f9800008e985cb20ea000000000000000429061f91fd31240000000128c254e798c9020000081a534800017e1000000000069dbc00003ef4111800000001df4546800047cc0000961867800000000df50000000070a400021fa00006f3c7c91a7c2bea126400008790736000025a037237562fc858405c1351475347ae890917b213fcc9d80003d3e5c70b5701f800000000ef38000000024180000000000000000000000000000000000bfa463c38a800009d0000076780000e4d209087746898e3b0c4210302da0000462c4b9cd87885937ac64382aca08400000000475800000005aa80000f59000000011c20000000006b846d8765263c000000016d800004c900001cf7399079b0004a3da17e88f240000150000000007b3085c438a7b8400003803772853863a17f60bbc63989200000000021e062d9d4e29ee222800000000a662e6897223221d6c000000000003a1e5fbccb411e3422a00000000000000000000001d4900000000000223636a8000000019de00000000cd39675110c80143ae800000000000000000019ce00000001f451c680000db1000000000000000162700001d5c0001694256a6ccc00023c000007140000000000001870d1e87520444531000004690c867a18b1413100b2000009451da2412087f808c017c000076dc00000003e9c077cf0200923b804bf501490a018ce13b4dce0c3919d08e485cc0cdd24de635d0618138000000007ec922600003f7d08a00001b0400000001eb0000000003320000000000009f8138e000067591ae800000004d64000000000000000000000000000000605000000000000010800042b8000091800003a5416c40000000195a115c625000000000000000220e150221948e8988f28f034e8641143a41b43c10fd500000000249c8a6a13b073c0000963000000003278000112042a085b4f5e8e6100000000000120500000000a138e83
  | 74 => 0xc0700003b84000000002a036a64ff005b800015d21e8402b1bfb007000011e680001ee834946e680002fca00007d683a031d800000000abc000000000000c6c2a780000da1800000000ff8eed921a00e8558c00014320000321cf81096825a415b519e000041fe0000000081c2ffc0000da7848f3f3642f4e610f84000059d8000000016a42a000000e250000177cb1b8d35000029f0f0b1193000000011088000000000006a29b942dba399c0230010076a2f988cd80000000000050f232405d60bd86e000d31046275c5300000422c07f0000115a0000550c9161f4700002a0c53b800000002750650a24912660000d4110b300003164aeb0000000062a00000000000027700000000000007ac6260b0b0b523dcc000093437825408000123101120000000000000000000bde8000418a0000000017a45060000000000000005f3c3fd800000002e748c88eca1bee00005831f0b00002ba805f8f160b9e2c6c1180ddc000086880001a3a0000000020e204600001ddc7698bfc3d926724a8d083a0000569495893da000000000000000000054a00038d1705e80000f17227a113e2ac00001f1c00000000387027300004d6cfc180000d42357d114a2d5096451686c205d040b061680000000000087d000000003ff80000000183a40866a643669f132b9007a4b22000009c4000084a000003741f7c84f10401cb6592061a057420c2000000000000cce07dcf8f1ee8126e32c450400000ccc033500197782d702dac19615f100000000000000000000000bce94ee029049b0ee50da628f48b2c000163623ce0000275000c38fc7a340b60da02e9226f46020d0519407ed88d215e0399600000001341406e08080001f29000030f80001a2f00008d60000196b0e5000008959ce400003b0849c1dd618525d900001cba000000000000e0521a00000000173b0b1a00000000000363c000000013912e645b0916b0f8e388200000000000000000000000461000000008cc000002b8035d1ee00000000000000000000000000043a8000110000008a9000022460000187116f00000000000000000000b1
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x862d649885204326b1cc4290219558e6114810c72c9300a40865963980520422f398cba1021175cc65d08108eaeb30e840845e73196420422eb98cb2102117dcd65508108b8e6b2a840845e73195420422eb98caa10211d5d46150810c6aa830a840866552185420423cba8c0a10219a54860508108bce6328840845d73194420423d380ca210210f9d065cc81087ae832e640847575987320421f3a0cb190210f5d0658c8108f2eb304640843f74595320421e3a2ca990210f9d0654c81087ae832a640847575185320432aa98c2990211e5d4604c810cd2a4302640843e74d94320421eba6ca190210f9d0650c81087ae8328640847671194320423d380ca190211b9ca64944108dae5324a20843e7498a510421eba4c528821361cd60904108bce7b28820845d73d94410430f2a2c62082187551631041087ce9b28620843d74d94310430eb24a61882187591530c41087ce9b2c420843d74d96210422f39ecb10821175cf6588410cd2a530442084d87358021042d2ba4c4108211ddd95208410acaeb2104208665659082104332b2a8410821781c14208410acaea19042085a5740c8210423bbaac010821741cd60084108bce7324a00845d73992500421f3a4c7280210f5d2639401087ee8b0ca00843c74586500422fb9ac328021171cd61940108dee4b0ca00846c725865004272392c3200211b9cb65100108dae5b28800845e73194400422eb98ca200211b9c865100108dae4328800862e545884004316aa2c4200211e5da51cc01087ce9b2c600843d74d963004237396cb180211b5cb658c010caaa730c600843e74194300421eba0ca180211b9c8650c0108dae432860084e47258430042ccba4c6180211edd9530c010ab2eb21860086596590c300432cb2a8618021741c5430c010ab2ea1906008599740c8300423dbaac218021781c9610c010cb2cb1886008659650c430042ccba062180213c5d8210c010f8064108600856575086200423bb8eca900210f9d3650801087ae9b28400843e74194200421eba0ca10021179cc65080108bae6328400862d649482004316b22a410021595d42108010d4ac810840084757518b100423abb4a3080211e5d463840108f2ed28c200863765d91100431bb28c88802195d976344010caeca31a20086946418d1004333b2ec4880211d5d662440109cce53122008667651891004353b20c488021a91906244010d8ec631220086c4631891004332314a088021b818b4044010dc0c4202200863b65d91100431db28c88802196d9763440108f2eb31a20084da7398d100432db28c688021a6d906344010d30c831a200866b65d89100436431ec4880219ad946244010d50c831220086c8631891004370316c2880211e9da5144010cb0c728a20086d063945100436831e8288021b418c4144010
  | 1 => 0x304421ebb0a9982218799353cc110c3ac9a9e608861e6414f304430eb20a7982218b99352cc110c5ac9a96608862e6414b3044316b20a5982219514e61cc110cc8a530e608866452587304421f3a6ca982210f5d3654c1108dce5b2a608846d72d95304421fba2ca982210f1d1654c1108dee4b2a608846c72595304431a2a6c2982219914b614c110c68a830a6088657531853044332290c2982219914a61c8110cc8a4b0e408843e74d95204421eba6ca90221179cf65481108bae7b2a408843f74595204421e3a2ca9022117dcd65481108b8e6b2a408843e75d91204421f3a8c8902210f9db5448110878edaa2408843e76151204421e3b0a890221179d76348110c3ea9b1a408861c54d8d204422f3a8c69022187d506348110c38a831a408845e76d4d204422e3b6a69022187d935348110c38c9a9a408845e7614d204422e3b0a69022187d905348110c38c829a408862f64d492044316326a49022193d8f5248110c98c7a92408862f641492044316320a49022193d8c5248110c98c6292408863754d85204431a2a6c29022195d4f6148110ca8a7b0a408866452d85204431baa0c2902218d1506148110caea630a4088654531852044333a90c29022199148614811087eedaa0408843d76d50204421fbb0a8102210f5d85408110c3cc9a98408861d64d4c204430f320a610221875905308110c5cc9a90408862d64d482044317320a4102218b5905208110ad0ea90040886a96448020443942a24010221d214d2008110e36a829e20887185414f10443a429ea588221ca15052c4110e90a629620887145414e1044393aa0a508221c91505284110e8ea629420887445314a1044237396c2aa0211b5cb61550108bce7b02a80845d73d81540421fbb2a82a021875516315010c5aa8b10a80861e6458c540432731cc42a0219358e6215010c5cc8b10a80864e635885404326b1ac42a0219558e6115010cd2c5300a80843e74189530421eba0c4a98210fdd16154c10878e8b0aa60846f725855304236392c2a98210f9d36054c1087ae9b02a60845f7654c530430eb22a6298219354d6214c10c3ac9318a60862e649885304316b24c4298218b9916214c10c5ac8b10a60864e63588530431ab24c2298219958a6114c10cd2c5300a60846e721974304236b90cba18211e5d660d0c108dce432c860846d721964304237b92caa18211b1c96550c108dce432a860846d72195430423aba8c2a18219554c6150c108f2ea302860863954181430432ca98c0a18211b9c86510c108dae4328860847671194430421f3a0c6a90210f5d0635481087ce9b0aa40843d74d85520421fba2c0a90210f1d160548108bee6b02a40845c735815204237bb2a4290218b5915214810c9ac6a90a40861e6498c520430eb24c629021879916314810c3ac8b18a4
  | 2 => 0xc2192219914a610c9108e8eab08648866452584324432c29cc0192219a14a600c9108f0eab0064886585358032442373acc5a0a218bd5262d0510c58a9316828864f5398b414432629cc5a0a211b1d562d0510c5ea8b16828862c5458b4144327a9ac5a0a219314d62d05108deeda96828846d76d4b4144237bb0a5a0a211b5d852d0510c70a9306828865853983414432c29ac1a0a219614f6050510cd0a5b02828863b54181414432c298c0a0a219a1486050510c3ea9318828861c5498c414430faa2c620a218715163105108beeda98828845d76d4c414422fbb0a620a21175d85310510c9cc7a90828864d63d484144327318a420a219358c5210510cb0a7306628865853583314421f3aec898a210f9d4644c51087cedaa2628843c76d51314421f3b0a898a210f1d8544c510c3ec9a9a628861c64d4d314430fb20a698a2187190534c5108dcebb12628862f54d8931443162a6c498a2193d4f624c510c98a7b12628846e751893144317aa0c498a218b150624c510c9ea6312628864c5318931442373b6a498a211b1db524c510c5ec9a92628862c64d4931442373b0a498a211b1d8524c510c5ec8292628862c64149314431daa6c098a218e153604c510cb0a7b02628866b52d813144334296c098a218ed50604c510c70a8302628865b53181314432c298c098a219ad48604c510cd0a4302628843f76d50314421ebb6a818a210fdd8540c51087aec2a0628861e64d4c314430eb26a618a2187990530c510c3ac8298628862e64d483144316b26a418a218b990520c510c5ac82906288554754c4314434ab226218a21c5151310c510e88a4988628843e75993214421e3aac990a210fddb54c851087aedaa6428843f76153214421ebb0a990a218799353c8510c3ac9a9e428861e6414f214430eb20a790a218b99352c8510c5ac9a96428862e6414b2144316b20a590a219614e60c8510cd0a5306428865853583214431c2a6c090a219614f6048510c70a83024288658531812144335a90c090a21179d663d0110c3ea931e808861c5498f404422e3aac7a022187d5163d0110c38a8b1e808845f76d4f404422ebb6a7a022117dd853d01108baec29e808864e63d4b4044326b1ea5a02219398c52d0110c9ac62968088634549874044332294c3a02219914961d01108bce7b2a808845d73d954044237396caa02211b5cb65501108bee6b2a808845c735954044237b92caa02211b1c96550110ca8a7b0a808866452d85404431baa0c2a02219514c6150110cc8a430a808862f5498840443162a4c42022193d4e6210110c98a7310808862f5458840443162a2c42022193d4d6210110c98a6b10808846f76d484044236bb6a4202211bdd852101108daec290808843e75993304421e3aac9982210fddb54cc11087aedaa6608843f76153
  | 3 => 0x5353d4910e18a9a9ea48852e7494f5244296ba4a7a92214bdd153d4910a58e8a9ea48870f5414f52443862a0a7a92214b9d263d4910a5ae931ea48852f7458752442963a2c3a92214b9d360d4910a5ae9b06a48854e73d8352442a6b9ec1a922187d526394910c38a931ca48861f5458e524430e2a2c729221879935394910c3ac9a9ca48861e6414e524430eb20a7292218b9935294910c5ac9a94a48864e63d4a5244326b1ea529221879926394910c3ac931ca48861e6458e524430eb22c7292219698d609491087cedaa2a48843e76151524430faa6c6a9221871536354910c3ea831aa48861c5418d524422f3b6a6a922187d935354910c38c9a9aa48845e7614d524430fb20a6a9221871905354910c3ec9b1aa48861c64d8d524430fb20c6a9221871906354910c5ec9b12a48862c64d895244327b1ec4a92219318f6254910c6ec9b0aa48863464d85524432bb1ec2a92219518f6154910c70c9b02a48865863d815244237bb2a4292214bdd15214910a58e8a90a48854f7354852442a639aa4292214b9d26214910a5ae9310a48854e7398852442a6b9cc4292210f9d0601491087ae8300a48862e65d505244236bb4a829221539ce5414910a9ae72a0a48846f7655052442a7b9aa829221531cd5414910c5cca2a0a48864e65d4c5244387aa6a629221c315353149108daed298a48852e7494c5244296ba4a6292211bdd95314910a5ee8a98a48852c7454c5244327328a629221c3d505314910e18a8298a4885697019052442973a0c6292214b5d06314910acae2318a4885697018c52442b33888629221595c44314910a5ce9b08a48852d74d845244297ba2c0292214b1d16014910a9ee6b00a48854c735805244297ba220292214b1d11014910a9ee6880a48854c73440524422f39ecba1221175cf65d09108eae3b2e848845f73597424422e39acba1221179cf65909108bae7b2c848845f73596424422e39acb21221179cf65509108bae7b2a848845f73595424422e39acaa12211ddc565509108f6e0b2a848845e73d94424422eb9eca2122117dcd65109108b8e6b28848863854980424432c29cc0212219a14a60109108f0eab00848865853580424421f3a6cb992210f5d365cc9108eae3b2e648843f74597324421e3a2cb992210f9d3658c91087ae9b2c648847970d96324421fba2cb192210f1d1658c91087ce9b2a648843d74d95324421fba2ca992210f1d1654c9108eee2b2a648847b70595324421f3a6ca192210f5d3650c91087ee8b28648843c74594324421f3a0ca192210f5d0650c91087ceb320648843c75590324421fbb6a8192210f5db540c91087eec2a0648843d76150324430f326a61922187593530c910c3cc8298648861d6414c3244317326a4192218b593520c910c5cc8290648862d64148324432a29c
  | 4 => 0x3ae72a481084e472586408428eb9ca8204218b9516210210c5aa8b10810851d7494e308428eba4a6184219594d610c2109c8e4b08610862d649482084316b22a410421a95902108210bc2e010841086a96448020842f038a40104214bdc961d5110a58e4b0ea88851f73583544428e39ac1aa22187d526395110c3ea8b1ca88862f5498a5444317aa2c52a2219398e6295110c9ac7314a88864e6358a5444326b1ac52a221999896195110cb4c6b04a88861f64d8d544430fb20c6aa2218bd936255110c9ec7b12a88864c63d895444317b20c4aa22193d8c6255110c98c6312a88865463d855444332316c2aa2219618f6055110cd0c5b02a88843f76550544428fb9aa82a221471cd5415110a5ee4aa0a88852c72550544428f39cc82a221475ce6415110a5ce5320a88852d72990544422f398c22a221175cc61151108dce4300a88846d72180544429ab88c62a2214e5c06215110a5ce5b08a88852d72d84544428f39ec02a221475cf601511087ce9316a68843d7498b53442a7394a9a9a21535ca54d4d10a9ee4aa6a68854c72553534428f3a4c5a9a21475d262d4d10a3ce9b0ea68851d74d8753442a7396c3a9a21535cb61d4d10a3ee8b06a68851c74583534430f326a729a21875935394d10c5ea9314a68862c5498a5344327a9cc529a218bd516294d10c58a8b14a68864f5358a5344317324c529a218b5926294d10c5cc8b14a68862d6458a5344333312c329a210f9db5454d1087cec2a2a68862f54d8953443162a6c4a9a218bd506254d10c58a8312a68861f64d8d534430e326c6a9a218bd936254d10c58c9b12a68864f63d895344317b20c4a9a218b1906254d10c9ec6312a68863464d855344332316c2a9a218ed936054d10c70c9b02a68866b62d815344334316c0a9a2117dd95314d10a3ee8a98a68851c7454c53442a7b92a629a21531c95314d10a3ce9318a68851d7498c53442a7394c629a21535ca6314d1087ce8308a68843d74184534430f32ea829a21175da5414d10a9ce52a0a68854d72950534422fbb2a829a2153dc95414d10a98e4aa0a68861e6515053442aab88c829a21479d06214d10a3ae8310a6885557118853442acb80c429a2147dd16114d10a38e8b08a68854f7258453442a6392c229a21479d36014d10a3ae9b00a68851f74440534428e3a22029a211b9cb65d0d108dae5b2e868847970d974344237b92cba1a211b1c965d0d108dce5b2c868846d72d964344237b92cb21a211b1c96590d108dce5b2a868846d72d954344237b92caa1a211b1c96550d108eee2b2a868847b705954344237396ca21a211b5cb6510d108dee4b28868846c72594434431a2a4c221a219514e6110d108e8eab08868843e7498f524421eba4c7a9221539ce54d4910a9ae72a6a48854f7355352442a639aa9a9221c3d
  | 5 => 0x852d7295042c421fbb2a8216210f9d065ccb1087ae832e658843e74d9632c421eba6cb196210f9d2658cb1087ae932c658843e7499532c421eba4ca996210f9d3650cb1087ae9b28658843e7419432c421eba0ca1962187592530cb10c3ac8a98658852d7295241c426c39ac120e214b5ca5410710c3ca8b18838861d5458c41c430eb24a618e2187591530c710d2ac898863885d0704c431c4296ba4a510e214b5d252087109b0e6b00438866a5258021c4296b94a9a06218795163d0310c3aa8b1e818851d7315240c421f3b4a8a06214b5ca545031087aedaa0818851d7315040c4317aa2c4206218b1516210310c3ac929e618861d6454f30c431cb2cc9986218e59564cc310a3ae829c618845e7694d30c422ebb6a618621475d0530c310b32e9318618847976d4c30c426cbb6a618621749c7530c310b32e829861885d27114c30c42ad3ac8618621569d4320c310b32e819061885d2710c830c42ccba06218621b4584310c310a5ae9296418846e7694920c4296ba4a490621999486148310ccaa430a418846d76d4820c4316b26a4106218b5905208310ce2c3306a90861f5458e548421fbb2a82a4218b5516215210a3ae7320a90862e64588548430eb9cc9a9c218b99262d4e10c5ac9316a70862e6458b5384316b22c5a9c218e99260d4e10c72c9306a70866a629835384334b14c1a9c21875935394e1087ce8312a70843d74189538422fbb2a629c21475d26314e108dce432e870846d721974384296b90a9a1c211b9ca6590e108dae532c870851d73952438428f3a6a721c211b9ca6550e108dae532a870843e761514384296b90a8a1c2195d4c6150e108dce4328870846d72194438428eb9ca821c210fdd95410e1087ce931ea50843d7498f5284237bb2a4294218b5915214a10c5ac9310a50845e73d97428422eb9ecba1421475ce54d0a10c6ca8b0e850845e73995428422eb9ccaa1421475ce5450a108bce7b28850845d73d94428421f3a6cb994210f5d365cca1087ce932e650843d74997328421f3a0cb194210f5d0658ca1087ce932a650843d74995328421f3a6ca194210f5d3650ca1087ce8328650843d741943284316b24a4194218b591520ca10a3ae72a6830862e5458b4184316aa2c5a0c214b5c8549061087ced2a2830851d73951418421ebb6a820c214b5c85410610c3ea8b18830861c5458c418428eba4a798c21179da534c610a3ae929a630865a53181318432ca98c098c21175db530c610c3ac9a98630861d6414c3184316b24a590c218b59152c8610c6acb3264308635655932184296ba0a510c211b9da52486108daeda90430852d7414821842d2ba4c410c211d5db52086109caeda9043085e270d4821842d2ba0a410c21789c05208610acceb2104308566750c821842d2ba06410c21789c03208610a
  | 6 => 0x1082b2b88a6108418b5526108420e4aa930842107255494421083932a2a210841ca5526008420c5aa8b004210729545802108275baac0108419add56008420d56e8b0042106a8745802108335aa2c010841aa9516008420cd2a8b0042106a9545802108314aa2c010841b2dcd6008420d90e6b00421043e7498e500821eba4c7280418795263d0020c3aa931e801061e5458f400830eaa2c7a00418b55262900208deeab14801062d5458a4008316aa4c4200418b9516210020c5aa8b10801043f76953300821ebb4a9980410fdd954cc02087aecaa6601062d5498a3008316aa2c5180410f9d2650c02087ae9328601043e74194300821eba0ca180418b552620c020c5aa8b10601062d549872008236bb4a5100411e5da528802087ced2a2401043c76951200821f3b2a8900410f1d95448020c3ca9b1a401061d54d8d200830f2a0c690041875506348020c6ca9b0a401063554d85200831b2a0c2900418d5506148020c5ee9b2a401062c74d952008317b2ec8900418bd9464480208dcedaa2401052d759512008317b2ca8900418bd955448020a5cecaa2401052c765512008394382a89004193d976348020e1aa9b1a401064f6518d2008346320c690041c35506348020ccecbb0a401072554d852008316aa0c29004199d946148020d4ec830a40106a4641852008392aa0c290041b1d8c6148020d88c630a40106675418520083532a0c290041995506148020d4aa830a4010625541852008370b80c2900418b5536048020e52a9a0240105ca73d01200837030e80900415a5d44048020dc0c220240105aa74cc12008394aa66090041b81873048020e52a818240106e0610c1200831dba6ca900418e1d36548020c76cbb22401063b65191200831db2ca8900418ed955448020cb6cbb1a401065b6518d200834c320c690041ca5525248020ad2eba1240105aa740c92008339b2ec2900419cd946148020d60c830a40106d0631852008371b10c2900413a9db2148020b54e990a40106726158354c4317aa2c52a6210fdd95415310c3aa8b18a98852d7299054c430f322c62a6210f9d262d4f1087ae9316a78845f7654c53c430eb22a629e21875926314f108dce5b2e878846d72d9743c4296b94a9a1e218e95160d0f108dce532a878846d7299543c4296b94a8a1e211b9cb6510f108dae5b28878862d7299352c430f324c7a96218759263d4b10c3cc8b1ea58861d6458f52c431b324c3a96218d59261d4b10cacc730ea5886556398752c4316b26a5296210f9d06354b1087ae831aa58846f7654852c4296ba4c429621179cc65d0b108bae632e858851d7315342c422f39ccb21621175ce6590b10a5ae52a4858852e74d4a42c422f39ccaa1621175ce6550b1087cec2a2858851d7315142c4335a90c0a1621179cc6510b108bae6328858
  | 7 => 0x790241cc15051c8120ea0a628e409070c5414e2048393aa0a310241c91505188120e8ea628c4090744531462048333b20a310241995905188120c3ac631ca81051e7318a540828eb98c52a0414b9cb6195020a3ce630ca81051d73186540822f398c2aa041175cc6155020a58e4b1aa8105377158d540829a38ac6aa0414e1c16355020c3ac631aa81052e72d85540828fb9ac2aa041471cd6155020a58e4b0aa81053870585540828f398c2aa041475cc615502087eecaa0a81062d6498b530831cb24c1a98410fdd16194c20878e8b0ca61043e74185530821eba0c2a98410f5da5414c2087eecaa0a61045f7654c530831b2a4c2298418d5526114c20c6ca8b08a61063554584530832aa9ac2298418b5926214c20c6cc9308a61063564984530831b322c2298418d5916114c20cacc6b08a610666625845308332392c2298419c5866014c208dce432e861047a70197430823b388cb218411d5c46590c208eee2b2a861047471595430828e39aa8a18418b5536250c208daea312861062d54189430831caa6c0a18411e5d46050c20c72a8302861046e72194430823b388ca218411d5c46510c20a3ae72a0861063954582420822f39eca21041175cf6510820c74a8b00841063954982320832ca9cc1190418e551608c82087ce9b28641043d74d94320821ebacc8190410fdd5640c82087eed2a0641043d76950320821fbb2a8190410f5d9540c82087ee8b1ca21043c7458e510821f3a0c6a88410f5d0635442087aed2a0a21043f76550510830f2a4c628841875526314420c3ca8b18a21061d5458c510823bbb2a2288419558d5114420c5aa931682104e97098b41083172a2c5a08418b55162d04208bee6b2a821045c735954108316aa6c4a08418b5506250420c72a9b02821045e73d94410822eb9eca20841879526310420c3aa9318821061e5458c410830eaa2c6208410f9d265cc42087ae932e621062d5498b3108274b84c5988418b55162cc42087ce932c621043d74996310821fba2ca988410f1d1654c42087ce832a621043d74195310821ebaec8988410f5d4644c42087ced2a2621043c76951310821f3b2a8988410f1d9544c420c5ca9b12621062d54d8931083172a0c4988418b550624c420c9ca6312621066462945310831d2a6c0988418e553604c420c74a8302621063954181310832d298c0988419654c604c420ce4a2302621043e74d94310821eba6ca188410f9d2650c42087ae9328621043d75990310821fbaac8188410fdda540c42087aed2a0621043f76550310821ebb2a8188410f5d664c842087eeab26421043d76953210821fbb2a9908418b59554884208daec29c421052d7414e21082b2b88a7108418b5516088420e4ca8908421063954980210831caa2c010841595c75408420a5aeb2a0421052d7414c2
  | 8 => 0x85110520e4a84288829063854980414833828cc020a41aa509601052087ee8b2e629043c74597314821fba2cb18a410f1d1658c52087ce9b2a629043d74d95314821f3a4ca98a410f5d2654c52087cebb22629043e75191314821f3b6a898a410f1db544c52087cec2a2629043c76151314830fb26a698a4187193534c520c3ec829a629061c6414d3148317aa6c498a418b153624c520c9ea7b12629064c53d893148317aa0c498a418b150624c520c9ea6312629064c53189314831bb26a298a418d193514c520cc8c5a8a629063764145314831a320a298a4199d88514c520cc8c428a629063b54d81314831c2a6c098a419614f604c520ce0a3b02629063b54181314831c2a0c098a4196d4c604c520cb0a63026290673511813148338288c098a410fdd1650c520878e8b28629043e74194314821eba0ca18a410f9d6640c520878eab20629043f76d50314821ebb6a818a410fdd8540c52087aec2a0629061e64d4c314830eb26a618a4187990530c520c3ac8298629064c53988314831b326a218a418d593510c520c6cc82886290635641443148333310a218a4199588510c520cb0a7300629067051980314821fbb6a990a410f5db54c852087eec2a6429043d76153214830f326a790a418759353c8520c3cc829e429061d6414f214831b320a390a418d59051c8520ce0a3304429063854d81214832c29ec090a418e1506048520cb0a6302429067351181214822f3acc7a024187d5263d0120c38a931e809045c7558f404830faa2c7a02418715163d01208beeda9e809045d76d4f404822fbb0a7a0241175d853d0120c58a9316809052c7550b4048346b1a85a02416a1c142d0120cacc7a8e809065563d47404832b318a3a02419558c51d0120cccc428e8090665621474048392a10a3a02418b9964290120e4c8428c809045e73d95404822eb9ecaa024117dcd65501208b8e6b2a809064c53d894048317aa0c4a02419314c6250120a58eaa128090667621454048332310a2a0241c95085150120c5ea9310809062c549884048327a9cc4202419314e6210120c5ea8b10809062c545884048327a9ac4202419314d621012095aed210809062e659084048333316a2202419958b5110120cccc42888090665621444048393210a2202410f9d664cc120878eab26609043f76d53304821ebb6a9982410fdd854cc12087aec2a6609061e64d4f304830eb26a7982418799053cc120c3ac829e609064c5398b304831b326a3982418d59351cc120c6cc828e6090635641473048333310a3982419958851cc12087ce9b2a609043d74d95304821fba2ca982410f1d1654c120c58a9b1260904ad7418930483162a0c49824193d4c624c120ccec428a60906646214530482ac3aa6018241c6151300c120b90e49806090750514c0304838c2a0a
  | 9 => 0xce7326a2905557399351482b2b90c9a8a414d9d363d4520a6ae9b1ea29056572d8f51482b8b86c7a8a414d9d263d4520a6ae931ea290536740cb514829aba065a8a414d9d360d4520a6ae9b06a29055673d8351482aab9ec1a8a4187d526394520c38a931ca29061f5458e514830e2a2c728a41879935394520c3ac9a9ca29061e6414e514830eb20a728a418d9935194520c6ac9a8ca29065663d46514832ab1ea328a410f9db545452087cec2a2a29061f54d8d514830e2a6c6a8a4187d506354520c38a831aa29045e76d4d514830fb26a6a8a418719353545208bcec29aa29061f6414d514830e320a6a8a411ddd95114520a6ee8a88a2905347454451482abb9aa228a41551cd511452087ee8b18a29043c7458c51482b43828428a418d9975414520e4ee5aa0a2904757695051482ab39ca828a41555ce54145208eeecaa0a2905577355051482aa39aa828a418d9945414520e4ae42a0a29065665d4c514838baa6a628a41c515353145208eaed298a2905367494c514829aba4a628a411ddd95314520a6ee8a98a2905347454c514832b328a628a41c5d505314520e28a8298a290566759085148393aa48428a41c91524214520e8ea7210a290744539085148393aa28428a41c91514214520e8ea6a10a2907445350851482f03828428a41595ca6414520aace6320a2905557319051482b2b90c828a415c5c06414520a6ee8b18a2905347458c51482b3b92c628a415cdc16314520a6ce8318a2905357418c51482b2b90c628a415c5c06314520acce5a18a29056572d0c51482b93868628a415c5c34314520acce4218a2905657210c51482b33848428a415cdc14214520ae0e0a10a290727745085148393b228428a41c91914214520e4e86a10a2907254350851483b1b828428a41591c14214520ec0e0a10a290560705085148392a108428a415cdc13214520ae0e0990a290536740c8514829aba06428a414ddd16014520a68e8b00a2905577358051482aa39ac028a414ddd12014520a68e8900a2905577348051482aa39a4028a4117dcd65d05208b8e6b2e829062f5498b41483162a4c5a0a4193d4e62d0520c98a7316829062f5458b41483162a2c5a0a4193d4d62d0520c98a6b1682904e87058b4148333316a3a0a419998851d0520ccac428e829045f73596414822e39acb20a414b1d54290520b50e0a14829072542146414822f39ecaa0a41175cf65505208bee6b28829045c73594414822f398ca20a41175cc65105208bceb318829061f5498c414830e2a4c620a41171d56310520c3ea8b18829061c5458c414822fbb6a620a41175db53105208beec298829045d7614c41483162a4c420a414b1d54210520d1ac6a1082905a870508414832b31ea220a419558f5110520cacc62888290655631444148333310a220a419958
  | 10 => 0x70d7215353482a6b90c9a9a41565c064d4d20a3ce9b0ea69051d74d8753482a6b96c3a9a41565c361d4d20a3ce930ea69051d74987534828fba2c1a9a41471d160d4d20c3cc9a9ca69061d64d4e534831baa4c329a418d1526194d20caea730ca69063754586534831a2a2c329a4195d4d6194d20c6cc930ca690635649865348332b14c329a418d9916194d20c6ac8b0ca69043e76d51534821f3b0a8a9a418dd536154d20c68a9b0aa69063754185534831a2a0c2a9a4187d936354d20c38c9b1aa69062c64d89534831bb26c2a9a418d1936154d20caec7b0aa69063764185534831a320c2a9a4195d8c6154d20ccec430aa69063864d81534833830ec0a9a4117dd95314d20a3ee8a98a69051c7454c53482abb8aa629a41551c55314d20a3ce9318a69051d7498c53482ab38cc629a41555c66314d2087ce8310a69043d74188534821fba2c229a410f1d16114d20c3ccbaa0a69045d7695053482ab38ca829a41555c65414d208beecaa0a6905577155053482aa38aa829a41879945414d20e1ae42a0a69054d72190534828fba2c229a41471d16114d20a9ee4b08a69055b70584534828f3a0c229a41475d06114d20a9ae4308a69055970184534828f3a6c029a41475d36014d20a3ee8900a69051c74480534823b38ecba1a411d5c765d0d208eee2b2e86904747159743483162a4c5a1a4193d4e62d0d208d8eab16869062c5458b434831c2a4c1a1a4196d4e60d0d208f0eab06869063854583434823b38ecb21a411d5c76590d208eee2b2c869047471596434823b38ecaa1a411d5c76550d208dee4b2a869047771595434823a38acaa1a411edc16550d208ece3b28869047571d94434823bb8aca21a411d1c56510d20c58a9310869064c5398843482363aac421a413a1c16210d20c70a9306849062e65d5242482b338ca921241c31535390920c9cca29c849070c5414e424832c29ec0a12418ed506050920cb0a6302849062c65d9142482b338ca8a12411b9d85450920e18a829a849062c65d0d42482d4b8686a12414b1d54350920c58caa1a84904ea7518142483353a8c0a1241aad506050920d50a830284906cb531814248364298c0a1241aad0c6050920d5286302849062c5498842482963aa8421241c314d4210920b50e0a10849065853983324831c2a6c0992418e150604c920cb6a6302649043f76d50324821ebb6a8192410fdd8540c92087aec2a0649061e64d4c324830eb26a61924187990530c920c3ac8298649045e73993514822eb9cc9a8a410f9d263d452087ae931ea2905567395351482aab9ca9a8a4155dcd54d4520aa8e6aa6a29072572153514838baa6a7a8a41c515353d4520a6ce929ea2905357494f514829bba2a7a8a414d1d153d4520e2ea829ea2907145414f51483922a485a8a41781c142d4520aa
  | 11 => 0xc830eb22a629e41875926314f208ece332a87904757199543c823b38eca21e411d5c76510f20a3ae62a6859043e7615142c828eb98a8a16416a5c35450b208dcec2a285904ae7615142c82c6b98a8a16414b1d54350b20b56e0a1a859043f7655042c8354a12c02164187592530cb20c3ac8a98659065a5358032c822f398c8a8e41175cc645472087ce831aa39043d7418d51c823bbb2a228e41179ce65907208bae732c839045e73d9441c822eb9eca20e41879516310720c3aa8b18839068d6350841c821f3a4cb18e410f5d2658c72087ee8b2a639043c7459531c821f3a6ca18e410f5d3650c720c3ac929863905557194c31c830eb22a618e418795163d0320c3aa8b1e819068d6350b40c828eb98a9206410f9da545032087aedaa0819051d7315040c8317aa2c4206412b5da4210320c3ac929e619061d6454f30c828eba0a718641179da534c32095ae8312619045d76d4c30c828eba0a6186419a58a60d522087eecaa0a91066962983538822fbb2a629c410fdd16114e20878e8b08a71063854583438823b38ccaa1c411d5c66550e20a3ce7aa2871062f54189438823b388ca21c411d5c46510e2087ced2a2851043d76d50428822f3b4a699441175db530ca208eeeca88a31045e73d94418822eb9eca20c414d5c45410620c3ea8b18831061c5458c418821f3a6cb98c410f5d365cc62087ee8b2c631043c74596318821fba2ca98c410f1d1654c62087ce9b28631043d74d943188296ba4a710c414bdd15188620a5ee8b284310567715502188296ba4a610c41595c653086208daec29843104e576d4421882f1386a210c414bdd15108620bc4e0288431061f5458f408830e2a2c7a04410f9d8545022087eecaa0811062e545884088316aa2c420441475d2538c220a3ae9298611052f74597208822f39cc3aa241175ce61d5120a3ce730ea89051d739875448297b92c3aa24147dcd60d5120a38e6b06a89061f5498e544830faa2c72a2418dd526195120c6ea8b0ca89065663986544832ab1cc32a2419958a6195120cacc6b0ca89065563586544830fb26c6aa24187d906355120c98c7b12a89063764d85544832bb1ec2aa2419518f6155120c6ec830aa89065763185544832a318c2aa24199d886155120cb0c7b02a89067061d81544821fbb2a82a24147dcd5415120a38e6aa0a89053771550544829a38aa82a241479ce6415120a3ae7320a89053671990544829ab8cc82a2414b5cb6315120a72e1b18a89052d7218c5448317b1ac42a2418b58d6215120a5ae5b08a89062d62984544828f398c22a241475cc6115120a5ae4308a89062d62184544829cb80c22a241479cf6015120a3ae7b00a89062d62d805448316b12c02a2410f9d261d4d2087ae930ea6905567195353482aab8ca9a9a4155dc554d4d20aa8e2aa6a690
  | 12 => 0xa1861669c35450c308bcec2a2861855571151430c24f3b0a8a1861635c85450c30b2ae22a286184d970189430c21fbb2a821861a650e6010c308deeca90a41862d64548520c332a92c229061365c263d08308eee2b2a841847471595420c23b388caa10611d5c46550830c3aa831a841861c6550d420c2c639286a10619318d5250830d3286302841866952181420c26db82c91906127dd1608c830c5ac9290641862d64548320c26cb86c819061275da640c830d1ac9290641868d64548320c34cb24c019061a6991600c830d32c8b0064184db75580320c32dbaac019061361c5600c8308dce5324a21846d72992510c21f3a4c5288610f5d26294430c3ce6322a21861d73191510c31ab88c8a8861871924354430aa8e2a1aa21862f64d89510c316326c4a88618bd906254430c58c8312a21863b64181510c31c320c0a88619ad886054430cd0c4302a21847776544510c31ab22a2288619958951144308dce5b2e821846d72d97410c3172a2c5a08618b55162d0430d1a86b16821869943983410c296b90a9208614d5c45490430a68e8a8c821871643546410c237b92caa08611b1c965504308dce432a821846d72195410c21f3b4a8a08619518d5150430e2a86a8a821869943181410c338a88c0a08610f5db5410430a5ae42a0821853571150410c26cb84c62086187d516310430c38a8b18821849d7690c410c30eb2c86208610fdd1658c430878e8b2c621849f74596310c26db82c918861275d2628c4309b2e1314621855975d82310c24fba2c1188618d592510c430c6ac8a8862184d970d90310c24ebb4c818861555d6610c430d2ac9288621861d64544310c34ab22a21886155dd9510c430caeeca88621871774544310c38a3a2a21886195d91510c430e2cc8a88621865564544310c38ab22a21886185591510c430e8ee4a88621874472544310c3a8382a218861a6592600c430d34c8b00621843e74d97210c21eba6cb908618b59252c8430c5ac8a9642184d97098e210c2c6ba06510861591c9518843087ee8b2a421843c74595210c21f3a0ca908610f5d0654843093ae831a421865463545210c22ebaec610861275d063084309b2e0318421864d650c8210c2c6ba06410861475d03294030a3ae818ca01862e54588400c316aa2c420061a350d6210030d52c4a00801845d7694e300c28eba4a7180611e5da538c030b32e929c6018599740ca300c36930c6318061665d0318c0308beeab2260184cc72591300c26a38ac898061275d0624c03093ae9b0260184da76d01300c34cb208098061725c8404c030b34e929a60184da7610d300c26d3b66498061b4186314c030b34e818a601866a6258354c821fbb2a82a641875516315320c3cc8b18a99065a6358054c8335312c1a9e410fdd16194f20878e8b0ca79045f7654c53
  | 13 => 0x63d0330c3ca8b1e819861d5458f40cc30eaa6c6a0661875506350330c5ca9310819862d5498840cc3172a2c4206618b5516210330d52c4a00819865963983548c237396c2aa4611b5cb615523087eecaa0a91862d54588548c317322c42a4619a58a6015230c72a8302871845e76951438c21f3a6c2a94610f5d36154a308deeca90a51862d64548528c23b38ecba14611d5c765d0a30c3ca8b1e851861f6550d428c2c639286a146127dd1608ca308dce5324a31846d72992518c21f3a4c528c610f5d262946308eeeca88a31846e72d97418c236b96cba0c61a350d62d06308dce532c831846d72996418c30f2a2c620c6187551631063093aed218831849d7498a318c24fba2c118c619c944604c630c3acab20631861d64544318c21f3a6cb90c610f5d365c863087ce9b2c431843d74d96218c21f3a4cb10c610f5d26588630b1ae8194431849d7418d218c24eba0c610c61365c06308630acae3290431858d740c8218c26c39ac010c618b9516210230c5aa8b10811868d43588408c30eb2cc9984618759564cc230c72cb326611863965593308c237b92c3aa2611b1c961d5130c5ec8312a89864f63189544c333b16c2aa2619918b6155130c6ec830aa89865763185544c333b10c2aa261991886155130cd0c5b02a89867061d81544c21fbb2a82a2614b1c95415130a68e2aa0a89863854583434c21fba2c3a92610f1d161d49308deeca90a49852c74548524c2b238aa4292618b1c96414930a3ae72a6849852c72553424c29a38aa9a12614b5d052d093087ced2a2849851d73951424c296392a8a12614d1c554509308eee2b28849847471594424c21ebb6a8212611ddd95114530a68e8a88a29856472544514c237390cba0a611b5c865d0530cccc5a8e829866662147414c237b92ca20a611b1c96510530c3ea8b18829861c5458c414c26c382c620a619558f5110530c68c9a8a629866462d45314c31a320a298a6199188514c530ce0a3b02629843e74197214c21eba0cb90a618d99351c8530c6cc828e429852d7414a214c21fba2ca10a610f1d1650853087ce8328429843d74194214c22f3acc610a614b5d05208530cd0a4b00429861f5458f404c30e2a2c7a0261475ce5490130a58e4aa4809853471552404c21f3b0a8a0261475ce5410130a72e12a0809843f76550404c296392a8202614d1c55410130c5ca8b10809862d54588404c2a6392a918261551c5548c130a3ae8294609846f72587540c236392c3aa0610fdd95415030c5aa8b10a81863554584540c317322c42a0619998a6115030ccac5308a81863664584540c32b31ac22a061999896115030ccac4b08a81852d72153430c29ab88a9a1861555c45490c308beeab0486184db75582430c32dbaac121861361c56090c3087cec2a2861852d72151430c29ab88a8
  | 14 => 0x86a92622063464945311038aa1aa2988819a94b604c440cd2a5b02622065a53181311032ca98c098881a650c604c440cd4a43026220669521813110339288c0988811b9ca650c4408dae5328622062e649483110316b24a4188818b991520c440c5ac8a90622062d6494b2110317322a5908818b59152c8440c5cc8a94422062d6454a2110296bac851088117dcd65484408b8e6b2a422062f645492110316322a490881591c55248440cd2a5b02422043d75d90211024eb98c8108812e5c06408440acae3290422062f645482110316322a4108814b5d64208440c5acb210422043d7610a501028eb9883280819398e52d0040c9ac7296802064e6354b4010326b1aa5a0081a358e52d004087eeca96802061d6354b4010317312a5a0081a358d52d0040c5eeca96802070e6354b4010316b1aa5a0081c358d52d0040c1ac6a96802062d52987401021ebb4a9200811e5da5490040b32e72a48020599731064010317b2ca4a00818b1895250040c5ecaa92802062c765494010317b1aa4a00818b5486150040b34e72a280204ba7610d4010335b2ca4a00819ad955250040e54a8a92802065a6358354cc297390c72a6614b5c86395330a6ce231ca9985357118e54cc316b10c52a6614e5c06295330a5ce5b0ca99852d72d8654cc29cb86c32a661479cc61953308dce5b0aa99846d72d8554cc29db82c4aa6618b5886255330a5ce5b0aa99852d72d8554cc29db82c2aa661479cc6155330a5ee4b02a99852c7258154cc29bb8ac0aa6614d1c5605533087eecaa0a9986395498243cc31d2a4c021e618d95261d4b30c6aa930ea5986365458752cc31aaa2c3a9661599c75294b3087ce9b0aa59843d74d8552cc21ebb4a8296610fdd95414b308deeca90a59852c7255142cc31caa0c0a16614b5ca5410b30c74a9300859843d7599032cc21fbaac8196610f5da540cb3087eecaa0659862e5498b51cc316aa4c5a8e618b95162d4730c5aa8b16a39856672d4651cc21f3a4c528e610f5d2629473087aed2a0a39843f7655051cc23bbb2a228e611b9cb65d07308dae5b2e839862e5498b41cc316aa4c5a0e618b95162d0730c5aa8b16839863a5498341cc31caa0c0a0e61875526310730c3ca8b18839861d5458c41cc21f3b4a898e610f1d9544c730c5ca9b12639862d54d8931cc3172a0c498e618b550624c730c74a830263986395418131cc21ebacc818e610fdd5640c73087aed2a0639843f7655031cc38b2a26218e610f9d365c873087ae9b2e439843e7499721cc21eba4cb90e610f5d664c873087eeab26439843f7695321cc21ebb4a990e610fdd954c873087aecaa6439843e7499621cc21eba4cb10e610f9d0654873087ae832a439863a54d8121cc31d2a0c090e610f9d2650873087ae9328439861d5498c21cc30eaa2c610e6187552
  | 15 => 0x667114e52102b2b88a7290816a5c34394840e18a6a1ca42054e7319252102a6b98c9290814b9d06394840e1a8621ca42052e74d865210332b08c3290814b9cb4354840a72e1a1aa42061c6350d521029639286a90811b9db53548408dcec29aa4205667114d52102b2b88a6a9081c354f4354840b52e1a1aa42052f7550d5210387a9a86a9081539ce6454840a9ae7322a4205667199152102b2b8cc8a90814b9d26354840a58e8b1aa4205677158d52102b238ac6a90815a1c16354840a5ce831aa42056a70d0d52102b4b8686a90814b9db4354840a5ce3a1aa42072a70d0d5210296b8686a9081ca5c34354840a52e1a1aa42052c7650d5210387b9a86a9081c3d8d4354840e18c6a1aa42052c7150d5210297b8286a90814b9d36154840a5ce930aa42052c7458552102a7b9ac2a9081531cd6154840ad0e0b0aa420665611855210237bb2a4290819a54960d0840c5ce4b2c84204bb7058e4210316b2ca5210818b58d5290840c5aa530c842049f735824210316a92c1210819a9496010840a5aeb310842052f765484210317bb2a4210818b58d5210840c5aa5308842062e6454b3210316b22a5990810f5d7648c840972e0324642062f6454a3210316322a5190811ddc5654c8408e8e2b2a642062f645493210316322a4990819a54b604c840cd2a4302642062d649483210317322a4190818b591520c8408dee4b1ca22046c7258e511021f3b686a88811b5da5214440c9cc7290a22064d639485110237bb2a4288819398d5214440c9ac6a90a22047776544511032ab1aa2288811b5d662d04408deeab16822046d7694b4110237bb2a5a08812edc16390440c5cc4a94822062d6554a4110317bb2a5208818b58d5290440e4ee2a9482207247154a411024fb9ac1208818b5496090440c9cc7290822064d63948411032731aa4208819358d5210440caac72888220655635444110334a94c0208819a5496010440c3eeab18822061c7558c411021ebb4a6208818758e531044087aeb310822068d63948411030eb1aa4208818b9895210440d1ac6a90822062f76548411038731aa4208818b58d5210440e1ac6a90822060d635484110392a94c220881a558e5110440e4aa5288822061d63544411034ab1aa220881c99495110440d32c73008220729529804110316a92c020881a698d6010440e52a4b00822046e729973110236b94cb988818b99152cc440c5ac8a96622070d4354b3110237394cb188811b5ca658c440972e0324622062f6454a3110316322a5188811bdc9654c4408d8e4b2a622046e721953110236b90ca9888187192534c440938eca1a62205947150d3110236baec4988811b5d4624c4408dced292622046c769493110317b24a4988818b192524c4408dceca92622046c765493110317b22a4988818b191524c440e1a
  | 16 => 0x386a9ec4a1681c354f5250b40b4ce3a9285a05a970d4942d02573b0a4a1681c394c5250b40c3aa630285a070e5350842d032d29cc0216819694d6010b40d5284b0085a061e6454e32d030eb22a7196819654c604cb40c3ac929865a061e6454c32d030eb22a6196819394e62d4740c9aa7316a3a064e5358b51d0326a9ac5a8e81599cb51947408baed298a3a045f7654c51d023bbb2a228e819394e62d0740c9aa731683a064e5358b41d0326a9ac5a0e819998a51d0740cccc4a8e83a065a5398341d032d29ac1a0e81175d663107408beeab1883a045d7694c41d022fbb2a620e811bdc9654c7408d8e4b2a63a061f6494d31d030e324a698e8187d91534c740c38c8a9a63a05547154d31d032729ec498e819354f624c740c9ca631263a064d5318931d032d29ec098e819694c604c740cb2a630263a061d6494c31d02aab8ca618e8187991530c740c3ac8a9863a045e7399721d022eb9ccb90e818799253c8740c3ac929e43a061e6454f21d030eb22a790e818d99251c87408bce732c43a045d7399621d0386a9a8510e81179cc65487408bae632a43a065a53d8121d032d298c090e81179ce65087408bae732843a061e6454c21d030eb22a610e81c354d4208740e4a8528843a045f7654c539021eba8c4a1c811bdd95214a4093ee6b04852047671d97329023ab8ecb994812e5c0648ca40970e8b04652043c7650d5190317a1ec4a8c818b50f62546408eeeca88a32043d7694e419021ebacc520c814bdc9519064093ee6b04832061d6558c419030fbaac620c81a6dc16310640d30e0b18832061d6394c419030eb1aa420c814ddc55210640c3ac6a88832052f725444190237396cb98c811b5cb65cc6408dee4b2a632046c7259531902ca38a8698c81a650c604c6408bce7b2c432045d73d96219024eb98c810c812e5c06408640970e8b0043206aa42580219030eb2cc7a04818759563d0240c3ac6a96812062e6254b409032cb2cc7a04819659563d02408beeca98a6a054c7254c53502aa38aa629a811bdc96114d408d8e4b08a6a046f7654852502a639aa429281591c5521494087ceb32464a047771594325023a38aca1928187593530c940c3ac829864a062d64d48325023bbb2a228a81551cd5114540ac8e4a88a2a046f7258c5150236392c628a811b9ca654c5408dae532a62a046f725943150236392ca18a8187593530c540c3ac829862a063564d44315031ab20a390a8117dcd65085408b8e6b2842a045e73194215022eb98ca10a810f9d66408540e4a8428842a0668525802150354a12c010a819c1456008540c5ac429480a046f725865310236392c32988117dd95314c40caaa6b08a62043d7598b431025dbaac1a18818edd560d0c40b34e1a9a862049e7614d43102cab88a6a1881a650e6010c40b1ae6324a4205
  | 17 => 0x98431e9c065d0c218f2e032e8610c6d7598b4308672b8cc5a18431e9c06590c218f2e032c8610c7b70595430863c382caa18431e9c06550c218f2e032a8610c6d751894308716aa0c4a18439354c6250c218eaea30a8610e5553185430863d380ca218431e5c06510c218daeb3108610c7575984430868eb98a9a10434e5c054d0821ad2e02a48410c6f755864208673baac32104399dd561908219c8e0b0c8410c3e76151420868eb98a8a10434e5c05450821b4ce3aa28410c6e7615142086b4b80a8a10432b9d85450821b1ae62a28410da9701514208672b88c6a10434b1d54350821d18c6a1a8410da47150d420861fbb2a821043a950a61108219cee2b266410caf74587320861f3a6cb190430f5d3658c82187ce9b286410c3d74d94320870eb24a61904387591530c8218daebb206410ce571d903208656bb4c8190438b596640c821c5acab206410e8d6494c3208637bb2a619043a3591530c821d4ac93086410c6f755843208753322c219043a9591610c8219ceeab086410e67755843208672382c2190434b5d032944218bce7b288210c5d73d94410862f398ca20843175cc6510421c3ca8b188210e1d5458c4108746b1a8420843a558d411042195ae93146210c3e74d94310861eba6ca188430f9d0650c42187ae83286210e1d6494c310870eb22a618843a5591310c421ba0e09886210cad7418f2108636bb4a5108434b5d252884218eaed2944210da57494a21086d2ba065108431bdd56448421998e6b224210ce8705912108636bacc6908432b5d0634842195ae9b0a4210ce676d052108752b208290843715cc41484219c8ec98a4210da4744c5210876231a6290843781c13148421b4ce92924210ce67610921086733b46490843179ce64940218bae7324a010c3e7498e500861eba4c7280438b9c86454021c5ae4322a010e3970191500870fb26c6a8043871936354021c3ec831aa010e1c6418d500872cb80c6a80438b1924254021ad0e0a12a010c7b76540500871cb22a0280439658d50140218dee4b0ca7a046c7258653d02a7390c929e81535c86494f40aace2324a7a05557119253d028f3a0c529e81471d16194f40a9ee4b0ca7a054c7258653d02adb82c329e81479d06194f40caac230ca7a054e7299153d02a6b94c8a9e81479d26254f40ab6e0b12a7a051e7418953d028e3a2c2a9e8153dc96154f40a98e4b0aa7a055b7058553d028f3a0c2a9e81955846154f40a9ee4b02a7a054c7258153d02abb8ac0a9e81551c56054f408beeca98a7a06595398343d032d29cc021e819594e61d4b40caaa730ea5a06565358752d032aa9ac3a9681599c75294b408baed298a5a045f7654c52d0237bb2a429681c354d52d0b40c3aa730685a061f6594d42d0296392a6a168187d955350b40e1ee4a9a85a070c7254d42d
  | 18 => 0x39432187ae931ca190c3d7695050c861fbb2a8286431edd95014321ccac530ea910c5e73d81548862eb9ec0aa4430fdd95415221c3aa8b18a910e1e6458c548872ab1cc22a4430f9d36054e2187ae9b02a710c5f7654c538870eb22a629c43875926314e21c6ac9308a710e6562984538863d386cba1c431e5c365d0e21c5ca8b168710c7a70995438863cb84caa1c438d5506150a218dced2a28510d2f7550d428874631a86a14432bdd161cca21caaa630a6510c6d76d4c328870f2a2c620c43875516310621d1ac6a108310cad7498a318870eb24a618c4387591530c621c5acb3264310e2d655932188656ba0c790c438d59664c8621c6acab264310c5e73992508862eb9cc9284430f9d2639422187ae931ca110c7b76540508862fb9ac1aa243171cd60d5121c3ec831aa890e4c63d89544872a31ec2aa24396d8f6055121cb0c7b02a890e3b64181544872db18c0aa2439618c6055121cd6c4302a890e7361181544861fbb2a82a243471cd5415121a70e0aa0a890c3f74583534861e3a2c1a9a430fdd16194d21878e8b0ca690e1c64d8d5348717b26c4a9a438b1936254d21c68c9b0aa690e3b64d81534871c326c0a9a439ad8b6054d21c76c8302a690e3864181534872db18c0a9a439ad886054d21ce6c2302a690c5f7654c534868e3a2a629a43561c15314d21c38e6b20a690c6d72d97434863d386cba1a431e5c365d0d21a5ae52a68690d1c73553434869c382a9a1a43475d053d0d218f4e1b2c8690c7970d964348637b92cb21a431bdc96550d218eee2b2a8690c7b70595434863c382caa1a430f9da5450d21a5ae52a28690c3c76551434868e39aa8a1a434e1c15450d218dae5b288690c7571d94434863db82ca21a431e1c16510d2187ce83288690c3d76d50434871a2a2c3a12439514d61cc921c5ea8b168290e2c5458b4148696b94a920a43471cd5490521a70e0aa48290c5f73595414862e39acaa0a430f9d85450521a5ae52a08290d3571950414861fbb2a820a43471cd5410521a70e0aa08290e1e5458c414870eaa2c620a43475d053cc52187ce932c6290c3d74996314861fba2ca98a430f1d1654c521c38c9a9a6290d1d7414d314870e320a698a439314f624c521cb6a63026290e585318131486a639aa910a435a1c15488521a5ae829c4290c7b76540504869c3a2a028243561cd50141218bee6b06a810c5c73583540861fbb2a82a043875516315021c72a8b00a810e1e6458c540872d31cc02a0439658e6015021c74c8b00a810e5a63580540872cb1ac02a0439a989601502187ce9316a610c3d7498b530861fba2c1a98430f1d160d4c218beeca98a610e1d6454c530872ca9ac029843875926314c21c74c9300a610e3964980530871d322c0298438e5916014c21cb4c6b00a610e6a62580530873930ac02
  | 19 => 0x83126218e2d54189310c71d2a6c0988638e553604c431c74a83026218e3954181310c70fba6ca98863871d3654c431c3ecbb226218e1f65191310c62f3b6a898863475d6544c431c3ecb2a26218e1f65551310c68f3b2a898863471d9544c431e28e2aa26218e4f65d89310c786aa6c49886393d94624c431d18c83126218f0d54189310c70eaa6c298863c5553414c431b8ce5a0a6218d5575105310c72db2ec098863c6553604c431c3aa83026218e5b65181310c74db20c098863a6190604c431e32a83026218ecb62181310c764310c09886396d50604c431d34a83026218e5954181310c74caa0c09886386550604c431da6823026218ed041181310c71bba6ca988638d1d3654c431c6ecbb226218e3765191310c71bb2ca8988638dd95544c431e2aa929a6218d5575d0d310c733b2ec49886399d94624c431d48c83126218d96740c9310c739b2ec0988639cd94604c431d60c83026218ed363181310c770310c0988630fdd16294031878e8b14a018c3e74189500c61eba0c4a80630f5da541403187eecaa0a018e2e54988500c716aa4c4280638b9516214031c5aa8b10a018c7b76540500c734b12a0280639998961d5321c3ac631ca990d357118e54c868f398c52a643475cc6295321a74e0314a990d397018a54c868f39ec12a643475cf6095321a6ae3b04a990d2e7218254c862f39ec0aa643175cf6055321a6ee2b1aa990e1d6318d54c868fb9ac2aa643471cd6155321a76e0b0aa990d387058554c868f39ec0aa643475cf6055321a6ee2b02a990d2e7218154c861fbb2a82a6438e95260d4f21c72a9306a790e3a5458353c871caa2c1a9e438b99262d4f21c5ac9316a790e3a6498353c871cb24c1a9e439a98a60d4f21c74c8b06a790e396458353c8735312c1a9e43569c35394f21ab4e1b1aa790c3e74d8153c861eba6c0a9e430f5da5414f2187eecaa0a790c5f7654c53c8716b24c429e43999896114f218f4e032e8790c797019743c863d384caa1e431e5c26550f21a38e6aa28790e355418543c868eb9ca821e438d9526110f21c6aa930c8590e365498442c861ebacc8196430fdd5640cb2187aed2a06590c3f7655032c8716aa4c5a0e438b95162d0721c5aa8b168390e2d54d8941c8716aa0c4a0e43879526310721c3aa93188390e1e5458c41c870eaa2c620e43a558d4110721c5aa93166390e2d5458b31c861ebaec898e430f5d4644c72187ced2a26390c3c7655131c87172a6c498e438b553624c721c5ca83126390e2d5418931c8727298c498e438e953604c721c72a9b026390e3a5418131c871caa0c098e439694c604c721cb2a63026390c3d7695031c861fbb2a818e43a5591310c721e2ca89886390dd0704c431c870f2a4c7a86438755263d4321c3ca8b1ea190e1d5458f50c86ad39ea1286430f9d26
  | 20 => 0xb74540504c69c3a2a0282635adc95014131ad0e4a80a098d547150c504c61fba2c4282630f1d16214131c74cbaa0a098f1b73d50504c63cbb4a8282635a9ca5414131ad2e52a0a098c7b76550504c6b5b92a8282635a1c95414131c74ca2a0a098f1973150504c6ad3ac8628263c6d524314131e30a9218a098f1b5450c504c78c2a28628263741c54314131cd4cba90a098f2b54d48504c7942a6a428263d290f5214131e9287a90a098c7976948504c69d3a4a4282634e5d252141318f6eca90a098d3b74548504c69c3a2a4282639a9945214131e56a8290a098f2854148504c7a5218a428263d250c5214131e60a9988a098f6052cc4504c78daa46228263c61523114131e96a5188a098f48528c4504c6acb9cc828263565cc6414131ad4e4320a098d6972190504c6b8b88c828263569c64314131ae6e2a18a098d707150c504c78dba28628263c6d914314131e30c8a18a098f537150c504c6ac38a8628263d41c54314131aa0e2a18a098f194310c504c69dba2c4282634e1d16214131ab6e6b10a098d7371588504c69d3a0c4282634e5d06214131ab2e6310a098d7171188504c6ad39e8428263565cf4214131e3287a10a098d7271d08504c6b8b8e8428263c650d4214131ab4e6210a098d5973108504c6b9b8a64282635c1c53214131a74e8190a098d39740c8504c6ad39e8228263565cf4114131e3287a08a098d6a72d04504c6b4b968228263c690e4114131ab6e6a08a098d5873504504c78ca1a8228263569cc4114131ab2e6208a098f1a43104504c6adba46228263565d23114131a76e8988a098d38744c4504c6b5b9262282635a1c93114131a5ce431ca818d2d7218e540c716b10c52a063479cf6095031a5ce4304a818d2d72182540c637390c0aa0631b5c86055031a38e6b12a818d3471589540c69db82c4aa0634e1c16255031c5ac4312a818d1e73d81540c68e39ac0aa0634bdc96055031a58e4b02a818d3471581540c697390c0aa0634b5c8605503187eecaa0a818e3554586430c71b2a2c2218630fdd16094831878e8b04a418c3e74181520c61eba0c0a90630f5da541483187eecaa0a418c6f76548520c71d2a4c0290638e5526014831c74a8b00a418e3954580520c734a92c0290631edc165508318f0e0b2a8418d2c72551420c70eaa6c6a1063875506350831c6aa9b0a8418e3554185420c696b94a8210638d55261cc831c6aa8b0e6418c3d75990320c61fbaac8190630f5da540c83187eecaa06418e2e5498b410c716aa4c5a08638b95162d0431c5aa8b168218e1d5498e410c62fbaac720863875516390431c3aa93188218e1e5458c410c70eaa2c6208638755260cc4318baed29c6218c757694e310c61f3b4a8988630f1da544c43187cecaa26218c3c76551310c7172a6c4988638b553624c431c5ca
  | 21 => 0x61f3b6a8a92630f9d85454931c76a9b02a498e3854d81524c71daa0c0a92638e15060549318deeca90a498d2f74548524c6963a2a4292635adc15214931ad0e0a90a498c3f74580524c61e3a2c0292638b99754149318daed2a0a498d6a70950524c6b4b84a8292631bdd95414931ad6e0aa0a498d6870550524c717328a829263c35cc5414931a9ceb218a498f0c5490c524c7862a28629263711c54314931a9ae6320a498d677150c524c6b238a8629263c350c4314931a5ce9b08a498d2d74d84524c697ba262292634b1d13114931a5ee8b00a498d2c74580524c6a7b9ac02926359dc56014931a5ce8300a498d2d74180524c6a6b98c029263595c460149318f6e0b2e8498c7870597424c70e2a4c7a12638715163d0931a38eaa1e8498d947150f424c72731ea5a12638d15261d0931ccea530e8498e3454587424c74aa1ac3a12631edc165909318f0e0b2c8498c7a70d95424c63cb86caa1263471d54350931c38caa1a8498d947150d424c63db82ca212631e1c16510931c38a93188498cd47158c424c727318a4212639914a618c931c68a9b0a6498e3454185324c733a90c2992630fddb540c93187aedaa06498c3f76150324c61ebb0a8192638b993520c931c5ac9a906498e1c5498f414c68e3aa87a0a63651c543d05318dceb3168298e2f5498b414c7162a4c5a0a631b1d562d0531c5ea8b168298e2c5458b414c746a1ac5a0a631b5db52d05318daec2968298e1e6590e414c70faa0c6a0a63471d54350531c9ec62928298e4c63149414c70faa4c620a63871526310531c3ea8b188298e1c5458c414c64ebb48620a63879964310531c9cc7a908298e4d63d48414c727318a420a639358c5210531e48a82966298f0c5414a314c637394c9a82631b5ca64d413187ce9316a098c3d7498b504c6b5394a9a82635a5ca54d4131ad6e4aa6a098d6872553504c78cb98a9a8263c615243d4131ba0e2a1ea098f2b54d4b504c7942a6a5a82634e9d252d4131a72e9296a098d3b7454b504c69c3a2a5a8263cad5052d4131e50a8296a098d6a72993504c6b4b94c9a8263565cc64d4131a74e9b16a098d3974d8b504c6acb9ec5a82635c5c762d4131a74e9316a098d397498b504c69d3a065a82634e5d032d4131a74e9b0ea098d3974d87504c6b5396c3a82635a5cb61d4131ad4e5a0ea098d6972d07504c6ad39883a8263565cc41d4131c5ea9314a098e2c5498a504c717aa2c5282638b1516294131c5cc9a94a098e2d64d4a504c717320a5282638b5905294131c74c9a84a098e3964d42504c735316a1282639a58b509413187cedaa2a098c3e76151504c717aa6c4a82638b1536254131c5ea8312a098e2c54189504c6373b6a4a82638bd935254131c58c9a92a098c6e76149504c717b20a4a82638b19052541318f6eca80a098d3
  | 22 => 0x88387d955350441c38eca9a8220e1d53d89411070ea98c0a0883699ca5450441caecb29a8220e576554d411078b2a2a6a08832d9d842504418bee6b14a020c5c7358a501061f3b684a8083175da53140418beeca98a020e4e539885010726a9cc4280839394d6214041c9aa6b10a020c7b765405010734b12a0280839598d61d533187eecaa0a998e2d5458854cc717322c42a663999896115331a5ae42a68798c3e7615143cc696b90a8a1e63655c75450f318bcec2a28798c9e7615143cc6c6b90a8a1e630fdd95410f31d2a86b088798c3f7458252cc61e3a2c1296631bdd95214b31c5ac8a90a598e1c6550d42cc74aa1ec2a16631e9c36510b318f2e1b288598e2d6494832cc716b22a4196638b95162d0731c5aa8b168398e8d4358b41cc696b90a920e630f9da545073187aedaa08398d2d7215041cc70faa2c620e63275da43107318dce4322a198c6d7219150cc61f3a0c4a86630f5d062543318f6eca80a198e5563987548c61fbb2a82a4630f9da5450e3187aedaa08718c6f76548528c71a2a2c3a14634b9cb5450a31c3ea831a8518e2f5458b418c7162a2c5a0c630f9d8545063187eecaa08318e1e5458c418c70eaa2c620c6347dd165cc6318f6eca80a118c6e72983544c636b94c1aa2634bdc961d5131a58e4b0ea898d2e72983544c696b94c1aa26347dcd60d5131c5ea9314a898e2f5458a544c71daa4c12a2638ed516095131cb2c7304a898e6a62982544c734b14c12a2639a9896095131cd2c4b04a898e2f64d89544c717b20c4aa26393d8c6255131cc8c5b0aa898e3b64d81544c735b16c0aa2639a18b6055131c76c8302a898e5b63181544c735b10c0aa2639a1886055131ce6c2302a898c3f76550544c697b92a82a2634b1c95415131a76e0aa0a898d3870550544c697394c82a2634b5ca6415131a74e1320a898d3970990544c68eb9ec42a2638758f6215131a6ae3b10a898e1d63588544c68eb98c42a2638758f6115131a5ce5b08a898d2d72d84544c70eb1ac22a263475cf6015131c3ac7300a898d1d73180544c697390c02a2634b5c86015131a6ae2300a898e3454987434c70f32ea921a63569c25490d31c6ea830a8698e1c65d91434c6ad384a8a1a63179d85450d319acea30a8698e5675185434c74baa0c2a1a63a51506150d31c38a93188698d1c7550c434c6ca38a8621a630f9d260d493187ae9306a498d6a70953524c6b4b84a9a92635adc154d4931ad0e0aa6a498f0d73153524c7862a487a9263711c543d4931a9ae6326a498d6571193524c697ba2c3a92634b1d161d4931a5ce9b06a498d2d74d83524c6a6b9ec1a9263595c760d4931a5ce9306a498d2d74983524c717326a5292638b5935294931c76a9304a498e3854982524c735a94c1292638ed516094931c70a8b04a498e6b52582524c
  | 23 => 0xccb41c5ac8a9665a0e655218532d0716b24a4196838b991520cb41c5ac8a9065a0e4e6394b50d0726b1ca5a86839398d52d4341c9ac6a96a1a0d5a73d4250d0636bb4a4286831bdd952143418f6eca80a1a0c5f7654c5390657b92c321c831bdd95214a4187aea31a8520cb571193329065a3a2c3994831e9c3658ca418f2e1b2c6520e1e6354f4190716b2cc5a0c838b59562d0641c5aa6b168320e656598b4190732b2ac5a0c8387d8f4254241878eca12a120e1f63509509063dbb2a02848317dd95314d41a98e4a98a6a0d587054c5350637bb2a429283531cd5214941ad0e0a90a4a0c5f73580525062e39ac0292830f9d664cc9418f6e0b2864a0c7870594325070eb26a6192838b593520c941c5ac829064a0e1d6314e415063dbb2a028283561cd5014141ad0e4a80a0a0c5f73588505062e39ac428283635c86494c41a9ce4324a620d4d72192531068f3a0c529883479d36094c41cb2c0304a620d4e7299153106a6b94c8a9883569c26454c41ab2e1322a620d1e74989531068e3a2c4a9883551c56254c41ab6e0b12a620d5870589531068f3a0c4a9883479d36054c41a3ce9302a620d1c7458153106a7b92c0a9883531c96054c41aa8e2b02a620e5960181531062fbb2a6298839554d61d0c41c3ce6b2c8620e1d6594e431070ea9ac5218832ddc56290c41c3aa6b0c8620caf72586431070ea9cc1218839594d6110c41a3aeb3188620d1f7654c431070fbb2a6218838754d6210c41c3aa73008620c5f73582521062e39ac129083175da53148418beeca98a420c6f76548521072d29cc0290839654e6014841cb4a6b00a420e59535805210734a92c0290839554e61d0841caaa6b0e8420c3d7598f421070f31aa7a108387dd953d0841e1aa6a968420f1553987421070ea9ac3a1083c554d61d084196eeab0e8420e3775587421074b29ac3a10838d54d61d0841d2aa6b0e8420e1553587421070ea9cc1a10838718d5350841a58e4a9a8420e1f6554d421070e3b2a6a1083c3dc95350841e18e4a9a8420f0d53d894210786a9ea4a1083699c7525084195cec2928420f0e5314942106d4b80a4a10838754f6150841c3aa63028420f0e535084210752a14c2210830f5d764cc84196ae23266420e1f6454f321070e322a79908387991538c841c3ac8a9c6420c7b70595321063c382ca9908387d91534c841c38c8a9a6420e5553d85321072aa98c29908387592530c841c3cc8a986420e1d6454c321061ebb087288839394e62d0441c9aa73168220e4e5358b4110726a9ac5a08830fdd953d0441c3cc6a9e8220e1f7654f4110786a9cc5a08838754d62d0441e1aa6b168220e8e5358b4110716a9ac5a0883a354d62d0441c1aa6b168220e1d53983411061ebb4a9208831d5da5490441b4ae52a48220e1f6594d411070e31aa6a0
  | 24 => 0x2a6879943e7615143cca9ab88a8a1e650fdd95410f32c3aa831a859943f7458251cca1e3a2c128e65879cc6454732c3ae6322a3996357119151cca3bbb2a228e658d59151147328f6eca80a19964d6398b548ca1fbb2a82a4658e5516015232cb2c7300a91963a64580548cb35312c02a4658b5506250e32a72e02a6851943e76151428ca9cb80a8a14650fdd95410a328eeeca88a31943f74586508ca1e3a2c3284658b9c86454232c5ae4322a11963970191508ca3dbb2a0284658e5915014232c6ec830aa89965763185544cb33b10c2aa2659cd876055132ce0c3b02a89963b64181544cb2db18c0aa2659ad886055132ce6c2302a89967061181544ca1fbb2a82a2654d1c55415132a70e0aa0a89962c5458b434cb0e2a2c7a12651ddd95114532a68e8a88a29957070544514ca1fba2c028a650f1d160145328f6eca80a09953874540504cab838aa0282650fdd16114132878e8b08a0995367118e540ca9ab88c72a0654e9c06295032a72e0314a81952e72d86540ca8f398c32a065479cf6095032a5ce4304a81952e72d85540ca8e39ac2aa0654b1c96155032a76e0b0aa81953870585540ca8f398c2aa065479cf6055032a38e6b02a81952c72581540ca9bb8ac0aa0654d1c56055032a5ce4302a81943f76550540cb16aa2c521865875954310c32c5ca8b10861961d5458e420cb0f2a2c6210658b59542108328baed29c641946d7694e320cb0fb2ca89906587d95544c832c5ecb2a2641962f65551320ca1fba2c1288650f1d1609443287aed2a0a21943f76550510ca3bbb2a2288658e9526014432c72a9300a21963a54580510cb1caa2c0288659c545601443287ee8b0ca01943c74586500ca1ebb4a8280650fdd95414032c6ca9308a01963554984500cb1b2a2c2280658d55161140328f6eca80a01967161540500caad386a729e8317dd95314f41b2ae3a9a87a0d9a70d4d43d064f3b0a6a1e83a550d6110f418bee6b04a5a0c5c7358252d06b5386a7296835a5c35394b41a5eeaa1ca5a0f0c5350e52d06a7398c929683535cc6494b41ad4e0324a5a0d697019252d06973a0c729683c350c4394b41acce221ca5a0d657110e52d06963a2c12968353dcd6094b41a98e6b04a5a0d677158252d06973a0c1296839a5806094b41c38c6a1aa5a0c6e76d4d52d06b5386a6a96835a5c35354b418dcec29aa5a0f0d53d0d52d0697baa86a9683c3d4d4354b41a9ce7322a5a0d4d7399152d06973a4c6a968359dc56354b41a5ce831aa5a0d2e71d0d52d0787b9a86a9683c3d8d4354b41e18c6a1aa5a0d2c7150d52d06a7b9ac2a9683531cd6154b41ad6e0b0aa5a0d687058552d06963a2c0a968353dcd6054b41a98e6b02a5a0d677158152d06973a0c0a96839a5806054b418deeca90a5a0e655298742d0733294c2216838b99152
  | 25 => 0xb0000004006006006802c04c00b004800400c000001808c000000004000006200301980000180040020000000004001000801400f0030008006000000005001a015004801400c0070000018018001007003803800c0078000000001011000000800800d802801001a00100e400400000000040420120038070000004000001002800000d8008018000000000002800901000100f8000003005c00000201b00000040010000000000003004003004200100b003001000a000800407600600080140000050120000020000001806400000300980c4076000013002403a00e001800000605300000600040170038020008009001000002600b001002800000b00600080000050028000036000001800802201e002803400a00e00d00000000010008020062008004802c014026005800001600000200100020000058004002003000001a37bb2a4296879a5496014b438eeeca88a3a1c6f7258650d0e36392c3286871edd95014343cd2c4a80a1a1c6f765485290e9b38e86a8c878bd0f62546438eeeca88a321c7b765405090e57b92c321a871bdd95214943ac8e2a90a4a1d68705485250e3bb8ac0292871d1c560149438eeeca88a2a1d64725445150eb8382a228a874d5c643145438dee4b00a2a1c6c725805150e3dbb2a0282875a1c95014143ae0e2a80a0a1c77715885050e3a38ac4282871bdc961141438d8e4b08a0a1c3d769524310e2ebb4a921887599c752948438deeca90a421d6672d465110e9b38e86a88874d1c543544438eeeca88a221c777158a5010e3a38ac5280871bdc961940438d8e4b0ca021c7b765405010e2fbb2a629e859554d6114f4287eeab0687a145f7358251d0a2e39ac128e850f9db4354742a68e2a1aa3a14777654451d0b2ab1aa228e851edd950143428beeca98a721477765445190b0fb1e84a84854e9c342542428f6eca80a12145f7654c5350aaa38aa629a85561c15314d428f6e0b08a6a1478705845350a8f3aec6a1a85479d85350d42c3cec29a86a151d7114d4350a8f380a6a1a852b9d46250d42c5cea31286a14ae711894350a56b80c4a1a858714c6150d4287cebb0286a149f735824250a1fbb287a8a854d1c543d45428eeeca88a2a1554735445150ab8382a228a851edc163145428f0e0b18a2a145f735805150a2e39ac028a851edd95014142ab0e6a80a0a1570715405050a9cb8686282854b1c94314142a76e0a18a0a1539709085050a2fb9ac228285171cd6114142ab4e1a9ca62145f7654c5310a1ebb4a9210851b5da5490842a5aeb21a842147b7058e5110a3c382c72888517dcd60944428b8e6b04a221477765445110aad39ea1280854e9c34254042a70e0a12a02147b765405010b2731ac5aa6650fdd95415332c6aa8b08a9996656298454ccb1b322c22a6659598d6115332a6ae2
  | 26 => 0xe0000000000000400c003000002c0000020000044004000000801001400b0108008006012000801000400200900200060030000000000008001000009c0030018018002006001002400a008000800400a01400000740000080028000000002004001400c013000000c006008003000000200f000000000000300b005400200c000002000200b001002800800200380080a8000000802c00200b0080004002001000000800c01400f0014014002000007400a01300480480000430000004002004024801800a007000000c006000004800002a00600101780020000060000002001000000800400000e00240000090000030002002009002400000100000780000050068040014006004804400a0150008004022000004000000000002a001c00400000b8000022000004000803e00900000000060090100000000014000000c0040060198014024001009002400200d0088000000000007000c00e000004800000a0000010010002000000800000400b002802403c019009000000000b000803402000000081080020040020010028026000001801404300500000040050020030020010000800400200300000c400e003000000c026000004000000000900000000040050000000000008000006801a000000000800e007000008400400800000480380000010004018016006800009c0000018004002000008801001c000006800800000f003000802000f00900040060200078084008004006800c01e00900e0018010002006000801602b000003400e000000002001e0000010010002000002801c00e00a0028028004000003800c00000b002800000000100000000040010018004004000000801400c00300c000c00200c001000000400000080500140000008004002003000800000000100000500000030020004002000000000000c001002004004a00a003000000200900500100560000270050006001001002000600100100980120060000008006005006001c01400400c801000000000081c801e0050010004000043000802c02e0000010014004006000000406400b00d000402a006001002c006013002001000400100100500020000010004000000007001c0000000008008000000002000800000000a01280200000058050004001002802000000e0000000000023005003000600200100000080230078004004000003801004800b005004400600b0038000006000006000401a01f00180200140250028030076018000000400800700d000400e00a0020014020000001807c02001500000180000250008000024002005803000c00e011800800200200f003002e0020020008000004000000001c000000800800000000100000000000040000030005000001000a00b00400c40000000000000012002006002c008028000000402e
  | 27 => 0x42a2c58fe73c0046a1c644b223cc7393d4cbbe00f8b7d3a840a33e509921a1c70d113038f30b0a4128e02222be8001000000000000a002800400e0000028064008039003800c01000b004003c082001004002000000f00a80140020010018004004001003005c00001000000ac06800300480000040120038008024013006001400c000007001400800b0088010022008016805000c02400f000000c000000801400c0000040000018000000000c01800d011001c03000a00c0058010000003001000e000001000009a003001002800600000000000280010030014010002002806800002b02d00000000110000010000002000017000a000001007c00200f0000068028011000809c00e00500080000020000030024002004002803c0ce00300a000000c004002800002a05c0010034008009013801c03800b004801001a000000000000000300880a8018001000801000004b004800000200e0040000020006000007800000a000005800200c000001401600401e0048038000001000c00200200300300000060018000006009001000000a00300a000c006000002001800a00b0010010004009003802408e00800800080120240178000026054009001402000500a0044000031000000400e00e000800400000d000000000e000000000800e0020000008000003003000006a0000058000010006003800000600a0008094006000004800800401600280000160000000028002010006801c03c00d002800401200600500500000070000008172000000003c00000a00f000004c00000200300000070010000014000005800000001e00000180140040050010000003011800000a0100028010006003000001c00a019003000800200100280300000000060164000018005806800c00f00180380040060058008004001000800000c003003000400000000000080000040048054006000000804c01000000b800000c001000000400200400a802400600000780280100020008000004002000802c000008004001401000a002001002401500680100020000008000016000002800c01a00400080f801e015000800001e00100c804c02a005000009400804c008807c01a000000000000400100400000000030060084004005001800001c00000c00600000080000000012005000806c004002005800000000f00080280020000020008000004000002001c0010018008002002001000000000a000800803e005000010000000b005804400c00500d8100000001007801c018013000000800000200d800000e009003801401000000400d40040000000020008000007002800600100e000802000a0008000002005001800800e012003000002a00b00500200040040010048000000029000c00e008003000400201f010001000600a0000008096027000
  | 28 => 0xc3b509b0157cb051fbc52d24dc49f29c400030849391c5816c24941280064ca711c80000000000000034627e42832e601dd3d6c0d30d6c5540ce84be07c8b2525806352cb459d0a500001df0000138800030e800012545bc00000003e0443d1e94750000034312e907820dc24a35342d12eec000082061c41e4fb33514195161c6c0318c15222dc6772b84dc126dcfc41c60bed04202a92ae0539333487d18348ae23d800b0000bd937d00000ad811026e8d7f2f8800040e0cfd00005ba021035a03c45160000000000017c000054e0000f2d0bb86120f38dc92594a651bbcbaa30e08120ab81c21020150000000037306473fd8987000107d042c74415a48a33a90243297102c0d44000257c7990e14a3e1e00f8e1f9802a1b3ce9c0508000000094d2b748b63ab047c2d3cc0440105c230a04993f18bc12e1900d216c9b623789c82b6c9bb28082b82724000272cbde12680630bdc1803ac4aca3cd81b800002f234fc60b2efced3387842f33d4daf0ad067a3d7cb8e22f0fdc2ecd0071e5c4830000b04069429c166c4fb1b4c00036ec00007b88eb281000031950441f6c8bd42ec32719c483e0ee090f0940fb1000088804a83573afc24f38e40053c045ce044ce25043866d34e80790008901099490a26802a4007c20e28147ab01f50a02cecccf00003703ff8ed52d84b0a2fa8ebb00407e70f4cdd82b3044f161856e32f0e4f14b09d43ee8bc50198b5b1a903f32598e2d1bc8c70323904f27b0bfe0834868201c1de3cc8a9342b027b03f8f502b78ab4369800038d464b190c97a00000000000f9a2be48e50000ba610d0000195493c00000740b2800030287c921dc0460adc4640000000365c000344466006a07d33958de9086c3740000d6b15f41f52ccc3dd28343293a9c3a82f68f7b2cc49ea3ac8dc51690a160cec82c18c04cd1990ec81678734027c90728d843226c84b3362482108ec8ee33d8ec32740599430c3022ef0d0623142c51bc4000008878f3bb40000a48a4501f80000ce505000005f01c707f51788c470be400003a062f36a466e3a985cf00000003f14cf91ddc4480d584f122b00000000b5e000057b3fc87290280a9c2bbcb0e098045021685d3218ce2c000000000003420000d880cb4722178d06535f4b3d038400000000531fa8ee20b5478200005d83b30a5b000000018e8caa29f050b0aa00000000d992830b321aa434a1888d0e22141891b2cbd33f58bcc2260ad62f4884900010631c94f7736e436d021d0aa0000fd225f400038d0ae82a5064041c023000001b42ec0df814100f2368400428b083a01280d2304483513ccba20ca8fa20a605f90664f1e04102c92b88dce38e83c7256478b11241ce0d40ffd1c040703c50be131b0f9d1abcf4437e4a62372c0060f80ba414bc5d73458b6b3324a6b31c44753df
  | 29 => 0x5840078c3434ec1e0098cdbf27e89b314c0f701edc0c61d688e402fc7723ccc1e42f28eff1d601e818ec00016284a3080c88e004403c37403cf00000623fa4c5921ac9ca29a4f1b0840fff27ac76e2928fa32dcc73d043018512d90611a3824c423468232181d2053506d000000000006b10000000000045c220c0003744860331c6df3338d5914e048526043bc226c0f022e08bb14ec0001cf047a36480001c2c4ea30c8000125c5051198096304c0a21f20c88232400029a8ac21608000096454929247a40af8000193c5e71fed08a0000058000000027803550000f032f7c1a62df000037f80003d181e739b85330c586290e64d6a2650391247c16a2f6c96d20e026b23f42550b601a936a0cb7141833739bc0522da401c04cc9ff2af498e40940c920a0e471ca8ff826f05573ed09f30190af81430521171c00000000751f94135049cff723dc1f71368ca10081015111cb1404c0f2405445bb3e2c4bd27d4ab5109012222a451a0618f7125cc9233c750b216686581f141d119c870002340004174efb2fb8515402c0003a044003e9109b4268cfa00d8c932320ca32cf0df33f60489384006c362c0ab29d01e9041405b20f02dd2bdcc730c1012c3288f6d002464813c0cb830c0e002f58c561c4070a10dc7fc000000028dc9cf1dd80003e940000000b282c3c5e6000000000000000000000000079d0000f0528b85b61830000000098b15a902008a0ea80000cf73030f3106085aa41700c224d8afe2aa8dfd236cf623b8402825c85c13e24000283c8e1194cea015740002e94a890ec0013074c9902fdcc0941288d7020800020408ea05acce71eb107e15d031832546a22fcc24006b81171e30f4900005f700000511e38000033cc5e0000df60000ee4167c000059cd5336c898c2614000000106f15e827c1da808140d0eba0b888aa07b00001438db8355cb95398c6fd1324a872fb02773f1d0260a3d0a43c80927270c49325d844133c80ec40482d4213501a00001c42e5c18b000036038143f2000067d209806d039c62500008d3427c7ad3398c2d0000000000058127c90600a5c8b506fc7bb2b20e3f2d70ac73a0c4cb1d7c4813af80fd18e019f375866900000001ea8ae71f347ed00000161b08c5f0dd8000263cb6d2294d6e19d47e005640002d34fa61ef8000378cd0f00005602d04ddc31f8f2f04986ba1cdcb5f00000001b6cbff38bcf761d982863598b8a00000000000f3c24c47f20000000002068c169400000005ea0000000023000021b894b13e800037106b435680f8038c19a0db807311080800d504e30ba0169052810239684870d240b53ce0c990300f742c7cd9d07f4b0035d81362828dee334c1760ec809700000003a8c000000000000010011bd8fc80e6818c0000a8135f1027000069a19885432484280000097
  | 30 => 0x4b23482bf03e4d60000046d0e4c6bf221ca4320005421f680850cfc56110ac52615a0881407827d2584b3639cc5ad01643591d1c5d22944f0d4028458388c2fe15186f411f404806c825c36589c11a28bb60e7492d258cedb19b0aba2a944df07b4760213091128ace55350c6962cb80002a5400000004ad42a40003c1c3301064fe2000087f06e8000200d0c10c341650000000155826c0fe80003ce832600000ca349000005185a01818c3d000004200000001ee000000008692a7883038c40001994ff93d940003dfd0b620ecb4c0af0bdc0000f30000000000000001a00fda332c000000000000002cb389c00017900003fe83ac3fcc0f427610750ba43b905ecd5d3d48f6b3cf8c7c063cc1a14f81ea41350973b2432b00005eb306051839f4ada12d002e00004653d3ced11648af61aac99f382c2a101542fa3e085e50000d0a0000dc701a8000000058c41fcdb60000000000000a1004b1100000b108d8a6e1db4d5b35c808f052451c303c7b61838cc33be4fe60000c9b10f0e7608503920e18a780a2491321d4b271c747de03e86892010202000100c089c0073af0000083c0000000bce00000001cb86c632c897818a0e4200006d80394000385092e0000154301ca8f00001ac367cd5c042811b3eb8afd000032e0000fea0cd4e4012ac5b83f340c50344341230105400003323da88f23e9c7eb000075b3e000d800003831a7076b36f430f2d64d2d10b413706d498326c4d170000c7d10605c300003893a2c3aa0000b401578f39030434c269c60a0c2437321e42df000059319a022c35483e4000090312b0e770a6800036dc000148c40b2190e9e0000dde1da509235240001efc000146c20020441a3000004d2a607ee2154c9103fc32c0f289fe319c6730399028369029029541142f183fb338c3a12e400df1e10eb3114c85000b401709d482b23c0d8a000001a2774e29101875934dc2111be8fce12205f53d446953eace78115034401c86ce0a202af383836a08f41fe08e01291c1873025a829531609290fdc0003de02161d04b6e3bd40000000de625a0b0800f481a19305f436042e4053058f38647353d0d068000065b0000e490000e262e683e513bcd2c10d836f01003cc3bd8dda1bfc8a605d0f47098455a01245ca3d64f8317cc8450bc0cbb0e7c0002f242052d9800018c886d0000e7438cc5442d8c46100001f416980002d1caff2090ad23b086e10ea409207bcc8524904510fe0b810dd4c4b3090e600a7409d27b883f00000003da417513d00003154ed73ea40002794000000056613d82f329480004164c8140c472f17784e11be488d0000c87351ced90864efe1b490550000ee635b0f7e40507c00bd4bd10998000112c0003430000197c7d2000074d231800000002dc21e8000246446c00000001ab000027bc5a900
  | 31 => 0x71d01317205cc38dcd691ae0f4b34a4b10395c56b0000c2b0000bc400005d12afc00000006e22f2cf3f2a30bb10578fe329b4e413d60cb10bbc79115c8c6105b843014e87ec380887b3f40305219c1a43a186983b1464241387e90de802f071485e0728f57105c0002dc40003c58000000086f36300000b1076300002e736d400026e400012982ce2c4896936a824200fc58804f434716845ae11a40bc19e089724581782884c0b25240291b702c110f84b70074bfc3aa81f32c78d713f0cc3e22407b333a8ccc00000001174a1a0fb023c282c0000000310052c8cf000051f2670e0328a8e8200000180000d58000000000005e117f4000214c00000009c60000aa2394484000005af00000002078d0b1640e4a0c204461808eb61f5c00031e49540c44b9e338079f0000b65000084a1424f122bc8a682ac8f88261033e211086535e0ba83d045ed3c644801178331250c78a26908e81c6cbfb000000042743be1a9c0000000a4e0000e3e3dc85f82184b293484818000055019ecf5e0becbb412a875d0f5c0001aa8f1335310840138f7a3fb4627000097f4148fb73c5c056136c21f019c59627c00a11364a88058cc6240608560d3c72b2334b7b2e243c538ecc5327310452d54a58292c0000ce0a56227ca9d00000001d200002dfc5b731e8577358c00010380000df80000000d233494372165cb022b24a1c13b4b0b1500f043c6000000cc00024c883418587df15cc0003e4cf0608a435c33d00001c380000bd87891078cc800007c22ce45911e7018710cc0000000e241c206740b8d0770f0ceb4222429b204c3062058f42207441341c466628505ee1910e6428205fb00000002e10f352f3cf8d30d878715d80001a0cee83880b3f3ee0ba920884dc2398c7b2b18e4e2028d3632cc2233a40c9f3bc10000a048ef24787f615c4b072150a3b0b84b4636503f0043425d17c439c2bd03c83b106452acc771287cf3b1dbc31f0eec3f9248832f0490910024cc2a0638b8c0920e7122c0b832ab06e71adc9f60770740143c0cd0874f3d1138d2f0ae8b4516f48f406a820a0604f732a690bd2fe50ba02d0e6112409c01a34a673ac0ab111cc1f941a4e59355464a132848b10e858d2ee8a260e2c67f02d8bf540182db0000000069c0470000d312430beb044479216ccd7928c806b21641881eb83642848000336c8bf2c300000320fef24b00001330ef126d000000000000a310290000b8f0000e8f00008a7000000005b40000000eca00001e500005253b680000000e790001056008400000000000a9509c000109400000002eb812d1c7c0000000947000014000006410000000000000014d8f60000106a3340ed8077cd0d0fd0e3c23fc00009e4b2235cca8e18ac00040ac00000000002548b500648acf308cc800c486b0085c0000000e1b2cbce
  | 32 => 0x97900007671308f0e00008f9214817316d0e0623647b43b950420000000000000000009d100000000e6036837a8cde39b400016143ab37c08d808709ac00006a612a48d53f80ead30184601f5848e1b500002950aee02e4f111f40e9718a8d071cf800040390ae0d7cb1c369c8b10b3c0002138f4e00009d61b64b300950ae507187dd24ec0000000000000092600000003eb0000000026800000000ff0db000002510000c393a7c0002cac000000085800010b0307c0000000895329400009c04594240098000000025548c320c800000000001b2400029f5041379445230485c40f70160115c43937501b10b486b229f8af00a889a318f851e20244a405c041013c800033844e60000c00130000011f87861cc4690254c0000d7800027843400000b1826340002888000019439605f81011ab4aad04540000ecc35d350505832400001d54d380edc1d91570d4e0e50d2214c442604c502f28bc00000007753788651152c0000000da2000074a0c300611af10910000000251848a00000003c2c00041987b12d74dcf2380f8c12d40033e3ce701bd4b870000b092c34f6f26bc00012c06111d380000000e98082c49d000009138687bc0b209482b380000584000145c58309b80000f780000f0811a0b801e61a188a8000060327090a3017c4e431700fb1b0c100165000000001da241400017f826740fc0000000000012c7a93a6ca1d000021a00007ff000004f3668bf12368a4c0c287b90f347901400d2b00c80541a84752421861d408c6630fc400025040002cf8000423cad406843630a10c9200005d42d4c0000000f841b80814403c6c527e0a000b34749051501c1e4cb9b1bacce82d0cdca3f5c0d61480cd2352901929dc9381cb0dd70d34a4f31809e202b87a001681482da01180000a6f0610e6b28440bd3fc400026540002188db13318a192434f9f2e58bf40c909353db0000381098a3c089500f9c75412e498618b4bd73c400002fc0bab34d0a5918f0bd53ae4b3821d05450e20468086011d367051d1a48d2831040001a780001b0495629c075736b87c61a5c3d01b205d636940003374000188400016540001f90c69000000000000000000ec70000dfc00001e30e9d07a056c05d41d0cab0f7ca6116c4ad523ecf563e580003ff10ab0704be73978b6f1c4c02b1d784eb3b186762674f54276c66a0000e8e181ccd53d5400007ac4d316fc5753b80cef2b3403b0c8cfdf1bb06cc31390b709d86bd0f84df230d495c2e8095e184ce952d50989286ce931fa0a470df0be914d08661ad42b516601903bf44452a9ccff1d44b6c3c5492003680c73918c262f80bfd00e466f26e0c273d28a6428fcb1d1cec1fa0000041125809a1ee8e891404443347c77b315022a142874242883c60000fc02310cf11c8cca838242bb0340d542a907882
  | 33 => 0xc4a3bf046229fcc964014e922f743b53934abc0a2cba700008861058f2e19f8000000084306bc71500007612968f1c3abc0001304e720d4cdec28c4608051cf860f6c273410000010447a70e080001048a460be040c0000cee05982ac34c8e69394c5414230a852c6cff51a2cc1b12e095821c807c3efc5032d440000688cb930c41be0e400002f209022fe8717169c2783cb020c13a4871303400005bce5c00b008e0d2c3362574d05359c12032688f81270a2433ec0441ca0a993de401541cc48f1208cb00000c76000000000005df07d837700002fc13f400000010be05e4000000071100008b42b04ac50000fa11bc0ad822589e60c550ad000046f000021e10fd03e2c040782b400dd36acde4211c45f1b3400018e43e60c0cdba00000002f60000335cc941a3c30e00000002d58000000058917005141dc04201b58ec1349c0000cd011e37dc0003974000000065a00000000000319000024100003692d240001ed40001c98a0918d0e5b1a64e652a28000000000000000000000aed367902e1490f9916b05dc0ab400017646d000c03d23ba8a7210e0b440fd895b08f80001c7896e13f8cb62cd0d683460e6200007f905e8c290000b5a0e3419b04e0f6417fc8e30b5cd561860aa904b8cbf35dcab93bb000031b8a4d31a8a271f28eb70b084e832d4a331e8c423047108e20bc0003d849e73fb0b153c7c00000000000000a1038600d9000100900000003a3400000003e341acc0502780000298000000000001fc08812603c9365400034f0cbe2a5c89d2038ad7103cc773e8050240445520b6803a202c00000004ff00000001c80000125089a1bcc839000000000000002590fe4116847800000001898f7d15540261b2800039100dc2170ce901a0a2900000000000000000015c0c4c7fa02e8c970000000000000000381623a68f3441ec1c30000dcd34d400000000000000c7f0bc40002ad80001588d0403d4d14131ce8009b400024d08a00000baf000000000000003aa4558000000034b8232000068431e04dd11548d12438e0c313c1d5032c00000000000000000018105f00010af385c94212b80003c3c00027b50173ec8c6b25c0a63094cefa153c9ce3a1c64d2aecf9727dced0128088c189000f2418899075c65c2ac00003ef4be322bc00028d0193035449e37201fc339000014a060039d4dd90004912000025a36b4ef80bb486a3b2c23938a84740000d3d00006703070b9f1fc480801b8a7a15f8cf8404064e0000aaf0000567360cdc022ac000235800000000003c280570df400025b095108d469f0000d9142d000000505593c30d203478a5032603fd0000e11076c8cc0000000370cd7a0bf413c2b9825e0ac43ba0000d870c1ccdc3db90962474a39194800001ec00022282242094000183c000231cb930dc43d90000
  | 34 => 0xca8b02400002c4ccc111c4b761068ddf000044a02cc85d352c07700d4a910000e0f172461e1a8c0001a80f5a18500b740740002270e0a149c4073e482ec3f2ccd925dcc570dace7c1b8ceae2664faa3ca42a734cc9ae40ccdf1419c2091aa0b6706c0c4024604d02688af3134879408941f1344809c06d83872e08cad1974fcc23f83fe042414412885e901a47c40000fdd40589d228f0b78000000015b494a1b1c00042a000007249c40f2cdd328a054715900e4003000038e0a35036c5e83b7902122e89441d94d4402a0b35091470413808fa382106e3940c6402e098240b4cfe14ac5cb40f48ca0a7c5290574802176caec25d0d981cd82d6113490b0784c1609109910178ca9035cbb90b3038e39989001d0c99639201d0067484208104282694cc514fc61b314838a363849b0a088411ff90c40aa87e333b42520b98cae4204e2b16c886c21f877a1e145103ad4b622cb013400003c43b9c96b16e4b4e06e4d2601e838405dc70c1448b6a0cf0e1d38c0be813784d61de4aa8160009b0e80e130f88b0330dc57f39e8da3220813e1344a6c2e8c7c11008e670a3419c1a6c2c035903ed048440d13501560b64ce209a4e99109415f097c5790958d9b40dd0b518fc91c12f03ff364c4700e0000000010b309240002dd4adc2c805370fd40001050bac0fa000035d48be21f093d1fe0a231d88e0d00003bf2adc8df0000a7538b8bb837d46ae12c4c332e70f5c20b48fc000027e109c9670000ac435780003bbcd822f083b40000000422091b008ca83076000024cd00224ac5e00000b371670cac24a07021e6c0000000e451cc8b571f50233095cfc20a800a70de07271320ceb23b02313780be6000091a2600cf32a000001b98c4d1dfc4ee41688d00a1429e04e4aeb0f54b1a397c60427f45ef26a08d42b449ad277cfb517540451e547ce20a46bb1e0497e215c91426f48462f9099a0f043e9357c9a60d946ed0c68c03429c37b2ddcc3b3290801187c5f20634f9b3858172313042c24c000000003001c1400000004a10590f2a1e0c4f70a384041e68c022034c1531d000009fcb7e2e44dbe3408878130c3a42ef48922f503b128187f000000000504bb73e2854a35400002768cd6344cd85135c000118c35202240002fe0000379c3d10bad0b10000a1e37fc000426000026a80001b54d6d3eb4c5b185c00001bc00002180af1b104c41b748f508841a037540000338e012b8c7a60448d80000018336d03d8078842e23b4679281cafb00000001b90b2100000002d800002e7400006ece8c25ed03b1f30d151de02b93a500f30378f48208c62032bd0b83fa0c754298e360000a532a48b88245cea2009d09e00dcce52f0c0001e8400000005b030f00000c500000000ecf3280f1a2500b4a2e34f23213c0001f2c0002588e883f500000000194
  | 35 => 0x6000000000009a104fcf9840f0444337d036129c00000006b300006103f942c72880aab2e004ec1a14a132538c0e09390490fad0991088e281864bad0fbcfe12a3474f03d81190b4c01230b88b92454da0106d0242bc42e532e8b17144cb941af80000fb8d610f00b700934c0800000c31ff44cf0c04eeb2d48000000000000000003b5904b0000ec0000103000004fc000033d00c4f2610702342c64fee422cf221dd03a60000000043c0000000c9e2c8c000280c0001f650530818e8511d8043000079e332800016a03ae0000a574284de12dc8e7b02905073b8cc89223ca2d000043b42245be3d745fa1d2c55b3e1c08b1f3cc49000031b067823733005c522b42151ea06d1123000000003212f1cb7a17740003ef8f9e212048400908273ee466b41184bf0eb4f280e6c6910a4c0003d1440a3420071381cbb2000031e2070b4b100c000000000040d400004588c2361101f18683a334045783fd0ad921cccb400006010000b5800000001f880000000000000036c0000123009463735c0264384883121c0f210494f6811ec8800d38a401854d1923047f4107ca821d589de00000001ec82b3312070727f0ebd38f481b3360bd03040dac41d8cfc0554abe1420650222d093274cca62ca8c203aac3610c8039518d8a3d02283b62ed4bf61100038278c28712489751244c6803a81682514805098869437080002a84d62346c7e117d868112eca3006cc22f0f50e96297c6462d200000aacd300000c2f2b2d02242f0aea3c94c720000e5802ed07c255cffb3c9c6de0000000420ca25242480f0000c8b0000fb61dccc8a0658a48055ccec000062c3b4832500000002e2c9983f4d05b3f4463320f417131982a30c7023a053cc5a0e787532244d401984a791da09dc2e480501df858e406c0000bfc0003ebc6231014f913544f9c065cd900898fc92860c1e305098811fc000123400000001f816d400039a0000091c000000040908fd080394817f22784ce029413b0de450d1bf0a66116c9be03b4328162cd033088d392c906b61bf863d073053d2dd095a06f027137ac00017690390254cc20dfc0000d8899302c800010c40be0000dd20000db300002c61ba0a961cb465739fc0000ac00003884f903fac0003ea04c6000067c07344e70000cbd2b90ac0000015a000000000008b23f0400030fc0002de471400000000000c8c13e44a50e047a212bd0821d710bf054c6930c5c12f1534f081db06d721d90a5000000000000003eec76400000000ac80003b7c000020c000000000000000000000000307473a000000027ec10624e8000031000023880000000c9c1d1490824fc0001314f370000a15253c000371804c107443527a479643089e83f54e7e0b785351488edc24a8c8d071c26f14f0a17400c486390cd861c90c820000d481bec5512a6
  | 36 => 0xef505e43001ab3d98e221c48cd10e5c2ea1d18aa60c2cfde1bdd0873bdcece14c8201073c8930000c010000cc405380e907ec47722cca4216880002c1854c17f0b2611e40ad393046b181432207fd08503806ee062857c06f49bf00d106407c00eb1c685c6265cd741734be51fcc73804ac6f8115851940a8654047c656323c14310a4b64413028a34686a50af4cda2054d6531bc15839a873f0d208942974f090e301cb12a00000ebcee91e6052a37b4fdb2d08d091f708332b4cf751444aa01ec0103214477d02b0ddd24f88cb31b4ddb217c703000056529cc000351892f15b057006b400029d821200000001f0c8364144c19091800000004d508b8fcf196481f3b34e1531745ec00009a902c0c510000a442a7c9e41f447c72030ba114b882e00009c500000001ae46e502a821300008842a1000000000003634b9935f80000000806119ce910000def23a41c02a180002b7c2c300000003f64bf241c87af3114fbc35bc0003cacc2517408e708b413a09d0bef000000034f87213e5469d09c800000007333ec054833509ab275ca3a066065e20a8e6c3d000000000000000104800009f40000d00096094c38c800039500001360000154c3a50d609f126780ee092c0000b40c4237a08ce2bd400025c4ff00a4505716ac05c0250d1d03dc01b0720000000029626d45630000000182400000003ea000099b0000ae90d150433d30000199c8a20f580002bf062e3ae0cf001d87093f281071c3cd8f321013231186490a9833300000003140ac3229009935ec0002764f67000000041b0e1f2ce846e29ed0471a2022b2838f4d1f60ef234a8edd13940001084e1c13d40d415bcd103470ae0081c00d327474c2410ef30000e84096c00036f00000000817168cd422754ef403306ea28050622e150b91ef44f803f0eee212cbc003bcaa337e89cd0bd096f29788dd22840a93a7478d09a80e20880aae105509523c400007503660a64819305c0001fdd0320c747d50644f6340e80000000c444314d4f1ba500805f40002980c8306dc27a0000f8537ec820310c6312a406da3a288dc00003da0e88bcd0d9cea500001d
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x96090840a2b8058d5290440c0f735496090440a0d821d56310440e056354a5110440e05639495110440e096354a6010440e0a635496010440a2980191528c440c0c7650d524c440b048150d524c440a908150c604c440e0943548604c440a0d831915208440b0a839515250040c29625c06295330a1586951310c730a29841496008530a248155162101308d0815c06250c30a15811954350830989801c94350830a888250c6050830e11435446050430a0d821516310430a15811516310430a1687591510c430a1487591510c430e0564dc9510c430d04741c9510c430e05641c9510c430d10741c1510c430e11641c1510c430d40721c1510c430a158418d5148430c0d655d03208430a8882590404c030a9081590404c030c89645c8404c030c15645c6530c720a15811516310620a2980d8d6215120c0d735886115120c29625c06115120c0d7358b6015120c28655c34350920e085414c6050920a288550c6050920d08531c14210920d23541c14214520d20541c14214520d43531c14214520d40531c14214520960805c84314520b05831914214520b21801914214520b2180d0d4214520d23641c14214520d20641c14214520d23431c14214520d21431c14214520b20805084214520a608058851d0520b20805085190520a0c8558d4210520c0c7558d4210520c89631c14210520e05635085110520b20805085110520a0c8558d42d0120c0c7558d42d0120c89631c142d0120e056350851d0120b208050851d0120a2586908511012082d87150624c120a2584188514c120989841c9300c120d08541c9300c120d4072145300c120a148158c6355020c29545c262d0420c29545c262cc420a2a875516008420a28875516008420e0954dcd6008420c88741cd6008420e09541cd6008420a0c865506348020a26865506148020a24865506148020e0554d8c6148020e055418c6148020e20805506148020aa0845c06148020e21545c06148020ac0835c06148020d09549cf4048020e21541874048020cc273187404802092b875533048020ca2741873048020e21541873048020e21541843048020929859d03248020929859d32148020a0d829916315310a298295160d0f10a0d829516310710c91641c1310c710a29849496008710a0d8295163d0310a0d831516210310c9174584310c310a25849486148310a0d839916215210a158395161d0a10a0d8395162d0610a0d821516310610a198494c604c610a0d839516210210a158494d610c210ca1645c02108210ca1641c52008210c1475591310c510a1586151310c510e0564149310c510c28755912008110a29861512008110e096414d2008110c61651c14208410c51651c5430c010c19655d0310c010cc1760c8210c010b41850c8210c010b81840c8210c010c25755902108010
  | 1 => 0xcc00171f150244b5700000bb441a19237001a80a1018145a000002accc550023000aa6a264ec0002338001d5625982005a124005d15000e0dd0037800001c94c1a0000000ae4501a8c58001c0004000000ac004a0f800000048001264e2f800c0651691cf8b12080412000f22400b7000896a9b5e80068a56d968364347984766d290294c5861171a669389ad80480000172c5130011a0057a7d487914a5c0419592600c362f1f4a0001d000001a39a18000045b606a000980088003f08528bf2c8c81e25580913a4d661dcea5b6b8010e0000000dca2001198c2e5009d06da00210c42f140000000000002800410010200640018ea7693540085452380e800aae9669a05ae1b8bc54871b2d1488600000619bc7a234a98c00c4188300000001e07e0008804050c800000401000000b050001a010980014060282c0607010000200008080002018140200000100c030b0700c0c008140400070180c0a0400c00000000004060000c0221008040c07028600012010640000918805c45350d428a4815c06250d42d05435c44394b41a0e86d4d4354b41b0a80d4d4354b4190d839d06054b4190d829d36054c41a48825806054c41a50815806054c41c1553dc56290c41c0d53dc96190c41d05539c7525084190d8794c5250841d0a535c05250841b06829515350441c15635c76215131c0d635cb6115131d04541c54314931b048150c4314931c14651c54350931c0c7550d62d0531a848150d62d0531d13541c54314131d10541c54314131b408150f5214131b408150c5214131b09821914314131b11811914314131d13641c54314131d10641c54314131b108150c4314131b108150f4214131d11435c74214131b108150d4214131950815cc4214131b108150f4114131d09435cb41141319198790c4114131a28805886255031a0c86550624c431d05549cb414c431a1a86550604c431a1886550604c431e0954d88604c431e0954188604c431e1081550604c431e1154d04604c431ac282d04604c431915859d0324c431c15635c46395321a1586951310c721c91641c1310c721d12541c1310c721a0d829516310521a15819516310521a1880551631052181d87190534c521a198414c604c5218e0805c46350821929801d54350821a858118d4350821c84631c54350821c91641c1310c421a84835904148421aa0805904148421c85645cc4148421a858418d3148421c847418d3148421cc0631c1314842190d829d06154f40d05539c75250b4090d8794c5250b40e0a535096010b40a508154c604c740c15645c6530c740c1563dc55210640c0d63dc95110640a908150c604c640e21421456008540b058114d4394840a0e86d4d4354840b0a80dcd435484090d839d36154840a44835846154840a60805846154840a2b8058d5290840c0f7354
  | 2 => 0xa10032d38b63a13d3c1620020987a541ed94725699d7c5649358d8cf071fc00cd0010800641e0
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x2a00001600000000001220012200e000000000600000000324000980000b82d3678002ca1051acb883a286c0001c0000000040c200003008ea40a86b168298d40648641c54314131a8048a86b968228263a0154a0b41181310c68232d2a0e09886390ca02418118d4350821a40482c8b988290843085981d0634c52108690328318e098a4210e011d88150d524c440b0048a86a90c098881180916007250d420c28092eb20e4a88621850425d641c1510c430e00b20e4382a2188614809159172101300c2a0326320e0a10a290502255631c14210520d00b1900a10a220a414089558c7050b40483402c64028428e8090442660541c9300c120a80ca0e428a601824140897550735802108244130aa2e030a4010680550835c06148020e00aa4e630e80900414239755061cc120083082ecc286410860086205d9840c8210c010
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 40
  | 6 => 1844
  | 5 => 9193
  | 4 => 4294
  | 3 => 223
  | 2 => 30
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
  | 6 => packedAt gbK6 (57156+((h/614+packedAt gbK6 (49788+(h % 614)*12) 12) % 2434)*12) 12
  | 5 => packedAt gbK5 (392230+((h/3064+packedAt gbK5 (349334+(h % 3064)*14) 14) % 14682)*15) 15
  | 4 => packedAt gbK4 (229009+((h/1431+packedAt gbK4 (210406+(h % 1431)*13) 13) % 5153)*14) 14
  | 3 => packedAt gbK3 (14046+((h/74+packedAt gbK3 (13380+(h % 74)*9) 9) % 294)*9) 9
  | 2 => packedAt gbK2 (2190+((h/10+packedAt gbK2 (2130+(h % 10)*6) 6) % 62)*6) 6
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xff01fff80ffffff03fffffc0ffe0fff9fc71ff
  | 1 => 0x3ffffffff01fffffc0fc0fffffff07fe47fe3f
  | 2 => 0x3ffe03ffffe03fffff000fff07fff87f878fc7
  | 3 => 0xc00003ffffffc07ffffff00007ffff87f80ff8
  | 4 => 0xfffffc000000007ffffffffff8000007fff000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x814c2888e24489100b2c92c8496048c89c30db
  | 1 => 0x9214511121c91222c055055192a9051241d62d
  | 2 => 0x24289aa24483a455550289aa44d2d065868b46
  | 3 => 0x30b1634489120769a69b2030871ca607680db0
  | 4 => 0x38c183870e1c387e38e3ce3ce018c447f76000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xeac8e880eac8e880eac8e880eac8e880eac8e880eac8e880eac8e880eac8e880eac8e880eac8e880eac8e880eac8e880eac8e880eac8e880eac8e880eac8e880, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_12849
namespace PEqualNP.Outside.L_meta_12849
open PEqualNP.Outside.L_meta_12849.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 30 := bgb_2_0
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
theorem bgb_3_192 : Interval gbAtlas 3 192 31 := block_range (n:=31) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 223 := (concat (concat bgb_3_0 (concat bgb_3_32 bgb_3_64)) (concat (concat bgb_3_96 bgb_3_128) (concat bgb_3_160 bgb_3_192)))
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
theorem bgb_4_3904 : Interval gbAtlas 4 3904 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3936 : Interval gbAtlas 4 3936 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3968 : Interval gbAtlas 4 3968 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4000 : Interval gbAtlas 4 4000 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4032 : Interval gbAtlas 4 4032 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4064 : Interval gbAtlas 4 4064 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4096 : Interval gbAtlas 4 4096 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4128 : Interval gbAtlas 4 4128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4160 : Interval gbAtlas 4 4160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4192 : Interval gbAtlas 4 4192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4224 : Interval gbAtlas 4 4224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4256 : Interval gbAtlas 4 4256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4288 : Interval gbAtlas 4 4288 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 4294 := (concat (concat (concat (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 bgb_4_224))) (concat (concat (concat bgb_4_256 bgb_4_288) (concat bgb_4_320 bgb_4_352)) (concat (concat bgb_4_384 bgb_4_416) (concat bgb_4_448 bgb_4_480)))) (concat (concat (concat (concat bgb_4_512 bgb_4_544) (concat bgb_4_576 bgb_4_608)) (concat (concat bgb_4_640 bgb_4_672) (concat bgb_4_704 bgb_4_736))) (concat (concat (concat bgb_4_768 bgb_4_800) (concat bgb_4_832 bgb_4_864)) (concat (concat bgb_4_896 bgb_4_928) (concat bgb_4_960 (concat bgb_4_992 bgb_4_1024)))))) (concat (concat (concat (concat (concat bgb_4_1056 bgb_4_1088) (concat bgb_4_1120 bgb_4_1152)) (concat (concat bgb_4_1184 bgb_4_1216) (concat bgb_4_1248 bgb_4_1280))) (concat (concat (concat bgb_4_1312 bgb_4_1344) (concat bgb_4_1376 bgb_4_1408)) (concat (concat bgb_4_1440 bgb_4_1472) (concat bgb_4_1504 (concat bgb_4_1536 bgb_4_1568))))) (concat (concat (concat (concat bgb_4_1600 bgb_4_1632) (concat bgb_4_1664 bgb_4_1696)) (concat (concat bgb_4_1728 bgb_4_1760) (concat bgb_4_1792 bgb_4_1824))) (concat (concat (concat bgb_4_1856 bgb_4_1888) (concat bgb_4_1920 bgb_4_1952)) (concat (concat bgb_4_1984 bgb_4_2016) (concat bgb_4_2048 (concat bgb_4_2080 bgb_4_2112))))))) (concat (concat (concat (concat (concat (concat bgb_4_2144 bgb_4_2176) (concat bgb_4_2208 bgb_4_2240)) (concat (concat bgb_4_2272 bgb_4_2304) (concat bgb_4_2336 bgb_4_2368))) (concat (concat (concat bgb_4_2400 bgb_4_2432) (concat bgb_4_2464 bgb_4_2496)) (concat (concat bgb_4_2528 bgb_4_2560) (concat bgb_4_2592 (concat bgb_4_2624 bgb_4_2656))))) (concat (concat (concat (concat bgb_4_2688 bgb_4_2720) (concat bgb_4_2752 bgb_4_2784)) (concat (concat bgb_4_2816 bgb_4_2848) (concat bgb_4_2880 bgb_4_2912))) (concat (concat (concat bgb_4_2944 bgb_4_2976) (concat bgb_4_3008 bgb_4_3040)) (concat (concat bgb_4_3072 bgb_4_3104) (concat bgb_4_3136 (concat bgb_4_3168 bgb_4_3200)))))) (concat (concat (concat (concat (concat bgb_4_3232 bgb_4_3264) (concat bgb_4_3296 bgb_4_3328)) (concat (concat bgb_4_3360 bgb_4_3392) (concat bgb_4_3424 bgb_4_3456))) (concat (concat (concat bgb_4_3488 bgb_4_3520) (concat bgb_4_3552 bgb_4_3584)) (concat (concat bgb_4_3616 bgb_4_3648) (concat bgb_4_3680 (concat bgb_4_3712 bgb_4_3744))))) (concat (concat (concat (concat bgb_4_3776 bgb_4_3808) (concat bgb_4_3840 bgb_4_3872)) (concat (concat bgb_4_3904 bgb_4_3936) (concat bgb_4_3968 bgb_4_4000))) (concat (concat (concat bgb_4_4032 bgb_4_4064) (concat bgb_4_4096 bgb_4_4128)) (concat (concat bgb_4_4160 bgb_4_4192) (concat bgb_4_4224 (concat bgb_4_4256 bgb_4_4288))))))))
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
theorem bgb_5_6048 : Interval gbAtlas 5 6048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6080 : Interval gbAtlas 5 6080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6112 : Interval gbAtlas 5 6112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6144 : Interval gbAtlas 5 6144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6176 : Interval gbAtlas 5 6176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6208 : Interval gbAtlas 5 6208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6240 : Interval gbAtlas 5 6240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6272 : Interval gbAtlas 5 6272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6304 : Interval gbAtlas 5 6304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6336 : Interval gbAtlas 5 6336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6368 : Interval gbAtlas 5 6368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6400 : Interval gbAtlas 5 6400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6432 : Interval gbAtlas 5 6432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6464 : Interval gbAtlas 5 6464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6496 : Interval gbAtlas 5 6496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6528 : Interval gbAtlas 5 6528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6560 : Interval gbAtlas 5 6560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6592 : Interval gbAtlas 5 6592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6624 : Interval gbAtlas 5 6624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6656 : Interval gbAtlas 5 6656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6688 : Interval gbAtlas 5 6688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6720 : Interval gbAtlas 5 6720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6752 : Interval gbAtlas 5 6752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6784 : Interval gbAtlas 5 6784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6816 : Interval gbAtlas 5 6816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6848 : Interval gbAtlas 5 6848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6880 : Interval gbAtlas 5 6880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6912 : Interval gbAtlas 5 6912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6944 : Interval gbAtlas 5 6944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6976 : Interval gbAtlas 5 6976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7008 : Interval gbAtlas 5 7008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7040 : Interval gbAtlas 5 7040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7072 : Interval gbAtlas 5 7072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7104 : Interval gbAtlas 5 7104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7136 : Interval gbAtlas 5 7136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7168 : Interval gbAtlas 5 7168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7200 : Interval gbAtlas 5 7200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7232 : Interval gbAtlas 5 7232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7264 : Interval gbAtlas 5 7264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7296 : Interval gbAtlas 5 7296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7328 : Interval gbAtlas 5 7328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7360 : Interval gbAtlas 5 7360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7392 : Interval gbAtlas 5 7392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7424 : Interval gbAtlas 5 7424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7456 : Interval gbAtlas 5 7456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7488 : Interval gbAtlas 5 7488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7520 : Interval gbAtlas 5 7520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7552 : Interval gbAtlas 5 7552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7584 : Interval gbAtlas 5 7584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7616 : Interval gbAtlas 5 7616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7648 : Interval gbAtlas 5 7648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7680 : Interval gbAtlas 5 7680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7712 : Interval gbAtlas 5 7712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7744 : Interval gbAtlas 5 7744 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7776 : Interval gbAtlas 5 7776 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7808 : Interval gbAtlas 5 7808 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7840 : Interval gbAtlas 5 7840 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7872 : Interval gbAtlas 5 7872 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7904 : Interval gbAtlas 5 7904 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7936 : Interval gbAtlas 5 7936 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7968 : Interval gbAtlas 5 7968 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8000 : Interval gbAtlas 5 8000 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8032 : Interval gbAtlas 5 8032 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8064 : Interval gbAtlas 5 8064 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8096 : Interval gbAtlas 5 8096 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8128 : Interval gbAtlas 5 8128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8160 : Interval gbAtlas 5 8160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8192 : Interval gbAtlas 5 8192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8224 : Interval gbAtlas 5 8224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8256 : Interval gbAtlas 5 8256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8288 : Interval gbAtlas 5 8288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8320 : Interval gbAtlas 5 8320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8352 : Interval gbAtlas 5 8352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8384 : Interval gbAtlas 5 8384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8416 : Interval gbAtlas 5 8416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8448 : Interval gbAtlas 5 8448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8480 : Interval gbAtlas 5 8480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8512 : Interval gbAtlas 5 8512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8544 : Interval gbAtlas 5 8544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8576 : Interval gbAtlas 5 8576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8608 : Interval gbAtlas 5 8608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8640 : Interval gbAtlas 5 8640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8672 : Interval gbAtlas 5 8672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8704 : Interval gbAtlas 5 8704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8736 : Interval gbAtlas 5 8736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8768 : Interval gbAtlas 5 8768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8800 : Interval gbAtlas 5 8800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8832 : Interval gbAtlas 5 8832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8864 : Interval gbAtlas 5 8864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8896 : Interval gbAtlas 5 8896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8928 : Interval gbAtlas 5 8928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8960 : Interval gbAtlas 5 8960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8992 : Interval gbAtlas 5 8992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9024 : Interval gbAtlas 5 9024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9056 : Interval gbAtlas 5 9056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9088 : Interval gbAtlas 5 9088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9120 : Interval gbAtlas 5 9120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9152 : Interval gbAtlas 5 9152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9184 : Interval gbAtlas 5 9184 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 9193 := (concat (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)))) (concat (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)) (concat (concat bgb_5_416 bgb_5_448) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))))) (concat (concat (concat (concat bgb_5_576 bgb_5_608) (concat bgb_5_640 bgb_5_672)) (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)))) (concat (concat (concat bgb_5_864 bgb_5_896) (concat bgb_5_928 bgb_5_960)) (concat (concat bgb_5_992 bgb_5_1024) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)))))) (concat (concat (concat (concat (concat bgb_5_1152 bgb_5_1184) (concat bgb_5_1216 bgb_5_1248)) (concat (concat bgb_5_1280 bgb_5_1312) (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)))) (concat (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536)) (concat (concat bgb_5_1568 bgb_5_1600) (concat bgb_5_1632 (concat bgb_5_1664 bgb_5_1696))))) (concat (concat (concat (concat bgb_5_1728 bgb_5_1760) (concat bgb_5_1792 bgb_5_1824)) (concat (concat bgb_5_1856 bgb_5_1888) (concat bgb_5_1920 (concat bgb_5_1952 bgb_5_1984)))) (concat (concat (concat bgb_5_2016 bgb_5_2048) (concat bgb_5_2080 bgb_5_2112)) (concat (concat bgb_5_2144 bgb_5_2176) (concat bgb_5_2208 (concat bgb_5_2240 bgb_5_2272))))))) (concat (concat (concat (concat (concat (concat bgb_5_2304 bgb_5_2336) (concat bgb_5_2368 bgb_5_2400)) (concat (concat bgb_5_2432 bgb_5_2464) (concat bgb_5_2496 (concat bgb_5_2528 bgb_5_2560)))) (concat (concat (concat bgb_5_2592 bgb_5_2624) (concat bgb_5_2656 bgb_5_2688)) (concat (concat bgb_5_2720 bgb_5_2752) (concat bgb_5_2784 (concat bgb_5_2816 bgb_5_2848))))) (concat (concat (concat (concat bgb_5_2880 bgb_5_2912) (concat bgb_5_2944 bgb_5_2976)) (concat (concat bgb_5_3008 bgb_5_3040) (concat bgb_5_3072 (concat bgb_5_3104 bgb_5_3136)))) (concat (concat (concat bgb_5_3168 bgb_5_3200) (concat bgb_5_3232 bgb_5_3264)) (concat (concat bgb_5_3296 bgb_5_3328) (concat bgb_5_3360 (concat bgb_5_3392 bgb_5_3424)))))) (concat (concat (concat (concat (concat bgb_5_3456 bgb_5_3488) (concat bgb_5_3520 bgb_5_3552)) (concat (concat bgb_5_3584 bgb_5_3616) (concat bgb_5_3648 (concat bgb_5_3680 bgb_5_3712)))) (concat (concat (concat bgb_5_3744 bgb_5_3776) (concat bgb_5_3808 bgb_5_3840)) (concat (concat bgb_5_3872 bgb_5_3904) (concat bgb_5_3936 (concat bgb_5_3968 bgb_5_4000))))) (concat (concat (concat (concat bgb_5_4032 bgb_5_4064) (concat bgb_5_4096 bgb_5_4128)) (concat (concat bgb_5_4160 bgb_5_4192) (concat bgb_5_4224 (concat bgb_5_4256 bgb_5_4288)))) (concat (concat (concat bgb_5_4320 bgb_5_4352) (concat bgb_5_4384 bgb_5_4416)) (concat (concat bgb_5_4448 bgb_5_4480) (concat bgb_5_4512 (concat bgb_5_4544 bgb_5_4576)))))))) (concat (concat (concat (concat (concat (concat (concat bgb_5_4608 bgb_5_4640) (concat bgb_5_4672 bgb_5_4704)) (concat (concat bgb_5_4736 bgb_5_4768) (concat bgb_5_4800 (concat bgb_5_4832 bgb_5_4864)))) (concat (concat (concat bgb_5_4896 bgb_5_4928) (concat bgb_5_4960 bgb_5_4992)) (concat (concat bgb_5_5024 bgb_5_5056) (concat bgb_5_5088 (concat bgb_5_5120 bgb_5_5152))))) (concat (concat (concat (concat bgb_5_5184 bgb_5_5216) (concat bgb_5_5248 bgb_5_5280)) (concat (concat bgb_5_5312 bgb_5_5344) (concat bgb_5_5376 (concat bgb_5_5408 bgb_5_5440)))) (concat (concat (concat bgb_5_5472 bgb_5_5504) (concat bgb_5_5536 bgb_5_5568)) (concat (concat bgb_5_5600 bgb_5_5632) (concat bgb_5_5664 (concat bgb_5_5696 bgb_5_5728)))))) (concat (concat (concat (concat (concat bgb_5_5760 bgb_5_5792) (concat bgb_5_5824 bgb_5_5856)) (concat (concat bgb_5_5888 bgb_5_5920) (concat bgb_5_5952 (concat bgb_5_5984 bgb_5_6016)))) (concat (concat (concat bgb_5_6048 bgb_5_6080) (concat bgb_5_6112 bgb_5_6144)) (concat (concat bgb_5_6176 bgb_5_6208) (concat bgb_5_6240 (concat bgb_5_6272 bgb_5_6304))))) (concat (concat (concat (concat bgb_5_6336 bgb_5_6368) (concat bgb_5_6400 bgb_5_6432)) (concat (concat bgb_5_6464 bgb_5_6496) (concat bgb_5_6528 (concat bgb_5_6560 bgb_5_6592)))) (concat (concat (concat bgb_5_6624 bgb_5_6656) (concat bgb_5_6688 bgb_5_6720)) (concat (concat bgb_5_6752 bgb_5_6784) (concat bgb_5_6816 (concat bgb_5_6848 bgb_5_6880))))))) (concat (concat (concat (concat (concat (concat bgb_5_6912 bgb_5_6944) (concat bgb_5_6976 bgb_5_7008)) (concat (concat bgb_5_7040 bgb_5_7072) (concat bgb_5_7104 (concat bgb_5_7136 bgb_5_7168)))) (concat (concat (concat bgb_5_7200 bgb_5_7232) (concat bgb_5_7264 bgb_5_7296)) (concat (concat bgb_5_7328 bgb_5_7360) (concat bgb_5_7392 (concat bgb_5_7424 bgb_5_7456))))) (concat (concat (concat (concat bgb_5_7488 bgb_5_7520) (concat bgb_5_7552 bgb_5_7584)) (concat (concat bgb_5_7616 bgb_5_7648) (concat bgb_5_7680 (concat bgb_5_7712 bgb_5_7744)))) (concat (concat (concat bgb_5_7776 bgb_5_7808) (concat bgb_5_7840 bgb_5_7872)) (concat (concat bgb_5_7904 bgb_5_7936) (concat bgb_5_7968 (concat bgb_5_8000 bgb_5_8032)))))) (concat (concat (concat (concat (concat bgb_5_8064 bgb_5_8096) (concat bgb_5_8128 bgb_5_8160)) (concat (concat bgb_5_8192 bgb_5_8224) (concat bgb_5_8256 (concat bgb_5_8288 bgb_5_8320)))) (concat (concat (concat bgb_5_8352 bgb_5_8384) (concat bgb_5_8416 bgb_5_8448)) (concat (concat bgb_5_8480 bgb_5_8512) (concat bgb_5_8544 (concat bgb_5_8576 bgb_5_8608))))) (concat (concat (concat (concat bgb_5_8640 bgb_5_8672) (concat bgb_5_8704 bgb_5_8736)) (concat (concat bgb_5_8768 bgb_5_8800) (concat bgb_5_8832 (concat bgb_5_8864 bgb_5_8896)))) (concat (concat (concat bgb_5_8928 bgb_5_8960) (concat bgb_5_8992 bgb_5_9024)) (concat (concat bgb_5_9056 bgb_5_9088) (concat bgb_5_9120 (concat bgb_5_9152 bgb_5_9184)))))))))
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
theorem bgb_6_1824 : Interval gbAtlas 6 1824 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1844 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)) (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 bgb_6_416)))) (concat (concat (concat bgb_6_448 (concat bgb_6_480 bgb_6_512)) (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640))) (concat (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 bgb_6_768)) (concat (concat bgb_6_800 bgb_6_832) (concat bgb_6_864 bgb_6_896))))) (concat (concat (concat (concat bgb_6_928 (concat bgb_6_960 bgb_6_992)) (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 bgb_6_1120))) (concat (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216)) (concat (concat bgb_6_1248 bgb_6_1280) (concat bgb_6_1312 bgb_6_1344)))) (concat (concat (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440)) (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 bgb_6_1568))) (concat (concat (concat bgb_6_1600 bgb_6_1632) (concat bgb_6_1664 bgb_6_1696)) (concat (concat bgb_6_1728 bgb_6_1760) (concat bgb_6_1792 bgb_6_1824))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_32 : Interval gbAtlas 7 32 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 40 := (concat bgb_7_0 bgb_7_32)
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
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 5 zero,inputs.getD 4 zero]
def fullWord : Sig := 0xeac8e880e880e880eac8e880e880e880eac8e880e880e880eac8e880e880e880eac8e880e880e880eac8e880e880e880eac8e880e880e880eac8e880e880e880
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 0 32) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,19,51)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,19,51)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (3939035264 * 2 ^ 32 + 3900762240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_12849.Model.Repr at out
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

def mono : List Gate := [⟨.and,[1,2]⟩,⟨.and,[4,5]⟩,⟨.and,[1,3]⟩,⟨.and,[0,2]⟩,⟨.or,[8,9]⟩,⟨.or,[0,6]⟩,⟨.or,[1,3]⟩,⟨.or,[7,10]⟩,⟨.and,[11,13]⟩,⟨.or,[1,12]⟩,⟨.and,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3939035264 * 2 ^ 32 + 3900762240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3939035264 * 2 ^ 32 + 3900762240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_12849

open PEqualNP.Outside.L_meta_12849 in
theorem PEqualNP.Outside.L_meta_12849 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3939035264 * 2 ^ 32 + 3900762240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3939035264 * 2 ^ 32 + 3900762240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
