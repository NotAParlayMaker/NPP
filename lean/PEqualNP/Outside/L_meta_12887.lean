import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_12887.Model
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


end PEqualNP.Outside.L_meta_12887.Model

namespace PEqualNP.Outside.L_meta_12887
open PEqualNP.Outside.L_meta_12887.Model
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

def SBf (j : Nat) : Nat := [7, 7, 7, 7, 7, 7].getD j 0

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

end PEqualNP.Outside.L_meta_12887

namespace PEqualNP.Outside.L_meta_12887
open PEqualNP.Outside.L_meta_12887.Model
def s0K6 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x12880524780700310a982ac1289860000a058e6ae0080048000c2bfe65f8cbe997c32fe63f8c7e98fc31fe43f887e90fc21fe61f8c3e987c30fe41f883e907c20fe21f843e887c10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0xa070e00804100483c4c040b030140102874000d0283400060003c0002090142c000204404330e8041a13be41ccaf50732be40ccaf50332bd438caf90a32df328cbbcca32be418caf50632be408caf50232ef324cb78c932bf414cbdd0532b7414caf10532f4414cad10532bf404cbed0132bb404caf10132f8404cae10132be430caf90832df320cbb8c832dd320cbb4c832cd320caf90432bd410caf90032bd400caf90b31bd42cc6f90331bd40cc6f50e31be428c6f50a31de328c770ca31be418c77cc631f7318c6f90231bd408c6fd0931ef424c6bd0931bc424c7b10931ac424c7dcc531de314c6fd0131fb404c6ed0131bc404c7e10131b8404c6f90c31be420c6f50831de320c770c831be410c77cc431f6310c774c431f5310c754c431be400c6f50031bf43c86f90f21bd43c86f10f21f731c87d0c721be40c86f50321bf43886f90e21bd43886f10e21bd42887bcca21ec32886f90621ef21887dc8621be40886f50221bf434877d0d219f43486f90d21bd43486f10d21dc43486710d21f721487b88521bf40487ed0121bb40486f10121f840486e10121bf43086f90c21bd43086f10c21be42087bcc821ec32086f90421f731087d0c421ef21087d88421ed21087d48421e521086f90021bd40086f90b30bd42cc2f90730bd41cc2f50e30be428c2f50a30de328c370ca30be418c2f50630de318c370c630be408c37cc230fb308c2fd0930ef424c2bd0930bc424c3b10930ac424c2fd0530f7414c2dd0530bc414c3d10530b4414c3ecc130de304c2f90c30be420c2f50830de320c370c830be410c2f50430de310c370c430be400c37cc030fa300c374c030f9300c364c030bf43c82f90f20bd43c82f10f20be41c82f50720fb30c83e0c320bf43882f90e20bd43882f10e20bd42883bcca20ec32882f90620bd41883b88620ec21882f90220ef20883ec8220bf434837d0d209f43482f90d20bd43482f10d20dc43482710d20bf41483dd0520b741482f10520f441482d10520fb20483b88120bf43082f90c20bd43082f10c20be42083bcc820ec32082f90420bd41083b88420ec21082f90020fb30083e0c020ef20083e88020ed20083e48020e920082fd0f10be43c42f50f10bc43c42fd0b10be42c42f50b10bc42c43ecc310f830c43ec8310f820c42fd0e10be43842f50e10bc43842fd0a10be42842f50a10bc42842f50610f731843d0c610f721843d08610be40843dc4210fb10842fd0d10df434427d0d10be43442f50d10bc43443710d109c43442fd0910ef42442bd0910be42442f50910bc42443b10910ac42443ec4110f610442fd0c10be43042f50c10bc43042fd0810be42042f50810bc42042f90410f731043d0c410f721043d08410be40043ecc010f830043ec8010f820043dc4010fa10043d44010f910043c44010
  | 1 => 0x1723e1e8001928d9ba000f44a23c240744892e3488631a16730b06005a6e04e9382c58800420f02fa086115a00000001966880063800070c48f80c7ba388a82a468008998a00000849f064000198005c00000060000001900006a1a15000750b65b1b015968230a2759d06aa400021c7c86a000e63ea0e0b97a4394c9484a4086c4d000350ec1fa303814e0c8aa6d1423a93e4483a779c4828dc000300000076a06001a6928b4001440f000760002009a808d84e80000000001fa718001780086156771a800042009600019400072959ce000140d0ac831ea7d9c21192a6ba46001e6048280025a3a15e0000000138001764d9c000250028e42b8767924c0603e95174188ee78222680920013c2f07c599f8608705200e4911e148445f9003416a23a48091e2570fc6791822800121bc001d2260de001ac2e8fe00210001ec000584323425130000008e9547d0062081e561887f8006f98c4b1b27f06e519c835838670b821016850cc879a42a1ca8b114428782c8da080688a000170000009e0004c541101e8a445836498a65f140002420019a548885e0ca040e248106320c20216e528a06d8f633a24141048811c81040800f22589c59232099864c8c09624408a2e660040d80c0609058201608030100c0b028380403018100a040405c0a11000100602000080000028100a0f0401400000081006030402c22000b824000c0180002010201416000000c
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x88632f5250031962928018ce94343c8672a1a1e4397430c7219d2868710ce543438871e86194431e5390d219d2848690ce542434865ea4a1a43375150d219da828690ce141434863ca821a439443c8521c621c4290e6d0f404873087a02439b4310121cc2188090ecc84404875442202433b5050c219c2828610ce9404308672a0218432d540c821c6a186410d9544320866aa81884395430c421b2a906210f10c831086caa5108432f5448421a629a4210da141210866ea890843545348421b82824210d9d51210874ea890843c75348421b329a4210d914d2108788a690843445348421f1a824210d914121087c0a0908436050484218fa9a8010c714d400874e85a0a61a442d0530d3a10829869108414c3508598261b041cc130c6214609865106304c26ea2a1061345150830c6a10641856540320c25ea4a08612c5250430caa08621856540310c2b2a7180611f544c030a6292601855145300c276a89806168524c030b828a601856d51300c336a898061cb524c030ac292601872149300c290a498061d3514c030ac28a601874145300c2a0a2980613651d0f209aa8e879066d0c30c826ca3a1c413551d0e20c7a1865104794e434826ca321a41355190d2097a9286904dd454348268a2a1a413b5050d208f2a0869065d0f414832887a0a41974310520ca21882906610f204836083902418c4388120d220c40904dd454308268a2a1841365110c209aa8886104b550320831a861904169500c8208fa9a82104714d410834a82108416950084209caa060106650c30082d2a418041c8320c020b4a9440104bd512008298a6900416451480209daa240105614d20082e0a2900416b5448020d5aa2401072d4d20082d4a690041685348020e429a40105214d20083c6a290041685148020f028a401058145200825ca5a1e212d52d0f108f29e85884754f42c43368618621ab42083109729687084b54b438423ca7a14211d53d0a10cba18630869d08218423ca721a212e5290d1096a9486884bd494344258a4a1a21375150d109da82868847950434431e87a12218c43d09108f29c84884754e424425ca5212211f53509108e29a84884dd454244276a0a12212e5410910c7a1884886310c42443308788221a842c4110ca21c20886910a104425ea4a18212c5250c109729086084b548430423ea6a10211c53508108f29884084754c420426aa81882195430c410b8a8062084d550210434a84108217150084109caa060086650c30042e2a218021d0310c0109caa040086a50820042e2a210021e021080109caa420085c546100426ea888021545344010b229220084ed5110042b0a688021685244010b9aa220086cd5110043a6a688021725344010b829a20087414d10042a0a688021e35244010b929220085c14910043c0a488021605244010
  | 1 => 0x96591da2f10c6a17c001bc000007d9b4001b80d0a4000002a05071222831783f98c5c81a14800708726e9ce391ac2d800170002c0aa1a8c6188d65a92c001060010a6da185d13647000479605a08a338542215a00028000c800194000d8231b0001ca38008558cc351e0409fa649867b9620a89e839ae001f42816c002008486e060900401c0f92e4c2042618a788005615e168204a8007495c790f2678003a074289082b13e001f05f87a000000000000000000840000000138688ec000244107e809b27a80c00216000a62e0d01e1d4659d6698e611198109fc4614e180465084e178da3a9c855030079880ba28828581010e089f813126898dc8213a2004a3b928001aa0f13c000be1c14600000842061f1905d8660288e1b1821922a63a2c0e00e268f07b1243e94a2e9a0598768721a2c802051be761525000445848468165b800510fc45000000003d000308ae7417a301a40b100770ca70000001702480000000778264c8f62094800000348002d1347980627150000680e836001f2610000c980000f8251c685112389cc21a20481227a2241599a7f94c37910878c40499c0380802080880816000202c080c0780400080d00000290001c0c09010000005390000000010000c000481402000006c0e290b8441007008200022010183c1b22060600000044020001068180e0000000010080c020a038040207018300a0e00054020600004060006e9cc8414cb2c6420a65b341d0132d820e80996cd04404cb608220265ab3210132cd19080995354e320ca3ea89906554514c832ac28264194bd51320cac8a29906568504c832a7aa2641963d51320cb8ea2990654c514c832e228a641951145320cb96a0990654c504c832e4282641952141320ca76a0a08653850504329ba8a80194d145400cb488598a638c428c531d5a168098ea10b404c7568420263a84210131d99888098e68c4404c676a0a1063385050831c6a106418d5544320c6aaa7188631f544c431a62926218d6141310c66ea89886364524c431b82826218d5d51310c72ea898863c7524c431aa2926218f1149310c688a498863d3504c431aa2826218f4141310c6a0a09
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x280159b978f890000000e00800f001e9b149c999d0a801e000e9508128d071a130a07898c961c05140c120b9010848b11968308801391001806069f000002191d8d858100039a9f801720a0188000000000018400000000009a080050b0090680080408540080020400100d0147504c832d0d44504c832d0144504c832a2181420c83194181510c831d014b504c431d0d48504c431d0148504c431a4983430c721a2983430ca21a2181430c82198181510c821a4181430c42198181520c421a1590320c421c1550320c4219198e5348421989825348421d014f5048421d0d4c5048421d014c5048421a1185420c83094185500c830a1189410c43092189500c430d014b514c030d0d48514c030d0148514c030a4987430c320a1987430ca20a1185430c82098185500c820a118d41084209218d5008420a4185430c02098185520c020a2590320c020c2550320c0209298e5348020989865348020d014f5148020d0d4c5148020d014c5148020a298b430c310a298f4208310a198b430c610a198f4208610a1189430c41098189500c410a118d42084109418d5008410a2189430c01098189510c010a4590310c010c4550310c010a218d42080109418d5108010a85902108010c855021080109498e53440109898a5344010d014f52440109498e52440109898a5244010d0d4c5244010d014c5244010
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 24
  | 4 => 302
  | 3 => 279
  | 2 => 66
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (i*4) 4
  | 5 => packedAt s0K5 (i*15) 15
  | 4 => packedAt s0K4 (i*26) 26
  | 3 => packedAt s0K3 (i*37) 37
  | 2 => packedAt s0K2 (i*48) 48
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (5+((h/1+packedAt s0K6 (4+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s0K5 (400+((h/8+packedAt s0K5 (360+(h % 8)*5) 5) % 29)*6) 6
  | 4 => packedAt s0K4 (8752+((h/100+packedAt s0K4 (7852+(h % 100)*9) 9) % 363)*10) 10
  | 3 => packedAt s0K3 (11160+((h/93+packedAt s0K3 (10323+(h % 93)*9) 9) % 335)*10) 10
  | 2 => packedAt s0K2 (3322+((h/22+packedAt s0K2 (3168+(h % 22)*7) 7) % 88)*8) 8
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffdfc3ffff1ff1ff
  | 2 => 0xffffffffffffffffffffffffeffc3fffe3fe3f
  | 3 => 0xfffffffffffffffffffffffff7ffc3fffc7fc7
  | 4 => 0x7bfffc3fff8ff8
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffa078888b0490db
  | 2 => 0xffffffffffffffffffffffff908b911521262d
  | 3 => 0x9113a26484b46
  | 4 => 0x62223b8920db0
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 30 s0Pos s0Neg, 0xfcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_12887
namespace PEqualNP.Outside.L_meta_12887
open PEqualNP.Outside.L_meta_12887.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x1191ea95914e00b00520071c44243282014da446812843e00c0016546800000d0000500002e0000c000cf0000040000074000000132c001c5001000013424810085062c000000c380002c181ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fb40fe40be40fd40fc40bc40f840b840ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x7d2d3c008d5c34789db459988001913121c445d04180b0b570fc006d4c01016895b0f0617ca40c01bd28cc01c80001cce0c1ada58c386471a0b93524018800997400000000014800684c5d84015448dc0431d96cc4d81ca16539c158291cf818c8f4000104e5796114ec0020840015405511a890d001b8ac01d51800bd0c2cd544e800a8243d9408755089099c501000161a0e000820040a0826020a180c04020804001004040402002c2c00080e00344a0404341a097a5090ef2a121dbd4943b629287775150ee8a2a1ded4143bc282877a5090af2a12157d4d42ae29a85775150ae8a2a15ed4142bc282857651ccaeaa3995d94632baa8c65cd320caf4a120de54241afa9a835c53506dea4a0db14941bda82837850506dca598db54b31b7294636d528c7aa6218d794f21aea9e435e53886baa710f948421bd284813e5090274a1206e500409f28081ba50102f4a8206e95040dda1881ba431037286206e10c40dda1081ba421037284206e10840dda0881ba411037282206e10440dda9881ba5310372a6206e14c40dda9081ba5210372a4206e14840dd99081ba321037264206e0c840dda8881ba5110372a2206e14440dd98881ba311037262206e0c440dd90881ba211037242206e084409f2a6613d54cc37081986e102309faa2613c544c2dea4985b14930bba8a6174514c37080986e100309f2a6413d54c837081906e102209faa2413c54482bea6905714d20bba8a4174514837080906e100209f2a6213d54c437081886e102109faa2213c54442bea6885714d10b7a92216c524437080886e10010
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x3776000000001fa34e0003e000151900018007401e05182c01d00b4fa11044c15668878d00e000026000001cbc00240414125801900141db0048002003c6933d005d8831200b2500a40000005c9438d003536ad700000030002003880204000040c3000100000000210005aad8943102a86250c40acd8543102b06150c40a6d8d42102986350840acd8542102b06150840a6d8d41102986350440aad8941102a86250440aad8953102a86254c40acd8553102b06154c40aa98853102a96214c40ac98453102b16114c40a6d8d52102986354840acd8552102b06154840a698c52102996314840ac98452102b16114840ac98732102b161cc840ac98632102b1618c840e24c8321029b6354440a618d51102ab6254440aa189511029a6314440a658c51102aa6214440aa58851102aa62cc440aa58b31102aa628c440aa58a3110391310c440a698f211029963c8440a698e21102996388440e8484211032b5210130ca148404c3335110130cc144404c31b5310120c614c40483335110120cc14440482386015110c6d4c40443185310110cad4840443285210110
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 45
  | 4 => 119
  | 3 => 64
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s1K6 (i*5) 5
  | 5 => packedAt s1K5 (i*16) 16
  | 4 => packedAt s1K4 (i*27) 27
  | 3 => packedAt s1K3 (i*38) 38
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s1K6 (6+((h/1+packedAt s1K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s1K5 (825+((h/15+packedAt s1K5 (720+(h % 15)*7) 7) % 72)*7) 7
  | 4 => packedAt s1K4 (3525+((h/39+packedAt s1K4 (3213+(h % 39)*8) 8) % 143)*8) 8
  | 3 => packedAt s1K3 (2579+((h/21+packedAt s1K3 (2432+(h % 21)*7) 7) % 101)*7) 7
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x1ffffffffffffe03f03ffffffffffe001ffff8
  | 2 => 0xe01fe03fc07fffffffc0fc07e03fffffe631ff
  | 3 => 0xffe0003fff80ffffffff0007ffc07ffff83e3f
  | 4 => 0xffffffc00000fffffffffff800007fffffc03f
  | 5 => 0xffffffffffff0003ffffffffffff8000ffffc0
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x82a2a186450a0238700b2c69634696340ad6f8
  | 2 => 0xba88ca9293146449b2c05522a9372ad566315b
  | 3 => 0xc8da95250a26a892d5550244db924d66b83a2d
  | 4 => 0x131306362c58d12369a69b70122471b8df4036
  | 5 => 0x1c1c18383060e1c38e38e3871c3801c0f5ad80
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaaaaa0f0000000faaaaaa0f0000000faaaaaa0f0000000faaaaaa0f0000000faaaaaa0f0000000faaaaaa0f0000000faaaaaa0f0000000faaaaaa0f0000000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_12887
namespace PEqualNP.Outside.L_meta_12887
open PEqualNP.Outside.L_meta_12887.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x10010e002ea08003e90d191858f061e50518002090b568c38e0aa81a23655080000000000080291a9401300b04a63a0139100800080016805c62450024470cbff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fb40fe40be40fd40fc40bc40f840b840ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x151d0edac000005144840347c0000c5b000000169c8f000000001a90cb80121349408c80001d8186400d1818964391ca918d400000000fd304ccdbc2c00001000dc700000000000000110e13c0061719579d4d9a05800000000000000000001b800ac01755c016c747801a40000001c000000019c9d0108b0000000008d2990000000014800217ca4a1980001c40000f468e80084b481c1845561b401cd44980c003d8d4ce490bd54f830885000280000000000000000c0006c00012d0539240000145c4400015800014000240a2204000400000602001e00041c00080200000400040208000a0a000208080c020410000600017a5090ef2a121dbd4943b629287775150ee8a2a1ded4143bc282877a5090af2a12157d4d42ae29a85775150ae8a2a15ed4142bc282857651ccaeaa3995d94632baa8c65cd320caf4a120de54241afa9a835c53506dea4a0db14941bda82837850506dca598db54b31b7294636d528c7aa6218d794f21aea9e435e53886baa710f948421bd284813e5090274a1206e500409f28081ba50102f4a8206e95040dda1881ba431037286206e10c40dda1081ba421037284206e10840dda0881ba411037282206e10440dda9881ba5310372a6206e14c40dda9081ba5210372a4206e14840dd99081ba321037264206e0c840dda8881ba5110372a2206e14440dd98881ba311037262206e0c440dd90881ba211037242206e084409f2a6613d54cc37081986e102309faa2613c544c2dea4985b14930bba8a6174514c37080986e100309f2a6413d54c837081906e102209faa2413c54482bea6905714d20bba8a4174514837080906e100209f2a6213d54c437081886e102109faa2213c54442bea6885714d10b7a92216c524437080886e10010
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x72a5a300e2151900b80a17a9002f469d30e44615802cedb1374fc0310051bbc004049734b4780000001b4075a8a0001c120cf800216006953c140000000000007142c66108a518c8f830d186c907040c984100400f00010020024000aad8943102a86250c40acd8543102b06150c40a6d8d42102986350840acd8542102b06150840a6d8d41102986350440aad8941102a86250440aad8953102a86254c40acd8553102b06154c40aa98853102a96214c40ac98453102b16114c40a6d8d52102986354840acd8552102b06154840a698c52102996314840ac98452102b16114840ac98732102b161cc840ac98632102b1618c840e24c8321029b6354440a618d51102ab6254440aa189511029a6314440a658c51102aa6214440aa58851102aa62cc440aa58b31102aa628c440aa58a3110391310c440a698f211029963c8440a698e21102996388440e8484211032b5210130ca148404c3335110130cc144404c31b5310120c614c40483335110120cc14440482386015110c6d4c40443185310110cad4840443285210110
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 45
  | 4 => 119
  | 3 => 64
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (i*5) 5
  | 5 => packedAt s2K5 (i*16) 16
  | 4 => packedAt s2K4 (i*27) 27
  | 3 => packedAt s2K3 (i*38) 38
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (6+((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s2K5 (810+((h/15+packedAt s2K5 (720+(h % 15)*6) 6) % 60)*7) 7
  | 4 => packedAt s2K4 (3525+((h/39+packedAt s2K4 (3213+(h % 39)*8) 8) % 207)*8) 8
  | 3 => packedAt s2K3 (2579+((h/21+packedAt s2K3 (2432+(h % 21)*7) 7) % 84)*7) 7
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x1ffffffffffffe03f03ffffffffffe001ffff8
  | 1 => 0xe01fe03fc07fffffffc0fc07e03fffffe631ff
  | 3 => 0xffe0003fff80ffffffff0007ffc07ffff83e3f
  | 4 => 0xffffffc00000fffffffffff800007fffffc03f
  | 5 => 0xffffffffffff0003ffffffffffff8000ffffc0
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x82a2a186450a0238700b2c69634696340ad6f8
  | 1 => 0xba88ca9293146449b2c05522a9372ad566315b
  | 3 => 0xc8da95250a26a892d5550244db924d66b83a2d
  | 4 => 0x131306362c58d12369a69b70122471b8df4036
  | 5 => 0x1c1c18383060e1c38e38e3871c3801c0f5ad80
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaaa88cc000000eeaaaa88cc000000eeaaaa88cc000000eeaaaa88cc000000eeaaaa88cc000000eeaaaa88cc000000eeaaaa88cc000000eeaaaa88cc000000, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_12887
namespace PEqualNP.Outside.L_meta_12887
open PEqualNP.Outside.L_meta_12887.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x1414614a5182c223066492a5620d80000141600702a40438017444c0070c2538d3a44020000401500840000098f803c00d005840782102180141007000700041ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fb40fe40be40fd40fc40bc40f840b840ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x13c00dc982c9c00c9200000cc840001a10539c80141013414e40001580000d80000000001d4000001304c0000547c01240000680001d0000000f40000e9a49000d41808e0017c00018c002001c03c957470a19d4585d9140025940000000000ec5c00643400583001c46c2800b801708d9800000088010c00004841ac01bd8011a800a9506050c11c7800b00000018800800074fd7838ad28000000000001cdb4040000000108014c0000000000d00cc444f00001199000b55c00000001481d68f910bc0164a56c000001b954012c0001b00000000000000000000000000000016000000600020208020600000200020600060010040004020a02040000060006020608041402020200017a5090ef2a121dbd4943b629287775150ee8a2a1ded4143bc282877a5090af2a12157d4d42ae29a85775150ae8a2a15ed4142bc282857651ccaeaa3995d94632baa8c65cd320caf4a120de54241afa9a835c53506dea4a0db14941bda82837850506dca598db54b31b7294636d528c7aa6218d794f21aea9e435e53886baa710f948421bd284813e5090274a1206e500409f28081ba50102f4a8206e95040dda1881ba431037286206e10c40dda1081ba421037284206e10840dda0881ba411037282206e10440dda9881ba5310372a6206e14c40dda9081ba5210372a4206e14840dd99081ba321037264206e0c840dda8881ba5110372a2206e14440dd98881ba311037262206e0c440dd90881ba211037242206e084409f2a6613d54cc37081986e102309faa2613c544c2dea4985b14930bba8a6174514c37080986e100309f2a6413d54c837081906e102209faa2413c54482bea6905714d20bba8a4174514837080906e100209f2a6213d54c437081886e102109faa2213c54442bea6885714d10b7a92216c524437080886e10010
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x3540d82327eb000022a8d802e011be00000004e51cbb1e2800034bd49d00a06b8301d83156540032c7130e74786085ccc1131289e0000400867adcca16894f8b48b429207001878200081030c04400063811e1824980aad8943102a86250c40acd8543102b06150c40a6d8d42102986350840acd8542102b06150840a6d8d41102986350440aad8941102a86250440aad8953102a86254c40acd8553102b06154c40aa98853102a96214c40ac98453102b16114c40a6d8d52102986354840acd8552102b06154840a698c52102996314840ac98452102b16114840ac98732102b161cc840ac98632102b1618c840e24c8321029b6354440a618d51102ab6254440aa189511029a6314440a658c51102aa6214440aa58851102aa62cc440aa58b31102aa628c440aa58a3110391310c440a698f211029963c8440a698e21102996388440e8484211032b5210130ca148404c3335110130cc144404c31b5310120c614c40483335110120cc14440482386015110c6d4c40443185310110cad4840443285210110
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 45
  | 4 => 119
  | 3 => 64
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (i*5) 5
  | 5 => packedAt s3K5 (i*16) 16
  | 4 => packedAt s3K4 (i*27) 27
  | 3 => packedAt s3K3 (i*38) 38
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (6+((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s3K5 (810+((h/15+packedAt s3K5 (720+(h % 15)*6) 6) % 60)*7) 7
  | 4 => packedAt s3K4 (3525+((h/39+packedAt s3K4 (3213+(h % 39)*8) 8) % 227)*8) 8
  | 3 => packedAt s3K3 (2579+((h/21+packedAt s3K3 (2432+(h % 21)*7) 7) % 77)*7) 7
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x1ffffffffffffe03f03ffffffffffe001ffff8
  | 1 => 0xe01fe03fc07fffffffc0fc07e03fffffe631ff
  | 2 => 0xffe0003fff80ffffffff0007ffc07ffff83e3f
  | 4 => 0xffffffc00000fffffffffff800007fffffc03f
  | 5 => 0xffffffffffff0003ffffffffffff8000ffffc0
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x82a2a186450a0238700b2c69634696340ad6f8
  | 1 => 0xba88ca9293146449b2c05522a9372ad566315b
  | 2 => 0xc8da95250a26a892d5550244db924d66b83a2d
  | 4 => 0x131306362c58d12369a69b70122471b8df4036
  | 5 => 0x1c1c18383060e1c38e38e3871c3801c0f5ad80
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeaeaa8a8c0c00000eaeaa8a8c0c00000eaeaa8a8c0c00000eaeaa8a8c0c00000eaeaa8a8c0c00000eaeaa8a8c0c00000eaeaa8a8c0c00000eaeaa8a8c0c00000, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_12887
namespace PEqualNP.Outside.L_meta_12887
open PEqualNP.Outside.L_meta_12887.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x220000a8e360000012a051d00a539000b042442010000000b000034a0c008cc870200ba600082a5387c01a001002a000019816000002600f06243c00022ac10105081810304000000204100ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fb40fe40be40fd40fc40bc40f840b840ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x6141b8804000011d29d598380001c0352c24784c009d4400f0bc01083d0c01147c00013dd0d4b4ac000000e54c0000518148007000881400017cf5cd90000001bc000008c8011001644994208400000028f934d1a1ad19b4300000e00000000000012000010000980151d80001c4640001053000c0008c0000001d6db00000b00000fcdc00a8ec7401a4000154440174118854699cd8c4cc0000001859396000940000012578a1716959c89184a46ce95c0c002c045c0000b801a8018c040008081200060e0404060018000604000000000a0c02060208020406000000000000080000037a5090ef2a121dbd4943b629287775150ee8a2a1ded4143bc282877a5090af2a12157d4d42ae29a85775150ae8a2a15ed4142bc282857651ccaeaa3995d94632baa8c65cd320caf4a120de54241afa9a835c53506dea4a0db14941bda82837850506dca598db54b31b7294636d528c7aa6218d794f21aea9e435e53886baa710f948421bd284813e5090274a1206e500409f28081ba50102f4a8206e95040dda1881ba431037286206e10c40dda1081ba421037284206e10840dda0881ba411037282206e10440dda9881ba5310372a6206e14c40dda9081ba5210372a4206e14840dd99081ba321037264206e0c840dda8881ba5110372a2206e14440dd98881ba311037262206e0c440dd90881ba211037242206e084409f2a6613d54cc37081986e102309faa2613c544c2dea4985b14930bba8a6174514c37080986e100309f2a6413d54c837081906e102209faa2413c54482bea6905714d20bba8a4174514837080906e100209f2a6213d54c437081886e102109faa2213c54442bea6885714d10b7a92216c524437080886e10010
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x7cf4d87220d686580898032c1aa148310151aa979f4c000012001398345c03f000118064edc806e2003300f05003aa403a002c0005639c124a1000f3cc400050d1b22121401600717140a0064181040841a00002100e1c100060448baad8943102a86250c40acd8543102b06150c40a6d8d42102986350840acd8542102b06150840a6d8d41102986350440aad8941102a86250440aad8953102a86254c40acd8553102b06154c40aa98853102a96214c40ac98453102b16114c40a6d8d52102986354840acd8552102b06154840a698c52102996314840ac98452102b16114840ac98732102b161cc840ac98632102b1618c840e24c8321029b6354440a618d51102ab6254440aa189511029a6314440a658c51102aa6214440aa58851102aa62cc440aa58b31102aa628c440aa58a3110391310c440a698f211029963c8440a698e21102996388440e8484211032b5210130ca148404c3335110130cc144404c31b5310120c614c40483335110120cc14440482386015110c6d4c40443185310110cad4840443285210110
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 45
  | 4 => 119
  | 3 => 64
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
  | 5 => packedAt s4K5 (825+((h/15+packedAt s4K5 (720+(h % 15)*7) 7) % 72)*7) 7
  | 4 => packedAt s4K4 (3525+((h/39+packedAt s4K4 (3213+(h % 39)*8) 8) % 189)*8) 8
  | 3 => packedAt s4K3 (2579+((h/21+packedAt s4K3 (2432+(h % 21)*7) 7) % 84)*7) 7
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x1ffffffffffffe03f03ffffffffffe001ffff8
  | 1 => 0xe01fe03fc07fffffffc0fc07e03fffffe631ff
  | 2 => 0xffe0003fff80ffffffff0007ffc07ffff83e3f
  | 3 => 0xffffffc00000fffffffffff800007fffffc03f
  | 5 => 0xffffffffffff0003ffffffffffff8000ffffc0
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x82a2a186450a0238700b2c69634696340ad6f8
  | 1 => 0xba88ca9293146449b2c05522a9372ad566315b
  | 2 => 0xc8da95250a26a892d5550244db924d66b83a2d
  | 3 => 0x131306362c58d12369a69b70122471b8df4036
  | 5 => 0x1c1c18383060e1c38e38e3871c3801c0f5ad80
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeaa8eaa8c000c000eaa8eaa8c000c000eaa8eaa8c000c000eaa8eaa8c000c000eaa8eaa8c000c000eaa8eaa8c000c000eaa8eaa8c000c000eaa8eaa8c000c000, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_12887
namespace PEqualNP.Outside.L_meta_12887
open PEqualNP.Outside.L_meta_12887.Model
def s5K6 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x12880524780700310a982ac1289860000a058e6ae0080048000c2bfe65f8cbe997c32fe63f8c7e98fc31fe43f887e90fc21fe61f8c3e987c30fe41f883e907c20fe21f843e887c10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xa070e00804100483c4c040b030140102874000d0283400060003c0002090142c000204404330e8041a13be41ccaf50732be40ccaf50332bd438caf90a32df328cbbcca32be418caf50632be408caf50232ef324cb78c932bf414cbdd0532b7414caf10532f4414cad10532bf404cbed0132bb404caf10132f8404cae10132be430caf90832df320cbb8c832dd320cbb4c832cd320caf90432bd410caf90032bd400caf90b31bd42cc6f90331bd40cc6f50e31be428c6f50a31de328c770ca31be418c77cc631f7318c6f90231bd408c6fd0931ef424c6bd0931bc424c7b10931ac424c7dcc531de314c6fd0131fb404c6ed0131bc404c7e10131b8404c6f90c31be420c6f50831de320c770c831be410c77cc431f6310c774c431f5310c754c431be400c6f50031bf43c86f90f21bd43c86f10f21f731c87d0c721be40c86f50321bf43886f90e21bd43886f10e21bd42887bcca21ec32886f90621ef21887dc8621be40886f50221bf434877d0d219f43486f90d21bd43486f10d21dc43486710d21f721487b88521bf40487ed0121bb40486f10121f840486e10121bf43086f90c21bd43086f10c21be42087bcc821ec32086f90421f731087d0c421ef21087d88421ed21087d48421e521086f90021bd40086f90b30bd42cc2f90730bd41cc2f50e30be428c2f50a30de328c370ca30be418c2f50630de318c370c630be408c37cc230fb308c2fd0930ef424c2bd0930bc424c3b10930ac424c2fd0530f7414c2dd0530bc414c3d10530b4414c3ecc130de304c2f90c30be420c2f50830de320c370c830be410c2f50430de310c370c430be400c37cc030fa300c374c030f9300c364c030bf43c82f90f20bd43c82f10f20be41c82f50720fb30c83e0c320bf43882f90e20bd43882f10e20bd42883bcca20ec32882f90620bd41883b88620ec21882f90220ef20883ec8220bf434837d0d209f43482f90d20bd43482f10d20dc43482710d20bf41483dd0520b741482f10520f441482d10520fb20483b88120bf43082f90c20bd43082f10c20be42083bcc820ec32082f90420bd41083b88420ec21082f90020fb30083e0c020ef20083e88020ed20083e48020e920082fd0f10be43c42f50f10bc43c42fd0b10be42c42f50b10bc42c43ecc310f830c43ec8310f820c42fd0e10be43842f50e10bc43842fd0a10be42842f50a10bc42842f50610f731843d0c610f721843d08610be40843dc4210fb10842fd0d10df434427d0d10be43442f50d10bc43443710d109c43442fd0910ef42442bd0910be42442f50910bc42443b10910ac42443ec4110f610442fd0c10be43042f50c10bc43042fd0810be42042f50810bc42042f90410f731043d0c410f721043d08410be40043ecc010f830043ec8010f820043dc4010fa10043d44010f910043c44010
  | 1 => 0x1723e1e8001928d9ba000f44a23c240744892e3488631a16730b06005a6e04e9382c58800420f02fa086115a00000001966880063800070c48f80c7ba388a82a468008998a00000849f064000198005c00000060000001900006a1a15000750b65b1b015968230a2759d06aa400021c7c86a000e63ea0e0b97a4394c9484a4086c4d000350ec1fa303814e0c8aa6d1423a93e4483a779c4828dc000300000076a06001a6928b4001440f000760002009a808d84e80000000001fa718001780086156771a800042009600019400072959ce000140d0ac831ea7d9c21192a6ba46001e6048280025a3a15e0000000138001764d9c000250028e42b8767924c0603e95174188ee78222680920013c2f07c599f8608705200e4911e148445f9003416a23a48091e2570fc6791822800121bc001d2260de001ac2e8fe00210001ec000584323425130000008e9547d0062081e561887f8006f98c4b1b27f06e519c835838670b821016850cc879a42a1ca8b114428782c8da080688a000170000009e0004c541101e8a445836498a65f140002420019a548885e0ca040e248106320c20216e528a06d8f633a24141048811c81040800f22589c59232099864c8c09624408a2e660040d80c0609058201608030100c0b028380403018100a040405c0a11000100602000080000028100a0f0401400000081006030402c22000b824000c0180002010201416000000c
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x88632f5250031962928018ce94343c8672a1a1e4397430c7219d2868710ce543438871e86194431e5390d219d2848690ce542434865ea4a1a43375150d219da828690ce141434863ca821a439443c8521c621c4290e6d0f404873087a02439b4310121cc2188090ecc84404875442202433b5050c219c2828610ce9404308672a0218432d540c821c6a186410d9544320866aa81884395430c421b2a906210f10c831086caa5108432f5448421a629a4210da141210866ea890843545348421b82824210d9d51210874ea890843c75348421b329a4210d914d2108788a690843445348421f1a824210d914121087c0a0908436050484218fa9a8010c714d400874e85a0a61a442d0530d3a10829869108414c3508598261b041cc130c6214609865106304c26ea2a1061345150830c6a10641856540320c25ea4a08612c5250430caa08621856540310c2b2a7180611f544c030a6292601855145300c276a89806168524c030b828a601856d51300c336a898061cb524c030ac292601872149300c290a498061d3514c030ac28a601874145300c2a0a2980613651d0f209aa8e879066d0c30c826ca3a1c413551d0e20c7a1865104794e434826ca321a41355190d2097a9286904dd454348268a2a1a413b5050d208f2a0869065d0f414832887a0a41974310520ca21882906610f204836083902418c4388120d220c40904dd454308268a2a1841365110c209aa8886104b550320831a861904169500c8208fa9a82104714d410834a82108416950084209caa060106650c30082d2a418041c8320c020b4a9440104bd512008298a6900416451480209daa240105614d20082e0a2900416b5448020d5aa2401072d4d20082d4a690041685348020e429a40105214d20083c6a290041685148020f028a401058145200825ca5a1e212d52d0f108f29e85884754f42c43368618621ab42083109729687084b54b438423ca7a14211d53d0a10cba18630869d08218423ca721a212e5290d1096a9486884bd494344258a4a1a21375150d109da82868847950434431e87a12218c43d09108f29c84884754e424425ca5212211f53509108e29a84884dd454244276a0a12212e5410910c7a1884886310c42443308788221a842c4110ca21c20886910a104425ea4a18212c5250c109729086084b548430423ea6a10211c53508108f29884084754c420426aa81882195430c410b8a8062084d550210434a84108217150084109caa060086650c30042e2a218021d0310c0109caa040086a50820042e2a210021e021080109caa420085c546100426ea888021545344010b229220084ed5110042b0a688021685244010b9aa220086cd5110043a6a688021725344010b829a20087414d10042a0a688021e35244010b929220085c14910043c0a488021605244010
  | 1 => 0x96591da2f10c6a17c001bc000007d9b4001b80d0a4000002a05071222831783f98c5c81a14800708726e9ce391ac2d800170002c0aa1a8c6188d65a92c001060010a6da185d13647000479605a08a338542215a00028000c800194000d8231b0001ca38008558cc351e0409fa649867b9620a89e839ae001f42816c002008486e060900401c0f92e4c2042618a788005615e168204a8007495c790f2678003a074289082b13e001f05f87a000000000000000000840000000138688ec000244107e809b27a80c00216000a62e0d01e1d4659d6698e611198109fc4614e180465084e178da3a9c855030079880ba28828581010e089f813126898dc8213a2004a3b928001aa0f13c000be1c14600000842061f1905d8660288e1b1821922a63a2c0e00e268f07b1243e94a2e9a0598768721a2c802051be761525000445848468165b800510fc45000000003d000308ae7417a301a40b100770ca70000001702480000000778264c8f62094800000348002d1347980627150000680e836001f2610000c980000f8251c685112389cc21a20481227a2241599a7f94c37910878c40499c0380802080880816000202c080c0780400080d00000290001c0c09010000005390000000010000c000481402000006c0e290b8441007008200022010183c1b22060600000044020001068180e0000000010080c020a038040207018300a0e00054020600004060006e9cc8414cb2c6420a65b341d0132d820e80996cd04404cb608220265ab3210132cd19080995354e320ca3ea89906554514c832ac28264194bd51320cac8a29906568504c832a7aa2641963d51320cb8ea2990654c514c832e228a641951145320cb96a0990654c504c832e4282641952141320ca76a0a08653850504329ba8a80194d145400cb488598a638c428c531d5a168098ea10b404c7568420263a84210131d99888098e68c4404c676a0a1063385050831c6a106418d5544320c6aaa7188631f544c431a62926218d6141310c66ea89886364524c431b82826218d5d51310c72ea898863c7524c431aa2926218f1149310c688a498863d3504c431aa2826218f4141310c6a0a09
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x280159b978f890000000e00800f001e9b149c999d0a801e000e9508128d071a130a07898c961c05140c120b9010848b11968308801391001806069f000002191d8d858100039a9f801720a0188000000000018400000000009a080050b0090680080408540080020400100d0147504c832d0d44504c832d0144504c832a2181420c83194181510c831d014b504c431d0d48504c431d0148504c431a4983430c721a2983430ca21a2181430c82198181510c821a4181430c42198181520c421a1590320c421c1550320c4219198e5348421989825348421d014f5048421d0d4c5048421d014c5048421a1185420c83094185500c830a1189410c43092189500c430d014b514c030d0d48514c030d0148514c030a4987430c320a1987430ca20a1185430c82098185500c820a118d41084209218d5008420a4185430c02098185520c020a2590320c020c2550320c0209298e5348020989865348020d014f5148020d0d4c5148020d014c5148020a298b430c310a298f4208310a198b430c610a198f4208610a1189430c41098189500c410a118d42084109418d5008410a2189430c01098189510c010a4590310c010c4550310c010a218d42080109418d5108010a85902108010c855021080109498e53440109898a5344010d014f52440109498e52440109898a5244010d0d4c5244010d014c5244010
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 24
  | 4 => 302
  | 3 => 279
  | 2 => 66
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (i*4) 4
  | 5 => packedAt s5K5 (i*15) 15
  | 4 => packedAt s5K4 (i*26) 26
  | 3 => packedAt s5K3 (i*37) 37
  | 2 => packedAt s5K2 (i*48) 48
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (5+((h/1+packedAt s5K6 (4+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s5K5 (400+((h/8+packedAt s5K5 (360+(h % 8)*5) 5) % 29)*6) 6
  | 4 => packedAt s5K4 (8752+((h/100+packedAt s5K4 (7852+(h % 100)*9) 9) % 363)*10) 10
  | 3 => packedAt s5K3 (11160+((h/93+packedAt s5K3 (10323+(h % 93)*9) 9) % 335)*10) 10
  | 2 => packedAt s5K2 (3322+((h/22+packedAt s5K2 (3168+(h % 22)*7) 7) % 88)*8) 8
  | _ => 0
def s5Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffdfc3ffff1ff1ff
  | 2 => 0xffffffffffffffffffffffffeffc3fffe3fe3f
  | 3 => 0xfffffffffffffffffffffffff7ffc3fffc7fc7
  | 4 => 0x7bfffc3fff8ff8
  | _ => 0
def s5Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffa078888b0490db
  | 2 => 0xffffffffffffffffffffffff908b911521262d
  | 3 => 0x9113a26484b46
  | 4 => 0x62223b8920db0
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 30 s5Pos s5Neg, 0xfcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_12887
namespace PEqualNP.Outside.L_meta_12887
open PEqualNP.Outside.L_meta_12887.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xf080005c4c2cdc00ec00a054acb0004424c40488fca4f894f4e0009000e8580000cc5084300000003408007c0000982000007400143800b428a8009c8c00d01c000078c87068e4c0b8481900bc0c60646cd4d840103c48000000868b0000085000c1a00c0020252000dff5402ff95001fd5402ff1500dff53027f94c01fd53027f14c0bff43027f90c01fd43027f10c0dff5201ff94801fd5201ff1480bff4201ff90801fd4201ff10809ff3201ff8c801fd3201ff0c80dff51017f94401fd51017f1440bff41017f90401fd41017f10409ff31017f8c401fd31017f0c407ff21017f88401fd21017f0840dff50037ed4003fe5000df94001fd5000ff140037c50037e14001785002ffd0003fe40007f50003fc40027fcc003fe30007f4c003fc3001ffc8003fe20007f48003fc20017fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x826001ff8c13000fbc6098007fc304c003ee1826001fe0c13000ffe4098007fe204c003fe1026001ffc413000ffc2098007fc104c001ffb2a4000bfd9520006feca900027f6548017ff32a4006bf99520007faca90002fd6548017fe32a4006bf19520006f8ca9001a7c6548001ffb224000bfd9120077fcc890016fe6448001feb224000bf59120077f8c890016fc6448017ffaa2400eff95120007faa89003bfc5448001ffb1a4000bfd8d2006ffcc690012fe6348001feb1a4000bf58d2006ff8c690012fc6348017ffa9a400dff94d20007faa690037fc534801dffa1a400dff90d20007fa8690037fc43480037fb124003ffd492001ffca49000ffd5248007fe2924003ffd092001ffc849000ffd4248007fe2124003ffcc92001ffc649000ffd3248007fe1924000ffd8520005fec290033fe61480057f30a4000ff58520067f8c29000afc6148017ffa8a400cff94520007faa290033fc514801dffa0a400cff90520007fa8290033fc414801bff98a400cff8c520007fa6290033fc3148007ff90a4003ff8852001ffa429000ffc21480037fb024001ffd412005ff6a090007fe5048003bf2824001ff5412000ff8a0900077c5048003fc2824001de1412000ffe8090007fe4048003fea024001ff1012000ffe6090007fe3048003fe9824001ff0c12000ffe409000ffb2048003ff1024001fb8812000ff84090007ec2048003fc1024001ffc412000ffc2090007fc1048001ffb2a2000bfd9510006feca880027f654400fff32a2006bf99510007faca88002fd654400ffe32a2006bf19510006f8ca8801a7c6544001ffb222000bfd9110057fcc888016fe6444001feb222000bf59110057f8c888016fc644400fffaa2200aff95110007faa88802bfc5444001ffb1a2000bfd8d1004ffcc688012fe6344001feb1a2000bf58d1004ff8c688012fc634400fffa9a2009ff94d10007faa688027fc5344015ffa1a2009ff90d10007fa8688027fc4344001ffb122000bfd8910047fcc48800efe6244001feb122000bf58910047f8c48800efc624400fffa922008ff94910007faa488023fc5244015ffa122008ff90910007fa8488023fc4244013ff9922008ff8c910007fa6488023fc32440037fb0a2002ffd4510017fca28800bfd5144005fe28a2002ffd0510017fc828800bfd4144005fe20a2002ffcc510017fc628800bfd3144005fe18a2002ffc8510017fc428800bfd2144005fe10a2001bfd811000ffea08801ffb5044003ff2822001df9411000ffaa088007fc5044003be2822001fe1411000ef0a088007ff4044003ff2022001ff5011000ff88088007ff3044003ff1822001ff4c11000ff86088007ff2044003ff1022001ff4811000ff84088007ff1044005fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x77a4314001bca18a019de10c5000ef6c4280077a6214003bcb10a001de188500d6f684280637a4214001bca10a018de108500cef664280637a3214001bc990a018de0c85000ef6c2280077a6114003bcb08a001de184500d6f6822805f7a4114001bca08a017de104500cef6622805f7a3114001bc988a017de0c4500c6f6422805f7a2114001bc908a017de08450007fecaa0002ff6550001bfb2a80009fd954009ffccaa001afe6550001feb2a8000bf5954009ff8caa001afc6550001be32a80069f1954000dfec8a0017ff545000bff2a28005ff5514002ff8a8a0003ff63500017fb1a8016ff98d40025fcc6a0003fd635002dfe31a8004bf18d4009ffea6a005bfe5350001fea9a8016ff14d4002ffe86a0017fe435000bfea1a8005ff10d40007fec4a0002ff625002bff3128003bf98940007fac4a0057fc62500077e3128013ffd49400affca4a0003fd525002bfe2928005ffd094002ffc84a0017fd425000bfe2128016ffcc9400affc64a0003fd325002bfe1928000ffd8540005fec2a0053fe61500057f30a8000ff585400a7f8c2a000afc6150027ffa8a8014ff94540007faa2a0053fc515000bffa0a8005ff9054002ffa82a0017fc415002dff98a8014ff8c540007fa62a0053fc315002bff90a8014ff88540007fa42a0053fc21500037fb028001ffd414009ff6a0a0007fe5050003bf2828001ff5414000ff8a0a00077c5050003fc2828001de1414000ffe80a0017fb4050003ff2028001ef9014000ff880a0007bc4050003fc2028001ffcc14000ffc60a0007fc3050003ff9028001ff8814000ff840a0007ff1050003ff0828001ff04140007feca98002ff654c001bfb2a60009fd953007ffcca9801afe654c001feb2a6000bf5953007ff8ca9801afc654c001be32a60069f19530007fec898002ff644c025ff3226005bf99130007fac898002fd644c025fe3226005bf1913007ffea89804bfe544c001feaa26012ff1513000dfec698013ff534c009ff29a6004ff54d30027f8a698013ff434c009ff21a6004ff50d30027f88698003ff624c0017fb126011ff9893001dfcc498003fd624c023fe3126003bf1893007ffea498047fe524c001fea926011ff14930097fe8498047fe424c001fea126011ff10930027fe6498013fe324c009fe9926004ff0c930007fec298002ff614c021ff30a6002bf98530007fac298043fc614c0057e30a600fffd4530087fca298003fd514c021fe28a6012ffd0530087fc8298003fd414c021fe20a6004ffcc530027fc6298013fd314c009fe18a6011ffc8530087fc4298003fd214c021fe10a6001bfd813000ffea09803ffb504c003ff2826001df9413000ffaa098007fc504c003be2826001fe1413000ef0a098007ff404c003ff2026001ff5013000ff88098007ff304c009fd9
  | 2 => 0x3111ffcc098806fe604c401feb026223ff1813100df8c09889bff504c44dfda826223ff9413111efca09888ffc504c447be2826226fe1413112ffe809888ffe404c447fe2026204ffcc131027fc6098813fc304c449ff9026223ff8813111ff8409880bff104c405ff0826202ff04131007feca90802ff6548445ff32a4206bf99521007faca90802fd6548445fe32a4206bf19521007fec890802ff6448443ff3224205bf99121007fac890802fd6448443fe3224205bf19121117fea890887fe5448401feaa24221ff15121007fec690802ff6348441ff31a4204bf98d21007fac690802fd6348441fe31a4204bf18d21117fea690883fe5348401fea9a4220ff14d2110ffe8690883fe4348401fea1a4220ff10d21015fec49080fff5248407ff2924203ff5492101ff8a49080fff4248407ff2124203ff5092101ff8849080fff3248407ff1924203ff4c92101ff8649080aff6148405ffa8a4202ff94521017faa29080bfc5148405ffa0a4202ff90521017fa829080bfc4148405ff98a4202ff8c521017fa629080bfc3148405ff90a4203fdc8521017fc429080bee2148405fe10a4202fb08521017e8429080be42148401ffb024200bfd81210fffcc090806fe6048401feb02421fff1812100df8c09088bff5048445fda82421fff941210fefca09087ffc504843fbe2824222fe1412110ffe809087ffe404843ffe2024220ffcc1210fffc609087ffc3048407ff9024203ff8812101ff8409080bff1048405ff0824202ff0412100dfecaa80067f6554001ffb22a000bfd91500f7fcc8a8016fe6454001feb22a01eff1915002df8c8a801bff545400dff2a2a006ff55150037f8a8a8003ff63540017fb1aa01dff98d50025fcc6a8003fd635403bfe31aa004bf18d50037fea6a801bfe535400dfea9aa006ff14d500f7fe86a8077fe4354001fea1aa01dff10d50007fec4a8002ff6254039ff312a003bf98950007fac4a8073fc62540077e312a006ffd4950037fca4a801bfd525400dfe292a01effd09500e7fc84a8003fd4254039fe212a01dffcc9500e7fc64a8003fd3254039fe192a000ffd8550005fec2a806ffe61540057f30aa000ff585500dff8c2a800afc615400dffa8aa006ff94550037faa2a801bfc515403dffa0aa01bff90550007fa82a806ffc415403bff98aa01bff8c550007fa62a806ffc3154039ff90aa01bff88550007fa42a806ffc21540037fb02a006bed815000ffea0a801bfb5054003ff282a001df9415000ff8a0a80077c5054003fc282a001de1415000ffe80a8007fe4054003fe202a001ffcc15000ffc60a8007fc3054003ff902a001ff8815000ff840a8007ff1054003ff082a001ff0415000ef6c8280077a6414003bcb20a001de1905000ef6c6280077a6314003bcb18a001de18c500d6f6862806
  | 3 => 0xfa92a206ff94951037faa4a881bfc525445dffa12a22cff90951007fa84a88b3fc425445bff992a22cff8c951007fa64a88b3fc32544057fb0aa202ffd4551037eea2a880bfe5154405bf28aa202ff14551016f8a2a880bf45154405ffa0aa202ff90551017f882a880bff3154405ff18aa202ff0c551017fe42a880bfe2154405fe10aa200ffd8151005fec0a8803fb60544017db02a22bff9815100dfcc0a8803fd6054457fe302a201bf18151007f0c0a8806f8605440dffa82a206fed4151037fca0a88af7e505440dfe282a206df14151037f0a0a881b78505445dffa02a22bff9015115ff880a88b7ff3054457ff182a22bff0c151167fe40a88affe2054457fe102a202ffc4151017fc20a880bfc1054401ffb2a8200bfd9541157fccaa081afe6550401feb2a8200bf59541157f8caa081afc65504057fb228205ffd514102ffca8a0817fd545040bfe2a28200ffd8d41005fec6a08a7fe63504097f31a8200ff58d4114ff8c6a0812fc6350455ffa9a8229ff94d41007faa6a08a7fc535040bffa1a8205ff90d4102ffa86a0817fc4350401ffb128200bfd8941147fcc4a080efe6250401feb128228ff1894101df8c4a08abff5250451ff2928200ff54941147f8a4a0817ff425040bff2128205ff5094102ff884a08a7ff3250451ff1928200ff4c941147f864a080aff6150405ffa8a8202ff94541017faa2a080bfc5150405ffa0a8205fdd0541017fc82a080bbe4150405fe20a8202ef10541017e882a080bb44150405ff98a8202ff8c541017f862a080bff2150405ff10a8202ff08541007fec0a0802ff605044fff3028201bf98141007fac0a089ffc60504037e302822affd4141157f6a0a089ffe505044fbf2828227ff1414113ef8a0a08abf8505040bffa028205ff9014102ff880a08a7ff305044fff1828227ff0c141147fe40a089ffe205044ffe1028202ffc4141017fc20a080bfc1050401ffb2a6200bfd9531137fcca9881afe654c401feb2a6200bf59531137f8ca9881afc654c401ffb226200bfd913112ffcc898816fe644c401feb226200bf5913112ff8c898816fc644c44dffaa26225ff95131007faa898897fc544c4057fb1a6204ffd4d31027fca698813fd534c409fe29a6204ffd0d31027fc8698813fd434c409fe21a6200ffd8931005fec498893fe624c4077f3126200ff58931127f8c49880efc624c44dffa926224ff94931007faa498893fc524c44bffa126224ff90931007fa8498893fc424c409ff9926204ff8c931027fa6498813fc324c4057fb0a6202ffd4531017fca29880bfd514c405fe28a6202ffd0531017fc829880bfd414c405fe20a6202ffcc531027ee629880bfe314c405ef18a6202ff0c531017b8629880bf4314c405ea18a6202ffc8531017fc429880bfc214c401ffb026200bfd81
  | 4 => 0xdffc3054807ff902a403ff8815201ff840a90e3ff105486fff082a437ff04152007fecaa1002ff655086dff32a8406bf99542007facaa1002fd655086dfe32a8406bf1954201dfec8a1017ff545080bff2a28405ff5514202ff8a8a1003ff63508017fb1a8435ff98d42025fcc6a1003fd635086bfe31a8404bf18d421b7fea6a10d7fe5350801fea9a8435ff14d4202ffe86a1017fe435080bfea1a8405ff10d4201dfec4a100fff5250807ff2928403ff5494201ff8a4a100fff425080bf7a128403ff9094201f7c84a100ffc4250807de2128403fb1094201f5884a100fff3250807ff1928403ff0c942007fec2a1002ff6150869ff30a8402bf98542007fac2a10d3fc61508057e30a8436ffd45421a7fca2a10d3fc515080bffa0a8405ff9054202ff882a10d7ff3150869ff18a8434ff0c54201ffe42a100ffe2150807fe10a8400ffd8142005fec0a10cffe60508037f3028400ff5814219ff8c0a1006fc605086dffa828436fed414219ffca0a10cf7e5050867fe2828433df141421b7f0a0a1017ff405080bff2028405ff101421affe60a10cffe3050867fe1828403ffc814201ffc40a100ffc2050869ff8828433ff8414219ff820a1003ff654c8017fb2a6432ff99532035fcca99003fd654c8017eb2a6432ff19532035f8ca99003ff644c8017fb226431ff9913202dfcc899003fd644c8017eb226431ff1913202df8c8990cbff544c863ff2a26400ff5513218ff8a89900eff634c809ffa9a6404ff94d32027faa699013fc534c809ffa1a6404ff90d32027fa8699013fc434c8077fb126403ffd493201ffca49900ffd524c807fe2926403ffd093201ffc849900ffd424c807fe2126403ffcc932027de649900ffe324c807ef1926403ff0c93201fb8649900fec324c807e61926400ffd8532005fec2990c3fe614c8057f30a6400ff58532187f8c29900afc614c865ffa8a6430ff94532187f8a2990c7ff414c861ff20a6430ff10532027fe6299013fe314c809fe18a6403ffc853201ffc429900ffc214c801ffb026400bfd813217ffcc099006fe604c801feb02642fff1813200df8c0990cbff504c865fda82642fff9413217efca0990bffc504c85fbe2826432fe1413218ffe80990bffe404c85ffe2026404ffcc132027fc6099013fc304c807ff9026403ff8813201ff840990c3ff104c85fff082642fff04132015fecaa8803ff64544017fb22a22eff9915102dfcc8a8803fd645445dfe322a205bf19151037fea8a881bfe545440dfeaa2a206ff15151007fec6a8802ff635445bff31aa204bf98d51007fac6a88b7fc63544097e31aa206ffd4d51037fca6a881bfd535440dfe29aa22effd0d5116ffc86a8803fd435445bfe21aa200ffd8951005fec4a88b3fe62544077f312a200ff58951167f8c4a880efc625440df
  | 5 => 0xc953007fec2a9802ff6154c81ff30aa602bf98553007fac2a9903fc6154c057e30aa606ffd4553037fca2a981bfc5154c85ffa0aa640ff90553207f882a9813ff3154c09ff18aa604ff0c55320ffe42a9903fe2154c81fe10aa600ffd8153005fec0a9803fb6054c017db02a63fff9815300dfcc0a9803fd6054c7ffe302a601bf18153007f0c0a9806f86054c0dffa82a606fed4153037fca0a98ff7e5054c0dfe282a606df14153037f0a0a981b785054c85ffa02a63fff901531fff880a9813ff3054c09ff182a604ff0c15320ffe40a98fffe2054c7ffe102a640ffc41531fffc20a98fffc1054c01ffb2a8600bfd95431f7fccaa181afe6550c01feb2a8600bf595431f7f8caa181afc6550c097fb228605ffd514302ffca8a1817fd5450c0bfe2a28604bfd8d43027fea6a1813fe5350c09fea9a8604ff14d43027fe86a1817df4350c09ff21a8604ef90d43027f886a1813bc4350c09ee21a8604e710d43007fec4a1802ff6250c7bff3128603bf98943007fac4a18f7fc6250c077e312863effd49431effca4a18f7fc5250c0bffa128605ff9094302ff884a1813ff3250c09ff1928604ff0c943007fec2a1802ff6150c79ff30a8602bf98543007fac2a18f3fc6150c057e30a863effd45431e7fca2a18f3fc5150c0bffa0a8605ff9054302ff882a1813ff3150c09ff18a8604ff0c5431effe42a18f3fe2150c79fe10a8600ffd8143005fec0a18effe6050c037f3028600ff581431dff8c0a1806fc6050c7dffa82863efed41431dffca0a18ef7e5050c77fe282863bdf141431f7f0a0a1817ff4050c0bff2028605ff10143027fe60a1813fe3050c09fe182863dffc81431dffc40a18effc2050c79ff882863bff841431dff820a180eff6554801ffb22a400bfd91521d7fcc8a9016fe6454801feb22a43aff1915202df8c8a901bff545480dff2a2a406ff55152037f8a8a9003ff63548017fb1aa439ff98d52025fcc6a9003fd6354873fe31aa404bf18d52037fea6a901bfe535480dfea9aa406ff14d521d7fe86a90e7fe4354801fea1aa439ff10d5201dfec4a900fff525480df7a92a403ff9495201efca4a900ffc5254807be292a403fb1495201ffe84a900ffe4254807fe212a403ffcc95201ffc64a900ffc3254801ffb0aa400bfd85521c7fcc2a900afe6154801feb0aa438ff18552015f8c2a901bff515480dff28aa406ff145521d7fe82a90e3fe4154871fe20aa439ffcc5521c7fc62a90e3fc3154807ff90aa403ff8855201ff842a9003ff60548017fb02a400fed8152005f6c0a90dffe60548037f302a400ff581521bff8c0a9006fc6054801fc302a401be18152037fea0a901bfb505480dff282a437df94152037f8a0a901b7c505480dfc282a406de141521d7fe80a90dffe405486ffe202a439ffcc1521bffc60a9
  | 6 => 0x12024070000080180681201a0240102a000034030000040e001809004010018050020480380502203803000006128028000080100701e0020980200303a0080000300001814001044010008060420040682801c00006816002000028030060000700200a0280b01d02a0540000d0040000201800007800001002004060030380100280600a0002f0000000201e00002a0040280300002c0080a036080000070200280200100c0000080001000c000040000240701906c0140000202000c03002004008010000060584500100201c00800006008078010180000080001801400002012004048170000002b00400a02c0000200c0080102700a01c00000008000000060000000500300602c0280001a0100400200a01c0000a0000180f80d0100880003c0020380000800000001005008048050080420000280c00a000080100060000082800e06409011000000000180040040c8040340000380d016038018000040040401602000402825000004050220040300100f002004160020640000000200c00c048050020080000201a0200700900601c01800000030010000020000080001202000838010030008000160080100000c00407016ff655500b7fb22a805ffd51540377ea8aa017fe545500bbf2a2a805ff1515402ef8a8aa017bc5455001ffb1aa800bfd8d54237fcc6aa012fe6355001feb1aa846ff18d54025f8c6aa01bff535500dff29aa806ff14d5402ffe86aa017fe435500bfe21aa800ffd8954005fec4aa117fe62550077f312a800ff5895422ff8c4aa00efc625500dffa92a806ff94954037f8a4aa017ff425500bff212a805ff10954237fe64aa117fe325508bfe192a800ffd8554005fec2aa113fe61550057f30aa800ff58554227f8c2aa00afc615500dffa8aa806ff94554037f8a2aa017ff415500bff20aa805ff10554237fe62aa113fe3155089fe18aa845ffc8554227fc42aa113fc2155001ffb02a800bfd8154007f6c0aa002fb6055087ff302a801bf98154007fac0aa10ffc60550037e302a800fe1815400df0c0aa01bff505500dfda82a806ff9415421efca0aa01bfc505500dbe282a806fe14154036f0a0aa017ff405500bff202a805ff10154237fe60aa10ffe3055087fe182a845ffc815421ffc40aa10ffc2055089ff882a843ff8415421ff820aa012ff6554c01ffb22a600bfd9153217fcc8a9816fe6454c01feb22a642ff1915302df8c8a981bff5454c0dff2a2a606ff55153037f8a8a9812ff6354c09ffa9aa606f7d4d53027fca6a98137e5354c09fe29aa604df14d53027b8a6a9813ff4354c09ff21aa604ff10d53007fec4a9802ff6254c83ff312a603bf98953007fac4a9907fc6254c077e312a606ffd4953037fca4a981bfc5254c85ffa12a641ff9095320ff884a9813ff3254c09ff192a604ff0
  | 7 => 0xe8fc24d95c82f8f124d25a1af0c922582d2842c80982208e09ed0001e4ac418a8000528e11ab0812d326f0a827d9249ad99d88c8690d925607aa040f98190858d51a11f822d25b89f83e8000ed8000249dd2d6268a2e800271228a330001980000000001c89f4a868830c21cb1ba8f900010725895923ba510001640ef077000033233a0c26c08280497b0001938c68480299e38f89bd8658789fe01304c0989c688212c9faa0e0222cd8818bb9909420002302411b727e025a2b1e99c228d90f0261bb8012a996595313219b84b29f8c384d0bb137a9901280084402886d81aa892d0ab901f041a0d2bd9f117e83095e1c280000025aabc00000014001813519f16197d0ea2af8b0aac1f285716f8d7a2d99421f15295aa88ab71838000b723e1730cb80f24020380028282d92f9581600da000017ac8a08a4caca1cb98b0a18740ca0b38e027b8488109bf90d19d07fa731d800000012189d1eca6b1af9ff1b88402118000000000170b29b60342c195799284d80027d110ac6042aa69200f415013a25c922920a6ea50187a0514f10998d23283aacf10fa971258000001da1571fc9db90d9e090c8a39c49140002682ad8000539cc92d033a2f9b5a572c907d8ac09000014c1d01ae0000000000e48000000e9000000000171295a2180c2299b29971ea1df05e9b51f58000000268ea8c7800294000106000206a1a80002b24ea79ac709207281fa7286b98c919800129aab947862acd0fb9809d594aa5f00016f1319902be189074827283a8c1e689f17f8040001068001a70000001e30e720b17d9ee8d89be0002c503816a0568002ca8000852a1a802229121cc1869fb13682927b0159a51100af04580a92386783b8a9092870a189ce05c90e21b2d19f0186290985a660468c0a12933abc9c313988a8e99558358449651230348d4a1829f23b06192f09a2c49e00498052a9134978ad380ca581ea92b2b5a84a1600006ca4f9ec0000000a415d0002240001dc0001e814685422a89d9c61d70fa0002549289b30000731a40000000001428000d110e80014828d0000001e50ec8c500000022706312121598ba821280be97b85f00001a09a80008f80888b00080502a05000002002004030000000280300101e0040281100e00c0380000200c0f0120060281403f012000010010220440900100a000020020000280000201400401002006068080010060300080a00a0240080100400c0900100600c068280000380480e00c01c000000080000100c0000200f800018048040460080000100d02c000040000400040080e00402c018000220180400f0180fc0181100602c020050260000100001e0000001900601c0e002004004078180000240000100c0000380000201800803000000000010000200503000e0040000e0040000380502800000005
  | 8 => 0x9d680000021e2a700029e0000001a2ac08880000001f09848001fb8f58fd1371430000002200c308c0002949e218800003f8001bd0869052b000000013e1ac173902000023a151090b69f980026d80e88ea0f96300013d0000148b18fc8c1aa120da348de21925d9a02442ac89e1418f6a4488ba1ca0980997004c8c89ac9148038651388e8998aa8ac205013ca7a14d19527f8c60888dda8fa4f0ad8d087ea109268862310f22912b8954abd01e1c119a8b81c52081699de92a15f07217a0cd96785f8ff97e174a8a021aba2830200422d59e72b112d8ec03b2758638bf09c0ad1f881b91c8d18cf98ea9c1d08000000991b200000000000005a9a99a31b11112101612ae80000024782411e0b599e80007ba690310211cd0000f70ee27c95b91d0961f78f60a980005e2630608eb07f261a9998507517210416393b81b11ba542678b502c1bf0ab2a499c160a368e1922238000257800000000115877a6e15b00a01d2268d81db24c1b98000b48000c98001c18fea2a00024a80028120120e8999d18000002a608d8f280025080025e191a451beacc14629d2bb00000000017c1831cf0dba5314d82e04a8c280025d01387c113252864abf8a12a0a6baaa1b92ad1a3a9aab1a7f05100021d2cc8ff291a778d287380009697080005ba40ac383c01e953ad6a058d40a68fd80000000d20ba498d200021f86219302098f80fa558002988000dd11da792260d98361bc0c41489f20d72c79308231b000008711e93fa749a819b2282000db09728b24e18a2c30371ed9d92900de90b263a7803c96d0d6ace9fc1f7253a459250318ce80018f1921cd9a600005c26c962a019078141119dda980460b000002c8d00c5a14091a4727c00012e83d80b8b31ad238866a41a6a8ca9568b41541272721fe86101d9898670001c59aa10396b0169680a5059a4b8d61c0ab207623fab69eb8060ef98017511f0979aa94f92c1c809e9080cc08d14ea4a26203a17f01c02e9ca8ee9a90a700028e2870000f09b09e913126a02f0000790f380000023712e0002522230000e2abe8931ee2c10e6181a89a719f407815c1eb00002a80000000023f07a12ba008000000000000b78000a29bb0000fe0b1069aa506f057a3c07d23413e97a9e8abaa3a9160001c7843002abba519d20002b496680021d8001ba293a5b17c887977ace0492a58c806c03e054a7e8000000229c000013d8000fa893800224a110390681e2837991000000286105a9c811230a2e12400008f02500000020f0a593316d9622819392bf2879dc8840cd10a13426f91aa17982a7a8000000100280120558e41d481ca029a880197980018200203019c81529795f9409188070f191f8000531521fd06b00021c265ad11302789ef1c40b614e1551440550001d985809087b1519f916b9030e2168a9a23
  | 9 => 0x19900026285085a19594c8bd800000150ab38b91ff80002b80005899f9768001da95a1278839e1a592b99a58bcacf9452250eb86e8c12378278388002a3296ad70be0001e400000000000000020a2d200022b80005d8000e58890ba8001c9a600689f506000b0478b88759de25e9b800029da2928e80003680000009b1a22c00350002d400025686e16a9472930a480000016c10a9969840dfa850562b78ce000138280917a3d90100020205213c0472071328000002768000001d38000001a78001b48188940910000950000642b284f8ae0cb000267171a1a175a650002ae2420f498d9359a48001772b404385b00000028ba6091c00000015d9589f310180e20a80da48a3589b94984f00000000020ca2c0452a824b2a22c99362b08dcaa3926242a278000068aa2a00a799484ea550fb23a1492752c69ef8000001889b68e6a9e83216e29b17420321e89487e0958000c019a1168dc11b14386f80013a80000008493b0ae82a0000d59a694b000000285ab81649128a88e31d2a468002950001182168000000002a41d418e1e59cea708660000001d88898b22cb2060a60001661151a086a040a772b300000000025f859204a739e128c9762120002920001abad484ba212490000000f028a92a8000000f7a4600007000000023d26d1df8e79c70000000000001e7a7401616c9d10da91a04a0000800b98d3259a8f1ca079a430199f61f1ac580007100000017922c9870000e52b6007a8800008a2199562960000001d600000005d2350001c38000f80031598a0aa28000c70cf2669172cb8000002139d32091f69782b5144a6423c8df06d1bc9b413f1961e600018c1b3aaf0329fa23220794a14123900803f19984e1729b7a14a9296915ea3183996e880a221fda2f0002610ed1048001670000412d00bf80000010b9a192901180025c0000001811000002170ab8092d52438c49510f50d38001978002d299e2360002760000f308e0000a21c922394b8a30e8113ac2a9b8ac9b19190768aa8518e38bd2ab1d783d145a480bc09ca7007c9d50afa132698718000a00cc800264aaa8000058002a7a1b8000001f380010886a90c1009029cf8000000001ae8ba000239
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x850d8d10266df30d8d10266dd30d8d10024ff7658d100057f7558d1003d7c7558d100067f6558d100067c6558d10005bf7458d10055bc7458d1004edc6358d10005ef7258d10045ec7258d1025df77158d1026dfb7058d1011f785058d10004ff7558d100067f7558d100047f7558d10034fe7558d10034fc7558d100067c7558d100347c7558d10004ff7458d10006bf7458d10004bf7458d1002cfe7458d1002cfc7458d10006bc7458d1002cbc7458d10264ff7358d10006df7358d10004ff7258d10006ef7258d10004ef7258d1001cfe7258d1001cfc7258d10006ec7258d1001cec7258d1025cff7158d10006f77158d1011cff7058d10006fb7058d10006fb5058d1011e7e5058d1011e7c5058d1011ef85058d1011e785058d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100067f6554d100367c6554d10005fb7054d1000df87054d101ff785054d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100067f6550d101f67c6550d1004f9c4350d101df785050d1001cfe76d89100067f65d89100067c65d8910046ee62d89102477850d8910034fe75d8910004fd75d8910034fc75d891002cfe74d8910004fd74d891002cfc74d8910024fe73d8910004fd73d8910024fc73d89100fcfd72d8910006ef42d8910046ec42d8910006ef32d8910046ec32d891000cff71d8910014fe71d891000cfd71d8910014fc71d8910256ef21d8910256ed21d8910014ff70d891000cfe70d8910014fd70d891000cfc70d8910006fb50d89102467e50d89102467c50d8910246f850d89102467850d8910246ef20d8910246ed20d891001cff76589100057f755891003d7c75589100067f65589100067c6558910005bf7458910055bc7458910005df735891004ddc7358910046ec625891023df7715891024dfb70589100ff785058910004ff75589100067f75589100047f7558910034fe7558910034fc75589100067c75589100347c7558910004ff7458910006bf7458910004bf745891002cfe745891002cfc7458910006bc745891002cbc7458910004ff7358910006df7358910004df7358910024fe7358910024fc7358910006dc7358910024dc7358910244ff7258910006ef725891023cff7158910006f771589100fcff7058910006fb7058910006fb50589100fe7e50589100fe7c50589100fef850589100fe785058910004ff7654910004fe7654910004fd7654910004fc76549100067f65549100367c6554910005fb705491000df870549101bf785054910004ff7650910004fe7650910004fd7650910004fc76509100067f65509101b67c6550910047ac425091019f785050910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c9101967c654c910047cc324c91017f78504c910
  | 1 => 0x9510034ff765951003e7c65595102b5f771595102adfb705951015f7850595102a4ff75595100067f7559510004ff745951002cfe745951002cfc7459510004ff7359510024fe7359510024fc7359510004ff725951001cfe725951001cfc72595102b4ff7159510006f7715951015cff7059510006fb70595102acfb705951003efb505951015e7e505951015e7c505951015ef8505951015e7850595102a57e761951003e7e76195102a47e76195100067e64195100067c64195100067e63195100067c63195100067e62195100067c621951029e7f61195100bf7b701951000d7e701951000d7c701951029f78701951000d78701951029e7f60195100be7b60195100bf7b101951029f76101951029f74101951029f78101951002cfe76d91100067f65d91100067c65d9110056be64d91102877850d9110034fe75d9110004fd75d9110034fc75d911013cfd74d9110024fe73d9110004fd73d9110024fc73d9110006be43d9110056bc43d911001cfe72d9110004fd72d911001cfc72d9110006be42d9110056bc42d911000cff71d9110014fe71d911000cfd71d9110014fc71d9110296bf41d9110296bd41d9110014ff70d911000cfe70d9110014fd70d911000cfc70d9110006fb50d91102867e50d91102867c50d9110286f850d91102867850d9110286bf40d9110286bd40d911002cff76591100057f755911003d7c75591100067f65591100067c6559110056bc6459110005df735911004ddc7359110005ef7259110045ec725911027df7715911028dfb705911013f785059110004ff75591100067f75591100047f7559110034fe7559110034fc75591100067c75591100347c7559110284ff7459110006bf7459110004ff7359110006df7359110004df7359110024fe7359110024fc7359110006dc7359110024dc7359110004ff7259110006ef7259110004ef725911001cfe725911001cfc7259110006ec725911001cec725911027cff7159110006f7715911013cff7059110006fb7059110006fb505911013e7e505911013e7c505911013ef8505911013e785059110004ff7655110004fe7655110004fd7655110004fc76551100067f65551100367c6555110005fb705511000df8705511021f785055110024fe76d8d100067f65d8d100067c65d8d1004ede63d8d102677850d8d10034fe75d8d10004fd75d8d10034fc75d8d1002cfe74d8d10004fd74d8d1002cfc74d8d1011cfd73d8d10006df43d8d1004edc43d8d1001cfe72d8d10004fd72d8d1001cfc72d8d10006de32d8d1004edc32d8d1000cff71d8d10014fe71d8d1000cfd71d8d10014fc71d8d10276df31d8d10276dd31d8d10014ff70d8d1000cfe70d8d10014fd70d8d1000cfc70d8d10006fb50d8d102667e50d8d102667c50d8d10266f850d8d102667
  | 2 => 0x4fd74d852002cfc74d8520024fe73d8520004fd73d8520024fc73d852000cfd72d8520014fc72d8520006f741d8520066f441d8520006f731d8520066f431d8520066f621d85202cef521d852000cfe70d852001cfd70d852000cfc70d8520006fb50d852023e7e50d852023e7c50d852023ef850d852023e7850d852023ef710d85200057f755852005d7c75585200067f65585200067c6558520005bf7458520075bc7458520005df735852006ddc7358520066f461585202c5fb70585200ff785058520004ff7654520004fe7654520004fc76545200067f65545200367c6554520005fb705452000df8705452015f785054520004ff7650520004fe7650520004fc76505200067f65505201567c6550520067b4415052013f785050520004ff764c520004fe764c520004fc764c5200067f654c5201367c654c520067d4314c52011f78504c520034fe76d951003e7e65d951000dfa70d9510015f970d951003f7b50d951015cfd75d951002cfe74d9510004fd74d951002cfc74d951003e7f54d95100067e54d951003e7c54d9510024fe73d9510004fd73d9510024fc73d951003e7f53d95100067e53d951003e7c53d951001cfe72d9510004fd72d951001cfc72d951003e7f52d95100067e52d951003e7c52d951000cff71d9510014fe71d951000cfd71d9510014fc71d95102be7f51d95102be7d51d9510014ff70d951000cfe70d951000cfa70d9510014fd70d95102bef970d9510014f970d951000cfc70d95102a67f50d951003efb50d95102a67d50d95102a6f850d951029d7e76d95100347e76d95100067e64d95100067c64d95100067e63d95100067c63d95100067e62d95100067c62d95102a77a70d95102bf7970d95102bf7b10d95102a77610d95102a77410d95102a77810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067e42d95100067c42d95100067f32d95100067e32d95100067c32d95102a67f71d95102be7e71d95102a67d71d95102a67c71d95102be7f41d95102be7e41d95102be7d41d95102be7c41d95102be7f31d95102be7e31d95102be7d31d95102be7c31d95102be7f21d95102be7e21d95102be7d21d95102be7c21d95102a67f70d95102a67e70d951000c7e70d95102a67a70d951000c7a70d95102a67d70d95102be7970d95102a67c70d951000c7c70d95102a67f40d95102a67e40d95102a67d40d95102a67c40d95102a67f30d95102a67e30d95102a67d30d95102a67c30d95102a67f20d95102a67e20d95102a67d20d95102a67c20d95102a67f10d95102a67e10d95102a67c10d
  | 3 => 0xc71d9120006be41d9120076bc41d912001cff70d912001cfd70d9120006fb50d91202fe7e50d91202fe7c50d91202fef850d91202fe7850d91202febf40d91202febd40d912002cff76591200057f755912005d7c75591200067f65591200067c6559120076bc6459120005df735912006ddc73591202f5ef7259120005f77159120065f47159120305fb705912019f785059120004ff75591200067f75591200047f7559120034fe7559120034fc75591200067c75591200347c75591202fcff7459120006bf7459120004ff7359120006df7359120004df7359120024fe7359120024fc7359120006dc7359120024dc73591202f4ff7259120006ef7259120004ff7159120006f77159120004f77159120014fe7159120014fc7159120006f47159120014f4715912019cff7059120006fb7059120006fb505912019e7e505912019e7c505912019ef8505912019e785059120004ff7655120004fe7655120004fd7655120004fc76551200067f65551200367c6555120005fb705512000df8705512021f785055120024fe76d8d200067f65d8d200067c65d8d2006ede63d8d202df7850d8d20034fe75d8d20004fd75d8d20034fc75d8d2002cfe74d8d20004fd74d8d2002cfc74d8d2017cfd73d8d20006df43d8d2006edc43d8d2000cff72d8d2001cfe72d8d2000cfd72d8d2001cfc72d8d202eedf32d8d202eedd32d8d20014fe71d8d20004fd71d8d20014fc71d8d20006de31d8d2006edc31d8d2001cff70d8d2001cfd70d8d20006fb50d8d202de7e50d8d202de7c50d8d202def850d8d202de7850d8d202dedf30d8d202dedd30d8d20024ff7658d200057f7558d2005d7c7558d200067f6558d200067c6558d20005bf7458d20075bc7458d2006edc6358d202d5ef7258d20005f77158d20065f47158d202e5fb7058d2017f785058d20004ff7558d200067f7558d200047f7558d20034fe7558d20034fc7558d200067c7558d200347c7558d20004ff7458d20006bf7458d20004bf7458d2002cfe7458d2002cfc7458d20006bc7458d2002cbc7458d202dcff7358d20006df7358d202d4ff7258d20006ef7258d20004ff7158d20006f77158d20004f77158d20014fe7158d20014fc7158d20006f47158d20014f47158d2017cff7058d20006fb7058d20006fb5058d2017e7e5058d2017e7c5058d2017ef85058d2017e785058d20004ff7654d20004fe7654d20004fd7654d20004fc7654d200067f6554d200367c6554d20005fb7054d2000df87054d201ff785054d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200067f6550d201f67c6550d2006f9c4350d201df785050d20014fe76d85200067f65d85200067c65d8520066f661d852023f7850d8520034fe75d8520004fd75d8520034fc75d852002cfe74d8520
  | 4 => 0x952005e7f54d95200067e54d952005e7c54d9520024fe73d9520004fd73d9520024fc73d952005e7f53d95200067e53d952005e7c53d952000cff72d952001cfe72d952000cfd72d952001cfc72d95203367f52d95203367d52d9520014fe71d9520004fd71d9520014fc71d952005e7f51d95200067e51d952005e7c51d952001cff70d952001cfd70d9520336f970d952001cf970d952031e7f50d952005efb50d952031e7d50d952031ef850d95203157e76d95200347e76d95200067e64d95200067c64d95200067e63d95200067c63d95200067e61d95200067c61d952031f7a70d95203377970d95203377b20d952031f6e20d952031f6c20d952031f7820d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d95200067f43d95200067e43d95200067c43d952031e7f72d95203367e72d952031e7d72d952031e7c72d95203367f42d95203367e42d95203367d42d95203367c42d95203367f32d95203367e32d95203367d32d95203367c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f41d95200067e41d95200067c41d95200067f31d95200067e31d95200067c31d95203367f21d95203367e21d95203367d21d95203367c21d952031e7f70d952031e7e70d952031e7a70d952031e7d70d95203367970d952031e7c70d952031e7f40d952031e7e40d952031e7d40d952031e7c40d952031e7f30d952031e7e30d952031e7d30d952031e7c30d952031e7f20d952031e7e20d952031e7c20d952031e7f10d952031e7e10d952031e7d10d952031e7c10d9520034ff765952005e7c655952032def7259520325fb70595201bf78505952031cff75595200067f7559520004ff745952002cfe745952002cfc7459520004ff7359520024fe7359520024fc735952032cff7259520006ef7259520004ff7159520014fe7159520014fc71595201bcff7059520006fb7059520324fb705952005efb50595201be7e50595201be7c50595201bef850595201be78505952031d7e761952005e7e761952031c7e76195200067e64195200067c64195200067e63195200067c63195203167f62195200067e61195200067c61195200c77b701952000d7e701952000d7c701952031778701952000d7870195203167f60195200c67b60195200c77b20195203176e20195203176c201952031778201952002cfe76d91200067f65d91200067c65d9120076be64d91202ff7850d9120034fe75d9120004fd75d9120034fc75d912019cfd74d9120024fe73d9120004fd73d9120024fc73d9120006be43d9120076bc43d912000cff72d912001cfe72d912000cfd72d912001cfc72d912030ebf42d912030ebd42d9120014fe71d9120004fd71d9120014f
  | 5 => 0x5f77159130085f4715913036dfb70591301df785059130004ff75591300067f75591300047f7559130034fe7559130034fc75591300067c75591300347c7559130364ff7459130006bf745913035cff7359130006df7359130004ff7259130006ef7259130004ef725913001cfe725913001cfc7259130006ec725913001cec7259130004ff7159130006f77159130004f77159130014fe7159130014fc7159130006f47159130014f471591301dcff7059130006fb7059130006fb50591301de7e50591301de7c50591301def850591301de785059130004ff7655130004fe7655130004fd7655130004fc76551300067f65551300367c6555130005fb705513000df8705513021f78505513001cfe76d89300067f65d89300067c65d893008eee62d89302d77850d8930034fe75d8930004fd75d8930034fc75d893002cfe74d8930004fd74d893002cfc74d893000cfd73d893001cfc73d8930006ef42d893008eec42d893008eee32d8930356ed32d8930014fe71d8930004fd71d8930014fc71d8930006ee21d893008eec21d8930024fd70d8930006fb50d89302d67e50d89302d67c50d89302d6f850d89302d67850d89302d6ef20d89300057f755893007d7c75589300067f65589300067c6558930005bf7458930095bc745893008eec6258930005f77158930085f4715893034dfb705893017f785058930004ff7654930004fe7654930004fc76549300067f65549300367c6554930005fb705493000df870549301bf785054930004ff7650930004fe7650930004fc76509300067f65509301b67c655093008fac425093019f785050930014fe76d85300067f65d85300067c65d8530086f661d853025f7850d8530034fe75d8530004fd75d8530034fc75d853002cfe74d8530004fd74d853002cfc74d853000cfd73d8530014fc73d853001cfe72d8530004fd72d853001cfc72d8530006f741d8530086f441d8530086f631d8530346f531d8530006f721d8530086f421d8530024fd70d8530006fb50d853025e7e50d853025e7c50d853025ef850d853025e7850d853025ef710d85300057f755853007d7c75585300067f65585300067c6558530005bf7458530095bc7458530005ef725853008dec7258530086f4615853033dfb705853011f785058530004ff7654530004fe7654530004fc76545300067f65545300367c6554530005fb705453000df8705453015f785054530004ff7650530004fe7650530004fc76505300067f65505301567c6550530087b4415053013f785050530004ff7648530004fe7648530004fc76485300067f65485301167c6548530087e421485300ff785048530034fe76d952005e7e65d952000dfa70d952001df970d952005f7b50d95201bcfd75d952002cfe74d9520004fd74d952002cfc74d
  | 6 => 0xc51d9530024ff70d9530024fd70d953039ef970d9530024f970d95303867f50d953007efb50d95303867d50d9530386f850d953037d7e76d95300347e76d95300067e64d95300067c64d95300067e62d95300067c62d95300067e61d95300067c61d95303877a70d953039f7970d953039f7b30d95303875e30d95303875c30d95303877830d95300067f74d95300067e74d95300067d74d95300067c74d95303867f73d953039e7e73d95303867d73d95303867c73d953039e7f43d953039e7e43d953039e7d43d953039e7c43d95300067f72d95300067e72d95300067d72d95300067c72d95300067f42d95300067e42d95300067c42d953039e7f32d953039e7e32d953039e7d32d953039e7c32d95300067f71d95300067e71d95300067d71d95300067c71d95300067f41d95300067e41d95300067c41d953039e7f31d953039e7e31d953039e7d31d953039e7c31d95300067f21d95300067e21d95300067c21d95303867f70d95303867e70d95303867a70d95303867d70d953039e7970d95303867c70d95303867f40d95303867e40d95303867d40d95303867c40d95303867f30d95303867e30d95303867c30d95303867f20d95303867e20d95303867d20d95303867c20d95303867f10d95303867e10d95303867d10d95303867c10d9530034ff765953007e7c6559530395df735953038dfb70595301ff785059530384ff75595300067f7559530004ff745953002cfe745953002cfc7459530394ff7359530006df7359530004ff725953001cfe725953001cfc7259530004ff7159530014fe7159530014fc71595301fcff7059530006fb705953038cfb705953007efb50595301fe7e50595301fe7c50595301fef850595301fe7850595303857e761953007e7e76195303847e76195300067e64195300067c641953037e7f63195300067e62195300067c62195300067e61195300067c61195300cf7b701953000d7e701953000d7c701953037f78701953000d78701953037e7f60195300ce7b60195300cf7b301953037f5e301953037f5c301953037f78301953002cfe76d91300067f65d91300067c65d9130096be64d91303677850d9130034fe75d9130004fd75d9130034fc75d91301dcfd74d913000cff73d9130024fe73d913000cfd73d9130024fc73d9130376bf43d9130376bd43d913001cfe72d9130004fd72d913001cfc72d9130006be42d9130096bc42d9130014fe71d9130004fd71d9130014fc71d9130006be41d9130096bc41d9130024ff70d9130024fd70d9130006fb50d91303667e50d91303667c50d9130366f850d91303667850d9130366bf40d9130366bd40d913002cff76591300057f755913007d7c75591300067f65591300067c6559130096bc645913035ddf7359130005ef725913008dec7259130
  | 7 => 0x8d4035e7e50d8d4035e7c50d8d4035ef850d8d4035e7850d8d4035edf30d8d400057f7558d4009d7c7558d400067f6558d400067c6558d400b6dc6358d40005ef7258d400adec7258d40005f77158d400a5f47158d403c5fb7058d401df785058d40004ff7654d40004fe7654d40004fc7654d400067f6554d400367c6554d40005fb7054d4000df87054d401ff785054d4001cfe76d89400067f65d89400067c65d89400aeee62d89402f77850d8940034fe75d8940004fd75d8940034fc75d894000cfd74d894001cfc74d8940024fe73d8940004fd73d8940024fc73d89400aeee42d89403beed42d8940006ef32d89400aeec32d8940014fe71d8940004fd71d8940014fc71d8940006ee21d89400aeec21d894002cfd70d8940006fb50d89402f67e50d89402f67c50d89402f6f850d89402f67850d89402f6ef20d89400057f755894009d7c75589400067f65589400067c6558940005df73589400b5dc73589400aeec6258940005f771589400a5f471589403b5fb705894019f785058940004ff7654940004fe7654940004fc76549400067f65549400367c6554940005fb705494000df870549401bf785054940004ff764c940004fe764c940004fc764c9400067f654c9401967c654c9400afcc324c94017f78504c940014fe76d85400067f65d85400067c65d85400a6f661d854027f7850d8540034fe75d8540004fd75d8540034fc75d854000cfd74d8540014fc74d8540024fe73d8540004fd73d8540024fc73d854001cfe72d8540004fd72d854001cfc72d85400a6f641d85403aef541d8540006f731d85400a6f431d8540006f721d85400a6f421d854002cfd70d8540006fb50d854027e7e50d854027e7c50d854027ef850d854027e7850d854027ef710d85400057f755854009d7c75585400067f65585400067c6558540005df73585400b5dc7358540005ef72585400adec72585400a6f461585403a5fb705854013f785058540004ff7654540004fe7654540004fc76545400067f65545400367c6554540005fb705454000df8705454015f785054540004ff764c540004fe764c540004fc764c5400067f654c5401367c654c5400a7d4314c54011f78504c540004ff7648540004fe7648540004fc76485400067f65485401167c65485400a7e421485400ff785048540034fe76d953007e7e65d953000dfa70d9530025f970d953007f7b50d95301fcfd75d953002cfe74d9530004fd74d953002cfc74d953007e7f54d95300067e54d953007e7c54d953000cff73d9530024fe73d953000cfd73d9530024fc73d953039e7f53d953039e7d53d953001cfe72d9530004fd72d953001cfc72d953007e7f52d95300067e52d953007e7c52d9530014fe71d9530004fd71d9530014fc71d953007e7f51d95300067e51d953007e7
  | 8 => 0x3f67f54d95403f67d54d9540024fe73d9540004fd73d9540024fc73d954009e7f53d95400067e53d954009e7c53d954001cfe72d9540004fd72d954001cfc72d954009e7f52d95400067e52d954009e7c52d9540014fe71d9540004fd71d9540014fc71d954009e7f51d95400067e51d954009e7c51d954002cff70d954002cfd70d95403f6f970d954002cf970d95403de7f50d954009efb50d95403de7d50d95403def850d95403d57e76d95400347e76d95400067e63d95400067c63d95400067e62d95400067c62d95400067e61d95400067c61d95403df7a70d95403f77970d95403f77b40d95403df3e40d95403df3c40d95403df7840d95403de7f74d95403f67e74d95403de7d74d95403de7c74d95400067f73d95400067e73d95400067d73d95400067c73d95403f67f43d95403f67e43d95403f67d43d95403f67c43d95400067f72d95400067e72d95400067d72d95400067c72d95403f67f42d95403f67e42d95403f67d42d95403f67c42d95400067f32d95400067e32d95400067c32d95400067f71d95400067e71d95400067d71d95400067c71d95403f67f41d95403f67e41d95403f67d41d95403f67c41d95400067f31d95400067e31d95400067c31d95400067f21d95400067e21d95400067c21d95403de7f70d95403de7e70d95403de7a70d95403de7d70d95403f67970d95403de7c70d95403de7f40d95403de7e40d95403de7c40d95403de7f30d95403de7e30d95403de7d30d95403de7c30d95403de7f20d95403de7e20d95403de7d20d95403de7c20d95403de7f10d95403de7e10d95403de7d10d95403de7c10d9540034ff765954009e7c65595403edbf74595403e5fb705954021f7850595403dcff75595400067f75595403ecff7459540006bf7459540004ff7359540024fe7359540024fc7359540004ff725954001cfe725954001cfc7259540004ff7159540014fe7159540014fc715954021cff7059540006fb70595403e4fb705954009efb505954021e7e505954021e7c505954021ef8505954021e7850595403dd7e761954009e7e76195403dc7e76195403d67f64195400067e63195400067c63195400067e62195400067c62195400067e61195400067c61195400d77b701954000d7e701954000d7c70195403d778701954000d7870195403d67f60195400d67b60195400d77b40195403d73e40195403d73c40195403d7784019540024fe76d8d400067f65d8d400067c65d8d400b6de63d8d4035f7850d8d40034fe75d8d40004fd75d8d40034fc75d8d4000cfd74d8d40024fc74d8d400b6de43d8d403cedd43d8d4001cfe72d8d40004fd72d8d4001cfc72d8d40006de32d8d400b6dc32d8d40014fe71d8d40004fd71d8d40014fc71d8d40006de31d8d400b6dc31d8d4002cfd70d8d40006fb50d
  | 9 => 0x861504500bf7b41504500d77341504500bf7a41504500bf3a41504500bf7841504500bf3841504500bf7041504500bf3041504500bf7b31504500bf7a31504500bf7831504500bf7b21504500bf7a21504500bf78215045011f7b764c45011d7b764c45011f7a764c45000d7a764c45011f79764c45011d79764c45011f78764c45000d78764c4500077b744c4500057b744c4504177a744c4500d57a744c45000779744c45000579744c45041778744c4500d578744c45011f7b644c45011f7a644c45011f79644c45011f78644c4502657b734c45011f7b634c45011f7a634c45011f5a634c45011f79634c45011f59634c45011f78634c4500cf7b434c4500cf7a434c4500cf79434c4500cf78434c4500077b724c4500057b724c45040f7a724c4500c57a724c45000779724c45040f78724c4500c578724c45011f7b624c45011f7a624c45011f79624c45011f78624c4504177b424c45040f7a424c45000779424c45040f78424c4500cf7b324c4500cf7a324c4500cf79324c4500cf78324c45025d7b714c45011f7b614c45011f7a614c45011f72614c45011f79614c45011f71614c45011f78614c4500bf7b414c4500bf7a414c4500bf79414c4500bf78414c4500bf7b314c4500cf73314c4500bf7a314c4500bf5a314c4500bf78314c4500bf58314c4500bf70314c4500bf50314c4500bf7b214c4500bf7a214c4500bf78214c4500ff7b76484500fd7b76484500ff7a764845000d7a76484500ff7976484500fd7976484500ff78764845000d7876484500077b74484500057b74484504077a74484500d57a74484500077974484500057974484504077874484500d57874484500ff7b64484500ff7a64484500ff7964484500ff7864484500077b73484500057b73484503ff7a73484500cd7a73484500077973484500057973484503ff7873484500cd7873484500ff7b63484500ff7a63484500ff7963484500ff7863484504077b43484503ff7a43484500077943484503ff7843484502457b72484500ff7b62484500ff7a62484500ff6a62484500ff7962484500ff6962484500ff7862484500c77b42484500c77a42484500c77942484500c77842484500c77b32484500c77a32484500c77932484500c778324845023d7b71484500ff7b61484500ff7a61484500ff7261484500ff7961484500ff7161484500ff7861484500bf7b41484500bf7a41484500bf7941484500bf7841484500bf7b31484500bf7a31484500bf7931484500bf7831484500bf7b21484500c77321484500bf7a21484500bf6a21484500bf7821484500bf6821484500bf7021484500bf602148450034fe76d954009e7e65d954000dfa70d954002df970d954009f7b50d954021cfd75d954000cff74d954002cfe74d954000cfd74d954002cfc74d9540
  | 10 => 0x85019f7a635085019f79635085019f7863508500d77b43508500d77a43508500d77943508500d77843508502f57b725085019f7b625085019f7a625085019f6a625085019f79625085019f69625085019f7862508500c77b42508500d76b42508500c77a42508500c73a42508500c77842508500c73842508500c76842508500c72842508500c77b32508500c77a32508500c77832508500077b71508500057b715085043f7a71508500bd7a715085000779715085043f7871508500bd78715085019f7b615085019f7a615085019f79615085019f7861508500d77b41508500d77a41508500d77841508504477b315085043f7a315085043f7831508500c77b21508500c77a21508500c778215085017f7b764c85017d7b764c85017f7a764c85000d7a764c85017f79764c85017d79764c85017f78764c85000d78764c8500077b744c8500057b744c8504377a744c8500d57a744c85000779744c85000579744c85043778744c8500d578744c85017f7b644c85017f7a644c85017f79644c85017f78644c8502dd7b734c85017f7b634c85017f7a634c85017f5a634c85017f79634c85017f59634c85017f78634c8500cf7b434c8500cf7a434c8500cf79434c8500cf78434c8502d57b724c85017f7b624c85017f7a624c85017f6a624c85017f79624c85017f69624c85017f78624c8500c77b424c8500c77a424c8500c779424c8500c778424c8500c77b324c8500cf6b324c8500c77a324c8500c75a324c8500c778324c8500c758324c8500c768324c8500c748324c8500077b714c8500057b714c85042f7a714c8500bd7a714c85000779714c85042f78714c8500bd78714c85017f7b614c85017f7a614c85017f79614c85017f78614c8504377b414c85042f7a414c85042f78414c8500cf7b314c8500cf7a314c8500cf78314c8500c77b214c8500c77a214c8500c778214c85013f7b765045013d7b765045013f7a765045000d7a765045013f79765045013d79765045013f78765045000d7876504502857b745045013f7b645045013f7a645045013f3a645045013f79645045013f39645045013f7864504500077b73504500057b73504504277a73504500cd7a73504500077973504504277873504500cd78735045013f7b635045013f7a635045013f79635045013f7863504500d77b43504500d77a43504500d77943504500d77843504500077b72504500057b725045041f7a72504500c57a725045000779725045041f7872504500c578725045013f7b625045013f7a625045013f79625045013f7862504500d77b42504500d77a42504500d77942504500d77842504504277b325045041f7a325045000779325045041f78325045027d7b715045013f7b615045013f7a615045013f72615045013f79615045013f71615045013f7
  | 11 => 0x4fd74d895002cfc74d8950024fe73d8950004fd73d8950024fc73d89500e6ee52d8950476ed52d8950014fe71d8950004fd71d8950014fc71d8950034fd70d8950476fb50d895032e7e50d895032e7c50d895032ef850d895032e7850d895032eef20d89500e6ec625895046dfb70589501bf785058950004ff7650950004fe7650950004fc765095019e7f65509500e7ac4250950326fb605095019f785050950004ff764c950004fe764c950004fc764c95017e7f654c9500e7cc324c950326fb604c95017f78504c950014fe76d85500def661d85502b77850d855000cfd75d8550014fc75d855002cfe74d8550004fd74d855002cfc74d8550024fe73d8550004fd73d8550024fc73d855001cfe72d8550004fd72d855001cfc72d85500def651d8550466f551d8550034fd70d8550466fb50d85502b67e50d85502b67c50d85502b6f850d85502b67850d85502b6f710d85500def4615855045dfb705855015f785058550004ff7650550004fe7650550004fc765055013e7f65505500dfb441505502aefb605055013f785050550004ff764c550004fe764c550004fc764c55011e7f654c5500dfd4314c5502aefb604c55011f78504c550004ff7648550004fe7648550004fc76485500fe7f65485500dfe421485502aefb60485500ff7850485501df7b7650c501dd7b7650c501df7a7650c5000d7a7650c501df797650c501dd797650c501df787650c5000d787650c503657b7450c501df7b6450c501df7a6450c501df3a6450c501df796450c501df396450c501df786450c5035d7b7350c501df7b6350c501df7a6350c501df5a6350c501df796350c501df596350c501df786350c500cf7b4350c500d75b4350c500cf7a4350c500cf3a4350c500cf784350c500cf384350c500cf584350c500cf184350c500077b7250c500057b7250c504577a7250c500c57a7250c50007797250c50457787250c500c5787250c501df7b6250c501df7a6250c501df796250c501df786250c500d77b4250c500d77a4250c500d7784250c500cf7b3250c500cf7a3250c500cf783250c500077b7150c500057b7150c5044f7a7150c500bd7a7150c50007797150c5044f787150c500bd787150c501df7b6150c501df7a6150c501df796150c501df786150c500d77b4150c500d77a4150c500d7784150c500cf7b3150c500cf7a3150c500cf783150c504577b2150c5044f7a2150c5044f782150c5019f7b765085019d7b765085019f7a765085000d7a765085019f79765085019d79765085019f78765085000d7876508502fd7b745085019f7b645085019f7a645085019f3a645085019f79645085019f39645085019f7864508500077b73508500057b73508504477a73508500cd7a73508500077973508504477873508500cd78735085019f7b635
  | 12 => 0xd73d8d21006df53d8d21106dc53d8d21106de43d8d21014ff72d8d21014fd72d8d214b6df32d8d214b6dd32d8d2101cff71d8d2101cfd71d8d214a6df31d8d214a6dd31d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21006fb50d8d210067e50d8d210067c50d8d21006f850d8d21006de30d8d21106dc30d8d21024ff7658d21106dc6358d2149def7258d214adf77158d21187e42158d21004ff7558d21034fe7558d21034fc7558d21004ff7458d2102cfe7458d2102cfc7458d214a4ff7358d21006df7358d2149cff7258d21006ef7258d21184ff7158d21006f77158d21004ff7058d2100cfe7058d2100cfc7058d21006fb5058d210067e5058d210067c5058d21006f85058d21004ff7654d21004fe7654d21004fd7654d21004fc7654d21207e42154d21005fb7054d210fdf87054d21117785054d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21006bf6450d2102ebc6450d21006df6350d21026dc6350d211079c4350d21005ef7250d2101dec7250d21005f77150d21015f47150d211e7e42150d2100cfe76d81211157e75d81210057d75d812124fe421d81210fefa60d81210ff7850d8121034fe75d81210067e75d81210347e75d8121004fd75d81210067d75d81210047d75d8121034fc75d812102cfe74d8121004fd74d812102cfc74d8121024fe73d8121004fd73d8121024fc73d8121014fd72d812100cfc72d812101cfd71d812100cfc71d8121006fb50d81210fe7e50d81210fe7c50d81210fef850d81210fe7850d81210fefa20d81210fefa10d81210057f75581211157c7558121005bf745812110dbc7458121005df7358121105dc7358121067e421581210fef860581210ff78505812102cfe76d91500f6be64d91503ef7850d915000cfd75d915002cfc75d91500f6be54d9150496bd54d9150024fe73d9150004fd73d9150024fc73d915001cfe72d9150004fd72d915001cfc72d9150014fe71d9150004fd71d9150014fc71d9150034fd70d9150496fb50d91503ee7e50d91503ee7c50d91503eef850d91503ee7850d91503eebf40d91500f6bc645915048dfb705915021f785059150024fe76d8d500eede63d8d503977850d8d5000cfd75d8d50024fc75d8d5002cfe74d8d50004fd74d8d5002cfc74d8d500eede53d8d50486dd53d8d5001cfe72d8d50004fd72d8d5001cfc72d8d50014fe71d8d50004fd71d8d50014fc71d8d50034fd70d8d50486fb50d8d503967e50d8d503967c50d8d50396f850d8d503967850d8d50396df30d8d500eedc6358d5047dfb7058d501ff785058d50004ff7650d50004fe7650d50004fc7650d501de7f6550d500ef9c4350d5038efb6050d501df785050d5001cfe76d89500e6ee62d895032f7850d895000cfd75d895001cfc75d895002cfe74d8950
  | 13 => 0x8131014fd73d813100cfc73d813101cfe72d8131004fd72d813101cfc72d8131024fd71d8131006fb50d813111e7e50d813111e7c50d813111ef850d813111e7850d813111efa30d813111efa10d81310057f75581311357c7558131005bf745813112dbc7458131005ef7258131125ec7258131087d4315813111ef8605813111f785058131034fe76d95211167e65d95214e7e421d95210fdfa70d9521005f970d95211177850d95211c4fd75d952102cfe74d9521004fd74d952102cfc74d9521024fe73d9521004fd73d9521024fc73d9521014ff72d9521014fd72d95214f67f52d95214f67d52d952101cff71d952101cfd71d95214e67f51d95214e67d51d952100cfe70d9521006fa70d952100cfa70d9521004fd70d9521006f970d9521004f970d952100cfc70d9521116fb50d95210067e50d95211167c50d9521116f850d95211167850d9521034ff76595211167c6559521005bf745952110dbc7459521005df7359521105dc73595214ddef72595214edf771595211c7e42159521005fb70595210fdf870595211177850595214e4ff75595210067f7559521004ff7459521006bf7459521004bf745952102cfe745952102cfc7459521006bc745952102cbc7459521004ff7359521006df7359521004df7359521024fe7359521024fc7359521006dc7359521024dc73595214dcff7259521006ef72595211c4ff7159521006f77159521004ff7059521006fb7059521004fb705952100cfe705952100cfc7059521006f8705952100cf87059521116fb50595210067e50595211167c5059521116f8505952111678505952102cfe76d912110ebe64d91214c7e421d9121034fe75d9121004fd75d9121034fc75d91211a4fd74d9121006bf54d912110ebc54d9121024fe73d9121004fd73d9121024fc73d912110ebf43d9121014ff72d9121014fd72d91214d6bf42d91214d6bd42d912101cff71d912101cfd71d91214c6bf41d91214c6bd41d912100cfe70d9121004fd70d912100cfc70d9121006fb50d91210067e50d91210067c50d9121006f850d9121006be40d912110ebc40d912102cff765912110ebc64591214bdef72591214cdf771591211a7e42159121004ff7559121034fe7559121034fc75591214c4ff7459121006bf7459121004ff7359121024fe7359121024fc73591214bcff7259121006ef72591211a4ff7159121006f77159121004ff705912100cfe705912100cfc7059121006fb50591210067e50591210067c5059121006f85059121004ff7655121004fe7655121004fd7655121004fc7655121227e42155121005fb70551210fdf87055121117785055121024fe76d8d21106de63d8d214a7e421d8d21034fe75d8d21004fd75d8d21034fc75d8d2102cfe74d8d21004fd74d8d2102cfc74d8d21184f
  | 14 => 0x34ff76595311367c6559531005bf745953112dbc745953152ddf7359531005ef7259531125ec725953153df77159531207d43159531005fb705953111df87059531137785059531534ff75595310067f7559531004ff7459531006bf7459531004bf745953102cfe745953102cfc7459531006bc745953102cbc745953152cff7359531006df7359531004ff7259531006ef7259531004ef725953101cfe725953101cfc7259531006ec725953101cec7259531204ff7159531006f77159531004ff7059531006fb7059531004fb705953100cfe705953100cfc7059531006f8705953100cf87059531136fb50595310067e50595311367c5059531136f8505953113678505953102cfe76d913112ebe64d9131517d431d9131034fe75d9131004fd75d9131034fc75d91311e4fd74d9131006bf54d913112ebc54d9131014ff73d9131014fd73d9131526bf43d9131526bd43d913101cfe72d9131004fd72d913101cfc72d913112ebf42d9131024ff71d9131024fd71d9131516bf41d9131516bd41d913100cfe70d9131004fd70d913100cfc70d9131006fb50d91310067e50d91310067c50d9131006f850d9131006be40d913112ebc40d913102cff765913112ebc645913150ddf735913151df771591311e7d43159131004ff7559131034fe7559131034fc7559131514ff7459131006bf745913150cff7359131006df7359131004ff725913101cfe725913101cfc72591311e4ff7159131006f77159131004ff705913100cfe705913100cfc7059131006fb50591310067e50591310067c5059131006f85059131004ff7655131004fe7655131004fd7655131004fc7655131227d43155131005fb705513111df8705513113778505513101cfe76d8931126ee62d893149fd431d8931034fe75d8931004fd75d8931034fc75d893102cfe74d8931004fd74d893102cfc74d8931014fd73d8931006ef52d8931126ec52d8931126ee42d8931126ee32d8931506ed32d8931024fd71d893149eef21d893100cfe70d8931004fd70d893100cfc70d8931006fb50d89310067e50d89310067c50d8931006f850d8931006ee20d8931126ec20d8931126ec62589314fdf77158931187d43158931004ff7654931004fe7654931004fc76549311c7d43154931005fb705493111df87054931137785054931004ff7650931004fe7650931004fc7650931006bf645093102ebc6450931005df7350931025dc7350931006ef625093101eec6250931127ac4250931005f77150931015f471509311a7d4315093100cfe76d81311357e75d81310057d75d813126fd431d813111efa60d813111f7850d8131034fe75d81310067e75d81310347e75d8131004fd75d81310067d75d81310047d75d8131034fc75d813102cfe74d8131004fd74d813102cfc74d
  | 15 => 0xc7259541224ff7159541006f77159541004ff7059541006fb7059541004fb705954100cfe705954100cfc7059541006f8705954100cf87059541156fb50595410067e50595411567c5059541156f85059541156785059541024fe76d8d4114ede63d8d4150fb441d8d41034fe75d8d41004fd75d8d41034fc75d8d41014fd74d8d41006df53d8d4114edc53d8d4114ede43d8d41566dd43d8d4101cfe72d8d41004fd72d8d4101cfc72d8d4114edf32d8d4102cfd71d8d4150edf31d8d4100cfe70d8d41004fd70d8d4100cfc70d8d41006fb50d8d410067e50d8d410067c50d8d41006f850d8d41006de30d8d4114edc30d8d4114edc6358d4155df77158d411e7b44158d41004ff7654d41004fe7654d41004fc7654d41207b44154d41005fb7054d4113df87054d41157785054d4101cfe76d8941146ee62d89414bfb441d8941034fe75d8941004fd75d8941034fc75d8941014fd74d8941024fe73d8941004fd73d8941024fc73d8941006ef52d8941146ec52d8941146ee42d8941556ed42d8941146ee32d894102cfd71d89414beef21d894100cfe70d8941004fd70d894100cfc70d8941006fb50d89410067e50d89410067c50d8941006f850d8941006ee20d8941146ec20d8941146ec625894154df771589411a7b44158941004ff7654941004fe7654941004fc76549411c7b44154941005fb705494113df87054941157785054941004ff764c941004fe764c941004fc764c941005bf744c94102dbc744c941006df634c941026dc634c941006ef624c94101eec624c941147cc324c941005f7714c941015f4714c941187b4414c94100cfe76d81411557e75d81410057d75d814128fb441d814113efa60d814113f7850d8141034fe75d81410067e75d81410347e75d8141004fd75d81410067d75d81410047d75d8141034fc75d8141014fd74d814100cfc74d8141024fe73d8141004fd73d8141024fc73d814101cfe72d8141004fd72d814101cfc72d814102cfd71d8141006fb50d814113e7e50d814113e7c50d814113ef850d814113e7850d814113efa40d814113efa10d81410057f75581411557c7558141005df735814114ddc7358141005ef7258141145ec72581410a7b4415814113ef8605814113f785058141034fe76d95311367e65d9531537d431d953111dfa70d9531005f970d95311377850d9531204fd75d953102cfe74d9531004fd74d953102cfc74d9531014ff73d9531014fd73d95315467f53d95315467d53d953101cfe72d9531004fd72d953101cfc72d9531024ff71d9531024fd71d95315367f51d95315367d51d953100cfe70d9531006fa70d953100cfa70d9531004fd70d9531006f970d9531004f970d953100cfc70d9531136fb50d95310067e50d95311367c50d9531136f850d95311367850d9531
  | 16 => 0x815115f7a75d81512af7975d8151006fb64d8151006fa64d8151006f964d8151006f864d8151006fb63d8151006fa63d8151006f963d8151006f863d8151006fb62d8151006fa62d8151006f962d8151006f862d815145ff351d81512af7a51d81512af7851d81512aff051d81512aefb75d815115efa75d815115e7a75d81512aef975d81512ae7975d81512aef875d815100cf875d8151006fb74d8151006fa74d8151006f974d8151006f874d815145efb54d815145efa54d815145ef954d815145ef854d8151006fb73d8151006fa73d8151006f973d8151006f873d815145efb53d815145efa53d815145ef953d815145ef853d8151006fb43d8151006fa43d8151006f943d8151006f843d8151006fb72d8151006fa72d8151006f972d8151006f872d815145efb52d815145efa52d815145ef952d815145ef852d8151006fb42d8151006fa42d8151006f942d8151006f842d8151006fb32d8151006fa32d8151006f932d8151006f832d81512aefb71d815115efa71d81512aef971d81512aef871d81512aefb51d81512aefa51d81512aef851d81512aefb41d81512aefa41d81512aef941d81512aef841d81512aefb31d81512aefa31d81512aef931d81512aef831d81512aefb21d81512aefa21d81512aef921d81512aef821d815115ef8605815115f7850581512adfa761815115efa761815115f7b7518151035fa7518151035f8751815115f7875181510357875181512a6fb65181512a67b6518151006fb6418151006fa6418151006f96418151006f86418151006fb6318151006fa6318151006f96318151006f86318151006fb6218151006fa6218151006f96218151006f862181512b6fb611815158ff351181510bf7a51181510bf7851181510bff05118151034fe76d95411567e65d9541577b441d954113dfa70d9541005f970d95411577850d9541224fd75d9541014ff74d9541014fd74d95415867f54d95415867d54d9541024fe73d9541004fd73d9541024fc73d954101cfe72d9541004fd72d954101cfc72d954102cff71d954102cfd71d95415767f51d95415767d51d954100cfe70d9541006fa70d954100cfa70d9541004fd70d9541006f970d9541004f970d954100cfc70d9541156fb50d95410067e50d95411567c50d9541156f850d95411567850d9541034ff76595411567c655954156dbf7459541005df735954114ddc7359541005ef7259541145ec725954157df77159541227b44159541005fb705954113df87059541157785059541574ff75595410067f755954156cff7459541006bf7459541004ff7359541006df7359541004df7359541024fe7359541024fc7359541006dc7359541024dc7359541004ff7259541006ef7259541004ef725954101cfe725954101cfc7259541006ec725954101ce
  | 17 => 0x17e7c50d813217ef850d813217e7850d813217efa30d813217efa20d81320057f75581321957c7558132005bf745813218dbc745813208fcc3258132005f77158132185f4715813217ef8605813217f78505813202cfe76d9151176be64d91515bf7850d9151014fd75d9151176be54d91515bebd54d9151024fe73d9151004fd73d9151024fc73d9151006be43d9151176bc43d915101cfe72d9151004fd72d915101cfc72d9151006be42d9151176bc42d9151034fd71d915156ebf41d915100cfe70d9151004fd70d915100cfc70d91515befb50d91510067e50d91515be7c50d91515bef850d91515be7850d9151176bc6459151005df735915116ddc7359151005ef7259151165ec72591515b5f77159151005fb705915115df87059151157785059151024fe76d8d5116ede63d8d515af7850d8d51014fd75d8d5102cfe74d8d51004fd74d8d5102cfc74d8d5116ede53d8d515aedd53d8d51006df43d8d5116edc43d8d5101cfe72d8d51004fd72d8d5101cfc72d8d51006de32d8d5116edc32d8d51034fd71d8d5152edf31d8d5100cfe70d8d51004fd70d8d5100cfc70d8d515aefb50d8d510067e50d8d515ae7c50d8d515aef850d8d515ae7850d8d51005bf7458d51175bc7458d5116edc6358d51005ef7258d51165ec7258d515a5f77158d51005fb7058d5115df87058d51137785058d51004ff7650d51004fe7650d51004fc7650d5116f9c4350d511def86050d511f7785050d5101cfe76d8951166ee62d895159f7850d8951014fd75d895102cfe74d8951004fd74d895102cfc74d8951024fe73d8951004fd73d8951024fc73d8951166ee52d895159eed52d8951006ef42d8951166ec42d8951006ef32d8951166ec32d8951034fd71d89514deef21d895100cfe70d8951004fd70d895100cfc70d895159efb50d89510067e50d895159e7c50d895159ef850d895159e7850d8951005bf7458951175bc7458951005df735895116ddc7358951166ec6258951595f77158951005fb705895115df87058951117785058951004ff7650951004fe7650951004fc7650951167ac425095119ef860509511b7785050951004ff764c951004fe764c951004fc764c951167cc324c95117ef8604c95119778504c95100cfe76d81510357e75d81510157d75d815115efa60d815115f7a50d8151014fd75d815115e7d75d81510147d75d815100cfc75d815102cfe74d8151004fd74d815102cfc74d8151024fe73d8151004fd73d8151024fc73d815101cfe72d8151004fd72d815101cfc72d8151034fd71d815115e7e50d815115efa50d815115e7c50d8151006fb40d815115efa40d815115ef840d8151006fb30d815115efa30d815115ef830d8151006fb20d815115efa20d815115ef820d815115efa10d815115dfa76d815100cfa76d
  | 18 => 0xe71d9532004fd71d9532014fc71d953200cfe70d9532006fa70d953200cfa70d9532004fd70d9532006f970d9532004f970d953200cfc70d9532196fb50d95320067e50d95321967c50d9532196f850d95321967850d9532034ff76595321967c6559532005bf745953218dbc74595325e5df73595325f5ef725953220fcc3259532005f77159532185f47159532005fb705953217df870595321977850595325ecff75595320067f7559532004ff7459532006bf7459532004bf745953202cfe745953202cfc7459532006bc745953202cbc74595325e4ff7359532006df735953220cff7259532006ef7259532004ff7159532006f77159532004f77159532014fe7159532014fc7159532006f47159532014f47159532004ff7059532006fb7059532004fb705953200cfe705953200cfc7059532006f8705953200cf87059532196fb50595320067e50595321967c5059532196f8505953219678505953202cfe76d913218ebe64d91325cfcc32d9132034fe75d9132004fd75d9132034fc75d91321ecfd74d9132006bf54d913218ebc54d913201cff73d913201cfd73d91325debf43d91325debd43d9132024ff72d9132024fd72d91325cebf42d91325cebd42d9132014fe71d9132004fd71d9132014fc71d913218ebf41d913200cfe70d9132004fd70d913200cfc70d9132006fb50d91320067e50d91320067c50d9132006f850d9132006be40d913218ebc40d913202cff765913218ebc64591325c5df73591325d5ef72591321efcc3259132004ff7559132034fe7559132034fc75591325ccff7459132006bf74591325c4ff7359132006df73591321ecff7259132006ef7259132004ff7159132014fe7159132014fc7159132004ff705913200cfe705913200cfc7059132006fb50591320067e50591320067c5059132006f85059132004ff7655132004fe7655132004fd7655132004fc765513222fcc3255132005fb705513217df87055132197785055132014fe76d85324afcc32d8532186f661d8532034fe75d8532004fd75d8532034fc75d853202cfe74d8532004fd74d853202cfc74d853201cfd73d8532024fd72d8532006f751d8532186f451d8532186f641d8532186f631d8532186f621d853200cfe70d8532004fd70d853200cfc70d8532006fb50d85320067e50d85320067c50d8532006f850d8532006f610d8532186f410d8532127cc3258532186f4615853200cfe76d81321957e75d81320057d75d81322e7cc32d813217efa60d813217f7850d8132034fe75d81320067e75d81320347e75d8132004fd75d81320067d75d81320047d75d8132034fc75d813202cfe74d8132004fd74d813202cfc74d813201cfd73d8132024fd72d8132014fe71d8132004fd71d8132014fc71d8132006fb50d813217e7e50d8132
  | 19 => 0x9542006f970d9542004f970d954200cfc70d95421b6fb50d95420067e50d95421b67c50d95421b6f850d95421b67850d9542034ff76595421b67c6559542615bf7459542005df73595421addc7359542625ef725954222fac4259542005f771595421a5f47159542005fb705954219df870595421b778505954261cff75595420067f7559542614ff7459542006bf7459542004ff7359542006df7359542004df7359542024fe7359542024fc7359542006dc7359542024dc735954222cff7259542006ef7259542004ff7159542006f77159542004f77159542014fe7159542014fc7159542006f47159542014f47159542004ff7059542006fb7059542004fb705954200cfe705954200cfc7059542006f8705954200cf870595421b6fb50595420067e50595421b67c50595421b6f850595421b6785059542024fe76d8d421aede63d8d425c7ac42d8d42034fe75d8d42004fd75d8d42034fc75d8d4201cfd74d8d42006df53d8d421aedc53d8d421aede43d8d4260edd43d8d4202cfd72d8d425c6df32d8d42014fe71d8d42004fd71d8d42014fc71d8d421aedf31d8d4200cfe70d8d42004fd70d8d4200cfc70d8d42006fb50d8d420067e50d8d420067c50d8d42006f850d8d42006de30d8d421aedc30d8d421aedc6358d42605ef7258d421efac4258d42004ff7654d42004fe7654d42004fc7654d4220fac4254d42005fb7054d4219df87054d421b7785054d42014fe76d85424cfac42d85421a6f661d8542034fe75d8542004fd75d8542034fc75d854201cfd74d8542024fe73d8542004fd73d8542024fc73d854202cfd72d8542006f751d85421a6f451d85421a6f641d85421a6f631d85421a6f621d854200cfe70d8542004fd70d854200cfc70d8542006fb50d85420067e50d85420067c50d8542006f850d8542006f610d85421a6f410d8542147ac42585421a6f4615854200cfe76d81421b57e75d81420057d75d8142307ac42d814219efa60d814219f7850d8142034fe75d81420067e75d81420347e75d8142004fd75d81420067d75d81420047d75d8142034fc75d814201cfd74d8142024fe73d8142004fd73d8142024fc73d814202cfd72d8142014fe71d8142004fd71d8142014fc71d8142006fb50d814219e7e50d814219e7c50d814219ef850d814219e7850d814219efa40d814219efa20d81420057f75581421b57c7558142005df73581421addc73581420afac4258142005f771581421a5f4715814219ef8605814219f785058142034fe76d95321967e65d95325efcc32d953217dfa70d9532005f970d95321977850d953220cfd75d953202cfe74d9532004fd74d953202cfc74d953201cff73d953201cfd73d95325fe7f53d95325fe7d53d9532024ff72d9532024fd72d95325ee7f52d95325ee7d52d9532014f
  | 20 => 0x5bf74585521d5bc7458552005df73585521cddc73585521c6f46158552005fb70585521bdf8705855211778505855200cfe76d81520357e75d815201d7d75d81521befa60d81521bf7a50d815201cfd75d81521be7d75d815201c7d75d815202cfe74d8152004fd74d815202cfc74d8152024fe73d8152004fd73d8152024fc73d8152034fd72d8152014fe71d8152004fd71d8152014fc71d81521be7e50d81521befa50d81521be7c50d8152006fb40d81521befa40d81521bef840d8152006fb30d81521befa30d81521bef830d81521befa20d8152006fb10d81521befa10d81521bef810d81521bdfa76d815200cfa76d81521bf7a75d81523277975d8152006fb64d8152006fa64d8152006f964d8152006f864d8152006fb63d8152006fa63d8152006f963d8152006f863d815246feb52d81523277a52d81523277852d8152327e852d8152006fb61d8152006fa61d8152006f961d8152006f861d8152326fb75d81521befa75d81521be7a75d8152326f975d81523267975d8152326f875d8152006fb74d8152006fa74d8152006f974d8152006f874d815246efb54d815246efa54d815246ef954d815246ef854d8152006fb73d8152006fa73d8152006f973d8152006f873d815246efb53d815246efa53d815246ef953d815246ef853d8152006fb43d8152006fa43d8152006f943d8152006f843d8152326fb72d81521befa72d8152326f972d8152326f872d8152326fb52d8152326fa52d8152326f852d8152326fb42d8152326fa42d8152326f942d8152326f842d8152326fb32d8152326fa32d8152326f932d8152326f832d8152006fb71d8152006fa71d8152006f971d8152006f871d815246efb51d815246efa51d815246ef951d815246ef851d8152006fb41d8152006fa41d8152006f841d8152006fb31d8152006fa31d8152006f831d8152326fb21d8152326fa21d8152326f921d8152326f821d81521bef860581521bf785058152325fa76181521befa76181521bf7b7518152035fa7518152035f875181521bf78751815203578751815231efb651815231e7b6518152006fb6418152006fa6418152006f96418152006f86418152006fb6318152006fa6318152006f96318152006f8631815232efb6218152637eb52181520c77a52181520c77852181520c7e85218152006fb6118152006fa6118152006f96118152006f86118152034fe76d95421b67e65d954261fac42d954219dfa70d9542005f970d95421b77850d954222cfd75d954201cff74d954201cfd74d954262e7f54d954262e7d54d9542024fe73d9542004fd73d9542024fc73d954202cff72d954202cfd72d954261e7f52d954261e7d52d9542014fe71d9542004fd71d9542014fc71d954200cfe70d9542006fa70d954200cfa70d9542004fd70d
  | 21 => 0xc50d8943006f850d8943006ee20d89431eeec20d89431af9c43589431eeec6258943014fe76d854351f9c43d85431e6f661d8543034fe75d8543004fd75d8543034fc75d8543024fd74d854302cfd73d854301cfe72d8543004fd72d854301cfc72d8543006f751d85431e6f451d85431e6f641d85431e6f631d85431e6f621d854300cfe70d8543004fd70d854300cfc70d8543006fb50d85430067e50d85430067c50d8543006f850d8543006f610d85431e6f410d854314f9c43585431e6f4615854300cfe76d81431f57e75d81430057d75d814336f9c43d81431defa60d81431df7850d8143034fe75d81430067e75d81430347e75d8143004fd75d81430067d75d81430047d75d8143034fc75d8143024fd74d814302cfd73d814301cfe72d8143004fd72d814301cfc72d8143014fe71d8143004fd71d8143014fc71d8143006fb50d81431de7e50d81431de7c50d81431def850d81431de7850d81431defa40d81431defa30d81430057f75581431f57c75581430b79c4358143005ef72581431edec7258143005f771581431e5f471581431def860581431df78505814302cfe76d91521d6be64d91526577850d915201cfd75d91521d6be54d9152656bd54d9152024fe73d9152004fd73d9152024fc73d9152006be43d91521d6bc43d9152034fd72d9152616bf42d9152014fe71d9152004fd71d9152014fc71d9152006be41d91521d6bc41d915200cfe70d9152004fd70d915200cfc70d9152656fb50d91520067e50d91526567c50d9152656f850d91526567850d91521d6bc6459152005df73591521cddc735915264def7259152005f771591521c5f47159152005fb70591521bdf870591521b7785059152024fe76d8d521cede63d8d526477850d8d5201cfd75d8d5202cfe74d8d52004fd74d8d5202cfc74d8d521cede53d8d52646dd53d8d52006df43d8d521cedc43d8d52034fd72d8d525e6df32d8d52014fe71d8d52004fd71d8d52014fc71d8d52006de31d8d521cedc31d8d5200cfe70d8d52004fd70d8d5200cfc70d8d52646fb50d8d520067e50d8d526467c50d8d52646f850d8d526467850d8d52005bf7458d521d5bc7458d521cedc6358d5263def7258d52005f77158d521c5f47158d52005fb7058d521bdf87058d52197785058d52004ff7650d52004fe7650d52004fc7650d521cf9c4350d521def86050d521f7785050d52014fe76d85521c6f661d85525977850d855201cfd75d855202cfe74d8552004fd74d855202cfc74d8552024fe73d8552004fd73d8552024fc73d8552034fd72d85521c6f651d8552006f741d85521c6f441d8552006f731d85521c6f431d85521c6f621d855200cfe70d8552004fd70d855200cfc70d8552596fb50d85520067e50d85525967c50d8552596f850d85525967850d8552
  | 22 => 0x815338efb73d81531fefa73d815338ef973d815338ef873d815338efb53d815338efa53d815338ef853d815338efb43d815338efa43d815338ef943d815338ef843d8153006fb72d8153006fa72d8153006f972d8153006f872d815347efb52d815347efa52d815347ef952d815347ef852d8153006fb42d8153006fa42d8153006f842d815338efb32d815338efa32d815338ef932d815338ef832d8153006fb71d8153006fa71d8153006f971d8153006f871d815347efb51d815347efa51d815347ef951d815347ef851d8153006fb41d8153006fa41d8153006f841d815338efb31d815338efa31d815338ef931d815338ef831d8153006fb21d8153006fa21d8153006f821d81531fef860581531ff78505815338dfa76181531fefa76181531ff7b7518153035fa7518153035f875181531ff787518153035787518153386fb65181533867b6518153006fb6418153006fa6418153006f96418153006f86418153396fb631815367fdb53181530cf7a53181530cf7853181530cfd85318153006fb6218153006fa6218153006f96218153006f86218153006fb6118153006fa6118153006f96118153006f86118153034fe76d95431f67e65d95436679c43d95431ddfa70d9543005f970d95431f77850d9543234fd75d9543024ff74d9543024fd74d95436767f54d95436767d54d954302cff73d954302cfd73d95436667f53d95436667d53d954301cfe72d9543004fd72d954301cfc72d9543014fe71d9543004fd71d9543014fc71d954300cfe70d9543006fa70d954300cfa70d9543004fd70d9543006f970d9543004f970d954300cfc70d95431f6fb50d95430067e50d95431f67c50d95431f6f850d95431f67850d9543034ff76595431f67c655954365dbf745954366ddf73595432379c4359543005ef72595431edec7259543005f771595431e5f47159543005fb70595431ddf870595431f7785059543664ff75595430067f755954365cff7459543006bf7459543234ff7359543006df7359543004ff7259543006ef7259543004ef725954301cfe725954301cfc7259543006ec725954301cec7259543004ff7159543006f77159543004f77159543014fe7159543014fc7159543006f47159543014f47159543004ff7059543006fb7059543004fb705954300cfe705954300cfc7059543006f8705954300cf870595431f6fb50595430067e50595431f67c50595431f6f850595431f678505954301cfe76d89435d79c43d89431eeee62d8943034fe75d8943004fd75d8943034fc75d8943024fd74d894302cfd73d8943006ef52d89431eeec52d89431eeee42d89431eeee32d8943014fe71d8943004fd71d8943014fc71d89431eeef21d894300cfe70d8943004fd70d894300cfc70d8943006fb50d89430067e50d89430067
  | 23 => 0x6f86218154006fb6118154006fa6118154006f96118154006f8611815402cfe76d9153216be64d915368f7850d9153024fd75d9153216be54d915368ebd54d9153034fd73d915365ebf43d915301cfe72d9153004fd72d915301cfc72d9153006be42d9153216bc42d9153014fe71d9153004fd71d9153014fc71d9153006be41d9153216bc41d915300cfe70d9153004fd70d915300cfc70d915368efb50d91530067e50d915368e7c50d915368ef850d915368e7850d9153216bc6459153685df7359153005ef725915320dec7259153005f77159153205f47159153005fb70591531fdf870591531f778505915301cfe76d895320eee62d895363f7850d8953024fd75d895302cfe74d8953004fd74d895302cfc74d8953034fd73d895320eee52d8953006ef42d895320eec42d895320eee32d8953014fe71d8953004fd71d8953014fc71d8953006ee21d895320eec21d895300cfe70d8953004fd70d895300cfc70d895363efb50d89530067e50d895363e7c50d895363ef850d895363e7850d8953005bf7458953215bc745895320eec6258953005f77158953205f47158953005fb70589531fdf87058953197785058953014fe76d8553206f661d85535a77850d8553024fd75d855302cfe74d8553004fd74d855302cfc74d8553034fd73d855301cfe72d8553004fd72d855301cfc72d8553206f651d8553006f741d8553206f441d8553206f631d8553006f721d8553206f421d855300cfe70d8553004fd70d855300cfc70d85535a6fb50d85530067e50d85535a67c50d85535a6f850d85535a67850d8553005bf7458553215bc7458553005ef725855320dec7258553206f46158553005fb70585531fdf8705855313778505855300cfe76d81530357e75d81530257d75d81531fefa60d81531ff7a50d8153024fd75d81531fe7d75d81530247d75d815302cfe74d8153004fd74d815302cfc74d8153034fd73d815301cfe72d8153004fd72d815301cfc72d8153014fe71d8153004fd71d8153014fc71d81531fe7e50d81531fefa50d81531fe7c50d8153006fb40d81531fefa40d81531fef840d81531fefa30d8153006fb20d81531fefa20d81531fef820d8153006fb10d81531fefa10d81531fef810d81531fdfa76d815300cfa76d81531ff7a75d815338f7975d8153006fb64d8153006fa64d8153006f964d8153006f864d815347fdb53d815338f7a53d815338f7853d815338fd853d8153006fb62d8153006fa62d8153006f962d8153006f862d8153006fb61d8153006fa61d8153006f961d8153006f861d815338efb75d81531fefa75d81531fe7a75d815338ef975d815338e7975d815338ef875d8153006fb74d8153006fa74d8153006f974d8153006f874d815347efb54d815347efa54d815347ef954d815347ef854d
  | 24 => 0xc6258954005f77158954225f47158954005fb705895421df870589541b7785058954014fe76d8554226f661d85545b77850d855402cfd75d8554034fd74d8554024fe73d8554004fd73d8554024fc73d855401cfe72d8554004fd72d855401cfc72d8554226f651d8554226f641d8554006f731d8554226f431d8554006f721d8554226f421d855400cfe70d8554004fd70d855400cfc70d85545b6fb50d85540067e50d85545b67c50d85545b6f850d85545b67850d8554005df7358554235dc7358554005ef725855422dec7258554226f46158554005fb705855421df8705855415778505855400cfe76d81540357e75d815402d7d75d815421efa60d815421f7a50d815402cfd75d815421e7d75d815402c7d75d8154034fd74d8154024fe73d8154004fd73d8154024fc73d815401cfe72d8154004fd72d815401cfc72d8154014fe71d8154004fd71d8154014fc71d815421e7e50d815421efa50d815421e7c50d815421efa40d8154006fb30d815421efa30d815421ef830d8154006fb20d815421efa20d815421ef820d8154006fb10d815421efa10d815421ef810d815421dfa76d815400cfa76d815421f7a75d81543e77975d815448fbb54d81543e77a54d81543e77854d81543e7b854d8154006fb63d8154006fa63d8154006f963d8154006f863d8154006fb62d8154006fa62d8154006f962d8154006f862d8154006fb61d8154006fa61d8154006f961d8154006f861d81543e6fb75d815421efa75d815421e7a75d81543e6f975d81543e67975d81543e6f875d81543e6fb74d815421efa74d81543e6f974d81543e6f874d81543e6fb54d81543e6fa54d81543e6f854d8154006fb73d8154006fa73d8154006f973d8154006f873d815448efb53d815448efa53d815448ef953d815448ef853d81543e6fb43d81543e6fa43d81543e6f943d81543e6f843d8154006fb72d8154006fa72d8154006f972d8154006f872d815448efb52d815448efa52d815448ef952d815448ef852d81543e6fb42d81543e6fa42d81543e6f942d81543e6f842d8154006fb32d8154006fa32d8154006f832d8154006fb71d8154006fa71d8154006f971d8154006f871d815448efb51d815448efa51d815448ef951d815448ef851d81543e6fb41d81543e6fa41d81543e6f941d81543e6f841d8154006fb31d8154006fa31d8154006f831d8154006fb21d8154006fa21d8154006f821d815421ef8605815421f7850581543e5fa761815421efa761815421f7b7518154035fa7518154035f8751815421f7875181540357875181543defb65181543de7b65181543eefb6418154697bb54181540d77a54181540d77854181540d7b85418154006fb6318154006fa6318154006f96318154006f86318154006fb6218154006fa6218154006f96218154
  | 25 => 0x600040000000018014002003001800800e0010008000000009006001801c00400300440020010030044000000002002c00000d00100080300050000008006006000800002e000003000401000200880280000130050024008004001002400000000c0000008003000801000000f002007800000200180100060060060004054047002000000800900d80840180010048004000000000001800000e00080000400040010030008004000005c00c00300a800400c005000003400c0010008014000001007000401800100e000000400100600180000190018000002000000801403e0010098000034011001800c000012000800401a001008804400c0000018000008001000000c00c01d003000804e000012000002a0160010000000000001800400a004000803000e000000800000000600100000020000008098022002001805c030000004801000c004004800c000000000000401401500f000400800b002000000e0060000004004027000800000c0090020000034005018801c004004000000403000400000700040010038004008006002000002603200600240020050028020018003000000400e00900400a0010000003801800800d03800000380060008000038002008803800c006033003c01e0240010000002000005000000600a0008010000003006000000000800780080060000068000008008000000000a000000000800e01f01000340200000098060028000001801c00e008003801000c00b001000c00200000100040080000008070000015000800c01e00500f000000c002002007c00800d0040010012002003005802a009000000000601a002000002602c000000801c0000120060018000006001800200b009000c002009000000004c000000000000201000000040080030010000004009024fe76d8d54236de63d8d546877850d8d5402cfd75d8d54034fd74d8d54236de53d8d54236de43d8d5401cfe72d8d54004fd72d8d5401cfc72d8d54006de32d8d54236dc32d8d54014fe71d8d54004fd71d8d54014fc71d8d54006de31d8d54236dc31d8d5400cfe70d8d54004fd70d8d5400cfc70d8d54686fb50d8d540067e50d8d546867c50d8d54686f850d8d546867850d8d54236dc6358d54005ef7258d5422dec7258d54005f77158d54225f47158d54005fb7058d5421df87058d541f7785058d5401cfe76d895422eee62d895464f7850d895402cfd75d8954034fd74d8954024fe73d8954004fd73d8954024fc73d895422eee52d895422eee42d8954006ef32d895422eec32d8954014fe71d8954004fd71d8954014fc71d8954006ee21d895422eec21d895400cfe70d8954004fd70d895400cfc70d895464efb50d89540067e50d895464e7c50d895464ef850d895464e7850d8954005df7358954235dc735895422ee
  | 26 => 0x10048000000800402a000001000a0000030038018025000800000200a00b0004018000016001c00000f000803400a0380070008018009004803000e01d002800803000b000819c000000000003400002300100080060000000000044013005800000000e00000100020030018070006000008000000e00000180480000070010000028000010012c00a0010010000000000003813000a000006001c02402600000000000000000004004001001805000c01d003000402001d0028000000000000000801a006004002404a00000000140280050048000024003001000801200000000000180000008030000000000001805e00b00d000800000203e00000000040000020000009007800000000301e005c00000200c800000400b002800000201f00080040160040000008002000001803800200b000806c05000000b000c004007000800c00000b002801000000c0020038006002006003c0000090030000008000000005801002a0060028000005000000802c005003000800800000a8004002002008801c00200500100040180010000000014003008800c0000240000000036000000003400c000000803403a000004801001401400c002c000000003001407a01b001801800400a001803c00000400202100380010010014020008001801000c000000001800a003006800000a0000000018012000000000000800d00500000300130008000002001008003c00000000d802c01c00100900000020010108014008020006003401200000180e4002000005000000000303480ec0060010020000010006006802400600600a800000a00d00780800180030000000030001004802c0160120000030012003002803c01200002900480020000000018024000000000800e00000c8008000000001801801a000000000000e000010002004c002000805402200101680000140160038008000008000001000400000100780020000038028002003000001006a018002002401a00001780000060090058018000013000000400600201c009800800000d005400000600000000020040058000002001000001801200700380080240140090084028006005003006a000015001000001100f80000080000090080004011004000000e0070008004004000000800000000b00600000140010008000008003003801400000101080740060040008000042024000001c022001000002c000001008002402e00200280100320000050000022000003003804602c007000800201c00b000000600a002803c00400e002803800001900300080060000068030046016003000c02006b00480380020140030000004002005000c012002000802000c015004800c018000004800000200d01400280100030010010000015001002c000004004800c00c002006803400200100
  | 27 => 0x5c091000019781c42131d103780a287c695b06618d8c80f0f027f58e36255919800016723b309720a2851a0491a4c4c117485530e8a33b21548318c243e901c26cc0aa0011839858913e641294a87720f54598130c1e901d42c613e84959cba3a780002f7116260407ba44b980a2b2971a19f858239193d28691c9e08c14dc62f87c405186ea6418d9219200fe0a085da0b90546000180817f045c1db9514555862665e850048280001c21cee1408a9862696c26c3000071605a8000062c81920a6000000000000007b903f00b1829062e8830866a1ca1ab9fe030782fa00000cc8381ec83ab80001909890428869200000000bf9c780001b22106989200005d453194e04b4213424d17603c61edc700800081180002a39a7e000000073b00000c49e8e00b19b460d1ddc1b08f664690000000102857e029e2790dca35380006168e702141d980000000000129a00000000000000837800074e9fc45830000677800039600000001da40000258473000200200000140660000000000000013002800400e007007007400801b000000c00400d0088008004014012002001801d0018010004000001000800c00300c80040000000018000002007000004000800d00080040160050010008034055000806c00601a00000b0068017000001800200000180b0036033001004800800d000000000e0280058034010001010000c004000002000c00601b002000004e00600500580140260000030000000000805c01600e001000400000a0088000006016000003c000004000007c00e0250070014000001008000001400500080080020170000050012002001800400401e00b8010056015002000c004001034000400200001c800000000400180440000000020014006000010001c000000007000c01600800400000060070190004014003006810c01200000600040200000000028002000001802401200600080240020010008020018000004804c00a00000100080000030000000000016000003002c00300000000340710010018000005001004801e00000e0004000008001801c02c000003812800a00e000800401c016002800003c004003800c000000000000001e00f005004800000001a8048000005000002000e00b00580400060360008020010003007001c00002d0040000010006010800000000d0010028000000001800c064001015801c0380010048000034002000004400c01700580080060020058014006006006800c00e001005800002a0020030000008001000800001c000004801c018001005801001e002002804802200600480140000020168008002000013800000c014000801c00200500d0014094000002808c00000b000801c0220040000038004000007002400000b004002400e0000010000004003003001000602301300400
  | 28 => 0x671fa24929ad65421e7e7258cba5ba154e5648f3831200f67ba1c04355992a843036686c985e4f09eb2319a17a34893361b29ff432404da28a87006e183384ba874c2118000068204e60a1426609144c5a6952c74286627368000000000034b999c698058e4341a6c7f18f100f11c5000013ac39782967e000003080d6c2380cea1a9860a0001ad234500002aa813e5388f747e497be1f199003611e7800000005839b9626521102b40744000194033582662f887740df0a72629000045500000001b90048038e0b6800070b80006f99552000066a00015d2544800000017b456e80000000a2680d0c6e0001e4a74e058c13780000001ef67f68df200000007a900000000000224042a1fa92c60001eba6590dfa000073019b0f1c4da112a0000000000000015c992400009d0000000068619224298f7e01100ec3860f407e39dcc24311d628b02023ee80d000000004e0846a41f913212a800852c9ff00070d2a3bc871e73d90361bc9db210f900621c9bb041386ce80c1de22fb1d0c6de80567cb06083ea9236612825e00021587a5975442a93a47c312465fc0cfc20020aa8048bf4719172a16b86b26840a105e412bc6539a00632206c3e5865017982927250638210112c3c01c8226f94d61f006545ab209486807587269e66299934e38912ee63102ae48e80fa3c11bb444609147bd03d061505c6872184604280005c804424d208181c11fd828f1fd27501c5e59511661d3800034f89264f0175c73c059211e835471511b0311890a3e98f3078e9ebe0639e1c028877e5909cc22a280008558c366ad8f58000200867b9b4873204d20478cd04968000530910c65f9ec46a004e66b08cb802c81de5b5164870215a81af18321fd0afa78c0f460001ba80001d6852a9e5c2c700003cf202c01488f40000a383aa00007bb80000000e6a000038a06885bc34e8f9c2e78b880000c4c4dd000000005d865a8000000054200018002fc893a1a61c2800010e259f8b4e0f285f85a00aa43a1177035f14444c51e90000088606a08940a91c146e804d8676a0745f913927711a0a64e9d907f2836e11a100219380004e3851c23b80001b400000b0800056fa06212880000000000108824a4ec0520587882c37d80000000ad400010ca58711605c5059a6c000002ef1a3811680000001f763fd8f5000001e85c4991221b00000759fe257a8d60000000083980005e493546688a9077617b872996f662204f83b09a325f0064c68497ec69a908a08618fe1da0c403a606d20280c0037f81d017d97a01b000007ff1d9a417000024792b282705a451402a81f69e9200000aa3eb1ab400010d61260d800fb9d2a6d407600b000000001274258842864d8fa00988b525cc80002348132208000000000007b096c45b9955e1091d14510964480f909e44d853c2c50d
  | 29 => 0x64466f121e22a1f0a59f13da69780006181f6a000000003f108e7d1803e5440aa28519b1639da1a2000000007ca0a44b90eb02660cfe7b887066d00e1c1000cce64e00003439126603000000005944cc0942393000035d83847459f7a43b09c83fd1afe7c20d98429102c81b940e4b29dce7158fd40669666814a1405fa8b6e7a61fd000000007ea986400021327289674823880207901e078780000a50000000000056901a67a195b848f85b01cf00e241ba05653100f467b101a68d89d65338eb681d912061aa01680291b678019e62810d0663f216c30d13d008281880ff0bf83710bc85d009e01579872543985214281ac7fa10724be9afa612055410214a20ec04be25c0a061be881a09f816c6ae8082369803a42b94ec5249b3a7b019be2f2907c2d20d460a980f045c130e04e9d4a2c010ee6ea8f343f11f1e0001b0629b09ca6ee0a783e312a6145a16e7e50e5644794e43309e2829886c813a0a9255e05b81678000295818a2ab047c0fd00003159af20409f6c74a1b9228c89a651b089e3300a20757074804313dc790908682418580591e622d98000401179c00007666df9ac653d0b741ee17181031bdc00000c06fd8000000106000015980001d3c47c0fb059288fe358800013412ce00000000001c4039480005b817003b600000438a500000aa671085ec58d0d6828b80420000780375800000000000001f785419b58000193c00012240000f6027480005571af804600003639c76000000021f80001b71f2427b00000dd800008480007b989907e199e807380004d71cac6d49e884b883a218585a67001b28354154a0ce96621cfa13e38f835c0ad9110000000000010f838200007c11c8e42100003ca8000000163a0ba12f813c027000006344308000316800000000007421fc20000dac3708000000063e4f19a145e61e6a654155411399104d9128820914ea0000fb246e87b65f48af655680004ea17b05c700006368d966c799c63ef9d640c38bb05d6913c8151e081a791be0c1049c23d8eea5c407ce1521eca2830ed6101805460782605c2937e683a06826d16c632b8ba800107aa388079421081cc0ea187006d85c27c09bfe2e98e6600003bc05e9fac07c1c1c162846e49505c850b9df60000000719904800002d82b000003200000498874685c93fe00000006ec958e4e68ea0816851216d11243c39e0c00017567cc80000000000648000000d0000064189475e87bc0001cde3830fae6360b3a58084c021200007778c7c66002780000c0800020ac28d82280001a745da15ae38c9c7c83b1d0054a1f500cb14388060d0a3098a0e207947a0221adc3c5961223910f02d30000326881033720fe840075022c8ff8721194a1710bfe7b513ce0000ea61a3a0e24ad17221c80000000211231080d87e70d6613b08364038e288
  | 30 => 0x5d38db800021480eb0b1250a096c85d97803b2848c000071a679091a10418a64c8996680a0aa8000000024b965a64f956624e11c0367948c00013b44459c2a0000cd8705a04c6fb000084b0000000000000000000000eba79e8cc80000c0a00013f882c1ca85e51d220eb90540f880000001d7204d89882a505646aa132a84e9dca0ca96f4000208a000002e000202e3fa80003b4825a0da00ae000011a01288ba4ca0cde1561d5802c08ac00c80000598000000148e11519426a9000000004361f5199e000027600004ce1a71daa7418ada6d680002df00005a2147658a19fe73f07e2114a07a00005de685846231d80008718000539a1b06c381720000a5841a8372000000000000004a8800039e000015b00006b7a17c000115600000000001de4000000039f03b40000a5a000000005f800000011463a09aaa0000c04123898a368a0e4621000049a8a1c31e8ea20000000000000013c91ee3009c1800015905361fdc32383203bd80007c1998e7c60ec02cf1dee0ca03f81d8968e0001ece00019704f8090e756800070991c842000002ed00000001dc0000140c30a975242200006bc190e6e10d3800013fc00003fa000156e5c783220001a4436f807e7dfa0ce01008cc1ef8ef818c891c000169078e0ae03140de25ca069a0a399f21f999cc5f11b2459600c661d000042f11c200014ac6218de40dc0eaa31801a40c089b015a1ad430514206629e0a23c90787c380000578000006800000010f645d80007c885f453c1f4a29a945664b871434812804b710de1d082be2f915180a205be01995e23fc9c0626395862d08c7200017cc32d21824a3000077c89dc11900006da979a34b0000000045e00d80002738f9a796000014b924427982466111830084021c869847e82080002809b662f303d2373827a07e91962329a8e19901b26fc07cc1d799265aa05ac1d59dd062c114a1199b4a50684587f216bc7471bc82ed95ca4b989bc7fd94ba81e0b304eb9a6835508ae380950a809826a4d6802677a03e666c04c810384406c206c432a970c53a0e122869278442109075492b81281b2c53c8924795050c4f505fa04b009c261168c75b96765651dd220191f205d0a3068705520b1006004486961c5943e00017b640d1946065022c5f5000039e817600000002058d74579800034680007371eb85a8068468a82241c388e67598d4c0c5a1ae84c14107128a5c70f9ebc34a02f46f1815041b000054116145600738824800059300007e08ee223417c245a00001ec04cc44d04e404b800000008fa4f213bc4058a6037a8bb81fc18c00001c2222815f2000035800016c058c090033d000000019ea000000083f07966db0b2858d8bd23ca079224596563ab0fee6a08e4a1d91c9c3df04567189f563ed977c4110c1a3c28000548000073f80005620
  | 31 => 0x67074981380f0800069496a600007127718d08617156c1c6182262a19ac28497ba3178f0c04d05ee219866e0000000000126e84d93780000f1e2ac99d619c913a0d0113843101281bb92921e99e9c267a13876d9a7c41d9ac882d018064c98121d7219440402b829f80000001bfc00005841de000000003426e980001a5010600011f446992f02bb94ae81a8000786067c76b0b10733000033a190c00006c67850fce198079e00000007f0182646400000f21b3c6eb80dc000023640e9ed000e1bfa1870c682d106103e111e675c039069180004538af84c4078e4631b9e00000000000666673827c1d2820061d853252f00008528c0e74102e067880000bc02143940a4e40c0e38000148283e0b5840e1d1e0001f38805000040797862308d1857d8c4e7bf1a966bb8c8235e804c6d088ea0001fb81fd80000e7887a74d8ae22f080005ad1c8a2f1933241012d45b91d9c4d4141854312a807000bc3671bd211e18e25860d100a0160800012f40fa99fa0da8df08701d6a13710ea56580000001ba42e5800005c10ac000124c1eb20a800006b84fd87220c3168a2f389103d91e5a6bd8a3a36d9ac400000000c19d4813809063b50e1a07b0bd814197462671bca59400005df8a3e7fc9d3239880622d0000044a01dc0001f8455e988058f882e0000000172981a3e78a0a2ad903233c897e0ff8f4c3908578755000c33518ec2751aca50c84a86f30ad6526882a42a18f41a9123c0820e0015d83e82d70b0e83516845e29f005ea03aa3368ffc79d81aa2da91a81bf00000000f780a18d0079f203867f169210f072a034837a50f1a6654e9aec5f417a275783b66c08b20770855a19e80007e98e2a59917504db1e9a509085c00009ee7110f6a4d280006fb8e9262784fa0db06f421c00000d597a60001758178a070655868a0000000000133a4df0f2e2b491802689c8878582748178b32487057c3f09b1c3cc8a6e0c99478035811470287b20000b5a0888ac28008b3875d95ec259000017c84ac60b8cb6327a1023d699f83f3079016c8000591a1707f505ce78880001aa0f082e315685f7878812e16fe4ae8ae43430514000000000512de0000f828032184000028458000004c180000af00000000000804037e6e29b821eb80005bc0c8861000a86f68000203801253289c672d95b21af8d7e000000059a81625211b1854c881c5cf8db277d05d00498f441351a4a0000d424729a2c09a0c125731aa656289662a688de000118625e983e6749cea61e80000000e960000000000160a48d0ab083c0d8837d101259b12405c380003ed162e13aa0506cd9dbe09310be20e1dea29305c027d000016813902760000466878442c810427f01d208e020c16612322d7806a0fc8798000126035c000027e20662681f8818f0522000217400019c206b8000
  | 32 => 0x235c8e10723064a2ba9eec4b00c321c918040279d20713894c0d7a01e75815c87a500008458ce26901bf88589318273071c45b80001f28f4a45a84c641999047a08f2445e03503cf9f207b60a187558000173103e2548f562e600006fd21b47d893263f6131c54d14f84971dfa1f90b2628898e46e01c24000031876880006e31e728268646000000064786580e080001790fa83ef06cc02296060000000859016a21589fa0001a241181536032053812d959a64d00002f10adc03a919428780000001e465b594b40ab207e2410d5a37018ea0898a7a4fd0bd40261c38033a0f42460e8058f0dd43b9165c7f39aac2151a0205094086f021a829a151c7c486ec0f9007215313600001aea61389e2000188e4021b9c63c87c87649ce8372123851202a02320fc0000000000019ae57a10ce14780002338000000000003780002fa99a85ae90f2866000043a00005dd92ae4d893ca18ea1b8471153c485860234106d45a59b342929f6e5c21e8a6328b7284218362dc19f005214b06a71c6c40307ec16a938624d825600020060d89284000000029c0ac43d38000260088e000132c195934400000005c900001050bbe6199f5a19d18ae476000011197f80ac80007ab0d32000043481704320580a7c72003ba78395306ac822e0001a886a6207c000000009c9eae40000000d10c3862d92025340844000053e2540f527d7006821e1b385678edc32a1aae3288ee81df09da49099680238e260fd80006f89e524719d027ef20da08392765af92e83c9835268b9e2400001b02f992a4314978c0000b568081a5c05006e44868000000000024a217e00013d60001bc4329800000005880001436430138839b997812291ec0c21da00001eb67931ef22560862000162607210d229011fe1c99ae01948bda42da15c0001ada29901686cf807455901ca3510d9020a16ee3969f5e4a780b46d70c1c4bc800019e0000000126c0001cc66ac04a44568c9663b98f60000dd8000000046881ee527000076e8af278100006da186c48a8d6e6a18e04000006e72a80000000b603a7017c76594343318abc605043060a8c3a6908a9e26e1572837099239d154863a13f063521905938e340000dde3a304486819962000000079111581f09c1e69580920000eb47c4000072c800048c16f286b10b850098ce00000006f7800036a837800000000000f80225a1bc2e89b325229dfc8120000000007816186227388ce62a0128e265893e484000248a174c49f1184014155026a028c82180002098330000084a0c2a1c45a889400f81b0a186202400002ea1501a9430320be1a810e66b419ba7dc00004a29c602910e44438043826300007dc8000526109249200d400011140000eec7ed0efc1131a7a1f714be2e115226b3216a29d144615f935e3db95407d6200e1e098d041d
  | 33 => 0xc8abe73c8dbc1749e2031f8a2400012142ec9b207329e3473e1ad86f60db027f805e0ad1d8816d95ee5709f266a29a9e1e89a642e01bd461089764141f9a6b014a483584902cb887465d948048382404a580006131f341688b0c0000e0620e836011d9e401c280007dd03487ff9b567f90fe80f30090316168675086906e693846578b4a500183840913ec72f9560294852805280007bf8cf86d195627e920802e190945fd204003c8af43f585801060c9200017345f59ce055d0676285853680c879a661115024c20a25ce931e7fb835a5b40d4a56319a47d1000073013a2000000017a187c24c80da5689e6c789834602d8a421a01d6c0f6040a64b0000000002200000000161ba2000000063c01d822880000e1955825e18b800001c6055a17815a82b02ae96d845782f60000ba049600004408bd62e700006468baa22c1eea59a142c0000604848197208c91820001cd01a18afc00012fc1b8138a84101307cd903c38f00000cc8f7a5811982185001e6648e0a000195a76c00000b480000001c86000135646a81783f7885e55d80be5f289b684b86f00c78d1e0f000ac22d951e670157e2a1a15e3d088041cd81220b9856657400001d502a23a90000551000000010204c59e2c6d32186000026e231800015711226b99dec03105d6178190845f9ee069c90420cf136e16e96b834f0d523c510ba1221290423097c59e13e259b80005b21b704e5117264a11e42b20d8255a8c8610e8688683056250890fa822204a2de1f280aa990a71a145a12001fe3a210524d1853029795f42b980007c589f221f0094512889a2da1c1a4cf14047aa113e0000ebe00020446dc83d446787f20000000000000009080005cd9d820869b1468f01524da915c5f8800048600000001ce407a80001f4800061e211400008687b31524000000073e95a6067125044281006381ede38c18fa3f88fd0189199a7d984122919cce453059c2c18b244520f88000191c873195232c80205dd05246af169c73592081771b7c0001f2a82d8b6437b9b6008d00002cd08a683600008231c0e0e69358603994c2850c2c4649dbc2260cf037e0ec8026988c1819bea0000000000072c1b693e469221b61421aa23f4983c62a845015b80007cf9ffa1ac00007c519d03c69dae2f4029876502d6000000027017e638b98162b316fc00010b02821a267d31c701e1800046712d26e20ed00001de6736122c1f4000030400005de91ce4b09ed255c0860446841635607e86260aae2249bb667d153814d17305fa0b90000065a3d7800071a8cbc18013f2000122e2089cf47be18c25e2052672f145466e10fc849896e68d02541659fe656d9cb8222826c326211a7978ef45b7086e47a01be000000010700183089b5e2778570597a022013800033e94a615e8dd007d8ffa067a1281b59a2
  | 34 => 0xf687fa570000055091b431896ec00a8e5c3f802520000ce41cd0f3a03a00004e700005fc80002fc015839b00002c780002c080005611d1800006f800011404d309600000efa3c18ade7ac00002ad1a70000000000000004ef8a3422f97ee7cf12fe6de19942f814963f2905e6461e8c6e6151a7be9d4e3e895fc590188a55f03a6501a0cc11b000005b892a18680001269d340258000000000072800000e311d2000034e65103b21580f1225221960290c283fc182c3d200e04b69818000000030582ee6f095bc26c8b226081e3e42802ec7399c484bb141e00014686969c3a82b83142d4146266812aa000000084f0b7631d1be478a9c9270c04f64e59df810b82503850000846086a00015824050f9230f80002920ccc000126851b800039500a63980d261de800000020b800010c800000005171e1a00014fa00000006288d362b38a541f5a06082f20ee5f205fe7cc0fc831e133e18d9b2e44111d47ee9cc44fa86683dc1c6e71f800032300000be15d4842850e53b888c00c13a662b1d842c211da7c704d60d91c7a64507a846b1e060b293c4862885a36a00008630b3633498f80b41c9001210b41a08a888508e4e7d809a465b98b40c68b7e6a103ce0001370695052a41913984b309200e00dcc55191423f91b8e5ff202a63188820bc896a3fb20983061c460000000000079c2fb800080000002d500003b39a305f3976c70480846728ddc5d080000001a4e00021660000e9a6158b820a700004a7000047a800000015dc3ac8000000000040a80007d000004511fb00000aec50e861e663023c5d999742e681ba0000000000152e7a80000000122206301da5c591dc4c21d7479c0b2c08e92a00000c7065208124fe9e023e3800000000000000a9600014f6474000000012d67ea06d80001f9e6a6917463983a020f00004189cae23b03de5be9c1001c0de85778e720d3060c43f97ae392094e4a1a1502618ee06760192053a1aa586905805709682a113cc84389ae84703ec1ed214479b82dc74699543408494436800002e8d8600016ca4c089440000b1672d2122399133400001f418b80103bc178e00000004b607a0019062072c201c2ae00007da1fea00019980001e7442684ee7fb000041e8000000092c0000e8e3380300251800062098065b888c485a1e3645e82d43e29a3a61b8f683dd9e800e90c545ad99b627c1f96534995825714407a78000000000050a890877f8864112952a00017d8000110e042153e04704047ef9b044789ed67e803b834480000000000696139e83e9c0c792021e80e889c00000003e197847a8849e1b7a14e18a000086e85180001f8a57e92be58408e283088f02eb0d308568f725881b4e0ef9ec65f6946001f1dd40dd14d415580ee1539a28000000017a95d84d0800071c8006000081400008aa62
  | 35 => 0x3880168648b8a74916ce2c2883e5ac127a504962256811a020200001249b2a8621b101a8884e35aa12a56a9470000073a3f988d84418f945de07ee463853a23707fe44719607780ae800004b200392001e30e1e00000001f786ba7d0a1c2402833442600000000d164f780000200e9075314da76295f03a188e800900003d8800000000000000ac67e6076a0618fc65b798503ff96163bb99b253211ae00017aa53789f60c900006f5a0725ef15ce35e1fde03920966ef00003cb167004409ea0329a8c0001b7436b987e24f1c741bf80003af1da8000197c3b18d6478b8dd24dc9f6470c80000609fb667d88b483417fe000204268209e839006e643511005f184fc4fb99d45d78cbe6a49ab85db908212d162c221000a4371d44000215279809c4000000084793b66f38f3600000005b68af000020f611d125e0000000081000075180000001b9447e80003d700002fa0000000000000000000000000000000000000000000000184948600010181ba09220230e94000102269da03675f1c5c5250000000000068807762ff12c851f00b81cb8000045800045f000003982e22e901e600014fe00014a005317a41d00f6c4a51ea600002ce3b992f682100006b882c86878000505905a5be101c20288d60cb9ae82ee9be8489803c1ff0d8a10b052c4ab13b85a50484411938c125860e6a420ca000189651900002d88000793907005106b4000135213f95fe1511a3e00008da00019a653f1266030970623e0c6c7cb84ba784909c5cb10f47f30cc443616820b78cac000000069b9f7c0f589aa6af96aa7639e565eb080c26b16cc6781e6482e972e00012823128000055033e0938000000000086380002a080005759d3e4b101b4000000000004ae00000005c9952600000000000000431800000013ba1bd80000001ff833d995c5c084b0776a0ea1cc9b643500f226770394000076c769800066403c600000000000d9a0001e502c68cee681132e5fd80006a8000000000000a6983a0d288585b49db41ca0f98514831c1110c9c758805c5a60c84357a0c04ad8a763888c4408180004de800075e1f3a000000031713a082784ca52794144b81458000218000000000000000000000039f9cd264c0b3e76e0ec432c14b67e4000057813767439fb246c812a74c0a0000007d837f1ace1e297440000000000186267201965a918d262711bc7169eda46213202fd946a19007100c402484a60bfa66a8c06000022a1d688b86d8911240b9afc2579e1007f0d1c409979e6009b4475414747eb9472477868c70b1eb44e0041e4849eaa5ab9a7878c88882f017726bd005a7600000481800070d84c23ee131274b0e2c0000db413d09c200a178263587700cd80005f800004d993380001e684258cca379800000020e847e0e0e488120c4590b0485800006ef80
  | 36 => 0x2b6132477c1ef001e931a2ca9516729174a4ea94b8240a0a05240a9c12f1b761008ca078f0e683f68834640981c83c9bba58e0000000144e46e075270f1d7e0000000000124e831162a6f814cc0000dc60000efe62f04c45ec8832735159c0f712700000dba5c10eb80001d1232908a43e4000005680007d48da01f81a1a6c4897408f95e438e82208321a5011c969e841842000001f850c0000763127241a1b2630f1ae43b780000001b1a000000049f8f2085315b41ab095a0001bf24629152000130a4c00000000055031908fc000000045b00000000000499039c0000c94665913000000001dc98a058c9d2e502865c2de97627a108c063785106621500801196c5070392109a01a00007f81b89bac816173c1299c4c76780005f700005ac8000522150234912b070d04860610b920990d4800017fa7d2087651f80766989f8c34d0bde00000006f4173808590e43b68dec5da95da22001bc1aa859072612048678000000062a31a800063700004ec800003e0000000145e00011f62148afe56b1b5441310cc0bf19160e20b461c098cc5ba9f5417c18687d397960000da44d000860000c8a6710fdc775899a0e594c0376870c82c8b6c1ad976415281b824489ba86f95c62e3894a30c01987149d8630b8574141025c38581e20ae96521208a8c04f063057111fc59ea0d22eb946611c098222f006c8491c204f602cc6db8000494905625511e02e500002350d941
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x87f855d9434400d0f90abb286880022fe117650d100046fc1aeca1a20008ef825d943440071d904bb286880023de057650d100063c282eca1a2000c9c431d943440018f0a03b286880038710f6550d101dd3d406caa1a20558fb805d762440031f100baec4880031e14175d89100063c282e9b122000c78505cf62441afcd0a1a16c48835b9a14332d89102453d42ea1b12205487c86dd562440010fd0fb2ac4880030f1d365589100062e39ecab12200087e871956244001878e832ac488003171cc65589106ae3db80cab122000c3f65dd16244001878cbba2c4880034e14374589100062fb2ee6b122000c5c65dcd6244001ab0a1b9ac4880063ea0375589100343f43eeab12200187e80dd562440018f501baac4880061ea0375589100063cc06eab12200187c80dd562440018f0a1ba2c4880162fa1f74589100061fbaee8b122000c3c75dd16244001c70a1ba2c4880030f94374589100061e286e8b122000cb850dd16244001870a1ba2c4880030fdd474589100061e3a8e8b122000e38501d162440018f0a1b9ac48801237a1f73589100062fbaee6b122000c5c75dcd624400193ee9b9ac488003271d373589100072c286e6b122000c5e50dcd62440018b8a1b9ac4880033614373589100062c286e6b122000c5f751cd62440018b8ea39ac48800327dd073589100064e3a0e6b122000e58501cd6244001958e9b92c488003331cf72589106a734286e4b122000cb474dc562440019a8e7b8ac48834f9c143715891000c7d43ee0b122000a7a85dc162440018f0ebb82c4880023ea1f50589100fd3d42ea0b122000c7b75d41624400d8f0eba82c4880032edd350589103e65c3a6a0b122000cdb73d4162440e39b0e7a82c4880031e14376549100063c284eca92200087f855d9524400117f08bb2a4880162f21176549100046fc1aeca9220048dc835d952440011f700bb2a4880031e14176549100343e428eca9220018f8801d952440018f0a03b2a48800e1fa1f65549100353d406caa922054c7870d9552440051f50db82a4880065ea1770549100063db2ee0a92208dc7865dc1524400d0fd0bbb284880021f61776509100063c286eca122000cac429d942440018f0a13b284880021fe1576509100343e42aeca1220008bf845d942440011bf06bb284880123720d765091000477c12eca1220008f7815d942440018f0a0bb284880032b10876509100063c280eca122000e2c42d9542440674f501b2a848801a1fa17764c9100043ec2eec9922000c7850dd93244001998653b264880031e142764c9100043fc2aec992200687c855d9324400117f08bb264880162f211764c9100046fc1aec99220008ef825d932440011ef02bb264880031e141764c91000666190ec9922000c78501d93244001c9865b2a64880be9ea03654c910
  | 1 => 0xa1b9ac8880031614373591100062fba8e6b222000c5c751cd644400193ee839ac8880039614073591100063c286e4b2220038ee87dc964440018deebb92c8880031b1d7725911000667b9ee4b222000ccc73dc96444001cd0a1b92c8880031b943725911000636286e4b222000ce850dc964440018d0a1b92c8880031bdd47259110006363a8e4b222000caf741c9644400199ee6392c888003331cc725911000734280e4b222000cd473dc564440019c8e5b8ac8883779c14371591100053d42ee0b222000c7875dc164440011f50fa82c88809e9ea1750591100363c3aea0b222000cdb73d4164440e39b0e7a82c8880033adcb505911032674396a0b222000c7850dd954440018f0a13b2a8880021fe1576551100046fc1aecaa220048dc835d954440011df04bb2a88800e3b20976551100047dc02ecaa22000c78505d954440031f1003b2a8880031e140765511002c3f43ecaaa22006a7a80d9554440a98f0e1b2aa88800a3ea1b705511048e3c32ee0aa220558fb805d763440031f100baec6880031e14175d8d100063c282e9b1a20dce5850d0f63440018f0a0b96c68836f9614232d8d102653d42ea1b1a200087e87d956344001878e9b2ac6880031b1cb6558d100043f438cab1a2000c3c7419563440018d8e432ac68836b1edc06558d100061fb2ee8b1a2000c3c65dd16344001a70a1ba2c6880031bd977258d100063632ee4b1a2000d6850dc9634400d0fd0fbaac6880031ea037558d100063cc06eab1a2000c7850dd1634400b17d0fba2c6880030fdd77458d100061e3aee8b1a2000e3850dd1634400187ca1ba2c6880030f1437458d100065c286e8b1a2000c3850dd1634400187eea3a2c6880030f1d47458d100071c280e8b1a2000c9c74dcd63441b3cb0a1b9ac6880031e1437258d1001c7743ee4b1a2000c6f75dc963440018d8ebb92c6880032bdd37258d10006563a6e4b1a2000e6850dc963440018dca1b92c6880031b1437258d1000674286e4b1a2000c6850dc963440018deea392c6880031b1d47258d1000657ba0e4b1a2000cac741c9634400199ee6392c6880039a1407258d100065a3a6e2b1a2000ce472dc563441b1ce0a1b8ac6880029ea177058d100063c3aee0b1a20008fa87d4163440474f50ba82c68801b1e1d75058d100065dba6a0b1a207ccb874d4163440019d6e5a82c6881933a1cb5058d100063c286eca9a2000c78509d953440010ff0abb2a6880022fe117654d1002c5e422eca9a20008ef825d953440071d904bb2a6880023ee017654d100063c282eca9a20018f8801d953440018f0a03b2a6880121fa1f6554d100353d406caa9a2054c7870d9553440051f50db82a68823f1e1977054d100343f42eeca1a200087d85dd943440018f0a1bb286880032710e7650d100063c284eca1a2000
  | 2 => 0x17650d200064e218eca1a4000c78501d94348001c3887b2a86901923ee0175d852000c7c402ebb0a4000c78505d761480018f0a0ba6c2900031e14173d852077f3828683b0a40eee7050cc7614808f4f50ba86c29018e1f21b75585200043f43ecab0a4000c3c74d9561480018b8e7b2ac2900021fa1c65585200061e3a0cab0a4000c5c7319561481db8f6e032ac2900030fd9774585200061e32ee8b0a4000d3850dd161480018becbb9ac290003171977358520006ac286e6b0a4000c7850dd951480018f0a13b2a29001a1f214765452000c7c400eca8a4000c78501d951480050fd0fb2aa29001a9ea03655452031e3c386caa8a40038fa86dc151480032f50bb82a2900031ed97705452045e3c32ee0a8a400687e85dd941480010fb0bbb282900031e14376505200065a20ceca0a4000c78509d94148001968823b282900031e14076505200071a20ecaa0a4027a7a80d95414800d0fd0bbb262900021f617764c5200063c286ec98a4000cd4319d931480018f0a13b26290003350c4764c5200063c280ec98a4000e5431d9531480474f501b2a62900030f5d254d95100053cc04a9b2a2006c7a7095365440018bae729eca880029e60253d95100363d384a7b2a2006c7a7094b65440af4f301ba6ca8806b1e9c274d95100063d382e9b2a2000c3d741d365440a94f5003a6ca8815e9e60074d95100d63d380e9b2a2057a7980dcf65440338f4e139eca880031e9c173d95100062eb98e7b2a2054a7a801cf65440af4f30039eca880671e9c073d951035e3d38687b2a206cc7a7090f65441d98f4e021eca8815e9e60372d95100c63d384e5b2a2000c7a705cb65440a94f500396ca8815e9e60072d95100c63d380e5b2a205ec7a70d0b65440bf8f4e1216ca883af1e9c042d95102d63d38665b2a205bc7a708cb65441d58f4e0196ca880031e14374595100063c286e6b2a2000c7850dc965441d38eeebb8aca883a39c143715951015d3d42ee0b2a20e7a7980990654409f8f0e1320ca8839b1e1c0641951072d3cc04c632a204bc787098c65441c98f0e0318ca8838e9e602621951023e3c384c432a20e2c787018865440ab1f700baec8880063e20175d91100063c282ebb222000c78505cf64441c3c70a121ec8880031e14172d91107071c28485b222050a7a85d4364440010fd0fb2ac888003171cf655911000636396cab22200087e8719564440018b8e632ac8880031b1c865591106fe3db80cab222000c5f65dcd64440018b8cbb9ac88800356143735911000637b2ee4b222000c6c65dc96444001ad0a1b92c88801a1fa1f75591100063d406eab222000c7980dd564441bdc70a1ba2c8880031e14373591100246f43ee6b222000c5f75dcd64440018b8ebb9ac8880039614373591100062f286e6b222000c5c50dcd64440019b
  | 3 => 0x6b224000c5c751cd644800193ee839ac8900039614073591200066639ee4b2240f5e6850dc964480018f0a1b8ac89000a3da1f71591200063bbaee2b224000c7475dc564480019aee7b8ac890003351cf715912000738286e2b224000c7650dc564480018e8a1b8ac8900033c143715912000638286e2b224000c77751c564480018e8ea38ac8900032ddd071591200066bb98e2b224000cd4731c564480019cee438ac8900039c14071591200053d42ee0b224000c7875dc164480011f50fa82c8900ce9ea1750591200363c3aea0b224000cdb73d4164480e39b0e7a82c8900033cdc750591202ae7838ea0b224000c7850dd954480018f0a13b2a8900021fe1576551200046fc1aecaa240048dc835d954480011ef02bb2a89000a3d20576551200047dc02ecaa24000c78505d954480018f0a03b2a8900161fa1f655512031e3c386caaa240038fa86dc154481238f0cbb82a8901923ee0175d8d200063c282ebb1a4000c78505d363481e9cb0a1a1ec6900031e14171d8d2079f2c28463b1a405ba7a85d4363480010fd0fb2ac6900030f1d36558d200063a38ecab1a400087e871956348001878e832ac6900031d1c46558d207963db80cab1a4000c3f65dd16348001878cbba2c6900034e1437458d200063bb2ee2b1a4000c7465dc56348001ae0a1b8ac69001a1fa1f7558d200063d406eab1a4000c7980dd563480018f0a1ba2c6900162fa1f7458d200061fbaee8b1a4000c3c75dd16348001c70a1ba2c6900030f9437458d200061e286e8b1a4000cb850dd16348001870a1ba2c6900030fdd47458d200061e3a8e8b1a4000e38501d16348001938e9b9ac6903c7961437358d20006563a6e4b1a40f0e6850dc963480018f0a1b8ac69000a3da1f7158d200063bbaee2b1a4000c7475dc5634800196ee9b8ac6900032d1d37158d2000738286e2b1a4000c7650dc563480018e8a1b8ac6900033c1437158d2000638286e2b1a4000c77751c563480018e8ea38ac6900032ddd07158d200065a3a0e2b1a4000cd7731c563480019cee438ac6900039c1407158d200053d42ee0b1a4000c7875dc163480011f50fa82c6900be9ea175058d200363c3aea0b1a4000cbb74d4163480f9970e9a82c6900033cdc75058d202ae7838ea0b1a4000c7850dd953480018f0a13b2a6900021fe157654d200045fc22eca9a40058bc845d953480011ef02bb2a69000a3d2057654d200047dc02eca9a4000c78505d953480018f0a03b2a6900121fa1f6554d2031e3c386caa9a40038fa86dc1534811f8f0cbb82a69001a1fa177650d200043ec2eeca1a4000c7850dd94348001938873b286900031e1427650d200043fc2aeca1a400687c855d9434800117f08bb2869000237e0d7650d2000477c12eca1a40008f7815d943480051e902bb286900031e14
  | 4 => 0x24c0070fd0fb2aa4981c31e1c365549300247d436e0a92608dc7865dc1524c00d0fd0bbb284980021f61776509300063c286eca126000cac429d9424c0018f0a13b284980032b10876509300063c280eca126000e2c42d95424c0e31f700baec2980031e14175d85300063c282e9b0a6000c78505cb614c203ce0a1a0ec2984039c14321d853025d3d42ea1b0a607087c86dd5614c0010fd0fb2ac2980030f1d3655853000636396cab0a600087e87195614c001878e832ac2980031b1c865585307fe3db80cab0a6000c3f65dd1614c001878cbba2c2980034e143745853000637b2ee4b0a6000c6c65dc9614c001ad0a1b92c2980031e14376545300063c284eca8a600687c851d9514c0018f0a03b2a29800a1fa1f65545303863c386caa8a60048fa86dc1514c0032f50bb82a29822f1e19770545300343f42eeca0a600087d85dd9414c0018f0a1bb282980032d10676505300063c284eca0a6000cb4411d9414c0018f0a03b282980038d10765505300343f42eec90a600087d85dd9214c0018f0a1bb242980033908676485300063c284ec90a6000ce4211d9214c0018f0a03b242980039908765485300fd3d406ca90a6000c3d7495365480014f3012a6ca90003175ce53d95200053cc04a7b2a4006c7a7094765480cd4f301ba6ca9006b1e9c274d95200063d382e9b2a4000c3d741d365480c74f5003a6ca9019a9e60074d95200d63d380e9b2a4066a7980dcf65480338f4e139eca900031e9c173d95200062eb98e7b2a4063a7a801cf65480cd4f30039eca900671e9c073d95203353cc06e3b2a4017c7a709c765480018f4e0b8eca9018e9ea0071d95203353cc00e3b2a4017c7a701c7654809f8f4e1a0eca901431e9c241d95207363d38083b2a404bc7a70cc765480998f4e118eca903931e9c031d95200063c286e8b2a4000c7850dcd65481fd8deebb92ca903f79a14372595200063c286e2b2a4037a7a85dc165481f94f301320ca9017b1e1c2641952075e3c380c832a40fba798098c65480b58f0e1318ca903ab1e1c063195207d53cc04c232a4048c787098465481c58f0e0308ca901923ee0175d91200063c282ebb224000c78505cf64481f3c70a121ec8900031e14171d91207c71c28483b22405fa7a85d4364480010fd0fb2ac890003171cf65591200063a38ecab22400087e8719564480018b8e632ac8900031d1c465591207be3db80cab224000c5f65dcd64480018b8cbb9ac8900035614373591200063bb2ee2b224000c7465dc56448001ae0a1b8ac89001a1fa1f75591200063d406eab224000c7980dd564481edc70a1ba2c8900031e14373591200246f43ee6b224000c5f75dcd64480018b8ebb9ac8900039614373591200062f286e6b224000c5c50dcd64480019b0a1b9ac8900031614373591200062fba8e
  | 5 => 0x806b1e9c274d95300063d382e9b2a6000c3d741d3654c0e14f5003a6ca981ce9e60074d95300d63d380e9b2a6073a7980dcb654c0318f4e1396ca980031e9c172d95303853d400e5b2a6073a79801cb654c0318f4e0396ca981ce9e60371d95300be3d384e3b2a6000c7a705c7654c0e14f50038eca981ce9e60071d95300be3d380e3b2a6047c7a70c87654c0918f4e110eca9838b1e9c021d95300063c286e8b2a610ec5f75dcd654c21bcb0a1b9aca980031e14372595300063c286e2b2a603fa7a85dc1654c2194f301320ca981af1e1c264195307663c380c832a610ba7980988654c0b78f0e1310ca983ab1e1c062195308553cc04c232a604cc7870984654c1c98f0e0308ca981c63ee0175d91300063c282ebb226000c78505cb644c213c70a1216c8980031e14171d91308471c28483b22606ca7a85d43644c0010fd0fb2ac8980031b1cb65591300063a38ecab22600087e87195644c0018d8e432ac8980031d1c4655913083e3db80cab226000c6f65dc9644c0018d8cbb92c8980035a14372591300063bb2ee2b226000c7465dc5644c001ae0a1b8ac89801a1fa1f75591300063d406eab226000c7980dd5644c20dc70a1ba2c8984179614373591300063c286e4b2260038ee87dc9644c0018deebb92c8980031b1d7725913000734286e4b226000c6e50dc9644c0018d8a1b92c8980033a143725913000634286e4b226000c6f751c9644c0018d8ea392c8980032bdd0725913000667b98e4b226000e68501c9644c0018f0a1b8ac89800a3da1f71591300063bbaee2b226000c7475dc5644c0019cee5b8ac898003391cb715913000738286e2b226000c7650dc5644c0018e8a1b8ac8980033c143715913000638286e2b226000c77751c5644c0018e8ea38ac8980032ddd071591300066bb98e2b226000ce7721c5644c0019c8e438ac8980039c14071591300053d42ee0b226000c7875dc1644c0011f50fa82c8980ee9ea1750591300363c3aea0b226000ceb72d41644c0c99d0e5a82c8980033cdc750591302ae7838ea0b226000c7850dd9544c0018f0a13b2a8980021fe15765513000477c12ecaa260038ec825d9544c0011ef02bb2a89800a3d20576551300047dc02ecaa26000c78505d9544c0018f0a03b2a8980161fa1f65551303863c386caaa260048fa86dc1544c1238f0cbb82a8981c63ee0175d89300063c282ebb126000c78505d3624c209cd0a1a16c4980031e14171d893081f3428443b12605aa7a85d43624c0010fd0fb2ac4980030f1d365589300063a38ecab12600087e87195624c001878e832ac4980031d1c465589308163db80cab126000c3f65dd1624c001878cbba2c4980034e14374589300063bb2ee2b126000c7465dc5624c001ae0a1b8ac4980031e14376549300063c284eca926000c78501d95
  | 6 => 0xce3d380e7b2a807ea7980dcb65500318f4e1396caa00031e9c172d95403dd3d400e5b2a807ea79801cb65500318f4e0396caa01fa9e60371d95400be3d384e3b2a8000c7a705c765500f74f50038ecaa01fa9e60071d95400be3d380e3b2a811cc3f75dd16550237c70a1ba2caa00031e14373595400063c286e4b2a8000c7850dc565500874f50bb82caa046a9e60263195403663c384c632a80ecc787018c65502334f301310caa017f1e1c2621954075e3c380c432a8118a798098465500a18f0e1308caa039b1e1c061195403e47dc02ebb1a8000c78505d763500018f0a0b96c6a045f9614232d8d400063c282e3b1a8116e58508c763500d74f50ba86c6a00021fa1f6558d4000636396cab1a8000c7471d9563500010fd0e32ac6a00031b1c86558d400063a388cab1a8115c7b7019563500018decbb92c6a00031b1977258d40006b4286e4b1a8000c7765dc563500018e8cbb8ac6a00035c1437158d400063c286eca9a8000c78509d953500018f0a03b2a6a00121fa1f6554d403de3c386caa9a80058fa86dc1535011f8f0cbb82a6a01f23ee0175d89400063c282ebb128000c78505cf6250229cd0a1996c4a00031e14171d894089f3428443b12805ea7a85d4362500010fd0fb2ac4a0003171cf65589400063a38ecab12800087e8719562500018b8e632ac4a00031d1c465589408963db80cab128000c5f65dcd62500018b8cbb9ac4a00035614373589400063bb2ee2b128000c7465dc56250001ae0a1b8ac4a00031e14376549400063c284eca928000c78501d952500070fd0fb2aa4a01ef1e1c3655494002c7d436e0a92808dc7865dc1525000d0fd0bbb264a00021f617764c9400063c286ec9928000ccc329d932500018f0a13b264a0003330c8764c9400063c280ec9928000e4c32d9532500f91f700baec2a00031e14175d85400063c282e7b0a8000c78505cb6150223ce0a198ec2a04439c14321d854027d3d42ea1b0a807b87c86dd561500010fd0fb2ac2a0003171cf655854000636396cab0a800087e8719561500018b8e632ac2a00031b1c8655854087e3db80cab0a8000c5f65dcd61500018b8cbb9ac2a000356143735854000637b2ee4b0a8000c6c65dc96150001ad0a1b92c2a00031e14376545400063c284eca8a800687c851d951500018f0a03b2a2a000a1fa1f65545403de3c386caa8a80058fa86dc151500032f50bb82a2a022f1e19770545400343f42eec98a800087d85dd931500018f0a1bb262a0003350c6764c5400063c284ec98a8000cd4311d931500018f0a03b262a0003950c7654c5400343f42eec90a800087d85dd921500018f0a1bb242a00033908676485400063c284ec90a8000ce4211d921500018f0a03b242a00039908765485400061eba4a9b2a6000a7980953654c0e74f301ba6ca9
  | 7 => 0x6b21dc93114103ad0e4b9262284a6dce05724c45042fa818ae4988a00097b8750931140012f50ea1262280025e21d424c4500069dba284988a01ad387450931140016b706a126228066d620d424c450006b5b9284988a018d68725093114103e5084a126228002dce05424c4500bdb840a84988a087f503150931140352f50fba242282034e9d3744845093fb010ee8908a00097b86dd121140032f50dba242280025e61b744845000cbc436e8908a12397984dd12114001a76c9ba242282034e19374484500ccbd41ee8908a00097983dd121140332f107ba242282034ed0f74484500bcbdc16e8908a01797982dd12114251ad4c5ba242280035a58b74484509469da16e8908a128d3942dd121140312f703ba242280625e607744845093eb930ee8908a000d7161dd1211424fa7683ba2422849f4e50774484500d4bdc3ae8908a080d38745d121142496d704ba2422849adce05744845043fb010ae8908a00097b865d121140032f50cba242280025e619744845000cbc432e8908a12597b845d12114001a7708ba242282034e99174484500069cb22e8908a00097b835d121140332f506ba242280665e20d7448450924bdc12e8908a000d6b825d12114107ad4c4ba242280035a589744845091cbdc0ae8908a000d73815d1211410fae4c2ba242280035c58574484500ccbd43ee6908a07fd5a73dcd2114243ec043b9a42280025ee1b734845000cbd436e6908a00097986dcd21140032f10db9a422806a5ea137348450004bcc26e6908a01a97884dcd211423b2f307b9a422800356d8f73484503feac31ee6908a07fd5a43dcd211402f2f705b9a422805e5e60b7348450916b5316e6908a000d6962dcd2114245ab665b9a422848b564cb73484500c4bdc0ee6908a01897981dcd2114243ae4c3b9a42280035c587734845090ead98ee6908a121d5931dcd21140332f70eb9a42281ff561cd73484508f5b5c12e6908a120b73815cd211410bec042b9a42280025ee19734845000cbd432e6908a000979865cd21140032f10cb9a42280025ee1173484500d4bd422e6908a01a978845cd211423f2f706b9a422800356e0d73484503fead31ae6908a000d59635cd211423d2f704b9a42280035ae09734845040eb5312e6908a000d69625cd211423b2f702b9a42280035ce05734845042eb930ae6908a000d71615cd21140012f70ea1a42280025ea1d4348450004bcc3a86908a0009788750d2114001a76e8a1a422806b4e1d14348450006adb9a86908a019d587350d21140ffe3086a1a4228002dae0943484500c5b441286908a000b738150d211402f6e102a1a4228227d808543484500062eb9ca7b2a8000a798094f65500fd4f301b9ecaa00671e9c273d95400063d382e7b2a8000c5d731cf65500f74f50039ecaa01fa9e60073d95400
  | 8 => 0x83b8a64282175c8c7714c85042eb910ee2990a081f48325c5321410bae0e2b8a64280665ea1f7350450426ad39ee6a08a136f3041dcd41140012f70db9a82280065ea1b7350450004bcc36e6a08a00197886dcd411402f2f309b9a82284df4e99373504500069cb26e6a08a000d5b63dcd4114109ab0c7b9a82282135690f73504509beaca1ee6a08a01897a82dcd41140012f305b9a82280625e20b7350450426ad996e6a08a01a97981dcd411426dae4c3b9a82280035c58773504509b6ad98ee6a08a084d58735cd411426b6e702b9a8228227cc10573504500c4bd43ee4a08a083d6a72dc94114267e6083b9282280025ee1b725045000cbd436e4a08a00097986dc941140032f10db92822805e5e61372504509a69d326e4a08a000d3964dc941140332f507b9282280025e60f72504500ccbc41ee4a08a000d6b62dc94114107ad0c5b92822820f5a90b72504509a6b4a16e4a08a083d6a32dc941140352f303b9282284cf5c9877250450006b8b0ee4a08a133d6b21dc94114107ad0e4b9282284cadce05725045043f9820ae4a08a00097b874c941140012f50e99282280025e21d32504500059dc2264a08a01ab38844c94114001ab6e69928228067561cd3250450006b5b9264a08a018d68724c94114107e90649928228002dce0532504500bdb840a64a08a085f30414c941140352f50fba2622820b4e9d3744c450987a818ee8988a00097b86dd131140032f50dba262280025e61b744c45000cbc436e8988a12c97984dd13114001a76c9ba2622820b4e193744c4500bcbdc1ee8988a01797983dd13114263ab4c7ba262280035658f744c45098e9da1ee8988a131d3943dd131140312f505ba262280025e60b744c4500c4bc416e8988a082d3b42dd131140332f703ba262280665e607744c450986b930ee8988a000d7161dd13114261a7683ba262284c34e507744c4500d4bdc3ae8988a082d38745d1311425b6b706ba262284bedce05744c45044fa818ae8988a00097b865d131140032f50cba262280025e619744c45000cbc432e8988a12e97b845d13114001a7708ba2622820b4e991744c4500069cb22e8988a12d97b835d13114001ab706ba262282135698d744c450006acb1ae8988a00097b825d131140312f504ba262280625e209744c450964bdc0ae8988a000d73815d13114113ae4c2ba262280035c585744c4500c4bd43ee4988a081d6a72dc93114255ea063b9262280025ee1b724c45000cbd436e4988a00097986dc931140032f10db92622806a5ea13724c450004bcc26e4988a01a97884dc9311402f2f307b9262284af5698f724c450006acb1ee4988a000d6b62dc93114103ad0c5b9262282075a90b724c45040eb5196e4988a12bd6932dc931140332f303b9262284ab5c987724c450006b8b0ee4988a12ad
  | 9 => 0x7150c50a2f8c21ee2a18a089d7271dc543140012f70db8a86280065ea1b7150c50004bcc36e2a18a00197886dc543140332f309b8a862851b4e9937150c500069cb26e2a18a01a97983dc5431428bab4c7b8a86280035658f7150c500c4bd416e2a18a00097982dc543140312f105b8a86280035cd877150c5044eb830ee2a18a089d7241dc54314113ae463b8a86282275c8877150c504278c21ae2a18a089d70715c543140332f50fb9a8428223569cf7350850a1f94216e6a10a00097b86dcd42140032f50db9a84280025e61b735085000cbc436e6a10a01897984dcd4214289a74c9b9a84280034e5937350850006adb1ee6a10a088d5863dcd4214111ab487b9a84285135650f73508500d4bcc16e6a10a143d6a62dcd4214001ad2c5b9a842850f56ccb73508500bcbd40ee6a10a00097981dcd421402f2f103b9a842822356cc77350850446ac39ae6a10a142b6b825cd4214115e5084b9a842805e5ea1f7150850a0794216e2a10a087d7271dc542140012f70db8a84280065ea1b7150850004bcc36e2a10a00197886dc542140312f309b8a84285074e99371508500069cb26e2a10a01997a83dc542140012f307b8a84280665e20f71508500d4bcc16e2a10a140d6a62dc54214001ad2c5b8a84280035cd87715085043eb830ee2a10a087d7241dc5421410fae463b8a842821f5c887715085041f94212e2a10a087d70715c542140352f50fba2642821b4e9d3744c8509f7a4196e8990a00097b86dd132140032f50dba264280025e61b744c85000cbc436e8990a13a97984dd13214001a76c9ba2642821b4e193744c8500c4bdc1ee8990a01897983dd1321427fab4c7ba264280035658f744c8509fe9da1ee8990a13fd3943dd132140332f705ba264280665e60b744c8509f6b5316e8990a000d6962dd1321427da7685ba264284fb4e50b744c8500bcbd40ee8990a00097981dd1321402f2f103ba2642821b4ed07744c8500d4bdc3ae8990a086d38745d132142776b706ba264284f6dae09744c850457a4192e8990a00097b865d132140032f50cba264280025e619744c85000cbc432e8990a13c97b845d13214001a7708ba2642821b4e991744c8500069cb22e8990a13b97b835d13214001ab706ba264282235698d744c850006acb1ae8990a13a97b825d13214001ad704ba2642822b5a989744c850006b4b12e8990a00097b815d1321402f2f502ba2642805e5e205744c8500bcbd43ee2990a138f4832dc5321410bae4e3b8a64280025ee1b714c85000cbd436e2990a00097986dc532140032f10db8a642806a5ea13714c850004bcc26e2990a01a97884dc532140312f307b8a64284e75698f714c850006acb1ee2990a01997982dc53214271ad4c5b8a64280035a58b714c850006b9b0ee2990a085d7061dc5321410bae4
  | 10 => 0xaa242048dc835d954484011df04bb2a8908023de0576551210047dc02ecaa242018f8805d954484018f0a0bb2a8908033908476551210063c280ecaa24200de021dc154484011f700baec6908063e20175d8d210062ebaea7b1a420087f855c3634840d0f90ab86c6908071e9c050d8d210063cb80a1b1a4201c78701436348693cb060286c69081b1e9d450d8d210063cba8a1b1a4206c78751436348401cb6a6286c690d279614c50d8d210072c28461b1a42018fa80dd563484011f301baac69081a1fa177058d210043ec2ee0b1a4200c7b7014163484038f4e0282c6908071e1c05058d210063dba8a0b1a4206c7a75141634840d8f0ea282c690803390877654d210063c286eca9a42018fa809d953484011f3013b2a6908031e1427654d210045fc22eca9a42058bc845d953484011bf06bb2a6908023be097654d210047bc0aeca9a42008fb805d953484031f100bb2a6908031e1417654d2100672108eca9a4200c78501d95348401bc043b82a6908021fe157650d210343e42aeca1a42008fb805d943484031f100bb286908122fa1f6450d210254f41ec8a1a42058de87d8d434840b53d09b1a869080a3ba1b7250d2100657b26e4a1a4200ccf63dc943484053cd03b92869080e3da1b7150d210065bb26e2a1a4200cd763dc543484073cd05b8a86908035908575d81210343fc3aebb024200c7b805d760484018f100baec0908031e14174d81210063c282e7b02421fa7a85d43604840d8f4eba86c090803590877558121006d210ee8b024200d3850dd16048401b8843b9ac0908035614373581210063c282e7b22a000c78505cb64540018f0a0b8ec8a80031e14174d8d500063c282e5b1aa000c78505c763540010fb0bbb286a80031e1437650d500063c284eca1aa000c78501d943540018f0a0ba6c4a80031e14173d89500063c282e3b12a00087d85dd942540018f0a1bb284a80031e14276509500063c280eca12a00087d85dd932540018f0a1bb264a80031e142764c9500063c280ec992a000c78505d361540018f0a0b9ec2a80031e14172d85500043ec2eeca0aa000c7850dd941540018f0a13b282a80031e14076505500043ec2eec98aa000c7850dd931540018f0a13b262a80031e140764c5500043ec2eec90aa000c7850dd921540018f0a13b242a80031e14076485500c4bd43ee4a18a147f1843dc94314115ad4e5b9286280025ee1b7250c5000cbd436e4a18a00097986dc943140032f10db9286280665e6137250c50a469d326e4a18a000d3964dc943140352f307b92862851f5698f7250c50006acb1ee4a18a000d6b62dc94314115ad0c5b92862822b5a90b7250c50456b5196e4a18a01797a81dc943140012f303b92862805e5e2077250c50456b590ee4a18a088f18435c94314115ad0e4b92862805e5ea1f
  | 11 => 0x4c4018f0a03b2a898803740c770551310047dc02ebb1262018f8805d7624c4010ff0ab86c49881a1f21570d893100e3d380a1b126200c7970143624c4038f0e0286c498d379a08050d89310363d3a8a1b126200c7975143624c40d8f0ea286c4988039ad4850d8931a6f34290a1b126200e6850883624c4019a863bb2a4988031e143765493100c7d404eca9262008f9809d9524c4018f0a13b2a498803350c476549310063c280eca926200dd031dc1524c40717d0fb22849880eaba0b64509310146f436e6a126200c9f64dcd424c4053ad03b9a84988163ba1f625093102d57426c4a126200ccf73d89424c4091ed0db8a84988032dd937150931024eb41ee2a126200ce762dc5424c401aa862baec09881a1fe1d75d81310063dc02ebb026200c78805d7604c4018f0a0ba6c0988031e14172d813111d3d42ea1b026206c7a75d43604c401aa863baac098803650c774581310069c286e8b026200dc431dc9604c401ad0a1b92c0988037808570d95210063c282e9b2a4200c78505cf65484031f70eb86ca908031e21570d95211153d404a1b2a4201c7a709436548401b4843ba2ca908034e1437459521006e210ee6b2a4200d5850dcd6548401bc043b82ca908029ea0375595210063c286e8b2a42058be87dd16548401c70a1ba2ca908032ed4374595210061e286e8b2a4200cb850dd16548401870a1ba2ca908038e14074595210063c286e6b2a42048de87dcd654840193ee9b9aca90803271d373595210072c286e6b2a4200cdb50dcd65484018b8a1b9aca908033614373595210062c286e6b2a4200c9f741cd6548401938e839aca90803961407359521006563a6e4b2a4200ccc73dc96548699cd0a1b92ca908032d1d371595210066a39ee2b2a434be7050dc565484031f50fb82ca908032edd370595210065c3a6e0b2a4200cdb73dc165484019b0e7b82ca908031ea17705952100c7c42ee0b2a4200c7b751c16548401976e8382ca908032e1d070595210066db98e0b2a4200cd8731c1654840187ee9282ca909fb0f1d250595210062fb9ca0b2a4273c5c7394165484454f501282ca908031edc2505952100e3c384a0b2a42008fb805d764484031f100baec8908030f5d754d91210043fc2ae1b22420687c855c364484038f4e0286c8908031e5c050d912100e3c380a1b22434ae3840143644840d8f4ea286c8908031e5d450d91210363c3a8a1b224200e3b541436448695c70a8286c8908038e14240d912100c7d406eab2242008f980dd5644840d0fd0bb82c8908021f61770591210063db80a0b224201c7a7014164484038f0e0282c8908031edd450591210363d3a8a0b224206c787514164484019c843bb2a8908031e143765512100c7d404ecaa242008f9809d954484018f0a13b2a8908022fe1176551210046fc1aec
  | 12 => 0x8071e9c050d89410063cb80a1b128201c787014362506a5cd040286c4a081b1e9d450d89410063cba8a1b128206c78751436250401cd6a4286c4a0d4b9a14850d89410073428441b128200cb441dd952504018f0a1bb2a4a08063ea0276549410047cc04eca928200c78509d95250401968823b2a4a08031e1407654941006d820ee0a9282028be86dd1325040536d03ba264a080e37a1f634c9410064fba6c69928203ace82d8d32504091dd0fb1264a08032bdd3624c9410256741ec499282058f686dc5325040b36d09b8a64a080335d8f714c94100673b16e29928200d34415d7605040d0ff0ebaec0a08031ee0175d81410063c402ebb028200c78505cf60504018f0a0b96c0a089e9ea1750d81410363d3aea1b028200d3441dd56050401b2883b9ac0a0803561437358141006d220ee4b028200d6850dc96050401ba062b86ca988031e14174d95310063c282e5b2a62018fb875c3654c4018f10ab86ca9889a9ea0250d953100e3d384a1b2a6200d9431dd1654c401a70a1ba2ca98803710c77259531006b4286e4b2a6200dd031dc1654c4014f501baaca988031e143745953102c5f43ee8b2a6200e3850dd1654c401976a1ba2ca988030f14374595310065c286e8b2a6200c3850dd1654c401c70a03a2ca98d4717dd773595310064e3a6e6b2a6350e5850dcd654c4018f0a1b92ca9880e3ba1f725953100657ba6e4b2a6200cac74dc9654c401cd0a1b92ca988033ad43725953100636286e4b2a6200ce850dc9654c4018d0a1b92ca988032bdd07259531006563a0e4b2a6200ccf731c9654c401cd0a0392ca988032d1d3715953100672396e2b2a634fe7050dc5654c4031f50fb82ca988032edd370595310065c3a6e0b2a6200ceb72dc1654c4019d0e5b82ca988031ea1770595310063dba8e0b2a6200cbb741c1654c401970e8382ca988033adc8705953100674390e0b2a6200c3f74941654c4fd878e9282ca988031bdca505953133636394a0b2a6226a7a80941654c4038f0e1282ca988023ee0175d913100c7c402ebb226200c3d75d53644c4010ff0ab86c89881a1f21570d913100e3d380a1b226200c7970143644c4038f0e0286c898d3b8e10050d91310363d3a8a1b226200c7975143644c40d8f0ea286c8988038ed5050d9131a771c2a0a1b226200e3850903644c4031f501baac8988023e60375591310343f42ee0b22620087d85dc1644c4018f6e0282c8988071e9c0505913100e3c380a0b226200c7b75141644c40d8f4ea282c89881b1e1d450591310066a18eecaa26200c7850dd9544c4031f5013b2a8988023e60276551310063c284ecaa262008bf845d9544c4011bf06bb2a8988023be09765513101c76412ecaa262008f7815d9544c4011f700bb2a8988063e20176551310063c282ecaa26200cd4311d954
  | 13 => 0x56c41ac5b02a255a7985dd360544358f4eb3a6c0a88031e9d574d815145d3d428e9b02a255a79851d360544358f4ea3a6c0a89569e61773d81510ce3d3ace7b02a200c7a755cf60545174f50a39ec0a89569e61473d81510ce3d3a8e7b02a200e994310f60544ab4f30bb96c0a88631e9d672d81510063d3aae5b02a28ba7a851cb60544ab4f30a396c0a88631e9d472d815100754a1085b02a200ec9320cb605456f8f0ebb20c0a88023e61e6418151ae53cc2cc8302a21ac787599060544011f70eb20c0a8d6e9ee1564181510056dc1ac8302a200ad88359060544015d704b20c0a8802ba20964181510d63c3a8c8302a2b5c7875d8c60544011f30f318c0a8d6a9e61663181510ce3c3acc6302a2008fb8758c60546b34f70ab18c0a8802aee1163181510055c422c6302a200aeb8258c60544015d104b18c0a88671e1d4631815159e3c3aec4302a2008f98798860546b14f30b310c0a88631e1d662181510047dc3ac4302a357a7b85588605440157708b10c0a8802ae21162181510056dc1ac4302a200ad88358860544318f0ea310c0a88036c10570d95410063c282e7b2a8200c78505cb65504031f70eb86caa08031e21570d95411553d404a1b2a8201c7a709436550401b2883b9acaa0803561437359541006d220ee4b2a8200d6850dc96550401b6083b82caa08029ea037559541ab61fbaee8b2a8355e3850dd165504018f0a1b9acaa081237a1f73595410072c286e6b2a8200cdb50dcd65504018b8a1b9acaa08033614373595410062c286e6b2a8200c9f741cd6550401cb0a039acaa08031e143725954101c7743ee4b2a8200ccf73dc96550401998e7b92caa08039a143725954100675a86e4b2a8200c6c50dc965504019d0a1b92caa08031a143725954100657ba0e4b2a8200ccf731c96550401998e6392caa08039a14072595410066a39ee2b2a8200ce472dc565506a9ce0a1b8acaa08063ea1f70595410066db9ee0b2a8200cd873dc165504019d6e5b82caa08033a1cb70595410063d42ee0b2a8200c7b751c165504019b6e6382caa0803361cc705954100675b90e0b2a8200ce8721c165504018bee7282caa09cf171ce505954100637b94a0b2a8266c6c7294165504554f501282caa08071e1c250595410047dc02ebb1a82018f8805d763504018baeba9ec6a08021fe1570d8d410343e42ae1b1a8201c7a7014363504018f2e0286c6a08071e1c050d8d41a9f2c180a1b1a8206c7a7514363504018f2ea286c6a081b1e1d450d8d410072da98a1b1a8353e58531436350401cb0a1186c6a08032d1077654d410063c286eca9a82018fa809d953504011f3013b2a6a08031e1427654d410065a208eca9a8200c78501d95350401b6083b82a6a08023ee0175d894100c7c402ebb12820087f855c3625040d0f90ab86c4a0
  | 14 => 0xf74941654c8fd878e9282ca990031ddc650595322be3a38ca0b2a6432a7a80941654c8038f0e1282ca990023ee0175d913200c7c402ebb226400c3d75d53644c8010ff0ab86c89901a1f21570d913200e3d380a1b226400c7970143644c8038f0e0286c89958f8e10050d91320363d3a8a1b226400c7975143644c80d8f0ea286c8990038ed5050d9132b1f1c2a0a1b226400e3850903644c8031f501baac8990023e60375591320343f42ee0b22640087d85dc1644c8018f6e0282c8990071e9c0505913200e3c380a0b226400c7b75141644c80d8f4ea282c89901b1e1d4505913200666196ecaa26400c7850dd9544c8031f5013b2a8990023e60276551320063c284ecaa264008bf845d9544c8011bf06bb2a8990023be0976551320047bc0aecaa264028f4815d9544c8011f700bb2a8990063e20176551320063c282ecaa26400ccc321d9544c8018f0a03b2a899003720cb70551320047dc02ebb0a64018f8805d7614c8010ff0ab86c29901a1f21570d853200e3d380a1b0a6400c7970143614c8038f0e0286c2994779c04050d85320363d3a8a1b0a6400c7975143614c80d8f0ea286c2990039cd4450d85328ef38288a1b0a6400e7050843614c801a9864baec09901a1fe1d75d81320063dc02ebb026400c78805d7604c8018f0a0ba6c0990031e14171d813217d3d42ea1b026406c7a75d43604c801a9865baac099003630cb74581320069c286e8b026400dc432dc5604c801ae0a1b8ac0990031e14173d9151b171c28487b22a200c78505cb64546c3c70a1216c8a895e1fe1570d915102c3e42ae1b22a200c78505c36454401ab0a1b9ac8a88035a14372591510063c282e9b1aa360e5850d0f63544018f0a0b96c6a8d7f9614232d8d512bc3fc2ae1b1aa20487c855c363544018f0a0b86c6a88034e1437458d51006b4286e4b1aa2018fa80dd943544011f301bb286a88031e1437650d510064e21ceca1aa200c78509d94354401938863b286a88031e1407650d510063c282e9b12a200c78505cf62546bdcd0a1a16c4a8d779a14332d89512bc3fc2ae1b12a20387c855c362544018f0a0b86c4a88034e1437458951006ac286e6b12a22b8f886dc162544031f501bb284a88023e60376509510063c286eca12a200cac429d942544018f0a13b284a88032b10876509510063c280eca12a2018fa80dd932544011f301bb264a88031e143764c95100666194ec992a200c78509d93254401998643b264a88031e140764c9510053cc2e81b02a201c7a75d0360544014f30b986c0a88071e9d730d815100e3d3ae41b02a200adb8359360544015b106b26c0a8802bae0964d815100574412c9b02a200abb8458f605440157108b1ec0a8802bae0963d815100574412c7b02a200abb8458b605440157108b16c0a8802b6e0d62d815100
  | 15 => 0x1b9acaa10033614373595420062c286e6b2a8400c9f741cd6550801cb0a039acaa1003331cf7259542b4734286e4b2a8400c7850dc565508051ed0fb8acaa100335dcf71595420066a39ee2b2a8400e7050dc565508019e6a1b8acaa10031d143715954200678286e2b2a8400c7050dc5655080196ee838acaa100335dcc71595420066a398e2b2a8400ce7721c56550801ce0a038acaa10063ea1f70595420066db9ee0b2a8400cd873dc165508019e6e3b82caa10033c1c770595420063d42ee0b2a8400c7b751c165508019b6e6382caa1003361cc705954200679b88e0b2a8400cf0711c165508018bee7282caa11cf171ce50595420063bb8ca0b2a8457c7471941655086d4f501282caa10071e1c250595420047dc02ebb1a84018f8805d763508018baeba9ec6a10021fe1570d8d420343e42ae1b1a8401c7a7014363508018f2e0286c6a10071e1c050d8d42b3f2c180a1b1a8406c7a7514363508018f2ea286c6a101b1e1d450d8d420072da98a1b1a8567e58531436350801cb0a1186c6a10032b10b7654d420063c286eca9a84018fa809d953508011f3013b2a6a10031e1427654d4200656210eca9a8400c78501d95350801b5085b82a6a10023ee0175d854200c7c402ebb0a840087f855c3615080d0f90ab86c2a10071e9c050d85420063cb80a1b0a8401c78701436150a47ce020286c2a101b1e9d450d85420063cba8a1b0a8406c78751436150801ce6a2286c2a148f9c14450d85420073828421b0a8400d2c425d7605080d0ff0ebaec0a10031ee0175d81420063c402ebb028400c78505cf60508018f0a0b8ec0a10ce9ea1750d81420363d3aea1b028400d2c42dd56050801b1885b9ac0a1003561437358142006d2216e2b028400d7050dc56050801b9064b86ca990031e14174d95320063c282e3b2a64018fb875c3654c8018f10ab86ca990ca9ea0250d953200e3d384a1b2a6400d8c32dd1654c801a70a1ba2ca99003710cb7159532006b8286e2b2a6400dc832dc1654c8014f501baaca990031e143745953202c5f43ee8b2a6400e3850dd1654c801976a1ba2ca990030f14374595320065c286e8b2a6400c3850dd1654c801c70a03a2ca9959b17dd773595320064e3a6e6b2a6565e5850dcd654c801958e9b92ca995939a14372595320063c286e2b2a64028f687dc5654c80196ee9b8aca990032d1d3715953200738286e2b2a6400cf350dc5654c8018e8a1b8aca990033c143715953200638286e2b2a6400cb7741c5654c801968e838aca9900335dcc715953200673b90e2b2a6400e70501c5654c8031f50fb82ca990032edd370595320065c3a6e0b2a6400cf371dc1654c8019e0e3b82ca990031ea1770595320063dba8e0b2a6400cbb741c1654c801970e8382ca990033cdc4705953200678388e0b2a6400c3
  | 16 => 0xd85430063cba8a1b0a8606c78751436150c01ce6a2286c2a1cb39c14450d85430073828421b0a8600d1c435d76050c0d0ff0ebaec0a18031ee0175d81430063c402ebb028600c78505cb6050c018f0a0b8ec0a18ee9ea1750d81430363d3aea1b028600c7975d436050c01a3887baac0a18036310f7258143006b4286e4b028600d9443dc56050c01ae0a1b8ac0a18031e14173d9152bb71c28487b22a400c78505c76454aebc70a120ec8a919a1fe1570d91520063c282e1b22a400d5850dcd6454801ae0a1b8ac8a90031e14174d8d52ba72c28687b1aa400c78505c76354ae7cb0a118ec6a919a1fe1570d8d520063c282e1b1aa400d3850dd16354801ae0a1b8ac6a90063ea037650d520047cc06eca1aa400c7850dd94354801938873b286a90031e1427650d520064e218eca1aa400c78501d943548018f0a0ba6c2a90031e14173d8552b973828683b0aa571e7050cc761548cd0ff0ab86c2a900a1f21570d85520063c282e1b0aa400d3850dd16154801ab0a1b9ac2a90de3e21b70585520053cc2e81b02a400a7985cc360548038f4eb886c0a9002b6e0d64d81520056c41ac9b02a400af38159360548015e102b26c0a9002aee1163d81520055c422c7b02a400af38158f60548015e102b1ec0a9002aee1161d81520055c422c3b02a400adb8358760548015b106b0ec0a91929e61774d81520d63d3ace9b02a400c7a755d3605491b4f50a3a6c0a91929e61474d81520d63d3a8e9b02a464a7985dcf60548338f4eb39ec0a90031e9d573d815246d3d428e7b02a464a79851cf60548338f4ea39ec0a9003a650c43d81523253cc2ee3b02a417c7a759c760548018f4eab8ec0a92369ea1471d81523253cc28e3b02a417c7a751c760549958f0ebb20c0a90023e61e6418152b853cc2cc8302a41ac787599060548011f70eb20c0a95be9ee1564181520056dc1ac8302a400ad88359060548015e702b20c0a9002bc20564181520d63c3a8c8302a4c8c7875d8c60548011f30f318c0a95ba9e61663181520ce3c3acc6302a4008fb8758c6054adb4f70ab18c0a9002aee1163181520055c422c6302a400af38158c60548015e102b18c0a90671e1d463181525963c3aec2302a4008f9879846054ad94f30b308c0a905f1e1d661181520047dc3ac2302a56ba7b85584605480157708b08c0a9002ae21161181520056dc1ac2302a400ad883584605482f8f0ea308c0a90036a10970d95420063c282e7b2a8400c78505c765508031f70eb86caa10031e21570d95421b53d404a1b2a8401c7a709436550801b1885b9acaa1003561437359542006d2216e2b2a8400d7050dc56550801b5085b82caa10029ea037559542b561fbaee8b2a8569e3850dd165508018f0a1b9acaa101237a1f73595420072c286e6b2a8400cdb50dcd65508018b8a
  | 17 => 0x2a600abb845876054c0157108b0ec0a9802bae0961d815300574412c3b02a671a7985dd36054c358f4eb3a6c0a98031e9d574d815347d3d428e9b02a671a79851d36054c358f4ea3a6c0a99c69e61772d81530c63d3ace5b02a600c7a755cb6054d1f4f50a396c0a99c69e61472d81530c63d3a8e5b02a671a7985dc76054c2f8f4eb38ec0a98031e9d571d815347d3d428e3b02a671a79851c76054c2f8f4ea38ec0a9b471e1d764181530047cc3cc8302a780a79859906054c358f0eb320c0a98023ee1d6418153bfd3dc2ac8302a600aeb825906054c015d104b20c0a9802bce0564181530057840ac8302a61ac78751906054d8f8f0ebb10c0a98023e61e6218153bf53cc2cc4302a618c78759886054c011f70eb10c0a9df69ee1562181530055dc22c4302a600ab8845886054c015e702b10c0a9802bc20562181530c63c3a8c4302a6b4c7875d846054c011f30f308c0a9df29e61661181530be3c3acc2302a6008fb875846054ef74f70ab08c0a9802aee1161181530055c422c2302a600aeb825846054c015d104b08c0a985f1e1d46118153006cc21ae1b2a8600c78505cb6550c018f0a0b8ecaa18063ee1d70d95430063c42ae1b2a863ea7a809436550c038f4e1286caa18031e5c250d9543006c621ee4b2a8600d6850dc96550c01b2887b8acaa18035c1437159543006cc21ee0b2a8600a7a80dd56550ef587eebba2caa1de78e1437459543bc62fbaee6b2a8777e5850dcd6550c018f0a1b92caa180e3ba1f725954300734286e4b2a8600ceb50dc96550c018d8a1b92caa18033a143725954300634286e4b2a8600caf741c96550c0199ee6392caa18039a14072595430063c286e2b2a86028f687dc56550c019cee5b8acaa1803391cb715954300738286e2b2a8600cf350dc56550c018e8a1b8acaa18033c143715954300638286e2b2a8600cb7741c56550c019aee638acaa180339dc8715954300672390e2b2a8600e70501c56550c031f50fb82caa18033adcb705954300674396e0b2a8600cf371dc16550c019e0e3b82caa18031ea1770595430063dba8e0b2a8600ceb721c16550c019d0e4382caa18033cdc4705954300678388e0b2a8600c6f729416550ccd8d8e5282caa18031ddc650595432be3a38ca0b2a863ea7a809416550c038f0e1282caa18023ee0175d894300c7c402ebb128600c6d75d4b6250c010ff0ab86c4a181a1f21570d894300e3d380a1b128600c79701436250c038f0e0286c4a1ceb9a08050d89430363d3a8a1b128600c79751436250c0d8f0ea286c4a18039ad4850d89439d734290a1b128600e68508836250c011f700baec2a18063e20175d85430063abaea3b0a860087f855c36150c0d0f90ab86c2a18071e9c050d85430063cb80a1b0a8601c78701436150e59ce020286c2a181b1e9d45
  | 18 => 0x801001c00400401c00000400806002403400802400801801805800001000001806400005400002000c0100000040080000040a40000040a00dc01c00401001404400400401c24402402c01c00000000005000407000804000006404400000c02c02400c01c00800c03802401400802802800400403c020018f0a0b96c6aa64b9614232d8d540063c282e3b1aa991e58508c763550fd0ff0ab86c6aa0031e14170d8d54006b4286e4b1aa800d7050dc563550018f0a0b9ec4aa6439a14332d89540063c282e3b12a98fe685088762550fd0ff0ab86c4aa0031e14170d8954006ac286e6b12a800d7050dc562550018f0a0b9ec2aa0031e14172d8554c773828663b0aa98de7050c8761550fd0ff0ab86c2aa0031e14170d8554006ac286e6b0aa800d6850dc961550871f10db82c2aa0029e61730d815400575c12c7b02a800ae88258f60550015e702b1ec0aa002bc20563d81540056dc1ac5b02a800ad88358b60550015e702b16c0aa002bc20562d81540056dc1ac3b02a800ad88358760550015d704b0ec0aa002ba20961d81543e53cc2ee7b02a819c7a759cf60550018f4eab9ec0aa2469ea1473d81543e53cc28e7b02a819c7a751cf60550f94f30bb96c0aa0631e9d672d81540063d3aae5b02a891a7a851cb60550f94f30a396c0aa0631e9d472d81543e53cc2ee3b02a817c7a759c760550018f4eab8ec0aa2469ea1471d81543e53cc28e3b02a817c7a751c760551a18f0ebb18c0aa0023e61e6318154c653cc2cc6302a819c787598c60550011f70eb18c0aa62e9ee15631815400575c12c6302a800ae88258c60550015e702b18c0aa002bc20563181540ce3c3a8c6302a8c9c7875d8860550011f30f310c0aa62a9e61662181540c63c3acc4302a8008fb8758860553134f70ab10c0aa002b6e0d62181540056c41ac4302a800af38158860550015e102b10c0aa0631e1d462181545b63c3aec2302a8008f98798460553114f30b308c0aa05f1e1d661181540047dc3ac2302a987a7b8558460550015b706b08c0aa002b620d611815400575c12c2302a800ae882584605502f8f0ea308c0aa0031e14172d9153c371c28485b22a600c78505c76454f0bc70a120ec8a99ce1fe1570d91530063c282e1b22a600d6850dc96454c01ae0a1b8ac8a98031e14174d8953c273428685b12a600c78505c76254f07cd0a110ec4a99ce1fe1570d89530063c282e1b12a600d3850dd16254c01ae0a1b8ac4a98031e14174d85530063c282e5b0aa782e7050d076154f03ce0a190ec2a99ce1fe1570d85530063c282e1b0aa600d3850dd16154c01ad0a1b92c2a98fe3e21b70585530053cc2e81b02a600aeb825936054c015d104b26c0a9802bce0564d81530057840ac9b02a600abb8458b6054c0157108b16c0a9802bce0562d81530057840ac5b
  | 19 => 0x1401802c01000003013801400c00001c01002c18c00000000002c05802801000000c07400408800400405c00002000002409400000017c04800800c01022802800000003801401000c00409400801403000c04800002c00802800002c03800c02800c02000000806412800c0900040c801c02801007000800001c00003c01400406800001401001400002c07c00001400000401000000407c0340080080140040bc14c01c00c00404c00804000000400000801c04409c00c03c01c00400400000000800000002003800000000003800400400000800400400c0080b003403003001013004405402c07401400001800c00005801808000000000400010800c00803000000404801400803408000c06001401c0b800400002400405000c0000180000040140240140580b00080080040040400200000140240240000b804c0100000d005009400000c01400000801019c00800005c02800804800c07c00001c00400401003808000001406401000000804802c0000000000140000040180000000000200080080340040540000000040000280080000000240040f800c00800c00001801000002001800c02400000808000800000803000400400c02800000802c00405c00003401c08000003801005401c01400400000003400000c00400801001000002c00801001c01c00000800400c09c00409c05c00000000800000002000c00801c04c0000000440000200080000080140ec05c00401001404403000000c00003000800000003407005002800000000000403000001c00000000000801800000000406c00409c03000002401c0040000180580780100000a807407c00800400000400403000000000801800c00000000020400c00007c02800802405803c0300140a403c0100040000b406800004000400008c04003406c11401c00000000000805c0040180dc1bc0380a40640340040940480080340080180000100040000040d019802800c00000401400801000000000000406806800c00c07401800004000c00c0100380000000a007800800000000c04800401801c02807000c02002801c0000ac0040000080000081181000040dc00400000402403800c01c01800000803c00800401400004c01402805009401c00000000c02400004800001001c0000180080f00000000a401401801002c0000380140ec00c05400c00401400c00801803000403801c03800802c02001800401c01c02003c00000400001800400400c00000000c02400c02000406800800800400000c0100200000440000ac21c0000700040040140780340180100040200080000e00380f802800c04406800807817802400004c01400005c0700000500000b000001401004c00000000001400004402003402400c01801800001403001c02402400800400000000406c07400
  | 20 => 0xa400000003a90201e64480fb43122eb4ec1414fa89920000540e3228108c136800040f1c7851070011b0000b64c9e5101fc8b680003223be10c0e3e2db0568000b5264000000000000004378e4c3f6000000208d1c40000e11c307be30b3cf8f145aa04238e8e68e7816e00000000fc97c000272c1287423468000b3269434b02285c00004ac8000a8e44a3c80e6cbd01592c318651fea042791c3826a0001040e250b68ac03c1a3000057446198b0a4e7c53091a282161e9477996c0000004dc8e640be8ce3b2000011200000017e40005721e187b44046e82ce869528861b0d68000f1a3550001ce88e00913d1210c1c40004101fc4d3a24d354a1ec7409cc18694b44fc0003a2800143c75c0001b6cdb20003a78ee049476a51480005de2013f411a53285500000a2c0826e631827d08124ee4f30b7cda818822d8c706c457051605e04244e04ed0f210224fc1ee9790f2a1530cf04d0f160220a4973085c41018b98b48e23e13cf0ced26472211696283ca4e52b20ad895e0c91568220af832c3fa9600e9889929a0fdcdbe39c0dea11cd0862328f8a141c67f939f93302a49a3000249121224831f8b3cb3636c15c80007f810000003446ae2c000004f8b4801b1cb13ecdb80b149fa3b400050848e0000dae7e50c6288117841f20380012b87a32f62500d9054914e000000e2102a701d91ba00006524792109a44f4a02d28c98151080b80126530349b5458e7a511b80003567a42c9945c4de64545f81e45846cf4278bec5b800051696ac3f000022a9b4ce2003e183222526679c00a121475e97018da58122c53546f11bc0180b041d07190e60280ef105c74441e3140f4c0008634c3000040e000138151546a9233af800047630e0ae1be84d4000000199800030f0000520fc647240b1d540000000000000400000000000048c2d600015e0722543105073800050940d15dcba259e364a8d800000000011e80000000001fd8aa201536100000002e823c0d588163e232b8c493169612401e6c23200000015348900002d8236940000a0001f30d4ca06089819893e76c13a1fe8000000000185400043129814641860002060000a300000799e7535622b00000008780002ae8000ff8000386a2301543cc2ee0f04fa02ff3b180011644cb00000000002c3045a4e800052b3c221d008e7ee19b82f800037913600180000140200040fc00800401c0000080040140081d800400002801c0000140140000000080000f000c00001803c00001000400800400006c03003400400004402801001c00802401002001000000c00000400800802800008802802400c01c01802c00800c14400000000003c0000200040140000000040580480340000e80000d400c00800400800c00002000001000800802001c00806000001400000803c000074070080008
  | 21 => 0xce093cb7c86015482d8c709010340ea8bc09eb3bc271c2726bb23b87cd1ee6ab48312b098a73543a862903602c2e114e06c66cc0001f640009c80ca869d46e46302721c810c4763b480000166bc2a61074c2051b4b8a1788ea0004868358000097147812832e50e0c6800122e47c06916a84121a92e822ecb6661e3e09704d5a5e74950000ec00000748000a7e0000b9920c0007c441510cc0007ff0991dac2186b40c90be80002ec11ca2a43ea4eb332207ce4097d20901fc39a45a2020888cbc0000001dec6c05b10bf05e400016434825a80d4a2e18817c02c6a2b0001a8c0006633f61dc47ae0000000000a426762cfa8ec74693c4fa88cce802f7180090458a0004d415201d873923580007c60080000000000516000278cb4c44500000013b800024c86580002b52a123189b200050480000000001a718a92a200000000000009f633b9058bc20002c2068c0000f03b8159924a7811cb892ce140004c61fcc00016b3350ef904c44c34b8000d40000000009cda41911a4282c39e15825087490380001921dd40000003ed000087e0003359a6cfbc85c1c5a5580002b70000000b7053c0001d18f9c0004ea117c00027500011810267b70001a00cb06ed07b07587d889a0a61af84dc6820000cf0ea405e30c16940329be1ea9cb126243b17885889a2182264203400050b0f8000066200046ca25800086202e80000fa44314a9db8afe6c53b919752ae23e01a075038e12637e0df84ca05c36581f057063d301256013a5de4b48a6d0fa8c438f00004f80bb451901888e29244597f8c00524370183c7c82c145a0000dc435a3858000a6e9103e69f0869e24e00024a45f8313139a7e48685d624412692c838a4a79044e700001dd924d13800047d18712da5bb4e48eac5c48f622f029c31e03a29d053cb1c4873b691988b20811ee018107a2064a50c0d47006d4bf000043c69a066a01ce306cd1d883ad1d06bd0ba164865e4023f90c289627944dd041023e9f728e09a4ede1d925c1bd13320931ce9f74c9a2d009505d81f6108029939c8fc154021a20cc1a4b5404261c8003ac00012a816a4bb3ec0a303dc5b6326095c000000507a67ce864e829f0b900008f0151a21822c2191aa191866831e40f0df0ffa16109c0decfce2154280000a9e6d629910b40000000c712f051070f0000000e8e15f20c91a00006883bb01503f8a022e2a1a124e6413af28384cc2af41789e448e77f3ef819104a0000911da0ffc3292368f64e10a0d1a50a944b63f511b06dc25a1fe0cc89c40001332eb8330a28451148204891411c4440d909ae1ae00014693f40002c680005446f8162033cecc4222ad243928e4db4b10000d3c3cb2950000000011000106c00023d00021e814c75a00000000003e64b59de80007ca3270cf8d1227f25680000001a44dda1207
  | 22 => 0x14a0000c8c57486b078800000045331200000005592ed20048a85f54060988884529264923038a160000016c97299500025e01a023c2ca045400000051780c114010108889090a83d11189444fd689336c16e50e252e50d800097482908915c400071a16605e897a82d359999c0004f4000004042e0004c895a400099e3759f1c60820400021b4c268c932a000000052600007d000000000000091e60f92cb10151503f802ba79017e7bd000138855819400018dd24267e10e864c42602500000011cc19b1f003193be6b200000008ce66802b00cd32017039400005d24f7000000000082851380013420001c390b00000002bc80002cc55f144841d41887c27c81941e47a038180000007002f98000b9c744135800064e86706a8000ce021a0000729388627000000083464a17a269cfe03db1c9072c7e84ab05a0508522895007236c78801226700014505f80f625dd22850037f84bc94408c305942892a4444c9a144e829374811d2009200030281c4e2471b2321ac0ace8c800004684220e83e313b01ee2bb468126c5a688d00016d131c04600021851f62550be1f4cc6c8382ce00000009b534197fc26253b00006990944e64eba6cca8c83651220884b872a4352214c6464326b00013345c715a2594a0631d3ac0d051c80002ab2524046701000000142400000180000007ad0849a3851ca391078d18cdc4a8210a354d5e8a52e400000009e74ee882cfc400022580002a20004c6800135c6b100027f8a243f028f1eb812400004000014102263fc1e68cda2f82a58c209aa85551a0d445781870380dc91ce8f900008bc0006651a580000003b92928000d70575257134135a8d42290660af670403d263c00036132b13f533072d30708608801f13c91e4cad621400e140430840d130a35c3c826850a975007e47f3048948dca1b90ff988539e84b2d4000000096700000000000000e890e82820243540a9c36477331f000000056300022748382bf00000000400000000000a663831b80f191d43cd17928444f426700023945300000000000000000241104cbaa0003d394310fc6ee31a8bd4d5c88f31d1c1848816944080002527cb35b154d06a000164000067e0000000f587a835f30889e01f85fb2268210b807b432910a09f442f45b99f0fd48b50f00fa0dd87b0252860497e558194161cb4090c3c489f43783fd377a010e1225e01c909537a5c44a28a2823c2a426a05ec9e0282281094002601f1d4a3d0f6c565511a69874e63b50d11713069b8397a3f8e525ca3171ad4a8205808a2334fee2e32a00db8bfa55c3fa234d0ae62604d94bcd584b04678240a580c51a60e5143a44131485a104e5bd3cba47d3de83c165013d10072745992111c66b72ab94a0b0267426e8474e4a75708723845cc84c410a1e00a49f1304148004c1e30
  | 23 => 0x4e19a653da38249d97483b04a91d29060c3e6c02e7a360c689c52e322c400038e42f8000d8873d3c304080004c73e199fd06897337e80003aa6dd4c5040c6e63da25b056803034544f02603d41721af26bc00089b00000151141d01f988b947400000026fd09c6014e0896017430950b1c907669420469b8ce9a93005107dce2e8663e7823c4c68004cb0cd414642044b8a580ce56832d05783ae0482709e30fc08a41f500a80b24a74ae93a92223a416700ed3123111e3859cd3e9b42f91de485683f1a82748ca05151f5934d2bc7db041011523633a2e9836446816f0ba9eb02ba97a437018916003624c1a606566753680a1c91e0d305c8c044929db19297d90e019a3631290b2a7513b0a41d27c1773f082711b80dc477256c76e9384610dd4cc465511fa2d89e63b62aa28c053c333014800044e2cb12a086c64c1b0000000000006b30d00008ba7af10b05fc6b21860ef94180000d421f035c00000000002b02ca8062d08000000000482a0b0000000115068813c6bf00f041491a02b128a0c499e11017724a00000000aaa0c013e04427488d522a374168a15800050400007700000000dc28cd2de00005913c4000000000237d2dc80f45508853944351e515bceca6c3000000039800000000006546ea343217400000019c214d2860002b08374ac093400021dcde63bc2fe172448a5ac351094cbc42c606216bc86c16d1ae243d3108d214ba0508f6491201a328bb03521990a85338918000078460a00026e1a48be266018a0fa43c47dc12ca4680004e443213186f42b200020142149a2000185c0000000541774920976026800097c3f131e0dd88fa2cd2f19becc283bf21ea05ceee56229c86fc28e4de1118f3c70c5ba1f79c5800036919700f512226d000000081000000024b4f6a04046b1f905c23de09ba2851825bf3df8b5d17230c0000000bee000000000086e03c04399e80008ec37091186ba0000548990702388190151007036806d21d8a447a62f4a4f40aa2764f9a4bc89c59840526b0c0800009e0c602482f6424a32c3ce1900390c64dec65f12b12c88a012830b10505549d50f7a7eccde7bb33d81d52004ed000163c8e6a1748584fc0007b2000257d0b20510371f44f7858921480040004741f393012d00000c1800000086c41b800147800000000000004794a424640000ef00000000de20c0001aa8a1e42a2f780013f81c33f300000008fc00000000000fe0000e61282a18415a52c33e46e319a87c7fe3e542d00012b43fe37f0bf8c5634301903d13363fa4198a18774649353a5d50725a236d13d46347072bea038ec4695519102914459705b855c2ac7c82c804ed3fa4570000d1c000462000181817090a10f82851d6378072026918e4ca4d5285000000049aa8a91a226000026010ca3fb000048c3542dd45e8000
  | 24 => 0xeb20004a99c084e400024b8000bbe20d2f29cc4cf200044386d49b000042300005609b12b69c852a825d27c1828c4a642330a2acf722250001fbc9380ed09ea1080007a84f2a864de073716f210000000011d018530a4862d906b091ca221b780587ec1b1345838534a1c83dc00000008e02af10c8afc7a137200010322284bc938cdf26310d9a448f047493e4a2e00005b5114a84ce7662250803e93a264b00b9038a462bd41228049de95200009305f20000000c5872a00017516b88ac69109088b0dea3b23d525d0bd40004601a3c35e6733f697b4c5e0061a01248f0a7110001434e966e726f8674ad8415323a6100629364e72764f6273e067045c3405c31810a50672a263ada0603823773cc800076a25f06086ec48600005724ac00075418f92801400c81b500012f69bc21c852c53a3a844723e09165ee4b3216015e2e702d1e453fe9b623612d01ce8be4e80a64ca29a038a0fc8c723ce000000000053d44f80010043583ae83600000002898000000000478a6081fe0044f527a029a2f03d49ae82860e03fd836ce0a9ec00015285a89cd3670300c400001b59a1c00088401ba6dd20812500000007802fd140029018e00049106011300001cf1764c066a5352020c3ba6070529fa42b697f3ab220843875350383b8f1e9f23a51554000583501a5388d49c619b068404232147e9c8c10a10f12d240c6fe0502b994c40e84583c39920bcc1f9000041884c5eb1191df8f56366164947472079615f01dc30a4940a29ba4cb238d1a48d6d14e0bc38a86e87849ee4491278aa4a1c0da1cad2aa6c116c030801e0b342090e11748ae33c112470856a27b20f83505bc169163029c00001a9f00adc4a33e900000004b7055800093a1eb1ec000108a00000000000000001a120249a45a727fa0ec5260000000db4de24654e98ef45569e02e68000b226b91b3800054059a34284800006de1418cf40000000398d34b961fd14d200c26c04b48e9a4d03a71c51282580000003c18880000000179800098600000024800000004d90000b1017d000118400077d00000004708f51070264984424120000011c1461588f248022240000eb505c94c466122499a7332dba2bcb169c20178000e9c00000004b918a58500004e8f308e9496000000000007a976cd949630e214d84f633004a9a70c187ba08683f4ece8f23ba07241be78800020c824e4c400019f4b0484d22788c055c96c3c72498d023b03d999712a00003980000d8e27700003980004a6399000060e07b4ef000000012c000244c75c0001c61874902000502818ce6c3ee00024e4da29e1456a7c03ec6f70b8a1a4af48793c521fd29a3d000027000000bd21380000000001b89bc80001fa4290e8541400042200000000000b60d4c0000000000a340001be00025c854c0003508cb547a66c
  | 25 => 0x53e894339000076801d026141c68872e0e980000000cb2d19e00ea012b1cfa05456655b2118000b5a1300f90000c889e20000bb45087be5189c4c00037d4cb9cd05ca2052bb19a405a99d24b1f5400016a00026a470a00d260800114c3a64eb12cc3161da000080cce21c0000076c9fc01a06f000036c5fa00000000001e83930d9455000000017d01ca1403eba4b8fac31503603e000000000000000009b04fc000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x1c3041140765053000718084509d9214c001c602114076485300be98a0021d95214c03507b9760254d95200cc1ee5d8094f6548033458901d4735912000706dd0501cd6448001c48501cf725912000714dcc50dc56448001c507314371591200bd1c240751c56448001c3374140715912000714dcc501c56448001c5073140715912000718dc8501c5644800185b8314176551200ce1620c505d954480018738114176551200be1c204505d95448035438901d47458d200070614074dcd6348001c28501d37258d200070cdd050dc56348001c30741437158d200bd1c240751c56348001c33741407158d200070c1d0501c56348001c53731407158d2000718dc8501c5634800183b841417654d200d60e210505d95348001873811417654d200be1c204505d95348001c18431427650d200060ee10505d9434800185b831417650d200061ae08505d94348001873811417650d200be1c204505d94348001c18431407650d200070c104509d94148001c304114076505200be8ca0041d954148001c5031142764c520007140c4501d9314802fa52800c7654c5200d41ee5d80953654403307b9760253d95100cd16240751cd6444001c1b74140735911000712dcc50dc96444001c487314372591100c51a240751c96444001c2b74140725911000712dcc501c96444001c487314072591100071414073dc56444001c60501cb715911000616e0c505d954440338588314176551100061ae08505d954440318688214176551100d50e240751d16344001c18501d37358d100070add050dc96344001c28741437258d100c51a240751c96344001c2b741407258d100070a1d0501c96344001c4b731407258d100070c14074dc56344001c60501cb7158d100060ee10505d95344035838841417654d100061ae08505d95344031868821417654d100070610c509d9434400183b841417650d1000616e0c505d9434400186b821417650d100c61a208505d94344001873811417650d100070610c501d94344033a1a8010f6550d100d50e240751d16244001c1b741437358910007061d050dcd6244033458901d4735891000706dd0501cd6244001c187414073589100070a14074dc96244001c48501cf72589100070c14074dc56244001c50501cf71589100060ee10505d9524403583884141765491000616e0c505d952440338588314176549100041e66365dc15244001c284214276509100060ee10505d9424400185b8314176509100ce1620c505d9424400186b8214176509100061ce04505d94244001c284214076509100c68aa0042d954244001c4832142764c91000c1ea43855d9324400183b84141764c9100d60e210505d9324400185b83141764c9100061ae08505d9324400187381141764c910007120c8501d93244031a4a800cb654c910
  | 1 => 0x45ae49865d1321400117391619744c8500bc5c245865d1321400313898591744c85000c56261635d1321400316898589744c8500055464f61dc5321400156192d87714c8500061661b63dcd411400151994d8f73504500055464763dcd411400152994d8b72504500055864762dc9411402f13a97e1132504500bccca47844c9411403115a98dcd325045000646e13734c9411403154a92dcd32504500cc5aa63724c9411400192b84dc932504500cd52a4f724c9411403517297e0532504500d4cca53814c9411400195373e05325045000658dcb814c9411400183986d93744c4500054664f64dd1311400153191d93744c4500044ee51865d1311400115b93619744c4500045ae49865d1311403116892619744c4500045ce45865d1311400313898591744c45000c56261635d1311400317098585744c4500055264f62dc9311400156191d8b724c4500c44ea6374509311403152a92dd1424c4500bc56a5f83509311400191b74e0d424c4500bcd4a4783509311403516a98dc9424c4500d54aa5372509311400194b83dc9424c4500cc5ca5f81509311400193374e05424c4500ccd4a4f81509311400196372e05424c4500060e61b64dd1211400152992d9374484500054c64764dd1211400113b94619744845000456e4d865d121140331589361974484500045ae49865d1211400117391619744845000c4e261645d1211400383886591744845000c5a261625d1211400386886589744845000c5c261615d121140038708658574484500061661b63dcd211400154992d8f73484500055464763dcd211400113b9461973484500d44e251865cd211400115b9361973484500045ae49865cd211400117391619734845000c56261635cd21140038588658d734845000c5a261625cd211400386886589734845000c5c261615cd21140038708658573484500041ee598750d21140030789661d43484500cc4ea637450d211403351a93dd143484500d456a637350d211403551a94dcd43484500bc5aa5f8250d211400192b74e09434845000652dcf8250d211402f36291e0943484500c45ca5f8150d211400193374e05434845000654dcf8150d211403136292e0543484500cc1ee5d8094f6550001c4832142764c940007120c8501d93250001c5031142764c540007140c4501d93150001c6021142764854000718084501d9215003507b9760254d95300c51a240751c9644c001c2b74140725913000712dcc501c9644c001c63721437159130007181c850dc5644c02f470901d471591300070cdd0501c5644c001c5373140715913000718dc8501c5644c001c607214071591300061ae08505d9544c0318688214176551300061ce04505d9544c02f8708114176551300070a108509d9424c001c284214076509300070c104509d9414c
  | 2 => 0x801d084214373581420074810850dc56050801d08321437459532007500c850dc5654c801c18501d373595320070a14074dc9654c801c337414371595320070c1d050dc5654c801c337414071595320070c1d0501c5654c801c5373140715953200718dc8501c5654c835838851d070595320be1c214711c1654c801c483214376551320060ee10505d9544c80185b8314176551320061ae08505d9544c8018738114176551320be1c204505d9544c801c48321407655132007420c850dd1604c801d403214371581320070610c509d94354401c18431407650d510070a108509d94254401c28421407650951007120c8509d93254401c4832140764c9510074410450dcd6550401d2041143725954100706dd0501cd6550401c4b731437259541007121cc50dc96550401c2b74140725954100712dcc501c96550401c487314072595410071414073dc56550401c60501cb71595410ce16214731c16550431868851c870595410070c10450dd95350401c30411407654d410070c10450dd95250401c304114076549410074410450dcd6050401d20411437258141007440c450dd1654c401d403114372595310070614074dcd654c401c2b7414372595310070a1d050dc9654c401c2b7414072595310070a1d0501c9654c401c4b7314072595310070c14074dc5654c401c60501cb71595310d60e214741c1654c431868851c87059531007140c450dd9544c40183b84141765513100616e0c505d9544c40186b8214176551310c61a208505d9544c401873811417655131007140c4501d9544c401c50311437654931007140c4501d9524c401d10311437458131007500c450dc9604c401d202114374595210075008450dcd6548401c1b741437359521007061d050dcd6548401c1b741407359521007061d0501cd6548401c28501d372595210071214073dc96548401c30501d371595210071414073dc56548435838851d070595210ce16214731c16548401c602114376551210060ee10505d9544840185b8314176551210ce1620c505d9544840186b8214176551210061ce04505d95448401c602114076551210071808450dd9534840183b841417654d210d60e210505d9534840185b831417654d210061ae08505d95348401873811417654d2100718084501d9534840307a90e157650d210341ea57805d94348401d202114374581210075008450dcd6048401079981437650d500061a61b62dc9431400152994d8b7250c500055264f62dc9431400187186d877150c500054c65361dc5431400155193d877150c500061661b63dcd421400151994d8f73508500055264b63dcd421400153194d8771508500055864b61dc5421400183986d93744c8500054664f64dd1321400152992d93744c8500044ee51865d1321400115b93619744c85
  | 3 => 0x9c000001f800000c4000000009aa90dc000440008a6ca1e002ca64a803b9660000000108b70900019400050ab000002203480009a9600202b60001617200218000001ba8a532bab900000240000b20011011828101fa98800658003b00000000001200000061256000041a8003680000134a516e338be070005f0006803e4a00e000ba9081e000006787a8b9524111c759124580034236061e2000a274000000000000000216520969f824929bc920200002eb418c6c0020203a4f232608000f03088800000524797ab82b884000b127c768006e8221b0a00022439a52498ac74800781dc9e1f40001427a34000001f2da2985c0680082800000563d18e79000628000014677986a80001280000000002c20013a00000ac000000880026a3c800208000000000000aaaf00025e4f8124080000000001989b85e000001e1b86a1700415e3c1eeb005430a12ac80a1d8000011aad974000b618900ad0e0002e8002c800188002d28a9aa1c00043000000b41926c00000002766f9a67a1cea8a68a21c6000069eabc001ae001f0709900000c1090a000008189400000550860020cb18000019c3f20e001fe821b67025831a9812178130004c1ec2915c0028cbb1c83d9602ba2620180000fa1caea4d9d4001f8000000c8e2590d4a780000000452f868906489cc3200037a468529a0023a5a1620aad450a4472ace000008c05a510000000000290001560e000002047daee6b0b800176ab9ea930349524e001240da5cbd8006d2be9d0c00000000150b9800b30e4bd292760008b29c000743a9c4528008f12cbc8005a918058f8b58000b2382a9fc00000000005f8b000000004080000200c050000000400004000000001c00010030040201c000040100c0400400000000140000000008000000300000004060140002802014000040000c040140700800008040001904407000050080100413018040140000003004000240000800000010002000c02000010100201c0501c030080000000000000000303401008090040002800000090080d0080304c0106402018010080401401d084314372595430074410c50dc56550c01c2b74140725954300712dcc501c96550c01c63721437159543007181c850dc56550c01c3374140715954300714dcc501c56550c01c63721407159543007181c8501c56550c31868851c870595430be1c214711c16550c01d084314372581430074410c50dc56050c01c18431427650d520070610c501d94354801d084214373595420074810850dc56550801c1b7414073595420071214073dc96550801c53731437159542007141cc50dc56550801c3374140715954200714dcc501c56550801c5073140715954200718dc8501c56550833858851cc70595420be1c214711c16550801c28421437654d420070a108501d9535
  | 4 => 0x14e000009c80000000361328012e0008c260000028e799589428686a3e3316c96a84a984e24ae2668ca9808e50282182a84e10e870002f000002708a1f2690e8990fe358000012a56800002de000002a0002126600068198
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x3
  | 4 => 0x4
  | 5 => 0x5
  | 6 => 0x6
  | 7 => 0x94e
  | 8 => 0x94b
  | 9 => 0x94c
  | 10 => 0x94d
  | 11 => 0x98e
  | 12 => 0x98a
  | 13 => 0x98c
  | 14 => 0x98d
  | 15 => 0x9ce
  | 16 => 0x9ca
  | 17 => 0x9cb
  | 18 => 0x9cd
  | 19 => 0xa0e
  | 20 => 0xa0a
  | 21 => 0xa0b
  | 22 => 0xa0c
  | 23 => 0x14a
  | 24 => 0x14b
  | 25 => 0x14c
  | 26 => 0x14d
  | 27 => 0xa4a
  | 28 => 0xa4b
  | 29 => 0xa4c
  | 30 => 0xa4d
  | 31 => 0xb09
  | 32 => 0xb0c
  | 33 => 0xb0d
  | 34 => 0xb0e
  | 35 => 0xb49
  | 36 => 0xb4b
  | 37 => 0xb4d
  | 38 => 0xb4e
  | 39 => 0xb89
  | 40 => 0xb8b
  | 41 => 0xb8c
  | 42 => 0xb8e
  | 43 => 0xbc9
  | 44 => 0xbcb
  | 45 => 0xbcc
  | 46 => 0xbcd
  | 47 => 0xcc9
  | 48 => 0xcca
  | 49 => 0xccd
  | 50 => 0xcce
  | 51 => 0xd09
  | 52 => 0xd0a
  | 53 => 0xd0c
  | 54 => 0xd0e
  | 55 => 0xd49
  | 56 => 0xd4a
  | 57 => 0xd4c
  | 58 => 0xd4d
  | 59 => 0xe89
  | 60 => 0xe8a
  | 61 => 0xe8b
  | 62 => 0xe8e
  | 63 => 0xec9
  | 64 => 0xeca
  | 65 => 0xecb
  | 66 => 0xecd
  | 67 => 0x1049
  | 68 => 0x104a
  | 69 => 0x104b
  | 70 => 0x104c
  | 71 => 0x1549
  | 72 => 0x1409
  | 73 => 0x150a
  | 74 => 0x128a
  | 75 => 0x16c9
  | 76 => 0x1449
  | 77 => 0x168a
  | 78 => 0x12ca
  | 79 => 0x1849
  | 80 => 0x1489
  | 81 => 0x180a
  | 82 => 0x130a
  | 83 => 0x2c9
  | 84 => 0x14c9
  | 85 => 0x198a
  | 86 => 0x19c9
  | 87 => 0x134a
  | 88 => 0x138b
  | 89 => 0x124b
  | 90 => 0x1709
  | 91 => 0x15c9
  | 92 => 0x168b
  | 93 => 0x12cb
  | 94 => 0x1889
  | 95 => 0x1609
  | 96 => 0x180b
  | 97 => 0x130b
  | 98 => 0x449
  | 99 => 0x1649
  | 100 => 0x198b
  | 101 => 0x1a09
  | 102 => 0x134b
  | 103 => 0x138c
  | 104 => 0x124c
  | 105 => 0x150c
  | 106 => 0x128c
  | 107 => 0x18c9
  | 108 => 0x1789
  | 109 => 0x180c
  | 110 => 0x130c
  | 111 => 0x5c9
  | 112 => 0x17c9
  | 113 => 0x198c
  | 114 => 0x1a49
  | 115 => 0x134c
  | 116 => 0x138d
  | 117 => 0x124d
  | 118 => 0x150d
  | 119 => 0x128d
  | 120 => 0x168d
  | 121 => 0x12cd
  | 122 => 0x749
  | 123 => 0x1949
  | 124 => 0x198d
  | 125 => 0x1a89
  | 126 => 0x134d
  | 127 => 0xb0154
  | 128 => 0xb0155
  | 129 => 0xb4153
  | 130 => 0xb4155
  | 131 => 0xb8153
  | 132 => 0xb8154
  | 133 => 0xcc152
  | 134 => 0xcc155
  | 135 => 0xd0152
  | 136 => 0xd0154
  | 137 => 0xe8152
  | 138 => 0xe8153
  | 139 => 0x138e
  | 140 => 0x124e
  | 141 => 0x150e
  | 142 => 0x128e
  | 143 => 0x168e
  | 144 => 0x12ce
  | 145 => 0x180e
  | 146 => 0x130e
  | 147 => 0x170a
  | 148 => 0x15ca
  | 149 => 0x16cb
  | 150 => 0x144b
  | 151 => 0x188a
  | 152 => 0x160a
  | 153 => 0x184b
  | 154 => 0x148b
  | 155 => 0x1a0a
  | 156 => 0x164a
  | 157 => 0x19cb
  | 158 => 0x14cb
  | 159 => 0x154c
  | 160 => 0x140c
  | 161 => 0x18ca
  | 162 => 0x178a
  | 163 => 0x184c
  | 164 => 0x148c
  | 165 => 0x1a4a
  | 166 => 0x17ca
  | 167 => 0x19cc
  | 168 => 0x14cc
  | 169 => 0x154d
  | 170 => 0x140d
  | 171 => 0x16cd
  | 172 => 0x144d
  | 173 => 0x1a8a
  | 174 => 0x194a
  | 175 => 0x19cd
  | 176 => 0x14cd
  | 177 => 0x4e
  | 178 => 0x154e
  | 179 => 0x140e
  | 180 => 0x16ce
  | 181 => 0x144e
  | 182 => 0x184e
  | 183 => 0x148e
  | 184 => 0x18cb
  | 185 => 0x178b
  | 186 => 0x188c
  | 187 => 0x160c
  | 188 => 0x1a4b
  | 189 => 0x17cb
  | 190 => 0x1a0c
  | 191 => 0x164c
  | 192 => 0x170d
  | 193 => 0x15cd
  | 194 => 0x1a8b
  | 195 => 0x194b
  | 196 => 0x1a0d
  | 197 => 0x164d
  | 198 => 0x8e
  | 199 => 0x170e
  | 200 => 0x15ce
  | 201 => 0x188e
  | 202 => 0x160e
  | 203 => 0x1a8c
  | 204 => 0x194c
  | 205 => 0x1a4d
  | 206 => 0x17cd
  | 207 => 0xce
  | 208 => 0x18ce
  | 209 => 0x178e
  | 210 => 0x10e
  | 211 => 0x154b11
  | 212 => 0x140b11
  | 213 => 0x15512
  | 214 => 0x171411
  | 215 => 0x189411
  | 216 => 0x16cb51
  | 217 => 0x144b51
  | 218 => 0x15692
  | 219 => 0x15d451
  | 220 => 0x18d451
  | 221 => 0x184b91
  | 222 => 0x148b91
  | 223 => 0x15812
  | 224 => 0x161491
  | 225 => 0x179491
  | 226 => 0x209
  | 227 => 0x14992
  | 228 => 0x249
  | 229 => 0x149d2
  | 230 => 0x289
  | 231 => 0x14a12
  | 232 => 0x19cbd1
  | 233 => 0x19d4d1
  | 234 => 0x3c9
  | 235 => 0x409
  | 236 => 0x589
  | 237 => 0x15393
  | 238 => 0x16d551
  | 239 => 0x185551
  | 240 => 0x170cd1
  | 241 => 0x15ccd1
  | 242 => 0x15693
  | 243 => 0x1455d1
  | 244 => 0x18d5d1
  | 245 => 0x188d11
  | 246 => 0x160d11
  | 247 => 0x15813
  | 248 => 0x149611
  | 249 => 0x179611
  | 250 => 0x14953
  | 251 => 0x149d3
  | 252 => 0x14a13
  | 253 => 0x1a0d51
  | 254 => 0x1a1651
  | 255 => 0x15394
  | 256 => 0x1556d1
  | 257 => 0x1856d1
  | 258 => 0x15514
  | 259 => 0x141711
  | 260 => 0x189711
  | 261 => 0x18ce91
  | 262 => 0x178e91
  | 263 => 0x15814
  | 264 => 0x149791
  | 265 => 0x161791
  | 266 => 0x14954
  | 267 => 0x14994
  | 268 => 0x14a14
  | 269 => 0x1a4ed1
  | 270 => 0x1a57d1
  | 271 => 0x15395
  | 272 => 0x155851
  | 273 => 0x16d851
  | 274 => 0x15515
  | 275 => 0x141891
  | 276 => 0x171891
  | 277 => 0x15695
  | 278 => 0x1458d1
  | 279 => 0x15d8d1
  | 280 => 0x14955
  | 281 => 0x14995
  | 282 => 0x149d5
  | 283 => 0x1a9051
  | 284 => 0x1a9951
  | 285 => 0x14cd2
  | 286 => 0x15712
  | 287 => 0x155d2
  | 288 => 0x156d3
  | 289 => 0x15c152
  | 290 => 0x144153
  | 291 => 0x14d12
  | 292 => 0x15892
  | 293 => 0x15612
  | 294 => 0x15853
  | 295 => 0x160152
  | 296 => 0x148153
  | 297 => 0x15554
  | 298 => 0x170152
  | 299 => 0x140154
  | 300 => 0x14e92
  | 301 => 0x158d2
  | 302 => 0x15792
  | 303 => 0x15854
  | 304 => 0x178152
  | 305 => 0x148154
  | 306 => 0x15555
  | 307 => 0x188152
  | 308 => 0x140155
  | 309 => 0x156d5
  | 310 => 0x18c152
  | 311 => 0x144155
  | 312 => 0x16c153
  | 313 => 0x154154
  | 314 => 0x14e93
  | 315 => 0x158d3
  | 316 => 0x15793
  | 317 => 0x15894
  | 318 => 0x178153
  | 319 => 0x160154
  | 320 => 0x184153
  | 321 => 0x154155
  | 322 => 0x15715
  | 323 => 0x18c153
  | 324 => 0x15c155
  | 325 => 0x184154
  | 326 => 0x16c155
  | 327 => 0x188154
  | 328 => 0x170155
  | 329 => 0x14b14
  | 330 => 0x14b15
  | 331 => 0x154b16
  | 332 => 0x140b16
  | 333 => 0x14b53
  | 334 => 0x14b55
  | 335 => 0x16cb56
  | 336 => 0x144b56
  | 337 => 0x1a57d2
  | 338 => 0x14b93
  | 339 => 0x14b94
  | 340 => 0x184b96
  | 341 => 0x148b96
  | 342 => 0x1a9952
  | 343 => 0x15652
  | 344 => 0x14d52
  | 345 => 0x157d2
  | 346 => 0x14ed2
  | 347 => 0x15952
  | 348 => 0x15052
  | 349 => 0x171416
  | 350 => 0x189416
  | 351 => 0x15d456
  | 352 => 0x18d456
  | 353 => 0x161496
  | 354 => 0x179496
  | 355 => 0x14cd5
  | 356 => 0x170cd6
  | 357 => 0x15ccd6
  | 358 => 0x1a57d3
  | 359 => 0x14d14
  | 360 => 0x188d16
  | 361 => 0x160d16
  | 362 => 0x1a9953
  | 363 => 0x154d3
  | 364 => 0x14bd3
  | 365 => 0x157d3
  | 366 => 0x14ed3
  | 367 => 0x15953
  | 368 => 0x15053
  | 369 => 0x16d556
  | 370 => 0x185556
  | 371 => 0x1455d6
  | 372 => 0x18d5d6
  | 373 => 0x149616
  | 374 => 0x179616
  | 375 => 0x18ce96
  | 376 => 0x1a57d5
  | 377 => 0x178e96
  | 378 => 0x1a9954
  | 379 => 0x154d4
  | 380 => 0x14bd4
  | 381 => 0x15654
  | 382 => 0x14d54
  | 383 => 0x15954
  | 384 => 0x15054
  | 385 => 0x1556d6
  | 386 => 0x1856d6
  | 387 => 0x141716
  | 388 => 0x189716
  | 389 => 0x149796
  | 390 => 0x161796
  | 391 => 0x154d5
  | 392 => 0x14bd5
  | 393 => 0x15655
  | 394 => 0x14d55
  | 395 => 0x157d5
  | 396 => 0x14ed5
  | 397 => 0x155856
  | 398 => 0x16d856
  | 399 => 0x141896
  | 400 => 0x171896
  | 401 => 0x1458d6
  | 402 => 0x15d8d6
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 65
  | 7 => 1455
  | 6 => 4327
  | 5 => 2622
  | 4 => 381
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 9 => packedAt gbK9 (i*15) 6
  | 8 => packedAt gbK8 (i*26) 17
  | 7 => packedAt gbK7 (i*37) 28
  | 6 => packedAt gbK6 (i*48) 39
  | 5 => packedAt gbK5 (i*59) 50
  | 4 => packedAt gbK4 (i*70) 61
  | _ => 0
def gbH (k i : Nat) : Nat :=
  match k with
  | 9 => gbHint (packedAt gbK9 (i*15+6) 9)
  | 8 => gbHint (packedAt gbK8 (i*26+17) 9)
  | 7 => gbHint (packedAt gbK7 (i*37+28) 9)
  | 6 => gbHint (packedAt gbK6 (i*48+39) 9)
  | 5 => gbHint (packedAt gbK5 (i*59+50) 9)
  | 4 => gbHint (packedAt gbK4 (i*70+61) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 9 => packedAt gbK9 (16+((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 2)*1) 1
  | 8 => packedAt gbK8 (1837+((h/21+packedAt gbK8 (1690+(h % 21)*7) 7) % 86)*8) 8
  | 7 => packedAt gbK7 (59170+((h/485+packedAt gbK7 (53835+(h % 485)*11) 11) % 1747)*12) 12
  | 6 => packedAt gbK6 (226442+((h/1442+packedAt gbK6 (207696+(h % 1442)*13) 13) % 5193)*14) 14
  | 5 => packedAt gbK5 (165186+((h/874+packedAt gbK5 (154698+(h % 874)*12) 12) % 3147)*13) 13
  | 4 => packedAt gbK4 (27940+((h/127+packedAt gbK4 (26670+(h % 127)*10) 10) % 553)*10) 10
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffffffc0fc01f803f007e00031fc7fffe38e38
  | 1 => 0xc01fffff0001fffffffffff1ce6398c703ffff
  | 2 => 0xffe00ffffffe0003fffffffe0f83e0f8fc0fff
  | 3 => 0xffffffffffc0007fffff003ff00fff03f
  | 4 => 0xffffffffffffff8000ffffc0000ffffc0
  | 5 => 0xfffff000000000000000000fffffffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0xc3a1dfc02c6858d0b1a1634010ac2b5be38e38
  | 1 => 0x489de2cb0000ab5556aaad50c66198c501b6db
  | 2 => 0xbbc4455555aa00026b34d6660b82e0e86c0b6d
  | 3 => 0x110889a69acd359800071b8b70037d00b6d036
  | 4 => 0x22110e38e371c6e38dc0000dbdf40000db6d80
  | 5 => 0x3c1e0000038007000e001c0fef5bd6b6000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeaa8fcc0c000feeaeaa8fcc0c000feeaeaa8fcc0c000feeaeaa8fcc0c000feeaeaa8fcc0c000feeaeaa8fcc0c000feeaeaa8fcc0c000feeaeaa8fcc0c000, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_12887
namespace PEqualNP.Outside.L_meta_12887
open PEqualNP.Outside.L_meta_12887.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 66 := block_range (n:=66) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 66 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_96 : Interval s0Atlas 3 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_192 : Interval s0Atlas 3 192 87 := block_range (n:=87) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 279 := (concat bs0_3_0 (concat bs0_3_96 bs0_3_192))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_96 : Interval s0Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_192 : Interval s0Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_288 : Interval s0Atlas 4 288 14 := block_range (n:=14) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 302 := (concat (concat bs0_4_0 bs0_4_96) (concat bs0_4_192 bs0_4_288))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 24 := bs0_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 1 := bs0_6_0
theorem alls0 : ∀ k ≤ 6, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
  · exact alls0_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 64 := block_range (n:=64) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 64 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_96 : Interval s1Atlas 4 96 23 := block_range (n:=23) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 119 := (concat bs1_4_0 bs1_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 45 := block_range (n:=45) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 45 := bs1_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_6_0 : Interval s1Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_6 : Interval s1Atlas 6 0 1 := bs1_6_0
theorem alls1 : ∀ k ≤ 6, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
  · exact alls1_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 64 := block_range (n:=64) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 64 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_96 : Interval s2Atlas 4 96 23 := block_range (n:=23) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 119 := (concat bs2_4_0 bs2_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 45 := block_range (n:=45) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 45 := bs2_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 1 := bs2_6_0
theorem alls2 : ∀ k ≤ 6, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 64 := block_range (n:=64) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 64 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_96 : Interval s3Atlas 4 96 23 := block_range (n:=23) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 119 := (concat bs3_4_0 bs3_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 45 := block_range (n:=45) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 45 := bs3_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 1 := bs3_6_0
theorem alls3 : ∀ k ≤ 6, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
  · exact alls3_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 64 := block_range (n:=64) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 64 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_96 : Interval s4Atlas 4 96 23 := block_range (n:=23) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 119 := (concat bs4_4_0 bs4_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 45 := block_range (n:=45) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 45 := bs4_5_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 66 := block_range (n:=66) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 66 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_96 : Interval s5Atlas 3 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_192 : Interval s5Atlas 3 192 87 := block_range (n:=87) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 279 := (concat bs5_3_0 (concat bs5_3_96 bs5_3_192))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_96 : Interval s5Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_192 : Interval s5Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_288 : Interval s5Atlas 4 288 14 := block_range (n:=14) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 302 := (concat (concat bs5_4_0 bs5_4_96) (concat bs5_4_192 bs5_4_288))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 24 := bs5_5_0
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
theorem bgb_4_0 : Interval gbAtlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_96 : Interval gbAtlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_192 : Interval gbAtlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_288 : Interval gbAtlas 4 288 93 := block_range (n:=93) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 381 := (concat (concat bgb_4_0 bgb_4_96) (concat bgb_4_192 bgb_4_288))
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
theorem bgb_5_2592 : Interval gbAtlas 5 2592 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2622 := (concat (concat (concat (concat bgb_5_0 (concat bgb_5_96 bgb_5_192)) (concat (concat bgb_5_288 bgb_5_384) (concat bgb_5_480 bgb_5_576))) (concat (concat bgb_5_672 (concat bgb_5_768 bgb_5_864)) (concat (concat bgb_5_960 bgb_5_1056) (concat bgb_5_1152 bgb_5_1248)))) (concat (concat (concat bgb_5_1344 (concat bgb_5_1440 bgb_5_1536)) (concat (concat bgb_5_1632 bgb_5_1728) (concat bgb_5_1824 bgb_5_1920))) (concat (concat bgb_5_2016 (concat bgb_5_2112 bgb_5_2208)) (concat (concat bgb_5_2304 bgb_5_2400) (concat bgb_5_2496 bgb_5_2592)))))
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2016 : Interval gbAtlas 6 2016 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2112 : Interval gbAtlas 6 2112 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2208 : Interval gbAtlas 6 2208 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2304 : Interval gbAtlas 6 2304 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2400 : Interval gbAtlas 6 2400 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2496 : Interval gbAtlas 6 2496 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2592 : Interval gbAtlas 6 2592 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2688 : Interval gbAtlas 6 2688 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2784 : Interval gbAtlas 6 2784 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2880 : Interval gbAtlas 6 2880 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2976 : Interval gbAtlas 6 2976 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3072 : Interval gbAtlas 6 3072 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3168 : Interval gbAtlas 6 3168 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3264 : Interval gbAtlas 6 3264 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3360 : Interval gbAtlas 6 3360 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3456 : Interval gbAtlas 6 3456 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3552 : Interval gbAtlas 6 3552 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3648 : Interval gbAtlas 6 3648 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3744 : Interval gbAtlas 6 3744 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3840 : Interval gbAtlas 6 3840 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3936 : Interval gbAtlas 6 3936 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4032 : Interval gbAtlas 6 4032 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4128 : Interval gbAtlas 6 4128 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4224 : Interval gbAtlas 6 4224 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4320 : Interval gbAtlas 6 4320 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 4327 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 (concat bgb_6_288 bgb_6_384))) (concat (concat bgb_6_480 (concat bgb_6_576 bgb_6_672)) (concat bgb_6_768 (concat bgb_6_864 bgb_6_960)))) (concat (concat (concat bgb_6_1056 (concat bgb_6_1152 bgb_6_1248)) (concat bgb_6_1344 (concat bgb_6_1440 bgb_6_1536))) (concat (concat bgb_6_1632 (concat bgb_6_1728 bgb_6_1824)) (concat bgb_6_1920 (concat bgb_6_2016 bgb_6_2112))))) (concat (concat (concat (concat bgb_6_2208 bgb_6_2304) (concat bgb_6_2400 (concat bgb_6_2496 bgb_6_2592))) (concat (concat bgb_6_2688 (concat bgb_6_2784 bgb_6_2880)) (concat bgb_6_2976 (concat bgb_6_3072 bgb_6_3168)))) (concat (concat (concat bgb_6_3264 (concat bgb_6_3360 bgb_6_3456)) (concat bgb_6_3552 (concat bgb_6_3648 bgb_6_3744))) (concat (concat bgb_6_3840 (concat bgb_6_3936 bgb_6_4032)) (concat bgb_6_4128 (concat bgb_6_4224 bgb_6_4320))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_96 : Interval gbAtlas 7 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_192 : Interval gbAtlas 7 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_288 : Interval gbAtlas 7 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_384 : Interval gbAtlas 7 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_480 : Interval gbAtlas 7 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_576 : Interval gbAtlas 7 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_672 : Interval gbAtlas 7 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_768 : Interval gbAtlas 7 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_864 : Interval gbAtlas 7 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_960 : Interval gbAtlas 7 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1056 : Interval gbAtlas 7 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1152 : Interval gbAtlas 7 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1248 : Interval gbAtlas 7 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1344 : Interval gbAtlas 7 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1440 : Interval gbAtlas 7 1440 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1455 := (concat (concat (concat (concat bgb_7_0 bgb_7_96) (concat bgb_7_192 bgb_7_288)) (concat (concat bgb_7_384 bgb_7_480) (concat bgb_7_576 bgb_7_672))) (concat (concat (concat bgb_7_768 bgb_7_864) (concat bgb_7_960 bgb_7_1056)) (concat (concat bgb_7_1152 bgb_7_1248) (concat bgb_7_1344 bgb_7_1440))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 65 := block_range (n:=65) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 65 := bgb_8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_9_0 : Interval gbAtlas 9 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_9 : Interval gbAtlas 9 0 1 := bgb_9_0
theorem allgb : ∀ k ≤ 9, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allgb_4 i (by omega) hi
  · exact allgb_5 i (by omega) hi
  · exact allgb_6 i (by omega) hi
  · exact allgb_7 i (by omega) hi
  · exact allgb_8 i (by omega) hi
  · exact allgb_9 i (by omega) hi
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 7 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 36, 37),(inputs.getD 2 zero, 24, 28),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 34, 35),(inputs.getD 1 zero, 24, 26),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 34, 35),(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 18, 22),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 34, 35),(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 34, 35),(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeaa8fcc0c000feeaeaa8fcc0c000feeaeaa8fcc0c000feeaeaa8fcc0c000feeaeaa8fcc0c000feeaeaa8fcc0c000feeaeaa8fcc0c000feeaeaa8fcc0c000
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
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
    slice_correct (ms:=fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds5 certs5)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808360 * 2 ^ 32 + 4240490496) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_12887.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,3]⟩,⟨.and,[1,6]⟩,⟨.and,[4,7]⟩,⟨.and,[0,5]⟩,⟨.or,[1,4]⟩,⟨.and,[2,3]⟩,⟨.or,[8,11]⟩,⟨.and,[6,9]⟩,⟨.or,[9,12]⟩,⟨.or,[10,13]⟩,⟨.and,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808360 * 2 ^ 32 + 4240490496) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808360 * 2 ^ 32 + 4240490496) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_12887

open PEqualNP.Outside.L_meta_12887 in
theorem PEqualNP.Outside.L_meta_12887 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808360 * 2 ^ 32 + 4240490496) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808360 * 2 ^ 32 + 4240490496) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
