import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_16243.Model
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


end PEqualNP.Outside.L_meta_16243.Model

namespace PEqualNP.Outside.L_meta_16243
open PEqualNP.Outside.L_meta_16243.Model
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

def SBf (j : Nat) : Nat := [6, 4, 4, 6, 7, 7].getD j 0

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

def mirrorSteps : List Move := [swapRows 84]

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

end PEqualNP.Outside.L_meta_16243

namespace PEqualNP.Outside.L_meta_16243
open PEqualNP.Outside.L_meta_16243.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x7480c000580281a458068101451400ef42ec42ef32ec32ef21ed21be40bc40de30dc30ee20ec20f610f410
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x1800201407220c13825394f42972a6652c5448698a690da14121cc20061b040043a060087808010
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 9
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (i*5) 5
  | 4 => packedAt s0K4 (i*16) 16
  | 3 => packedAt s0K3 (i*27) 27
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (6+((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s0K4 (244+((h/4+packedAt s0K4 (224+(h % 4)*5) 5) % 20)*5) 5
  | 3 => packedAt s0K3 (255+((h/3+packedAt s0K3 (243+(h % 3)*4) 4) % 12)*5) 5
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xfffffff807ffffffffffff80fffffffffc3fff
  | 3 => 0xf07c1ffff801ff00ff807fff01fc03f807ce38
  | 4 => 0x7ffffffffe0000fffffffffe0003fffff03f
  | 5 => 0xff801fffffffffff00007ffffffffc0007ffc0
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x22088258292a490a2889158b162d545aa9d6db
  | 2 => 0x441104aea24c929451522ac0ab569aad342b6d
  | 3 => 0x8ea3a932b7691ca69a474fd58198d331a6ce38
  | 4 => 0xef4211c4c471d8d8e4647366cd0303c7c77036
  | 5 => 0x87bde070781e0e0f8787c78f1e3e20607bd80
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xccc0c0c0c0c00000ccc0c0c0c0c00000ccc0c0c0c0c00000ccc0c0c0c0c00000ccc0c0c0c0c00000ccc0c0c0c0c00000ccc0c0c0c0c00000ccc0c0c0c0c00000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_16243
namespace PEqualNP.Outside.L_meta_16243
open PEqualNP.Outside.L_meta_16243.Model
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
  | 2 => 0xfff00fffe01fffc07c0fff81ffe07ff0139e7c
  | 3 => 0xffff01fffe03ffffff01ffe07ff81fffce38f
  | 4 => 0xf000001fffffc0007fffe00007fffe001f03f0
  | 5 => 0xffffffe0000000007ffffffff80000001ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x1210a08422420490105162a288a8a215452cb5
  | 2 => 0xa4aa694a51d4a90aae0ab591556455a0d2965c
  | 3 => 0x88c94a529491b22a4ea81954465511ca98c30a
  | 4 => 0xce8d8d9d191923b3773cd061879e78831f03e0
  | 5 => 0xf0e0e1e1e1e3c3c7bcf1e79e418610c1ff800
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xaaa0aaa0aaa0aa00aaa0aaa0aaa0aa00aaa0aaa0aaa0aa00aaa0aaa0aaa0aa00aaa0aaa0aaa0aa00aaa0aaa0aaa0aa00aaa0aaa0aaa0aa00aaa0aaa0aaa0aa00, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_16243
namespace PEqualNP.Outside.L_meta_16243
open PEqualNP.Outside.L_meta_16243.Model
def s2K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s2K3 (i*5) 5
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s2K3 (6+((h/1+packedAt s2K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfc07ffffffffffffffff01fffffffffffc3fff
  | 1 => 0xfff803fe01ff00ff007ffe07e03f01fc07cccc
  | 3 => 0xffffffffffffffffffffffffffffffffffffff
  | 4 => 0xfffffc0001ffff00007ffff8003ffe0007f0f0
  | 5 => 0xfffffffffe000000007fffffffc0000007ff00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x97412493145192925215812caa6552a5541555
  | 1 => 0x2d4f61354cb28ea436af9705662b31e835cccc
  | 3 => 0x48124a2829242448a44a2a525492a552a2eaaa
  | 4 => 0x726473b1b1c8c88ec773cd9c183cf860c770f0
  | 5 => 0x838783c1c1f0f0f0f87cf1e79f20c18307bf00
  | _ => 0
def s2Atlas : Atlas := ⟨3,rawDecor 59 s2Pos s2Neg, 0xee00aa00aa00aa00ee00aa00aa00aa00ee00aa00aa00aa00ee00aa00aa00aa00ee00aa00aa00aa00ee00aa00aa00aa00ee00aa00aa00aa00ee00aa00aa00aa00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_16243
namespace PEqualNP.Outside.L_meta_16243
open PEqualNP.Outside.L_meta_16243.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x1201833004a580a041d20209bf43de43bd43dd439d43be42bc42de32dc32f721f421fb20f820
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x1114c3400003808002410023aa921c7149438ea98851f548ca3aa8196550f21caa18439943c833286107808420
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x8802846250c21a218943083814308420
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 13
  | 3 => 10
  | 2 => 3
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (i*5) 5
  | 4 => packedAt s3K4 (i*16) 16
  | 3 => packedAt s3K3 (i*27) 27
  | 2 => packedAt s3K2 (i*38) 38
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (6+((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s3K4 (224+((h/4+packedAt s3K4 (208+(h % 4)*4) 4) % 16)*5) 5
  | 3 => packedAt s3K3 (285+((h/3+packedAt s3K3 (270+(h % 3)*5) 5) % 24)*5) 5
  | 2 => packedAt s3K2 (116+((h/1+packedAt s3K2 (114+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x7fff00ffff00fffff80fffc0fff81ffe71e3f
  | 1 => 0xf80ffff00ffff00fffff01fff03ffe07f9e3c7
  | 2 => 0xffffffffffffffffffffffffffffffffffffff
  | 4 => 0xfff000000ffffff00ffffe00003ffff83e03f8
  | 5 => 0xfffffffff00000000fffffffffc000003ffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x42929a68a318e92923c0972c866590ce630e1b
  | 1 => 0x4e84a8aa652928ea45cb8155922ab246a962c5
  | 2 => 0x102841414842424488152a9a2893451114b56e
  | 4 => 0x64ce8d8d8e8c8c88eee6cd030c3c79e23e03b0
  | 5 => 0x870f0e0e0f0f0f0f0f78f1e3cf2061843fd800
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xe0e0e0e0e0e08080e0e0e0e0e0e08080e0e0e0e0e0e08080e0e0e0e0e0e08080e0e0e0e0e0e08080e0e0e0e0e0e08080e0e0e0e0e0e08080e0e0e0e0e0e08080, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_16243
namespace PEqualNP.Outside.L_meta_16243
open PEqualNP.Outside.L_meta_16243.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0xb000f3830000302048e2800023400c3002000202142caa13a0001a361d52d0078c93525c28d56052224e7c91100580004a994020000446461810c8283540ff43fe43fd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21f721fe21fd21fc21f421ff40fe40fd40fc40ff30fe30de30fd30fc30dc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x330000006d00374f04000000023928006100007014000000050071001d006a0000000000000007003a002f00000000000000690e0000590b00000000000000000032000a21003d255600001863003000004a002b68293100244c06354700440000480c00000100647200005d5b2e0000002a5e530074000000000000001e4e00001000000000080038000000000000001300004d55261b172300003c15000f00001a1f000000000000220019002c67400000005f4200125700455c0000166e5a1c0009003b1150414960660000000d004300270046000000033f00003e0058520000340000364b542d730065006f6c20516b620000000001800081808100830000000500008100820080810101020080000081000200818100008280db94a43b6a9487765190eeaa321dd94742baa8e853e5290aeea2a15d14542af298855d5310b3ca6216754c429f29085ae5210a7ca9994f55332bb28e657551ccb5885194fd51329e2a265ac424caeea2995d14532bda826578504cadea4a0db14941daa08833e54cc67aa998db94b31b6a9663b642c87688590cf952219eaa443ac42886eca310cfd51219e2a2435e53086baa610eb10821eb29843d553086eca410f994821f3a1043b642087688410f910821d221043e632087ca6410d794f40aea9e815f53502b8a6a05bd4940b6292817751502e8a2a05d94440baa88819e428c338851875c8630ea10c615e508c27ca8184f55030b7290616d520c2eca2185d54430cf2a0619d540c39ca4187354830cf210619c420c3aca2187554430eb90861d4210c2bca0187694030af29e415d53c83b061904f952209eaa441ac42882eca3105d54620f210c413f5448278a89057d4d20ae29a417751482e8a2906b10820f210841d830082bca7885754f109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x24a0e0a270058452a01a60001ebac02018032648840a0064c600e0c9108514cb284214132a9189411070d5310821a998a42086c56310821e198c42087856310821e194c42087855310821a919132086e0604c8219918951103844208630c3551520c21d6510830d1549510c2556508430e1108210c3244294620c99502188388420c020f0084300822c6255010
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x100190a0aeb3188410c857694c4208682ba88410861815944208430
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 117
  | 3 => 24
  | 2 => 4
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
  | 5 => packedAt s4K5 (826+((h/15+packedAt s4K5 (736+(h % 15)*6) 6) % 61)*7) 7
  | 4 => packedAt s4K4 (3471+((h/39+packedAt s4K4 (3159+(h % 39)*8) 8) % 247)*8) 8
  | 3 => packedAt s4K3 (952+((h/8+packedAt s4K3 (912+(h % 8)*5) 5) % 29)*6) 6
  | 2 => packedAt s4K2 (199+((h/1+packedAt s4K2 (196+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xff01ffffffffffe07ffffe03fffffffe3f1fff
  | 1 => 0x7ffe07f01fc07fff83e07ffc1f07e03fd9e267
  | 2 => 0x7fffffffe0007ffffc007ffffff8003fe1ff87
  | 3 => 0x800007ffffff81ffffff80001fffffc1fe03f8
  | 5 => 0xfffff800000001ffffffffffe0000001fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x14c11124488104014a49641230a29a20b0cab
  | 1 => 0x2a14b321c91aa4e5816c2ad50d4742b4d96265
  | 2 => 0x4c28644483a3492aac104d1a56d1051960b786
  | 3 => 0x68b1468912320db34a59019218e59611f40350
  | 5 => 0x70c1870e1c3c71dc739e71e380861821bfd800
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeae0eae0aa80aa80eae0eae0aa80aa80eae0eae0aa80aa80eae0eae0aa80aa80eae0eae0aa80aa80eae0eae0aa80aa80eae0eae0aa80aa80eae0eae0aa80aa80, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_16243
namespace PEqualNP.Outside.L_meta_16243
open PEqualNP.Outside.L_meta_16243.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x286c384309c680240001a520801900807244a8828b004119e0c5d32a0020e1526ace83000401f5a4560c12007a82c290810c5542006243190002004ff43fe43fd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21f721fe21fd21fc21f421ff40fe40fd40fc40ff30fe30de30fd30fc30dc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x372b206e0063170033004b23055d3b393a0b71694d006d0000740000000000006000002a521f36187000003f000000002919093c000000006b735c72000d000600005e0000321b26432500685a622208003d4c00004002545b031c4e5544004f301e6f420400000047582d006151650000242e3828466a006756592100164a0000003e0007574800003149131500115f5053001412450000000000002f000000001a00000100000041346c0e0f000a35001d660010272c0064000c0001000180810280010002020001810080878200800100010180010200000083040281000000005b94a43b6a9487765190eeaa321dd94742baa8e853e5290aeea2a15d14542af298855d5310b3ca6216754c429f29085ae5210a7ca9994f55332bb28e657551ccb5885194fd51329e2a265ac424caeea2995d14532bda826578504cadea4a0db14941daa08833e54cc67aa998db94b31b6a9663b642c87688590cf952219eaa443ac42886eca310cfd51219e2a2435e53086baa610eb10821eb29843d553086eca410f994821f3a1043b642087688410f910821d221043e632087ca6410d794f40aea9e815f53502b8a6a05bd4940b6292817751502e8a2a05d94440baa88819e428c338851875c8630ea10c615e508c27ca8184f55030b7290616d520c2eca2185d54430cf2a0619d540c39ca4187354830cf210619c420c3aca2187554430eb90861d4210c2bca0187694030af29e415d53c83b061904f952209eaa441ac42882eca3105d54620f210c413f5448278a89057d4d20ae29a417751482e8a2906b10820f210841d830082bca7885754f109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x918010b2800000078849488c39c58028299a1201ae00002a0002c2008000241c9108514cb284214132a9189411070d5310821a998a42086c56310821e198c42087856310821e194c42087855310821a919132086e0604c8219918951103844208630c3551520c21d6510830d1549510c2556508430e1108210c3244294620c99502188388420c020f0084300822c6255010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x8b0a0aeb3188410c857694c4208682ba88410861815944208430
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
  | 4 => packedAt s5K4 (3471+((h/39+packedAt s5K4 (3159+(h % 39)*8) 8) % 187)*8) 8
  | 3 => packedAt s5K3 (960+((h/8+packedAt s5K3 (912+(h % 8)*6) 6) % 34)*6) 6
  | 2 => packedAt s5K2 (199+((h/1+packedAt s5K2 (196+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xff01ffffffffffe07ffffe03fffffffe3f1fff
  | 1 => 0x7ffe07f01fc07fff83e07ffc1f07e03fd9e267
  | 2 => 0x7fffffffe0007ffffc007ffffff8003fe1ff87
  | 3 => 0x800007ffffff81ffffff80001fffffc1fe03f8
  | 4 => 0xfffff800000001ffffffffffe0000001fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x14c11124488104014a49641230a29a20b0cab
  | 1 => 0x2a14b321c91aa4e5816c2ad50d4742b4d96265
  | 2 => 0x4c28644483a3492aac104d1a56d1051960b786
  | 3 => 0x68b1468912320db34a59019218e59611f40350
  | 4 => 0x70c1870e1c3c71dc739e71e380861821bfd800
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xeae0aa80eae0aa80eae0aa80eae0aa80eae0aa80eae0aa80eae0aa80eae0aa80eae0aa80eae0aa80eae0aa80eae0aa80eae0aa80eae0aa80eae0aa80eae0aa80, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_16243
namespace PEqualNP.Outside.L_meta_16243
open PEqualNP.Outside.L_meta_16243.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x210058018c300c831c3b38d8401027a0007800020026b83f2a0c9242843a8a01b8000b800200000472c3260029400241d49a5544025806a6643c660222861513187cd8d2a00000000000000011830e06085010000102140008e0214000000403fe54007f55003fc5400ffd0c01fe43007f50c03fc4300ffd0801fe42007f50803fc42007fcc801fe32007f4c801fc3200ffd0401fe41007f50403fc41007fcc401fe31007f4c401fc31007fc8401fe21007f48401fc2100ffd0001fe40007f50003fc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x242006ff95210007faa90801bfc5484005ffb1c2002bfd8e10017fcc708012fe6384005feb1c2000bf58e10017f8c70800afc638400dffa1c2000ff90e10007fa870801bfc4384005ffb142002bfd8a10017fcc508002fe6284005feb142000bf58a10017f8c50800afc628400dffa142000ff90a10007fa850801bfc4284001ff9942000ff8ca10007fa6508003fc32840017eb0c2006ffd0610007fc8308003fd418400dfe20c2000ffcc610007fc6308003fd3184001fe18c2000ffc8610007fc4308003fd2184001fe10c2002bf98210017fe810800bfe4084005fea042002ff10210017fe610800bfe3084005fe9842002ff0c210017fe410800bfe2084005fe9042002ff08210017fe210800bf71084001fd8842000ffd9110005fec888003bf64440015fb222005ff9911000dfcc888003fd64440017eb222005ff1911000df8c888003bc64440035e3222005ff95110007faa888017fc5444001ffb1a2000bfd8d10007bec688002df6344001ff31a2004bf98d10007fac688002fd6344001fe31a2004bf18d10007b8c688002dc634400bffa1a2000ff90d10007fa8688017fc4344001ffb122000bfd8910007dec488002ef6244001ff3122000bf98910007fac488002fd6244001fe3122000bf18910007d8c488002ec624400bffa122000ff90910007fa8488017fc4244001ff9922000ff8c910007fa6488003fc324400bffa0a2000ff90510007ec8288003fd4144001faa0a2005ff10510007fe6288003fe3144001fb18a2000ff4c510007ea6288003fc3144001ff90a2000fdc8510007fc4288003fd2144001fe10a2000fd0851002ffe808800bfe4044001fea022002ff10110007fe608800bfe3044001fe9822002ff0c110007fe408800bfe2044001fe9022002ff08110007fe2088003fb1044005ff0822002fd84110017fec80800aff6404005ff3202001bf990100177cc808006be6404005feb202000bf590100177ac808002bd6404005fe3202002bf1901001ffca808003fd5404007fe2a02002ffd8c10015fec60800bfe63040097f3182002ff58c10005fac60800bfc63040057e3182003ffd0c10007fc8608003fd4304007fe2182002ffd8810015fec40800bfe62040017f3102002ff58810005fac40800bfc62040057e3102003ffd0810007fc8408003fd4204007fe2102000ffcc810007fc6408003fd3204001fe1902000bf9841001ffe8208003fe4104001fea082003ff10410007fe6208003fe3104001fe9882000ff0c410007fe4208003fe2104001fe9082000ff08410015fcc00800bff4004005ff2002002ff50010017f8800800bff3004005ff1802002ff4c010017f8600800bff2004005ff1002002ff48010017f8400800bff1004005fb8802002ff84010017f4200800bfd1004005fa8802000fe44010
  | 1 => 0xafe6088005ffa044002ff90220017fa811000bfc4088005ff9844002ff8c220017fa611000bfc3088005ff9044002fbc8220007f64110003ff64480017fb224009ff9912000dfcc890003fd64480017eb224009ff1912000df8c890027fe5448001feaa24009ff15120007fec690002ff6348001ff31a4004bf98d20007fac690002fd6348001fe31a4004bf18d2004ffe8690003fe4348001fea1a4009ff10d2004ffe8490003fe4248001fea124009ff10920007fe6490003fe3248001f71924000ff4c920007da6490003fc3248001ffb0a4000bfd8520007fcc290003fd6148001fe30a4000bf1852004ffe8290003fe4148001fea0a4009ff10520007fe6290003fe3148001fe98a4000ff0c520007fe4290003fe2148001fe90a4000ff0852004ffe809000bfe4048001fea024002ff10120007fe609000bfe3048001fe9824002ff0c120007fe4090003fb2048005ff1024002fb88120017fec81000aff6408005ff3204001bf99020017fac810002fd6408005fe3204002bf19020047fca810003fd5408011fe2a04002ffd8c20015fec61000bfe63080097f3184002ff58c20005fac61000bfc63080057e3184008ffd0c20007fc8610003fd4308011fe2184000bf98820047fe8410003fe4208001fea104008ff10820007fe6410003fe3208001fe9904000ff0c820017fec21000bfe61080017f3084002ff58420005fac21000bfc6108011ffa084000ff90420007fa8210023fc4108001ff9884000ff8c420007fa6210003fc3108001ff9084000ff88420007dc4210003fd2108001fe1084000fb08420015fcc01000bff4008005ff2004002ff50020017f8801000bff3008001fd9804002ff8c020017fa601000bfc3008005fc1804002ffc8020017de401000bfe2008005fd1004002ff48020017da4010003f92008001ffb262000bfd931003ffcc988006fe64c4001feb262000bf5931003ff8c988006fc64c400fff2a62000ff5531003ff8a988003ff63c40017fb1e2000ff98f10025fcc788003fd63c40017eb1e2000ff18f10025f8c78801fff43c4001ff21e2000ff50f1003ff88788003ff62c40017fb162000ff98b10005fcc588003fd62c40017eb162000ff18b10005f8c58801fff42c4001ff2162000ff50b1003ff88588003ff32c4001ff1962000ff4cb10007f8658801fff41c4001ff20e2000fd90710007fa8388003f541c400ffe20e2000ffcc710007fc6388003f631c4001fe98e2000fd4c710007f86388003ff21c4001fb90e2000ff88710007fa4388003fc21c4001fa10e2007ffd0310017fc8188003fd40c4005fe2062000ffcc310017fc6188003fd30c4005fe1862000ffc8310017fc4188003fd20c4005fe1062002ffd9210015fec90800bfe64840037f3242002ff59210005fac90800bfc64840057e3
  | 2 => 0x30007fa8298037fc414c009ff98a6000ff8c530007fa6298013fc314c001ff90a6000ff88530007fa4298003fc214c01bffa026002ff90130007fa809800bfc404c009ff9826004fecc130017fc609800bde304c005ffb206002bfd9030017fcc818006fe640c005df3206001af99030017fac818002fd640c005deb206000af59030017f8c81800afc640c019ff2a06000ff55030067f8a818012fe630c009ffa18600cf7d0c30027fc8618013fd430c009fe2186004f710c30017fec41800bfe620c0017f3106002fb98830005dcc41800bfd620c0017eb106002fb58830005dac41800bfc620c019ffa106000ff90830007fa8418033fc420c009ff9906004f7cc830027fc6418013fd320c001ee9906004ff0c830017fec21800bfe610c0017f3086002fd98430005ecc21800bfd610c0017eb086002fd58430005eac21800bfc610c019ffa086000ff90430007fa8218033fc410c009ff9886004ff8c430007bc6218013fd310c009fe1886004f70c430007fe4218003fe210c001fe9086000ff08430015fcc01800bff400c005ff2006002ff50030017f8801800bff300c005ef9806002ff8c030017f4601800bfd300c005ee9806004fe4c030007fec990002ff64c8017ff3264001bf99320007fac990002fd64c8017fe3264001bf1932005ffca990003fd54c8017fe2a64000ffd8f20005fec790003fe63c80097f31e4000f798f20005bcc790003fd63c80017eb1e4000f758f20005bac790003fc63c80097e31e400bffd0f20007fc8790003fd43c8017fe21e400bffd0b20007fc8590003fd42c8017fe2164000ffccb20007fc6590003ee32c8001fe9964000fb4cb20007f86590003ff61c8001ff30e4000bf98720007fac390002fd61c8001fe30e400bffd0720007fc8390003fd41c8017fe20e4000ffcc720007fc6390003fd31c8001fe18e4000ffc8720007fc4390003fd21c8001fe10e400bffd0320017fc8190003fd40c8005fe2064000ffcc320007f6619000bfe30c8001fe9864002ff0c320007f0619000bff64880057fb244002ff9922000dfcc91000bbe64880035f3244002ff59220005fac91000bbd64880015eb244002ff19220015f8c91002bfe5488001feaa4400aff15220017fec71000aff6388005ff31c4004bf98e20017fac710002fd6388005fe31c4002bf18e20057fe8710003fe4388001fea1c400aff10e20005fac51002bff4288001ff2144000ff50a20057f88510003ff3288001ff1944000ff4ca20007f8651000bff6188005ff30c4000bf98620017ecc310002f66188005feb0c4000bf58620017eac310002f56188005fe30c400affd0620007fc8310003fd4188015fe20c4000ffcc620007fc6310003fd3188001fe18c4000ffc8620007fc4310003ee2188001fe90c4000ff08620007d8431000
  | 3 => 0xf31a8000ff58d40007f8c6a0012fc6350001ee31a8000b718d40087fea6a0003fe5350001fea9a8010ff14d4000ffe86a0007bf4350003ff21a8001ff50d400077a86a0007fc4350001ffb128000bfd8940007fcc4a0003fd6250001fe3128000bf18940087fea4a0003fe5250001fea928010ff1494000ffe84a0007fe4250001df2128001ff5094000ff884a0007bc4250001ff9928000ff8c940007fa64a0003fc3250001ffb0a8000bfd8540007fcc2a0003fd6150001fe30a8000bf18540087fea2a0003fe5150001fea8a8010ff1454000ffe82a0007bf4150003ff20a8001ff505400077a82a0007fc4150001ff98a8000ff8c540007fa62a0003fc3150001ff90a8000ff88540007fa42a0003fc21500037fb028010ffd4140017fca0a0003fd5050005fe2828001ffd014000ff680a000bfe4050005df2028002ff101400177880a0007f84050009ffb266004bfd9330027fcc998006fe64cc009feb266000bf59330027f8c998012fc64cc01fff2a66000ff5533007ff8a998013ff43cc009ff21e6004ff50f30027f88798013ff62cc009ff3166000bf98b30027fac598002fd62cc009fe316600fffd0b30007fc8598003fd42cc01ffe2166004ffccb30027fc6598013fd32cc009fe1966004ffd8730027fcc398002fe61cc009feb0e6000bf58730027f8c39803fff41cc001ff20e6000ff5073007ff88398013ff31cc009ff18e6004ff4c730027f86398003ff21cc001ff10e6000ff48730007f8439803fff40cc005ff2066000ff50330017f8819800bff648c0057fb246002ff9923000dfcc91800bfd648c0017eb246002ff19230015f8c91803bfe548c001feaa4600eff15230005fac71803bff438c01defa1c6004ff90e30007fa8718013fc438c01dee21c6002ffd8a30017fcc518002fe628c005feb146000bf58a30017f8c51803bff428c001ff2146000ff50a30077f88518013ff328c001ef9946000ff8ca30007fa6518003dd328c009fe1946002ffd8630017fcc318002fe618c005feb0c6000bf58630017f8c31803bff418c001ff20c6000ff50630077f88318013ff318c001ff18c6000f78c630007fa6318013fc318c001ee18c6000ffc8630007fc4318003fd218c001fe10c6002bf98230017fe811800bfe408c005fea046002ff10230017fe611800bdf308c009fd9846000ffd9130005fec898037fe644c0037f3226000ff59130005fac898037fc644c0037e322600dff95130007faa898037fc544c01bffa1a6004ff90d30007fa8698013fc434c001ffb126000bfd8930007fcc498003fd624c001fe3126000bf1893006ffe8498003fe424c001fea12600dff10930027fe6498003fe324c001fe9926004ff0c930007fec298002ff614c001ff30a6000ff58530007f8c298002fc614c01bffa0a6000ff905
  | 4 => 0x803fc608842bffa044215ff10221007fec890802ff6448401dfb224200afd91210a7fcc890806fe6448401feb224200bf591210a7f8c890806fc6448401de3224201af191210a7fca890803fd5448429fe2a24200ffd8d21005fec690803fe63484097f31a4200ff58d21005fac690803fc63484097e31a4214ffd0d21007fc8690803fd4348429fe21a4214ffd0921007fc8490803fd4248429fe2124200ffcc921007fc6490803fd3248401fe1924214ffd0521007fc8290803fd4148429fe20a4200ffcc521007fc6290803fd3148401fe18a4200ffc8521007ee4290803fe2148401f710a4200ffd8121005fec090803fe6048401feb024200ff18121015f8c090853ff4048429fe2024200ffd9021005fec81084ffe64084037f3204200ff59021005fac81084ffc64084037e3204213ff95021007faa81084ffc5408401ffb184200bfd8c21007fcc610812fe6308401ef3184200b798c21007fac610802fd6308401eeb184200b758c21007f8c610812fc6308427ffa184200ff90c21007fa861084ffc43084017f3104213ffd0821007fc8410803fd4208427fe2104200ffcc821007fc6410803ee3208401fe9904200fb4c821007f86410802fe6108427ffa084213fdd0421007fc8210803fd4108427fe2084213fd10421007fe6210803f73108401ff1884200ff4c421007f86210803f43108401ff9084200fbc8421007fc4210803f62108401fe9084200fb48421007ea4210803ff6008401ff3004202bf98021007fac010802fd6008401fe3004213ffd002109ff8801080bff65900057fb2c8002ff9964008dfccb2000bfd65900017eb2c8002ff19640015f8cb20006fd6490003ffaa48001ff9524000ffaa920007fc5490005ffb1c8002ff98e40025fcc72000bfd63900017eb1c8002ff18e40097fea720003fe5390001fea9c8012ff14e4000ffe8720007fe4390003fea1c8001ff10e40017fec52000bfe62900017f3148002ff58a40005fac52000bfc6290025ffa948000ff94a40007faa52004bfc5290003ffa148001ff90a4000ffa8520007fc4290001ff9948000ff8ca40007fa6520003fc3290005ffb0c8002ff98640005fcc32000bfd61900017eb0c8002ff18640097fea320003fe5190001fea8c8012ff1464000ffe8320007fe4190001df20c8001ff5064000ff88320007bc4190001ff98c8000ff8c640007fa6320003fc3190001ff90c8000ff88640007fa4320003fc21900057f3048002ffd4240017fca12000bfc5090005ffa048002efd024000ff6812000bfc4090005fc2048000ffd9540005fecaa0043fe65500237f32a8000ff59540005facaa0043fc65500237e32a8002bfd914000ffea8a0007fe5450003df2a28001ff551400077aa8a0007fc5450001ffb1a8000bfd8d40007bec6a0002df6350001f
  | 5 => 0xa31007fa8518867fc428c409ff9946200ff8ca31007fa6518813fc328c4097f30c6219ffd0631007fc8318803fd418c433fe20c6204ffcc631007be6318813f7318c401ffb046200ff98231015fcc118803fd608c4017eb046200ff182310cffe8118867fc408c401ffb226200bfd91310c7fcc898806fe644c401feb226200bf591310c7f8c898806fc644c431ff2a26200ff551310c7f8a898863ff434c409ff21a6200ff50d31027f88698803ff624c4017fb126200ff98931007fac498803fc624c4017e3126218ffd0931007fc8498803fd424c431fe2126204ffcc931007be6498803fe324c401fe9926200f74c931027f86498863ff414c401ff20a6200ff505310c7f88298813ff314c409fb98a6200ff8c531007bc6298803ff604c4017fb026200ff98131007fac098803fc604c4057e3026218ffd01310c7f88098813ff640c4097fb206204ff9903100dfcc818813fd640c4017eb206204ff19031025f8c81885ffe540c401feaa06217ff15031025fcc618813ff430c409ff2186204ff50c31027f88618813ff620c409ff3106200bf98831027fac418802fd620c409fe3106217ffd0831007fc8418803fd420c42ffe2106204ffcc831027fc6418813fd320c409fe1906200bf984310bffe8218803fe410c401fea086217ff10431027fe6218813df310c409ff1886204fd8c431027fa6218803dd310c409fa9886204ffd8031027fcc01880afe600c409feb006200bf58031027f8c01885fff400c42ffe2006200ffd9321005fec99085bfe64c84037f3264200ff59321005fac99085bfc64c84037e3264216ff95321007faa99085bfc54c8401ffb1e4200bfd8f21007fcc790812fe63c8401feb1e4200bf58f21007f8c790812fc63c842dffa1e4200ff90f21007fa879085bfc43c842dffa164200ff90b21007fa859085bfc42c8401ff9964200ff8cb21007fa6590803fc32c842dffa0e4216fdd0721007fc8390803fd41c842dfe20e4216fd10721007fe6390803f731c8401ff18e4200ff4c721007f86390803f431c8401ffb064200ff98321015fcc190803fd60c84017eb064200ff183210b7fe819085bfc40c8401ffb244200bfd92210affcc910806fe6488401feb244200bf592210aff8c910806fc648842bff2a44200ff552210aff8a910803ff63884017fb1c4200ff98e21025fcc710803fd63884017eb1c4200ff18e21025f8c710857ff4388401ff21c4200ff50e210aff88710802fd628842bffa144200ff90a21007fa8510857fc4288401ff9944200ff8ca21007dc6510803fd3288401f69944200ff0ca21005fcc310857ff4188401ff20c4200ff506210aff88310803ff3188401ff18c4200ff4c621007f86310803ff2188401f790c4200fdc8621007fec110803fe60884057f3044200ff58221005fac110
  | 6 => 0x9ff3006402bf98032027fac019002fd600c809fe300641dffd00320eff88019003ff65904017fb2c821cff9964108dfccb20803fd65904017eb2c821cff1964108df8cb20806fd6490403ffaa48201ff9524100f7ca920807fd5490401deaa48201ff15241007fec720803fe63904097f31c8200ff58e41005fac720803fc6390439ffa9c8200ff94e41007faa720873fc5390403ffa1c8201efd0e4100ffc8720807fd4390401dea1c8201ff10e41007fec520803fe62904017f3148200ff58a41005fac520803fc6290439ffa948200ff94a41007faa520873fc5290403ffa148201ff90a410077c8520807fd4290403fe2148201ef10a41007fe6520803fe3290401fe9948200ff0ca4100dfcc320873ff5190401ff28c821cff1464100ffe8320807bf4190403fba0c8201ff1064100fe88320803ff6090401ff3048202bf98241007fac120802fd6090401fe304821cffd42410e7f8a120807ff4090403fe2048201ef10241007fecaa0802ff6550437ff32a8211bf99541007facaa0802fd6550437fe32a8211bf1954100dfec8a0807ff5450403ff2a28201ff5514100ff8a8a0803ff63504017fb1a8200ff98d41007fac6a0803fc63504097e31a821bffd4d41007fca6a0803fd5350437fe29a8201ffd0d4100ffc86a0807fd4350403fe21a8200ffd8941005fec4a0803fe6250401feb128200ff18941005f8c4a086fff5250401ff2928200ff549410dff8a4a0807ff4250403ff2128201ff5094100ff884a0803ff3250401ff1928200ff4c941007f864a0806ff6150437ffa8a8200ff94541007faa2a086ffc5150403ffa0a8201fdd054100ffc82a0803be4150403fe20a8201ef1054100fe882a0807b44150401ffb028200bfd8141007fcc0a0803fd6050401fe3028202bf181410dffea0a086ffc5050403ffa028201efd014100ff880a0813ff64cc4097fb266204ff9933100dfcc998813be64cc4035f3266204ff59331005fac998813bd64cc4015eb266204ff19331025f8c99886bfe54cc401feaa6621aff15331027fe8798813fe43cc409fea1e6204ff10f31027fec598813fe62cc4017f3166204fb98b31005dcc598813fd62cc4017eb166204fb58b31005dac598813fc62cc435ffa166200ff90b31007fa859886bfc42cc409ff9966204f7ccb31027fc6598813fd32cc401ee9966204ff0cb310d7fe8398803fe41cc401fea0e621aff10731027fec198813fe60cc4057f3066204ff58331005fac198813fc60cc435ffa06621aff10331007fec918802ff648c433ff3246201bf99231007fac918802fd648c433fe3246201bf192310cffca918803fd548c433fe2a46200bf58e310cffe8718813fe438c401fea1c6204ff10e31007fec518803fe628c4017f3146200ff58a31005fac518803fc628c433ffa146200ff9
  | 7 => 0xa1007be5450803feaa28400ef5514200ff8a8a1003ff63508017fb1a8400ff98d42007fac6a1003fc63508097e31a8421ffd4d42007fca6a1003fd5350843fe29a8401ffd0d4200ffc86a1007fd4350803fe21a8401bfd894210ffea4a1003fe5250801fea928421ff1494200ffe84a1007ef4250803ff2128400ef9094200ff884a1007bc4250803f62128400ffd8542005fec2a1003f761508017bb0a8400ff98542007fac2a1003fc61508017e30a8400fd18542005e8c2a1087ff5150843fe28a8401ffd054200ff882a1003ff60508017fb028400ff98142007fac0a1003fc60508057e3028421ffd414210ff8a0a1007ff4050803fe2028404ffd9332025fec999013fe64cc8037f3266404ff59332005fac999013fc64cc8097e3266420ff95332007faa999083fc54cc809ffa1e6404ff90f32027bc8799013fd43cc801eea1e6404ff10f32107fe8599003fe42cc801fea166420ff10b32027fec399013fe61cc8017f30e6404ff58732005fac399013fc61cc841ffa0e6420ff10732027fec199013fe60cc8057f3066404ff58332005fac199013fc60cc841ffa066420ff10332007fec919002ff648c83fff3246401bf99232007fac919002fd648c83ffe3246401bf192320fffca919003fd548c83ffe2a46400bf58e320fffe8719013fe438c801fea1c6404ff10e32025fcc51907fff428c801ff2146400ff50a320fff88519013ff328c801ef9946404fbcca32007fec319003fe618c8017f30c6400ff58632005fac319003fc618c83fffa0c641fff10632007fec119003fe608c8057f3046400ff58232005fac119003fc608c83fffa04641fff10232007fec899002ff644c801dfb226400afd91320f7fcc899006fe644c801feb226400bf591320f7f8c899006fc644c801de3226401af191320f7fca899003fd544c83dfe2a2641effd0d32027fc8699003de434c801fea1a6400f750d32027f8869907bff424c801ff2126400ff509320f7f88499013ff324c809f79926400ff8c932007bc6499003ff614c8017fb0a6400fdd8532005eec299003fe614c801feb0a6400ff18532005f8c299003f4614c8017a30a641effd05320f7f88299003ff604c8017fb026400fed8132005f6c099003fe604c801feb026400ff18132015f8c099003f8604c8017c302641effd01320f7f88099013ff640c8097fb206404ff9903200dfcc819013fd640c8017eb206404ff19032025f8c819077fe540c801feaa0641dff15032025fcc619013ff430c809ff2186404ff50c32027f88619002fe620c83bffa106400ff90832007fa8419077fc420c809ff9906404f7cc832027fc6419013ee320c809fe9906400f74c832027da6419013ff610c809ff3086400bf98432027fac219002fd610c809fe308641dffd04320eff88219013ff600c80
  | 8 => 0xf58d54007f8c6aa012fc6355003ffa1aa801ff10d5400f7886aa003ff62550017fb12a800ff98954007fac4aa003fc62550017e312a801ffd095400f7e84aa007fc4255001ffb0aa800bfd8554007fcc2aa003fd6155001fe30aa800bf1855400ffe82aa007fc4155003de20aa800ffd8154005fec0aa003fe6055001feb02a800ff18154015f8c0aa007ff4055003dfa02a801ff10154027fecb21812ff6590c09ff32c8611bf99643027facb21802fd6590c09fe32c8604bf1964300dfac921807ff5490c03ff2a48601ef9524300ffaa921803bd5490c03fe2a48604bf98e43027fea721813fe5390c09fe29c8604ffd0e430277e8721807df4390c09fe21c8604f710e43027fec521813fe6290c017f3148604ff58a43005fac521813fc6290c49ffa948624ff14a4300ffe8521807fc4290c03de2148604ffd8643027fcc321802fe6190c09feb0c8600bf58643027f8c321893ff5190c49fe28c8601ffd064300ff88321813ff6090c09ff3048602bf98243027fac121802fd6090c09fe3048624ffd4243127f8a121807ff4090c03fe2048600ffd9543005fecaa188ffe6550c237f32a8600ff59543005facaa188ffc6550c237e32a8604bfd914300ffea8a1807fe5450c03feaa28601ff1514300dfec6a188fff5350c09ff29a8600ff54d43027f8a6a1807ff4350c03efa1a8604ff90d430277c86a1813fc4350c09de21a8601f710d43007fec4a1802ff6250c01ff3128600ff58943007f8c4a1802fc6250c47ffa928623ff1494300ffe84a1807fc4250c01ffb0a8600bfd8543007fcc2a1803fd6150c01fe30a8600bf1854311ffea2a188ffc5150c03ffa0a8601ff1054300f7882a1803ff6050c017fb028600ff98143007fac0a1803fc6050c057e3028623ffd414311ff8a0a1807ff4050c03dfa028601ff10143007fecb21002ff6590845ff32c8411bf99642007facb21002fd6590845fe32c8411bf1964200dfac921007ff5490845dfaa48401ff9524200ffaa921007fc5490803de2a48400ffd8e42007fcc721012fe6390801feb1c8400bf58e42007f8c72108bff5390801ff29c8400ff54e42117f8a721007ff4390803ff21c8400ef90e4200ffa8721007fc4390803de21c8401bf98a42117fea521003fe5290845fe2948401ffd0a4200f7e8521007ef4290803fe2148401fb10a42007fec321003fe61908017f30c8400ff58642005fac321003fc6190845ffa8c8422ff1464200ffe8321007fc4190803de20c8400ffd8242007fcc12100afe6090801feb048400bf58242007f8c12108bff5090845fe2848401ffd024200f7e8121007fc4090801ffb2a8400bfd9542006fecaa10027f6550843ff32a8411bf99542007facaa1002fd6550843fe32a8411bf19542006f8caa10467c65508037fb228401ffd514200ffca8
  | 9 => 0x1c40000040880340d400802800805c06800400806800401400000800400002003000800000403001000800000001000800000406c00001c00406c01000009800c05000c00c00001005804c03c0180100040100240100480300240b000c0e400802c00400000c07c07000c00404000006800400c00801c0240000000000080a802007401402c07005401c01c00c00000000c07c09001403000008400000c00001001c07802800800c01c00400c00004401c00400008400001402406c00407405802001400c0180900080200000000240040a800002c00000000400004800000c00003402801002405401000002801c03001401401400400000400002400002800400003800805403c00400000000001000800000400001000000401c01000402400001400800000404400801c03400003800802403001009c00c0000b800002002400c00400c02800400000001c00012003800001001006404400003000800002800001000800406405411c00001000003000400801402800001000002c0000000140300300140480f400403004806800c00001003806803c01003c0040000640000a400401400400800803802802400403801800401400000800001005c04800000000006403800c00c00c02801001000001c0000340000000c40380900640000bc0080000080000040ac02800000401806c05402000000400c00c00006001402c01c10400800c0000200380080080080300240080680182640a400802804c00407800c01002c00800000001800000001000004001002800001403815c03800000400403405804c0140100940d00140d800804800800400001003c00c00402804405003413800400400c00404c00001c01402000000003800c00001401003401c0b001400003401000000000000001400016c0b000000400407c00000000400003c03c02801403800008400805001400401806c02804803000000000000c01003800800404c0140000000a000800000001804000400c00000000001400400004800402400c01000001007404401400006c03c00403802814c00c01002c01000408400000005000002401401c00800400400003800001807803404419001800414800803c0000a40000400000340380980701a801008800800002400004400804002400007801001801002000c00401c02c00003801401c00402c02800401001400c00002802001000c03005c00000c01400000400000013802802805c00c04400000800800001000000800c01c00000c0080000e400000000800008000402000400000800002003000003400001c00000400400800c0000200000400140080680000200600340b00180200180140300f4010037fb22a801ff9515400efca8aa007fc5455003de2a2a801cf15154007fec6aa002ff6355001ff31aa800f
  | 10 => 0x9318136faa71638316c001bf000000330e0bbba9c013d84e9a820100035840002c12f962042d3380018b0000fd800000217208df38000000e9abc4000003132ce8000001688a6bab2a3dc800000000000000000000012144195398993b3a330d10d65cc002cf0cb40000000024d08f03d390000080dadb335233c825b72a00035117f527c00230c002d70000000cbdd084bab7018812d966d2348850be8085a98681a1955a800074a899b1077b5a25d9500a52a37073162e5b9f90ebbb8ddaeab2100036b276024e98d6d8001844621ca01fdcb51d90cf0521c8000000000000578eb3548698000001a903655f0000000001f20eec76318917e65c000a380a2e300015eaaebb633c0cc4e1180b6bb3ee1aa871277de195e18e4e84f0688962c63b71d0251c2a02d1008531bc807fceab30c691400000028408633f40000024817065a86611952e90917c8e8a21c430226d4aefad98002b0a4049c45a3ac02b983ed68fb1518f98fec00008c003338a21e203d9e31bab83ad181b1f08d22e718e314aaa3e696fd87957d4284525a6ef0aa84c0e73360af9aab358f7d49a73c84d6a114bc380000000017520cf1ba365b6b12d4129e854a9c6ba0f8ef400ffb330799f9c3885778a5380000036436506fce40000ffc000dd0c600032872f4a9000236c56a55a8cd7947c37800036eafeb18c000510d664c70f000312a42373a2680009d400240d40400063a4c90643a4002b7c000000001629c9f648a3c003038f6b405561a61f7b55a02a64aac93811b7428c020b5f534e80003ac001947a79604003252b4d2d031bb2c43a7b329b5461665bee1ab9f27e8280028800014c8000002628002e4a09e2500000000031347280002627680005c00006dbd019f4001f634c0a0286cd5c0027bb2dda3ae5002402c00800401400002803000000000000004401000c00000c01401800802400408000400402400007800800400004000002000002800c00000400001802c0040040d806000007801003c04400000000407800c02c00000401c00401001800000001401003009c00404001c01c09400400001c00000801c03800400c0b400401c01402c07800001006400c0540600cc08c03400000803c00000c04c00000401800c05000402400400801c00c01800400002c05000002c00000c00001c01402800002000800000007c09401801402000c00000000000402401400000402c00000408406800402c02000008803c0000880140ec00002c08800402c02c00001407400807003006c02400400004c10c05000400401803003c17007c03400000802803801000401c00000009c00800400c01000c02409408000402401800403c00000000003c03000401400006400000401400001400800000000001c0080000e002c00c020004000000004000008054028010
  | 11 => 0x2000bd91520f0000002311e89cccb49af40000382131508c1e5dd584400012f03b8e3241f28e980c40003da8002c30003b9bad11ebe31ed0000b8a8dba80000000cdb0bb822a9fd9d9c89824b333f599dd35b382818d890715363b3a00d3d50edeb800346036a27570f68ae3a724000dbf468c881ea3f2588002068f28000bf8e1baaa9d99ef8e08c9d9b10b9237697164e131f3ea8909f18b7722b79ffa270002f09e140014b80033497d1168002b006939f3d60d7b5a648abb65f11bc0037f0000ea8000ec00036e356145e1af9db41ba63a38bab879a23bf220a631861299b024716a93e3c9a4f87f09d8bcabc1c933bbb197cebd79b2cedd92889ea1de2a2931538b2694a2561fea03a0b1bd9ac22889a08498f86e1f7e258dce392c4b3267298acb448d04499b2a71e69a023fa23de0e3639cb2940c10287813cf0ebe7aa8a8e152af3ada0f64a4020b51a43c7d3320e49b1823e58c270e36fc17552220c201a095769ab0e6110b15aa20349d4937a820c1992d7b97825c0f6177ae68739512a2e4b48b1c70dfa3aaf71be41d8160d283a384062ad591fdaa19517f9e73dba8c546c2da8ac0038631c15cc001e78002129a0d9c07b197aa2659a920f1a9f2338cd7d881b99422d359063032b1269b17df379159c28988c20a8920c292cbac127d94bdef32fc25d290215c632c8428e2dc7ad39430ca04629d5384d805f0cd321be5aad93fcf809a8751a4b2f030bd55fdf74a4ad5e37c877329dc217ec1d1b394837336fa928f6f595d1be6128fcd34326f87f400372aab96c37c19e0052970000aac0023b1650239db22a9b74003d18002d63416bd9a429d0003b4b778002a4e6518540000000035f8000cdcbc0cfb0b1b28001fe51a75369ab6782a94b6e980ab2e57af770000002a8e801b6ed3000034fb433838c36da866da460b3d800211bc282c88ac4c9b8a9df080ac96b3d68aa501022a8d067cccad82dc80015b40019880000012434100007e39609025e00029a15c05b2671c13d80920002f222f0000b763e37029c8b3eb8f5abc622b2dc3ba299000046afd80009140000009e8000cf1ba00000039480007ea38c003343a19f824515dc06936800341ec81c8bc12d5c9376d3d95bb2bc80000f2224a58b5092883a6c833849aa862fbad80009bf4cb390c357a9ce1120d1bcfaaa8f529988aa352798fd1059278002062695ff740a6db3104252b89ce07238b8a290a1eb3ca033818bd39e0f3a7d293d7c60a4ba3a420a86b08b491d633398f925832b74983433a1842d566d1128ed15bc5e301039215976eefe221cc093d9bfdc84d120526076a397c0811284b938bbaba8a4e247be8c51938421eab69228268e548000b092b08e80015cb1032b28a8000d133150a9cd2f315a17e6eb4fb88a3a93041828b78001d61d7b4aab1be400025
  | 12 => 0xee072002baea75f63827a4083fb80870fb22e101c3e4ada8000ff0000d600000000026882f9d6c5662fc000000000000b1021c000d300022400011626e8001478000003b5b8829fbb68a45770da2bbe3ca44af697d74665ea8f346ce399daa6154acd18e8c784df2880d9cbd4196409903445766f79a870000b4ce492a15c5a1081f306bd29f87bb09c8fa44d674c003e1399865a4b800204bd3a5c99731a1f8904000000019ca712c80027d400000140c001170cb8000003dd80037580007128e8d589b3ce00005e53b9e51e036b759d3a00e138e6e3e8d4c143a1400010fc0000000017c000343a988d50ea01280032c0000f33b7a3d2c9a4a11922662116081698fd0486f400000369819800000169a541a28945918f8800000332e4d8c7273a1bf620000000000000b190c994f3500004b000272c8036180010fa6111ac0000026540006a9a97328000000002838ec69536c21480000011c8ab73f23f618ab9007b5d89091878d01a54002438aab2acb0b600004e5ed91055091c358a89e4ff0fa8a61ba3e9249b98191348d49081733971670abdcb26a9a99788ee2718fe835800094d442a3aa92fd00000010f00000039330d8ebc002d533fa46232b940ccf450c997667c0001fd9818d77170000c5b45a512f82c2b8125adec04a21c53330460c952d9fe968850f545d29ce4f567a22cc0b7e9aad7b5bc3239bdee60b0322236aecaa332fa2996f9aea3b856e3fc5296bab9800350952486a0080021b1760001ee2f591300000027a0de2c9c0f4002ab0002585a332d00021f358fa080000015705ba468f080191a3df31db574819fb3c72810db5f2b6f03a808a2a08db7da22905f2bf139775961da405a320d6f3d0001ae0000e45b30889602c68618acc0032ec00269f40cb2ae0b48d5a71f8002436f8a9e0fc00727f215c968ffaadf8497b374f79b2780993ec0037b88726a4001471bfb7f9758000600000c3b2b8002764dc437307e3c3790832f50fe260a59c0000037b2cb4e835e092457ef999d224dc9b1c9d3234922b0c14540000016eac229405d7580003d4ed7a7453a5caedda7c4faab4089078bdd72c59a88e3e203b2ad4001c49f108a4003198b6f6618010687ca2b80025300037180036fe3873020e80000024cf6025500000000022e2b7400000051800168fe84250a10002e8813da7ac920414640008bb2ab31800059b389acb65892d722ff8389f65f580014274c6fb02e20799bbc881454ce4156126ddd40c4841cfb51e10dc000af2f118d822c321cf00028a12827be1d3c4000344ea46004002703d440005cf2a50e7444003871a5826ac500027e18f1f6b6f55fadd2cc919db5000219d848000002bebcf0000003d8c00193c002eac0028b9e4000357c000001fcbd48000cb2748002d421a47248113f941ddbb31c002f0
  | 13 => 0x23566e71a8001f75a501080018100039186cb17a61ab490880021a000318490e9478b28ca790001461d9c9422611d04fe3eeb385aabd01aaac0410807b506f9d657910987912038bb6118cbb09990650396fe1a8a2872314493f4003b88001740001f18002088000003da0001e83cb8000ed4000ecfa2353fd7338c76fc183c1a1800000216abb04a57e1959718708000003a70002fd40015b0b70d4c000000e9000035c000194002a97ae00002e8001f6c9481200025057100011a877eb20002ee83eb1e800179b063c20959cc8001949880000fa02c40000000c800250f2da659ca53c3539e5926800139d0c1ef8ab39c0000fac0009d173a2326025b0022af98331d10f4f87b10c29e10e7abad5346ec6a1031f011820d88140016caea21d8002315920000505a4e181cdabb9af0f9453abce932f878f953c00190f45c1482d5272a1b9521b6c43291d73d5b1649734546f1df1310ae2131af8bcc000001398000c10000000000a080000028944fa75059000000183800000000352adfafbacc0ee43c8000000f40000003de436e8bf868259a058aabf8b924c3a4b7100fb3ab3b0caaff251709aca8b4ea119094e0f732e1932ae5e1aa6b4bb47774395e97b0c906137347daefa98c91c516f2f7ced93ad1fb70847257000000302aeb899a5d000175c000000001576aef242699659c40002d12f78bdfd127c99160bcc2daa67aa6609c1dea9625c57d8f213921600000000005512aac792c19989f80009320820505d91b2b1156b0ffabb6715900004bdfa33e02071119028de5f8a787fafa0001303c52620000001b6397b5f1a6b01b90f56dbd23000000031e00002184d8e0a9353d3270732df00005035c00026f0001eb3e50000003168bf334f2ac0030f7c4a1fb5eb11a7e8a28000001d10002731fe07747d9663c59284b324799e40000005fae28350003154000000002c722e800093ace54da0f800013ab85729690f5d79c000adc0025b887847920800184ee7934350c288c27e7300017b4e0002b47e2484285acaeb61490090103905c182cf898a32816359073d78aa3747579f990d8330f597e91f19f03f34d082800292df9061eba6254003573a899555d8001000000ada340000f1228c00004ba0303c1a04c627f5200007854f8002198003ca8398000001b23608003507cc8000b7c0030aa3073080000004cc4e08832022787fef9280fc920d00b8d8ad08000002a09100ae756596c5e8383c031833840000010b09bb85a290615b80671020a6288cf786e5da1ee8b58e580021c3259d54dea4006480002df492709c09fc071d872639be95ac7a1324000000ad0000001ffc062a1faf9e29423087d09f40001111da95b9e4a12000348400398aa0170a6ec3568b000132c00008058a9b98be6b3dc0fcbbca640b558c56184a81e07ee
  | 14 => 0x1d88ecb1b2788003d200038f2f6041659000000348354c000491408041fd4202a980865d7a13d98001050234ae800135275aea40017a18c1ad35d015a5035328754f0003d30b5c0000000031740d0b98efa438d71d5c000001fcdd505620a000068e64fb037534f800308903a52af1a1504028612e35c8000001648000002850ff420f4a3db07b8000003204000000001ff0130e01530be8679468002a5b52e2d8254480000000000b418891bbbe00000000000000000027f8000000000583d500001199de5686ba0861384ed9a13e50d317c000000000000e680001c8000002ebc0000000023700950bbe0b4b0d997bc001d68310d68ac158a647e3a5971f1b5948b05ac033041827cd680001a54c306ea1938c8db930b228232d02c58df1004e52ae2410d45ebefcc5dc0ede0a17b008d099e8bb1396441253aa1907191cb8b3a203bf8000003a2aa4b03396b9580319698a2fcb10505560c5420d6b825a0d41b08571d296680b22caa5000022293840aca2f287a954000000107b10f90a0918215d6c380021000029107422c1c94b226b8f4a8b5f8c5580e6ec1dd901848945b8898d3830e22157e28f77a51d3be0170155ab5b2eab896e3208ab8798912ed0010d3d218003803980d000024984f511b020c82eb0b6a4a6110ef641b8e8002db800030257ae2125a022cf942d93614c003b9161d04f15dcf8299d2225e959a9f515288f9ce280027560afc7800366a524d39c32ce2deb910000000caceb8000000000a80ef39a281ee0351ec877d1599e3862f1956840014aa4a82f0627ca00000018517a7c6b63297f2800034213f24f27100028270915840038d9b90001859a08001be311c000758002523990000668919416f4b14326000000080800000163ad280000000039d1b72cdb629dc8db3dde309ec94b0efddc2740ca4cc00033334424271a53582b1abb4489e26a1521e92a7967f6a8001a134dadb3e18003de800158000252c001a704aca9a4326c0000eea77a976ca6333af0361f72a0e9c2de0d373e5b48ad6902e83cc15e400224bcdec18706d93e7ca1ab6a398be2f040016d245abf3890822518522879551c6a0c75535267213df5694536ca099b7a9fdf4a736b5558c1f92db36aa076a19d517a85dd838534f1e9aad0bc6669ceb24ba69321983d901733734028f8ceb04aa812133dc643761d0dbb8003e6c000e3c6755780020580006d28302471fc003dd09500011988458b837a8d52a1fd3e1c002b53cdabe1b43e897f242e35f43e2190a0dc347a4bd3eb7aa773cb1df8d901400014c74713aa3a1fb8bd5910daaa42b9424a31918ca4b7a2b5cf035bac8986ad887195d0c3f6803e3bd94e913a26dca92384b55c50e0003e2d74ae41ec7acbd41cc439c89800268083f344000003b28ce1f327830a237b9ebc30d540000000
  | 15 => 0x1e6118a2353c8000000003df8153502429fa8687121617bc37e2edb54174f92a692c0b19fb8089c4580000000022388f8b67bd3cd5d1637e3d800280992a9485cba5bb0cdc8280b800006c00028c2af0a370e20e28696979b94d00e861000267a91a1e271c000978000002e9132868000
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc7058810016ee2058810016ec2058810004ff7690810014fe7690810004fd7690810014fc76908101167e65908100067d659081000ebe6490810006bd6490810004ff7650810014fe7650810004fd7650810014fc76508100057f755081012d7c755081010e7e65508100067d655081000ebe6450810006bd6450810005f77150810005f47150810024ff76cc810014fe76cc810004fd76cc810014fc76cc810106be64cc810006bd64cc810026de63cc810006dd63cc810004ff768c810014fe768c810004fd768c810014fc768c8100febe648c810006bd648c810006ee628c810006ed628c810004ff764c810014fe764c810004fd764c810014fc764c810005bf744c81001dbc744c8100f6be644c810006bd644c810026de634c810006dd634c810006ee624c810006ed624c810005f7714c810005f4714c810005fb704c810015f8704c810024ff760c810014fe760c810004fd760c810014fc760c8100eebe640c810006bd640c81000cfe749841003cfd749841000cfc7498410024fe7398410004fd7398410004fe7298410004fd7298410014fe7198410014fd7098410016f61098410016fa1098410016f4109841003cff7690410014fe769041000cfd7690410014fc76904100e67e65904100067d659041000ebe6490410006bd649041003ef66190410015fa7090410005f9709041003cff76504100de7e65504100067d655041000ebe6450410006bd645041003ef6615041001fb44150410004fd76cc41001dbe74cc410005bd74cc4100d6be64cc410006bd64cc410005ee72cc410005ed72cc410004ff768c410024fd768c4100cebe648c410006bd648c410026de638c410006dd638c410006f6618c410015fa708c410005f9708c410004ff764c4100c6be644c410006bd644c410006f6614c410024ff760c410014fe760c410004fd760c410014fc760c4100bebe640c410006bd640c410026de630c410006dd630c410015fa700c410005f9700c410004fd76c84100b6be64c8410006bd64c8410006f661c8410004ff7688410004fd76884100aebe6488410006bd6488410006ee6288410006ed6288410015fa7088410005f97088410004ff7648410005bf744841001dbc74484100a6be6448410006bd6448410004ff7608410014fe7608410004fd7608410014fc760841009ebe6408410006bd6408410005de7308410005dd7308410006ee6208410006ed6208410006f66108410007e52108410015fa7008410005f97008410015fb7644010006fb7644010004fb7644010007bb7444010007b87444010017ba6444010017b96444010007db7344010007d87344010007eb7244010007e87244010015fb7144010017f37144010006fa6144010017f26144010007f25144010007f15144010007f33144010007f03144010
  | 1 => 0x8110005f671c8110005f571c8110004ff7648110004fd7648110004fc7648110006bf644811004ebc6448110006df6348110006dc6348110006ef6248110006ec6248110005f77148110005f47148110006bf64c411003ebc64c4110006df63c4110006dc63c4110006ef62c4110006ec62c4110015f671c4110016fa76c4110014fa76c4110007bb64c4110007b864c4110007db63c4110007d863c4110007eb62c4110007e862c4110015fa71c4110017f361c4110007f241c4110007f141c4110007f231c4110007f131c4110007f321c4110007f021c4110004ff755901008cfe755901008cfc7559010016bf7459010006bf545901001ebe545901001ebc5459010004ff7359010024fc735901001ebf435901001ebc4359010004ff7259010004fc725901001ebf425901001ebc425901000cff715901000cfd715901001cfc715901001ebc4159010014ff7059010014fe7059010014fd7059010014fc7059010016be4059010016bc4059010016f71059010016f51059010006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf5359010006bc5359010006bf7259010006be7259010006bd7259010006bc7259010006bf5259010006bc525901001ebf7159010006be7159010006bc7159010006bf5159010006bc5159010016bf7059010016be7059010016bd7059010016bc7059010016bf5059010016be5059010016bd5059010016bc5059010016bf3059010016be3059010016bd3059010016bc3059010016bf2059010016be2059010016bd2059010016bc2059010016bf1059010016b71059010016be1059010016bd1059010016b51059010016bc1059010004ff7655010014fe7655010004fd7655010014fc765501000ebe6455010006bd645501001f3c5455010005f77155010005f47155010004ff7458c1000cfe7458c1000cfc7458c10016df7358c10004ff7258c10004fc7258c10024ff7158c10024fd7158c10014ff7058c10014fe7058c10014fd7058c10014fc7058c10016de3058c10016dc3058c10016f71058c10016f51058c10024ff7690c10014fe7690c10004fd7690c10014fc7690c101267e6590c100067d6590c1000ebe6490c10006bd6490c10004ff7650c10014fe7650c10004fd7650c10014fc7650c1011e7e6550c100067d6550c1000ebe6450c10006bd6450c1000cfe7498810004fd749881000cfc7498810024fe7398810004fd7398810016ee7298810014fe7098810014fc7098810016ee2098810016ec2098810016f71098810016f51098810004ff745881000cfe745881000cfc7458810004ff7358810024fc7358810016ef72588100b4ff71588100a4fd7158810014ff7058810014fe7058810014fd7058810014f
  | 2 => 0x15f8704c510015f4764c510026f4764c510014f4764c510005f7744c510005f5744c510007b7644c510007b4644c510007d7734c510007d7634c510026f6634c510026f4634c510007d4634c510005f4724c510007e7624c510007e4624c510007d7324c510007d5324c510007f3704c510015f6704c510015f4704c510007f0704c510015f0704c510004fe760c510006bf640c5100bebc640c510006df630c510026dc630c510006ef620c510006ec620c510005f6710c510014fe76c8510006bf64c85100b6bc64c8510006df63c8510006dc63c8510006ef62c8510006ec62c8510015fa70c8510005f970c8510015f676c8510006f676c8510014f676c8510005f774c8510005f574c8510007b764c85100b6f664c85100b6f464c8510007b464c85100b6b464c8510005f773c8510005f573c8510007d763c8510146f663c8510146f463c8510007d463c8510006d463c8510006f762c8510007e762c8510006f562c8510007e462c8510015f670c8510007f270c8510007f170c8510015f470c8510004fe7688510006bf64885100aebc6488510006df6388510006dc6388510006ef6288510006ec6288510005f67188510014fc7648510005bf744851002dbc7448510006bf64485100a6bc6448510006df6348510006dc6348510006ef6248510006ec6248510005fb7048510015f87048510004fe7608510006bf640851009ebc6408510005de7308510005dd7308510006df6308510006dc6308510006ef6208510006ec6208510005f67608510006f67608510005f77408510005f57408510007b7640851009ef6640851009ef46408510007b4640851009eb46408510005f77308510007d67308510005f57308510007d57308510005d57308510007d7630851013ef6630851013ef46308510007d46308510006d46308510005f67208510007e67208510006f76208510007e76208510006e76208510006f56208510007e46208510007e63208510007e53208510015f67008510015f47008510137e62008510137e4200851000cff765011002cfd765011000cfc76501100067f65501100867c6550110006bf645011000ebc6450110005df7350110005dc7350110006df6350110006dc6350110006ef6250110006ec6250110005f77150110005f47150110007b54150110004fe76cc110006bf64cc11007ebc64cc110006df63cc110026dc63cc110006ef62cc110006ec62cc110005f671cc110005f571cc110017f010cc110024ff764c110004fd764c110024fc764c110006bf644c11006ebc644c110006df634c110026dc634c110006ef624c110006ec624c110005f7714c110005f4714c110004fe76c8110006bf64c811005ebc64c8110005de73c8110005dd73c8110006df63c8110006dc63c8110006ef62c8110006ec62c
  | 3 => 0xe76cc910004fd76cc910024fc76cc910006bf64cc910106bc64cc910006df63cc910026dc63cc910006ef62cc910006ec62cc910005f671cc910005f571cc910004ff768c910004fe768c910004fd768c910004fc768c910006bf648c9100febc648c910006df638c910026dc638c910006ef628c910006ec628c910004ff764c910004fe764c910004fd764c910004fc764c910005bf744c91002dbc744c910006bf644c9100f6bc644c910006df634c910026dc634c910006ef624c910006ec624c910005f7714c910005f4714c910005fb704c910015f8704c910024ff760c910004fe760c910004fd760c910024fc760c910006bf640c9100eebc640c910006df630c910026dc630c910006ef620c910006ec620c910005f6710c910005f5710c910034fe76905100067f65905100e67c6590510006bf649051000ebc6490510006df6390510006dc6390510006ef6290510006ec6290510005f67690510036f67690510005f77590510005f5759051000777659051000774659051002df57490510007b7649051000ef6649051000ef4649051002fb4649051000eb4649051002fb65490510007b55490510005f57390510007d76390510007d4639051002fb74390510007b54390510005f67290510007e76290510007e46290510007b6429051002fb44290510015f67090510015f47090510157b64090510157b44090510014fc76505100067f65505100de7c6550510006bf645051000ebc6450510006df6350510006dc6350510006ef6250510006ec625051002fb44150510005fb7050510015f87050510015f4765051000ef47650510014f47650510005f77550510005f5755051000777655051000774655051002df77450510007b77450510007b7645051000ef6645051000ef4645051002fb4645051000eb46450510005f77350510007d76350510007d46350510005f47250510007e76250510007e46250510007f37050510015f67050510015f47050510007f0705051002fb74050510014fe76cc510014fc76cc51002dbe74cc510005bd74cc510006bf64cc5100d6bc64cc510006df63cc510026dc63cc510005ee72cc510005ed72cc510006ef62cc510006ec62cc510015fa70cc510005f970cc510004fe768c510006bf648c5100cebc648c510006df638c510026dc638c510006ef628c510006ec628c510005f6768c510006f6768c510005f7748c510005f5748c510007b7648c510007b4648c510005f5738c510007d7638c510026f6638c510026f4638c510007d4638c510026d4638c510005f6728c510007e7628c510007e4628c510015f6708c510015f4708c51014fd6308c51014fd4308c510014fc764c510006bf644c5100c6bc644c510006df634c510026dc634c510006ef624c510006ec624c510005fb704c510
  | 4 => 0x8910166ef71d8910006ed71d8910006e571d8910006ef41d8910006ec41d8910006ef70d8910166ee70d8910006ed70d8910166ec70d8910006ef40d8910166ee40d8910166ec40d8910166ee30d8910166ec30d8910166ee10d8910166ec10d891002dbe7498910005bd7498910006bf6498910006bc6498910005de7398910005dd7398910006df6398910006dc6398910006ef629891000cfe7498910006be749891000cbe7498910004fd7498910006bd7498910004bd749891000cfc7498910024fe7398910006de7398910024de7398910004fd7398910006dd7398910004dd7398910004fe7298910004ee7298910004fd7198910006f57198910004fd7098910006f97098910005bf745891002dbc7458910006bf6458910006bc6458910005df7358910005dc7358910006df6358910006dc6358910004ff7458910006bf7458910004bf745891000cfe745891000cfc7458910006bc745891000cbc7458910004ff7358910006df7358910004df7358910024fc7358910006dc7358910024dc7358910006ef7258910004ff7158910006f77158910004ff7058910006fb7058910004fe7618910006bf6418910006bc6418910006df6318910006dc6318910006ed621891000cfe7418910004fd741891000cfc7418910024fe7318910004fd7318910006ee7218910006ef4218910006ec42189100acfe711891009cfc7118910014fe7018910014fc7018910005ee7618910006ee7618910004ee7618910006ef6418910007af6418910006af6418910006ee6418910006ed6418910006ec6418910007ac6418910006ac6418910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc6318910137e77118910137e61018910137e41018910006ef7418910006ee7418910006ed7418910006ec7418910006ee5418910006ed5418910006ec5418910006ef7318910006ee7318910006ed7318910006ec7318910006ef4318910006ee4318910006ed4318910006ec4318910136ef7118910006ed7118910006ef4118910006ec4118910006ef7018910136ee7018910006ed7018910136ec7018910006ef4018910136ee4018910136ec4018910136ee3018910136ec3018910136ee1018910006ed1018910136ec1018910004ff7690910004fe7690910004fd7690910004fc76909100067f65909101167c6590910006bf649091000ebc6490910006df6390910006dc6390910006ef6290910006ec6290910004ff7650910004fe7650910004fd7650910004fc76509100057f755091015d7c75509100067f655091010e7c6550910006bf645091000ebc6450910006df6350910006dc6350910006ef6250910006ec6250910005f77150910005f47150910024ff76cc910004f
  | 5 => 0x6dd54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df42d8d10006dc42d8d1014edf71d8d10006dd71d8d10006df41d8d10006dc41d8d10006df70d8d1014ede70d8d10006dd70d8d1014edc70d8d10006df40d8d1014ede40d8d1014edc40d8d1014ede20d8d1014edc20d8d1014ede10d8d1014edc10d8d1002dbe7498d10005bd7498d10006bf6498d10006bc6498d10006df6398d10005ee7298d10005ed7298d10005bf7458d1002dbc7458d10006bf6458d10006bc6458d10005ef7258d10005ec7258d10004ff7458d10006bf7458d10004bf7458d1000cfe7458d1000cfc7458d10006bc7458d1000cbc7458d10006df7358d10004ff7258d10006ef7258d10004ef7258d10004fc7258d10006ec7258d10004ec7258d10004ff7158d10006f77158d10004ff7058d10006fb7058d10004fe7618d10006bf6418d10006bc6418d10026de6318d10006dd6318d10005de7618d10006de7618d10004de7618d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d10007d57118d1016fd61018d1016fd41018d10026df7418d10026de7418d10026dd7418d10026dc7418d10006de5418d10006dd5418d10006dc5418d10026df7218d10026de7218d10026dd7218d10026dc7218d10006df4218d10006dc4218d10026df7118d10026dd7118d10026d57118d10006df4118d10006dc4118d10026df7018d10026de7018d10026dd7018d10026dc7018d10006df4018d1016ede4018d1016edc4018d1016ede2018d1016edc2018d1016ede1018d10006dd1018d1016edc1018d10024ff7690d10004fe7690d10004fd7690d10024fc7690d100067f6590d101267c6590d10006bf6490d1000ebc6490d10006df6390d10026dc6390d10005f67190d10005f57190d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100067f6550d1011e7c6550d10006bf6450d1000ebc6450d10006df6350d10026dc6350d10006bf64d8910006bc64d8910006df63d8910006dc63d891000cfe74d8910004fd74d891000cfc74d8910024fe73d8910004fd73d8910006ef42d8910006ec42d8910006f571d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d8910007e571d8910167e610d8910167e410d8910006ef74d8910006ee74d8910006ed74d8910006ec74d8910006ee54d8910006ed54d8910006ec54d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef43d8910006ee43d8910006ed43d8910006ec43d
  | 6 => 0xc6288610005bf7448610035bc7448610006ee6248610006ed6248610005fb7048610015f87048610005de7308610005dd7308610136ef6208610136ec6208610007e52108610015f976c4210006f976c4210017f271c4210007f251c4210007f151c421000cfe76d911002ebe64d911008cfe75d9110004fd75d911008cfc75d9110006bf54d911002ebe54d911002ebc54d9110024fe73d9110004fd73d911002ebf43d911002ebc43d9110004fe72d9110004fd72d911002ebf42d911002ebc42d911000cfe71d9110014fd71d911000cfc71d911002ebf41d9110014fe70d911002cfd70d9110014fc70d911002ebf40d911002dbe76d911000cbe76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bc65d9110157b771d9110157b610d9110157b410d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006bc52d9110156bf71d911002ebe71d9110006bd71d9110006bf51d9110006bc51d9110006bf70d9110156be70d9110006bd70d9110156bc70d9110006bf50d9110156be50d9110156bc50d9110156be30d9110156bc30d9110156be20d9110156bc20d9110156be10d9110156bc10d91100057f755911015d7c75591100067f655911002ebc6459110005df7359110005dc7359110005ef7259110005ec7259110004ff75591100067f75591100047f755911008cfe755911008cfc75591100067c755911008c7c755911002cff7459110006bf7459110004ff7359110006df7359110004df7359110024fc7359110006dc7359110024dc7359110004ff7259110006ef7259110004ef7259110004fc7259110006ec7259110004ec7259110034ff7159110006f7715911003cff7059110006fb7059110005be761911002ebe7619110004be7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c651911002fb57119110176bf6119110177b61019110177b41019110004ff7655110004fe7655110004fd7655110004fc7655110006bf645511000ebc645511002f3c5455110024fe76d8d10006bf64d8d10006bc64d8d1000cfe74d8d10004fd74d8d1000cfc74d8d10006df43d8d10006dc43d8d10004fe72d8d10004fd72d8d10024fe71d8d10024fc71d8d10014fe70d8d10014fc70d8d10024de76d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d1014fd771d8d1014fd610d8d1014fd410d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006de54d8d10
  | 7 => 0x310005f47150310007b54150310026de63cc310006dd63cc310005f671cc310005f571cc310024ff764c310026de634c310006dd634c310005f7714c310005f4714c310005de73c8310005dd73c8310006ee62c8310006ed62c8310005f671c8310005f571c8310006ee6248310006ed6248310005f77148310005f47148310004ff755921008cfe755921008cfc7559210016bf7459210036be5459210004ff7359210024fc7359210036bf4359210004ff7259210004fc7259210036bc4259210036bf4159210014fc7059210016be4059210016bc4059210016f71059210016f51059210004ff7655210014fe7655210004fd7655210014fc765521000ebe6455210006bd64552100373c5455210005f77155210005f47155210004ff7458e1000cfe7458e1000cfc7458e10016df7358e10004ff7258e10004fc7258e10014fc7058e10016de3058e10016dc3058e10016f71058e10016f51058e10024ff7690e10014fe7690e10004fd7690e10014fc7690e10004ff7650e10014fe7650e10004fd7650e10014fc7650e1000ebe6450e10006bd6450e1000cfe7498a10004fd7498a1000cfc7498a10024fe7398a10006de7398a10024de7398a10004fd7398a10006dd7398a10004dd7398a10016ee7298a10014fe7098a10016ee2098a10016ec2098a10016f71098a10016f51098a10004ff7458a1000cfe7458a1000cfc7458a10004ff7358a10024fc7358a10016ef7258a10014fc7058a10016ee2058a10016ec2058a10004ff7690a10014fe7690a10004fd7690a10014fc7690a1000ebe6490a10006bd6490a10004ff7650a10014fe7650a10004fd7650a10014fc7650a100057f7550a1018d7c7550a10005f77150a10005f47150a10024ff76cca10014fe76cca10004fd76cca10014fc76cca10186df63cca10026dc63cca10004ff768ca10014fe768ca10004fd768ca10014fc768ca10006ee628ca10006ed628ca10004ff764ca10014fe764ca10004fd764ca10014fc764ca10005bf744ca10035bc744ca1017edf634ca10026dc634ca10006ee624ca10006ed624ca10005f7714ca10005f4714ca10005fb704ca10015f8704ca10024ff760ca10014fe760ca10004fd760ca10014fc760ca10014ff7158610016f6105861002cfd7690610156bf649061000ebc649061000cff7650610014fc765061000ebe6450610006bd6450610037b44150610005fb7050610015f87050610035be74cc610005bd74cc610026de63cc610006dd63cc610005ee72cc610005ed72cc610015fa70cc610005f970cc61014edf638c610026dc638c610024ff764c610026de634c610006dd634c610005fb704c610015f8704c61016edf630c610026dc630c610006ee62c8610006ed62c8610015fa70c8610005f970c8610166ef6288610166e
  | 8 => 0x4ff764cb10004fe764cb10004fd764cb10004fc764cb10005bf744cb1003dbc744cb10026de634cb10006dd634cb10006ef624cb10006ec624cb10005f7714cb10005f4714cb10005fb704cb10015f8704cb10024ff760cb10004fe760cb10004fd760cb10024fc760cb10005f6710cb10005f5710cb10014fd769071000ebe6490710006bd6490710015fa7090710005f97090710015f5769071000ef57690710014f57690710005f77590710005f5759071000ef6649071003fb66490710007b5649071000ef4649071003fb65490710007b55490710005f5739071003fb74390710007b54390710005f67290710007b6429071003fb44290710015f67090710007f27090710007f17090710015f47090710157b64090710157b4409071001cff7650710006bf645071000ebc645071003fb44150710005f7765071001ef77650710005f77550710005f57550710007b77450710007b7645071000ef6645071000ef4645071003fb4645071000eb46450710005f77350710005f47250710015f67050710015f4705071003fb7405071003dbe74cc710005bd74cc710005ee72cc710005ed72cc710014fd768c710026de638c710006dd638c710015fa708c710005f9708c710015f5768c710026f5768c710014f5768c710005f7748c710005f5748c710026f6638c710007d6638c710007d5638c710026f4638c710005f6728c710015f6708c710007f2708c710007f1708c710015f4708c71014fd6308c71014fd4308c710005f7764c710006f7764c710005f7744c710005f5744c710007d7734c710026f6634c710026f4634c710005f4724c710007d7324c710007d5324c710015f6704c710015f4704c710014fd760c710026de630c710006dd630c710015fa700c710005f9700c710005f576c8710006f576c8710005f774c8710005f574c87100b6f664c87100b6f464c8710005f773c8710005f573c8710146f663c8710146f463c8710006f762c8710006f562c8710015f670c8710015f470c8710014fd7688710006ee6288710006ed6288710015fa7088710005f97088710005bf744871003dbc7448710014fd7608710005de7308710005dd7308710006ee6208710006ed6208710015fa7008710005f97008710015f57608710006f57608710014f57608710005f77408710005f5740871009ef6640871009ef46408710005f77308710007d67308710005f57308710007d57308710005d5730871013ef6630871013ef46308710007e67208710006f76208710007e66208710006f56208710007e56208710006e56208710007e63208710007e53208710015f67008710007f27008710007f17008710015f47008710137e62008710137e4200871000cff765031000ebe6450310006bd6450310005df7350310005dc7350310005f7715
  | 9 => 0x976cc020015fa73cc020017da73cc020016fb63cc02019ef963cc020005f972cc0201a6fa62cc020017ea62cc020007ea21cc020007e821cc020015fb7648020006fb7648020004fb764802019dfa734802019df87348020015fb7248020017eb7248020006fa6248020017ea6248020007ea5248020007e9524802003ebe64d9310005de73d9310005dd73d931008cfe75d9310004fd75d931008cfc75d931003ebe54d9310024fe73d9310006de73d9310024de73d9310004fd73d9310006dd73d9310004dd73d931003ebf43d9310004fe72d9310004fd72d931003ebc42d9310006f671d931003ebf41d9310006f970d9310156be40d9310156bc40d931003ebc6459310004ff755931008cfe755931008cfc7559310006bf7459310004ff7359310024fc7359310004ff7259310004fc7259310014fc715931003ebc415931003ebf4059310004ff7655310004fe7655310004fd7655310004fc7655310006bf645531000ebc645531003f3c545531000cfe74d8f10004fd74d8f1000cfc74d8f10004fe72d8f10004fd72d8f10006f671d8f10006f970d8f1014ede30d8f1014edc30d8f1003dbe7498f10005bd7498f10006df6398f10005ee7298f10005ed7298f10004ff7458f1000cfe7458f1000cfc7458f10006df7358f10006df4358f10006dc4358f10004ff7258f10004fc7258f10026de6318f10006dd6318f10024ff7690f10004fe7690f10004fd7690f10024fc7690f10005f67190f10005f57190f10004ff7650f10004fe7650f10004fd7650f10004fc7650f10006bf6450f1000ebc6450f1000cfe74d8b10004fd74d8b1000cfc74d8b10024fe73d8b10004fd73d8b10006f671d8b10006f970d8b10166ee20d8b10166ec20d8b10006ef6298b1000cfe7498b10004fd7498b1000cfc7498b10024fe7398b10004fd7398b10005bf7458b1003dbc7458b10004ff7458b10006bf7458b10004bf7458b1000cfe7458b1000cfc7458b10006bc7458b1000cbc7458b10004ff7358b10024fc7358b10006ef7258b10006f47158b10005de7318b10005dd7318b10006ed6218b1000cfe7418b10004fd7418b1000cfc7418b10024fe7318b10006de7318b10024de7318b10004fd7318b10006dd7318b10004dd7318b10006ee7218b10006f67118b10006f97018b10136ee2018b10136ec2018b10004ff7690b10004fe7690b10004fd7690b10004fc7690b10006bf6490b1000ebc6490b10004ff7650b10004fe7650b10004fd7650b10004fc7650b100057f7550b101957c7550b10005f77150b10005f47150b10024ff76ccb10004fe76ccb10004fd76ccb10024fc76ccb10026de63ccb10006dd63ccb10005f671ccb10005f571ccb10004ff768cb10004fe768cb10004fd768cb10004fc768cb10006ef628cb10006ec628cb10
  | 10 => 0x882000cfc7498820024fe7398820006de7398820024de7398820004fd7398820006dd7398820004dd7398820016f83098820016ee2098820016fa2098820016ec209882005cff7690820014fe769082000cfd7690820014fc769082000ebe6490820006bd6490820015fa7090820005f9709082005cff76508200057f75508201b57c7550820047ac4250820005f77150820005f47150820004fd76cc820186df63cc820026dc63cc820015f870cc820187d830cc820004ff768c820024fd768c820026de638c820006dd638c820006ee628c820015fa708c820005f9708c820004ff764c820005bf744c820045bc744c82017edf634c820026dc634c820006ee624c820005f7714c820005f4714c820005fb704c820015f8704c82017fd8304c820024ff760c820014fe760c820004fd760c820014fc760c820026de630c820006dd630c820015fa700c820005f9700c82000cfe7498420004fd749842000cfc7498420024fe7398420004fd7398420016f67198420016f61098420016f41098420004ff7458420006bf7458420004bf745842000cfe745842000cfc7458420006bc745842000cbc7458420004ff7358420024fc7358420016f77158420016f61058420016f41058420004ff7690420014fe7690420004fd7690420156bf649042000ebc6490420006f66190420006f56190420004ff7650420004fd7650420014fc765042000ebe6450420006bd6450420005ef7250420005ec7250420006f66150420006f56150420047b44150420024ff76cc420014fe76cc420004fd76cc420045be74cc420005bd74cc420026de63cc420006dd63cc420005ee72cc420005ed72cc420004ff768c420014fe768c420004fd768c420006f6618c420006f5618c420015fa708c420005f9708c42014fd8308c420004ff764c420004fd764c420014fc764c420026de634c420006dd634c420005ef724c420005ec724c420006f6614c420006f5614c420005fb704c420015f8704c420024ff760c420014fe760c420004fd760c42016fd8300c420006f661c8420006f561c8420015fa70c8420005f970c8420004fd7688420165ed7688420006ed7688420166ef6388420006ed6388420135ee7188420006ed6188420165ed7088420166ee6088420167ea6088420167e83088420004ff7648420005bf7448420045bc7448420005de7308420005dd7308420006f66108420006f56108420007e52108420015fa7008420005f97008420007ce7308420007cd7308420136ef6308420006ed6308420165ee7108420007e67108420137e66108420006ed6108420137e561084201afe741084201afe44108420007e73108420007e43108420137ea7008420135ed7008420007e97008420136ee6008420137ea6008420137e83008420015f976cc02019ef
  | 11 => 0x4fd74d852000cfc74d8520024fe73d8520004fd73d8520006f741d8520006f441d8520006f76198520005bf745852004dbc7458520005df7358520005dc7358520006f5611852000cfe7418520004fd741852000cfc7418520024fe7318520004fd7318520006ee3218520006ed3218520006f74118520006f44118520136ee2018520136ec2018520004fe7690520004fd7690520004fc7690520006bf649052000ebc6490520004ff7650520004fe7650520004fc765052004fb44150520004fe76cc520004fd76cc520024fc76cc52004dbe74cc520005bd74cc520005ee72cc520005ed72cc520007cd32cc520006f761cc520006f461cc520004fe768c520004fd768c520004fc768c520006df638c520026dc638c520004ff764c520004fe764c520004fc764c520007cd324c520004fe760c520004fd760c520024fc760c520006df630c520026dc630c520005ee720c520005ed720c520006f7610c520006f4610c520004fe76c8520014fe7688520006f76188520006f46188520015fa7088520005f97088520014fc7648520005bf744852004dbc7448520006f76148520006f46148520005fb7048520015f87048520004fe7608520005de7308520005dd730852000cff765012004cfd765012000cfc7650120006bf645012000ebc6450120005df7350120005dc7350120005ef7250120005ec7250120004fe76cc120006df63cc120026dc63cc120005ee72cc120005ed72cc120024ff764c120004fd764c120024fc764c120006df634c120026dc634c120005ef724c120005ec724c120005de73c8120005dd73c8120015ee72c8120007da73c8120007d973c81201a6fa63c81201a6f863c8120015fa72c8120017eb62c8120007ea32c8120007e932c8120004ff755902008cfe755902008cfc7559020016bf7459020046be5459020004ff7359020024fc7359020046bf435902000cff725902000cfd7259020044fc7259020046bc4259020004ff7159020004fc7159020046bf4159020014fe7059020014fc7059020016be4059020016bc4059020004ff7655020014fe7655020004fd7655020014fc765502000ebe6455020006bd64550200473c5455020005ef7255020005ec7255020004ff7458c2000cfe7458c2000cfc7458c20016df7358c20024ff7258c20024fd7258c20004ff7158c20004fc7158c20014fe7058c20014fc7058c20016f87058c20014f87058c20016de3058c20016dc3058c20016f83058c20016ef2058c20016ed2058c20024ff7690c20014fe7690c20004fd7690c20014fc7690c20026de6390c20006dd6390c20004ff7650c20014fe7650c20004fd7650c20014fc7650c2000ebe6450c20006bd6450c20026de6350c20006dd6350c20005fb7050c20015f87050c2000cfe749882005cfd749
  | 12 => 0x261c8220017f161c822000cfe76d912004ebe64d912008cfe75d9120004fd75d912008cfc75d9120006bf54d912004ebc54d9120024fe73d9120004fd73d912004ebc43d912000cfe72d9120014fd72d912000cfc72d912004ebf42d9120004fe71d9120004fd71d912004ebc41d912004cfd70d912004ebf40d91200057f75591201bd7c755912004ebc6459120005df7359120005dc7359120005f77159120005f47159120004ff75591200067f75591200047f755912008cfe755912008cfc75591200067c755912008c7c755912004cff7459120006bf745912004ebe5459120004ff7359120006df7359120004df7359120024fc7359120006dc7359120024dc7359120054ff7259120006ef725912004ebc4259120004ff7159120006f77159120004f77159120004fc7159120006f47159120004f4715912005cff7059120006fb7059120004ff7655120004fe7655120004fd7655120004fc765512000ebe6455120006bd645512004f3c5455120024fe76d8d2000cfe74d8d20004fd74d8d2000cfc74d8d20006df43d8d20006dc43d8d20024fe72d8d20024fc72d8d20004fe71d8d20004fd71d8d20006df6398d20005bf7458d2004dbc7458d20005f77158d20005f47158d20004ff7458d20006bf7458d20004bf7458d2000cfe7458d2000cfc7458d20006bc7458d2000cbc7458d20006df7358d20004ff7258d20006ef7258d20004ff7158d20006f77158d20004f77158d20004fc7158d20006f47158d20004f47158d20004ff7058d20006fb7058d20004fb7058d2017ede3058d2017edc3058d20004fe7618d20026de6318d20006dd6318d20024ff7690d20004fe7690d20004fd7690d20024fc7690d20006bf6490d2000ebc6490d20005ee7290d20005ed7290d20004ff7650d20004fe7650d20004fd7650d20004fc7650d20054fe769092000ebe6490920006bd6490920014fc76509200057f75509201bd7c7550920006bf645092000ebc6450920005f77150920005f47150920005fb7050920015f87050920014fe76cc920014fc76cc920006df63cc920026dc63cc920015fa70cc920005f970cc920004fe768c920005ee768c920006ee768c920005ed738c920026ee638c920026ec638c920015ee708c920015ec708c920014fc764c920005bf744c92004dbc744c920006df634c920026dc634c920005f7714c920005f4714c920005fb704c920015f8704c920015ec764c920026ec764c920014ec764c920007af744c920007ac744c920007cf734c920007cf634c920026ee634c920026ec634c920007cc634c920007ce434c920007cd434c920007e7714c920007e4714c920007eb704c920015ee704c920015ec704c920007e8704c92017fce304c92017fcc304c920004fe760c920005ee720c92000cfe74d8520
  | 13 => 0x8620016f53098620016f43098620016f72098620016f62098620016f52098620016f42098620004ff745862000cfe745862000cfc7458620004ff7358620024fc7358620016f77158620006f74158620006f44158620016f61058620016f41058620006f77458620006f67458620006f57458620006f47458620006f65458620006f55458620006f45458620006f77358620006f67358620006f57358620006f47358620006f74358620006f64358620006f54358620006f44358620006f57258620006f74258620006f64258620006f54258620006f44258620006f73258620006f63258620006f53258620006f43258620016f77058620016f67058620016f47058620016f74058620016f64058620016f54058620016f44058620016f73058620016f63058620016f53058620016f43058620016f72058620016f62058620016f52058620016f42058620004ff7690620014fe7690620004fd76906200e67e65906200067d659062000ebe6490620006bd6490620006f66190620006f56190620004ff7650620004fd7650620014fc76506200de7e65506200067d655062000ebe6450620006bd6450620005ef7250620005ec7250620006f66150620006f56150620057b44150620024ff76cc620014fe76cc620004fd76cc620055be74cc620005bd74cc6200d6be64cc620006bd64cc620005ee72cc620005ed72cc620006f661cc620006f561cc620004ff768c620014fe768c620004fd768c6200cebe648c620006bd648c620006f6618c620006f5618c620004ff764c620004fd764c620014fc764c6200c6be644c620006bd644c620005ef724c620005ec724c620006f6614c620006f5614c620024ff760c620014fe760c620004fd760c6200bebe640c620006bd640c620006f6610c620006f5610c6200b6be64c8620006bd64c8620006f661c86200aebe6488620006bd6488620006f66188620006f56188620015fa7088620005f97088620167ae6488620167ad6488620166ef6388620006ed6388620167e66188620006ed6188620167e56188620167ea7088620165ed7088620007e97088620005bf7448620055bc74486200a6be6448620006bd6448620006f66148620006f56148620005fb7048620015f8704862009ebe6408620006bd6408620005de7308620005dd7308620006f56108620007e52108620135ed7608620006ed7608620137ae6408620137ad6408620007ce7308620007cd7308620136ef6308620006ed6308620007e67108620137e66108620006ed6108620137e56108620006e561086201c7e741086201c7e44108620007e73108620007e43108620135ed7008620015f976c8220006f976c8220017ba64c8220017b964c8220007da73c8220007d973c82201a6fa63c8220016f863c8220017ea72c8220017f
  | 14 => 0x24fc7359220056bf4359220056bc4359220056bf4259220004ff7159220004fc7159220056bf4159220056bc4159220014fc7059220016be4059220016bc4059220006bf7559220006be7559220006bd7559220006bc7559220006bf7359220006be7359220006bd7359220006bc7359220006bf5359220006bc5359220006bf7259220006bd7259220056bc7259220006bf5259220006bc5259220006bf7159220006be7159220006bd7159220006bc7159220006bf5159220006bc5159220016bf7059220016be7059220016bd7059220016bc7059220016bf5059220016be5059220016bd5059220016bc5059220016bf3059220016be3059220016bd3059220016bc3059220016bf2059220016be2059220016bd2059220016bc2059220016bf1059220016be1059220016bd1059220016bc1059220004ff7655220014fe7655220004fd7655220014fc765522000ebe6455220006bd64552200573c5455220005ef7255220005ec7255220004ff7458e2000cfe7458e2000cfc7458e20016df7358e20004ff7158e20004fc7158e20014fc7058e20016de3058e20016dc3058e20016ef2058e20016ed2058e20024ff7690e20014fe7690e20004fd7690e20014fc7690e201267e6590e200067d6590e2000ebe6490e20006bd6490e20004ff7650e20014fe7650e20004fd7650e20014fc7650e2011e7e6550e200067d6550e2000ebe6450e20006bd6450e20016ee2058a2004cfd7690a201167e6590a200067d6590a2000ebe6490a20006bd6490a2000cff7650a20014fc7650a200057f7550a201cd7c7550a2010e7e6550a200067d6550a2000ebe6450a20006bd6450a20057ac4250a20005f77150a20005f47150a20005fb7050a20015f87050a20106be64cca20006bd64cca20026de63cca20006dd63cca20015fa70cca20005f970cca200febe648ca20006bd648ca20024ff764ca20005bf744ca20055bc744ca200f6be644ca20006bd644ca20026de634ca20006dd634ca20005f7714ca20005f4714ca20005fb704ca20015f8704ca200eebe640ca20006bd640ca2000cfe7498620004fd749862000cfc7498620024fe7398620004fd7398620016f67198620006f74198620006f44198620016f61098620016f41098620006f77498620006f67498620006f57498620006f47498620006f65498620006f55498620006f45498620006f77398620006f67398620006f57398620006f47398620006f74398620006f64398620006f54398620006f44398620006f77298620006f74298620006f64298620006f54298620006f44298620006f73298620006f63298620006f53298620006f43298620016f67098620016f57098620016f47098620016f74098620016f64098620016f54098620016f44098620016f73098620016f6309
  | 15 => 0x8704cb20015e8704cb2017fce304cb2017fcc304cb20014fd760cb20026de630cb20006dd630cb20015fa700cb20005f9700cb2005dbe74d8720005bd74d8720005de73d8720005dd73d8720006de63d8720006dd63d8720006de6398720006dd6398720006f7619872000cfe7498720004fd749872000cfc7498720024fe7398720004fd7398720006ee3298720006ed3298720166ee2098720166ec2098720006de6358720006dd6358720004ff745872000cfe745872000cfc7458720004ff7358720024fc7358720005de7318720005dd7318720006de6318720006dd6318720006f56118720004ff7690720004fe7690720004fd769072000ebe6490720006bd6490720006de6390720006dd6390720004ff7650720004fd7650720004fc7650720006de6350720006dd635072005fb44150720024ff76cc720004fe76cc720004fd76cc72005dbe74cc720005bd74cc720026de63cc720006dd63cc720005ee72cc720005ed72cc720007cd32cc720004ff768c720004fe768c720004fd768c720026de638c720006dd638c720015fa708c720005f9708c720004ff764c720004fd764c720004fc764c720026de634c720006dd634c720007cd324c720005fb704c720015f8704c720024ff760c720004fe760c720004fd760c720026de630c720006dd630c720005ee720c720005ed720c720014fd76c8720006de63c8720006dd63c8720006f661c8720006f561c8720015fa70c8720005f970c8720006de6388720006dd6388720005bf744872005dbc7448720006de6348720006dd6348720014fd7608720005de7308720005dd7308720006de6308720006dd6308720006f66108720006f56108720015fa7008720005f9700872000cff765032000ebe6450320006bd6450320005df7350320005dc7350320006de6350320006dd6350320005ef7250320005ec7250320026de63cc320006dd63cc320005ee72cc320005ed72cc320005f976cc3201a6f976cc3201a6fb63cc3201a7da63cc3201a6f963cc320007d963cc3201a7ea72cc320005f972cc3201a7e972cc320016fa62cc3201a7ea32cc3201a7e932cc320024ff764c320026de634c320006dd634c320005ef724c320005ec724c320017d8304c320005f9760c320016f9760c320017ba740c320017b9740c320017da730c3201a6fb630c3201a7da630c3201a6f9630c320007d9630c320006d9630c3201d7db430c3201a7d8430c320017ea720c320005f9720c320017e9720c320005e9720c320017ea620c3201a7db320c3201a7ea320c320007d9320c3201a7e9320c320007c9320c320017f2710c320017f1710c320007da310c3201a7d8310c320004ff755922008cfe755922008cfc7559220016bf7459220006bf5459220056be5459220056bc5459220004ff7359220
  | 16 => 0x5320004fc765532000ebe6455320006bd645532005f3c545532000cfe74d8f20004fd74d8f2000cfc74d8f20006ee72d8f20004fe71d8f20004fd71d8f20006f970d8f20006df6398f20006df6498f20006de6498f20006dd6498f20006dc6498f20007ce7298f201a7db7098f20187ce2098f20187cc2098f20026df7498f20026de7498f20026dd7498f20026dc7498f20006de5498f20006dd5498f20006dc5498f20026de7298f20026ce7298f20026dc7298f20006df4298f20006dc4298f20026df7198f20026de7198f20026dd7198f20026dc7198f20006df4198f20006dc4198f20026df7098f20026de7098f20026dd7098f20026dc7098f20006df4098f20186de4098f20186dc4098f20186de2098f20186dc2098f20186de1098f20186dc1098f20004ff7458f2000cfe7458f2000cfc7458f20006df7358f20006df4358f20006dc4358f20004ff7158f20004fc7158f20006fb7058f20006df7658f20006df6458f20006de6458f20006dd6458f20006dc6458f2017fce7258f20007db7058f2017fce2058f2017fcc2058f20006df7458f20006de7458f20006dd7458f20006dc7458f20006de5458f20006dd5458f20006dc5458f2017ede7258f20006dc7258f20006df4258f20006dc4258f20006df7158f20006de7158f20006dd7158f20006dc7158f20006df4158f20006dc4158f20006df7058f20006db7058f2017ede7058f20006dd7058f2017edc7058f20006df4058f2017ede4058f2017edc4058f2017ede2058f2017edc2058f2017ede1058f2017edc1058f20026de6318f20006dd6318f20024ff7690f20004fe7690f20004fd7690f20024fc7690f20026de6390f20006dd6390f20005ee7290f20005ed7290f20004ff7650f20004fe7650f20004fd7650f20004fc7650f20026de6350f20006dd6350f20005fb7050f20015f87050f20014fd7690b2000ebe6490b20006bd6490b20006de6390b20006dd6390b20015fa7090b20005f97090b20044ff7650b200057f7550b201dd7c7550b20006de6350b20006dd6350b20005f77150b20005f47150b20026de63ccb20006dd63ccb20014fd768cb20026de638cb20006dd638cb20015fa708cb20005f9708cb20015ed768cb20026ed768cb20014ed768cb20026ee638cb20007ce638cb20007cd638cb20026ec638cb20015ee708cb20007ea708cb20007e9708cb20015ec708cb20005bf744cb2005dbc744cb20026de634cb20006dd634cb20005f7714cb20005f4714cb20015f8704cb20005ef764cb20006ef764cb20007af744cb20007ac744cb20007cf734cb20026ee634cb20007ce634cb20026ce634cb20007cd634cb20026ec634cb20007ce434cb20007cd434cb20007e7714cb20007e4714cb20007eb704cb20015ee704cb20015ec704cb20007e
  | 17 => 0x6f55458430006f45458430026f77358430026f67358430026f47358430026f74358430026f64358430026f54358430026f44358430006f77258430006f67258430006f57258430006f47258430006f74258430006f64258430006f54258430006f44258430026f73258430026d73258430026f63258430026f53258430006d53258430026f43258430016f77058430016f67058430016f47058430016f74058430016f64058430016f54058430016f44058430016f73058430016f63058430016f53058430016f43058430016f72058430016f62058430016f52058430016f42058430004ff7690430014fe7690430004fd76904300e67e65904300067d659043000ebe6490430006bd6490430025de7390430005dd73904300679f4390430006ee6290430006ed6290430006f66190430006f56190430004ff7650430004fd7650430014fc76504300de7e65504300067d655043000ebe6450430006bd6450430005df7350430025dc7350430006ee6250430006ed6250430006f66150430006f56150430067b44150430025dd768c430006dd768c430065de748c430065dc748c4300279e648c4300279d648c430005dd728c430027ce628c430027cd628c430025de718c430027d6718c430027d6618c430006dd618c430027d5618c430006d5618c43014ddd708c43014ede608c430027da608c430004ff76c8430014fe76c8430004fd76c84300b6be64c8430006bd64c8430025de73c8430005dd73c8430006ee62c8430006ed62c8430006f661c8430006f561c8430147d431c8430004ff7688430014fe7688430004fd76884300aebe6488430006bd6488430005df7388430025dc7388430006ee6288430006ed6288430007cd3288430006f66188430006f56188430015fa7088430005f97088430004ff7648430004fd7648430014fc7648430005bf7448430065bc74484300a6be6448430006bd6448430005df7348430025dc7348430006ee6248430006ed6248430006f66148430006f56148430005fb7048430015f87048430004ff7608430014fe7608430004fd760843009ebe6408430006bd6408430025de7308430005dd7308430006ee6208430006ed6208430007cd3208430006f66108430006f5610843013fd4310843005ebe64d9320005de73d9320005dd73d932008cfe75d9320004fd75d932008cfc75d9320024fe73d9320006de73d9320024de73d9320004fd73d9320006dd73d9320004dd73d9320006ee72d9320004fe71d9320004fd71d9320006f970d932005ebc6459320004ff755932008cfe755932008cfc7559320006bf745932005ebe5459320004ff7359320024fc7359320014fc725932005ebc4259320004ff7159320004fc715932005ebc415932005ebf4059320004ff7655320004fe7655320004fd765
  | 18 => 0xe7458830006ed7458830006ec7458830006ee5458830006ed5458830006ec5458830026ef7358830026ee7358830026ec7358830026ef4358830026ee4358830026ed4358830026ec4358830006ef7158830006ee7158830006ed7158830006ec7158830006ef4158830006ec4158830026ef3158830026ee3158830026ed3158830026ec3158830016ef7058830016ee7058830016ec7058830016e87058830016ef4058830016ee4058830016ed4058830016ec4058830016ef3058830016ee3058830016ed3058830016ec3058830016ef1058830016ee1058830016ed1058830016ec1058830004ff7690830014fe7690830004fd76908301167e65908300067d659083000ebe6490830006bd6490830025de7390830005dd73908301ef9c4390830006ee6290830006ed6290830004ff7650830004fd7650830014fc76508300057f75508301e57c755083010e7e65508300067d655083000ebe6450830006bd6450830005df7350830025dc7350830006ee6250830006ed6250830005f77150830005f47150830005fb7050830015f87050830025df764c830006df764c8300079f744c830065de744c830065dc744c8300079c744c8300659c744c830026df644c8300279e644c830006dd644c8300279d644c8300069d644c830025df724c830027cf724c830006de624c830027ce624c830006ce624c830027cd624c830007d7714c830005dc714c830007d4714c830005d4714c830027d6614c830027d5614c83017ddf704c830007db704c830005db704c83017fd8704c83017ede604c830027da604c83000cfe7498430004fd749843000cfc7498430004fe7298430004fd7298430016f67198430006f74198430006f44198430026f73198430026f43198430016f61098430016f41098430006f77498430006f67498430006f57498430006f47498430006f65498430006f55498430006f45498430026f67398430026f57398430026f47398430026f74398430026f64398430026f54398430026f44398430006f77298430006f67298430006f57298430006f47298430006f74298430006f64298430006f54298430006f44298430026f73298430026f63298430026f53298430026f43298430016f67098430016f57098430016f47098430016f74098430016f64098430016f54098430016f44098430016f73098430016f63098430016f53098430016f43098430016f72098430016f62098430016f52098430016f42098430004ff745843000cfe745843000cfc7458430004ff7258430004fc7258430026df3258430006dd3258430016f77158430006f74158430006f44158430026f73158430026dc3158430026f43158430016f61058430016f41058430006f77458430006f67458430006f57458430006f47458430006f65458430
  | 19 => 0x853000cff765013006cfd7650130024fc7650130006bf645013000ebc6450130005df7350130025dc7350130004ff755903008cfe755903008cfc7559030014ff7459030016bf7459030006bf5459030066be5459030066bc5459030024ff7359030024fe7359030024fd7359030024fc7359030026dc7359030024dc7359030066df4359030026be4359030026bc4359030026dc4359030004ff7259030004fc7259030066bf4259030066bc4259030026df3259030004ff7159030004fc7159030066bf4159030066bc4159030014fe7059030014fc7059030016be4059030016bc4059030006bf7559030006be7559030006bd7559030006bc7559030026bf73590300669f7359030026be7359030026bd7359030026bc73590300269c7359030026bf5359030026be5359030026bd5359030026bc5359030006bf7259030006be7259030006bd7259030006bc7259030006bf5259030006bc5259030026bf32590300269f3259030026be3259030026bd3259030026bc3259030006bf7159030006be7159030006bd7159030006bc7159030006bf5159030006bc5159030026bf3159030026be3159030026bd3159030026bc3159030016bf7059030016be7059030016bd7059030016bc7059030016bf5059030016be5059030016bd5059030016bc5059030016bf3059030016be3059030016bd3059030016bc3059030016bf2059030016be2059030016bd2059030016bc2059030016bf1059030016be1059030016bd1059030016bc1059030004ff7655030014fe7655030004fd7655030014fc765503000ebe6455030006bd64550300673c5455030005df7355030025dc73550301f79c435503000cfe7498830004fd749883000cfc7498830016ee7298830006ef4298830006ec4298830026df3298830026ef3298830026ec3298830004fe7198830004fd7198830016ee2098830016ec2098830006ef7498830006ee7498830006ed7498830006ec7498830006ee5498830006ed5498830006ec5498830026ee7398830026ed7398830026ec7398830026ef4398830026ee4398830026ed4398830026ec4398830006ef7198830006ee7198830006ed7198830006ec7198830006ef4198830006ec4198830026ef3198830026ee3198830026ed3198830026ec3198830016ee7098830016ed7098830016ec7098830016ef4098830016ee4098830016ed4098830016ec4098830016ef3098830016ee3098830016ed3098830016ec3098830016ef1098830016ee1098830016ed1098830016ec1098830004ff745883000cfe745883000cfc7458830016ef7258830006ef4258830006ec4258830026ef3258830026ec3258830004ff7158830004fc7158830016f87058830016ee2058830016ec2058830016f82058830006ef7458830006e
  | 20 => 0x25dc7388630007cd3288630004ff7648630004fd7648630014fc7648630005bf7448630075bc7448630005df7348630025dc7348630004ff7608630014fe7608630004fd7608630025de7308630005dd7308630007cd3208630006f66108630006f56108630007d4310863000cfe76d913006ebe64d913008cfe75d9130004fd75d913008cfc75d913006ebe54d9130024fe73d9130014fd73d9130024fc73d913006ebf43d9130004fe72d9130004fd72d913006ebc42d9130004fe71d9130004fd71d913006ebc41d9130024fd70d913006ebf40d913006ebc6459130004ff755913008cfe755913008cfc755913006cff7459130006bf7459130074ff7359130006df7359130074df7359130004ff7259130004fc7259130004ff7159130004fc715913007cff7059130006fb7059130004ff7655130004fe7655130004fd7655130004fc7655130006bf645513000ebc645513006f3c5455130014fc7650d30006bf6450d3000ebc6450d30005fb7050d30015f87050d3000cfe74d8930004fd74d893000cfc74d8930004fe71d8930004fd71d8930186de30d8930186dc30d8930006ef6298930005bf745893006dbc7458930005f77158930005f47158930006ed621893000cfe7418930004fd741893000cfc7418930004fe7118930004fd711893019efb301893019ef83018930004fe7690930004fd7690930004fc7690930006bf649093000ebc6490930004ff7650930004fe7650930004fc76509300057f75509301fd7c7550930005f77150930005f47150930014fe768c930006ef628c930006ec628c930015fa708c930005f9708c930027d8308c930014fc764c930005bf744c93006dbc744c930006ef624c930006ec624c930005f7714c930005f4714c930005fb704c930015f8704c93000cfe74d8530004fd74d853000cfc74d8530004fe72d8530004fd72d8530006f76198530005bf745853006dbc7458530005ef7258530005ec7258530006f5611853000cfe7418530004fd741853000cfc7418530004fe7218530004fd721853016ede301853016edc3018530004fe7690530004fd7690530004fc7690530006bf649053000ebc6490530004ff7650530004fe7650530004fc765053006fb44150530014fe768c530006f7618c530006f4618c530015fa708c530005f9708c530014fc764c530006f7614c530006f4614c530005fb704c530015f8704c530004fe76c8530004fd76c8530004fc76c8530006f761c8530006f461c8530004fe7688530004fd7688530004fc7688530006ef6288530006ec6288530004ff7648530004fe7648530004fc7648530005bf744853006dbc7448530004fe7608530004fd7608530004fc7608530025de7308530005dd7308530006ef6208530006ec6208530006f76108530006f4610
  | 21 => 0xb7050e30015f87050e3000cfe7498a30004fd7498a3000cfc7498a30016ee7298a30004fe7198a30004fd7198a30014fe7098a301a6fb3098a30016f83098a30016ee2098a30016ec2098a30004ff7458a3000cfe7458a3000cfc7458a30016ef7258a30004ff7158a30004fc7158a30014fc7058a30016ee2058a30016ec2058a30004ff7690a30014fe7690a30004fd7690a3000ebe6490a30006bd6490a30025de7390a30005dd7390a300779c4390a30004ff7650a30004fd7650a30014fc7650a300057f7550a302057c7550a30005df7350a30025dc7350a30005f77150a30005f47150a30185dd76cca30026dd76cca30075de74cca30025dc74cca30186df64cca30006dd64cca30006de62cca30005de71cca30025df70cca30185dd70cca30027da60cca30006ee628ca30006ed628ca30015fa708ca30005f9708ca30005bf744ca30075bc744ca30006ee624ca30006ed624ca30005f7714ca30005f4714ca30005fb704ca30015f8704ca300079f744ca30075de744ca30075dc744ca300079c744ca300759c744ca3017edf644ca30006dd644ca30025df724ca30027cf724ca30006de624ca3017fce624ca3017fcd624ca30007d7714ca30005dc714ca30007d4714ca30005d4714ca3017ddf704ca30007db704ca3017fd8704ca30026de604ca3000cfe7498630004fd749863000cfc7498630004fe7298630004fd7298630016f67198630014fe7098630016f61098630016f41098630004ff7458630006bf7458630004bf745863000cfe745863000cfc7458630006bc745863000cbc7458630004ff7258630006ef7258630004ef7258630004fc7258630006ec7258630004ec7258630006df3258630006dd3258630016f77158630014fc7058630016f61058630016f41058630004ff7690630014fe7690630004fd7690630156bf649063000ebc6490630025de7390630005dd73906300779f4390630006f66190630006f56190630004ff7650630004fd7650630014fc765063000ebe6450630006bd6450630005df7350630025dc7350630006f66150630006f56150630077b44150630006f6618c630006f5618c630015fa708c630005f9708c630075de748c630075dc748c630005dd728c630025de718c63014fd6618c630006dd618c63014fd5618c63014fda708c63014ddd708c630007d9708c630026de608c630006f6614c630006f5614c630005fb704c630015f8704c63016ddd760c630026dd760c630075de740c630025dc740c630005dd720c630027d6710c630006dd610c630025df700c63016ddd700c630027da600c630004ff76c8630014fe76c8630004fd76c8630025de73c8630005dd73c8630006f661c8630006f561c8630007d431c8630004ff7688630014fe7688630004fd7688630005df7388630
  | 22 => 0x854009fb74108540015fa7008540005f9700854000cfe765414021cfd765414000cfc7654140005bf745414000dbc74541400073d5454140006df6354140006dc6354140004ff755933008cfe755933008cfc7559330026bf7459330014fc7359330026be4359330026bc4359330004ff7259330004fc7259330004ff7159330004fc715933007ebc415933007ebf4059330004ff7655330024fe7655330004fd7655330024fc76553301f6bf645533000ebc645533007f3c545533000cfe7498b30004fd7498b3000cfc7498b30014fe7398b30026ee7298b30026ef3298b30026ec3298b30004fe7198b30004fd7198b30004ff7458b30006bf7458b30004bf7458b3000cfe7458b3000cfc7458b30006bc7458b3000cbc7458b30014fc7358b30026ef7258b30026ef3258b30026ec3258b30004ff7158b30006f77158b30004f77158b30004fc7158b30006f47158b30004f47158b30006fb7058b3017ede3058b30026dc3058b30004ff7690b30024fe7690b30004fd7690b301eebf6490b3000ebc6490b30004ff7650b30004fd7650b30024fc7650b300057f7550b302157c7550b30005f77150b30005f47150b30005fb7050b30015f87050b3000cfe7498730004fd749873000cfc7498730014fe7398730004fe7298730004fd7298730026f67198730026f73198730026f4319873014ede3098730026dc3098730004ff745873000cfe745873000cfc7458730014fc7358730004ff7258730004fc7258730026f77158730026f73158730026f43158730004ff7690730024fe7690730004fd769073000ebe6490730006bd6490730004ff7650730004fd7650730024fc765073007fb44150730004ff76c8730024fe76c8730004fd76c8730004ff7688730024fe7688730004fd7688730006ee6288730006ed6288730015fa7088730005f97088730004ff7648730004fd7648730024fc7648730005bf744873007dbc7448730005fb7048730015f87048730004ff7608730024fe7608730004fd7608730025de7308730005dd7308730006ee6208730006ed620873000cff7650330024fc765033000ebe6450330006bd6450330005df7350330025dc7350330004ff755923008cfe755923008cfc7559230016bf7459230076be5459230076df7359230076bf4359230076df4359230076dc4359230004ff7259230004fc7259230076bc4259230004ff7159230004fc7159230076bf4159230014fc7059230016be4059230016bc4059230004ff7655230014fe7655230004fd7655230014fc765523000ebe6455230006bd64552300773c5455230005df7355230025dc73552300779c4355230026fb3058e30016de3058e30016dc3058e30016f83058e3000cff7650e30014fc7650e3000ebe6450e30006bd6450e3020ddf7350e30005f
  | 23 => 0x15f8704c940004fe760c940004fd760c940024fc760c94000dbe740c940005bd740c940006df630c940026dc630c940006df63d8540006dc63d854008cfe75d8540004fd75d854008cfc75d8540014fd74d8540024fe73d8540004fd73d8540004fe72d8540004fd72d8540006f751d8540006f451d8540036f641d8540036f541d8540005de7398540005dd7398540006df6398540006dc6398540006f7619854002df970985400057f75585400857c7558540005df7358540005dc7358540006df6358540006dc6358540005ef7258540005ec725854003dfb7058540006df6318540006dc6318540006f5611854008cfe7518540004fd751854008cfc7518540014fd741854001ebe5418540006bd5418540024fe7318540004fd731854001ebf4318540006bd4318540004fe7218540004fd7218540006be421854001ebc4218540006f75118540006f4511854001ebf411854001ef6411854001ef54118540176be4018540176bc4018540004fe7694540004fd7694540004fc76945400067f659454008e7c659454000dbe7494540005bd74945400073d5494540006df6394540006dc6394540004ff7654540004fe7654540004fc765454000dbe7454540006df6354540006dc6354540014bc7650540005bf7550540005bd7550540005bf73505400079f63505400079c6350540005bc725054000dbf715054000fb77150540007b76150540006bc6150540007b46150540006b46150540007bb7050540015be7050540015bc7050540007b8705054000ebf605054000fbb6050540004fe76cc540004fd76cc540024fc76cc5400857e75cc5400057d75cc54000dbe74cc540005bd74cc540006df63cc540026dc63cc540005ee72cc540005ed72cc540004fe768c540004fd768c540004fc768c54000dbe748c540005bd748c540006df638c540026dc638c540015fa708c540005f9708c540004ff764c540004fe764c540004fc764c54000dbe744c540005bd744c540006df634c540026dc634c540004fe760c540004fd760c540024fc760c54000dbe740c540005bd740c540006df630c540026dc630c540004fe76c8540004fd76c8540004fc76c8540005bf74c854000dbc74c8540006df63c8540006dc63c8540006f761c8540006f461c85400b7b741c8540004fe7688540004fd7688540004fc768854000dbe7488540005bd7488540006df6388540006dc6388540006ef6288540006ec6288540004ff7648540004fe7648540004fc76485400057f75485400857c7548540005bf744854000dbc7448540006df6348540006dc6348540004fe7608540004fd7608540004fc760854000dbe7408540005bd7408540005de7308540005dd7308540006df6308540006dc6308540006ef6208540006ec6208540006f76108540006f4610
  | 24 => 0xd7118d40026dc7118d40006df5118d40006dc5118d40066df4118d40066de4118d40066dd4118d40066dc4118d40026df7018d40026de7018d40026dd7018d40026dc7018d40006df5018d4022ede5018d4022edc5018d40066df4018d4022ede4018d40066dd4018d4022edc4018d4022ede2018d4022edc2018d4022ede1018d4022edc1018d40004fe7694d40004fd7694d40024fc7694d4000dbe7494d40005bd7494d400073d5494d40006df6394d40026dc6394d400875f5394d40004ff7654d40004fe7654d40004fc7654d4000dbe7454d40006df6354d40026dc6354d40014bc7650d40005bf7550d40005bd7550d4000dbf7350d4000f9f7350d400079f6350d40026be6350d40026bc6350d400079c6350d40005bc7250d40005bf7150d40007bb7050d40015be7050d40015bc7050d40007b87050d4000ebf6050d4000fbb6050d40006df63d8940006dc63d894008cfe75d8940004fd75d894008cfc75d8940014fd74d8940056be54d8940006bd54d8940024fe73d8940004fd73d8940006ef52d8940006ec52d8940056ee42d8940056ed42d8940056bc42d8940004fe71d8940004fd71d8940005de7398940005dd7398940006df6398940006dc6398940006ef629894004df970989400057f75589400857c7558940005df7358940005dc7358940006df6358940006dc6358940005f77158940005f4715894005dfb7058940006df6318940006dc6318940006ed621894008cfe7518940004fd751894008cfc7518940014fd7418940024fe7318940004fd7318940006ef5218940006ec5218940046ee4218940046ed4218940004fe7118940004fd7118940004fe7694940004fd7694940004fc76949400067f659494008e7c659494000dbc74949402273e5494940006df6394940006dc6394940004ff7654940004fe7654940004fc7654940005bf745494000dbc74549400073d5454940006df6354940006dc6354940005f77154940005f47154940014be7690940005bf7590940005bd7590940116be6590940116bc6590940005bd73909400079f63909401eebc63909400079c63909400069c639094000dbe729094000fae7290940006bf6290940007af6290940007ac6290940005bd7190940015be7090940007ba7090940007b97090940015bc709094000ebf609094000fbb6090940004fe76cc940004fd76cc940024fc76cc94000dbe74cc940005bd74cc940006df63cc940026dc63cc9400079d43cc940004fe768c940004fd768c940004fc768c940005bf748c94000dbc748c940006df638c940026dc638c940004ff764c940004fe764c940004fc764c9400057f754c9400857c754c940005bf744c94000dbc744c940006df634c940026dc634c9400079d434c940005f7714c940005f4714c940005fb704c940
  | 25 => 0x9540005ef7259540005ec7259540005f77159540005f47159540235fb705954021cff7459540006bf7459540004ff7359540006df7359540004df7359540024fc7359540006dc7359540024dc7359540004ff7259540006ef7259540004ef7259540004fc7259540006ec7259540004ec7259540004ff7159540006f77159540004f77159540004fc7159540006f47159540004f47159540234ff7059540006fb7059540015bc765514008ebc7655140014bc765514000dbf755514000f3f75551400073f655514008ebe655514008ebc65551400873c655514008e3c6555140005bf73551401f6bc63551400873c5355140005bc72551400873f5255140005bf71551400873c5155140007bb7055140015be7055140015bc7055140007b8705514000ebf605514000fbb60551400873f505514008cfe75d8d40004fd75d8d4008cfc75d8d40014fd74d8d40006df53d8d40006dc53d8d40076de43d8d40076dd43d8d40004fe72d8d40004fd72d8d40004fe71d8d40004fd71d8d40006df65d8d40006de65d8d40006dd65d8d40006dc65d8d4020f9f74d8d400779c74d8d400779e54d8d400079d54d8d400779c42d8d400779f41d8d40077db40d8d4020f9e40d8d4020f9c40d8d40077d840d8d40006df75d8d40006de75d8d40006dd75d8d40006dc75d8d4020edf74d8d40076de74d8d40076dc74d8d40076df54d8d40076de54d8d40076dd54d8d40076dc54d8d40006df72d8d40006de72d8d40006dd72d8d40006dc72d8d40006df52d8d40006dc52d8d40076df42d8d40076de42d8d40076dd42d8d40076dc42d8d40006df71d8d40006de71d8d40006dd71d8d40006dc71d8d40006df51d8d40006dc51d8d40076df41d8d40076de41d8d40076dd41d8d40076dc41d8d40076df70d8d4020ede70d8d40076dd70d8d4020edc70d8d40006df50d8d4020ede50d8d4020edc50d8d40076df40d8d4020ede40d8d4020edc40d8d4020ede20d8d4020edc20d8d4020ede10d8d4020edc10d8d40006df6398d4006df97098d4007dfb7058d40026de6318d40006dd6318d40075de7618d40006de7618d40006df6518d40006de6518d40006dd6518d40006dc6518d400679e7418d400079d7418d400679e5418d400079d5418d400679c4218d400679f4118d40067db4018d4022f9e4018d4022f9c4018d40067d84018d40026df7518d40026de7518d40026dd7518d40026dc7518d40026df7418d40026de7418d400269e7418d40026dc7418d40066df5418d40066de5418d400669e5418d40066dd5418d400069d5418d40066dc5418d40026df7218d40026de7218d40026dd7218d40026dc7218d40006df5218d40006dc5218d40066df4218d40066de4218d40066dd4218d40066dc4218d400669c4218d40026df7118d40026de7118d40026d
  | 26 => 0x8e7e6594a400067d6594a40004ff7654a40004fd7654a40014fc7654a40005bf7454a4000dbc7454a40005f77154a40005f47154a40024ff76cca40014fe76cca40004fd76cca40026dc63cca40004ff768ca40014fe768ca40004fd768ca40006ee628ca40006ed628ca40004ff764ca40004fd764ca40014fc764ca400057f754ca400957c754ca40005bf744ca4000dbc744ca40006ee624ca40006ed624ca40005f7714ca40005f4714ca40005fb704ca40015f8704ca40024ff760ca40014fe760ca40004fd760ca4008cfe7598640004fd759864008cfc7598640024fe7398640004fd7398640004fe7298640004fd7298640016f6719864003ef6419864003ef54198640014fe7098640016f61098640016f41098640004ff75586400067f75586400047f755864008cfe755864008cfc75586400067c755864008c7c7558640004ff7358640024fc7358640004ff7258640004fc7258640016f7715864002ef6415864002ef5415864002ebc4158640014fc7058640016bf4058640016bd4058640016f61058640016f41058640004ff7694640014fe7694640004fd769464008e7c6594640006f66194640006f56194640004ff7654640004fd7654640014fc765464008e7e65546400067d6554640005bf745464000dbc7454640006f66154640006f56154640156bf6590640006bd6590640006bd6390640006be629064000dbe719064000fb67190640157b66190640006bd6190640157b56190640157ba7090640155bd7090640007b9709064000ebe609064000fba6090640024ff76cc640014fe76cc640004fd76cc6400957e75cc6400057d75cc64000dbe74cc640005bd74cc640005ee72cc640005ed72cc640004ff768c640014fe768c640004fd768c640006f6618c640006f5618c640015fa708c640005f9708c640004ff764c640004fd764c640014fc764c640005bf744c64000dbc744c640006f6614c640006f5614c640024ff760c640014fe760c640004fd760c640004ff76c8640014fe76c8640004fd76c864000dbe74c8640005bd74c8640006f661c8640006f561c86400b7b441c8640004ff7688640014fe7688640004fd7688640004ff7648640004fd7648640014fc76486400057f75486400957c7548640005bf744864000dbc7448640004ff7608640014fe7608640004fd7608640005de7308640005dd7308640006f66108640006f5610864009fb44108640015fa7008640005f9700864008cfe76d95400867e65d9540014ff74d954000cfe74d9540014fd74d954000cfc74d954023e7f54d954023e7d54d9540024fe73d9540004fd73d9540004fe72d9540004fd72d95400867c52d9540004fe71d9540004fd71d95400867c51d954000cfd70d95400867f50d95400867c6559540005df7359540005dc735
  | 27 => 0x5320c421005f5700c421006de63c8421006dd63c8421005ef73c8421005ed73c8421007ce63c8421007cd63c8421247e741c8421247e441c8421007e731c8421007e431c8421135ee70c8421006de6388421006dd6388421005ed7288421006ee628842109df6748842109df4748842113df6738842113df47388421007d66388421007d56388421005f57288421006f66288421007e66288421007e63288421007e53288421005f57088421004ff7648421005bf744842109dbc7448421006de6348421006dd6348421005ef7648421006ef7648421004ef7648421007af7448421007ac7448421005ef7348421005ed7348421007ce6348421007cd6348421005ef7148421006ee6148421007e63148421007e53148421135ec7048421005f77648421006f77648421004f77648421007b7744842109df6744842109df47448421007b4744842109db4744842113df6734842113df47348421007d66348421007d56348421005f77248421007e77248421006f66248421007e66248421007e63248421007e53248421005f77048421005de73d8021005dd73d8021006de63d8021006dd63d8021006de6398021006dd6398021006fb6098021006de6358021006dd6358021004ff745802100cfe745802100cfc7458021004ff7358021024fc7358021006ee3258021006ed325802109dbe7418021005bd7418021005de7318021005dd7318021006de6318021006dd6318021016fa6018021006f960180210167f755964021e7f545964021e7d5459640004ff7359640024fc73596400967f5359640004ff7259640004fc72596400967c5259640004ff7159640004fc71596400967f515964021ebc4159640014fe7059640014fc70596400167e50596400167c5059640016bf4059640016bd4059640004ff7558e4008cfe7558e4008cfc7558e40016df7358e4006ede4358e4006edd4358e40004ff7258e40004fc7258e40004ff7158e40004fc7158e4006ebc4158e40014fc7058e40016bf4058e40016bd4058e40016de3058e40016dc3058e40024ff7694e40014fe7694e40004fd7694e400975f5394e40004ff7654e40004fd7654e40014fc7654e4008e7e6554e400067d6554e4008cfe7598a40004fd7598a4008cfc7598a40024fe7398a40006de7398a40024de7398a40004fd7398a40006dd7398a40004dd7398a40016ee7298a4005eee4298a4005eed4298a40004fe7198a40004fd7198a4005ebc4198a40014fe7098a40016bf4098a40016bd4098a40016ee2098a40016ec2098a40004ff7558a4008cfe7558a4008cfc7558a40004ff7358a40024fc7358a40016ef7258a4004eee4258a4004eed4258a40004ff7158a40004fc7158a40014fc7058a40016ee2058a40016ec2058a40004ff7694a40014fe7694a40004fd7694a40
  | 28 => 0x8821024fe7398821004fd73988210b6f741988210b6f441988210b4ff769082100cfd769082100ebe6490821006bd6490821006de6390821006dd6390821005f67190821005f5719082109fb441908210b4ff76508210057f755082125d7c7550821006de6350821006dd6350821005f7715082109df47150821004fd76cc821026de63cc821006dd63cc821004ff768c821024fd768c821026de638c821006dd638c821005f6718c821005f5718c821026ed768c821024ed768c821005ed738c821026ee638c821007ce638c821007cd638c821026ec638c821007e6718c821005ed718c821007e5718c821257e7418c821257e4418c821135ee708c821004ff764c821005bf744c82109dbc744c821026de634c821006dd634c821005f7714c821005fb704c821005f8704c821005ef764c821006ef764c821007af744c821007ac744c821007cf734c821026ee634c821007ce634c821026ce634c821007cd634c821026ec634c821007ce434c821007cd434c821005ef714c821007e7714c821005e7714c821007e4714c82124fe7414c82124fe4414c821007eb704c821135ec704c821007e8704c821005e8704c821024ff760c821004fd760c821026de630c821006dd630c821005ee720c821005f6710c821005f5710c82100cfe74984210acfd749842100cfc7498421024fe7398421004fd7398421006ee3298421006ed32984210acff769042100cfe769042100cfd769042109cfc769042100ebe6490421006bd6490421006de6390421006dd6390421005ee7290421005ed729042109df6719042109fb741904210acff7650421006de6350421006dd635042109df7715042109fb44150421004fd76cc42109dbe74cc421005bd74cc421026de63cc421006dd63cc421005ee72cc421005ed72cc421007cd32cc421005f576cc42113ef576cc42109df674cc42113fb674cc42109db674cc42113fb574cc42113df474cc42113ef763cc42113fd663cc42113ef563cc421007d563cc421006d563cc42113fe672cc421005f572cc42113fe572cc421005e572cc421146f662cc42113fd732cc42113fe632cc421007d532cc42113fe532cc421007c532cc421005f570cc421004ff768c421024fd768c421026de638c421006dd638c421005ee728c421005ed728c42113df6718c421004ff764c421026de634c421006dd634c421007cd324c421024ff760c421004fe760c421004fd760c421024fc760c421026de630c421006dd630c421005ee720c421005ed720c421005f5760c42113ef5760c421004f5760c42109df6740c42113df4740c42113df6730c42113fd6730c42113ef7630c42113fd6630c42113ef5630c421007d5630c42113fe6720c421005f5720c42113fe5720c421005e5720c421146f6620c42113fe6320c42113fe
  | 29 => 0x5dc7358121006bf6418121006bc6418121166ef6218121016fa6018121006f9601812109ebe64d9021005de73d9021005dd73d902108cfe75d9021004fd75d902108cfc75d902109cfd74d9021024fe73d9021006de73d9021024de73d9021004fd73d9021006dd73d9021004dd73d90210b4fe72d9021006ee72d90210acfe71d9021006f671d902109ef741d902109ef441d9021014fe70d9021004fd70d902100cff765902109ebc645902109fb44159021004ff755902108cfe755902108cfc7559021006bf745902109ebe5459021004ff7359021024fc735902109cfc725902109ebc425902109cfc715902109ef4715902109cf4715902109ef7415902109ebc415902109ef4415902109eb44159021004ff7059021014fc705902109ebf4059021004ff7655021004fe7655021004fd7655021004fc765502100ebe6455021006bd645502109f3c5455021005ef7255021005ec7255021005f77155021005f4715502109fb4415502100cfe74d8c21004fd74d8c2100cfc74d8c21004fe72d8c21006ee72d8c21004fe71d8c21006f671d8c21014fe70d8c21004fd70d8c21004fd7698c21006df6398c21004dd7698c21006df6498c21006de6498c21006dd6498c21006dc6498c21007ce7298c2113fd47198c21007d74198c21007d44198c21026df7498c21026de7498c21026dd7498c21026dc7498c21006de5498c21006dd5498c21006dc5498c21026de7298c21026ce7298c21026dc7298c21006df4298c21006dc4298c21026de7198c21026dc7198c21006df4198c21006dc4198c21026df7098c21026de7098c21026dd7098c21026dc7098c21006df4098c21006dc4098c21024ff7658c21004ff7458c2100cfe7458c2100cfc7458c21006df7358c21006df4358c21006dc4358c21006f47158c21004ff7058c21014fc7058c21006df7658c21024df7658c21006df6458c21006de6458c21006dd6458c21006dc6458c21007ce7258c21007d47158c21007d74158c21007d44158c21006df7458c21006de7458c21006dd7458c21006dc7458c21006de5458c21006dd5458c21006dc5458c21006de7258c21006dc7258c21006df4258c21006dc4258c21006de7158c21006dc7158c21006d47158c21006df4158c21006dc4158c21006dc2158c21006df7058c21006de7058c21006dd7058c21006dc7058c21006df4058c21006dc4058c21005de7318c21026de6318c21006dd6318c21024ff7690c21004fe7690c21004fd7690c21024fc7690c21026de6390c21006dd6390c21005ee7290c21005ed7290c21005f67190c21005f57190c21004ff7650c21004fe7650c21004fd7650c21004fc7650c21026de6350c21006dd6350c21005f77150c21005f47150c2109fb44150c2100cfe74988210b4fd749882100cfc749
  | 30 => 0xc5455121024fe76d8d21006bf64d8d21006bc64d8d2100cfe74d8d21004fd74d8d2100cfc74d8d21014fe70d8d21004fd70d8d210a5be7498d21005bd7498d21006bf6498d21006bc6498d21006df6398d21005bf7458d210a5bc7458d21006bf6458d21006bc6458d21005fb7058d21005f87058d21004ff7458d21006bf7458d21004bf7458d2100cfe7458d2100cfc7458d21006bc7458d2100cbc7458d21006df7358d21004ff7258d21006ef7258d21004ff7158d21006f77158d21004f77158d21004ff7058d21006fb7058d21004fb7058d21014fc7058d21006f87058d21014f87058d21004fe7618d21006bf6418d21006bc6418d21026de6318d21006dd6318d21024ff7690d21004fe7690d21004fd7690d21024fc7690d210067f6590d211267c6590d21006bf6490d2100ebc6490d21004ff7650d21004fe7650d21004fd7650d21004fc7650d210067f6550d2111e7c6550d21006bf6450d2100ebc6450d210acfe76909210067f65909211167c6590921006bf649092100ebc649092100cfc76509210057f75509212657c75509210067f655092110e7c6550921006bf645092100ebc6450921005f77150921005f47150921004fe76cc921006bf64cc921106bc64cc921006df63cc921026dc63cc921005f671cc921005f571cc921004fe768c921006bf648c9210febc648c921024fc764c921005bf744c9210a5bc744c921006bf644c9210f6bc644c921006df634c921026dc634c921005f7714c921005f4714c921005fb704c921005f8704c921004fe760c921006bf640c9210eebc640c9210b4fe76905210067f65905210e67c6590521006bf649052100ebc649052100cff76505210a4fd765052100cfc76505210067f65505210de7c6550521006bf645052100ebc6450521005ef7250521005ec72505210a7b44150521004fe76cc5210a5be74cc521005bd74cc521006bf64cc5210d6bc64cc521006df63cc521026dc63cc521005ee72cc521005ed72cc521004fe768c521006bf648c5210cebc648c521024ff764c521004fd764c521024fc764c521006bf644c5210c6bc644c521006df634c521026dc634c521005ef724c521005ec724c521004fe760c521006bf640c5210bebc640c521006bf64c85210b6bc64c8521007b764c85210b6f664c85210b6f464c8521007b464c85210b6b464c8521146f663c8521146f463c8521006bf64885210aebc6488521007af6488521007ac6488521006ef6388521006ed6388521007e76188521006bf64d8121006bc64d812100cfe74d8121004fd74d812100cfc74d8121024fe73d8121004fd73d8121006f721d81210a5be7498121005bd7498121006bf6498121006bc6498121006fb6098121005bf74581210a5bc7458121006bf6458121006bc6458121005df7358121
  | 31 => 0xca21026ef764ca21024ef764ca21007af744ca21007ac744ca21007cf734ca21026ee634ca21007ce634ca21007cd634ca21026ec634ca21007ce434ca21007cd434ca21005ef714ca21007e7714ca21007e4714ca21007eb704ca21165ec704ca21007e8704ca21005e8704ca2100cfd769062100ebe6490621006bd6490621005ee7290621005ed729062109cff76506210afb441506210adbe74cc621005bd74cc621006df63cc621026dc63cc621005ee72cc621005ed72cc621007cd32cc621024fd768c621026de638c621006dd638c621005ee728c621005ed728c621006df634c621026dc634c621007cd324c621026de630c621006dd630c621005ee720c621005ed720c621005ed76c8621006ed76c8621005ef73c8621005ed73c8621007e651c8621007e551c8621165ee70c8621005f576c8621006f576c86210b6f664c86210b6f464c8621146f663c8621146f463c8621007e652c8621007e552c8621006fb6098221005df7358221005dc7358221004ff745822100cfe745822100cfc7458221004ff7358221006df7358221004df7358221024fc7358221006dc7358221024dc7358221006ee3258221006ed3258221006f721582210adbe7418221005bd7418221016fa6018221006f9601822100cfe76d91210a6be64d912108cfe75d9121004fd75d912108cfc75d9121006bf54d91210a6be54d91210a6bc54d9121024fe73d9121004fd73d91210a6bf43d91210a6bc43d91210a4fd72d91210a6bf42d91210a4fd71d91210a6bf41d9121014fe70d9121004fd70d91210a6bf40d91210a6bc40d91210a5be76d912100cbe76d9121006bf65d91210073f65d91210063f65d9121006be65d9121006bc65d9121006bf75d9121006be75d9121006bd75d9121006bc75d9121006bf73d9121006be73d9121006bd73d9121006bc73d9121006bf53d9121006bc53d9121006bf72d91210a6be72d9121006bd72d9121006bf52d9121006bc52d9121006bf71d91210a6be71d9121006bd71d9121006bf51d9121006bc51d9121006bf70d9121006be70d9121006bd70d9121006bc70d9121006bf50d9121006bc50d91210057f75591212657c75591210067f65591210a6bc6459121004ff75591210067f75591210047f755912108cfe755912108cfc75591210067c755912108c7c75591210a4ff7459121006bf7459121004ff7359121024fc73591210acff7259121006ef72591210b4ff7159121006f771591210b4f77159121004ff7059121014fc7059121005be76191210a6be7619121004be7619121006bf65191210073f65191210063f6519121006be6519121006bd6519121006bc65191210073c65191210063c6519121004ff7655121004fe7655121004fd7655121004fc7655121006bf645512100ebc64551210a73
  | 32 => 0x6bf649072100ebc64907210b7b7419072100cff765072100ebe6450721006bd6450721005ef7250721005ec72507210b7b441507210b5be74cc721005bd74cc721026de63cc721006dd63cc721005ee72cc721005ed72cc721005f576cc721146f576cc7210b5f674cc721147b674cc7210b5b674cc721147b574cc721145f474cc721146f763cc721147d663cc721146f563cc721007d563cc721147e672cc721005f572cc721147e572cc721147d732cc721007d532cc721005f570cc721024ff764c721026de634c721006dd634c721005ef724c721005ec724c721005f5760c721146f5760c7210b5f6740c721145f4740c721147d6730c721146f7630c721146f5630c721005f5720c721005f5700c7210b5be74d8321005bd74d8321005de73d8321005dd73d83210b5be7498321005bd7498321006fb6098321004ff745832100cfe745832100cfc7458321004ff7358321024fc7358321016fa6018321006f9601832126d7e75d92210057d75d92210aebe64d922108cfe75d92210067e75d922108c7e75d9221004fd75d92210067d75d92210047d75d922108cfc75d92210aebe54d9221024fe73d9221004fd73d9221006ed72d92210aebc42d9221006f671d9221014fe70d9221004fd70d92210aebc6459221004ff755922108cfe755922108cfc7559221006bf7459221006bf54592210aebc5459221004ff7359221024fc73592210aebc43592210aebf42592210aebc4159221004ff7059221014fc70592210aebf4059221004ff7655221004fe7655221004fd7655221004fc7655221006bf645522100ebc64552210af3c5455221005ef7255221005ec72552210adbe74d8e21005bd74d8e21005fa70d8e21005f970d8e2100cfe74d8e21006be74d8e2100cbe74d8e21004fd74d8e21006bd74d8e21004bd74d8e2100cfc74d8e21006ed72d8e21006f671d8e21014fe70d8e21006fa70d8e21014fa70d8e21004fd70d8e21006f970d8e21004f970d8e21006df6398e21004ff7458e2100cfe7458e2100cfc7458e21006df7358e21004ff7058e21014fc7058e21026de6318e21006dd6318e21024ff7690e21004fe7690e21004fd7690e21024fc7690e2100ebe6490e21006bd6490e21005ee7290e21005ed7290e21004ff7650e21004fe7650e21004fd7650e21004fc7650e210a4fd7690a21006bf6490a2100ebc6490a2100cff7650a210057f7550a2126d7c7550a2100ebe6450a21006bd6450a21005f77150a21005f47150a21026de63cca21006dd63cca21005f671cca21005f571cca21005ed768ca21006ed768ca21026ee638ca21026ec638ca21005ed718ca21165ee708ca21024ff764ca21005bf744ca210adbc744ca21026de634ca21006dd634ca21005f7714ca21005f4714ca21005fb704ca21005f8704
  | 33 => 0xc7458831026ef7258831026ef3258831026ec3258831006f47158831026df3158831004ff7058831014fc7058831026dc3058831004ff7690831024fe7690831004fd76908311eebf649083100ebc6490831004ff7650831004fd7650831024fc76508310057f755083127d7c7550831005f77150831005f4715083100cfe74984310ccfd749843100cfc7498431026df3198431026f73198431026f431984310ccff7690431024fe769043100cfd7690431024fc769043100ebe6490431006bd6490431025de7390431005dd73904310ccff76504310bfb44150431025df764c431006df764c431004df764c431006dd624c431025df714c431027d7714c431006de614c431027d6614c431007d6514c431007d5514c43116ddc704c431004ff745803100cfe745803100cfc7458031004ff7258031004fc7258031026f63158031026f53158031026fb7058031026fb3058031026dc3058031026f830580310b6be64d93210b7b441d932108cfe75d9321004fd75d932108cfc75d9321024fe73d9321004fd73d9321006ee72d9321006f571d93210b6f741d93210b6bc41d93210b6f441d93210b6b441d9321014fe70d9321004fd70d93210b6bf40d93210b6bc64593210b7b74159321004ff755932108cfe755932108cfc7559321006bf74593210b6be5459321004ff7359321024fc73593210b6bf43593210b6bc42593210b6f771593210b6bf41593210b6f741593210b6f44159321004ff7059321014fc70593210b6bc4059321004ff7655321004fe7655321004fd7655321004fc765532100ebe6455321006bd64553210b73c5455321005f77155321005f471553210b7b4415532100cfe74d8f21004fd74d8f2100cfc74d8f21006ee72d8f21006f571d8f21014fe70d8f21004fd70d8f21006df6398f21004ff7458f2100cfe7458f2100cfc7458f21006df7358f21006f77158f21004ff7058f21014fc7058f210b5be7418f21005bd7418f21026de6318f21006dd6318f21024ff7690f21004fe7690f21004fd7690f21024fc7690f21026de6390f21006dd6390f21005f67190f21005f57190f21004ff7650f21004fe7650f21004fd7650f21004fc7650f2100ebe6450f21006bd6450f21026de6350f21006dd6350f21005f77150f21005f47150f210b7b44150f2100cfd7690b2100ebe6490b21006bd6490b21005f67190b21005f57190b210b7b44190b2109cff7650b210057f7550b212757c7550b210b5f77150b21005f47150b21006df63ccb21026dc63ccb21024fd768cb21026de638cb21006dd638cb21005f6718cb21005f5718cb21005bf744cb210b5bc744cb21006df634cb21026dc634cb21005f4714cb21005fb704cb21005f8704cb21026de630cb21006dd630cb21005f6710cb21005f5710cb210a4fd7690721
  | 34 => 0x9131014fe70d9131004fd70d91310c6bc40d91310c6bc6459131004ff755913108cfe755913108cfc75591310c4ff7459131006bf74591310ccff7359131006df7359131004ff7259131004fc72591310d4ff7159131006f771591310c6bc4159131004ff7059131014fc70591310c6bf4059131004ff7655131004fe7655131004fd7655131004fc7655131006bf645513100ebc64551310c73c5455131005f77155131005f4715513100cfc7650d31006bf6450d3100ebc6450d31005f77150d31005f47150d3100cfe74d8931004fd74d893100cfc74d8931014fe70d8931004fd70d8931006ef6298931005bf74589310c5bc7458931005fb7058931005f87058931006ed621893100cfe7418931004fd741893100cfc741893113ef7311893113ef43118931014fe7018931004fd7018931004fe7690931004fd7690931004fc7690931006bf649093100ebc6490931025de7390931005dd7390931004ff7650931004fe7650931004fc76509310057f75509312857c7550931005f77150931005f47150931005de76cc931026de76cc931006df64cc931006dd64cc931006dc62cc931005de71cc931026df61cc931027d761cc931186dc60cc931005dd738c931006ef628c931006ec628c931005f6718c931005f5718c931005bf744c9310c5bc744c931006ef624c931006ec624c931005f7714c931005f4714c931005fb704c931005f8704c9310079f744c9310079c744c931006df644c931006dd644c931025df724c931027cf724c931007cf624c931006dc624c931007cc624c931007d7714c931005dc714c931007d4714c931026df614c931027d7614c931007db704c931007d8704c93117edc604c9310d4fe769053100ebe6490531006bd649053100cff76505310c4fd7650531024fc7650531006bf645053100ebc6450531005df7350531025dc73505310c7b44150531025f6718c531005dd728c531025de718c531027d7618c53100cfe74d8131004fd74d813100cfc74d8131004fe72d8131004fd72d8131006fb6098131005bf74581310c5bc7458131005ef7258131005ec72581310c5be7418131005bd741813114edf6318131016fa6018131006f96018131004ff755903108cfe755903108cfc7559031026bf7459031024fe7359031024fc7359031026be4359031026bc4359031004ff7259031004fc72590310bcfc71590310bebc4159031004ff7059031014fc70590310bebf4059031004ff7655031024fe7655031004fd7655031024fc76550311f6bf645503100ebc64550310bf3c545503100cfe7498831004fd749883100cfc7498831026ee7298831026ef3298831026ec3298831014fe7098831004fd7098831004ff7458831006bf7458831004bf745883100cfe745883100cfc7458831006bc745883100cb
  | 35 => 0x6df764cb310079f744cb310079c744cb31026df644cb310279e644cb31006dd644cb310279d644cb310069d644cb31027cf724cb31006de624cb31027ce624cb31006ce624cb31027cd624cb31007d7714cb31005dc714cb31007d4714cb31005d4714cb31007db704cb31007d8704cb3117ede604cb310c4fd76907310e67e65907310067d659073100ebe6490731006bd6490731006ee6290731006ed629073100cff7650731024fc76507310de7e65507310067d655073100ebe6450731006bd6450731005df7350731025dc7350731006ee6250731006ed62507310d7b44150731004ff745833100cfe745833100cfc7458331004ff7258331004fc7258331026f63158331026f53158331026fb7058331026fb3058331026f830583310cebe64d923108cfe75d9231004fd75d923108cfc75d9231006dd73d9231004fe72d9231004fd72d9231006f671d9231014fe70d9231004fd70d92310cebc6459231004ff755923108cfe755923108cfc7559231006bf74592310cebe54592310cebf4359231004ff7259231004fc72592310cebc4259231024fc71592310cebc4159231004ff7059231014fc70592310cebf4059231004ff7655231004fe7655231004fd7655231004fc765523100ebe6455231006bd64552310cf3c5455231005f77155231005f47155231026f73158e3100cff7650e3100ebe6450e31006bd6450e31005f77150e31005f47150e310cdbe74d8a31005bd74d8a31005fa70d8a31005f970d8a31006ef6298a3100cfe7498a31004fd7498a3100cfc7498a31146f73198a31146f43198a31014fe7098a31004fd7098a31004ff7458a3100cfe7458a3100cfc7458a31004ff7058a31014fc7058a31006ed6218a31004ff7690a31004fe7690a31004fd7690a3100ebe6490a31006bd6490a31004ff7650a31004fd7650a31004fc7650a310057f7550a3128d7c7550a31005f77150a31005f47150a31006ee628ca31006ed628ca31005f6718ca31005f5718ca31005bf744ca310cdbc744ca31006ee624ca31006ed624ca31005f7714ca31005f4714ca31005fb704ca31005f8704ca31024fd769063100ebe6490631006bd6490631025de7390631005dd73906310bcff76506310cfb44150631005dd76cc631026dd76cc6310279e74cc6310279d74cc631027ce72cc631027cd72cc631006dd62cc631027d661cc631007d651cc631007d551cc63114dde70cc631006fb6098231004ff745823100cfe745823100cfc7458231004ff7258231004fc72582310cdbe7418231005bd7418231016fa6018231006f9601823100cfe76d91310c6be64d913108cfe75d9131004fd75d913108cfc75d91310c6be54d91310c4fd73d91310c6bf43d9131004fe72d9131004fd72d91310c6bc42d9131024fd71d91310c6bf41d
  | 36 => 0xf7259331004fc72593310d6bf42593310d6bc4259331026df32593310d6bf4159331004ff7059331014fc70593310d6bf40593310d6bc4059331006bf7559331006be7559331006bd7559331006bc7559331026bf7359331026be7359331026bd7359331026bc7359331026bf5359331026be5359331026bd5359331026bc5359331006bf7259331006be7259331006bd7259331006bc7259331006bf5259331006bc5259331026bf32593310269f3259331026be3259331026bd3259331026bc3259331006bf7159331006bd71593310d6bc7159331006bf5159331006bc5159331026bf3159331026be3159331026bd3159331026bc3159331006bf7059331006be7059331006bd7059331006bc7059331006bf5059331006bc5059331026bf3059331026be3059331026bd3059331026bc3059331004ff7655331024fe7655331004fd7655331024fc765533100ebe6455331006bd64553310d73c545533100cfe7498b31004fd7498b3100cfc7498b31026ee7298b31006ef4298b31006ec4298b31026df3298b31026ef3298b31026ec3298b31014fe7098b31004fd7098b31006ef7498b31006ee7498b31006ed7498b31006ec7498b31006ee5498b31006ed5498b31006ec5498b31026ee7398b31026ed7398b31026ec7398b31026ef4398b31026ee4398b31026ed4398b31026ec4398b31006ef7198b31006ed7198b31006ef4198b31006ec4198b31026ef3198b31026ee3198b31026ed3198b31026ec3198b31006ef7098b31006ee7098b31006ed7098b31006ec7098b31006ef4098b31006ec4098b31026ef3098b31026ee3098b31026ed3098b31026ec3098b31004ff7458b3100cfe7458b3100cfc7458b31026ef7258b31006ef4258b31006ec4258b31026ef3258b31026ec3258b31006f77158b31004ff7058b31014fc7058b31006ef7458b31006ee7458b31006ed7458b31006ec7458b31006ee5458b31006ed5458b31006ec5458b31026ef7358b31026ee7358b31026ec7358b31026ef4358b31026ee4358b31026ed4358b31026ec4358b31006ef7158b31006e77158b31006ed7158b31006ef4158b31006ec4158b31026ef3158b31026ee3158b31026ed3158b31026ec3158b31006ef7058b31006ee7058b31006ed7058b31006ec7058b31006ef4058b31006ec4058b31026ef3058b31026ee3058b31026ed3058b31026ec3058b31004ff7690b31024fe7690b31004fd7690b311167e6590b310067d6590b3100ebe6490b31006bd6490b31025de7390b31005dd7390b31006ee6290b31006ed6290b31004ff7650b31004fd7650b31024fc7650b310057f7550b312957c7550b3110e7e6550b310067d6550b3100ebe6450b31006bd6450b31006ee6250b31006ed6250b31005f77150b31005f47150b31025df764cb31
  | 37 => 0x8d410cedd43d8d41004fe72d8d41004fd72d8d410cebc41d8d41014fe70d8d41004fd70d8d410cebf40d8d410dd7e7598d410057d7598d41006df6398d41005ee7298d41005ed7298d410c5f57198d410d7b44198d410d5f77158d410c7b44158d41026de6318d41006dd6318d410bfb44118d41004fe7694d41004fd7694d41024fc7694d410df5f5394d412c7b44194d41004ff7654d41004fe7654d41004fc7654d410067f6554d4108e7c6554d412bfb44154d410afb441d894108cfe75d8941004fd75d894108cfc75d8941024fe73d8941004fd73d8941006ef52d8941006ec52d89410aeee42d89410aeed42d8941014fe70d8941004fd70d8941006ef62989410a5f571989410b7b441989410057f75589410dd7c75589410b5f771589410a7b44158941005de7318941005dd7318941006ed621894109fb4411894108cfe7518941004fd751894108cfc7518941024fe7318941006de7318941024de7318941004fd7318941006dd7318941004dd7318941006ef5218941006ec521894109eee421894109eed421894109ef7411894109ebc411894109ef4411894109eb44118941014fe7018941004fd701894109ebf4018941004fe7694941004fd7694941004fc76949410067f659494108e7c6594941227b44194941004ff7654941004fe7654941004fc7654941005bf745494100dbc7454941005f77154941005f471549412b7b44154941004fe76cc941004fd76cc941024fc76cc941026de63cc941107b441cc941004fe768c941004fd768c941004fc768c941006ef628c941006ec628c9410ffb4418c941004ff764c941004fe764c941004fc764c9410057f754c9410dd7c754c941005bf744c94100dbc744c941006ef624c941006ec624c941005f7714c941005f4714c9410f7b4414c941005fb704c941005f8704c941004fe760c941004fd760c941024fc760c9410efb4410c9412acfe769454108e7e65945410df7751945412a7b4419454100cfe765454129cfd765454100cfc7654541005bf745454100dbc745454129fb44154541006bf6590541006bd6590541006bf6390541006bc629054100dbe719054100fb6719054100db6719054100ebf619054100fb76190541005bd709054103fb441d814108cfe75d8141004fd75d814108cfc75d8141024fe73d8141004fd73d8141004fe72d8141004fd72d814103efa40d8141037b44198141006fb60981410057f75581410dd7c7558141005df7358141005dc7358141005ef7258141005ec725814102fb441581410dd7e75181410057d7518141156bf641814101fb44118141016fa6018141006f96018141004ff755933108cfe755933108cfc7559331026bf7459331006bf54593310d6be54593310d6bc5459331024fc7359331026be4359331026bc4359331004f
  | 38 => 0x155bc7050e410e57e75d8a410057d75d8a4109df671d8a41006ef6298a4108cfe7598a41004fd7598a4108cfc7598a41024fe7398a41004fd7398a410b6ee4298a410b6ed4298a410b6f74198a410b6f44198a41014fe7098a41004fd7098a41004ff7558a4108cfe7558a4108cfc7558a410a6be5458a41006bd5458a41004ff7358a41024fc7358a410a6ee4258a410a6ed4258a410a6bc4258a41004ff7058a41014fc7058a41005de7318a41005dd7318a41006ed6218a410adf67118a41004ff7694a41004fe7694a41004fd7694a4108e7e6594a410067d6594a4100dbc7494a412273e5494a41004ff7654a41004fd7654a41004fc7654a41005bf7454a4100dbc7454a410073d5454a41005f77154a41005f47154a41005bf7590a41005bd7590a41116be6590a41116bc6590a41005bd7390a411eebe6390a4100dbe7290a4100fae7290a41007ae6290a41006bd6290a41007ad6290a41007b67190a41005bd7190a41007b57190a4100ebe6190a4100fb66190a41155be7090a41024ff76cca41004fe76cca41004fd76cca4100dbe74cca41005bd74cca41026de63cca41006dd63cca410079d43cca41004ff768ca41004fe768ca41004fd768ca41005bf748ca4100dbc748ca41004ff764ca41004fd764ca41004fc764ca410057f754ca410e57c754ca41005bf744ca4100dbc744ca41026de634ca41006dd634ca410079d434ca41005f7714ca41005f4714ca41005fb704ca41005f8704ca41024ff760ca41004fe760ca41004fd760ca4100dbe740ca41005bd740ca4108cfe769464100cfd769464100dbe7494641005bd74946410073d54946412a7b74194641005de73d8241005dd73d8241006fb6098241004ff755824108cfe755824108cfc755824102ebe5458241006bd5458241004ff7358241024fc735824102ebf4358241006bd4358241004ff7258241004fc7258241006be425824102ebc425824102ebf415824102efa4058241156bc40582410e57e75182410057d7518241016fa6018241006f9601824108cfe76d95410de7e65d95412a7b441d95412a4ff74d95412a4fd74d95412a67f54d95412a67d54d9541024fe73d9541004fd73d95410de7f53d9541004fe72d9541004fd72d95410de7c52d954100cfd71d95410de7f51d95412a6bc41d9541014fe70d9541004fd70d95410de7c50d95412a6bf40d95410de7c6559541005ef7259541005ec72595412cdf7715954129fb4415954129cff7459541006bf7459541004ff7359541024fc7359541004ff7259541006ef7259541004ef7259541004fc7259541006ec7259541004ec72595412ccff7159541006f7715954129ebc4159541004ff7059541014fc705954129ebf40595410cfb441d8d4108cfe75d8d41004fd75d8d4108cfc75d8d410cede43d
  | 39 => 0xc72590320eebc4259032026df3259032004ff7159032004fc71590320eebc4159032004ff7059032014fc70590320eebf4059032004ff7655032024fe7655032004fd7655032024fc765503200ebe6455032006bd64550320ef3c545503200cfe74988320fcfd749883200cfc7498832026df3298832026ef3298832026ec32988320fcff7690832024fe769083200cfd7690832024fc769083200ebe6490832006bd6490832025de7390832005dd73908320fcff76508320057f75508322d57c7550832005f77150832005f47150832025df764c832006df764c832004df764c8320079f744c8320079c744c832026df644c832006dd644c832025df724c832027cf724c832006de624c832027ce624c832007ce524c832007cd524c832007d7714c832007d4714c832007db704c832007d8704c83217ede604c83200cfe7498432004fd749843200cfc7498432026ee3298432026ed3298432026f67198432026f73198432026f43198432014fe7098432004fd7098432004ff745843200cfe745843200cfc7458432026df3258432006dd3258432026f77158432026f73158432026f43158432004ff7058432014fc7058432004ff745803200cfe745803200cfc7458032026ee3258032026ed3258032004ff7158032004fc7158032026fb7058032026fb3058032026f830580320e67e65d96412adf671d9641024fe73d9641004fd73d9641004fe72d9641004fd72d96412acfe71d9641006f671d9641014fe70d9641004fd70d964108cff76596410e67c65596410067f755964129e7f545964129e7d5459641004ff7359641024fc7359641004ff7259641004fc72596410e67c525964100cfc71596410e67c5159641004ff7059641014fc70596410e67f50596410e5bf765524108ebf765524108cbf765524100dbf755524100f3f755524108ebe65552410e73e655524108e3e65552410073d655524108ebc6555241005bf73552411f6be63552410e73c5355241005bc72552410e73f5255241005bf7155241007b77155241007b4715524100ebe615524100fb661552410e73c5155241155bc70552410e73f50552410bdf671d8e41006df6398e41004ff7558e4108cfe7558e4108cfc7558e410c6de4358e410c6dd4358e41004ff7258e41004fc7258e41004ff7058e41014fc7058e41026de6318e41006dd6318e410cdf67118e41024ff7694e41004fe7694e41004fd7694e4100dbe7494e41005bd7494e410073d5494e410e75f5394e41004ff7654e41004fd7654e41004fc7654e4100dbe7454e41024bf7650e41005bf7550e41005bd7550e4100dbf7350e4100f9f7350e41026be6350e410079e6350e410079d6350e41026bc6350e41005bc7250e41005bf7150e41007b77150e41007b47150e4100ebe6150e4100fb66150e41
  | 40 => 0x8532006f5431853213ef4431853213ef77218532006f74218532006f64218532006f54218532006f4421853213ef73218532006f63218532006f5321853213ef43218532006f77018532006f67018532006f57018532006f47018532006f74018532006f4401853213ef7301853213ef43018532006bf64d8132006bc64d8132006f761d8132006f461d813200cfe74d8132004fd74d813200cfc74d8132004fe71d8132004fd71d8132006fb40d8132006f840d8132006fb64d8132007bb64d8132006bb64d8132006fa64d8132006f964d8132006f864d8132007b864d8132006b864d8132007d973d8132007da43d8132007d943d81321a7eb72d81321a7eb32d8132007da32d81321a7e832d8132006fb61d8132007f361d8132006f361d8132006fa61d8132006f961d8132006f861d8132007f061d8132006f061d8132006fb74d8132006fa74d8132006f974d8132006f874d8132006fa54d8132006f954d8132006f854d8132006fb73d81321a6fa73d8132006fb43d81321a6fa43d8132006f943d81321a6f843d81321a6fb72d8132006fb42d8132006fa42d8132006f942d8132006f842d81321a6fb32d8132006fa32d81321a6f832d8132006fb71d8132006fa71d8132006f971d8132006f871d8132006fb41d8132006f841d81321a6fb31d81321a6f831d81320f5be7498132005bd7498132006bf6498132006bc6498132005f67198132005f57198132006f76198132006f46198132006fb6098132005bf74581320f5bc7458132006bf6458132006bc6458132005f77158132005f47158132006f76158132006f46158132006bf6418132006bc6418132006f76118132006f46118132016fa6018132006f96018132005fa7618132006fa7618132006fb6418132007bb6418132006bb6418132006fa6418132006f96418132006f86418132007b86418132006b8641813217fdb7318132007da4318132007d94318132007e9721813219feb3218132007da321813219fe83218132006fb6118132007f36118132006f36118132006fa6118132006f96118132006f86118132007f06118132006f06118132016fb7418132016fa7418132016f97418132016f87418132006fa5418132006f95418132006f85418132016fb7318132016fa7318132016f87318132006fb431813219efa4318132006f9431813219ef84318132016fb7218132006fb4218132006fa4218132006f94218132006f8421813219efb3218132006fa3218132006f9321813219ef83218132016fb7118132016fa7118132016f97118132016f87118132006fb4118132006f8411813219efb311813219ef83118132004ff755903208cfe755903208cfc7559032026bf74590320eebe5459032024fe7359032024fc7359032026be4359032026bc43590320ecf
  | 41 => 0x79d5490d32005de7290d32026df6290d32027cf6290d320f79c4290d32005dd7190d3217dde7090d3200cfc7650d320067f6550d3211e7c6550d32006bf6450d3200ebc6450d32005ef7250d32005ec7250d320f5dc7650d3200edc7650d3200cdc7650d32005df7550d32005dd7550d320075f6550d320075c6550d32025df7450d320279f7450d320079f6450d3200ede6450d3200edc6450d320f79c6450d32007cf7250d32005dc7250d32007cc7250d32026df6250d32027cf6250d32005df7150d320f79c4150d3217ddc7050d320f79f4050d32104fe76909320067f65909321167c6590932006bf649093200ebc64909320079e439093200cff76509320f4fd7650932024fc76509320057f75509322dd7c75509320067f655093210e7c6550932006bf645093200ebc6450932005df7350932025dc73509320f7ac4250932005f77150932005f47150932006bf648c9320febc648c932025ee728c932005df748c932005dd748c9320079f648c9320079c648c932025de728c932027cf628c932005dd718c93217dde708c932006bf64d8532006bc64d853200cfe74d8532004fd74d853200cfc74d8532006f741d8532006f441d8532014fe70d8532004fd70d8532006f764d8532007b764d8532006b764d8532006f664d8532006f564d8532006f464d8532007b464d8532006b464d8532007d773d8532007d643d8532007d543d8532007e572d8532147e732d8532007d632d8532147e432d8532006f774d8532006f674d8532006f574d8532006f474d8532006f654d8532006f554d8532006f454d8532006f773d8532146f673d8532006f743d8532146f643d8532006f543d8532146f443d8532146f772d8532006f742d8532006f642d8532006f542d8532006f442d8532146f732d8532006f632d8532146f432d8532006f770d8532006f670d8532006f570d8532006f470d8532006f740d8532006f440d8532146f730d8532146f430d85320f5be7498532005bd7498532006bf6498532006bc6498532006f76198532005fa7098532005f97098532005bf74585320f5bc7458532006bf6458532006bc6458532005fb7058532005f87058532006bf6418532006bc6418532006f5611853200cfe7418532004fd741853200cfc7418532006f74118532006f44118532014fe7018532004fd7018532005f67618532006f67618532006f76418532007b76418532006b76418532006f66418532006f56418532006f46418532007b46418532006b46418532007d57318532007d64318532007d5431853213fe7721853213fe73218532007d6321853213fe43218532006f77418532006f67418532006f57418532006f47418532006f65418532006f55418532006f45418532006f7731853213ef67318532006f7431853213ef6431
  | 42 => 0xf64cca32006dd64cca32027ce62cca32007ce52cca32007cd52cca32186de60cca32006f7619863200cfe7498632004fd749863200cfc7498632014fe7098632004fd7098632005bf74586320fdbc7458632004ff7458632006bf7458632004bf745863200cfe745863200cfc7458632006bc745863200cbc7458632006df3258632004ff7058632014fc7058632006f561186320fdbe7498232005bd7498232005f67198232005f57198232006fb6098232004ff745823200cfe745823200cfc7458232004ff7158232004fc7158232016fa6018232006f9601823200cfe76d91320f6be64d913208cfe75d9132004fd75d913208cfc75d9132006bf54d91320f6be54d91320f6bc54d91320f4fd73d91320f6bf43d9132024fd72d91320f6bf42d9132004fe71d9132004fd71d91320f6bf41d91320f6bc41d9132014fe70d9132004fd70d91320f6bf40d91320f6bc40d91320f5be76d913200cbe76d9132006bf65d91320073f65d91320063f65d9132006be65d9132006bc65d91320079f73d91321efaf32d91321efac32d9132006bf75d9132006be75d9132006bd75d9132006bc75d9132006bf73d91321eebe73d9132006bd73d91321eebc73d9132006bf53d91321eebe53d91321eebc53d91321eebf72d91320f6be72d9132006bd72d9132006bf52d9132006bc52d91321eebf32d91321eebc32d9132006bf71d9132006be71d9132006bd71d9132006bc71d9132006bf51d9132006bc51d91321eebf31d91321eebc31d9132006bf70d9132006be70d9132006bd70d9132006bc70d9132006bf50d9132006bc50d91321eebf30d91321eebc30d91320057f75591322dd7c75591320067f65591320f6bc6459132005f77159132005f47159132005fb7059132005f87059132004ff75591320067f75591320047f755913208cfe755913208cfc75591320067c755913208c7c75591320f4ff7459132006bf74591320fcff7359132006df7359132104ff7259132006ef7259132004ff7159132006f77159132004f77159132004fc7159132006f47159132004f47159132004ff7059132006fb7059132004fb7059132014fc7059132006f87059132014f87059132005be76191320f6be7619132004be7619132006bf65191320073f65191320063f6519132006be6519132006bd6519132006bc65191320073c65191320063c65191320f79d73191322e6bf62191322e7af32191322e7ac3219132004ff7655132004fe7655132004fd7655132004fc7655132006bf645513200ebc64551320f73c5455132005ef7255132005ec7255132005de7690d32026de7690d32025df7590d32005dd7590d320075f6590d320075c6590d320f5dd7490d320079f6490d3200ede6490d3200edc6490d320f79c6490d3200e9c6490d320f79e5490d32
  | 43 => 0x8142004fd71d814205efa40d814210d7e75981420057d75981420067f65981420067c6598142005f67198142005f57198142006f76198142006f46198142006fb60981420057f755814210d7c75581420067f65581420067c6558142005df7358142005dc7358142005f77158142005f47158142006f76158142006f461581420067f65181420067c6518142006f76118142006f46118142016fa6018142006f96018142004ff755933208cfe755933208cfc7559332026bf7459332006bf5459332106bc5459332024fc7359332026be4359332026bc4359332106bf4259332004ff7159332004fc7159332106bc4159332004ff7059332014fc7059332106bf4059332004ff7655332024fe7655332004fd7655332024fc76553321f6bf645533200ebc64553321073c5455332025de73553321f79e4355332025df7650f320eedf7650f32005df7550f32005dd7550f320279f7450f3200ede6450f32026dc6450f32005dc7250f32005df7150f321079c4150f32185dc7050f321079f4050f320f4fd7690b321eebf6490b3200ebc6490b32025dc7390b321ef9e4390b3200cff7650b32024fc7650b320057f7550b322f57c7550b3200ebe6450b32006bd6450b32005df7350b32025dc7350b32005f77150b32005f47150b3200cfe7498732004fd749873200cfc7498732026ee3298732026ed3298732026f67198732006f74198732006f44198732026df3198732026f73198732026f43198732014fe7098732004fd7098732026dc3098732004ff745873200cfe745873200cfc7458732026f77158732006f74158732006f44158732026f73158732026f43158732004ff7058732014fc7058732004ff745833200cfe745833200cfc7458332026ee3258332026ed3258332004ff7158332004fc7158332026fb7058332026fb3058332026dc3058332026f83058332026d830583320febe64d923208cfe75d9232004fd75d923208cfc75d9232006dd73d92321eebe43d92321eebc43d9232006ee72d9232004fe71d9232004fd71d92320febc41d9232014fe70d9232004fd70d92320febf40d92320febc6459232004ff755923208cfe755923208cfc7559232006bf74592320febe54592320febf4359232024fc72592320febc4259232004ff7159232004fc7159232004ff7059232014fc7059232004ff7655232004fe7655232004fd7655232004fc765523200ebe6455232006bd64552320ff3c5455232005ef7255232005ec7255232026ef3258e3200cff7650e3200ebe6450e32006bd6450e32005ef7250e32005ec7250e32024fd7690a3200ebe6490a32006bd6490a32025de7390a32005dd7390a320ecff7650a320057f7550a322ed7c7550a320ffac4250a32005f77150a32005f47150a32005dd76cca32026dd76cca32006d
  | 44 => 0x6f451d85420b6f641d8542014fe70d8542004fd70d8542006f765d85420077765d85420067765d8542006f665d8542006f565d8542006f465d85420077465d85420067465d85420b7b654d8542007b554d8542006f763d8542006f663d8542006f563d8542006f463d85420b7e742d8542007b642d85420b7b442d85420b7e442d8542006f775d8542006f675d8542006f575d8542006f475d85420b6f774d85420b6f674d85420b6f474d85420b6f754d85420b6f654d85420b6f554d85420b6f454d8542006f773d8542006f673d8542006f573d8542006f473d8542006f753d8542006f653d8542006f553d8542006f453d85420b6f743d85420b6f643d85420b6f543d85420b6f443d85420b6f772d85420b6f572d8542006f752d8542006f652d8542006f552d8542006f452d85420b6f742d85420b6f642d85420b6f442d8542006f770d8542006f670d8542006f570d8542006f470d8542006f750d8542006f450d85420b6f740d85420b6f640d85420b6f540d85420b6f440d854210d7e75985420057d75985420067f65985420067c6598542006f761985420057f755854210d7c75585420067f65585420067c65585420067f65185420067c6518542006f5611854208cfe7518542004fd751854208cfc751854209ebe5418542006bd5418542024fe7318542004fd7318542006be421854209ebc4218542006f75118542006f4511854209ef54118542014fe7018542004fd70185420b5f67618542006f67618542006f76518542007776518542006776518542006f66518542006f56518542006f4651854200774651854200674651854209fb65418542007b55418542006f76318542006f66318542006f56318542006f4631854209fe74218542007b6421854209fb4421854209fe44218542006f77518542006f67518542006f57518542006f4751854209ef7741854209ef6741854209ef4741854209ef7541854209ef6541854209eb6541854209ef55418542006b5541854209ef45418542006f77318542006f67318542006f57318542006f47318542006f75318542006f65318542006f55318542006f4531854209ef7431854209ef6431854209ef5431854209ef4431854209ef7721854209ef57218542006f75218542006f65218542006f55218542006f4521854209ef7421854209ef64218542006b6421854209ef5421854209ef4421854209eb44218542006f77018542006f67018542006f57018542006f47018542006f75018542006f4501854209ef7401854209ef6401854209ef5401854209ef440185420067f65d81420067c65d8142006f761d8142006f461d814208cfe75d8142004fd75d814208cfc75d814205ebe54d8142006bd54d8142024fe73d8142004fd73d8142006be42d814205ebc42d8142004fe71d
  | 45 => 0xf51d954210e7c51d9542014fe70d9542004fd70d954210e7f50d954210e7c50d95422fd7e76d954208c7e76d95420073f74d95422273c74d95422276f42d95422273c42d95422276c42d95422267f74d95422267e74d95422267d74d95422267c74d95420067f73d95420067e73d95420067d73d95420067c73d95422267f43d95422267e43d95422267d43d95422267c43d95422267f72d954210e7e72d95422267d72d95422267f42d95422267e42d95422267c42d95420067f71d95420067e71d95420067d71d95420067c71d95422267f41d95422267e41d95422267d41d95422267c41d95420067f70d95420067e70d95420067d70d95420067c70d95422267f40d95422267e40d95422267d40d95422267c40d954210e7c6559542305ef7259542005f77159542005f471595422b4ff7459542006bf7459542004ff7359542024fc7359542304ff7259542006ef7259542004ff7159542006f77159542004f77159542004fc7159542006f47159542004f47159542004ff7059542014fc70595422257e761954210e7e76195422247e76195422ff3e741954210f3d74195422fe7f64195422fe7f62195422ff6f42195422ff3c42195422ff6c421954210dbc765514208ebc765514208cbc765514200dbf755514200f3f75551420073f655514208ebe655514208ebc655514210f3c655514208e3c65551421f6bc635514210f3c5355142007af7255142005bc7255142007ac725514200ebf625514200faf625514210f3f525514210f3c515514210f3f50551420067f65d8d420067c65d8d4208cfe75d8d42004fd75d8d4208cfc75d8d420fede43d8d420fedd43d8d42004fe71d8d42004fd71d8d42014fe70d8d42004fd70d8d4210d7e7598d420057d7598d420067f6598d420067c6598d42006df6398d420f5ed7298d42005f67198d42005f57198d420057f7558d4210d7c7558d420067f6558d420067c6558d42105ef7258d42005f77158d42005f47158d42005fb7058d42005f87058d420067f6518d420067c6518d42026de6318d42006dd6318d42004fe7694d42004fd7694d42024fc7694d420067f6594d4208e7c6594d420073d5494d4210f5f5394d42004ff7654d42004fe7654d42004fc7654d420067f6554d4208e7c6554d422fcfe76949422267f659494208e7c659494200dbc74949422273e549494210f6f529494200cfe76549422b4fd765494200cfc7654942005bf745494200dbc74549420073d5454942005bf7590942005bd75909420073f6590942116be6590942116bc65909420073c65909421163c65909421eebc639094200dbe729094200fae729094200ebf629094200faf62909420067f65d85420067c65d854208cfe75d8542004fd75d854208cfc75d8542024fe73d8542004fd73d8542006f751d8542
  | 46 => 0x814311d7e75181430057d751814320edf6318143005f67118143005f57118143016fa6018143006f960181431167e65d96422273c54d96422fdee72d96422267e54d9642226bc54d96422263c54d9642024fe73d9642004fd73d9642226bc43d96422fcfe72d9642006ee72d9642226bf42d9642004fe71d9642004fd71d9642226bc41d9642014fe70d9642004fd70d9642226bf40d964208cff76596421167c655964200dbc74596421173f54596420067f75596422b67f5459642116bf54596421163f54596422b67d54596422b6bc5459642004ff7359642024fc73596422b6bc435964200cfc72596421167c52596422b6bf4259642004ff7159642004fc71596422b6bc4159642004ff7059642014fc70596422b6bf40596420edee72d8e42006df6398e420057f7558e421157c7558e42004ff7558e420067f7558e420047f7558e4208cfe7558e4208cfc7558e420067c7558e4208c7c7558e420f6de4358e420f6dd4358e421eebc4358e42004ff7158e42004fc7158e420f6bc4158e42004ff7058e42014fc7058e420f6bf4058e42026de6318e42006dd6318e420fdee7218e42024ff7694e42004fe7694e42004fd7694e4208e7c6594e4200dbe7494e42005bd7494e421173f5494e42026de6394e42006dd6394e421175f5394e42004ff7654e42004fd7654e42004fc7654e42005bf7454e4200dbc7454e42026de6354e42006dd6354e42115be7590e421edbc7590e42006bf6590e42006bd6590e4200dbe7390e4200f9e7390e421ef9e6390e421eebd6390e420079d6390e421efae7290e42005bd7290e421efad7290e4200ebe6290e4200fae6290e42005be7190e42005bd7090e4208cfe7694a4200cfd7694a4200dbe7494a42005bd7494a422273c5494a42227af4294a420b7b441d8642006f7619864208cfe7598642004fd759864208cfc7598642024fe7398642004fd73986420aef54198642014fe7098642004fd70986420057f75586421157c7558642004ff75586420067f75586420047f755864208cfe755864208cfc75586420067c755864208c7c7558642004ff7358642024fc73586420a6f641586420a6bc4158642004ff7058642014fc70586420a6bf4058642005de7318642005dd7318642006f5611864209fb44118642005de73d8242005dd73d82421157e75982420057d7598242005f67198242005f57198242006fb6098242004ff755824208cfe755824208cfc7558242004ff7358242024fc7358242004ff7158242004fc715824204efa4058242016fa6018242006f9601824208cfe76d954210e7e65d9542224ff74d9542224fd74d95422267f54d95422267d54d9542024fe73d9542004fd73d954210e7f53d954210e7c53d954200cfd72d954210e7f52d9542004fe71d9542004fd71d954210e7
  | 47 => 0x6ec5258a430f6ee4258a430f6bc4258a43026ef3258a43026ec3258a43004ff7158a43004fc7158a43004ff7058a43014fc7058a4308cfe7598643004fd759864308cfc75986430cebe5498643006bd5498643024fe7398643026bf4398643026bd4398643004fe7298643004fd72986430cebc4298643026f67198643006f75198643006f451986430cef54198643026f73198643026f43198643014fe7098643004fd7098643004ff755864308cfe755864308cfc7558643024fc7358643004ff7258643004fc7258643026df3258643026f77158643006f75158643006f451586430c6f64158643026f73158643026f43158643004ff7058643014fc7058643004ff755824308cfe755824308cfc755824306ebe5458243006bd5458243024fc7358243026bf4358243026bd4358243004ff7258243004fc725824306ebc4258243004ff7158243004fc7158243026fb705824306efa4058243026fb3058243026f8305824308cfe76d954311e7e65d9543024ff74d9543024fd74d95432c67f54d95432c67d54d954300cfd73d954311e7f53d9543316be43d9543316bc43d9543004fe72d9543004fd72d954311e7c52d9543004fe71d9543004fd71d95432c6bc41d9543014fe70d9543004fd70d95432c6bf40d954311e7c655954330ddf73595432bcff7459543006bf745954330cff7359543006df73595431f6be43595431f6bc4359543004ff7259543004fc7259543004ff7159543004fc71595432bebc4159543004ff7059543014fc70595432bebf405954300cfe7654d432bcfd7654d4300cfc7654d43005bf7454d4300dbc7454d430279c4354d4308cfe75d8943004fd75d894308cfc75d8943024fd74d8943106ee42d8943004fe71d8943004fd71d8943014fe70d8943004fd70d8943006ef62989430057f755894311d7c7558943005f77158943005f47158943005fb7058943005f87058943006ed621894308cfe7518943004fd751894308cfc7518943024fd74189430eedd73189432e6be43189432e6bc43189430eeed4218943004fe7118943004fd71189430eebc4118943014fe7018943004fd70189430eebf401894311d7e75d85430057d75d854308cfe75d85430067e75d854308c7e75d8543004fd75d85430067d75d85430047d75d854308cfc75d8543024fd74d8543004fe72d8543004fd72d85430d6f641d85430d6bc41d8543014fe70d8543004fd70d85430d6bf40d8543006f76198543006f5611854308cfe7518543004fd751854308cfc7518543024fd7418543004fe7218543004fd72185430bef54118543014fe7018543004fd701854308cfe75d8143004fd75d814308cfc75d8143024fd74d8143004fe72d8143004fd72d8143004fe71d8143004fd71d814307efa40d814320edf6398143006fb609
  | 48 => 0xc43d8d54004fe72d8d54004fd72d8d54004fe71d8d54004fd71d8d5430ebc41d8d54014fe70d8d54004fd70d8d5430ebf40d8d542c73c5498d54006df6398d54005ee7298d54005ed7298d54005f67198d54005f57198d542bf3c5458d543373c5418d54026de6318d54006dd6318d543073c54d895408cfd74d8954024fe73d8954004fd73d8954306ee42d8954004fe71d8954004fd71d8954014fe70d8954004fd70d89542273c5498954006ef62989542b73c5458954005f77158954005f471589542ff3c5418954005de7318954005dd7318954006ed621895408cfd741895432ebd74189542fe7e54189542febc54189542fe3c5418954024fe7318954006de7318954024de7318954004fd7318954006dd7318954004dd73189542febc43189542febf42189542feed4218954004fe7118954004fd71189542febc4118954014fe7018954004fd70189542febf40189542cf3c54d855408cfd74d8554326bd74d8554024fe73d8554004fd73d8554004fe72d8554004fd72d85542cef641d85542cebc41d8554014fe70d8554004fd70d85542cebf40d85542a73c5498554006f7619855429f3c5458554005ef7258554005ec72585542af3c5418554006f5611855408cfd7418554024fe7318554004fd7318554004fe7218554004fd72185542aef54118554014fe7018554004fd7018554014fe76d81542373c54d815408cfd74d8154024fe73d8154004fd73d8154004fe72d8154004fd72d8154004fe71d8154004fd71d8154236fa40d815423f3c5498154006fb609815421f3c5458154005df7358154005dc7358154005ef7258154005ec7258154005f77158154005f4715815431f3c5418154005f67118154005f57118154016fa6018154006f960181540267f75596432be7f54596432be7d5459643024fe7359643024fc73596430267e53596430267c5359643004ff7259643004fc72596431267c5259643026df3259643004ff7159643004fc71596431267c5159643004ff7059643014fc70596431267f50596431f5bf765524308ebf765524308cbf765524300dbf755524300f3f755524308ebe65552431f73e655524308e3e65552431f73d655524308ebc65552431f5bf73552430079f73552431f79c735524300ebe635524300f9e63552431f73e53552431f73c5355243005bc72552431273f52552431273c51552431273f505524308cfe7598a43004fd7598a4308cfc7598a43024fe7398a43026de7398a43024de7398a43026ee7298a43006ef5298a43006ec5298a430feed4298a43026df3298a43026ef3298a43026ec3298a43004fe7198a43004fd7198a43014fe7098a43004fd7098a43004ff7558a4308cfe7558a4308cfc7558a430f6be5458a43006bd5458a43024fc7358a43026ef7258a43006ef5258a43
  | 49 => 0x140010004000004c0030030000000c0020000000001c034001800100780000004000000000a000c003004c00100000000000009002c001000800c0010003002800300000050004004000000000080120000002001400000000000004002000c000002000600000080008000005000000000120004005001c002002c006001400600340160008003001400000040020004000005400200a40000000008000000100040020010000000000000180010008000001800000000000000001000800000040010004005000000a00140050004003000c0360044003000000000080000000007000800f00040000000006000000d0004002009c000001001100040080000001000c00400400020004001000c00100080020004007000400d000000000000070008000000000200000030010017000000000180080000000000c0040000004000000500a8000007c0000000000000000100040010004006000c01c0040001000000b000000000040010034005000000a000400b001400000280070010006004c000000400c0000000001c00000040040004000000001c00c8013001000400080040000011001c00000380110004003000800000640030004000003c00000000000024005000c000000c00200000080000000000c016000400600080030004009003000100040030000001001000200080180000002000800c000400a0000002000000500040030010000000000200080050018008003c0000058003006c000000000b0030000000000000140010004034000c003001c000001800400280000008000000000100000000044014000400700000030000001000000200000030024001000c0090018000004400000180010000001000001000200060000003000800a00000020008000000400100840000004000000801b0000002000c016002c0080040000000800200240000090006000c0000008000001000a0000000001800700100050010003003c0000074006000c0000000008000000200000000010002001400300240050000005001c004000000100180010018010000400a002c0080008003002c00a00000030008040000000100000060000001001c0000020001006c001000000100040000004005000800100840000010000001800400000040024000007c00300080030010003000400c003001d00000010004002001000000940080000006000400100040000008000000400b0014000000000500000020040005000400100a0003000c001006000600140010000008001c005000800000080000000003000800300000110018003000000a00240040004000000c00200d4001000c002000000a00180000010021001800300100010008000024fe76d8d5430f3c54d8d5408cfd74d8d5433ebd74d8d540065e53d8d5430ede43d8d541f6b
  | 50 => 0x5002801000040030054000000400d000c002000c00e001800000380030014003003c0020010000000c0070018000000400200100000000014001c0000000000003400700040060000002005c000003c00e000003b00dc0090030004000801600000010000002000800100000100000004002400200480080004026004000800000030008000000c00200100070004000000000600080080004002000401a000400200000000004001002c00e003c009000000000000060064001000400500300190044003007c00d000000600100060000000000000a005c00000080050004002002c002000000f006800c0008000001c000000000c002c0080004029000c00d00240000014001001400000080010004000003000000000040000000000000900140110000003002801100980000018013000400a000c0000000000002800400080000014000000c003000800100040200008001000000200000020000001002000b009c00000f800400180050000005001c0010000002000000b00100090010005000000700440420004016000001100000190000002000c000000800100180110020005004c00500180000000007005403600200030024015002000e00100030000006000800f002400100000000000004003c00000140010010003003801a000c01f000000100240000000008002800100080040004002002c000001000200000030000000000800b00040080000002000001000000000034000002800200100010004004001c002010c00200340050048000001000000180000024002003000000000010000000005c0060050003001c000004402d00000010004002000000000140020008000000000200780040004000003c0020040000005800600100040004002000c0000000000000000100000010010002000002700000250008000001400c0008002000c004003c0000010001002000000140160008007000c0040020005001400400a0000000c00100d800000140070000050000c0040000009000000300000000008007000000100000120008000000002d0028001007c00100040180004004000400c000c02600040010024001000401600040000000002000002f000000000040000010000002800100000020008016000c001000000200000000000000001c003000000b001400500000090004002002c0040010008001400200040000008000000801b000000000b4003000c000005c003001800000000140000004000800c000c03000000070000000000000300400040000003004400000040020000002004c00000000070000001000001100040050000001000000400080180030011000000000200350064002001c00000000000008001001800100140000004000001401b00a00030084002001000000580100058000009400e00
  | 51 => 0x40260000003008c00000140130004000000801600040050000010000000900000000000001000000900040000000007000001000040010000015000c0170060004002c00000000000010008000400200c4005000800000000070048005000400000200060000000005c00100600050000007005000500000160000009000c013000800100280080018003002000e005c00700040000000003000801200100070004001000000c0008002000c000001c013002001d0000007002c00400000020004000001400000200030018001000800400100090000001000c0000004001001c002000000200480030008000000c000000000000080000040009004800c0008002000400f0064000000000200200110068003000000a000c00200000010004006000400c000400b00000050018004005c0060010009006000b000c0080034035006000c002c000000401b000c0000044000007000d0028000000000e00040130004000000000100040000008000002c001001400000040080020001000c0020000000001400300280090004000003c00100100000000015004000500340030008003001800300140140004000003000000640150004000000400200000090008010000800500300040000002000c012000c00400500060000000000000e000000100380040010016000802e0018003004400000180000000017000c007001000000000040000000001c00300100000014000000000b000400b0000001001c00200040120018001001002e0008004000c00000400090058006000c0000004000004000f002000700040030014001000001300040020018027005000800000040018000002c00100040060010000001800a001c022000c001003c00400000000004008005000300040030018018002c0000008003000000000040000010001000000e002000900080020000007000800000340040004002001c0050010001003400200400010004005001c0040004005002801e0014009001c0000004000000000100180050008004002c0050004000002400000000040014011000000300340000014005006001200240030014008001800000040030010003000000600000030020001003c000000800700000040038014002800100300060000003001c00600180000010003001400000040040044000000000000240010018001001c045000003200340020004001001000b0018002000800a0000007000c002008401500000010000000000000800980080000000000000700000010054006001c00000000020000001000000000100000004003000c003000c00000100000030006000c001000802500080010008004000c0000008007003400c00600000004000002001d0000004000400200080030004002000000100c4000003800b000801100140
  | 52 => 0x20000001002c0000000008000000000180030000010002c002000800200000000000000002800500b4001002000000000090000000000c00a000c00100000010028000001c00000200010004009000c0000010001000800700200090000001000801d004c002004c00000000090008007000c0040040000000c001000c009001c0060008019002c01400140130024004008800e007c00100080070000004001c00b0048004000400b00300000010001000000f00d00050010004000000b000401d0040000000c0130000002000000100040010000006000c0000000026000c001000c006003c0240000001001000a003800500000020038000000000000380010000006000400a000c000000000100040030088006006800400000070004001000800000040150080001000800200080120030015000c00300000180024001000400100040010014003001000000340010044001001801f001c014000400700040000000009001001d0040000004c00600040000018001001c000001802900080000004001004c001000000800740000000002000000c001400000040040020004000400000540000000000000c0090000002001000b0000003000c00100040100000003001000100040050010000001c0020000010000c00a000400f00000080028004004001a000400a0010005000000e0004000000000100000010020001000000100240000038005000c000002c005000001a0034009001c000000400000140020008001000800200440000004006000000000140150138004002400d00000080000000001000000280030000002000c006000800500200070000017000801500300040000007000c00100080080000005000400700540000000002000c00200100030000004000c00a0038014000400000b00000010000000c0100008000002c0080000006001000c0000003005c004002c01400000050008000000000400000020004014001400c002400400980000008002003c0030000016000000e00100010008000001c037000000a000c0290004002001c006003c00100100000088000000000800080080000000000401700100100030008000800f004c00300440000000002000000000340040050007000c00000080010014001000c0030028009003c0010034000001400000000020008002001800000040210008000001800400840010008002006c000004000e002000000540030000001000000000240020014000000c0160000003000400a0010001004400100100010070001000000100f00000000002000400200040100008004000000000040020000003001800500000030008000000001f00500140024001000800000280020014003002400100a400600300010000003000800d0004001001c021000400e000400000040010
  | 53 => 0x10006000400100000010044002004c0000010002002c00000840040000011000801e0008018000c00000140030000000002000100080000038003001c000002400300000000034000001c001007c01c00000030014004000000000540060080004000c0010018009000800700000010004003000c01d00000050010001003c0050018000000c0160008004000800100040000040006002c02e0008000002c005003c01a003000000040000018013000000100300160014008000c007001c00000100080004008000c0020008000001800900100020014011000400c00000020038000000c0070000001005800800000060004009000000300480000008000000000000000000018005000c00200800010024002006000100040060008006002000500040000044000000c00600400020008000000400a008000000080000000002001000400040000000000001800100200100000000000800b000c00f00000020004004003c00e0004004000000800000030004001000c00400080040068000000400a000000100680020074011002c010000000100100010018000001800000200080004001000400100000010020004001000b001800200140020068000001c001006800e002c008001c00100000000018002002400d004000200100000044000002401a001c00100a4000000800200080020074006000000300000000084000002c0180060007001400101580030008005000400100300040000000004c0000000001003c01000000000034004000800300000010010003000000000080010000002001800f0000000000000c0000006000400200040050000000001c00100640060010000001c00b000000e000c00100040050044007000000300140000000005003c00300400080004000001400900340020050008000c0070048002003c0050000000002c0040000000004c00000300140084000004c012002000300380080000002002400a0010016000400900000000000000001800000000010054026003800b002c003000c006000400000100040010002000c0040008012001401b001400a001c00e002c01a0004000008c003000800100200000000004000000300080020000000002c011000c00700000140010001002802800340060010000000000a001c00300080090000000001800e0040004003001b001400b0018006001001300740000014003000000700280060004000000c0050034004000400f000001100280010000001002000200040030014000003000500000130000000000400000b4000001000100c8001000002c000000b00000120020003002800100000030010000000800000080030048001000c00a0004023009000300040000004002003800000280010000006002800500000000024007001400000080000048
  | 54 => 0x6a300003eb83640c0938265970bf7968003485cce8791e9b11e600000000bbb98bc0cb4cb81a4537651a9cdb09d219998790426b886a3cea3ef8130406a04b400000000e9823621b1e00016ec22740000e0852df80001fd0c53004c282d68a45eb022425bc463800000b0296f0000f6a139589fa3970af488643e0800006bd80001a6a000064cc8f3aec42774000000011f3000000007a5000012bc5fcced9338a00007f2000038e421300df800000000000684000b0000005000c006000c010000400100040010000006004c0050004002001c00200780000000000000400100000020008000000400100000000008001000000a0000002000400200040020000014004000200100010014001002c006000c0030000003005000a000000300300000010008005c0000000025008c0060000000000000b006c004000001a0078002001400900000040024000001001000080060000002002000f00040020004011002400d000c007000800700300000018006000c013000000800000020010000003800100200050008007001000b000000000000000014000000000c000c002000000a0004002000c0010000000001400500080060008005005000e0004003005400c0004003002400400140000000008000800800000010004005009800600440000000002001c009001001a0000006000000d00b0018000c000001000b00000060028003000c01400180080000000000800a0000000002800000340010008002002400100000020028004000401100100020004020000c01b0004003004000500000020040002000c0010024003000800000000000000006000c0080018004001c00a00300030010019001000a001000500200000000000000c0000008003000800300040000000004000c004000c00000000000000005000c0010000004001c01300040000020001001803100180020024005000c00200000020000000000400e002800000000000000000000c0000004000000400300140070004002001c027000000400000220008005001c000003800600c80040000001000000100080040000000002000b00240000014000000c000001000100080020004000000800d00000040034003008000000000000004002001401200000020000000000400000040130014007001c000000400a00600290000001002400a000001100080030000001006800000140040018004000000000140020004002000c001001c00a00180050004000002400e00140040000006000800000000120048006000000000140000000000000c001000000000000030000005005800400080050008025001c002001800600040000000002001c000001800b0004002002c000000400800180020004003001400000000010000006000000600040000030001
  | 55 => 0xa475121c3f1678550388000000028608e10c050000124400016c700002470f86c0280aa45bf265d083421700014398a04321f02decb9700003f4241b8f6380003b04776c59d000016ee00007b19eac00002bd871b04f633a4628458203c934060b202aa0182b4aa5be047549611cd36c8483d9eed133c4a546f717f60c4f57da00e1bd1340050983390ce0a7c000000001cd603b24308ddb50e3016b0000eaf8e6405041790dd29d0f38b6629036201a3167c0000a5e80002956000052f09af352e5b0860d849f00000000ee1829f00001670ce1958227005a2812800003ea811307ae5442000020b09a8cbbb2e5200005e50000263a0000cdf80001e50106277d929312eb6b0614904703ff237ac7f81a318a5e0f6400006813a7a000105285ef3cba5cdc0e490473fd840f447d00002d435ca2c29ddde00000000000176f3e1e01f6000000000000000af58e4b09be56e104418330e94809ce7ad4d83a864534baf9b3a1605159c6af07231a145b94fa28000000021be0d906072e6000000000f5c0df800009d800000aba7628b2e8241b6bb00003160000000020a847d5f8a0000000000000000000000023180000eb300008060000296a6f68d6a042d80003702851054b000060e00001c08000012fc18ec02f0ac041300000000000000002df9eeb00000000ec780003c8e0000cb68025000000000000c8c00000000f8e8c0f0000000000000002a1a0000de78000000000000000363950002f41e417fabeac00007da0e162b227b488f61d7b250b5b1455689aa1e9b5b7461e574633a0283cda28ac60bc2498000012dd171a0000a839cd3000079f0f359c0e1730000005580000cae64e85ca0b0522b842d8047183b1b58000069f88eb063600008c789c4000000006179fa480002c18ea8000003005460d2c00000c8f0000000002b00000f86cf5175a268e00003b916278000356ca4ac0002938000000000000000495a23581b805fc7794427902c23d61d528a99df80dd60000e4d400037c20fd20001886080404ecc4f8685018c08c0000000025f100001b289fc3a88000000006ec3d226de8000000000005104419048332b058e45f483bea57a00004220963a8e80f0c000000012f62e9d0279b5f19ca1dbc00000000a121cc00000000000064885e686b4a6de2dcc19905331dff00001d6039300002aa8000000000000000000006f22c400006059203328845a8474cea8190c62d0000027c196f333878e9c9c3c0c3f14f898000000000000000d918000207ce941d99000002a8892400000000000dfd80003b10440ce7c0335b6180000951800033164f30d25c2d503f80000dbf400032f83468000178fbff40000000141c89dc0000761834527c63d1c565973dbc622b74000206100000000d178000000052d000003cb000019f44ec9511
  | 56 => 0x5a20b539418a8b400000000d5d018936a86470000000030a800006552dd34b48029052403fe3ee2d5506de13186e126c25bd2364e45041c0191e40b0615c6491c2e370e186c0b798a7133e66d013d80ec39de4e40e54c000351c02c4000139518084eac0690a9b0ff468c07e00f3400008060cd40cea35a3000051f8000000020404c720a1195179f8c9a86d8000058185e4890b80000000a2559ce020e1d2600009ac076a40c0707998f1f920c96ccb94fb2e4e2d1a3749eca00005074f09d527101e54f03249fd70aae008433f800000006a74eac8aec3da03f4c24711dd000072e80000000000000000000c5f00002b0a00003bd183b0001037d7e61d3921bc70680fb361a817025c1c9006b153c04c75c340dc870dc00f19953b0e000078600002afa000044780622b5200005d5977923520000d6d0000084c097c9d08f609b423718658972dc020745cca1979b800000000000edc000000000001df73022348894111ef00000058a5cc0003f2470540000812241a0000c709445000000000000bc50000066ceb38000000035acaa580a28dce0000e269cffabd007e81a113c104ec2d1489c4000000054ea2a796050000328c000071a983a1578a0f143680000000b5c05e207650000a5d0c0805762d000000000000005180000000262a00004a04e1f0e243a048ab9a4d31a0105c46d00001a383d008a19f07000014a6d37001717aa4db00000cb4233e0000000087227ce319221f82490ffa2d705c580000841000000000000e7a5f90678800000003e4840f000000000000000182100006e8c7784fdb22547dd80000000357e4e20ef08dbfc0ae6cd2f4603282e0b3418c7a1ccd28c627cc0001f952fb479443411f4100000e3c000208e4049000002a5c7d18d276dc387d63a3848725e0000436293d72d800012461ce924e0446105f25000000dcdda4203f1262ce2502670dfe05920000a1b04e80cf800011260000541426511cb1cff00007c20b4815f247a058812381c7a4600a3b00003902810027413e538df354003909a93503725863fddf013446e5c89657fc17620f481a8400000000000000000000006c00f210000000064f4039800000007ee0000000000001f8cc6180000730781cc000000000037bce9a8bcd8efa684c000000028340000a52157a0000000000009ab06d25e20000185aa06c00003dc0000000041a4a009e5500000000000075c10b00000000000000000000000000000005ae8d73dff4301a78ec1740e5100000000a0695850000504cfe18728094e04288430da537c800000000ae8a81e00000000b4b0000538c000053621d46f2c0002020119a47ecad99f4f131b00000000e4eb6b6239006493a43f94667e0000a93361f00005e3d95d279c11bc39a96521f5e3614f2a1a9a3a64527caa400001628424
  | 57 => 0xa8c72850e03a200001c7208d02fa00aa7be96d10824652cfb68cee98526d28ab1004f039c579c0001611000052380001d612810420a00018803ab81d58bf19dd9052881cc19a209f25b26dd0000060600001bd03ce99a8b62104a43311eb600004a700b694502bf61d2cf901d0a02f30000719000b283f000092100e23dc46b0eece8b4e2f985be83778abf3e022d10a2615a428e94b188e2883b2b726dd4000155a00005cc6148dd1b11cb00001edcd7d15f00000de0c0002e7e00009e208f90000000095c830b000047dc0375f15129d37ccc1a84982f525b840000c5b162d3d087c64ab093c810a087718df1e72276ca85530d377e000094c80002fcd0244eab951331cd15c82d40c01257874b057d1b5721f40f4493486c026125e66b279e501e4f4751036817925f753bc640142b0b4c0c900781bf70cd7231850a0da831ee2d986fb1d940f4472b03751e1a10407f1819ce02917f5297c71d83b1275f06800001447a6ec00008c2000019ad00000000000132724fcfcc1ac28d9a4bbe00007c5000000000e940001c7468f613c4edf8d702d0200016bb00005d4c000000040442b289be1c102116684416dc024a4b87eb8daad44287c60000ed689e300007f98d0b10c900970e7a74893b70ad24fa459f41f3124d3e305cb153900404a32899dc820fb605889df0ea8b7123acc485840c10b1110882a09233a566cf4f450a31095c1b3c73189ae12d10df8b1a0cb606aa4eaecaf840822ac2ca884d817225d20000000000031161e64d065cde3a905c30795d96500001bf4000090409b869a60e30d980c3c5dec0c08c0c35d42e74f5f96cb1c6321d49b2d7c438c24948acc4618819a42dc23f000000a076e000014a731cb216eb5f119916b63cacf8b96c640ac7306f9a80000000000067d89d3104800005b489f8000017c04b2d8481bda442413a465d134e00009771967136a7190eb7903324c4316070b99dc3ca7497a18e5cdf0e300e8502988cf276c00000000e0a0e0e09c8fce5f2e3ff0248819e17e234422c1ce498ccdb1403b80a3e1beb34867928aa1922d13cc21ec000201500001012a661f420e482566454804d80000000403838d255261cccc7181e3a2c3c440000c0ab7c00e084b3100a16d02264ebe81712baf0000a6210d04062587c0001efa28f62bc07c011db08630000000152900000000000000000006d7a0000000000000000001db2000000000000000286850e20000000081d2ef40001318397c00000000bfb2f0b2058a9e9cdb25d70b527070e61000025920000944a35e6d74479000000006e600000d7c004c10e0ba59bb53a7238c04eb1fbd042b000019c95d72e6a00006f2934c36ce3e2c12f02b419bb20542949c8c05d80cb000008be2c861fceac844b1106a51186570000167e0000f1590cd000000004f6800
  | 58 => 0x7a16aa2d402791f0514b66986c1c800022da31e800014192e106c763d3185b2c24309eb47872d91247c3417c405900003a8c5b8000000007d0a8480ca7931a07843c50000257e03b81331da200001c180000628a4bc3584df9000040d252689ec000000006b8200000000e383ef20bbd40a10b668dc6281cf39bcf55d46fa81ac048a5f44e8103d8aa3a2b10c8210ca2b403ba000000001cf668420fddeb40000525c5f09b6c27066cc803d965b198220a05ab9ab82d5719bc2bc8c480000218c0000f90000000002b8000900000000f78000027e730d0a4100000000000017d910a1e040000bb482000000000059895ff00002868a500ca000001fca6d1816c000007ea0000000170801d860d1d920000000025300000be400004c780000e254bf40001fb73be86cc20a89a4600000000000000039c47a506369411372c3c7800000e682ee45303f68fc70f864aec55cc77532c880fc9ee8000365404080000827000026b400000000000671cdff87ea27844314000000000002398000200b2bac5bf062f4000000000000001b7f00005c1c2b0800019f47614fb100001dd4264896616b11b946eb80001ba280005410587c00000001570e328e693a244094afd018b2da46b94f6580001e764e6a47340001502418c000186b17500000e6319f718e657745fb8ce0139a5a40ab497be1e7044200000000000038cc00dc36f0ae30000cda995100327bf079e1dc82f400000bb80000132872ec1b989861504000019b4d510e821d6000000002a060000d71ca761c0e4dd00000000200500000000000000053e400019d800003c90000000000003fc405308d43efe000086f9bfa19a6829800003df993a26a0fe0848b0000000040983c100003d9816b9add132922b000000000000000075000000666000000000000000667200000000000792cbfdc00005b06a24fcc8000000000005c800001a2209caa7d110d137e0000433d01039cc486c74b9b14a0a05b8c5709002376144acb79967b26096f1e75b1403ab293e5a2c1021031cc451c75e80003bc649cebb900002db7720000002b000005c9e7c98485b3527d94e870e2c3da621a45e61cf60000000049900fd4057397c2bb000037892f3c00002141ecf000036b95f810fc035cd519b6480000000d88c0000e6c2924434c000297c510ea26861f2f34472402d8303162470e8c1cc6b71dfe6f349cf97282aae4a1c5850537393c09c481d99ef149005fe6f50f96164c0278cf9800f07f242588ec0936a1780000474807a18ea0dd62d86078a3e23cd4bec90a030040000822030d167822985bc9c60246000009e790dc06fd0000e4b4000000014889c591e282920000000087c0f4e70ec73f8fe231c00000040997ca7470c8469b8f653df016f2d7bc6bb358d00cc74509fe126a000034c8cd0151213
  | 59 => 0x834000153b40f44b1cbe28b323f3a0166cfa1b06b19400004889f4b9afe0000f59826b977513440450bc61dc8138cde70d3836e7520c8028c8c860408105981b602e066f9485301120f2c0000a9b0fd9133944dcf0196faa1bc3224b3cc6fe066a00003221c1a29215010ae216b511a271741f8047f1b5200007989694347623c40001643ad7710ca00010e03ecc1c14f528a710b9e1b186d8175e3fc635903a88baf3dbe3500000149d261030fca238ed4000077e409288599b4850540f01bef2c427838a360000346218344ab8b8c1b96370c3c08a0c1ac4423e0000ffe11a32f8e000043080003e5ce51c22b87cf68b038e81769c888270661c0002c83318e579877426eb3daa0a703140000000088f087118645aba1379aab161b361ac1e80001c4a4cec2db80003a070000000000009f8000044f8000001a6e546441ab780006f7c000000000003ab48e90000051c5b0cdd500000652654c0000000001000000001faf305081fd00b8ac51d1863442de8000081f6e1080180001b662f8c000000000004224000050c3b400000000003918e8423066186fa0a9c00000001fd000006a440000000000069e000000003fdc62c8f9e9669145836209895c2115e221ba57695983e76554cf2d95ec9bae38ce231180f02ec22e25470328a77e5324f4e830507601d082d9000008134e280000d6a09cc66803f2974a00006458b57093e01640c1ae999826188f307e2fb19b9008218e4b730cf40a7e0fec7829ea42d587b9418780000000462c30e8000000050ec7a29db5000058a46b0206f000078e84bb8000382251aca6b0000395600000741eb900005fa4c3107fc000008f8ba79ca190743d10e50970a21e6800420d42c1000057b6172da940ad408ec00000002c5c6e00f285c991ed446d800000001368808a39b98f232817d64c5802d118947cfc39017ee05ec739cdc10e42305d2c6600015193b760000000179600004c0000002f218fe175c0001a77023006a000011aa000004900001b1e988d0000ff9096b00000264b3e925116477120a4cd51c26bf5e74260578717990000000198c000027280708bcfa53176b00000000156468566cc8c45000049762fc04413f2625e60000e382b200e24a4fc16b403c47344f485851220000005c1b81077f00001f39c0329160b18d96c00003264770d4a98ac167b6408138dd3426b8000000000000000000000000000c62580800000002eda00000000000000000000010000306e0000b8f82bf2903000000000001823000004a968700005318000000000003be4000086a80000de400019df182e634c000044600004c880000c413692000000011bd26840000f090614b6db50421f297ed11a11bea0000c0e3ac4090c2f2936900003e8800020728a56469cc2585f3388c5b5a3790000000000006979e
  | 60 => 0x293120e5f580001fdf0780669c5b1832a1bbc50bcc668c0281427314000000017740000c3a01e537aa1680cc080001e346254bb9dd9f0c4a2f5c15e14d30000344c1100618410e4e4835f000020b800007fd15748cdf4e2eb27000001e419381011b418f602932000000008bc00000689fa70000000000004180cc278445cc85930000000035911d630c3798003e03480ef41d50ca40000000021e419d59e424680000000000004806ed8b2f1a5e39190000586171129461f088bc000000000170e6b8f9b41122af80798000348241c45b8800032c00c684b10af23bb400003c4109416480f7a000073c272f576c79a40bc2e16239491f000000006b5453a96202d360b907438119243e2be6ec480701d248136784d2f701a849046d5534483550000c314a463f4374a80000f5926a241bc32f0000000070183568a2524246e4e1fd1e0a33b220980001c70964063249898c25043c27e8c6e87c001d200000001926249400000001429b0a60574b179efd000029bcd9b800018d60fbe00012e3a68012583e71496ab3e1b58f801af1a5c1231434f838c1caf32dc62a06890b9a80189ce8993000033f441e0376bb301d340f48dd03f1a01388ec94870e926a784238a8d800037e60000000171261aa50380001aae536cf348fac364a293489f9f390000327a0001701000076d8de08000374300005e812ec1a2e03748fe94dd0f34534000000002dd60570459800000922c60233000000080dc267f0afc32581c7200003e0c05661c43f98e700c96285ebb19b012dfa5036000087f38c64b9cf5797941dc15c6cfe2000027670000eb4813136ad000104a0d300fd8337cd0c1c551d1c7baedd988ae35a167b4edd12f23978229c0d11bffb2ae0000234131a281261ecb070e6c1bb600000cec00000005fe89671f3230a03b1c00008c025085aacf85000000003560cae001400001da4c3c0000148070da00017d73bfe709800005810878413c000000000003da0c238f692772000009e8000347a0488315942a0000000061080000a3618d600000002e640000000077cb5b03bb8000000008880ce8269026e1e40056021714bc0000000048a07d63a8458a8bc8841c0f586a9c2a3800018b90fd0527812f000008183201fba000006f68b30dfa00001f3c000063c800000007b680002ba653ac0000f7a20501b2886913939e282a5e000000000005ada22d800000003a5494684d634ac7ff460959b6b779318888f8397328e7412eb31d259d4470a0aa386b40e210fe2c218c9b0a0a14c0618162c000061dc125012d000027bc15e80000000639000000000fe33ad00001d3c406c582ee478b47af940ae800000001d2000006530a66121e78046890bf21072458054296fb96a41e50fb886b6401a42a43bbc2818f5c3fe067481cf954a358c696059621546
  | 61 => 0x77a46e208d0081580d4e4200b3a14e0000fc317bf0c633ce81e2800005ac221c9e294828000497c78700002b280a24d0a87ca3d3c00006278c2c13b46e9240b83c880000c0605a465325b6078ca3897a08000315c00014171d713294dbb5c98000000000000000000000007c4000000005046e54965500000000000000035a44438c05818f357a4e940001f26000000000001a6103fa0000000110010e80d607dc03f309bc26086651fa0a2513cc872e975200006e64aa688783d3833b281680000000000076482991568089c33c0be013493d5c01f0ac91bd80000806531600301148b3991e119808020b0d16a200002d7427a02011ccf0e7097bd8cf00002c4608e800023e47c640000d8700006bb40000000303e00190481be809d20000a24911b304f00007fb82cc00001998515132e08a8460859b81b5383f7ea4c4e891e08e6543caa294a59d5c79661b4101936240ec8ca2843430b000003c1829d06cc2500000157600000870f120a00066f68fc7db127f1bc82874ef7142298515c6865794fd0e5a7fa044d007e90dc00007cf9b0e1519193c000207940346d0c1a5c00000005272000000029e2039c38b1f1c00000000cde80003c9000000000000000051c003183ba8000774c6f48e5212215d86dce1e1026513d5800013da2b541ee8000000000005cf8000000025504ae288b9b01870c66c0000060400007e50000000000006830521897ebd563870eba4a58000057006f02011087250d47269ffb31de1deebc184ad1cfd7d80c629169000081f800012ac00006e6c19782f98f9a493c00000000ff200004a811860bb2101056b83b68df3177c211024239c678a8dd7c0000f543914d98108307881324dc2839100000000000000000000000c278000000000001eda085267e00004021fa6000077f8e3780003ebc6184000095f318e3b60a07142e80000bcea8ac00000000000142000035807ba400009510000226c58f5455af745180ba100000572616800005ed0a1e1cbc077818323884ab489b142301a6310c40017810e1a69f8e3f17a1000033d80148eeb22d000007b593500b0e25641c20000275c1f723c100000da40000c7e81e71ece40787a4096c3a4c28588be9a6500000000dc5de198000000000001c8000044b0aa4815629f80000da9800028000d400000000000074d800000000000794a0000000000000000161bb934ad1d849d8a025120b21482478000000026e800016e439fa69100001851367745b028403788bbc5788bb4000025343f600001ae32da00000bb2ce2d0000000096d000012fa46eedc6101a87403a983aad1ba2fd64670f130e13a1de197a4948fe03095176890e881b41180950c029b223ba40000b0c1d78174c2fc429d80000a010000000125a2d2900000000c7900003c2cced155bb75d46b68e08
  | 62 => 0x92a60000000000000000e7e5944cbc0fc1b4964936ab794b2182764449b5955186e35ba4e6d183c00000f5e00011fa21fc73100000000000000001048000327800007a7182c239c4bc44e7959c2bfc00000000000000040a8f168010212200000001ae8000069aa819d6f02104438894d96d800003a64af21b7b3f3c14d00000c07000036b471385e700000000000158627700000ea90cc90d924824000000020e64fd401b9d702ad058d43479d1f37684e92f5b959da83851d6bf416271a9e3fb0bab94fe2baa0b10158c97fa5146d4495a20aa97f46d200f116a4097c3e9000004f899ac7d182781c7335090a5c70d04d52f720000b0c8000000000000001dc1155e6a6cbf29f633089024819d9e3d025813e842f19cb3dbc202c09b117080002a8c000058e000000000000e5600007e7016d800000000000000065996168098db4800004d50000ac09bdd00000000210173c35100000b32930300007000d7a148f1f4a00000000ced82ce06f27c5c9cb3ce43aec00016db30cc0ee4a368bed18c57860c9a08882b9477ac4831384411408e09130d8a3a2604585b28d422a18439cec618f124ed1d4c5fe93af00787f6ce45167e09644d326eb14da03f038405f2cccb37f0032806408d52ae874101759a5338a405905069001808c33169bd853c2f205e6abff5dbe2dae58c5017187005be00008d0143000002e08fc100000436000030493d603a1000000007eb80460c58f2f5b0900005aa4a2bd77d00001de4fd74219059f3bc4ea2844b17440000000000000000000a9318ad000060e2000209b0eed0ef6caa000033a54a2c2a0963e363e600414052df3aa840fc2f01ebe000081886a4065005544a508b2056305fa1fdea1c8d7a200249f8bdc135f3722000065c903b9aa462b87749bc380000000000154200000bf00001599800000008c09ac42f544f342970090001967e0776060236d74bc60001e6a00006a3c6540d9026ad46dc6130000000000000000746000072ccde10a130000000035f8f5b9e380000000000000000000fa21630171e2a7c23d8b613afe0000000000000000000ad08e800901000082018140bf75b30980881800004cdc6de8d3e26c67e1ce9f1235000000000b9835600003bd47590ba880000000d570000261e58340001acb13556bac4de1e450e283ab000007e12ef8402cc17c00020380000d7993063e90000048712fa045500004c180001c302f743770f5b000065180000c0a00005354def075e959a00009c3145800000000a50d49aac803334799925531bc6104a530000098240740000fe136bc39282a600cf34701da881f029b23c43bf80000c4c0c7c06d2000000037a6055404e1afa1fbe000016a09e7284a000085f99a7b886038c5f7c3208ae61be405b07d500002cbe035d0b529662ba0ac9c23899d1
  | 63 => 0xe0000b7b87f8218234840001d1412a6000096b9318b5260f84ccf997b3d3400000000000259a79607a99f9f3b065daae4f59213e060074c510df83efa1990000000000000000000142114ae262455481c2330022a891999de0f427c385749675000000008d2080518617ed00000000079a2d882890de5b0d000000001b150a0c5b4c5e001df33ce0000e658e780238128428509e11fd60000cd7000024a01a3000911303c7c03949b89fd600000000000200a000026264e0c2f4800030eeb4ac67300003704000028301be4b701959644b5314e300001b501e4207b0157c000174f06e8bf2d9981e366d94d67426225200000a2f8000000030aa0cc00002e722380526d278026d0000833000001f26fae84542a72fb1000000011e637631c020000eda17d800005c30000000003d8000155b2cd424f40000acc40ea000094f20034090000090880003f3b6030d3588490836098e2be000002e33c2873a8c1e870514b00438a9a3656000000015b4000028dce1f1a14892a3b408d58000052c02880000000000007406c09621b21a1f90c221fd125f22f200ee886004fc746800000000e2324b458bdac72a6a5030d6f0000000000002a80f9114ee4e705281493aa2c0000b1c16dca92665bcb9316bc21e83d78b8e134b1853039033553bc36bf00003df83a639480000e66132d1d4f59e20000713010433c879f9936223825207be142aaf8c2aec73398ea01ea4c7e0000e8f0b3a00000001eedb2f235348d11af81719136a4e49b7792185d929e40c8f054a38bcf269c7f3f5f6d4820800000e5c2d6017191a80680552e08888df01281fee0000e933a522c5862e800003aa58206821aa5000000000000898086646506fd4000003e2a0c000000008021ab0dbb0d0103fc08a0326da3c956279fc9a0920000000000345908f37294b4ce381259395e6070e9f88fe325c4accff50efe844400002558a72b9ed17a00000ef627f6661ce7a80420000148000015ac40f37b080000000178109a83689ff31382085440895d819760000000000023186de0b711f0185640000bc100000000000000000001372000000000001c5225c62e4800038b8000000001993c9e1ce9023952204340b2485f1cca06fa0734f3c059700007560ee31256366a1686000000030094854fb58d0011027b80000093886f462a40000bf804aa00000c509dc000058780001dcc3fea0606e720f8d0000560e000000000003350b3a0fab0000369a000040a000055e00000000240c00005491e893cf61682b4e189e0353030c000144b176848784c44a1928cd547e15591f505b22a44b90080d1632456800016ac9973000000010a514ba25a469d00003b38000019282b586082a74ad70f002c3a09e01a1400014fc147c000000000000000000000000005e7ca024000000000000fb
  | 64 => 0x50000000011e8fc707af1d985320000164c28db488ce8818e9ae2a0bfcbc90000000039acf6c962500268140794cf7c89b00bd09a70abd0000320e00009632ccc0000000000033544624161c00002267274742800007f36ea0e161f5b096c2182a8a84a338bc0000bac1088036b3f74bfe5b730c2664f8cbf4af70bfc00000000000359a5648dd1c2953412377d0181626036281f0f3a00000000000000017dc934c52e05869af892cf0fba8ef1f8f00003c9a59b10b120520000d451b17000043f4015c000369d042039291fbbcdc18cc4d9183028e4602031f8dd7ac9225fc1381a86151a6bbc4f8902e24032b3c86c198520252a863608e413e12468d0268e541b2432ae882000006c30000fea14442d6e7a8c125845003b0000000014408000000000018631d900000d2e00000d060000629000000004f900000bf08000000000000001d03094e00015fc22c20000b5a0e6898d937380000e9b857f66f8f589375365c16cc63b18a3148e0958ab01da90a380918b4a93a0b6402970037c00023216ff400003300bc63caa00019002e000000000127a38545ccc157580931e01a181dc00002cf239bce100dfb000028ee0ed8b39000030b8000022c9e945b54bd3400000000000a834e8b3e04003e42e823222882ad89bd4f2a3080829c97e1d192b363f2c00015eab4e46b2476d830db13244e45999ee30de6386c00009f50000701adb70b0f2d460000f110f04181a2ed4d0e17ae0c37129000007fe315e0000a11d3d700002884723000008ec0c00502000000005f0c01ec00000003d4684c82a33c4e54bc04b017f1cec60dafe01ad294761e70d191dfd23a64d74127c000000036e84a5986c00004b1402653310183582477ed774000012cc70000000000191a00000002b1663601cc99a433a86414765000006f80000c8d992f35a61dec4b80000128a668cb5916a600006848d8f198a0ead04300001d0900005a1800015020ce23de40000f95834a0f1e0000df20000673403f0aa7010841d04638f8237c48200c0b886628410000000000000005dc49768000000000000000000342e81a8000063d92af441c4e1932831b92becdbd49fb0ce81da00000f9a12a800009e19c0d20ea16ac41095612b10047c090809da11d10bc4040331000000009061929285f1124f3b538580000000c3955f0000000002e1000003a67220550925cbb960000000025900002738000145eb21200008a700002fb02d9097080001f2a1714000186400004b980001da130314c2c09f851d000052b4a4f0cad000031bc79e837119560000ded9b1baa420000000199e1aaa329c0000000000068d64be00000fcd3ee400014280a202a5a4c3966b14fd61d45b000000000000096784cf01b637b696b0740372457c80001c9425c45ddcdfc870a159c7a0cd0783cf229
  | 65 => 0xea00007f318972d2e4fdc00000003b2c0000659024d374e0000e9103dd000000003d1a04c000000003908c1300000000717000000000000bd609f63b8e740400000000000000000016ee000000001a2400024440000cc40c99221e6d50eeb040500004ec800011ca1e310000d459ca2ab746c0800006142d3e000037180002b085a0c72d0379baf2000000015d400005904d128000000074b836d8814187c3a700ca11bb0424000066e82c315be48800d79e872160000041e4000296e2172ede000000000d2a811905d3124000000001a7000000000000e0507525dd46e7800034a007bc81b8000000044b40001b0f188c0ed850f16c1000011440a280000000000000000000000031064b99a1000000003f4834f099c1024f338000000000006c5c1140cac225cbc5812a33081c4eac984c236b967f01b040000637000000009b11e9d435ca1f9b1391ae7714af319a233b600005040a4400004d6c20cca670ab660def5e08b0b01444968c915512b9e3d848689f1f37014ae8311208b0cbe604c15ecefc110a00000001b998000000065043a5800000000000000299655c000004f83f9663a40000000013416d04398c42942e7cc0767929126593d34ed700003e28000062d0947936600005504c331e2c6d588f71cb7301c20fcf7f00000a1653ca3149bec97428264a9293450000674e5d218b909e154fcdce938387ee27a00001b6a9b6a78a0a8b9a4f2ab80000dcb5ac11e8270580000e0403a90000c2c40003f460cd81e70030000000dafcb0000000000000000000000059200001b630c780000000144f32ac5f700ed08760575369840f5fa40683000013b905624d80000a619cb40000421cbc00bee00004e580001c2480004af8504905e23c90936e7c9820368b3518a3945fc00005b80c8c0a2926aa825ac2b1ac59dbe43106731491a87c5162c60186b86880072bdb1f500216395c706098b8b3c4a881c44e2239ef4c501fb1a08011e71589e0c49000001fd8151143231224e4cef20e26000009449cc84cb40d56964d3400000b106e840001983111a55ce56b12fe23d41dd80000000201000003138000110c00000001b95b8ee6c020000000000064488cc5f6101815426a6f1ece00004fe4c18800000000000ec00000000000002e38bc7170200000000000000000008301c7508d23fa0a5d8000008b000095015793634543800000002afc3808b5804253b9a36380d99c221aa71c38c799177817f3efc6ec0f0627da000091d99f2000000008a920ac000033bc0000b1a00004a38db4c0001c7e07d400001fb000046b49658000301f2e2e22e8b3d26df4e98d3a1a49b66f3a9c9135c4f278e41648350384a91255b083e81eb1b7e748003312020000696c5d61247367e08f46c9922f30522db812780001a4a7834d8c17a20a8c3d74ab
  | 66 => 0x1843800055ac4df03de08c8517e1eb00003aac4e269abcbf891ea103443386e128868108201d0ff0ea472a87cf10a3001d3fd452708ab2a706b5c0ae40681d54335208b95f7266a28f05df89c71ccd646900c8b2f1e5e00000000b219a162f08ca7800034f40000357030c800049b40000e1e0f6a0000cc81cea20f84120c989dbd06c8014c16cdd9329024ce00001ae9800072b828a4943b7742ab8a6520209d2879b4679824c2ba43f94a0809c7af2a5ba85f9492b16314c9c59ac77c21644f260c608bf000005f8000204419d30d50fa1800007f8453ac7c8632126c43f033b0000119230e85c28000154800001815128040d3044000207b07eb288c5c415f599085e98c3e9a1014e6503a0111acc06871a28e4ec70102863b183680d45a45445c00000be4800049ec00002c739502670ce8c00016040dc06624000033506b85bd00002e590000d110786000025049ef167000005fc800000000136430c288542d14c43f38000197a37b20000f0b0bd91f0a29b800002cea56050cc0001827380e1ad60000273214200000001ef1067a0000b5089151c551d38596934608461a38dfe1ceb0aa623f4a9d0660000010a8000172f17e35fd00000c4e33ac578400013c080000000000190f18f34eb0a504a2400005c8c30e1f099517202ed15917a14e015f4c1fc000367866b00000000410200008678efd00000000dd54b4c07c4000045880000000501abfa82bc80005e8c3230000369829080001fa02a287cce000052d07b01edce989c33224e08b828997212c9415c2122110b072a0ab47671a9abd000c700001966410915fa12b92ff3e8b67e402b134d2d1f000000000000000000005b81101c6e0000c4508b19afc000000006cb38dc1fc0000069c0a3249740000aed9e6c5cf40998000000032a4c1202e521c2450000000001198316e0000000314a36dcb1a5be7248a17d44240bbfbfc459f000019fb00004e8cff68000303666dc8d6041a1785021a7520f0d04ba6ae40e60fcf19a260e8244d3ba3ba85bec000093b11b666ecad580000499598cd071e9700005abed7916ef14603dcafbb9c91805c25bc23b9bc50fc50386000086880000000e2600002bbe4ce800001cf18385bb4f3c80ce00000000f20000000007d7c97988ba000000000001d6c0000742c00004781d364ff020f05ba172e000080f931f0000396c000000000006ebc000188400000000a03a023415c1c20fc810f130c779467b21b7dbe5a1e44ef90ceb81125f20d39c19e40b4271a4e89d8411502e4cc7f0de63a74373000000000000143aab69112093862d41c0deb3a7e601fc00017020afe5664d1e02881fb84bd8f9bc0000e6416b80000efa206d4a941ab49881a9824e61e608f002e16eb60a3927307695220e4e40000074123000016af0ffd000099489d231
  | 67 => 0x6b6000000000000000641849383231f42000051c0e7c286f1d5c31b5b8a193177a03b0db1c80004c801a303882b0e17e4d0e808e95cc69d60000000177000001ba0000000000000000a9925fd0000d2e9905b7e0401807881903c180c388249a3a045a00008ae800001b22150489c0002a205595011d3ef2e7455ec26800003d526648cf3133e2d3a133427fde39283719a04281c1e02567d4c59095a333e23c883b81dce322e57e49059976077439e4db647921a4c3054d999ef9077c4f7c3210b2c40f05a94fa4de7100000898401000025c818d0d6e17d52b25020c00018360c240000000184930ba4194b000e24b8be5b28295400018482b064ad09b0000000008da910c202e1cd0000000031ae000000002e72d8839400000c163aa21f40bc70db794f645641724e404008378c91e826325a002f8d5984c52b765a34a5b566f06a300001b60a5a17d0079e0c494f309512d7c6f80f7e38f03078799d82d000000000288000231a3b5c65e852139fe01744410273800069002309aa1000008f048ac00000005c94fad00003e5e4480000000000003b547aa09a0190635b026a056f00001a800000bd10b1843000a102f3129b00000000000355a14920000cfc17b300000000c61972251a8000168e0c480000000116715ea579452280ba0ba07bd06c7d5d1391548c86a39b2c13362dd800018c400003164a2e8973a7a86b9831a400000006cbe00016891bce1b94d7f1d72000037f433713e48000000000000002e0973f06d94000000070e41734be700003c9c000042d00006d3e00a94e72aa4208835e83c0ac8a608c053cc70339e1dfce6080601ce72674000000009780000000000000000882cb88f8e21a6531aa4807a90fd60fb40000c350cfc167c5348813a54325300000f1f21145cac734133c10b86ce4000000003d47086a8f8b2a800000006b6800000000000000109e2c080000de1800000000000000152b0b4a000090c04a9000055c4000182f02a4131cddbc31f1cfc71402439ffe000000000000000072c0000f6a800000002b900001f6408ae71a0da381000d780000000176b2a0c0000000127000000dfcd6f8000333a7048ad81e3002dc14108195352800011b083c90d406ee2494d7140001c54309c0001f4d00004d0e3ad00000b585de8d920b460000000000000000000000000000001c2a416ce8880000000013400000000b1240e4c2a5b3680000000b5400003dd03fec36d00001dce00003fc40000000393cb1e800000004baca10c000240e752894c04dd304a5eac0000000128569d2ea08134000057d067199130000747044700003ac80000e448e49800000000000000303d0146ac18000000053640000ee100005c9a30c800000006c6403889721fc60000121553233320960a4c869800006d9800003ea000043740
  | 68 => 0x4514000000000000000ddcca7f154c4ff8c21458a0ba20534000190b0000150d02a168c000082ba0000000000008e800009d80622000025c9b9337a01c98f6191d72ba1711c3051e860000193200005be02ea553814849d524dc27a86031ace2a480a34000000000003fe40000000156a51b865e000000005e8a00000000000054c1f60ee2000000002ddc0001b9a0000ade02231ba42d0862fd89835dc000056912f082377ba2a8f6059000040bc82281bc2d2443b0e4c42ca3e8e5a4e7ed1f8407dc6df409c00003c920bdcf260bf6152a613000015cdbe540000c35032e105e0000bcb8974b7ec13cc2c00000387a73600e5105733bd0378000000016033d4a00000003b1a0000d0200002b6200000000000000000006e994e025ca7e5c7aa93aabbda28bcdd69ca00000394c0001bd580000000a07dc5313a8046c000122900000000ce4072c17cc16103f900000000389100392ef132c00000000ede0cee7bfcb0a0d2e066e29307cc17af181700008c8052300004f701402077091400000000cce91603ef40001b1f80000000000179b3aa600007a9000000000000000101206300000b1b975415443a525b6917f1dac118000017cb367000000000148089e0b5600000002ed100000001c6215906a401f3058f05de5612a20000026cc2a7800005d61fac435814dc0000000403441c0ad110be000075d0150321548c41845d07256c782c8468628000000006c841823b566bd4eb88000399e73800000d79800017985758f0f0900565c00017b41faa00001ea8d560b1a328613499b307563fc84380a1234d8589a726d1581df03fa42fe9671317c44c419dcaab000062144a7926723f02a2cc9ba0a936ee24d0f3615801e26563829f071f12e26ced048878f297708a902505a2352450a438c9b6f38231194f15565a07f00000f5800001e9200007508d9e138000001a48ebe0f206a80cd6848795b80000ef387ff00000000cf100001bf256589aac5861806000000000003ffe0f907af8d7d8000000028680880000581c0000000000000000001e5d80000000ea68359000000000000d4a34d43474000000000000000e201e230de98166fc602c21b333e1cc1900001c280e2ef7b000000000000000000000005e12c7d80000f660000000000028740000f5719630000000000000000000246cb080261000005e200000002360171850815d19b3e1bc42cc9f4c3b721f10a4a1cb9124f176c017c00a0adc6d3400019b2000036d0f17085dafc20000ac5000008690c28000058eb0ec056831e8000000000000bd0e3c365200005f519d70000000000000000000000000000002c5000007d000003a60000062b00002b845c3904b0000000000000000ee6332c2114336000012fc000004e92a70000000000000000bb905e00000a030
  | 69 => 0x9ade19aceb400002b0b096c912066ea0aa6f8c58f0dc5238638d034699ba00003ff4c371c9534405090000002a03a35f4cfa5095b000000006780d440000052c4a69dd000000000fa54fc839f45d58c8387de25ea0f060001cf328c47ad64ae800040c807049aa0bc3316225a67a81171060e00006298000000013d4bb61ae2000000001459009a16860f800000000000000000019d11ffb79c00000590ad265e609588f433d320d308fc4000000011c80000000275213e482895661eb0171000011f61a3c0eee32ec1b419bc403cf4780002e700000000013e00dc722ecd85986153829f49ccc000000000001a5000027cc11f010fc00027aa4fe843d1fb0258600009719bcc3df658e62f48ebf39e280488cb1a94b94a401c484146f083a380c082844e36a92ae2545033f2ece490021a81030ab40000c740d833b9e73fa6ad000000001650e36000031b112d400010db40041eee5a8800032381b30b360e0b298a7da84148c38bf1226680428ef209fe798c2e991730000019093b8b9b1eb404a07d915342e7968e4dac00001916000021398ab316e1a58a160d711b9228442c88000219c18ca8f81b5180002b540001e8b0dec234aa295d8b000047f82929ced25800000d540000000038243171a18af4f51380d0440c903409e8000000000963c404c8199a000000004f5813c00000150d0a101131c43598000114819da40d0000193b1c022b6209800003ae645d90230b7d1e5a478e618903a2f786dc015f135b9d3a3dc8f8596593bec1684cb499008e291d7c1364d1640fa1ef400000000000261449996fd80004bc0a549e092844485006640002cd01660bf390ad00007efc010dd6a2a7c0000c5f8d342c9a1f680ca89ee12f42200b9d91e40000682c00011ae0c904ff65329201272803fcb69d37d0936224c73653020620056e3a819afa26a4718d7e00c000006f1ae179407b6a13adcdeb985c06f006a49bdd1b200007ec8f8d920e0d3c3af0e0116e8161d5c50761108412026a5876200002faf1ef0000000017c43db0944947e00001ac42bfd69e01d4250cbfc400019843a100001a3e029e5b640000f4f000000001b5800011510000b91119828a61c9ca401f2c163f00008b7c2619c7c600ef179a4832a4343c19c4c9e00007e040001573276d0b34bfcd62b345b234c14797c700006c6c0f6800038700000000000d800035b8000000000000000d9f000000000000e61062f08b26608277800040dc45d4000025c00000000f490b52b4c84ab850f93b0ad0263589cb993035ed3784db9045f0f162dac2e6142e41564e14a5098e8a6977d600001e26a08c3db80000000401e7984925943c30fc44506919940000027186aa57b1a4eb73b8102da60b90a7b601938b83000024f102f59c9000000005e700000000499489f000000000000
  | 70 => 0x72c840b000000000001a79152c4b10bb98575000000007e300c717e676980000000043a785071e400000003e6ef6e86ab00000000000209528f0366847b884b1ce437c437b800007d15950c7180da07410000494c0002f3c6ee2000000000000a6a6638a011d3e819c1d9c8d813424a182888cd817b667f4f220392009d3fccd4c178421da22f49478d4b00000000b67124c08220000bedc00014fb6c1075a4b541b1581ea00009ff000000000a5108e0000107c2a694af17d65cc465a8135a5d96af02e4052604303e643db05d24144807c200460f386c25d05de000000000000ce20bdc24204204000000000000000388000000001d0c67105ea186e0c4803e80002fe001a4d5b82ac3c7e0000000000022fc7ae86ba1e8e3ba20a28ba28be434ce4bd2df600000000000000000000000000022a8b22b62b33104a102d22f765f507844dbe8000486860e489d33477baa292c000000000002c58c191a8200000c9066a0ed800007d69fbe8e112d582ec1c1c3cc80b383319456270477bc989151480005d249ed819fa9250e4000012e00cf200002ff80003af4196adbf00000c020000db2c000088d000045c19192a62185c892800000000000000000000006ad499600000000000037da03a09ee65760758c8db68c00000000f12bbf65b9c73b94ee1f627568000053802ae6ec86c783c700005fa6000152d074a7ef8352092109533bb49c15038800004e8679c481803620d84a39a8c2e9c0000e1e00001b8e0000b585fb3000023849688fa811684960d1b102606e737f820a80a33794414860c00001d9a0db82fa0ac13b340c7e90b86d537ac4d100001ac7991a22d84cc83aaad726a7c6ae0000126300000000a3600005d705b3800011086e160000000147c000000000001638000105012fb0000000000000001e0e0380587000040bc478075c8a6d070e12b0fea924839ee130cc9c01dfbf8a0000a9dd69600003e4e52a9648918800007bb80003cfa000078a8000107a00000000d3b000025780001e760f96000000015ee8c4c000000008f6032c5d989da4bef36d4000049206a607b50b1e10195b619d0018463092430e764eccebe20a599f00ba4a2b89793ee873b2af5c5663e185f4850308ee1e580c0400007850f8e48b80000ab1a0f400007578bfc3a5a15ece7083a3018f824c5480ad420360a9ed97936727ec5590b5fa05d16fc40542cd9fe1097a0972b82000035a05ec00000ef680000000000057400006da2b7a9c7a097f77cc5d28000000067d870e95f63d3e60ac00002ee3b7e00002ea0e7311386fa8a7b00003bb00000b64111936c448d9049000000004190000000003cd25b4b21180c80006494000000000000000e8f1c2317954eb447f800000000000281178a2dbb2f3aaf8800030f43680a5a413224e9000000019d5
  | 71 => 0xd256e26e102700002bd40000476133000000000482400040be0000d9a1b4080000000000037200000000c2293e21aa846f8ae4400039e500000001705000010503218231000000000001c8b00000000cd880000cce14580458c3ab86243acae7119b008e3490b3203ff135b000046f0e7430da51780001ae8ac960000efe094a3ee4692800012270000664c00000750c7d2e3800000000000000000000001a8a6a0000000001a28799ea8480000000000074684e700003764f190b4f08b468a863c07932f656554b67932400000000dea43ed80000000000108535ec4db8aa50ae0120507d831c0551271c73a0e8a81630e3604041afd2b2000058040001e000000000000000002510094c000006700002b641320cee00005d10f468a790b245530000114f842e429103819ff1873000000000002e1e00000001af0ab9500000000000361400009d4039a00006b9cf0984d30310000014f00004092000093a948403ae0a705840c2d359f0d04d270e12a0873c5c20980003e467f4ccf803d984ea7af492215c8166d7ff00000b9e2937196008ed1162e1a42cc0000fd032d3697e6b9029000002474000000006ae06ce7431a7100e80000e8e8a4b00000000000000000003d88594d18500000fc800012833552384847a1646070651f400004b02ed31b704449fe02fc05d361e99508338424dc99180000cc54274000127607fa75000000000101465a898c800027855f6c0000b0927d67bee7d49c0a0a34136c91b86971baa79189ff982d80008218f7a9716299f0578dfa075523780000b5016e89de073380000d10311067ac09a800030db22ec3e4863b40ca00000001c858c6a128832c99b6109c3a204899e6f000068182ea9b7480f00838000000013c46e829f70db615bf7bb8a1c1d3b2b2a40f0ad6800031b404e4054863a3a48182c6140c6810d028ea88e98408000000000000002ca6739469b1b2ca0d8553c22413333e522dbcde140c13bba46940f214792d160bda74051d10ef0359cb2c068705e26182c375556286211145dca024000027d001f55281d4a00009558000187640c8b8984b703dc73000000c02185f000016e08e7000073708b7000031506e38dddde170000465e69680000000000100d9747000000006580000015a00006d9000014746e682448000380a000000011ed12740000aec40113e683fd0f661cad0b6a650818d59f51eec530849c8000401c695066315010ab04ddacfd1f082c157d5493903380fa46f60cad0a798f1c7c688218fb321b22d4c9e912ca35fa6c2c0db0620148231c8eae8a524130000044f40000000603a0000000000025d800004940000000000014e400006164c4d919e3e625d80aaa8637a4146a907691adfb83a4700c631b06000038d2f7787661bba82a0eb583f112fb5050000000004b7000
  | 72 => 0x78bd89c861cd40550cb9925b3e9235d8000145100001c6ef73196b32fe61e42a004998805571885c88e3932a584ca00db989738000079b80002a88000000005b8033a82b60000fba00005b3471882d32b6e324c9f81f703492000045e019a2592326815b180409c2748c64c063980007c4901d800000000920e3e00000a4772fc000000016b226041af131e00000000000021785ea000000009442922533c00000001606000000000001d70710e000000000002b6893bd381b9860120711de841b9144bedb4005a3a0c5190d5b4d5319693998c2bdadb042c5a6edc354f51a3e5c181a4cdae00007fc043281c41f861a884c0c000056600009bd000000000000000193902c256560f88000000025aa0000a1f97888024465400000000000000000018aa4ef4325000018017a4033d89bd29c43f04319ccd703bd0c789b80f8119b9471c0001684209465b0bc2a03d0f8c3720988d92418e23c240000d3d1b0b712461b1c411b5e22de23700000000000078c80001cd748105b51f6e23ca0000ed38c95081e0b8a48180001de663de0001a820000000000018d580000d8aa55c96e31965630ce314023abc44f056f00003cae5fecc5d00c538520c184360c8a00002a80c77019e800038e4000000000000a9a3d20fea00000c98df48bf900000000b8b80002d300d1ca534c65373e240ec5b0cd514d63b44109800028060000bf980001d123610e6391b185623ae6e22035c00000b683de5fa9819636c60a3df3e2cbe2f4c000054923b41558785453a000028a104d09df19ee410421815891abd3e7a00008d3a02671aca7500001f6a0000000000000000000de21c250000514eee000000e5d0000000107e082f00001c591b928a923646371d05aa602ae00c69b8abc4a53a4fe3800016a70000ea600000000324003289f03210000000000001b2a73d0cb5d8420000000037685070d105540000000030be63ca0000000346945dc000800029300000000000039364c5c95087e0006f3d181de57bd00000000000000000004d80000032200005b50f6093ea3fc825e22de05392afe0e0400018e70000000042b97553dce6440086817021cc350c56108e2b29a7644882984980d845285c6dc7629584168fae18120c4224240cb800000004de063b54df360e6118000178c317a1ddc000141ea7fd2254d9ac5b908424f448111cd02d71699855d2082b4fa298d02d8bf500006438f2987b39d6051fc72193590ab275d0000061a2f2b3348dc40d5f0000716050e14d200000000387871731b3000088102980000203095bc0000000000000000003b9d33cabff82b8125e17703edc00008b81ee400000003ada00004c05b4405520000000036203f24e5a6e3cc7b1e5c0594276194118c850805138856000076bcde30e4c00004ca82bc07be36eb63f202354e
  | 73 => 0x40cc00003ee9f1e2196605899786ce000026ec00020b011464c8415b8603076b0000825989c1cb15778cac9a9983650000cce1761162e0000b339bc90bd81c3a70410780000000000000000d08576464f981d1f0726dc0000573933007a04ab0ca983b80000f02882b08da7cfe3f65acf3776250600012710d5e0000b2b999b0d8a80f80eb00000000000075893c63d2634240001a8380000000ee100001c4600000000a3520480000ae393aa334a54b8b22160a3cf552a0b6d126f00b92ffc9341297311a6ab05fa1c45378e69fc420800033ad336c0000000000052581ff203c1bfe00003c5400031ff0000c419d9e0ad64cace4380e627f03f2898805420000000000002a4000000000001a230f2e24c0f218343000000c800002e130f86624af61a8707b82f8af2d15cc0000000087b047d164a42540000cc2ad0a60a8912874f0d2a5f045ef9c181c9c2c040001f25037c47400000cbf000035a000008533e20000034d860c350a6804e828c941e2457b440c86f50cea40ac3d4122c059b1b98af000dfbb020f287e68857919605800f80e5501aa5ff650714951c3242b028a92b5329c0dd8bfb8b07b5ee00008ea9305bf986c5a8aa1d46369600004a7000019425a64db895a800005bd0000000029821ce45e58f3e0000000000009840000578c084958f2abe0294bc3130e25fb478c2600f180d74460c5eacb7f3d2a259cc6e143d3f9e0834dd217d02ea27f34a138e603ef8232e391018e18a281a64db1e1f15860abc0000bde1e967ea00001fd8385a32f8d7d996e19587374aae8df715fe2cc2e352028000012ec206d0a800000ef09e81ee10000352407c013700002984bbb000000f918c071a829100701ed041b82373b941b647778ae7192c0000a8b595b05960d56e0f800029710000d8e95402b8264cc00006dd15fc00006d9df7831785668bb28a7209e27a98a6389163112222901a000000004c980001cb00fcc323e8ff85550d4268bac4390d529f00000f54127c31902dd44641c320bf51704bc694f201482154000000000003124000000035910000d1680003db80000dfa831329ae5578bd395460a881134f51116f1b7863300000b1080004cd0430c71527341a4c8948b7200000000000006d391c623cfd2800000007400000000000001a745d4987f00000000000146534ec00007d84000004e5fa891e20683f9c0000d7cca2d1904210c3951fef001c41880001a6f305156c83618087b4f61b8033481ad0e9841dc952000006182eb80001c1da242000000009d031d600000001092329200000d58000000080006819b05b8f249980ea02b0bc9c0000486800037286ca000011b314046404471929f000024cab2380002cf00000a4900000f6462085561d951be805f040181260000282cda7082e389c1d9c00010c7145c27
  | 74 => 0x59008a9871b5020f9a994c0000fde15ca4c000001bc400000000d863c106e18c34912311ba0000e86000000000afa31180000fbe39883b59cb2000024ce0cdd72d08621970ecb8c2b32ee4c30018452700000b785dcd1c813ca0000833800013f200000000ceb26e67a080000f8a311800000000000000000000000800b32809b05df138105c7237600000000000082c7b99a6d1fce25620a3512402b26696ed1800000006ea400000000000000000000002062000021598b82b6a00000001c1918285726000000000000000dd6480100000000000000013853cd67b7800018704518000000037a1023e000000000005b00b890a34000060fc48100000000000000015cd167f0000d05000000000d74c27037d98ee29580000000000028c8430800017542b94d7c99320f12093abba400021ea5350b41000012b05f2448550fb2a160000c0c00000f8200d0000000000001e1c000000000000000ea384c4000052300001ed111850000da000000ad8585c00000001c220000000000000000000000000039fc00000001b6d16bc08205440f26000000001d98638b2c40000091800006c630064a651322aee4da000009b280000000ba080af23702e4800000003d927bdc00007d3041e000000010da3ab65d6454c452a000066f00000000101c3e70000000000006e0c000000009b347f000000002ab9444ccced9c00000000000000000000235800000003dc83290000000000007978d35c22c323e000017c9d7e1c9265d0d651bb386e912e8e614b8015286c0a3fd9d8e3f6a72c40001d9b0ec03eeea961a27219029641601f3c08ea00003b9a00c17e05eb40001172000e0000970c00029290000d165165297e140c72b4043000000006361361327e2b6c0000e28373c76a09408d8b123b245a1a99af03134106450f5be63ef600fc382087701f4025c58f820c2a341100b215e1595d463040001e5931764b8a0000bf7aeba0ab8006136a3626820c00014aa2ca00000fdd800019445c7400000002f8400000000d701a526541041ccd38d20000000012391a7280e00001d760fae00003bf0fed3c080000000082300000000302940600000000000000000000000000000034a481b0a3095201f884644000000005b14a5800000fe29fe0000ff38ab92e5880a8c2f1b081766558c2d18d311507529e2bf0000000000000000000291a307c8bd9e2923ef431800009f203a72c8ce11553321f200007fe043e14d0669838615a529602372a3d0000413a000024c800000001ce012900003db48070184a070b8a873ae57dd098289041ac1eb9c14260e00000000000000064745158b28190a620400000001888124800000000000000028b8000358a00008aa8ed31ea24fa04b980002c661394000031739d23e980001d753944726893e8d0510627f08d5300
  | 75 => 0x466040e5740000000000005b7ca5280000000048010f939e00000fac9a417f12a460000f290000162a07c85be0a8c3eba00005a089c816a15f74acf400000004a7449510181c4234ac9611fab06da4cf4c0a8c488b5a67422001b11000000008108f0139a80000000106800000000cad4000000024606c11ff70c5470fc0001b8b04421e2ec7e00002cec0000c03d1a132d14c10000196100007d5c75580000000500a00020ab800002b900e44e22c1e778818f44088a942f508f98285147a1654d9880b3054252c47a615fd21d24ddcd4e4185315424680001faa0dd028800001c4200007a58000000000000000241d59d000061280000654261441fc4e6104d000004100000000000000001be51883c1e0000000002d19b4057c0c300570cb47d9d049c1d2249c08ccb3f85aa380845aaf6d814fba9243dc897082d2d7545f09d01bbc27192ff8465079e106663645ba163b0f5a400234d1c0c3fb44d68e0d9dd537706dfebd2859a175a4bd038493d915660000000028fb5864fc8a7a089c9626570c1700bd83cca705c601d41b270d761856010040000582c5c5000001402024c038234271a00000000c674145552adf884820fea2c9cfe480000000425c69e0f2500005714794400000001b0800000001b380000b92000016942d16df7015b093a40007c31ae40b6c0000594926432564ba8760030834660000a72909a279500003cf80000000230cc1117a42b9268be9d1000021ca000093c87dc3de67364daddf3a24a6140029e97932c7731ae6111c570e066ccf03b01cb33d83658f441a75006a638e0001ba6000000000000f0329592134ddf19ab0000000025418fa3d7000007355f68024100008881e168fb273ec28c08c3b6f36ac400000e096d8241479644430cf4339000000000000550400000003be200009318fbc1a404674ff880003f10572c48511421e5261bc74183a820da55c82e51d25126f7492aaa03ef3efc466812707a016707c88b16a07437446d54b1107ffab7c0f5acf086a51200024c6c00d5f95a010ec7dd976a18fa5564ac7cfd43775000000002f7b9db000010282682292000000017b32dac63b0df983ab881c4e02bb20fff1b2e19b48cb82653b9231f052980002d346b84000000000000000000000000002ec83cc00003cc46c70ddea0ad0b606b9acd34cb8126931981a695a738da4d8847101b0092e0000264126a00885a443071a47021c742000000001a50029c3b70000119c00000000b2e2c2a5370e3d80cc1aee4d90957800000000000d31000012ca6ec01cfda9c0000000000000003906719c3f4000000000000f2f8000000024a200000dc171d515003fc00022d62cd4fe40000215c697c57e8e8bbfbc24649b2800000000000cf40000000000000001d7734f835d49d64b4f9a645926cea88b90dc41
  | 76 => 0x79a0c815b3d80002523016400001305170000000002f67de428f1bed000000005db90bb000027dc00009e0371a0e9099051f9114449ac229c0000848000092a1de00000000000000000c00000053dd567069c6c40a5108ef15a60e2a9a19b2d3d7671642250b5a384e4d58e791a022d556faa3364000060f0d7cf62014100005c4011c8b950e6667286550f7112aa7266a2a8000000034649b91c909d96000088d0ae30000786c64880001b4477100400d0e242c461ce690665000000000db924d3e6c00003a40dd12e3047aa9c95c743126341c056123f0000000032685eb0b863dc01780000000000001b7c49e250a000000004fb27157c44000192d0da641d815cc3d5863280c80b50b4e8a284f4c3d5875d04da0500c6a840bb37d0f8092b966e3ac64d2832d800029cc169cb36848101e854789c499dd18467f64afa811e3d640000d9e400030df000003c8000273637a00001d4b1c8e2240ded48fc000051a49c380b9282b2e7c0000577232a318c235000023982b1cd610b1117391fdc3634c4201760e88000197500000b12635184d2edc000cd7000003c780418f33000037a85ccab3900003c40469800015da34c66d68d41956e1cfa815487401f44146220c4250762070a7c907bfa0aa3a06090ec4700000000587000d000037fc091c2d887290000000068a8000000000005dc40000000207684997d9a36828882b6997e021e580c381dd380b9c0360dd007fa9d520f7c8809ab20a5074bcf3bdb448abe4f0104b86aa0d284db4bad9ecf07d068786201b4100007da4b060d942061554aa090000131556fcb9b1c7180001268ff481c5411e00f43b8800031df339d052000020705edc072c8b236467b5800012c814d40000e5e80001d8a2290f9094670de08180c2a9cb819fe000007b9b4235603f5c6999b7c3468318227580001d3b36240000f4b80aa6180b8fd1e90ec830c64e05fb60000533477b86a926fe6c98f760dbe0eb23674fd680000ce0546c0e741e635ff0d2c0001c8d17465ff411780001f1e1b1c88a8891282c413865c400000007a8041ddff61a3678cceaa823980000000ae64f0815af0000b0b03ae027d4820a80066388b0270857110f007a8000087207f106ea4dba1db9357000036300000022800000000000d59092649242b2816929e13170e531e24bc3a10767d18b1b00000160435800035e257cc00000000000000000000001fa27168840148603221fb86598000318476c4e03d95e00007eb6dae00001a1a7198e689d0d00000000d6b13b512c800000001317ab4400002ee8744129216bcf2e15123c6e00003d95daa2db8678c217d3f41472377050505cb3e2c285496a1db01142051073d05622d6c17e86c68d43925866440ba179c1c9934087728b9a077659e8ea70db88b1b7580895562bb5b200000001
  | 77 => 0x82c506f63c8c14751bf0a6a111c74f14b93ede133075a848d2d6f1d94d5d83670000606466797193a4e00006b48d1814c87e68474143719556b922190352405a7c18000119b883758eaccd46b931280234e044a78b61d0000f998a97033e2c0000000b4286c000096c1a510000210042c9eb523260000000000019b80000e49000019c2787a4b50bda239e03b4381027f045677b02b41859b9aa30403c6087d0c2708284d20f9d38607d000001305189a300011b1fb938965646000000000004cc83490a860000000000000000000000000016ff00000fd4b1f80002e9a51eabd0c2d02cf523b4bd91e5630292af0dc3ce13299c6ad8e9085fb225e59802e00e4b8c910b883168c9f800022949e51274273f75b820b00d608a60d845a1910601840000c598000000000001ad0394800017dc2339349331a3f785e08f9402431ad40000000000000001d68e6e00000f08fc01ea10c82000000008f80ae20e78f4dc00000000000000064c12ea1f20b79111820b00dcaf108e7140c600ec49302f280001318d605cf0000033209888f38b66c00004ad5e8511840ebc00008fb04520000000150a196b5ed474b1c3523e81380ec80e5e0000000083816fe27681f9c000157c116e7b185c3940522664c6c62581a100007eaa4c89f3740791944000000019f243300001da5000036e039f000000002cf257a18d23fba1acced20a982fc31ac00e390bd37587ab40000e9a0eda00000000279191d00000001e7708e8000061e9a1f324e0000f959c20acee6868d688a6c071451a0e348590072101868a580361ba81aa0eeb89ec0ebc5d20be7019ca45641087bd800016f02c743dd9e38000000000000d270f2a39b4fe90d65201c40808fd40002e12702c53d0000000000000000000000068b8fba854507cb00007fb07d13d80049ce555261000052b86090407335e31e2000039410b566e0ba61f7315dc6ba4b31071128a400007e9061002cc0844547842c000053450579bc007360000000202111a4000000000000000337a00012283c5836ec00003bf128c070c703000000006528ad30f74281300001359e1e41040468c671ea71cb000008ba0be534d210a42019bdc0b5f7b14830823690a27e145301835bc040000b0d897812a400000000cc509b27870000000026bc0000000036a369e0000c7b008c1ae67f700001a28100c462811f8000155000008a8804500002280a428000107c7ce00001339059e2e80b7b00bf16ff4a12907800022c54ff4686029a01f8000050b4b4892c52f060000000000000001da1e3500006a0a000000037ef23707980c5d80000000d120000346a000052a16ada75b000000018ed26bd29ceb789b538c6e0be00000000000036c4c170000000012d069500000000000029883a692e54cb6e15a04b29510000be000000000
  | 78 => 0x81368280db8f300c7ec41934000410b06e400013533e961cacb5680000b486bfcb2b0000000000009dad63c25d032040970fc2000077a876e800000008104c018000000000000001b64004800000ef03a7000031c6000080ca69e19f000000b50e050000000178936cf00001430cec00007ef0431006b188e11581b00912062a0000f66800022f2000000000000000369c2031a9940a24a30b649e813a9e1d1c2f705bb274e364474100003c6865a0175018712c0370900292a2a7877eb034017de04fa06a903347000cb90f68c165ddf33ca648c27f000003805ea097c000040e4640c28080003a30457c0001c090ca4814800002a62811000000012c136066b18574d8f827096ae8000000033dc0d4475341841668129400000003f442dfae2880000000210876090143fca1390c850f4aa01223caeda1b160000505e00009a31c568074f8c1138000008d4620d1b480000000a5b00000000589000000000fc400000001a7000000000000000007540be8eee158d07d26ea701b8000027b00000001b32a2687b20210c4aa126269305028faa167642e879bc9d718fc0000a0ed22b80002a10aac0fa7134a458c036c0003436000020e512200004e441e32033044a0000888819c36dd5d0c3a298ff2f1e069800007758af403400000b28b2fa35e021b93bb375651269490a7820340bd684e172a15602b968ef977809da163e90c8ee3354474dc0fccd4e112c58ce92bcc2002cb2d24b7c8a2640285b5e443cc87356841c8299177f180967f8ef3071e04c0204adac99cc015056f50358e652ea054dd042192000800b74be69b38912853b098e000010da0000c391b9006af000002f800000000000b550000000035e4be7800000000000fbd1ac8111656784608aef22a17d38d468b0892b84de464e1035227a53c60364320376e4aa83089f511644703cd72c830273038803c69418090a60d0d420000149427143ea1e98116a08620000000402c2d34000060800002168b5e8fef37901e10ce081bd1c900218cf492130f36619c95c15af1eea2cacfb6084615f550d6154135232283fb8ca6148a1760427c0001027168e81d64cb8bb636634f2ca399eea1f9825a0c0ed4e800000000000115e0eb6454045782e600004f845cdc22d93fa60689bf0c3928941f30c94185400004d42bbf0000000078d8f0c8000399210f4af788ad0062759400000003e4e000000000003432000030a800015bd6258000193c97a47244e4ddca322765c7894cc70b32e47ca014094751f6e5fb0314cf892fbe4d603c014f71b720000c32533630200000715d2d52ffc053ae0082359b5669cc6ed1df5321829f07d8115b394e5cd015002ed104a33646cd800000001218000000000000000dbc8a3319bf502c2c1985203766240dcd5b0500007b5cb308f602c64245cf39
  | 79 => 0x1a0734c0414c193ccf510386194af7000000005b4a23fccd5913c588c90293038874000101c809f1de80000f551abe1b310000ce9800000001b5054394a4c08a7e4400000000000488437c048400470000dd8945b0d220f40c8a82da8298000000000000000026304f128b82d080b000017f83f06247c000000008030000a9505a9271e507c10b4a510a90000030b0f7815b05b78f9e5a9daff20ad43b19db31bf86dac1461719a79242bc40e8e4a80000a1c000007700004ebae5a9a57125c7d48000039d34b48152e640a7429c217c4727d5dc31a8636cefd0c329b8042ac02f092008e24fc4000000038e20904f7914c009407e6c0001325405e526cd5786df00000e7c23c96363e057facb88dcec0c8a725cbcc886b9f066bb032387d828b224a00000ab713145acc000000018781bce00007b1393e0000d130488202c804c0001b14063a8086a3b8000340a18d8cf0174000000128287c0000000246638d11e72e2148e8c950c6027d
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8be87d4d640400117b0fa9ac8080038794f53590100051fc2ae4b202000a3c855c9640400156902b92c8080028fa1472590100051ec28e4b202000a9e831c9640400153b06392c8080022fa1c52590100045ec38a4b202000a9e83149640400153b06292c808002a7a0e71590100054ec1ce2b2020038be87d45640400117b0fa8ac80800aaea0051590100055cc00a2b202000c3c54dd95404001878a8bb2a8080023be09765501000476412ecaa020028bc8759154040234790ab22a8080023d61b71550100065ab26e2aa020008f5861c5540400196ac838aa80800a2fe1d6490c100145e43ac8a18200087f855d262040230f90aba4c4080022fe11739881000c5e422e731020028bf8759242040230f90bbb2840800a2f21376508100043fc2aeca10201187c855d9420402d1ef02bb284080021f61b75508102261f326eaa10200087e8759542040010f90eb2a840800a2f21d64508100061fbaac8a102000c3c7559142040018eccbb8a84080031d59771508100b65b326e2a102000cb564dc542040011eb0c38a84080031d99471508100063ab28e2a102013cb6641c5420400196ac838a840800a3b61e628c81000c5e426ec99020008bf845d9320400317908bb264080a23de05764c8101a47dc02ec99020028f8805d9320400117b0dba264080030f997744c8100045f43ac899020008bc87591320400187eeab2264080030f1d5644c8100165c382c899020028dc8758d32040059b0e0b1a640800b3a1c2624c8100147643ac49902000cb664dc5320400196ac9b8a64080023d618714c8100065b320e29902000cb5641c5320404f9acc638a640800339988714c8100065d326e09902000cb964dc1320400117f08b94c2080062f21172984100065cb22e12082000e3441595410400756902b2282080062fa1176cc4100d45fc32e99882000c3e655d3310400717f0eb2662080022f61d64cc4100061f3aac99882000c3d75593310400195cc939662080032b59272cc41000657322e59882000cad645cb3104005974e0b24620800a3d61e618c4100065cb22e118820018bc84dd9210402917b0dba242080030f99774484100045f43ac890820038bc87591210400187eeab2242080030f1d564484100246f41eec10820008dd83dd82104005974e0b2042080032799273084100064eb24e61082000c9e645cc210400193ac8b984208003335ce620841000666b9ac410820028f58798421040019aae73084208002b960a610841000573c32421082000cb9645c0210400197709bb220080032e21376440100065dbb6e88802000cbb761d110040019b6edb9a200800336dd8734401000675bb6e48802000ceb761c91004001b90e6392200800a3ea1e614401000679bb4a28802000cf37654510040015e30d98a2008002dc6173144010
  | 1 => 0x8c8b98428809f35e1973085100066a432e610a2000d97645cc2144001b28c8b98428800374e017308510006e8402e610a20009d787d8c214404f5ad0db184288003a51936308510004eac38c610a2000e976418c2144001d28c8318428809eb5e1c630851013e6b438c610a2000ad58718c214404f9ab0e31842880023561c630851013f63410c610a2027ec58218c21440d1d8c4031842881a3b108063085100b65a324e410a2028cd4639c82144091d48c93904288003b118e7208510135f1404e410a20028f587d882144001d4ec9b104288003a91936208510006e2b9ec410a2000ec763d882144001d88c7b10428809ab961f620851016672c3ec410a2000ec673d882144001d8ae7b1042880023de1d620851009d5a422c410a2027ad48358821440015cd0c3104288003399d8620851000752320c410a2000dc5731882144001d88c63104288002b9a1a3208510257523246410a2027ec4638c821440015c90c9904288127a9191320851013f6231a6410a2026be0804c821440011bd0db9a808800317d9773501100062e32ee6a022000c9f64dcd404401d938c9b9a808800237a1873501100062fb28e6a022000c5c651cd404400193ec839a80880332719073501100646f43ec6a02200e8dc87d8d404401d1bd0e31a80880123721c635011000667b9ec4a022000ccc73d89404400199ee63128088003331cc62501100063a32ee2a022000ce462dc540440018e8ca38a80880032dd90715011000672310e2a0220029b48750540440055690ca0a80880072d1d94150110015d840282a022004cd4639c7304400117f08bb260880062f211764c11000477c12ec98220008ec825d930440019c8c5b8a608800335d8c714c11000672310e298220008de869cf204400193ec939e40880032719273c81100046e432e79022000c9f645cf2044001938c8b9e408800237e1f63c81100046ec3ec790220048df8718f20440011bb0e31e4088003339cf62c811000666b9ec59022000cce7318b204400199ae631640880033918a71c811000672312e390220018be84dd9204400117b09bb2408801237a0f76481100046ec1eec90220008bf845d9204400317908bb2408800237e0d76481100246e41aec9022000cb464dc520440019a8c7b8a40880032d19071481100066a318e29022000ce7621c52044055974edb2620880072e9d864c411014e6d3b6c78822004cda7618f10440599d4edb16208809b3a9d862c411000764318c58822000bd183087104400517d0faa2c8080030fdd7545901008c3f42ee6b20200087d85dcd64040230fd0a392c8080021f61472590100246f418e4b2020008dd831c9640400187eeb3aac808002abe09755901000556412eab202000ab4815d5640400187aea3aac8080028fa1773590100051ec2ee6b202000
  | 2 => 0x36250510136723b0c4a0a2000e64651894144001d48c83128288003b118c6250510156d9ba0e0a0a202e8bc865d33144001878caba662880132718d74cc5101545fc3ec998a20008bd87d93314400187cebb2662880030f5d764cc5100064f3a6c798a2000c9d74d8f31440591dd0d39662880032bd9272cc51000656324e598a2000ccf639cb3144009998c7396628809a3b21972cc51000657b22e598a2000cac645cb314400199ec6b9662880133318d72cc51016477c3ec598a20008ed87d8b314400195ce9b1662880032b5d362cc51013477c38c598a20008ed8718b314400195ce831662880032b5d062cc5100071a328c918a20028f4865ce31440019acedb1c6288003a5d90638c5100074a320c718a2028cd4639ca3144001d88c7b146288003399d8628c51000752320c518a2000ec46318a31440539b0e1b1a628809b3a1c0624c51000674316e098a20028f4865d131440053e100ba262880ab2d1db644c510156d8386c898a202ecb4761913144001c68ca32262880bb6c1c0644c5100266a3b6e698a2029cd476d8d3144053ba0e1b1a6288013351d8634c5100072bb28c698a2000e946418d314405bba0e031a62880b3391db624c510166f0386c498a2026ce4761893144001d48c83126288003b118c624c510136f0380c498a2004cd476cc93144061ba0e19926288002b5219324c5100266a3b26498a202fdd0704c931440053e50fb8262880a774dcc704c5100266a31ce218a2026cea7018b21440051ed0dba6428805b2d19374c85100b65a322e990a202acb676d93214405d96cec32642880038dd9464c85100071a328c990a20028f686dcf21440053e501b9e42880a33518d73c851014e6b3b6c790a2000e9464d8f214405b9acec31e4288003a5d9063c85100074a320c790a2028cd68718f21440519ab0e31e428800399d9762c851000752326c590a2016ab48458b21440515a906b16428809b399d862c851000752320c590a2000ec46318b214405d17d0dba242880030f19774485100045f43ec890a202a8bc87d91214400187eebb2242880030f1d764485100064fba6c690a2000c9c74d8d214400193ee831a4288003271d0634851016e6c380c690a2000caf74d892144001958e9b1242880b33a1c3624851000657ba0c490a2000cac7418921440019b0c7b82428800327d9273085100064e324e610a2000c9f645cc2144001938c8b98428800237e1f63085100046ec3ec610a20048df8718c21440011bb0e3184288003339cf620851000666b9ec410a2000cce73188214400199ae6310428804f2d1937408510004eac1ee810a20138f4865d02144027968c8ba0428804eada1b64085100071bb28c810a2000e346519021440013ab0f3984288003a5192730851013c7a432e610a20029f0805cc2144001d2
  | 3 => 0xaa122044c3c64dd542440010fd0fb2a84880021f21f65509100061fbaec8a122000c3c75d9142440018beebb1a8488003171d763509100062fba8c6a122000c5c7518d42440031dd0fb1284880031bdd76250910006363aec4a122000c6f7518942440018d8ea312848800a3da1b71509100063bb2ee2a122000c7465dc5424400196ec9b8a848805b2d19371509100066bb1ee2a122000cd463dc542440019cec5b8a84880033918b71509100063bb28e2a122000c74651c5424400196ec838a848804f2d19071509100066bb18e2a122000cd4631c542440019cec438a84880033918871509100045fc22ed99220018bc845db3244001968c938e64880133518e71cc91000673b14e399220028f4865c73244001968c8b8e64880133518d71cc91000c5f426ed19220008bd84dda324400117f08bb464880062f211768c91002476c38c519220018be84dd9324400117b09bb264880062fa12764c9100045ec24ec99220008bf845d9324400317908bb264880023de05764c9100047dc02ec99220018bc841d9324404f1e9023b2648800a3e200764c9100045f436e89922000c3c65dd1324407b938c7ba264880022fa1f644c9100045e43ec89922000c3f75d913244001878ebb2264880ab2e1c3644c9100064fba6c69922000c9c74d8d32440539b0e1b1a64880123ba1f624c91000657ba6c49922000cac74d8932440599d0e1b1264880032bdd0624c910006563a0c49922026ce87018932440051ed0db8a64880032dd93714c9100065a326e29922000cd763dc532440519a8c7b8a64880033918b714c9100065bb20e29922000cb4641c532440019aec638a648809f3518c714c91000673b10e29922000ce4621c532440011f50db8264880032ed93704c9100065c326e09922034cd863dc132440019d0c5b8264880022fe11760c91000c5e422ec1922004cd4639c432440019c8c5388648800a3d219710c91000672312e219220008f686dd64144001c68c9b2c82880031d9d865905100071a320cb20a2001ab686d92414400196cedb248288002ad2195490510014f8402e720a2000e9464d8e4144001d28c831c8288002ad21943905100b65a324e520a2000ea464d8a41440019ccec314828800399194629051000752320c520a2000ec46318a414400156d0d21482880038d107655051000d5b40ec8a0a202acb870d914144001d2883b1a8288003a510463505100075220ec4a0a2000ea44118941440051e90cbaa82880027920975505103563a3b6caa0a2000e3464d9541440d38e8ec32a82880038d19065505100355b436e8a0a2001cb476dd1414400356d0db2282880ab2d1db645051014e6a3b6c6a0a2000e9464d8d414405b9a8ec31a8288003a5190635051009e5a320e4a0a20009d5831c941440599c8edb128288003a919
  | 4 => 0x244001938c9b9ac48800327d9073589100064e320e6b1220008de87d8d624400193ee9b1ac488003271d363589100046f438c6b122000c9f7418d6244001938e831ac4880030fdd774589100061fba8e8b122000c3c751d1624400193ee9b9ac488003271d373589100064fba0e6b122000c9c741cd624400195ee9b92c4880032b1d3725891000667b9ee4b122000ccc73dc96244001968e9b8ac488003351cf71589100066c39ee0b1220008ef87588624400155f08b10c488002ab211621891000567c1ac43122000acc8358862440010ff0aba0c4880461f21574189100045fc22e631220018bc845cc624400155d09390c488002ab61272189100056741ce43122000acd839c862440014dd0a210c4880029b614421891000567418843122000acd8310862440015cb02210c4880032b9db641891000717b2ec831220008ed8799062440014dd0b320c4880029b61664189100056741cc83122000acd8399062440011df0eb20c4880029be1564189100053642ac83122000acf83590624400159906b20c4880032b9d8641891000717b28c83122000e2c651906244001d4b02320c4881afa9dc4641891035f53080c8312206bea410190624400199cedb18c488003a3d93631891000746326c631220008ed8798c624400155d09318c488002ab612631891000477c3ac63122000aaf8458c624400155908b18c488003339d8631891000747b20c63122000e8c6418c6244001d8b02318c4881a3b1dc4631891034763080c63122068ec41018c62440014df0aba0c4880029b215741891000573c0ae83122000a6e851d062440014db0a3a0c488002b3a0c741891000566c18e83122000ae6811d0624404d5cb023a0c48809abaa00741891000574c00e83122000e2f5495062440015cd032a0c488002b9606541891000716aa0a83122000aaf845cc624400155908b98c488002b9e05731891000575c02e63122026ae5811cc62440014dd0ba18c4880029b61743189100057340e863122000ae581d0c624404d5d501a18c488002ba60343189100057340c863122000ae58190c624400155f08b88c488002ab21171189100053742e823122000a6d85d04624400159d07b80c488002b360f701891000557c22203122000aac84440624400159f06880c488002b320d101891008c3f42eed212200087d85dda42440091bd07bb484880023760f769091000477416ed212200087f855da42440230f90abb4848800237e0d76909100246e41aed21220018ed8718a42440230fd0bbb284880021f61776509100246f41eeca1220008dd83dd942440230fd0b3b284880021f61676509100043fc2aeca12201187c855d942440011bf06bb284880123720d765091000477c12eca1220008f7815d942440230f90a3b2848804e3d20476509100043f436e
  | 5 => 0x80033a1cb7058d100046fc3ac631a2000a9f8458c634400153908b18c688002b3e096318d1000566412c631a2000c9e76d906344001c3ecbb20c6880023761e6418d100052f42cc831a2000a5d85990634400159d05320c688002b360a6418d100046fc3ac831a2000a5f8559063440014b90ab20c688002b3e096418d1000566412c831a2000c9e761906344001c3eca320c688003871946418d100074ac08c831a2000e97645c46344001d28c8b88c68800387d525418d100070eaa0a831a2000ad681d0863440015ab03a10c68801237a1c4218d100046ec388431a2000a5e8510863440014bb0a210c68800297a174118d100052ec2e8231a2000a9f84440634400153908880c6880021fe157690d1008c3e42aed21a20048dc835da43440011df04bb486880023b2097690d100063a32ce321a2000cb7649c643440099a8c738c868800a3d2197190d100063a32ae321a2004cd4635c643440230fd0bbb286880021f6177650d1000477416eca1a20008ed82dd943440010ff0abb286880461f2157650d100046fc1aeca1a20008ef825d943440011d904bb286880122fa1f6450d1000c6f43ec6a1a2000a6e8510b62440014db0a216c488002b3a0c42d891000566c1885b122000e2f65d9362440014dd0b326c4880029b61664d89100056741cc9b122000acd8399362440014df0ab26c4880029b21564d891000567c1ac9b122000acc835936244001c5eca326c4880038b19464d891000752c08c9b122000e8f64d8f6244001d18c9b1ec488002aba1263d891000556c24c7b122000aaf8458f624400155908b1ec488003a3d9063d891000746320c7b122000ec58118f6244001d4ec8b8ec488003a919171d891000763b1ae3b122000ec4635c762440014dd0bba6c4880029b61774d891016572c0ee9b122000a6e859d362440014db0b3a6c488002b3a0e74d891000566c1ce9b122000ae6811d362440595cb023a6c4880038bd5254d891000716aa0a9b122000aae84dcf624400155b09b9ec4880b2b960773d891000574c06e7b12202cae5811cf62440014dd0ba1ec4880029b61743d89100053742e83b122000a6d85d07624400159f06b86c488002b320d70d89100061f3aec93122000c3d75d92624400187cea324c4880030f5d464989100064fb24e73122000c9c649ce624400193ec8b9cc4880032719173989100064f3a6c73122000c9d74d8e624400193ce831cc488003275d06398910006573a6c53122000cad74d8a624400199ce7b14c488003335cf62989100061f3ace93122000c3e755d2624400187aeaba4c488003279d273989100064eba4e73122000c9e745ce624400193ae8b9cc4880022fa1f64589100061fbaec8b122000c3c75d91624400117d0e322c4880030fdd464589100061e3a8c8b122000c9f64dcd6
  | 6 => 0x71b28ea3b222000a9e83dc3644400153b07b86c8880ab8e94350d91100061e326eab222000c5f65dcd6444001938c9b9ac88800317d9473591100064e320e6b222000c6f65dc96444001958c9b92c8880031bd94725911000656320e4b22201187e87dd5644400187eebba2c8880030f1d774591100246f43ee6b222000c5f75dcd64440018b8ebb9ac88800327dd373591100062fba8e6b222000c5c751cd644400193ee839ac8880031bdd77259110006363aee4b222000caf74dc9644400199ee7b92c888003331cf725911000637ba8e4b222000c6c751c9644400195ee8392c88800333dcc725911000666398e4b222000c7475dc564440019c8e5b8ac8880030f9db65191100071ab8eca32220008bd87994644400147d0b328c888002a7a0e65191100054ec1cca3222000aae82994644400155b05328c8880022fe1d65191100054fc1aca3222000a9c83594644400155f04b28c888002ab20965191100061f3b0ca3222000e357119464440d9c6c20328c8881b38d04065191100246f41eecaa220008dd83dd954440011dd05bb2a8880023b60b76551100061e2a4ecaa220008bf845d954440011bf06bb2a8880123720d765511000477c12ecaa220008ec825d954440011ef02bb2a8880030f150765511008c5f43ec8aa22011a3e85d9154440014bd0ba1ec6880029761743d8d100070fb2ec9b1a2000a5e8599363440014bb0b326c688002b3a0a64d8d1000566c14c9b1a2000a5f8559363440014b90ab26c688002b3e0964d8d1000566412c9b1a2000e1f651936344001c38ca326c688003a560464d8d100052f428e9b1a2000a5d851d363440015ad023a6c6880a6b560474d8d1014d6d400e9b1a2000ad9801d36344001c3ea92a6c6880038755054d8d100054f426e5b1a2000a9d84dcb63440535ab03b96c688002b660372d8d100046f43885b1a20008dd8710b63440014bd0a216c6880029761442d8d100054fc22e3b1a2000a9c845c7634400159f04b8ec688002b320971d8d100052f42e83b1a2000a5d85d076344009938c6ba4c6880030f9d76498d100061ebaec931a2000c3e75192634400187aea324c688003279d36398d100064eba6c731a2000caf649ca6344001958c9394c68800333d8e7298d100266631ce531a2000caf645ca6344001958c8b94c68800333d8d7298d100266631ae531a20008be87d91634400187eebb22c6880030f1d76458d100045f438c8b1a2000c3f751916344001878ea322c6880032bd937258d1000656326e4b1a2000caf641c96344001958c8392c6880030fdd77458d100061fba8e8b1a2000c3c751d1634400193ee9b9ac688003271d37358d1000657ba6e4b1a2000cac74dc9634400199ee7b92c6880032bdd07258d10006563a0e4b1a2000ccf731c963440019c8e5b8ac68
  | 7 => 0xde831da42c40011bb063b485880f6a7a0f6490b1008c3f42ceca16200087d859d942c40091bd073b285880023760e7650b100043fc2aeca16201187c855d942c40051eb0c38a858800a3d61a71ccb100266b31ce399620008bf845da32c400317908bb465880123b61c628cb1000c5f424ec99620008bd849d932c400117f08bb265880062f211764cb100064e3a2c699620048ee87d8932c400959d06312658809b3a1c0624cb100147ac30e29962027cd6631c532c40019aac638a65880d33698f704cb100147ac34e219620028f586dd641c400517d0fb2283880025d6177650710004f2412eaa0e2000bb180d9141c4027968c839283880027560c72507100147ac36e918e20009b584dd931c400136f08bb6438805aad21176c87100b65a326e990e20168f7865d321c40511ef0cb9e438805aad21162c87100147ac36e810e20009d583dd021c4027968c8ba0438800a3d61b73087100066abb4e610e2027cd6635cc21c40019aaecb98438800335e1973087100066a432e610e20008f78758821c402756908b104388002b9e1d620871000673c3ac410e2000ea78458821c4001d4908b104388003b19cd620871000762b9ac410e2000ae5868c821c40015cf0c990438809fb198d3208710135f04026410e2000dd1735c021c400196ac838a818800a6d21d415031000e5a3b282a0620298df8758f30c40591df0eb16418809a3ba1e624831000672b10e290620028bc8759154840234790ab22a9080031d59771552100145e43ac8a1c2000cd7815ce62840019a902b9cc50800336e017398a1017e6c402e7314202fcd7105ce628405f9aa20b9cc50801237a0f7690a100046ec1eed21420028bf8759242840010ff0abb285080461f2157650a100246e41aed99420028ed8798a328405f1bb07bb265080022fe11764ca1000c5e422ec99420028f8805d9328400959d07312650800b3a1c2624ca100147643ac49942002ce87058932840019ccc5b8a650809f3518c714ca1016c6fc3ac798c20268ef8758b21840591dd0f31243080030f5d754d91100055ac0ea9b22200087f855cf64440230f90ab9ec8880461fa1672d91100043ec2ce5b2220048de839cb64440011bb07396c888002a7a0e65d91100054ec1ccbb222000aae82997644400155b0532ec8880030fdd675d91100061eba8ebb222000ab6811d7644405556b023aec8880028fe1573d91100051e42ae7b22202aab5811cf644400117d0fa9ec8880022f61f53d91100070f29ea7b222000a3e85dcb644400147b0bb96c8880aaad60772d91100051f42ce5b222000a3d859cb644400153d07396c888002a760e72d91100045f438a5b2220008bd8714b644400153d06296c888002a760c52d91100051fc2ae3b222000a3c855c7644405517d0fa8ec8880022f61f51d91100
  | 8 => 0xabb286900461f2157650d200046fc1aeca1a40008f7815d943480011e902bb286900023ee017650d200145fc3ac92124022a3c85592424807b53906b248490002ad20564909200061e3aec8a124000cb7641c54248027968c838a84900133618d70cc92001476432e71924000c9c74d8d32480019aec638a649009f3518c714c9201a66c31ee0992403dcac76dd132480b9958ec3a26490002b3219434c920146723b6e29924027ce4761c532480699d0edb82649000b3a1d8704c920006b5ba8e09924000da8741c13248001bc0e238264900029da1741d85200047bc3ac230a4000ab48458461480015a906b08c290013339cd32185200053b42e8230a4000cb5741046148001968833b282900032d104765052002476414ed98a4000cce764cb3148001b1ae899662900032d9d361cc5200065b3a0c398a4000ce5721873148001d8a6430e6290003331d9324c5200045fc22ec18a40018bc845d831480019cae430862900032d1d361485200065a3a0c290a4000c9f641cd4048019938c839a80900be3761f63cc1200045fc22ec98240018bc845d930480055d10c99640900d3b218d32c81200047bc0aecaa040008f4815d954080051790eb22a8100468f215645502000476c30e4aa0406dd2c541c954080051f100bb2861000a2f21d6450c200146e43ac6a184000cdb805ce620805f9b100b9cc4100d76910871508200246e41aed9904030cd8305db32080051db0f31464100be3760f764c82017e6c186ec9904004ace8398932080059d0e131264100bfb20c2624c820006e8180e299040308df8758c320800317d0fba2c2100030fdd774584200061fba8e8b084000c3c751d161080051eb0f30c8210006ad21161904200043fc2aeca08401187c855d9410800156902b2282100d769104725042000d5a424c2a0840028f487585410800356908b0a82100123b60976cc4200264f31ae99884000c9d7458f310800199ac739662100022fe11764c42000c5e422ec9884002cf070585310802d56908b0e42100b2ba20163884200066ab9cc21084013ab48458421080019aae6b0842100d6e9211210842000573c0ac61084026ae88058c21080015cb0d98842100d6e9a13310842000762b1e621084000ae5860c421080d1f8060188421001237e1d73d93100246f418e4b2620008dd831c964c40091bd073b2a9880023760e765531000477414ecaa620008ed829d954c402317d0fb22a9880468fa1764553101f54f41ec8aa62000cf2715c363c40014bd0ba1ac78800237e1d6318f100147ac34e321e201187e85dd943c40010fb0bbb287880023760e7650f100245f43ec8a1e2000c3f75dd162c400187eea3a2c5880030f1d47458b100065bba0e2b162000cb4741c562c40011df0eb10c5880021fe157690b1008c3e42aed21620048
  | 9 => 0x42586200053b42884b0c4000a758510961880015ad06212c310002b560c42586201447bc3a64b0c40278f4874c9618800156f08992c310002ad211325862000579c0264b0c4002af0804c961880091bd07bb483100023760f76906200147ac3cc320c40028bc84dd9418800196883bb283100032d10576506200071a20acaa0c4000ab48159141880018dccbb9283100031b994725062000656b20e4a0c4038da4411c941880035690930a831000a3d21d615062000d5a422c2a0c4000ce472585418800317d08bb663100022fe1974cc6200061f32ae998c40008bf87593318800117b0eb2663100030f9d564cc6200061ebaac998c4000cae649cb318800195ac939663100032b99172cc62000656b22e598c4000cb674987318800196ae930e6310003399ca61cc62000672b94c398c4000cb674587318800196ae8b0e6310003399c961cc62000672b92c398c4000ce47258531880019e4c2b8443100022f61b74486200061f32ee890c40008bc87591218800187eeab2243100030f1d564486200065bba4c290c4000cb474985218800196ee8b0a43100032d1d1614862000678b0ee090c4000c9e649cc218800193ac939843100032799173086200064eb22e610c4000cd67358421880019aae6b0843100e2e9211210862000666bb2e610c4000be1809c42188001d8ce6b084310003b15cd610862000572c366210c4038ba684cc421880015cb0c1884310003365da73c82200066cbb2e79044000c3d75d5364480010ff0ab9ec8900461f21573d91200043fc2ae3b22401187c855c76448001938c839ac8900032d190715912008c3f43eeab224000c3c75dd164480091bd0fb9ac89000317dd773591200062e3aee6b224000c5f751cd64480018b8ea39ac89000327dd07359120006363aee4b224000c7775dc564480018e8ebb8ac89000335dcf71591200066a39ee2b224000c77751c564480018e8ea38ac8900032ddd071591200066bb98e2b224000cd4731c564480019cee438ac8900032d95071591200065a210e2b224000cd873dc16448001878a93b2a8900022fe1176551200046fc1aecaa240048dc835d954480011df04bb2a8900023de0576551200047a40aecaa24000c3c541d954480231790eb22a8900468f21564551201f54e41ac8aa24000ab48159154480014bd0ba1ec6900022fe1171d8d2000c5e422e3b1a4000c3f75dd1634800187eea3a2c6900030f1d47458d200064e3a6e6b1a4000cb774dc56348001968e9b8ac6900032ddd07158d200065a3a0e2b1a4000cd7731c563480019cee438ac690003358c07158d200066a180e2b1a4000cbb74dc16348001970e9b82c6900033cdc77058d200067838ee0b1a402fcda83dc163480011bf0eb18c690002a72116318d200056a40ac631a40028ec865ca43480010ff
  | 10 => 0xb244000c3f75d5164880230fd0bb9ac9100021f617735922008c3f42ee2b24400087d85dc5648800187eeb3aac910002a7a0e75592200054ec1ceab244000aaf825d5648800187aea3aac9100028fa1773592200051ec2ee6b2440008be87d4d648800117b0fa9ac9100038794f53592200051fc2ae4b244000a3c855c9648800153f06b92c910002a720d72592200055bc0ae4b244000ab4815c9648801517d0e292c9100022f61c52592200054f418a4b244000a9d83149648800147d0bb8ac9100028f61771592200054f41ce2b244000a9d839c5648800155f04b8ac9100032d5c471592200045f43ea2b2440008bd87d4564880055750028ac910002ae60051592200061e2a6ecaa44000c3c545d954880051790eb22a9100468f215645522000656b20e4aa4406ed2c541c9548800317d09b8ac7100022f6137158e200145fc3ac921c40028bc8759143880010fb0dbaa85101130f9937550a202243f43acaa14405f87c87595428800187eeab2285100030f1d56450a200047ac36e2a144000c7665dc542880018eacbb8a851005b2d9937150a200065ab26e2a1440008f5861c542880018ecca38a85100031d5947150a2009e5b320e2a144000cb5641c54288071b488438a85100032e5937050a2019c7dc32e199440008bd86dd1328800187ccbba265100f62fa1d644ca202e45e43ac89944000c3f755913288001878eab22651000b2e1c1644ca200166c382c699440008f586dc5328800196cc9b8a65100032d593714ca200047ac30e29944000cb6641c5328800196ac838a65100032e993704ca200065cb26e09944000a7685d0661880014eb0ba0cc3100032d5d041986200056b41ee930c4000ad583dd261880014ed0b3a4c3100029d61674986200065aba0e930c4002af2801d261880015e3003a4c3100038dd52549862000573c12a930c4000ae4825526188001c6aa82a4c310002ada1273986200055ac24e730c4000ae5829ce61880014ed0ba1cc3100029d61743986200b47bc3a8530c40138f48750a61880014ef0aa14c3100029d21542986200053b4288530c4000a758510a61880015ad06214c310002b560c42986201447bc3a6530c40278f4874ca618800156f08994c310002ad211329862000579c026530c4002af0804ca61880014ed0ba0ac3100029d61741586200053b42ce8b0c4000a75859d161880015ad073a2c310002b560e745862000573414e8b0c4000ae5829d161880015cf04ba2c3100032d5d074586200071baa4a8b0c4000e3554151618800156d0939ac310002ad612735862000572c14e6b0c4000ae7825cd61880014ed0ba1ac3100029d61743586200055bc22e4b0c4000ab4845c961880015af06b92c310002b520d72586200b47bc3a84b0c40138f48750961880014ef0aa12c3100029d215
  | 11 => 0xc800153b09b8ac790002b3a0b7158f200054f424e2b1e4000a9d849c563c80015b30138ac790002b6e017158f200052f42e82b1e4000a5d85d0563c800153f08b82c790002a72117058f200056bc0ae0b1e4000ad4815c163c80011bf0eb18c79001237a0e7690f2001476c34e521e4004cce639ca43c800999cc6b9487900023760e7650f2000c6e43ac6a1e402fcd87058d43c80018beeb31a8590003171d66350b200062fbaac6a164000c5c7558d42c80019acc7b8a85900033558f7150b200066b318e2a164000cd5631c542c805f9b4e0b1c6590013335da638cb2017e66bb2c7196403dc9e63dd132c800193ee8b1a6590003271d1634cb2017e6c382c69964028cd663dc532c80019aac7b8a659009f3598c714cb200066ab18e2996403de8e63dd132c80b9d1cc63a26590012b361b734cb2017de5406e69964030dc87098d32c800199eecb1a65900bf721c1634cb2000567c3286996402fbc88050d32c8051d8cc7b8a659000339dd8714cb2013f63318e29964000ceb76dc132c8069d94c7b8265900036add0704cb20006d43a0e09964033eca631c132c8001bc6e23826590003781c4704cb200064f3a4c7b0e4000c9d7498f61c800193ce8b1ec390003275d163d8720165744026530e40008dd8798c61c80011bf0eb18c3900023de1d611872008c3f42eed20e400087d85dda41c80230fd0b3b483900021f61676907200246f41ced20e40008dd839da41c80091bd063b283900023760c76507200074a20cc6a0e4000e944158d41c800993cc6ba66390003279d163cc7200064eba2c798e4004cce639cb31c800199ac739663900133398d72cc72000666b1ae598e4000ccd764cb31c8001b1ae899663900062fa13768c7200045ec26ed18e402fcda7058e31c805f9b0e0b1a639000333dd9324c72017ee43826498e4034cd8305d831c800999cc6b9063900d3720c1720c7200064fba4c690e4000c9c7498d21c800193ee8b1a4390003271d1634872017c6ec34e610e40308df865cc21c80011bb0f318439000237e1d63087200046ec36e6a0640008dd861cd40c801d1bd0f31a81900123721e63503200746f43ac6a06400c8dc8758d40c800195ac839281900133398d72cc32017ee4182e59864034cda635db30c800199ac7b9261900d33698d760c32017f4d3a2c6186402fe997458c30c805fd94e4b1861900bfb25c9630c32017f6938ac6186402fed17158c30c8069b94c6b9061900037258d720c3201d5cc422641864000bd0814c830c805f7970e990619000372e1d320c320185e5c32641864033ecb864c830c8001b92ec99061900bfb25d9320c320007c5c22641864000f88844c830c805ff14e899061900bfe25d1320c320007e1c0a641864000fc0814c830c805ff84e299061900bff05c5320c3200145f43ea8
  | 12 => 0x12b520d725843001578402e4b086004ad6831c9610c04f9a8e6392c218012b5a0e42584300056ac1c84b0860008f787509610c0011e90ea12c2180029de1542584300053a42a84b086000a7685109610c0014eb0a212c218012b5a0c42584300056ac1884b086000cd7874c9610c0015a90e992c2180033521d32584300074bc2264b086000e94844c9610c009d8f04992c218003b1dc932584300076239264b086000ed3804c9610c05fda100992c2180bfb1c81325843017f6290264b086000c9d645ce410c00999ce6b148218003335cd62904300147ac3cc32086000cd573986410c00517909bb282180032d10776504300065a20aeca086000e3441595410c00156902b2282180032759373504300075220cc4a086000ea441589410c0035690930a821800a3d21d615043000d5a422c2a086000cd773585410c0013b700b946218003355c9618c4300264f39ac99086000c9d645cf210c00199ae73164218013359cd61c84300066ab9ac3908600c99e84dce210c0013b301b9c4218003335d9328843000746b22651086000cd773586210c001d8a64b0c421800276e0d708843000674b12e11086000dc9325c2210c0019e4c2b8442180062f21376484300045fc22ec90860018bc845d9210c00117b0dba242180030f99774484300045f43ac890860008bc87591210c00187eeab2242180030f1d5644843000657ba4c49086000cac74989210c00195ee8b1242180032b1d1624843000667b9ac49086000cb774985210c001968e930a42180032ddd161484300065a3a2c29086000cd773585210c0019d2c5b8242180033c58770484300046ec1aec1086027cd4315d8210c00993ce6b2042180032799173084300064eb22e610860279d4815cc210c00199ae73104218013339cd620843000666b9ac41086000ccd764c8210c001d1ac89904218003355ce61084300266b39ac21086000cd573584210c001d8a64b08421801237e1d73d932008c3f42ee2b26400087d85dc564c80091bd073b2a9900023760e76553200047b40cecaa640008f5819d954c80091bd063b2a9900023760c765532008c5e43ac8aa64011a3c8559154c80014bd0a324c790002976146498f200070faa4a931e4000e1d5415263c80091bd0e214c7900023761c4298f200052f4288531e4000a5d8510a63c80014bd0ba0cc790002976174198f200052f42e86b1e4000a5d85d0d63c800317d09b8ac7900022f6137158f200046f43ec8b1e40008de8719163c80014bd0a322c790002976146458f200052f42ce8b1e4000a5d859d163c80015ad033a2c790002b56067458f2017d6d404e8b1e4000ad9809d163c80015b700ba2c79000387d525458f200070eaa0a8b1e40008de8710963c805f1bb0e212c79000297a144258f200052ec2884b1e4000a9e84dc563
  | 13 => 0x567418e2b106026ce8701c5620c0014dd0ba0ac4180029b61741588300256741e82b106000acd83d05620c0055d50020ac418002ba60041588300262f39acb210603da9c83592420c00993ce6b2484180f25721573908300062eb2ae72106000c9d645ce420c0051db0f3148418003335ce629083008c3e42eeca10600087f855d9420c0230f90abb284180023de0576508300047a40aeca10600087d86dd5420c08987cc9baa84180021fa1d65508300043e43acaa106000c3f75591420c001878eab22841800327593735083000637bacc4a106000c6c75989420c0051d90eb1284180031bdd56250830006363aac4a106000ccf73589420c0011eb0db8a84180031d99771508300063ab2ee2a106016cb664dc5420c00196ac9b8a84180033998b715083000672b16e2a1060008f5861c5420c0018ecca38a84180031d594715083009e5b320e2a106000cb5641c5420c0019ccc438a84180033958871508300065cb26e0a106000ce962dc1420c05f9b0e1bb2641817267a1f744c8300068fba8e89906000d1c751d1320c001b30e03a264180323721d644c8300664fc3ac89906000a9e87591320c0015390eb2264180332721d644c8300644e43ac89906000e1f75591320c001c38eab22641801327dc9644c83002747b92c8990602fe9870591320c05fd1e40b2264180bfa3481644c83000747ba4c49906000e8c74989320c05fd90e13126418003651d3714c8300074ab26e29906000ec662dc5320c001b2ee838a6418003651d0714c8300074ab20e29906000ec6621c5320c001ba0e038a641809e75e18714c83013ceac30e29906000cd5861c5320c04fb2cc838a641809f65590714c83013ee3310e29906027dc5621c5320c0019acc038a641809f74980714c830006cdba6e09906000d9874dc1320c001d32c9b826418003b298b704c830006e9b8ee09906000dd071dc1320c05fb34c9b8264180bf66593704c83017ee5316e0990602fdc962dc1320c05fba4c3b8264180bf74587704c8300045fc22e530860018bc845ca610c0014ed0ba0cc2180029d61741984300065aba0833086004ad683dd2610c0014ed0b3a4c2180029d61674984300065aba0e93086002af2801d2610c0015e3003a4c2180038dd5254984300071aaa0a93086002af280dca610c00156f08b94c218002ad21172984300256b418e530860008f78750a610c0011e90ea14c2180029de1542984300053a42a853086000a768510a610c0014eb0a214c218012b5a0c42984300056ac18853086000a7685d05610c0014eb0ba0ac2180029da1674584300053ac2ce8b086004ad6839d1610c0015ab073a2c218012b520d74584300065aba0e8b086000e3754951610c001c6aa82a2c218012b520f72584300256b41ce4b086000ab7845c9610c00156908b92c218
  | 14 => 0x782584218c001d8a64b084318002f160831086300246f41ce5b22600087f855c7644c0230f90ab8ec89800237e0d765513000477c12ecaa260008ec825d9544c0011ef02bb2a8980023d205765513008c5f43ec8aa26011a3e85d91544c0011df0eb10c498002b920562189300045fc22e231260018bc845c4624c0010ff0abb484980461f215769093008c3f42ceca12600087d859d9424c0011ed033b284980023d606765093000673b10e29926000ce4621c5324c0019d0c5b8264980023de1d611853000572412c230a60008bf845c8614c00317908b90c2980021fe15769053008c3e42aed20a60018be849d9214c00117b093b242980022fe11760853000c5e422ec10a60048de831d8214c00199ae7b104298003355cf61085300764e326e6a0260028be87d51640c00187eebaa2c818012a7a0f545903008c3f428e4b20600087d851c9640c0031bb06392c8180461fa1771590300043ec2ee2b206062c9c73dd5640c00187eeb3aac818012a7a0e75590300054ec1ceab206004a9c835d5640c07d938e6baac8180030f5d475590300254e41ee4b206004a9e839c9640c07b938e7392c8180028fe1572590300051e42ae4b206004a9c835c9640c00156f02b92c818002ad20572590300155c402e4b206000a3e851c9640c00147b0a392c818012a7a0c72590300654ec18e4b20605cc9c731c9640c00117d0e292c8180022f61c52590300254f418a4b206000a9d83149640c00147d0bb8ac8180028f61771590300254f41ce2b206004a9c835c5640c00196ae238ac8180022fa1f51590300045ec3ea2b206002aba80145640c0015730028ac8180030f15376550300061e2a2ecaa060048dc835d9540c0051790eb22a8180468f21564550301f54e41ac8aa06000c9d64dcd540c0010ff0aba4c4180461f21574988300047bc0ae931060008f4815d2620c0014dd0a214c4180029b61442988300045fc22e331060018bc845c6620c00959d07ba4c4180029be1574988300053642ae93106000ae7815d2620c0015c902ba4c4180029ba14749883000536c28e93106004ace831d2620c00159b063a4c4180038bd52549883000716aa0a93106004ace83dc6620c00155f08b8cc418002ab211719883002567418e33106000a6e85d06620c0014db0ba0cc4180029ba14425883000536c2884b106004ace83109620c0055d5013a2c418002ba602745883000537c2ae8b106000a6c855d1620c00959906ba2c418002b9e0574588300057240ae8b106002ae8805d1620c0014dd0a3a2c4180029b614745883002567418e8b106000acd831d1620c001c5ea92a2c418012b3a0e545883000566c1ca8b106000e2d54151620c0055d50138ac4180b33a1c2715883000557c22e2b106000aac845c5620c00959906b8ac41800aba201715883002
  | 15 => 0x83b242a000317dd763485400062e3aec690a8000c9f74d8d215001d938e9b1a42a000317dd463485400062e3a8c690a8000c9f7418d2150019938e831a42a00021fe15760854008c3e42aec10a80008df835d821500091b906bb042a00461fa1476085400043ec28ec10a80048de831d821500011bb063b042a000237a1a73085400046e432e610a80008df87d8c21500011bb0fb1842a001237e1c63085400046ec38c610a8000cad74188215000196ae830842a00063e21970085400061fb2ee8a828002a3c865515050003878ecaa2a0a000ace20154541401e46f43ec6a82800e8dc87d8d50500811bd0e31aa0a00123721c63541400070eaa0c6a82801187e85dc564cc0010fb0bb8ac9980462f61376553300045fc22e331660018bc845c662cc00317d0fba2c5980030fdd77458b300061fba8e8b166000c3c751d162cc00196ee9b8ac5980032d1d37158b3014672c16e2b166000cb7741c562cc001968e838ac59809f35a0c7158b300066ac18e2b166000cd6301c562cc04f9a86038ac5980032edd37058b300065c3a6e0b166000cf371dc162cc0019e0e3b82c5980021fe157690b3008c3e42aed216600087f855d942cc0230f90abb285980023de057650b300047a40aeca1660018be84dda21cc00117b09bb443980022fe11764873000c5e422ec90e60028de83dd821cc00999ce6b104398002b9e05620873000477c12ecaa460008ec825d9548c0011ef02bb2a9180023d20576552300145e43ac8aa46011a3c85591548c0018bacbb9aa918102572157390a300043fc2aeca14601187c855d9428c0011ef02bb285180023d2057650a300746fc3ac999460348fb865c2328c0059d0e131265180bfb20c2624ca30074cf43ee89946000d1f751d1328c001a38ea3a26518003661c0744ca300764e3a2c89946000d9474dc5328c001b2ee838a6518003651d0714ca30006e8380e29946000cd6861c5328c0019ab0c38a651800356dd7704ca300045fc22e530c60018bc845ca618c00317d0fba2c3180030fdd774586300061fba8e8b0c6000c3c751d1618c00195ee9b92c3180032b1d3725863016672c0ee4b0c6000caf741c9618c001958e8392c31800333a0c725863000666c18e4b0c6000c9f74cc9618c00193ee8992c318003331c932586300056a40a64b0c60028f587986418c00356908b0c83180021fe15765063008c3e42aeca0c60008ef825d9418c0011d904bb28318002ad205645063000d5a424c2a0c60028f487585418c00356908b0a831800b3c1c1614c630074ce422e418c60018be84ddb218c00117b09bb6431805aad21161c8630074cf426e710c6000ccd764ca218c00117f08bb243180062f211764863000666bb26410c6000cd573984218c0015cb05308431804ead21161086300066ab9ac210c6000ae
  | 16 => 0x2189400043fc2ae2312801187c855c462500011bf06bb4a4a00123720d76949400664e3a0c72928070e1e5418e52500091bd07bb2a4a00023760f76549400047b40ceca9280008f5819d95250003179083b2a4a00064f21d54549400061e3b2a8a928000c9f74d8d525001d938e9b1aa4a000327dd063549400664e3a0c6a928000e1d5418d52500019aec7b8aa4a00033518f71549400069aaa0e2a928000cd7631c552500019a8c638aa4a000a2fa1b75909401161e32eeb212800093f855ce425007b938c6b9c84a0107279db639094022e4f3b0c7212803dc9d8718e425000193eea31c84a0003275d463909402e64f390c7212800ce8e7218e425001317b0fb1484a0003a318c62909401745e432e3212800093f855c64250009938c6ba664a000a2fa1b748c94008c3f42cec992800087d859d932500011ed033b264a00023d606764c94000c5e420ec992806fc5c63dd5325007b938c7ba264a000317dd7634c9400062e3aec69928000c9f74d8d325001d938e9b1a64a0107361c3634c94000cce43a869928004a9c8650d3250001938eca1a64a000335d8f714c9401466a31ee29928000cd7631c5325004f9a8c638a64a00063ea1b704c9401a66c31ee099280048de839cb61500011bb07396c2a00031d5d751d85400055ac26a3b0a80008de87d8d61500018beebb1ac2a0003171d763585400046f438c6b0a8000c5f7518d61500018b8ea31ac2a000333d8f72585400066631ee4b0a8000ccf631c96150001998c6392c2a00023de1d61185400053a42ac230a8000ae4825846150023878eaaa0c2a0002ade0554185400043fc2ae430a801187c855c8615000156b09a88c2a0002ad61051185400071aaa0a230a8000af18014461500011bf06bb4a2a00123720d76945400053ac0ecb28a8000c3f655d2515000327f0eaa4a2a00468f21954945400061f3b2a928a8000e1d5418e51500091bd07bb2a2a00023760f76545400145e432eaa0a80009ac825d54150083938edb1a82a0117271d86350540004cec18e4a0a80078be871854150001d2ec630a82a0003a518c615054003d5b438c2a0a8000cb6871854150001968e430a82a00122f21276cc5400262e31aeb98a8004c9c635d331500018bcebb1e62a0003175d763cc5400764f3a6c798a8000c9d74d8f315000199ec739662a00133318e72cc54000667b1ae598a8004ccc635cb31500230fd0a3b462a00021f614768c5400764f3a6c718a8041cda70d8e31500031f10cb8462a00123720c764c5400145e432e898a80418df835d831500011bf06bb642a00123720d76c85400145f436e990a8000cb77418721500011bf06bb442a00123720d76885400664f3a0c710a8000c9d7418e21500091bd07bb242a00023760f764854008c3f42cec90a800087d859d921500031790
  | 17 => 0xc804ba748558421900019aae6b0843200062f21173d954000c5f424e5b2a80048de839cb65500011bb07396caa00062f21171d954000636328e4b2a8000c74651c5655000199ee7b92caa0003331cf725954000657ba0e4b2a8000ccf731c96550001998e6392caa000335dcf71595400066a39ee2b2a8000ce772dc565500019c8e5b8acaa00032ddd071595400066bb98e2b2a8000cd4731c565500019cee438acaa0003391c8715954008d1f436caaa2803ec9c63dcd54500cb878ca392a8a00026760c72551401745f436e2aa28000c5d75d4f635000153b09a9ec6a00021fe1571d8d4008c3e42ae3b1a80008ef825c763500011d904b8ec6a0002b3e0965d8d4000566412cbb1a8000ad78159763500015a902b2ec6a0106a721954d8d400070e32aa9b1a8000c5d751d7635001d53d083aec6a0106a761075d8d400052f42ee5b1a8000a5d85dcb635008353b09b96c6a0002b5a0772d8d400056ac0ee5b1a800ead980dcb63500011bd0e296c6a00023761c52d8d400754f420a5b1a8000a9d8414b63500014bf0ab8ec6a00029721571d8d400054fc22e3b1a8000acf825c7635000159904b8ec6a000297a1471d8d400052ec28e3b1a8041a9d841c7635001d5b30038ec6a003aa7a1351d8d400054ec26a3b1a8041e5a50d4363500011bf0eb18c6a0012a72127618d400046ec3cca31a80008df87594635000159f04b28c6a0002b32096518d400056bc0aca31a8000ad481594635008b5390caa0c6a000387d955418d400070e32aa831a803ea9f8755063500c553f0aaa0c6a003387e155418d401f70fbaaa831a803ee1c75550635000153904aa0c6a0032a7a135218d400054ec26a431a8000e1d54d4863500091bd0e290c6a00023761c5218d400654f420a431a8000a9d8414863500e3c3ca8290c6a0032a7a135118d400054ec26a231a800ca9e84144635000153b08288c6a0003875505118d4022d6d400a231a8000ad980144635001953d09a80c6a0002a76135018d400070eaa6a031a80048dc835da535000327f0eaa4a6a00030f9d95494d400058fc1aa929a803ee1c6355253500231bd0fb1aa6a000a2f2197550d40014dc402eaa1a8041c9c76d8d4350009938ec31a86a00ba2fa1b7150d400049ec2ee2a1a8041d9b731c143500cb17f0eaa6c4a00470f1d554d894000556412a9b128000aad84d4b6250001c5aa9a96c4a0002ab61052d8940377172a0a5b1280048de839c762500011bb0738ec4a000237a1f63589400062fbaec6b128000c5c75d8d62500011bd0e31ac4a000317dd463589400062e3a8c6b12803acdb7018d62500019aec7b8ac4a00033518f71589400066bb18e2b128000cd4631c562500011df0eb10c4a00029b21562189400057240ac431280008f7815d462500011e902ba8c4a0002ab6105
  | 18 => 0x844f9acc6bb66210803659d163cc42113f4b3a2c79884227e957458f310844fd8ce4b1e621089fb15c963cc42114673c32e59884227dc6635cb3108401b8ac6b9662108a2b5e1932cc42113de3c3a659884200dc7874cb310840178f0c99662108a3b1e1932cc421006e2bb2659884227ec5764cb3108401f0f089966210803e121132cc42113fc33a2659884227f85744cb3108401f87009966210803f020132cc4210066ab1ae198842009e7825c3310840317d09bb462108022f613768c42100666b1ae51884227cd77158d310840199eec992621089f71dc5324c4210266731ae41884227dc7315c8310844f9acc6bb0621089f35a0d760c4210066abb2c618842288f7865c8310842736908b90621080279e19720c42114673c32e41884200da7845c83108401b4908b90621089f7198d720c421006e2b1ae41884227dc4305c831084013cf04b806210922e9a1331c8421006e2b9e6390842008ed8798a21084011eb0f314421089e79e1d328842113ee339a651084200be0804ca210844f3a906b84421080327dd263484210064e3a4c69084200c9f7458d2108401938e8b1a42108032bddb744842100657bb0e89084200d2c751d121084011df0cb9a421080279e057348421134f4402e69084200ccf7698d210840199eecb1a421080279a1e314842109cdb43ee89084200cb776dd1210840196eec3a242108034ddd474484210069a3a8e89084200cd77698d2108401b28e931a421080335dd96348421006ca3a2c69084216cb4749892108491b48e9312421092b691d2324842113cf243a649084249da4744c921084017c100992421089a3b21d32580210165d302e830042008dd8798c600840193ce9318c010803275d263180210046fc3ac63004200c9e7458c600840193ae8b18c0108023ee1d60180210065cba2c03004200cb441dc5659000193f08b9cc520003272117398a400064e20ae73148000cdb805ce629005f9b100b9cc5200bf27d017398a4017e4ea02e731480048de83dda52900011bb07bb4a5200023de057654a400047a40aeca94800087f855d932900230f90abb265200023de05764ca400047a40aec99480028f8805d9329000195ee93126520012b3a0e624ca4001674384c49948002ce87058932900010ff0ab94c3200461f215729864008c3f43eeab0c8000c3c41dd561900d587e81baac3201ab0f50375586400147ac3cc328c8011a7485586519000187acbba2a32000a3d21d61546400054ec1cc520c802e8bf87586419000147f0ab0c832000a3ea03768c6400043fc2aec98c801187c855d931900230fd0bbb643200021f61776c86400246f41eed90c80008dd83ddb219009d4e90ab0e43200021fe15764864008c3e42aec90c80048de83dd821900011bb07bb0432000a3ea0376086400066ab9cc21
  | 19 => 0x23761c4298c210052f428853184200a5d8510a63084014bd0ba0cc610802976174198c210052f428813184200a5d8510263084015ad02204c610802b56044098c210052f42e86b184200a5d85d0d63084011bd0fb22c61080237a1c6458c210052f428c8b184200a5d8519163084015b500322c610802b66006458c21005ab42e82b184200e956410563084014bd0b3a2c610802976167458c210056b40ce8b184200ad5819d163084015a902ba2c61080387d525458c2100567c12a8b184200acc8255163084015af02aa2c610802b52055458c210070eaa0a8b1842008de8710963084011bb0e212c61080297a144258c210052ec2884b184200a9e849c5630840153b0938ac610802b6a027158c210056cc04e2b184200ad5801c563084014bd0ba0ac610802976174158c210056b40ce0b184200a9f845c1630840153908b82c610802b32097058c210056a40ae0b184200a9e841c1630840153b08382c610802b3a087058c210056b408e0b184200cd4711c163084014bd0a202c610802976144058c210056b40880b184200ad58110163084011bf0eb18c61081237a0e7690c2102476c34e52184204cce635ca43084091eb0d38c86108133598d7190c210046ec1ceca1842018dc8758d43084972ed0bb8a86108033558f7150c210047ac30e2a184200cd5631c5430842756902b2484108032d592719082125cba42ae32104200c5f7598d42084018b8eb31a8410803351c663508210062fbaac6a104200c5c7558d42084019a8e2b1a84108033598f71508210066ab1ee2a104227cd7315db320842736908b8c64108033558d718c82100477c32e3190424aba4845c6320847b93cc7ba2641080327dd1634c8210064e3a2c69904228cd663dc532084019aac7b8a64108d33698f704c8210066cb1ee09904233cda631c132084019b2c638264108f7a398f744c821006963a8e8990425ce8e631d1320840959b0db9a6410802f1607734c82102567c32c69904200ccf7658d320840178b0321a6410802b3e19434c821005e3c0a869904249f844150d3208401b4ee9b8a6410803691d3714c8211476331ee29904200dc663dc53208401b8ac7b8a641080339dd8714c82113f63318e29904234eca63dc13208401bc6e3b8264108036add0704c821006d43a0e09904233eca631c13208401bc6e23826410803781c4704c82113674c30e09904200dca631c13208401b92c6382641089b78a04704c821136f0c08e09904200de3411c13208401bc08238264109cb78cc4704c821396f0188e09904204cd6635c4320842796ce2b248210803a510663504210074a20ac6a084204c9e635d3310840193ce8b1e6210803275d163cc4210266731ce59884200ccd639cb310840999cc6b9662108033358d72cc42100666bb2659884200d8d744cb310
  | 20 => 0x5f43ec8aa24211a3e85d91544840187cebb24c6908030f5d76498d210061f3a8c931a4200c3d75192634840117d0fb22c6908030fdd76458d210061e3aec8b1a42008be87191634840187eea322c6908030f1d46458d210065db26e0b1a4200cb864dc16348401976c8382c6908032e1907058d210061fbaee8b1a4200c3f751d16348401878ea3a2c6908032ddd37158d210065a3a6e2b1a4200cbb74dc16348401970e9b82c6908033cdc77058d210065dba0e0b1a4200cb8741c163484019b6e6382c6908033adc87058d2100679b88e0b1a42008df8758c63484015b100b18c6908021fe157690d2108c3e42aed21a421187e85dd943484010fb0bbb286908021fe157650d2108c3e42aeca1a42008f7815d943484011f700bb2869080a3e2017650d210245f43ec8a1a420087e86dd54248489878c9baa849097e1fa1f65509212243e43ecaa124200c3f75d914248401878ebb2284908031dd9771509210063a32ee2a124200cb764dc5424842d968c9b8a84908031dd9471509210063a328e2a124200cb7641c54248427968c838a84908032d19271cc9210065a322e399242008be86dd13248401878cbba264909722fa1f644c9211ec5e43ec89924200c3f75d913248401878ebb2264908032dd93714c9210065a326e29924228cd463dc5324840196ec838a64908032d190714c9210065db26e09924200cb864dc13248401976c838264908032e190704c9210066db18e09924233cd8631c13248401c6883b2a82908031b197725052100636328e4a0a4200caf641c94148403179093b662908022f21974cc5210061e32ae998a42008bf87d93314840117b0fb2662908030f9d764cc5210061ebaec998a4200caf649cb3148401958c939662908032bd9172cc52100656322e598a4200ccf635cb314840117f08bb262908062f211764c5210071bb28c990a4200e34651932148401c58ca32442908b2ba201638852100733b2ec310a4200c3e75d92604840187aebb24c0908030f9d464981210061eba8c930242148bc86dd1604840117d0fb22c0908030fdd764581210061e3aec8b0242008be87191604840187eea322c0908030f1d464581210064fb26e6b024200c9c64dcd604840193ec839ac0908032719073581210047dc3ac03024200ad88358060484091bf0eb9ec81081237a0e76550210046ec1cecaa042048de831d954084011bb063b2a81080a3ea0076550210047cc00ecaa042118bc8759154084234790ab22a81084ead205645502100476c30e4aa04273d2c541c9540840139b06392a8109cf6910472550210047ac30e2aa04200cb5641c554084014bd0a324c610802976146498c210056d400c93184200ad98019263084016ad0ba0cc610803a55904198c210070faa4a93184200e1d5415263084091bd0e214c6108
  | 21 => 0x855da420c4230f90abb484188021fe15765083108c3e42aeca106200cd776945310c4019aeeca8a62189dba910672d93210246f418ecaa642008dd831d954c84231790eb22a9908468f21564553210264f31ae831e42008df8758c63c840193ae8b18c79081237a0e7690f210247bc32e321e4204cd6635c643c84230fd0a3b287908021f6147650f210245e43ac8a1e42018dc8758d43c849d2ed0bb8a879093a5d2157190b210b4da422e319642008df8758c32c84edb488239283908132798d74cc7210064eba2c798e4200ccd639cb31c842d36908b9063908023ee1d601832108c3fc3aebb244200c76759c764884018eaeb38ec9108028fa1774592210061fbaea8b24421187e85dcd64884010fb0bb9ac9108030f15376552210045ec24ecaa44200c3c545d9548842317d0fb22a9108468fa1764552213ae962a0e4aa442009cd831c9548840187ceb3a6c7108030f9d574d8e210061ebaae9b1c4200cb6749c7638840196ae938ec7108032e9d270d8e210065cba4e1b1c4200cf2719c36388401974e8b86c7108032e5d170d8e210067938ae1b1c42008df8758c63884091df0cb9487108461fa167650e210043ec2ceca1c42028fa809d943884011f3013b2871088a8fa176490a210061e3aac8a144213cb6641c5428840196ac838a851089e3de1971cca2113e6b318e2994423dcaf76dd132884b995eec3a265108034b1d4744ca2100567c32869944200d6775dc5328844f9ceec38a65108d33addb704ca2119e75bb0e09944200dab741c13288401b50e83826510803781c4704ca2116674c30e09944200d8d744cb31884011bf0eb1863109d2b9e1951c862127573c32a590c4200cd980dcd60884591dd0f192c110813331cd32582211657440264b044228cd473c8560884011f70eb00c1108030f5d754d91210043fc2ae7b22421187c855cf644840187eeb3aec8908030f5d475d91210051fc2ae7b224200a3c855cf644840117d0fa9ec8908022f61f53d91210070f29ea7b224200a3e85dcb644840147b0bb96c8908022fa1c52d91210a45ec38a5b224200a9e8314b644840153b06296c89085b2d9c771d91210051fc2ae3b224200a3c855c7644840117d0fa8ec8908022f61f51d91210054f41ee1b224200a9d83dc3644840147d0b386c8908028f61670d91210a55b40ce1b224200ab5819c3644840117d0e286c8908022f61c50d91210055b408a1b224200ab5811436448401878c9baac8908461fa1f75591210061fbaee8b224200c3c75dd164484018d8ebb92c8908031ddd771591210063a3aee2b224200c3e76d94644840117b0f328c8908028fa1665191210055ac0cca32242008bf87594644840187cec328c8908030f15276551210045fc22ecaa242008ef825d954484011ef02bb2a8908030f150765512108c
  | 22 => 0xb8ac598802bae017158b3100574402e2b166200a6e85d0562cc4014db0ba0ac598812b3a0f4158b3100566c1e82b166204ace83dc162cc40155d09382c598802ab6127058b3100572c0ce0b166200ae7815c162cc4014dd0a202c5988029b6144058b310057340880b166200ae58110162cc4098bce6b2c8598813279cd6490b310062eb2ae72166200c9d645ce42cc4091db0f3148598803335ce6290b3108c3e42eeca16620087f855d942cc4230f90abb285988021f61b7550b312261f326eaa16620087e8759542cc4010f90eb2a85988030fdd56450b310061e3aac8a166200c6f7598942cc4018d8eb31285988123b21d6250b3100637baac4a166200c6c7558942cc4018eccbb8a85988031d5977150b310b65b326e2a166200cb564dc542cc4019ccc5b8a85988033958b7150b310063b328e2a166200c75651c542cc42796cc838a85988032d5907150b3100673310e2a166200ce5621c542cc40153d0eb226598802a721d644cb310070fbaac89966200e1c7559132cc40993ee4b226598813a3dc9644cb3100747ba4c49966200e8c7498932cc4019aeedb8a6598803a5593714cb3100763316e29966200d97741c532cc401b28e838a6598803a5590714cb3100763310e29966227d96641c532cc44fb2ac838a659889f71988714cb3113ee2b10e29966200cd6601c532cc401d32c9b826598803b298b704cb31006e838ee09966200cdb761c132cc401b30e83826598803a6590704cb3100765310e09966200dd0711c132cc401c6882b2a83988032759373507310075220cc4a0e6200ea44158941cc40317d09b92c1988022f613725833100477c12ecaa462008ec825d9548c4051f5003b2a9188023e600765523108c5e43ac8aa46211a3c85591548c4091eb0c38aa9188032d59071552310065ab20e2a1c62008ef87588628c4230fd0b3b485188021f6167690a310147d404ed21462008f9809da428c4010ff0abb285188461f2157650a311447bc32e31946200ce6621c5328c40317d09b92c1188022f61372582310165d302e830462008fb87580608c401972e8b00c1188023be09765513100476412ecaa262008fb805d9544c4051f100bb2a8988462fa1f645513108d1f42ec8aa262048f686dc5544c4011df0eb10c498802ba20162189310043fc2aed212621187c855da424c4230fd0b3b284988021f616765093113c7b434e31926200ce462dc5324c4019d6c438264988033a188704c93113f63b08c49926200d57751c5324c401b30e83826498803741c4704c9310245fc3ac920a62008bf845cb604c40317908b96c0988023ee1d601813100574412c030262118bd84dd9540c40317d0fba2c4188030fdd774588310061fba8e8b106200c3c751d1620c40196ee838ac4188032d1d071588311a66c186e0b10620087f
  | 23 => 0x189410074a20ae63128200c9f845cc625040193908b98c4a080335e0573189410066a40ae63128200c9c415cc625040193e80b98c4a09e7a9107521894100566c18a43128273ea44114862504091bd063b4a4a08023760c76949410065a20eeca928200cb4411d9525040136d03ba2a4a08063da1b715494100cdb426e2a9282019b4841c55250401968833b664a08032d10576cc9410043fc2aed192821187c855da32504f1d488231464a08032d107764c94108c3f42cec992820087d859d932504051f5013b264a08023e602764c9410065a208ec9928200d3441dd5325040136d03ba264a08031b1d7624c941006363a8c49928200caf74189325040959d0631264a09dfa9104624c94100c7b436e299282019b684dc532504019c8c5b8a64a08066d210714c941006d820ee09928200ceb621c132504019d0c438264a08036c104704c9410061fb2ee8a8a82118bf87596415040155904b2c82a0802a760c629054109e5b388c520a82018bc865c24150455970c0b8482a08021fe1572d814108c3e42ae5b028200d3441dd56050401b2883b9ac0a0803651047358141006d220ee4b028200da4411c9605045587ec8ba8c0a08034d10575181410047dc3ac030282048be87d5164cc40187eebaa2c9988461fa1472593310043ec28e4b266200c3f759d564cc40187aea3aac998812a7a0e72593310051fc2ae4b266200a3c855c964cc40156f02b92c9988028fa1472593310051ec28e4b266204a9e831c964cc43553b06392c9988022fa1c52593310045ec38a4b266204a9e8314964cc40153b06292c9988028fa1771593310051ec2ee2b2662008be87d4564cc40117b0fa8ac998812a720d70593310051f428e0b266200a3d851c164cc43556d02382c998802ad60470593310045f438a0b2662008bd8714164cc40156d02282c998802ad60450593310061e2a6ecaa66200c3c545d954cc4091790eb22a9988468f21564553310043fc2ae9316621187c855d262cc4014dd0a214c5988029b6144298b310256741ee93166200a6f855d262cc4014d90aba4c598802b9e057498b3100537428e93166200a6d851d262cc40959d063a4c598802b360c7498b3100717aa4a93166200e2d5415262cc40155f08b8cc598802ab2117198b310053742e833166200a6d85d0662cc40959d07b84c598802aba127098b3100556c24e13166200ae5819c262cc40959d06384c5988029ba144098b3100536c28813166200ae68110262cc4015cb02204c5988029ba144258b3100536c2884b166204ace8310962cc4015cd033a2c598802b96067458b3100537c2ae8b166200a6c855d162cc4015cf02ba2c5988029ba147458b3100536c28e8b166204ace831d162cc40159b063a2c5988038bd525458b3100716aa0a8b166200aaf845c562cc40155908
  | 24 => 0x264008fb87584604c80157708b08c099002ae2116118132006793b0c23026400eb364184604c801d60c8308c099003b460c611813200769b98c23026400ed243184604c801da286308c0991efb8e08611813200770b90c2302647bee332184604c801da464308c0991efb80c861181320071daa4a83026433ada83950604c8015b3072a0c099002bae09541813200574412a83026400e3954150604c8014f50ba18c0990029e61743181320053dc2a843026400a7885508604c8015b706a10c0990ceb620d421813200579c0a843026400af081508604c8014f50a210c0990029e614421813219d6d418843026400ad983108604c801d5284210c099002aee1132181320055c422643026400af3814c8604c8015e102990c0990029ea1741181320053cc2e823026433ada83d04604c8015b307a08c099002baa0b411813200574c1682302641187e85dc5640c8010fb0bb8ac8190122f21d645503208d1e42ac8aa064008df865ce420c80193eedba2641900327dd8744c83200667bb4a49906400ccf76549320c8019aeedb8a641900335dd8714c8320066dbb6e09906400cdb761c1320c801b30e83826419003741c4704c8323d53b40eeab2c82048de831c965904011bb06392cb208468fe19655524132e1f328e4aa4820099d831c954904a717b0db8aa92080237e1d6318e4100c9fc3aa929c8200c3d76552539040163f06aa4a7208622f61b7150e410049ec2ee2a1c8248ae681d8a62904cb1790eaa2c5208470f9d55458a410246f41ee0b1482008dd83dc162904011df0eb10c5208064f21d5454a410061fbb2a8a9482018f5861c55290401a6aa838aa52088b0f9977590a410049fc2ae7214823dc9e635ce429042dd4cc331485208562fe1d6290a410b45fc32e3214820093f855c6429042d56f0cb8c85208021fe15764ca4108c3e42aec99482008fb805d932904051f100bb265208f72798f744ca4100cce43a869948204a9f8650d32904031eb0c38a652089f3598c714ca4119e6d318e09948200cd9631c1329040187acaba4a3208468fe19549464100e1ebb2a928c8200b3781552519042387ceaaa2c1208461fa1772582410043ec2ee4b048200cac42dc960904011f70eb00c1208031e94170d9541006d220ee4b2a8200c6c651c96550401b4882392caa081237a0c72595410046ec18e4b2a8200caf741c9655040199d06392caa08033360c725954100656208e4b2a8200caf401c965504019c8e5b8acaa08034d1057598d41006d220ce531a8200da4415ca63504011bf0eb18c6a08032d1067694d410065a20aed29a8200aad8414b625040159b06296c4a080237e0d70d89410246e41ae1b128200d3441dd56250401b2883398c4a080365105731894100477c3ac43128200a6c8558862504ed5cf02b10c4a0803a510673
  | 25 => 0x8011ed0e200c2990023d61c40185320053b4288030a6400a7585100614c80317d0938ec0990022f61271d81320053d42881b026400a7985103604c8015e502206c099002bc60440d81320071db2ec9b026400a7a85993604c8014f30b326c099002bca0664d813200578c0cc9b026400a7b85593604c8014f10ab26c099002bce0564d81320057840ac9b026400e3b65193604c801c70ca326c099003a660c64d81320074db22e7b026400e98645cf604c801d30c921ec099003acd9361d813200758326c3b026400ed173d87604c801dc305b0ec099002aea1261d81320055cc24c3b026400abb84587604c80157108b0ec099003acd9061d813200758320c3b026400ed183187604c801da2e630ec099002b660f74d81320053d42ce9b026400a79859d3604c8015e5033a6c099002bc60674d81321a56d418e9b026400ad9831d3604c801c76a92a6c0990038e55054d81320053d42e87b026400a7985d0f604c8014f70aa16c0990029e21542d813200579c0a85b026400af08150b604c8014f50a216c0990029e61442d81321a56d41885b026400ad98310b604c80157509b8ec099002ae61371d81320056cc1ee3b026434ae982dc7604c8015750938ec099002ae61271d81320056cc18e3b026400a7a85d07604c8014f30ba0ec09900b2e18174981320061f3aec93026400c3d75d92604c80187cea324c0990030f5d464981320065bb24e33026400cb4649c6604c8059e0c138cc0990032dd9171981320065a322e33026402cf0605c6604c80196ce9b0cc0990032d5d361981320065b3a0c33026400cb574186604c801974e9b04c0990032e5d360981320067938ec13026400cf171d82604c87b1790dba2c0990022fa1f64581320061fbaec8b026400c3c75d91604c80117d0e322c0990030fdd464581320061e3a8c8b026400cb764dc5604c801968c9b8ac0990032dd9071581320065a320e2b0264008f687d85604c80196ee9b0ac0990032d1d361581320047b438c2b026400cb774185604c801968e830ac0990023ee1d60181320055dc22c03026400ab884580604c8015e702b00c099002bc20560181320065d3b6c83026400e3b65d90604c8011f30f320c0990029ea1664181320053cc2cc83026400af281990604c8015e303320c0990023ee1d64181320053dc2ac83026400a7885590604c8015e702b20c099002bc20564181320065d3b0c83026400e3b65190604c801c70ca320c099003a660c64181320074db98c83026400ada8690c604c801cb0cb218c099003a619243181320072c32a863026400e986450c604c801d56c8b90c099003aa19172181320074c324643026400cf276d84604c801d66c9b08c099003ac193611813200770c16c23026400ee172d84604c8011f30f308c099002aea1261181320055cc24c230
  | 26 => 0x23da1871509320063bb28e2a126400c74651c5424c80196ec838a849904f2d19071509323bed2210e2a12640099f845c6324c8014ed0ba0ec2990029d61741d85320071bb2ec9b0a6400a7685993614c8014eb0b326c299002bca0264d853200578c04c9b0a6400a7785593614c8014e90ab26c299002bce0164d853200578402c9b0a6400e3765193614c801c68ca326c299003a560c64d85320074a32487b0a6400ea7645cb614c801d48c8b96c2990a2b960b74d85320065bba4e9b0a6400a76851d3614c8014eb0a3a6c2990a2b5a0c74d85320056ac18e9b0a6400ae6821d3614c8515cb043a6c2990038dd5254d85320071aaa0a9b0a6400a7685d0f614c8014eb0ba1ec29904e3de1d42d85321447a43a85b0a6400a778550b614c8014e90aa16c2990029da1442d85320053ac2885b0a6428ad68310b614c8015ab06216c299002ada1370d85320055ac26e1b0a6400ad583dc3614c8515cb05b86c299002ada1270d85320055ac24e1b0a6428ae5821c3614c8011ed0e206c2990023d61c40d85320053b42881b0a6400a7585103614c80187cebb24c2990030f5d764985320061f3a8c930a6400c3d75192614c80196ce9b0cc2990032d5d361985320065db24e130a6400cb8649c2614c8019e6c3384c2990032ed9170985320065c322e130a6400cf3615c2614c80117d0fb22c2990030fdd764585320061e3aec8b0a64008be87191614c80187eea322c2990030f1d464585320065db26e0b0a6400cb864dc1614c801976c8382c2990032e19070585320047bc3ac230a6400ab784584614c80156908b08c299002bce01611853200578402c230a6400a7685d04614c8014eb0ba08c2990032d5d041185320045fc22e030a64018bc845c0614c80196cedb20c2990038dd9764185320047ac3cc830a6400a7685990614c8014eb0b320c299002bca02641853200578c04c830a64008f787590614c8014ef0ab20c2990029d215641853200579c02c830a6400af080590614c80196cec320c2990038dd9464185320071a328c830a6400e9583190614c801d2ec8b98c299003a519173185320074a3248630a6400ad583dd0614c8014ed0b3a0c2990029d61674185320065aba0e830a6427ad6831d0614c8015ab063a0c2990038dd52541853200573c12a830a6400ae482550614c801c6aa82a0c2990029da1743185320053ac2e8630a64168f787508614c84f1e90ea10c2990029de1542185320053a42a8430a6400a7685108614c8014eb0a210c29909eb5a0c42185320056ac188430a6400ab7844c8614c80156908990c299002b560f70185320055bc22e030a6400ab4845c0614c8015af06b80c299002b9e0970185320055b420e030a6400ab5841c0614c8015ab06380c29909eb9608701853213d6b41e8030a6400ad583d00614c
  | 27 => 0x6c30e4aa4647ed2c541c9548c8f1b488438a85190030fdd774586320061fba8e8b0c6400c3c751d1618c80193ee9992c3190023de1d611863217e4eb1ae9304642fcd5635c6608c8011f70eb00c1190030f5d754d91320054ec1ea9b22640087f855c7644c8230f90ab8ec899002ada0665d91320055ac0ccbb226400aba80997644c8015730132ec8990f6ab60b75d91320061fbacebb226400c3d751d7644c87b53d063aec899002a760c75d91320051fc2ae7b226400a3c855cf644c80117d0fa9ec8990022f61f53d91321ef0f29ea7b226400e2e52d4b644c80117d0e296c89907a2f61c52d91321ed4f418a5b22643daad82dc7644c80196ee338ec8990028fe1571d91320051e42ae3b226400a9d831c7644c80117d0fa8ec8990022f61f51d91320054ec1ee1b226400a3e859c3644c80147b0b386c899002ada0670d91320055ac0ce1b22643daad821c3644c80117d0e286c8990022f61c50d91320055b408a1b226400ab581143644c801878c9baac8990031dd9771591320065a326e2b226400c77651c5644c801968c838ac8990031ed9770591320065c326e0b226400c7b651c1644c801970c8382c8990461fa1f75591320061fbaee8b226400c3c75dd1644c8018eeebb8ac8990031d1d771591320065bba6e2b226400c77751c5644c8018e8ea38ac8990032ddd071591320063dbaee0b226400c7875dc1644c801976e9b82c8990033cdc770591320067838ee0b226400c7b751c1644c8018f0ea382c8990032edd070591320066db98e0b226400cf3711c1644c8019e0e2382c8990030f9db65191320070eb9eca32264008bd87994644c80147d0b328c899002ada0665191320055ac0cca3226400aba80994644c80157301328c8990022fe1d65191320055bc0aca3226400ab481594644c80157700b28c899002ae20165191320061f3b0ca3226400e1d73194644c8011ed03bb2a8990023d60776551320147d406ecaa264008f980dd9544c801878a93b2a8990022fe1176551320047bc0aecaa264008f4815d9544c8011f700bb2a89900a3e20176551320061e2a0ecaa264118be87d91544c82347d0bb22a8990123ba1b725513200657b20e4aa2647dd2c541c9544c80939d06392a899003871936590d320070e320cb21a6401a9e86d92434c80193cedb248699002a72195490d32005c6412a921a6400caf641c9434c8011b90cbaa8699003171db6550d320070e326caa1a6400c5c76195434c83d938edb22869917363dd07250d32004aec2ee2a1a64009ce82dc5434c8b993ced21c84991f21fa1b75509322261e326eaa12645f87e87d95424c8df0f90fb2a84990030fdd764509320061e3aec8a12643dc9c73d91424c84f1ed0db8a84990031dd9771509320063a32ee2a126400cb764dc5424c82d968c9b8a84990a
  | 28 => 0x619461508e7c6d08328c2a10038d610651854239f33a10ca30a8473e344219461508e7cc884328c2a10038dd9554185420071a32aa830a84008f58798c61508014ed0b318c2a10029d61663185423bd72c14c630a84008f78758c61508014ef0ab18c2a10029d215631854200579c02c630a8400af08058c6150801c6ecb210c2a10038d196421854209d5b424ea30a8400ab5849d4615082756d083a8c2a1002ad610751854200579400ea30a8400af1801d4615082756f0aaa0c2a104f8de1554185420071bbaaa830a8400e34755506150801d4f04aa0c2a1002ad209541854200752412a830a8400a76859cc61508014eb0b398c2a1002ad61273185423bd72c14e630a8413ab684d4c615080156b09a98c2a10038d55253185420072ba9ca630a8413ab68414c615080156b08298c2a10038d550531854200573410a630a8400ae58214c615082756d09a90c2a1002ad61352185420071aaa6a430a8413ab48494861508ffc6ca9290c2a113a3de1d521854209c7a43aa430a8400ab784548615082756908a90c2a10038d551521854209d5b420a430a8400ab58414861508e7c6ca8290c2a1002b5a0c52185420056ac18a430a8400ab785908615080156b0b210c2a104eada0a421854209f534148430a8400a77855c061508014e90ab80c2a1002ade1170185420056bc1ae030a8400ad4835c061508715cf04b80c2a10029da1470185420053ac28e030a8400ab5841c0615082756d09a80c2a1002ad61350185420071aaa6a030a84008f68714061508011eb0e280c2a104eada1050185420055ac20a030a8411c3c7555360508230fd0b38ec0a10021f61671d81420063bb2ce33028400c74659c660508018eecab8cc0a10031d19571981420063b3aec33028400c7575d8660508018ecea30cc0a10031d5d461981422243e436eab02840087e87d9560508010fd0e32ac0a11bb1bdc865581420062fb2ee6b028400c5c65dcd60508018beca39ac0a10031719473581420063bb2ee2b028400c7465dc560508018eeca38ac0a10031d19471581420047b43ec2b028400c7775d8560508018e8ebb0ac0a100335dcf61581420066a39ec2b0284008f68718560508018eeea30ac0a10031d1d461581420066bb98c2b028400cd47318560508719cee430ac0a10023ee1d60181420056c41ac030284048be87d5164cc80187eebaa2c999012a7a0f545933208c3f42ee2b26640087d85dc564cc82317b09bb2a9990030f15376553320246f41eecaa6643ec5e53dd954cc801878a8bb2a999002576177150f320061e3aac8a166413cb6641c542cc80196ac838a85990029da1741987320065aba08330e6400a7685d0561cc8010ff0ab8ec9190461f21571d92320047bc0aecaa464008f4815d9548c8231790eb22a9190468f21564552320247
  | 29 => 0xb4a721046972156394e4208c6e43ac6a9c8422c3e75d9643908b917f0cb9487210030f5957494a420046fc1ae130c84048dc835c261908230fd0fbaac3210030f10775586420061fa06eab0c84008f78758461908011f70eb00c1210028fe1173d95422251e422e7b2a8400c5d731cf655080147f08b8ecaa11128f21171d95420052f41ee1b2a8400a5d83dc3655088947d09386caa10028f61270d95420053b40ce1b2a8400a75819c365508018e8cbb8acaa10031d19471595420065bba6e2b2a8400cb7741c565508019cee438acaa10468fa1b655514210e1e3b6caaa284448be861c954508bf878ca392a8a117f4bdd472551420043fc2ae3b1a841187c855c763508fb8dae432cc6a10031dd967198d420063a32ce331a843dcb7649c663508018eecab8cc6a10031d1957198d420043f43ecab1a840087e8719563508018eecbb8ac6a10031d1977158d420063bb28e2b1a8400c74651c563508018f6cbb82c6a10031e1977058d420063db28e0b1a8400c78651c163508011bf0eb18c6a1002b62016318d420047bc0aed29a84008f4815da53508014bb07b2ca6a10468f2195494d420061f3b2a929a84008f681dd953508011eb03bb2a6a10030fd9774549421161e32ee8a928411a3c865515250803878ecaa2a4a1002cb209545494208c5f436eb2128422c3c65dd642508031790cbac84a108b0f19575909422fd1f436cb2128444e2f62d96425080156b09a8ec2a12038da1065d85420071ac20cbb0a8480e34421976150801c68caaa6c2a10029da1663d85420053ac2cc7b0a8400a778558f61508014e90ab1ec2a1002bce0163d854200578402c7b0a8400e346590b615082d56d083aec2a1002ad61075d85420053b428e7b0a8400a75851cf615080156b0839ec2a105ab960873d85420b55b426a7b0a8400ab584d4f6150801caea729ec2a112e3de1d52d85420b47a43aa5b0a8400ab78454b615082d56908a96c2a105aada1052d85420055ac20a5b0a8400ad68314b61508015ab06296c2a10029da1770d85420053ac2ee1b0a8400ab584dc361508015ad07b86c2a1002b560f70d85420b572c16e1b0a8400a76859c361508014eb0b386c2a1002ad61270d85420047b438a1b0a84008f587143615082d56d08286c2a1002ad61050d85420063b3aec330a8400c7575d8661508010fd0fb2ac2a10021fa1c65585423ae37b90cab0a84008f78758461508014ef0ab08c2a10029d215611854208e1e3aaa830a8400ab584d44615080156b08288c2a10038d55051185420043fc2ae030a841187c855c061508011bf06b80c2a10123720d70185424263b3b6ca30a8400e3784d9461508ffc6909b28c2a11ff8d10b65185420047ac3cca30a8483a768599461508011ef0eb28c2a120ab9e09651854240d3b430ca30a8480c767
  | 30 => 0x8002000000000c00200700100080020020000018006003000000000000100380040060010000004002000003801400200100480000000000008070000002000000c00000000180000260030010010012009000801400a0020000000000006002001c01200b00100040200000000008010004000800800000000000100080030000004000001001801c00a00c000000c000001001000000000400000040020010000000012004000002c000001000001c000000002800000600a001800c024009000001000200400080140180030000004004001001000000000c000000c002000000800801401300000040040020052ec3ca7b1aa83ec5d8794f635507dc3ce929ec6aa0fb875d253d8d544470e20ca7b1aa888e1f4094f63550011df04b8ec6aa0023b20971d8d54006962a4e531aa800d2c545ca6355001a68a938cc6aa0034d1517198d540046fc3ac631aa8008df835c362550091b906b86c4aa0034d15371589540069a2a0e2b12a800d1c549cc6255001a38a8b98c4aa0023be1d621895443d57c22c4312a800ae481588625500193ae9398c4aa0038715273189540064eba2e6312a800e1c545cc625500193f08b98c4aa0032721173189540064e20ae6312a800c9f405cc6255001a58a9b92c2aa0034b15072585540047bc3ac230aa87ae345458461550015c904b08c2aa00237e0d70185540246e41ae030aa8008ef825c061550011d904b80c2aa0023de0572d81540047a40ae5b02a800d1c54dcd6055001a38a839ac0aa0034b1537258154006962a0e4b02a800d3454dc56055001a68a838ac0aa0034d15271181540069a2a2e2302a8008fb8758060550cb87cca392a9218026760c72552430047bc0aeb31486008f4815d66290c0155b08294c521812b3a0c5298a430043fc2ae3314861187c855c66290ccb1790eaa2c5218470f9d55458a4300556412a8b148600aad84d496290c01c5aa9a92c521802ab6105258a433ef172a0a4b148604ace831496290c23878eaaa4c3218021fe15729864308c3e42ae530c8600ab584d466190c0156b0828cc3218038d55051986430055ac26a2b0c8611c3e755516090c230fd0bb92c1218021f61772582430047b40ee4b0486008f581dc96090c018dca4b96caa18032d10571d95434362fbaee6b2a8600c3f65dd15350c011df0eb10c4a18461fe1d75d85430061e20aebb0a8600c3f405d76150c011ef0eb08c2a18021fe15721854308c3e42ae430a860087f855cb6050c230f90ab96c0a18023de0572d81430047a40ae5b0286008fb875806050c835b706b00c0a18031794d73d964242f162a4e5b2c8444c3c74dd5659080196883b8acb210461fa1f7558e420061f21eeab1c8400c3c43dd5639080187883baac7210030fd037558e420065a20ee2b1c84008df8758c63908091bd073
  | 31 => 0x20010000005004000c0000040000010020001003800401000300000080020040008000000002000002000a0000018004000000001800800200200180040040000008018002000002000c01a001000000c000006000001000000200080080020060000000002000000800800600000280040080000018058004000000000000a000000801000a005000800400a004000001000000300200300000010000010002002001000400000000200040000000050010004000004802801e00000100040200030000008000001000000800000300000300000030008008008000007000400000200100040060010020000004009000000800600300280000280000000000002001000000000c00a0010008004001002801400a001002000c00c001000000000600000c80040040010020010000000003000c01c0000030000004000000805400000000200380000010000018000000000004c000000000002c00800100000000020000008000000001002000400a000001800c0000000008018006002000800400e0060010000004000000000000800a000000000600d000000400800000000040060010000010016003001800001a0000038018004000000001c000003001800000000800000180020010000000000000001000000000500000000080000000000000001001001c01a011001000000800300080040120010018010004003000800400000300000100000030008014026000003000000a0030058018002002000000800200100280040080000008000010000000800c00400f000801c0020090018008002006000000000200300c003c00e0010048024002000002000001800500a0000004000002000000000100200000000010108010004002002800400400800e803000200000080000060000010014000000003000000000000000000000180088000018003000803400a00e000800800200700080000060000020000002001007002c00000000000180000000000000040001000000000400a000800400800000100040120010000000006000000800400600d004800c0060040068000006009000000c0060000008004000001002000000a00b0008000014001001802400000000500100080000090000024004000000000e000000000000e0050060004014003000000401e001000000000a0000008014004003000000400800000000080000020030000002011006801000200000580080000010018000004000001000800e0000040008002000001800000c0000038018004000004801800400000080080040010000000002002001800000400000180040000070000008000002000800400200000000000180010010000000001000000000000300f00000020000000010000004000801000000b0010004004000000801000a00e00780
  | 32 => 0x4000000000001000000e000000000a000000000400a002003000401c0010008004008000007002000200000080000080140000008002000002000800600f000000000e004001800400a00500080000080060000000006003002000000400000700000020050000008000001000800000c000001000000800400100000020000000008010000000800c000000004800400401300000100000030028000006002000001800600000100000020000008000000001002000c000000000001400a0000028000002000000000400a0010008000012002000000404a0020000000002004000800c02c0000000000000009000006002000100d80040020040008008002000000000000c003002000400000100180000020000000000004000000002400600800000400020010000034002009002000400c001004805800800000200000000000000014004001002000800c00a000800000000100900040060010038008002000000000001c00c0020000000007003000000c000001800800e00600400000080030000054002003001000000a003000000000a00100100000040000000018000000000000000400600a00000000000000038000000000006400400d0000058000002002800000000a0038004018003002000400600300000080000020028000000003002801c000003000000c0040010018000002003002800802600000000280000010008018000000005000000000100000000000040030004016000000002800400100180000000040038000004000000000000000000500080060050008010006003000000000c0080008030002017000800400200200000100060010010004002000000000400600500000080100010000014000001000800400000500180080040000038000000005000001400000000e800c01a000000002c01000d0000000024000000005400a00000200140040010000000004000003000001201400080180000080000018006004000000400a009000000000c00000000040000000008024028002000003c00200000000000000000000020014000001001400a0000048004002004000000400000100080000040000088000020000000802c002002002801c02000e0020018008011000000c00000700000040040000008000004011000000000200000400000020020000008002003002800000e000000001c000000005802001c001001000000e00900000140140010000004008000001000000400000000000020040000000002000001001400e009000000000a0060028014004000000000000200100000000000010000000014001004800800800000280000060010020000008001001000400000200000140140000008000004001000000400000000000080000040018018004006000002400e00000300000000
  | 33 => 0xa0d732fdcc970000d7e33e484d1834115800000000006ce004c00000000000eac0001ef4f000000000000040e000033305043e8082400000000000000000329c000000084c051400000004050000cb10e3c00013a67bc3710000000000000009a33ab8000365200000007de000000000008461e20bda406c60b26d40002238000000000023d422a06b80001d9481280000000000000000059f13489b73f44000000046e00000000000440000000035702b60000b7932c800000004222aa40000000eca00000000001074000064b8bd00000ad01443f60dbe800000037860000000000000441523ec000060c0000000ca527c89b414c800014be1e800000fd800000db0180002ebc7001158c8817040000001061000034e8e14c0c191e4aa0b9c0000000eec09c60289e8c00041a0000000000000009e617ac4cf35b80002e8807f3afc00000000000000d8d00000000000000025045c37d0a9a2dcc000000000001a4fa2368e0003d1aadd38b903339d0000000000000006ce8c0863c38c400000000000aeed4029bc91d000054137c401dc2081a02b4404100008301ae00002e80a083d8829c8000000204cfc50000a6110607f900007722d9e000255400000005450000000000000034d80000000000000000000000000000c148000f9d37e0fca01be3760000bee0000000174c44480008b612bc0001a40000219064342b8e3600006513f9ce1d2f44ae618cc264402c2d9225ca4333c838b12449f9a2a40840054000107400004fc2910000000000000000000600200080000000000000010000000000000000000400380040000050000008008001003001c00800000100080020030028004002004000000c000000000800000c001001800400c0040008004000001003003000000000c80000080000058028002006000000000c00000080040000010018000000001001800000a000002800000200d00500080000010050018000002000000000200700100000060110020008000000003000c00e002000000c0040000050000000000000000c0020000078008002001006800c000000000001001a0030000008006003000000000000100000000000000020008000000000800001400600c000001400a00000000000090000004000002000000400000000000240040000028000000000000800400600000f0010006000001800400c00200100000000020020028000000001802800001400000040080000040028000000002800400000100300240040000008020000000003001400200000080340080010008020000000000000001c000005000400c00a000003400e00000000340000050018024004004008002800600300100140040000038014004004002801800000000e000000000c0008008000006000000000800100080100020020030
  | 34 => 0x3600000001e54d913ac03ad367c6d00000a2d20fa0000000000000104500000000fe4a310d9c0003cec00019100000000fd206063a1289012e8fb466220fcece1b5e4cd2328392b36846107e000000001cd0000620385800007a8cf3293ab481e40c9d00000003b24000245cf653fc8e5e0000c8e052c80225d800024400000ed000000005e90000be036ac7f220ac0000000120000000000000000000000000000019709df30f500700007e6137c9e7000045a27b8e6cab5445130d4003216c9cc00000003278000249cc833d380c40000cd00aba8881478b3f20108d02d8e3460000000429084e000000033ecb69c2a4b6f2f1cd8800004b080004b893fcdce3ba8000000023b14b8000000000000000002c3495000000002a2000027a800000000001678ca21140bc224fc14e0744f78109c7d200000001728f8b000000000000001a6418bac107d12c51066088467520545e120b00000000000325400034dc530b0fc2e63f8c174000032c082e7f000000000000fb500000001ebc6c5800020e033ee6f000000017088170db0000328c137b77c68b32e01dd000041d80000000958aaa00000003b5a00000000000a4c0002baa1593aee0ad000018e0000ba186048f3104c000323c8e10000d030000000000010c38d00002fa48dc000000022b40000000000000000000000000000c23b12400000000000574e06c17400000007c300000003ff8000316cf4800010911b141d087bead636d4c38333c000000000028623e900001371beeb1200008531ab000000000000000000201c0003d101fdbe9ca0c0000f8820e80000728a530000000000094438d411808e40000000df78b5050b0000f291d70e9c038c08e4034247b5c44d312e0d4b24982f58116f35148c09f322ca098984e200c7c34512140002968b4e00d00001d7a000044502c3b1400000000004190421800069a0000000188e0003b56dfc8000000286000015ec00014a4fb83e6c74fa55cd210980e7841509850e002e40b3600028b002c06f06320134bc50000a2e3530577167003a974901600000000cbc1a7234800000005ba00000002710ab3368105300000003814fdc143070c1ff8000003c00016b00ec0000e9821641fa13e8ede80000000b08000000029783fe000000002ca2c8dcb1a20000188cf51043c00012989822be6a0080000000000000351468000004e70000ebc000000000000002e98cac000072d357410a3f88844800073e800000000008031838cc000001c119e0ad00186bc131bc00000000003b98f2c412cbdc0c98000148849b4228fd92a1a41f0000e090000000000000000003fe224032400000001c3a00000000000000266380a96413aadeb0e6c000309438c13442c40d54d58000078a0000b47000000029f48a7000000040500000b2eff6000090810
  | 35 => 0xa8ccbc0000eb68ac8906056000000000001894000116a14c00000000000000000000000002a2000000028d000031ec92400004ef0000000000000015e4000000037a0000ec08000446000023033f89a737580003b8000005b05661528000000000000000003c70e893404c4680000000000ed802d46e600008fe25e00003618d8cb410b1c80000003598000267800006007dc00001b503bcd7d276800013d4b1298e00004118000200200002ba1530000000155400000000001bc00001e04776389a000372a000000000000000000000c1a2b20f2426e07773ca6e2d08900ea12fcbb88000dbe277000001540000000000000000032280002fcefc12280c902b9c0000000000113427f22221f6c1dc61313540001ce455e05ccc1405a0463345432e3d5c51213d07ac228ca5816907c82dc40002c28000000019a0000000016c000241400000010200000d9c0000bc90000000096cdb9297600000000002decbb9382800000000000000b1600009521f90a910e4c27c1458f59008ad43315c61a3afe3840f24ed39c70ecc1104c7312cc7423ca870532d037c375104a1ed26371596d0e20b20003324000056cbd600e07db3a28000000009604ac000363efc03a0000000001ba156438b800000033c4c4e40d8000409014f2d2c589b9942bb1f0ec2413e29422e147193d18f4500d200037bc4ee25640001e58aaa80000000d7e304000104820a466c298045d9aa04e400000003e60dbd3640000159c48e00000fe080466197702a880006448000aa110b8000112670e31ea40f000000028ee7f582f0067b0565cf00000000a9a4fe1c50b88393a65200000000f586d205e8dba11e200000004748000881a56800013e48ac2fe6c660000911169e2e10000388334c0000000000000105e0000000000021100008bd2ae402700007e210a8bd82314e0b2fe047722cc5dd26b401c0780d3f000045900000003ff402b223c677227431e2230b3a252c0001cce000087800000000be00000000040c798b6c35d8f3600bb038b2000004f3b95c000000092800001bc800041e29d800000000002ec0d93000000007ac00000004ce2be89b621e80000000b0bb2708aa0908e1a0220c740000a3926280000000000305c000000000000000000ac000020a0d87000000015f8000000000017fe8e3000012995700000000cba1350b7e0230000233cf3d2c9870b1ab400010bce8c059c05c08688ba1328b5d30f806340fc000000054b07643532018000020817ba381010284e0000f285be000035902fc373292afbc25d40360000e0e00000000e609962a14f8f224b0830794dc5a8ec34002b6378174492200008f0342834908f000022c00003b10534003a000000000003e200021a099111d0dd383f068f001c000134b0a23bb40dc35720321aa4ba40ed472200005
  | 36 => 0xc9304a0d5600322e200000c93b880002288251187813fa7d60001db4d99896a91800006d100000003c0800015a80002b6053587d4cb6380200000002ad9934000000000033089ff0fb81fc074058e40f00000e34000242834313c654014deb9400000002a78000409cabf00000c537208323c480000000000000000000000b200009073dd000031f0be10d1c5443674c7117f800000000000000d3e051c000000000021c4000020cd081a0c27f988631430340000d80000318ce7c000002d00005352bda1141000bdd183000000003220118fa414186312bd200000001d39e448f221c09c1385600019c488b8000000000000014dc2ec80000740000f1500000000000c7e3c7cb4ea42c000000100680000002824aff8000191354e5b600006db00007ca03e80001f640000000ad937483a315d8bbd4104e4e25fc52cc2b06213a4044f01d85269a487c9000102f0048e4c00000000000cea42648d636a82ce8000ed105c46f936f638736380000350000000045b000057d328000027ccb0e86980001fb4000000000000000000000c110000bf6000010200008430000aa635e802699c84983bb831a1e9475a000038a36b48110000000097810ab690000217435b00000003ea80892d78ce60000000000054b94241ef28000a44000b56ad36b6e3a4cc5e2ffc0000000b810000c000000000272400000000000000000000079719f87cb0000bd392b8a8d34e834200000002c380dd000038900000000000acb253c5aa05c0b8334f0afe8000a813cc6b2baa9424e2facac2000081780010591d4ef7b1becedb2cf485a28180000000000180c5f70000cce0cc42d00000216111600000004bb0e4000000000000bd8ce23f74b030ac4d1a88c4a3a00007b4229406d800096904700000000000000000000000000000e400f38b81af980000248b1b00000000000127000000000000000000eeb330cca6000052612503c703d44b40000d1700004470000e1f800074d8b24eb8986c0000414afe000000000001f6268908703d086f32249aa000000000005a880002b6a34c000000000041450523594a5f35dcf5a10900003b409d301501940ad304000000002ac064580fa24c000000000003ba3fc4c478bca2808000000001000000000000000f0d000000000000002760000030c00000000000000000388a0000d880352cde00029cc0000001063000043f24386fc3de81a3004400012045fcc284447ad40e7928bc9ce1be8e7708b2a462e0022f30f200013886c980003b633fc7630b76000411000000003ae07aa62b09ba0000000d8d80000000000de30e1800000000000000ffb17d40000000000135c52f172502822ec5da33e855200000000000cef16fc6e40000000325600030f600024ac3e609d0a6d36dc6ba000000000004c2000000000004260
  | 37 => 0xe688ba8c2e19a8e550000e210000000000000023bc0001b94000000000024840001d30c4d000000000009873c647020000e2f066400029f800022646702b34c4700000b90000b4b95300001864538242eb1900001189a500d10000000000000039a476a3a2c000112c0001af40001fbc0000000a4bb2f8182374ac2b00000001bcc40c0000d9a0000000000000000001e4844601fb754dd9000029480004970000000050a3a600000000000099800080f000000000000000000d86b164000000000000005e82d983540000e26000000030c42133b18c0f000000026de26a0000e4f1230000000047807820000000a441da501d1ecc514000000013ec0000000de10c7a2bda96c0001cf6000000018f0000000000061c05845742d2a0002d52cb326e80000a10902200066e2fd0fed00002a5bb4a8422ab6531acd40001650000169c1b70dece6ab3ac2ba000041600000001d7cabe0000bfc0000f2000000002bb400000000001f5c72300004b986f459729a49be000000012a00000000000367655d000092d8000f1a000000024f8000000000009d6b0b332c00000006ae1a580002fa00000000000000000009c45650000cf8000000019600002748000000000000000000be080d1f58a99292c00002805720000e52000020d297800018089710d3c84b03185892c18d0234a051f1ec40001ba8597b5fcf8d2988480a63c00000007a938940000000965000030b09c000000000000000000347820980000000000bfd0f04396284c0000f4cc58000000008e8e2221ba000198400006243c410c0db20000000000054f327c3c01ad801f0000706000000000000003b54a2200000001cb8c150ec400000000001cc0000005c00000000000000aeb358c33808a4ab400000000000000267c0000000bcb0478a54b0dcedc0c3892c057c0000a501c78806000000065b3ab4c5433180000000000000012e0000a4116140000000446ba640002c146fa8000a51000035e36f200000000002c9a1c900002d620588db3a90bc60000146000000016986b11590912338c6ff32ac8838000d491f8400005c8744abc42bd0000c6c23385d63f1043c2c200002970d1d1d905f60440000162000041fc00019ec0000000000000106f16742d53046e293b5899c36d0f662c86bb600000000be82d141a45ff3d509603b1c12a0000a0e1ba4000000063000000000ef0fb428f824526e400008640002da00001980b7a334899700004b005f070934f6000000000000000001b2c0000000f2e00003290000a8732b80000000000308d02500000001a7420b29a84b100000000000000080a40600006170cf65fa0000000000000011eadc5000000000000f905544f28000b211bf4000000000000000a91f6017806f8000000103033d8000000057c374d0843f3812212f0
  | 38 => 0x7990000000099c0003e54000000800000000002120a03800009c1360c31b6eca4c8000ccd04e80000000d990000d4e1d88000214600030080bcc1300000000e00349cdb5bc1829638e40850f3000000bcbbb87c0d858fcc3db0014000000090913acf6a00000002d5808000000d73fb80002f40708000076000000003db450a02ac0000000000000019f0000ebd0000000370000000009041e6e0001b78d8300000003ac800000002f6800000025600000f142ef19d85752928b2b00001af80004720d04f32075100c8338e1916540002ef000000008fd1520fab02dc7573c1c6b88000ed335b2f3e41ac0003a5000025ec000000020816080001034a209dd00000000856351893428060001fa4dbf145c08b0bb4f8415cd05c0000679b704f4d0dbcfbb366e6dd134025d1d210673ec8cd1422c0001a5cc6423d86e30000bf6b8600003c20c0318244662ae0e7e0d840003510e258b3d0a000001072f90c690000223000060010b404736c4a0a8000d9831ac0002ff616411e4a4e0000dff23900000000000149c4190e480000a560000d66a98202cecd127407d2930b870000000000000042344581f18a3599e20000000000000072626fca2994ca73b087056f09606181468ced2a240000000ac613f00403b3c00038203ec1eb8b50800046c00000000c4c5a02eb43da388c000000093d0afa5a300006822160000000026d000000022b800009dca0a00000000000000000000037f80000ea00001ca8000212b09d3b7400000010343aac1a9326874b00007fa2bf2000159200001481b0200b0060000000000000000f060e8000753000000017a8000000003e00000001a9c0000612a1d21f6588aec84a3000000000000e122d0f753d7000000000000000c083f2094125380003da0a2041cc27b38acc4f2cbca3dbbd06731736829af0089a3fcc4a20a20a68c29c06a030878b2d3e08712ae6609d2902bad80b23a7582401a0461d0dc0e880dace3823547a700000003fc013487685c522a0000179c2fe00000001d34067000000000008c40e44a8b00001ce2e1098812d8fe80000f3020ec13e000061121def932c70000000107517320452e4000008d05f028fc0aa00000000a300002bb88c3000000021ac00000000002d240002f384aa800009b243c3ea1924000000086c8000d090000000000000003c46050000000375cb62044c000000039a84f40000000000000000000008a61d4800015b0d964138e8f00000001d7875d27fa361b798cc6a57469530d0e1340e8c1307a4af028704c800008192e6c44a36144e509bc63f1640c0a353aa1918d8b6d1f9c00000001d2068907b00001510000009372e10cbec48bc005a1fe8000561000000017fa3fc8164ebb1440af2351c0000000a7b00000000000f110000b25000000000000000000c6e
  | 39 => 0xd000100e387a000037c00000001501bac5313f4c551895000000002f1a7ac96d0268f64000000000000000000000139200000007980000e8400003110da4a6e00000001f14a7f3772f6c0ca0c942b92ecc90440900000f6907d09941af86d3000000039d40bb0000000379d09b808ecc830c811ca15c00031d8bb80d5c1b93070db841d855841b400037441120000000073e24100000001c10c3c0a925498000ab59c783f71fdc43313801e41898ff842247150b68fb01304d98ad660af2d4af3a2ea4b7f05b4dff8a70312227cc6500000003c58488326c00020b87e314fc0e800000002a50a552f200002e74f770000c0c8000fcd418907d150c35e80005c320f0e700000c5314e683300000001fa00003e50bab050c0980174b1522541d62b78ab607208b71adcf390000724a2c40530c1845332f436a00007dd3d0410e1cd07710000f9a0000000000050d00f64642eb8037800034d363c62f2fb067e89c800000002c00d2c00000005ce00004b500000ee27bc00036b80000000000000000000002a10000000000080904aacdf27c05fd000000000000000074f86209cde22598f103734d1437800000000dfa1ad4ae2000021b0000000092c000000000005f20003200028376cc871dc00e7345908e1b801333e785531495029348000020b49dd3902bed362a483078cb0c93842500000cf51b2808117de98e0000140425800000006ed0000a300000640000000021ae000000000000000f9800100c067a0c111d86b0070c88200007d5000044500000001604000066ce5b96e06bfb564e6d25bcbef3e840001d6400000002d08000fdf1e3000000009f43b040000000a4f0000000000022700000001a347df13100d808b80000000000000000000002872e343652852f2b00000b12a744390000b0c000000000000000000000235a06f36881230db80000000bbea30400034a2000000047100002150f902fc2245093ae3851941580000000000000000005e422d00006f51d4a00000000000000b07b6f0eb412102e311bc62bb47cc4c1d8e2038d26f96164c000356c31813747b902d800027940000084cd900009a00000000000012f8000b920cba1c4bdf0a7528502903bc8ee80660e3f000000000000000000000000102b0b1c0000000000280a0000000af600000002fea00000000002f8cdc300000001a8400028a40004064c6a03acaf4000074c80000001938f851c6cd620000e6b3fbccfd2e70a1e13a8000000000025783729bc49b13d7400033100002f5e6410000f9039101cb0000000270c14d2104000000032d1c3c12bb4b87ff370812f0fec000262cc308000db69a1452c1b6a8a438c0f530000d9b2764954263448a25180001b700003a0c5c785500000000138065408d0c0c00023003270000cb017bce64800000000000000d1
  | 40 => 0xc6139d295b1c407c21f2ae640a74000000071300000000e76397123e90d0000000000087319f000000005d022e000002f4b8900008ee2bdcd8c07eeac306b48671d84851331c70dbf943f10cf454da198dee3b84d783c3c9fb00000002bd4e7f3c9d03e1ce69f8800026500000002470000000095f144c0000038abb033caf92edc00024ec0003aa45693ee400002a0bc791ec000000044300000000000ac1000040800002c5061458d34c8cb19358f9216c8ae800b80a70340000000045d3ffc0002d5e28524bc00000000003d58334426cc460000e0d00004a90168c2729c6b5f2dc8ef300000003cf0fea100888d20bad6c0edc869407cc2a1ee8cb9207400021f80000ebc00000009131ea8bc301406e23e047e5152af5801360001d14068b5202b180000002cb40001a940d605941e38ba480e0b2031b23a49203c985cc2c8c8352dd0e630a2507c8000c56391428c8000b5737d86cf84d000035a40000000000272c0000000dc642ac000000000000000000000fb627a0e5994eca1f214061435841fa8daa8458d6818a000000000000001b64f611c9032980009ae20880000df4e7781cc5e5404c5789b849b0119d0030e54ff407dc8781da00000c9400005680000000072000020f15fc55e800000013c21b1123c4cb0000ddc0000933386c6a40778000204e00019f426f8000cf71feca8f00005b2b5a05ae115c24f000000000002bc3f0c0000a60df23d480003bf400027f80000000bf0800047d000000000003e500001b2000000035ac0000000a258000e9e00000000e65022000000024e8000000056200000001ef8000000000000004ef89b00002a4000025ac000000000016a60002b84000000000000008f80000000161821d2a08ad30000000211cf9f000000000000000000000000000000000002090000000081f0000fc6000000028f40002fd424600000000000000051ee6e0000a6800000001b2e000000050131e4794426865f0000000000000000000000d9800000000003795021000000000000000000000199c00041c828200010a50000000239c63a0000000337097c005800020a865e080279b0000d3d08f40000000bd315502cc1f4c05727200001f0aa6400000002a9c00014cc27d0000000420000000004e3000000000000000cb637f00003e12648e0400009830d58b1d91f8a112b5071136ee2362e1888635c0a159a98b3327c4c441eb4a558298d16a9c81d5065cec827e843240ec1c42ea8e4a00000003154000114803a1e0c9a42654274a5e451b16dc00000000001d04000112a87b2d5088b13b40000000000045899b20f82dc0000000000000000008203c6c81f80001ba8000449070800000000a493f4e8710ca00028f06980000dd6a544b5300000002106ba5341855f0000fe9299c00000000001d50b1
  | 41 => 0x34602f90000c5f2d56dfa8fc000000006948ec0b65000089b000000031749af2f2800000622c98000000000064f00004db032ca32000094300009e2191c77e423000000002d207b80000c70dca391c00017c42df3ea400008ac85692ce1f228405bb36caeda29b0f9c183c94a29e800000000000030000000000000001c600dc84a16b45d927f000000000000000000000000000000000000e63a2480002d5400000007ec3a7ad420ea42050000fc900003bd17d089640b800017b00001afc0001ce08508f7c000076a72c0000000420477b3ae4eaa2c1c0000000b1eab0000037e6d30000000011fe8808000000061cc993a48f5e196404a0000000107ac70800000000000000d4af25254c34c0ffc9192a18d82367824d40101c53c0482b9fd804f1fac8753f5400000000000000000000000000003640964000225085c1c8033633747cc3bf02a800009321cdcd2c000000000000001a4400005a82922ae8000000000000000003cbc00012b02070a980000000d6b8000000000000039840002d34000000000024d88553dfc00000000000000ff70000480200600030a06f40000000273c43726042e50b7a00038040002a806c800000001ac668a00004ec1cd422000000004140a02212453a000000000000000000d2900000000000b700000000000029906b2be717880000000c40987cd8a1abc015a094f7000000001fcc00000000000000000000005800000000000000000000013de0000000000000079d0000b9f082adfb8000caa0000000000000000000b99b1a0002f7c000000086e05bce5b2c44782064a00000000001d5827542200000000fd7000000000000000000000416c000000030a3360a3316d4b7d00000000000fe610b0000000000000006ef000000012e45712584d5229dc000253062d80000000000a030000d2a35d400037f0bc5b0e6ae50f5008a15c000036a0e5410a4d76283cf7d1b0600000000a30000000000000034c4f720000475240055742bc7510000000000100216aa000000000020920000000f140ce8000000028b063e70d0828bc09e38aff21c8000310eea3000000033581d48586d072500000067400004680000000000393704728f2000002849637328d400009f610d0131b6242c880000000f48185a99e5de23f03f80000000000060800000000000000000000000002ed972c7f4000010d000000037f40001b7c00004f04010000000156c0001d240000000e5a26ac000000000000000000000f0323082552804044011eaf5abde2cf831612c38a07b624047ee3cd84c71558bf01c4852b05980002950984000072512f4ec22c6033210f4150a3dca250282c5200000000d1e0000000d2f000083d8d3e0003fac0002a4c9630000b01b4449b2258878d000004eb774f4b00340000c3c24ca17c78000
  | 42 => 0xd220000ec839c2e8c000000097700008be000000000000000000ae40000000000000000000004254e9d1ca01a813140001028000000000000000002c4ca2a355c0003a80320310823203682c2a1f462e0000000000000000000002816e41000000008a00000a5a0003120dd4800000000000000188bb500002b0a0be5ab0726e5100002a91d6a0004278000000061600009ec40701491ba0000000000000000000a9c2e00000000000000026980141840000428c5a12cf8000000101500000000000e1f00000003d400003ccc00034ecb4a0000ce830c00000000000000000000006660000a7113184ba41a8000000074ba97a00000008770001001000065d0528eb81ec106e00005478000000000036d0000ca80000e6080003fc00000000000d8100002d30788c2907005a90000686017800026a0e4800008d918b2c8411a00000000000173400000000eb800006000d63790000000000043080003cd3024000001800016100000000afc0f2c4553f6c000117846000000003ff00002cc0000000000000009de396448b000000000000001694e7b0ca8135ac9200000000002bb0c4b0c5c0002b5c000129c3213244980000101e3830aca000107802aa759bf787851f4053c0fd8fb73048c8c0d8e000000042cad8444c000018d2ee6a152d044d92f50cfc19e81ab0580109143c6ab365ce532cc400000c2dec33800000000a282a7cda28b74cbf0d700002b7101a0000b2e381c10617ec05f0000000346c0002718f2d04c0b2ca9c07a600003eb2c90b371a6c831133096a0098d4a3b0e7211acc0000000b40394013511944a51a4cffa0000b9106527ab1b543a52e3c35233a4c682c68bf1bd8c22c29e4d89806cfc23074fe00a5c681b6109bd17b4a26be380001dbc00000007a0424c04c00002170000b930e900780e7e0000bbe3810520c41307c09e04200d531c800001dd0940cf0000000000032489492e080000f402f33960237044ad90b96a39a0000000357cf6e000015c00000000000000000095c1f504230000dc3800000000000000f8c00000000000000330000108522fc49310f80f63ecc0000f9c000000063d0000ac901b42cb24dcf1e0ad4a7c069477f000076c40f49c2000000000008c800005392624a8c00008b93cc4da11120000000053d00000e226a4b6a100c9f72e7aaa41edcbe20acc44e141097325f400005dc5490f3cdb037a4a422388e67a6f0000000047029244f21378184000000000000000f200000000e68000000041e800000000f229ac74000000000000caf2d7a00000000ca21807a40000e9b01d465a20200491b3cda600006694014000403c7a200009932f300b8000093903dc0001c9c000110e1fe36ce3bb25d000000010978000d790000000000023f0378000000000009de0
  | 43 => 0x4c900007730000bb100003aa00000004044000000000028d8968000000000009230bf4d130000000188a00040c462c20e00003e940e942b40002ad50420192e7300006d08000a123c6017500004420bac0003b64000000000000008288410000019881b00010980000c3300fca3727900000ae0000000000000000000000000000000023b46271c58bf20b4a7f51fa82f49d3c1fd3f1c3150000b0942a81930000a803b500000bc48ec000024680005d709ca6060000ce11954e661b186f838f6aae86d01db006891b30a665631c66790f80000213cfbe38485db0000dd080000003e30000417c00000000991ed45418000c3a00000000000e7d00000001b60000000008f0000d6400000000b320001188f0e08887c11d3807115162101c040000a346c0800000000005301d54431984800012343f400001df00003de0b0c00000005c0339c6c116c44c2b65e83627b431d181033a8000f433bbc0000000998000000000006b9369c0a68000633b1e049c0494000000063e2f6ca70981d008309829b0fd4000058c000000000000010863a14ac715222c617e000000000000a68c2121507181ffe000000000000001520c24f420cd505517c86c033b850304c4000000032b2a8c000350400000000000000000000000038cc00000000000000000349909f000000003be12caf4889800000000000ccc227839d4252f212e3012633280000390d393414000000000010e8ab2000000005f8e5880004fd97cc82f1648dcd9de40ba1a8c00000000000000000208400000000000000000000000000000000000000000000023e80000000c860d280000000279057800027daded0a808011fc4fe112ac8d71ea000000000002d3cf7640b40bd80002ab37780002a6c7500f0c9db00008df0000000000066417109153a043bf3bec0003e120002c3c000000000000004e936a4000000045f3010000000000000000000000000000000013681ac00008f92d18139000000000003ac3170511000000040dc000402441b00000000000edf00003fa00001240f88268166c00000000c800001900000000000000010c400041c09a100000003a840001fea000310c000323e00001f800000009d01454ba710d85983c8cfd61538e4d281cca41534a380658257000000007c45798000c1b4098000000094d031c0000d3634480000003d240000000d000ab40003b9c00040aa00013dc6de89ac45baf54f730000036b0eccec0c1c0b43bd8e460a3c00000000000000000000090c36b08f44194bde34e00e7a7d5079385d043010c9860dc40a12bbc76725b01d8259c67f80002b8898c2f995ce7b8405c00000000000000dc90000a8496000000d4035aadacca90000000000000000006010000ea82374af82c040002eec0000000000000051c0cf80000000000120a23e0
  | 44 => 0x469a95800000009311bdc00023a86240000000000003023247bf0000c8d0000c358000a0880000000000ef038dc79e17549e936560000dd042b1a1000000008931b58a2b35b45b93a4a00035500a51928c850784a1b1a80b7c0364a2317500000000000000000009284b2800000005acf22282ea401c0c2c7800000000009bb37606b2000039e00006353e280000000000000000011a800000005b400000e500007da2060b9900000000000c7700000c4800016e0000a272cb0b2241b00000a04ef538502731932c070d1a60787b4afb2b687b581206cc00005fdaac4a8980003fb800086a2d8c9030000f8305220002a0c8840bb80003284b3906782f51f80b441aa8e6980e430d30b40000000cb72a580000000863002a2430000d553ad40000000ec01b0c00000000000000ea514b40003e444f302a60000000000000020600ee0001ff0daf9bb60000000dc8968870a10944b200000001a7800035d000012dc1bb00000000000e1c34acb18b058b953078ce500000003080e9100008a1000080a00007922fe8657176105a389c316231ce560ce43738c0000000007780000a4d00000002d640000690ebc80002250000000000000000000ff0000000000095638902bf8ab0668171875080010390000000000000013a0fac00007173b5e0000000df300007472cf000000006d700008cd00000003c249b08000b383a540003c14000000000000000002ba800036e600000007361290b6d897c000000061508980000000a591c96e8200000000000fd02a4849f0cec00000000e01cca7753dac645251462a2adca16b56882da48e0003b0c00027ce00000000000000000000000000005962cd000000000001d18b58030056829480004028b6c00000000000000000000000003a20ee0c510454c49bc2c00034482ae0000000212e2f02f10db8963000034340e600000000000000000067f000000000001ff000001e0000e1e38c80000a7c00019b402a8000000008800012683a03082e8e8000269000000039c4a1600000000000b3214a0e7380004a13534fa32fa800000000000000d92000000000008e500006c4a5b819cbc28c2c2f94f1d40607860288136bcae79305fcb45064e79f1aecd0c385200020409e039e28ff000080c09d8363000000000000000254bb41580650271c0d300000002af4018055c3be00000612c78000000000030640003e98aaf36d8f4181b0c2241f00000000e670000029800000003f418ab0eae3a0000000000000000008810000ea20b1ac42879eb5c8000000000000000003b3000071a32089d50000a178afcaa239064104160c980cdca8a29d00ed35bc6d426740cd3782142000102a045c0ae08cc29e0000acc1f3459a00805782ecc0000000000000000000000000000bba09e0ff91ade00000000000000
  | 45 => 0x8d5e002000014389fd3b5200000000001628000075c9163d54b9a266841a00002de00000003a3400000007312c560003d9c00000000002dd87c02a0e8612f3c000318000021b047f1720551000000000000ba80002f2000087e92542862c7ccd5a318745a08c9990000c8123a07a135560001d6cea70e380972e7860a2aa072900000002784000102400000006c920e4000198c00017986420dd4ebe000000016f02471ff4093000000000002d7359ce3d000004b0da0b6700000000d6012d16b2c052bcc5df33c000000000001ccc0002dd40001c1c00024a407b39240003740bf3079858b00000000000000371c0000000000343c00023442030000f0403cc76625c80000000bd921e20000b34000000052402c0a34bc305b0000000018a05fc00008452b6c6c7808c7c4000079a8ad66533dc41cc38400004048f60393e19082b0a573b8d095aab88401dac2b3bae88cc24e0259846c00035440000000000000035d2ef20000000177afe400000000000000000000000034645e026940b313c02ff0000000299400006190a61280a353be8f159e240000000000318871d1b0ab002a38a952e8aeb604e6c362a70a630400e5d8e507ce3ee869f1b1cdfb424800000000000000a1a319c000000012908d4000014486d07cc7582de0e0f3b2c00000000000aa8000000000000004f60dc803d00002183a6834b8000d24000017b000000002864be3d280000d4200038f04992efceb10c1504f1218132af9600017e476e373c682a21a00000000003ef400031284691b083b900000000000df88fbc4c0291c39f005e0000f60c6d20160000000fec00003c22228000000000003e0000000018800003d700000001400000000000013d6d22000000006bc0002c5c00000009a8a01400000006743040ef800000000090000392c454000094708160000000000000023816a09c50a763f2000000004c87320b02000000078f00000000000000105c00000000000d7c00038a807c3854000000000000004ad0000a0500000000000ba8000000000008120000000000000011f600000008d8000000000000003d00000000009d00000000000826000000031000000000f6f381800015ca11d0000000000078400000002b8a93c10500001bd80000000ace384400031d400019bc0000d3800009f800022d50a800000000000cf40abc68e08300191cfe6cd38f82490000000096888787705e3064907e21b60003468dc0b4d0252278c00027e406e0684d503b9000000003fd0000c28924824421d80000000000232c000000062d2078e03800028a0c4099000003d91414695c1c4000040c56b30e4faf17908372998b281bf883400003d53a987c71460ec6aa10f5b34d400000004af963c00039d8547000032a92deb970000ac539088ab0df8f4724684c3399aa48
  | 46 => 0xbe18000fa80000c0b0e0800000001b80000000000000000000001af0bfb04849c040e01e6800000025e8c963440df51b9ceaf0c04c7a3726283220cc0108503438000c7d249417615b881c415c56d0f440000000d9501aceb700007cf2ca487f31140000000e5f0000ac4199403b0d2000009e8119000039e96443608000689000077a00000000e72bf13f3000000001011cbc81a349400024b400037e4000191aa260e6ed2d1e7073e0000ce400007440000ae300c429537a90323acc00000000000f180003974cd519acf340bc2df03956b2098ec0001bb8f1300000001e1d06007b0000000000000cc0001c7c64c00000002f5c0000e9c9cd0000f822f46e02046ea9710ed035000000b26303830af85988aaeb2a071cb4c06cc47c16f44821420d530000bfe00007430000000000000001e4000000000000000003bf85ad8000000000000000000000000b5a00000000000daf34cc648221d04d0000e3ca368000000000005a421f0a3818c373e0000000cc101080002aa600000002040b280000000000000000000000fb2224000365000000006c40000c5a0000e3b0000000397013639b024800002802ada000000000000000001010d8b00005348000000150a0000000000098800014740000000000000086228eaae93694f793bc49483e1cfe4000000000002fb14da0912478fcf11ac5469fe0b3635f0fda0000e7a0000842941cae003c000000004dc00000000000c702ef6d23408c4120bdc8790000fbf000064b3c5c0000000000000026e000004f988200009e21b6285ce23be64068217863487f20003b948af1541099aaaccd4000002a3060504bd7cdda000000011b4000000000000005203776847a81000032b40002d70000000025c0000b982ef8da33e8091f0bce000274450228841eead829143580b42423ce9f3378646042c1f993c400000a4563000092e00000002cce58705f400000000003fd4f4c1950e8e4240aac18880001ad04072b3c4f822004e621f00003988afd26cc00039a86a22e5800016cc000000000000000000ddc1622c26c90852a52a1eecb77000092a076ecd70b60f800000b0d800000000000000000000000000000000003f5000000000000000000000049e0000cb51508865000000024c00000000e860d450928e9aede41243558000f3f0000000000048711e806429e1097353cb5b0000c7f18a4adf062cc94902c30c1518f9710d40002da41cf3b48b1000000000cfcb3b1ce283d2c9d09c000000000008140000fad14840701b68000291463930bcd720dfa1e71e68fae2b48b430a9024db470e961bb011f2c7eb08b5a88e618d07b23790f7e17b85af1224d8000008ada3324900adc0860330b8b0000d5da1480003314180bcdc0000000f8900000000670109a3c400010e00000000e722e2
  | 47 => 0x37300db2c08ee907ec0002eb0e9701582c11cf4f280000319000000026b00000000000000000000000000000000336c00000002a1bbe4b523b5c57a0000000000087435ec0000000f4f094cba10000a5000000003ab000000004200000a0b0ba02a5171c5990000d0b0ae4fcb0848e4331401df800000000000002c3e0000000de8000085280000000000000275041c00944440aa653e0138a5d237897e000073c0c7633e86b6000000000000000000000935074cb64000068701942a7b45e9d738b03dc000000006a873f3a368eb00009ca05584730c2072b00000000b2a68c00001eba8340000000df736cce60156800000000000dae0000bb007a2110cbb0000f380000000183e69c08080d20000b510000200000000006fc806a2704210000ef7380c0002af00002ab4c3e87e458325c06f20000bcd1ce82ce0f740000c8c9f800000001df0885395aeff173e0001df402780000e480006a384ec00
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x40103e9815376553310040fa60545d954cc40122f985505498b310048be615415162cc40149497590714cb310052625d641c132cc401c1875590704cb31007221d2621c132cc401c91641c4704cb3100730988711c132cc40103d9815376552210040fa60545d9548840103f985d475d91210040f660549d9544840103e98150765512100661105831c9540840121f985505498c2100487e6154151630840160c925505458c2100534640711c163084f7cc2631c4704c82100558a57411c132084e55c293d04704c82114631e1b874cb31084018c7865d932cc42100670e1c804cb3108401b808420132cc42100649214845c831084019a074201324842100427259831c9545000109d972095418d4045487e6154d48635000181e5461c5218d400068655180144635011322f9855352d89400650725d5418d5250001c155418c71549400060718f855ce4250001a3154600511854000427259831c9415007d81c8755063541400040fe61751d5640c00181c7361472590300040fa6054dd9540c00103e9815176550300048be6154152620c00122f9855054588301e417261655ce420c0b909e97a1d644c830006261c087591320c00181c87dd5644c8300060721c75591320c001c18701d5644c830007221c074989320c00149497593714c8300052525d641c5320c001c91641c0714c83000730988701c5320c00149897593704c8300048de6154152610c00123798550545843000634200874c9610c00189487e1132584300062521c844c9610c001a908021132584300063421f804c9610c0014b19010776504300058c64041595410c0016a190105625043000487e615415263c800121f985505458f203df3098c711c132c80678cb86e1d320c32018632e19764c830c80f7ac386205320c3200040fe61751d5648800103e9815376552200040fa60545d95488001237985505498620005892495415261880012379855054586200052c64041dd9418800163190105655062000709106651c9418800141d9519073591200050d654641c564480014359510871591200040f660549d9544800103d9815076551200052c640411d94148001a248521162087100040fe61751d7644400103d9815276551100040fa60541d954440014369115076551100050e640541d9544400121f9855054d8d1000487e6154150634400122f9855054d89100048be615415062440010d49660c72505103670c1c06519131440d7ca070190624c510347301c06318931440018d070219324c51000705194645cc214404f0d696e1f63085100062561f6418c21440018958719063085100053165c63d882144001c84645cc62085100053165c63188214400103f985d475590100050b249751d5640400103e9815376550100040fa60545d9540400182c542097655010
  | 1 => 0x1e54ca20e8300074408000c07001b600000023c3271001343600378005e004191096680016a00290280000990000000331a1484e543f0101e302a8000d9a46d7040002998844a50e2912032000002a002c1800077400acf4000000138311f962920e36ab83e21351ed0e6ea41e11ca916284bc943a860f83e0b197545a1b995563a2608d366c49078ec35af9900667001028a574e8b9303d319ac00a32c8950c17068691451002b12ca02da7c0000000d8260248999122a000006d00000e1500834a9d2a5d1ca08786100a207643250a0d909890912e6e280410a0a56a7916422b0004c0b2713cfa0016a4ce400000441241a08f2e67023234fe40460508eaf1a8230808110e11030800000f0b03000014000024092e0a390903001807030c0406130705010f08010512020202050001150b000005020200225801210410150500000050ba58549ca635500142e961517298d540050da58549c66355001436961517198d540050da5854dc5625500143696150715895400507a58549cc625500141e96151731895400543648545cc625500141d97152731895400583648549cc625500141d97151731895400583648545cc625500142e9615372585540050ba58541c96155001a2454209611855400507a5854dcd605500141e9615073581540050ba5854dc9605500142e9615072581540050da5854dc560550014369615071581540050da58549c460550014369615171181540054c640545c4605511722f985535258a432240f261655d252908bf82c7620954549420058c6407555061508e7a27852095418542006895518214c615090723798553521854209c8d2615454861508278348755152185420058924954548615087d03d9815376553321f507a4c54dd954cc80103e9815176553320040fe61751d7644c80103d9815276551320040fa60541d9544c80141e9315076551320050b648541d9544c8012379855054d85320048de6154150614c8016249255054185320048ee6154153604c80123b9855054181320058a24954150604c801628955084218132005a824542108604c8014a696104725954100709194411c96550401c24511047259541006a1105831486250401c24411d4624c94100728188411c132504015319010575181410040fe61751d564cc
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x8000642000941285921517318954004c0942c90a9398c4aa002604a1648545cc62550e781243924aa2a430a8400909285921507655132
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x5
  | 2 => 0x1
  | 3 => 0x4d
  | 4 => 0x4
  | 5 => 0x94d
  | 6 => 0x124d
  | 7 => 0x138d
  | 8 => 0x8d
  | 9 => 0x98d
  | 10 => 0x128d
  | 11 => 0x150d
  | 12 => 0xcd
  | 13 => 0x9cd
  | 14 => 0x12cd
  | 15 => 0x168d
  | 16 => 0xa0e
  | 17 => 0x6
  | 18 => 0x130e
  | 19 => 0x20d
  | 20 => 0xb0d
  | 21 => 0x140d
  | 22 => 0x154d
  | 23 => 0x24d
  | 24 => 0xb4d
  | 25 => 0x144d
  | 26 => 0x16cd
  | 27 => 0xb8e
  | 28 => 0x148e
  | 29 => 0x3cd
  | 30 => 0xccd
  | 31 => 0x15cd
  | 32 => 0x170d
  | 33 => 0xd0e
  | 34 => 0x160e
  | 35 => 0xe8e
  | 36 => 0x178e
  | 37 => 0x4e
  | 38 => 0x209
  | 39 => 0x20c
  | 40 => 0x154c
  | 41 => 0x1449
  | 42 => 0x1489
  | 43 => 0x94e
  | 44 => 0x1409
  | 45 => 0x249
  | 46 => 0x289
  | 47 => 0xcc9
  | 48 => 0x1709
  | 49 => 0x124e
  | 50 => 0x138e
  | 51 => 0x8c
  | 52 => 0x150c
  | 53 => 0x20095
  | 54 => 0x8e
  | 55 => 0x98e
  | 56 => 0x21295
  | 57 => 0x128e
  | 58 => 0xd515
  | 59 => 0x150e
  | 60 => 0xce
  | 61 => 0x160c
  | 62 => 0x104c
  | 63 => 0x9ce
  | 64 => 0x12ce
  | 65 => 0x18c9
  | 66 => 0x168e
  | 67 => 0xa4d
  | 68 => 0x164d
  | 69 => 0x589
  | 70 => 0x198d
  | 71 => 0x134d
  | 72 => 0x154215
  | 73 => 0xcc215
  | 74 => 0x15c215
  | 75 => 0x20e
  | 76 => 0xb0e
  | 77 => 0x140e
  | 78 => 0x154e
  | 79 => 0x24e
  | 80 => 0xb4e
  | 81 => 0x144e
  | 82 => 0x16ce
  | 83 => 0xbcd
  | 84 => 0x14cd
  | 85 => 0x2cd
  | 86 => 0xd4d
  | 87 => 0xecd
  | 88 => 0x17cd
  | 89 => 0x19cd
  | 90 => 0x3ce
  | 91 => 0xcce
  | 92 => 0x40c
  | 93 => 0x15ce
  | 94 => 0x170e
  | 95 => 0x44d
  | 96 => 0x1a0d
  | 97 => 0x1a4d
  | 98 => 0x194c
  | 99 => 0x14d
  | 100 => 0x184e
  | 101 => 0x40e
  | 102 => 0x5cd
  | 103 => 0x18ce
  | 104 => 0x24211
  | 105 => 0x2c9
  | 106 => 0x14c9
  | 107 => 0x28211
  | 108 => 0x2c291
  | 109 => 0x44095
  | 110 => 0x45295
  | 111 => 0x164c
  | 112 => 0xd655
  | 113 => 0x440d5
  | 114 => 0x8214
  | 115 => 0x44215
  | 116 => 0x154216
  | 117 => 0x45415
  | 118 => 0x21555
  | 119 => 0x20cd5
  | 120 => 0x215d5
  | 121 => 0x1a0215
  | 122 => 0xbc2d5
  | 123 => 0x20094
  | 124 => 0x44c
  | 125 => 0x44cd5
  | 126 => 0x455d5
  | 127 => 0x164215
  | 128 => 0x45555
  | 129 => 0x21655
  | 130 => 0x21a15
  | 131 => 0x20455
  | 132 => 0x165555
  | 133 => 0x45655
  | 134 => 0x1a57d5
  | 135 => 0x41616
  | 136 => 0x17da55
  | 137 => 0x128455
  | 138 => 0xc455
  | 139 => 0xcc455
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 43
  | 7 => 2002
  | 6 => 8369
  | 5 => 4272
  | 4 => 176
  | 3 => 5
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 9 => packedAt gbK9 (i*15) 6
  | 8 => packedAt gbK8 (i*26) 17
  | 7 => packedAt gbK7 (i*37) 28
  | 6 => packedAt gbK6 (i*48) 39
  | 5 => packedAt gbK5 (i*59) 50
  | 4 => packedAt gbK4 (i*70) 61
  | 3 => packedAt gbK3 (i*81) 72
  | _ => 0
def gbH (k i : Nat) : Nat :=
  match k with
  | 9 => gbHint (packedAt gbK9 (i*15+6) 9)
  | 8 => gbHint (packedAt gbK8 (i*26+17) 9)
  | 7 => gbHint (packedAt gbK7 (i*37+28) 9)
  | 6 => gbHint (packedAt gbK6 (i*48+39) 9)
  | 5 => gbHint (packedAt gbK5 (i*59+50) 9)
  | 4 => gbHint (packedAt gbK4 (i*70+61) 9)
  | 3 => gbHint (packedAt gbK3 (i*81+72) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 9 => packedAt gbK9 (16+((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 2)*1) 1
  | 8 => packedAt gbK8 (1258+((h/20+packedAt gbK8 (1118+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (84874+((h/900+packedAt gbK7 (74074+(h % 900)*12) 12) % 3243)*12) 12
  | 6 => packedAt gbK6 (449074+((h/3383+packedAt gbK6 (401712+(h % 3383)*14) 14) % 13400)*15) 15
  | 5 => packedAt gbK5 (274083+((h/1695+packedAt gbK5 (252048+(h % 1695)*13) 13) % 8124)*14) 14
  | 4 => packedAt gbK4 (12824+((h/63+packedAt gbK4 (12320+(h % 63)*8) 8) % 230)*9) 9
  | 3 => packedAt gbK3 (408+((h/1+packedAt gbK3 (405+(h % 1)*3) 3) % 7)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x1ffc07ffffff007fffffffffd8731f8e3f1fff
  | 1 => 0xe03ff81f807fff80f81fe00fef9cecf1d9e267
  | 2 => 0xffffffe0007fffffffe0000ff01ff0ffe1ff87
  | 3 => 0x3fffffff800000fffffff03fe0ff01fe03f8
  | 4 => 0x3fffffffffffff000000003fff0001fffc00
  | 5 => 0xffc0000000000000000000003ffffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0xa4800b2a4cb0829182a2a6c483105860b0cab
  | 1 => 0xa21c58158c555a88691f40ae8b946cb0d96265
  | 2 => 0xd4a6ad601026a352b7410143300ab05b60b786
  | 3 => 0x8437364959003210c795958235c0fa01f40350
  | 4 => 0x183bc79e7e78fc7c020606043eff0001bfd800
  | 5 => 0x1f0204106040c060041818083f7fdfec000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeee0eae0eae0aa80eee0eae0eae0aa80eee0eae0eae0aa80eee0eae0eae0aa80eee0eae0eae0aa80eee0eae0eae0aa80eee0eae0eae0aa80eee0eae0eae0aa80, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_16243
namespace PEqualNP.Outside.L_meta_16243
open PEqualNP.Outside.L_meta_16243.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 9 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 14 := bs0_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 1 := bs0_5_0
theorem alls0 : ∀ k ≤ 5, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
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
theorem bs2_3_0 : Interval s2Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 1 := bs2_3_0
theorem alls2 : ∀ k ≤ 3, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 3 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 10 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 13 := bs3_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 1 := bs3_5_0
theorem alls3 : ∀ k ≤ 5, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 4 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 24 := bs4_3_0
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
theorem bs4_4_96 : Interval s4Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 117 := (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 bs4_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 46 := (concat bs4_5_0 bs4_5_32)
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
theorem bs5_2_0 : Interval s5Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 4 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 24 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_32 : Interval s5Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_64 : Interval s5Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_96 : Interval s5Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 117 := (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 bs5_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 46 := (concat bs5_5_0 bs5_5_32)
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
theorem bgb_3_0 : Interval gbAtlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 5 := bgb_3_0
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
theorem bgb_4_160 : Interval gbAtlas 4 160 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 176 := (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat bgb_4_96 (concat bgb_4_128 bgb_4_160)))
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
theorem bgb_5_4256 : Interval gbAtlas 5 4256 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 4272 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 bgb_5_480)))) (concat (concat (concat (concat bgb_5_512 bgb_5_544) (concat bgb_5_576 bgb_5_608)) (concat (concat bgb_5_640 bgb_5_672) (concat bgb_5_704 bgb_5_736))) (concat (concat (concat bgb_5_768 bgb_5_800) (concat bgb_5_832 bgb_5_864)) (concat (concat bgb_5_896 bgb_5_928) (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)))))) (concat (concat (concat (concat (concat bgb_5_1056 bgb_5_1088) (concat bgb_5_1120 bgb_5_1152)) (concat (concat bgb_5_1184 bgb_5_1216) (concat bgb_5_1248 bgb_5_1280))) (concat (concat (concat bgb_5_1312 bgb_5_1344) (concat bgb_5_1376 bgb_5_1408)) (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 (concat bgb_5_1536 bgb_5_1568))))) (concat (concat (concat (concat bgb_5_1600 bgb_5_1632) (concat bgb_5_1664 bgb_5_1696)) (concat (concat bgb_5_1728 bgb_5_1760) (concat bgb_5_1792 bgb_5_1824))) (concat (concat (concat bgb_5_1856 bgb_5_1888) (concat bgb_5_1920 bgb_5_1952)) (concat (concat bgb_5_1984 bgb_5_2016) (concat bgb_5_2048 (concat bgb_5_2080 bgb_5_2112))))))) (concat (concat (concat (concat (concat (concat bgb_5_2144 bgb_5_2176) (concat bgb_5_2208 bgb_5_2240)) (concat (concat bgb_5_2272 bgb_5_2304) (concat bgb_5_2336 bgb_5_2368))) (concat (concat (concat bgb_5_2400 bgb_5_2432) (concat bgb_5_2464 bgb_5_2496)) (concat (concat bgb_5_2528 bgb_5_2560) (concat bgb_5_2592 bgb_5_2624)))) (concat (concat (concat (concat bgb_5_2656 bgb_5_2688) (concat bgb_5_2720 bgb_5_2752)) (concat (concat bgb_5_2784 bgb_5_2816) (concat bgb_5_2848 bgb_5_2880))) (concat (concat (concat bgb_5_2912 bgb_5_2944) (concat bgb_5_2976 bgb_5_3008)) (concat (concat bgb_5_3040 bgb_5_3072) (concat bgb_5_3104 (concat bgb_5_3136 bgb_5_3168)))))) (concat (concat (concat (concat (concat bgb_5_3200 bgb_5_3232) (concat bgb_5_3264 bgb_5_3296)) (concat (concat bgb_5_3328 bgb_5_3360) (concat bgb_5_3392 bgb_5_3424))) (concat (concat (concat bgb_5_3456 bgb_5_3488) (concat bgb_5_3520 bgb_5_3552)) (concat (concat bgb_5_3584 bgb_5_3616) (concat bgb_5_3648 (concat bgb_5_3680 bgb_5_3712))))) (concat (concat (concat (concat bgb_5_3744 bgb_5_3776) (concat bgb_5_3808 bgb_5_3840)) (concat (concat bgb_5_3872 bgb_5_3904) (concat bgb_5_3936 bgb_5_3968))) (concat (concat (concat bgb_5_4000 bgb_5_4032) (concat bgb_5_4064 bgb_5_4096)) (concat (concat bgb_5_4128 bgb_5_4160) (concat bgb_5_4192 (concat bgb_5_4224 bgb_5_4256))))))))
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
theorem bgb_6_1824 : Interval gbAtlas 6 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1856 : Interval gbAtlas 6 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1888 : Interval gbAtlas 6 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1920 : Interval gbAtlas 6 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1952 : Interval gbAtlas 6 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1984 : Interval gbAtlas 6 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2016 : Interval gbAtlas 6 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2048 : Interval gbAtlas 6 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2080 : Interval gbAtlas 6 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2112 : Interval gbAtlas 6 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2144 : Interval gbAtlas 6 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2176 : Interval gbAtlas 6 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2208 : Interval gbAtlas 6 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2240 : Interval gbAtlas 6 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2272 : Interval gbAtlas 6 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2304 : Interval gbAtlas 6 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2336 : Interval gbAtlas 6 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2368 : Interval gbAtlas 6 2368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2400 : Interval gbAtlas 6 2400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2432 : Interval gbAtlas 6 2432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2464 : Interval gbAtlas 6 2464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2496 : Interval gbAtlas 6 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2528 : Interval gbAtlas 6 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2560 : Interval gbAtlas 6 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2592 : Interval gbAtlas 6 2592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2624 : Interval gbAtlas 6 2624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2656 : Interval gbAtlas 6 2656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2688 : Interval gbAtlas 6 2688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2720 : Interval gbAtlas 6 2720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2752 : Interval gbAtlas 6 2752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2784 : Interval gbAtlas 6 2784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2816 : Interval gbAtlas 6 2816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2848 : Interval gbAtlas 6 2848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2880 : Interval gbAtlas 6 2880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2912 : Interval gbAtlas 6 2912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2944 : Interval gbAtlas 6 2944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2976 : Interval gbAtlas 6 2976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3008 : Interval gbAtlas 6 3008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3040 : Interval gbAtlas 6 3040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3072 : Interval gbAtlas 6 3072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3104 : Interval gbAtlas 6 3104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3136 : Interval gbAtlas 6 3136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3168 : Interval gbAtlas 6 3168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3200 : Interval gbAtlas 6 3200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3232 : Interval gbAtlas 6 3232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3264 : Interval gbAtlas 6 3264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3296 : Interval gbAtlas 6 3296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3328 : Interval gbAtlas 6 3328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3360 : Interval gbAtlas 6 3360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3392 : Interval gbAtlas 6 3392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3424 : Interval gbAtlas 6 3424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3456 : Interval gbAtlas 6 3456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3488 : Interval gbAtlas 6 3488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3520 : Interval gbAtlas 6 3520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3552 : Interval gbAtlas 6 3552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3584 : Interval gbAtlas 6 3584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3616 : Interval gbAtlas 6 3616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3648 : Interval gbAtlas 6 3648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3680 : Interval gbAtlas 6 3680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3712 : Interval gbAtlas 6 3712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3744 : Interval gbAtlas 6 3744 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3776 : Interval gbAtlas 6 3776 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3808 : Interval gbAtlas 6 3808 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3840 : Interval gbAtlas 6 3840 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3872 : Interval gbAtlas 6 3872 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3904 : Interval gbAtlas 6 3904 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3936 : Interval gbAtlas 6 3936 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3968 : Interval gbAtlas 6 3968 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4000 : Interval gbAtlas 6 4000 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4032 : Interval gbAtlas 6 4032 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4064 : Interval gbAtlas 6 4064 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4096 : Interval gbAtlas 6 4096 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4128 : Interval gbAtlas 6 4128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4160 : Interval gbAtlas 6 4160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4192 : Interval gbAtlas 6 4192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4224 : Interval gbAtlas 6 4224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4256 : Interval gbAtlas 6 4256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4288 : Interval gbAtlas 6 4288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4320 : Interval gbAtlas 6 4320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4352 : Interval gbAtlas 6 4352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4384 : Interval gbAtlas 6 4384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4416 : Interval gbAtlas 6 4416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4448 : Interval gbAtlas 6 4448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4480 : Interval gbAtlas 6 4480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4512 : Interval gbAtlas 6 4512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4544 : Interval gbAtlas 6 4544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4576 : Interval gbAtlas 6 4576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4608 : Interval gbAtlas 6 4608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4640 : Interval gbAtlas 6 4640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4672 : Interval gbAtlas 6 4672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4704 : Interval gbAtlas 6 4704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4736 : Interval gbAtlas 6 4736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4768 : Interval gbAtlas 6 4768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4800 : Interval gbAtlas 6 4800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4832 : Interval gbAtlas 6 4832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4864 : Interval gbAtlas 6 4864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4896 : Interval gbAtlas 6 4896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4928 : Interval gbAtlas 6 4928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4960 : Interval gbAtlas 6 4960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4992 : Interval gbAtlas 6 4992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5024 : Interval gbAtlas 6 5024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5056 : Interval gbAtlas 6 5056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5088 : Interval gbAtlas 6 5088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5120 : Interval gbAtlas 6 5120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5152 : Interval gbAtlas 6 5152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5184 : Interval gbAtlas 6 5184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5216 : Interval gbAtlas 6 5216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5248 : Interval gbAtlas 6 5248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5280 : Interval gbAtlas 6 5280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5312 : Interval gbAtlas 6 5312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5344 : Interval gbAtlas 6 5344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5376 : Interval gbAtlas 6 5376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5408 : Interval gbAtlas 6 5408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5440 : Interval gbAtlas 6 5440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5472 : Interval gbAtlas 6 5472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5504 : Interval gbAtlas 6 5504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5536 : Interval gbAtlas 6 5536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5568 : Interval gbAtlas 6 5568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5600 : Interval gbAtlas 6 5600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5632 : Interval gbAtlas 6 5632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5664 : Interval gbAtlas 6 5664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5696 : Interval gbAtlas 6 5696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5728 : Interval gbAtlas 6 5728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5760 : Interval gbAtlas 6 5760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5792 : Interval gbAtlas 6 5792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5824 : Interval gbAtlas 6 5824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5856 : Interval gbAtlas 6 5856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5888 : Interval gbAtlas 6 5888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5920 : Interval gbAtlas 6 5920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5952 : Interval gbAtlas 6 5952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5984 : Interval gbAtlas 6 5984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6016 : Interval gbAtlas 6 6016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6048 : Interval gbAtlas 6 6048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6080 : Interval gbAtlas 6 6080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6112 : Interval gbAtlas 6 6112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6144 : Interval gbAtlas 6 6144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6176 : Interval gbAtlas 6 6176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6208 : Interval gbAtlas 6 6208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6240 : Interval gbAtlas 6 6240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6272 : Interval gbAtlas 6 6272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6304 : Interval gbAtlas 6 6304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6336 : Interval gbAtlas 6 6336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6368 : Interval gbAtlas 6 6368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6400 : Interval gbAtlas 6 6400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6432 : Interval gbAtlas 6 6432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6464 : Interval gbAtlas 6 6464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6496 : Interval gbAtlas 6 6496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6528 : Interval gbAtlas 6 6528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6560 : Interval gbAtlas 6 6560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6592 : Interval gbAtlas 6 6592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6624 : Interval gbAtlas 6 6624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6656 : Interval gbAtlas 6 6656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6688 : Interval gbAtlas 6 6688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6720 : Interval gbAtlas 6 6720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6752 : Interval gbAtlas 6 6752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6784 : Interval gbAtlas 6 6784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6816 : Interval gbAtlas 6 6816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6848 : Interval gbAtlas 6 6848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6880 : Interval gbAtlas 6 6880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6912 : Interval gbAtlas 6 6912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6944 : Interval gbAtlas 6 6944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6976 : Interval gbAtlas 6 6976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7008 : Interval gbAtlas 6 7008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7040 : Interval gbAtlas 6 7040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7072 : Interval gbAtlas 6 7072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7104 : Interval gbAtlas 6 7104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7136 : Interval gbAtlas 6 7136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7168 : Interval gbAtlas 6 7168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7200 : Interval gbAtlas 6 7200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7232 : Interval gbAtlas 6 7232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7264 : Interval gbAtlas 6 7264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7296 : Interval gbAtlas 6 7296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7328 : Interval gbAtlas 6 7328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7360 : Interval gbAtlas 6 7360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7392 : Interval gbAtlas 6 7392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7424 : Interval gbAtlas 6 7424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7456 : Interval gbAtlas 6 7456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7488 : Interval gbAtlas 6 7488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7520 : Interval gbAtlas 6 7520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7552 : Interval gbAtlas 6 7552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7584 : Interval gbAtlas 6 7584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7616 : Interval gbAtlas 6 7616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7648 : Interval gbAtlas 6 7648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7680 : Interval gbAtlas 6 7680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7712 : Interval gbAtlas 6 7712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7744 : Interval gbAtlas 6 7744 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7776 : Interval gbAtlas 6 7776 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7808 : Interval gbAtlas 6 7808 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7840 : Interval gbAtlas 6 7840 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7872 : Interval gbAtlas 6 7872 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7904 : Interval gbAtlas 6 7904 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7936 : Interval gbAtlas 6 7936 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7968 : Interval gbAtlas 6 7968 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8000 : Interval gbAtlas 6 8000 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8032 : Interval gbAtlas 6 8032 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8064 : Interval gbAtlas 6 8064 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8096 : Interval gbAtlas 6 8096 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8128 : Interval gbAtlas 6 8128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8160 : Interval gbAtlas 6 8160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8192 : Interval gbAtlas 6 8192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8224 : Interval gbAtlas 6 8224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8256 : Interval gbAtlas 6 8256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8288 : Interval gbAtlas 6 8288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8320 : Interval gbAtlas 6 8320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8352 : Interval gbAtlas 6 8352 17 := block_range (n:=17) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 8369 := (concat (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224))) (concat (concat (concat bgb_6_256 bgb_6_288) (concat bgb_6_320 bgb_6_352)) (concat (concat bgb_6_384 bgb_6_416) (concat bgb_6_448 bgb_6_480)))) (concat (concat (concat (concat bgb_6_512 bgb_6_544) (concat bgb_6_576 bgb_6_608)) (concat (concat bgb_6_640 bgb_6_672) (concat bgb_6_704 bgb_6_736))) (concat (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 bgb_6_864)) (concat (concat bgb_6_896 bgb_6_928) (concat bgb_6_960 bgb_6_992))))) (concat (concat (concat (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 bgb_6_1120)) (concat (concat bgb_6_1152 bgb_6_1184) (concat bgb_6_1216 bgb_6_1248))) (concat (concat (concat bgb_6_1280 bgb_6_1312) (concat bgb_6_1344 bgb_6_1376)) (concat (concat bgb_6_1408 bgb_6_1440) (concat bgb_6_1472 bgb_6_1504)))) (concat (concat (concat (concat bgb_6_1536 bgb_6_1568) (concat bgb_6_1600 bgb_6_1632)) (concat (concat bgb_6_1664 bgb_6_1696) (concat bgb_6_1728 bgb_6_1760))) (concat (concat (concat bgb_6_1792 bgb_6_1824) (concat bgb_6_1856 bgb_6_1888)) (concat (concat bgb_6_1920 bgb_6_1952) (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048))))))) (concat (concat (concat (concat (concat (concat bgb_6_2080 bgb_6_2112) (concat bgb_6_2144 bgb_6_2176)) (concat (concat bgb_6_2208 bgb_6_2240) (concat bgb_6_2272 bgb_6_2304))) (concat (concat (concat bgb_6_2336 bgb_6_2368) (concat bgb_6_2400 bgb_6_2432)) (concat (concat bgb_6_2464 bgb_6_2496) (concat bgb_6_2528 bgb_6_2560)))) (concat (concat (concat (concat bgb_6_2592 bgb_6_2624) (concat bgb_6_2656 bgb_6_2688)) (concat (concat bgb_6_2720 bgb_6_2752) (concat bgb_6_2784 bgb_6_2816))) (concat (concat (concat bgb_6_2848 bgb_6_2880) (concat bgb_6_2912 bgb_6_2944)) (concat (concat bgb_6_2976 bgb_6_3008) (concat bgb_6_3040 (concat bgb_6_3072 bgb_6_3104)))))) (concat (concat (concat (concat (concat bgb_6_3136 bgb_6_3168) (concat bgb_6_3200 bgb_6_3232)) (concat (concat bgb_6_3264 bgb_6_3296) (concat bgb_6_3328 bgb_6_3360))) (concat (concat (concat bgb_6_3392 bgb_6_3424) (concat bgb_6_3456 bgb_6_3488)) (concat (concat bgb_6_3520 bgb_6_3552) (concat bgb_6_3584 bgb_6_3616)))) (concat (concat (concat (concat bgb_6_3648 bgb_6_3680) (concat bgb_6_3712 bgb_6_3744)) (concat (concat bgb_6_3776 bgb_6_3808) (concat bgb_6_3840 bgb_6_3872))) (concat (concat (concat bgb_6_3904 bgb_6_3936) (concat bgb_6_3968 bgb_6_4000)) (concat (concat bgb_6_4032 bgb_6_4064) (concat bgb_6_4096 (concat bgb_6_4128 bgb_6_4160)))))))) (concat (concat (concat (concat (concat (concat (concat bgb_6_4192 bgb_6_4224) (concat bgb_6_4256 bgb_6_4288)) (concat (concat bgb_6_4320 bgb_6_4352) (concat bgb_6_4384 bgb_6_4416))) (concat (concat (concat bgb_6_4448 bgb_6_4480) (concat bgb_6_4512 bgb_6_4544)) (concat (concat bgb_6_4576 bgb_6_4608) (concat bgb_6_4640 bgb_6_4672)))) (concat (concat (concat (concat bgb_6_4704 bgb_6_4736) (concat bgb_6_4768 bgb_6_4800)) (concat (concat bgb_6_4832 bgb_6_4864) (concat bgb_6_4896 bgb_6_4928))) (concat (concat (concat bgb_6_4960 bgb_6_4992) (concat bgb_6_5024 bgb_6_5056)) (concat (concat bgb_6_5088 bgb_6_5120) (concat bgb_6_5152 bgb_6_5184))))) (concat (concat (concat (concat (concat bgb_6_5216 bgb_6_5248) (concat bgb_6_5280 bgb_6_5312)) (concat (concat bgb_6_5344 bgb_6_5376) (concat bgb_6_5408 bgb_6_5440))) (concat (concat (concat bgb_6_5472 bgb_6_5504) (concat bgb_6_5536 bgb_6_5568)) (concat (concat bgb_6_5600 bgb_6_5632) (concat bgb_6_5664 bgb_6_5696)))) (concat (concat (concat (concat bgb_6_5728 bgb_6_5760) (concat bgb_6_5792 bgb_6_5824)) (concat (concat bgb_6_5856 bgb_6_5888) (concat bgb_6_5920 bgb_6_5952))) (concat (concat (concat bgb_6_5984 bgb_6_6016) (concat bgb_6_6048 bgb_6_6080)) (concat (concat bgb_6_6112 bgb_6_6144) (concat bgb_6_6176 (concat bgb_6_6208 bgb_6_6240))))))) (concat (concat (concat (concat (concat (concat bgb_6_6272 bgb_6_6304) (concat bgb_6_6336 bgb_6_6368)) (concat (concat bgb_6_6400 bgb_6_6432) (concat bgb_6_6464 bgb_6_6496))) (concat (concat (concat bgb_6_6528 bgb_6_6560) (concat bgb_6_6592 bgb_6_6624)) (concat (concat bgb_6_6656 bgb_6_6688) (concat bgb_6_6720 bgb_6_6752)))) (concat (concat (concat (concat bgb_6_6784 bgb_6_6816) (concat bgb_6_6848 bgb_6_6880)) (concat (concat bgb_6_6912 bgb_6_6944) (concat bgb_6_6976 bgb_6_7008))) (concat (concat (concat bgb_6_7040 bgb_6_7072) (concat bgb_6_7104 bgb_6_7136)) (concat (concat bgb_6_7168 bgb_6_7200) (concat bgb_6_7232 (concat bgb_6_7264 bgb_6_7296)))))) (concat (concat (concat (concat (concat bgb_6_7328 bgb_6_7360) (concat bgb_6_7392 bgb_6_7424)) (concat (concat bgb_6_7456 bgb_6_7488) (concat bgb_6_7520 bgb_6_7552))) (concat (concat (concat bgb_6_7584 bgb_6_7616) (concat bgb_6_7648 bgb_6_7680)) (concat (concat bgb_6_7712 bgb_6_7744) (concat bgb_6_7776 bgb_6_7808)))) (concat (concat (concat (concat bgb_6_7840 bgb_6_7872) (concat bgb_6_7904 bgb_6_7936)) (concat (concat bgb_6_7968 bgb_6_8000) (concat bgb_6_8032 bgb_6_8064))) (concat (concat (concat bgb_6_8096 bgb_6_8128) (concat bgb_6_8160 bgb_6_8192)) (concat (concat bgb_6_8224 bgb_6_8256) (concat bgb_6_8288 (concat bgb_6_8320 bgb_6_8352)))))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_32 : Interval gbAtlas 7 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_64 : Interval gbAtlas 7 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_96 : Interval gbAtlas 7 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_128 : Interval gbAtlas 7 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_160 : Interval gbAtlas 7 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_192 : Interval gbAtlas 7 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_224 : Interval gbAtlas 7 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_256 : Interval gbAtlas 7 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_288 : Interval gbAtlas 7 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_320 : Interval gbAtlas 7 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_352 : Interval gbAtlas 7 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_384 : Interval gbAtlas 7 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_416 : Interval gbAtlas 7 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_448 : Interval gbAtlas 7 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_480 : Interval gbAtlas 7 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_512 : Interval gbAtlas 7 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_544 : Interval gbAtlas 7 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_576 : Interval gbAtlas 7 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_608 : Interval gbAtlas 7 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_640 : Interval gbAtlas 7 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_672 : Interval gbAtlas 7 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_704 : Interval gbAtlas 7 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_736 : Interval gbAtlas 7 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_768 : Interval gbAtlas 7 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_800 : Interval gbAtlas 7 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_832 : Interval gbAtlas 7 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_864 : Interval gbAtlas 7 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_896 : Interval gbAtlas 7 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_928 : Interval gbAtlas 7 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_960 : Interval gbAtlas 7 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_992 : Interval gbAtlas 7 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1024 : Interval gbAtlas 7 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1056 : Interval gbAtlas 7 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1088 : Interval gbAtlas 7 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1120 : Interval gbAtlas 7 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1152 : Interval gbAtlas 7 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1184 : Interval gbAtlas 7 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1216 : Interval gbAtlas 7 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1248 : Interval gbAtlas 7 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1280 : Interval gbAtlas 7 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1312 : Interval gbAtlas 7 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1344 : Interval gbAtlas 7 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1376 : Interval gbAtlas 7 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1408 : Interval gbAtlas 7 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1440 : Interval gbAtlas 7 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1472 : Interval gbAtlas 7 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1504 : Interval gbAtlas 7 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1536 : Interval gbAtlas 7 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1568 : Interval gbAtlas 7 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1600 : Interval gbAtlas 7 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1632 : Interval gbAtlas 7 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1664 : Interval gbAtlas 7 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1696 : Interval gbAtlas 7 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1728 : Interval gbAtlas 7 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1760 : Interval gbAtlas 7 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1792 : Interval gbAtlas 7 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1824 : Interval gbAtlas 7 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1856 : Interval gbAtlas 7 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1888 : Interval gbAtlas 7 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1920 : Interval gbAtlas 7 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1952 : Interval gbAtlas 7 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1984 : Interval gbAtlas 7 1984 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2002 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat (concat bgb_7_96 bgb_7_128) (concat bgb_7_160 bgb_7_192))) (concat (concat (concat bgb_7_224 bgb_7_256) (concat bgb_7_288 bgb_7_320)) (concat (concat bgb_7_352 bgb_7_384) (concat bgb_7_416 bgb_7_448)))) (concat (concat (concat (concat bgb_7_480 bgb_7_512) (concat bgb_7_544 bgb_7_576)) (concat (concat bgb_7_608 bgb_7_640) (concat bgb_7_672 bgb_7_704))) (concat (concat (concat bgb_7_736 bgb_7_768) (concat bgb_7_800 bgb_7_832)) (concat (concat bgb_7_864 bgb_7_896) (concat bgb_7_928 bgb_7_960))))) (concat (concat (concat (concat (concat bgb_7_992 bgb_7_1024) (concat bgb_7_1056 bgb_7_1088)) (concat (concat bgb_7_1120 bgb_7_1152) (concat bgb_7_1184 bgb_7_1216))) (concat (concat (concat bgb_7_1248 bgb_7_1280) (concat bgb_7_1312 bgb_7_1344)) (concat (concat bgb_7_1376 bgb_7_1408) (concat bgb_7_1440 bgb_7_1472)))) (concat (concat (concat (concat bgb_7_1504 bgb_7_1536) (concat bgb_7_1568 bgb_7_1600)) (concat (concat bgb_7_1632 bgb_7_1664) (concat bgb_7_1696 bgb_7_1728))) (concat (concat (concat bgb_7_1760 bgb_7_1792) (concat bgb_7_1824 bgb_7_1856)) (concat (concat bgb_7_1888 bgb_7_1920) (concat bgb_7_1952 bgb_7_1984))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 43 := (concat bgb_8_0 bgb_8_32)
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
  · exact allgb_3 i (by omega) hi
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 6 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 18, 22),(inputs.getD 3 zero, 50, 58),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 17, 21),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 4 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 56, 58),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 42, 58),(inputs.getD 5 zero, 26, 58)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 5, 21)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeee0eae0eae0aa80eee0eae0eae0aa80eee0eae0eae0aa80eee0eae0eae0aa80eee0eae0eae0aa80eee0eae0eae0aa80eee0eae0eae0aa80eee0eae0eae0aa80
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4007717600 * 2 ^ 32 + 3940592256) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_16243.Model.Repr at out
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

def mono : List Gate := [⟨.and,[1,4]⟩,⟨.and,[5,6]⟩,⟨.and,[1,2]⟩,⟨.or,[4,5]⟩,⟨.and,[2,9]⟩,⟨.or,[3,8]⟩,⟨.and,[8,9]⟩,⟨.or,[10,11]⟩,⟨.or,[0,7]⟩,⟨.or,[12,14]⟩,⟨.and,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4007717600 * 2 ^ 32 + 3940592256) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4007717600 * 2 ^ 32 + 3940592256) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_16243

open PEqualNP.Outside.L_meta_16243 in
theorem PEqualNP.Outside.L_meta_16243 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4007717600 * 2 ^ 32 + 3940592256) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4007717600 * 2 ^ 32 + 3940592256) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
