import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_12833.Model
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


end PEqualNP.Outside.L_meta_12833.Model

namespace PEqualNP.Outside.L_meta_12833
open PEqualNP.Outside.L_meta_12833.Model
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

end PEqualNP.Outside.L_meta_12833

namespace PEqualNP.Outside.L_meta_12833
open PEqualNP.Outside.L_meta_12833.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x28000341541912513180e9491e0088021180001c167c00020089832e1149d109001500580000034da700808801e187014600004e00e8030820c244bff43fe43be43fd43fc43bc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x41ff30083f660107f8c020fe98041fc30083f060107fc8020f790041fe20083f440107f48020f690041f920083fea9885fd5310ff2a6217e54c43faa9885f55310fe2a6217c54c43fea7885fd4f10ff29e217e53c43faa7885f54f10fe29e217c53c43fe87887f90f10df21e21fd43c43f887886f10f10ffa96217f52c43fca5885f94b10f7296216e52c43faa5885f54b10f6a96216d52c43f8a5885f14b10ffa1621fe42c43fa85887f10b10ff99621fe32c43fa65887f0cb10ffa0e21fe41c43fa83887f10710ff98e21fe31c43fa63887f0c710ff90e21fe21c43fa43887f08710ffa0621fe40c43fa81887f10310ff98621fb30c43fc61887f4c310fe18621f830c43fe41887f88310fe90621fc20c43fea9085fd5210ff2a4217e54843faa9085f55210fe2a4217c54843fea7085fd4e10ff29c217e53843faa7085f54e10fe29c217c53843fe87087f90e10df21c21fd43843f887086f10e10ffa94217f52843fca5085f94a10fea94217d52843f8a5085f14a10ffa1421fe42843fa85087f10a10ff99421fe32843fa65087f0ca10bea8c21ff41843ee83087f90610fea0c21fc41843e883087fcc610fb98c21fe31843fa63087f0c610fa18c21ff21843fc43087d88610fe90c21f521843f843085f94210ffa0421fe40843fa81087f10210ff98421fe30843fa61087f0c210ff90421fe20843fa41087f08210ff88421f710843f621087fd5110bfaa221fe54442fca8887f55110beaa221fc54442f8a8887fd4d10bfa9a21fe53442fca6887f54d10bea9a21fc53442f8a6887fd0d10ff21a21be43443fa86887f10d10de21a21ff52442fea4887f94910bf29221fd52442faa4887f14910be29221ff42443fc84887f50910fe21221ff32443fc64887f4c910fe19221ff41443fc82887f50510fe20a21ff31443fc62887f4c510fe18a21ff21443fc42887f48510fe10a21ff40443fc80887f50110fe20221ff30443fc60887f4c110fe18221ff20443fc40887f48110fe10221ff10443f620887f84110fb08221ff54042fea8087f95010bf2a021be540427ca8087f55010beaa021bd540427aa8087f15010be2a021ff53042fea6087f94c10bf29821fd53042faa6087f14c10be29821ff43043fc86086f90c10fea1821fc430437886087fd4810bfa9021fe52042fca4087f54810bea9021fc52042f8a4087fd0810ff21021fd42043f884087fcc810ff19021fd32043f864085f94410ffa0821f741043fc82087f50410fe20821f441043fe62087dcc410ff18821fd31043f862087d0c410ff90821fe21043ec42087f48410fa90821fc21042fca0087fd0010ff20021fd40043f880087fcc010fd98021fe30043fa60087f0c010fc18021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0xe430c37c86187f50c30fe21861bc430c3b886186710c30ffa9061fe520c2fca4187f54830bea9061fc520c3fe84187f90830fea1061fc420c3fe64187f8c830fe99061fc320c3fea2187f94430bf28861fd510c2faa2187f14430ffa0861fe410c3fa82187f10430ff98861fe310c3fa62187f0c430ff90861fe210c3fa42187f08430bf28061ff400c3fc80187f50030fe20061ff300c3be60187f8c030fd18061fd300c3ba60187e4c030ffaa6417f54c83fca9905f95320feaa6417d54c83f8a9905f15320ffa9e417f53c83fca7905f94f20fea9e417d53c83f8a7905f14f20ffa1e41fe43c837c87907f50f20fe21e41bc43c83fe85907f90b20fea1641fc42c83fe65907f8cb20fe99641fc32c83fea3907f94720bf28e41f651c82eca3907f54720bea8e41f551c82eaa3907f14720ffa0e41fe41c83fa83907f10720ff98e41fe31c83fa63907f0c720ff90e41fe21c83fa43907f08720ffa0641fe40c83fa81907f10320ff98641fb30c83fc61907f4c320fe18641f830c83fea9105fd5220ff2a4417e54883faa9105f55220fe2a4417c54883fea7105fd4e20ff29c417e53883faa7105f54e20fe29c417c53883fe87107f90e20df21c41fd43883f887106f10e20bea9441ff42883de85107f90a20fea1441fc42883d885107fcca20f799441fe32883fa65107f0ca20f619441ff51883fca3105f94620fea8c417d51883f8a3107fd0620ff20c41fd41883f883107fcc620ff18c41fd31883f863107fc8620f790c41fe21883fa43107b48620fe10c417e50883fe81107f90220fea0441fc40883fe61107f8c220fe98441fc30883fe41107bc8220fd90441ff54482fea8907f95120bf2a241fd54482faa8907f15120be2a241ff53482fea6907f94d20bf29a41fd53482faa6907f14d20be29a41ff43483fc86906f90d20fea1a41fc434837886907fd0920ff21241fd42483f884907fcc920ff19241fd32483f864907fd4520bfa8a41fe51483faa2907f14520be28a41ff41483fc82907f50520fe20a41ff31483fc62907f4c520fe18a41ff21483fc42907f48520fe10a41ff40483fc80907f50120fe20241ff30483fc60907f4c120fe18241ff20483f640907f88120f710241ff54082fea8107f95020bf2a041be540827ca8107f55020beaa041bd540827aa8107f15020be2a041ff53082fea6107f94c20bf29841fd53082faa6107f14c20be29841ff43083fc86106f90c20fea1841fc430837886105f94820ffa1041ef42083fc84107f50820fe21041ec42083fe64107bcc820ff19041fd32083f864107b0c820ffa8841fe51082fca2107f54420bea8841fc51083fe82107f90420fea0841fc41083fe62107f8c420fe98841fc31083fe42107bc8420ff10841fd21083da42107f08420bf28041ff40083fc80107f50020fe20
  | 2 => 0x2bea6a07f94d40fea9a81fc53502f8a6a07714d40ae29a81ff43503fc86a06f90d40fea1a81fc435037886a07fd4940bfa9281ef52502dea4a07f94940fea9281fc52502f8a4a07b14940b629281ff425037e84a07f90940fea1281bd42503f884a07fcc940ff19281fd32503f864a07fd4540bfa8a81f751502eea2a07f94540fea8a81fc51502f8a2a07d14540ba28a81ff415037e82a07f90540fea0a81bd41503f882a07fcc540ff18a81fd31503f862a07fc8540ff10a81fd21503f842a07fd0140fda0281fe405037c80a05f95040ffa9881fe53102fca6207f54c40bea9881fc53103fe86207f90c40df21881fd43103f886206f10c40ffa9081fe52102fca4207f54840bea9081fc52103fe84207f90840fea1081fc42103fe64207f8c840fe99081fc32103fea2207f94440bf28881fd51102faa2207f14440ffa0881fe41103fa82207f10440ff98881fe31103fa62207f0c440ff90881fe21103fa42207f08440bf28081ff401037e80207f90040fd20081fd401037a80207e50040ffaa6617f54cc3fca9985f95330feaa6617d54cc3f8a9985f15330ffa1e61fe43cc37c87987f50f30fe21e61bc43cc3fea5987f94b30bf29661fd52cc2faa5987f14b30ffa1661fe42cc3fa85987f10b30ff99661fe32cc3fa65987f0cb30ffa8e61fe51cc2fca3987f54730bea8e61fc51cc3fe83987f90730fea0e61fc41cc3fe63987f8c730fe98e61fc31cc3fe43987f88730fe90e61fc21cc3fe81987f90330fea0661fc40cc3fea9185fd5230ff2a4617e548c37ca9184f95230feaa4617d548c37aa9184f55230fe2a4617c548c2faa7187fd0e30efa1c61fe438c37c87187f50e30fe21c61bc438c3b887186710e30ffa9461fe528c2fca5187f54a30bea9461fc528c3fe85187f90a30fea1461fc428c3fe65187f8ca30fe99461fc328c3fea3187f94630bf28c61fd518c2faa3187f14630ffa0c61fe418c3fa83187f10630ff98c61fe318c3fa63187f0c630ff90c61fe218c3fa43187f08630bf28461ff408c3fc81187f50230fe20461ff308c3be61187ecc230ffaa2617f544c37ea8984fd5130ff2a2617e544c3faa8985f55130fe2a2617c544c378a8984f15130ffa1a61fe434c37c86987f50d30fe21a61bc434c3fea4985fd4930f7a92616f524c3fca4987f54930fe292617c524c3d8a4985b14930ffa1261fe424c3fa84987f10930ff99261fe324c3fa64987f0c930ffa8a617f514c3eea2985dd4530ff28a61fd514c3f8a2985f14530fa28a6174514c3fe82987f90530fea0a61fc414c3fe62987f8c530fe98a61fc314c3fe42987f88530fe90a61fc214c3fe80987f90130fea0261fc404c3fe60987ecc130ff18261de304c3fea8185fd5030ff2a0617e540c3faa8185f55030fe2a0617c540c2fca6187fd0c30efa1861f
  | 3 => 0xa990ffd4f21bfa9e43fe53c86fca790ff54f21bea9e43fc53c86f8a790ffd0f21ff21e43be43c87fa8790ff10f21de21e43ff42c87fc8590ff50b21fe21643ff32c87fc6590fb8cb21fe99643ed32c87f86590ffd0721ff20e43fd41c87f88390ffcc721fb98e43fe31c87fa6390ff0c721fa18e43ff50c87fca190df94321fea86437d50c87f8a190ffd5221bfaa443fe54886fca910ff55221beaa443fc54886f8a910ffd4e21bfa9c43fe53886fca710ff54e21bea9c43fc53886f8a710ffd0e21ff21c43be43887fa8710ff10e21de21c437d52887fe8510ff90a21fea1443fc42887fe6510fbcca21ff19443fd32887f86510fb0ca21bf28c43ff41887fc8310ff50621fe20c43ff31887fc6310fd8c621fe98c43f531887f86310ffc8621f790c43f721887fea110ff94221bf28443fd50886faa110ff14221ffaa2437f54487fca890df95121feaa2437d54487f8a890df15121ffa9a437f53487fca690df94d21fea9a437d53487f8a690df14d21ffa1a43fe434877c8690ff50d21fe21a43bc43487fe8490ff90921fea1243fc42487fe6490ff8c921f719243fd32487da6490ff0c921ffa0a43fe41487fa8290ff10521ff98a43fe31487ec6290ff4c521fa98a43fc31487fe4290fdc8521ff10a43ee21487fea090dfd4121ff28243fd50487f8a090df14121ffaa0437f54087fca810df95021feaa0437d54087f8a810df15021ffa98437f53087fca610df94c21fea98437d53087f8a610df14c21ffa1843fe430877c8610ff50c21fe21843bc43086fca410ffd0821ff21043fd42087f88410ffcc821f799043fe32087fa6410ff0c821f6190437e51087fe8210ff90421fea0843fc41087fe6210fdcc421ff18843fd31087f86210fd0c421ff90843ef21087fc4210fd88421fe90843ed21087ea4210f948421ffa8043fe50086fca010ff54021bea8043fc50087fea7a07f94f40bf29e81fd53d02faa7a07f14f40ffa1e81fe43d037c87a07f50f40fe21e81bc43d03fea5a07f94b40bf29681fd52d02faa5a07f14b40ffa1681bf42d03fc85a07f50b40dea1681fc42d03fe65a07f8cb40fe99681fc32d03fea3a07f94740bf28e81fd51d02faa3a07f14740ffa0e81bf41d03fc83a07f50740dea0e81fc41d03fe63a07f8c740fe98e81fc31d03fe43a07f88740fe90e81fc21d02faa9207fd4e40ff29c817e53903faa7205f54e40fe29c81ff43903fc87206f90e40fea1c81fc439037887207fd4a40ff294817e52903faa5205f54a40fe29481ff42903fc85207f50a40fe21481ff32903fc65207f4ca40fe19481ff51903fca3205f94640fea8c817d51903f8a3207fd0640ff20c81fd41903f883207fcc640ff18c81fd31903f863207fc8640ff10c81fd21903f843205f94240ffa0481bf40903f681207fd4d40bfa9a81df535
  | 4 => 0xff90e41df21c83fd43907f88720ef10e41ffa9483fe52906fca520ff54a41bea9483fc52907fe8520ff90a41fea1483fc42907fe6520ff8ca41fe99483fc32906fca320ffd0641dfa0c83f741907fea120ff94241bf28483fd50906faa120ff14241ffa9a837f53507fca6a0ff54d41fe29a837c53507fe86a0ff90d41df21a83fd43507f886a0ef10d41ffa92837f52507fca4a0ff54941fe292837c52507fe84a0ff90941fea1283fc42507fe64a0ff8c941fe99283fc32507fe82a0fdd0541ff20a83be41507fea0a0dfd4141ff28283fd50507f8a0a0df14141bf2a083ff53107fca620df94c41fea98837d53107f8a620ffd0c41ff21883be43107fa8620ff10c41de21883ff52107fca420df94841fea90837d52107f8a420ffd0841ff21083fd42107f88420ffcc841ff19083fd32107f86420df94441ffa0883bf41107fc8220fd90441fea0883bd41107ea8220ffd4041ff280837e50107faa020df54041fe28083ff54cc6fea998ff95331bf2a663fd54cc6faa998ff15331be2a663ff43cc7fc8798ef90f31fea1e63fc43cc7788798ffd4b31ff296637e52cc7faa598df54b31fe29663ff42cc7fc8598ff50b31fe21663ff32cc7fc6598ff4cb31fe19663ff41cc7fc8398ff50731fe20e63ff50cc7fca198df94331fea86637d50cc7f8a198ffd5231bfaa463fe548c6fca918ef952319f2a463fd548c6faa918ef552319eaa463fc548c6f8a918df54e31ffa1c63fe438c77c8718ff50e31fe21c63bc438c7fea518ff94a31bf29463fd528c6faa518ff14a31ffa1463fe428c7fa8518ff10a31ff99463fe328c7fa6518ff0ca31bf28c63ff418c7fc8318ff50631fe20c63ff318c7be6318fdcc631ffa8463fe508c6fca118ff54231bea8463fc508c7fea898dfd5131dfaa2633f544c7fca898df95131feaa2637d544c7f8a898df15131de2a2633c544c7fe8698ff90d31df21a63fd434c7f88698ef10d31ffa92637f524c7dea498dbd4931ff29263fd524c7f8a498df14931f6292636c524c7fe8498ff90931fea1263fc424c7fe6498ff8c931fe99263fc324c7fe8298ff90531fea0a63fc414c7fe6298fdcc531ff18a63de314c7fea098dfd4131fda82637b504c7fca098ff54131fe282637c504c7f0a098de14131ffaa0637f540c7fca818df95031feaa0637d540c7f8a818df15031bf29863ff430c7fc8618ef90c31fea1863fc430c7788618ffd4831ff290637e520c7dca418db94831fea90637d520c7daa418db54831fe29063ff420c7fc8418ff50831fe21063ff320c7fc6418ff4c831fe190637e510c7fe8218ff90431fea0863fc410c7fe6218f7cc431ff18863f6310c7fa6218f74c431fa98863ff500c7fca018df94031fea80637d500c7f8a018ffd5321bfaa643fe54c86fca990ff55321beaa643fc54c86f8
  | 5 => 0xf42fea1e85fc43d0b7887a17fd4742ff28e857e51d0bfaa3a15f54742fe28e85ff50d0bfca1a15f94342fea86857d50d0bf8a1a15f55242ffa9c85fe5390afca7217f54e42bea9c85fc5390bfe87217f90e42df21c85fd4390bf887216f10e42bf29485ff4290b7e85217bd0a42ffa8c85fe5190afca3217f54642bea8c85fc5190bfea1217f94242bf28485fd5090afaa1217f14242ffa9a857f5350bfca6a17f54d42fe29a857c5350bfe86a17f90d42df21a85fd4350bf886a16f10d42ffa1285ef4250bfc84a16f90942ffa8a857f5150bfca2a17f54542fe28a857c5150bfea0a15fd4142ff28285fd5050bf8a0a15f14142bf2a085ff5310bfca6215f94c42fea98857d5310bf8a6217fd0c42ff21885be4310bfa86217f10c42de218857e5210bfe84216fd0842ff21085ee4210bfa84216f50842f6a1085ff5110bfca2215f94442fea88857d5110bf8a2217fd4042ff280857e5010bfaa0215f54042fe28085ff54ccafea9997f95332bf2a665fd54ccafaa9997f15332be2a665ff43ccbfc87996f90f32fea1e65fc43ccb7887997fd0b32ff21665fd42ccbf885997fd4732ff28e657e51ccbfaa3995f54732fe28e65ff50ccbfca1995f94332fea86657d50ccbf8a1997fd5232bfaa465fe548cafca9196f952329f2a465fd548cafaa9196f552329eaa465fc548caf8a9195f54e32ffa1c65fe438cb7c87197f50e32fe21c65bc438cafca5197fd0a32ff21465fd428cbf885197fcca32ef99465ef328cbfea3197f94632bf28c65fd518cafaa3197f14632ffa8465fe508cafca1197f54232bea8465fc508cbfea8995fd5132dfaa2653f544cbfca8995f95132feaa2657d544cbf8a8995f15132de2a2653c544cbfe86997f90d32df21a65fd434cbf886996f10d32ffa1265fe424cbfa84997f10932ff99265ef324cbfc6499778c932ffa8a657f514cbeea2995dd4532ff28a65fd514cbf8a2995f14532fa28a6574514cbfea0995fd4132fda82657b504cbfca0997f54132fe282657c504cbf0a0995e14132ffaa0657f540cbfca8195f95032feaa0657d540cbf8a8195f15032bf29865ff430cbfc86196f90c32fea1865fc430cb7886195f94832ffa1065fe420cbfa84197f10832ff99065df320cbfc64197b8c832fe99065dd320cbda64197fd4432ff288657e510cbeca2195d94432fea88657d510cbeaa2195d54432fe28865ff500cbfca0195f94032fea80657d500cbf8a0197fd4f41ff29e837e53d07faa7a0df54f41fe29e83ff43d07fc87a0ef90f41fea1e83fc43d077887a0ffd4b41ff296837e52d07faa5a0df54b41fe29683ff42d07fc85a0ff50b41fe21683ff32d07fc65a0ff4cb41fe19683ff50d07fca1a0df94341fea86837d50d07f8a1a0df55241ffa9c83fe53906fca720ff54e41bea9c83fc53907fe8720
  | 6 => 0x1a00000000000000600000c01200000c01200000000000000000a00200000000801600e02600e04a00800000005000400400a00600c00200e00000200002601400000001200202600e00000402c06000200600800200000000001401401000002c00001a00400404200600400603600000001601400801200000400602000400000400c00c02800000604004800201800200e00c02400000c00c00a00201e01801201a01c00c01400600202201400601c00201a00200800402403200201201e00200400600a00000000400400600000000601e00402400400000a00e01600000005a00600200800202e01c01800400600000001000200600004200600001e01e00000c00000000600400400000000400603400200600001003403e01a01800202801205001400004e02600800801800e00200801001000404200000400000602600201200400600202c00002800001c00600001c02c00400000600000801601800000000000200200400800602400801600000400000c00c00800000a00001800800600000000000601000800400000200400001200200401401600a00000400600400000202202200201800400000000602000000600201e00201400000a02400000000600200600400400400800e00000200200000000000800000000003a00400e00000400a00a00200e01e00c00400001a04200400800600800201600200400000400200200400000200400000e03000a00800600a00000000002002000601200402a00001c00400000802a05200400200400604402202a00000802202e00600400c00000200800000201800e01a00601e003ff52d0ffca5a1df94b43fea96877d52d0ff8a5a1ffd4743ff28e877e51d0ffaa3a1df54743fe28e87ff50d0ffca1a1df94343fea86877d50d0ff8a1a1df55243bf29c87ff4390f7e8721f7d0e43ffa9487fe5290efca521ff54a43bea9487fc5290ffea321ff94643bf28c87fd5190efaa321ff14643ffa8487fe5090efca121ff54243bea8487fc5090e7ca721efd4a43df29487bd5290f78a521efd4643df28c87bd5190f78a321efd4243df28487bd5090f78a121ffd0d43efa1a87fe4350f7c86a1ffd4943bfa9287fe5250ffaa4a1ff14943be29287ff5150efea2a1ff94543fea8a87fc5150ef8a2a1ffd4143bfa8287fe5050ffaa0a1ff14143be282877e5410efca621ffd0c43dfa1887fe4310fbc8621ff50c43dea1887dd4310ffea421ff94843bf29087fd5210efaa421ff14843ffa8887fe5110efca221ff54443bea8887fc5110ffea021ff94043bf28087fd5010efaa021ff14043df298873e5310f3ca621efd4843df29087bd5210f78a421efd4443df28887bd5110f78a221efd4043df28087bd5010f78a021ffd4f42ff29e857e53d0bfaa7a15f54f42fe29e85ff43d0bfc87a16f90
  | 7 => 0x8503000136520c000d31098b001e462004800195d9a94b49e4614eb82b02adaf40003446d9cf0f4da08000df0b60bf4001cc1961db9ad4000000000320dbd7441e1344438cd11a9e1ce50ae1c1d319b751adc713d16b5a80284234e3db309ac3910180000000015d5a780000017d0711aa85f80000000018fdd4c000001afc000000000d70000001a055f1179799db0000001bd1399ce43c04e1158f3800000087c0000b926830000193862c55cb58cd4000c2c0000007cd2d4431a286b8cc800175c001468ac17643a5840000890000000d199f80000004ac000000001d20de961800000066483c0000018a80005bc2f57180006d12f8a6d8cdb111e80009b841c4e890c23dd50000000e48000dec0011e59e95b00009ec86c001de4191b653a80000ac60055535d12099cca131c0013d476da2cbb8fc4000a204c001069dcfc0001a503400134c000e81685508188310d10001bc5918b2d549449accf741b4084080788001c24c797103f57bc8782e939ce40e09e11bf1a689e9781d9d195124d7d8c40004100018180018308d4ba1b595a4000000f7c10c8a506c000db4984001b453480382bc5b40002c000167daf11040000147e801950c9580007a93812b4645628c54974199add188449a20000541b3c00174098de08640b21ad0d755f8000000f900003e9784001580cec000001998000279465c2d4cc538001151b94259d3825d610001180000d9cee0000530c25d3dd49e496ed990aec0000000fc01d2b8000c403cce94001340ff4001bdc0018b5298000628000ff000020c045525bd8001af9c1124052c000000000c58e340e88749b49a948c00166d4b1be4000395978bc8090c386e40a59b02600010c965800118da6c8a0404ce01a0e889905c8c6da0dd7544000601800000400601200600000000600200800200000401a01000200000000000c02a00001200800201400000200200a01a00001e00200000402200600201402a00800600a00000000002c00000600001e00200600000800200000201e00000001e00000400401800602a00c00200200800001a00000000000400000001200200000800200a00801001c00600400000601201400601c00800400600800604c00202200000e00a00000201800000201200600800a00600000000000000000202000000000000c00200a00a00000206200e01201200c03200001e00800200000800000400400000000601601a00400200c00801400a00000c00003600000200001e00400000000600c00605001e02000200000400200800800200200600600002000201400000a01e01400200202000601a00003200002000200e00200600000600000400202200000400000e00000400000000000200801c00400400002c00400000000002e06000600200201600600200000200000200200a
  | 8 => 0x19107744595c8ad4550510000229bb559400136c3b400002c480aaca2c585184160139ba1da8001cbd2a464d7f0ae8000000470000ef0889cf8dc4ac83c83acf49dc93680000016203502a80008c80000001f1b1da51230af9a94f01a580dd83943c250d35b5cfe10b8fe927d3c43d92800f4318000000000bb0000dc1c380004d800092cc9413c000ebd601c451cc001ca5264860adc650388a400016fd23c0784946e9a184f000098112cdf4000ee87f00004c8000f50d2c7c13e0331cecc4494cea1dcc3bd0f57c4548000a888bcca917c9114e152c501100c894300000015e4f9db48964f857498f8000000001bb9e5c001b042b4f3000085915ccb8a5597d1c94f17a56ccff80010f0000f58ccda88001768b680016b1b6d060d4d415410001e140016c44e40000000007d499400000151c00186c440c5000000000000089d700a454dc9c92ec4a40008e80b590cf28c9cb48000114ae52c0358dc8720000f800b1cc500169ccc43c47950040005c0da1631288001634000001e201d53319f4000e5dac1ba8c7c678001295e440004250599f0e8dca8a8c2f0924d55ab19d0565208a009f8221254b754ac2ec84c000000000001224d218d4001d287855ac001674df92d8374130619284000000000f954ed5a80001f44ecc694d5450000ca40c8001a55721dc41d8001c80000d0c00072c001bf90b03f1e64bbc000000000b28028b254bc00034155400147541c000f040017c00005cda6578d5ecb08bd00000000003ec001864000000bb4898001249108a71389ca00010494288c484041970568c00000180c0000005e59b8be0a051553ac26c8ac0e000113c0009fd4f4f5c000000001d1d53d74d5ccb119cc71800103cfac0007fc00022d46c53d419d1066176c1409d87a5a240599a0000354535de800000000042c000ce8e0d24d66875097c001c30bc5b20daca69bbcda4ce57b40000000007c431da980016e90380000009a045c1649bc0013a4810384b38000000001a7c2956e58b0000000001011920671ce929c0018ac2900012d0d646856bd0cc000e3121cb1538d10d01400144c508c48c64570001234c75320484001abdaace0572d6558f5c8c1b9cb11b51b0f118c1810d79804a11bad651b997e1ae0a18fdc4747588a80544a0000000000118000ad16940000005891c55f40000003b0001980bcca340000000000000007d00013bc85d854f78941e1816c001371b600007799e40eddbc8057d8000920000000d040019ed42c000000eb4000000001808214185b912a035c000839198da909d2600346a48dd1a0de5a10001d24001484f45a60401988d380a04d0000dccfb89185f0efc32905c074db0000070604001904800a1ca29c5c000a15c0d3242094a894501cc918498515dc8940000e4274c106958e8c0c5e84d5858e
  | 9 => 0x7780002f9bd4001490001e4c0009f414800063060c0015c40017741a9cc86cc5209880c114d4c55b4000bc0971355551480b85d444b4000001c4ce900000000000000000019b5160000000001518edd898a940008b9a00001a49c7d8252ad2a9908218174d88b305adde07e41dcd002fc66dd8570c15871d1d983c8f04688803f80000000012440007dc0006a09c06ad5b87f8000001211cd5d6c000000c35e4081874c000820000969e2dac960994d944000001ab440ce65bcd639b5459d5788088d0b9de61da0f6cc210bc1e8a74e2db2c0007ecb34744001aa5cf415ced450de340000013c8fe454473c3fcfed4393b0000cf0001754024d4845400017c0018005d8bfc000000200000aa0a49190001c2023900c639a71c04000001434001c941b1d70f080014080004647396f96f0dfc001dec0007b8e119140001bd0211f85a99c98b8fd826973107434c93c00000000054c09809c000000700000fd00000000000006697e40000001ac6c0124b7d2fc6b09a4f8935859877d7c9140cf59c1458eb1c68ffcd417f565c81c868815c981200018bd6f5814eec0300000002d82d569861c001641b9cfd5734fb00010715996c16a8fcc241d7d5219353cc381a84aa592cec87f4a4d169564001cac04d7dd3f94b8930001895130000000000000001661d940013f40000000002700000000000000000013044889cd6705f4000001055530fa0001068afcea50ad2f08fcd3dd015fc0f00003dc001a4dbc800028800095c000e00000498135c289e1d550d973d7a8000000bf16a5ac53e89c584d8e4179a14e71dd1d808b4691009c5038c8c06c912933d3389f057832c764c18f18c61df86810b5bc0848845c49e38d587093513e5529d34f2d0a8730a592c4f98a81558c845055e137c1c0ac47994c0000d6db018615403a91d0960001c14d50b8d9696d0001828001219d797a0cbd2dc8b00009d4b442107b17900000000016c847cc1cb656d530cd807050a4420001a5c4a8000000000001d5927043d56d26c0000000001557ede3ccc104400000000000048d11d96d3d9901be08cdd8904145c96d2bc0000004c400000000108c000000000905c7800157c000d61750245845be9d0d63ca5ca79504001478ed8c8000046c929170f710a0000000000a84000560000000000001bfdb880613b4e7805d79c195665dddb6878d77c88ce9dd610c11f160cd289dd8dcaa9e50ec0b04370d1d08890007dccc128000fc9455cd1b700511100006c5bf45b171d33400132d3c0e1400193c29800029c000e740018f00018d00017280954f87e000147154d2b0d68000000f60000b0c0000002b800181d0ed514001149e247ac0011f400000028c42812c0013ddb257700c45a056d4d00000014d8735688001cd8be5a9c0000002d0000f24000a3000006c00000
  | 10 => 0x58af58808e40004341cc3d4e1976058d58c1c8000e2519db0c0012055bc0007c8b18fb4000001b408f9a8c000000ddc000000000e58c140008d83e00000000000014a4001a309d0870041dac000e392919a4001c4079075d228908e6c224000000001ad8fa40ccaf04bce4db15b391a5c605598ec3d196513477030985d085bb1e541104fc1ede68e7c24d02c00c830d143151fdb78829535a914c9080525ba400079da35164000000780000d5c0000000008eccb46f851d9597147b59240a8c08c70001dd9794ecd25c1680017accd80018c983400085027d2f4000000001cb865c4f99dcdd56d8e619300019280f8000001708000000000000bd5aed681955c9d391b341040000012145d0000cb0f41b814054240000002e4100000000cfda1c3349792512c962cde15a1624855460001890ba51ec0005fc368e28ab84140000000016455d104c18d585e0400000000000074839c0007a0ee40006540008f55e80000000016b8000000254001d8c5e074082d1e00d59d4000000068b1d7e8001dc044c000b80824ed0064000000000000a983e598ce68b715c0000bed22161c0018212380002dc001c194884457fdc3c000000000001b199ad0509b04b891d1dc0005b9494bf8f0c0017f947c0011440010e53950e8ef82a42a0000000000ba94980013a154421cc3c0005c4000b540000000004090f80000000005280011b8939a40bdc001ae4934914648f20e1c001b4c1445a4d8cd946b4d84c00569da400045033c204cdd568ad9975a454e436516cb983b8d24eacf34a9ddfcbd9d3107d6dcf8c001c08ea90d4020c31b7d574001d64ec4460688000a3989d7250d16045941700d0e98715d5c000b4072800130080c000001b280000000000012e58d8001aa0b9463d2794a026400000019c948000000000f146dc1f9374a09079648d45ae80016a173800000000122ddf030dc6c0001fc00128d8e1614b79c004dc7bd690518000000000000608dd1588180001a39138000000a3c6e0001c88000000e452007d8c99d69378000000000000001951025c850e0a615380005d40004cc10930803d1c06a8fa8348b4d0dc580000a0c0000019e11d59c4ef57b1b5037c6757898a1ab8864dd8fbdc6587cd98e2191d40cab4574d905918746988e0001d08000f1ddd5b842310940000000000000011bd5719bd3fc725401ce16ad88400155c1d0000cf9420000000000be89980d8000950e54624c0400036c0000012cc00188c4906ec001a74000768000c29b099d97ccb6c11d118c4d869175275091c58f54accab0c5c5dc884005cb57b80086bca64a91b8d0640bc659c911157d52e12590c4000000000000f65310398611e5800199ca50001501511985e0cc8c6f41c582c000f680000006354fd9fdd98b899953ec000478001db415014c954000761
  | 11 => 0x1d150fdd91d406d44f46fca252e96e02813853f02cc325328b51028515bedc5587149ccac835e298a408c49d361c74a7c75587800070cbad4440880015d9e00b3c3382e1948db9591d19e3068d940b5dc344b1678000fc13b9970249a3c3780003054e9df5560d08b9159dd0564c360000f3d3142c43a0001d2c57cabc0005ec6f067dcdc2c98897
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x140042df6350010b718d40042ef6250010bb18940042f76150010bd18540043b741500109fd94400427e65100109f594400427c6510010cf950400433d5410010bd98440042f56110010ee500400427d65cc010cf953300433d54cc010be597300437965cc010ee95330043b954cc010ded4f300437953cc010ee90f30043b843cc010de94b300437852cc010fcd8730042f961cc010fc187300437a51cc010fcd0730043f041cc010fccc730043f031cc010fc88730043f121cc0109fd96300427d658c010af99230042bd648c010cf952300433d548c010d794e300435d538c010e710e30042f6618c010bd58630042fa608c0109fd9530042bf644c010af191300433e544c010cf55130042ef624c010bb18930042f7614c010bd185300427f650c0109f994300427d650c0109f194300433e540c010cf550300435e530c010d754c300439c430c010bd98430042f5610c010be5943004379650c0109e59430043ba540c010ee55030042fa630c010f698c300437b530c010f694c3004379530c010f654c30043db430c010ee90c30043b8430c010f610c3004398430c010de9483004378520c010fc98430042f9610c010fc584300437a510c010fcd0430043f0410c010fccc430043f0310c010fc88430043f1210c0109f597200433e54c8010cf55320042f661c8010bd587200427f65880109f596200433e5488010cf552200436e5288010db54a20042f66188010bd58620043e521880109fd95200433e5448010cf551200427f65080109f994200427d65080109f19420042be6408010af590200433e5408010cf550200436e5208010db54820042f66108010bd58420043e52108010fa480200433e54c4010cf55310042ee62c4010bb58b100437565c4010bd99310042f464c4010ed95310043b554c4010bd98f10042f463c4010ed90f10043b443c4010bdd8b10043e662c4010bd58b10043e562c4010b958b10043f330c4010fc0c3100433e5484010cf55210042f56184010dd94610042f96584010de59610042796584010ee95210043b95484010be98e10042f86384010ee90e10043b84384010be586100437a5184010fc94610043f34184010fc10610043f33184010fc0c610043f22184010fc486100427f6544010cf951100433d5444010bdd95100437765440109dd9510042f66444010bd19110043b65444010ed55110042f66344010bd18d10043b64344010ed10d10042f76244010bd58910042f76044010dd94110043f24044010fc50110043f33044010fc0c110043f32044010fc08110042fb6544010ded95100427b6544010ee95110043b95444010be98d10042f86344010ee90d10043b84344010bed8510043f36144010de94510043f25144010fc90510043f14144010fccc510043f03144010fcc8510043f02144010
  | 1 => 0x433d54d0410bd597410437565d0410ddd5341043b654d0410dd55341043b554d0410cd55341042f663d0410ed90f41043b443d0410bd58b41042f560d04109fd96410427d6590410cf952410433d5490410bd98641042fa6090410be582410427f6550410cf951410433d54504109fd94410427d6510410cf950410433d5410410be98041042f96010410dd59441042756510410bd99041043b66410410ddd5041043b65410410dd55041043b55410410bd98c41043b64310410ed10c41042f56210410fc98041042f56010410fc58041042f160104109f597310433e54cc410cf55331042f565cc410dd59731042f664cc410bd19331043b654cc410ed553310437753cc410dd54f31043b643cc410ed10f31042f562cc410dd94b310437452cc410fcd8331042f560cc410fc183310427f658c4109f59631042be648c410af592310433e548c410cf552310435e538c410d754e31042f6618c410be98231042f9608c4109fd9531042bf644c410af191310433e544c410cf55131042ef624c410bb18931042fb604c4109fd94310427d650c410cf950310433d540c410d794c310435d530c410bb98831042ed620c410be98031042f9600c410dd5943104275650c410bd99031042f4640c410ed95031043b5540c410bd98c31043d6630c410ddd4c31043d6530c410dd54c31043d5530c410ed90c31043b4430c410f998831042f5620c410f958831042e5620c410dd9483104374520c410fc98031042f5600c410fc580310427d65c8410cf953210433d54c8410dbd4b210436c52c84109fd96210427d6588410cf952210433d5488410db94a210436d5288410be98221042f96088410dd59621042756588410bd99221042f46488410ed95221043b55488410bd98e21042f46388410ddd4e21043755388410ed90e21043b44388410bd58a21043765288410f994a21043e55288410dd14a21043e73288410f90ca21043f26088410bd58221043f16088410bc582210427f6548410cf951210433d5448410dbd49210436c5248410bdd9521043776548410bd99121042f46448410ed95121043b55448410bd98d21042f46348410ddd4d21043755348410ed90d21043b44348410f9d8921043e75248410dd94921043745248410f914921043645248410f98c921043e53248410bdd81210427f65084109f594210433e5408410cf550210436e5208410db54821042f66108410f948421042fa6008410be580210427e64940109f592500427e63940109f58e500433e4394010cf10e500427e62940109f58a500427d6194010ddd0650043744194010ddcc650043743194010dd886500437521940109f597400433e54d0010cf55340043b741d00109fd96400427d6590010cf952400433d5490010bd98640042f561900109fd95400433e5450010cf55
  | 2 => 0x6590c10cfd96430423f6590c10cf99643042bd6590c10cf596430423d6590c10cf19643042be6390c10cfd4e430433e5390c10cf54e430433c5390c10ed98643043b56190c109fd95430427e6550c109f595430427c6550c10cf951430433d5450c10bdd8543042f46150c10bed8143042f86050c109fd94430427e6510c109f594430427c6510c10cfd50430433e5410c10cf550430433c5410c10afd94430433f6510c108fd94430433e6510c10af594430433d6510c108f594430433c6510c10af98c430439e6310c10cfd4c430433e5310c10cf54c430433c5310c10edd8443043b46110c10af99352042bd64d4810cf953520433d54d48109f993520433e64d48108f993520427d64d4810cf593520423d64d48109f98f520427d63d4810cf90f520433c43d48109f987520437661d48109f983520437a60d48109f596520433e5494810cf552520436f52948109f992520427d64948109f98e520427d6394810cf90e520433c4394810dd986520433e5454810cf551520427f64548109f191520427f63548109f18d520433e4354810cf10d520436f62548109fd85520427d61548109fd81520427d6054810af99052042bd6414810cf950520433d5414810b798c52042dd6314810db548520427e6414810cf990520423e64148109f590520433d64148108f590520427e6314810d798c520425e63148109f58c520435d63148109758c520433e4314810cf10c520427e6214810db988520427e6114810dd984520427e6014810de980520427f65d08109f997420427d65d08109f197420433e54d0810cf553420427f65908109f996420427d65908109f196420433e5490810cf55242042f66190810bd586420427f65508109f995420427d65508109f195420433e5450810cf55142042f76150810bd18542042fb6050810be181420427f65108109f994420427d65108109f194420433e5410810cf55042042f66110810bd58442042fa6010810be580420427f65cc8109f997320427d65cc8109f197320433e54cc810cf553320435e53cc810d754f320436f52cc810db14b320427f658c8109f996320427d658c8109f19632042be648c810af592320433e548c810cf552320436e528c810db54a32042f6618c810bd58632042fa608c810be582320427f654c8109f995320427d654c8109f19532042bf644c810af191320433e544c810cf551320435e534c810d754d320436e524c810db54932042f7614c810bd18532042fb604c810be181320427f650c8109f994320427d650c8109f194320433e540c810cf550320436f520c810db14832042f6610c810bd584320427e64944109f592510427e63944109f58e510433e4394410cf10e510427e6294410db98a510426e62944109f58a510436d62944109b58a510427d65d0410cf953410
  | 3 => 0x1109f19530442bf644c110af191304435f534c110d714d30442ef624c110bb18930442f7614c110bd185304427e650c110e710c304427e65c8110dbd4b204436c52c8110bd98720442f561c81109f996204436e5288110db54a204427f65481109f595204427c6548110dbd49204436c5248110bdd8520442f461481109f99420442be6408110af590204436e5208110db54820442ee62c4110bb58b104437a53c4110de14f10443ba43c4110ee10f10443ea62c4110fa58b10443765484110dd15210443765384110dd14e10443b64384110ed10e10443775284110dd54a10443f350841109f98f540427d63d50109f98b540427d62d50109f987540437661d50109f983540437a60d50109f596540433f54950109f98e540427d63950109f98a540427d62950108f59654042be6395010ed186540433f6395010cf98e540423e6395010cf58e540433c6395010cfd8a540433e6295010cf58a540433c6295010cf986540433c6195010cf982540433c6095010cfd91540427f63550109f18d540427f62550109f189540427f61550109f585540437461550109fd81540427d6055010cfd9554042bc6355010ed185540433f6355010cf98d540433d6355010cf18d540423c6355010cfd89540433e6255010cf589540433c6255010cf985540433c6155010cd185540433e6055010cf181540433c1055010af990540433d54150109f990540433e64150108f990540427e63150109f58c540427e62150109f588540427e6115010dd984540427e6015010de98054042be64d4c10af593530433e54d4c10cf553530427e64d4c10cf993530423e64d4c109f593530433d64d4c108f593530427e62d4c109f58b530427e61d4c10dd987530427e60d4c10de983530427d6594c10cf952530433d5494c10d7d4e530433f6494c109f992530427d6494c10cf192530427e6294c109f58a53042bf6454c10af191530433e5454c10cf55153042ef6254c10bb189530427f6454c10cfd91530423f6454c109f191530433c6454c108f191530435f6354c109fd89530436f6254c109bd89530427c6254c10db189530426c6254c109fd85530427d6154c10dd185530427f6054c109f58153043786054c10af99053042bd6414c10cf950530433d5414c10d754c53042ee6214c10bb588530427e6414c10cf990530423e6414c109f590530433d6414c108f590530427e6314c10d798c530427e6214c10db988530426e6214c109f588530436d6214c109b588530427e6114c10dd984530427e6014c10de980530427f65d0c109f997430427d65d0c109f197430433e54d0c10cf55343042f661d0c10bd58743042fa60d0c10be583430427f6590c109f996430427d6590c109f196430433f5490c10cf952430433d5490c10cf15243042f66190c10bd58643042bf
  | 4 => 0xf150434435f5310d10d714c43442f66110d10bd58443442fa6010d10be580434433f6510d10cf994434433d6510d10cf19443442be6310d10e798c434433f5310d10e7d4c434431f5310d10cf94c434433d5310d10cf14c434439c5310d10c714c43443b66110d10ed58443443ba6010d10ee580434427e64d49109f593524427e63d49109f58f524433e43d4910cf10f524436f52949109f992524427d64949109f98e524427d6394910cf90e524433c43949109f98a524427d6194910dd586524427561949109f58252443796094910afd9152442bc6454910b7d8d52442dc63549109fd91524433f64549108fd91524427c6454910cf191524423c64549109fd8d524435f635491097d8d524427c6354910d718d524425c6354910cf90d524433c4354910dbd89524427f6154910ddd85524427f6054910ded81524427e6514910db548524427e64149109f590524427e63149109f58c524433e4314910cf10c524436e62149109f984524427c61149109f980524427c60149109fd97424427e65d09109f597424427c65d0910dbd4b424436c52d0910bd98742442f561d0910be98342442f960d09109fd96424427e65909109f596424427c6590910cfd52424433c54909109fd95424427e65509109f595424427c65509109fd94424427e65109109f594424427c6510910cfd50424433c5410910dbd48424436c52109109fd97324427e65cc9109f597324427c65cc910dbd4b324436c52cc9109fd96324427e658c9109f596324427c658c910af99232442bd648c910d7d4e324435c538c9109fd95324427e654c9109f595324427c654c910afd9132442bc644c910bdd8532442f4614c910bed8132442f8604c9109fd94324427e650c9109f594324427c650c910d7d4c324435c530c910dbd48324436c520c910bd98432442f5610c9109f997414433f54d0510cf15341442fa60d0510be583414427e65905109f195414433f5450510cf15141442fb6050510be181414427e65105109f997314435f53cc510d714f31442fa60cc510be583314427e658c510af99231442bd648c5109f19531442bf644c510af191314435f534c510d714d31442ef624c510bb18931442fb604c510be181314427e650c510bb98831442ed620c5109f997214436f52c8510db14b21442fa60c8510be583214427e65885109f195214436f5248510db14921442fb6048510be181214427e6508510f9484214427e65d0110cfd53404433c54d0110bd98740442f561d01109f996404427f65501109f595404427c6550110cfd51404433c5450110b7d8d40442dc6350110bbd8940442ec6250110bdd8540442f461501109f994404427e65cc110d7d4f304435c53cc110bd98730442f561cc1109f99630442be648c110af592304439c438c1109fd95304427d654c
  | 5 => 0x21843e53248610bdd8121843f36048610fc18121843e52108610cfd53408433c54d0210edd07408433e5490210cf55240842f66190210bd586408433f5450210cf15140842df6350210b718d40842ef6250210bb18940842f76150210bd18540843b74150210cf950408433d5410210bd98440842f56110210af99230842bd648c210d794e308435d538c210e710e30842f6618c210bd58630842bf644c210af19130842ef624c210bb18930842f7614c210bd185308435e530c210d754c308439c430c210bd98430842f5610c210bd98720842f561c8210db94a208436d5288210bd98620842f56188210f948620842be6408210af590208436e5208210db54820842f66108210bd58420843e52108210bb98b10842ed62c4210bd597108437565c4210bd99310842f464c4210bd98f10842f463c4210ed90f10843b443c4210bdd8b10843e662c4210bd58b10843e562c4210b958b10842f965c4210de597108437a53c4210de14f10843ba43c4210ee10f10843ea62c4210fa58b108427e63d51109f58f544427e62d51109f58b544433f54951109f992544427e63951109f58e544427e62951109f58a544427d6195110dd586544427d6095110de58254442df6355110b718d54442ef6255110bb189544433f64551109fd8d544435f635511097d8d544427c6355110d718d544425c63551109fd89544436f62551109bd89544427c6255110db189544426c62551109fd85544437761551109dd85544427f6055110ded81544427e6515110cf550544433e64151109f98c544427d63151109f988544427d62151109f984544427c61151109f980544427c6015110af99353442bd64d4d109f993534433e64d4d108f993534427d64d4d10cf593534423d64d4d109f98b534427d62d4d10d7d4e534427e6494d109f592534427e6394d109f98a534427d6294d109f58653443756194d109f58253443796094d10afd9153442bc6454d10bbd8953442ec6254d109fd91534433f6454d108fd91534427c6454d10cf191534423c6454d10d7d8d534427f6254d10dbd89534426f6254d109f189534436c6254d109b189534427f6154d10ddd8553442776154d109fd81534437b6054d109ed81534427e6514d10d754c534427e6414d109f590534435e6314d109f988534427d6214d109f984534427c6114d109f980534427c6014d109fd97434427e65d0d109f597434427c65d0d10d7d4f434435c53d0d109fd96434427e6590d109f596434427c6590d10cfd52434433e5490d10cf552434433c5490d10cfd96434433e6590d10cf596434433c6590d10af98e434433f5390d10cf94e434433d5390d10cf14e434427f6550d109f995434427d6550d109f195434427f6510d109f994434427d6510d109f194434433f5410d10cf950434433d5410d10c
  | 6 => 0x27d63d4a10cf90f528433c43d4a10dd587528437a60d4a10dbd4a528427e6494a109f592528427e6394a109f58e528433e4394a10cf10e52843756194a109fd91528427c6454a109fd8d528427c6354a10cf90d528433c4354a10dbd8952842be6414a10af590528436d5214a109f990528433e6414a108f990528427d6414a10cf590528423d6414a109f98c528427d6314a10cf90c528433c4314a10db98852843756114a10de980528427f65d0a109f997428427d65d0a109f197428433e54d0a10cf55342842fa60d0a10be583428427f6590a109f996428427d6590a109f196428436e5290a10db54a42842f66190a10bd586428427f6550a109f995428427d6550a109f195428433e5450a10cf551428436e5250a10db54942842f76150a10bd185428427f6510a109f994428427d6510a109f19442842f66110a10bd584428427f65cca109f997328427d65cca109f197328436e52cca10db54b328427f658ca109f996328427d658ca109f19632842be648ca10af59232842f6618ca10bd586328427f654ca109f995328427d654ca109f19532842bf644ca10af19132842f7614ca10bd18532842fb604ca10be181328427f650ca109f994328427d650ca109f194328436e520ca10db54832842f6610ca10bd584328433e54d0610cf55341842fa60d0610be583418437565d0610ddd5341843b654d0610dd55341843b554d0610bd98f41843b643d0610ed10f41842f562d0610fc98341842f560d0610fc583418433e5450610cf55141842fb6050610be18141842f56510610dd59441843b66410610ddd5041843755410610bd98c41843b64310610ed10c41842f56210610bd580418435e53cc610d754f31842fa60cc610be583318437565cc610bd99331842f464cc610ddd4f31843d653cc610dd54f31843d553cc610ed90f31843b443cc610bd58b318437652cc610dd14b31843f260cc610bd58331843f160cc610af99231842bd648c610afd9131842bc644c610d794d318435d534c610bbd8931842ec624c610bed8131842f8604c610bb98831842ed620c610bd5943184375650c610bd99031842f4640c610f598c3184377530c610dd54c31843b6430c610ed10c31843e6620c610bd58831843e5620c610b95883184376520c610dd14831842f5600c610db94b218436d52c8610be98321842f960c8610bd59621843756588610bd99221842f46488610bd98e21842f46388610ddd4e21843755388610ed90e21843b44388610dd94a21843745288610f9cca21843e43288610bd582218436e5248610db54921842fb6048610be18121843776548610bd99121842f46448610bd98d21842f46348610ddd4d21843755348610ed90d21843b44348610f9d8921843765248610f994921843665248610f954921843745248610f98c9
  | 7 => 0x450310cf55140c42df6350310b718d40c42ef6250310bb18940c436e5250310db54940c42f76150310bd18540c436e5210310db54840c43b94010310d794f30c435d53cc310db94b30c436d52cc310bd98730c42f561cc310be59730c437965cc310ded4f30c43da53cc310de54f30c43d953cc310ee90f30c43b843cc310de94b30c43ea52cc310da94b30c43e952cc310de14b30c43f261cc310be58730c43f161cc310af99230c42bd648c310e710e30c436e528c310db54a30c42bf644c310af19130c435e534c310d754d30c42ef624c310bb18930c436e524c310db54930c42f7614c310bd18530c439c430c310db94830c436d520c310be59430c4379650c310f698c30c437b530c310de54c30c43db430c310ee90c30c43b8430c310f610c30c4398430c310de94830c43ea520c310da94830c43e9520c310de14830c42f9610c310db94b20c436d52c8310bd98720c42f561c8310db94a20c436d5288310db94920c436d5248310bdd8520c42f46148310af99020c42bd6408310db94820c436d5208310fa48020c427e63d52109f58f548427e62d52109f58b548437561d5210de983548433f54952109f98e548427d63952109f98a548427d6295210cfd91548427f63552109f18d548427f62552109f18954843776155210cf55054842ee6215210bb588548433e64152109f98c548427d63152109f988548436e62152109b988548427d6215210db588548426d6215210dd584548437a6015210af99353842bd64d4e10bb98b53842ed62d4e109f993538433e64d4e108f993538427d64d4e10cf593538423d64d4e109f98b538436e62d4e109b98b538427d62d4e10db58b538426d62d4e10dd587538437a60d4e10d7d4e538427e6494e109f592538427e6294e109f58a53842bf6454e10af191538427f6454e10cfd91538423f6454e109f191538433c6454e108f191538435f6354e109fd89538427c6254e10ddd85538435d5314e109f990538427d6414e10d798c538427e6214e109f58853843756114e10de980538427f65d0e109f997438427d65d0e109f19743842f661d0e10bd587438427f6590e109f996438427d6590e109f196438433f5490e10cf952438433d5490e10cf15243842f66190e10bd586438433f6590e10cf996438433d6590e10cf196438433f5390e10cf94e438433d5390e10cf14e43843b66190e10ed586438427f6550e109f995438427d6550e109f19543842f76150e10bd185438427f6510e109f994438427d6510e109f194438433f5410e10cf950438433d5410e10cf15043842fa6010e10be580438433f6510e10cf994438433d6510e10cf194438439e6310e10cfd4c438433e5310e10cf54c438433c5310e10edd8443843b46110e10ee98043843b96010e109f993528427d64d4a109f98f5284
  | 8 => 0x10dd98752c437960d4b10dbd4a52c427e6494b109f59252c427e6394b109f58e52c433e4394b10cf10e52c436f5494b10db95252c436d5494b10db15252c436f5394b10db94e52c436d5394b10db14e52c43ae4394b10eb10e52c436f6494b10db99252c436d6494b10db19252c436f6394b10db98e52c436d6394b10db18e52c436f4394b10db90e52c432e4394b10db50e52c436c4394b10cb10e52c436e6194b10db18652c436f6094b10db58252c427f6454b109f19152c427f6354b109f18d52c433e4354b10cf10d52c436f6254b10dbd9552c436f5454b10db95152c436d5454b10db15152c436f5354b10db94d52c436d5354b10db14d52c43ae4354b10eb10d52c436f6454b10db99152c436d6454b10db19152c436f6354b10db98d52c436d6354b10db18d52c436f4354b10db90d52c432e4354b10db50d52c436c4354b10cb10d52c436e6154b10db18552c436f6054b10db58152c436d5214b109f99052c427d6414b109f98c52c427d6314b10cf90c52c433c4314b10db98852c43766114b10de58052c427f65d0b109f99742c427d65d0b109f19742c436e52d0b10db54b42c42f661d0b10bd58742c427f6590b109f99642c427d6590b109f19642c436e5290b10db54a42c427f6550b109f99542c427d6550b109f19542c436e5250b10db54942c42fb6050b10be18142c427f6510b109f99442c427d6510b109f19442c436e5210b10db54842c42fa6010b10be58042c427f65ccb109f99732c427d65ccb109f19732c436e52ccb10db54b32c427f658cb109f99632c427d658cb109f19632c42be648cb10af59232c436e528cb10db54a32c42fa608cb10be58232c427f654cb109f99532c427d654cb109f19532c42bf644cb10af19132c436e524cb10db54932c42f7614cb10bd18532c42fb604cb10be18132c427f650cb109f99432c427d650cb109f19432c436e520cb10db54832c42f6610cb10bd58432c433f54d0710cf15341c436e52d0710db54b41c433e5490710cf55241c436e5290710db54a41c42fa6090710be58241c433f5450710cf15141c436e5250710db54941c433e5410710cf55041c436e5210710db54841c42fa6010710be58041c436e52cc710db54b31c42be648c710af59231c435e538c710d754e31c436e528c710db54a31c42fa608c710be58231c42bf644c710af19131c42ef624c710bb18931c436e524c710db54931c42f8604c710d794c31c435d530c710bb98831c42ed620c710db94831c436d520c710be98031c42f9600c710db94b21c436d52c8710db94a21c436d5288710be98221c42f96088710db94921c436d5248710db94821c436d5208710f948421c42fa6008710be58021c433e54d0310cf55340c436e52d0310db54b40c42f661d0310bd58740c436e5290310db54a40c433e5
  | 9 => 0x58720083eb30c8020fa0c3200833e5488020cf55220082ed6288020db94a20083ba5488020ee55220082fa6388020be18e20083ba4388020ee10e20082f96288020de94a20083ea5288020fad0a20083e84288020facca20083e83288020fac8620083e921880209fd95200833e5448020cf55120082ef6548020dbd95200826f6548020bb99120082ec6448020eb95120083ad5448020bb98d20082ec6348020eb90d20083ac4348020bbd8520082ef6048020db94120083ea4048020fa50120083eb3048020fa0c120082fb6548020ded95200827b6548020ee95120083b95448020be98d20082f86348020ee90d20083b84348020bed8920083eb6248020de94920083ea5248020fa90920083e94248020facc920083e83248020fa88520083e82148020b798f54c42dd63d5310bb98b54c42ed62d53109f98f54c435e63d53109798f54c427d63d5310d758f54c425d63d53109f98b54c436e62d53109b98b54c427d62d5310db58b54c426d62d5310dd98754c437960d5310cfd5254c427e63953109f58e54c427e62953109f58a54c433f64553109fd8d54c427c63553109fd8954c427c6255310cf55054c42ee6215310bb58854c433e64153109f98c54c427d63153109f98854c436e62153109b98854c427d6215310db58854c426d6215310dd98454c43796015310af99353c42bd64d4f10bb98b53c42ed62d4f109f99353c433e64d4f108f99353c427d64d4f10cf59353c423d64d4f109f98b53c436e62d4f109b98b53c427d62d4f10db58b53c426d62d4f10dd98753c437960d4f10d7d4e53c427e6494f109f59253c427e6294f109f58a53c42bf6454f10af19153c427f6454f10cfd9153c423f6454f109f19153c433c6454f108f19153c435f6354f109fd8953c427c6254f10ded8153c435d5314f10bb98853c42ed6214f109f99053c427d6414f10d798c53c427e6214f10db98853c426e6214f109f58853c436d6214f109b58853c43766114f10de58053c427f65d0f109f99743c427d65d0f109f19743c435e53d0f10d754f43c42fa60d0f10be58343c427f6590f109f99643c427d6590f109f19643c433f5490f10cf95243c433d5490f10cf15243c433f6590f10cf99643c433d6590f10cf19643c433f5390f10cf94e43c433d5390f10cf14e43c427f6550f109f99543c427d6550f109f19543c42fb6050f10be18143c427f6510f109f99443c427d6510f109f19443c433f5410f10cf95043c433d5410f10cf15043c435e5310f10d754c43c42f66110f10bd58443c433f6510f10cf99443c433d6510f10cf19443c439e6310f10cfd4c43c433e5310f10e794c43c431e5310f10cf54c43c439d5310f10c754c43c433c5310f10ed98443c43b56110f109f99352c427d64d4b109f98f52c427d63d4b10cf90f52c433c43d4b
  | 10 => 0x1082bf644c420af191310833e544c420cf551310835e534c420d754d31082ef624c420bb1893108376514c420dd54531082fb604c420be181310827f650c4209f994310827d650c420cf950310833d540c420bb98831082ed620c420cf953210833d54c8420dd947210837551c8420be98321082f960c8420bb99321082ec64c8420eb95321083ad54c8420bb98f21082ec63c8420dbd4f210836d53c8420eb90f21083ac43c8420db94721083e651c8420f954721083e731c8420f90c721083ea60c8420bb58321083e960c8420ba583210827d6588420cf952210833d5488420bb58a210827f6548420cf951210833d5448420bbd95210836f6548420bb99121082ec6448420eb95121083ad5448420bb98d21082ec6348420dbd4d210836d5348420eb90d21083ac4348420f9d8521083e75148420db94521083e45148420f98c521083e53148420bbd81210833e5408420cf55021082ee6208420dd94421083755108420f948421082fa6008420be580210827e64940209f592500827e63940209f58e500833e4394020cf10e500836f4294020db10a500836f3294020db0ca500836f2194020db486500827d65d0020cf953400833d54d0020ebd0b400827f65900209f596400833e5490020cf55240082ee6290020bb58a400827f6550020cf951400833d5450020b7d8d40082dc6350020bbd8940082ec6250020ebd0940082f76150020bd185400827f65100209f994400827d65100209f194400833e5410020cf55040082ee6210020bb58840083b940100209f597300833e54cc020cf55330082f965cc020de59730083ba54cc020ee553300837b53cc020de54f30083ba43cc020ee10f30083eb62cc020be58b30083e862cc020de94b30083eb42cc020fa10b30083eb32cc020fa0cb300837a51cc020fac8730083e921cc0209fd96300827d658c020af99230082bd648c020cf952300833d548c020d794e300835d538c020e710e30082ee628c020bb58a30082fa608c0209fd9530082bf644c020af191300833e544c020cf55130082ef624c020bb18930082f7614c020bd185300827f650c0209f994300827d650c0209f194300833e540c020cf550300835e530c020d754c300839c430c020bb98830082ed620c020be5943008379650c0209e59430083ba540c020ee55030082fa630c020f698c300837b530c020f694c3008379530c020f654c30083db430c020ee90c30083b8430c020f610c3008398430c020fa98830082f9620c020fa588300837a520c020fad0830083e8420c020facc830083e8320c020de94430083eb210c020fa484300833e54c8020cf55320082f661c8020bd58720082ee64c8020bb19320083ae54c8020eb55320082ee63c8020bb18f20083ae43c8020eb10f20083e661c8020bb58720083e561c8020b9
  | 11 => 0x3d6510c208f594430833c6510c20af98c430839e6310c20cfd4c430833e5310c20cf54c430833c5310c20ebd8843083ac6210c209f992520827d64948209f98e520827d6394820cf90e520833c4394820dd986520837561948209f597420833e54d0820cf55342082ed65d0820db597420836f54d0820eb953420836d54d0820eb553420832d54d0820bb98f42083ae43d0820eb10f42082ed61d0820bb583420827f65908209f596420833e5490820cf55242082ee6290820be98242082f960908209fd95420833e5450820cf551420827f65108209f594420833e5410820cf55042082fa6010820be580420836d65108209b59442082ee6410820eb990420836f5410820eb950420836d5410820eb55042082ee6310820eb90c42083ac4310820bb58442083ea6010820bb58042083e96010820ba580420827d65cc820cf953320833d54cc820bb597320836d65cc820bb99332082ec64cc820eb95332083ad54cc820dbd4f320836d53cc820eb90f32083ac43cc820bb58732083eb60cc820bb58332083e860cc8209fd96320827d658c820af99232082bd648c820cf952320833d548c820d794e320835d538c820bb98a32082fa608c820be582320827f654c820afd9132082bc644c820cf951320833d544c820bdd8532082f4614c820bed81320827f650c8209f594320833e540c820cf550320835e530c820d754c32082f6610c820bd58432082fa600c820be580320836d650c8209b59432082ee640c820bb19032083ae540c820eb55032082ee630c820f398c320836f530c820f394c320836d530c820f354c32083ae430c820eb10c32083e6610c820bb58432083e5610c820b958432083ea600c820bb58032083e9600c820af99351082bd64d4420cf953510833d54d4420cf952510833d5494420ddd46510827e64944209f592510827e63944209f58e510833e4394420cf10e510836f3294420db0ca510833e5454420cf551510827f64544209f191510827f63544209f18d510833e4354420cf10d51082be6414420af590510833e5414420cf55051082de6314420b758c510837551144209fd97410827e65d04209f597410833e54d0420cf553410827f65904209f996410827d6590420cf952410833d5490420bb98a41082ed62904209fd95410827d65504209f195410833e5450420cf55141082ef6250420bb18941082fb6050420be181410827f65104209f994410827d6510420cf950410833d5410420bb98841082ed6210420be98041082f960104209fd97310827e65cc4209f597310833e54cc420cf553310835e53cc420d754f310827f658c4209f996310827d658c420af99231082bd648c420cf952310833d548c420bb98a31082ed628c420dd9463108375518c420be98231082f9608c4209fd95310827d654c4209f1953
  | 12 => 0xc8120de94f204837853c8120ee90f20483b843c8120fc98720483f161c8120db952204836c5488120db94e204836c5388120eb90e20483ac4388120dbd4620483eb50881209f98f540827d63d50209f98b540836e62d50209f987540827d61d50209f983540837a60d50209f596540833f54950209f98e540827d63950209f986540827d61950208f59654082be6395020eb18a540833f6395020cf98e540823e6395020cf58e540833c6395020cf98a540833c6295020cfd86540833e6195020cf586540833c6195020cf982540833c6095020cfd91540827f63550209f18d540827f62550209f589540836c62550209fd85540827c6155020cfd9554082bc6355020eb189540833f6355020cf98d540833d6355020cf18d540823c6355020cf989540833c6255020cb189540833f6155020cf985540833d6155020cf185540833e6055020cf181540833c2055020af990540833d54150209f990540833e64150208f990540827e63150209f58c540827e6215020db988540827e61150209f584540827e6015020de98054082be64d4c20af593530833e54d4c20cf553530827e64d4c20cf993530823e64d4c209f593530833d64d4c208f593530827e62d4c20db98b530827e61d4c209f587530827e60d4c20de983530827d6594c20cf952530833d5494c20d7d4e530833f6494c209f992530827d6494c20cf192530827e6194c209f58653082bf6454c20af191530833e5454c20cf55153082f76154c20bd185530827f6454c20cfd91530823f6454c209f191530833c6454c208f191530835f6354c209fd89530827d6254c20db189530827f6154c20ddd8553082776154c209f18553083746154c209d18553083786054c20af99053082bd6414c20cf950530833d5414c20d754c53082f66114c20bd584530827e6414c20cf990530823e6414c209f590530833d6414c208f590530827e6314c20d798c530827e6214c20db988530827e6114c20dd98453082766114c209f58453083756114c209d584530827e6014c20de980530827f65d0c209f997430827d65d0c209f197430833e54d0c20cf55343082ee62d0c20bb58b43082fa60d0c20be583430827f6590c209f996430827d6590c209f196430833f5490c20cf952430833d5490c20cf15243082ee6290c20bb58a43082bf6590c20cfd96430823f6590c20cf99643082bd6590c20cf596430823d6590c20cf19643082be6390c20cfd4e430833e5390c20cf54e430833c5390c20eb98a43083ad6290c209fd95430827e6550c209f595430827c6550c20cf951430833d5450c20bbd8943082ec6250c20bed8143082f86050c209fd94430827e6510c209f594430827c6510c20cfd50430833e5410c20cf550430833c5410c20afd94430833f6510c208fd94430833e6510c20af59443083
  | 13 => 0x9fd97434827e65d0d209f597434827c65d0d20d7d4f434835c53d0d209fd96434827e6590d209f596434827c6590d20cfd52434833e5490d20cf552434833c5490d20cfd96434833e6590d20cf596434833c6590d20af98e434833f5390d20cf94e434833d5390d20cf14e434827f6550d209f995434827d6550d209f195434827f6510d209f994434827d6510d209f194434833f5410d20cf950434833d5410d20cf150434835f5310d20d714c43482ee6210d20bb58843482fa6010d20be580434833f6510d20cf994434833d6510d20cf19443482be6310d20e798c434833f5310d20e7d4c434831f5310d20cf94c434833d5310d20cf14c434839c5310d20c714c43483ae6210d20eb58843483ba6010d20ee580434827e65d0920cfd53424833c54d0920be98342482f960d09209f996424827c6550920cfd51424833c5450920bed8142482f860509209f994424827e65cc920d7d4f324835c53cc920be98332482f960cc9209f99632482be648c920af592324827c654c920afd9132482bc644c920d7d4d324835c534c920bdd8532482f4614c920bed8132482f8604c9209f99432482f6610c920bd584324827e64d45209f593514827e63d45209f58f514833e43d4520cf10f51483775194520afd9151482bc6454520b7d8d51482dc6354520dd544514827e64145209f590514827e63145209f58c514833e4314520cf10c514827e65d05209f597414827c65d0520bb98b41482ed62d0520ddd47414837451d0520be98341482f960d05209f996414827d65905209f196414833f5490520cf152414827f65505209f995414827c65505209f994414827d65105209f194414833f5410520cf15041483775110520dd144414827e65cc5209f597314827c65cc520ddd47314837451cc5209f996314827d658c5209f19631482be648c520af592314835f538c520d714e314827f654c5209f995314827c654c520afd9131482bc644c520bbd8931482ec624c520bed8131482f8604c5209f994314827d650c5209f194314835f530c520d714c31482ee620c520bb5883148377510c520dd144314827e65c8520ddd4621483745188520be98221482f96088520ddd4521483745148520bed8121482f860485209f99421483e521085209f997404833f54d0120cf15340482ee62d0120bb58b404827e65901209fd95404827d65501209f195404833f5450120cf15140482df6350120b718d40482ef6250120bb18940482f76150120bd185404827e65101209f997304835f53cc120d714f30482ee62cc120bb58b304827e658c120af99230482bd648c120e710e304827f654c1209f595304827c654c120afd9130482bc644c120d7d4d304835c534c120bbd8930482ec624c120bdd8530482f4614c1209f994304839c430c120bd98720482f561
  | 14 => 0x8a31882ed628c6209fd95318827d654c6209f19531882bf644c620af19131882ef624c620bb18931882fb604c620be181318827f650c6209f994318827d650c620bb98831882ed620c620dd9443188375510c620bb597218836d65c8620bb99321882ec64c8620bb98f21882ec63c8620dbd4f218836d53c8620eb90f21883ac43c8620db94721883e731c8620f90c721882ed60c8620dd94621883755188620be98221882f96088620dd94521883755148620bed8121882f86048620bb99121882ec6448620bb98d21882ec6348620dbd4d218836d5348620eb90d21883ac4348620f9d85218836e5148620f994521883665148620f954521883e63148620f94c521882ef6048620fad8121883e86048620f9484218833f54d0220cf15340883af42d0220cf952408833d5490220bb98a40882ed6290220cfd51408833c5450220b7d8d40882dc6350220bbd8940882ec6250220ebd0940882f76150220bd185408833e5410220cf55040882ee6210220bb58840882be648c220af592308835e538c220d754e308839c438c220bb98a30882ed628c220afd9130882bc644c220bbd8930882ec624c220bdd8530882f4614c220d794c308835d530c220e710c30882ee620c220bb58830882f661c8220bd58720882ed65c8220db59720882ee64c8220bb19320882ee63c8220bb18f20883ae43c8220eb10f20883e661c8220bb58720883e561c8220b958720882f965c8220de597208837a53c8220de14f20883ba43c8220ee10f20883f261c8220fc587208827e63d51209f58f544827e61d51209f587544833f54951209f992544827e63951209f58e544827d6295120db58a544827e61951209f586544827d6095120de58254482df6355120b718d54482f76155120bd185544833f64551209fd8d544835f635512097d8d544827c6355120d718d544825c63551209fd89544836f62551209bd89544827f6155120ddd85544827761551209f185544837461551209d185544827f6055120ded81544827e6515120cf550544833e64151209f98c544827d63151209f988544827c62151209f984544827d6115120af99353482bd64d4d209f993534833e64d4d208f993534827d64d4d20cf593534823d64d4d209f987534827d61d4d20d7d4e534827e6494d209f592534827e6394d209f58a534836d6294d209f986534827d6194d209f58253483796094d20afd9153482bc6454d20bdd8553482f46154d209fd91534833f6454d208fd91534827c6454d20cf191534823c6454d20d7d8d534827f6254d20dbd89534826f6254d209fd8553483776154d209dd85534827c6154d20dd18553482746154d209fd81534837b6054d209ed81534827e6514d20d754c534827e6414d209f590534835e6314d209f988534827c6214d209f984534827d6114d2
  | 15 => 0x8837661d4e209d987538827d61d4e20dd587538827561d4e20de983538835f5394e209f992538827d6494e209f986538827d6194e20afd9153882bc6454e209fd91538833f6454e208fd91538827c6454e20cf191538823c6454e20d7d8d538836f6254e209fd85538827c6154e20d754c538827e6414e209f590538835e6314e20db588538827e6114e209f584538837a6014e209fd97438827e65d0e209f597438827c65d0e20bb98b43882ed62d0e209fd96438827e6590e209f596438827c6590e20cfd52438833e5490e20cf552438833c5490e20bb98a43882ed6290e20cfd96438833e6590e20cf596438833c6590e20cfd4e438833e5390e20cf54e438833c5390e20eb98a43883ad6290e209fd95438827e6550e209f595438827c6550e20bbd8943882ec6250e209fd94438827e6510e209f594438827c6510e20cfd50438833e5410e20cf550438833c5410e20be98043882f96010e20cfd94438833e6510e20cf594438833c6510e20e798c438833f5310e20cf94c438833d5310e20cf14c43883af6210e20eb18843883ba6010e20ee580438833e54d0a20cf55342882fa60d0a20be583428836d65d0a20dbd5342883ae54d0a20db55342883ad54d0a20bb98f42883ae43d0a20eb10f42882ed61d0a20fa98342882ed60d0a20fa583428833e5450a20cf55142882fb6050a20be18142882ed6510a20db59442883ae6410a20dbd50428836d5410a20bb98c42883ae4310a20eb10c42882ed6110a20bb580428835e53cca20d754f32882fa60cca20be583328836d65cca20bb99332882ec64cca20dbd4f32883ce53cca20db54f32883cd53cca20eb90f32883ac43cca20bb58732883ea60cca20bb58332883e960cca20af99232882bd648ca20afd9132882bc644ca20d794d328835d534ca20bdd8532882f4614ca20bed8132882f8604ca20bd98432882f5610ca20bb594328836d650ca20bb99032882ec640ca20f398c328836f530ca20db54c32883ae430ca20eb10c32883e6610ca20bb58432883e5610ca20b958432882ed600ca20ddd46518827e64946209f592518827e63946209f58e518833e4394620cf10e518836f3294620db0ca518827f64546209f191518827f63546209f18d518833e4354620cf10d51882be6414620af590518837551146209fd97418827e65d06209f597418833e54d0620cf55341882fa60d0620be583418827f65906209f996418827d6590620bb98a41882ed6290620dd946418837551906209fd95418827d65506209f195418833e5450620cf55141882ef6250620bb18941883765150620dd545418827f65106209f994418827d6510620bb98841882ed62106209fd97318827e65cc6209f597318837651cc620dd547318827f658c6209f996318827d658c620af99231882bd648c620bb9
  | 16 => 0x45354720ed90d51c83b44354720ddd9151c83766454720dd59151c83746454720ddd8d51c83766354720dd58d51c83746354720ddd0d51c83764354720cd90d51c83754354720dd10d51c83344354720dd98951c83774254720dd90951c83754254720dd10951c83773254720dd8c951c83753254720dd0c951c83776054720dd58151c837551147209fd9741c827e65d07209f59741c82ee62d0720bb58b41c837651d0720dd54741c827f65907209f99641c827d6590720dd94641c837551907209fd9541c827d65507209f19541c83765150720dd54541c82fb6050720be18141c827f65107209f99441c827d6510720dd94441c83755110720be98041c82f960107209fd9731c827e65cc7209f59731c837651cc720dd54731c827f658c7209f99631c827d658c720af99231c82bd648c720dd94631c8375518c720be98231c82f9608c7209fd9531c827d654c7209f19531c82bf644c720af19131c82ef624c720bb18931c8376514c720dd54531c82fb604c720be18131c827f650c7209f99431c827d650c720bb98831c82ed620c720dd94431c8375510c720dd94721c837551c8720be98321c82f960c8720dd54621c83765148720dd94421c83755108720f948421c82fa6008720be58021c833e54d0320cf55340c82ee62d0320bb58b40c837651d0320dd54740c83765190320dd54640c833e5450320cf55140c82df6350320b718d40c82ef6250320bb18940c82f76150320bd18540c83765150320dd54540c83765110320dd54440c83b94010320d794f30c835d53cc320bb98b30c82ed62cc320dd94730c837551cc320be59730c837965cc320ded4f30c83da53cc320de54f30c83d953cc320ee90f30c83b843cc320fa98b30c82f962cc320fa58b30c837a51cc320fc94730c837251cc320fc54730c82be648c320af59230c839c438c320dd94630c8375518c320afd9130c82bc644c320d794d30c835d534c320bbd8930c82ec624c320bdd8530c82f4614c320dd94530c8375514c320e710c30c8376510c320dd54430c82f9650c320de59430c83da630c320ded4c30c8379530c320f6d0c30c83ba430c320ee10c30c83d8430c320e610c30c82f9620c320de94430c83f2510c320dc94430c83f1510c3209f98f548827d63d5220db58b548827e61d52209f587548837a60d5220cfd52548827e63952209f58e548827e61952209f586548833f64552209fd8d548827c6355220dbd89548827f61552209f185548833d5415220bd98454882f56115220cf990548827e63152209f58c548836d62152209f984548837661152209d984548827d6115220dd58454882756115220de98054882be64d4e20af59353882f661d4e20bd587538827e64d4e20cf993538823e64d4e209f593538833d64d4e208f593538836d62d4e209f98753
  | 17 => 0x5320cfd5254c827e63953209f58e54c827e61953209f58654c833f64553209fd8d54c827c63553209fd8554c827c6155320cf55054c82f66115320bd58454c833e64153209f98c54c827d6315320db98854c827e6115320dd98454c827661153209f58454c837561153209d58454c83796015320af99353c82bd64d4f20bd98753c82f561d4f209f99353c833e64d4f208f99353c827d64d4f20cf59353c823d64d4f20db98b53c827e61d4f20dd98753c827661d4f209f58753c837561d4f209d58753c837960d4f20d7d4e53c827e6494f209f59253c827e6194f209f58653c82bf6454f20af19153c827f6454f20cfd9153c823f6454f209f19153c833c6454f208f19153c835f6354f209fd8553c827c6154f20ded8153c835d5314f20bd98453c82f56114f209f99053c827d6414f20d798c53c836e6214f209f98453c83766114f209d98453c827d6114f20dd58453c82756114f20de58053c827f65d0f209f99743c827d65d0f209f19743c835e53d0f20d754f43c82fa60d0f20be58343c827f6590f209f99643c827d6590f209f19643c833f5490f20cf95243c833d5490f20cf15243c833f6590f20cf99643c833d6590f20cf19643c833f5390f20cf94e43c833d5390f20cf14e43c827f6550f209f99543c827d6550f209f19543c82fb6050f20be18143c827f6510f209f99443c827d6510f209f19443c833f5410f20cf95043c833d5410f20cf15043c835e5310f20d754c43c82ee6210f20bb58843c833f6510f20cf99443c833d6510f20cf19443c839e6310f20cfd4c43c833e5310f20e794c43c831e5310f20cf54c43c839d5310f20c754c43c833c5310f20eb98843c83ad6210f20cfd5342c833c54d0b20cf95242c833d5490b20be98242c82f96090b20cfd5142c833c5450b20cf95042c833d5410b20be98042c82f96010b20af99232c82bd648cb20d794e32c835d538cb20be98232c82f9608cb20afd9132c82bc644cb20bdd8532c82f4614cb20be18132c835e530cb20d754c32c82f6610cb20bd58432c82fa600cb20be58032c837751947209f99251c827d64947209f98e51c827d6394720cf90e51c833c4394720ddd5251c83765494720dd55251c83745494720ddd4e51c83765394720dd54e51c83745394720ed90e51c83b44394720ddd9251c83766494720dd59251c83746494720ddd8e51c83766394720dd58e51c83746394720ddd0e51c83764394720cd90e51c83754394720dd10e51c83344394720dd18a51c83774294720dd90a51c83754294720dd10a51c83773294720dd8ca51c83753294720dd0ca51c83776094720dd58251c827f64547209f19151c827f63547209f18d51c833e4354720cf10d51c83776554720ddd5151c83765454720dd55151c83745454720ddd4d51c83765354720dd54d51c837
  | 18 => 0xaf990510c2bd6414430e710c510c2ee6214430bb588510c37551144309fd97410c27e65d04309f597410c33e54d0430cf553410c39c43d0430be983410c2f960d04309fd96410c27e65904309f596410c2de6390430b758e410c39c4390430dd946410c37551904309fd95410c27d65504309f195410c33e5450430cf551410c2df6350430b718d410c39c4350430dd945410c3755150430bed81410c2f860504309fd94410c27e65104309f594410c39c4310430e710f310c37651cc430dd547310c2fa60cc430be583310c27d658c430af992310c2bd648c430e710e310c27f654c430afd91310c2bc644c430e710d310c2ef624c430bb189310c2fb604c430e710c310c2ee620c430bb588310c376510c430dd544310c2fa600c430be580310c27f65c84309f997210c27d65c8430e710f210c36e52c8430db54b210c2fa60c8430be583210c27f65884309f996210c27d6588430e710e210c3765188430dd546210c2fa6088430be582210c27f65484309f595210c27c6548430b7d8d210c2dc6348430e710d210c36e5248430db549210c3765148430dd545210c2fb6048430be181210c27f65084309f994210c27d6508430e710c210c3e521084309f992500c33e64940308f992500c27d6494030cf592500c23d6494030d7d0e500c33e4394030cf10e500c35c4394030c710e500c27d65d0030cfd53400c33c54d0030e710f400c27f65900309f596400c33e5490030cf552400c2de6390030b758e400c39c43900309fd95400c33f5450030cf151400c2df6350030b718d400c39c4350030bbd89400c2ec6250030bdd85400c2f461500309fd94400c27e65100309f594400c27c6510030cf950400c33d5410030b798c400c2dd6310030e710c400c39e43cc030e710f300c2de64cc030b7193300c2be648c030af592300c2dd638c030d794e300c39c438c030ee992300c3b9648c030be58e300c37a538c030f694e300c3db438c030ee90e300c3b8438c030f610e300c398438c030be98a300c2fa618c0309fd95300c2bf644c030af191300c39e434c030e710d300c2ef624c030bb189300c2f7614c030bd185300c2df654c030d7d95300c25f654c030e7d91300c2de644c030b7191300c39c644c030a7191300c3cf624c030f3189300c3d7614c030f5185300c2df604c030d7941300c2fb654c030ded95300c27b654c030eed91300c3b8644c030bed8d300c3db634c030de94d300c3da534c030ee90d300c3b8434c030fad89300c2f8624c030fa189300c2e8624c030fcd85300c2f8614c030fc185300c2f0614c030b798f54c82dd63d5320bd98754c82f561d53209f98f54c835e63d53209798f54c827d63d5320d758f54c825d63d5320db98b54c827e61d5320dd98754c827661d53209f58754c837561d53209d58754c837960d
  | 19 => 0x2304c3cf528c130f314a304c3d7518c130f5146304c3db508c1309f98f540c35e63d50309f98b540c27d62d50309f987540c27d61d50309f983540c37a60d50309f596540c33f54950309f98a540c27d62950309f986540c27d6195030cfd91540c27f63550309f58d540c35c63550309fd89540c27c62550309fd85540c27c6155030cf550540c2ee6215030bb588540c2f66115030bd584540c27e6415030cf990540c27e6315030d798c540c27e6215030db988540c26e62150309f588540c36d62150309b588540c27e6115030dd984540c27661150309f584540c37561150309d584540c27e6015030de980540c27e6494c309f592530c27d65d0c30b7597430c35d65d0c30d7d53430c35d54d0c30b7583430c27f6590c309f596430c33e5490c30cf552430c2de6390c30be982430c2f96090c30cfd96430c33e6590c30cf596430c33c6590c30af98e430c29e6390c30cf94e430c3ba6090c30ee582430c27f6550c309fd94430c27d6510c30cf950430c33d5410c30e750c430c2fa6010c30be580430c33f6510c30cf994430c33d6510c30cf194430c2be6310c30e798c430c33e5310c30ee980430c3b96010c30d7594430c25d6510c30b7990430c39e6410c30d7d50430c39e5410c30d7550430c39d5410c30f6980430c2dd6010c30f6580430c39e6510c30c7994430c39d6510c30c7594430c39f6210c30e7988430c39d6210c30e7188430c39f6110c30e7984430c39d6110c30e7184430c39f6010c30e7980430c39a6010c30e7580430c3996010c30e7180430c39c43d4830e710e520c36f52948309f992520c27d6494830cf90e520c33c43948309f986520c27d6194830e710d520c27f64548309f191520c33e4354830cf10d520c27f61548309f185520c3786054830af990520c2bd6414830e710c520c36d5214830bd984520c2f561148309fd97420c27e65d08309f597420c33e54d0830cf553420c39c43d0830be983420c2f960d08309fd96420c27e65908309f596420c2de6390830b758e420c39c4390830db94a420c36d52908309fd95420c27d65508309f195420c33e5450830cf551420c2df6350830b718d420c39c4350830db949420c36d5250830bed81420c2f860508309fd94420c27e65108309f594420c39c4310830e710f320c36e52cc830db54b320c2fa60cc830be583320c27d658c830af992320c2bd648c830e710e320c27f654c830afd91320c2bc644c830e710d320c2f7614c830bd185320c2fb604c830e710c320c36e520c830db548320c2f6610c830bd584320c2fa600c830be580320c39c43d4430e710e510c37751944309f992510c27d6494430cf90e510c33c43944309f98a510c27d6294430e710d510c27f64544309f191510c33e4354430cf10d510c27f62544309f189510c3786054430
  | 20 => 0xc3745214530f9148514c3645214530ddd90514c3766414530dd590514c3746414530ddd8c514c3774314530dd90c514c3364314530dd50c514c3744314530cd10c514c3776214530dd988514c3756214530dd188514c3774214530dd908514c3754214530dd108514c3773214530dd8c8514c3753214530dd0c8514c3776014530dd580514c37530145309f997414c27d65d05309f197414c33f54d0530cf153414c36f52d0530db14b414c37751d0530dd147414c27e65905309f596414c27c6590530cfd52414c33c5490530dbd4a414c36c5290530ddd46414c37451905309fd95414c27e65505309f195414c33f5450530cf151414c36f5250530db149414c3775150530dd145414c27e65105309f594414c27c6510530cfd50414c33c5410530dbd48414c36c5210530ddd44414c3745110530be980414c2f960105309f997314c33f54cc530cf153314c36f52cc530db14b314c37451cc530af992314c2bd648c530cfd52314c33c548c530dbd4a314c36c528c530ddd46314c374518c530be982314c2f9608c530afd91314c2bc644c530cfd51314c33c544c530bbd89314c2ec624c530dbd49314c36c524c530ddd45314c374514c530bed81314c2f8604c5309f994314c33f540c530cf150314c2ee620c530bb588314c36f520c530db148314c377510c5309f997214c27d65c85309f197214c33f54c8530cf153214c36f52c8530db14b214c37751c8530dd147214c27e65885309f596214c27c6588530cfd52214c33c5488530dbd4a214c36c5288530ddd46214c37451885309fd95214c27e65485309f195214c33f5448530cf151214c36f5248530db149214c3775148530dd145214c27e65085309f594214c27c6508530cfd50214c33c5408530b798c214c2dd6308530dbd48214c36c5208530ddd44214c3745108530f9484214c27e65d0130cfd53404c33c54d0130b798f404c2dd63d0130dbd4b404c36c52d0130ddd47404c37451d01309f996404c33f5490130cf152404c36f5290130db14a404c3775190130dd146404c27f65501309f595404c27c6550130cfd51404c33c5450130b7d8d404c2dc6350130bbd89404c2ec6250130dbd49404c36c5250130bdd85404c2f46150130ddd45404c37451501309f994404c33f5410130cf150404c36f5210130db148404c3775110130dd144404c3b94010130cfd53304c33c54cc130dbd4b304c36c52cc130ddd47304c37451cc130eed53304c3b854cc130ee90f304c3b843cc130fad4b304c37852cc130fa14b304c36852cc130fcd47304c37851cc130fc147304c37051cc130af992304c2bd648c130cfd52304c33c548c130e790e304c39c438c130dbd4a304c36c528c130ddd46304c374518c130e7992304c39d648c130e7d52304c35e548c130d7152304c39c548c130c715
  | 21 => 0x43d4930cb10f524c36f61d4930db987524c36d61d4930db187524c36f60d4930db583524c2be6494930af592524c33f5494930cf152524c36f5294930bd986524c2f56194930afd91524c2bc6454930cfd51524c33c5454930bdd85524c2f46154930cfd50524c33c5414930db548524c27e64149309f590524c33e4314930cf10c524c27e61149309f584524c2ee6514930db994524c36f5414930ebd50524c32f5414930db950524c36d5414930db150524c3ac5414930cb150524c3ae4314930eb10c524c36f6414930db990524c36d6414930db190524c36f6314930dbd0c524c36e4314930cb90c524c36d4314930db10c524c32c4314930dbd84524c36e6114930db584524c36c6114930dbd80524c36d6014930db4c0524c27e65d09309f597424c27c65d0930cfd53424c33c54d0930dbd4b424c36c52d09309f996424c27d65909309f196424c33f5490930cf152424c36f5290930db14a424c27f65509309f995424c27c6550930cfd51424c33c5450930dbd49424c36c52509309f994424c27d65109309f194424c33f5410930cf150424c36f5210930db148424c2fa6010930be580424c27e65cc930cfd53324c33c54cc930db14b324c2be648c930af592324c33f548c930cf152324c36f528c930db14a324c2fa608c930be582324c2bf644c930af191324c33f544c930cf151324c36f524c930db149324c2f7614c930bd185324c2fb604c930be181324c27e650c930cfd50324c33c540c930dbd48324c2f6610c930bd584324c33f54d4530cf153514c36f52d4530db14b514c27e64d45309f593514c33e43d4530cf10f514c27e62d45309f58b514c37754d4530edd53514c33754d4530dd953514c37554d4530dd153514c3b454d4530cd153514c3b643d4530ed10f514c37752d4530f9d4b514c36752d4530dd94b514c37552d4530dd14b514c3e452d4530d914b514c37764d4530dd993514c37564d4530dd193514c37763d4530ddd0f514c37643d4530cd90f514c37543d4530dd10f514c33443d4530ddd8b514c37662d4530dd58b514c37462d4530ddd0b514c37642d4530dd50b514c37442d4530ddccb514c37632d4530dd4cb514c37432d4530ddd83514c37560d4530af992514c2bd6494530cfd52514c33c5494530bb98a514c2ed6294530dbd4a514c36c5294530ddd46514c2bf6454530af191514c33f5454530cf151514c2ef6254530bb189514c36f5254530db149514c33f5414530cf150514c36f5214530db148514c37551145309f990514c27d6414530cf90c514c33c43145309f988514c27d6214530bd994514c3766514530ddd50514c3b75414530cdd50514c3765414530dd550514c3745414530ed150514c3345414530ed90c514c3b44314530ddd48514c3e75214530d9d48514c3765214530dd548514
  | 22 => 0x630e710f218c37651c8630dd547218c27f65886309f996218c27d6588630cf952218c33d5488630e710e218c36e5288630db54a218c27f65486309f595218c27c6548630cf951218c33d5448630b7d8d218c2dc6348630e710d218c27f65086309f994218c27d6508630cf950218c33d5408630e710c218c36e5208630db548218c3765108630dd544218c3e52108630cf953408c33d54d0230e710f408c33e5490230cf552408c2de6390230b758e408c39c4390230cf951408c33d5450230b7d8d408c2dc6350230e710d408c2ef6250230bb189408c2f76150230bd185408c33e5410230cf550408c2de6310230b758c408c39c4310230ee500408c33e54cc230cf553308c39e43cc230e710f308c2dd65cc230d7597308c2de64cc230b7193308c39e54cc230e7553308c2f965cc230de597308c3ba54cc230ee553308c3ba43cc230ee10f308c37a52cc230de947308c27e62d51309f58b544c27e61d51309f587544c33f63d5130cf58f544c33f62d5130cf98b544c33d62d5130cf18b544c33f61d5130cf987544c33d61d5130cf187544c33f60d5130cf583544c33f5495130bb98a544c2ed6295130bd986544c2f561951309f992544c23e64951309f58e544c35d63951309f98a544c36e62951309b98a544c27d6295130db58a544c26d62951309f986544c37661951309d986544c27d6195130dd586544c27561951309f582544c3796095130bbd89544c2ec6255130bdd85544c2f46155130cfd91544c27f6355130d7d8d544c25f63551309fd89544c36f62551309bd89544c27c6255130db189544c26c62551309fd85544c37761551309dd85544c27c6155130dd185544c27461551309fd81544c37b60551309f994544c33d5415130cf990544c27e63151309f18c544c27e62151309f588544c27e61151309f584544c2be6515130cf994544c23e6515130cfd8c544c23e6315130cf58c544c23c6315130cfd88544c33e6215130cf588544c33c6215130cfd84544c33e6115130cf584544c33c6115130cfd80544c33d6015130cf4c0544c27e65d0d30cfd53434c33c54d0d30be983434c2f960d0d309f996434c33f5490d30cf952434c33d5490d30cf152434c2be6590d30cf996434c23e6590d30af98e434c27c6550d30cfd51434c33c5450d30bed81434c2f86050d309f994434c33f5410d30cf950434c33d5410d30cf150434c2be6510d30cf994434c23e6510d30af98c434c39e6310d30cfd53524c33c54d49309f993524c27d64d4930cf90f524c33c43d49309f987524c27d61d4930dbd53524c3af54d4930cbd53524c36e54d4930db553524c36c54d4930eb153524c32c54d4930eb90f524c3ac43d4930dbd93524c36e64d4930db593524c36c64d4930dbd8f524c36f43d4930db90f524c32e43d4930db50f524c36c
  | 23 => 0x7550438c31d5410e30e7150438c2dd6010e30e7594438c29d6510e30c7594438c39f6210e30e7988438c39d6210e30e7188438c39f6110e30e7984438c39d6110e30e7184438c39f6010e30e7980438c39d6010e30e7180438c2be64d4a30af593528c33e54d4a30cf553528c39c43d4a30bd987528c2f561d4a30cf952528c33d5494a30e710e528c36f5294a30bd986528c2f56194a309f992528c27d6494a30cf90e528c33c4394a309f986528c3766194a309d986528c27d6194a30dd586528c2756194a30cf951528c33d5454a30e710d528c27f6454a309f191528c33e4354a30cf10d528c27f6154a309f185528c2be6414a30af590528c33e5414a30cf550528c39c4314a30db548528c27f65d0a309f997428c27d65d0a30cf953428c33d54d0a30e710f428c27f6590a309f996428c27d6590a30cf952428c33d5490a30b798e428c2dd6390a30e710e428c27f6550a309f595428c27c6550a30cf951428c33d5450a30b7d8d428c2dc6350a30e710d428c27f6510a309f994428c27d6510a30cf950428c33d5410a30e710c428c2fa6010a30be580428c33e54cca30cf553328c39c43cca30af992328c2bd648ca30cf952328c33d548ca30e710e328c36e528ca30db54a328c2fa608ca30be582328c2bf644ca30af191328c33e544ca30cf551328c39c434ca30db949328c36d524ca30bdd85328c2f4614ca30bed81328c2f8604ca30cf950328c33d540ca30e710c328c2f6610ca30bd584328c2be64d4630af593518c33e54d4630cf553518c39c43d4630bb98b518c2ed62d4630cf952518c33d5494630e710e518c2ee6294630bb58a518c37751946309f992518c27d6494630cf90e518c33c43946309f98a518c36e62946309b98a518c27d6294630db58a518c26d6294630cf951518c33d5454630e710d518c27f64546309f191518c33e4354630cf10d518c27f62546309f189518c2be6414630af590518c33e5414630cf550518c39c4314630dd544518c27f65d06309f997418c27d65d0630cf953418c33d54d0630e710f418c27f65906309f996418c27d6590630cf952418c33d5490630b798e418c2dd6390630e710e418c27f65506309f595418c27c6550630cf951418c33d5450630b7d8d418c2dc6350630e710d418c27f65106309f994418c27d6510630cf950418c33d5410630e710c418c2fa6010630be580418c33e54cc630cf553318c39c43cc630af992318c2bd648c630cf952318c33d548c630e710e318c376518c630dd546318c2fa608c630be582318c2bf644c630af191318c33e544c630cf551318c39c434c630bbd89318c2ec624c630dd945318c375514c630bed81318c2f8604c630cf950318c33d540c630e710c318c2ee620c630bb588318c27f65c86309f997218c27d65c8630cf953218c33d54c8
  | 24 => 0x32cc36d52ccb30be98332cc2f960ccb30af99232cc2bd648cb30afd9132cc2bc644cb30bdd8532cc2f4614cb30be18132cc36e520cb30db54832cc2f6610cb30bd58432cc2fa600cb30be58032cc2be6494730af59251cc37751947309f99251cc33e64947308f99251cc27d6494730cf59251cc23d6494730cf90e51cc33c43947309f98a51cc27d62947309fd9151cc27c6454730cf90d51cc33c43547309fd8951cc27c6254730ded8151cc2ee6214730bb58851cc37551147309fd9741cc27e65d07309f59741cc33f54d0730cf15341cc37651d0730dd54741cc2fa60d0730be58341cc27f65907309f99641cc27d65907309fd9541cc27d65507309f19541cc33f5450730cf15141cc2fb6050730be18141cc27f65107309f99441cc27d6510730dd94441cc3755110730dd94731cc37551cc730be98331cc2f960cc730af99231cc2bd648c730afd9131cc2bc644c730bbd8931cc2ec624c730be18131cc2ee620c730bb58831cc376510c730dd54431cc2fa600c730be58031cc27f65c87309f99721cc27d65c8730db94b21cc36d52c8730be98321cc2f960c87309fd9621cc27e65887309f59621cc3765188730dd54621cc2fa6088730be58221cc27f65487309f59521cc27c6548730db94921cc36d5248730dd94521cc3755148730bed8121cc2f860487309fd9421cc27e65087309f59421cc2de6308730b758c21cc3e52108730cf95340cc33d54d0330b798f40cc2dd63d0330cfd5240cc33c5490330cf95140cc33d5450330b7d8d40cc2dc6350330bbd8940cc2ec6250330bdd8540cc2f46150330cfd5040cc33c5410330d758f548c27e62d52309f58b548c27e61d52309f587548c37a60d5230cfd52548c27e62952309f58a548c27e61952309f586548c39f6395230cfd8e548c33d6395230cfd8a548c33e6295230cf58a548c33c6295230cfd86548c33e6195230cf586548c33c6195230cf982548c33c6095230cfd91548c35f63552309fd89548c27c62552309fd85548c27c6155230cfd95548c39f6355230cfd8d548c31f6355230cf58d548c33f6255230cf989548c33d6255230cf189548c33f6155230cf985548c33d6155230cf185548c33e6055230cf181548c33d5415230cf990548c35d63152309f988548c27d62152309f984548c27d6115230de980548c33e54d0e30cf553438c2fa60d0e30be583438c35d65d0e30d7d53438c39e54d0e30d7553438c39d54d0e30f6983438c2dd60d0e30f6583438c33f5490e30cf952438c33d5490e30cf152438c2bd6590e30cf596438c33e5450e30cf551438c2fb6050e30be181438c33f5410e30cf950438c33d5410e30cf150438c39d4310e30af594438c33d6510e30e798c438c2dd6510e30d7594438c39e6410e30d7d50438c39f5410e30e7950438c35d5410e30e
  | 25 => 0x2fa60d0440be583411027d65904409fd95411033e5450440dd94441103755110440be98041102f960104409fd97311027e65cc4409f597311027f658c4409f996311027d658c440af99231102bd648c440dd9463110375518c4409fd95311027d654c4409f19531102bf644c440af19131102ef624c440bb1893110376514c440dd54531102fb604c440be181311027f650c4409f994311027d650c440bb98831102ed620c4409fd97211027e65c84409f597211037651c8440dd547211027f65884409f996211027d6588440db94a211036d52884409fd95211027d65484409f19521102bf6448440af19121102fb6048440be181211027f65084409f994211027d6508440db948211036d5208440dd94421103755108440f9484211033e4394040cf10e50102be63d0040cf94f401033d52d0040cf54740102bd6490040cf95240102f96490040de95240103ba5490040ee90e40103b843900409fd9540102df6350040b718d40102ef6250040bb18940102f76150040bd18540102bf6550040cfd95401023f6550040e7d8d40102bc6350040e718d401029c6350040cf94d40103af6250040eb189401033d5250040edd8540103b46150040cf54540102bf6050040cf94140102fb6550040ded95401027b6550040bed9140103bb6450040de95140103ba5450040f6d8d40103d86350040eed0d40103b94350040fad8940103e86250040ee90940103b84250040fcd8540103f06150040ee90540103b84150040bb98b54cc2ed62d5330bd98754cc2f561d5330d798f54cc27e62d5330db98b54cc26e62d53309f58b54cc36d62d53309b58b54cc27e61d5330dd98754cc27661d53309f58754cc37561d53309d58754cc37960d5330cfd5254cc27e62953309f58a54cc27e61953309f58654cc33f64553309fd8954cc27c62553309fd8554cc27c6155330cf55054cc33e6415330d798c54cc27e62153309f58854cc27e61153309f58454cc3796015330cf95243cc33d5490f30be98243cc2f96090f30cf99643cc33d6590f30ee98243cc3b96090f30cf95043cc33d5410f30be98043cc2f96010f30cf99443cc33d6510f30e798c43cc3ba6010f30ee58043cc2be6494b30af59252cc36f5294b309f99252cc33e6494b308f99252cc27d6494b30cf59252cc23d6494b30cf90e52cc33c4394b309f98652cc27d6194b309fd9152cc27c6454b30cf90d52cc33c4354b309fd8552cc27c6154b30ded8152cc36d5214b30bd98452cc2f56114b309fd9742cc27e65d0b309f59742cc33f54d0b30cf15342cc36e52d0b30db54b42cc2fa60d0b30be58342cc27f6590b309f99642cc27d6590b309fd9542cc27d6550b309f19542cc33f5450b30cf15142cc2fb6050b30be18142cc27f6510b309f99442cc27d6510b30db94842cc36d5210b30db94b
  | 26 => 0x50c5409f19431502be640c540af590315035f530c540d714c31502ee620c540bb588315036f520c540db1483150377510c540dd14431502fa600c540be580315027e65c85409f597215027c65c8540af99321502bd64c8540d7d4f215035c53c8540dbd4b215036c52c8540ddd47215037451c8540be98321502f960c85409f996215027d65885409f19621502be6488540af592215035f5388540d714e215036f5288540db14a21503775188540dd14621502fa6088540be582215027f65485409f995215027c6548540af99121502bd6448540d7d4d215035c5348540dbd49215036c5248540ddd45215037451485409f994215027d65085409f19421502be6408540af590215035f5308540d714c215036f5208540db14821503775108540dd14421503e52108540d7d4f405035c53d0140dbd4b405036c52d0140ddd47405037451d0140f6d4f40503d853d0140ee90f40503b843d0140fad4b40503e852d0140eed0b40503b942d0140fcd4740503f051d0140eed0740503b941d0140d7d4e405035c5390140dbd4a405036c5290140ddd4640503745190140af98e405039f5390140cf14e405039c5390140c714e40502bd6290140ebd4a40503ac5290140af58640503b75190140ed14640503bb5090140d7d4e531033c6494c409f98a531027d6294c409f986531027d6194c409fd89531027c6254c409fd85531027c6154c40d754c53102ee6214c40bb58853102f66114c40bd584531035e53d0c40d754f43102fa60d0c40be583431027d6590c40cf95243102bd6590c40cf59643102be6390c40cf54e43102bd6090c409fd95431033e5410c40d794c431035d5310c40e750c43102fa6010c40be58043102be6310c40e798c431033e5310c40e794c431031e5310c40cf54c431039d5310c40ee98043102bd6010c40ee58043102b96010c40bd98752102f561d4840dbd4a521027e63948409f58e521033e4394840cf10e521027e61948409f586521027f63548409f18d521033e4354840cf10d521027f61548409f185521036d5214840cf953421036e52d0840db54b42102fa60d0840be583421027d65908409fd95421033e5450840db948421036d5210840be98042102f960108409fd97321027e65cc8409f597321027f658c8409f996321027d658c840af99232102bd648c840db94a321036d528c8409fd95321027d654c8409f19532102bf644c840af191321036e524c840db54932102f7614c840bd18532102fb604c840be181321027f650c8409f994321027d650c840bd98432102f5610c840bb98b51102ed62d4440ddd46511027e63944409f58e511033e4394440cf10e511027e62944409f58a511027f63544409f18d511033e4354440cf10d511027f62544409f18951103755114440cf953411037651d0440dd5474110
  | 27 => 0x40f514f515035453d4540ed90f51503b443d4540ddd4b51503e752d4540d9d4b515037652d4540dd54b515037452d4540f914b515036452d4540edd0b51503b542d4540ddd93515037763d4540dd98f515037563d4540dd18f515037743d4540dd90f515033643d4540dd50f515037443d4540cd10f515037762d4540dd98b515037562d4540dd18b515037742d4540dd90b515037542d4540dd10b515037732d4540dd8cb515037532d4540dd0cb515037760d4540dd58351502de6394540b758e515035f5394540d714e51502ee6294540bb58a515036f5294540db14a51503775194540b7d8d51502dc6354540d7d4d515035c5354540bbd8951502ec6254540dbd49515036c5254540d7d4c515035c5314540dbd48515036c5214540dd544515027e63145409f58c515033e4314540cf10c515027e62145409f58851502f66514540dd99451503b56414540ddd4c51503d75314540d5d4c51503765314540dd54c51503745314540f514c51503545314540ed90c51503b44314540ddd4851503e75214540d9d4851503765214540dd54851503745214540f914851503645214540edd0851503b54214540ddd9051503776314540dd98c51503756314540dd18c51503774314540dd90c51503364314540dd50c51503744314540cd10c51503776214540dd98851503756214540dd18851503774214540dd90851503754214540dd10851503773214540dd8c851503753214540dd0c851503776014540dd580515037540145409f997415035f53d0540d714f415036f52d0540db14b415037451d0540af997415033e65d0540af98f415039f53d0540cf14f415039c53d0540c714f41502bd62d0540ebd4b41503ac52d0540edd47415033c51d0540ed147415033451d0540af98341502bd6490540d7d4e415035c5390540dbd4a415036c5290540ddd4641503745190540be98241502f96090540d7d4d415035c5350540dbd49415036c5250540ddd4541503745150540bed8141502f86050540af18d415039f5350540cf14d415039c5350540c714d41502bf6250540ebd4941503ac5250540edd8541503b75150540cf14541503b45150540eed8141502bc6050540ee18141502b860505409f99441502be6410540d7d4c415035c5310540dbd48415036c5210540ddd44415027e65cc5409f597315027c65cc540afd9331502bc64cc540d7d4f315035c53cc540dbd4b315036c52cc540ddd47315037451cc5409f996315027d658c5409f19631502be648c540af592315035f538c540d714e315036f528c540db14a3150377518c540dd146315027f654c5409f995315027c654c540afd9131502bc644c540d7d4d315035c534c540bbd8931502ec624c540dbd49315036c524c540ddd453150374514c540bed8131502f8604c5409f994315027d6
  | 28 => 0xd4d435035c5350d40bed8143502f86050d409f994435035f5310d40af994435033e6510d40af98c435039e6310d40cfd4c435039f5310d40c7d4c435039c5310d40af58843502bd6110d40af980435035f53d4940d714f525027e63d49409f58f525033e43d4940cf10f525027e61d49409f58752503af64d4940dbd4f52503cf53d4940d3d4f525036e53d4940db54f525036c53d4940f314f525034c53d4940eb90f52503ac43d4940dbd93525036f63d4940db98f525036d63d4940db18f525036f43d4940db90f525032e43d4940db50f525036c43d4940cb10f525036f61d4940db987525036d61d4940db187525036f60d4940db58352502de6394940b758e525035f5394940d714e525036f5294940bd98652502f56194940b7d8d52502dc6354940d7d4d525035c5354940bdd8552502f46154940d7d4c525035c5314940db548525027e63149409f58c525033e4314940cf10c525027e61149409f58452502ee6514940db99452503ad6414940dbd4c52503cf5314940d3d4c525036e5314940db54c525036c5314940f314c525034c5314940eb90c52503ac4314940dbd90525036f6314940db98c525036d6314940db18c525036f4314940db90c525032e4314940db50c525036c4314940cb10c525036f6114940db984525036d6114940db184525036f6014940db580525036d40149409f997425035f53d0940d714f425036c52d0940af997425033e65d0940af98f425039f53d0940cf14f425039c53d0940c714f42503af52d0940cf14b42503ac52d0940cb14b42502bd61d0940af98342502bd6490940d7d4e425035c5390940dbd4a425036c5290940be98242502f96090940d7d4d425035c5350940dbd49425036c5250940bed8142502f86050940af18d425039f5350940cf14d425039c5350940c714d42503af6250940ebd49425033c5250940eb14942502bf6150940eed8142502bc6050940ee18142502b860509409f99442502be6410940d7d4c425035c5310940dbd48425027e65cc9409f597325027c65cc940afd9332502bc64cc940d7d4f325035c53cc940dbd4b325036c52cc9409f996325027d658c9409f19632502be648c940af592325035f538c940d714e325036f528c940db14a325027f654c9409f995325027c654c940afd9132502bc644c940d7d4d325035c534c940dbd49325036c524c940bdd8532502f4614c940bed8132502f8604c9409f994325027d650c9409f19432502be640c940af590325035f530c940d714c325036f520c940db14832502f6610c940bd58432502fa600c940be580325035f53d4540d714f515036f52d4540db14b515027e63d45409f58f515033e43d4540cf10f515027e62d45409f58b51503b764d4540ddd4f51503d753d4540d5d4f515037653d4540dd54f515037453d45
  | 29 => 0x39027e6194e409f586539027f6254e409f189539027f6154e409f185539035d5314e40d794e439035d5390e40be98243902f96090e40cf94e439039e5390e40c794e439033d5390e40e754e43903ba6090e40af58243903b96090e40d794d439035d5350e40bed8143902f86050e40e750c43902bd6510e40cf594439039e6310e40e7d4c439033d5310e40e714c43902bd6010e40dbd4a529027e6394a409f58e529033e4394a40cf10e529027e6194a409f586529027f6354a409f18d529033e4354a40cf10d529027f6154a409f185529036d5214a40db94a429036d5290a40be98242902f96090a40db949429036d5250a40bed8142902f86050a409fd97329027e65cca409f597329027f658ca409f996329027d658ca40af99232902bd648ca409fd95329027d654ca409f19532902bf644ca40af19132902f7614ca40bd18532902fb604ca40be181329027f650ca409f994329027d650ca40bd98432902f5610ca40be98032902f9600ca40ddd46519027e63946409f58e519033e4394640cf10e519027e62946409f58a519027f63546409f18d519033e4354640cf10d519027f62546409f18951903755114640dd94641903755190640be98241902f96090640dd94541903755150640bed8141902f860506409fd97319027e65cc6409f597319027f658c6409f996319027d658c640af99231902bd648c6409fd95319027d654c6409f19531902bf644c640af19131902ef624c640bb18931902fb604c640be181319027f650c6409f994319027d650c640bb98831902ed620c640be98031902f9600c6409fd97219027e65c86409f59721902fa60c8640be583219027f65886409f996219027d6588640be98221902f960886409fd95219027d65486409f19521902bf6448640af191219027f65086409f994219027d6508640f948421902bd65d0240cf59740902be63d0240cf94f409033d52d0240cf54740902f965d0240de597409027e62d4d409f58b535027e61d4d409f587535039d64d4d40d7d93535035f62d4d40d798b535035d62d4d40d718b535035f61d4d40d7987535035d61d4d40d7187535035f60d4d40d7583535035f5394d40bb98a53502ed6294d40bd98653502f56194d40bbd8953502ec6254d40bdd8553502f46154d40d754c535033f6414d409f988535027d6214d409f984535027d6114d40b7994535035e6514d40e7d90535035f6414d40c7d90535035f6214d40d7988535035d6214d40d7188535035f6114d40d7984535035d6114d40d7184535035f6014d40d7580535035d4014d409f997435035c53d0d40d7d4e435035c5390d40be98243502f96090d40af98e435033f5390d40e7d4e435033c5390d40e714e435031c5390d40af58a43502bd6190d40af98243503ba6090d40ae98243503b96090d40d7
  | 30 => 0xf661d4f40bd58753d035f5394f40cf19253d027e6294f409f58a53d027e6194f409f58653d027f6254f409f18953d027f6154f409f18553d035d5314f40d794f43d035d53d0f40be98343d02f960d0f40af59643d033d6590f40cf54e43d02bd6290f40af58643d02be6090f40d794c43d035d5310f40be98043d02f96010f40e798c43d033e5310f40e794c43d031e5310f40cf54c43d039d5310f40c754c43d02bd6210f40af58443d02be6010f40ee98043d03b96010f40dbd4a52d027e6394b409f58e52d033e4394b40cf10e52d027e6194b409f58652d027f6354b409f18d52d033e4354b40cf10d52d027f6154b409f18552d036d5214b40bd98452d02f56114b40db94b42d036d52d0b40be98342d02f960d0b40af98f42d033e53d0b40cf94b42d03ae52d0b40eb54b42d02bd61d0b40af98342d03ba60d0b40ee58342d02bf6550b40cfd9542d02bc6350b40cf94d42d03af6250b40cf94942d02bf6150b40af18142d036e5210b40db54842d02fa6010b40be58042d027f65ccb409f99732d027d65ccb40afd9332d02bc64ccb40db94b32d036d52ccb409fd9632d027e658cb409f59632d02be648cb40af59232d027f654cb409f59532d027c654cb40afd9132d02bc644cb40bdd8532d02f4614cb40bed8132d02f8604cb409fd9432d027e650cb409f59432d02be640cb40af59032d036e520cb40db54832d02f6610cb40bd58432d037751947409f98e51d027d6394740cf90e51d033c43947409f98a51d027d62947409fd8d51d027c6354740cf90d51d033c43547409fd8951d027c6254740bb98851d02ed6214740dd54451d037651d0740dd54741d02fa60d0740be58341d02be63d0740cf94f41d02bd62d0740cf94741d03b651d0740ed54741d02be60d0740ee98341d03b960d0740afd9541d033f6550740af18d41d033e5350740afd8941d03b76150740cf94541d02bc6050740dd94441d03755110740be98041d02f960107409fd9731d027e65cc7409f59731d02bf64cc740af19331d037651cc740dd54731d027f658c7409f99631d027d658c740af99231d02bd648c7409fd9531d027d654c7409f19531d02bf644c740af19131d02ef624c740bb18931d02fb604c740be18131d027f650c7409f99431d027d650c740af99031d02bd640c740bb98831d02ed620c740dd94431d0375510c7409fd9721d027e65c87409f59721d02be64c8740af59321d036e52c8740db54b21d027f65887409f99621d027d6588740af99221d02bd6488740dd94621d037551887409fd9521d027d65487409f19521d02be6448740af59121d036e5248740db54921d03765148740dd54521d02fb6048740be18121d027f65087409f99421d027d6508740af99021d02bd6408740f948421d035f5394e40cfd92539027e6294e409f58a5
  | 31 => 0xc821bb58432087e5610c821b9584320867e64944219f592510867e63944219f58e510873e4394421cf10e510876f3294421db0ca510867d65d04219fd96410867d6590421cf952410873d5490421bb98a41086ed62904219fd95410867f65104219f994410867d65104219f194410873e5410421cf55041086ee6210421bb58841087b541104219f59731086f565cc421dd597310867565cc421ddd4f310877553cc421ed90f31087b443cc421f9d8b31086f562cc421f918b310877652cc421f9ccb31087e432cc4219fd96310867d658c421af99231086bd648c421d794e310875d538c421bb98a31086ed628c421bd9863108776518c4219fd9531086bf644c421af19131086ef624c421bb1893108776514c421bed8131086f8604c4219fd94310867e650c4219f594310867c650c421d794c310875d530c421bb98831086ed620c421bd5943108775650c4219d59431086f6630c421f598c3108777530c421f594c3108775530c421f554c31087b6430c421ed10c31087e6620c421bd58831087e5620c421b95883108776520c421f9cc831087e4320c421bb98f21086ec63c8421dbd4f210876d53c8421eb90f21087ac43c8421f9cc721087e431c8421bb58a210876e5288421bd98e21086f46388421ddd4e21087755388421ed90e21087b44388421bd58a21086e56288421dd94a21087e65288421f9cca21087e432884219fd9521086ef6548421dbd95210866f6548421bb98d21086ec6348421dbd4d210876d5348421eb90d21087ac4348421bbd85210876e5148421f9d0521087e64148421f950521087e44148421f9cc521087e63148421f94c521087e43148421bdd95210877765484219dd9521086f66348421bd18d21087775348421dd54d21087b64348421ed10d21086f76248421f9d8921087765248421f994921087e74248421f990921087e54248421f910921087e73248421f98c921087e53248421f90c921087e76548421b9d9521087676548421f9d9121087e66448421f959121087e46448421f9d5121087e65448421f955121087e45448421f9d8d21087e66348421b998d21087e56348421f918d21086e46348421f9d4d21087675348421f994d21087e55348421d954d21087e45348421f9d0d21087e64348421e990d21087e54348421f910d21087a44348421f9d8121087e66048421f958121087e46048421f948750087e52194021ded42500867e64940219f592500867e63940219f58e500873e4394021cf10e500876f3294021db0ca50087773194021dd0c6500876f2194021dd886500876d2194021dd48650087652194021f9485500867f64540219f191500867f63540219f18d500873e4354021cf10d50086be6414021af59050086de6314021b758c50087e52114021de54050086ee62d4f40bb58b53d02
  | 32 => 0x19f58c504873e4314121cf10c50486de63d5021b758f540867e63d5021d798f540865e63d50219f58f540875d63d50219758f540867e62d5021db98b540867e61d5021dd987540867e60d50219f583540867d6595021cfd52540867e63950219f58e540867e60950219f582540873f64550219fd8d540867c63550219fd81540867c6055021cf550540867e6415021cf990540867e63150219f58c540867e6215021db988540867e6115021dd984540867e60150219f58054086be64d4c21af593530867e64d4c21cf993530863e64d4c219f593530873d64d4c218f593530867e62d4c21db98b530867e61d4c21dd987530867e60d4c219f583530867d6594c21d7d4e530867e6494c219f592530867e6094c219f58253086bf6454c21af19153086fb6054c21be181530867f6454c21cfd91530863f6454c219f191530873c6454c218f191530875f6354c21db18953087746154c219fd81530877b6054c219ed81530867c6054c21de18153086786054c21d754c530867e6414c219f590530867e6314c21d798c530867e6214c21db988530866e6214c219f98453087766114c219d984530867e6014c219f580530867f65d0c219f997430867d65d0c219f197430875e53d0c21d754f43086ee62d0c21bb58b43086f661d0c21bd587430867f6590c219f996430867d6590c219f196430873f5490c21cf952430873d5490c21cf152430873f6590c21cf996430873d6590c21cf19643086be6390c21cfd4e430873e5390c21cf54e430873c5390c219fd95430867e6550c219f595430867c6550c21bbd8943086ec6250c21bdd8543086f46150c219fd94430867e6510c219f594430867c6510c21cfd50430873e5410c21cf550430873c5410c21d794c430875d5310c21cfd94430873e6510c21cf594430873c6510c21af98c430879e6310c21cfd4c430873e5310c21e794c430871e5310c21cf54c430879d5310c21c754c430873c5310c219f992520867d64948219f98e520867d6394821cf90e520873c43948219f597420867f65908219f596420873e5490821cf55242086f66190821bd586420867f65508219fd94420867d6510821cf950420873d5410821eb50842086f66110821bd584420867d65cc821bb597320876d65cc8219b597320876f53cc821db54f32087ae43cc821eb10f32087e761cc821bb58732087e461cc8219fd96320867d658c821af99232086bd648c821d794e320875d538c821bb98a320876e528c821bd98632086f5618c8219fd9532086bf644c821af191320876e524c821bdd8532086fb604c821be181320867f650c8219f594320875e530c821d754c32086f6610c821bd584320876d650c8219b59432086ee630c821f398c320876f530c821f394c320876d530c821f354c32087ae430c821eb10c32087e661
  | 33 => 0x95434867e6550d219f595434867c6550d219fd94434867e6510d219f594434867c6510d21cfd50434873e5410d21cf550434873c5410d21d7d4c434875c5310d21bb98843486ed6210d21bd98443486f56110d21cfd94434873e6510d21cf594434873c6510d21af98c434879e6310d21cfd4c434879f5310d21c7d4c434873e5310d21cf54c434873c5310d21e714c434871c5310d21eb98843487ad6210d21ed98443487b56110d219f997424873f54d0921cf15342486f661d0921bd587424867e65909219f195424873f5450921cf15142486f76150921bd185424867e65109219f997324875f53cc921d714f32486f661cc921bd587324867e658c921af99232486bd648c921bb996324876e658c9219b99632487ae648c921eb59232486ed638c921db94e324876c538c921eb90e32487ac438c921f9d8632486ee618c921f918632486ee608c9219f19532486bf644c921af191324875f534c921d714d32486f7614c921bd18532486fb604c921be181324876c654c9219b19532487af644c921eb19132487cf634c921f3d4d324876e534c921db14d32487cc534c921eb90d32487ac434c921f9d8532486ec614c921f918532486e4614c921fad8132486ec604c921fa18132486e8604c9219f99432486ee620c921bd984324867e65d0521cfd53414873c54d0521bb98b41486ed62d05219f996414867f65505219f595414867c6550521cfd51414873c5450521bbd8941486ec62505219f994414867e65cc521d7d4f314875c53cc521bb98b31486ed62cc5219f99631486be648c521af59231486f6658c521dd9963148676658c521ed99231487b5648c521bd58e3148776538c521dd14e31487b6438c521ed10e31487e7628c521bd98a31487e4628c521f98ca31487e5328c521bd982314867f654c5219f595314867c654c521afd9131486bc644c521d7d4d314875c534c521bbd8931486ec624c521bed8131486f8604c521bd1953148774654c5219d19531487b7644c521ed19131487d7634c521f5d4d3148776534c521dd14d31487d4534c521ed90d31487b4434c521f9d8931486f4624c521f918931486e4624c521f98c931487e5324c521fcd8131486f4604c521fc18131486f0604c5219f99431486ee620c521bb58831486f6610c521bdd8f21486f563c8521dd94f214877453c8521ed90f21487b443c8521f98cb21487e532c8521bd98321486ef6388521bb58e214876e5388521db14e21487ae4388521eb10e21487e75188521f98c621487e53188521bb982214867e64d41219f593504867e63d41219f58f504873e43d4121cf10f504877b5094121afd9150486bc6454121b7d8d50486dc6354121af99050486bd6414121de540504867e6414121cf990504863e64141219f590504873d64141218f590504867e631412
  | 34 => 0x8873d5410621bb98841886ed6210621af99231886bd648c621d794e318875d538c621bb98a31886ed628c621bd5963188775658c621ed99231887b5648c621dd94e31887d6538c621f554e3188774538c621ed90e31887b4438c621bd98a31887e6628c621f958a31887e7328c621f90ca31886f6608c621afd9131886bc644c621bbd8931886ec624c621bed8131886f8604c621bdd953188777654c621edd9131887b4644c621f5d8d3188776534c621dd14d31887b6434c621ed10d31887e7624c621bd18931887e4624c621b918931887e7324c621f90c931887f3604c621bd18131887f0604c621bc181318875e530c621d754c31886ee620c621bb58831886ed65c8621db59721886ee63c8621bb18f218876f53c8621db54f21887ae43c8621eb10f21886f565c8621dd59721886f763c8621bd58f218877653c8621dd14f21887b643c8621ed10f21886f660c8621ded42508867e64942219f592508867e63942219f58e508873e4394221cf10e508876f3294221db0ca508876f21942219fd91508867c64542219fd8d508867c6354221cf90d508873c4354221af99050886bd6414221de540508867e63d51219f58f544867e60d51219f583544873f54951219f992544867e63951219f58e544867d6295121db58a544867d6195121dd586544867e60951219f58254486df6355121b718d54486fb6055121be181544873f64551219fd8d544875f635512197d8d544867c6355121d718d544865c63551219fd89544876f62551219fd85544877761551219fd81544877b60551219ed81544867c6055121de181544867860551219f994544873d5415121cf990544867e63151219f58c544867e60151219f58054486be64d4d21af593534867e64d4d21cf993534863e64d4d219f593534873d64d4d218f593534867e60d4d219f583534875f5394d219f992534867d6494d219f98e534867d6294d21db58a534867d6194d21dd586534867e6094d219f58253486bf6454d21af19153486fb6054d21be181534867f6454d21cfd91534863f6454d219f191534873c6454d218f191534875f6354d219fd89534876f6254d219bd89534867f6154d21ddd8553486776154d219fd81534877b6054d219ed81534867c6054d21de18153486786054d219f994534875d5314d219f990534867d6414d21d798c534876d6214d21dd584534867e6014d219f580534867f65d0d219f997434867d65d0d219f197434875f53d0d21d714f434867f6590d219f996434867d6590d219f196434873f5490d21cf952434873d5490d21cf15243486ee6290d21bb58a43486f66190d21bd586434873f6590d21cf996434873d6590d21cf19643486be6390d21cfd4e434873e5390d21cf54e434873c5390d21eb98a43487ad6290d21ed98643487b56190d219fd
  | 35 => 0xe534c721d754d31c86ef624c721bb18931c86fb604c721be18131c86ee620c721bb58831c86f5650c721dd59431c87d6630c721ddd4c31c8775530c721ed90c31c87b4430c721f998831c86f5620c721f958831c86e5620c721f98c831c87e5320c721ded4250c867e64943219f59250c867e63943219f58e50c873e4394321cf10e50c87773194321dd0c650c867f64543219f19150c867f63543219f18d50c873e4354321cf10d50c86be6414321af59050c877950143219f98f548867d63d5221db58b548877661d52219f983548867d60d5221cfd52548867e63952219f58e548867e60952219f582548873f64552219fd8d548867c63552219fd81548867c6055221cf55054886fa6015221be580548873e64152219f98c548867d6315221db588548877661152219f980548877a60152219e980548867d6015221de58054886796015221af99353886bd64d4e21be98353886f960d4e219f993538873e64d4e218f993538867d64d4e21cf593538863d64d4e21db58b538877661d4e219f983538877a60d4e219e983538867d60d4e21de583538867960d4e21d7d4e538867e6494e219f59253887766194e219f982538867d6094e21afd9153886bc6454e219fd91538873f6454e218fd91538867c6454e21cf191538863c6454e21d7d8d538876f6254e219fd81538867c6054e21d754c538867e6414e219f590538875e6314e21db58853887766114e219f980538867d6014e219fd97438867e65d0e219f597438867c65d0e21bb98b43886ed62d0e219fd96438867e6590e219f596438867c6590e21cfd52438873e5490e21cf552438873c5490e21bd98643886f56190e21cfd96438873e6590e21cf596438873c6590e21cfd4e438873e5390e21cf54e438873c5390e21ed98643887b56190e219fd95438867e6550e219f595438867c6550e21bbd8943886ec6250e219fd94438867e6510e219f594438867c6510e21cfd50438873e5410e21cf550438873c5410e21bd98443886f56110e21cfd94438873e6510e21cf594438873c6510e21e798c438873f5310e21cf94c438873d5310e21cf14c43887b66110e21ed584438873e54d0a21cf55342886f661d0a21bd587428873e5450a21cf55142886f76150a21bd18542887ad4210a21d794f328875d53cca21bd98732886f561cca21db597328876f53cca21f394f328876d53cca21f354f32887ae43cca21eb10f32887e661cca21bb58732887e561cca21af99232886bd648ca21afd9132886bc644ca21d794d328875d534ca21bdd8532886f4614ca21bed8132886f8604ca21bd58432886ed650ca21db59432887ce630ca21dbd4c328876d530ca21eb90c32887ac430ca21f998432886ed610ca21f958432886e5610ca21cf952418873d5490621bb98a41886ed6290621cf95041
  | 36 => 0x4031bb988500c6ed6214031db948500c76d5214031de540500c67e63d53219f58f54c876e62d5321dd58754c867e60d53219f58354c873f54953219f98e54c867d63953219f98254c867d6095321cfd9154c867f63553219f18d54c867f60553219f18154c873d5415321be98054c86f96015321cf99054c867e63153219f58c54c876e6215321dd58454c867e6015321de98054c867a60153219f58054c877960153219e58054c86be64d4f21af59353c86fa60d4f21be58353c867e64d4f21cf99353c863e64d4f219f59353c873d64d4f218f59353c876e62d4f21dd58753c867e60d4f21de98353c867a60d4f219f58353c877960d4f219e58353c875f5394f219f99253c867d6494f21db98a53c867e6094f219f58253c86bf6454f21af19153c867f6454f21cfd9153c863f6454f219f19153c873c6454f218f19153c875f6354f21ddd8553c867f6054f219f18153c875d5314f219f99053c867d6414f21d798c53c876e6214f21dd58453c867e6014f219f58053c867f65d0f219f99743c867d65d0f219f19743c86f661d0f21bd58743c867f6590f219f99643c867d6590f219f19643c873f5490f21cf95243c873d5490f21cf15243c86ee6290f21bb58a43c873f6590f21cf99643c873d6590f21cf19643c873f5390f21cf94e43c873d5390f21cf14e43c87ae6290f21eb58a43c867f6550f219f99543c867d6550f219f19543c86f76150f21bd18543c867f6510f219f99443c867d6510f219f19443c873f5410f21cf95043c873d5410f21cf15043c86ee6210f21bb58843c873f6510f21cf99443c873d6510f21cf19443c879e6310f21cfd4c43c873e5310f21cf54c43c873c5310f21eb98843c87ad6210f21cf95242c873d5490b21bd98642c86f56190b21cf95042c873d5410b21bd98442c86f56110b21af99232c86bd648cb21d794e32c875d538cb21bd98632c86f5618cb21db59632c87ae648cb21eb59232c876e538cb21f394e32c87cd538cb21db14e32c87ae438cb21eb10e32c86ee618cb21f998632c87e5618cb21bb98232c86bf644cb21af19132c86f4614cb21bed8132c86f8604cb21bbd9532c876f654cb21ebd9132c87ac644cb21f3d8d32c876e534cb21db14d32c87ae434cb21eb10d32c87e7614cb21bb18532c87e4614cb21b918532c87eb604cb21bb18132c87e8604cb21ba18132c875e530cb21d754c32c86f6610cb21bd58432c873e54d0721cf55341c86ee62d0721bb58b41c873e5450721cf55141c86ef6250721bb18941c87b54110721d794f31c875d53cc721bb98b31c86ed62cc721bd59731c877565cc721ddd4f31c87d653cc721dd54f31c87d553cc721ed90f31c87b443cc721f998b31c86f562cc721f958b31c87e632cc721f94cb31c86be648c721af59231c86bf644c721af19131c875
  | 37 => 0xcf10d520c77461548319fd81520c67c6054831dbd95520c76f5454831db951520c76d5454831db151520c7ae4354831eb10d520c7e46154831dbd91520c76e6454831db591520c76c6454831db98d520c76f4354831db90d520c72e4354831db50d520c76c4354831cb10d520c76e6154831db185520c7646154831db0c5520c76f6054831db981520c76d6054831db181520c6ee6214831db548520c67f65d08319f997420c67d65d0831db94b420c76d52d0831bd987420c6f561d08319fd96420c67e65908319f596420c76e5290831db54a420c67f65508319f595420c67c6550831b7d8d420c6dc6350831db949420c76d5250831bdd85420c6f461508319fd94420c67e65108319f594420c76e5210831db548420c76e52cc831db54b320c6f661cc831bd587320c67d658c831af992320c6bd648c831e710e320c76d528c8319fd95320c6bf644c831af191320c76e524c831bdd85320c6fb604c831be181320c79c430c831db948320c76d520c831bd984320c6f5610c8319f992510c73e64944318f992510c67d6494431cf592510c63d6494431cf90e510c73c43944319f597410c73f54d0431cf153410c76e52d0431db54b410c67f65904319f596410c73e5490431cf552410c6de6390431b758e410c76e5290431db54a410c67f6550431cfd51410c73c5450431db949410c76d52504319fd94410c67e65104319f594410c67c6510431cf950410c73d5410431b798c410c6dd6310431db948410c76d5210431e790f310c79c43cc431db94b310c76d52cc431f394b310c7cd52cc431af992310c6bd648c431b758e310c75e538c431db94a310c76d528c431ed992310c7b5648c431bd58e310c776538c431f594e310c7b6438c431ed10e310c6f6628c431f994a310c775528c431f954a310c765528c431bd982310c67f654c431afd91310c6bc644c431e790d310c79c434c431bbd89310c6ec624c431db949310c76d524c431bed81310c6f8604c431b7d95310c75f654c43197d95310c79f644c431e7191310c7cf624c431f3189310c7ce524c431f3549310c6df614c431d7945310c7d7414c431f5105310c7db604c431f6181310c6f7654c431ddd95310c677654c431edd91310c7b4644c431bdd8d310c7d7634c431dd94d310c7d6534c431f5d0d310c7b6434c431ed10d310c7d4434c431e510d310c7e7624c431bd189310c7e4624c431b9189310c7e6524c431dd549310c7e5524c431d9549310c7f3604c431bd181310c7f0604c431bc181310c6ee62d4031bb58b500c76e52d4031db54b500c76e5294031db54a500c77b50940319f992500c67d6494031cf90e500c73c43940319f98a500c67d6294031db949500c76d52540319fd91500c67c6454031cf90d500c73c43540319fd89500c67c6254031af990500c6bd641
  | 38 => 0xb504c77962d4131de18b504c77b42d4131de90b504c77942d4131de10b504c77b32d4131de8cb504c77932d4131de0cb504c77b61d4131ded07504c77a41d4131de507504c77841d4131decc7504c77a31d4131af992504c6bd6494131cfd52504c73c5494131bb98a504c6ed6294131dbd4a504c76c5294131ded42504c6bf6454131af191504c73f5454131cf151504c6ef6254131bb189504c76f5254131db149504c73f5414131cf150504c76f5214131db148504c77950141319f990504c67d6414131cf90c504c73c43141319f988504c67d6214131ddcc4504c6fa6514131de994504c77b5414131eed50504c73b5414131de950504c7795414131de150504c7b85414131ce150504c7ba4314131ee10c504c77b5214131fad48504c76b5214131de948504c7795214131de148504c7e85214131da148504c7f33114131f68c4504c77b6414131de990504c7796414131de190504c77b6314131ded0c504c77a4314131ce90c504c7794314131de10c504c7384314131ded88504c77a6214131de588504c7786214131ded08504c77a4214131de508504c7784214131decc8504c77a3214131de4c8504c7783214131ded84504c77b4114131de904504c7794114131de104504c77b3114131dccc4504c77a3114131de4c4504c6ee62d5031bb58b540c67e63d5031d798f540c67e62d5031db98b540c66e62d50319f58b540c76d62d50319b58b540c67e61d5031dd987540c67e60d50319f583540c67d6595031cfd52540c67e62950319f58a540c67e60950319f582540c73f64550319fd89540c67c62550319fd81540c67c6055031cf550540c6ee6215031bb588540c6fa6015031be580540c67e6415031cf990540c67e6315031d798c540c67e6215031db988540c66e62150319f588540c76d62150319b588540c67e6115031dd984540c67e6015031de980540c67a60150319f580540c77960150319e580540c67e6494c319f592530c67d65d0c319fd96430c67d6590c31cf952430c73d5490c31bd986430c6f56190c31cfd96430c73e6590c31cf596430c73c6590c31af98e430c73e5390c31ed986430c7b56190c319fd95430c67f6510c319f594430c73e5410c31cf550430c6f66110c31bd584430c73f6510c31cf994430c73d6510c31cf194430c6be6310c31e798c430c73e5310c31ed984430c7b56110c31dbd4a520c67e64948319f592520c73e4394831cf10e520c67e60948319f582520c76f5494831db952520c76d5494831db152520c7ae4394831eb10e520c7e46194831dbd92520c76e6494831db592520c76c6494831db18e520c76f4394831db90e520c72e4394831db50e520c76c4394831cb10e520c76e6194831db186520c76f6094831db982520c76d6094831db182520c67f64548319f191520c73e4354831
  | 39 => 0xc76c60d4931af992524c6bd6494931cfd52524c73c5494931dbd4a524c6fa6094931be582524c6bf6454931af191524c73f5454931cf151524c6fb6054931be181524c73f5414931cf150524c76d52149319f990524c67d6414931cf90c524c73c4314931dd584524c67e60149319f580524c6ee6514931db994524c76f5414931ebd50524c72f5414931db950524c76d5414931db150524c7ac5414931cb150524c7ae4314931eb10c524c7e56114931dbd90524c76e6414931db590524c76c6414931dbd8c524c76f4314931db90c524c72e4314931db50c524c76c4314931cb10c524c76f6114931db584524c7656114931db4c4524c76f6014931db980524c76d6014931db180524c67e65d09319f597424c67c65d0931cfd53424c73c54d0931dbd4b424c76c52d09319f996424c67d65909319f196424c73f5490931cf152424c6de6390931b758e424c76f5290931db14a424c6f66190931bd586424c67f65509319f995424c67c6550931cfd51424c73c5450931dbd49424c76c52509319f994424c67d65109319f194424c73f5410931cf150424c76f5210931db148424c6f66110931bd584424c67e65cc931cfd53324c73c54cc931e710f324c76c52cc931af992324c6bd648c931cfd52324c73c548c931dbd4a324c76c528c931bd986324c6f5618c931afd91324c6bc644c931cfd51324c73c544c931e710d324c76f524c931db149324c6f7614c931bd185324c6fb604c931be181324c67e650c931cfd50324c73c540c931dbd48324c6f6610c9319f997414c73f54d0531cf153414c6de63d0531b758f414c76f52d0531db14b414c67e6590531cfd52414c73c5490531dbd4a414c76c52905319fd95414c67d65505319f195414c73f5450531cf151414c6df6350531b718d414c76f5250531db149414c67e6510531cfd50414c73c5410531dbd48414c76c5210531cfd53314c73c54cc531dbd4b314c76c52cc531edd53314c7b454cc531ed90f314c7b443cc531bd58b314c7e752cc531dd14b314c7e452cc531d914b314c6be648c531af592314c73f548c531cf152314c79e438c531e710e314c76f528c531db14a314c79e648c531e7592314c79f548c531e7152314c7cf528c531f314a314c7d7518c531cfd53504c73c54d4131dbd4b504c76c52d41319f993504c67d64d4131cf90f504c73c43d41319f98b504c67d62d4131ded53504c7bb54d4131ced53504c77a54d4131de553504c77854d4131ee153504c73854d4131ee90f504c7b843d4131ded4b504c7eb52d4131dad4b504c77a52d4131de54b504c77852d4131fa14b504c76852d4131fccc7504c7da31d4131ded93504c77a64d4131de593504c77864d4131ded8f504c77b43d4131de90f504c73a43d4131de50f504c77843d4131ce10f504c77b62d4131de98
  | 40 => 0x544ca31cf551328c76e524ca31db549328c6f7614ca31bd185328c6fb604ca31be181328c73e540ca31cf550328c79c430ca31bd584328c73e54d0631cf553418c73e5490631cf552418c6de6390631b758e418c73e5450631cf551418c73e5410631cf550418c6de6310631b758c418c73e54cc631cf553318c79e43cc631e710f318c6dd65cc631d7597318c79e54cc631e7553318c6f565cc631dd597318c7b654cc631ed553318c7b643cc631ed10f318c6f562cc631dd94b318c6be64d4231af593508c73e54d4231cf553508c6ee62d4231bb58b508c73e5494231cf552508c77b50942319f992508c67d6494231cf90e508c73c43942319f98a508c67d6294231ddcc6508c73e5454231cf551508c67f64542319f191508c73e4354231cf10d508c67f62542319f189508c6be6414231af590508c73e5414231cf550508c77950142319f98b544c67d62d51319f983544c67d60d5131cfd8f544c73d63d5131cfd8b544c73e62d5131cf58b544c73c62d5131cfd87544c73d61d5131cfd83544c73e60d5131cf583544c73c60d5131cfd52544c6ee6295131bb58a544c6fa6095131be582544c67e64951318f992544c67d6395131d758e544c67e6295131db98a544c66e62951319f58a544c76d62951319b58a544c67d6195131dd586544c67e6095131de982544c67a60951319f582544c77960951319e582544c6ef6255131bb189544c6fb6055131be181544c73f64551319fd8d544c75f63551319fd89544c76f62551319bd89544c67c6255131db189544c66c62551319fd85544c77761551319fd81544c77b60551319ed81544c67c6055131de181544c67860551319f994544c73d5415131cf990544c67e62151319f588544c67e60151319f580544c6be6515131cf994544c63e6515131cfd8c544c73d6315131cfd88544c73e6215131cf588544c73c6215131cfd84544c73d6115131cf4c4544c73f6015131cf980544c73d6015131cf180544c67e65d0d31cfd53434c73c54d0d31bd987434c6f561d0d319f996434c73f5490d31cf952434c73d5490d31cf152434c6be6590d31cf996434c63e6590d31af98e434c67c6550d31cfd51434c73c5450d31bdd85434c6f46150d319f994434c73f5410d31cf950434c73d5410d31cf150434c6be6510d31cf994434c63e6510d31af98c434c79e6310d31cfd53524c73c54d49319f993524c67d64d4931cf90f524c73c43d49319f983524c67d60d4931dbd53524c7af54d4931cbd53524c76e54d4931db553524c76c54d4931eb153524c72c54d4931eb90f524c7ac43d4931f9d87524c76f64d4931db993524c76d64d4931db193524c76f63d4931dbd0f524c76e43d4931cb90f524c76d43d4931db10f524c72c43d4931dbd87524c76d61d4931dbd83524c76e60d4931db583524
  | 41 => 0xb31ddd8552cc67f6054b319f18152cc76d5214b319fd9742cc67e65d0b319f59742cc6f661d0b31bd58742cc67f6590b319f99642cc67d6590b31b798e42cc6dd6390b319fd9542cc67d6550b319f19542cc6f76150b31bd18542cc67f6510b319f99442cc67d6510b31e710f32cc76e52ccb31db54b32cc6f661ccb31bd58732cc6be648cb31af59232cc6bf644cb31af19132cc79c434cb31bd18532cc6fb604cb31be18132cc76e520cb31db54832cc6f6610cb31bd58432cc73e54d0731cf55341cc6de63d0731b758f41cc73f5490731cf15241cc73e5450731cf55141cc6df6350731b718d41cc73f5410731cf15041cc6be6494331af59250cc77b50943319f99250cc73e64943318f99250cc67d6494331cf59250cc63d6494331cf90e50cc73c43943319f98a50cc67d6294331bbd8950cc6ec62543319fd9150cc67c6454331cf90d50cc73c43543319fd8950cc76f62543319bd8950cc67c6254331db18950cc66c6254331de54050cc75d63d52319f98b548c67d62d5231dd987548c67e60d52319f583548c73f54952319f98a548c67d62952319f982548c67d6095231cfd8e548c73d6395231cfd8a548c73e6295231cf58a548c73c6295231cf986548c73c6195231cfd82548c73e6095231cf582548c73c6095231cfd91548c67f62552319f189548c67f60552319f181548c73f6555231cfd8d548c73d6355231cfd89548c73e6255231cf589548c73c6255231cf985548c73c6155231cfd81548c73e6055231cf581548c73c6055231cf550548c73e6415231d758c548c67e62152319f588548c77661152319f980548c67d6015231cf953438c73d54d0e31bd987438c6f561d0e31cfd52438c73e5490e31cf552438c73c5490e31af596438c73d6590e31cf951438c73d5450e31bdd85438c6f46150e31cfd50438c73e5410e31cf550438c73c5410e31af594438c73d6510e31e798c438c6be64d4a31af593528c73e54d4a31cf553528c6fa60d4a31be583528c73e5494a31cf552528c76f5294a319f992528c67d6494a31cf90e528c73c4394a31dd986528c67e6094a319f582528c73e5454a31cf551528c67f6454a319f191528c73e4354a31cf10d528c67f6054a319f181528c6be6414a31af590528c73e5414a31cf550528c76d5214a319fd97428c67e65d0a319f597428c73e54d0a31cf553428c67f6590a319f996428c67d6590a31cf952428c73d5490a31bd986428c6f56190a319fd95428c67d6550a319f195428c73e5450a31cf551428c6df6350a31b718d428c67f6510a319f994428c67d6510a31cf950428c73d5410a31bd984428c6f56110a31cf953328c73d54cca31af992328c6bd648ca31cf952328c73d548ca31e710e328c76e528ca31db54a328c6f6618ca31bd586328c6bf644ca31af191328c73e
  | 42 => 0xdd4641506bd60905419f98f505067d63d4141cf90f505073c43d41419f98b505067d62d4141ded4250506df6354141b718d50506ef6254141bb189505077950141419f98c505067d6314141cf90c505073c43141419f988505067d6214141ddd04505075f5394c41cf192531067e6294c419f58a531067e6094c419f582531067f6254c419f189531067f6054c419f181531075d5314c41bb98853106ed6214c41be98053106f96014c41d794f431075d53d0c41bd98743106f561d0c419f596431073e5490c41af596431073d6590c41af98e431073d5390c41af586431067f6550c41cf950431075e5310c41d754c43106f66110c41bd58443106be6310c41e798c431073e5310c41e794c431071e5310c41cf54c431079d5310c41ed98443106bd6110c41ed58443106fa60d4841be583521076f52948419f98e521067d6394841cf90e521073c43948419f982521067d60948419fd8d521067c6354841cf90d521073c43548419fd81521067c6054841db548521076e52d0841db54b42106f661d0841bd587421067d65908419fd95421076e5210841db54842107ad4210841bd98442106f561108419fd97321067e65cc8419f597321067f658c8419f996321067d658c841af99232106bd648c841db94a321076d528c8419fd95321067d654c8419f19532106bf644c841af191321076e524c841db54932106f7614c841bd18532106fb604c841be181321067f650c8419f994321067d650c841bd98432106f5610c841cf90e511073c4394441af98f411073e53d0441af592411073e5490441bd59241107765490441ed95241107b64390441ed10e41106f660904419fd9541106bf6550441cfd95411063f6550441af18d411073e5350441afd85411073e5150441bdd95411077765504419dd9541106f76450441edd9141107765450441ed95141107b64250441ed10941106f46050441bb98b50106ed62d4041ded42501067e63940419f58e501073e4394041cf10e501067e62940419f58a501067f63540419f18d501073e4354041cf10d501067f62540419f189501073f4154041cf50550107795014041d798f54cc67e62d53319f58b54cc77561d53319f98354cc67d60d5331cfd5254cc67e62953319f58a54cc67e60953319f58254cc73f64553319fd8954cc67c62553319fd8154cc67c6055331cf55054cc73e6415331d798c54cc67e62153319f58854cc77561153319f98054cc67d6015331cf95243cc73d5490f31bd98643cc6f56190f31cf99643cc73d6590f31ed98643cc7b56190f31cf95043cc73d5410f31bd98443cc6f56110f31cf99443cc73d6510f31e798c43cc7b66110f31ed58443cc76f5294b319f99252cc67d6494b31cf90e52cc73c4394b319f98252cc67d6094b319fd9152cc67c6454b31cf90d52cc73c4354
  | 43 => 0x539067e6094e419f582539067f6254e419f189539067f6054e419f181539075d5314e41bb98853906ed6214e41d794e439075d5390e41bd98643906f56190e41cf94e439079e5390e41c794e439073d5390e41e754e43907b66190e41af58643907b56190e41d794d439075d5350e41bdd8543906f46150e41af594439073d6510e41e798c439073d5310e41af584439076f5294a419f98e529067d6394a41cf90e529073c4394a419f982529067d6094a419fd8d529067c6354a41cf90d529073c4354a419fd81529067c6054a41b798c52906dd6314a41db548529076e5290a41db54a42906f66190a41bd586429076e5250a41db54942906f76150a41bd18542907ad4210a419fd97329067e65cca419f597329075e53cca41d754f329067f658ca419f996329067d658ca41af99232906bd648ca41db94a329076d528ca419fd95329067d654ca419f19532906bf644ca41af191329075e534ca41d754d329076e524ca41db54932906f7614ca41bd18532906fb604ca41be181329067f650ca419f994329067d650ca41bd98432906f5610ca41af597419073d65d0641af98f419073e53d0641bd597419077565d0641b798f50906dd63d4241bb98b50906ed62d4241ded42509067e63942419f58e509073e4394241cf10e509067e62942419f58a509077741942419fd8d509067c6354241cf90d509073c43542419fd89509067c6254241cfd05509077950142419f98b535067d62d4d419f983535067d60d4d41d7d4e53506ef6254d41bb18953506fb6054d41be181535075d5314d41cfd90535067e6214d419f588535067e6014d419f580535067e65d0d41d7d4e435075c5390d41bd98643506f56190d41af98e435073f5390d41e7d4e435073c5390d41e714e435071c5390d41af98643507b66190d41ed58643506bd6090d41d7d4d435075c5350d41bdd8543506f46150d419f99443506be6510d41cf99443506be6310d41e798c435073f5310d41af98443506bd6010d419f98f525067d63d4941cf90f525073c43d49419f983525067d60d4941dbd4a52506df6354941b718d52506fb6054941be181525076d52149419f98c525067d6314941cf90c525073c43149419f980525067d60149419f997425076f5290941db14a42506f66190941bd586425076f5250941db14942506f76150941bd185425067e65109419f997325067d65cc9419f197325076f52cc941db14b325067e658c9419f596325067c658c941af99232506bd648c941d7d4e325075c538c9419fd95325067e654c9419f19532506bf644c941af19132506f7614c941bd18532506fb604c941be181325067e650c9419f594325067c650c941d7d4c325075c530c941dbd48325076c520c941bd98432506f5610c941ed90f41507b443d0541af98e415073c5390541e
  | 44 => 0xbe63294432f54ca510cbe53294432ddd92510cb766494432dd592510cb746494432dd18e510cb774394432dd90e510cb364394432dd50e510cb744394432cd10e510cb746294432ddd0a510cb764294432dd50a510cb744294432ddcca510cb763294432dd4ca510cb776094432dd982510cb756094432dd182510ca7f64544329f191510cb3e4354432cf10d510cb6e3254432db4c9510ca7f60544329f181510cb776554432ddd51510cb765454432dd551510cb745454432ed90d510cbb44354432f9189510cbd73254432f98c9510cbd53254432f94c9510cb776454432dd991510cb756454432dd191510cb766354432ddd0d510cb764354432cd90d510cb754354432dd10d510cb344354432dd989510cb774254432dd909510cb754254432dd109510cb773254432dd8c9510cb663254432dd4c9510cb653254432dd0c9510cb776054432dd981510cb756054432dd181510caf66114432dd544510caf661d4032bd587500cb7651d4032dd547500cb765194032dd546500cb7b50940329f992500ca7d6494032cf90e500cb3c43940329f986500ca7d6194032dd945500cb7551540329fd91500ca7c6454032cf90d500cb3c43540329fd85500ca7c6154032af990500cabd6414032bd984500caf56114032dd944500cb755114032de540500caee62d4f41bb58b53d06fa60d4f41be58353d075f5394f41cf19253d067e6294f419f58a53d067e6094f419f58253d067f6254f419f18953d067f6054f419f18153d075d5314f41d794f43d075d53d0f41bd98743d06f561d0f41af59643d073d6590f41cf54e43d06be6190f41af58243d075e5310f41d754c43d06f66110f41bd58443d079e6310f41cf94c43d079e5310f41c794c43d073d5310f41e754c43d06be6110f41ed98443d07b56110f41af58043d076f5294b419f98e52d067d6394b41cf90e52d073c4394b419f98252d067d6094b419fd8d52d067c6354b41cf90d52d073c4354b419fd8152d067c6054b41db54852d06fa6014b41be58052d076e52d0b41db54b42d06f661d0b41bd58742d076e5210b41db54842d06f66110b41bd58442d067f65ccb419f99732d067d65ccb41db94b32d076d52ccb419fd9632d067e658cb419f59632d06be648cb41af59232d067f654cb419f59532d067c654cb41afd9132d06bc644cb41bdd8532d06f4614cb41bed8132d06f8604cb419fd9432d067e650cb419f59432d076e520cb41db54832d06f6610cb41bd58432d077b50943419f98e50d067d6394341cf90e50d073c43943419f98a50d067d6294341bbd8950d06ec62543419fd8d50d067c6354341cf90d50d073c43543419fd8950d076f62543419bd8950d067c6254341db18950d066c6254341bb98850d06ed6214341de54050d075f5394e41cfd92539067e6294e419f58a
  | 45 => 0x214132ded44504cbf35114132dcd44504cb7a5114132de544504cb785114132fc144504cb705114132ded90504cb7a6414132de590504cb786414132ded8c504cb7b4314132de90c504cb3a4314132de50c504cb784314132ce10c504cb7b6214132ded08504cb7a4214132de508504cb784214132decc8504cb6b3214132de8c8504cb793214132ded84504cb7a6114132de584504cb786114132bd987540caf561d50329f98f540cb5e63d50329f98b540cb6e62d50329f987540cb7661d50329d987540ca7d61d5032dd587540ca7561d50329f983540ca7d60d50329f596540cb3f54950329f986540ca7d61950329f982540ca7d6095032cfd91540ca7f61550329f185540ca7f60550329f181540cb3d5415032bd984540caf56115032be980540caf960150329f990540cb3e64150329f98c540cb5e63150329f988540cb6e62150329f984540cb7661150329d984540ca7d6115032dd584540ca7561150329f980540cb7a60150329e980540ca7d6015032de580540ca7960150329f992530ca7d6494c329f597430ca7f6590c329f596430cb3e5490c32cf552430caee6290c32bb58a430cb3f6590c32cf996430cb3d6590c32cf196430cabe6390c32cf94e430cbae6290c32eb58a430ca7f6550c329fd94430ca7d6510c32cf950430cb3d5410c32bb988430caed6210c32cfd94430cb3e6510c32cf594430cb3c6510c32af98c430cb9e6310c32cf94c430cbae6210c32eb588430ca7e6494832cf992520ca3e64948329f592520cb3d64948328f592520cb3e4394832cf10e520ca7d65d0832cfd53420cb3c54d08329fd96420ca7d6590832cf952420cb3d5490832b798e420cadd63908329fd95420cb3f5450832cf151420ca7f65108329f994420ca7d65108329f194420cb3e5410832cf550420cade6310832b758c420cb9e43cc832e710f320cabe648c832af592320cadd638c832d794e320cbae648c832eb592320caed638c832db94e320cbce538c832eb90e320cbac438c832bb986320caee608c8329fd95320cabf644c832af191320cb9e434c832e710d320caf7614c832bd185320cafb604c832be181320cadf654c832d7d95320ca5f654c832e7d91320cb9c644c832b7d89320cb5e524c832f3d09320cbcc424c832f5d85320cbd4614c832f6d81320cbd8604c832bbd95320cb6f654c8329bd95320cbaf644c832eb191320caef634c832f3d8d320cb6e534c832f394d320cbcf434c832eb90d320cbac434c832f310d320cb8c434c832f9d85320caec614c832f9185320cae4614c832fad81320caec604c832fa181320cae8604c832ddd46510ca7e64944329f592510cb3e4394432cf10e510ca7e60944329f582510cb775494432dd952510cb755494432dd152510cbb64394432ed10e510cbe46294432f5cca510c
  | 46 => 0x32ebd53324cbac54cc932eb90f324cbac43cc932bb587324cabe648c932af592324cb3f548c932cf152324cb9e438c932e710e324cb9e648c932e7592324cb9f548c932e7152324cbcf528c932cfd53514cb3c54d45329f993514ca7d64d4532cf90f514cb3c43d45329f983514ca7d60d4532ddd53514cbb754d4532cdd53514cb7654d4532dd553514cb7454d4532ed153514cb3454d4532ed90f514cbb443d4532f9d8b514cbe732d4532f58cb514cb7764d4532dd993514cb7564d4532dd193514cb7763d4532ddd0f514cb7643d4532cd90f514cb7543d4532dd10f514cb3443d4532ddd8b514cb7742d4532dd90b514cb7542d4532dd10b514cb7732d4532dd8cb514cb7760d4532dd983514cb7560d4532dd183514cabe6494532af592514cb3f5494532cf152514cb775194532be982514caf96094532afd91514cabc6454532cfd51514cb3c5454532bed81514caf86054532cfd50514cb3c5414532dd544514ca7e64145329f590514cb3e4314532cf10c514cb6f32145329f980514ca7d6014532bd994514cb766514532ddd50514cbb75414532cdd50514cb765414532dd550514cb745414532ed150514cb345414532ed90c514cbb44314532f9588514cbe73214532f58c8514cb776414532dd990514cb756414532dd190514cb776314532ddd0c514cb764314532cd90c514cb754314532dd10c514cb344314532ddd88514cb774214532dd908514cb754214532dd108514cb773214532d9cc8514cb763214532dd4c8514cb776014532dd980514cb756014532dd180514cb3f54d4132cf153504cb7751d4132dd147504ca7e64d41329f593504cb3e43d4132cf10f504ca7e61d41329f587504cb7b54d4132eed53504cb3b54d4132de953504cb7954d4132de153504cbb854d4132ce153504cbba43d4132ee10f504cbeb32d4132f68cb504cb7b51d4132fcd47504cb7351d4132de947504cb7951d4132de147504cbf051d4132dc147504cb7b64d4132de993504cb7964d4132de193504cb7b63d4132ded0f504cb7a43d4132ce90f504cb7943d4132de10f504cb3843d4132ded8b504cb7b42d4132de90b504cb7942d4132de10b504cb7b32d4132de8cb504cb7b61d4132de987504cb7961d4132de187504cabe6494132af592504cb3f5494132cf152504caf66194132bd586504cb775194132dd146504cb7b5094132afd91504cabc6454132cfd51504cb3c5454132bdd85504caf46154132ddd45504cb745154132cfd50504cb3c5414132ddd44504cb745114132de540504ca7e64141329f590504cb3e4314132cf10c504cb6f32141329f984504ca7d6114132be994504cb7a6514132ded50504cbbb5414132ced50504cb7a5414132de550504cb785414132ee150504cb385414132ee90c504cbb84314132facc8504cbda3
  | 47 => 0x553428cb3e5490a32cf552428cade6390a32b758e428cb3e5450a32cf551428cb3e5410a32cf550428cade6310a32b758c428cb3e54cca32cf553328cb9e43cca32e710f328cadd65cca32d7597328cb9e54cca32e7553328caed65cca32db597328cbae54cca32eb553328cbae43cca32eb10f328caed61cca32af993518cabd64d4632cf953518cb3d54d4632be983518caf960d4632cf952518cb3d5494632ddd46518ca7e64946329f592518cb3e4394632cf10e518cb6f32946329f982518ca7d6094632cf951518cb3d54546329fd91518ca7c6454632cf90d518cb3c43546329fd81518ca7c6054632af990518cabd6414632cf950518cb3d5414632dd544518cabe64d4232af593508cb3e54d4232cf553508caf661d4232bd587508cb3e5494232cf552508cb7b50942329f992508ca7d6494232cf90e508cb3c4394232dbcca508ca7e61942329f586508cb3e5454232cf551508ca7f64542329f191508cb3e4354232cf10d508ca7f61542329f185508cabe6414232af590508cb3e5414232cf550508cb7950142329f987544ca7d61d51329f983544ca7d60d5132cfd8f544cb3d63d5132cfd8b544cb3d62d5132cfd87544cb3e61d5132cf587544cb3c61d5132cfd83544cb3e60d5132cf583544cb3c60d5132cfd52544caf66195132bd586544cafa6095132be582544ca7e64951328f992544ca7d6395132d758e544ca7d6295132db58a544ca7e6195132dd986544ca7661951329f586544cb7561951329d586544ca7e6095132de982544ca7a60951329f582544cb7960951329e582544caf76155132bd185544cafb6055132be181544cb3f64551329fd8d544cb5f63551329fd89544cb6f62551329fd85544cb7761551329dd85544ca7c6155132dd185544ca7461551329fd81544cb7b60551329ed81544ca7c6055132de181544ca7860551329f994544cb3d5415132cf990544ca7e61151329f584544ca7e60151329f580544cabe6515132cf994544ca3e6515132cfd8c544cb3d6315132cfd88544cb3d6215132cf4c8544cb3f6115132cf984544cb3d6115132cf184544cb3f6015132cf980544cb3d6015132cf180544ca7e65d0d32cfd53434cb3c54d0d32bb98b434caed62d0d329f996434cb3f5490d32cf952434cb3d5490d32cf152434cabe6590d32cf996434ca3e6590d32af98e434ca7c6550d32cfd51434cb3c5450d32bbd89434caec6250d329f994434cb3f5410d32cf950434cb3d5410d32cf150434cabe6510d32cf994434ca3e6510d32af98c434cb9e6310d329f997424cb3f54d0932cf153424cade63d0932b758f424ca7e6590932cfd52424cb3c54909329fd95424ca7d65509329f195424cb3f5450932cf151424cadf6350932b718d424ca7e6510932cfd50424cb3c5410932cfd53324cb3c54cc9
  | 48 => 0x210aee60908429fd954210abf6550842cfd954210a3f6550842af18d4210b3e5350842afd894210b3e5250842bbd954210b6f65508429bd954210aef6450842ebd914210b6e5450842eb9514210aec6050842be9835110af960d4442ddd465110a7e63944429f58e5110b3e4394442cf10e5110a7e60944429f5825110a7f63544429f18d5110b3e4354442cf10d5110a7f60544429f1815110b755114442bd9875010af561d4042ded425010a7e63940429f58e5010b3e4394042cf10e5010a7e61940429f5865010a7f63540429f18d5010b3e4354042cf10d5010b3f4254042cf5095010a7f61540429f1855010b795014042d798f54ccb6d62d53329f98754cca7d61d53329f98354cca7d60d5332cfd5254cca7e61953329f58654cca7e60953329f58254ccb3f64553329fd8554cca7c61553329fd8154cca7c6055332cf55054ccb3e6415332d798c54ccb6d62153329f98454cca7d61153329f98054cca7d6015332cf95243ccb3d5490f32bb98a43ccaed6290f32cf99643ccb3d6590f32eb98a43ccbad6290f32cf95043ccb3d5410f32bb98843ccaed6210f32cf99443ccb3d6510f32e798c43ccbae6210f32eb58843ccb3e54d0b32cf55342ccade63d0b32b758f42ccb3f5490b32cf15242ccb3e5450b32cf55142ccadf6350b32b718d42ccb3f5410b32cf15042ccb7751947329f99251cca7d6494732cf90e51ccb3c43947329f98251cca7d60947329fd9151cca7c6454732cf90d51ccb3c43547329fd8151cca7c6054732dd54451ccabe6494332af59250ccb7b50943329f99250ccb3e64943328f99250cca7d6494332cf59250cca3d6494332cf90e50ccb3c43943329f98650cca7d6194332bdd8550ccaf461543329fd9150cca7c6454332cf90d50ccb3c43543329fd8550ccb7761543329dd8550cca7c6154332dd18550cca746154332de54050ccb5d63d5232db98b548ca7e61d52329f587548ca7e60d52329f583548cb3f54952329f986548ca7d61952329f982548ca7d6095232cfd8e548cb3d6395232cf98a548cb3c6295232cfd86548cb3e6195232cf586548cb3c6195232cfd82548cb3e6095232cf582548cb3c6095232cfd91548ca7f61552329f185548ca7f60552329f181548cb3f6555232cfd8d548cb3d6355232cf989548cb3c6255232cfd85548cb3e6155232cf585548cb3c6155232cfd81548cb3e6055232cf581548cb3c6055232cf550548cb3e6415232d758c548cb6e62152329f984548ca7d61152329f980548ca7d6015232cf953438cb3d54d0e32bb98b438caed62d0e32cfd52438cb3e5490e32cf552438cb3c5490e32af596438cb3d6590e32cf951438cb3d5450e32bbd89438caec6250e32cfd50438cb3e5410e32cf550438cb3c5410e32af594438cb3d6510e32e798c438cb3e54d0a32cf
  | 49 => 0xf56114342de54050d0b5f5394e42cfd925390a7e6194e429f5865390a7e6094e429f5825390a7f6154e429f1855390a7f6054e429f1815390b5d5314e42bd9845390af56114e42d794e4390b5d5390e42bb98a4390aed6290e42cf94e4390b9e5390e42c794e4390b3d5390e42e754e4390bae6290e42af58a4390bad6290e42d794d4390b5d5350e42bbd894390aec6250e42af5944390b3d6510e42e798c4390b3d5310e42af5884390abd65d0a42cf5974290abe63d0a42cf94f4290aed65d0a42db5974290b7751946429f98e5190a7d6394642cf90e5190b3c43946429f9825190a7d60946429fd8d5190a7c6354642cf90d5190b3c43546429fd815190a7c6054642b798c5190add6314642dd5445190ade63d4242b758f5090af661d4242bd5875090b7b50942429f98e5090a7d6394242cf90e5090b3c4394242dbd0a5090a7e61942429f5865090a7f63542429f18d5090b3e4354242cf10d5090b3f42542429fd855090a7c6154242de5405090a7e61d4d429f5875350a7e60d4d429f5835350b5f5394d42bdd855350af46154d42bed815350af86054d42d754c5350b3f6414d429f9845350a7d6114d429f9805350a7d6014d429f9974350b5f5390d42d714e4350aee6290d42bb58a4350abe6390d42cfd4e4350b9f5390d42cf14e4350b9c5390d42c714e4350abe6290d42eb98a4350bad6290d42af5824350b5f5350d42d714d4350aef6250d42bb1894350a7e6510d42af9944350b3e6510d42af98c4350b9e6310d42cfd4c4350abe6210d42af5804350bae43d0942eb10f4250abe6390942cf14e4250baf5290942af5824250a7e63d45429f58f5150b3e43d4542cf10f5150a7e60d45429f5835150b775194542b7d8d5150adc6354542bed815150af86054542dd5445150a7e63145429f58c5150b3e4314542cf10c5150a7e60145429f5805150a7e63d41429f58f5050b3e43d4142cf10f5050a7e61d41429f5875050b7b5094142b7d8d5050adc6354142bdd855050af46154142de5405050a7e63141429f58c5050b3e4314142cf10c5050b6f42141429f9845050a7d6114142d7d4e5310b3c6494c429f9865310a7d6194c429f9825310a7d6094c429fd855310a7c6154c429fd815310a7c6054c42d754c5310af66114c42bd5845310afa6014c42be5805310b5e53d0c42d754f4310aee62d0c42bb58b4310a7d6590c42cf9524310abd6590c42cf5964310abe6390c42cf54e4310abd6290c429fd954310b3e5410c42d794c4310b5d5310c42bb9884310aed6210c42af98c4310b9e6310c42cf94c4310b9e5310c42c794c4310b3d5310c42e754c4310bae6210c42af5884310bad6210c42cf90e5210b3c4394842af98f4210b3e53d0842af5924210b3e5490842bb5924210b6e5490842eb9524210bae4390842eb10e4
  | 50 => 0xd4843af9835210ebd60d4843af5965210f3e5394843e794e5210f3f5294843ebd4a5210ebe6194843af5865210ebe6094843af5825210f3e5354843e794d5210faf5254843cf9495210ebf6154843af1855210ebf6054843af1815210f9e6314843e794c5210ebe6214843cfd485210fae5214843cf5485210fad5214843af9845210fb66114843ad9845210ebd6114843ed5845210eb56114843af9805210fba6014843ae9805210ebd6014843ee5805210eb96014843e798f5110f9e53d4443af98b5110ebd62d4443af9835110ebd60d4443af5965110f3e5394443e794e5110ebe6294443af58a5110f3f5194443edd465110ebe6094443af5825110f3e5354443e794d5110ebf6254443af1895110fb75154443cf9455110ebf6054443af1815110f9e6314443e794c5110ebe6214443eb9885110eae6214443af5885110fad6214443ab5885110ebe6114443cfd445110fb65114443cf5445110fb55114443af9805110fba6014443ae9805110ebd6014443ee5805110eb96014443e798f5010f9e53d4043af98b5010ebd62d4043cfd4b5010f3d52d4043af9875010ebd61d4043cfd475010f3d51d4043af5965010f9c6394043cf94e5010f9e5394043af98a5010ebd6294043af9865010ebd6194043cfd425010fbb5094043e718d5010f3e5354043e794d5010ebf6254043ebd895010eaf6254043af1895010fac6254043ab1895010f3f5254043cf5495010ebf6154043edd855010eb76154043af1855010fb46154043ad1855010f3f5154043cf5455010fbb5054043cf9415010f9e6314043e794c5010ebe6214043eb9885010eae6214043af5885010fad6214043ab5885010ebe6114043ed9845010eb66114043af5845010fb56114043ad5845010ebe6014043cfd405010fba5014043cf5405010fb95014043ce5405010ef661d4f42bd58753d0afa60d4f42be58353d0b5f5394f42cf19253d0a7e6194f429f58653d0a7e6094f429f58253d0a7f6154f429f18553d0a7f6054f429f18153d0b5d5314f42d794f43d0b5d53d0f42bb98b43d0aed62d0f42af59643d0b3d6590f42cf54e43d0abe6290f42af58243d0b5e5310f42d754c43d0aee6210f42bb58843d0b9e6310f42cf94c43d0b9e5310f42c794c43d0b3d5310f42e754c43d0abe6210f42eb98843d0bad6210f42af58043d0b7751947429f98e51d0a7d6394742cf90e51d0b3c43947429f98251d0a7d60947429fd8d51d0a7c6354742cf90d51d0b3c43547429fd8151d0a7c6054742dd54451d0afa6014742be58051d0b7b50943429f98e50d0a7d6394342cf90e50d0b3c43943429f98650d0a7d6194342bdd8550d0af461543429fd8d50d0a7c6354342cf90d50d0b3c43543429fd8550d0b7761543429dd8550d0a7c6154342dd18550d0a746154342bd98450d0a
  | 51 => 0x3cfd445190fb65114643cf5445190fb55114643af9805190ebd6014643e798f5090ebe62d4243eb98b5090eae62d4243af58b5090fad62d4243ab58b5090f3f52d4243cf54b5090ebe61d4243ed9875090eb661d4243af5875090fb561d4243ad5875090f3f51d4243cf5475090ebe6294243af58a5090ebe6194243af5865090f3f5094243eed425090f3b5094243afd895090ebc6254243cfd495090f3d5254243afd855090ebc6154243cfd455090f3d5154243eed415090f3e5054243e798c5090ebe6214243af5885090ebe6114243af5845090f3f5014243ee9405090f3d5014243ee5405090f9f5390d43cf90f5250e7e61d49439f5875250e7e60d49439f5835250f6f5294943bdd855250ef46154943bed815250ef86054943db5485250f3e43149439f9845250e7d61149439f9805250e7d6014943cf90f5150e7e62d45439f58b5150e7e60d45439f5835150f775194543bbd895150eec6254543bed815150ef86054543dd5445150f3e43145439f9885150e7d62145439f9805150e7d6014543cf90f5050e7e62d41439f58b5050e7e61d41439f5875050f7b5094143bbd895050eec6254143bdd855050ef46154143de5405050f5f4314143cf90c5050e7e62141439f5885050e7e61141439f5845050ebe62d0c43af58b4310ebe61d0c43af5874310ebe60d0c43af5834310ebd6490c43cf9524310edd6490c43d79524310f9e5490c43b79824310e7f6550c43afd954310f3f6550c438fd954310ebf6350c43cf94d4310ebf6250c43af1894310ebf6150c43af1854310ebf6050c43af1814310edf6550c43d7d954310e5f6550c43b7d914310f9f6450c43d79514310f9e5450c43b71814310f6f52948439f9865210e7d61948439f9825210e7d60948439fd855210e7c61548439fd815210e7c6054843db5485210ef66114843bd5845210efa6014843be5805210f7751944439f98a5110e7d62944439f9825110e7d60944439fd895110e7c62544439fd815110e7c6054443bb9885110eed6214443dd5445110efa6014443be5805110f7b50940439f98a5010e7d62940439f9865010e7d6194043bbd895010eec6254043bdd855010ef461540439fd895010f6f62540439bd895010e7c6254043db1895010e6c62540439fd855010f7761540439dd855010e7c6154043dd1855010e746154043bb9885010eed6214043bd9845010ef56114043de5405010ebe6294c43af58a5310ebe6194c43af5865310ebe6094c43af5825310f1e6394c43cf98a5310f3d6294c43cf9865310f3d6194c43cf9825310f3d6094c43e75965310f9f6294c43e798a5310f9d6294c43e718a5310f9f6194c43e79865310f9d6194c43e71865310f9f6094c43e79825310e9e6094c43e75825310f9c6094c43e798f5210f9e53d4843af9875210ebd61
  | 52 => 0xb0008003000000100c4003006400300080070020000000000d005800400dc000000400a007004a000001700100020080012011000000c80050004002000c0000000013000000100500000010017002400200e4000000800200700060020000008c036000400200040220014002000c00c000c003000000a0068001002400a00380030070002004400202000080010005000c002000003600280080014001001400c0004004000c00200040010044001001000e0028000000c0050000000000000000100080008002004400d000800000080000000004000008100280030000001003000200100080008001004c00a002c008000000b001400400280090018004003c0000000002000c017003000f0040007002400400b0001000c0030008000000c002000c038002401c0034033003001c0000003001800f0024000001c00f00cc00c00080020048009001400e003ef661d4b43bd58752d0efa60d4b43be58352d0f6f5294b439f98652d0e7d6194b439f98252d0e7d6094b439fd8552d0e7c6154b439fd8152d0e7c6054b43db54852d0eee62d4743bb58b51d0efa60d4743be58351d0f7751947439f98a51d0e7d62947439f98251d0e7d60947439fd8951d0e7c62547439fd8151d0e7c6054743dd54451d0eee62d4343bb58b50d0ef661d4343bd58750d0f7b50943439f98a50d0e7d62943439f98650d0e7d61943439fd8950d0e7c62543439fd8550d0e7c6154343de54050d0ebd65d0e43cf5974390ebe62d0e43af58b4390ebe61d0e43af5874390ebe60d0e43af5834390edd65d0e43d75974390f6f5294a439f9865290e7d6194a439f9825290e7d6094a439fd855290e7c6154a439fd815290e7c6054a43db5485290ef66114a43bd5845290f7751946439f98a5190e7d62946439f9825190e7d60946439fd895190e7c62546439fd815190e7c6054643bb9885190eed6214643dd5445190eee62d4243bb58b5090ef661d4243bd5875090f7b5094243d7d0e5090e7e62942439f58a5090e7e61942439f5865090e7f62542439f1895090e7f61542439f1855090f795014243e798f5290ebe61d4a43af5875290ebe60d4a43af5835290f3f5294a43ebd4a5290ebe6194a43af5865290ebe6094a43af5825290faf5254a43cf9495290ebf6154a43af1855290ebf6054a43af1815290f9e6314a43cfd485290fae5214a43cf5485290fad5214a43af9845290fb66114a43ad9845290ebd6114a43ed5845290eb56114a43af9805290ebd6014a43e798f5190ebe62d4643af58b5190ebe60d4643af5835190ebe6294643af58a5190f3f5194643edd465190ebe6094643af5825190ebf6254643af1895190fb75154643cf9455190ebf6054643af1815190f9e6314643af9885190fae6214643ab9885190ebd6214643eb5885190ead621464
  | 53 => 0x140000000005000401e0040077000400100700130000000000000800040000034004001000b0014000009801f000000100000010004007001405000000130010001002800000840010000000002801e000c00000000000028000000000900040010014002001004d0000008000401d00100280014000000c00000180210010002000401d0000000001c014001800900200000048000000c0020000029002800000dc002000401700c80000034028006800600100000000000006c012002c00100b40050028002007c00000440010008003000c000000001000140090010000000c000000000f006c009002c0280010029004c004003c006000400100240050004001016c0bf000401d0020059000c00c000000900440740040000001c00100040000000002000000200740020020008000400c0018011000003c0004000001800000300000008003002400b0054000007c000000000b0044008000401300080010008005005400600140040000000001c001007000b00000010000000000001e00b4001001c06f00040000000000000c0110014005008400200000000008005000000000200010058003000801a002803e000c0010080007006000000140000004007004803a000000100000010050016000c0200040007002000700040280000000000000a0034000003000a0000000001c0150018007000c000000000000100150020007000000a001400000000000000002007c00e0004002005800000000220000002001c006000000000e000200080000030003000c00b00140160020000000400300000010000000000c000000000c00e800800000480008000003400b002c00200100120010007006400f001400c00040030008001002c0050004000000000000180150090011006c00200000040008000001c0060030000000400a00200020044007002c001012802a000800000140410024034005000d00000110004001000000000d00050028001005401800b4000001c00500040090018000002000b0000001000000f004c00400040000018000001800f000003d00040020000000002000600940000010033005800600000010038017008c0000188007000000700380000000001000c00600100060004003003c006001800200c40020000006003801d0084001001c00000000010000002000c00900000060024002001c002000000b0014007001400000700060000025005c00000ac00b003c005003401500000010000013001c000007400c009000900040000020001000000f000000d00180080010019000400200280050000000001000900400000024015000401f00380090000000000c002005800d001800000480050000000000c000000000300100000014024009c0130034000001402300540060010000000400b0008003001c
  | 54 => 0xc019003402200340060000001000000c0010059001c0030024001006801b00180090008015006400b00300030000002003c001000c0170068002001000100bc003003800000680030008008000c00000100010000005000000000040010008014000c0120000006003c000000400b000c002002c0040000002000c0000044005001c00000540220010004005c019002c004000000200380010008005000c00b0008007001400300440000050002000000000000030000000001c0020018002000c001004000b001400400100050034000005800000400080000001014000500000000000006001800000140000054015004400000040000040003001c001005c01f0018003007000a000c00c000001700000040014001005800100000020018042000c0000010004000c0000000001007c0010038000004402d0004001000400a000407d00000020004009003c0110018002006000300ec00001a0003002000000040000028003000400200080040208006000000000040040010000002006100240220070001001c0000028004000001600040110040002000c04a002800d002402a00280070044022000000600080000004003001c01e000001400040030000016001000100a80160008005002800300440000004004002800900040000034000000400000140040000000011c02200000000010002010002a0014015000002b0018001002c006002000000000010020002001c0540000023000c007000803100d000000d40010020008000400500180020008002000000201e000d003c000002c01d006c00a00a4002000000000000000090024000c021000000d0024002001000600000060018022000000600680020018000000c027001c0260040001006c000006c001000c00b0004004005800a001c00200700020014000002c0100000001000000300a40010010005001c001000000200180000004003002000600000110014005004000200ac0030004000003c001000c000000000c004c000001800b00040010000000003c0010090006000001b0044035000000100000070098001002400c0004004005c0020000000002802d00440200018001000000200580060004016000c0000008002000c00400c40000008004003801d0004001004800000b4000000000000e80010008010001400100580000000003008800600080000008000001c005000400000380050004009005c000000000100000040000004002801c001c004001400600000030000001001006e002401200040520088012002c0000000008000c01c001c00b00540050010006001c0000014002000800601c401a001400300000030000000000c02f000c01b000000b00100000048000000800b0000003002c00000380070034011001401d000400d000000d004400f003c001
  | 55 => 0x4012000c0000004004006c001000001d001000500a8004000c007000002b0004001001c00f0028000002801b0000001001c00100000010160005000c000000c0060030007001800c000400500080040018001000400c0000005003c001004c003000400000100000004001001000400080090008015000800300540050054001000c02400540000184005000402c000000600180070054001007c005001c0030088004002c00700000000010017000000200b4003000000200000050064005004c005000002000080010004008002400600c8006008000100140280004000000c003000401700040020000005000c00400a4001000000d000000600b4008003801b00140090018007000000300d8000000c014000400000080100000004000000f00c800d0004002006c001002c01e0000002001400300000270024002002c01200140090018000004c0060010002001c00300000120004000000000b00a801a0018005014c0020148001000c0000000004000c00a0070001022000b000c000000000000140010000001001c00b004800a0008000000000200a000000100000054005001800e0010000000800800180000000018000c001000000f0064002000c006000000b000c00300480050000007003800a0040002000c00500440100014011004c0030010000000000400080070038002001400300080090000023000000300000040004006000000000040000010032001c0060090000001c00300400040034026000000d005c04c00500170068002002c0000010002002001500000020000008000c00b000c002015400000000090000000003c01700040080004001002800400080090010001003000e0008000002000300080020004001010c0000000005000801400140320058015006000b00bc011002800600000130010007002c000000c000000c0080000001000001000180020010009003800000000010000037005c00700000050008025000001301c80130024002001800100000000004015000400000040000018017003c0000000000001400000040250024000002c002000000400100020000001003c0010000001001c00100000280060018001800100040010058000000c019003c000005403800100000000001001400500000020048014000401b000800c001402600400020014000002c00f00000000008001002000d0024000001800b002c0070004008005003f00040000004000000c0020028002000c00100300090064000001c00900a4014005c010001c00d0008006001c00700000050044000000c006001400000180000000007000000c000c0050008006000001400000000014045001800700bc00000080230008000007401200000060010032002000400080110000000001801b0000003000c0160000017000
  | 56 => 0xc0040010005000400700240020000002000c00c0094000002000300040000008008001c0000000054003c000001c00600100010020000005c001003000200000050010001002c001004c026000800400180a200000000004000000000b0018002002c00000b001b001c00500840000068031000802d00000020118001000000200a8000000000200040230000006003400e0000003002000200200000004009000000000000010068004000c009000402700080000000005000000a000800a0004005000000600100040000008005000100180160004018002800c000400000340070000007006c02b000000200040010018005003000200a0018005401a00ec004002803e00140060000002000400100100040020028000000b001000200000040014005000000100840020000002000800f002c00000280000000001000800000040020000003001c000008800100000000014036000400500080030000007007c000000800b000400400400030000009001800000000040000002001c003002c0120048013000000100040020008004006c00200100080054002000000200000070020003003800100a80030000000001c00d000003700100030000000000000000000100000009000c00b001000d001c0000074000000001400080120044014000401a0008011000c009007c008005c00400000070004001000c00000980020008009000c001000000600200000000005003800300000000008000007c03500700000000001000400500140060004008001c004014c000000000f000c011000c006002c00400400000070000000002900080020000006002000d00000260000009002c0120000007000c053000c001001800e000c00b001c0000014000000000a000400600a803e0058002000c01101100000000003001000001ac004000c00000040010000003001c001001800100400050000007005c0050004003001400000380290128000000400000000000010037001400a00040080040000001800000140150098000000000500080140008001000001300000010004002000000c000800200dc00500b000100b800400780070000000000c00f000000400080020008001002400500040010024003002400c00200020028000003c01f000c0010044000003c00d000c013001c004002802b00380050004000001400000040000000002000000e0000000005000100240010000001000c000000001d0004008000000b0000000003400700000030000002002001c00400000000006000000000a8002003000a000400d004000b000400600000040028002009c01b000400100c801100000000078000005400a001c008014c0090048006002801a00580030000000001402b000c09200000020000000000c0000010003000400f000c00c001c00
  | 57 => 0xf0004003001400100440060008004000000000040000000000000800900180000000002000c00000000070000008025c002000400200000010000000001400f000c00000740010004000009c01e00780020098002000800000700250008009000c00200000000010000001401e0004023009000f008c009006400a00000010070003002001a001c0030010000000401600480050018001000c01100300000010000000c0090010022005c00f00000030000005001c00d0008014000c00e00140050008000002c005004000800100020000017000c00300540180010000001000b000800e000000100000030010001002400700140090000000000800600380010008000005800100440000018000003400b001000000040030044018000000000040000014005001000d0044002007c0020008003005c0000010000000000200100020000000000800f000c000000800d0030033004c0060000090001800b00040060000020000400a0030000001002100300010014000000c00e0074006002000f0004018000000a0024002000000c001800b0018006000003b0024001002c000000000f001800b005800000080020014008000001c001c0040024000001c00f000c0020000003003c00000b40040000004000c00a001c0300010039004000300040290004001000c000001000b000000100540180000001005800000140000000004007c005000800000f00000014001003c00f00080150000003000001f00b8008000401400180000014001000800d005800b00080020104008004400600040020014003003c000008c0010034000006c0260004018000c001000c008000c0000010000004400200040030008000000001f000400600500000000008000000e0004002000400b00300030000006000c00000000030004011002000000040180000006001c03c0008000001400400f400a00000000004000005c001000c00100740010154009000800800780020028009000000a000400b0028002008000c0000000000c00100040030024004001400a0024015000c00a0008000000001e003c003000400300000030004002017c00100400020038002001400000000070004008000800500040000004000000c00a001c0000014011001c013000400f00380000000002000c00e00080070288012000001500000010000001000c001004c0100014000009400601580190000000006c00b001400800d80000050005001400d000400900240000010002000c00900300180194009004c0010004011002000a0024008004400600a80030000007000000900000030030003006401500000050000002001c004000800900040010040008000000100100040034000001c00e002802c000400900000110008009000c000000000c00000000010001005c00600
  | 58 => 0x174003003c000002005d001000600040000038000003c00200140020014002001c00d0000000002c00000e00280028006000400e0018016001c0030034000006c00300040c2004000e001800100000020038000000402e000000e0000005003c0040000005001000e00600010000003000000300300000000006000004400100000008000003000a0000023001401700000040018003000c000002800000000000028009000c044000000f000c0060000000000c0010004002001000200800000010001012002a0008014000c007001c00300b0003000002a000c004001400b00480010010003000400300040280068000001402a00000120004004003c04f006400c00540050010003003c03f000400000000a700040070038000000c000000400b0058000022c01e00bc006000800c000c020024800f000000900000000004008000800f0010002000c00d00080030004002001c0020010012006401400280000004000000c0070000007002000d01cc00c00440160004000000c01400000010050000001000b000400000100040044000000c0200008000000401f0028000001c000002c00400bc004000000000080020000005001400400040000004004000000000100370004006001c01c0000005000c00f0008003005c000000c002001c00000000000014004000401300a40020094002000000b008c002004400000000040014009002000000040040028000000400e00300060000001000c01e002c003003800700080000040009002800100080060000018006800100080000068002000000300180130024002000400400000090000000000400000000040008018006c00200000070004003000c01e000000101d00010074000000802a000400200480000010000000000e0058000001c00500180080004001006000a0004002003c000000401b000400000100000010003000000000000010134008005000c0018000001400700200000028002000001a00000090018010000c0010008001005401a001c0000064008002000300000070014000004800500200090024001000000e01700000074000003c008000000c000400700240000000001000000500080000044005001c005002c01200000090030000008000000000140000000001400001680120040000003001500140010038000000c00100040100010001000c012000801e0000004001c0040000000000000000b80020034002000000100680180020006002001600e00000000000008c009001400600680030020002000000200500000008000003800c0000011000400a002400e00100080000000005400200240050008002000800200580030038001000401d00000020004003008c016000400a0024007009801d000800a005c0020000000001405100100150004002000c0
  | 59 => 0x427806940000503076c5fe86b487060f404880000267f20807864f41974f089e74c000004540b1e83a83bf9d0c0d4a00000001897323a41f85e1163c2fe88c740002a87000000000000000000000013f10000576a0000000213b000098540ca23a9000000000000000000000010ffa18c16042fa800006310000298cabf80b5211c90b058506e337c24c48000030a0000aef4785272732026ff4000000029f2000151da2f62ac80000000000020be58942ed9e6c2560ae9cd5f8dc3028600013560c1408a44ae935a1dc84cb45b293790ae617dc6931023239f4c3425a54ef93c739a403a4516800a18c6390037c985938324e0501680d8154871e82cd82ba3c3826e4a3f940224d6153461b821913980f1d2081bc72fdcafd80002ae22f1e3b04e8eaa802024892526192ce00004b9064e26bc0f6241602c612fd3fc2916016d04f304249f254b787d82b08648c96a83c549b493d846d29ce54d05dd498d0fe32cc248353170beb22da09b52269f9c15d833b49b00c52313c4bdc0001ab0000e05a857a1d8b502c5bac2e6a12900fa92e45ee077d13568b8c6b10c3b36ec41783c9003c000081704030559120e307c46b04294a8413b86fa99103df89cec6e5992b3d6a1618a18832e256eae1449d13360fe029146da80002d3c043d2811cdb00000000f5d037e0f0a0000342000030a691d84750b5a08548bfc00003b435049ef135f277c06de42f0b3803460000000068280004e328ad8e2300001cfe4638da21de1249671fc000036c0c2e97b4a1f95c3031a2e10fb59b5b39440000c342b440eaeaef0c9420ce47a057e54fb000006a000000000bab000000008c61378000084e03d118ff000023ccef529d248543c74634872e3e5808ed06d954451e22fd8980235a19a059ac8ad186542b64d4c5c826eb1da87aec47a83321e02040c16f24070afaacb0ac424f71c723bbd0411fe43dee52b8b342750359e2a2442d8f4618e60040ad4165036989c74c3f8cc13db03ef051d9a2503e49df542002c71f0c7a6d5d880000ec84aa90bc00bb2ac676bd4dc24eb04468890000090f1b466a289b60591000017500001aa8126e3bdc00017614a781c99397abab31be837447402261d5a33f4fc4828813a4a70d0a81297464099b0db10f07215e6d2c4972aa2485a463507f1b4e2c96afac05123383234730ccc7a4c440045d70e6a044b000055cc0a0a37b250c086d2a4103f24fe000c0200008000004c00201bc00300340000084001000000800000060000000003400100ac002001800600140150028005006400100280010000000000800b0010005005c03d000000200000150018004005c003001800d000000f0000010005c003000c0030010001000c000000400000740130010009000801200040060004000001000000000110018007000000d0
  | 60 => 0x140000b5500005dbc0000d43000000000000cf84ee82a748df8bdb3d9200000000000000013f52848000000057a94c3049d000000013c397411b8e2a8d4dd8000000000003db0349351e9fb0c3c285a2cb01e54493104b4dfe932cbd915774002354cd6aa3dd03c431701d329430b68a30800024133eaa00009088b8b2bb0000027d198118b06e84cd991c21ec618e81db86cf22e674e0000032f00000e4caae219f0928a23027b847300006a7846609de0000000014d04b51ee067ec8950000424a1360155800002fc94e457709971d36000000024a61cb400000000636162c1470978102739487150271236f42d00000054224b56266ba513f9a1b1b08700800013fd4ade654d54e83cb00000000000238638cc000000019024f70301cb2501e7431c7f4c53c800056ee24f0b21843822e200000000b3b1420a4881c7a20e000098080001ab70abe8e8838b0000454a4c843a683c431740000d930526309c00002cc997b367c1f8849815384dc6253c2e9ab9d3ef221d8708207c1ede8e445680000000000006bc000000005284ffca0c30000a6c5613ac22151e645499c80003eec10ad07592050fe80001196995148c00a9c9ce2a793afe0000a680000586e00000000a033f94a6d00001d8036fc47ec000000000008ba52288c232780535800008e0000015190489e9f4c86b06000000002a78000074d04184b8c778864b877c073210b0233896b1b16b0155222c0f1d6e29b84b30000479850108cb215e000033f903900001182a7a05f18000025e0ca9033048d3c1a3fe88b906704cf22b7d3b393b61ef698004082bc324c657d40000000000036440000000000051e4a4e00000000b11102e8000287288992bb1f0f036a08dc9ac8ec750fa58a400016d3234603642441e771ae45f788ae8a0c376096e538d219023605a4cf2d8000000096887968000000030493b7abcf000000000001a7600005c0800023172b440d5c7f325f63d72000000000002826855c26426c0000019d800011a54216000000027d6074421f40000f924a86000081681b750dc0000000019100006e7131595c42588000000028eb0000a6dc7a7968606ee4fb000000004dbe0e446bb27723cfe7eac000153900004800c9488f6488800000001113263015b11320e740c7a00004ff9f0b4d16388c0001fd83ed87a5c2651c7b149c4d30dec9d4708bc89ad2bf21ae459c11f400009a84fb400009e982d5533e952d48d23880b2a60447529e2929f833ecb6fa1c949be56786368afa38de3604f3f0cc931a60ca03de003a0070104c0320cf23ea27c580420d4500004f08a991bfe43362d88d1e80000d5a57c82e29a912ad450c0f3d8f18534839d8bad000053e80ac8000153d4a9e215c8078000180401c92c714860a1c78c8a958bbc41e40d9512d000000001ad4000000
  | 61 => 0xbe141a0bc80000000016e664045f0000166a480c3a30cb84d1c9b100ad8c1c4fa200002a48ec502fe3b78846a2ee27ac0000eae192f1a4a9ce8266215135f430f0e551da725b015106078b751bd0153d4428c9a26f4382076c0b0310569de42f1941652da324800000001ec4ae8114828b645240f9000000004f7640dc000243d543e40a03118e911e9a3710000174744a4000000000a300000d580641526194601b4194a97129f633bc11505142ece64ec351a4f93720000000000001cee4f7c00000000000000095e0a7d000086b47af22092056a04d3f8aa014538793162822bd3c420000834937c538ea4f0d6c03ca18c25cfc1d420f638602e302811b02087824086a7000019682d7c7e4a34706561ee4891295400006e7888900005880449c0001a453b72665cba491e913ee59cd0a518722c585c70fa0181611ce00014b700000dca19140ab076d00005e5c00018f84f50a10c8ea91f20000090c8ec8a0200020001303a8b04fc05b24bc421e400000c151d3182f00005ee40001b351f8484d00000f422efc1d14e2e2ade57f23038771a71f1dcc7c90c86256e2e680000bda9c7756946bbc2f0166c5424594c99ba2c716a869a0ecc199b0d2a11b07b080000000000137227a930d61f6551c105a2f6c93b40002bff46689ca90818640000053d861203ec0e3aa87439c8000412019380001b873b0c67f90870564377262dc9c22425119c000034e8000000055f05bba9994c5460f800000000de4aac400006dd00000000c0590db56aa4de4000000043125684765157552549a191410a7f00000000e4f201f1e183e8938f041533f2a7512449501589261eccc894d350f43d60cb80d011aaa57d939600d457029750b5080000b8418e00048c213fa86a6c62fa2311ec043582fd0ce51392aa713121d703a0060347c122d6000006209bb0dd13ad46fe803b208b50a898f04d7194301567c0cce8800000001ca0d4b21b2140c00015b08a9a12627e40c58029510364760f9ba222363445b04b08542105c3954f15a96b03d4493400000002c0204c4adaa8a340326e9134a1e2e0000739936814351e083ac433d00b437ec9aa05b900001b2a00000002a864ca81fb87a20e8f000042a800018de00001864832a572307400002482b932876000086c0000000000006db8000437a000000026c54fd200880000000361c08d4c46000049c6357cb0710a2298815553cc9619000075ed4cb8000296c86f01120f9d36bc00013398cb545160000bcc800030304d24979143a30e8000007413dd293a8b113e200003a6ca74084f959b00000000bd583b01cf244f8d99a9ad31303520a4c9ece000000003b9a39d4f486cdcf81000004522e8011b10bb1f74000049101dc41a8a5c0edf92b939ee2f583ad8e8102264b48000189a0b520000000009511f851
  | 62 => 0x62a0db64ed88e506099a850000a74cd271155090843f8cca84ac53fa8b713ea0000452c8bc859387613de091580c100002c20a0fc5302933110e898000024593678199952d98354f6a6e18d4e1184324c421017880000e56675c8ed1cf63edc51c91dea9e701726618515a1aa583408383e903df46ee0d7c97613f41c9e382962616842ff244041cf10da4c6a50d8b249aad150a6c8d324273f49dc10dc8b5299c3f086cf4c3f250638804e8c10e00000428198cd189a782c36144065c8c0811540cd04949681417e888472ba7541ddc07553df14290e5a29c4c708b302f44a5c91cb97503cd43ff954c17a533500a046f78ad51b8a7ecc58a12a13516332c8b4000035dc17848ac0136227e7f98b6884d607ca00002510f9e17525c10a7c0f7736a885904d62597396c43fc5f41f8a436e2658700910f050e00000002b2f3a7cb10800000003fd876c94be1e0c4b38000146b1b734bc20cfcf88a778000000000002bdd1df228c021f80003642000146212224d1401040001a893aae33d439296ce3fe214b422b07c32b520ab500200004a700000088849916709a142a280000000364cd39a3d9218405307bd0000270a0000b6000000b04324c2102a904d38246ca898fd40000848c6969e6d000009c41be298419d207f80000f1530ce53c91b10c1e218e85206990000000056b04b9800002a6abe49f507f536e0b06c0001a542b2a00008388000000054f836a00003d7845a5099800000000000000193120ba14bc9e417e057580000000000039088d3cedd8eba00000000b5f234300000000f8e80004c703e2cb8c256d21524260000121b4d46759959800000d3872a156f876a069a09fd4390d94460c0670000225f033c5e18d3a978443324460c4fab0516f64214aac81f444d424ac6d8821f254049506ab288a00000001494000025da1680000018500002b1c0000713000017dd0a21da31e0aa56d22e9da603c00000975800004b670bd1168e9814420000000000054ce116103a1d963e4a3648000000040de00000000422044e7ac8b6c2333314c28f8382a4191b94552cf76000000000000000196e43bc0564000000032ac885c1e980da1ea2017492b25ba370684e49c7821e43141610000000000009cb800000ca47584a554bc8a562b1812f800013e226a8aa6495e815f3078508540e15e5332c00012a000002a202b0c7dc16ba4cf6a08025f809142fe3d4c7799b57142a0380788a2bb05288c7ca3c2ab44f9a8ed90f29a5c4d702c6464299e534d895d00000eb81c98828cce429370000af5c56613e04dc44a28da819fc069e1f1d04f8d070d960c50f621bf10000187869c84df02dc77c0000136e00007ec8dec0068184c000066d2c1f125e40c09b317c30c240001286a3e6458c9d149952bde44fca2346c6919c04729ed0f2b1c
  | 63 => 0xa2f4aa49454cba97100e341c8d26403ac1c96000117e000024889c311ea84d10b7c000075e240841d8477c9f79eaa42e472e00001aeb4eda81fcc2ba26716f46d813371ea4100241586e60000516e42848f62aa444507a1920da7520696829c50e88ad30085b149d30e1407660130ffe800000009a20b54a4a31d9e27802fe1b6c000000008fc834e02cc71612d19d8244bc6089506895e382a40ec7c803022d6a87dcd0e8000000061800000a9933ce5a985699b2f3810a12959b94c80046320c0000c1a2da8a45901593563f3e600c39b266a327c00002dd9a6647ea6f6cc0a01b21afa9dc52d701de1ea041d4493838a3e8c63f92e526d74f8a47b9207a2301e740000a25800022481f986f3a9f039e078ec31f9f3a000000000001d08460a88754831bc5568a000108504c6562e0c3cf7a087237647e0000028b350900478b96800009221d302120b7e558c9a9516019b50a3e37c0e0e92900000046400000004b609e940000000120814c4fd70073219200007f800004d986620000047f00003d6931120c11d7e12b8f8f02c4531c9fb8287a20847425070ab619ff4caa934c9ed27cc449a6aece96ab1f27b02d380002c3b00002a4c0e7024844f83edc0d49639070066e0ace194e45e2a17c02a0b05000071cc32d8000363697a90e305c635525a44454ab8f3f580000000167d000000012e593e94d4834892180e605268000000000003e200000b3d164500008708f650924000012380000dd62bbc000145c1d480d58000015c00001302287800000002feea3780002bbf0000396000016f12848a18400023801db20000c1599250000731c0001a2a0000201546fabed063242e00000059000092a1224aa183f6a4b08c908536000068380000176000000005d1916b00000000eff1bac3fa4000117986fe4a5a6c1d168a00c1e1a09c0000043b24d4901034c014e0cc20000000000012b89f4ca2a80004bb495a928080001a7867715969185000000000000000203e2d5cd3680001d6a00001d884a8286ea54815e1d782a68500c0000000394a1e28066203f206600000599e8c00005f8c000000054a00ae4a59aa48230654a863a87b5344e4dc84bf8f270fd23ca0ca414e1018a1a4946d14580bd870a502907da000032a8c292153378c6e307da1bab514a25440ed19e91e70a9005879edc42ac42f54932a3516d69c98bfda7a2144a039cc0013cb3b9e000014f8808453a3e803d80bde409c2f9d59280001bc6220cca69c0e55a4159d0809c7927bca238e1c0b0c2ffc00013af296300ea0000000000000000b30a02915922006dace4100003e888bc0fa51fc016ec09653688acb3e720000f2f00ef000000006b08a010f1c003c6f00e8951f00000993868a56d6a9e8eb19f4128ce1f292d996e5243053b80000382000039e911b20d752640
  | 64 => 0x4e2425e40671f67507608e8414934e2a90a9450f72c31000000004541073524665f41ddab5853a280dc1988efc0c5a00006c423d1264c226cd5e9f38586048b091f230c221c0000d671f7c210c08cd1d8270233769a84fb420b81d08569c7fcaaf418e461c52058b0403168310f7d8bb916e03bd000020b507f80000e1289bc00001bc557209dc49d47b1caf48000114800004fe23500b90000128d80002b060000ea8000033602ca8893000041b4635c6c80e50193a66d1415220537801ecc468a865339ea31c41124d021504ab4a8c9d49236a00005b2aafb51e6093c55b93ed094c000000024ab323237f4000059a2a5c10d87461ae607701798a2e815c4bf263a8f790fa1000000012420c8a43f45430592000039d4000089626de4b6445049a8135800003eb4ca508bc14a86a18a6e9cfc1e3268295168c6200d208454e7800050c6612c7df0707065843a48570257406c97fd4f605fe247e2d1839b92f82ea40f58000037f114eabdd1648665413c447035d98960000719c2d8019905c02b80c6b1ef63ca2aae0eba26ba46946fdcf231c640f1644f4bc7128023e659313ee17ce1d0412046560e3f1a200000f1c82d11820698c64b1f7e57309b4800013342dec8a9cf4509da00009778ab728ec3f7c9b38d0224924e262f853d306550a1881204722a811e68a68cc268b1d57a6ac104a490b12ab05ad8000017d000098e400016f05008464017c08f753fe6614bd41e742e862210cbe00001ac00000bcd1c7c297e00003a780002ae00000b948000000000000000000000081c0bd6800000007f3c000138a2f62858562b0000241253d54c1a91100008cd8814a28e133895c4c211ffc27d60000e6f257f0c78a4112d5954a52d47a60f438ca6541c000046a97ca07eaa82c998150346729d80094068e40949cc8fc0a0404b7875b888d06d820b660dca90031d010610d0de19bee1590af2133822161bb4354402587243a0c16e547e8d1f447635e92321772064600012e3813c37cc01d0a112a200fde340d62b8c4f1c8c0000ef22a2900001b390ad066e32e62ccc12aa4154a46a06019d80000e84ab5c9ce80003d4e428085209f94b244fecd841c3a502e830110812b130b60000b2b0000553662047031174000029c13af9912392e4f8c0001f7108c4b0d505e12c00000000000014521652a0a10080e623d6e000069d8000040a841c00000003ec28dc4000280f2cca1b9d2430fe21f0aa8aca6f012752382cf0f86949b47e851a01ce20ed00b6a4b948602e600001bd46fe0e1108a2814c11f1fb7557c000000000001cd89294aa9a43e0fec09014490e7d000023e09b38c742e2c00005cc8c8d4432718c220800003060001234002a00000000000000045ce000038aa5573374156c0998e6e555c7898e4b173926d0547851e9
  | 65 => 0x91c028249744d4c234200003aa0dee0000242862a4dfc1e031c709528000287300002a0d37a247517ee9f384aa82ce00007968808296616bc261ca12a1cf4886084c43f1d5f1f122c80a97aa1535e80000e721cba0184894134e94c32904000072126f83a124268bd3174d111446ed5dc800036ee394d3738fd82b7818cc56a293d439c13ac000158709887b146fb9a9309ca3600dcd11175322907862526f6000099f88d113574ad21230ec689983dd069607ee990428a6683c01ba4a13da04340a8729a50e2e3c24c0313cc493446c43c21c2e56dc6110e1399ad032c5a8d6170508397e0000ffb940f1c885c8c04da94b345a8d6cae4a6143af811f93a118ab2e56a5055f390380d54895ca008c671cd08bf950f0f3e000043c46541a9200000914a3a800041fa2b5c3cf8ba40b2648580002a5f433457c50a6a04b325a46b489a889620c834a875b29c81134622401684f950189998c6285c426522cdc8fa0cde49cc649d2a700f62bdc3a905ca0aa73238315c409a80a46ae1730bba295804c04bf94948ad64d6612f4bf403104eba650441d888c501606905d3859c27b22b74edb29140c1c32dd58c02e451783045083255a041a16f4a96882757443f04af40be225686de8546092104c204b81e12ae50880240c000226f0218862c39a8b670e5ea0b0b8391b61054963c8f2aa4126da1ed0f9480001d0c96eca8411cd2bf4acf424908153c30823c66c01c137c80000f80a17d3c46345091a899036186ca116500000000a0244489b9b1f60030157b2a8e2fa41b2845b860150bc1b80f7788c73b5a18711dc14e5000030052d50df30f9882802df80004ffc6d70c04000017a0000151d139f00004d8c00026a912e8ab98000223821245dcc4a927ca0e147f0d1d71d9d4df6455853f0fe526f6015434c800048ce00fc25203e620f2742c51d16b7274e83fc7fd95a629d29f3c4022881000056bd02a1a4f14a601ad3169baa4a164474acc229337267a20f3d03fa00005ac80002ab938c2118c0002baa33b45b0c9e2800022462d8500986ae4df40000e6100000000a4fc0718a4f5684adbc00028be000011c8000261f1f8800002a081d64c0a5875139ac2a26325e28c142b2e4102a5a00000727049c69fc08aa59b3ba44ffc0fb80004c8ea0bc000125a48a80000caa8ef51f8a512831a000048aa13bc528a0e54430006819f1d8a0a4a2f011a9000025522888c491c4b557a3c18187165a56e634246270d660000735d4128b001e3e86e893707a9298e6bf420ea7ae0cb81f1534d80002db624b160f234800007b8400014b900009a5515aa08000000178a8299c21db411b9065a30f01faa500aa914da26501af861d076e3fd02a28d89044552748288810862e24800ac136a000005802f6960c80002974a7310b4903508d4000000022c80000
  | 66 => 0x81dbd5dc272943ea09700001a343cf200007afa5b73fc02c612ba80313ab24ecc00025c500000000fd8a5e911caaaec40e13771bd87ebcd15948b000060295819e1b50a6061cd95a68201ac31046852bf32e2a072419d0b43500a3ed51fba44e0000a66c5d3045d00006718c54128837460000aab853a41107068f1524ba04baa3b4794877e43aa4ba900f17c101a6ae18f168d63170a00000000000059024f90e180000000000098b884b4a927818090aabc39c24aac48e813d5522675812985aa190e5428a4082a8545c461928000004166000160a000010485dc40000000000015840002c3f000090503e8149039200228638a432000091b800022511b382f4892f060d179800009ad24bb39dc0000f98168734b417d454380000c8e92440000000290e000000010820ab00000000000000003534da2909e386c257cc381d5a4d3c00014c582a112a800005a08d301f72000073c20503d680d283b300004616000151e00003a363b30000000000000000000003b000082bc00015760000857c0001bbb49ea91d0fe606b94750000028d95fb21da1e441f380000000000000000000000000070c8aa1459a361500d8d28000086704b88000438a8a7928a0000000000007909ea117149f9035a0000576e690c000057b14000001357800028d2882c00021284fe65d2c08d17e50000331432521be33063f70ed981642b567c8073f0000000009e468e2c1002de1a9872c87941b2e0e75030191100000000a288000547a805c6b683d742b037e55260944559e9118dad138b40fc968122e26b600007f14dd32658379200012668bbf4b125974b99238e30865cf10341992261287750c41f851b545f64f049a80452e3facd0c29be4e16706106423760bb407f0ab30cbf08ec20395411e1502e47db490a82ca4af47b7d2902a4d31c0021c2d12aca38a6b14cc238e4a0a24947933398e612dc127920894ad09740540a52809728cc4884ff2974e56a087e0249a9e9292c493cb058610401062d0e90088227287648eb6155109d80f7836286da33b2233c3cea000331a7ff8c4e0cd53774abe8f84121304bc4500f52838d28a86a74a7e9a9029260e0d0e6a09346ea14e0e4e94b10000800d0a780002ae8209815605d2189622354c08ed148fe7ed121419841d140000000208502a4890d18c800054720000c0d00000000000000009f31d9a32ec000140a12ea13a85b322b451f679bcf1800003c66000121b9095079c31240002581346400001fda6c91bd44c78000093f31a234b852ba1c1082e000016918c34c0c000012fa48d344861b8cf62bc12e5c64809e20d1823125328000000000003c500001fc41c684d914802a624c8c766c9df24712c746ffc00000004ec80c4c0000000000000000001885000069754711d8f000087ad05691194daa0000333
  | 67 => 0x60000000000000000000263a7dd4317800043e01da5586279100005714104933b0972a564391000000007dfc329018133385308a8028010000a2595cb21353c0800006bb80000000669c1cd2a5d4f8e36a0cdb80004c02458400000003258af84e990b0b00000000de88de91dc248b55fa857f2a447d302b4926412ae00000002aed044a8eec00011e84296a6a8e06268d000056cc1a980000326475c00026783f78377c35810ac19e800011479cf836fe1cfc000000000009128193000024a60001243abdb121c6cece1b8000000044300dda89f33642270f17abc60538aebcc421e251fda00001b8057845066f095e292f443ae8060000238b00008378fbe9ceb0048a07c0001825013a000106c0ec000005e040002aee29c056b800020860000acc548580002dfa5c0000019c9100600012991ea90f04000140c8f6706023e31082107203081a351a289cb2cfc53a960b81cc1d900c9c0339ddb378256445ec10442846058436f1f1f314e5e14c740000388417e034d868602944589057241610c44bbcac586d61d1a9a104beaae8095e0000d3a27824e8e18f8de5006323ce252d0fa27e64cd610780e2a10800001ba07a38ff82eb28df813626f0289c1a80b900cc44aa629002cf0dcf05a85054adf28064984a76871f05e2000067e0038ab0a0000120cb898fe003c83f28000125f321c64fc52a800027ec8954ac5295e3c8e02bc0000c7f191e3e554d4a7ad2aa85b3517321f638d4708840c237d1b4a0bb49a8a2894b3e924cde598ce53122aa8a76a4f435565bbc9740bcb00580280000138800001a8948f00000000a7c857a800016025898000064603a252a02e7000032124e804f392cc33dc0054f988000000045b8cf680000000000015e800057807838853226849c48e94000287f0000a2a0e6e010a33c414f46e115a01a681d0d15c000000004928fe88a97208a0f64a62a1dc43a86c10e8c256205b259dc2ea9ce94c68aa48fe6924c43244345308106d40f06704a609ff800fc5854e9aa52b0e18a35108b90e64f46ab84a002c1d2e3c8a6406b84472fda37c8bbda0df47d01b112e994c908382f24efb221132722ee9114a418315842cd38822f908aa114c56687442d2494c067d00001fdc000000015ba55d6a38000008d92ce42ab83ba8a4d378877e000006c6031c2d1cb9d1d972ceaaeb8b8d80000000000120614184644621c00027b711e476108c400000000974961ea05f0eee909017f901507d69d014838000106e6a9095601692d36704d2889f192ef2ac84fe31641124666603ffa248326c6c78000277f0aec4ccc6ff2235269e569541800000e9c6cfd5b01f052c502b610a4800044380000757969f4c620000a88aa10268600000001c7d0000000129316980000a2ec8ce80001eec715912721d00a94196943818660ed
  | 68 => 0xe000000000ba118521fc8cdf000000002340dbd800000000000000000054b80a40a0d0000430a6879220a36912808ae420102325396190415110474d9080247002c1319ee5cd4b3899f74f6256e407c0d584bae3e3d39b800000000f451f5839439b004387e1800023722280000029d3a5200000001a8d00000000c1c81aa04580000f7d0db23eb232850810000535849e1065083a0000b08439e139a512e8964d37022d0b4682e800002a65154000130627d249ba389c74000aa05004698f57000008a06b8400000000000a494000020112d8a2b4f03800000000000dbe800000000014c6c01e9305c7c6130e100900003c4c00000000236a8d147d1d4428fc000000000003d58255878d0a7a283e000133487550000849000016d63ade8488c7200003f2c3f58c6300000000000000015c64764a5703e480000c2c5824c28800054d6301400005ac4a6a00000001e124b18000001a800000000084a5522742b9005940001f7700003bec0001f332d72000105426fc47fe585cf2a80000000ad3c015800000000000000000000008f1429700004b0c000000007d3242e4f7000013cd54e2477129980000000b0ac000000055f040a894097aa513080b00001de8067a73011e4822839345b9d4b1064f00ac63d54208306460e889c000249415fa8d7d11ea792572e638c36487123876ab5809b963f4d20a798f4a85c05734626d3c180001eb65b9072724004ba0a8850d280003bae00004dfab1c57d034845d29acd28e00f8925b04fc0000b144e49000000001af400006fd18546d001570000256600000000c5b0680ac8106384b2121a6e11531881f1b7ea9d022dac11518212246aa0a8d3bd86d60a4022ae0acc1e5c1868af900002c6800007ed07e620293d8297b3d9a167c1e30a074e902f0d502214100000000001a3de32fe3628141099117e018ec0e907874c1298e872a08920cf037b8d28a1812f486cd0acf8dbb436800a5289a80d411c72649f224f236dc10147ed82422d1c7a154969ebf26360000bcf1fe9350e52608ff06d7135237e07d987f34b3463cc82403f035b23b9400007002f4286b0ddf962026583a88d781fc92c3e00002429e9439ba0fe4cc5a12b28166bc43d6986c245c66f0b45a81b4b3c319006e82d0000094b00000d49000000008ca233a25f4860c8868fa94456a1a80001899521200008021f8e00005fc000010d30c366714e3610eb00005b2c18b000032808a54000289100ae2a38f7399e63c86000000021183aba0d8457e16d73e3827143b39f5c47dc0e40b3100003ec80f60db68bfc412a0a44ea1884113ea2941603064832be8330f8da48315d2970139a0dbe23169e9cb2e09fd07de6518883897a1be21ec8eba91643d44620c43480000000812400021a84a4872195921d5416382e351a7250722c667c455
  | 69 => 0xf587682bc254515ae02784564000095b255830b0382400017dd00009e0001b0a642ef06de12f4000000000000e1e8000456ea21c93a1c8e2e7cab2c9c601c3000000f80002207010451593969bf42036000086ba3ce2d76782ce9a21700cfea82032f02fc000010c40000000000091312a3a1e900006a5509b9a221df43114eda1bef219060380f987d42300ad7c3d50caf039a77c5291269927ce29489a2247925864c34dea9ba809400000843805f47b60000f2e1d6d08cc0ef01038e2e39884eb454b0bc507468ed0033206a17cc35f0431a8795446a048000062200002904000060f00f43ba0c5ea696470878f4a068000358e2c8cefd0000022c4744a6d81580000000000000000000000101400003bb041fc0002a2a00004394475a20d0000a79548daad4505a489c9159c0900002968000274d493e0000213968900005e0c7d41b8a21f64f840000000400a0000a8e8c79075c000000020b03c6200000001019000000008a926750846134144c9ce006988e0c7c400004fe08fed38c0000000064b8d1b279f44886c7c5a790e10c0029c8000000000006ae4000000035a030a00000ea10aa434007c2129b21000dc4a1581922314aa8c0002bd03e5400003a00e6b26ca1b44a781ab80000ae44aa3953100006d1c00000000000949c10200000000000000000005484000000000004d8602249d2800049440000000000005ca8f9cbb49b314c5864e93ef906e00e01a440000eb90000234d2c8800000009ce54790520396e595c000096057280868fad83b23c6e45981841cfe534035b8d97000024085d90b279c8d2d2c9e4c796144105dc78b11942363522a7f9d14696ee54aaa6304d8885e0000218472e03a70f7698c0ba114b40b2c64e0e778c0957c40a815f811eb3f2e4aec679804322e01efca7f1ef80c4014443df0dad364e8b945c4aabf309e439121d9fd723669f78f339ee34c24456cc7e84d905b6274c8fd17eb0a020a789151fa145c23b2468c8482381eaa691f98baf0138661c0ea15e738508c447d398804b5a11c44c4212005366fcc90d05d121ce00007a0086738ae4d001b3087f333e000161a1c950fa26738d8c000000008134353800031e861001d204e300006be45f486c20000acf074702471aba1868d30076020441414818871112de0000be685f644b006f4deea6274ad692c450f9af74082ac448fb163e31e4a63477f0af121c64cbc26e9a9f47be7a2469899f42edc08fcd249e360a5081ed2fb8c1b321673254b21ed951a69c44e18972653f81d1d0701283049a0f74df48f7e431e434876e80003470a99000024623d16000027a14d701e40000abc8000299e0000a1380003a740000515017c00007b0489e11ff07427bcd0749303479a78e81a21ac00e7005d415a124e271c98381e19e0a059a34d8a5b800033
  | 70 => 0xa0d800055de00000001de001cc717ccc9838b0000000070ba0e200005c191e0945f0942420cfcd18cf3a7e2214d0ba2dd55a27c2884c84b703b048e516a130135bea3e44fb2b57347812a4d7102bf3be67d811c509ed07c645bcb1ba78117f00ee40bc08992778708caf300004ac000011c79e1f2f9e0000000000043a497f15e1233e24c4000078da32f000056c80001c600d2e2aad5700335262007e10d029492bfe8f08b06959a02601e255b1129950a27d3cedc1237150293582ec22d94dc00d4909f96c70cc48d61595a9a2000007b8e4987dd3842291c0002c48284075d8b1c14fa3d80495cacb8570258a181110999dd00000000947a1d624641d28b61134843a6000148500000000000093c80003daa713149780c442221484b15a05615feade85fa070b161c0000fc3800043d800003d7800012a01d68f4e00003d1e000157f12302ba418951b5a0d3276880ecc8da30a4326694823c096a440054946f11b5f512839585c41e4d1b92322531baa8f0e320000b4e8f6a229c000127d086640b20000000020254ac4b44f3585fd44346f5cf9f233d0cf6076d2a327ea2dba97e051e03be00001d44ac8085d051258d934b8938000003240d180004bc04e6c000256119fea2e501c9238001c000101a0846259e5b688a5132500005f711e91a625056a7e95b8836422140000000000000000000fc9808046e874443f4104a32c47e485b8800053c286ec000075349b0544809d9fa6000044154cc000000261e4c93980001eba7098c8304bb4d727af42ab98b3544a4a515aca24f3b3427ed30195b14a34a85d60911b4064a9f08812129d03a03f382ff80000be200002a00000083600009d6134126560000918833c06d23cf0bed10253d406080798a653079877043cc27f449605ca08d40e0b30665ef077582c33bac8d30139860811000f84dca93520a2c1f083ab23013ce66e60f90a5673b6e4c7139f0aa8000049d40002c3a3b846985194872c3fe404980000000000000014b4a55b1cf65e302ca0d3a3ec48c94cb889354bfc7d7cdc68bb1175a4904d53a029229a827557f94834eee4750b85050010b03e60d38000033041084fe08adc57b20a2cb680000279ea6c85ee9524345042ac56901d30318984c1c90000408e28d89de800046e600007698000324883dc22180002e4e69c81b1955e07ec116444ea19707aa9b34d0a1cff3ef078f844489b016840ed517b8bed288e0d88c0b9873203859115a40cbc50ea99b45ad979822a0262932fab9c398aa275585a98800009458da18994140860b46b987b8316c6350fc3037510943e389749bce28ec7c0124e17912f1229dd4eb029915662ef4d3508b824ec609d3c416b1000068b12952a3603fa777016e9529377a435497b046530325130096133c000064012f80eb23ba82d114
  | 71 => 0x15b2b1e2c8e8a283bd29b63b3c00002eca031270e2e786b2800000000830000000000008d000001d654a1c55c4e22a588000000011f2253e27ea699cd40800029c49ac553b21a32bee00003efa0cd0000000034a06c800003978000000000000000e24a6c22f92000129f90132ff039f00000baa108e3ebc0000d7f00000000bc3a6410f2000008248000108a151c00009a1102446085e989533b022df47c99f560066000151ba1cc219c103101506903e0e61140440b5c04ecab04b4b89a4101e58786a7a4e040c814f8fff8ebb1930489553ea59513662194000006055c632e89fc17255682957558c83684630474d4c795dd0ff40bb0ed5220f40b600210368a5e425c550482a28dc0ca82035561a2f80ec67cad34485eb21f45ebd27f80001e007b74c6e80003dc8642018b8e850000000096e0ff6521a697d3a713f001f40000000191f00000000d118d1700000000aa3088e233600000001cf3438043f529790a522a855bd2380177205c2fb08ed94eb01282ffc6b60bd7372282b12bc104216f88fe4a1e22af2b60046142b99f54bc8825d38210f90f58a728c770e2d0d2628709e09c2a55742d743191f325142351ca742c0b2b9e000045090d412ba9a8074c8d6b2a9aa608ae6872a442a322156202e732ba2b10429881943e6a26c87b813222ae6b6c261918f094e6bcc9282a243e5093140001c8820de452ce4884f61e4c5ac135593550c422f1cfa80312211291bd1a32a2c44a84d1800028bd000045940dd08794abc0000222000016a61b1c0002c0d06ba538c851888b412c266400005cf1a3432ac62f036e5646a2553569167258c2e8946c132432fc9ff4b8192712a380f80bfe8bc44de60eb54f7a2d308ae33002248e41008e7b6ce82238217f21334a5224e128f6684896c935b3b8614d15fea00632ca68fc17d211c3b0e1d206f2a7f20d662b041b590f00faa329c9a501c82f885a50b01ab660000332857419bd2aba5af0000006f47624a98933a1464f862058533800035d811380ee80003806000046e26574dca0000b350aca47720000b7500ae4688545c91da04321f011804d01cac47f43680ee49ba5455035d4829242245566f595bc294a4d22501c27f9dc542f2858cb3389252e329d2541f08330a56998c00013d731ec000062b020a0cbeabb029922912b1c3e8ca961df725be895860000001592afe80a2a12a1240601c1cb96aa00000000e53a9c61ff85334000255f29406680667163400002694bb00000000073e40001bed17c800000000e1d472a000147b075e49e28cfc61825b837c600000002143070c0000b1d80f000000000b84ab291430000000001e124840000dc4894c530a518c3f2a85d093882d8029862a38ba02c86a523b729241169319a4bf24e0a6280000000450a6c9400000000000407434f001c0
  | 72 => 0x53f25a288d580002594098d1b383da31f68e582af147a0410a4482e598cb08c20ee841a919543faa4d911d04070da006fceb58000116805690ba99f30000a59434d19783e8431b8a580123501c4e78f918e1c33a445e87a4224642ee57b4000010b000091850d586fc2b0c761400018f941184a08022a9d9165ea5d8e1689f4422c5e7097f800000008cdd4729fd600006de461791fc31224f6c828220a2d6800008ba83c02fde75c86ec068209ce311800000000af29d4c656965b416229a80589b0350c0b160c2d1fe33cba361d392a91d4d8e3c781f499cb13b00000ca497ec0000000050b18563d1c59d0400276a1160189c3521a99134e24a12028d573942387d2929556303e73c56169de309306a8c9ff09b602726fad3fb904332cc27594a6963301ca309c7e008db436054a0da41ee64dc27d4c08a277e4f1aa9782baaaa54b0438d466d87742c4e752d05e998054966c5078b0a590f6e000019c00003542000021ca0650616325046c103c142e0000042917b00000e7c000000041f8914800000000000219000006c14aeea1d85faa03d1fde47753cd28310f4a0218029160f41b830800002776159e68cd49a8c7e4e9e8aa40001ed7000000009d9297a179a4ea8dc0a8890874000145d18fa0000a0000001a7704c80874000000000000ce4000000000004728418089012f600014d720690000330c9a5a855519680749af287b250a00000001b921cde000000015800000099400002a436520000a08827e00007f74245000019165f580000049183a6fd4f558000389e774538316fc580223f92e08bb80e38472023aabef240400015629462498c12d06430000176a98581c700003a489f5489da2ba0710490cc8280000e080001453aa095378869c000083657d2000000008cd0000038800027bf58720e5553480000000246127eaa8b24ba82a92091f5d46ca010957490cd49e633445f992ee00a025185780d0e14f6851489c885c14842e7414624214cd020f8699a4fc4626634800011ef2b685c312e68edf42da193525b9ac457b874a92e1187d02f44f400000d7154329d04c6509b23bda1bc12d8919e3f04aa3056ca49543be00f41fa1a481f7e1cecc6c9af51b3a4c147a59f9553ba36d113107a1209a0c88c6d16043f3088c81e695df551a4898e5e123305528b488a62147437e51200000ec44ecc2d644e319f230da24f4ea11ef123924848cad850b0000652d1df9c7209b439445e31a40267c0bd818a8ac5033021a0685a0621dda6c194bf0385368287a05088a431c6000000002a73044000015661cb944e000012e180002de620f008e15420ca20000ca9000024480000fde8be5508e00000000000558e00004e50000414800000002768289a44e8000028f00004e586050000546287c849ca2c22e5e65b400013321eb80000
  | 73 => 0x524b94640aca94304600c8c58aa6c404f78c7b3d6600011ab25984a822698110a131547e415d4fc0e9c2d9808ac67625453b6a2a4447ea3f818ba00000001a1a179c5900633000009f603b8a1f00000cb00b6000a07db129a0be48a2800000003b5945f8c5a00003c3943208f05792039150880004e42000027300001496add10b98b6d4e1447f5443199900002928b909e1644ea0b25236979d03feb090f4200000000000121c8000292a82ac0000ea900000fe02dc2a0c4ec47c889fc898f13d639cc000158500000000fdfa7d8486cadc8b74a7842ec4000000015da55fa8d710b502c2000000010c028a435da4ff083502fb00007a7800022b100007bd49d716bf00000000970230320069dac98f988f3c84ae9562a201c1ca4a4b0000000000003d5424300000ff68eace3c29b52812828483804f0126499902049a031eda64f00ae8c6b03e2af511b9149f3c80000077c1660478c99e91b52b073fe8000000b8fa412b66934000000049b808c0c76a0122a7436b15dd027a1e06000054123a43e2438a4e5826604132314cbc900001f8c4ebc39e9ff656ce48f40000f333578147544e153710d6469063d06064f2044c906326ca1568352d4f101730a528d4549390390200216484d8a5f1f4ca96000010020000a47c0000897087a0000e81a3120000813ca130000114622bca93a5b61e566c152c9a5df226085ac4280c912f700000d8e01ac268ea964a6ca6212bb85b810e399b606b200000000000430c9dec8741bb40000000000017704dcc43105a5a74c39ac9b642d424b200008e80d3d800046544a69010aa30128200010b31e5030d40000000000026840c2410199e841e000005a400df0000377107a0e961f2c977400011813b4a4bc40000cee00009bf87022c2f4edc0000d52800051048cac69317d00000646129e977d00000000c3d1a830000ab70c5000000000000000000004ff442f8e281046374089d855800002646a4e000028233ca63af4000000000009c2141b28d10e8238ac92da4b81e921e0558e990329b8000117527a0570616b44262392376ea48135810ca4c16674c755999a395ca32878809ba56d41f58000177f0000298400008de509c97944048000368479948988c9e0d9a4bf14378873035a0520046014034b6354087e09011e82170ce36a48b29ee07b09d8106c457e62b88a9887b1f363858cae144433c269f400000000c845f9d1ed29394e389a600000ae5528481f417400003d8c06d018898dc4d4e9d8c0271655339851cce0daba1175ca0f4bada9e304de5a40dca230031481648afc02e300006f8800000000000a12c0001c0a000015801c48000000082485ff1d3c00000404e08a19529d80000baa175811d88228c5c1a022cda9b701d49b6a1fbe8f2048b117c1e6a5f4400007793a5800000001794
  | 74 => 0x335600014d5a7301c2aaf60000000000009348f4d11cf21166694673066c000000006978ada257c7e0d13289ad321e4a4c60c24aa0f468034db094be000026a85340419013e70fc00000004bb600015be800051200000861800052a20000ba603740000000000007d7000020f547ba6652dc26c5cc1e8b6e3a024058a9b173d0b0a3ab83ce14f41dc05f14000285215006e153a88f6916445d14000000000000000000000006e400002b1800000004c8819b060a1ce2000109d0ce7034000000000000070e00002748c330ac4000154a15fc3b787d792ab15094518a7789470b1500000aec26e0f4e475a312117128cc000063c41ee16832204603078e051721c45d78c999ac647129cac2e0981b32d678d4621231b4fd0340837d270f3a9477d02a6055a49b20000fc795c000004b20af115553c4400000002b3b53ea97d400000002d0000000000c9b153079480000000552a820c00000000a7e00004649ad410b400012c3a733337e7a9917d1c94085c20840000000571800001e9289a4be4ac9800013a208645a68abd00001c8e2350cf78834000054540000f0f2c0e64dc9d5915e02da41a13c5261d3bb492d4e7398a51af27c50a17ac151a6e08c498889ce32b0516ce8e10762a86075c00fa1423bf8afa8c0099173cc21f38abe97125436275547f9da032644d7ccf59695281000014a41a8c450c9928b1a8a0e00fe8fa80680b2851e89cd8e291ae5226695113460b110b1a55e06ec800023580888d5f252140d8acf80001461094600004e800002b9400006c11530074000006780000128e0f3c9ae21b60000000028c000000000000000000000000000430002600000000ff5800056ea3510000009900000294000000010a85f0130d8000019e0000ac904122564078c00022d5507200000000adb0b30588d11a29b34deea1f82041ab62ca83ba40001f2f37ce7c6823485044d966cc8c7b8fe400000949272884310f486e000012dd1c8a7c311d78fab4ae6000000025360000000000003003fda000100b00000068a80c000000000005c7c000286b00000000000000045b40ba42e3a3a3413400010898553000077a4cba000000001bb8000000034161d9546a8000103a15a8f6927e10000a19d2aaab6347346bec9609651389a471055d1deb5886754cf37264e113e0001028981d0c0468e4cdc9f2600004cfd46305684f42583101d1876201a000000006b8000093e120e22ed092c8d7910608ed027c581801929c10000992cc45867d020e2b8942c2a6e4224816000026190708a7906d397ac137690240001ab357aa000000010184f8200011a98db328922d902c82b5450cc5ea42f8000016622a180fd98051c302374000264f176c13f960506bf2f600000bb600bd0b161478cb60d2b19c83808fdd98c455a602c01170411396a1fc
  | 75 => 0xb845e8c0b331400000828fe14f908d80b3300510a34659102280000c1800000001d4c2e28618800000003d5e27052650000096600000001ae70bda12e09071f9e000083bc00029d53418a71031480000000774048b800040c604754c92af00000000107c000000000000bda22ef0f906fe4b87a57d311a0000659000049fc8cc45a813982be80001347980200007d50000000058b42c983b90ae442fc6751627866f139020c48301757163ca84cc31852225a025c0000000007a08b2c18c168d04d000a00001053491e0000d0416a814287734d57000000005b3d5f210900000109400014172f362678125923a35740bcc1208703469a03fc68a9c9f1c18801d4dca2812da4677cd6299a326c2523c1af25d630bc4f991bd265250b649a077909892d4a9cc40000000122622214c38000000004a800000003fbe0000000260417767ea400024d101b80000e3a8000329e5a1490797904e0029ac00003603cae000026a0ba842606fc8d3488b919a4aa1074f965f52a62ce800002a526404ee85d980000000887916b9442000022c55c589d74bce56040000061009e76e952a000000003cd83bc0000000091c800013902550a5690610000572449554ca02750000a94c000049a4bde52452c59d930000000000000000158000162909e10000000114d8ff40000670d1742a460000289d0f3a39b25a80000e999e1056004ce000017e254ae51d0778943231442cfd09300004fca00000000000257e0fdd2ca0ab6399aad5930f17a049480000ea2a0752c225f6c75601a612287f540000000580043b00001e91497c4130b3e275704dc547c7b2ac47000028d473a986400007e88e158dff481a829471428c5229ea888000000034ae95f09caa41f2a46792c7db1e171cce86cca442b08576097ec8909d1a253025682c709af2cf24da4ff791d02a6a00004be1cf24f6c58095da0e334e70068800024991efa33c4c5518300000a9b400008c30d1218a1324929f47b8a29855d888f465c0e0508f138d556a32051f18000362c0000000000023401b4c00008782a04a92483e198c14da6da1068098c058c402000011cc22080684aff00922dfeb164bb58e20013488e509f0000052e376c0002b7029b0745c4e1068334ac8e1c63504d50000a18800010913eae64d44628e034da685d134d10660b3a54ec0000000054630888e0a3e9334c973d3c280002d5e7ee05c1267223c85dd837b20d50b6ea8a000000000000000016b000000000001349000000f29108adb178200000000d65a4960f0c00003e2200b00001958ecaa1c41d0e97651842590000000010d481f915ec2288f9aa7f636ca1c614aa97ff27226530f3a80003fbc5538fa7020045601f702ef97404a983a5d2d4abfc000060400001d710a96190cd66000031760000000196f1b701e0d19e000
  | 76 => 0x5a16a200005bfa4d443a200000000000163636e93f1a73c00006aa80000b34310c0c7147e26aa091ea3744a429ea000023a4000281a554214cc5242c0723a486bd26a80000000720cddf0000064244d13de91af13e061bd6021f362c384c38000120b034e9d0c37a00002c5c000000000001c0e00000001ec300000000cbb81c711563434af99faa09b6a3908288fda000000000000e2c281808f02b98a9b3b5c9bc40000000000000011c81e4e559c00005c72433439037381b99bb13aa470100001813260c8ef000004953ca8691ce4299f647f8000140823cf207ca7dc2f927b34168a770c761e490cf22f28dde1eee33b6a33d42201443ea43fd56040a4645782d584df26ea3ac872ac7840e614dd23a48c588d6839b2a4380bd9c6b220c69c45bc176d3ce483c494b1fdb0284105093b86f840440d7147719570000a3992ea883902e0a7004059bec00001d750c2237c23ac27b0a6aa31c55841fdc32596322e7618c05a901b6519a64c01b385e5026894602d922792d9012c4f34091035ac48d0c1c0fde341a9614abf0000533a000157522eb2b5a0d60000100b54fca21102ba85900004458000000017aa000158d0e880000b0b06d7a3c0157c458000000004f5868447d504e12b7e23e40001e1e44668e4c00011c51a364220499a48a331206c4803a0d248fc000108698fc1880a9dc000084f3f3a07c0f7e8ef62832286466a06b204880fc455c80000db80000ee018f00b94ab000000000551093ec6af11142fe6a981326237818fa477803c047425caa22ce54962f5342003096b9ba932e411a000024ef098a0000fbd800035fc0000cb40eb3459e78f14649284355e7194cc725ee0000a584000000004a20d0c0000fcb2128aaa0bdd0fbb32f206a121396423886968452e061310223ac0a3b84e848fa8784d922a832ac46dc90799737286805ac1ada58350e870510689b75477c9230592873235a2b138a518285188e55a0aaf90de110c00445cd95ec440629d5340a6771fd22a4037506fb366050780cd94f1163e0bbd4fd81e54eb055405c89af623306d1812b058147aca098f2f9c353ed20ded6128908450e00002168a7400002dd075302e21620a07476182b5383ea1e06740000222a4b680001d7a408476700000000000000000f78000083436990120e900000379139e8d4200002c345ce1b8b2ac00001227844836a6a3851b6906b2970acd52200266000027c4db480000004427450d23ec18aa522813e2bd257e40da850585dc0aba65511ff0de1109ab0811118a58542c01ecc5a80001e4600004b21f1537be2068c71075012ce85c502624902dd8941024b9d190ef679a43320f9c3da60cdc2ab0ccd519c7f6866b81af10e81d2490802340c2a4a71558000000009080a8d9e5840d627e000000000f829e1800022aa00003c
  | 77 => 0x690ba891ae0f347bfc000206e3ab600005cbaa9f000047d4a578000000000010cf000015287921138800029762f7d3ac8000000080cc9e88985283a09dc00023640000000109b162200007f3899d1a094692a0e00e7800055667bac42480001c1a8cc13ca009304d2000000000004a6225655bf000025ea93c0d2980003c4e0bd501c04aa3a7230b83d595db5674ac2554ba1da27329facc5f846b45343e3525a18323f9660c4438027221b8403811c1b01165a6508421066d42585d20c150b6308f28984e220aeb090e4b855be1ada56f6827066b102c105a2430c13232c1f624c585a624ce1eea8ff456f1f2e20fa833ce1908b5463c0188568828a39ca56510708da1037228bcdd3a2c102d0821105babd1279c314129da34b32260ba92da90c6000061409dd800010d447380c51e66540a783c51006ed3a2c5cd83d38fd000000a48000026b3c48808153606871dfe6a50612aa7b51905fc8a2014143092063d519800058703410e270a7328860c6800011934eca1098add84f55804755942301622ace91ad2a898c139e800002ba00003ac2826cbea27553ff42de52b18ea350665be0a1eaa4a2b9673d4496a5f12ac2000138d81ca39762a2c0000c173b9885555391a2e015a17d10bd80001d2646f40000840000000e400016f2000000000000f594f300000c9500000000466907206a9192a936c4f900005654425c46500000e40712072d8000000031d842b00000000a3a53ad1d210bae6818caf00004fb200005b513ca00000298d7213353ce06ad451a0000000000014738f9a3c940000f752aa747c09c8951f0571000c000000000001e165f2c47f8d351642000044993310000a9d466319aa000099740000b060000000161199944234872c987a55c354c1d2c2b719630a5400002ef01952f90acc876598545838984542811991dae0000f3e80002eee8d546c70cb00000375d1b60d5900007620c569b094eb600007369315134483eca692165087c00000000b811f5cabf04e893b100003db0c4500004d3ea4c491e1c39170c6cb546c876b2f766d580000000000092ccff11882000004e80001110003c072c713128b2fb05d58000000000004c08390815116722aa4dce80000d860ef400011f04b7e97e800006603600acd0000046d1b8c91f1377aaf50d50878d1e58d984a5c9e7800023d7276a38f4217aaac433a6d8c9c12b4d24e4a800ebc904f560c0f215681c7147e2594950391b83e1247b54ca95454510687010c0d7b3c0072bc4daa3e1063cafb000b2a7c146421dd490899f1c3603a8419010226e61a04e341dcb0e52a13535d98cc32d23b6c5511f434c7a0858cd723144c7616bc30284281b78af2c57c1ead2ecc000042aa399570ea72400028f53b9cb0a09f423ed2e58006541d25af336233804f20110556e417005d0d
  | 78 => 0x345226c36587f40f7224509e583aa019d117488b9059293e16c000000001a4b00009908a53000021dc5f7d0ca000027485c395c8282e00001b48000008d3b880001447a6b51dd8000000024014a3e2528b18836d17600000205a8ab1fb29c1d24409680000000104a0ca420f6a780eb4a9f32980a0d45c00a293afc7ee49379ac305c222945f0290300005194e6418af564e9afd30525e6528e6ce4cf180d51ce06e5902d28d02ef86780799000036ba90fd0d10e1a44b64f480000d891e440000c591ef912002bcc3c7921e47ec0000082130a18640dd8b34a0c94f2a701c02d154c552c1ef40690a6947a669f08450626464836c08cba2be10a45c2c2d229a63e5a6ee0d9623593bcc0a5926f001b46080700504a83c47ca87c49579dbd1aa451f4457068814f84a247fb88f124f84870d1f207a255cadb42612b1b029293b161999144a10515d3b817551b7aaab4bf4975d156a9c90d0984462a1a25d8ea0242b3bfa4a1ca3682c512da03dd27425a43a765d4c04803c92df231b101292b8297a2e48bf8a60f2fcc1fe093d108c3a56a69d1e3ac0c52acb12c0329bad52323d5c6ba0af74cb611c0d4d148c46428f115bb2be53a1a77284179b6f026a74bd35920891ea417595d408df4e2a991536d0635049811dc09117d33a4a3b186dc94590d1696d075394cb3dc0a76092e294e318003cc002007738d237787ca22ad4e462dbd30c27163e8e35a84ec981e243a1e78e8f1dab120c9d5871b8a6c0ec4ab74f7684c93820000004b00c30e6827a0207290552ae28b86e819a127ca8798fb91b8e3b28a9fcd6b95a3347698a09c01cb13d243a2ce7628070f50023d1918ceb3d1a755496d858a52ce10344bc2ad80ebe278c2db066b0c123b70bf08d40418a2db0d5617462d701381151890a3d6080995c1000024f68b814a624a030aa0000a5e2b65448a4b7848a800034bc30fcb2316b3290a18ac8311ecb1c909984eee90e01c1e000129ba8fe4424ae2813510cc46041b303dd136a14ba0000a4499af1ee6112800029ba4cde000000000eb165860a541a201a147000008819a424bc4537c40f297f000041e0e1600002452633429e285c495e972495a8f5406a85c90fb98000000000004ca92f3405c60912539cc621e800000001b2200006854000102657be4dc400000463a1e918c00020d949ae208c00016142f4e000000003f248be87f0f6d0c1955ce00000000000182a5cc46b2215200000000e680000348800002de000018980000000000022be34e14980a390eb200004cd0b453a4619a562528711e6e84007cfa978000055b44b28246066095644e189b40bce749936b000032ec266c0242485458a00015fda63f42329414884a6bd380291a400024ad22fe915c4c68bfa04a8231958097332f2c077ca3e227b0c066d3cf831aca17683
  | 79 => 0xaa2869480000a4e00007ab1f7a1b324b9d43696d538ec000000005192fea0b70f40000057885d8c00011254ff80000ed1258d3fd4131c4409386000000007f90ef028660000c7280000000303127226445202419d0da98c9153c85752c217c24e409ab900aa8a035681ac465e8f3b34c81b6cf9389fe30ba47846ad8b8337c09fd41f727971e409be4964aa4f157aa2b8a8322d048345ef459597bf161243741df80b84d9e067c070815402bc9ee87c522414458437c1ea22e4515e6a10adc1f043ff6230863025540000a91400000004846af289062a2614b60000e88004a3a5ca3a0b9500001b5221c43812580100e6c4c0b60179516a4000fc89861320e7a8c1a0934d1c4a39a448e07a43f74b0580002b800000ae98000270912fc8a7cee3ab02278604180002b8904e8000099e86e90ee02a7120b91280ad6a808a8788ac01e264f4339896346cc90a478bab6956869698384a1ef0d74a9389529c7e01b6134c05e1c4a37f671c11c680cb4f722e69112a65e47a876909c90430421875f40b02b9e212c238482a94ce312a1adc0dc08940bd00000e03000022ee000133127730d7828ccb04130b3930a2c80370bd118e091cc49d99601e04348c15502982b1e1040867923655643b900001b0a1cba388800028022cb29b7400000ed27505460bbd000042ce000000004cb36320000d231af200006f6916c00002b12000000005d011de082cd2c80001222000005b243c0b4c9834b3f814624cc9b6d2b40000000079e0817803048700000f2c8000445e00004950c6f3fe679f0ac6936f265a6a20b8b814744d854fca9997f605e002a4efd9d314ad8529c000018011e83cc136095d12bae574d328818600008580ca2800003d06fa807a282141cc2138e56975f1fe600000000000130441e8000292b0e620000a8214971fd8aca0000297345bcaff93fc9bb3568033700000cb311ae98800000000000048bc66e85ab00002478b91000020e80000a4a1cca27ee6814e718bd9211e0a0d52380004a9a5f3024d80fc521e8d84dea0000000097acb7d80004408ad78557a1210dc2ac380001041568cb0989be8c9f399c2cf85841ad246ba6ba1236215913a81cc09ba1ff534a0749c25e26fd14ec4e0c5f902581afc103d1e50cc7101845f51869149000090b88d09313019a60eceb40dab01f26a38000000003ea723d071a6f54a2e9e6c5739c0d5084ad2c7bc81ed553c6f302918fcd206c117000580002cec876ce502b9f369280f08608e4332ce5c74fb80c90138e05c49309bc83cc400006d1000005260000c6a8000000000009360fd218702734fe406370000047c689000020b28928de6966f000098d9579857c579c28c4fb2a705000031e096b12e639be1c3c0ba1fc20000000160727ef4c4a268cc0787102e7075dc41602b30000000150d1
  | 80 => 0x1b7403129de8a77a65c22843d0d25e832d19088e9c89c236e00005bb509e856d285c3a8000029a8480c00011f9250f000037ec0001cb2307e4b1d4e29eb8189a85d885a94b207fa728c64007a62bb296a0f408653157e77d4bcf8464555475894a81eb6223e247ca42073e500645f819028ac06b46564671148e52ba8c408f116053b3e74508499d5e005e9ba03c416de3bca94a4a4f1afc48ee7504e7eac4d194a1424f098d410f96ae3517e9c74386800014cd0b072b6e7454c20ab7f3a26ad1c6019e380c285c0464c9cda4c105bf8aada20113161f344c323d8182c57f55079b80483a2b08fd213040b42260d2941dd94b4e6df11531020488a2c495b417ea2c2c429c2051a552a0e4521538054855b485507189223313a301072f8abc0a6090388a1887c28e23dfd0a61c5e53fc6a8929a247852d8379804587ae430e0000000170d152a7cd0010000039c4b1148569d90105087b48a3111b4558333cd4b92013c343ad0fa69032556c2464fd815e45852667896692484b7c7c4c5b989cf19f82bc85751a6500b06858000000030981bb00001cfa20c2000000000000000a600fa280000000000124c000000003164f4b26763c88374c2aa1c3c4e1c9da4a2d11a726c48ced505000049528028b7a0a0800000000000007c57368c381a2a3164be897613a20c2c39826898a72000000005a90773a49b57dc084132b012b2618a3bd2739b4a00000000000068f4d8c351800000002e8821b82d890b002aa5bdd5e3961a04c40c6ce8901be1ed00fa01471d0723f0ab24b09a2772dcc57043fe93f1024aa4080001b824fb67f700f58799162e17bc3602105473c1b7cfe387760000491ca7309924f162ae0daa96e338a249652471ab208de46a5159980907fe117d2411cfb276e734c7be023d48963f3d110111e0dcc9a0c6f5837803609ca00ab8ce311a4617c0002b12587826f467c8b364a2069ace0280004b98000000000005748ab202f20000476a6bfd1c6000035c67eb4bd9a1fb0d3e651c128101a032e00007ba091a1bba1f9079212453a9aa9a8eef293b415200014a22c32000014dc00000002ba8a30d08a2c3617309f19087a9740000000122d149a3b62793c26727892386a2d000009df22ec04e0bd1ab530fc0733ca631540022421b474a9b200d56ad6c3fc90f62f5c8cc889680005628681c5779e1d17fa75cc38680002c247d68df41bb545006250b4e1d8c2cf04a3000026d857762d007072132376ca9e113320142a16169438d8ca025482a489bf994421d44ea4fd180001b3e6b2000026400dee5a64175a77535d42b18d0f85b3000077b80000a6535404d74894a79c382c22ed13d028d219656900e20f6b1b3c01a912e81b31fe211349d0814d40ee135c98a226d4498a85158a848b1b82758042f8c3e1cc88f880639e64248c
  | 81 => 0x800012748ffd3dd20000000126d0de60000840a78e358402905b42385454227a4ccea80839382cb82fca91823640000d9b20672f16aecd030a0bb48f67684e20abd6072c624c4f2a1a4238c0abc37f927e2c1437553a5047a29e6853933a1f4856f2037926395eb318e34b0715067119049bb04128d4c2f7c04a4ef3a8db4b8873447ff8f3f502aa1dce53232727925e542a18c36171e26e14190820172652a42198733197c9cd53d580270cee3701097a4ae114c2638c3e0d2704b43b40e2c8a2c050c8ee94c81d3d1f7aa22156da02f12123ec8e0e0e3a4d00a3c0471a162176ea6bc5500ae33fb2759ceea866a338e4c1c1ff12f91436af3467097802ba0900c54f9bcf462aa15943e02fe09007b78f209c20548685701679dbe00000001458a97725a6292487aa59d0000000050529cd493c0000308a42628c00000c232341236e000000022631580513c201a7dd5028a288de80d1d28d89300278939304fa2560b7402df0c3e29115790000169a00000001630000087281998e72408855c8ce214cc00009f2c08495ce43c053fcf6628220000000080f1add1b1882f80000206000050b162091790b5c0000e8f84f8008812d85330000000059200000efd4304000035b00000c9200001cd9a3521b20de8000168f1f0e2f204f700bf00b887f8efca0ee384876440000bcf00009e3d2cc875c4e0200000001ec823ee32c400009841dc4726c0001ee5424e0000117a84c46d04f50dfe1ab1146e40447c1960000004cb80000b1326e013b50a02023423e00006841f8c406495e4e460f81000061dc0000c3500008a10dcfa4cf0dc4130119329100dc88234c6d8c440000344c2c19151567090bce4516a044e435702b793f2049425c832e800037bc00014c9a70d133a9d18000000037a4aa148cf8000000000000001ed62a9e23109b59c80027e62e4e2a9a10446e7c5ccd1004d4702aeb445902b7000000000000000000069bc000192230b85609121211d0000722d4cb104e3f50142817e8fd500009e301d5aa890000a24c00000002d187808000244708f82e54fa5927d0c587980cb5137e291a5a2111f8b4909bc00004e00e6623e20000d6e0d3f0000a76c182090b00000718d000a28154c894c0920000000000000000000082c7a74c5e00001d9c0000000000034601454000184a4d6e0000e0b8e9e24a453442eea8a9078233d800000002cc80c9000012e21c92169d5fb800000000000ff8008e14de3c94af18a3f060e000000000000cd077c80000cb643b25e3481d12065226451000000002cbc00008e3a9bf0000000128ea0d600007af8f1f8000107e00000000e6500002cf40001dd300007e9cb7a8ace1ecc478c97d800049583d280a580000e1c55a54401f0e00000000bdb8c391426226000027c0000024d14089b711862ac3ca35
  | 82 => 0x40cae000090c44828f80317c674008683db00002fec00010c500002cc907d262300001b6400010ef383c1f853ae0b584c9a9bb440b97c62f8e59ecc471c3e207a6be085b97080c987cf00000e6a049249a4946a115038483a031200c11c0a798d59f8e2f3394a5d46fb159d4ae038ec86016fa00003e45601a8684f649274d9d1a2935bc22d800016ab240eaf6870f000028de0000ff701632e0a57803b88000005c86e53fda632000076a4800801d2b26194000020f90a1a3ca885ca1b10a0e19f000026a641ce161c020174a4e967ed853c245305ee2bb4ea300004598107c0de0bf145be04b46d7006c0a58a7c52b32ba9362a5890acc8fa547e037e8b1e9006042ea3a9586879b1fd456a94f7084453ae7d608d5000029a8688520507ec00000000e2d04c100004f1928916c645b647a800019de555600010d0894541306734c749ac139da07d928ca00f3d32ad395cc84cf0d002254e4399162b2c42e8ed807e73142624133e16a24ffea09ccd229462d825b108df25f352be7a08000000019be000087922c300000001260800054a442d0bb525ac3ab0000101f1c4709e40d087b8a2fb36a2000068f000000003034628898006180035317a9bd56a463084ee865917827f407e389771f9844ad41ba8241d5427e956a945e0000000089b9e2000006434f68a109544e12c0303a07900009ebc2bb80000808a9954a7ab5a452807e8b6e17650f8c398c4f314ab1fa600014e102b103349f5d42785c94bfaa8c847105fb17a87544f0400000000528953099ea0000000156c80000ae40000a03027b3c2299655f30644202e5b64cfd0fe728544648d1b914740bc00000000912057c762523300fe0f2c1ff95500000375c00012f18c8e14460420f54000000007d9912e1ad34530009400006574ac8000070912584634586076114b53a6e12b400000000000989800000000000139149206eb18563f5c31c82842d04571d0c89f94000002f8c8503aa080000000001f6f31d681cc41c11e013d40e304288d8f0d0a21b02030c43431a8cd479ca7aa060634f837780002a9264d0000245007d47cf43f18d3d000019d4db39f3b45447e80f4827f83146000061e8000000000000000000000000015a4844c19526d64709a5a52c5a4029008a2a400008e70000058000000000000112033b0a6795b2219800000000c09205544d20de400013890aa0227800018d000007428897a4480000000000000000af400011cc27e70b2e6864687894e4480aabcf02a4cc01023330cd4ab950fd43eb103b0cd31ef00000fc69ba230d25af51b80ebe382465411e1801824a22ef87b205e9386612955330c7c56ba0000811800038dc46f066ca37f3e927e2cc1b1b2a51800798692068c51ae6e65123ab842f261e0029aa94547662788fba1c8900000000cea8bb2305
  | 83 => 0xca5934859000000009c0c9658000000000003e7800053da00006751bd30bdca5f440100001a22aa4d44f0a840b1238d8a169e9357c069e509686af28a000005a52717406a00003c60e83000031a03c691cb1bda35bd32828693d62940cfcd8c06000000010b70df40000000110dab1649008658d8ea71407da7354ce020300000881808b9e76249289e10532b36141e716c473164e390259b8d7018233dc485f13512af11b904b8caea971a254e10d423d853b4a38920445f8ed527f46220570a0b90d4234183a905061a2c741447705242524753cc8f09c42b98258959c855c2138000074a15bd443e14e4d1d0943063e37480000936014272f546918e7287055acc3c8dd40afc23202a8ab6c069065848028012348244b91f7920a4a14083d17a05b519905709343a5ec48045ab41609d224b900318af825bd3ed49fb4df2871410280b4c6611a010000accd17a8d6728b80260bea8a2654b43934ecca0872fae844007aa57b4aca4a89232ab8e2a34511800028832e6091e8a081d8e23cc360c9301ce83a9c03eceef93b82ff82e589f70000576c6320fd29c00361a07640000000000016e8e0590bf2bac3ba87cb9d281e24000085b286c24327b08d25110b42360ebcaad23792c423480e5a01ae15101f78068ab5157f06fc05c39191154a85b01cc1da81edcaef961f0000000030d0a56110844fa4a8cf679e71281c000042400004454a0a400005f300007e200000ab2486a51ace311711401c30b45261a7e3042ac415d1a53a48d42bed2ee13bf05ae88f80001e284ec26ce11372b221e7a38c84378000237481c430e946e3bfe6b24da693f3253c366c50283474d2625083ac054e372e0000a8b1308375e5594b5718341e8a809cb1500004c7c000122f197a19448d500000000396683d425580001da41ff0459800006a2afc49cb89b73dfc0001424800000000000305a67d0000af30af78e2414c40000f1a02672d4e3cbcda92a2f1d3a00002f50000000000000000000000000001aa80001b0c37340001e01000087e4000281e0fd6612043a80000c305b88c0e2434042a19f87a6000043c492f15549dac36220bd0f9f8bef11961c7d422899329ce96289ba8d0c3b06771847d1875521044446b809db230e0000ef7800020281f007e4103432b4885000019e44404b1193e802cb00000000380800036c82e7c0002be300009e748ae1a20000000000001a7a277200000000e21035610052e70000540c6055176117802401a5883b9b88000028912a8216f11f6053ccfea6290000b025537ab4c5360029d1d528e31b349bb8bb40000554c1c78904259616d2144cf0a0a122d58732ce8105880ce4a45c269073a499250a0fb18e3c447831dc831849f000043ccdb32309000090e82211b0f00004a455668aad1f3255ed0f5267133586e3d5c
  | 84 => 0xfd142f40001150037d156200009ea900c52c006400000708434c985ce6617e4243e6c2d50e2bb231de916d5fa067443b00000f6a06d501d80e94fcc8bac3a1c2bf8b319e45013c0000a90800024ca000000000000000059c000000018
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x843f76552300421ebb2a918021471cd548c010a38e8a9c600851f7510e300428eba88718021395ca618c0108eee3b2a600843e76951300421e3b4a8980210f9d9544c010878ecaa2600862e54d893004316aa6c4980218b950624c010c5aa8312600863654d85300431aaa6c2980218d950614c010c6aa830a600843e74994300421eba4ca180210f9d0650c01087ae8328600846e721943004236b90ca18021471cd540c010a38e8a98600851f7510c300428eba886180218d552610c010c6aa8b08600863965950300431cb2aa818021661cd540c0108f6eca9860085687254c30042cc3a2a6180214e5d6430c010c72cb218600859a7390c300429cba886180218e594430c010b36ea218600871a7510c30042ccba88618021c65d4430c010e34ca21860087196510c30043c9b888618021e41c4430c010e3087290600847976148300438c218a418021e410e610c0108f6eab08600879043584300438c21ca2180215a9ca510c010f2087a0860084f17610430043c821882180219c597310c010f20879886008571750c43004338b286218021e410c310c010bc2e418860084f17688430042b8bac42180219c596210c010f208710860086716548430042e839a4218021e410d210c010ec0a4908600847571597200431b2a4c3900218d55261c8010c6ca8b0e400863554587200431aaa4c3100219954a6188010c6aa8b0c400843e74d94200421eba6ca100210f9d2650801087ae9328400843e74194200421eba0ca10021179cc65080108bae6328400843d75990200421fbaac8100210fdda540801087aed2a0400843f76550200421ebb2a810021991952108010e52a8900400862e5498b1004316aa4c5880218b95162c4010c5aa8b162008475751931004272b90c9880211d5d463c40109cae431e20085357510f100434b31887880211d5d762c4010ccacb31620086656558b10043532a2c588021a955162c4010d4c86b1620086a44358b100436931e6188021b858b30c4010f208618620086e1620c3100423abb4a308021595ca5184010c72cb2a4200863965552100423cba8c7080218e5964384010a72ea21c20086396510e100423cbb4a308021785ca5184010da4c798c20085e1720c6100423abacc8880218dd965444010c6ecaaa220084757598d100431bb2c86880214d5d44344010c6eca21a20086946310d100423bbaac4880212d1d162440109a8e6b1220084e572d8110042783b28088021ac1914044010ba0e6a0220085e072501100436831e6088021e410c30440109e4ed90220085b1740811004370b1040880218ed965444010c76caaa220084797598d100431db2c86880214e5d44344010c76ca21a20086986310d100423d3b4a288021789ca51440109e4ed20a20086d063cc510042f139062880213c9d82144010
  | 1 => 0x31043172a6c4988218b553624c410c5ca8312620862d54189310431d2a6c0988218e553604c4108dce5b28620846d72d9431043172a4c4188218b552620c410c5ca8b10620862d54588310432729ac4188219354d620c410c72a9300620863954580310423aba8c818821395c8640c4109e2e032062084777654c31042b2392a618821c5951530c410a6aeb21862086356590c310429aba886188218d594430c410e2aa62186208665659883104332b2ac41882199dd5620c410cc8eab1062086a6545883104352aa2c41882199d4d620c410d8ca6b106208665535883104362a9ac418821a990d620c410d4886b106208475769483104332b14a4188211d5d8520c410aaae62906208665621483104370b14c0188211ddd5600c410dc4c4b00620854d7314b210431caa4c1108218e55160884108eaea32442084f170192210423aba8c7108213c5c063884108eaeda9c42084777654e21042b2392a7108214d5d64388410c6acb21c42085357510e210431ab288710821555cc5288410e8aa79944208565750ca210423bbaac1108213cdd56088410ce6eab0442086b2545822104358aa2c1108213c1cd6088410d6486b0442086b04358221042b338ea4908211b9d85248410a9ae62924208475759912104278b80c8908218dd9554484108eceda9a42084747654d21042b2392a6908214d5d64348410a6aea21a42086946310d21042f1386a4908211d9d85248410aaae629242084e67614921043932a0a490821c95505248410b8ae629242085667614921043333b0a490821c99d05248410e4ae829242087467314921042b2b98a490821d15cc5248410a8ae62924208666631492104332318a490821c990c5248410e488629242085667014921043b1380a490821399da3248410ac8eb19242085e2708c921042723b26490821591d53248410e8aa699242085e0704c92104237bb2a410821595c55208410e4ca8908420872554484210437090cc0108210fdd16394010878e8b1ca008565720c6500433331243280218d59741d0010c6aa8b0c800847771d95400430f2a6c6a0021875536350010c3ca831a800861d5418d40043172a6c4a00218b5536250010c5ca8312800862d54189400431b2a6c2a00218d5536150010c6ca830a800863554185400431bb2e82a0021a518f41500108dce5b28800846d72d94400431b2a2c2200218e5954010010b30e6a0080086b161500400431cb2aa9980215a1c953cc010a72eb21e60085397510f30042acb98a5980215c5d761cc010bc2e430e60084797694730042b5394a3980213c9d841cc010ae2ea18e60085e1720c730042793b443980215c5d621cc010ec0a490e600843e74d96300421eba6cb180211b9cb658c0108dae5b2c600843d75992300421fbaac9180210fdda548c01087aed2a460
  | 2 => 0x86290218798c4314810c3ac6218a40864d63988520432ab1cc2290211d9c465d08108f4e032e840845e73196420422eb98cb210211d5d661908109e2e130c840863554586420422fb9acaa1021171cd6550810c6aa9b0a840847575185420431aaa0c2a10218e55360508108f2ea302840863954181420422f398ca21021175cc65108108eaeb308840863654584420423cbacc0210218e951601081087ce932e640843d74997320421f3a0cb990210f5d065cc810a98e4a9e640854d7314b320421f3a6cb190210f5d3658c81087ce932c640843d74996320421f3a0cb190210f5d0658c81087aeb324640843f75592320421fbb4a9190210f5da548c81087eecaa4640843d76552320428e39aa9190211d5d6618c8108f2eb304640843e74995320421eba4ca990211d9c6654c8108f4e132a640843f74595320421e3a2ca990211bdc9654c8108eee2b2a640847b70595320421f3a0ca990210f5d0654c81087aebb22640843d75191320421f3b4a8990210f1da544c81087cecaa2640843c7655132042373b4a4990218d953614c810c6aa9b0a640847575185320431b2a0c2990218d550614c810caca630a6408666521853204332a90c2990218e953604c810c72a9b02640847975181320431d2a0c0990218e550604c810cb4a6302640866a521813204334a90c0990210f9d2650c81087ae9328640847571594320421f3a0ca190210f5d0650c8108ece2328640851c735503204236bb6a4190211b5d8520c810a9ae6290640847575984320431b2a4c2190218d552610c8109e2e1308640863654584320431aaa2c21902199d49610c810cc8a4b08640843f7458e510421e3a2c7288218798c4394410c3ac621ca20862e4398a510431621cc5288218b90d6294410c5886b14a20863565953410429aba887a0821a598c43d04109e6e0b1682084e772583410422f39ecb20821175cf65904108dce5b2c820846d72d96410431caa2c1208211b9cb65104108dae5b28820863a54580410431ab2cc8208211ddd95410410c6cc8aa082086356590c410429aba886208218d5944310410d2cc62188208477755804104279baac0208219cdd56010410d64a8b0082086b154580410427839ac020821ac90d6010410d6086b00820846f725973104236392cb98821471cd54cc4109cee4b2e6208564725973104278b84c9988211d5d464cc410c6acaaa662085947355331042b2392a7988214d5d643cc410a6aea21e62084f37058b310423abb4a5988211d5d852cc410aaae6296620857175d833104273b92c1988210f9d3658c41087ae9b2c620846e72d963104236b96cb188210f5d6648c41087eeab24620843f76952310421ebb4a9188210fdd9548c41087aecaa4620843e76951310421e3b4a8988210f9d9544c410878ecaa2620851c73551
  | 3 => 0x8c6155010c68c630aa80843f765505404237394c3a98211b5ca61d4c10acae530ea60851e73d92530428f398c9298210f9d26294c1087ae9314a60843f7458a530421e3a2c529821479ce5454c10a38e6aa2a60862e54d895304316aa6c4a98218b9506254c10c5aa8312a60862f64d895304316326c4a98218bd906254c10c58c8312a608666711895304332b88c4a98210fdd16154c10878e8b0aa60846f725855304236392c2a98218dd906154c10c68c830aa608667621855304332310c2a98210fdd16054c10878e8b02a60846f725815304236392c0a98218ed906054c10c70c8302a60866b621815304334310c0a98219c1846054c1087aed2a0a60843f76550530422fbb2a6298218b9526214c10c5aa9310a60862e545885304316aa2c4298219354d6214c10c5cc9310a60862d649885304317322c4298218b5916214c10c9cc6b10a608635649845304332b14c2298218e5926014c108dce5b2e860846d72d97430423abacc3a18218d95161d0c108f2eb306860863a545834304237390cb218211b5c86590c108eaeb30c8608635549864304278b84c3218218d5516190c10a3ce7b2c860861e73d96430431b38ecb21821479cc6590c10a5ce432c860852d721964304297b92a7218214b1c95390c10a5ce429c860852d7214e430429abacc3218218dd966190c10b62e130c860863765586430421fba2caa18211bdc96550c108d8e4b2a860843e76951430431aaa6c2a18211d5d46150c10c72a9b028608479751814304237390ca218211b5c86510c108ece2328860847a70194430421ebb6a8218210f5d85410c10a3ce7b28860843e73d94430430f39eca218210f5da6510c10c68e2b28860851e731944304297390ca218214b5c86510c10a6ce2328860853a70194430421ebacc6218210f5db5310c1087eed298860843f7654c4304297b92a6218214b1c95310c1087cec298860843d7614c4304297390a6218214b5c85310c10a6aebb08860863565d84430429aba8c2218218d5946110c10b4ae430886085b170184430421f39cc9a90210f1cd64d481087ee8b1ea40843c7458f520421fbb487a90210f5da43d481087eec21ea40843d7610f520431ab24c3a90218e59260d481087ee8b1ca40843c7458e520421f3a6c6a90210f5d36354810c3ec621aa40861c6310d520421ebb4a8290210fdd95414810c3ca9318a40861d5498c520430f2a2c6290218755163148108deeca90a40864d63548520421f39cc8290210f1cd6414810c3cc9318a40861d6498c520430fba4c629021871d2631481087ee8b18a40843c7458c520430f322c629021875916314810c3ee8b18a40861c7458c5204326392c629021951c56314810cb0e0b18a40843f7690c520421ebb486290218798e4314810c3ac7218a40843f7610c520421ebb0
  | 4 => 0x62c2b00868843f7458f524421e3a2c7a92210fdd16394910878e8b1ca48861e6310e524430eb1887292218d90d6194910c6886b0ca48843e73d91524421f398c8a92210f9d3635491087ae9b1aa48861f64d8d524430e326c6a9221879d36354910c3ae9b1aa48861f6418d524430e320c6a922187dd06354910c38e831aa48843e7690d524421e3b486a922187d8e4354910c38c721aa48843e7610d524421e3b086a922187d8c4354910c38c621aa48862c64d89524432631ec4a92218d1936154910ca8c7b0aa48863864d81524432c31ec0a92211bdd95214910a58e8a90a48854c73548524421fba2c6292210f1d163149108eee2b18a48847b7058c524421f3a0c0292210f5d060149108bce7b2e848845d73d97424423bb8acba12211d9d661d09108e8eab0e848847875583424422f39ecb21221175cf65909108eae3b2c848845f73595424422e39acaa12211ddc565509108f6e0b2a848847571d94424423cb86ca2122117dcd65109108b8e6b28848843e74d97324421eba6cb992211ddc565cc91087ce9b2c648843d74d96324423ab8ecb192211e5c3658c91087ce832c648843d74196324430f326a71922187990538c91087ce932a648843d74995324421fba2ca992210f1d1654c9108eee2b2a648847b70595324423a388ca992211e1c0654c9108ecebb0a648847a75d81324423ab8eca192210fdd1650c910878e8b28648847671194324423a3aac21922195d4d610c910ccea4b086488664525843244278382c2192218e15160d0510c38c9a9a628861c6414d3144327a98c498a219314c624c510cb0a7b02628866852583214433332a4210a2117dcd65501108b8e6b2a808846f725954044236392caa022187d506350110c38a831a808862f5418940443162a0c4a02218d1536150110c3cca21c608843f74595304421e3a2ca982211bdc9654c1108d8e4b2a608861c64d4d304430e320a69822193d4c624c110c98a6312608865453d85304430f328861822199d4961c8110cc8a4b0e40885657194a20442963a2a510221531cd528811087ee8b2a408843c74595204422fb9aca90221171cd65481108dcec29240885657194820442b4b84a4102211bdd95208110a58e8a90408854c73548204438c2988788221c514c4384110a68e8a9420885547354a10442d2b90c32a0214b9cb6395010a5ae5b1ca80853671d8e540429d386c72a0214d9c46295010a74e0314a80852e721865404296b90c32a0214b9c86095010a5ae4304a80845f73581540422e39ac0aa0211bdc960550108d8e4b02a8085367198d5404297b92c6aa0214b1c96355010a68e2b1aa8085387058d540429b38cc4aa02147dcd6255010a38e6b12a80853471589540429c382c4aa021479ce6155010a3ae730aa80852e729855404296b94c2aa0218d9
  | 5 => 0x86a643588318435221ac418c21b8dc1620c610dc0e0b106308475769483184332b14a418c211d5d8520c610ccac429063084f170192218423abb6a710c21599cb53886108eeeca9c43086695218121842b3396a690c211d1d95348610d28c621a43084767694921842b33b4a490c21999da5248610acae7292430866663949218433231ca490c21c990e5248610e488729243084e6768c921842b3bac6490c2159dd53248610bc0e0992430852d72153408421f3b0a8a04214b5c85450210c3ea831a810861c5418d408434a31e82a04210fdd95410210a38e8a9c61084e572986308428e3a2a6184218b5925208210c5ac8a904108666525842084272b90c988421395c863c4210d2cc621e21086656598b1084332b2ac588421a990d62c4210d4886b1621086696598b1084334b2ac5884211bdc960951108d8e4b04a88861f6418d544430fba0c6aa22193d8f6255110c98c7b12a88862f641895444327b18c4aa2219318c6255110caec7b0aa88865463d855444333b16c2aa2219918b6155110cb0c7b02a88866862d81544421fbb2a82a221471cd5415110a58e4aa0a88861f73593534423ab8cc5a9a211bdc96094d108d8e4b04a68861c64d8d5344317b26c4a9a218b1936254d10c5ec8312a68862c641895344327b18c4a9a218dd936154d10c68c9b0aa68866762d855344332316c2a9a218ed936054d10c70c9b02a68866b62d815344334316c0a9a2117dd95314d10a38e8a98a68854c7254c534421fba2c429a210f1d16214d1087ce9308a68843d749845344237390c229a211b5c86114d1087ce9300a68843d749805344237396cba1a211b5cb65d0d108eae3b2e868847970d974344237396cb21a211b5cb6590d108eae3b2c868852f725524344296392a921a214ddc55490d10a3ce7b2c868852e72d964344296b96cb21a214d5c76590d10a3ce632c868852f7254e4344296392a721a214ddc55390d10a76e0a9c868843d749954344237b92caa1a211b1c96550d108eee2b2a868847b705954344237b92ca21a211b1c96510d108eee2b28868846e721944344236b90ca21a210f5da5410d10a3ae72a0868851f735504344297b92a821a214b1c95410d10a6ee2aa0868851d74d4c434423b3acc221a211d1d56110d108f0eab00868863854580434428f39eca21a214bdc96510d10a58e4b28868853771594434428f398ca21a214b9c86510d10a5ae4328868851e7598c434421ebb6a621a21475db5310d10c3aeda98868851e7394c434421fbb2a621a214bdc95310d10a58e4a9886885377154c434429db82a621a21479d45310d10a3eec298868851d7614c434428f380a621a21471c05310d10a6ceb308868871453984434429a3aac221a21c514d6110d10e30a7300868853875580434431c32ac021a21c614d6010d10d
  | 6 => 0xc438621aa51862187192534c310c38c8a9a618846d75d8930c4236ba8c4986211b9da524c310c5ec9292618862c6494930c42363b2a4986218bd91524c310c58c8a92618866652d8530c4332a96c2986219594c614c310ccca430a61886655218530c438621ca418621c310d520c3108f2eda98618856a72d4c30c438ca988618621c69d4430c310e32ea21861886996510c30c438cb288618621e49c4430c310f22e221861887184394830c43c421ca418621d298e520c310e9687290618872a4394830c439421ca418621d210e520c310e108729061887884354830c438c218a4186219954a61c8310ccca4b0e41886655258720c4332a96c290621995486148310c5cc9290418862d6494820c4317322a4106218b591520831087eecaa0a90862d545885484317322c42a421999896115210cd2c5300a908671619805484317324c5a9c218b59262d4e10ccae3316a70862e6458b5384316b22c5a9c219998961d4e10c74c9306a708639649835384335314c1a9c219a58a60d4e10ce2c3306a70843e7498a538421eba4c529c218dd936154e10c68c9b0aa70845f7654c5384237390cba1c211b5c865d0e108dce5b2c870846d72d964384237394cb21c211b5ca6590e10a5ce42a4870852d72152438428f39ecb21c214b9cb6590e10a5ae5b2c870852e729964384296b94cb21c21479cc6590e10a5ce5a9c870852d72d4e4384237394caa1c211b5ca6550e108dce4328870846d721944384297390a821c214b5c85410e10c70a8b0087084f071580438428f39eca21c21479cc6510e10a5ce4328870852d72194438421ebb6a621c214b9cb5310e10a5ae5a98870843f7654c43842d2b90c221c216c5c06110e10c70cab0087085b0715804384359b0ac021c210fdd163d4a10878e8b1ea50861e6310f528430eb1887a94219c58660d4a1087ee8b1ca50843c7458e528430f31887294218758c4394a1087ce9b1aa50843d74d8d5284237bb2a4294218b5915214a1087ce7320a50843c73590528421fba2c6294210f1d16314a1087eed218a50843d7690c528421fbb086294210f5d84314a10c5ac9310a50863964980528427838ac1a1421179cf6590a108bae7b2c850866652586428422f39ccaa1421175ce6550a1087ce932e650843d74997328421f3a6cb194210f5d3658ca1087ce832c650843d74196328421f3a4ca994210f5d2654ca1087ee8b2a650843c74595328421f3a0ca194210f5d0650ca10ccca4b08650866552584328434b31887a0c216c5c043d06109cee4b06830863954181418423abb6a820c21a598c4310610acce5a9e63084757694b3184273b92c198c219694c604c6109cae432063084f170190318423abb6a618c21599cb530c610e2ea62186308665655883184333baac418c2199d4d620c610ccaa6b10630
  | 7 => 0x7a96218798c43d4b10c3ac621ea5886726158352c421fba2c7296210f1d16394b10a9ce7aa4a58854d73d5252c42973a6a7296214b5d35394b10a5ee8a9ca58852c7454e52c43872988729621c354c4394b10ad2e0324a58852e74d8e52c4296ba6c7296215a5c36394b10a5ee8b1ca58852c7458e52c42b238ac7296215adc16394b10acce231ca58856a70d0e52c42b4b8687296215adc14394b10ad0e0a1ca58870e7310e52c42973a0c3296214b5d06194b10a9ce630ca58854d7318652c421f3a6c6a96210f5d36354b108dcedaa2a58854e73d5152c42a6b9ea8a96211b9d85454b108dceda9aa58852e74d4d52c4296ba6a6a96214bdd15354b10a58e8a9aa58846e7614d52c438729886a9621c354c4354b10acce3322a58856b7059152c42973a6c6a96214b5d36354b10a5ee8b1aa58852c7458d52c42b238ac6a96215adc16354b10acce231aa5885667110d52c42b2b8886a9621c39cc4354b10e4ce221aa5887257110d52c42973a4c2a96214b5d26154b10a5ee8b02a58852c7458152c42a7b9ac0a9621531cd6054b108deeca90a58843f7458c52c421e3a2c6296218798c4314b10c3ac6218a5886655298742c4332a92c3a1621179cc6590b108bae632c858845e7399542c422eb9ccaa16219a5486050b10cd4a5300858866a5258042c421f3a6cb196210f5d3658cb1087ce832c658843d7419632c4317324a5196218b592528cb10c5cc8a94658862d6454a32c4335294c1196219a949608cb1087ce932a658843d7499532c421fba2ca996210f1d1654cb10c5ec9292658862c6494932c4317b22a4996218b191524cb10ccca5b0a658866552d8532c4333290c29962199548614cb10cd4a5b02658866a5218132c4334a90c0996219954a610cb10ccca4b0865886655258432c428f39ea9a0e21479cf545071087cec2a2838843f7655041c4335294c020e219a9496010710c3cc929c638861e6454e31c4317324a518e218b592528c710c5cc8a94638862d6454a31c4335294c118e219a949608c7108dced292638862f6494931c4316324a498e211b1d9524c710c5ec8a92638862c6454931c4335290c098e219a548604c7108daeb310638846f7558831c4236bb4a418e211bdd9520c710cd2a5304438866a5298021c4332a94c3a06219954961d0310c3ca831a818861d5418d40c4236baec4a06211b5d462503108dced292818864f6394940c432631ca4a06211b1d95250310c9ec6a92818864c6354940c4333296c2a06219954b6150310c6ca830a81886665218540c4332a90c2a0621661cd4010310e54a4a0081886655298730c4332a92c3986215a9cb53cc310cd2cb296618874a5394b30c439521ca598621ca10e52cc310cd2caa96618862e6494a30c4316b24a518621c310e528c310c5cc8a94618862d6454a3
  | 8 => 0x4430c020b36ea218601071a7510c30082ccba88618041c65d4430c020e34ca21860107196510c30083c5b908618041e21c8430c020f1087310601047b7558830083c421ac418041c610e520c020f1087a1060104e97610830083c421884180419a597320c020f10879906010569750c83008334b286418041e210c320c020bc2e21906010718439443008274bb642180419a597210c020f108790860106696548430082e439a4218041e210d210c020c6ca930e401063554987200831b2a2c3900418d55161c80209cae232640104e57118f2008296ba88790041a398c43c8020d4ca8b0e40106a554587200835321ac390041a910d61c8020d94c798640106e161cc320083c42186190041b858430c80208daed29440105397510e200823cbb4a510041785c65288020d94c799440105e1710ca2008236bacc8900418bd965448020c5ecaaa2401046d7598d2008317b2c86900414b5d44348020c5eca21a401068c6310d20082743b28090041aa1914048020b90e6a0240105e071501200836431e6090041e210c3048020c76cb2a2401063b65551200823cbacc6900418ed964348020a72ea21a401063b6510d200834c3188690041789c652480209d4ed21240106c863cc920082f138864900413a9d82148020c3ee931ea98864e6398b54c4326b1cc5aa6219398d62d5310c9ac6b16a9886566398754c432ab1cc3aa6219998a61d5310ccac530ea98851e73d5254c428f39ec8aa6210fdd95415310ccac5308a98866a6258054c433930ac02a6218b99262d4f10c5ac9316a78862e6458b53c4316b22c5a9e218d99261d4f10c6ac930ea7886666298753c4332b14c3a9e219a98960d4f10ce4c2b06a78851e74d4e53c430eb9ec8a9e21479d36354f10c76c9b02a78863864d8153c422fbb2a629e219958a6114f108dce532e878846d7299743c4237390cba1e211b5c865d0f108dce532c878846d7299643c4237390cb21e211b5c86590f10a5ce5aa4878852d72d5243c4297390a921e214b5c85490f10a3ce7b2c878852e7299643c4296b94cb21e21479cc6590f10a5ce432c878852d7219643c4297396a721e214b5cb5390f10a5ce429c878852d7214e43c4237394caa1e211b5ca6550f108dce432a878846d7219543c4237394ca21e211b5ca6510f108dce4328878846d7219443c428eb9ea821e214b9cb5410f10a5ae5aa0878851d7315043c4297390a821e214b5c85410f10a3ee8a98878851e73d9443c4297394ca21e214b5ca6510f10a3ce6328878852e7219443c4296b90ca21e21475d66310f1087aeda98878852e72d4c43c4296b96a621e2147dda5310f10a3aed298878843f7654c43c428fbb2a621e2187dd95310f10e36e0a98878852e7214c43c4296b90a621e21c594e6110f10e2ca6b08878843f7458f52c421e3a2c
  | 9 => 0x2a8302821062e54588410831d2a2c0208410f9d265cc42087ae932e62105547154f310821f3a6cb188410f5d3658c42087ce932c621043d74996310821ebacc9188410fdd5648c42087eed2a4621043d76952310821fbb2a9188410f5d9548c420a38e6aa4621043f74595310821e3a2ca988410f9d0654c42087ae832a621043d75d91310821eba8c8988410f9da544c420878ed2a2621043e76551310821e3b2a8988418b953624c420c5aa9b12621062e541893108316aa0c4988419394c624c420cc8c528a621066462545310831d2a6c0988418e553604c420c74a8302621063954181310832d298c0988419c944604c420ce2a2302621043e74994310821eba4ca18841471cd540c420c5ca9310621062d549883108274b84c4188418b951620c420c5aa8b10621063954983210831caa2c1908413a5c064c84209d2e031e421046f7654f21082b238aa7908414b5d643c8420a5aea21e421074553cc721082b2ba863908413add560c8420cd6eab0642106aa545832108354aa2c1908413a1cd60c8420d5486b0642106a8435832108236bacc8908413a5c06448420c5ecaaa2421046e76d4d21082363b2a690841591c55348420a5aeb21a421052d7510d21083463188690841789c351484209ccec28a4210726541452108392aa0a290841715cc51484209cced18a42105e2708c521082723b26290841591d53148420e8aa698a42105e0704c521083932a24210841c95512108420dc243300421043f7458e500821e3a2c728041595c43294020c5acba16801062d5458a400830f2a6c6a0041875536350020c3ca831a801061d5418d40083172a6c4a00418b5536250020c5ca8312801062d541894008317b2e84a0041a318f4250020c6ca9b0a801063554d85400831b2a0c2a00418d5506150020c5ca8b1080106396550040082cc39a8020041aa5894010020c72caaa660105707154f300829cbac87980414e5d443cc020ad2ebb1660105e17118b30082753b085980415a5d432cc020bc2e219660104ea76c87300821f3a6cb180410f5d3658c02087aeb324601043f75592300821fbb4a9180410f5da548c02087eecaa4601043d76552300828e39aa918041471d1538c020a3eea21c601051d7510e3008272b8cc5180410f9da544c020878ed2a2601043e76551300821e3b2a8980418b953624c020c5aa9b12601062e541893008316aa0c4980418d953614c020c6aa9b0a601063654185300831aaa0c2980410f9d2650c02087ae9328601043e74194300821eba0ca18041471cd540c020a38e8a98601051f7510c300828eba886180418b552620c020c5aa8b10601063965950300831cb2aa818041661cd540c0208f6eca9860105707154c30082cc3a2a6180414e5d6430c020c72cb218601059a7390c300829cba886180418e59
  | 10 => 0x5377154e430829a38aa7218414d9c45390c20a6ae229c861052d7598a4308317b2cc5218416a5c26290c20c5ecab14861043f74595430823bb8acaa18411d1c56550c2087ced2a2861062d54d894308236ba8c4a18418e5536050c208f2ea302861046e72194430823b388ca218411d5c46510c208f4e0328861043d76d50430821ebb0a821841479cf6510c2087ce7b28861061e73d94430821ebb4ca218418b1c96510c20a3ce6328861052e72194430829b388ca218414d5c46510c20a74e0328861043d7598c430821ebb6a6218410fdda5310c2087eeca9886105377154c430829a38aa6218410f9d85310c2087aec29886105367114c430829ab88a6218414b5d76210c20c5acbb10861052d751884308316b28c421841695c46210c20b52e0310861043f7458e520821e3a2c7290418798c4394820c3ac621ca41062d659534208296ba887a1041a398c43d08209d6e0b0e84104e771583420822f39ecb21041175cf6590820c72a8b04841063a545804208316b2cc8210411bdd95410820c5cc8aa0841062d6590c4208296ba886210418b5944310820d1cc6218841046f755804208275baac0210419add56010820d54a8b0084106a954580420827439ac021041aa90d6010820d5086b00841047771597320823a38acb99041471cd54cc8209cee2b2e6410564715973208274b84c9990411b5d464cc820c5acaaa6641058c7355332082b238aa7990414b5d643cc820a5aea21e64104eb7058732082b4baec19904139dc560cc82087ce9b2c641043d74d96320821ebacc9190410fdd5648c82087eed2a4641043d76952320821fbb2a9190410f5d9548c82087ced2a2641043c76951320821f3b2a8990410f1d9544c820a38e6aa2641063654d85320831aaa6c2990418d950614c820c6aa830a641063a54d81320831caa6c0990418d952610c820c6aa9308641063654584320831aaa2c2190419594d610c820caaa6b08641063954980320831caa2c0190411b5d4640c8209cae232064104e9701903208237bb2a619041591c5530c820e1ca8a98641052d7590c3208316b2c86190414b5d4430c820c5aca218641070d5310c3208332b2cc21904199595610c820cceeab0864106647558432083532a2c219041a9551610c820ccea6b0864106c6535843208332a9ac219041b154d610c820d4c86b0864106a4435843208370b0cc0190411bdd5600c820dc4c2b00641043f7458e510821e3a2c7288411b5d83294420acae2194a21043e74d8d510821eba6c6a884187d8c4354420c38c621aa21043d76950510821fbb2a828841879526314420c3aa9318a21061e5458c510830eaa2c6288411ddd95114420caac6a88a2104e97098a4108316aa2c52084117dcd65504208b8e6b2a821062d54d894108316aa0c4a08418e5536050420c7
  | 11 => 0x48297b92ca21a414ddc56510d20a68e2b28869051e73194434829b388ca21a414d5c46510d20a3ceb318869043d76d4c434828ebb6a621a41875db5310d20a3ce7298869043f7654c4348297b92a621a414ddc55310d20a68e2a98869053b7054c434828f3a8a621a4147dd85310d20a3aec298869052e75988434838629cc421a414b1d56210d20e18a6b10869071853980434829c3aac021a418e1956010d20e30a6b0086906a962580434831c2a2c1a124187193534c920c38c829a649065753185324832a298c2992419614f604c92087ee8b1ea29043c7458f514823bbb2a228a414d1d15114520aa8e6a88a29043f7458c514821e3a2c628a411b9d662d05208bee6b28829045c73594414821f3a0cb18a410f5d0658c520c3cc9a9c629061e6414e314821f3a4ca98a410f5d2654c52087ee8b28629043c745943148327a9ac418a413a1c1620c520ccac5a88629066562144314833332a4210a4117dcd65501208b8e6b2a809061f5418d404830e2a0c6a02418b1536250120c6ea830a809063454185404830f32887182410fdd1654c120878e8b2a609061c64d4d304830e320a6982419314f624c120caea630a609065453185304830f3288618241c614c43c8120e18a621c40905a57118a5408297396c72a0414d9c76395020a6ae3b1ca81053a70d8e540829b388c52a0414d5c46295020a5ce430ca81053a70186540829b388c12a0414d5c46095020a5ce531aa81052c7258d540829bb8ac6aa0414d1c56355020a70e0b1aa81051e73989540828eb9cc4aa0414d9c66255020a6ae3312a81062e631895408316318c4aa0414b9ca6155020a3ee6b0aa81051c735855408296392c2aa0414e1c1615502087eecaa0a8105657198b530828f39ec929841479cc6494c2087ce930ca61043d74986530821fba2c3298410f1d16194c20a3ce72a2a61051c73551530831b2a6c2a98418d5536154c20c6ca830aa61063554185530821fba2c4a98410f1d16254c20c5ec8312a61062c64189530831bb26c2a98418d1936154c20cc8c5b0aa61063764185530831a320c2a9841991886154c20ccce430aa61066572185530831db20c0a98418e1906054c20cd0c4302a610673611815308338308c0a98410f5da5414c2087eecaa0a61045f7654c530831b2a4c2298418d5526114c20c6ca8b08a61063554584530832aa9ac2298418b5926214c20c6cc9308a61063564984530831b322c2298418d5916114c20cacc6b08a61066662584530831cb24c0298411d9c765d0c208eae3b2e861046d7598b43083172a2c5a18411e5d660d0c20c74a8b06861047671196430823ab88cb218411b5d66290c20c5aa931486104e97098a4308316aa2c521841479cf6590c20c3ce7b2c861062e72d96430828f398cb218414d9c46590c20a6ae232c8610
  | 12 => 0x21c414d5c75310e2087eeca9887105a57118843882d4b80c421c418e1956010e20b50e4b0087106ab62580438834731887a14416a5c043d0a209cee2b068510639541814288236bb6a821441a398c4310a20acce3a9e65104e771583328832d298c099441395c4640ca209d2e0320651046d76d4c32882b338ea619441c3d4c430ca20ccacab086510667755843288333a9ac2194419954d610ca20d4c86b0865106a4435843288371b82c219441b81c1610ca2087ee8b1ca31043c7458e518830f3188728c418758c43946208daed994a310565710ca518821f3a6c6a8c410f5d363546208eeeca88a310635645445188274392c1a0c41179cf65906208bae7b2c831066562946418821f3a4cb98c410f5d265cc62087ce9b2c631043d74d96318821fba2ca98c410f1d1654c620ccac52886310665625443188274b80c990c411b5db53c8620acce3a9e431046f7654f21882b338ea690c411b1d95348620d18c621a43105667694521883333b4a290c41595ce5148620cccc728a431066463945218839321ca290c41c910e51486209cced18a4310567758c521882b3baa6290c41781c13148620a6ae22a6811043e76151408829ab88a8a044187d506350220c38a831a811068c63d09408821fbb2a820441471d1538c2209cae3314611051c7454c3088272b88c990441395c463c8220d1cc621e4110665659872088332b2ac390441a990d61c8220d4886b0e4110671659872088338b2ac39044187d906355120c3ee831aa89064f63d89544832631ec4aa24195d8f6155120ca8c7b0aa89066762d85544831bb20c2aa24195d8c6155120ca8c630aa89066762185544832c31ec0aa2419c187605512087eecaa0a89051c73550544829a38aa82a24187dcd64d4d20c38c9b1aa69062f64d895348316326c4a9a418dd936154d20c68c9b0aa69066762d85534831bb20c2a9a418d1906154d20caec630aa69066762185534831db26c0a9a418e1936054d20ce6c3b02a69067061d81534822fbb2a629a41471d15314d20aa8e2a98a69043e74988534821eba4c429a410fdd16114d20878e8b08a69046d72d97434823b38ecba1a411d5c765d0d208f2e1b2e869046d72d96434823b38ecb21a411d5c76590d20a5ee4aa4869053771552434829a38aa921a41479cf6590d20a5ae5b2c869053671d96434829ab8ecb21a41479cc6590d20a5ee4a9c86905377154e434829a38aa721a414edc15390d2087ae932a869046f72595434823bb8acaa1a411d1c56550d208f6e0b2a869046f72594434823bb8aca21a411d1c56510d208ece2328869047571194434821ebb4a821a41475ce5410d20a3ee6aa0869052f72550434829bb8aa821a414d1c55410d20a3ae9a98869046e7598843482363aac421a411e1d56010d20c70a8b00869051e73d9443
  | 13 => 0x4354720e2ce621aa3907267210d51c8392b9086a8e414d9d26254720a6ae9312a390536748c951c829aba464a8e414ddd13254720a68e8992a390570704c951c823b3b064a8e414ddd16054720a68e8b02a3905577358151c82aa39ac0a8e411ddd95114720cccc4a8e83906656254741c8338a88c0a0e419c9466010720ce4a2b00839043e74d9631c821eba6cb18e418d992518c720c6ac928c63906366454631c831ab22a318e419c946608c720ce4a2b04639043f7459531c821e3a2ca98e418dd92514c720c68c928a63906676294531c8332314a298e418dd91514c720c68c8a8a63906676254531c8332312a298e419c947604c720ce4a230263906715118131c8332b14a218e4199989510c720ccac4a8863906715198321c833928cc010e419998951d0320ccac4a8e819061e5418d40c830eaa0c6a06418b95062503208eaebb0a81904757518540c823b3b4a2a064195d8e5150320ca8c728a81906676294540c8332314a2a06411d1d95150320caec6a8a81906546354540c8333b12a2a0641991895150320b30e6a0081907325150040c8333312a3986419958951cc320ae4e3a9e61906716594730c83a929ca398641cc90e51cc320e608728e61906716554730c831b324a3186418d592518c320e288728c61906366454630c831ab22a318641c510d518c320c38c929a619061c6454d30c8327298c4986411d5d7614c3208eaea30a61904767694530c831bb24a2986418d192514c320ccec528a61906646294530c823a3b2a2986418dd91514c320c68c8a8a61906676254530c8332312a298641c510e510c320e2886a88619047976d4c30c82b938ea618641c654c430c320e34ea21861907197510c30c834cb288618641c6594430c320f14e421861907897210c30c838c21ca218641e410e510c320ea4c728861907534394430c839921ca218641cc10e510c320ea08728861907104394430c83c821aa2186410fdd95415220c6aa8b08a91066562984548831b322c22a4419a58a6015220ce2c3300a91063664987538831ab24c3a9c419958a61d4e20ccae530ea71063664587538831ab22c3a9c418e99260d4e20c72c9306a71066962983538833930cc1a9c419c58660d4e2087ce930ca71043d749865388317b26c4a9c418b1936254e208beeca98a71047671197438823ab88cba1c411d9c76590e208eae3b2c871047671996438823ab8ccb21c414d9c45490e20a6ae22a4871051e73d96438829b38ecb21c414d5c76590e20a6ce332c871053571996438828f398cb21c414d9c75390e20a6ae3a9c871047671995438823ab8ccaa1c411d9c46510e208eae2328871053671150438829ab88a821c418e1516010e209d0e4b00871051e73d94438828f398ca21c414d9c46510e20a6ae2328871043d76d4c438829b38ea6
  | 14 => 0xca30a60186b364185300c358320c298061b8d88614c030dc0c430a60186d253185300c359218c298061ac10c614c030c3ee931ea99064e6398b54c8326b1cc5aa6419598e61d5320caac730ea9906666298754c832b31ac3aa6419558d61d5320cccc4b0ea99051e73d5254c828f39ec8aa6410fdd95415320cccc4b08a99066a6258054c833930ac02a6418b99262d4f20c5ac9316a7906366498753c831ab24c3a9e419998a61d4f20c6cc8b0ea7906356458753c8333312c3a9e419a98960d4f20ce4c2b06a79051e74d4e53c830eb9ec8a9e41479d36354f20c76c9b02a79063864d8153c822fbb2a629e41999896114f208ece332e87904757199743c823b388cba1e411d5c465d0f208ece332c87904757199643c823b388cb21e411d5c46590f20a6ce3aa4879053571d5243c829b388a921e414d5c45490f20a3ce7b2c87905367199643c829ab8ccb21e41479cc6590f20a6ce232c87905357119643c829b38ea721e414d5c75390f20a6ce229c87905357114e43c823b38ccaa1e411d5c66550f208ece232a87904757119543c823b38cca21e411d5c66510f208ece232887904757119443c828eb9ea821e414d9c75410f20a6ae3aa0879051d7315043c829b388a821e414d5c45410f20a3ee8a98879051e73d9443c829b38cca21e414d5c66510f20a3ce632887905367119443c829ab88ca21e41475d66310f2087aeda98879053671d4c43c829ab8ea621e4147dda5310f20a3aed298879043f7654c43c828fbb2a621e4187dd95310f20e36e0a9887905367114c43c829ab88a621e41c394e6210f20e1ca6b10879051e73d5342c828f39ea8a16410f9d85450b2087eecaa0859061e6494e32c830f322a7196411d5d6610cb208eeeab08659043f7458e51c821e3a2c728e41559cf5494720aaae7aa4a39053674d4e51c829aba6a728e414ddd15394720a68e8a9ca3907165310e51c838aa988728e415c5c06494720a6ce9b1ca39053574d8e51c82b8b86c728e414ddd16394720a68e8b1ca3905647258e51c82b9b82c728e41599c86394720ae4e1a1ca39057170d0e51c82b9b828728e415c1c14394720e2ce621ca3905367418a51c829aba0c528e41559cc6294720aaae6314a3905727010a51c82b8b808528e414d9d23294720a6ae9194a390572708ca51c82b8b846528e414ddd13294720a68e8994a390570704ca51c823abb06528e410f9d3635472087ae9b1aa39047676d5151c82ab39ea8a8e41555cf54547208ecec2a2a39047676d4d51c829b3a6a6a8e414d5d35354720a6ee8a9aa3905347454d51c823b3b0a6a8e41c594c4354720e2aa621aa3905667299151c82b9b82c8a8e414d9d36354720a6ae9b1aa3905377458d51c829a3a2c6a8e41591c96354720ae6e0b1aa3905667218d51c82b339086a8e41595c8
  | 15 => 0x9871580430c3c838ac021861641c56010c30b1ce4300861858d72180430c2cb388c021861655c46010c30b34e0300861846f76548520c316b22a429061c310d5214830d2887308a41869443584520c332a92c229061475d443d0830c3cca21e841869843983420c34c21ac1a10613c1c560d08308eee2b2a841847471595420c23b388caa10611d5c46550830a3aea21a841864c63549420c34c21ec0a10618e5506050830d3086302841861e6510c420c34c21cc199061a610d60cc8309e0e2b06641869443d85320c34a218c299061a610f604c830e1886a90641869443984320c34a21ac21906199949610c830ccaa4b08641869843980320c34621cc428861a310d62144308eeeca88a21863564544510c38a21aa228861995895114430a3aea21e821861e6510f410c34c21cc1a0861a610d60d04309d0e4b06821846f72595410c236392caa08611b9c865504308dae432a821851d7510d410c32a31aa2a0861a610f6050430c72a8302821869843181410c30f3288620861a610e60cc430d3086b0662184e872583310c34621ec498861a310c624c430d3087b02621868c43988310c34621ac4188619958a510c430e2886a88621866562544310c34c21cc018861a610e60c8430d3086b06421869843982210c34c21ac1108610fdd16548430878e8b2a421843e74195210c21eba0ca90861279d36348430c3eca21a421861c6510d210c2b238aa490861591c95148430d3087b02421869843181210c334a90c0908619c5446048430c3cca218421861d6510c210c333b2a4210861995952108430b88e6908421878443484210c30fb9ac9280610f5da439403087aec21ca01861d6410e500c28ebb08728061875d84394030a5ae42a6801853571153400c30eb2887a0061475d44390030a74e1aa2801843e76151400c296b90a8a00614d5c45450030c3ea831a801861c5418d400c30fb2886a0061a310f6250030d1886312801869443d85400c34a218c2a00610fdd95410030a3aea218801861e6510c400c22ebb4a7180611e5da538c030b32ec21c60186997610e300c34c21cc5180613c9c6628c030d308730c60184ea72986300c24f3b4869806187d96434c030c3eca21a601868c43d89300c346218c498061a510f614c030d288630a601861f65d91300c22ebacc898061279d2644c030c3eca322601864f65d89300c346326c49806193d94624c030d18c8312601865765d85300c34a326c29806195d94614c030d28c830a60186c462185300c30e324a0980618ed97644c030c76ca322601869864d8d300c25d3b486980618ed96434c030974ec21a601863b6510d300c34db1886980619ad97624c030cd6ca31260186ab64189300c354320c498061b294c624c030d548631260186a843189300c339b2ec298061b818b614c030ce6
  | 16 => 0xc21e3a2cb10a610f9d3654853087ae9b2a429856671d49214c2b3396a290a610fdd16508530878e8b28429861c5498c214c30e2a2c610a619398c5208530acae2290429865663144214c2b2b90a210a61599d52108530ac8ea908429866665484214c33232a4210a61c9d512108530e48a890842986c563484214c30e2a4c7a02618715163d0130c38a9b1a809861f5418d404c30e2a0c6a02611b9d76250130c5ea9b12809862c54d89404c2373a8c4a02618bd506250130c58a8312809846e76d49404c327b1ea4a02619318f52501308dcec292809864f63149404c326318a4a02611d9d76150130c6ea9b0a809863454d85404c333a96c2a02619914b61501308ecea30a809863754185404c31a2a0c2a026199d486150130cc8a430a809847676d45404c32bb1ea2a02619518f5150130ccec5a8a809866462d45404c23b3b0a2a026195d8c5150130ca8c628a809866762145404c332310a2a02614e1d54010130e50a4a00809873051500404c29d3ac87982614e9d443cc130e56a829660987285414b304c395218a598261ca10c52cc130ec0a5a8e609873354147304c3982a0a398261d8d4851cc130ec0a428e609873243147304c398218a3982618b993528c130c5ac9a94609870c43d4a304c317320a5182618b590528c130e1886294609863664d46304c31ab26a318261c510f518c130c6cc828c609863564146304c38a218a318261c3153528c130e18a8294609871454d46304c38a2a0a318261d1148518c13087eecaa0a81862d54588540c31aaa2c22a0618b9916215030cccc5308a81866562984540c31b322c22a061999896115030ccac4b08a81866962980540c338b0cc02a0618e5526090c30a5ce532c861852d72996430c29b38ccb218614d5c66590c30a3ce632c861863b65982430c274392c0218613c1c56010c30a3ce6328861851d7598c430c30eb2cc6218618e1956010c30b50e4b0086185b071580430c22fbb2a82186117dd56010c30b90e4b0086185d071580430c2cd384ca21861479c26510c30e34e1328861851d75d88430c30eb2ec421861669c36210c30b32e1b10861861d65588430c2cdb82c421861661c16210c30a3aea310861859671188430c2cab88c421861669c06210c30b32e0310861851d75d84430c30eb2ec221861669c36110c30b32e1b08861861d65584430c2cdb82c221861661c16110c30a3aea308861858e72184430c2c6b90c221861669c06110c30b32e0308861851d75d80430c30eb2cc021861665da6010c30d36cb300861869965980430c2cd394c021861669c66010c30a3eeab00861858f72580430c2c6392c02186165dc56010c30b28e2b00861869b76580430c2cdbaac021861c6dd56010c30f16e4b00861859872580430c3c4392c021861621c96010c30f26e2b0086185
  | 17 => 0x8a6199d8a62d4530a6ce9196a298535748cb514c23bbb265a8a614ddd132d4530a68e8996a298573704cb514c2b838265a8a611d9d832d4530acee4b06a29856472583514c317aa4c528a618b1526294530c5ea8b14a29862c5458a514c317326a528a618b5935294530c5cc8294a29862d6414a514c31b326a328a618d5935194530cccc5a8ca29866562d46514c21f3b6a8a8a610f9d85454530c5ea9b12a29862c54d89514c317aa0c4a8a618b15062545308dceda92a29862f64d49514c316326a4a8a611b9d85254530c5ec8292a29862c64149514c23bbb2a228a614ddd15114530a68e8a88a29856772544514c2b2392a228a618d99754145308eaed2a0a29856672950514c2b2b94a828a611ddd95414530acee4aa0a29856472550514c31b328a828a614d9d64314530a6cea218a29866665d48514c393aa6a428a61c91535214530e4c87a90a29872443d48514c23abb4a428a614d9d25214530a6ae9290a29847776548514c29bba2a428a614d1d15214530cccca290a29872754148514c3922a0a428a61c990c5214530e4886290a29857170190514c29b3a6c628a614d5d36314530ae4e1a18a29857170d0c514c2b9b828628a615c1c14314530e2ce6218a29855573188514c332b10c428a615c9c04214530ae2e0210a298536748c8514c29aba46428a615c9c23214530ae2e1190a298477764c8514c29bba26428a614d1d13214530ae6e0990a298570704c8514c23b3b06428a61599cb6014530acae5b00a298537744c0514c29a3a26028a6159dc93014530ac8e4980a29846f72597414c236392cba0a611bdc965905308d8e4b2c829846e72d95414c236b96caa0a611bdc965105308d8e4b28829863854980414c334294c020a619c1466010530cd0a4b00829867051580414c21f3acc918a610f1d5648c53087aedaa4629843d76152314c317326a518a618b593528c530c5cc8294629862d6414a314c31b326a318a618d593518c530c6cc828c629863564146314c334294c118a619c146608c530cd0a4b04629843e75d91314c21f3a8c898a610f9db544c53087cec2a2629846e75d89314c317aa6c498a618b153624c5308dcea312629862f54189314c3162a0c498a611b9db524c530c5ec9a92629862c64d49314c2373b0a498a618bd90524c530c58c8292629863764d45314c31a326a298a6199d8b514c530cc8c5a8a629863764145314c31a320a298a6199d88514c530cc8c428a629863b54d81314c31c2a6c098a619ad4b604c530cd0a5b02629867051d81314c31daa0c098a618e150604c530cd6a4302629866852181314c339a88c098a618bd52620c530c58a9310629862f54588314c3162a2c418a611bddb520c5308deec290629866662d44314c332b16a218a610fdd165c8530878e8b2e429843f74596214
  | 18 => 0x415130a5ee4aa0a89852c72550544c29bb8aa82a2614d1c55415130a5ce5320a89852d72990544c29b38cc82a2614d5c66415130a72e0310a89853970184544c297b92c02a2614b1c96015130a6ee2b00a89853471580544c31c2a4c1a1a614b9ca5490d30a5ae52a4869853671952434c29ab8ca921a614bdc95490d30a58e4aa4869853771552434c29a38aa921a610f9d85450d30c76a8302869851d73950434c297394a821a614b5ca5410d30a6ce32a0869853571950434c21fbb2a821a6147dcd5410d30a5ee4aa0869852c72550434c29bb8aa821a614d1c55410d30a38e7328869856671953524c2b2b8ca9a926159dc554d4930ac8e2aa6a49852e7590f524c2973a887a92614b9d363d4930a5ae9b1ea49856671d8f524c2b2b8ec7a9261c39cc43d4930ccec330ea49856771583524c2b238ac1a92618b9935294930c5ac9a94a49863754986524c31a2a4c32926199d4a6194930c6ea8b0ca49863454586524c333a92c3292610f9db545493087cec2a2a49863754d85524c31a2a6c2a92618dd506154930c68a830aa49846f76548524c297ba2a4292614b1d15214930acee2a90a49856471548524c31732ea8292611b5da5414930acce32a0a49856571950524c237bb2a82926159dc55414930ac8e2aa0a49862e65150524c2973ac86292614b9d44314930ad2e0320a49852e74d8c524c296ba6c6292615a9c34314930ad2e1a18a49856b7050c524c2b43828629261c39cc4314930a9ae6308a49866561184524c2b338ec029261595c76014930a5ee8980a49852c744c0524c23bb8acba12611d1c565d09308eee2b2c849847471596424c23b38ecaa12611d5c765509308eee2b28849847471594424c31c2a4c0212619a14a6010930cd0a4b00849843e75992324c21e3aac9192610f5db548c93087aec2a4649862e64d4a324c316b26a5192618b990528c930c5ac8294649866852982324c21f3aec8992610f9d4644c93087cedaa2649843e76151324c317b26a4992618b193524c930c5ec8292649862c64149324c23b3aec2992618dd53614c930c68a9b0a649866752d85324c332296c2992611d9d4614c930c6ea830a649863454185324c333a90c29926199148614c930c76a9b02649863854d81324c334296c0992618ed50604c930c70a8302649866b52181324c31baa4c2192618d152610c930ccea5308649863754584324c31a2a2c21926199d49610c930acce52a6a29856572953514c2b3b92a9a8a61591c954d4530a6ceb21ea2985367510f514c393aa6a5a8a61c915352d4530e4c87a96a29872443d4b514c29b3a4a5a8a614d5d252d4530a6ee8a96a2985347454b514c393aa0a5a8a61c915052d4530e4c86296a2987244314b514c29b3a6c7a8a614d5d363d4530acce5b1ea29856572d8f514c38b39887a
  | 19 => 0x7292651856571949328c31b2a6c2994618d553614ca30d2887b0a651863654185328c31aaa0c299461a510c614ca30ccca430a651866552185328c31d2a6c0994618e553604ca30c74a8302651863954181328c34c218c0994619a948604ca30c6ca9308651863554984328c34a21cc2194618d951610ca30c6aa8b08651869443584328c24ebb087a8c618b95262d4630c5aa9316a31868c4398b518c3172a2c5a8c618b55162d4630d1886b16a31862e5498a518c316aa4c528c61a310e6294630c5ca8b14a31862d5458a518c34621ac528c61c510f5194630acce5a8ca31866562d46518c31721cc528c618b10e6294630c5c86b14a31862c4358a518c21ebb4a828c610fdd9541463093aec218a31847776544518c30eb2887a0c611b9cb65906308dae5b2c831861d5498e418c30eaa0c6a0c611b9cb65106308dae5b28831861d6510c418c34c21cc020c618e951601063087aeb324631843f75592318c21ebb4a918c610fdd9548c630acae528c631869843982318c21ebaec898c610f5d4644c63087ced2a2631843c76551318c3172a6c498c618b553624c630d1887b12631862e54189318c316aa0c498c61a310c624c630e288728a631856572945318c332314a298c6199189514c630c74a9b02631863954d81318c31d2a0c098c618e550604c630d3086302631867251181318c3172a4c418c618b552620c630d1887310631862e54588318c316aa2c418c61a310d620c63087ce932e431843d74997218c2b2b94a390c610f9d2658863087ae932c43185657194a218c21f3a0ca90c610f5d0654863093ce9b1a431861e54d8d218c30f2a0c690c6187d944348630c38ca21a431843e74994218c21eba4ca10c61879944308630c3aca218431856571948218c2b2b94a210c6159dd52108630acaea908431866665484218c3932a24210c61c95512108630b88e6908431878443484218c30eaa4c720461879536350230c3ca831a811861d5418d408c3172a6c4a04618b5536250230d1887b12811862e54189408c316aa0c4a0461a310c6250230c6ca9b0a811863554d85408c34a21ec2a04618d9506150230c6aa830a811869443185408c30f2a4c620461665c04310230b30e6a00811861d65953308c30eb2aa9984618e59654cc230c72caaa661185727194b308c2b5394a3984614b9cb60d5130a5ae5b06a89853671d83544c29ab8ec1aa2618bd526295130c5ea8b14a89863754986544c31baa2c32a2619998a6195130ccac530ca89866662586544c332b12c32a2619a9896095130ce4c2b04a89862f64d89544c327b1ec4aa2618bd906255130c9ec6312a89863764d85544c32bb1ec2aa26199d8b6155130cc8c5b0aa89863764185544c32bb18c2aa26199d886155130cc8c430aa89866862d81544c33830ec0aa2610fdd95
  | 20 => 0x66258754cc332b12c3aa6610fdd95415330c74a8b0087984e87258043cc27838ac021e614b9ca6510f30a5ae532887985367199443cc29ab8cca21e616a1c96010f30b60e2b00879862c7259252cc21ebb487296610f5d84394b308deeca90a5986655258452cc23b38ecba16611d5c765d0b308ece332e85984757199742cc297396a9a16614b5d252d0b309e0e2b06859863b5418142cc27838ac19966199949610cb30ccaa4b0865986347159251cc21ebb48728e610f5d843947308eeeca88a3986656254451cc237396cba0e611b5cb65d07308dce532e839846d7299741cc29b38ea9a0e614d5d251d07309d0e4b06839863b5418141cc274392c198e619958a510c730ccac4a88639843e74d9721cc21eba6cb90e619a94960c873087ce9b2c439843d74d9621cc33928ac110e610f9d3654873087ae9b2a43985647154921cc2b2392a290e610f9d3650873087ae9b2843984d87058c21cc333b2a4210e61995952108730d8ac6908439843e7695140cc30f2a0c6a066187550635033087aedaa0819852e72d8e548c296b96c72a4614d9c76395230a6ae3b1ca9185367118a548c29ab88c52a4614e9c06295230a5ce430ca91852d72186548c29d380c32a4614b9c86095230a5ae4304a91853671182548c29ab88c12a4614bdc96355230a58e4b1aa9185377158d548c29a38ac6aa461475ce6255230a6ce3312a91853571989548c28fb9ac4aa461475ce6155230a5ce530aa91852d72985548c28fb9ac2aa4610fdd95415230c74a8b06871843e76951438c31caa6c0a1c610f5db5410e308baedaa0871849d76d50438c2cd386a821c61875965410e30b34e02a0871851d75d88438c28eba8c421c61659c46210e30b2ae2310871859a70188438c2ccb80c421c61475d76110e30a3aea308871858e72184438c2c6b90c221c61669c06110e30b32e0308871861d65980438c2c7b92c021c61631c96010e30b2ee2b00871859471580438c30eb28c021c61639c86010e30b1ae4300871859671180438c2cab88c021c61a65806010e3093aec21ea51863654987528c31aaa4c3a9461a510e61d4a30c6ca8b0ea51863554587528c34a21ac3a9461c310f5294a30acce3a94a51863654986528c31aaa4c329461a510e6194a30c6ca8b0ca51863554586528c34a21ac32946199d496194a30c6c8730ca51863443986528c31b21ac3294618d10d6194a3087aed2a0a51843f76550528c24ebb086294611bdd95214a30c3aca21e851847671d96428c23ab8ecb21461875526390a30c3aa831a851847671d94428c23ab8eca21461875944310a30d3087300851863a54580428c21ebacc9194610fdd5648ca3087aed2a4651843f76552328c2b2b8ca519461a610e608ca3087aebb22651843d75191328c21f3b4a8994610f1d9544ca30e188
  | 21 => 0x237bb0a418a811b5d8520c540cccc5a8862a066562d44315031b320a218a8199988510c540ccac428862a065853980315033828cc018a8117dcd65c85408b8e6b2e42a061e6414f215030eb20a790a818b99052c8540c5ac829642a063664d47215032c29cc190a819a14a60c8540ce6a330642a0658535832150334292c190a8117dcd65885408b8e6b2c42a061e6414e215030eb20a710a818b9935288540c6cc828c42a063564146215032c29cc110a819ad4a6088540ce0a330442a065853582215033828ac110a81179cf65485408bae7b2a42a043e75991215024e39ac890a812e1c16448540c3cc829a42a061d6414d21502b338ea490a81599cb51485408bee6b2842a045c73594215025c382c810a81879905308540c3ac829842a062e6414821502b2b88a410a818d9905108540acae428842a05667548421502b23aa4210a81999952108540cc8ca90842a07475348421503a229a4210a81d214c52d0140ea0a628e80a076052147405030f318a7202818714d6290140e18a7a9480a070c5314a405030e29ac320281c514f5190140e28a628c80a072452146405023bb8ac5298811d1c56294c408dee4b0ca62046c72586531022fbb2a62988147dd54310c40e34a7300862071a53580431025dbaac0218818edd56010c40c74a6b0086206ab725804310354392c021881acdc56010c40d60e2b00862056671d4a521023b388c6a90811d5c46354840a72e021aa42046f76548521023b38ccb190811d5c6658c840972e1324642062e6454a321023bb8aca990811d1c5654c840c58c92926420666521853210332a90c2990819a948604c840cd2a4302642047671d94321023ab8eca19081599cb51944408dce431aa22046d7218d511029cb8086a88811ddd951144408dce532c622046d72996311025cb84c9188818d991518c4408dee4b2a622046c72595311031a324a2988819918a514c440cc8c4a8a6220672511813110338a88c0988811b9cb650c4408dae5b28622045f73595211022e39aca908810f5d76448440acae329042205657294421102b3baa4210881595d52108440c3cc729e802043d76952401023cbb4a9200810f9cf6550040c3ecbb1a802061f6518d401030fba8c6a0081a65c06350040878ed29a802061c6394d4010317b2ec4a0081a318f6250040c5eca312802068c63189401030e31aa4a00818dd976150040d28c7b0a802063765185401034a318c2a0081a91886150040c38c6a8a802065b65d8d401032db28c6a0081a6d906350040974eda1a802053b7550d4010335b2ec4a00819ad946250040d90c63128020539759094010339b2ec2a00819cd946150040da0c630a80206e062185401029cbac82a00819398e62d5330c9cc6b16a9986566398754cc333314c3aa6619958a61d5330cacc6b0ea99866
  | 22 => 0xa81999945214540e8ea6290a2a0744531485150392ba0a428a81c95905214540e4c86290a2a072443148515029b3ae8428a81c514f4214540e48a5a10a2a07145350851503922928428a816c1c14214540a6ae9b18a2a05377458c51502b3b92c628a81591c96314540ae6e0b18a2a05357418c51502b3390c628a81595c86314540ae2e0318a2a05357690c51502b9b828628a815c1c14314540a6aec218a2a07167310c515029aba6c428a815c5c36214540a6ae8310a2a06656218851502b9b828428a815c1c14214540a6ce9190a2a0535748c8515023bbb26428a811d1d93214540a6ee8990a2a0534744c851502b9b826428a815c1c132145408ecec190a2a0475760c851502b3396c028a81595cb6014540aaee6a00a2a05547350051502b3b928028a81591c94014540974e131e82a061e6314f415030f328a7a0a8187dd853d0540c38a6b1682a04b87058b415038629ea5a0a818b99452d0540e18a629682a063665d47415038a29ea3a0a81c5d4c51d0540e28a628e82a0727521474150392290a3a0a818d98c51d0540c38a730682a067051982415032c29ec0a0a819a14b6050540cb0a630282a0668521814150339a88c0a0a818718c5350540c3eec29a82a061c7614d415030e29ec4a0a81c314f5250540e18a629282a071453d85415038a29ea2a0a81c514c5150540e48a428a82a071853d81415030e298c0a0a81c614c6050540974ea30282a063a75181415034da98c0a0a818e14c6050540d30a630282a0618531814150355a90c0a0a81aa1486050540d66a230282a06b0511814150237b92cb98a811b1c965cc540974e1b2662a061f6414f315031a320a398a811bdc9658c5408d8e4b2c62a04b870592315030f326a718a8187990538c540c3ac829c62a062e64d4a3150316b26a518a818b990528c540c5ac829462a063664d46315031ab26a318a818d990518c540c6ac828c62a046e72d953150236b96ca98a811b9ca654c5408dae532a62a061c64d4d315030fb20a698a8187190534c5408dcebb1262a064f53d89315032629ec498a811b9d4624c540c9ea631262a064c5318931502373b6a498a811b1db524c540c5ec9a9262a062c64d4931502373b0a498a811b1d8524c540c5ec829262a062c64149315031bb26a298a818d193514c540ccec5a8a62a066462d45315031bb20a298a818d190514c540ccec428a62a066462145315032c29ec098a819ad4b604c540cd0a5b0262a067051d81315032da98c098a819614c604c540cd6a430262a0668521813150339a88c098a819c144604c5408dee4b2862a046c725943150237390ca18a811b5c8650c540c3cc829862a061d6414c31502373acc418a8193d4e620c540c98a731062a046c755883150327a9ac418a819314d620c5408deeda9062a046d76d483150
  | 23 => 0x8c940970e0b2464a061e64d4e325030f320a71928187590538c940c5cc9a9464a062d64d4a3250317320a5192818b590528c9408ece3b2a64a047571d95325023b38cca992811d5c6654c940c38c9a9a64a061f6414d325030e320a6992818bd93524c940c58c9a9264a062f641493250316320a4992811d9d7614c940caea7b0a64a065453d853250333a96c2992819914b614c9408ecea30a64a065753185325032a298c29928199d48614c940cc8a430a64a065853d813250334296c09928196d4c604c940cb0a630264a066b521813250334290c0992811ddc5650c9408e8e2b2864a047671194325023ab88ca1928187990530c940c3ac829864a062e64148325023b3acc21928195d4e610c940ca8a730864a0667529843250332294c2192811d1d5610c940caea6b0864a0654535843250333a92c21928199149610c940cb0a730064a0668529803250237394c7a8a811b5ca63d4540e2ae9a9ea2a05667294f51502b2b94a7a8a8159dc953d4540ac8e4a9ea2a07177414f515038bb20a7a8a81c514e43d4540b64e121ea2a07175310f515038a29887a8a81d1d4f52d4540e88a7a96a2a072643d4b515039221ea5a8a81559ce52d4540aaae7296a2a05577354b51502aa39aa5a8a81d1d4c52d4540e88a6296a2a07257414b5150393218a5a8a81c910c52d4540e28a7a16a2a072452d0b515038a29a85a8a816c1c142d4540a6ae9b1ea2a056672d8f51502b2b96c7a8a815c5c363d4540acce531ea2a05657298f515029bba2c7a8a81c59cc43d4540ccec5316a2a05357418b51502b8b80c5a8a814d9d232d4540a6ae9196a2a0477764cb515023a3b265a8a814ddd132d4540a68e8996a2a0573704cb51502b838265a8a811d9d832d45408eaec196a2a05677258351502b2392c1a8a8193d4e6294540c98a7314a2a064f5358a515032629ac528a819398f5294540c9ac7a94a2a064e6314a5150326b18a528a819598f5194540caac7a8ca2a066662d465150332b16a328a81179db53545408bcec29aa2a064f53d89515032629ec4a8a8193d4c6254540c98a6312a2a046e76d495150327b1ea4a8a819318f52545408dcec292a2a064f631495150326318a4a8a811ddd95114540aaee6a88a2a05547354451502b3b92a228a81591c951145408dee4b18a2a046c7258c515029ab8c8628a81959975314540e2ae9a98a2a071564d4c515023abb4a628a81599ca5314540acae5298a2a04777654c51502b3b92a628a81591c95314540cacca298a2a07177414c515038ab20a628a81c514e4314540b64e1218a2a07175310c515038a2988628a81999975214540e8ea7a90a2a074453d485150392b26a428a81c990f5214540e4887a90a2a04757694851502ab39ca428a81555ce52145408eeeca90a2a05577354851502aa39aa428
  | 24 => 0xb20a6a051d71d90535038d386c829a81475d26214d40a3ee8b10a6a05577158853502aa38ac429a8156dc16214d40a3ae8310a6a05567118853502aab88c429a81565c06214d40a3ae9308a6a051f7458453502a7b92c229a81531c96114d40ab6e0b08a6a051d7418453502a7390c229a81535c86114d40ab2e0308a6a054f7258053502a6392c029a8155dc56014d40aa8e2b00a6a065853982435030e29ac521a818714d6190d40c38a730486a071853982435025d3acc121a818e9d66090d40d36a730486a063853982435034c29cc121a818614e6090d40e30a6b0486a065b53181435030f328a621a812e1c16210d40970e0b0886a04767198f525023ab8cc7a9281c35d353d4940acce329ea4a05657194f52502b3b8aa7a9281591c553d4940e1ee829ea4a070f6414f525038629c87a92816a9c243d4940e1ea621ea4a070c5310f5250296ba6c7a9281599c763d4940acae3b1ea4a056970d8f52502b338cc7a9281595c663d4940a5ee8b1ea4a070e7310f5250333b0cc3a92814b5d061d4940ad2e030ea4a05677158352502b238ac1a92819398f5294940c9ac7a94a4a065753986525032a29cc32928199d4a6194940caea6b0ca4a0654535865250333a92c329281179db53549408bcec29aa4a065753d85525032a29ec2a928195d4c6154940ca8a630aa4a046f7654852502a7b9aa429281531cd5214940acee2a90a4a056471548525023bb8ac6292811d1c56314940a5ae5218a4a064e65d4c5250386ba6a629281c359353149408daed298a4a05667194c52502b2b8ca6292811bdd95314940acee2a98a4a05647154c5250327328a629281c3dd05314940e1ac8298a4a070c5390c52502d53848629281c3d4c4314940e18a6218a4a052d74d8c5250297ba2c62928159dc56314940ac8e2b18a4a056b7058c5250296ba0c629281599c46314940acae2318a4a05697018c5250296bb486292815adc14314940ad0e0a18a4a052d7610c525038739886292814b5d36114940ad2e1b08a4a052d741845250332b08c229281599c76014940acae3b00a4a054f7350052502a639a80292812e9c263d0940c3cc629e84a061e6514f425030fbb0a7a12818b99752d0940e18a7a9684a070f5314b4250386298a5a12818b98c52d0940c38a6b0e84a04b870587425030e29cc1a12819a14a6090940cb0a7b0284a0658531814250335a90c0a12818718c5350940c3eec29a84a061c7614d425038629ec4a1281c314f5250940e18a629284a061c53d85425038c29ec0a12818714c6050940e30a630284a04ba75181425031d3a8c0a1281a6d4c6050940c70a630284a069853181425030c298c0a1281aad486050940d50a430284a047771597325023a38acb992812e9c364cc940c3ec829e64a062c6414b325023bb8acb192811d1c565
  | 25 => 0x7590d2108753b2c8690843c9d964348421b4ce721a4210ea66390d210875231c8690843c9d4e4348421e4aa721a4210ce77650d21086723b28690843599d44348421acaea21a4210ec46310d21087a2a988690843c99d44348421e4aea21a4210ea76510d2108793b288690843699cc4348421f0ce621a4210f876310d21087533188690843a918c4348421f08c621a4210e846310d2108793a988690843e194c4348421e4aa621a4210f855310d2108782a988690843595d66048421aceeab024210da77458121086d23a2c09084371dcd6048421b88e6b024210da67418121086d2ba0c090843b858060484219ceec90ea010c5f73592500862e39ac9280430fdd16394021878e8b1ca010d65710ca50086b2b90632804399dd92194021cc8ec90ca010d667348650086b239a43280439958d2194021e4c8690ca010f244348650087b1b824328043d81c1219402187ce9b1aa010c3d74d8d500870fb1886a80438718c43540219ceec908a010ea6644845008752b224228043b198d2114021d8ac6908a010c7b765405008696b90c929e814d5c46494f408ece2312a7a04757118953d0237390c2a9e811b5c86154f408beeca98a7a051f7654c43d030fbb2a621e81c694e6010f40e34a6b0087a04777158e52d023a38ac7296811bdd95214b40ccaa4b08a5a061c6394d42d023b38ccb996811d5c665ccb408eee2b2a65a04747159532d023b38eca196811d5c7650cb40ccca4b0865a06655258432d0237b92c728e811b1c963947408eeeca88a3a06656254451d030e31ca6a0e811b9ca65cc7408dae532e63a046f7259531d0236392ca98e811b9cb650c7408dae5b2863a06656294431d0332b12a218e81271cd6448740970e0b2243a05647154921d02b2392a290e812e5d060487408bce7b2843a045d73d9421d0333b2a4210e819959521087408beeca98a72071a53982439038d29ac121c81275db5310e40b34e1a98872059a7014c439030f31887294818718c4354a408deeca90a52047771595329023a38aca994811d9c7650ca408eae3b28652061e6310e519030e31886a8c811ddd951146408dee4b2a632046c725953190237396ca18c811b5cb650c640c3cc729e81204767198b535023ab8cc5a9a811b9ca61d4d408dae530ea6a051d74d8b53502ab38ec5a9a81555c762d4d40ab2e1b16a6a05567198b53502aab8cc5a9a81475d062d4d40a3ae9b0ea6a054e72d8753502a6b96c3a9a81565c361d4d40a9ce530ea6a054d72987535028eba0c3a9a81539cb60d4d40a9ae5b06a6a055671d8353502aab8ec1a9a8193d4e6294d40c9ea6b14a6a065753986535032ba9ac329a8117dd95314d40a9ee4a98a6a054c7254c53502abb8aa629a81551c55314d408eee2b10a6a0474715885350237b92c229a811b1c96114d40a3ae5
  | 26 => 0x1ab288798843c554c43cc421acaebb166210e6565d8b31086b2bae65988439959732cc421f08879966210d65750cb3108732b2865988430f9d3658c42187ae9b2c6210e1e6494e310870f322a7188431bdd5628c42187ce93286210c3d749943108726a9cc4188431ddd9530c421ae0e0a986210e356590c310871ab288618843c554c430c421ccacb3106210c77755883108732b2ac41884339dd5620c421cceeab106210e67535883108732a9ac418843a990d620c421d4886b106210c75769483108732b14a418843595d7320c421ccacb9906210d65750c83108732b286418843e110c320c4218deeca9e4210e4e6354f21086b4382a790843c354c43c8421d8cc798e4210d65750c72108636bb4a5108431ddd95388421cacc6a9c4210d707054e210878aa9887108431d5da5288421d8cc79944210d65750ca2108636bacc6908431b9db53484218d8eca9a4210e4c6354d21086b4382a6908438bd964348421c5eca21a4210e8c6310d2108786a988690843595d73148421d88c798a4210ce6768c521086d33a46290843695d23148421e8aa718a4210ce4764c521086d3ba26290843691d13148421bc6e098a4210de0704c521086b2ba862908431d5d663484218eceda9a4210c747654d210872a31aa6908435c1c15348421c6ecb21a4210e376510d210874a3188690843c554c4348421acaeb9924210ec463cc921086733b46490843699d23248421b4ae91924210f45538c921086723b2649084369dd13248421b48e89924210de3704c921086f03826490843595d43248421ccaebb2a4210ce673d9521087333b6ca90843595cf6548421acce1b2a4210d657599121086b3baac89084371dcd6448421b88e6b224210de37059121086f0382c890843a959064484219ccedaa24210dc673d5121086e2b9ea890843399d85448421b4ce9b1a4210da574d8d21086b2bacc690843395d66348421ccaeb31a4210ce67398d21086b3baac69084369dd16348421b48e8b1a4210de37058d21086f0382c690843995d46348421d8ce631a4210ce676d4d21086d33a6a690843695d35348421acceda9a4210e6676d4d21087933a6a690843c95d35348421cccc7a9a4210e6463d4d21086b3386a690843391da5348421acaeb29a4210ec46394d2108673bb2a690843391d95348421b4ee8a9a4210da47454d210876231aa69084378dc15348421bc0e0a9a4210d667654d21086b23b2a690843991d953484218c8eca9a4210f277454d21087923a2a690843d1dcd5348421e8ec6a9a4210e666354d210873231aa690843d118d5348421ec6e0a9a4210d647054d21087b0382a690843581c153484219ccec29a4210d667514d21086733b68690843395db4348421d88c7a1a4210f4553d0d21086b33ac8690843595d64348421e4ceb21a4210f25
  | 27 => 0x43b414c604c521d64863026290eb0431813148771b90c098a43b81c8604c521dc4643026290ee1321813148679386c790a439558c53c8521e28a621e4290ec5638cb21486f03826590a433a9c36388521c9ac629c4290f0c5310e2148762b1c6310a43781c1318852187ee8b1ea090c3c7458f504870f31887a82438758c43d4121938e6b20a090c7b76540504869c3a2a028243561cd501412187ce7320a090c5f73590504862e39ac828243471cd6414121c3ee6b20a090c3c73590504870e39ac828243071cd6414121c5ee4b20a090e2c72590504871bb8ac8282438d1c56414121c70e0b20a090c3f7458c504861e3a2c6282430fdda431412187aed218a090c3f7610c504861ebb0862824387dd263d5021c9ac7316a810e5563987540868f39ea92a043479cf645502187eecaa0a810d1e74d4e530861f3a4c1298430f5d26094c21c3ae7b22a610d1e74d8d5308717b20c4a98438b1906254c21c6ec830aa610e34641855308732310c2a98438ed936054c21c70c9b02a610e6862d81530873830ec0a98438ed906054c21c70c8302a610e68621815308738308c0a984317dd95314c218f4e1b2e8610c7970d9743086ac382a7a18431b5d662d0c219cae33168610c75759874308672b94c3a18431b9c86590c218ece232c8610d1e73d96430868f398cb218434b9c86590c21a6ce232c8610d3b7054e430869c382a7218434b9c85390c21a6ce229c8610c3f74595430863db82caa18431e1c16550c218daea3128610ce571189430863aba8c2a1843395c86150c218dce43288610c7671194430863d380ca218431e5c06510c21a3ae7aa08610c3d76150430868eb98a82184347dd15310c21ab0e0a988610d1e73d94430868f398ca218434b9c86510c21a6ce23288610d3a70194430869cb80ca21843475d66310c2187aeda988610d1d7594c430868fbb4a621843475da5310c21a3ce12988610c3f7654c430869db82a6218434e1c15310c21b30e0a988610d1f7654c430870fbb2a621843c31c95310c21e28e2a988610f1b7054c430868e382a621843c61c15310c21a30e0a988610d1e7314c4308697390a6218434d9c45310c2187ee8b1ca410c3c7458e520873238acb990435a1c153cc821c5acb21e6410e2d6510f3208786a988799043595d761cc821ccacbb0e6410c3e74d96320861eba6cb1904387992538c821c3cc8a9c6410c7775586320872aa9cc2190431bdd9530c821ad0e0a986410e2d6590c3208716b288619043c354c430c821ccacb3086410c6f755843208732b2ac21904339dd5610c821cceeab086410e67535843208732a9ac219043a990d610c821d4886b086410c3f7458e510861e3a2c7288431b5d83294421acae2194a210c5e73994410862eb9cca20843991c965cc421ae0e0a9e6210e356590f31087
  | 28 => 0xd2187ae932a8690c6f72595434863bb8acaa1a431edc16550d218f0e0b2a8690c7b70594434863c382ca21a431e9c06510d218f2e03288690c3d76950434868eb9ca821a4347dcd5410d21a76e0aa08690d3870550434868eba6a621a431b1d56210d21c58a8b108690ce471588434863a3aac221a438d1516110d219c8e4b088690d1e73d94434869db82ca21a434e1c16510d21a3ce63288690d3a70194434869cb80ca21a43479d66310d2187aeda988690d1d76d4c434870ebb6a621a43479c35310d21a3ce72988690c3f7654c4348697b92a621a434ddc55310d21a76e0a988690d387054c434868f3a8a621a4347dd85310d21a3aec2988690f0d7214c434878ab88a621a43479c05310d21e18a73108690d2c75588434871632ac421a43c314d6210d21b48e2b108690f1453984434869a3aac221a438d1956110d21e28a6b088690da472584434871a2a2c3a1243995c6658c921c5ccb3246490e2e65592324871732c87192438b994438c921e18a621c6490de270d8632486b33a8c31924399994618c921d4cc830c6490ea564186324867338cc11924387193534c921c38c829a6490e5453d85324872da98c0992439614c604c921c58cbb226490e2c6519132486373b0a6992432b9da434c921c58cb21a6490cae7610d32487163288699243c314c434c921cc8cbb0a6490ea7641853248752320c299243399d4614c921cccea30a6490e66531853248732298c299243a990c614c921d488630a6490ce670185324873432ec099243b8187604c921cd0ca3026490eab641813248754320c099243b8d84604c921dc0c23026490ecb531813248735298c0992439a14c604c921d90a63026490eaa431813248754218c099243b8dc4604c921dc0e23026490e2c5458b414862fb9acaa0a43171cd6550521ccae532c6290e3665992314871b32ac918a438d996438c521c6cca21c6290f145310e31486f1386c518a43599d4628c521cccca3146290ea66418a3148752b20c518a43599d6328c521ccccb1946290f84438ca31486b23aa6518a4399995328c521bc0e09946290ce672982314861fba2ca98a430f1d1654c521c38c9a9a6290e1c6414d314872629ec498a4396d4c604c521cb0a63026290e3465d91314871a328c898a431d9d8534c52196ced21a6290e346590d314865b3b08698a438d194434c521e28a621a6290e6465d893148753b20c498a43a9190624c5219ccea3126290e66751893148733298c498a439914c624c521d4c863126290ea4431893148673380c498a43599d6324c521cc8cb1926290d64754c9314873232a6498a43e110d324c521bc0e09926290e7065d813148770316c098a439c194604c521d66c83026290eb0641813148771b10c098a43b8188604c521da6a63026290e72531813148738298c098a
  | 29 => 0xa910e7071580548871b324c3a9c438d59261d4e21ccac530ea710e3a64983538871cb24c1a9c439a58a60d4e21ce4c3306a710e3a64583538871cb22c1a9c439c98560d4e2187ce9304a710c3d749825388717b26c4a9c438b1936254e218beeca98a710e6562984538863d380cba1c431e5c065d0e218f4e132c8710c7970996438869d380a921c434e5c05490e21c6aa930c8710d1e73d96438869d384cb21c434e5c26590e21a3ce632c8710d3a70d4e438869cb86a721c438dd966190e218f4e132a8710c7970995438863d380ca21c431e5c06510e21a74e02a08710d3970150438868f39eca21c43479cc6510e21a74e03288710d3970194438861ebb6a621c434e9c35310e21a72e1a988710c3f7654c438871aaa0c2a14435a9c353cca21caca630a6510c6d76d4c32886b5386a619443c3d4c430ca21ccacb3086510e67535843288732a9ac219443a990d610ca21d4886b086510e3565992318871ab2ac918c43e110c328c621c6ecbb226310e3765191318863b3b0a698c432d9da434c62196cec21a6310f145310d3188733b2ec498c43a9d90624c621d48c83126310e66531893188732298c498c43a990c624c621d48863126310ce676cc931887c221e6498c43399d8324c621ce6cbb026310ee062d813188739b28c098c43acd90604c621d60c83026310ee3621813188770310c098c439c94c604c621ce0a63026310eb2431813188758218c098c43b8cc8604c621dc0643026310e4d5358831886b5386a790c431bdd953c8621c9cc6a9e4310cf270d8f218863abb4a790c439558e53c862187ee8b1ca110c3c7458e50886b2b8865284430f9d3635422187ae9b1aa110e1f6310d508870e31886a84431edd95014221c72c8a80a110e1f6418d544870fba0c6aa2439318f6255121ca8c7b0aa890e5b63d81544872c31ec0aa2438ed906055121cb6c6302a890e58631815448735b10c0aa2439cd84605512187eecaa0a890d1c73550544869c382a82a24317dcd60151218b8e6b00a890e1f73593534861f3a4c129a430f5d26094d21c38c9b1aa690e2f64d895348716326c4a9a438dd936154d21c68c9b0aa690e3b64d81534871c326c0a9a439ad8b6054d21ce6c3b02a690e3b64181534871c320c0a9a4396d8c6054d21cd6c4302a690e7361181534862fbb2a629a43471d15314d21ab0e0a98a690e6562584534861fba2c029a430f1d16014d218dae5b2e8690c7571d97434863d386cba1a431e5c365d0d218f4e1b2c8690c7970d96434869db82a921a434e1c15490d218d8eab148690ce47158a434863a3aac321a43391c96190d21a3ce7b2c8690d3a70d96434869cb86cb21a43479cc6590d21a5ee4a9c8690d377154e434869db82a721a434e1c15390d21a58eab148690da47158a434869a3aac321a43691c9619
  | 30 => 0x3189310c752218c498863b110c624c431d08863126218ce476949310c733b2ca498863e110e524c431e2886a926218e6462549310c6723b2a49886399d95524c431f0886a926218d6676549310c6b23b2a498863991d9524c431e4ec8a926218f2464549310c7a3b1aa498863d1d0d524c431e4c86a926218f2443549310c7a221aa498863c110d524c431ce6cbb026218f9043d81310c770316c098863d854b604c431d28863026218e6552181310c739b28c098863acd90604c431d60c83026218f9043181310c771b10c098863b8188604c431ec2a43026218ed253181310c769a18c098863ac90c604c431d60863026218ed043181310c748218c098863b8948604c431ce2a43026218ee152181310c730a90c0988631bdc964940318d8e4b24a018c6d76948500c717324a4280638b59252140318deeca90a018e2e64548500c716b22a4280631edd95014031c72c8a80a018e666258754c861fbb2a82a6438e5516015321cccc4b08a990e716198054c871d322c02a6439a9896015321cd0e4b00a990e2e6498b53c8716b24c5a9e439998961d4f21c74c9306a790e396498353c8735314c1a9e439c58660d4f21c74c8b06a790e396458353c8735312c1a9e430f9d26094f2187ae9304a790e3764d8553c871a326c2a9e4317dd95314f21cccc4b08a790c7a7019743c863cb80cba1e431e9c26590f218f2e132c8790d3a7015243c869cb80a921e438b5526290f21a3ce7b2c8790d3a7099643c869cb84cb21e43479cc6590f21a74e1a9c8790d3970d4e43c8717b2cc521e431e9c26550f218f2e132a8790c7a7019443c863cb80ca21e434e9c05410f21a72e02a08790d1e73d9443c868f398ca21e434e9c06510f21a72e03288790c3d76d4c43c869d386a621e434e5c35310f2187eeca988790e2d6599232c8716b2ac9196438bd97644cb21c5eca3226590c6e7614d32c86573b486996432b9d8434cb21e18a621a6590e6765d8532c8753b20c299643a9190614cb21ccca630a6590e645318532c8753218c299643a910c614cb21cd6cbb026590ee061d8132c8735b28c099643aad90604cb21d50c83026590ee36118132c8770308c0996439a94c604cb21cd0a63026590eaa4318132c8754218c0996439554d610cb21c5aa83128390d7270d4f31c87c221a6598e43781c132cc721c9ca63126390c7576d4c31c86b9386a618e43c5d4c430c721ccacb3106390e675358831c8732a9ac418e43a990d620c721d4886b106390ce5768c831c87c221c6418e4339dd9320c721bc0e09906390c3f7458e50c861e3a2c728643595c8319432187ce9b1aa190c3d74d8d50c870fb1886a86438718c43543218f6eca80a190e396454050c8732b14c3aa4430fdd95415221c72a8b00a910e65629845488734b14c02a4438e9916015221ce4c2b
  | 31 => 0x439262282639398d62d5031ccac530ea818c6f72582540c636392c12a0630fdd95415031c72a8b00a818e6562984540c735314c02a0639a58a6015031c74c8b00a818e6a62580540c734b12c02a0639c9856015031ce0e2b00a818d2e72996430c696b94cb218634e9c26590c31a72e132c8618d1e73196430c697394ca218634b5ca6510c31a3ce63288618d1d7598c430c70eb2cc621863655c66310c31ad4e02a4a418d6970152520c78739887290634b9d06194831a5ae830ca418d6671d82520c6973a0c1290634b5d06094831cd2c0304a418c3e74181520c61eba0c0a90631b9db54548318dcec2a2a418d6a70151520c6b4b80a8a9063599c66454831a98e6b22a418d6471591520c6b5b82c8a90635a1c16454831acce321aa418d657190d520c79338c86a9063c95c64354831acce221aa418d657110d520c78739886a9063c99c44354831e4ae221aa418d2e74985520c696ba4c2a90635a9c26154831ad2e130aa418f2643185520c792218c2a9063599c06154831acce3b02a418d6671981520c697ba2c0a90634b1d16054831a98e6b02a418d6471581520c6973a0c0a90634b5d06054831cd2c0302a418c6f76548520c732a94c3a10639954961d08318f6e0b2a8418c7870595420c727b1aa4a10639318d5250831ccaa5b0a8418e6552185420c732a92c39906387594438c831c5cc8a946418e2d6454a320c78621aa5190638bd92524c831c58c92926418e6652d85320c735296c0990639a948604c831e1886a906418e6552984320c74a21ac21906399949610c83187aed21ca218c3d7610e510c69cb80a9a08639398d5290431c9ac6a948218c3e76151410c69cb80a8a08630fdd95410431e1886a966218c5d7694e310c717324a5188638b592528c431c5cc8a946218e2d6454a310c63abb4a71886399989528c431e4cc8a946218f256454a310c79321aa518863c910d528c431ccaa53046218e1f6590d310c70fb288698863a310c624c4318d8ed2926218e2f64949310c716324a4988631b9d9524c431c5ec8a926218e2c64549310c78621aa4988639a94b604c431cd2a5b026218e9843181310c735290c0988639a548604c431c9ee5b2a6218e4c72d95310c70fb2ec89886387d94644c431c9ecbb126218e4f65189310c746320c49886393d96524c431c9ecaa926218e5b65d81310c72db28c098863a6190604c431d90c43026218e6772d95310c732396ca988638dd97644c431c6eca3226218d9674d8d310c65b3b486988638dd96434c431b2ce721a6218cb67610d310c71bb288698863659d8434c431d2cec21a6218e976510d310c78bb28869886399d97624c431f0887b126218e9443189310c733b28c498863a9d90624c431d48c83126218f8443189310c732ba8c498863b194c624c431d8e863126218ea64
  | 32 => 0x39958852cc531e4ea82966298f245414b314c793218a598a63c910c52cc531c5cc9a946298e2d64d4a314c717320a518a638b590528c531e18862946298f0c5414a314c61f3a4c5a82630f5d262d4131ad4e52a6a098d6972953504c6b5b92a9a82635a1c954d4131a74eb21ea098d3a7510f504c795aa6a5a8263ca15352d4131e5487a96a098f2843d4b504c69d3a4a5a82634e5d252d4131a76e8a96a098d387454b504c795aa0a5a8263ca15052d4131e5486296a098f284314b504c7b0b88a5a8263d814b31d4131ab2e7b26a098d6a72d93504c6b4b96c9a82635c5c764d4131a74e9b1ea098d3974d8f504c6b5396c7a82635a5cb63d4131e34e621ea098d3a7498b504c69cba4c5a82635c5c462d4131a74e9196a098d39748cb504c63dbb265a82634edd132d4131a70e8996a098d73714cb504c6b838a65a82635c9c432d4131a74e918ea098d39748c7504c717aa4c5282638b1526294131c5ea8b14a098e2c5458a504c717326a5282638b5935294131c5cc8294a098e2d6414a504c71d326a1282638e5935094131cd4c5a84a098e6962d42504c61f3b6a8a82630f9d85454131c5ea9b12a098e2c54d89504c717aa0c4a82638b15062541318dceda92a098e2f64d49504c716326a4a82631b9d85254131c5ec8292a098e2c64149504c63dbb2a0282634edd15014131a70e8a80a098d6b72540504c6b4392a0282631bdc964141318d8e4b20a098e3a65d50504c63cbb4a8282635a9ca5414131ad2e52a0a098c7b76550504c6b5b92a8282635a1c95414131c74ca2a0a098d3a7590c504c69d3a886282639a9975214131e56a9a90a098f2854d48504c79521ea428263ca10f5214131ec6e3a90a098c7976948504c69d3a4a4282634e5d252141318f6eca90a098d3b74548504c69c3a2a4282639a9945214131e56a8290a098f2854148504c795218a428263ca10c5214131ec2e2290a098f3354cc4504c7982a66228263d8d4b3114131ec0a5988a098f18548c4504c7a4294622826356dcd6414131ad6e4b20a098d6872590504c6b9b8ac8282635c5c46414131a74e9b18a098d3974d8c504c6b938e86282635c5c74314131ae6e2a18a098d707150c504c78d3988628263c6d8c4314131ae2e3310a098d3a74188504c69cba0c428263565cc6214131ae2e2310a098d5a73908504c6acb9c84282635c9c64214131ae2e3210a098d7271108504c6b8b888428263c610f3214131a74e9190a098d39748c8504c6b938c64282635c5c632141318f6ec990a098d3b744c8504c69c3a26428263c610d3214131ae6e2990a098d70714c8504c6b9388642826356dcd4114131ab0e6a08a098f3243cc4504c79821e62282635c5cb3114131a74e9188a098d39748c4504c78c21c62282634edd13114131a70e8988a098d6b724c4504c6b
  | 33 => 0x131a5ee4aa0a898d2c72550544c69db82a82a2634e1c15415131a5ce5320a898d2d72990544c69d384c82a2634e5c264151318dee4b00a898c6c72580544c69ab88c42a26347dcd6015131a5ee4b00a898d2c72580544c69bb8ac02a2634d5c46015131c68a930e8698d2e72952434c696b94a921a634e9c25490d31a72e12a48698d2f72552434c696392a921a634edc15490d31a70e0aa48698c3e76151434c71baa0c2a1a634b9ca5410d31a5ae52a08698d3a70950434c69cb84a821a630fdd95410d31a5ee4aa08698d2c72550434c69db82a821a634e1c15410d3187ce9306a498c3d74983524c6b5384a9a92635a5c254d4931ad6e0aa6a498d6870553524c6973ac87a92634b9d443d4931a5ce9b1ea498d2d74d8f524c6b5386c7a92635a5c363d4931e1ce621ea498d2e74983524c696ba4c1a926359dc560d4931c5cc9a94a498e2d64d4a524c71daa4c1292638e1526094931cd6a5304a498e3b54582524c71c2a2c1292639ad49609493187cedaa2a498c3e76151524c71daa6c0a92638e1536054931c76a8302a498e3854181524c637bb2a4292634bdd15214931a58e8a90a498d6b70548524c6b4382a4292638b99754149318daed2a0a498d6a70950524c6b4b84a8292631bdd95414931ad6e0aa0a498d6870550524c717328a8292634b9d64314931a5cea218a498f2754584524c7922a2c229263535cf6414931acae3b20a498d6571190524c6973a6c6292634b5d36314931acce3a18a498d6571d0c524c6b3b8a8629263591c54314931e1ce6218a498f2643584524c79221ac2292634bdd13114931a58e8988a498d6571d80524c732b0cc0292634b9d06014931a5ae8300a498d4d73180524c6b2b88c0292631edc165d09318f0e0b2e8498c7b70596424c63c382cb2126387d526390931c9cc62948498e4d6314a424c71baa4c3212639914a6190931cc8a4b0c8498c7a70d95424c63cb86caa12631edc165109318f0e0b288498e3454984424c732294c221263991496110931c3cca21e6498f0c4314b324c61f3acc9192630f1d5648c93187aedaa46498c3d76152324c717326a5192638b593528c931c5cc82946498e2d6414a324c732294c3192630f9d7644c93187cea3226498c3e76d51324c61f3b0a8992638bd93524c931c58c9a926498e2f64149324c716320a499263c310c524c931c6ea9b0a6498e3454d85324c732296c2992638dd50614c931c68a830a6498e9443185324c733a90c2992631e9d7604c931c76a9b026498e3854d81324c735a96c0992639a14b604c9318f4ea3026498e3b54181324c71c2a0c099263a610c604c931cd6a43026498e6852181324c71baa4c2192638d152610c931ccea53086498e1c5498f414c70faa0c6a0a6393d8c5250531c98c62928298d367590f314c69b3a88798a6
  | 34 => 0xc6420c79709963210717322a5190831edc1654c8418f0e0b2a6420e2c649493210733290c29908399548614c841cd4a43026420e6952181321070f31ca7a08830f5da54904418eaed2a48220c3e73d95411061e3b4a6a08838718e5350441ad4e5a84a020e1f6310d501063dbb2a0280839598d61d533187eecaa0a998c6f7258054cc636392c02a6631bdd95214b318f4e1b2e8598c7970d9742cc74a218c299663a610c604cb31ccaa4b086598c3e7695141cc61ebb6a820e63471cd6494331c3ee6b24a198e1c7359250cc71bb8ac9286638d1c5649433187aed21ca198c3d7610e50cc71721ec4a86638b10f6254331c5c86312a198e2c4318950cc63dbb2a0286639558e61d52318dee4b04a918c6c72582548c697396c72a4634b5cb6395231a74e1b1ca918d3970d8e548c69b388c52a4634e9c06295231a72e0314a918d2e72186548c696b90c32a4634e9c06195231a72e030ca918d1f73582548c697b92c12a4634b1c96095231a68e2b04a918d2e72182548c696b90c12a4634d9c46095231c72c0304a918d2f7258d548c696392c6aa4634edc16355231a70e0b1aa918d3671989548c68fb9ac4aa4634b9ca6155231a5ae530aa918d1f73581548c697b92c0aa4634b1c96055231a68e2b02a918e3960181548c61fbb2a82a4638d95161d0e3187ced2a28718e3554d85438c61ebb6a821c638e95260d4a31c72a9306a518e3a54583528c71caa2c1a94635a9c35294a3187ce8302a518c3d74181528c61ebb4a8294630fdd95414a318deeca90a518e3554586428c70eaa0c6a14631e9c36510a318f2e1b288518e3654584428c61ebacc9194630fdd5648ca3187aed2a46518c3f76552328c61ebaec8994630f5d4644ca3187ced2a26518c3c76551328c71b2a6c2994638d553614ca31c6ca830a6518e3554185328c733290c2994638e953604ca31c72a9b026518e3a54181328c71caa0c0994639a948604ca31cd2a43026518e3654584328c71aaa2c219463a510d610ca31c3aa931c8318e1e5498c418c70eb2ca998c638759554cc6319cee4b2e6318d6472597318c71ab2ca998c638d59554cc631ccac52966318e2e5498b508c716aa4c5a84638b95162d4231c5aa8b16a118d6a72d42508c61f3a0c4a84630f5d0625423187aed2a0a118c3f76550508c63dbb2a028463475cc62d5131a6ae2316a898d1d73d83544c697396c1aa2634b5cb60d5131a6ae3b06a898e2f5498a544c717aa2c52a2638ed526095131c76a8b04a898e6662586544c735314c12a2639a58a6095131ce2c3304a898e6a62582544c734b12c12a2638bd936255131c5ec8312a898e4f63189544c732316c2aa2638ed936055131cd6c5b02a898e6862d81544c71db20c0aa26396d8c6055131cd6c4302a898e6862181544c739b08c0aa2630fdd95415
  | 35 => 0x4c9510caf038264a8865599ca6454432aa8e6b22a21956472591510cab9b82c8a88655c1c16454432acce521aa2195657290d510cb9339486a8865c95ca4354432acce421aa2195657210d510cb8b39886a8865c99c84354432e4ae421aa21953674989510ca9aba4c4a88655c9c26254432ae2e1312a21955673909510caaab9c84a8865c510f3254432a6ce9192a219535748c9510cb933a464a8865c95d23254432e4c87192a219724438c9510cab338464a88651ddd93254432a6ee8992a219534744c9510cb8a21a64a88655cdc13254432ae0e0992a219667764c9510cab23b264a8865991d93254432e4ee8992a219724744c9510cba3b9a64a8865d1d0d3254432e4c86992a219724434c9510cba221a64a8865c110d3254432ec6e0992a219564704c9510cbb038264a8865581c13254432acce5b02a21956672981510ca9bba2c0a88654d1d16054432aa8e6b02a21956472581510ca9b3a0c0a88654d5d06054432ce2c0302a21947776544510ca3bb8ac9280651d1c564940328eaed288a01963664944500cb1ab24a2280651ddd95114032c6cc8a88a01963564544500ca3dbb2a0280658e5915014032a72e0324a7a0c5f7654c53d068f384a621e83c594e6110f41e2ca6b0887a0cb47158043d063db82c7296831e1c16394b418deeca90a5a0e695258052d063d384cb996831e5c265ccb418f6e0b2a65a0c787059532d0733292c21968399549610cb418dee4b1ca1a0c6c7258e50d070fb1886a86838b90f6254341c5887b12a1a0e2e7418950d0716ba0c4a86838b90c6254341c5886312a1a0c7b7654050d0734b12a0286831bdc96094e418d8e4b04a720c5f7654c5390726a9ac429c83c594e6190e41e2ca6b0c8720e1c6310d5290637bb2a4294839358d5214a41c5ac8a946520c7b70595329063c382ca9948387d92534ca41c5ec92926520e5653185329072aa98c29948399948614ca41ccaa430a6520e5a53181329072ca98c0994839a948604ca41cd2a43026520e1e6394f419070fb1886a84838718c43542418f6eca80a120c5f7654c53506a6392a629a83561c15314d418f6e0b10a6a0c78705885350637b92c029a831b1c96014d41e28a730c86a0f14535864350637bb2a429283531cd5214941ad0e0a90a4a0c7b7058c525063c382c6292838798c4314941c3ac829c64a0c7a70995325063cb84ca992831edc1650c9418f0e0b2864a0e5753584325072a29ac21928399d49610c941cc8a4b0864a0e1e6314e415070f31887a82838758c43d41418f6eca80a0a0d587354050506b4392a0282831bdc963141418d8e4b18a0a0d397010c505063db82c5298831e1c16294c418dee4b04a620c6c72582531062fbb2a629883479c25310c41e2ca73088620f165358443106b5386a5290831bdd952148418f4e132
  | 36 => 0xbb2a2282654edd15114132a70e8a88a09967265144504cb99aa0a228265cc1505114132e6486288a09973043144504cbb0b90a228265d8cc85114132ea464288a09955b73590504cab5b92c8282655cdc56414132ae0e2b20a09956972190504ca9d3a6c6282654e5d36314132ad4e5a18a09956972d0c504cab5b9286282655a1c94314132e34e6218a09971b6310c504caadb9a8428265561cd4214132e5487990a09972843cc8504cab4b8e64282654e9d23214132a72e9190a099718438c8504ca9dba264282654e1d13214132ae6e2990a099570714c8504cab4b94c2282654e9d06114132a72e8308a09955973184504cab4b90c2282659598d61d5032cccc4b0ea81947771582540ca3a38ac12a0650fdd95415032c72a8b00a81966662584540cb3930cc02a0659c5866015032c74c8b00a81966a62580540cb3930ac02a0659c5856015032cd0e4b00a81953671996430ca9ab8ccb218654e9c26590c32a72e132c861951e73196430ca9b38cca218654d5c66510c32a3ce6328861951d7598c430cb0eb2cc621865635ca6310c3287aed21ca41943d7610e520ca9cb80a9a10650f9d85450832a72e02a2841943f76550420ca2ebb4a7190651b5da538c832c3ecb21a641961f6510d320cb4a218c299065a610c604c832caee3b2a641965471d95320cb0fb2ec89906587d94644c832caecbb0a641965765185320cb4a320c29906596d97604c832cb6ca302641969864181320cb68308c09906599dc7654c832cc8e3b2a641962f65d91320cb17b28c899065639d3634c83295ced21a641962f6590d320cac739c86990652b9d8434c832c5eca21a641958e7610d320cb473b08699065a3d94434c832e1eca21a641966765d85320cbc221ec299065a310c614c832cceca30a64196a764185320cb52320c299065e110c614c832ccaea30a64196c653185320cb63a18c299065a990c614c832d488630a64196c443185320cb42218c2990659ad97604c832f1087b0264196e061d81320cb46218c0990659ad94604c832d56c830264196a864181320cbc4218c099065b8d84604c832dc0c230264196ca53181320cb65a18c099065aa90c604c832d508630264196c843181320cb44218c0990655c9c05494432ae2e02a4a219557754ca510ca723b2652886559dd53294432f0886994a2195e0704ca510cb8b39887288654d9d06294432a6ae8314a219536748ca510ca9aba465288651d1d93294432a6ee8994a219534744ca510cab9b8265288655c1c13294432acce5b04a21953674182510ca9aba0c1288659c5806094432acce3192a21970c434c9510cab238a64a88655a1c1325443287ce8302a21943d74181510ca3b3b6a8a88651d9d85454432ae4e02a2a21957170151510caabbaa64a8865391d93254432aceea992a21978443
  | 37 => 0xf9d260d453287ae9306a29957270953514cab8b84a9a8a655cdc154d4532ae0e0aa6a2995367590f514ca9b3a887a8a654d9d363d4532a6ae9b1ea29957270d8f514cab8b86c7a8a65c59cc43d4532a6ce9196a299535748cb514ca9b3a4c1a8a654d5d260d4532acee4b06a29963664d46514cb1ab26a328a658ed526094532c70a9304a29967351982514cb1daa2c128a658e1516094532ce6a2b04a29943e76d51514ca1f3b0a8a8a658ed536054532c70a9b02a29963b54181514cb1c2a0c0a8a651ddd95114532a6ee8a88a29953474544514cab9b82a228a655c1c15114532acae3990a29963665d50514ca3abb4a828a655c9c25414532ae2e12a0a29947776550514cab9b82a828a655c1c15414532c6cca2a0a2995367590c514ca9b3a88628a65c9d516214532e48a8b10a29972754cc8514cb922a66428a65c51523214532aaae7b20a29956572d90514cab2b90c828a654d9d36314532a6ae9b18a29956672d0c514cab2b968628a6559dc94314532ac8e4a18a2997167310c514caabb9a8428a65551cd4214532e4c87990a29972443cc8514ca9b3a46428a654d5d23214532e2887190a299537744c8514ca9a3a26428a65595cb6014532a6ce8300a29953574180514caaab98c028a65595c8601453287ce930ea09943d74987504cab938ca9a82655c5c654d4132ae6e2aa6a09957071553504ca9d3ac87a82654e9d443d4132e66a9a8ea09973054d47504cb9921ea3a8265cc10f51d4132a74e928ea09953974947504ca9dba2a3a82654e1d151d4132e66a828ea09973054147504cb99218a3a8265cc10c51d4132ec2e428ea09976332147504caacb9ec9a82655a5cb64d4132ae4e3b26a09957171d93504ca9d3a6c7a82654e5d363d4132ae4e3b1ea09957171d8f504cb8d39887a82654e9d232d4132a72e9196a09953a74987504ca9cba4c3a82655a5c861d4132c6ea930ca09963454986504cb1baa2c3282658d1516194132c6cc9a8ca09963564d46504cb1b320a3282658d5905194132c74c9a84a09963964d42504cb3930ea1282659c587509413287cedaa2a09943e76151504cb1baa6c2a82658d1536154132c6ea830aa09963454185504ca3b3b6a2a82658dd935154132c68c9a8aa09947676145504cb1bb20a2a82658d19051541328f6eca80a09953b74540504ca9c3a2a0282655cdc55014132ae0e2a80a09947771590504ca3a38ac8282658e99754141328f2ed2a0a09957271950504cab8b8ca8282651edd95414132ae6e2aa0a09957071550504cb1d328a8282654e9d64314132a74ea218a09972b54cc8504cb942a66428265c61523214132ce4cba88a09973354d44504cb982a6a228265cc90f5114132e6087a88a09976372d44504cbb1996a2282651e5da5114132a74e9288a09953974944504ca3d
  | 38 => 0x4287aed2a4842146d769524210a1f39ecaa10850f1da5350842c38c729a842157270d465110a3bbb2a2288855c9c75094042c3ec621aa02147b765405010b2731ac5aa6650fdd954153328eee2b00a9994747158054cca1f3b4a8a16650f5db5410b328eeeca88a39951c7359250ccb0fb9ac928665871cd6494332c5ee4b24a19962c7259250cca1ebb487286650f5d84394332c6c87b0aa19963443d8550ccb1b218c2a86658d10c61543328f6eca80a19964d6398b548ca3bb8ac12a4651d1c56095232a6ce3b1ca91953571d8e548ca9d386c72a4654e5c36395232a6ce2314a9195357118a548ca9d380c52a4654e5c06295232a5ce430ca91953a70186548ca9cb80c32a46547dcd6095232a58e4b04a91953771582548ca9a38ac12a4654b9c86095232a6ce2304a91953571182548cb1cb00c12a4654ddc56355232a68e2b1aa91953b7058d548ca9c382c6aa4654d9c66255232a6ae3312a91952e72985548ca8fb9ac2aa46547dcd6055232a58e4b02a91953771581548ca9a38ac0aa4658e580605523287eecaa0a91962e5458b438ca1f3b4a8a1c658b5536250e3287aedaa0871961d5498e428cb0f2a4c6214658759654cca32c3acaaa665194e771597328cab238acb994658b59654cca32c5acaaa6651963a54983518cb1caa4c1a8c658e95160d4632c72a8b06a31957270d46518cab2b8e6528c650f9d0605463287ae8302a31943d76950518ca1fbb2a828c651ddd95114632c6ca930ea11963554987508cb1b2a2c3a84658d55161d4232ae4e3a84a11943e74185508ca1eba0c2a84650f5da541423287eecaa0a11947b76540508ca8eb98c3aa2654b5c861d5132a3ae7b06a89952d72d83544ca9b38ec1aa2654d5c760d5132c6ea930ca89963754586544cb1daa4c12a2658ed516095132ccac530ca89966962982544cb3930cc12a2659c5866095132ce4c2b04a89967161582544cb1bb26c2aa2658dd906155132caec630aa89966762185544cb1db26c0aa2659cd876055132ce0c3b02a89963b64181544cb2db18c0aa2659ad886055132ce6c2302a89967061181544ca1fbb2a82a2654ddc55415132a68e2aa0a89953b70550544ca9c382a82a2654d9c66415132a6ae3320a89953a70990544ca9cb84c82a2651ddc560151328e8e2b00a89952d72184544ca8fb9ac02a2654bdc96015132a6ee2b00a89953471580544ca96b90c02a2658b15262d0d32a6ce32a4869953571952434ca9d384a921a654e5c25490d32a6ee2aa4869953471552434ca9db82a921a654e1c15490d3287cec2a2869962f54189434ca9b38ca821a654d5c65410d32a74e12a0869953970950434ca1fbb2a821a654ddc55410d32a68e2aa0869953b70550434ca9c382a821a658715263d0932c3ea831a849952e7590f324ca973a88799265
  | 39 => 0xa421e9a635805210f5930ac029087ac5856014843d30e6b00a421e9a535805210f1da92c029087aa9496014843c72a4b00a421ea9525805210e57b92c1a88872b1c960d4443d1cc7310a221e8e539885110f4731ac428887a394d6214443d4ac5288a221c3f765445110e5bbb2a228887a95895114443d34c7300a221eaa629805110f54b14c028887a61ce6014443d34a7300a221e9a635805110f55312c028887aa5896014443d30e6b00a221e9a535805110f1da8ac028887ac9456014443c72a2b00a221eb1515805110ecd384a7280872d9c6629404396ae3314a021cae729865010e56b94c3280874e9c25354043b34e129aa021e8c63d895010f1729ec4a8087a394f6254043d18c6312a021e2e531895010f47298c4a8087aa5c06254043c58c5a92a021d38705495010f4a31ec2a8087a9d8b6154043d48c5b0aa021e3653d855010f4b29ec2a8087a518c6154043d4ec430aa021ea4621855010f1b298c2a8087a594c6154043d62e030aa021e3461d455010e9c382a2a8087a398e6214043d1ca7310a021e8e635885010f4729ac428087a598e6114043d4cc5308a021ea5629845010f4b29cc228087a598d6114043d4cc4b08a021ea5625845010f4b29ac2280878b58b5014043c6ac3a80a021ea9629405010f58b0ca0280870fdd95014043c5ac4a80a021e35615405010e5dbb2a028087aa5895014043d62c2a80a021d3b765405010f1dbb2a028087c61cd5014043e34c6a80a021f2b725405010f94392a028087ca9895014043c72c4a80a021f29625405010f14b12a028087ccdc55014043e60e2a80a021f32615405010f1cb0aa028087cc5855014043c62c2a80a021d397019253d0a2fbb2a629e85479c25310f42e1ca731087a170e5358843d0a56392c021e851edc163947428f0e0b1ca3a14777654451d0b38a8ac028e851ddc563943428e8e2b1ca1a161f6310d50d0b1b21ec2a86858d10f6154342c6ce830aa1a16357418550d0b1b218c2a86858d10c61543428f6eca80a1a16716154050d0a3bb8ac129c851d1c56094e428beeca98a721655535845390b8729cc521c85c394d6290e42c3cc729e852161c6310d5190a3bbb2a228c859558d5114642c3ec621aa12161c6310d5090a3dbb2a02848517dd95314d42aa8e2a98a6a15587054c5350a3db82c229a851e1c16114d428eee2b00a6a1474715805350b8629cc521a85c314d6290d42c3cc629c84a1477765445150aaa39aa228a855c1c151145428f6e0b18a2a14787058c5150b0f3188628a858798c43d4142c3ac621ea0a147b765405050aac39aa0282855c1c550141428eee2b18a0a14747158c5050a9cb8086282851edc16194c428f0e0b0ca621477715825310a3a38ac12988517dd95314c42a3ce1298862170e539884310b8729ac4218858798e53d08
  | 40 => 0x10800c02e00b0000008000001001000000000700380040060030038000032038000001c00000000100580000030008018002004000000005e004004808400005c00a8000020028004800c0c4002001000c000000000002800000d00000080080000070008004003006804000401600200380060050040000006000000800401401300c00000a201e0018000002002007005404c036007000c000014003801c05200700180100380000008098002018004000c00600c00080080060220008004018000003004401a000000003000000700180f4014012000801008c00e00000140020010008008008013001804400200000156671d4a52d0eb5386a5296871d9c76054b438eae3b02a5a1c6f7654852d0eb3396a328e875c9c351947438dce5b02a3a1c6d72d8151d0e3bbb2a228e875a9cb5094343ae4e3a84a1a1c7b7654050d0e3b38ec0a94871d5c76054a438deeca90a521e65525845290e37396c0a8c871b5cb60546438eeeca88a321e65625445190e3b38cc5284871d5c662942438dce530ca121c6d729865090e3dbb2a0284872d9c76054a4396ae3b02a521c3f765485290e57bb2a429487a598e6114a43d2cc6b08a521ea6525845290f52a92c2294872b9cb605464395ae5b02a321e8e639885190f4731ac428c87a958a511464387eeca88a321cb7765445190f52b12a228c87a398e62d4243d1cc6b16a121d3a70d4b5090f17312a5a8487a598e61d4243d4cc530ea121ea5629875090f4b31ac3a8487a998961d4243d4ac4b0ea121d3a70d475090f1b30aa3a84872d9c6629424396ae3314a121cae729865090e56b94c3284874e5db5094243c72eda84a121f1a73d425090f95396a128487ca5cb5094243e64e3a84a121f3171d425090e1fbb2a0284872edd950142438eee2b06a4a1c74715835250e37bb2a429287591c55214943ad0e0a90a4a1c6f725835150e36392c1a8a871ddd95114543ac8e4a88a2a1d70705445150e3dbb2a0282875a1c95014143ae0e2a80a0a1c3d769524310e2ebb4a9218871bdd95214843ccaa4b08a421e69525805210e3bbb2a228887995895114443ce2a2b00a221c767198a5010e3ab8cc5280871b9ca61940438dae530ca021e2e741895010f16ba0c4a808799d8b6154043cc8c5b0aa021e67621855010f32310c2a80878d9d06154043c6ae830aa021c7b765405010f34b12a0280879c5855014043d1ac4314a621d967118a5310ecab88c529887639c86194c43b1ae430ca621e95611865310ec7396c129887635cb6094c43b2ce3b04a621d9571d825310e5bb8ac1a90872d1c560d484387eeca90a421caf765485210f4b31cc229087a594e6114843d2cc6b08a421e96535845210f53292c229087a95496114843d34c7300a421eb2619805210f58b0cc029087a61ce6014843d34a7300
  | 41 => 0xc00c00b000001402a0020018004000003000005400000d001001400000e001801000c00301500f403a00200b0040020004000002c000004006020401800200400a800000e0058034018000003002000e000003009002e00c003829400e00100000380480000048000000006000800000000f0028000032006006000801c001003000c07c0010178024000001002806c00000600c00040000010000000000000000800c01e00000100000d40000088008002001004818c03801000000140320000010000000000003801800200f0008000020072004800c0b2001004001801c01a000000400a01400000500000190030000008000001802000e002010800c000000005001c01800401b0000006002000800401800b005002c032001000000800401b0008004006015004000801000002e032c02e05b00a80880460090010000016000001000800400f01700a40080070008058000002008000403e003000000c008000007802801403600a001800c00a0070000000005000000000c001000800400c00000000100000020000000004004000802400e00000400000060100000050000000003002803c00800000000020010000034000000006800002203e003800009400b006005c01e000000000401c00a01280000000040020098006000002802800e00100580240300200008050004000028003800a000001000001600300a0070000002006800000602b000000401c000002800c01c02000080a8000004003002000600e0010070030009006002c044002002003001a00a0018004000000001800001e009002000c008009003003000800000b000800c01d000000000c003000001800e000000800c00001500002880280020000094008000013000400400200b8004004000001000005200b0310004000001014803000402a00200a003e0000130000026002000000c00000c000001001a04300180000000010000004040000008006401e0000048010016000003003000400000c000000800d000000002400f000000000202a026800800600000080a800200b0100068014003000003400401d000802c006009018800402000000080180040000190024008000004001c006002000000c00000600680000040280010008006024007800800e0260000008000000000002800000100680100100000008014002001014000801a0020008000000000002801000c006000800002201b006800400000000080c801600c00580c400e004002808801c000001816405200600b001c000001002807000000000280080340000040000002000009002c0000020070074014000000800004c03400080cc000012007801400600000100000000010000000016005003006c01a0010030070004000001002802a0110000018020001001003406c0010090014000008
  | 42 => 0x1000802400001400c8014004002005000000401f00380140020010078008000000000802400000e004001000401c005001c000000000000001e021000000c00c000002803c00c06900000440300020040018002002023005c074033009008802001f00d000802e0000008028010003000001006001a000800401e00800100080000510008004008001001800400c003002001800a0050210028022002000001801200100a800c0a401e006805002402d005000801a00c008805800a000002003800e003001000c030001000000c0120030000000042001004000004e015000005c006003000009400000200c000800a008001000001a00c0000000010022005800805000000000b400804000100d00080040130084000002000000c008004001000000000002580000440000038000004004005008400a004000801000a002002802c01a001003801c004000001001403e0050000034000000001803400a01d002007000000500000000560190030000004000000000400200300d8004046028004027c02a00000a00340080000058000058000000000c002009000008000200400000300120030058030000003000801403000200080000000030030194094006000002400c0110008018026017003000000a01c0000064026010005800002c0090030008002002001001000e016015000400200a005804400400d000801800002400680000260000010000002033004800000600d0008028000000002000004c009001000401600d0038008000001017800000200300e800000400500b004c02200101d800c01c009001000400003f004800406e02d0000038000003000801c00200d00000100000010028004000001008800000000e000008400600b00000040320020038058012004014002000000000a800410400f00f002802400700b0000000000000800000802b004002802a0060008000008011006003800e00000c002000400000a8000006003004805c00a0860060034002001001004800c0000048000004007000800803201b002003001a0020000098008000000000c0e4008008801000400400b800400401e001001800800800b000801001b00080380460040000000006016000803801c0040000000002000000005000a002001000c000002000800801c00a0000064012008009803c016000002812800000000a0020004009000000001c004005800003601b0090034018002005802001203c000800c0000010068184004000002801c0020000010004000000001000803a006007003800a0250040000008012000804400a037000800000200f0068000030006000001c00201b006000000800001200000000060068018000002000005406001200c800000c00a003000800400100080bc00000001b002018c000001801c02600000d003
  | 43 => 0x3000a0000000000006000001805400c00100d800801e000000802400800600580000240010000004000000004000400a00f009005000401600180080000640058000002003002804803a00f004806405a008002001401e00100580580000000040078000001007801400400f03a802c00e0060058030008004000800000a001002002401c01a00980000000060000020014005003000800801700000a402000c003000001c010002000801c00e005803000a000000803000c02c00000a8004016001001400600e000003c00800100500000000000020000010001002800400001500380080100030038000034042009806c006001000001c00e000005000c006000007801c000000000800000004700000000080010000028000011001800800e000001003001a0030058014008036013800800a00b0000024000013001800800401f00a000002e00f004801c01c004000006c00400f01600000000020018000000006000804c00c000001008800003000100180280040028030000015009808400e0180078020006015002000000e0020000008000004006002c030002009000400600a000000000600a00e803c000000001002800600300981580000000008050000005001000c00e037000000800000200f0020000022000000c01a007001803c02e0080010010074007000002400a0000028014020000000004c002002012801802000701680600040000038000000000001001400c000003000000a02700800080220010180000004004000003c026002001000000a00600580240100130000014008000001800000000400400a400001a00200b002a001011001400400a00180280220000008038004008000000401600100a805001a010000000400600000000780080000048008016004006800800600600080000000230010010010010004001400000700f800000e00a00000080bc0220068000018009002802800000700100000120010000008004007005800c0040000188000016067001800400200e0008014004071006003400e01a00180000080030090008018001027004c002001006800000e000004002000c000006004c05801b0010018018000013001400401100b80400260030090004002002001803c00200d001000400c002003000402003f003000403a0070008018000003001000400a001000802c042013001804400801100100080040090068030002001005009c004008000802c01800000a0044000000002000001602700f0010042014011001c000000006807400000300101000080030018060002027000001c012002000800001c01a000000008601a00100000b6005006004801201800a800c00000500100000160000068048000003002807c00c00500b00240040000060010004006002800002800d000000800808
  | 44 => 0x2d3ea7f00004db88b276180000000e960000a8c76080eaad91e106baa8864788ba4bd4b1382da000016205ac0002a9c000120c0000e6ca5822e666b96ca00028fccc99e9e000216801b225e00023289028f4e0000000c8a1f7a2b41294d39b0a4cf080008668420bc680009ca215a4989352213221a8a3a50c35f99ce71791bccd89accbb40e2a74d2bc85f41a4e3af341a7b6afecc2e231a78f21d26081e70bf10c1a00022cc0001210d242f08d2d16028e72c94b7d229851c0ea05a18e260d613a6c4db128c0c27ca45780320c3039e225a4160fe00e29e012e40f4a5c8c779cf285aa3247b591a68ba00b20002dd2000073000003747f4892e78b83c64ce84c00510000557952c000000039f14440000570a2d00fa7ba00000000e7ea4900000002fa80db8ad8bb9af1400017220002dc878006bea690000408874ea6817b0c9480008f100000000000000000087cad160f81882000095000018ea83924c6a858830765a3e28d1a9400000000000000000000007d3a77231408920000c280000842000278400033744c79c3c72e102eb6700006b89110000154e4972a904bf000035518c268d80006d7125ecdd8bb83e793fc0df8098b06a6965b48b7056a9ffa5efb35800028ecb9013e89d99c2281d0de23dc227035697b4b93a5e227731327a29e2872f0fe023d98bc2d492f4b970a4a125922258a981cc988bbc71b1cba881a9d6be432c60001f3684124cc63e8ec600024046a02cb49328c44cb43048879a58279aa452426b4a67bb0000000081465814a81d690ae77226fed26b4f000018aa2a9000069e1d94c8cb2640001edc57518280000c14aef914cbaeacdebee80007df87806c223ec2c130584bd87a200002e28d89e86c3a2476a421c469f932fa0002ab46fd800a000001803c00000a00000080040020000104018000004003c00600e00a0000000003003800805001100380680020020008020014006004800c01800902d800c000007000000000802e010803000600000000000080000070008000000000000001000d0000084008014000000c00c008008800400a002001803800800900000000160110018000000003005000000a0060018000002000007000400401b00080000020120018000052001002800800400100102580240270010008002005000000003e001000000c00a0010008000034001002800400c033025802c000000009000002c006000001c0400000090008006002006001c00a005005006800a00a000000c00c00c0018024068002006813c05000200c800c006007000800c01000a006003c002000002000c01201e0000004004028007000807a003000800000200500000a002200e0058014000019000005000a0090018000012000001000c02a000001801c0040030018000044065000001800400400480
  | 45 => 0x22f4b5600004ee321600015587f7000095b00000001432b70087815e96a45b607d0b4f1b30cf18866ca1800005200000002db6af68000956b4380000000000028e72628e01a882c2000000021b80001f3b3b8b58000072830185dd9790000116a37a9f880002e980412720096a8227d62be4916800036d2e081050aba9a6a556c45af5695d9b785ed9c0c894136c30a809433c0000d37a69e7748000a310d10640b0bab761c3892e059c00000008d6a4f6000297cbd9ada21a817d242ca5340001fb48d99d927b325c055d0000ae88c667db97ead3baa64aeb8a2c72b30f87c08076a041c4891e00000000d6e4730000c0433b2c970dfeb6e263c75c2c5484f8000ba8a226a0d04d8000329826227141be21dc31e2782233a65802080009f2024c21ca29058614d40f880005eeb170aa898ceb888f4a4d61738cff14ac4d126f034e201643e2f38b81094c1600000882174e67e20001009452cbf2f7457cabb63220904c8b28f8774292a8f9897eb2e8c3c7b8071e6b98dc27ec0b983f598683a01b26582845a817a5b451e80000a20dc429000001efac46a9225f4a5886f485d0cb6a6884861b0914e461816e3ff80007ce07381ed0c1c7950a5c38f9eb2a5ba0309cb82e44a380001068000242ad7a87b800060a8a7a6f006360000000398ab5a00014c448d0aaac640a96336a26a2c18000c1288da71e137629c2b7090e92ac1128b18422ab02ca289001161268268ab2800020f2b278000b8ea3de00012fe899b46e1f00c321f90b34d0fa3d24012d66ce88f46bed83ba95c12d876db30c5cb14f22122aaeb3e2a8c9351a9e00002ea0002bc670980002ba80003ef2a00000245600000000000822439a9f8b88206a9670b5423f31986c42c0e4c2156c812825c6472d2ea450f8a60514b41530a3a40b12d0c1100008be8000961914854d97ae9ac8d9a7cb066ccb0206e5d98450743a51482380b06fbafa40be1d1cabe0ddeb359b5675c83563ebac16b6d15f82608ec0cc4862692e9f9a2698d84b73a2ca2cd92162b005ba00029cc4468ed8c68addc00018e663e00007b5055e00017f25780b863772ac488100847e0820a92aafd6000067012a02608e00dda0001b380f700008bd80fc804026621a9fdebd200000000000aaf80000000000955000000000001bf8fc00003364a1f126e00003a696aa91a30996de00029ec0000072ba7a086000000052915ca2d300000000cfe000000000000000002738b64932e8ab97e80000e704a6a020d22028a6661cc200013800001d568b08ca256d00000eb1eb8964109c4ce2b429eeb00e3720bd073f2decb6f82e6000231400005fa1b2a0687578000077352026f8012aad80000000d1c1f28834d31943eb6300b40002c2200000008fbac04c5b867c171b114546967eae58edc000236403e1920000
  | 46 => 0x2c9800013f6cc60a860002d2a0fc0000d2880008241ab28f725ec936a292518942659a19780001bf2d2923160000390cc788c2c6b1db014e177833f29520000000ac4336c00002707a880002158af04048ee2adba30280d206c22a835a9a60cc030b18b81ce8e8acf694bc21719fe000169e54313ea00022683cb000000005d20000000ad280002568980ae5085009d8df8acb800082c82682e528780000000000000000000000001b4200000008981ec2c048e8864a22561e4874896795a20002b4c745a7989170c42b021124d4030ee5498208b848000b2a99ee4c02588aeb075e7f2044000018da658a162000306831786a400e98228de91be88503c0c23b1725ca0b76b2b35160838ecc1478eb6a9d91f63bfa648d262d1ea8632ac62580004062f1804313e445c8db846c16d012c05544b488527878bfab259a080ad9c58012068a60d24eccc50fc82f0215421d34d2c0aab2a68f257e43d00009b1a53e1832a0c0a897f00002e6e2e0023c505b18cc1515e2c131938ce580a226601cebc5a0fc0c01c240d894e8a270aa63340a9ec1018f21a3348a175abc240a9fe48a9800059000009b586d20002c828a7800000034e400000002f8249a9c6ae34bc0052202e0000bf926422322a8e9d08582000000000000000002ae8110849089902247e4800000000000001474000135e5ac0e1600000000000000778b1e65f734a8b0ba27600034da0002fac7d1b472ab30000000335c00000001fb8000676859e7070000b8c0000000281857982742e780000002a062891f04000192c000000054780004f39eb686a000000021e02390ff228993823ee800065b80004838000000352a1848700c538c6a74e0a6c94c850400024d80000f1c692b15600029ba000248c3b8000000034be5a589620bcb51e98e167a00033e200000006728d900000000000000063c0000000014a0000000842289073d205200034fe1bb000074791c0bac800091980000000ec26741852544800094e2710000023855e8000000000000027545a6878673e19d6265118a251a43ca908d8abee29021c2a6cc166af9423cb3d0ba009e67d498cc5bc0fb029e01ba6cb0000838800044db2380000000c2d34585cfa5be78f80e46ea09b8a6c9cfe00021da000000030780007b78000349804600009ba5b900000000b44590800092fa1c64ea1e36000004c000242e1af342440cb15ca26aa581c32a728cbacd4b07000090ca9a8855800011a0000bfca27e4b3203c8d2af868bfa80a61c2d46c852a1c9440ceca221180b6680001b9aab898e8000b430d3272d01da2228472677a854c7b000015a970297a13b03c61c8e7ce99f41800e1c0880000c4fad78c8489e09beac8685bacf6a28956442b00e01061e5e5df9ab09b012ce28d0fac3a9191675825cc1f70d247d7000
  | 47 => 0xa34178cd130cf21d88000b130aec42e009c6488cd62e383fa7f1b1c000009d85cc800036604840001b347bc1e920000a4c51ca1060000000b3d000000029b08e30000ac2ab4e000175c4550000338afcac139d8877502320000c34b9a833ab41037c00026fc2e818e039727680003428cce17e00000340652223a9c3ac3a0000fc2000196c0000070000083ac5d23ba0002c00a9ab53216a8732015b20000000ee000808e9f500000003230aa58eae000051a1c804c67da8000000270400000006323514312933eb4a327e8b000002e720be9b9ab5cb480ce8318ad38a45988e3cd124e0002bc4d1d282605300009f42f70849ae3c06d1dca0000448bf096c0d1d85200000000bb5280404012e89259c7e3910e2814f9f061ca1c74a3d8710a778a64c051a62b299a906ce822aad9ac642ec16bed1f0ff61459126d049580d280a0834bac507b1aed2600a41000007020001242749016053d11f80001ff28bb0da24630b3e87a0d4ecaf072e5550292b9eadbcbabaa5241e854a946a99c0660920941238620f9a7e66ea2a84598ea21db99085069926ba2af22045b4408908d7674ca42613685da5d11084000321c32580000a78000bde12d461706d614993d20000e2254f82c69c4ab525f78d0834580000000430b3b1404c1d99c2783333c1aa8c541d13142000294a10305c80000e84000105a39521a007fb0a06af0d062252ad460b8000a8210304c90ef4a499cccc18312cc42822c464000000011dcc9505f483198784b785cc00000006f730a8bd50000a951dae0000000a881314d41b3f0857010e3460bcacda2e1a19e0560000148e5db92b24bc01626c797184d8800000000000000eba9380afe357a2129e9b1b868c091085f000073e88ba0001b0e00032a20000000a02210000028bc195a8e4953135070aaf3060e1ff63940ae047e800000000000c6051c3e52626ceb8e106b6913c8a3295e37830c035717a05d633784c4080c000339eaffb3c0a8e14c276a1e4ca75000071b90c4525800033925d2cce8a8040e01223430862ce380cc47f852806daa7e14625a6cf7221e09588bc45fa70a3b42770a6fad306b5acb26e405a6b5f82ae8be276e67e80c04d0904c4a9106088c200891c8ef67771b4e042a1505f5088841c00d656c2ae4a300972d119bb80000cc664009748d100000001ed8a749326a32ad909a726008c38e460000000c419c9662c191047516609779f68b7925ca3baa4ead1e31409ed0ec8c808ac47a01c9c47b82482e6892a771023e51e01acb4ea46ab861d128838e0c9cfae5e9420b6a6a99b50296819a0af89eaaee2348c439c5a96d80b6bf1b05244a1ffcb37072ac9184dc0d816b27cf1252651a946cefadc426aa6862212d269768d885f60000909246ca2da7ee000338caf996da00026b40000c7600
  | 48 => 0x418b6442d0000000337e41c80000000f5038134ac08b9698ca4085a2fc1b4a5a30668800af063558f8641d9df6191012ab958bde86a8c8e8d71cc60f08000243000064c09220002d105f89b16c830c0c133b1f41fe210cbccb23ac6f017497e026400000002409fac7c820ee5bca806be4a5964b8b49653f12ae00000003db2644d0b26c23c21a68113081c00000004c0b00891800f049597121b5310819305720d400009632b886d600007b9963c2f501e86da0a769f489a4b1fafce3f10fe452a96829fd2b7431d053a8f025fc8890000351ad0aa85112a00006224c18000753000090e22b07b8b4c49201bc251731b26430f9297bb278653ae1495b99bea448ec416e1630d0700000cba8580002b760b2922c41b2918d40a0d63d10bbaccb00005b5961c550336010d18800000000000230063906fc0d294c0c37984e1b680c873530944b6b292a0e80001e230925a408c67c71774a6514b8cdc91d0c0f1f6c15faff80a0346ad0b84225e183a49ba9e52bf7b34a9d4aec846b1c0827c8096d0e9de600011d6ad500000c52ffa809350c8faaf8a9f800006941270067aeeab6a31ee3fea3ac5f6b3a0af289e2a67aa56b0f86c8486a74628600a0d4d8e6ebbe17360001980c5d812868594120000000c47aaee0000eda000272abe01f4800030a2249a9e4b909d9096c9bfcb9d07bc91b8f744e392a645e937a81394ec984a40c4e61d6ca0b93de43718a407082b065415da476aa0272f9a4c217846e12b9b8a0782dc604b05781cd94a04ed2f1c6311c169f12dd0adeb2f075201aa0d7a36aaf4817210595ee0e62bf603111a4480118844b0000ba920441e91a124eca4f00000cfa1342036000056cd3211ba1172af03e69f620002b7cc48ac58953837ad200b0caf00f9049f20d4bb30000b2e27eac3403ea0000abec8d83523ac071c7628000cf3005458b2474c2f01ea01b80000001aec4ae8fcc18ca0dc4aa8184b7e8af86230000194a2eab53328041b9c347158f7ea30800011991e425dabf2000329663781ccd3a16c43c80d8ecd40000059132870bb46052300d05a8a6f6be98000cb30000950a486689a29a7bd8a060fb000000013605342adc4eba80c0622aacb802d88918b2f83c69c921e2871aa56b134791277a0db27aab5bb30e0c8ae582840000b098c9203c87765bf9c42d2b9a1a00028724709bc628a301a47b083212e251800aa6b671732c883aa9aa533195493f81e451b8290c60016a6a81b6a24d8000be60000387a850000000c9bb0cca83081d6000000079b0e6a0002176114b07877ca4d000009de95221381969b8eb8b00002382bb2a5a8000586b29e000262436b22c61d4abee7028b2ac5997f409116bc34496145be2cc465f1e047e801587d6955c350a55219a93e6354243098620a662790a0002131828282d41ba80
  | 49 => 0xe566e487f277622809739be80d232aa3058c0a94a97644b181eea1b8000b1b805c3c1326ca888000329999a52280000000f2836a8000115800047c8000b3c15f696b800000032a40a18000950107e82108206789af4c2700000000dbe6ec188805395fa000052c88fab8a290951ccdc0000ae6904878226ca6078e764e40baec89ab00cabb3a80002ee800000005a120e8d17000000031e40aa06e400d08869760000c3d200400000007718a62194233032d12a0000000000014fe8260e4010da7b063d1e16a4d84e0a4d214e014875cba400000000000000093c000163866ca4b41ff000000026625412f3a93782b4a109d083ed80000000000000000079212ca37901c82d089d4018ab6c99f33e60002836cad8dd2c7a344e20909c255e1a924c2afa2a6180001c51394af60000000083c7ab832048c26e2af7800077fb09676f00008b7938a3891ab85d290d23e121228c79e9667600000001d44d24a76a48c92ea2042ac255405ea8a1921e1bcb380b028000199000054cb2080bf1c7c0a9b2da7d783761e82684ab2b17827d973ab0780000000000d38b3fe732881600002a0a2b80005a72064206012eb7f1aa4cac9e76851b240190a50a6182c8e24e29660b68bf40192dae375878420b1fa4166008ac2b042e360822895a2eec78e01e6a2c0424c6990eab2228eac95aab20e8a68a000105811ea5fed271d10abc8e5a3290000bd41aaa1b80d666611c442e11be055687d4ad0280297d864aaa2268e5c50000c6ba53ac810996000105e72a80008da0000c7180000000136512982490a2f6c8a12ca04a70b9084a8ade00026d8afd12664f42018062986412f00009c88d7841920ba27e34325e730be00000000000000000000000000000001a9800000001ee9fba5d023080000000baaaf5a16109420001eac00026506889322000067e18a8000000077011a80005bb0000000306e00020e60001062bb280004c39afacc6a3565d809689d6216018b953c7c0000000004ec279349e7b41baa10e800012d857c70a0000cd3a22aa54128a588340a0001284000302e6ee80000ee0000000000069b10f0b5a931600000001f12922263a7084260a463a6ae4a43eb2ec7faa6aca2022b4d1294887c4297651a8e94000089a53622d8c672e446010eac7d0116042eb46c3bb1068047b2d2539310063005405ecb1108ab0ee40441692b6b22783cf84be299994022b84ea2db17c2604b004cf12dd6a069c182b39d363929efa98a04700762cd23d90a4e00000005a51194974173c0d0b4ecbf992e0496b03a570205604c0b28cba1f30c38819c6b027fa7eca070254839610aa07c3ad239836826763139cde0af1628995b168000012642083b442a219e98c049800020fa24180001d31e023b9b40c2fb00f6cca240e00033d61b611a82b492288ec8a14a
  | 50 => 0xb26c2aa1b80000be8247094e8b124e64500000a61156000024ac00000002dd2e32bc832d46d78000000079e00006de3b48000566000a1a523723d58a9a2fe0978c27990a81004805092e6099b33f2806ab9c47220967f8a45414a8000a3c800002417c800000000000000000178ac8694f6000288e00015c40003528c3d8f1e000255c09400000000000000000000000006c499c68a2800000033048321a0e458a3523c59a2e00029d852780006de99660000000000111ea932d701ea12920000000b120000000247a8e39bb4a522dda2c7b27600029c200000003e395ce872000073b8000a6ba6900000916000321ec9b8c1021d8202d4b1dbe0c729ee4021400b332a4a5a3a5a874028203beab4405b2fe886431b6a139944cfaa89632a1f1422330f0000093e524177a82a000085116488b4067ab70923a72a0cb298d32e219722dc00034505aaa6d0a12218e0cf3340843839c27f93c651a170ac0e30024ed8f52a771cce95eb1ba540aa8a0eba468ac2029405a2c8400023e87cb9ebe08d2c30000000000009c416b8d6c33500141dc97fc5e5a9906f1282825ead406dfa1520f28b5cd490ff08119f9cb15a3b60bc2efc1780568891853429a02c8129078c916078200002e04ea99a60001c64a8b8186738186a24ca5206262b607fc2b06b1f1ea05488f3c6c016c213a02aabb5a6dccde8000d358df65d0a8da1741a2acef348e30890de22d8afc857907c0001196179b354a8cb14a94f282a7f401348fe800000001f666ab08c7ca28f49a50a209a8b3ac64d06cc40f00001b0000065a000090b335e88f000021f994a93580000a1038099d2e8e756964a000196a64f800056300000000cb0d351f228fe0cde2e8a9b603b26e4b6933fa5d5ac363502502ce42ec43f4044674f98d40000000b4d0000564a0d85f1b18462c81b86c897b85ae028c00019968f18d22333b05694bb2ba0f383080bd9bf886b119aa91a71c7e98fb83f60000c0887d809eb01e13782265d31e12b2f0c7ca99815c0ce22c82bdb00caf32aa82f921122d895e8d039ae45ad9d50401917420291c48e08c3041393a4d008aa855a950666380066a331947d821ca42214a20d3b3f86a693beace33ba49601089d7b4ea9719a044cb0bda500960623eac604e7a172420050c6c5105233a9fd40f632707732cfc156275a2f8af407b103d419b92029be2bd0c21211a0ef2fbe0a5ad5a98aa2b6a9f0000c722140aed2b3c403811acb09b620001b7442c0000b50a35ed4baad67601f0eacda6889c611b8481899021ea57800000006f30d0aae80fa405e03b27e506820002128aa68e90ba580005fe322e74a23b0000000000000007901bbc4f08000000099c5510000000278a79199a80002e1ebfba1165a9875693b8000000000023300002f104ccb92000073a00009b50
  | 51 => 0x1808000000031811eac589d62287094882680007668c20b04800048728927f98000bdd8a589af150e70fa244802ac766690f3a1e4241a0000000275ab4600018d201e869cc74a95c24b15f405d9c1a869b1d638b800042dab8c0000d48979800045625b80000140a1e87081040384548273c18b0b3ca3229708df2972000333482a80006b38120000180e9628000cc41d743719c2c000000046baee2a3785c4628033e168000080ea77409f0000b4da8aacb718c6cedae161e5afda65ea22ebaf2a622b32932003a7da0a088546eb8ef06f40e8200022f031201a6c93b4b6c9a351a42ab37c65c9028a39830a0001ea40002490000000053b93841a10068000335a0000fce8280b72ba4ae5029a9f8000023121ae345a00021202a82e5a6412f3458880001751d3a0000000000000050380008cd02ec6732078997118480a855a3ea018225f14b024d17d6aba8218af5849a77b94801c492f28b4800000029fe1e3ab5e0000000a8d0000000007807eb510b8a0000d473462b43b36612b19f0000044e2e480009d28e200001af606a0d3a5950000bb61b20505327268c80002f380000001d300002a044b0a060000040a386aef400004004919eb4817000045733eea370000000013e37cacb08452c40be124c4502af2c6900000c0c800043a2f8c96f292831f882e0002dde662a73200014f81851e501a60ab67af1cea9eb1a0a7d521d4b3e8b8a1f80b5e29d07cc43cad004a31b6c280194cc368f2e87e84c2ab611b21e690d88160e64000096eaf51b2ed07b392959288217a0166b5f276c00012be757017ad1c000080f808833100006e696ea0001d4e0000000c332ec60551fbe17906c60002aaa36920aec430000071830491912dc16f2c5a00009da00003c472227e600014400001a560002e6c00112080001ad06aa0a12978233e501af0c200a5c2788800000000261e72672822296c798199e7cfafd83d982c0b1ca20a78ea5a4000261cb608000aa4a862517a60e2d3b0b06f99f4a28e0b082b6ab3e8690000577806a1871f56a668d86a93a8123d6124000023b8c3f24c837500008dfa1be000000000020ac29c8000057b2822de184c0000bb62682522a182f4c315ae388b89894a1b342618600008aaa118612a5e440e8d1400000001d0800000000006e11d9c447303e7a99d7e657239abb788067ccab1e00020c0b2a28323a380008eab34202a8bbe02f122499480009d304d40c48000bc784fc34780206890b500960454510af3649aa41e000333e0001c4a14ca98a1d815e4c6211ce70185b6a840722abf00007fe00009969db2c890e8c31e84d29f01d680fb87b21048000b4901be5fe9bde1f180005b383fcc60896659329c481d963400008dc6960f0a4c6a78e71a000013280003e88000b268132d32814613e946c02a24085a81e78
  | 52 => 0x4195136444108d4a1a3164000000043b285aa9780003f896087850058a2ea3049b125dc0b580001a01672865032c42f9524cc000000002c0658d8d1a468a2209c7a3600470e7a145274e27c020057a9ec89141e5a9a980a669816c65a2888ecb622da84f16b43270e363c31c8cc0d85ca862846480480281fa1806445b14643500007ea000000011786cf8000bc2a14c0001ba4507825e83d000018828ce8861a3e2a113ba173a594393099a5c1a7947fbad529de34c03268f80128a08cb13a30ac48140c00000004910e4e154161089280008bb8c5c8fc1e428710ede0001d9eb9ca6be749a1d0708051069c89eed0d018c0001fd64f680007df08a42510000abe800030e8000521800000021980000abca1c183e0002c284eb1e5c3c8a3a4532800053c15a63741a0069e88b05040cb804f30d8cf2b07acbcb2882a504a0b628ea6a8a2d6c0de12faa03a47074b1c709100bdcc268b30379ab2658023d045a34362ce270c6a8a08a88d14649f6136672c22167228ce00000a1677a1024be22898776b24a57f8c80c8f08b4464af2e7e7ac106830b02ca99420a4132200f79336bc495ba56bb4423060000273a2b809ab2343f52a9e0000fee00006300001bb2c118000d43b1a84fb000000000001d509ac728800094b2b30403049c6990e6888e038a47a00000002e642502f4652da39ea6e1b5a8189fb8b24264603990e2090180a000091e0179c764e1b322bc400001510000000298000002b84921e56ce2934a90720b8a4280002f630b62b920feb932ce800000002591e98182053c000042c00015c6c2080de000239000034e06ae964e000315ad14b16a7451eca74114ce8f91be456e1d6e316922e83480000002d76b522e68c4080006f2800000000000000576302000049906a80001df0000000038e800000000003322022b8381bc701003ca892e947dc97ca1deade81989dba5679e7a7a3aeb81689746b2332586a2900a1d620d032f95d027d082ac83892813c21d6b2faf96ce70f4266e297e7ed9ebaa4f93f89d70d9606392a2d08176ac3a8fbe4d3a5244aa1770713a7163219652ac8aace24623406e331261232d64aec304260b2f024ae1f163dc8b200000d92b0e11c699e9f347ef28c62a632b403f93d60000000007000062410209d920a4bbf8000226260c13c99760001ad21ff9a5c2b0914a6469e628d51ee42a70eb88620000be68d3e92c2ce45b5207e46381706388f5422a0392000170e5bf13d811d1fc4118a96455c000051d97ceaf3a9fa4ac25507689454bff82469448000153a9ca0002528000000031600000002c6280ba1f06e1a09c4f2863a7c99772a7a231cb7caaa06448a8ac4c2ef634399e80002f6278690fe867090ecdbab68a73800000000005958000000000037625f07758cf8cc80000664979842399ec2ed
  | 53 => 0xd2d2cd0c00004f019ac272000039d0000743127200000000002ef00000000b78a6b0bc1244800027f60000000597a342a051ed21bc1d18650a5c4000204818f80005aa0000a1da1864af000087f19a063f15ac3db91d800021f6c551430ac517c084d989a4f1126c0688000000000055281b02f185b493d009a5e134d84cc166232f27a254598ac2d20000c7a983082d08285e006660001bf02979458c62941c569166644301d000004d600024dc59a800074291e65c923b4ca692eec5e8bf2d1f9b0aa69b34634020de2b5076c1c11f669bcab2c64c94607c6997e1f99d6435c18263cd83e844004ba00c259893e9c00485161273008b899b937e098ae6680799d409c91d28f30a54b36800085b03022a38eb23fe0196a5a31da5ea0d4c0001b440000000860000044c800053887aa511a2ba6f4962617b2c425d790cac2234943d6acc67a7278cc9d2c9cacca81637b1b8017e0ac600011704c113461ae80000ef85c00001d0200000000f586b2294a654536963ab22a4880000fec684255e000000000028440000000b3080002618c0477900000000c6cbdea3d6b5100005fb1c50516800010f97fe18788f00001b64000000000030fac3180009ce84f41f68a486e88d0475a95820002daa9238000aea8000ce08000bad000000d9286741a6a4b170000864800094995460001b482d8001878aa79e674820c0002a6e94716dc5c80b3a07e0690a5eafd41788cdc08710e4561295627308e848f0b58922b2ea0ba0e9800000009261680b32949254a1e9a6b2832a87f899ea07a1f812497a69f700000000d7cb1a2fea000000000016ac158b25e0b48c8a883316cae62f3c4780f8273d874a00000006608000000000000004f8532000088b249c80e0000271b0628caacc88a900000002326cf50404997800000000007aa9658a2820b631300007a40eaad4e8050b7c18bea4423be5121c7a781a5d45c792360000e528108f484fcacfe00420ca1ab8000455ac32a829eee5e9217a6921340ab017262cc9ac8adc8000032a856055a2d600000007342ce22fa80000000beeb0d1a1400021ba2ffa37000000002a481c4477800026c17aa000050292bacf2d4f000027f0000ba71dfabe71ea85bd2dca86f165c7e286c441aac78a229370917aa1e632b006519ac4ad4486ce912b19614186eeb44a85c3c5338817b9fa200008905358b0043ba9d04dcb47a60e9872a2980000001d4a0000e9200000000000000493351800000006f5023652500002eb08e29c926a039080000218846451920a8952182b601abe00008361eb122a8dd800011f800069d800000000005d68c720002240aa50a906560bd2c69261e5b816e67be31d41c618ee0dc163ebb0104241502cc381916e0b13186a902f8eb1c1ac4a3c294249510100000000816b206a072b480e3857
  | 54 => 0x1c21100008141c0200006409c08000bff0000000000062a1c7200012606590590cb2a8a40000000000119800034ccced29967ac1aae0000e000001e8c1f7800030b800000000006a18000961233c59b000000000001a68e86c39000000024a00000000c7f135c00000004e88b2ec308cd200000000000192000000000000000000000b46800054e88c4cfa29e0868b2c412d264c50b80007c307ea28f333605424fc12ab2bed42800000029f2a720000000234c9998f968522d540000d94405800067d884024e8cf4ce99aac12500001edab34ada8044bda2e786579ca40e83074cd111a072685dec240c681390c9803d08be49d9b4c00000009298e72cb38000bb68b1a0000000c6aac926f8ad4e3bf1d767e329924fd1752212a63e0e3217e60624228961d78a3f84e2bd603c8c7e22a27a0a9f01659b1cd2c99e4b78123e1222374459314cca8214a400039a3850a22b3a9b4055cab5605fad94162a412ba81bc8489a604cb927bca9eac2419d2f7c32b885880a1816bbb8330cc926ba0000000688145000023bc55227b889ba47ecb780000001daa6e5a2223602a86406a79a0952da0c7330208a20d620002b240f6aeb60c7800000018d018f05f2a1f800056f80009e8247c429a1842b880000001500b7b80001bd87162cb00004f20e3c14b94ae6c9207ad0f143c9abb19e69a8ab44509b026878de8bdba49e41d34fc655aa3ac941c1208e993c431a7e889d15b2a8f1b9c3ed33a41b408a62280112228910a47f06023580a44b52802284b0b2266daef270c03fe8cca0264d59db4c191deac328ce623a9f9019215b64a598462f090781ab166e5422eac7e5ae2a1ee2a50d2f1144d4e313a068317e08780008e1000042f000000b9392539895400024a2314ae020778a7e5d20f4c8709238230002c6618592c63aa849209bac7a200008051cb253e80006702484d01a8bea0f000072412d640d00000490000000000066300002010c701f0a8a820e15f06d823502a20508cfd09b2ac62c7aa9a1a8400025441be9cc870eb05e8f6a734668acae5b21ac69eb821066d000045f2f9eb61800054d329c3960696c4a9cd889b285e74bb1507508386898a620690a0da0650ebecac0000d0a867608c2134311adf632130d428c000035d2580a8a8000bca8000d3e00002830ac800003a89ff00009aaaa2c5c72a4464b80007d0950a939151422700604290a0e99931c2982064ea388b0a9b483f214003328409604a551884120991e0c587688af1a6e4f7315e373a622b732d5052f8e48a348d2a5b3098c55497bc4338206a9b186217f00005618740ac4b2fe00000007f02e5256a29b40000000b488000c77183299e21b0d33826c6dc1bf4bfd30d2d3e903ebd116ae411b02899a881256f1d46d061b9e0e218668202e627dc17304a780169aa008c1d
  | 55 => 0xe730e635a8db606c9f84a6631e267cabdc18d133467f13cc84411b48f097aca96ad683630d28b3821641070fde0d99a345260a366ca8b7a9ef89ae7b02790615a7508a71ba6b899836afa000000000004fe800083380000ec00ae0858d3cc1f00000000b16000345400000000000000000131c51f00000000e087d30b247779db8000291c8c89ce263d90666b0ad5c6b780003e99810792a006cbd8af23d824a487d236e4258864a2308d8c88a4949fb0fd29560fc610228ee6948080aa009c00002ba456681e2d17b41060030e02ff18922df9674c2b8000407230c00008e62a89e7ec1400000000b6e78b000000000000001858827b3f6508ab58000024a2ac9f865d41afc000000000013d400f9e66144877c323021233329c017c1b7c6c10ef854627447c90ff400005d80000e34d21a436737167c4f8135a21f112e35906721f587b07312e9a0001da6ce6251ed159678703a8307630f3068b2b50562a434ce191522f2224e8eb8cac9829da0be82bba303a36c1fe99c844c31f6a0e05c29eda8246151fccb58b4f6c4f24e2825058ec999a385911f7871021d844ea2d456208fe64ab4ba143826ed34225c103ac1884eaeceb0303643510fdc1a7b2480e0a7e222098e825b341414db530072ab1a7c78dc0770ab7859c159039e1f76b34259ab00ad06735b36a629a44c6d4957ec19aa2622b305aaa92d9e6911290787283e0da12c8010841e1c9049ea7d20b031918ba55896885212bf09112776a27b352c8faba6b65a2028ff03949f1b14496e83e455a2a3e013813a281322a50d09142e22d74c46240036b8dba2563348ab7ad5e61f2546680aaec3de8c3e80caa5c142848e027b482856222850a8b104a0af5c74aa3a806405465f9a0cc6a3b408cec034664dafae1de1792b9f807c252ae8845dac3c9ba16467f0987a4b1116c3e22c2a55f0dfccc18ffc5c120bc52ea13244d110294031f0b69a8749fca124258142c040960cbf814d27bc81146e52726d213504d05b19a5c034449ae311c7c21026b9f0c36ab827c20002e54563a84c5ba23ce622b05c72d88f8a4b187655ba8d4000073e0102b82000000043820e0c9e800067727a80002bf84d30ae81b882148fd2afe000178e8ce1a662420eee83d8000bf412b600000009759f983838326000032818910c8b198bf600023e000000007fb0000000298809e0000d489594739195a8a8061a00000007148000bcf80000000baa0000a7c37b8ae6bf708de85c133c3b51b8800016168ac8000c7f962400019e06ef986ccea83cc9f78000000060aab9954c5878adc64eb15263b04ee5d892e60001ae8000261aa14b34c191ab86627000000014deac587ec86d136a746a62e9f30594681ab0e234830666f003888c96fa6bc9138d231a3a000292eae3856e185a5060001664b8919525f12b
  | 56 => 0x55c6979e18b8d8c90bb90d02454029c0000d34000000092d87f48cd8f104e7031071800000000000000072c0000000725000077d00000001af0cf7b39a00027600000a825940000bef0e9c0000000000141800004fe000346859d80000001fceabd000000000000000b8c61799140001c3200021ce7839566b4caca46a728fa0000a3e635976867ab3ce41582b2d2c3244c6d00004c8000046da67e10f05563b299949301b1a736afc8000110ecf22092101b07e0000000000000006ba7886110f6200023204e300000003210327a7b2cc280007bd000098c80000000da8b9180000002a98820ae1c000144e42192c0b1a89ca0000e0a5c200000198d6816f800000026e05f30dca0001ce694399242ea08265c5a86a0000000ae7970c0418f005c6943a6c1a2104881bea8bf081abd7a592859a02ca100bcc515b4aaa9c256a1840ba6aa9a84a5759ad48cb149ab638ee8c7107f0a4e179407c1d400748b4a65d31d80001bceab227a498426f48e20b1405697a21399874bf309b400019c4b831576789086c000134802fa68c9b209e8400804accaa1c002e800000023f60001ae000000000002ba800005fe93c81387fa2cd8813264083c1a1c5e78f68721aebe6f6095ea43308aa609bfa89e9b989982f7e48609fa460a7d63df2e84c5802428f224a871306dc6ddadf8707b2d63de291e8de0e02b4623584be18d80bfaf6a502328e117b4dc9bb9bdaba0afd236c0fca0d7108c4c30e66a330118be0801a424adba913ac6c9d89dfc0c905307bf00242d1a1e496c08d04848f5e4dd00d20be93884a61538c6482d01a9898400000009a0b1bebaa23d8446257238e027e9cc0f5c02b08d699c2abc01d0000924817c7dd2974ab88e607a100002e0abfa000320aa358000b84000000031581d909d2444800000000000000000b202af6c320000000000008100000002ce666c2a126a5acc07211e94159b38468a2958b66007e7201d7c4a2065ebfd88ca000190ebd39044a3a00005319632c299d2002485863849b8228b86381f48000bd911f0bc904762d0201c2741d582bba9bc8470000963a3a2435b4c28a09ff4b28a5741e601c044f85b20ae90a2b7506b4565836ac6c200e11e01ecc1aaea683b1e72a868dbc320b0720cd0b1c21a326081ca9301818fe8aff33e4c4928b89e181f412988f48c18ef249fa5fa0000a1e3b5a1cca788548958875084c21e223b830e952a75676b05429cd92ec246a8006edb33049e0c061980726caa30866adb024815068e50d81d4b471b543c4a94c7898b663d023a097a925075984b293a0000c9f09bc1838f0eae404384df10c0c9aacb6433286488daf267c293325fd8f267f2afb00d1070e118172a8a58e309081b32a63a9aca718c00a9d0444c0b1cd22bd3332d198f0274f1e5892c8b969b69842a53952a9
  | 57 => 0x87ab1120f40fda40d8ab869c3026576000058b83f40bb81a43c191083e811069b39efec3f821ad4d263600001f27b3a178000148200022003678000000000000024c2c4131ca2c3b24c5cbb4041f89af832eb0f2000000003600000000000154a7f08e28c949d21988933b0ce0fd94b2c0000000508686afb119c5cd29000002fe200006b600012745772dfe47d2e7683e1b18646256677b00005fb80000002d5632a9aeeb1100000000000bb700e8bf0165a00031ce430919e0001df800021962df0a56a9e03e6c969c6617d9c821e50734a2ca6de63f9f2a6a216f6cbd06b00001b28527000050e15c825c00000002f2846a82f4a210df04ad105c354869290fab0c9dfa5a271a82ac62b93541df955699a02982d5896a300a066c7cabbc00021b2000000000000002f58cd8000171072980001691a742869de0310047c249042635e8000456986e3529e749d02c5e73c0cf673b00000000f7600009b60002c520002680a512706cc0aa300938c245db233ad499c9e000035403380003049bec26a179a5132536af826923ec9d22255800000015d200010948b900000b3a51600007a6754924a7f6b3946a528949c0234e00002d838c8afac261e30ac1159c7ea9a82887000050a0000ba19c10a19a53011b00005298000a48127a36c95c2c7830b2831132a4fc00000eab5080dcb3d8667000070529780002efa3eaab92bea82dc0c688707c6242a2ab8fea1590aca8b3a1ec89f33d25d50d9c75eb17cc4b8ece3a7988679f218c03096ba3e61cae4c49b72573332e414160ea799e642278ad6b79ac14c359e6e6ad181aa0b2e06207a9da29403b6ca12602c682418ab4ae3ebfc00000001b0c000331c16c18b48e5800007f000069680000001a468e493fea4ea64a1fd90406cda64e00023a6b82adb0aae8a327eb80007d4152e1810000000000034800004e816e2cd58cee0b7a4467c4b422ae11afe612272c61f80000a9070668600004340d58000093000017881ba0c6eace95fc766200c8c62d02ba33016386279660f225acb8109e95f306c7d10f2491099e64812ac61a224f80000f2a34d80007f804c8aa0b0801da829a0000000b7ab4f200000008fc886017700005df0000788000038b19904a00766a8db242000147e00013ee000211e53a80008e5048aadf90900290000b33b01c3cc9d8e637099216a1b66b6107c8a439b4661015a078d1378b452f72d2e2c2033080003979f64901b40070da606bac0d72c742310203afb28932be284b98a2ab41d848ff94e0877abeacae307024480000001ba07ffab80958185a7700524ca30f8c00000d40548f381eb9bd62d6b0ecbd090da69f0000aac2e2ecc5898a9ffb0dc9df0222036a29489480000000c381d18658369a5f234c08ec78cb2180002a0e2ac000000024bcc0299709e480000000
  | 58 => 0x213a1ae5f901800168000bd8000027b0000b0b058c0002c74412adb2bb08000b4215423da9dce007aceea9804282022b2028a8000782af4a96b034c2f98df4934a41440790fc3730000c5231fa00000000370dfa79a0336cfb00007550000cf8261654413bc7151368a7d8628472800057b1b3c00000004e5800000032e60000f9c10c800000000000000000000284600028d80001014968180c0000bb2000298c8b80fe600016ee89221b6cbb80008bc93e2a2b2b625370b1229b9906d122ada0000000614073c8afa0a20001da489cafb4c0d139a00023d498527ce9fe34f4d190000000311a00033086951eeabb8000000011140001bfe00000000001e4ea7a8000000112054c0ea80001fd800000002571ad85e090f68509b6e13100000000000b9c23ca6b700000318a6062d9f8e094a402000262c0000d2c2ab329413d80000000000000210a3281122b5c80002000000718b0c4bc38000000293c2200a02
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x6350030c90439c6628c030c88439ca618c030d10739454010320b12819d4430c320a31811516010e20a31811956010e20b0681d4c430ca20e075310d610ca208658718e5148620d057310e5148620e046310e5148620a15811506350220a31811956010d20a28855896010d20e08535896010d20a14835506154c20a0e83d956290c20c25655c46210c20c29655c06210c20a298510d6010820c0d651cd54cc820a1483550614c820b048154c430c820e065454d610c820a258590d610c820a258510d610c820e055310d610c820a0c83551620c420a478654f31c8420a298510d60c8420c887310d60c84208c8835c06448420d06545cc5148420d05545cc5148420c19651cd4010020c88735894010020a0c83551620c020c19651cd540c020b0985dc8430c020a89861c8430c020b09851c8430c020d09751c8430c020b81811c8430c020b098510c320c020e096510c320c020c61655c4320c020d80435c4320c020c0d7598c43c8020a258510d61c8020b098510c30c8020e804358430c8020c0d7518c4348020c88641cd4048020ca0641c54048020c197518c4348020d08739494010310b0a829d4430c310a29821516010e10a29821956010e10b0682d4c430c610e075310d620c6108658718e5248610d057310e5248610e046310e5248610a0d821506350210a29821956010d10a30855856010d10e10535856010d10a0c835506254c10a1683d956190c10c25655c86110c10c31655c06110c10c18741c16314810a1483551610c810a4583149610c810a318510d6010410c15651cd54cc410a0c83550624c410b048254c430c410e065454d620c410a258590d620c410a258510d620c410e055310d620c410c4573588520c410a478654f3288410a318510d6088410c907310d60884108d0835c06448410d06545cc5248410d05545cc5248410d06745cc5248410d05745cc5248410c44865cc5248410d07845cc5248410d04845cc5248410d40805cc5248410c457398c52484108658718c52484109258790c5248410d057390c52484109258710c5248410d057310c5248410e046310c5248410c19651cd4010010c90735854010010b418314921cc010a1483551610c010c19651cd540c010b1185dc4430c010a91861c4430c010b11851c4430c010d11751c4430c010b81821c4430c0109198710c520c010c197610c520c010d08439ca510c010b118510c310c010e116510c310c010c61655c8310c010d80435c8310c010d117510e210c010a6186149210c010d4073149210c010f0043149210c01081c835d95408010a45831952108010c157598c43c4010a258510d62c4010b118510c30c4010e804358830c4010c157518c4344010c90641cd4044010ca0641c94044010aa0845882044010ac0835882044010c197518c4344010
  | 1 => 0x1b088054c4348421d067454e3148421c50631c15348421a148654c4348421b108054c4348421d067454e3248421a84835906448421aa0805906448421c847418d5348421cc0631c15348421962809d95348421c2476dd15348421c24761d15348421b0684dcd5348421b0684d8d53484218668798d53484218668718d5348421c6076dc15348421c60761c15348421d23741c15348421d20741c15348421d43631c15348421c62631c15348421c60631c15348421d40631c15348421a448654f4348421c467654f4348421b408054f4348421a248654e4348421e046354e4348421b208054e4348421c457518c4348421a448654c4348421b408054c4348421b05859cc4348421a868398c4348421e058518c4348421e067518c4348421e057518c434842192587d4c4348421e0463d4c4348421a848694c4348421b058594c43484219278754c4348421a248654c4348421b208054c4348421a848654c4348421b808054c4348421b078754c4348421d078754c4348421e078654c4348421b068654c4348421b048654c4348421e048654c4348421a048654c4348421f038054c4348421b048054c4348421f008054c4348421b008054c4348421984835d06048421aa0845806048421ac0835806048421d047310d2194021a4583d952108740d08539c243d4940d08539c24314940a1a80dd853d0940c18531c161d0940e0853d486050940e08531486050940a1a80d9053cc940a1880590538c940d10539c243d4540d10531c142d4540d10539c24314540b228090c5214540d10531c14214540d20521c14214540a1a80dd853d0540c18531c162d0540e0853d486050540e08531486050540e1053d446050540e10531446050540e20521446050540a1a80d9053cc540a1880590538c540a18805905348540a18805905308540ca0721c56010c40944835d52108440a88825c06350040a90815c06350040ac08058d2108730c89725806010e30c91715806010e30d04439c75294a30e0443d496194a30d04435c6524ca30e0443948614ca30e0843948604ca30a6181948604ca30d04439cb5194630e044358b5194630d04435ca514c630e044318a514c630e1043944604c630a6182944604c630866879952108630d06541cd2108630d077510d2108630e066510d2108630c45735846114930c45735886214530c447558d2108530e045458d2108530990815c36210c30c19651c16210c30988825c36110c30c19651c16110c30992819ca6010c3098a829c66010c30d8072dc56010c30d83721c56010c30d80721c56010c30e04435496114830c90431c560d0830c90431c560cc830e0443549610c830e04435895114430c88431c960d0430c88431c960cc430e0443589510c430e056510d2108430a1a80d506350030a0d821506350030a158115
  | 2 => 0xc614c832e8043187604c832e0b6510c604c832e8043d84604c832e8043184604c832c847610d3294432d80431c13294432d08431c13254432c847610d3254432d80431c13254432b05829cc4354432d10431c13254432c2476dd13254432c24761d13254432b0684dcd32544329268790d32544329268710d3254432b068710d3254432d068710d3254432e077610d3254432d047610d3254432e047610d3254432c6076dc13254432f0043dc13254432d04431c13254432c63761c13254432c60761c13254432d23741c13254432d20741c13254432f00431c13254432d43431c13254432d22431c13254432d20431c13254432d40431c13254432d00431c13254432914835d06054432a30845806054432a50835806054432c1473dc56494331c29725806095231e0843148604c931d10431c53214131b05819cc435483190c835d06054831a28845806054831a48835806054831e0843548604c431e057510c624c431c847610e524c431c847610d524c431c2476d91524c431c2476191524c431b0684d8d524c431a268690d524c431a268610d524c431b068610d524c431e068610d524c431d067610d524c431d047610d524c431e047610d524c431e804318b604c431a608654b604c431f004354b604c431e0443548604c431e136510c604c431e8043d88604c431e8043188604c431a6286548604c431a6086548604c431e2364548604c431e2064548604c431f0043548604c431e8043948604c431e1043548604c431e8043548604c431e4343548604c431e2243548604c431e2043548604c431e4043548604c431e0043548604c431e045310c614cb21e085310c604cb21d80431c132cc721b1280d4c430c721a6280d4d620c721e075310d620c721c857610e320c721b0a80d4c430ca21a6280d4d610ca21e075310d610ca21e045310c624c621c867610f324c621e105310c604c621e8043cc8604c621d05725c45310d21a29801956210d21d04531c56210d21a31801956110d21d04531c96110d21e045310c614c921e085310c604c921ac1831c4604c921d067510e328c521e066510e328c521c62651c1328c521e045310c624c521d047510d324c521e046510d324c521d80431c1324c521e105310c604c521ac1831c8604c521a62858c8604c521e80434c8604c521c0c73dc96414121c0c731c96414121c1473dc56414121c14731c56414121c18731c16414121d04721c55310c21d08721c15310c21d10711c15310c21b088054c43cc821b088054c430c821a608054d610c821e055310d610c821b108054c43cc421d057510f32cc421e056510f32cc421b108054c430c421a608054d620c421e055310d620c421d057510c320c421e056510c320c421b088054c43c8421b108054c4388421c48631c15348421a0c8654c434842
  | 3 => 0xbc00128000000012e7080000200001c6aca9a1719e7a82639800000cc000cad3b1aa180274b4c650a400000b51320a896a621cca300d096c9014a3485a4a80000000000008d29c002660020463000190003f22200000bfa7c29b3c942d2c8800bf1e06d9c0baaae72a025f0000033014800af000238d63e35000020002c4002900024827b48842be21000c7800b82b0b6b6a5a9d67f1d4bb16eb03242a0c82b8b49535ec0b20598826723a2304abc25856a84990be7e17487930a2260a9a460c000d9a9eba2e43f8000000074172c9800ca800a88000036446000280121db14001e622a76d8a7a9a8726ea2a8f00089800451387c0000a00000180ad9a49f9cc938e89694013068cb93a6f0060f2c82b18e868604f8f488000000003d9826c0ce0020e000002c9ae5e1de7ca6e3031607000002b4268000d1f41aa4a01312b5ace00054930001206e48000090000031c112960880c6f97e8b28acd2700628c542dc288e4443568e046c38ded2842a900800000588000000095a8000000d1b3e0b212000002e000002e68317a1620a44800421e26d000d6164001986990a00000003388d80000000458000033acdb10078000000022274250ba2480081ab8000c20030a000001b13c618e22600090992578008a0ee6a800bb8dc5610eb89524da1894b188503665800000d45db326e03ab79847fa62d10003e95c7a368001900594cd72a01f8b6219ec36000001c8cb00e76134712441c0b05c282b0ac61f11e00000c1000bd0ea00168beb0cb29881e000002aaa49eeab22e1794e0b90c522243c87a3c0007db40240328f800028408599a7e800d4b08aa1ac00000000000000000126bc8000000000066492d89a2f8d6960000110100700c06024000042600c1007c030040501c050200d0280101c010480100800010040080001c00008070040000804010010000400401000050202f02000000060080101c00008100040e01805000000201b000010080001823008000181901c06030020000801001020000040004c050000a000000080000403000100200004c000240402c00014020000202405000020082605c0d03c0301000000020040f0280401800018010041904c0204c020040300800d0a739cb5094243d0a735cb5094243d12739c75094243d22729c75094243d12735c75094243c85625c46294c43c85725846194c43a88835c06254043a90835c06154043c1b761cd5014043d08731c95014043a2a875895014043a28875895014043e08735895014043e2162dc55014043d10731c55014043d20721c55014043e21621c55014043e21629855014043e22625855014043e21625855014043a32875855014043a30875855014043e10735855014043e23725855014043e20725855014043c0c73dc96494332c31715806095232e05751
  | 4 => 0xe014978c4b3354510ecbd8c6a50e0188d04723268a30069a050800001a80026c5504e4b0746c856402780003e0400000000408009c92200000822d02a8002025c000500018a00146791da7391ad83060010441800ae80055a8e7709c368
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0xa17a13e195a418107a61ac12851c6d6800600e00580148128004874044e9324000101065700009c5172c011aa445411e342cc002210801231030048600400e060221c735895014043a104bac438aa028087c0073588715405010f0210e39ac2a80a021e0821c725855014043e00398e4b0aa028087c007610f704c9510cb806ec218e0992a2197001d8431c13254432d0043086a96c098863a028610d52181310c74010c21aa43026218d80a435310d620c721b01486a621ac2194436009054c4358432086c0120a9886b106210d40a53631c15348421c213b100a9e8690843a00632015390d2108700b0e31ea621a4210c81a5a8654c43484219814850ca988690843a0086e015310d210874070c402a621a4210e802188054c4348421d0021b03290c099461a004360a51181318c280d2f32886908431850165c6310e5148620c04c28e621ac190841809865d47210c30083202eac08e42186010540654435c4320c020e00b2886b8864180416019510d610c32008280b2e3188729243086046147310d6088410c0243108b98a49082184086201731492104320108402e6292420850165c6310c5248410c02c38c6218a490821811865d47110c30043202eac10e22186008540654435c8310c010e00b2886b9062180213019810c52484300434030c218a490860085806544358830c4010
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
  | 5 => packedAt gbK5 (484480+((h/3785+packedAt gbK5 (431490+(h % 3785)*14) 14) % 13627)*15) 15
  | 4 => packedAt gbK4 (363458+((h/2271+packedAt gbK4 (333935+(h % 2271)*13) 13) % 8179)*14) 14
  | 3 => packedAt gbK3 (27740+((h/146+packedAt gbK3 (26280+(h % 146)*10) 10) % 578)*10) 10
  | 2 => packedAt gbK2 (3575+((h/16+packedAt gbK2 (3479+(h % 16)*6) 6) % 59)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfe03ffffffffffc0fc0fc0ffffffffc88ffff
  | 1 => 0xfffc07ff80ffffff000fff07ff83fff0f1e3f
  | 2 => 0xf000007ffff01fffffff00007fffc1fff01fc7
  | 3 => 0xffffff83ffffe03fffffffff81fffe03ffe3f8
  | 4 => 0xfffffffc0000003ffffffffffe000003fffc00
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0xa42a83058922449802d02d0c965c62c4886cdb
  | 1 => 0x4941952a90e4892cb02457542aaa356b0b162d
  | 2 => 0x6d152a332241d235557502484d3691b3b01b46
  | 3 => 0x81860c20448903866986986101c3182155a3b0
  | 4 => 0xe183043870e1c3b8e38e38e700421c2eedc00
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xfe80a880fe80a880fe80a880fe80a880fe80a880fe80a880fe80a880fe80a880fe80a880fe80a880fe80a880fe80a880fe80a880fe80a880fe80a880fe80a880, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_12833
namespace PEqualNP.Outside.L_meta_12833
open PEqualNP.Outside.L_meta_12833.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 9, 25)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 5 zero,inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero]
def fullWord : Sig := 0xfe80a88080808080fe80a88080808080fe80a88080808080fe80a88080808080fe80a88080808080fe80a88080808080fe80a88080808080fe80a88080808080
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 0 32) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,11,43)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,11,43)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (3936927744 * 2 ^ 32 + 3363880960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_12833.Model.Repr at out
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

def mono : List Gate := [⟨.and,[1,3]⟩,⟨.and,[2,6]⟩,⟨.or,[0,7]⟩,⟨.or,[1,5]⟩,⟨.and,[4,9]⟩,⟨.and,[1,5]⟩,⟨.or,[2,11]⟩,⟨.or,[3,12]⟩,⟨.or,[7,10]⟩,⟨.and,[13,14]⟩,⟨.and,[8,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3936927744 * 2 ^ 32 + 3363880960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3936927744 * 2 ^ 32 + 3363880960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_12833

open PEqualNP.Outside.L_meta_12833 in
theorem PEqualNP.Outside.L_meta_12833 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3936927744 * 2 ^ 32 + 3363880960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3936927744 * 2 ^ 32 + 3363880960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
