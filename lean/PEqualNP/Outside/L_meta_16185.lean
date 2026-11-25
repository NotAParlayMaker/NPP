import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_16185.Model
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


end PEqualNP.Outside.L_meta_16185.Model

namespace PEqualNP.Outside.L_meta_16185
open PEqualNP.Outside.L_meta_16185.Model
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

def mirrorSteps : List Move := [swapRows 50]

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

end PEqualNP.Outside.L_meta_16185

namespace PEqualNP.Outside.L_meta_16185
open PEqualNP.Outside.L_meta_16185.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x600039c29fb80000a9d02c89b0337a4a00404c2f08d4b2b750313e620b25483461a64c58800e080041040210223ff42fe42fd42fc42fe32fd32fc32ff41fe41fd41fc41ff21fe21fd21fc21ff40fe40fd40fc40ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x241fc42483fe64907f8c920fe99241fc32483fea2905fd4520ff28a41fd51483f8a2905f14520ffa0a41fe41483fa82907f10520ff98a41fe31483fa62907f0c520ff90a41ef21483fc42907f48520f690a41fc21483fe80907f90120fea0241fc40483fe60907f8c120fe98241ff20483f640907f88120f710241ff54082fea8107f95020bf2a041fd54082faa8107f15020be2a041ff53082fea6107f94c20bf29841fd53082faa6107f14c20be29841ff43083fc86107f50c20fe218417e52083fe84107f90820f721041fd42083da84107f10820ff99041fe32083dc64107f4c820f699041fc32083fea2107f94420bf28841fd51082faa2107f14420ffa0841fe41083fa82107f10420ff98841fe31083fa62107f0c420ff90841fe21083dc42107f48420fe10841ec21082fca0107fd0020ff20041fd40083f880107fcc020ff18041fd30083f860107fc8020f790041fe20083f440107f48020f690041f920083fea9885fd5310ff2a6217e54c43faa9885f55310fe2a6217c54c43fea5885fd4b10ff296217e52c43faa5885f54b10fe296217c52c43fe85887f90b10fea1621fc42c43fc65887f4cb10fe19621ff41c43fc83887f50710fe20e21ff21c43fc43887f48710fe10e21ff40c43fc81887f50310fe20621ff20c43fc41887f48310fe10621ff54842fea9087f95210bf2a421fd54842faa9087f15210be2a421ff52842fea5087f94a10bf29421fd52842faa5087f14a10be29421ff42843fc85087f50a10fe21421fe32843fa65087f0ca10bea8c21ff41843fc83087f50610fe20c21ff21843fc43087f48610fe10c217e50843fe81087f90210fd20421fd40843f281087f10210ff90421fe20843f441087f48210fc90421fc20843fe21087dc4210fd88421ff54442fea8886fd51109faa221fe54442fca8887f55110beaa221fc54442f8a8886f151109e2a221ff52442fea4887bd4910b7a9221fe52442fca4887f54910bea9221fc52442f8a4887b14910b629221ff42443fc84887f50910fe21221fe32443fa64887f0c910ffa0a21fe41443fa82887f10510ff90a21fe21443fa42887f08510ffa0221fe40443f480887f50110fca0221fc40443fe40887f88110fd10221fd20443f240887f08110ff88221fb10443fc20887d84110ffaa0217f54043fca8085f95010df2a0213e54043faa8085f55010deaa0213d54043f8a8085f15010ffa90217f52043fca4085f94810f7290216e52043faa4085f54810f6a90216d52043f8a4085f14810ffa1021fe42043fa84087f10810ff19021fd32043f864085f94410ffa0821fe41043fa82087f10410ff90821fe21043fa42087f08410bf28021ff40043fc80087f50010fe20021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0xf21087de4210ff88421fb10843fd21087da4210fd48421ffa8043fe50086fca010fe94021bd28043fd50086faa010fe54021bca8043fc50087fea5a07f94b40bf29681ee52d02dca5a07f54b40bea9681ed52d02daa5a07f14b40ffa1681fe42d03fa85a07f10b40ff19681fd32d03f865a07fd4740ff28e817e51d03faa3a05f54740fe28e81ff41d037e83a07f90740fea0e81bd41d03f883a07fc8740ff10e81fd21d03f843a05f55240ffa9481fe52902fca5207f54a40bea9481fc52903fe85206fd0a40ff21481fd429037a85207f10a40ff19481fd32903f865207fd4640ff28c817e51903faa3205f54640fe28c81ff41903fc83206f90640fea0c81fc419037883207fc8640ff10c81fd21903f843205f94240ffa0481bf40903f681207fd4940bfa9281fe52503faa4a07f14940be29281ff42503fc84a07f50940fe21281fe32503fa64a07f0c940ffa8a817f51503fca2a07f54540fe28a817c51503fe82a06fd0540ff20a81fd415037a82a07f10540ff90a81fe21503fa42a07f08540ffa0281fb40503fc80a06f90140bf2a081ff52103fca4205f94840fea90817d52103f8a4207fd0840dfa1081fe42103fa84206f50840fe21081fe32103fa64207f0c840ffa8881fe51102fca2207f54440bea8881fc51103fe82207f90440df20881fd41103f882206f10440ff90881fe21103fa42207f08440bf28081ff401037e80207f90040fd20081fd401037a80207e50040ffaa6417f54c83fca9905f95320df2a6413e54c83faa9905f55320deaa6413d54c83f8a9905f15320ffa9e41fe53c82fca7907794f20af29e41fd53c82faa7907754f20aea9e41fc53c82f8a7907fd0f20ff21e41fd43c83f887907fd0b20ff21641fd42c83f885907fccb20ff19641fd32c83f865907fd4720ff28e417e51c83faa3905f54720fe28e41ff41c83fc83907f50720fe20e41ff31c83fc63907f4c720fe18e41ff21c83de43907f88720fe90e41ed21c83f843907fd0320ff20641fd40c83f881907fcc320ffaa4417f54883fca9105f95220feaa4417d54883f8a9105f15220ffa9c417f53883fca7105f94e20fea9c417d53883f8a7107fd0e20ff21c41fd43883f887105f54a20ffa1441fe42883dc85107f50a20f6a1441fc42883fe65107f8ca20f719441fd32883da65107f0ca20ffa8c41fe51882fca3107f54620bea8c41fc51883fe83107f90620fea0c41fc41883fe63107f8c620fe98c41fc31883fe43107f88620f710c41fd21883f843107b08620bf28441ff40883fc81107f50220fe20441ff30883fc61107fc8220f790441fb20883fea8905fd5120ff2a2417e54483faa8905f55120fe2a2417c54483fea6905fd4d20ff29a417e53483faa6905f54d20fe29a417c53483fe86907f90d20fea1a41fc43483fe84907f90920fea1
  | 2 => 0xcbdc64197f4c832f699065cd320cbfea2197f94432bf28865fd510cafaa2197f14432ffa8065fe500cafca0197f54032bea8065fc500cbfea5a0ff94b41bf29683fd52d06faa5a0ff14b41ffa1683bf42d07fc85a0ff50b41dea1683fc42d07fc65a0ff4cb41fe19683ff50d07fca1a0df94341fea86837d50d07f8a1a0df55241ffa9483fe52906fca520ff54a41bea9483fc52907fe8520ff90a41fea1483fc42907fc6520ff4ca41fe194837e51907fe8320efd0641fba0c83ff50907fca120df94241fea84837d50907f8a120ffd4941bfa9283fe52507faa4a0ff14941be29283ff425077e84a0ff90941fea1283bd42507f884a0ff8c941fe99283fc32507fe82a0fdd0541ff20a83be41507fea0a0dfd4141ff28283fd50507f8a0a0df14141bf2a083ff52107fca420df94841f7290836e52107faa420df54841f6a90836d52107f8a420ffd0841ff21083fd42107f88420ff8c841fe99083fc32106fca220ffd0441dfa0883fe41107ec8220ff50441dea0883f541107fea020ff94041bf28083fa50106f4a020ff54041bea8083f950106f2a020ff14041ffaa6437f54c87fca990df95321feaa6437d54c87f8a990df15321ffa9e43fe53c86fca790ff54f21bea9e43fc53c86f8a790ffd0f21ff21e43fd43c87f88790ffd0b21ff21643ee42c87fa8590fb50b21fe21643ff32c87fc6590fb8cb21fe99643ed32c87f86590ffd0721ff20e43fd41c87f88390ffcc721ffa8643fe50c86fca190ff54321bea8643fc50c87fea910dfd5221ff2a4437e54887faa910df55221fe2a4437c54887fea710dfd4e21ff29c437e53887faa710df54e21fe29c43ff43887fc8710ff50e21fe21c437d52887fe8510ff90a21fea1443fc42887fe6510ff8ca21fe99443fc32886fca310ffd0621ff20c43fd41887f88310ffcc621ff18c43ff21887de4310fdc8621ffa8443fe50886fca110ff54221bea8443fc50887fea890dfd5121ff2a2437e54487faa890df55121fe2a2437c54487fea690dfd4d21ff29a437e53487faa690df54d21fe29a437c53487fe8690ff90d21fea1a43fc43487fe8490ff90921f721243fd42487da8490ff10921ff99243fe32487dc6490ff4c921f699243fc32487fe8290ff90521fea0a43fc41487fe6290ff8c521fe98a43ff21487ee4290ff88521f710a43ff50486fea090ff94121fea8243fc50486f8a090ffd5021bfaa043fe54086fca810ef950219f2a043fd54086faa810ef550219eaa043fc54086f8a810ffd4c21bfa9843fe53086fca610f794c21af29843fd53086faa610f754c21aea9843fc53086f8a610ffd0c21ff21843fd43087f88610df94821ffa1043fe42087fa8410ff10821ff99043fe32087fa6410ff0c821bf28843ff41087fc8210ff50421fe20843ff31087fc6210ff4c421fe18843f
  | 3 => 0x800400000c00c01c00800000c00000403001400400400401800400001400400002400802400c00400800800c03400000000000800000800400000001000c00400800800000000000400000c00802400c00400800000400000c00400801c00800000000000000000000000000000800c00800400000402801c00000800c00000000000800800003000002800000000400000400001800400400800000000000400000800000000000400001400800800400000000800000400000800000800c00000000800c00000000400400800400000000800000000800800000400001000400000000000000000400000000c00400400400000000001c00001004400000000001c00401000000000401000c00000401400800000000000400c00401000000001c00800801c01800000001c00400000000000400c00801400000000c01002000000000c01400001400000000000400001c00002800000400000000000401400000401000c00001c00000400404802400000401c01001400400000c00000402000000400000bfea7a17f94f42bf29e85fd53d0afaa7a17f14f42ffa1e85bf43d0bfea3a17f94742bf28e85fd51d0afaa3a17f14742ffa8685fe50d0afca1a17f54342bea8685fc50d0afaa9217fd4e42ff29c857e5390bfaa7215f54e42fe29c85ff4390bfc87215f94a42ffa1485bf4290bde85217fd4642ff28c857e5190bfaa3215f54642fe28c85ff5090bfca1215f94242fea84857d5090bf8a1217fd4d42bfa9a85fe5350bfaa6a17f14d42be29a85ff4350b7e86a17f90d42fea1a85bd4350bfe84a17bd0942ff21285be4250bfea2a15fd4542ff28a85fd5150bf8a2a15f14542ffa82857f5050bfca0a17f54142fe282857c5050afca8217fd4c42ff298857e5310bbca6215794c42fea98857d5310bbaa6215754c42fe29885ff4310bfc86217f50c42fe218857e5210bfe84216fd0842ff21085ee4210bfa84216f50842f6a1085ad4210bfea2217f94442bf28885fd5110afaa2217f14442ffa8085fe5010afca0217f54042bea8085fc5010bfea9195fd5232ff2a4657e548cbfaa9195f55232fe2a4657c548cafaa7197fd0e32ff21c65fd438cbf887195f94a32ffa1465fe428cbdc85197f50a32f6a1465fc428cbfe65197bcca32ffa8c65fe518cafca3197f54632bea8c65fc518cbfea1197f94232bf28465fd508cafaa1197f14232ffaa2657f544cbfca8995f95132feaa2657d544cbf8a8995f15132ffa1265fe424cbdc84997f50932f6a1265fc424cbfc6499778c932ffa8a657f514cbfca2997f54532fe28a657c514cbfea0995fd4132ff28265fd504cbf8a0995f14132ffaa0657f540cbfca8195f95032df2a0653e540cbfaa8195f55032deaa0653d540cbf8a8195f15032bf29065ff420cbfc84197f50832fe21065fe320
  | 4 => 0xeec00040df200000000016610d93080002f1fb8000000000000000001079690000001b78001f00000edc000001a857a51340005e9cb80000000010e9a543e90849a5c7839525580d168e800000006e52240007680000000018593d01f0000000000000000000000000000001528000000000be8a38000000000000000001848000001d01a602a44f00000002d40020f21583a46c08e41ece58000000d3c00000000000000000000000000000000000029e078000001488000000000000000000eb0368000000001f300000015d4000000271864001d08000170000001378470001f503280000000000000003bd3f8c7c9e0000001568b28000179879895a404615a0001368000f1dc28000000000001e9c00072951c0006400000000003a8000a980000000002580000003c800000000000000000037800000000000205800000000102c0007c20adaa80005bc421a01459320001bb40014ec001034bc80004547b9358a62090361124838720e69595a5c9a8508000000001e69074c285200020315540000000003200020d0000000710000000b4c000000000000000305c30000000000001888000000000001db0000001541a350614186117e1150000000000000000000000000ab0000000000000000000000000058000f6400000000053c6d8498aec000000000fc1f70000000000001b0c0000008b9b499f1db8000a6cb8c400261e08ec80002080012d00000000000018700012600000000000001a00000000000000000000013d80000015b8e50000000000000000000000438981f400001a8000001820ec1f08000001fc0000e5c000000000001eb19b0000011c500000000000000000000000020a4741cd00000000000000000000000000000021b00000000000017100000002880003a0ac08b1fac00000001800800000000401000000401800800c00400000001000802400800400002000c00000400801800000802c00000800001c00403000800400400000000003000c00400400000000000800c00400000800c00c00800000401000000000001400c00000801000001400801004000000000000401800c00000000001400000000401000000800000400000c00000400c00400400801000401c00400000400400001c00000000000000000001400801001001801400400800000000800401000000400000800c00400000000001c00400800400000000000400c01000000000c00000801400c00403000401404c00c00001000c00000400000800400400001400801005000400000001c00801801c01400000000400401400400c02401001001000000800000800000800400000000400800400000002c00001400000000000800000400c01400001000000c03400000800000800001c00c00c00000400400000000000401800000
  | 5 => 0x454e419137010dbb8000cb58d933a201129ef88081552b9479cf884df88a59a21be4308c3dba1e80090000000d2ce11e4800000051815d110198000000619f6800000000000000000000009c0000c80000000003f94cc000000000000f096789b0000000000000000000000000000000000000658001a08000000301c61099b717bdb8cae5b15700e44001ec8001a2a1b8001ca80010fc000001c38000931e8c000000001641670200000000000000001f29560000000000221df0acd7f01d80001300016e00017ac0000000000000000014701219889c9511d480000000001381240000000000000000000020600000000000014a800000000012800000075885000170849000012d9800000000012e80000000002440000018f00000000000000003400002b80006c8000001c4081d4e92880014d4000000c80b580000009a10700016e80000010395212a0000000000960000e5400000000080e1a07d86500000000000005d0f100000000000000000006900000000004f80000000000002e400000000000008d018000000001e90e30000ea068c0000000000000000011480008200000000000000015f8000001e88a54be4919b04000ad4001504001048bb0de9b360d8ba08a2101ae9ab09706e05ada760b88950147f8f88748254001ba44c89294c4001bf00000000000000010b813545c000001fa1115c08de04b80000014f4000001819b9400000000004c13c0020380000002391041e5f997c9ac8001d880020e9601f38f000018d0000000000000000000d98c2daf0000b350a85c00020c8000000000000ee800000000123c00103d491a640000000000000000018c81f4000000000ac49d4f2c000000000000000001bf8e004ac5cd7a02d8000000b25c10000000b70000000c15771be90810c10097d8e706f000101d5a9d205a05e5239bc0608000ed40000000002b00005b89c0000000001e20db800020d98c0000000000002a0859441f48000c019080006a13f06683b0000a88001158001d2995cd39f18db03d02ec1f8f60538389984bd800000139c0001c0cc80022382180021e0001d101d1940000cf9c00000000000000b000000000000009e8670000268000000000000000000000350cc1e28295b2d21c6200014680000f5191c992fa0800000003fc000000000480000e48000000000000000000001921df80000000d8cb00019a80000000007a9850001d95d31090c38681948d09278000000000000000000001d680000000007900019b80000021f8b096c80019a0000000001cb0000648e3800000176a16143000000000000000030c0b9c8d6800000016cc001de0000920001d38068d700000e02484e2219621c70890709a497d61d0000000000779b80000001211b1000124a0b0000d690f0000000001a30000001d707cc
  | 6 => 0x95e0091e95c4001184754000a30001ce80000020f83acbb94b1ac2249bdc1161a8ef86889915995d80f89d8b695f10a08f400125c0556080019e1481c49900954ee0ca011c9100e8f24000001944001228d01778a48001d98000001ee8000000000a64000cf400000000050c0000015c9c19a89b41afdd81b580016a8000000000348001c9cf06010000000a80c8c0000000000000000a8001af4001c908d98256980000dc000cec0000001e0000000001610a20000000000001c805c8000001815a180000000000018110454012d99c0000001d6c000000001ec0000000000000000001b261180000000000016518080000000014fe1e80014d0000c59688000000001a121c00000000002b4000001795de9798001998000000001025c740000002d05ec0000000000000016b0000000000000ce0000c09460000000000000789174000000000000ef00019900000889f80000000019180000011440000000000000000000010880002e80000000000000000013fd500000000b2c000900000870002068000b98001c6922c000000001b3d00c0009480003c1868000e405a4000000b414219554a0000fc9130d30628000000b80000ff00000005880000000000000007d0a754f22104a14c800194c2a83d8000d280419ac0000001b0a1156c0000020a80002cc0000ece916d80018980001b9910ca8ae800155d97cee4b100009580000001000009d0000fa8b50a685713e135c0019a447c5282400001c8f49b315700e4ff92441099285908c9974001d85eb4000001a4dfd8000e780000009500021488f94dd788000c700b1b1c001d740011c1ef16c0df8ba60e00018e80000000000000020c1334000001b20002199381a99c84fb1ae1242128b9506c9b96b938c000000002150df00007a15d00015905f0000000000000000099659c7cea84a8000000000daa071d8c000000001860000000001ad8000000359dd0000000000add79d7b9b68c11d6063800000000213968c0000015c0da03900000003186b8000000f1449c000000000001ff82fe171214000cd9630000000000000d600012b18914b9744000738000001e180280017a8000a151f9dd978077c000000000cd0000495da0000c980000000009f1664f28000f30474d580000000000013a80013a107c0000000016bc000000000000000000000000000000000001ad096c7b07f00000000000011b071c0015380a0002240e60000000000940051da9058000001b2920069c5d4abc7bc8e8001cf21740000000000000000013c0000000000000000000cf1dc0001938000000d05e7a0a02c43f000091c0008300010e12c80021880000019680008a4868000995251e60000c61649a90000105c20001b18000001ea98e000144800178c001930000000880c91dc9ca0ce94090d04680d1a
  | 7 => 0xfa13047c4000440000000414001341655264000001310488f400008600000009ac000000001e388982e1748f51230000000500000000000000001588001a80000799198ef400099c000b908000016f000070c8280006791e1c6d0057611fc00000059c000000ed0001298000000000b88000000000002021b50000000000ffc0017b0000ae0594d448e00000019d80000006b000000000090e0880000002f4000000f98568d34000000001629cc0000000000000000000000e880005e00000016f8000000000000000ed80014c1ee0e202ac000000000000000000000000000000000000aa9a50000001a6c000000290000000ca4f78551ea556400000000132d290001030fb9a391706edeb8000b18f20be05f8001e9400201800000199d9e80002bc0000000000000000000000000015e0c199b561800000000113c000001300000278001cc80008ed2598c04040008f00013157519942982300021080011a8001235a24000314001715d7df100000021f1759050001fc8002000000b9c0000018b9e580000000007c88aa228000000674000000000000848000000000000000001548c840000000000007719c8000000000000001269be02f920c000000001530000ad04d165c000a403b4000018000000ab4a04f80c308785580005b52045104c1e401801fd438000df40000012c1f58000bc00013e80000006a9bb0a091a07185dc0007151601894d8000699ea00c1120781f80001518049644001fd1b98988000001c58e08000000061f61109fe888931c0311c8c78000000818000978008000000000000000000b300000009140021da0b5180fe80004b46fc000000580000000001bbc0000011b8000000000478aa037112e099fb4338000001fb0000548001580084f71978111508001830000b21840908ac8331fa5b080008fc00216a220fe0000968f7ccac57800011855522000000000134c000001971af8000000001a3dd50000001429e70001b600000002dca28000000000000000000001ff0001a2d30c00000000000126c000001801d400000020404d8c9564e208000c8934446d3980000000017319f80000017e8001ed8000e18001d58000001aec000450000001350001ba9140000000000000000000001189118c40704d91f78684000001154000bf00000000000000000008c009400000000000196d281791a7a028000000002050f38210d897d1e45330000fd000173803c430e993c9ce155967c905360e2873088d0683e0000000070459bd400140d8b0000000000000000000001550228d504e98398280016380000000001511f0001a697b5c5c0015780014e0764dd9040ba91d0001674c9c0018a9960000158ab8d200457c0d48841b9cf6c5d8c21bd1179a705446f400110ca01950dd0d10000000000000998000000a1902
  | 8 => 0xf7515c1e854cbf90c8001bd8251b00145aa0000000001880000000000000464001390700000661e98000a7031000000067c25c69428014e190f5839cfd9e3053045d3892700021204fc000000000000000000000000a79ab8000000001cd842a231e004853297f80000001412a9719fe0000af0000884038002110000001badd7889c001965720000d400005058f814800111dfa9b8800116c00048e130001b380000000008d00007610f8001a7c000f0c000000411e510280012f0630000000000b780000000021c8000000000d810102c86d0a50efc8100000005a80000fdd644b0c34b60000000514e4c6f8750f1a140001000000000000001728598000d78000c51a580010b0001b91d9c0000013b80000000000000000000000000011000000004a55e80003800000002c0000000000ad93a49396d0000f34000f90000000000000d18b48001959394560000000ff45c5c9475c00058c000000000cb917c000000000000000000000a5c00113800000000024d3b0000002178001f90600eb800000000114c0014f80021805b0000000418000000c493180003b86a40000f1324000000000000000000000b380014999d0000000000000000000001ed000000000000000000000124dd90079668000000000000000da40000000000000000000020488acbd1bcca900015b18a00200800000002051d9e116a16d4000000f68000000540000af9740000000000000000001c8800000181c0016c4448dc80007e1348160000000000001bed2194506e9bc9bc4399410c45d180007d40000000000001680004092080012e0000000000dc00007e8c69ee4
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xb410436d52d04109fd96410427d6590410cf952410433d5490410db94a410436d5290410be98241042f960904109fd95410433e5450410cf551410436e5250410db549410427f65104109f594410433e5410410cf55041042ee6210410bb588410436e5210410db54841042fa6010410be580410427d65c8410cf953210433d54c8410d794f210435d53c8410db94b210436d52c84109fd96210427d6588410cf952210433d5488410d794e210435d5388410db94a210436d5288410be98221042f960884109fd95210433e5448410cf551210435e5348410d754d210436e5248410db549210427f65084109f59421042be6408410af590210433e5408410cf55021042de6308410b758c210435e5308410d754c210436e5208410db54821042fa6008410be580210427e64940109f592500427e62940109f58a500427d61940109f597400433e54d0010cf55340042ee62d0010bb58b400436e52d0010db54b400427f65900109f596400433e5490010cf552400436e5290010db54a40042f66190010bd586400437a50900109fd95400433e5450010cf551400436e5250010db549400437a50500109fd94400427e65100109f594400427c6510010cf950400433d5410010db948400436d5210010bd98440042f561100109f59720042be64c8010af593200433e54c8010cf55320042de63c8010b758f200435e53c8010d754f200436e52c8010db54b200427f65880109f596200433e5488010cf552200435e5388010d754e200436e5288010db54a20042f66188010bd586200437a50880109fd95200433e5448010cf551200435e5348010d754d200436e5248010db549200437a50480109fd94200427e65080109f594200427c6508010cf950200433d5408010d794c200435d5308010db948200436d5208010bd98420042f56108010cf953100433d54c4010db94b100436d52c4010dd59710043b654c4010ed55310043e652c4010f954b100433e5484010cf552100436e5284010db54a10042f56184010dd94610042f96584010de59610042796584010ded5210043ba5484010de55210043b95484010ce552100437b5284010fa94a10043795284010fa54a10043695284010be586100437a5184010fc946100427f6544010afd9110042bc6444010cf951100433d5444010bbd8910042ec6244010db949100436d5244010bdd95100437765440109dd9510043b76444010ed19110043b65444010ed55110043e76244010f918910043e65244010f954910042f76044010dd94110042fb6544010ded95100427b6544010eed9110043b86444010ded5110043ba5444010de55110043b95444010ce55110043eb6244010fa189100437b5244010fa94910043795244010fa54910043695244010bed8510043f36144010de94510043f25144010
  | 1 => 0x426d62150109f984540437661150109f980540437a60150109e98054042be64d4810af593520433e54d4810cf55352042de63d4810b758f520427e64d4810cf993520423e64d48109f593520433d64d48108f593520427e63d4810d798f520425e63d48109f58f520435d63d48109758f520427e61d4810dd987520427e60d4810de983520427d6594810cf952520433d5494810dbd4a520427e64948109f592520427e63948109f58e520426d6594810dbd52520436e5494810eb952520432e5494810db55252043ad5494810cb552520436c5494810dbd4e520436e5394810f394e520434e5394810dbd92520436e6494810db592520436c6494810dbd8e520436e6394810db58e520436c6394810db986520436c6194810db982520436c6094810cf951520433d5454810d794d520427f64548109f191520427f63548109f18d520436f62548109fd85520427d61548109fd81520427d6054810dbd95520436f5454810db95152043ae5454810cb951520436d5454810eb551520432d5454810db151520436f5354810db94d52043ce5354810d394d520436d5354810f354d520434d5354810dbd91520436e6454810db591520436c6454810dbd8d520436e6354810db58d520436c6354810db985520436c6154810db981520436c6054810db04152042be6414810af590520433e5414810cf55052042de6314810b758c520435e5314810d754c52042ee6214810db548520427e6414810cf990520423e64148109f590520433d64148108f590520427e6314810d798c520425e63148109f58c520435d63148109758c520427e6214810db988520426e62148109f984520437661148109f980520437a60148109e980520427f65d08109f997420427d65d08109f197420433e54d0810cf553420435e53d0810d754f420436e52d0810db54b420427f65908109f996420427d65908109f196420433e5490810cf552420435e5390810d754e420436e5290810db54a420427f65508109f995420427d65508109f195420433e5450810cf551420435e5350810d754d420436e5250810db54942042fb6050810be181420427f65108109f994420427d65108109f194420433e5410810cf55042042de6310810b758c420435e5310810d754c420436e5210810db54842043ad42108109fd96320427e658c8109f596320427c658c810cf952320433d548c810d794e320435d538c810db94a320436d528c8109fd95320427e654c8109f595320427c654c810cf951320433d544c810db949320436d524c810bed8132042f8604c8109fd94320427e650c8109f594320427c650c810af99032042bd640c810cf950320433d540c810db948320436d520c810f34c8320427e64944109f592510427e62944109f58a510427d65d0410cf953410433d54d0410db94
  | 2 => 0x6590110cfd52404433c5490110dbd4a404436c5290110be996404437a6590110be59240443bb5490110de95240443785490110ee15240443385490110be58a40443eb5290110fa14a40443bb4290110ee50a40442fa6190110ee90640443b841901109fd95404427d65501109f195404433f5450110cf151404436f5250110db14940442f76150110bd18540442f86550110de19540442786550110eed9140443bb5450110de95140443785450110ee15140442fb6250110fad4940443e85250110fcd8540442f86150110fc18540443bb4150110ee505404427e6510110cfd50404433c5410110dbd48404436c5210110be98040443b940101109f99720442be64c8110af593204433f54c8110cf15320442de63c8110b758f204435f53c8110d714f204436f52c8110db14b20442f661c8110bd587204427e6588110cfd52204433c5488110d7d4e204435c5388110dbd4a204436c5288110be996204437a6588110bed9220442f96488110eed5220443b85488110bed8e20442f96388110f6d4e20443d85388110be58a20443eb5288110de94a20443785288110fa14a20443685288110fa90a20443e94288110fa8ca20443e93288110be98620443ea2188110fa086204427f65481109f595204427c6548110cfd51204433c5448110d7d4d204435c5348110dbd49204436c5248110bdd8520442f46148110be195204437865481109e19520442fb6448110be59120443bb5448110ee15120442fb6348110be58d20443db5348110f614d20443eb6248110fad49204437a5248110de14920443e85248110fcd8520442f86148110fc18520443eb2148110fa485204427e6508110cfd50204433c5408110d7d4c204435c5308110dbd48204436c5208110be98020443e92008110cfd53104433c54c4110dbd4b104436c52c4110bed9310442f964c4110eed5310443b854c4110bed8b10442f962c4110fad4b10443e852c4110cfd52104433c5484110dbd4a104436c5284110edd5210443b45484110f9d4a10443e45284110fcd4210443f24084110fc50210443f22084110fc48210442ee62d5010bb58b540427e62d5010db98b540426e62d50109f58b540436d62d50109b58b540427e61d5010dd987540427e60d5010de983540427d6595010cfd52540427e62950109f58a540423d6595010cfd8a540433e6295010cf58a540433c6295010cf986540433c6195010cf982540433c6095010cfd91540427f62550109f189540427f61550109f585540427f60550109f581540433f6555010cfd89540433e6255010cf589540433c6255010cf985540433c6155010cf981540433c6055010cf04154042be6415010cf55054042ee6215010bb588540427e6415010cf990540423e64150109f988540436e62150109b988540427d6215010db588540
  | 3 => 0x910d718d524425c6354910dbd89524427f6154910ddd85524427f6054910ded81524427e6514910cfd50524433c5414910d7d4c524436d52149109f990524427d64149109f98c524427d6314910db988524427e61149109f184524427e6014910de580524427c6014910bb994524436e65149109b994524436f5414910ebd50524432f5414910db950524436d5414910db15052443ac5414910cb150524436f5314910f3d4c524434f5314910db94c524436d5314910db14c52443cc5314910d314c52443e96014910dbd90524436e6414910db590524436c6414910dbd8c524436e6314910db58c524436c6314910dbd84524436d6114910dbd80524436d6014910da580524436d10149109fd97424427e65d09109f597424427c65d0910cfd53424433c54d0910d7d4f424435c53d0910dbd4b424436c52d0910be98342442f960d09109fd96424427e65909109f596424427c6590910cfd52424433c5490910d7d4e424435c5390910dbd4a424436c5290910be98242442f960909109fd95424427e65509109f595424427c6550910cfd51424433c5450910d7d4d424435c5350910dbd49424436c52509109fd94424427e65109109f594424427c6510910cfd50424433c5410910b798c42442dd6310910d7d4c424435c5310910dbd48424436c5210910eb50842442f66110910bd58442442fa6010910be580424427f658c9109f996324427d658c9109f196324433f548c910cf152324435f538c910d714e324436f528c910db14a32442fa608c910be582324427f654c9109f995324427d654c9109f195324433f544c910cf151324436f524c910db149324427f650c9109f994324427d650c9109f19432442be640c910af590324433f540c910cf150324436f520c910db14832443cd320c910bd98432442f5610c910be98032442f9600c9109f997414433f54d0510cf153414436f52d0510db14b41442fa60d0510be583414427e6590510cfd52414433c5490510dbd4a414436c52905109f195414433f5450510cf151414436f5250510db14941442fb6050510be181414427e6510510cfd50414433c5410510bb98841442ed6210510dbd48414436c5210510be980414427e65c8510cfd53214433c54c8510d7d4f214435c53c8510dbd4b214436c52c8510be98321442f960c85109f996214433f5488510cf152214435f5388510d714e214436f5288510db14a214427c6548510cfd51214433c5448510d7d4d214435c5348510dbd49214436c5248510bed8121442f860485109f99421442be6408510af590214433f5408510cf15021442de6308510b758c214435f5308510d714c214436f5208510db14821442fa60085109f997404433f54d0110cf15340442ee62d0110bb58b404436f52d0110db14b40442f661d0110bd587404427e
  | 4 => 0xc98640843f16190210ee90640843b84190210cfd51408433c5450210bed95408437b6550210eed9140843bb5450210de95140843785450210ee15140842fb6250210be18540843bb4150210ee505408433e5410210cf55040842f66110210bd58440843b94010210af99320842bd64c8210b798f20842dd63c8210dbd4b208436c52c8210db94a208436d5288210bd98620842f56188210be59620843796588210bed9220842f96488210bed8e20842f96388210de94a20843ea5288210fa54a20843785288210fa90a20843e94288210fa8ca20843e93288210be98620843f26188210fc58620843ea2188210fa086208436f5248210db14920842fb6548210ded9520842fb6448210be59120842fb6348210be58d20843eb6248210fad49208437a5248210de14920843e85248210be18520843eb2148210fa485208436e5208210db54820842f66108210bd58420843e92008210bd597108437565c4210be597108437965c4210bed9310842f964c4210bed8b10842f962c42109f98b544427d62d5110eed83544433f62d5110cf98b544433d62d5110cf18b544433f61d5110cf587544433f60d5110cf583544433f5495110bb98a54442ed62951109f992544423e64951109f98a544436e62951109b98a544427d6295110db58a544426d62951109f586544437561951109f58254443796095110bbd8954442ec6255110cfd91544427f6255110dbd89544426f62551109f189544436c62551109b189544427f6155110ddd85544427f6055110ded81544427e6515110cf550544433e64151109f988544427d62151109f984544427c61151109f980544437960151109f18054442be6515110cf994544423e6515110ee580544433f6215110cf988544433d6215110cf188544433f6115110cf584544433f6015110cf58054443396015110cf440544433f54d4910cf153524427e64d49109f593524427e63d49109f58f524436f54d4910ebd53524432f54d4910db953524436d54d4910db15352443ac54d4910cb153524436f53d4910f3d4f524434f53d4910fad83524436f64d4910db993524436d64d4910db193524436f63d4910db98f524436d63d4910db18f524436f61d4910db587524436f60d4910db58352442be6494910af592524433f5494910cf15252442de6394910b758e524435f5394910dbd4a524427e6494910cf992524423e64949109f592524433d64949108f592524427e6394910d798e524425e63949109f58e524435d63949109758e524427e62949109b98a524427d6194910dd586524427d6094910de58252442bf6454910af191524433f5454910cf15152442df6354910b718d524435f53549109fd91524433f64549108fd91524427c6454910cf191524423c64549109fd8d524435f635491097d8d524427c6354
  | 5 => 0x41c42ed6210710be98041c42f96010710dbd4b21c436c52c8710db94a21c436d5288710be98221c42f96088710dbd4921c436c5248710af99021c42bd6408710b798c21c42dd6308710db94821c436d5208710be98021c42f96008710cf95340c433d54d0310bb98b40c42ed62d0310bd98740c42f561d0310cfd5240c433c5490310cf95140c433d5450310bdd8540c42f46150310cfd5040c433c5410310af99320c42bd64c8310b798f20c42dd63c8310db94b20c436d52c8310bd98720c42f561c8310dbd4a20c436c5288310db94920c436d5248310bdd8520c42f46148310dbd4820c436c52083109f98b548427d62d5210dd587548437a60d5210cfd5254842ee6295210bb58a548427e6295210db98a548426e62952109f58a548436d62952109b58a548437a6095210cfd91548427f62552109f189548433d5415210cf990548427e62152109f58854843756115210de980548427e64d4a109f593528427e63d4a109f58f528437561d4a10de98352842be6494a10af59252842de6394a10b758e528436f5294a109f992528433e6494a108f992528427d6494a10cf592528423d6494a109f98e528435e6394a109798e528427d6394a10d758e528425d6394a10de982528427f6454a109f191528427f6354a109f18d528436f6254a10db548528427e6414a109f590528427e6314a109f58c528436e6214a10dd584528437a6014a109fd97428427e65d0a109f597428427c65d0a10cfd53428433c54d0a10be98342842f960d0a109fd96428427e6590a109f596428427c6590a10dbd4a428436c5290a10be98242842f96090a109fd95428427e6550a109f595428427c6550a10cfd51428433c5450a10dbd49428436c5250a109fd94428427e6510a109f594428427c6510a10b798c42842dd6310a10eb50842842fa6010a10be580428427f658ca109f996328427d658ca109f196328436f528ca10db14a32842fa608ca10be582328427f654ca109f995328427d654ca109f195328436f524ca10db149328427f650ca109f994328427d650ca109f19432842be640ca10af59032843cd320ca10be98032842f9600ca10cf953418433d54d0610be98341842f960d0610cfd52418433c5490610cf951418433d5450610bed8141842f86050610cfd50418433c5410610bb98841842ed6210610be580418436e52c8610db54b21842fa60c8610be583218436f5288610db14a218436e5248610db54921842fb6048610be18121842be6408610af59021842de6308610b758c218436f5208610db14821842f96008610cfd53408433c54d0210bb98b40842ed62d0210cf952408433d5490210bd98640842f56190210be59640843796590210de95240843ba5490210ee55240843785490210be58a40843bb4290210ee50a40842fa6190210f
  | 6 => 0x33e5490020cf55240082ee6290020bb58a40083ad42900209fd95400827f65100209f994400827d65100209f194400833e5410020cf55040082ee6210020bb58840083ad4210020ee500400827d65cc020af99330082bd64cc020bb98b30082ed62cc0209fd96300827d658c020d794e300835d538c020bb98a30082ed628c020f34ca300827f654c0209f994300827d650c0209f19430082ee620c020bb58830083cd320c020af99320082bd64c8020b798f20082dd63c8020bbd9320083ae64c8020bb59320083ad64c8020ab59320082ef63c8020f398f20082ed63c8020f358f20082cd63c8020bb987200836d51c8020bb58a200836e5288020be58a200837a5288020fa94a20083ea4288020fa50a20083ea3288020fa4ca20083795188020fa88620083e821880209fd9520082ef6548020dbd95200826f6548020bbd9120082ed6448020bbd8d20082ed6348020bb185200836d5148020bbd81200836e5048020fad0120083e84048020facc120083e83048020bed95200837b65480209ed9520082fb6248020fad89200837a5248020fa94920083eb4248020fa10920083eb3248020fa0c920083795148020fac8520083e921480209f98b54c427d62d5310dd98754c437960d5310cfd5254c427e62953109f58a54c433f64553109fd8954c427c6255310cf55054c42ee6215310bb58854c433e64153109f98854c436e62153109b98854c427d6215310db58854c426d6215310dd98454c437960153109f99352c427d64d4b109f98f52c427d63d4b10dd98752c437960d4b10dbd4a52c427e6494b109f59252c427e6394b109f58e52c427f6454b109f19152c427f6354b109f18d52c436f6254b10af99052c42bd6414b10b798c52c42dd6314b10db54852c427e6414b10cf99052c423e6414b109f59052c433d6414b108f59052c427e6314b10d798c52c425e6314b109f58c52c435d6314b109758c52c436e6214b10dd98452c43796014b109fd9742c427e65d0b109f59742c427c65d0b10cf95342c433d54d0b109fd9642c427e6590b109f59642c427c6590b10db94a42c436d5290b109fd9542c427e6550b109f59542c427c6550b10cf95142c433d5450b10db94942c436d5250b10bed8142c42f86050b109fd9442c427e6510b109f59442c427c6510b10b798c42c42dd6310b10eb50842c42f66110b10bd58442c427f658cb109f99632c427d658cb109f19632c436e528cb10db54a32c427f654cb109f99532c427d654cb109f19532c436e524cb10db54932c42fb604cb10be18132c427f650cb109f99432c427d650cb109f19432c42be640cb10af59032c43cd320cb10bd98432c42f5610cb10cfd5341c433c54d0710cf95241c433d5490710be98241c42f96090710cfd5141c433c5450710cf95041c433d5410710bb988
  | 7 => 0x350820db54d42083af4350820eb50d42082ec6150820bbd81420827f65108209f594420833e5410820cf55042082de6310820b758c42082ee6210820eb50842082fa6010820be580420827d65cc820d7d4f320827f658c8209f596320835e538c820d754e32082fa608c820be582320836d658c8209b59632082ef648c820bb592320836f548c820db55232082ed638c820db94e32083ce538c820f354e320836c538c820bb98632083ea608c820bb58232083e9608c820ba582320827f654c820d7d4d32082ef654c820dbd9532082ef644c820bb591320836f544c820db55132083cf634c820f3d4d320836e534c820db14d32083cc534c820d314d32083ce434c820f350d32082ec614c820bbd81320827f650c8209f59432082be640c820af590320835e530c820d754c32082ee620c820f34c832082fa600c820be580320837751944209f992510827d64944209f98e510827d63944209fd91510827c64544209fd8d510827c6354420db909510836d4254420db8c9510836d3254420af99051082bd6414420b798c51082dd6314420dd544510827f65d04209f997410827d65d0420cf953410833d54d0420bb98b41082ed62d0420eb50b410827f65904209f996410827d6590420dd946410837551904209fd95410827d65504209f195410833e5450420cf55141082ef6250420bb18941083ad4250420dd94541083755150420bed8141082f860504209fd94410827e65104209f59441082de6310420b758c41082ee6210420bb58841082fa6010420be580410827f65cc4209f997310827d65cc420d794f310835d53cc420bb98b31082ed62cc420f34cb310827f658c4209f996310827d658c420dd9463108375518c4209fd95310827d654c4209f195310835e534c420d754d31082ef624c420bb18931083cd324c420dd9453108375514c420bed8131082f8604c4209fd94310827e650c4209f59431082be640c420af59031082ee620c420bb58831082fa600c420be580310836e52c8420dd947210837551c8420be98321082f960c84209f59621082ed6588420db596210826d6588420bbd9221082ed6488420bbd8e21082ed6388420bb986210836d5188420bb582210827f6548420db94921082be6408420af59021082de6308420b758c21083765108420dd54421082fa6008420be58021082ef6408420eb99021082ed6408420eb59021082ad6408420bbd8c21083ce6308420bb58c21083cd6308420b358c21082ee6108420f998421083e65108420db54421083e55108420fa98021082ed6008420fa58021082e960084209f992500827d64940209f98e500827d6394020db90a500836d4294020db8ca500836d3294020db886500836c21940209f59740082de63d0020b758f40082ee62d0020bb58b400827f65900209f5964008
  | 8 => 0x20cf15340482de63d0120b758f40482ee62d0120bb58b404827e6590120cf952404833d54901209fd95404827d65501209f195404833f5450120cf15140482ef6250120bb189404827e6510120cf950404833d54101209f99730482be64cc120af593304835f53cc120d714f30482ee62cc120bb58b304835e538c1209f595304827c654c120bbd8930482ec624c120af99320482bd64c8120b798f20482dd63c8120ee99320483b964c8120f698f20483d963c8120be58720483eb21c8120fa487204836f5488120db552204836f5388120db54e20482ed6188120db14620483eb50881209f98f540827d63d50209f98b540836e62d50209f987540827d61d50209f983540837a60d50209f596540833f54950209f98e540827d6395020db98a540827e61950209f586540833f64550209fd8d540827c63550209fd89540827d62550209fd85540827c6155020cf55054082de6315020b758c54082f66115020bd584540827e6415020cf990540827e6315020d798c540825e63150209f58c540835d63150209758c540827e6215020db988540827e6115020dd984540827661150209f584540837561150209d584540827e6015020de980540827e64d4c209f593530836e62d4c209f987530827d61d4c20de983530827d6594c20d7d4e530827e6494c209f592530836e6294c209f986530827d6194c209fd91530827c6454c20d7d8d530827f6254c209f589530827f6154c209f18553082be6414c20af590530835d5314c20bd98453082f56114c209f990530833e6414c208f990530827d6414c20cf590530823d6414c209f988530836e6214c209f98453083766114c209d984530827d6114c20dd58453082756114c209f980530837a6014c209fd97430827e65d0c209f597430827c65d0c20cf953430833d54d0c20bb98b43082ed62d0c20be98343082f960d0c209fd96430827e6590c209f596430827c6590c20d794e430835d5390c20bb98a43082ed6290c20be98243082f96090c209fd95430827e6550c209f595430827c6550c20cf951430833d5450c20d794d430835d5350c209fd94430827e6510c209f594430827c6510c20e750c43082ee6210c20bb588430827e6494820cf992520823e64948209f592520833d64948208f592520835e63948209f58e520835d63948209758e520827d65d0820cfd53420833c54d08209fd96420827d6590820cf952420833d5490820be98242082f96090820db596420826d6590820bb592420836e5490820eb95242083ad5490820db15242082ed6390820dbd4e420836d5390820bb98642083ea6090820bb58242083e96090820ba582420827f6550820cfd51420833c5450820bbd95420836f6550820ebd9142083af5450820db951420836c5450820eb151420832c5450820bbd8d420836f5
  | 9 => 0x593534827e61d4d209f58753482be6494d20af592534835f5394d209f992534833e6494d208f992534827d6494d20cf592534823d6494d20db58a534827e6194d209f58653483796094d209fd91534827c6454d20dbd89534827f6154d209f185534827f6054d20ded81534827e6514d20d754c534827e6414d209f590534835e6314d209f188534827e6114d209f584534827f65d0d209f997434827d65d0d209f197434833f54d0d20cf153434827f6590d209f996434827d6590d209f196434835f5390d20d714e434827f6550d209f995434827d6550d209f195434833f5450d20cf151434835f5350d20d714d43482ef6250d20bb18943482fb6050d20be181434827f6510d209f994434827d6510d209f194434839d4310d20bb98843482ed6210d209f997424833f54d0920cf15342482fa60d0920be583424827e65909209f195424833f5450920cf15142482fb6050920be181424827e6510920b798c42482dd6310920eb508424835f53cc920d714f32482fa60cc920be583324827e658c920d7d4d324835c534c920bed8132482f8604c9209f99432482be640c920af59032483cd320c9209f993514827d64d45209f98f514827d63d4520ddd4651482bf6454520af19151482df6354520b718d51482be6414520af59051482de6314520b758c514837551145209f990514833e64145208f990514827d6414520cf590514823d64145209f98c514835e63145209798c514827d6314520d758c514825d6314520de580514827e65d05209f597414827c65d0520cf953414833d54d05209f996414827d65905209f196414833f5490520cf15241482ee6290520bb58a41482fa6090520be582414827f65505209f995414827c6550520cf951414833d54505209f994414827d65105209f194414833f5410520cf15041482de6310520b758c41482ee6210520bb58841482fa6010520be580414827e65cc5209f597314827c65cc520d794f314827e658c5209f596314827c658c520d7d4e314835c538c520bb98a31482ed628c520be98231482f9608c5209fd95314827e654c5209f195314835e534c5209f994314827d650c5209f19431482be640c520af590314835f530c520d714c31482ee620c520bb58831482fa600c520be580314827e65c8520bb997214836e65c85209b997214836f54c8520db553214836f53c8520db54f214836c51c8520fad8321482ee60c8520fa18321482ed6288520ddd4621483745188520be98221482f96088520ddd4521483745148520bed8121482f86048520dbd51214836d5448520dbd4d214836d5348520f9d8521483e75148520db14521483e45148520fad8121482ec6048520fa181214827e6508520af99021482bd6408520b798c21482dd6308520bb98821482fa60085209f997404833f54d01
  | 10 => 0x2883cd534ca20f390d32883cd434ca20bb18532882ef604ca20fad8132883e8604ca20af99032882bd640ca20f34c8328837751946209f992518827d64946209f98e518827d6394620de982518827f64546209f191518827f63546209f18d518836e4254620db509518836e3254620db4c951882be6414620af59051882de6314620b758c518837551146209fd97418827e65d06209f597418833e54d0620cf55341882ee62d0620bb58b41883ad42d06209fd96418827e65906209f59641882fa6090620be582418827f65506209f595418827c6550620cf951418833d5450620bbd8941882ec6250620eb509418827f65106209f994418827d6510620b798c41882dd6310620bb98841882ed6210620be98041882f960106209fd97318827e65cc6209f597318835e53cc620d754f31882ee62cc620bb58b31883cd32cc6209fd96318827e658c6209f59631882fa608c620be582318827f654c6209f595318827c654c620d794d318835d534c620bbd8931882ec624c620f34c9318827f650c6209f994318827d650c620af99031882bd640c620bb98831882ed620c620be98031882f9600c620dd94621883755188620be98221882f96088620bbd9221882ed6488620bbd8e21882ed6388620f9946218836d5188620f954621883ea6088620bb58221883e96088620dd94521883755148620bed8121882f86048620af99021882bd6408620b798c21882dd6308620be58021882ed6508620db59421882ef6408620eb99021882ed6408620eb59021882ad6408620bbd8c21883ce6308620bb58c21883cd6308620b358c21883e66108620db54421883ea6008620bb58021883e96008620ba58021882de63d0220b758f40882ee62d0220bb58b408833e5490220cf55240882ee6290220bb58a40883ad4290220cf950408833d5410220bb98840882ed6210220eb50840882be64cc220af59330882ee62cc220bb58b30882ee628c220bb58a30883cd328c220af99320882bd64c8220b798f20882dd63c8220bb597208836d65c8220bbd9320883ae64c8220bb59320883ad64c8220ab59320883ce63c8220bb58f20883cd63c8220b358f20882ee61c8220db54720882f965c8220de59720883ba64c8220ee59320883da63c8220f658f20882f961c82209f98f544827d63d51209f987544827d61d5120cfd5254482de6395120b758e544827e64951209f98e544835e63951209798e544827d6395120d758e544825d63951209f58a544836d62951209b58a544827e61951209f586544827d6095120de582544833f64551209fd8d544827c63551209fd89544836f62551209fd85544827c61551209fd81544837b60551209f994544833d5415120cf990544827e63151209f58c544827e62151209f188544827e61151209f584544827e64d4d209f
  | 11 => 0xef6548720dbd9521c836f5448720eb95121c836d5448720eb55121c832d5448720f394d21c836d5348720f354d21c834d5348720f9d8521c836e5148720bb18121c82be6408720af59021c833e5408720cf55021c82de6308720b758c21c835e5308720d754c21c83765108720dd54421c82fa6008720be58021c833e54d0320cf55340c82de63d0320b758f40c835e53d0320d754f40c82ee62d0320bb58b40c833e5490320cf55240c835e5390320d754e40c833e5450320cf55140c835e5350320d754d40c82ef6250320bb18940c833e5410320cf55040c835e5310320d754c40c83b94010320cf95330c833d54cc320bb98b30c82ed62cc320b798f54882dd63d52209f98f548835e63d52209798f548827d63d5220d758f548825d63d5220db58b548827e61d52209f587548837a60d5220cfd5254882de6395220b758e548827e6395220d798e548825e63952209f58e548835d63952209758e548836d62952209f986548827d6195220cfd91548827f63552209f18d548827f61552209f185548833d5415220cf990548827e63152209f58c548836d62152209f984548827d6115220de98054882be64d4e20af593538827e64d4e20cf993538823e64d4e209f593538833d64d4e208f593538827e61d4e209f587538837a60d4e20af99253882bd6494e20d7d4e538827e6494e20cf992538823e6494e209f592538833d6494e208f592538836d6294e209f986538827d6194e209fd91538827c6454e20d7d8d538827f6154e209f185538835d5314e209fd97438827e65d0e209f597438827c65d0e20cfd53438833c54d0e20d794f438835d53d0e20bb98b43882ed62d0e209fd96438827e6590e209f596438833e5490e20cf55243882ee6290e20bb58a438827f6550e209f995438827d6550e209f195438833f5450e20cf15143882fb6050e20be181438827f6510e209f994438827d6510e20cf950438833d5410e20d794c438835d5310e20e750c43882ee6210e20bb588438833e54d0a20cf55342882fa60d0a20be58342882ed6590a20db596428836e5490a20db15242882ed6390a20dbd4e428836d5390a20bb98642882ed6090a20cf951428833d5450a20bed8142882f86050a20dbd9542883af6450a20db95142883ae5450a20cb95142883ad5450a20db15142882ef6350a20dbd4d428836d5350a20ebd0d42883ad4350a20bb18542882ef6050a20fad8142883e86050a20b798c42882dd6310a20eb508428835e53cca20d754f32882fa60cca20be58332882ed658ca20db59632882ef648ca20bb592328836f548ca20db552328836e538ca20bb98632882ed608ca20d794d328835d534ca20bed8132882f8604ca20dbd9532882ef644ca20bb591328836f544ca20db55132883cf634ca20db94d32883ce534ca20d394d3
  | 12 => 0xd0f209fd9643c827e6590f209f59643c827c6590f20cf95243c833d5490f20d794e43c835d5390f20be98243c82f96090f209fd9543c827d6550f209f19543c833e5450f20cf55143c835e5350f20d754d43c82ef6250f20bb18943c827f6510f209f99443c827d6510f209f19443c833e5410f20cf55043c835e5310f20d754c43c839d4310f20bb98843c82ed6210f20cf95342c833d54d0b20d794f42c835d53d0b20cf95242c833d5490b20d794e42c835d5390b20be98242c82f96090b20cf95142c833d5450b20d794d42c835d5350b20cf95042c833d5410b20b798c42c82dd6310b20d794c42c835d5310b20eb50842c82fa6010b20be58042c833e54ccb20cf55332c835d53ccb20cf95232c833d548cb20d794e32c835d538cb20be98232c82f9608cb20cf95132c833d544cb20d794d32c82be640cb20af59032c833e540cb20cf55032c835e530cb20d754c32c83cd320cb20be98032c82f9600cb20af99351c82bd64d4720cf95351c833d54d4720b798f51c82dd63d4720d794f51c835d53d4720cf95251c833d5494720d794e51c835d5394720ddd4651c827e64947209f59251c827e63947209f58e51c833e5454720cf55151c835e5354720d754d51c827f64547209f19151c827f63547209f18d51c82be6414720af59051c833e5414720cf55051c82de6314720b758c51c835e5314720d754c51c837551147209fd9741c827e65d07209f59741c833e54d0720cf55341c835e53d0720d754f41c827f65907209f99641c827d6590720cf95241c833d5490720d794e41c835d5390720bb98a41c82ed62907209fd9541c827d65507209f19541c833e5450720cf55141c835e5350720d754d41c82fb6050720be18141c827f65107209f99441c827d6510720cf95041c833d5410720b798c41c82dd6310720d794c41c835d5310720bb98841c82ed6210720be98041c82f960107209fd9731c827e65cc7209f59731c833e54cc720cf55331c835e53cc720d754f31c827f658c7209f99631c827d658c720cf95231c833d548c720d794e31c835d538c720bb98a31c82ed628c7209fd9531c827d654c7209f19531c833e544c720cf55131c835e534c720d754d31c82fb604c720be18131c827f650c7209f99431c827d650c720af99031c82bd640c720cf95031c833d540c720d794c31c835d530c720bb98831c82ed620c720be98031c82f9600c720cf95321c833d54c8720d794f21c835d53c8720dd94721c837551c8720be98321c82f960c8720dbd5321c83ae54c8720db55321c83ad54c8720cb55321c83ce53c8720db54f21c83cd53c8720d354f21c836e51c8720f994721c83e551c8720bb98321c83ea60c8720fa58321c833e5488720cf55221c835e5388720d754e21c833e5448720cf55121c835e5348720d754d21c82
  | 13 => 0xaf593211036e52c8440db54b21103ad42c84409fd96211027e65884409f59621102bf6488440af19221103765188440dd546211027f65484409f595211027c6548440afd9121102bc6448440db949211036d5248440eb50921103765148440dd54521102fb6048440be181211027f65084409f994211027d6508440af99021102bd6408440b798c21102dd6308440be98021102f96008440cfd0a501033d4294040cf906501033c4194040bb98b40102ed62d0040eb98b40102bd62d0040eb58b40102ad62d0040af987401033d51d0040af592401033e5490040be592401037a5490040ee95240103bb4290040ee50a40103795190040ee90640103b841900409fd9540102bf6550040cfd95401023f6550040afd8940102bc6150040cf54540102bf6050040cf94140102fb6550040ded95401027b6550040bed9140103bb6450040de95140103ba5450040ee90940103b84250040de54540103bb4150040ee50540102de63d5320b758f54c827e63d5320d798f54c825e63d53209f58f54c835d63d53209758f54c836e62d53209f98754c827d61d5320de58354c833f54953209f98e54c827d63953209f98654c827d6195320cfd8e54c833e6395320cf58e54c833c6395320cf98a54c833c6295320cfd8654c833e6195320cf58654c833c6195320cfd8254c833d6095320cfd9154c827f63553209f18d54c827f61553209f18554c833f6555320cfd8d54c833e6355320cf58d54c833c6355320cf98954c833c6255320cfd8554c833e6155320cf58554c833c6155320cfd8154c833d6055320cf55054c82de6315320b758c54c833e64153209f98c54c835e63153209798c54c827d6315320d758c54c825d6315320db98854c827e61153209f58454c83796015320af99353c82bd64d4f20cf95353c833d54d4f20cf95253c833d5494f20d7d4e53c827e6494f209f59253c827e6194f209f58653c835f5494f20d795253c839e5494f20c795253c835d5494f20e755253c831d5494f20d715253c835f6494f20d799253c835d6494f20d719253c835c6294f20d7d8653c835e6194f20d758653c835c6194f20d7d8253c835d6094f20cf95153c833d5454f209fd9153c827c6454f209fd8553c827c6154f20d7d9553c835f5454f20d795153c839e5454f20c795153c835d5454f20e755153c831d5454f20d715153c835f6454f20d799153c835d6454f20d719153c835e6254f20d7d8553c835e6154f20d758553c835c6154f20d7d8153c835d6054f20af99053c82bd6414f20cf95053c833d5414f20d754c53c827e6414f20cf99053c823e6414f209f59053c833d6414f208f59053c836e6214f209f98453c827d6114f20de58053c827f65d0f209f99743c827d65d0f20cf95343c833d54d0f20d794f43c835d53d0f20be98343c82f960
  | 14 => 0x49325036c524c940bed8132502f8604c9409f994325027d650c9409f19432502be640c940af59032503cd320c9409f98b515027d62d4540ddd4651502ef6254540bb18951502ee6214540bb588515037551145409f988515036e62145409b988515027d6214540db588515026d6214540de580515027e65d0540af997415033e65d05408f997415033f52d0540cf14741503bb60d0540af98341503b860d0540af59241503775190540dd14641502fa6090540be58241503775150540dd14541502fb6050540be181415033f5250540edd8541503b75150540cf14541503b45150540eed8141502bc6050540ee181415027e6510540af99041502ee6210540bb58841502fa60105409f997215027d65c85409f197215027e65885409f596215027c6588540af99221502bd6488540dbd4a215036c5288540be98221502f960885409fd95215027e65485409f195215027e65085409f594215027c6508540af99021502bd6408540b798c21502dd6308540dbd48215036c5208540be98021502f96008540bb98b40502ed62d0140fa98b40503e962d0140be58740503bb41d0140ee507405033f5290140af586405033c5190140eed42405036e6295040db58a541036f52948409f98e521027d63948409f986521027d61948409fd8d521027c63548409fd85521027c6154840b798c52102dd6314840db54852102f66114840bd584521036e52d0840db54b42102fa60d0840be58342102bd63d0840cf54f421033e52d0840eb94b42103ad52d0840af98742103ba60d0840af58342103b960d0840ae583421027d6590840af592421027f6550840afd95421033f6550840afd8d421033d5350840ebd8942103af5250840cf94942103ac5250840af18542102bf6050840af99042102de6310840b758c421036e5210840db54842103ad4210840be98042102f960108409fd96321027e658c8409f59632102be648c840af592321036e528c840db54a32103ad428c840be98232102f9608c8409fd95321027d654c8409f19532102be644c840af591321036e524c840db54932103ad424c8409fd94321027e650c8409f59432102be640c840af59032103cd320c840ddd46511027e62944409f58a511027f62544409f189511033f4254440cf50951102ee6214440bb58851103755114440cf953411037651d0440dd54741102fa60d0440be583411027d6590440af596411033d65904408f59641102bd6290440af986411033d5190440af582411027f6550440cf95141102ee6210440bb58841103765110440dd54441102fa6010440be58041103ae6210440af58841103ad6210440ab58841102be6110440ed98441103b65110440cf54441103b55110440ee98041102bd6010440ee58041102b960104409fd97211027e65c84409f59721102be64c844
  | 15 => 0xd027d65487409f19521d035e5348740d754d21d036e5248740db54921d02fb6048740be18121d027f65087409f99421d027d6508740af99021d02bd6408740b798c21d02dd6308740d794c21d035d5308740db94821d036d5208740be98021d02f96008740b798f52902dd63d4a40b798e52902dd6394a40dbd4a529027e6394a40d798e529025e6394a409f58e529035d6394a409758e529027e6194a409f586529027f6354a409f18d529027f6154a409f185529036d5214a40af597429033d65d0a40af58f429033d53d0a40cf94b42902be61d0a40af583429036e5290a40db54a42902fa6090a40be582429036e5250a40db54942902fb6050a40be18142902bf6350a40cf54d42903af6250a40cf94942903ae5250a40cb94942903ad5250a40af18542902bf6050a40eed8142903b86050a40b798c42902dd6310a40eb508429027f658ca409f996329027d658ca40af99232902bd648ca40d794e329035d538ca40eb50a329027f654ca409f595329027c654ca40af99132902bd644ca40eb50932902fb604ca40be181329027f650ca409f994329027d650ca40af99032902bd640ca40db948329036d520ca40f34c8329037751946409f98a519027d6294640de982519027f62546409f189519033f4254640cf50951902ee6214640bb58851903755114640dd94641903755190640be98241902f96090640af58a41903b65190640cf54641903b55190640ee98241902bd6090640ee58241903765150640dd54541902fb6050640be18141902ee6210640bb58841902f96010640af594419033d6510640eb98841902bd6210640eb58841902ad6210640ed984419033d5110640ee98041902bd6010640ee58041902b960106409fd97219027e65c86409f59721902be64c8640af593219036e52c8640db54b21903ad42c86409fd96219027e65886409f59621902bf6488640af19221902fa6088640be582219027f65486409f595219027c6548640afd9121902bc6448640db949219036d5248640eb509219027f65086409f994219027d6508640af99021902bd6408640b798c21902dd6308640be98021902f96008640bb98b40902ed62d0240af597409033d65d0240eb98b40902bd62d0240eb58b40902ad62d0240af987409033d51d0240be597409037965d0240fa98b40903e962d0240be587409027e63d49409f58f525027e61d49409f58752502de6394940b758e525036f5294940db548525027e63149409f58c525027e61149409f584525027e65d0940dbd4a425036c5290940be98242502f96090940dbd49425036c5250940bed8142502f860509409f99442502de6310940b758c42503ad42109409f996325027d658c9409f196325036f528c940db14a325027f654c9409f995325027c654c940afd9132502bc644c940dbd
  | 16 => 0x92154021fc485500877b6454021de99150087796454021de191500877b6354021de98d50087796354021de18d500877b4354021de90d50087794354021de10d500877a6254021ded09500877a4254021de50950087784254021decc9500877a3254021de4c950087783254021de985500877b4154021de90550087794154021de105500877b3154021de8c550087793154021de0c5500877b2154021dac85500877a2154021de48550087692154021de08550086be6414021af590500873e5414021cf55050086de6314021b758c500875e5314021d754c50086fa6014021de54050086de63d4b40b758f52d036f5294b409f98e52d027d6394b409f98652d027d6194b40dbd4e52d036e5394b40f394e52d034e5394b40db19252d036f6394b40db98e52d036d6394b40db18e52d036f6194b40db98652d036d6194b40db18652d036f6094b40db58252d035e5354b409fd8d52d027c6354b409fd8552d027c6154b40dbd9552d036f5354b40db94d52d03ce5354b40d394d52d036d5354b40f354d52d034d5354b40db99152d036f6354b40db98d52d036d6354b40db18d52d036f6154b40db98552d036d6154b40db18552d036f6054b40db58152d02de6314b40b758c52d035e5314b40d754c52d036d5214b40d794f42d035d53d0b40db94b42d036d52d0b40be98342d02f960d0b40d794e42d035d5390b40db54a42d035e5350b40d754d42d036e5250b40b798c42d02dd6310b40d794c42d035d5310b40db94842d036d5210b40eb50842d02fa6010b40be58042d027f658cb409f99632d027d658cb40d794e32d035d538cb40db94a32d036d528cb40be98232d02f9608cb409fd9532d027d654cb409f19532d02bf644cb40af19132d036e524cb40db54932d027f650cb409f99432d027d650cb40af99032d02bd640cb40db94832d036d520cb40f34c832d02ee62d4740bb58b51d036e52d4740db54b51d036e5294740db54a51d037751947409f98a51d027d6294740db94951d036d52547409fd8951d027c6254740bb98851d02ed6214740db94851d036d5214740dd54451d036e52d0740db54b41d037651d0740dd54741d02fa60d0740be58341d03ae52d0740cf54b41d03ad52d0740cb54b41d033e51d0740ed94741d03b551d0740af98341d03ba60d0740ee58341d036e5290740db54a41d036e5250740db54941d02bf6550740cfd9541d03ae5250740cf54941d03ad5250740cb54941d03b76150740cf94541d02bc6050740bb98841d02ed6210740db94841d036d5210740dd94441d03755110740be98041d02f960107409fd9721d027e65c87409f59721d035e53c8740d754f21d036e52c8740db54b21d027f65887409f99621d027d6588740af99221d02bd6488740d794e21d035d5388740db94a21d036d52887409fd9521
  | 17 => 0x421d794f410875d53d04219fd96410867d6590421cf952410873d5490421d794e410875d5390421bb98a41086ed62904219fd95410873e5450421cf551410875e5350421d754d410867f65104219f994410867d65104219f194410873e5410421cf55041086de6310421b758c410875e5310421d754c41086ee6210421bb58841086fa6010421be580410867d65cc421cf953310873d54cc421d794f310875d53cc4219fd96310867d658c421cf952310873d548c421d794e310875d538c421bb98a31086ed628c4219fd95310873e544c421cf551310875e534c421d754d310867e650c4219f594310867c650c421cf950310873d540c421bb98831086ed620c421cf953210873d54c8421d794f210875d53c8421dbd5321087ae54c8421db55321087ad54c8421cb553210876f53c8421f394f210876d53c8421f354f210874d53c8421bb983210873e5488421cf552210875e5388421d754e21086ed6288421db94a21087b65488421ed55221087d65388421f554e21086f56288421dd94a21087e652884219fd95210873e5448421cf551210875e5348421d754d21086ef6548421dbd95210866f6548421dbd5121087ae5448421db55121087ad5448421cb551210876f5348421f394d210876d5348421f354d210874d5348421bbd85210876e5148421bb18121086f76548421ddd9521086776548421ed95121087b55448421f594d21087d55348421bdd8921087e76248421dd94921087e65248421af99350086bd64d4021cf953500873d54d4021b798f50086dd63d4021d794f500875d53d4021cf952500873d5494021d794e500875d5394021ded42500867e64940219f592500867e63940219f58e500877b5494021de95250087ba5494021ce95250087795494021ee55250087395494021de152500877b5394021de94e50087da5394021d694e50087795394021f654e50087595394021de14e50087e86294021fac8650087f22194021fa48650087f12194021ded92500877a6494021de59250087786494021ded8e500877a6394021de58e50087786394021ded0e500877a4394021de50e50087784394021de18a500877b4294021de90a50087794294021de10a500877b3294021de8ca50087793294021de0ca50087786194021ded06500877a4194021de50650087784194021decc6500877a3194021de4c650087783194021dec86500877a2194021de486500873e5454021cf551500875e5354021d754d500867f64540219f191500867f63540219f18d500876f2154021db485500877b6554021ded51500877a5454021ee951500873a5454021de55150087b95454021ce55150087785454021ded4d500877a5354021f694d500875a5354021de54d50087d95354021d654d50087785354021fa18950087eb2154021fc88550087e
  | 18 => 0x9e980540867d6015021de58054086796015021af99353086bd64d4c21cf953530873d54d4c21be98353086f960d4c219f993530873e64d4c218f993530867d64d4c21cf593530863d64d4c21db98b530877661d4c219f983530877a60d4c219e983530867d60d4c21de583530867960d4c219f596530873e5494c21cf552530875f5394c219f992530867d6494c219f982530867d6094c2197596530875f5494c21d7952530879e5494c21c7952530875d5494c21e7552530871d5494c21d7152530875f6494c21d7992530875d6494c21d7192530875e6294c21d718a530875e6194c21d7186530875f6094c21d7982530875d6094c21d7182530873e5454c21cf551530867f6454c219f191530875f6354c219fd81530867c6054c21d7d95530875f5454c21d7951530879e5454c21c7951530875d5454c21e7551530871d5454c21d7151530875f6454c21d7991530875d6454c21d7191530875e6254c21d7189530875e6154c21d7185530875c2154c21d7d81530875e6054c21d7581530875c6054c21af99053086bd6414c21cf950530873d5414c21b798c530875d5314c21be98053086f96014c219f990530873e6414c218f990530867d6414c21cf590530863d6414c219f988530876e6214c219b988530867e6114c21dd984530867e6014c21de980530867a6014c219f58053087796014c219e580530867f65d0c219f997430867d65d0c219f197430873e54d0c21cf553430875e53d0c21d754f430867f6590c219f996430867d6590c219f196430873e5490c21cf552430875e5390c21d754e430867f6550c219f995430867d6550c219f195430873e5450c21cf551430875e5350c21d754d43086ef6250c21bb189430867f6510c219f994430867d6510c219f194430873e5410c21cf550430875e5310c21d754c430879d4310c21bb98843086ed6210c219f992520867d64948219f58e520867d65d0821cf953420873d54d0821d794f420875d53d08219fd96420867d6590821cf952420873d5490821d794e420875d5390821db94a42086f66190821bd586420867f6550821cf951420873d5450821d794d420875d5350821db949420867f65108219f594420873e5410821cf55042086de6310821b758c420875e5310821d754c42087ad4210821bd98442086f561108219f597320873e54cc821cf553320875e53cc821d754f320867f658c8219f596320873e548c821cf552320875e538c821d754e320876e528c821bd98632086f5618c8219fd95320873e544c821cf551320875e534c821d754d320876e524c8219fd94320867d650c821af99032086bd640c821cf950320873d540c821d794c320875d530c821f34c832086f6610c821bd584320867e64944219f592510867e63944219f58e510867d65d0421cf953410873d54d
  | 19 => 0x242486ed6390921dbd4e424876d5390921bb98642486ed60909219f195424873f5450921cf15142486f76150921bd185424876c65509219b19542487af6450921ebd51424876e5450921db15142487ac5450921cb15142486ef6350921dbd4d424876d5350921ebd0d42487ad4350921f9d8542486ec6150921f918542486ef60509219f99442486de6310921b758c42486ee6210921eb508424875f53cc921d714f32486f661cc921bd587324867e658c921bb996324876e658c921bbd9232486ed648c921dbd52324876d548c921bb58e324876e538c921db14e32486ee618c921bb582324875f534c921d714d32486f7614c921bd18532486ef644c921bb591324876f544c921db55132487cf634c921f3d4d324876e534c921db14d32487cc534c921d314d32487ce434c921f350d32487e7614c921bb18532487e4614c921bbd81324867e650c921af99032486bd640c921bb98832487cd320c9219f997414873f54d0521cf15341486ee62d0521bb58b41487ad42d05219f996414867f65505219f595414867c6550521cfd51414873c5450521bbd8941486ec6250521eb509414867e6510521b798c41486dd6310521bb98841486ed6210521be98041486f960105219f997314875f53cc521d714f31486ee62cc521bb58b31487cd32cc5219f595314867c654c521bbd8931486ec624c521f34c931487e642c8521f950b21487e632c8521f94cb21486ef6488521bb59221486ef6388521bb58e21487e75188521bb582214867e64d41219f593504867e63d41219f58f504877b5094121afd9150486bc6454121b7d8d50486dc6354121de540504867e64141219f590504867e63141219f58c504876e4214121db508504876e3214121db4c8504876e2114121b798f54086dd63d5021be98354086f960d50219f98f540875e63d50219798f540867d63d5021d758f540865d63d50219f98b540876e62d50219f987540877661d50219f983540877a60d50219e983540867d60d5021de583540867960d50219f596540873f54950219f98e540867d63950219f982540867d60950218f596540873f6395021cf98e540873d6395021cf18e540873e6295021cf18a540873e6195021cf186540873f6095021cf982540873d6095021cf182540873f64550219fd8d540867c63550219fd81540867c6055021cfd95540873f6355021cf98d540873d6355021cf18d540873e6255021cf189540873e6155021cf185540873c2155021cfd81540873e6055021cf581540873c6055021af990540873d5415021b798c54086dd6315021be98054086f960150219f990540873e64150218f990540867e6315021d798c540865e63150219f58c540875d63150219758c540867e6215021db988540866e62150219f984540877661150219f980540877a6015021
  | 20 => 0x873e54d0a21cf55342886f661d0a21bd587428873e5450a21cf55142886f76150a21bd18542886de6310a21b758c42887ad4210a21d794f328875d53cca21bd98732886f561cca21d794d328875d534ca21bdd8532886f4614ca21af99032886bd640ca21f34c8328873f54d0621cf153418873e5490621cf55241886ee6290621bb58a418873f5450621cf151418873e5410621cf55041886de6310621b758c41886ee6210621bb58841886fa6010621be58041886ee628c621bb58a31886ed65c8621db597218876f54c8621db553218876f53c8621db54f21886ee60c8621bd597218877565c8621ded42508867e64942219f592508867e63942219f58e50886bf6454221af19150886df6354221b718d508867f6454221cfd91508863f64542219f191508873c64542218f191508867f6354221d7d8d508865f63542219f18d508875c63542219718d508876f2154221af99050886bd6414221b798c50886dd6314221de540508867e63d51219f58f544867e60d51219f583544873f54951219f992544867e63951219f58e544867d6295121db58a544867d6195121dd586544867e60951219f58254486df6355121b718d54486fb6055121be181544873f64551219fd8d544875f635512197d8d544867c6355121d718d544865c63551219fd89544876f62551219fd85544877761551219fd81544877b60551219ed81544867c6055121de181544867860551219f994544873d5415121b798c54486dd6315121cf990544867e6315121d798c544865e63151219f58c544875d63151219758c544876d62151219f980544867d60151219f993534867d64d4d219f983534867d60d4d21d7d4e534867e6494d219f592534876d6294d21dd586534867e6094d219f58253486bf6454d21af19153486fb6054d21be181534867f6454d21cfd91534863f6454d219f191534873c6454d218f191534876f6254d219fd8553487776154d219fd81534877b6054d219ed81534867c6054d21de18153486786054d219f99453486be6414d21af590534875d5314d219f990534873e6414d218f990534867d6414d21cf590534863d6414d21d798c534867e6014d219f580534867f65d0d219f997434867d65d0d219f197434873e54d0d21cf553434875f53d0d21d714f43486ee62d0d21bb58b434867f6590d219f996434867d6590d219f196434873f5490d21cf152434875e5390d21bb98a43486ed6290d219fd95434867e6550d219f595434867c6550d21cf951434873d5450d21d794d434867f6510d219f994434867d6510d219f194434873f5410d21cf150434875f5310d21d714c434879d4310d21bb98843486ed6210d219f997424873f54d0921cf15342486f661d0921bd587424867e6590921bb996424876e6590921bb592424876e5490921db15
  | 21 => 0x5390f21bb98a43c86ed6290f219fd9543c867d6550f219f19543c873e5450f21cf55143c875e5350f21d754d43c867f6510f219f99443c867d6510f219f19443c879d4310f21bb98843c86ed6210f21cfd5342c873c54d0b21cf95242c873d5490b21bd98642c86f56190b21db59642c876e5490b21eb95242c87ad5490b21db15242c86ed6390b21db54e42c86ee6190b21f998642c87e56190b21bb58242c873f5450b21cf15142c86ef6550b21dbd9542c87af6450b21ebd5142c876e5450b21db15142c87ac5450b21cb15142c86ef6350b21db54d42c87af4350b21eb50d42c86ec6150b21bbd8142c873e5410b21cf55042c86de6310b21b758c42c87ad4210b21bd98442c86f56110b21d794e32c875d538cb21bd98632c86f5618cb21bbd9232c86ed648cb21dbd5232c876d548cb21db94e32c87ce538cb21f354e32c876c538cb21bb98632c87e6618cb21f958632c86ed608cb21bbd9532c876f654cb21bbd9132c86ed644cb21dbd5132c876d544cb21f3d8d32c87cf534cb21db94d32c876c534cb21f314d32c874c534cb21f390d32c87cd434cb21bb18532c86ef604cb21af99032c86bd640cb21d794c32c875d530cb21f34c832c86f6610cb21bd58432c873e54d0721cf55341c86ee62d0721bb58b41c87ad42d0721cf95141c873d5450721bbd8941c86ec6250721eb50941c86de6310721b758c41c86ee6210721bb58841c86fa6010721be58041c86ee62cc721bb58b31c87cd32cc721af99350c86bd64d4321b798f50c86dd63d4321ded4250c867e64943219f59250c867e63943219f58e50c876e4294321db50a50c876e3294321db4ca50c867f64543219f19150c867f63543219f18d50c877950143219f98f548867d63d5221db58b548877661d52219f983548867d60d5221cfd52548867e63952219f58e548867e60952219f582548873f64552219fd8d548867c63552219fd81548867c6055221cf55054886de6315221b758c54886fa6015221be580548873e64152219f98c548875e63152219798c548867d6315221d758c548865d6315221db588548877661152219f980548877a60152219e980548867d6015221de580548867960152219f993538867d64d4e21dd987538867e60d4e219f583538875f5394e219f992538867d6494e219f982538867d6094e219fd91538867c6454e21d7d8d538867f6054e219f18153886be6414e21af590538875d5314e21be98053886f96014e219fd97438867e65d0e219f597438867c65d0e21cf953438873d54d0e219fd96438867e6590e219f596438875e5390e21d754e438867f6550e219f995438867d6550e219f195438873e5450e21cf551438875e5350e21d754d43886ef6250e21bb189438867f6510e219f994438867d6510e21e750c43886ee6210e21bb588438
  | 22 => 0x841d794c421075d5310841db948421076d5210841eb50842106f66110841bd584421067f658c8419f996321067d658c841d794e321075d538c841db94a321076d528c8419fd95321067d654c8419f19532106bf644c841af191321076e524c841db549321067f650c8419f994321067d650c841af99032106bd640c841db948321076d520c841f34c8321076e52d0441db54b41107ae52d0441cf54b41107ad52d0441cb54b41106be60d0441af592411073e5490441db94a411076d5290441bd59241107765490441ed95241107e65290441f954a411067f6550441db949411076d5250441afd95411073f65504418fd9541107ae5250441cf54941107ad5250441cb54941106bf6150441cf94541106bc6050441bdd95411077765504419dd9541106f76450441edd9141107765450441ed95141107e65250441f954941106ee62d4041bb58b501076e52d4041db54b501076e5294041db54a501077b50940419f98a501067d6294041ee192501077b5294041de94a50107ea5294041da94a50107795294041fa54a50107695294041de14a50107bb4194041fc90650107b94194041fc50650107786494041ded8a501077a6294041de58a50107786294041ded0a501077a4294041de50a50107784294041de8ca50107793294041de0ca50107786194041ded06501077a4194041de506501076e5254041db549501067f62540419f189501073f4154041cf505501077b6554041ee191501077b5254041de94950107ea5254041da94950107795254041fa54950107695254041de14950107bb4154041fc90550107b94154041fc505501077a6454041ded89501077a6254041de58950107786254041ded09501077a4254041de50950107784254041de8c950107793254041de0c9501077a6154041ded05501073b4154041de90550107794154041ce50550107784154041bb98850106ed6214041db948501076d5214041be980501077950140419f98f54c867d63d5321db98b54c877561d53219f98354c867d60d5321cfd5254c867e63953219f58e54c876e62953219f98254c867d6095321cfd9154c867f63553219f18d54c867f60553219f18154c873d5415321b798c54c86dd6315321cf99054c867e6315321d798c54c865e63153219f58c54c875d63153219758c54c876e6215321dd58454c867e60153219f58054c875f5394f219f99253c867d6494f219f98253c867d6094f219fd9153c867c6454f219fd8153c867c6054f21af99053c86bd6414f21d754c53c867e6414f21cf99053c863e6414f219f59053c873d6414f218f59053c876e6214f21dd58453c867e6014f219f58053c867f65d0f219f99743c867d65d0f21cf95343c873d54d0f21bb98b43c86ed62d0f219fd9643c867e6590f219f59643c867c6590f21d794e43c875d
  | 23 => 0xb94a429076d5290a41bd98642906f56190a41db949429076d5250a41bdd8542906f46150a41b798c42906dd6310a41eb508429067f658ca419f996329067d658ca41db94a329076d528ca419fd95329067d654ca419f19532906bf644ca41af191329076e524ca41db549329067f650ca419f994329067d650ca41af99032906bd640ca41f34c832906bd65d0641cf597419073d52d0641af98341906f565d0641dd597419077b50942419f98a509067d6294241bbd8950906ec62542419fd89509076f62542419bd89509067c6254241db189509066c6254241cfd0550906ee6214241bb588509077950142419f98f525067d63d49419f983525067d60d4941dbd4a52506df6354941b718d52506fb6054941be18152506de6314941b758c525076d52149419f98c525075e63149419798c525067d6314941d758c525065d63149419f980525067d60149419f99742506be65d0941cf99742506bd63d0941cfd4f425073c52d0941af98742506bd60d0941af592425076f5290941db14a42506f66190941bd586425076f5250941db14942506f76150941bd18542506bf6350941cfd4d42507af6250941ebd49425073c5250941eb149425072c5250941edd8542506bc6150941ed18542506bf60509419f99442506be6410941b798c42506dd6310941eb508425067e658c9419f596325067c658c941af99232506bd648c941d7d4e325075c538c941eb50a325067f654c9419f995325067c654c941af99132506bd644c941eb509325067e650c9419f594325067c650c941af99032506bd640c941dbd48325076c520c941f34c832507b742d0541ed50b41506bd6290541edd4641506bd60905419f98b505067d62d4141ded4250506ef6254141bb189505077950141419f988505067d6214141cfd08505073d4214141cf90450506de63d4841b758f52106fa60d4841be583521076f52948419f98e521067d63948419f982521067d6094841dbd4e521076e5394841f394e521074e5394841db192521076f6394841db98e521076d6394841db18e521076e6194841db186521076f6094841db982521076d6094841db182521075e53548419fd8d521067c63548419fd81521067c6054841dbd95521076f5354841db94d52107ce5354841d394d521076d5354841f354d521074d5354841db991521076f6354841db98d521076d6354841db18d521076e6154841db185521076c4154841dbd81521076e6054841db581521076c6054841b798c52106dd6314841d794c521075d5314841bb988521076d5214841be98052106f96014841cf953421075e53d0841d754f421076e52d0841db54b42106f661d0841bd587421067d6590841d794e421075d5390841db54a421067f6550841cf951421075e5350841d754d421076e5250841b798c42106dd6310
  | 24 => 0x420cb3e5450832cf551420cb6e52508329fd94420ca7e65108329f594420ca7c6510832cf950420cb3d5410832b798c420cadd6310832eb508420cb3e548c832cf552320cb6f548c832eb952320cb6d548c832eb552320cb2d548c832bb58e320cacd638c832db94e320cbce538c8329fd95320cb3e544c832cf551320caef654c832dbd95320ca6f654c832dbd51320cbae544c832db551320cbad544c832cb551320caef634c832db94d320cbce534c832f3d0d320cbce434c832f350d320cbcc434c832f3d95320cacf654c832d3d95320cbcf644c832f3991320cbcd644c832f3191320cbcf544c832d3d51320cbce544c832e3951320cbcd544c832d3551320cb8d544c832c3551320cbcc544c832f3d85320cbce614c832f3585320cbcc614c832f3d81320cbce604c832f3581320cbcc604c832af993510cabd64d4432cf953510cb3d54d4432f34cb510cb3e5494432cf552510cbcd3294432ddd46510ca7e64944329f592510ca7e60944329f582510cb3e5454432cf551510cbcd32544329fd91510ca7c6454432db8c9510cb6d3254432d34c9510ca7f60544329f181510cabe6414432af590510cb3e5414432cf550510cbcd3214432dd544510cafa6014432be580510cabe64d4032af593500cb3e54d4032cf553500cbcd32d4032cf952500cb3d5494032f34ca500cb7b50940329f992500ca7d6494032db8ca500cb6d3294032d34ca500ca7e61940329f586500cb3e5454032cf551500cbcd32540329fd91500ca7c64540329fd85500ca7c6154032af990500cabd6414032cf950500cb3d5414032f34c8500caf66114032bd584500cb795014032dbd4a52d067e6394b419f58e52d067e6094b419f58252d067f6354b419f18d52d067f6054b419f18152d06de6314b41b758c52d076d5214b41db94b42d076d52d0b41bd98742d06f561d0b41af58f42d073d53d0b41cf94b42d07ae52d0b41eb54b42d06be61d0b41ed98742d07b561d0b41af58342d06bf6550b41cfd9542d06bf6350b41cf54d42d07af6250b41ebd4942d073e5250b41eb14942d06bc6150b41afd8142d06de6310b41b758c42d076e5210b41db54842d07ad4210b41bd98442d06f56110b419fd9632d067e658cb419f59632d06be648cb41af59232d076e528cb41db54a32d07ad428cb419fd9532d067d654cb419f19532d06be644cb41af59132d076e524cb41db54932d07ad424cb419fd9432d067e650cb419f59432d06be640cb41af59032d07cd320cb41bb98b50d06ed62d4341ded4250d067e62943419f58a50d073f4294341cf50a50d067f62543419f18950d07795014341dbd4a529067e6394a419f58e529067e6094a419f582529067f6354a419f18d529067f6054a419f18152906de6314a41b758c529076d5214a41be98052906f96014a41d
  | 25 => 0xabe64d4232af593508cb7b50942329f992508ca7d6494232db90a508cb6d4294232d7cca508ca7e61942329f586508ca7f64542329f191508ca7f61542329f185508cb7950142329f987544ca7d61d51329f983544ca7d60d5132cfd52544cafa6095132be582544ca7e64951329f58a544cb6d62951329f986544ca7d61951329f982544cb7a60951329e982544ca7d6095132de582544ca796095132cfd91544ca7f6255132dbd89544ca7f61551329f185544ca7f60551329f181544ca7e6515132cf550544cb3e6415132db588544ca7e61151329f584544ca7e60151329f580544ca7e65d0932cfd53424cb3c54d0932b798f424cadd63d09329f996424caee6590932db996424caed6490932db952424cb6c5490932f3d8e424caee6390932f318e424cbce4390932bb586424caee60909329fd95424ca7d65509329f195424cb3f5450932cf151424cadf6350932b718d424cb6c65509329b195424cbaf6450932ebd51424cb6e5450932db151424cbac5450932cb151424cbcf6350932bb18d424cbcc6350932b318d424cbaf4350932f390d424cbad4350932f350d424cb8d4350932bbd85424caec60509329f994424cade6310932b758c424caee6210932eb508424cadf648c932b7592324cbcf528c932f390a324cbcd428c932b7586324cade608c9329f993514ca7d64d4532db90b514cb6d42d45329f983514ca7d60d4532ddd46514cabf6454532af191514cafb6054532be181514cabe6414532af590514cb755114532be980514caf960145329f990514cb3e64145328f990514ca7d6414532cf590514ca3d64145329f980514cb7a60145329e980514ca7d6014532de580514ca796014532af993504cabd64d41329f993504cb3e64d41328f993504ca7d64d4132cf593504ca3d64d41329f987504ca7d61d4132af992504cabd6494132ded42504cb7950141329f990504ca7d6414132db908504cb6d42141329f984504ca7d61141329f98b540cb6e62d50329f987540ca7d61d50329f983540ca7d60d50329f596540cb3f54950329f986540ca7d61950329f982540ca7d60950328f596540cb3e6295032cf18a540cb3f6195032cf986540cb3d6195032cf186540cb3f6095032cf982540cb3d6095032cf182540cb3f64550329fd85540ca7c61550329fd81540ca7c6055032cfd95540cb3e6255032cf189540cb3c3255032cfd85540cb3e6155032cf585540cb3c6155032cfd81540cb3e6055032cf581540cb3c6055032af990540cb3d54150329f990540cb3e64150328f990540ca7e6215032db988540ca6e62150329f984540ca7d61150329f980540ca7d60150329f992520ca7d64948329f597420cb3e54d0832cf553420ca7f65908329f596420cb3e5490832cf552420cade6390832b758e420cb6e52908329fd95
  | 26 => 0x3908429fd954210b5e5350842d754d4210abf6550842cfd954210a3f6550842e794d4210b3d5350842e754d4210b1d5350842afd894210b3e5250842bbd954210b6f65508429bd954210aef6450842ebd914210b6e5450842eb9514210bce5350842db54d4210bcd5350842d354d4210baf4350842eb90d4210bad4350842eb10d4210baf6550842abd954210b2f6550842ebd8d4210bae6350842eb58d4210bac6350842ebd4d4210bae5350842e394d4210bad5350842cb54d4210b8d5350842c354d4210bac5350842ebd854210bae6150842eb5854210bac6150842ebd814210bae6050842eb5814210bac6050842b798f5110add63d4442d794f5110b5d53d4442eb50b5110b5e5394442d754e5110bad4294442ddd465110a7e63944429f58e5110a7e60944429f5825110b5e5354442d754d5110bad42544429fd8d5110a7c6354442cfd095110b6e4254442cf5095110b6d4254442cb5095110a7f60544429f1815110ade6314442b758c5110b5e5314442d754c5110bad4214442dd5445110afa6014442be5805110ade63d4042b758f5010b5e53d4042d754f5010bad42d4042d794e5010b5d5394042eb50a5010b7b50940429f98e5010a7d6394042cfd0a5010b6e4294042cf50a5010b6d4294042cb50a5010a7e61940429f5865010b5e5354042d754d5010bad42540429fd8d5010a7c63540429fd855010a7c6154042b798c5010add6314042d794c5010b5d5314042eb5085010af66114042bd5845010b795014042be983548caf960d5232d758f548cb6e62d52329f987548ca7d61d52329f983548cb7a60d52329e983548ca7d60d5232de583548ca7960d5232cfd52548cb6e62952329f986548ca7d61952329f982548ca7d6095232cfd91548ca7f61552329f185548ca7f60552329f181548cb3d5415232cf990548cb5d6315232db988548ca7e61152329f584548ca7e60152329f580548cb3e54d0e32cf553438caee62d0e32bb58b438cb3e5450e32cf551438caef6250e32bb189438cb9d4310e32bb588438cb3f54d0a32cf153428cb3e5490a32cf552428cade6390a32b758e428caed6590a32db596428cb6e5490a32eb952428cbad5490a32db152428caee6390a32f398e428cbcd6390a32bb586428caee6090a32cfd51428cb3c5450a32bbd95428cb6f6550a32ebd91428cbaf5450a32db951428cb6c5450a32eb151428cb2c5450a32bb18d428cbaf4350a32eb50d428caef6150a32bb181428cb3e5410a32cf550428cade6310a32b758c428cbad4210a32bb597328cb6d65cca32bbd93328caed64cca32ddd46518ca7e64946329f592518ca7e60946329f582518ca7f64546329f191518cb6e4254632db509518cb5f32546329fd81518ca7c6054632af990518cabd6414632dd544518cafa6014632be580518c
  | 27 => 0x42b798f50d0add63d4342ded4250d0a7e63943429f58e50d0b3f43943429f98650d0a7d61943429fd8d50d0a7c63543429fd8550d0a7c6154342de54050d0afa60d4e42be5835390b5f5394e429f9865390a7d6194e429f9825390a7d6094e429fd855390a7c6154e429fd815390a7c6054e42d754c5390aee6290e42bb58a4390abd65d0a42cf5974290b3d53d0a42bb5974290b6d65d0a42bb58f4290aed61d0a42bb9834290b7751946429f98e5190a7d63946429f9825190a7d60946429fd8d5190a7c6354642cfd095190a7f60546429f1815190ade6314642b758c5190b755114642be9805190af96014642b798f5090add63d4242ded425090a7e63942429f58e5090b3f42942429f9865090a7d61942429fd8d5090a7c63542429fd855090a7c6154242de5405090a7e61d4d429f5875350a7e60d4d429f5835350b5f5394d42be9825350af96094d42d754c5350a7e6114d429f5845350a7e6014d429f5805350abe65d0d42cf9974350b3c53d0d42ebd8b4350abe62d0d42eb18b4350abd61d0d42af9834350abd6490d42d7d4e4350b5c5390d42bb98a4350aed6290d42bbd894350aec6250d42ebd894350abc6250d42eb1894350aac6250d42bb58f4250baf43d0942eb50f4250aed61d0942bb9834250abd6390942ebd4a4250abd6190942af9824250a7e63d45429f58f5150b3f43d4542cf50f5150a7e60d45429f5835150b775194542b7d8d5150adc6354542bed815150af86054542b798c5150add6314542dd5445150afa6014542be5805150a7e6314542d798c5150a5e63145429f58c5150b5d63145429758c5150a7e6014542de9805150a7a60145429f5805150b7960145429e5805150ade63d4142b758f5050a7e63d4142d798f5050a5e63d41429f58f5050b5d63d41429758f5050a7e61d41429f5875050ade6394142b758e5050b7b5094142de5405050a7e63141429f58c5050b3f4314142cf50c5050a7e61141429f5845050b5f5394c429f9865310a7d6194c429f9825310a7d6094c42d71925310b5e6294c42d718a5310b5f6194c42d79865310b5d6194c42d71865310b5f6094c42d79825310b5d6094c42d71825310a7f6154c429f1855310a7f6054c429f1815310b5f6554c42d79915310b5e6254c42d71895310b5c4254c42d7d855310b5e6154c42d75855310b5c6154c42d7d815310b5e6054c42d75815310b5c6054c42b798c5310b5d5314c42cf9534310b5e53d0c42d754f4310aee62d0c42bb58b4310a7d6590c42d754e4310a7f6550c42cf9514310b5e5350c42bb9884310aed6210c42d794f4210b5d53d0842e794f4210b3d53d0842e754f4210b1d53d0842af5924210b3e5490842d794e4210b5d5390842bb5924210aad6490842db9524210bae5490842f394e4210b6d5390842f354e4210b4d5
  | 28 => 0x1000c00000000020000000000000200040000000004000c00200000000010000000c00200000010000001001800400080000014002001000200000010008006000000000040000000000000000f00040010008000001c000003000000000000000000001400100000020008000000000200000020038002002000000040040000000000000300000010000003000000100000000000002000000000040000000000000400200080000010000001000400080020000000000c000000400000080000004001000000100040000000000000800000000010000000000c001001800000180090004001001800300040010004003000000100100000004000000000100000000000002000400500000000008003000c0000018001000000000080010000002000000000080030004000000000300080000000003000000a003800300000020004000000000000000050010000000000000000000014000000000000100000020007000c000001c0010004002000000e0000000000000000000000000000000000100080000000000000400700080000004004000000200000000004000000c00200080000018000000c00100100010014000000000300080040008000000000000000000000001000000300040010000000000c000000c0000000001000c0020000001000000000000000004001000000100140030004000000000200040000040000000800200080000004000000400100080000000000001c0000008000000000000080000000000000400b000c00000080020004000000000000000010000000000000300000030008000000800200040060014000000800200000000000006000000000080020010002000c00200040000000000000000300180000014001000400000000030000001000c001000c0080004001000400000000000000002001c0000000000000400300000000000003000000000080030000002000000200000010004001000000300000010000000000400200000040004000001000000000000004001000000000000020000000000000100040010000000001400000000000008001001400100140000008000000c00100000030014000000000600000000000001000000300000000000000001400500000000004006000400300000000014001000000100000000000001000400000000000018001001c00000080000000001be98353d0af960d4f42d7d4e53d0a7e6194f429f58653d0a7e6094f429f58253d0a7f6154f429f18553d0a7f6054f429f18153d0b5d5314f42bb98b43d0aed62d0f42af98b43d0bae62d0f42eb58b43d0b7751947429f98e51d0a7d63947429f98251d0a7d60947429fd8d51d0a7c6354742cfd0d51d0a7f60547429f18151d0ade6314742b758c51d0b755114742be98051d0af960147
  | 29 => 0x20001000000000100020000002002400800040020004001001000000000010004000000000c00140030000001000000000000010004006000400000040010000001000c00500040000000006000400300000000000001000c00100000020000000001000000000000000000002400000040010008000000400000080000000001001c004000c00000000000004001000000a00080000000002000000100000000000003000400000040000000000000c000000c0000004003000400100100010000000000c000000800200000000000000002c00500000000004000000c00300000030004000000c0030000000002c002003800600000000004004003000300000030004003001000100000000000000000000400000010008002000c0010000000000000e000c015000000000040030000001000400000080000008001000c003001800000180060000001000000000000020000000000000500000060010000000800000040000000005000c003000000100000000004003000400400080000004000000000000000000004001000c000000400000040000004002000000000080030000000000800000140080004000000000100040000008002000800100100010010000000000000040000004002002800000040000000000000400000000000000001000000000000040000000001400100040000000000000000000080040000001000c00000080030054002000c00000000000000000001c006000000100080000000000000400000000000000000001400000040000004002000c000000000200000000004000001000300000040000000000000000000000000003000000300080000000000000800000000000000000000400d00000010008000000000300000000024004000c00000000000000000000400a0000001000000600100020008001001000c0000005000000100000010028000000000000000040000000000000100000010000001000000500000020000000000400000180040000000000000000040030004000000c000000400000080030000000000000100000000004000000000100300010004003001400400040100014000001400000040000004000000000200080030000003000000500080020014000001c000000000000180000014000000c003000000400000070000000000800200000020004001000000000180000000000001c0000004004000000100000010008003000400000000070004001000000100040000004000000c000000000100000010000000000000100040000000002001800400280000008000000400a000400a00000000000003000800100000000000002000000300040040000000000400200000000000000000400d00080060004000000000000140020004001000400000040040000
  | 30 => 0x4000000200080030004008000000100080010000000000800000000000000000000000100040030000009001c000000800200000020004001000400000000090000000002000000000000004000000000000040000000000000400e00040010004000000000000080010000002001000100040020004004000400000000000004000000c002000000400040000000002001800000000070004004001c0030018002000000f0000000000c0010000000000000200000000010003000400100000000000008001000c0000002000c002000000000000000000002000000200040010004000000c0050004002000400000000000008003000c0000000002000400000000000000000001c000000400000040000008002000000000000000008000000c0050004002000000000040000000000000c00000000000000002001400400140010004000000400600080000008002000c00000040010004001000000000300010004000000400000000010000002000000600000040004004000c000000000000040040000001000400100000000000008000400000000040000001000800000000000010001000c005000400000040000020000002c00000040010008002000000000000020004002000800400000010000000000c009002c0000008000000c0000000005000000000000010000000000000100000020000004000400200000010000000000000000000010018000000000200180010008000000000100000020000001000000000180000000003000000000100000008002000c0000000000000c00000080010000003000000200080000000003001400000040000008000000800100000020008000000000300000000000000001400000140000004001000400000040010000001001400000000020000000000000000140060008007000000000000010000000000000000080020000000000000000000050000001001c004000400300000040000002000c000000800000000000004001001000000000000000001000c000001400000000030000001000000300000080000000000400200080000000004001000000140000008000001c0000008004000c0000000000000000500040000000001000000000000050000005000000100000000000005000000100000050000000000400000000000004008000800100040010004001001c000000c00a00000000008000000c0050000002000c0000000000004400100080000004000000000000000000000004000000300040020034002000400100000030000001000000000000020004000000c000000c00000000010008002000c0010004000000000000000000000005000c0000000001000000000200010018000000c006000c0030010002000c00000000000000001000c0000000000
  | 31 => 0xa00080020004003002000000000000004001000000000000000000001000c000000400000000000004000000000100040010000005000c001000c0000000001002800300000020010000000400100000000004001000000a00040010004000000800000000000018002000000200000000000002001400100000000008001000c00000000000004003000000000000020014002000000200000030000002000000000000020000000000000000040010000000000c00000040010008002000000100040000004000000000200080000008006000c0000008000000400000040000008000001000600000000030001000800100000000000003000000800000000004000000400000000030008006000000000080040000000000000300100020004000000000100000000004002001400100040030000002000c00100100010008000000000100000000000006000c000000000000000010010001001000000000040020000000c005000400100040030004001000800100080060000000000400000080000010000000800100040040000000000c000000000b000000200040070000000000800200040040000008000400200100000004000000c00000140000000004000000200100000000002000400000040010000001000000b00000000000000000c0000000000001c0010000000000000000000010000000000400100040050000007000c000000000200040000000000000c000001000100000010000000000000200000020000000000000900000000000000000c00300000000000008000000100000000018001000000000000010000000000000300080020018000001c00000040020004001000c004000400a000000200000000008000000c001000000000000050008001000000300000000000000000400100000030020000000000100040000000001000000500080050024000000c0000004004000400200140000000001000000200000010008000000000100340000004001000000c00040010010005000400300000020000000000000000080000004001000400a00000050008000000c0050008000000800e000000000080000000009000800000040060004000001000000000000004000000000000080020004000000000200000000000000000000000000030000003000000200000010000003000000000000000004001000000000000040000000000800000000010000001003000000040000000000000800400040000008000001800600000000000000000000e0004002000000000000030000001000000a00080000034003000c00700000010000000000c0010000001000800100000000034000000800200040020008001000400900080000000000000c00000000020000000000400200000010000000000
  | 32 => 0x206e0000000000094c242800000026e20000000b1980008308000415a0f2000000086b2eba18a400000000000000000000000056e24d092a000000000000000000a91000000000008cf9b39000064e000000000000003da8000000000039a800064e8000000000089017b5000000000029e0686d8a21fe1bcd000000025200000001e064818496780181883400004d7a41c00011ddb57165e13000000c05e150002b99700c0000000000000000000007427c580009a9c000000280a0000000909000000000000000000bce8000ba92be646e00009ca000000011c7158cea32908000000000000008fc99450f80000a8e000275800007b20000000000120e00000000000687ad22ee40000000000105d00000000002469372163c0000000bc3a36d1e9d10e00282bc00000005538000000000095b9040061a85800000002b60000819000000000000001a66000000000027cc000267f00000005ef8000000000000000000000000b7000000000000000000058c800000000000000c8800000000000000000000056c800000000000000000b1daa3c00000006104000000000018c0000000000000000000000000a70800045a1e0a4a2a2300000000000060643da814a6d80006811cd20002d6e0002f420000dd800015320000eac0000000000000000000009ad000000000003bf8000aac96b6000000032580006572f000d3400083740002bb400000000009756e850000000774000072711360000d0814a400000000005e05889000000000000000000a19b6c8000000000010b4000000400000100000000002000400100000000004000001400200000010000000000c000000800400000010000005000400100040020000004000000300000030000001000c00000040000004001000800c0000003000800000040000004000000000000000010000000000800200000000000000000000000080030000003002c000000000000000010000000000400a0000001000400400140000000002000400100000050000001000400300000000000002000000000300040010000001000300000000004005000400300000010000000000400000000020000003000c00e000400200000010000000000000100000000018000000800100040000000002000c000000c0040004000000c00000000000000005000400000000010004003000c0030004000000400000040000014004000000300000020014000001800100100030004002000000100080000004001000400300000000008000000c002000400000000000004006001c00400000000000001001c0020004002000000000240030000000000400100040000000006000c000000000000180000000000000c000000000600000000000001000000300000010000002000400000140000000000000400
  | 33 => 0x293244f06380002d9f0002d7a0000b3a0000000000000000024c200028dc0000d820001e2c6ea8000000174600021c6a08000000011ee1e4a1320000000000000000000009cfd8b900000000000000000000043507ba51280006662afe0000000139800000003b2318000000000003fa80000000000000212a00000000000000574450c00000000000000883aaf87fa062b37b000084a00000000c54000031024800006420000000226c0000000b7824661cd580300000008f794580ce881a0000000000000000000009679c660000f91000034a00000002b109c847080000002f0c69111766178000000035003f812a00017ef0000000000000000000000000000000000000000006d46c6200000000001724351c00000000000000000000000000014a300000000000000a82c0001bf000000000000000000000000000000000000000a3e5fb40000cbb0000b7eacac00000000008c100000000000000000000021212d9142a00000008d9800042fe7d84342af5000000000010e8004c6ae00024844ee15745d38514000000000000000000000000000000014af000110c87e4000aa8617e00000004068d0600000005f0aa725b1000015f800000000000000000000000000002e3530000000000000eac2a200000000c88000000000000000009be673e0001d5a6c9078c329a21c75500004901468000132c000249a218162e0b4e6c800009f000000000000da85e6c0000000000a4a0000000000000000000000000633800000000000000000000152c000000027080002718000000000000000004e2200e3ed537e9e4000000000000000000040800000025bd4e325ec3ed00000000000000000003a003a12e11f900014a6000000000017c61718000000000000000000900268000000000017900aa00006f6800000013ea000004900000000000000000000000000000002a5800000000000000643800000000001a300008515118000000000000000002cd00000b42000000012a47bf060c00000000000000b060000000000000000000009ff9cf400000000000000000000000000000000000000000000000002dc8dea7960140663e01a0002e64000012b0001fbe0002bed00000000d8400047627ac679d75aa8fddbaaad948876c1e7543d000065f1bdf1a5cdb6a244c5c00005f446185ae00000003e3668231ec00000027c4308119430680000001f2e65400000001402000000000000009640000000000000000005214000000000001840000000000143851227e8000000018e00022326e1089aa0e00008db80004142c98000000098a800000000000001e185e500007a900000000000000077a8ef00be0000000642400000000008b88000000000079c8000000000007d4000000000000026b2000000067c1d3200016f4000000000
  | 34 => 0xcda77768b9e463cc21267900d20000090e0001e56000000000000000000000000000012f564800025d61ac1b5d000000000008e58d4aca8000000084023400002bac9ff15ac0000641000000017b80004d9918a8e1879400000000000a8957ce5240000000b362158082c000000000000000009db80002ba2000a1040005e588ae00012e237f90710002024b28000031d800000014e60001bd900000000000000585a8220000000000000000000003f700000000000088400000000000000000000000000027e0000000099e50bc1f580000000000000038e5ec000000000006cc80006a1127800000000000230542124c0000000b48000000026a8000000078f085a00009ef000000003d8a7c0002738000210c2e5800000000001cfdb420000000000000000001ba00008f70000f4e00000000000000000000067e892400001c89080000135d2ca83ec0008cf0000000000000000009800000572202a000094a2ad9f64000000000014286ec8000aa580005fd8000140000000000000002a040000f4600000000002002567800092ca3c24cd45d2a7d40000000000000000000000000d7c0009220000000000089580008aa8e8862a9da2726000076a000057940000001e900000000133000000000008998000bcf00000000930adb00001ab1c04000000010240008dc80000002a08000000000000003a6063a58b29fb1920000659180200011c80310673322a61c9b800007c21b0c0001aaa0000a6f1782d4c000229c1f2c000000134a9e914162d390f200000007851cc89dbcbd300000000000000000000000000000001d340000000b69800000000009d58000906800094b80002bbce0400000000000000ae6c31141780006748a9000025ce00000006419d08000000000000000000000729800000025baa018000000000000000008a5000000000008bc800000000000001156287838c0c68000000210a0001b34000000077200000000000000000066e40000000000000000000016ea000003c75b242800000003b40000000000000000000000000a68af1c53e85529602139000000000000003bee24c00028a400020a0000000000000000000f9aa991e2f0000000000009483b80000001cce00000008c4c00000000000000000000000000000000001aed00000000001af400000000002d661f6000010700000000000140976c0000000000000010c80000b50b2e00000005ae00000000000000000000024d200000006d840000000000413c00000007dc97a400059680000000000000000000000003c18000ad8000042a8000304858000005b00000000000090800000001e9400000000009b7c95200000000001ee200000000000ca20000000635800000000000e70000a610a951ba00000000000000192d332996c0000000487df4a75280
  | 35 => 0x9b200000000001e160000000b9bc000000000025f2ef4375ca409d6e978000000000000000002e240002c5e00012b500024e800000003dec0003ff811600029a07f4000047322b2678805d10d0387000195371b82e883c0000680c0000002c7400000000001b520fd8000000000000000000002b380001a28000202e00000003c508123768a22430adcb00000000000dba000000000000000000000a591ac6b30800000000000000000000000000025a4190ce4d6c7e3caa74000098e517e0000000a5b000000000005ab0000984c00000002202c00000000000000000000000255000000000012363fd0000000000000000004b825e20001d585460000ba1ddd80000e18772a28400000006d19a2003300000000000000000009d818800000008208360000234a40f0000000000000013280002311000000030322a60000000a938000741800024e80005f003e4000010f52b28fa8411f980002c4100000000000b9900000006500791000000015940000001b2c00007cc0000000000000000027e8157ab5000000000002f640ae0015a24227647ea93016597de0000000000029aaf40c4200020b0aa65c5600029880000000000000000000001dd21da6c2c00096ec0009ad8000000000068e9bb4697400000017d42098000000000088d80000000ef90001dd11f9a6b9a74c00043594f298c40009bf97766818ee60000000bd58f0500000000000000716800000017a42c78b8c0d0800052480005c18000000000000014a10000000000206a00000001c20fbe70505710000eb000000002658000192c00079c28ac000000000026e80000000000040b23080000000000000000000000000000f420001a6a49912860fd0c1ea259f9a57f400000000004080000000000000000004468000b418000000000000000000002aea263c000aab195e0002e8a000246c97c8000000052f0000000000004b83680000000000000152a08d1fe400028500000ae9a1e00bcb3d17c800000008f821340fac000957834b000019e29685e512ac000ae4000003440007f7c0003b302030870f6614e96b06b4400000000000000000a36000071792e80000000000012000000000000000b0ec0000000ea2000000000000000001594978c00024a804589f0cfd000000000026d00000000822c000348974a2440000000140c000000000000000000000000258e00005f600005540001a62000000037902b300000000001722b3f25fd4c0800079dee08b4c0000175055c3f200007812baaad7d9d100000005648000000000000000005cd29d63f5800033f21430001438000000000005a800000009f180006ee8000000000000024ac000000000000000002d2a0000000000266452300c896314fc15e80000000f893dfc00000000000001e570cd1aa00fc016fa77113a3
  | 36 => 0x20f8000000000087ad99fa084000ac7c7360000be23c0800015baeda00000006d60000349a3413db8000000131c076d46256404bf000058200000000002f2e68d877579a887a99c80c984fc0000001e640001e84000000000000000fc8383ab780006492034880d36a00080006df516c20821853b58000000000099207a10000000000000000000000000000878000037ddb36747800028700000000000000000000000000000000b3c800000000000002d6c00000000e400000000000000000052f4000000000000000007698000000000000000002b6800081b1ee1000000000000000000000000187a12280004594000347800000000003b7000035089ea69f86a400000000000e8a0001f0a00000005eb06170000000292aa487cd9f100002866000000000000000001280000000000007500000f64000000000026444888c8d0002d22000074a000000072900000000000000000000002b0136400000000002d7132e000000070c8cba00002ca00000000001d72ad7a3a8000000006a800088018f800000000001a64022a46e000000000000009380000ac800000c28000a7900000000000b7b00000001aa40001bc662780000001a94b9f8000adf1c267c6000000000006cb80006af9dd20000000159c71e1e2c0000000000000000000020ebae828444c4d5c60000000000000074a80da00026de00000001e8000014d82240000000451aef80002ed0000000000000006e30000000067e14693d6567056ca3a27801c12e7a0000a0e00000000000000aaf80002fca2b400000001170000000000000000002e261d500022ba2ce00008c52c78a400d7c9df81da000000000000000002144000000000018860000000b6b80000001ffa7b000001790000000000000002c3872800000010cc771915e0000a5c0000fb30000d7e2af800056008e200000009bb80000b4a2860000fb296891be00000000002a07000000081119160001f940b8400000029c6a288000624493f45d03207a780000001eb0000000000000000002746a6e00003a700000000000000000000000000000000559800082b0000692800000000002b814344e50000386459414c4000584800000016de8e78c654c5ad320000000000000000000000000000000000000003e64552b6e0000000000000000008f000006a80000000b8101300000000000042e00000003dc80000000000000219200000000000db0000000000000000a09cd800000000000000000000000000000000000000059800000007ff000098b000000000000001bcc86f88aa20000000000bf6000000048c80000a1a3021c380000001f74000000000002257ba000000000000000827bcdc00000000000002a74000000064c90fe49aa0b20001359000000000017cd85acac60d7423800019d64ed00009798
  | 37 => 0xe347750000aa1000068fc00000000000002a134a126c417680000000000112800000018fa000000020a0000829000000000001c1800000000000001be60000f76475a4736f02d2e0000000000000000000000e600000000000a6aada028b93004c75b771b213d56109ba40d9c000baa00008592b240b880001d000009a400000000000210000071d00006ad2a92b62ad264f8abbe3e7dd229e3000000023da985c0000001b1a0e2058400000005ed0b1013cc39e00012f200017ed000130a000036690c400000029b20000000000000000000000000a74000000000000003e6ca6e0000000000126000000004f78000000257e6da00003d6800000000000000c6a00000000001b931466846626c45800000bd76b000093e0000418123a000007d1d7066498d89660000000845800000019721eb800040e28f200000001dc00004b2400000000000001336000211d6d3000061103c28cb2a3400005385502e798a9000007780000001c8a0000000000000000020c800023ba00003d239f188cad595160002a190000000000000000017800000000000000000004ed46880004d3cb241d30000000000000009260000000ba80000a8912be41f0000000131a09e000000000002eb8000320905b0000e5a4cd2a2855a92709118682000000000000000000000000000000021c900019170002a09000000000000001f0c000786572a00026ce00000000000cd6a4100002a3c00048a80000000ce20a92b1aba000000001e910b2400000007cd51900000002e718c3d5582f80060233ae667cd2bae41a0000000000000008110000000b581d9c3f18000000000056f08ec000262e9752e5e8d82ae601a800000000000000000000000000000007b900007fb0000029851c32a068866d0000190000000000000000000000000000011a083b28420000000000000001d80000000000000000000000000000000000175318d93194428a7e0000a84000000039b0ba80001ff200000007e3127600021c86cbdbd465e27746ac00002e38d2700006c21738b9854706b60994f87000074430d0000116800000014783cd00005812b08842d5d67911cae00000000000000af88ebe0000000000121ab0f06453f4400000000006a700003a680000364000000000000000000b7998c0000000000270c00000246cf800030e007cac747ee00000400000fe40000b6c000000000000000000000839c30b26500000000000b569d96000000000000000000000478ce401e38000a57890f97fdef36db800093b56a424680000001890000290a000000000000000eb0000000207c000000000000001aa800063600000000f446a316e00002eb03982b0fa5aa99e0000000b749740a438eec4f48000a2e87840000bca00021f8000000007ec0008e6000000000000000000
  | 38 => 0x17e97150000953800000025780000000000000000011ea0ef8b6a1668000000177099300002919f0e000000000014a20f14000000000083f000071712c41a880007be4000000000000000000001a9e000000000026b80002e7081589150001b744ac93d00001b5a58180001150000000068e0002b0c000000000000001770a44000032c20f0000b10c000768000014112905ce2748000000062480005da0293b6600c20000000000000013a285c00000000000000a2351580000223000000000000004c98000480800000029d803b591f0000ba3838968200000000000000000210200006b40001d9e4e78caf08d83f8a9a80000000000138800000027180efc0007a01398b05800000000000002e7dab68000972e826000123c740000000001be000000000000000000ce8197000038700000001f200000000000081e8c91f1a000270027b00004148000000020200000005fd00000000000000057c05b0305a670faf548800000015e200000006c580000002492458c000000240800000000000fe8752000000000008b300009e080000000bdc0000000b95077c31b93106620ff06d380000002f1d50c8000b2f80006b8542492b8000a1212ec00001fc0000eda6d980000ee26bb0000000a725f920002c7e51180004088000bb3909000000d400000005100000930000048ccb0f000182800000005b180008ad646a000000069daeae78248895a60cc2032856488e8d4c4dc80000bc9f68000216094180001e344f85fb29c00000aba0001918000083400016a2000000003840000002e2ab694000000000000015f49f91aba000217600009ba000000000000000201b06bcc27a0866a663218a9746960000874000030f0000000064c00008760002cd447dc000000224e1e00dd200000008f20942000096e00000000000000000000000000000000000aef2d74981d8c9746000000009a77ca000073400005ba29f79029f3c0000000000000000012d2af4800000000000002a3a4a5aa807428c510000c4b8cec00047000000000ab4607000000025aa19080003d8a71e00000000000bea8059fbf0001ecf000239c74080003490000000000000000000001cb65e1537a00019a700000000000000ae61f3d00013454c5c0009d68000a2ac2c6b080000000214232c9b023128df02d500cd96615f885728f83ab800025e0000a8b8000000000000000007e80bf00002bfc0000000ba200002a78abc00000000568c0400000002710000a65030495695640000000acc23263eb00004220000000000000000000000000000267400000005fac000000000091f0000000000024499f70002c02a8625b56efc000000000000021541ce8000442d0b90001d4c00000000000000000094676f80000001fea54d1dc400016ca93200000002c12000
  | 39 => 0xe800072400000001561000000000027080001c097bf1bde842000000000002da2148000167000008d844d24a200007c6000000008f800000000008e440000fb9b62000000000000000000000000069e0001ec600005e652d000061c0000000195862399262b48000266400084500000000000b4308b70000d50bc0985a83a459c73e12468662f400002cd26a88000701552000000004be220c94013fa0002dfe000000000000000000574000000028195095f60000000000000000008929aac0000000000000000022ca93980000000000a906792b270000000169009714be61b8000648000000000000001b1c00000e04c31327000000000000004768000a9eabc012000000001752514000047f40001440000000254c49dc0000001b81000019a4ada300ae300002cf6523703931e75a80000000000332000000016f0000012d09b80000001de4000000000011dc000000000007b800000000000000a58ab8e0000d740fe91aa13c00000002cee9c81fa50000000000000017640003c480000000000723000078a9b9a0f58000322c128a4988e806e0fb0086970a3e7547e3ac882e9919df300000000000000000128100024820000c8463480000002e780000000ada5ff0732a1b40002f4f8e000000000000b7d80000001d8e0000000000026000025fe0000000000000000004fa000000000012442b70000000000000000000bc000000000000000000ac400000000000000000091c8c300ab0af223dab6198ac09a37c400000000000000658518029668bc0007928c280002eb600000008034000a24a6c3afd9af0296000000021d438ba7ae000171f7c0c1d4a71000056d80008f71e12783274e07480000000000754a6ca725a7f40000970000056600001f600000000000dd0b972b5814180001d84000000078700000000da936c8c4ab2656bab820000000245000000023f0000000000000000001b4f0000000000000000001e40000a6800000002e08000000000000000000000000000036500000000000000000097aa6e800000000002208000637800000000000000000af500002cf800000002220001b6b000000000000008b700004f50000a1faf490000c9a2392eec0002e74a7a00000000000311d5ea00000000000000000000000000000000000000016700000000000000000000079a000000015a8087c452000000000000000002a940000e0f0000000000000013b80000002695181000b68200000001f7e0af45d7000022e0002976000122c97a8bf448503d475e955392f80004a0c0000001d7477a8187bbc9de567a254000000001d748d203600007d7800000000000000d300000bd68e680000f200000fb12cc00000005aca0c0000111600017bf97a2c7252a820e00000000000000000000000000000001072aee8000000000
  | 40 => 0x2a00000000000d559d8000015051140000000000000067980007f1000000001380000fde000000000009a0670000041600009daaf280000000a1a80008ed29580b01f1e000135ca7b8a16032c5df94080006668000000000000000000b700006190d033448778936800000014e88536a12224800093dd4a8422479a83381506250e249d416361fec000000000049e98101be110700000001a486ba0000000000000000000000bf80002be2597000000000000006deab4a9e60f6b0000000a7a85e8b11c000000000050500420000000255800000025cfa8400008ae0bd2000000075b8000000000000000000da1c072a680000000000000193ca6a01d819badff0e880005c7242f4fe00001d9a515bd82638441236215d800000021d939e00002d82330000000050f036309d000000000a2000103378e07160001e32221800000000000000000000000049fc5b60000dfa0000000000000000014773d2800000022743a5000000000000002430a2a2db893523a600002e000000002e1882a00000000002b040000000000000047c40000001b05000000040c2d2470f8ea60000000000000032ba4bc7538000000000021ba7f0000000061500007e0000000000000ae4000b0e800082b800000000003c2800000000000002a4007380a4000230853ed73c39c067c2588000000000088a0c4f0000000183000000000003840a5000020e000000000000000000000000029df9db099c00009440000000000000077b80840001ab600028c6524000000000000001f6c000000000028d230be6300000000000155287918337f5aae2635d3b005ade1734d400029b000000000000000f183fe1eb60770000475d61c00013cc960800000000000000000402ad40508800000000000000d363550000000000012982410001039000169e0002ebe0000e4c199823b000000067919120000000000000071a07988b6802a1b180000000000535a51c00000004e81fbc0000000000000000022520000000000232300000000000000000000056ac000000251bb9b40003d01a14000000000000000000000770a59a000000000009061928000a6f06f20001ada3731ad41ff80000002b6700000001c68a645c7800000018a4365800000016d8bcb2721b2e8000a5c43467058baa0000b1600000ff295065a000125400000008f9aca4acd80000001a7258680007c5c000000086f000000063225f6000000000000004b60000b6f12f6000000094c000000000000000eaa1b58e8e7ce174770024dc0000dd600010ca6cac00060b000036400000001fc6b4daa661af89801db8e6909840003ca000000000000000000000000064c0000730000072a8000000000000025b721a89a211a04ecab2adc21891fd27278f9763b8f7e0001305aa21c620000000000009e000000046
  | 41 => 0x1c30496000050127262630000052a337b13812600011705fa97181ba44a832194766f2400000000000000e09350107a00000001b6800000000004170000b0026344d80d601c0073e00000000001f9c00000000000dae77fc0000001f040002c92a50eb2f0cc00000000000855c00063f000000000000001b64a0e8000000214a00000007fb931b03e1f3f068e24655445f0a85800040500b4444aaf78d38000000199c0002a5f7bd00000000000000144e0001672234284c9fe800000000000000000533400000018821ed0000aa8e63e0002dde00000000000000000000049f497622d1bf00000000000000000000000f05b980000000000000000000000000586000074e0000000ac500003e784820001e8cb3300007a180000002ce0a21168e0000000a06000041b408800000000002e5800000000000000000000048d104899a000000000000000d0a00000006260516a22c5bf26d4ded329000000000000000000000000000000000000968018de1045f000000024ee0000000568a1a4268d9d70001c6c0000fc256190fc00029ac646d8367b8000000000000000000000169a000000000000008ad9a7c6c50430000000047b000000010ac8c143bb18b1e781b880009178964000000000016f64864b2ca7200d700000000c380005b400000bd0a3c00000000000000000000000021c404f007a00000000001bec0001eae000000000000007308000150ef2472b0000000000000000000000b7600017106d7800000000003eac0000000000807abe0317a91c1e40000593000000008566828154000000070728620000000a85d7e81a1a0b6a9ba1d66d9c00000005683e280000486bf21a70c5a370ddfe0000efab50800009415060002bce5082a220000bbaa7f0cf400008dc000228eb7d13b67de20d48e2865400000000002296b840ba0b8395602a6c8367da9d7802d574b2581de83978000000208851700000000000b8980b0068a3b08968000000237e00026bc000000043a80000000000bd619c44b3c00000000c795c8000ae5805637d4bc41a9c00087095d05d98000533800000024f200000009830000000000037280000000000200a3432788e220000ef400000000001bbe9590000538000000000000000000000194aa9400005cc400000000df00000000000000000000000017b13c067d416480002e00000000000001f9ac8279800000000000002dcc3ba94f60002776000000097b8000891000000000000001ed6b0c1ed000000000000000000000000000000000de049d00620000000000000000003d00000000a5c80000000000000294ea129d5e000218200000002730000000000000000000001a707239e310000dbe000101ead95abc1cd000000000000002692000160e0000000000000000000851b60000b1d4f9400023
  | 42 => 0x96e000000002565de80000000000ade20e500000008be000000004c40002d6859e8000000000000000000000000000000000011e00000000000000000007890000000000000078d8c1400011506ff0000000000000000003f4dafe08a00000000c482b3000000010dc00000009b000003f4a980000160c638800050b0e7a26d11de00000d2a9795da000000000018320000000ba99a3200000ce0000000000000042340000000000a7e67d200000000000000000000000000000050000000000000020be000000000000002bb00000001f7a9caad7c0000000000185f00010f0000000000000000000f99093da5e0e8000045e000085480000a7000020c800051b8f58b7700000001630b5886785cc88f81bb21a07948be79651e4c0002426627c00012200000000000000152400000000000000815000039228b60000000000000000000000002f3666faf4d00000000001412000096a9cf58b87c5245c0001c78383ab6600013ac1da1ce8000000094c800000000006cecf2288e400000000000000000000000000000000000000a8f400000000000000000000168c9f5d06b90f000029589ac02940000000ccc6e5a84050e854841180b957c800066740003c700000000000497934e9901db809480b80698997359000076c80005cb004a0000000000000000000de2808e0c27f282c4eb8caa00004f6bca800000004e40000000000060e02585db000000056f800012a86d20001ad8000084200000000f62abc000000000000009b1400041982ba96d800000000000000000000000096e40007c1c0000000000000000037840000f767c836a9bc46ea64de00000000000000000000045802880000000979d1e900000000000000a5000000000f700001f120000000000000000001b917c924a00000000000000000000000021e251ec000bd1cf0e000000001b00006930000a9080003041b655f7145a8cbca4e226176591000000048000000000000000000001ad0000000000000000001cba00000000000000000000059b000010500000000e0d34000008d84824000000080269100000000000000055b9de200000007771002a26c00000010ba00020aa00005080000000000174c8c300009c5414400002d138140006ba920a5e70df4000205e0000000325000000000000001e7100000000000000000000000000000002b2200000000000000000001e00019a40000000423000020b0000000121602b5b4b0000000000000000000004250158000203602b00000dc800000021ea31d00005a5a8020000000000000000000000c3d1db000271000018ca26ac0001dd80000000000000000054980002924000bce22d81e3c33e720986000000000001f2c00025a0000000030d846a00022f6012186a000000000006260000000a98899a00025920
  | 43 => 0x3144c80000000000000279400029547a28000000000000000000002aa467406ad0000e209388720000170e85d2c3f00000009bc800031900000002c5600000000000000000000087e80000000416000000000000000000d6e9849bd015a87565a700003f2c0007e7800038f17a66939b7f000000000000000002aee000031413600009278000000000000025a80002e9e0000d3e00009c06ae0a140002dd8000000000021b24574000000000099998fe595ad0200029380002e2cae71c2002608480059a2695b155f87b26ec8c6e62f8d70eba070cb92245c4209fe0492225147a6380df80000c7c00008d679b80002b4000040ec00000000002780000987c00000000000000000000000000000005c1dd9a00000000001cbc6de28000000000343836e00000007d0948400000002be4000a5800001e08cbe0001e2481d958c63c941000021220001a6c0001a381c0aad85f88d1077f6e5347f80000000000923289471c05c112f00005cc000000018f04c800000000000447000000000000000be60d5800000000000000000000000000000000000000000139a83e800078a00007879e4863010649a38000b3d800090b8d3c0000000000000019aa69a0000cfa00000006e5000000000000002ad0000000049d4000a034000000000000001650168ec40001b7e0ea21df00000000000f048619824000000027e00002cd0000000000000000000000b3200000000000000000000000000000002b642c82270728800021c846ebae000000c00a0113800000000000002e02000000027d233a0000000b2880009040fc094f190a9d297e00a387240000e126abaa9e688add000004fc0000000000292494650a20000000993800017740000000000000218a25d00003e8000000000000f6800013580000001ed48310dfc85c0000000000000000002ef80000e04000a02e7ba000000000000000000000a7680004a780004ae6288000000000011b600000001f780000000000a05800000000001f240006aca5140002b7aba6ad4e98400000000eb6000000000000000000000000150a00015c26dbd3321cc000001d26f407080005400000b2a8000000000000024b60002e730000000000000000000008ce45f83d5959800012951fa2eacb3680001da955087d57bc05a54085f48d024988b9e3bd80000002ac02f61c601a680ba0000000336800000000000000000000000053100005a18000000055a00000001b28000000000000000000000000142800000000002c080000000000000000000000006e72948000212e00009b800013500000f685570000437a0fe44b00007b7000000025ae00000000adc0008e88000000000000000000000000000000008d5e0141a8eff00021aa00009d20001f600001e82a7980003ba270f000000011e94f40000
  | 44 => 0xb269610000855ae761ecc0004ae990200000009d31d564a4c000000204824bcc26000235e0509e5002a000093c17442690000bc50000000000088500000002bb85568b2a000076c0001ef6b23259c4a09bb193e865000022d62e1c0005a48000406000085180000000e28000000000000000000000a530d1400000006a0c00013f8000000135600001560598000a3c117200016800000000000129717d400000000001fd800000014cf57b80000c2567800000000000000391800070b008289e8ad40001192000000022da5e5000000000000003df59c71b9df3a76d88510001668b9eddd673c26353cb2c9a000000000000005f58a82ad10e68295ec5b5b98a003df2310a8c000000000004e9a724000000000015d80002eee00004043132ebc000000016f218c000000009a8000000204200000008e2138000e14ee0000000000000000000007cec0003fb0000000000017280008fd12d00000f170002d3e36025f7000000000000008e90c4e000000079800000000000000000018640009dc4000000000000000000000c1c000000000007be000000000002c753600002bdc0002bd009fb87800000000000e2800070e80000000000486c00000000000001b853b600006a400009c580009e6984e8b0000038a8cc4000225300000009519bac23aa7be00000000000000000000071a800000000007a700000000a047f6000000000000002c5c5dfc000000000000015ca00020ba0719de0b3f800032f000000000000000086000000000000000002a210e1ac40af280007112e40ac1898e267c7a48a4000000000002e9c00000013440000000380105f000182673943df2d780000000000000000000000000000000000104221f285a113000000000002c72c1c0002242000046034a8000000000000028ca0b60000000150e151644a000000036313fd737a3aa0000000780800000000000000162000131200016d2000088a0000000000000000000000000000000000000000000000308000000000000000000000a3380006bac00008e49da00000000000b0c00000000000000001000000008a6000000000019380000000000031c000000000029820000000000091681a1dae1d79f720000000000000000012a40001390ab2000000000000002140bbe800085b000000000000000000bc482542bd80089710e0636884be000144400000001ea4000000095c8658a600000000000000040a400041f9235b310746000188a33c86a90001e5c20104b200000004b900003e59028a0d94ca0001181000000098dc000000000000006750000f781878c8eb7f247600017744568000000000087f25a60002e3e68f400000026947aa0000000000099bcfbc5d080005a5114e7f784c68e4a5608ee095a19800006b100004040000000000000027840000000
  | 45 => 0x9000000000025c04a740001ca871066c80000000000000000066b16c000008da68dc000a46977b00026870000000000000000000003eec00060f00009a580000002761aa18fe70002bb000024060000fb699b2f1682f00000002bf056eee3225380009d9c000bc80ccb9fc89540000000000000000029cb00002c445b8000000000066280000002ef300000000000000b5a8eb86368000000000091d11b400015f6000000092400000000e59028e9d7a895e2600000004a60000000091d00000008715c3c91e0000465837000007965a2ad64000219c8cd65dea6fac0e09f16660001124000000068696249b30000000049400000008b98000000192e5f92e6700025960000000000000068a800000000000001268a7740000000000b6a00000000000000017740dad34000000000000000002e891c500002cda01000013f40000000ac780b35d150dab5f802000026334f11fc0000000000021b6000000000028230e8438002b81a07f71af80001d1000000004f34000000120400000000000000000000000000007069a8a0002322b5e26f60000000000000020e00003bb83ce5af00000ef1e1a4cc0000b0a901c0be8850ba400004a399cf5d80000000064605a80000de80006e8800000014b819d0000413800000010c80000f3e000000008c800000000000001d2661980003bb400000007f02c280000000534075a3ac3facb1214a8000807121883d1f76321c93e27700000000000000000000000000000000000000000016084ea0000000000000029ca00023fe00000004c2005e00000009892aaa00022b000000004f2800000026764408cac0000000000000004f400000029cd00000000001fc2000000000000506e78000231000000019990000000704800000000000002ae8000115f17de29298860de76aaac612b000041d00006dc0d730000000000000074717ca8e10000000000002de178000000031c0136b08ac2c047ad4446c9a2b641134002d81a40002e560000bab000000000000000002a0c0000a0a95f2570000000041b80008ab2656000174800000c6000000098cad5633a85470040600000000000014825c8000017f2206ac4e402053a6b0b46000000000000000340000000019a11e7378a93ead300000000000000000000021e800020e60ad0000000000000012d63dd00002578000000000030e80000000000000000000000003719bb86fd1c940000000000155e0001a920000000425400049ca6980002b2800014bc00000009ce879e4ac21104eea1a900000000000000000000001a11660000000000000000000002c0c93c000281e5784000000153a0000000b5d80005970000000000000003adb1200008f0000068f800000000000732ee80c59e5eb2b8000000000000000001aac000000000000000000000249b0e
  | 46 => 0x74d0e8c00000000006fd8000a458000237800079511c600000000002ba40f18000ada8000371136800026530000000000000005ec00000021ce2f0067b42190320001adc00000000000000000291800016880002cf00002ce6521800091f80009a7800066a0000000000000000005270000ac280004ca400000000000001ef22bf80002ac000000029d5000260e0000000283000048b84220818000b91000026194e464fa2ec00000001340000000275f9728000000231d000000000000000001eda0000000989c0001142b320000000000182e0000000000000059d8000000000000000002ca0000000068b000293c78e8c5634340000000d49a01000000011d2000000000000008132c6ab939c08000000013680000000000000000082029f40001805000000088f80114dd84066031cf635a95ec0fa8000000000006d00000000dbb000116a24b0dacb7225d70002a9b0001f48000000000000000000f5e627000089800000002c7a000178e598aaae6c3814554c0cf021980000002ecc000000000029fa29ec00000000000000bd000000008f180000002791000124e0000000000000000000000000972000000000000009a3000000880000000440986c5893e000000000000000000000008e61378000000011c0bd8000000000000000001c2800000019ee00000000000bda0000000000085283cc0000000000000000033d4ab8743000000010e43e193ec00000003e04b937b3000000000000000000000000092bc0003cc87d438e1e4290f80000002902000230a00009914f39c5000000000001c460000000366043635e40a93d51cb800000000000000000016e0000000000000000020c68ec800000000000000000a2640000002599500000059400000001e300001f66000000000000000000000000000000000002a29afb0002d92a81aec67cc80000000000000000000007c192500000000000000000000000000000000000000000000000000000000000088880000000ba5aa04000014aab400000000000000000000000000000000c6800012ea8c82efe9b0ac1b00000007a6000034a1e9200014560935afc00004ae3b3af0600005260001de6000285e0000000000000000000000000000000165200025c85da80000000000000000000000000002e0c7f3c0007b614c60000e9000025f06ca00000002d501f206560002b3da3d800077a40002a204b4000000011229aeaa085400000000605800087d80000001f526a9800017f9728213ac2f00027ec1d2c000000000000000000002528b115b63b528000000000074c2e140000000000072ca878cfe6dc50df00000003e30000b858000000000000020df000000000028ae0000c80a928000a6d271c88680007690000510800000028bea260ac8126021e61f00000002e428b5124
  | 47 => 0x584000000000000000000000000000000000000000000032822802480000000000000000008f23708000000000049e400000001903ce87a20000000409ee92000000068610260001fd401eda6832c0000907a70d2e716e424e04c8000283400000006dcc00000000000000b7c000000000000007964df262d00000001572918ef500001887000000000000000000000000000000000009a12f4800007a63140000000000000000000002c080000685978155500000000002eca1978000000000000000002351f704c92a2d4c6002e536cbc64602952648a25073819b800000ab04900007f305567e180000000a8c0000000000000d00008bc0000000000000000000004cf2062000053241d800038587d0659a2d2a3d06f400020283bf07e4bd18000868c00046c000000016fe000176d0001f884d217fe0002ec400000000002f1000000000000000000000000015ad1f1691e3764000000000000000000000000b68e6cd93f09024f1a32e59828b224a40000000e26a4d9c0c0002e8c00004dc4638000b9a2b2c5290000000000000000003750000a41800000012006778000000000000025af80e18f4070000000000000001e6c0000e3e912127360800002b0800000001804e8800000025bcbd98195000000000000000000000000000010a1884000000000002669560000000000000000000000000284800000017b8000000000000000000000000000000000008b9000084808e30c94000b2c8fd80000000b8e000000000000991e5a3340036b71a9ec2300cc632d1bf8000000035180001c30000000024437e4000a48800000013079a4da0e000164a34054b60ac6b731d680008d30c7700000000001bae97e191d98f00002fe23ea02a800088902332e88000000000000012fc0001c427e0923800000000b069f20000000000000000000000002e9c00000000001f966130000000197ab29800000000005bb1a00000000000000000000000000000000000000000000000000000000006538000654800000000000000000000000093115a6000000042a0000b09085c000161e053596e8f917080001ccc8840d0bb469069000000000001c400000000000000420800000000000000000773800000000000000000bc100000000a2000000000000000000000000000006db2008000000071e800007640002a580000002f320002a900000000425800000004124502aa60001e3e22a133e17b183a58894b08d6a00495d0afa8cd949e95a14800002c4d52680006cb4c903088c16000000000000008fb80000e540005e1011d58a8000a2f19f2000000065225da9571d380000a4c879e770707ad08000231c29e8000b2380000000000a0c000000000003af000000000002b892035c0a09408dc4c264695de00000003a058000000000065000000
  | 48 => 0xb48648c29e99ec000092c00000007627ab00004d1800000000007a88fbd61021fd6a38fa70001c4a00008ca000000000016a865c266e3ee000011f8000af323169e0c00002751f46a68000000000000007330000000a61800000000007508d57a528000af70000635000074b110000019421fe97ccb6d0000000000092142bb7481504b1500002dc4000b849c407391a5c000000047f00000000000000000000000000001c2a84e8424000000000000008ed808e0cc8000000000000000003fba88a64dabea0000000a1f00000000000000000025427da93bc0001ec00000000000000000000006e4000000000010b69cd2c8018343fc4c39bd87f2000000021dc0000000000000092c00ea67300000000000000000000000000002262b8b845e000000018800335af94e244c000054b80000001cb41d4800000000000001783396000000013860580000b0fac8471399f40932a9a2758000000000000000003ff000000022c20000000000000000004b00af80000000000663400052500000000e61000000000000000000ace00000007870000000000000000000000e8600000006011fa400007cabd701ee02840000000000825800000000000000000162c00066d80006f22306675118205ca50911080000000000000000000000003f5400000000000000000000000083d9f2a79f80000000601916da243f51e6716aee7539897417a590ecaeec61c000000066404d27b8c98a8bd0f2588b8b620001d0e00023475cd8000000000098500003c81b3c000000000000009001d7c00000009ec0000000047c00000000000000000000000000000000000acc6c7c000197e000000000000006e38226000000079994720000000b678000000000000019ba9f706810002cb04b1a4610000d4e0000cec0000000264000000000008ce00007c9c00000001d07088d093db000042c897e6cdc00000000002e3c0001e8e6e905a00000000000af200008a28000000000000000000000000b2f1cc4976636a0b6800000000000000000000000057016cc000000000012990000000000150c99a800059601980000d8400013fe00000000000000b0127e24298a3e00000004e0800000005fd66c00000001dec14a012e3caa08e9e700000001e6f0000000000236765680007c305c8000000022d400020c104a0000000000220a0001f023f400000001e080000000ac24000000000000000000001bbd9f4270230a800000027990001ade000000015080006b39a980002d14000000077e00000001df200000000002b4295200002b9800000023ce0002e8b0002db081e822957900006f3adaf00000004530c49000000000000005150000000299200001ea00000000000000000000000000000002a5486f1ae800000001f3e3f600000000000000000149100000
  | 49 => 0x461000023b81b60001ffe3ea800000000002058ea1000000000000000000000000000000000007d300000000000000000000000007e3a23c357800000000000ff9bfe2030000438128c0000000000000000000000000000000000000021cc2f31c7cb60818486411f6000000039707da343010a0000ede3d800000001d806de496c6c28000843a1ba26111983d70000000065200000000000000a31c000a86aa5ca6c11e8000000042000000000b0e3f88bc20000000892000000000008ccc73d00000000000e4e9de800000000000002542971817a5a81d7e0000c0200021d80000ef748156c2993c000913debc824034e4ace25e426a50a0002f265c0225c9808c4d04ecee4691957053494f0000000000028154de265f00021db0000000000000000000000000fa20001b9518281790001bea0000000000000000000003e20000000000000000000000000b676b590001d123e4800000027ce8d8c0dc7090da400000001a500005e8ada2000203a1f48000a88c0005df800035e9bc29ee00580000000000160a9b6c0006f880009d5231e4f6204600000004d52d8c00000007df1ecdb1b8f820000a78000054e06bc0005fb8000b9a838400010c0422800000023d400007189e180000001c280001e8f76f29d9000000055180000000000000000098e94cc0000f4900000000000000000274200000000000b1800000000000000000205c00012ef974c000560800000008cc54683007abcdce7700000000000000016d4000245f0001e5f67a8000000000000980000000d0770d0000000000083c4000000000000021b00002dd4000000064a80000000000000000000000002778000502a4f40e684ca00001434710000af6800000000000002451000000000028b400015f0023c0006ea238258a246800000000002e0677aebde091eb210001b8a65d8000000000000000000000000371c000000000000000000000000000143694a8000000037c000000093291d00000000a2b5a5007ca26e0358000000000000000002a040006982b94183c0006c8c0003b08000a9f000000000000000cf39618000000040c8d400000e9e1ed000000000004640000a2c9a727cf18880000000ef800000000000a721f00000324c0000000e36000000018200003c6c00093b2cde18d23fc000005473aa7550000000877800000000001ec555400000000000000000014829e55fa04facc80001b4d000000000008a400015a439100009f7898200014da00005ff9655a0c5c5800094d16d600000000000ea85d7817657f1758000000008a80000000b44bb994528d19e6124d5190bad119e000196aa1d80000000000000000000000000000b94000000017781ae0000000000000071900000001778000000053e0000000000000000000000e08000157e57f836c0
  | 50 => 0x6593e45e6800000000000002c066c9800000000000001c1000024d6000000000000000002813000000000000009c4c0000de28a94a7000000000000d200000000000000000000023344b00a7f0000940951000000000002ec800000000000000000000238e0001d0467380000000000000011a0000000b0c9c019a1a8e32a015bf1204c5200002ea0001e0e17025dc34848f4000123e097800000000000000b46a80000000017a8634000036505d00002344000000000000002aaad2c000288e0000000000000000000009499542359a6fa5c68000000258864a0b0d0000000000027a1bf80009a98c06000000051aa4602b5800000000000000000000243a00000001e5c0000001502aca80001560000000000000000001b000000c8c00000011e2ae297927be2f52000000054faaf42f2000011dc0350000000ac0000000000000000000988000000026cf0000000000000000003cca3100000002bb4580075b0000000aa82a6184faa26000000000000000000000000000000000000000000bd38000000088c00000000000000000000061e0c7e5229b6a00264a6bb2249600000007ed80000000000000000029480000002a3e44b80000002e4a9176a465ae945e75d8000779c8730000000181c6f027500002e7580a0488456b20a1970e920187b3ab7e72fab9a000000087c2b83a870000b6680000000bbc62a00005b683c000018ae8ca000016412a8bd313c205f8aae16b400040180006f85cee3248814039a793222e1fe8b818720000000000000000006e0061400065d000000000005ed900e39d8000a04a9f62c200000000000523c0003a800002f34a240000000a83c0000001fa20000000b5521556e180002279896000000097e4000000288f00000006d6c0001ce4000b400000000270a16f8000677000000000008749df60001d44000000074b8000b27800021c64373c400000000000bd280000001e2ead1a5b000000000000ffa0000000000000000025040c560cd000024e0fa08c60000ed206cae3445299800342eaa2820000000000000000000000000000000051c00000002c4b00000009e3aafc0000bde00006eea8b0000000009c0002af60000000ac08777000000000027649c88000000000000017aa11d800000000007d024ea0001bcf00000006120000aa8840e4d928eaa7c00000000000000154c27b400000026dc7c70000000204a69e0000000000000000000000000922800000000000001396ad5400000022be1d518764a4400000000000000cf688d000000000000000a70b182b3a9e881f43e90000000133f000013200015e7af6009218c80002eb01750000c9c0000000a398c63000000081027304b089327c1a2c4000251e5d50000b800000788d7626d82d84000078636e40007f291d46b2a2ce0000
  | 51 => 0x8eb40002d3c88a800000000000000000000237600024770002b9e7b99eec0001e2200010258c62ded0001c3351312ac3678b8a6f80c2e00000002eec0004092227a0c836f522c000000000000027c00002b526f91d680000000000129a299933a05790ee0000000000000000000005f8c000000132a2038000000000000012c883e00000000000846a655000000000000003bbc000017c000a64000000000000000000000000000000faa2804ce4b7180e6c4800070b93fca5425e406dc000000004699dd0611210324000000095285130002dc440f80005eb9a162f74000a15abe400011f27e282427b6eb68ab5277c00000009a04000abc9f240ec251a000000042a4000000220856e800000001a82f5400004e8000000000045e8d9c0000000000000000000000002ee29cb0000000000000000000000000b50dad600000009b180000000000000000000000000000000555a9ef11ac000000293464428e0000000034744a048e4d13ae48bb01254000000032e1e54152000000092907c27d60a3899713220f788100000aac0bb0000a8ae51800014d07988000af10000000218ea25400000028b000000000002d0e43987e000000000000e4a58e80001542706000086c0000dde00000000000a1b00000000000c2411b0000bb480000002f2200000000000000b88000000000000000000291e11c72c1eb273e893400000002e5c000000066f00000000000bfc7fe15d4986800000000008d6176e00000006bd915b00000000001ea00cf0b84ba0e4ba23f628cb1b00000000000000000000000000002a0e000000080880000001f230928000000000026dd8a03a094dd77680002161874000278800000007d9e81b4a82092051a5cc00008be000048300000000000000000000000006ce0000000000156885ba3ec0000192916a9203a590ce00000009bac00000000005d70000ad6800000000000000000994a33d52380000000000000000024ba1304668000000000000024cc000219e000000000000009e280000000000655800090e00000000000000000000000000000be49b1ee840000000262000000019bc3668083000116461580000000000b131b1d000281a00000007aa9c84000000000000000000b3c000000000000007630cff000000000000000000000000041aa378000920000083a800067200001bd800000000006c8046926f820f931a7a8556400000000000631d3c00004930000000000000000022800002bf80000000000000000021aeb12800000026050f7207e92380000000fae000000000000000000000429014c966d9ec0000000000000000000000000000000000000002b50000000000000046310700002188000000000009ca00002700002418000000000000007b08000000000000000004f80000a8500000000000
  | 52 => 0x5c324aaa9fe562000000011cac10bbd430c9af80000000000000049018a8000b87000000004a20002b5c000000000000000001cb20002510b4e80004c50000000190c00012f46cc000000000000002020000000000000002d4000000000000000000a4a80000001d8472181704a880000000a30b578000a1b89a80000d2c90a920100000006c352209420c61ba880008dac0000000000000000000000000002dad00021246510111a658e1a0df861a0240dad82797c47ec00004111f300000000000000000000000000000000000000000007459edea2a8bb80000000647000091118621ca0000000000045200000000bd47bbac512d5826221c143e0000000948000070c400099614dc0000ce000000002bfc000a368000221000062b0000000000000000007cf80000002956000000000018e49a28000000048618f00000000000000000000000000000000000000000000006a200000001e7440b40000cd88e09a80000000000040b21a6bd788fe00000009b74000347c00000000000000f489b9c000000281948200007bc000091380009f988742a9216866100000000bfe0002c8a4ec800089cad706fea08c7b48dc0a321d3e31e8000369979e54f260a000061007bd6b400000000000000a04400005e1ad300020a682680000000d3400000000000000000000000022ea0000000129222c00006b2000000073c95cc0000000000000028c800000023944b78000000066256c09e4a0f080a58500008a88000ab0848e0000000b078000264800081e00000000000614276500000000000d780000000000000000000000001fda59f800000000000002e3a0002c1a6a0800060180000000000b789578000199b00004d460681e8818000000003ff000000000000000000000000075f0000a5e000017c011c6d40b3cb309da0000000000000000000000000000000000000000000000438800001c80009164000749000000000002cb4fba000266d0440f076dec00027d82c5352983800002fc000000000000002d628b8816a2f0afea80c000000015fe6289d0000000021b81c4934200f8c58668237abc619f992e000000000002c680000000c95a56973a000000000000009140e9e0000000000000035d800000000000000000ae18fcc859ee620000000000000076422de00000002bc136e9192c962840000000000000009b0954800078d0000000000000000006f6c000000000000000000000000000000018440004fc0000a3500003d48000aa2aafa8ef8000573a1dd2db80000fa626a000000c927069587ec00011c00000000000701862886884550684000000000000000b2735800000020a80001cdc6f1d54400000009b59331006a5567ee244296feace07c00009864000a0411268a78a3a651a0e8738977c000000019e6c4279b535a6f2
  | 53 => 0x8b80706b701cc475800013ee8950000839163e1a2800000009fe6fa00000000000000000024dd2124bc000086100000000000bb5000000000000000000000000000000000a500007eb0000000000000000002d4adce00000001009df100000000002bec000267d000018a232296600020980000000b7c8000000000000000000000e7e687000059000000000000000000000000000002d1000011ca4ef826c000000000000003f840000000000000147c48342b600000000000f162ed0d6c81c85602699e0f6dd8000000000007ce76667f2b1c84e00001b30f0c000121ea0705150000cd2ba08e145ff000000000006dc800024a2650bb0000000024750002b348da000000004b60d7800000000009030000000000067280000000000a8085a21708000b2200009d71d1421e00007778d6800006a0828800000014ae000188800002ce00000003278000000000000000000000000a7300008f1000000000000000000000267e0000d6b0002e6e00000000001b9200001fa00005516b80326976208a000000068f19a50002d28000277800000000001f5c0000788bb700004f20c72ace63d000000000000000000000000002a00000e840b5800085e80000000000000108400000006a180000002d880000900535c00000021f4af5a908436256604500000c34bec000000039c80005098000b51849e0002149000000000026600000000000000015e00000000000186000000002901a9996886a00006da43211b9a92e5c98000aea000089e06120d10e920000000629800028626ae00025030000e1e42d14a057a00005451a9600000000000000000000000000000000000a2212da000040000000002a98000bcf966e3958000afbc0009c441ac0000000586000060aabfe0001ceca38800083300000000a6a000000099ea43900000000000d7080519415b72c5891500000000000ac48000b050000a8c400000000008d590fab00c00000025b1501ae8600000001759e950a1000057989a10000000000000000000000002dee000000003d0a5d0000000000000000000004af22683fc800000018be0000000bbf000071c800000015d28bf8000000000000000000000000000000000000003e380000000000000212d0000000000138e0002a207a20000000000000028558e168d6ab3221864be4320230000879800042ba87461618c600000000001f4600000006e207e23280517945800062640000000000000250ca50454f41940003fd8000355a02c000275914792e628a9f6b0f3400000010b0000000000a01080002a33000000067180000000000458800000000006bc40005dc8fca44e00006fc804e11e0000ae9800095aaa4c00000001ba800078940000001a1206c1cd4b6f86130000ba1000000000000000001b48addaa700000000b86800
  | 54 => 0x2178000ba507ea0000000a30825a9db4ce40000000000000000013f6311800000000006d425122fb800000000008cca5d100029f84c123d85d41c9a35680000001c580000000647800000000000000000b2b0000000000026d9a8000021c01488000000157c0000d187008000000100c17e80000002e3c000203e0002cdc000127e01ba88c09c8998000000000000000001b80000139c000000000000009856cea0002de66948c088a680000000000000253600000000000000b7c053c5a980003188000000000000023483350285000000000004eb000000000000000000c4400011f83bd60260000000a0b8000000000029d80001af2bb6000217cab900003198000000000000000000000000000000097e80000000000000046200000000000000000000000000000000000000000000000000000000000000000000700000c7d310299a00017ce0000000000063e00003aa00000000002cec00000000c6000000000000000000a7fa65e00000000000d9f000000045100000001b3d00000001a400000001b130c4ca6917105b441b000036e00003c900000000000041800000000000001f5a00000000002854000091e6f5800042cc00000000000000000000000000008a21c14000000000000012660000dfb000000000000008fe05733d404719be0000b4e000068a66eaa1e8000aae126c00000000e4d751126c0000000fc400000000000000000000000021060000000000000026b40003f243e00000000000000000000004e480007f82d046638000000000000000000000000000000000020ef604a6aa2aa000000013fb8af00000000000b9801550000000974800038c800000000000000000000088800000000000000000280e00024572ef40000f94000af197daaa389bc30b2626697c0000002e0aa1c929b8de0000000000000006990000000000000000000004dd000047c00000000000a075a27000000000000000000000a3400001ff00000002ce4000059700025fb0000000736967c2a180000000000000061400000006b4800088794987ec800055d9f4ebac8ba9160448597f01821fb0000000268500000000000e0a3f81992a1b0fda000000000000002bf002faa61eeaa13800000000000002817693c000793800000017a0000105400000000001b22000000000000006bb0df645fc00081c000040dc000000289300000006ce2882000000052c987e000043a0000000000022c00016840000000000000000000000001f5600000007d400000000000000000000000000002f4400000000fd400000000000000000000000000000000c48000000244c8db0000a76c63300026258b4000000000004cf527b19c8c0e300126e418aa2a51d0de6000178226a509c816048c000209ca50ad7200022a059a8000762157a76d028c00
  | 55 => 0xca82819dd40005c10000380800000000000000000000000049f281f00009ee00000000000000000000056a6dab03bcc6b7e86f543560d482410aeb4d4ae98835a2aea1a0e2f47ace153e120523c0ca48b670000000000000000009ec800000012249e9aa7e00000000001108bd2c0007fd298e0001f0077f25f46f71efa5991ee500005a40000000758a50e568122822b00000000000a3b8000000066c7db8218211a2933572ef67b283641269ec40000204000215a33013c0b3180005e28000506804c000242baa300008e58000000000000000009d8a678158ae520002e1800020ca110c0001ea80000002364000081c000000000013f2b06058a10f800066a8000000000000380008ba00000c18000870c0000001929b9dc0000001008889907832d812c000264a60780005bc97884248fc53b52cb46c200004c0e2050000f38000000039d26a20000000000000000000009d48000000250b00000000000000a0200000565142585c0001b4689e00000000002c31996a9ce0000a28000002c0002c70bb08394000067a00000000000000000000000000000000000000000027600000000000364aaba426000000026f0b09800000000006618000000000000011ae46a0000108c000000000000000003a9204e00000000000000000000010600005b880000000ee20001a5a1b7842fa5f27d600017432238aea0000000000000088e000000025c2000000093d9a2d169ad480002b4300000000000000000000000025228360000000028000000000001d98000000076288fa000000000006715378aa00000a36a0fc0000000000000000011ce9a414906dc127614c000000003b9b040ab8c5b00000000000000b2d8ec0aaa0f081c883e23062e300000000000000035480003265a6e00017b300000000002a01000000000005ea000000094e800000000000000000b358000000231a0002bc214f80000002e8e000000000003ae00000000000000000000000000005b38000039000000016ae080021271305d808ac52000000001106cf84f4c00011340000001d3a0000d88000000000000002d0043c2de93dc162000089fa3e8b142a563770f1521904ea7062c2e33dc00000017ba0002cb80000000000151233e0000000000000000000000ae40001ba654a0000620067f32751bc0000000ac38000ad3a18100000000d70000916056d000000000000000002d94b3a22120000000bc68e640000000121c0000000670a4e958a000298c000000000018b22edc00000000000000000000200c7c88fe60000000376da42ae22704339800005910be00000008be9c3600026d86a7567400002e667d63d600000000001e2000000000afc0000000af1ab81ca800000000000000a9e2cc00000000b72800000000000000000af64000681400041bc00000000
  | 56 => 0xb4a0001d660001588000001c51b1d5c00000008bb8000000062514b00000000000000000000000000001f2662ea5547eb800000000000000000000261d0000000000000000000000000d44b8d80000000000000047487c800000001ed68080000001004057000000012100170000400000000000000000000000000000000009ef00000000000a5a2255a0a9e9a35c80002ed800000015d326941e021287ac48c0000a200000572c0005638000a5c00000e480000000d863de800000008b072209222a4d8c2000060204000000000000000000000026540000467047da5600000009628408000000000000000001c80441800040e800011980000460000b6e80000000000448028a000286468d449c5d240000000000000021600000000000f98b9f0000000000000000000dd0000178800080c2e222f3aad20000000000021400000000002680702a9d200027c200014c30000f4cadcad1c000000050c00005b22de400000f2000112221f93e80ac8371043a9fd63a0a94ad5c00000019272fa211e5f997f06ef1ac2ac600000000000000000067e0000990986c000000000000000e161315f96a68000125ab930000000000074a0000000000000000000000000000000007c40000001b87000000000000006148066a57000036f000008307c400029125e60d3a84626881fd0684000163840d0fe50000000000000000002cd631055300000006d10000718d1a6000156c1680000b2527ee0b322202868772000000085a6adc5f40000000000000000000be00007ac5a74b0f554a62c000000000008b2057000018eab7580009b9000000000000001af9a18000057112138f31ebe24d8000a5f80000000eca94b261800013aa72800000000000b69000000027b40002a600000d2e0f9c67724e6453a5cdf543411b90112d59a6c00d16b028000000000000000000002ce2000000000000007aea13c0001eb4000287071495dc0f0c00f00011e6000000084b2c5a64640009ab12fe000059904483079bf0c0a000000066580009c4ac5274680000000000000000600000000001d92000000000018b1363800000000003e7207400000001a0c00083700000001f84000025824240002a89a7a2e9800052e800020899fe6d72df89f2a43493c5a31a3f8ef05f9e2a8b7a08060ed800000000000000000000000001107b6413125298200009c68b9a4e2a7360000000000000000000009cc869638b00001cc800000000000000000000000052580000ef4000000000000000000000000000125c19116420002dea0000000000000000000000000000454800091583f710940001a26c0c0000000000000000000000000e541079ac00a368248d099d80b40b5a798c000000210d73f0a2600000000000bfa000000000000000000e2d00000006
  | 57 => 0xb90477ec3400019a2a8c81e68049562000000008f00005e2c0000000064000000000000000002d90000137c00018080000000792c0008d7e47a8212d8e1e2800000000000000000b9a40000002b2d0000000423aed65881a2c0002d522a7000000000340001c486450000490800077e80c00002ad6ac363d29c511e47398ec80000000000000000000004bb8d32000000000000000002b402b7800000004100000000000000019d84ef00023a016ea8860000844000105a000000000018460000c5900000000000000000000000010c40f551ac00000000002e969734000b11091b0001fce000000085380000000000064c0000002d58000000000000000002ba200000003370b78000267007e00004958764b2240002061288b76a72e326000000003036d580000001e9437a0000000135834703c9a3b1d9416b09582431a340000000ac5800000000007d8840a4e11c38000000012e80000000000000000000025b236d1d600000000000000000027720000000684062e00000000e98000ae1584b18b5afa000000042e00000000000000000000004f4000000003f000000000000002c8600000000002a5a0d500001ce18221ae283e31e16f86ec00003cb810c9d10000000000000026e60001d361415b217e4000000000000002414000000000000000000fa89d794d4000000000000005bea4fe000000027a03cb00015103b183c7871e6650002a38000279e0000000189c3ca79f000079d82aa6fb94fe0002a9c0000e0b00022fc00000009390000b92000000000007ea99ae0000e3a0002cca0001d700002ed8b6000001b40c7f0000000ad0470b37b80000000000000000070550a00001294000000000c80000000ee0bb785550000000000000000000000000000000000000000000000000000289a6b9000010e09ae494171404040003156538600477e5fc9a540b080000000000acf000067800000000000000000000000000000000000011b44a80000002f1e00000005611a48000000000000000000000000000000007ab0001aa80000000337800000009d00bb80000d8800000021e9000000071f80000002112185a7965808000655000000014660001d8696cc00000021230000000000000000012a65918000ae123250000000000000000005aa00000006e099629a9431e0000000b2425b4000000000000007f980000388737abb1cc667ec00000029e215bce301730000000115c75187f200000000000000b192b3326aa9de4f453da00000002150000592400000000000d6a0d2000000009f8000000000000000000002f6219340000000e42000000084bc0000000000000000000006806c780009b52377882400000006c40670be5000000000000000001d501cf19946ed8000a0b40000000000b478000000000000000000000
  | 58 => 0x80000000000000000000023545c1400000015aaa752d0aae024620000000220189aacb80002a60af3000000014600000000000a62af348eb8da0000063d880800000000003232cfa000042b000013482d000047540000000aee6768000000000010aa298a94a8e4336000069026d20000000aac000000000002130cce53a80006494000773175685988ba00000000001e2b4cdd8cc000000000000008e3000000019430001188b1a25ac00000009858c32000172e99f1fba3b0d016000000054d8b2200000000000000327c00000001ec0000b88000028b000000000000002461a30000054c000000077c00000d613cf0001c920000000054c00000000000001cfe40bc000000083a000000000000005c48000000000000003b440b8000000000092d000000023702ac8000000000000000000000f900000000000000000000000000000000000000026ada74660485880006db6b3e65300004aba03c0002e5a00023155e1aa27933844562d8e50000000000018140c080004ef000000000000002dfa0000000163007811127f68b180000000000526c0007fd9e8ea9d80000000f3c000000000000000000000000000000000000001b18b45800000000000002b74000262d3c8c0007ae2374b9400000000298101642d9360f1e00002080001b3a399abf47f8800000012484b524045bb80000000000000213600003a545840001b5d3e66c418300002b5446900000000000000000035b6dac0000b4c4e9292c000000081400000000000000000000000000000000000000000000000000000851c0000eea6da00003c400010817d105b200000000b20000000034c055c000000000071d80004278000000000063b572f00020b863d99001c9a9a6000165400000002c14000980edb600028280000000b9b2be80002cce1cb8f1a539eb624b39fa827c8000b6aa15e6d514c80000000a6600000000000000000051211ce0000000000070d000000000000000001548acdc000354c0000000000988a0328f88205000052e13800000001306000000000012b4521c54a86001ca7609479000059e00000000001362b61876066098bc0000000000089cacfcd62000089600000008650000000199e00000001cedaee00017f800000006b30000000000000010e109180000000544000000006240005ebc0005658000000000084acc3e00000000000000000000044400000002ee000021295f0649800000005d900008a0800094f80006df189d7bf95b4000000000004f200000000001ae65704fa60000000467260600029f3000237c0002a0ab6a4000000252d000102a5fe9ec839b99600e5a9cf547984a0002d9600000000000f002e90741084182300009ce95d81042d99b4a000183ea3f0000000216a0002258904a94600026ba0000000476665d00014c2
  | 59 => 0x13c40004dc01e2487164e00022160a4842c000000006b40005fc67bb0000000b4480006bcabee0f5cac01ef27b600019c248980006b8800000006910000f190061ea603b0b700002eea63705b8000000021a000000000002c50000483176b5780000639af085ecac280001e7a81980000001bab000000000000000b7c00053b23a390b000024728520000fce9806bb20000000000289c0000aca000000000000000000000000000015840000000000a5b879c85c8e8007f9a690000000000000000000000000000000000000000006d00b7461a2a6c346832a506000000002e4000193495414c1503a3f2000008d0002ac40000215a8d80000ce000000024220001df406f08b2447800044f8000000183490d800000000004ce000000000000000447141c808000000000028cc08358d94348000000000011180005aa858e000000000000000000000000071cabc0426687899e1a623900000000a51000036280000000f260a980004ae000028d05720000000000141c0dd863fa452ef034f600a01944c190599a6000000000000001f3ae7200000006f480009878ecf00000000000000b9180009e940001be80f09eaa4702c100001b6400000026625cf800000016fc6e80afd0001d400000000000134c00000000000000000275740480000000000000220432e0000149c000bd6800000012110000a91000297a000122d000000061725d033b81740000a620000000000153800000009cf192c1ea257a9fa80000000000082a150000000000028c0000212700000000000d380000000000000000000000000000a29a90c4bea30e00000004319d642a4a08692180008cc4000000000019f40005078000000000091480007e98ef20000000a8a4000000000063b000051d400000000000000000b11853090380008fe931f4a4a9ffb8a0000000000050b88904aa8000000178c43dc283000000000000008018e8cb0d800039480000000b950e08000000000044a000000000006454db20000000000000000000001d20000000000000000006cc670e0000c6c15180007bdc000589a1ee00000005910000000000096f8000000068f0000000b51440767da6a400018cf000000083e6f0a00024a0000000000000000000000000000058d00008990000000035208e
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x863a54580210431caa2c0108219694d6008410cb2a6b00420866a525802104334a92c0108211b9ca64940108dae5324a00843e7498a500421eba4c528021179ce62940108bae7314a00843f74586500421e3a2c3280211bdc961940108d8e4b0ca00862e5498b4004316aa4c5a00218b95162d0010c5aa8b16800846f7694b4004236bb4a5a00219398e52d0010c9ac7296800846f7654b4004236bb2a5a00219398d52d0010c9ac6a968008635545864004237394ca200211b5ca65100108dce4328800846d721944004332a94c2200218d9516110010ccaa4b08800843f76953200421ebb4a9900210fdd954c801087aecaa6400861e5498f200430eaa4c7900218795163c8010c3aa8b1e400845f7694f200422ebb4a7900218799253c8010c3ac929e400845f7654f200422ebb2a7900218799153c8010c3ac8a9e400862e6494b2004316b24a5900219398e52c8010c9ac7296400862e6454b2004316b22a5900219398d52c8010c9ac6a96400866552586200421f3a4ca100210f5d265080108bce7328400845d73994200421f3a0ca100210f5d065080108bce6328400845d73194200431aaa4c2100219554e6108010c6aa8b084008655535842004333292c210021c955152c4010e8aa6a96200847576946100423cbb6a9080215a5cb5484010c72cb2a4200863965552100423cbb6a5080214e5d35284010ab2e7a9420086696594a1004394aa4a5080219a5955284010e54a8a9420087295454a10043a529aa508021d254d52840108f2ed28c200843e76951100421e3b4a8880210f9d95444010878ecaa2200862e54d891004316aa6c4880218b9506244010c5aa8312200846e7694910042363b4a4880218bd925244010c58c9292200864f63949100432631ca4880211b9d952440108d8eca92200862f645491004316322a48802193d8d5244010c98c6a92200863774d95100431a3a6ca8802199dcb6544010cc8e5b2a200863765d91100431bb28c8880218dd965444010c6ecaaa2200866765d891004333b28c48802199d965244010ccecaa9220087255454910043a2a9aa4880218edd36544010c70e9b2a200866b72d951004334396ca880218ed976444010c76ca322200847a76d5110042b4b96a8880214e5d65444010c76cb2a2200863b65551100429d3b2a8880214e1d95444010cd6cbb12200872954d891004335b28c488021aa1906244010e52a831220086c863189100423d3b6a4880214e5d35244010ab2e7a922008569759491004335b2ca488021ca5525244010cd6caa92200872a545491004394aa2a488021d294d5244010e92a6a92200856a7654910042b43b2a488021cad915244010e50c8a92200874b6354910043a431aa4880218e5536144010cd2a5b0a200873154d8510043b0a96c2880211e9da5144010
  | 1 => 0x420422eb9ccb21021179cc65908108bae632c840847a70196420422f39ccaa1021175ce65508108bce632a840845d73195420423d380caa10214b1c95450810a58e8a92840847975d81420431caa6c0a10219654f6050810cd2a5b02840847975181420431caa0c0a10219654c6050810cd2a4302840845e73d94420422eb9eca21021179ce65108108bae7328840845e73194420422eb98ca210211d9c465108108f4e0328840852d72950420422ebacc621021879526310810c3aa9318840845f7558c420430f2a2c6210218755163108108beed298840845d7694c420422fbb2a621021175d95310810a5ae9290840864e639484204326b1ca4210219398d5210810c9ac6a90840852f755084204296baa84210218bd954210810c5acaa10840868d63508420438729a8421021c354d421081087ce932c640843d74996320421f3a0cb190210f5d0658c8108f4e032c640843e74995320421eba4ca990210f9d0654c81087ae832a640847a7019532042a639aa4990211e5d7604c810c72a9b02640866952d81320423cba8c0990218e550604c810cd2a4302640843e74d94320421eba6ca190210f9d2650c81087ae9328640843e74194320421eba0ca190211d9c4650c8108f4e0328640843d75990320421fbaac8190210fdda540c81087aed2a0640843f76550320421ebb2a8190218b992520c810c5ac9290640854d739483204317322a4190218b591520c810a9eea990640854d754c83204327b2a641902193595320c810d1ac8990640870e544c83204386aa264190218e5526090410cd2a5304820847b75582410431caa2c1208219a54960904108dce5b28820846d72d94410423cb82ca208211b5d66210410c5ca9310820862d549884104237baac4208218b9516210410c5aa8b10820846f769484104236bb4a4208219398e5210410c9ac7290820846f765484104236bb2a4208219398d5210410c9ac6a908208639549804104335294c0208219a54a6010410c74a8b008208639545804104335292c0208219a5496010410c72a93044208659539822104334a94c1108211edd56088410c72a8b044208659535822104334a92c1108210f9d3650841087ae9b28420845e73d94210422eb9eca108211e5c1650841087aeb320420843f75590210421fbb4a8108210f5da540841087eecaa0420843d76550210422ebacc610821879526308410c3aa9318420845f7558c210430f2a2c6108218755163084108beed298420845d7694c210430f324a6108218759253084108beeca98420845d7654c210430f322a610821875915308410c5cc9290420862d64948210432731ca4108219358e5208410c5cc8a90420862d64548210432731aa4108219358d5208410c74a9300420863954980210432d29cc0108219654e6008410cd2a530042
  | 2 => 0xa690221961945348110e30a829a408866865d89204433432ea4902211e9d85248110cd0ca29240887285414920443a4298a4902212e5d061481109b2e630a40886e36218520442753b642902219a1972148110cd0ca90a40886e0614852044334294c0102215a1d52008110e50a890040887485348020443942a0a588221d214c52c4110c9cc7316a80864e6358b5404326b1ac5aa0219a58a60d5010a5ce5aa4a80852d72d52540428f398c52a021475cc6295010c5ac4314a80852e721865404296b90c32a0214b9cb6455010a5ae5b22a80845e73189540422eb98c4aa0211b9cb60550108dae5b02a80853870589540428f398c4aa021475cc6255010c5ac4312a80852e721855404296b90c2aa0210fdd95415010c5aa9310a80862d545885404317324c42a0219398e6215010c5cc8b10a80864e635885404326b1ac42a0219958a6115010cd4c5300a80866962980540430f2a4c7a90218755263d4810c3ca8b1ea40861d5458f520430f324c7a90218759263d4810c3cc8b1ea40861d6458f520431cb24c1a90219658e60d4810a5ce9a94a40852d74d4a52042a739ea529021535cf5294810a9ce7aa4a40854d73d5252042a7398a929021535cc5494810a5ce9a9ca40852d74d4e52043872a4a729021c35525394810c5ac8324a40854e7319252042a6b98c9290214b9d06394810a5ae831ca40864d6318e52042973a0c3290214b5d06194810a9ce630ca40854d73186520422f398c8a9021175cc645481087ce831aa40843d7418d52042973a6c4a90214b5d36254810a9ce7b12a40854d73d89520421f3a6c0a90210f5d360548108bce7b02a40845d73d8152042373b6a8a9021539cf5454810a9ae7aa2a40846e7615152042a7398a8a9021535cc5454810a5ce9a9aa40852d74d4d52043872a4a6a9021c35525354810e1ca8a9aa40870d5454d52042b4382c8a90218b5906454810a9ce6322a40854d7319152042b4382c6a90214b9d06354810a5ae831aa40864d6318d52042973a0c2a90214b5d06154810a9ce630aa40854d7318552042973a020a90214b5d01054810a9ae6082a40843d76950520421fbb2a829021879526314810c3aa9318a40861e5458c520430eaa2c629021175da5314810c3cc9298a40861d6494c520422fbb2a629021879915314810c3ac8a98a40862e549885204316aa4c4290219394e6214810c9aa7310a40846f765485204317322a4290218b5915214810c9cc6a90a40864d63548520430f324c629021875926314810c3cc8b18a40861d6458c5204317324c4290218b5926214810c9cc7310a40864d63988520431ab24c2290219558e6114810c74c9300a40863964980520432d31cc0290219658e60148108bce732e840845d73997420422f398cba1021175cc65d08108f4e032e840845e73996
  | 3 => 0xd5610c910d8a64b086488668529803244364994c0192211e1d5600c910c70a9306828866852d81414431daa0c0a0a219a1486050510c5ea9310828862c549884144317aa2c420a218b15162105108deeda90828846d76d48414432731ea420a219358f52105108deec290828846d761484144327318a420a219358c5210510c76a93008288638549804144335a94c020a219a14a6010510cd0a5306428863854d81214432c29ec090a218e1506048510cb0a6302428866b52181214421fbb6a810a210f5db540851087eec2a0428843d76150214430faa4c610a21871526308510c3ea8b18428861c5458c214422fbb6a610a21175db5308510c3cc9a98428861d64d4c214422fbb0a610a21175d85308510c3cc8298428861d6414c2144317326a410a218b5935208510c9cc7a90428864d63d482144317320a410a218b5905208510c9cc6290428864d63148214431daa4c010a218e1526008510cb6a73004288658539802144335a94c010a219a14a60085108dceb316808862f5498b40443162a4c5a02211b1d562d0110c5ea8b16808862c5458b4044237bb6a5a02211b5db52d0110c9cc7a96808864d63d4b4044237bb0a5a02211b5d852d0110c9cc6296808864d6314b404431a2a4c3a02218e9975490110e50a9a94808866a6514a40443942a0a520221d214c5290110a70eaa14808853a75906404429d3a883202216a5c841901108dce5b2a808846d72d954044237b92caa02211b1c96550110c6ea830a808863865d91404431c32ea8a02211e9d85450110c70ca2a2808866865d494044334328a4a0221ca1505250110e90a629280884e9721854044359b20c2a02212e9db4150110c70cba0a808863865505404435830a82a02218e1526010110a70eaa00808872852500404421f3acc9902210f1d564c811087eedaa6408843d76d53204421fbb0a9902210f5d854c81108bceb31e408861f5498f204430e2a4c790221171d563c8110c3ea8b1e408861c5458f204422fbb6a790221175db53c8110c3cc9a9e408861d64d4f204422fbb0a790221175d853c8110c3cc829e408861d6414f2044317326a5902218b59352c8110c9cc7a96408864d63d4b2044317320a5902218b59052c8110c9cc6296408864d6314b2044332294c3902211e9d764881109b2e7b24408863a65152204423d3aec7102212e5d36388110cb4ca29c40887185414e204433532ea510221cad505288110e50a8294408874b5314a20443a4298a5102215a1d54288110ad0ea994408856a7588620442b53a843102216a5d02188110b92e610c408843e74d95204421eba6ca90221179cf65481108bae7b2a408843f74595204421e3a2ca9022117dcd65481108b8e6b2a408866752185204423c3aac8902218e1975448110c70ca2a240884787558d204432c32e
  | 4 => 0x98c7b12a48863864d81524432c31ec0a92211bdd95214910a5ee8a90a48852c7454852442a7b9aa429221531cd5214910a5ce9310a48852d7498852442a739cc429221535ce621491087ce8308a48843d74184524422f398c229221175cc6114910c5ccbaa0a48846d7695052442a739ca829221535ce54149108deecaa0a48854f7355052442a639aa8292218b9945414910e52e02a0a48864e65d4c5244387aa6a629221c315353149108daed298a48852e7494c5244296ba4a6292211bdd95314910a5ee8a98a48852c7454c5244387aa0a629221c31505314910e56a8b00a4887285458052443a5a9ac029221d214d6014910ad2e1b20a48862d6419052442a7398c829221535cc6414910acae2320a4885697019052442b4b86c6292214b9d06314910a5ae8318a48864d6318c52442b2b88c6292215a5c06314910a5ce9b00a48852d74d8052442a739ec029221535cf6014910cd6c2b00a488669615805244297ba220292214b1d11014910a9ee6880a48854c73440524422f39ecba1221175cf65d09108bee6b2e848845c73597424431c2a4c1a12219614e60d0910cd6a5306848847875583424431c2a2c1a12219614d60d09108bce7b2c848845d73d96424422fb9acb21221171cd6590910c76a93048488658539824244334294c1212211e1d56090910cb0a6b04848866852582424422f39ecaa1221175cf65509108bee6b2a848845c73595424423db82caa12214b9cb5450910a5ce9a92848845e73d94424422eb9eca2122117dcd65109108b8e6b28848845e73194424422eb98ca212214b5c854109108bceb318848861f5498c424430e2a4c621221171d56310910c3ea8b18848861c5458c424422fbb6a621221175db53109108beec298848845d7614c424432731ea4212219358f5210910a5ae8290848864e631484244326b18a4212214b9d54210910a58eaa10848862e65508424431632a8421221a358d4210910e1ea6a10848870c53508424431a2a4c2212219914a61109108e8eab0884886a542584424431c2a4c0212219a14a6010910d5285300848847875580424421f3a6cb192210f5d3658c91087ee8b2c648843c74596324431c2a4c11922196d4e608c910cd0a5304648847875582324431c2a2c1192219a149608c91087ce9b2a648843d74d95324421fba2ca992210f1d1654c9108f6e0b2a648854e73d49324421f3a6ca192210f5d3650c91087ee8b28648843c74594324421f3a0ca192210f5d0650c91087ceb320648843c75590324421fbb6a8192210f5db540c91087eec2a0648843d761503244317326a4192218b593520c910c5cc8290648862d6414832442a6b98a419221539d5320c910a98ea990648864e654c8324432632a6419221a3591320c910e1ea8990648870c544c83244332294c2192211d1
  | 5 => 0x862c655084284346b1a8421421aa50a6010a1087ce9b2c650843d74d963284334292c1194210f9d3654ca1087ae9b2a650843e74995328421eba4ca99421539cf524ca1087ce9b28650843d74d94328421f3a0ca194210f5d0650ca10c9cca990650864c654c83284346b226419421b24ca600ca10a5ae52a6830843e769514184296b94a8a0c210f5db5410610c5ea8b10830862c54588418431daa2c020c214b5d252c8610a9ae7296430846e769492184296ba4a490c21535ce52486108daeda90430862d64d482184326b1ea410c218b5905208610c9ac6290430866b525802184317aa2c5a04218b15162d0210a5ae52a481085a97295240842d4b9083204210f9d854502109d2e5b2a81085b171d51408423d3b0a8a04212e9d854502109d2e430a81084ba76d054084296b94a8204210fdd95410210d62c2a00810862d64d4b2084326b1ea5904218b59052c8210c9ac6296410852d7494a20842a6b9ca510421365cf6488210972e9b1c41085a97494a20842e4b9ca5104216a5d02188210b92e610c410846e76149208425cba6ca90421365cf6548210bc2e3a92410847a7614920842753b0a4904212e5d061482109b2e630a41084ea76c852084296ba4a410421535ce52082108deeca9041086e161480208425dba2cb884213adc965c42108bce7316a88845d7398b544428f39cc5aa221475ce62d5110c5ec5316a8885397018b5444297b92c1aa2214b1c960d5110c5ea9314a88862f5458a544432731cc52a2219398d6295110c9ac6b14a88862f64d895444327b1ec4aa2218bd906255110c9ec6312a88864c631895444334316c0aa2210fdd95415110a5ee4aa0a88852c725505444297394c82a2214b5ca64151108dce4308a88846d72184544429cb86c42a221479cc6215110a3ae6310a88862d62188544429ab88c42a2214e5c06215110a5ce5b00a88852d72d80544431db0ac02a2218e58560151108bce7326a48845d73993524421f3a4c7a92210f5d263d4910a9ce72a6a48854d7395352442a7b9aa9a9221531cd54d4910e52e02a6a48870f54d4f52443862a6a7a92218bd9264d4910a9ce7326a48854d7399352442b4b80c9a92214b9d263d4910a5ae931ea48864f6398f52442b4b80c7a92214bdd160d4910a58e8b06a48854f7358352442a639ac1a922187d526394910c38a931ca48861f5458e524430e2a2c729221879935394910c3ac9a9ca48862e64d4a5244316b26a5292219398f5294910c9ac7a94a48861e6498e524430eb24c729221879916394910c3ac8b1ca48843e76d51524421f3b0a8a922187d536354910c38a9b1aa48861f5418d524430e2a0c6a922187d935354910c38c9a9aa48861f64d8d524430e326c6a922187d906354910c38c831aa48862f64d895244316326c4a922193d8f6254910c
  | 6 => 0x823cbb4a5100416a5d25288020b92e729440105a97408620082e4b984310041d854421880208deeab22401046f7558d2008256ba0c290041335cc6148020cc8c2a8a40104ad74d812008266b9ec0900413a9db4048020b94e7a0240106a96410120082753b660900416a9d33048020d92c618240105aa7494920082e539ca4900413a9d84248020b94e621240104ea760c920082d53a064900413a9db2148020ec2a390a401045e7318954c422eb98c4aa6210fdd95415310c5aa8b10a98864e6398854c4317322c42a6219398d6215310c9ac6b10a98866a6258054c4334b12c02a621179cc6454b108bae6322a58843e7418d52c421eba0c6a96211bdd95214b10c5ac8a90a58864d6354852c430f324c629621875926314b10c3cc8b18a58861d6458c52c4316b24c4296219358e6214b10c74c8b00a5886396458052c432d31ac0296219658d6014b108bce632e858845d7319742c422f398cb21621175cc6590b108bee6b2a858845c7359542c422f398caa1621175cc6550b10a58e4aa2858852c7454942c422f39eca21621175cf6510b108bce6328858845d7319442c4317b2a84216218b5954210b10d1ac6a1085886a54258442c421f3a0cb196210f5d0658cb1087ee8b2a658843c7459532c421f3a0ca996210f5d0654cb10a98e6a92658843e74d9432c421eba6ca196210f9d0650cb1087ae8328658864f654c832c4326b2a6419621a3591320cb10d8a64b08658852d7215341c421f3b0a8a0e214b5c8545071087eecaa0838862e5458841c4316aa2c420e218e9516010710c72a8b00838852d7414b21c42a6b98a590e211b9d85248710a5ae8292438854d7314921c4316b24a410e219358e52087108deeca90438862d6454821c4326b1aa410e219a9496008710cd2a4b00438862e5458b40c4316aa2c5a06214b5c8549031087ced2a2818843d76d5040c4296b90a8206218b59252c8310c9ac7296418862d6454b20c4326b1aa5906214b5d05288310a9ae6294418846e7694920c4236bb6a4106214b5d05208310a9ae6290418845e7398b548422eb9cc5aa4218bd516295210c9cc7314a90864e6358a5484326b1ac52a4219a98a6095210cd2c5304a90843f765505484296b94c82a421179ce64d4a108bae7326a50843e7498f528421eba4c7a94218b5935294a10c9ac7a94a50861e6498e528430eb24c729421879916394a10c3ac8b1ca50863a64982528431cb24c1294219698e6094a10cb2c7304a50846f765485284296ba4c429421535ce6214a108bce7b2e850845d73d97428431c2a2c1a1421179cf6590a108bae7b2c850866852582428422f39ecaa1421175cf6550a108bce732a850845d739954284297396a8a14214b9d35250a108bce7b28850845d73d94428422f398ca21421175cc6510a10c5ccaa10850
  | 7 => 0x2a10413a5c0615082099ae7b02841045e73d94420822eb9eca210410fdd95410820a5ae4aa0841061e5458c420830eaa2c621041a358d4210820d5285300841043e74d96320821eba6cb190411b5d7648c8209d2e1b24641046d76d523208296ba0a719041595c4538c8208daeb30c641046f755823208275baac1190419add5608c8209d2e1b22641046f7559132082373b6a899041531cd544c820b94e1a9a641046e7614d3208296ba0a699041595c4534c82099cec29a641058d7414d32082e2b88a699041539d8534c820c9cec29a641070e7414d32082a6ba0a699041c35d0534c820a1ae829a64107467114d32082a6b88a699041d15c4534c820a8ae229a641054e7014d32083a5380a699041531d6434c820b94e121a641054c7550d3208386aa286990412b5d0614c8209d2e030a64104ad74d81320821f3a6ca190410f5d3650c820c3ac9298641045f7654c320830eb22a619041535c9530c820d1ac899064106c932980320822f398c8a8841175cc645442087ce831aa21043d7418d51082b4b8484a88418b1914254420ad2e1192a21064c634c9510823bbb2a2288418d5915114420caac6a88a2104e97098b410822fb9acaa0841171cd65504208bce632a821045d731954108316aa0c4a0841335cc6250420c58caa128210725425454108354a10c0a0841179cf65104208bae7b2882104e97098b310821fba2ca988410f1d1654c42087ce832a621043d741953108256ba0c4988419354c624c420c98ca9926210745325453108364990c0988410f9d3650c42087ae9b28621052d7494b21082a6b9ca5908411b5d764884209d6e0b24421046d75d8e2108275b82c7108412bdd1608842099ee6b04421052d7494921082a6b9ca4908418d5925108420caac7288421063564544210832ab1aa2108419c546600842099ae7b2042104e970d902108256bb4c8108412b5d363084209d2e1b1842104cd7698c2108346b24c610841a39916308420d1ac8b1842106a5649442108362b1ca2108418b5915108420c9ac6a8842106a5645442108362b1aa210841aa5926008420d92c730042106aa645802108354b22c010841b298d6008420d92c6b0042104eb755802108335baac010841179ce64940208bae7324a01043e7498e500821eba4c7280418b9914294020c9cc6994a01046d760865008296ba04328041535cc21940208bce7b2c801045d73d964008316aa4c520041335ce62900208bce6328801045d73194400831632a84200410f9d3658c02087ae9b2c60104ad7498a3008326a9cc5180410f9d0650c02087ae8328601064c654c83008266b9ec9900412b5d363c8020d1ac931e401068e6458f2008346b22c7900411bdd951c8020c5ac8a8e401064d63547200833330aa3900411b5da5288020a5ae9294401054d7394a2
  | 8 => 0x263d45208eeeca88a29061e6498c514830eb24c628a41879916314520c3ac8b18a29063a64580514831cb22c028a419698d6014520cb2c6b00a29051d739534148296b94a9a0a4117dcd65905208b8e6b2c829045e73196414822eb98cb20a411b9d6629052087ced2a2829051d739514148296b94a8a0a41179cc65105208bae6328829043d76d50414830faa2c620a41871516310520c5ea8b10829062c54588414831daa2c020a418e1516010520a3ae929e629043f74596314821e3a2cb18a410f9d0658c52087ae832c629046e7598a314822f3b4a698a41475d2534c52087ce8328629043d74194314830eb26a618a4187590530c520c9ea6b10629064c53588314832da9ac018a419614d600c520cd2e132e429046f765532148237bb2a790a414b5d051c8520a9ae628e429056a751832148335328c190a414b5d05148520a9ae628a429061f5458f404830e2a2c7a02418bd5162d0120c58a8b16809051d739524048296b94a920241175cf655012087cec2a2809051d739504048296b94a8202414e5c2541012087eecaa0809061d64d4f304830eb20a79824193d4d62cc120c98a6b16609051d7494e304834d324c790241b858721c8120a5ae828c409054d731462048332b08a310241175ce62d5020a9ae7316a81045e73185540822eb98c2aa0410fdd95415020c3aa8b18a81063554584540830f322c62a0419358e6215020cacc7308a81065563984540831b322c22a0419598d6115020caac6b08a810666625845408338b0cc02a0414b5d262d4c2087ce830aa61043d74185530822fbb2a629841875915314c20caaa6b08a61062d64988530831b324c2298418d5926114c20c6cc8b08a610635645845308333312c2298419c5866014c208ece232e8610475711974308236bacc5a18411e5d660d0c208ece232c861047571196430823d384caa18411d9c46550c208eae232a861051c73551430828e3a2a6a18411b5c96510c208ece2328861047571194430830fb2a8621841875954310c209d2e1310861068d43588430830f324c729041875926394820c3cc8b1ca41061d6458e520828eb98a9a10414d5c454d08208bce7b2c841045d73d9642082a6b98a921041595c454908208daeb30c841046f755824208275baac1210419add56090820a5ce5aa2841043e76151420828eb98a8a10414d5c45450820b54e1aa2841046e7615142082a6b98a8a1041595c4545082095cec2a2841058d7315142082d2b88a8a10414b9d85450820c5cec2a2841070e731514208296b98a8a1041c35cc5450820a1ae62a28410726711514208296b88a8a1041c95c45450820a4ae22a2841052e701514208395380a8a10413a5c363508208dceda9a841052c7454d42082963ae86a10416a9c34350820a58eaa1a841070d5350d4208266b98c
  | 9 => 0xae72a6851054d739524288236bb6a7214414b9d35390a20a3ae72a285106395418142882373b4a8a1441535ce5450a20b1ae72a2851052e7695142883173b4a8a1441c39ce5450a20a5ae72a2851070d739514288286b9ca8a14414b5c65450a20a5ce9a9a851052f75d0d4288386a9e86a14414bdd54350a20e1ea6a1a85105a87050d4288236ba8c2a1441335cc6150a209d2e030a85104cd73d814288346b1a8421441475d253cca209d2e1b24651046d76d5232882a739ea9194414b5d2538ca20a3ae929a65106595318132882a739ea8994414b5d2534ca20b1ae929a651054e7694d32883273b4a699441c39d2534ca20a9ae929a651070d7494d3288286ba4a699441535c6534ca20a9eeb21a651070d5490d32882a7baa8699441c3d51434ca20b90e0a1a651046d751853288256ba0c2994413a5c0614ca2095ae9b02651068d644c8328823bbb2a228c41179cf65d06208bae7b2e831045e73997418822eb9ccba0c41475ce54d0620c5ca8b16831062f6550b4188274392c120c41475ce545062099ae6312831062f65509418822f39eca20c41175cf651062087ce9b2e631043d74d97318821f3a4cb98c410f5d265cc620a3ae929e631064e5358b3188327b2a6598c413a1c9608c620a3ae929a63104ad741893188327b2a6498c410f9d3650c62087ae9b2863104af745822188267b9ac110c41335cf64086209d2e1b20431062d659902188316b2ac810c412b5d363086209d2e1b18431064d6598c2188346b24c610c41935956308620d1cc8b18431068d6458c2188316b22a210c419358d5108620cd2cb30043106a9649802188364b1cc010c41aa9916008620d52c8b0043106ca635802188364b1ac010c419a5456008620a3ae72a481104cd7398a408828eb9ca8204418b951621022095ae931461104cd73d932088316b2cc9904418b59564c8220c9acb31e411068d6498f2088326b2ac790441a399163c8220d1ac8b1e411062d645472088326b1aa3904419998551c8220c72cb326411063965593208832cb2cc790441a699263c8220cb2cab1e411061f5458e544832731ac52a2419358d6295120cb4c6b04a89045e73185544822eb98c2aa2410fdd95415120a3ae7320a89061d64d4e5348317322c529a418b5916294d20c74c8b04a69043e74185534821eba0c2a9a410f9d36054d2087ae9b02a69045f7654c534828eba4c629a410f9d06214d2087ae8310a69047970d974348236b96caa1a411ddc56550d208e8e2b2a869051e73d51434828f3a6a6a1a411b9d46250d208f4ebb02869046e72194434830f32a8621a41871954310d20d1a86b1086904e870588434831c2a2c1a12418b9954210920d1ac6a10849065853583324832732a6419241a3591320c9208bce7326a29045d73993514821f3a4c7a8a410f5d
  | 10 => 0x64e5358841c8326a9ac420e418e9526010720c72a9300839065a5398041c832ca9cc020e418e9516010720c72a8b00839065a5358041c832ca9ac020e410f9d265cc72087ae932e639043e7499631c821eba4cb18e418b552628c720c9aa7314639062d5458a31c8326a9ac518e410f9d0654c72087ae832a639063a54d8131c831d2a0c098e419654c604c72087ce9b28639043d74d9431c821f3a4ca18e410f5d2650c72087aeb320639043f7559031c821fbb4a818e410f5da540c72087eecaa0639043d7655031c830f324a618e4187592530c720c3cc8a98639061d6454c31c83172a4c418e418b552620c720c9aa7310639062e5458831c8316aa2c418e419394d620c720c9aa6b10639063a5498031c831caa4c018e419694e600c720cb2a7300639063a5458031c831caa2c018e419694d600c720cb2a6b00639054d73d5321c8386aa4a790e41c395153c8720e1aa8a9e43907255454721c83a2a9aa390e418b55260c8720c9aa7306439046e76d5121c82a6b9ea890e418bd965448720c5ecaaa2439064f6594d21c8386aa4a690e4193d955348720e1ca8a9a439070d5454d21c8392aa6c290e41d154f6148720c5aa8302439064d5318121c821ebacc810e410fdd5640872087aed2a0439043f7655021c822ebacc610e41879526308720c3aa9318439045f7558c21c830f2a2c610e418755163087208baed298439061e6494c21c830eb24a610e4117dd95308720c3cc8a98439061d6454c21c831d2a4c010e418e5526008720cb4a730043906595398021c831d2a2c010e418e5516008720cb4a6b0043906595358021c8338a8ac010e41175d663d0320c3ca931e819061d5498f40c822fbaac7a06418795163d0320c3aa8b1e819045d7694f40c822fbb2a7a06418b55262d0320c9ca7316819064d5398b40c83172a2c5a06418b55162d0320c9ca6b16819064d5358b40c8316aa6c4a06419354f6250320c5aa8312819064d5318940c838d29a80206410f5da54cc32087eecaa6619062e5498b30c8316aa4c5986418b95162cc320c5aa8b16619064e5358b30c8326a9ac598641935ca63d5220c9cc6b16a910659639835488334b14c1aa441479cf5495220c3ea8b1ca91064e6358a5488326b1ac52a441479cf64552208bce630aa91045d73185548821fbb2a82a441475ce6415220c5ae5326a71063964983538828f3a6a729c41875935394e20c38e6b24a71062e6458a5388316b22c529c41479d36354e2087ce830aa71043d74185538822fbb2a629c41479cf54d0e20a3ae929e871051d73952438828f39ea8a1c410f9d85450e209d4e5b02871051d73950438821fbb2a821c41475d25310e20a3eeaa18871051d7550c438830f32a8621c418b9516210e20c5aa8b10871064e535884388326a9ac421c41a350d6210e20a3
  | 11 => 0xc8297394c2aa6414edc16155320a3ce630aa99051d7318554c8297390c2aa6414e5c06155320a3ce7b02a99051d73d8154c821fbb2a82a641875526315320c3aa8b18a99061e6498c54c830f322c62a6419398e6215320c9ac7310a99051e74d4e53c828eba6a729e41565c36494f20c3ac8324a79054e7219253c828f3a0c529e41475d06294f20aace2314a7905557118a53c828f3a0c329e41475d06194f20a9ce430ca7905597018653c828f3a6c129e41475d36094f2087ce830aa79043d7418553c822f3b6a8a9e41179d85454f20ab2e1322a79054c7259153c830eb20c8a9e41539c86454f20a9ce530aa79055b7058553c828f3a0c2a9e41475d06154f20a9ce430aa7905597018553c828f3a6c0a9e41475d36054f2087aed2a0a79043f7655053c822fbb2a629e41879915314f20c3ac8a98a79062e6498853c8316b24c429e418e95260d0f20cb2a7306879063a5458343c831caa4c121e419694e6090f20cb4a6b04879051c7355143c828e3a2a6a1e418b5536250f20c9aa7b12879062d5418943c8326a98c4a1e41475ce5410f20a3ae9298879051f7550c43c828ebaa8621e4187d954310f20c3acaa18879062e5498843c8316aa4c421e419394e6210f20c9aa7310879062e5458843c8316aa2c421e419394d6210f20c9aa6b10879068d4358843c831caa4c1216419694e6090b20cb4a6b04859045d7598c42c830f2a4c621641875526310b208beeab18859061e5458c42c830eaa2c621641175da5310b208beeca98859068d6350842c838729a8421641c354d4210b20c74a9300859063a5498232c832ca9cc1196418e951608cb2087aeb320659043f7559032c821ebb4a8196410fdd9540cb20c3cc9298659061d6494c32c830f322a61964187591530cb20d1ac8990659070e544c832c8386aa264196419694e600cb20c3ca931ea39061d5498f51c830f2a2c7a8e418755163d4720c3cc929ea39061d6494f51c830f322a7a8e418759153d47208bce6322a39045d7319151c821f3a0c6a8e410f5d0635472087aed2a0a39043f7655051c830f2a4c628e41875526314720c3ca8b18a39061d5458c51c822ebb4a628e41879925314720c3ac9298a39045f7654c51c830f322a628e418759153147208eeeca88a39045e7399741c822eb9ccba0e41179ce65907208bae732c839062d5498a41c8326a9cc520e418b5516290720c9aa6b14839045e7319541c822eb98caa0e419694f6050720c72a8302839065a5318141c822f39eca20e41175cf65107208bce7328839045d7399441c822ebacc620e41879526310720c3aa9318839045f7558c41c830f2a2c620e418755163107208beed298839045d7694c41c822fbb2a620e41175d95310720c5aa9310839064e5398841c8326a9cc420e418b9516210720c5aa8b108390
  | 12 => 0xa0481a398d62d0240d1ac6b16812062d62547409031b30aa3a04819a59662d0240d94c731681206696558b4090326b1ea5292811bdd95214940c5ccaa1084a068d63508425021f3a8c899281539cf524c940970e0b2064a064e654c8325032632a6419281a3591320c9408bce7316a2a045d7398b515023bbb2a228a819398e6214540c9cc6b10a2a064d635885150335312c028a819a5896014540c72e132e82a052d72147415029d3a8c1a0a818e99460d0540a5ae428a82a045f73596215022e39acb10a81179cc65885408bae632c42a043e75992215022f398ca10a81175cc6508540c5ac9a9042a064d63d482150316b20a410a819358c5208540cd6a4b0042a066852580215036531cc5a0281ac58741d0140a5ae428c80a063561146405032731cc52a0819398d6295040c9ac6b14a82045e73185521022eb98c2a90811bdd95214840c9ac6a90a42066552584521021ebacc3a10812edd560d0840c76eab0684204b970d8d4210296392a6a10816a9c3525084095cec292842058d7314942102d2b88a4a1081275cc6150840972e030a842049d73d814210326b1ca4210819358d5210840d1ac6a1084206a9429804210354a14c1190811d9c4654c8408eae232a64204b970991321021fbaac899081531cd524c840c58caa12642070d53509321025cb84c81908193d95320c840c9aca990642068d644c8321022f398c4a8881175cc6254440a72e1a12a22062c62509511023bbb2a228881995895114440976e0b1482204af725824110332b14a220881995895110440ce2a3300822068e635884110346b1ac420881a958a5110440c5ac4a8882206a5625444110354b14c020881aa9896010440d52c4b0082204bb75580411031dbaac0208812e5c264c844087aebb24422049d73192211025cb80c91088117dcd65484408b8e6b2a422045e73195211022eb98ca90881275cc6448440c58c8a9242204ac76509211031632a8490881c95095148440d5284302422045e73d94211022eb9eca108810f5d84194040a5ae420ca02068e6358b4010346b1ac5a00810fdd951d0040c5ac4a8e802063661547401021ebb4a9200811e5da5490040b52e52a480205a9721064010398a8883200812b5c86150040c68c2a8a80205aa72951401025d3b084a0081669cc4250040974eda0a802073151d054010326b1cc5aa6419698d60d5320cd4c4b06a99051e73d5254c828eb9ea92a6414e5c36395320c3ac631ca99052e7218e54c828f398c52a641475cc6295320a6ce2314a9905357118a54c828f398c32a641475cc6195320a5ce430ca9905397018654c828f39ec12a641475cf6095320a3ce7b22a99051d73d9154c822f398c2aa641175cc6155320a72e131aa99052c7258d54c830eb18c6aa6414b9c86355320a3ce6312a99051d7318954
  | 13 => 0x5310b40c9cc729085a064d6394842d032731aa4216819358d5210b40d1ac6a1085a070e5350842d0386a9a84216819a94a6010b40cb2a730465a066a5298232d0335292c1196818bd91524cb40c58c8a9265a054c7354932d0317324a4196818b592520cb40a9ae729065a062e6454832d0316b22a41968153dd5320cb40a9aea99065a064f654c832d0326b2a6419681a3591320cb40c9cc7296a3a064d6394b51d032731aa5a8e819358d52d47408bce6312a3a045d7318951d0236bb4a428e819398e5214740c9ac7290a3a046f7654851d032731aa428e819358d52147408eeeca88a3a070e5354b41d0386a9aa5a0e81c954951d0740c5aa530683a062f6594941d0317b2aa4a0e81c394d5250740e1aa6a9283a072552d8541d0316a90c0a0e811b5d662107408deeab1083a046d7694841d032731ca420e819358e52107408deeca9083a064e6354841d0326b1aa420e819a94a6010740cd2a530083a066a5258041d0334a92c020e819c54560107408bce732e43a045d7399721d022f39ccb10e81175ce6588740c3cc8a9c43a061d6454e21d0317322a510e818b59152887408bce632a43a045d7319521d032d29ec090e819694c6048740cd2a430243a045e73d9421d022eb9eca10e81179ce65087408bae732843a045d7598c21d022fbaac610e8117dda53087408baed29843a061e6494c21d030eb24a610e8117dd953087408baeca9843a061e6454c21d030eb22a610e818b5925208740c9cc729043a064d6394821d0317322a410e818b5915208740c9cc6a9043a064d6354821d032d29cc010e819654e6008740cd4a530043a06695298021d032d29ac010e819654d6008740cd4a4b0043a06695258021d02a739ea5294819358f5294a408bce630aa52045d731855290237bb2a429481475ce52d0a40a9ae7294852054d73949429028eb9ca4a1481635ce5250a40a5ced292852062e76949429038739ca4a14814b5ce5250a40e1ae7292852050d739494290296b8ca4a14810f5d46150a4093ae630a85204b970185429024eb9ec0a1481a358d4210a40a9ae529c652062f6550a3290386a9a85194812e5c2644ca40c5ecaa1265204ba74d813290354a10c0994818b592520ca40a9ae7290652062d6454832902a7baa6419481535d5320ca40c9cca990652068d644c8329023bbb2a228c812bdc96090640c5acb310832062d65588419034731ac420c81a358d6210640c5ac4a888320639659804190354b14c020c81aa9896010640d52c4b00832063951580419022f39ecb90c81175cf65c86408bce732e432045d739972190316b24a590c81535ce52c8640c5ecaa16432049d73192219025cb80c910c812e1d1608864093ae6322432054d739492190317b2a8490c81179cf65086408bae7b28432062d6598b4090316b2ac5
  | 14 => 0x8621ca010d6a7210e50086b4b908728043569cc4294021ab2e6214a010f294210a500869d3a065280434e5d03294021e9264194a010d3a74186500869cba0c328043569cc6194021ab2e630ca010c797610650086ad3988328043565cc4194021ad4e420ca010d6972106500863cbb063280434e9d03194021a72e818ca010d6a720c650086b4b9063280435a9c32154021ad0e090aa010c7a76d5150086ad39ea8a8043565cf54540218f4ec2a2a010d5a7315150086acb98a8a80431e9db5354021a74e9a9aa010d3974d4d500878d2a4a6a8043c65525354021e34a8a9aa010f195454d500863d3b0a6a80434e9d05354021a72e829aa010f2a541895008794aa0c4a8043d294c6254021e92a6312a010f2a54c855008794aa642a8043d294f2154021e92a790aa010f315488550087a8a9c42a80435add52154021e54a890aa010f295448550087a529a42a8043d254d2154021ae6ea90aa010f315448550087a8a9a42a8043569ce6454021ab2e7322a010d6a7299150086b4392c8a80434e9d26354021a72e931aa010d6a7298d50086b4392c6a80435adc94354021ad0e4a1aa010f194310d50086b539086a80435a5c84354021a74e9312a010d397498950086ad39cc4a8043565ce6254021ab4e6212a010d59731095008794a1084a80435c9c44254021ae2e2212a010d3a740c9500869cba064a8043d24c83254021ae4e2192a010d71710c950086b539482a80435a5ca41540218f4ec20aa010d5a7310550086acb9882a80435a9c84154021ad2e420aa010d6a728c550086b4b9462a80431e9d83154021a74e818aa010d39740c550086b539062a80435a5c83154021ad0ec90aa010f6371485500869d3a042a80434e5d02154021ab4e610aa010d5973085500861ebb4a8280430fdd95414021c3ca9318a010e1d5498c500870f2a2c6280438755163140218baed298a010e1e6494c500870eb24a62804317dd95314021c3cc8a98a010e1d6454c500871d2a4c0280438e5526014021cb4a7300a010e5953980500863dbb2a0280438e9915014021c72c8a80a010e5a63540500872cb1aa028043539cf5294b40a9ae7a94a5a054e7319252d02a6b98c929681599c46494b40acae2324a5a056970d8e52d02973a0c7296819358c6394b40a5ce830ca5a054e7318652d02a6b98c3296815a5c06194b40a9ce7b04a5a054d73d8252d022f398c2a9681175cc6154b40ad2e131aa5a052c7458d52d02973a0c6a96819358c6354b40a5ce930aa5a056b7058552d02973a0c2a9681539cc6154b40a9ae630aa5a05697018552d02a739ec0a9681535cf6054b408baed298a5a045f7654c52d0237bb2a4296819398d5214b40c9ac6a90a5a065a5398342d0334a94c1a16819694d60d0b408baeb31885a045f7558c42d022ebb4a62168117dd9
  | 15 => 0x5f7558c420870f2a2c6210438755163108218beed2988410c5d7694c420862fbb2a621043175d95310821c5ecaa108410e2d655084208746b1a8421043c394d4210821e1aa6a108410e3654584420872aa9ac3190430f9d3650c82187ae9b286410c3d75990320861fbaac8190430fdda540c82187aed2a06410c3f76550320861ebb2a81904387992530c821c3ac92986410e1e6454c320870eb22a61904393d95320c821c9aca9906410e8d644c832087872a26419043c3551320c821caca6b086410e2d5498a4108726a9cc5208431bdd56290421c5aa8b148210e4d5358a410862f39eca20843175cf65104218bce73288210c5d73994410862f398ca20843175cc65104218baeb3188210e1e5498c410870eaa4c62084317dd56310421c3ca8b188210e1d5458c410862fbb4a620843175da53104218beeca988210c5d7654c4108716aa4c4208439394e6210421c9aa73108210e2e545884108716aa2c4208439394d6210421c9aa6b108210c7975980410871d2a4c0208438e5526010421cb4a73008210e5953980410863dbaac0208438e9516010421c72a8b008210e5a53580410872ca9ac0208438b552628c421c9aa73146210c6f7558a3108716aa2c5188439354d628c42187ce93286210c3d74994310861f3a0ca188430f5d0650c42187eed2a06210c3d76950310861fbb2a8188430f5d9540c421c5ca93106210e2d5498831087172a2c4188438b551620c421c9ca6b106210e4d5358831086a6b9ea9908435a5c354c8421a5ae9a9e4210d6970d4f2108786aa4a790843c395153c8421e1aa8a9e4210e2d549832108726a9cc1908431b5da52884218eaed2944210c6e76d5121086a6b9ea8908435a5c35448421a5aeb2a24210e2f659512108717b2aa8908431b9db5348421a5ae9a9a4210d6970d4d21086a6baca69084393d965348421e1aa929a4210e4f6554d21087872a2a690843c35515348421c5aa9b0a4210e4d53d852108716aa0c0908439354c6048421c6ecb2a24210e3765551210872bb2ca69084395d955348421e4aa92924210f4553949210870f2a4c7a80438755263d4021c3ca8b1ea010e1d5458f500870f324a7a80438759253d4021c3cc8a9ea010e1d6454f500869d3a6a1280434e5d35094021ab4e7a84a010d5973d42500862f39cc928043175ce649402187ce931ca010c3d7498e50086ad39ea928043565cf5494021ab4e62a4a010d5973152500869d3a6a7280434e5d35394021e34a929ca010f195494e500878d2a2a728043c65515394021a74e829ca010d397414e5008794aa0c528043d254c6294021e52a990ca010f4953c8650086b5baa4328043ca5512194021e92a690ca010d737548650086ad39cc928043565ce6494021ad4e5324a010d3a7498e500869cba4c7280435a9ca6394021e32
  | 16 => 0x869d380c32a0434e5c06195021a3ce7b04a810d1d73d825408697396c12a043479cf6455021a3ae7b22a810d3a70d91540869cb86c8aa043179cf60550218bae7b02a810d2c7258d540870eb18c6aa0434b9c86355021a3ce6312a810d1d73189540868f398c2aa043475cc6155021a74e030aa810d3970185540868f39ec0aa043475cf6055021a5ce5b02a810d2c72581540861fbb2a82a043875526315021c3aa8b18a810e3954980540871caa2c02a043879926315021c3cc8b18a810e4e639885408726b1cc42a0438e9926015021cb4c7300a810e59639805408735314c02a0438e9916015021cb4c6b00a810e59635805408735312c02a0439c9856015021c74a9306a610e3954983530871d2a2c1a98438e55160d4c21c5ac9316a610e3a64983530871cb24c1a98438e99160d4c21c72c8b06a610e6a625835308734392c1a9843479d35394c21a3ae9a9ca610d5a70d4e53086acb86a729843569c35494c21ab2e1aa4a610d5a7015253086acb80a929843875906494c21a9ce4324a610d1e7418a530868eba0c529843479d06194c21a3ae830ca610d5a7018653086acb80c329843479d36094c21a3ae9b04a610d4e72d825308637390c8a9843479d36354c21a3ae9b1aa610d5a70d8d53086acb86c6a98430f9d36054c2187ae9b02a610c5e76d5153086ad386a8a9843565c35454c218bcec2a2a610d5a7015153086acb80a8a9843531c96454c21c3ac8322a610d4e72191530868f3a0c4a9843475d06254c21a3ce830aa610d1d7418553086ad380c2a9843565c06154c21a3ce810aa610d1d74085530868f3a6c0a9843475d36054c21a9ce5b02a610d4c72581530861ebb4a8298430fdd95414c21c3ca9318a610e1d5498c530862fbb2a629843879915314c21c3ac8a98a610e3a54980530871caa4c0298439654e6014c21c74a8b00a610e3954580530872ca9ac0298438b9926214c21c5ac9310a610e3a64980530871cb24c0298439a98a6014c21c74c8b00a610e39645805308735312c0298439c9856014c218f4e132e8610c7970997430863d380cba18431e5c065d0c218f4e132c8610c7970996430863d380cb218431e5c06590c218f4e132a8610c7970995430863d380caa18431e5c06550c21a38e6aa28610d1c7454d4308636baec4a18438b5536250c21c9aa7b128610c6d751894308716aa0c4a18439354c6250c218f4e13288610c7970994430863d380ca218431e5c06510c21a3ae72a08610d1d7494c430868fbaa8621843475d54310c21c3ecaa188610e1d6550c43087172a4c4218438b5526210c21c9ca73108610e4d5398843087172a2c4218438b5516210c21c9ca6b108610e4d535884308746a1ac4218438d55161908218bce7b288410c5d73d94420862ebacc621043879526310821c3aa93188410c
  | 17 => 0x844393d8f2154221ad4e190aa110c7b76540508871cb22a0284439658d50142218bee6b06a890c5c73583544870fb20c6aa243935c86355121c98c7b12a890e5b63d81544872c31ec0aa2438ed906055121cb6c6302a890e58631815448735b10c0aa2430fdd95415121a38e6aa0a890d3870550544870eaa2c62a243879916315121c9cc6b10a890e4d63588544861fba2c1a9a430f1d160d4d21c5ae4322a690e2c64d89534871db26c0a9a438e1936054d21c76c8302a690e38641815348735b10c0a9a4317dd95314d21a38e8a98a690e1d6454c53486ac382a629a43871cd6414d21c3ac9318a690c7a70d97434863cb86cba1a43471cd54d0d21a70e0aa68690d1d7414f434863d386cb21a431e5c36590d21a3ae62a48690c7b70595434863c382caa1a430f9da5450d21a38e6aa28690d3870551434862f3b4a6a1a431edc16510d218f0e0b288690c3d76d50434868eb98a821a43475d05310d21a3ceaa188690d1c7550c434870fb2a8621a43875954310d21c5ea8b108690e2c545884348727a9ac421a439314d6210d21d1a86b108690d1d7315342486a6b98a9212431bdd95390921a58e8a9c8490d687054e424868eb98a8a12434b9d76450921a5ce92a28490c6e7615142486a6b98a8a1243635cc5450921a5cec2a28490e2e761514248787398a8a12434b5cc5450921e1ae62a28490d0d731514248697380a8a12431b1d95350921a58e8a9a8490d687054d42486963ae86a1243c3d4f4350921a58eaa1a8490f0d5350d4248666b98c2a12433a5c061509218dcebb028490ccd73d814248746b1a8421243475d053cc9218dcebb246490ce970d923248637bb2a919243531cd548c921ad0e0aa46490d2d7414e324868eba0a699243531cd544c921ad0e0aa26490d4e75d8d32486373b0a6992434b5d0534c921b1ae829a6490d4e7614d32487273b0a699243c39d0534c921a9ae829a6490f0d7414d3248686ba0a699243539c0534c921a98eb21a6490f0f5490d32486a63aa8699243c3551434c92195ae830a6490ce97018532486373aec0992432b5d3604c921d1ac89906490d1d7315341487162a2c5a0a434b1d542d05218bee6b2a8290d1d731514148666b98c4a0a434b1d54250521c58caa128290d1d7414f314872629ac598a430fdd1654c521878e8b2a6290cad74189314872632a6498a432bdd1608852199ee6b044290c7b76540504869c3a2a028243561cd5014121ad2e1210a090d6b7050850486b4b8464282435adc13214121ad2e1108a090e4d6398b540872d31cc1aa0439658e60d5021cb4c6b06a810e59635835408735312c1aa0439a1c960d5021a3ce7aa4a810d1d73d52540869d386a92a0434e5c35495021c3ac631ca810d2e7218e540868f398c52a043475cc6295021a3ce630ca810d1d73186540
  | 18 => 0x254041ab4e6212a020d59731095010794a1084a80835c9c44254041ae2e2212a020d3b744c9501069c3a264a80834e9d03254041a72e8192a020f49320c9501069c3b282a8083ccdc54154041ad4e420aa020d69721055010636bb4a4280839398e5214041c9ac7290a020c6f76548501072731aa4280839358d5214041cd4a5300a020e6952980501063dbb2a0280839a9895014041cd2c4a80a020d4d7398b54c862f39ec0aa643175cf605532187eecaa0a990e1d5458c54c870f322c62a6439358e621532187ce9b02a790c3d74d8153c862fbb2a629e43875915314f21c5ac9310a790c7a70d9743c863cb86cba1e431e9c36590f218f2e1b2c8790d1c7355143c868e3a2a6a1e4387d954310f21c3acaa188790e8d4358843c868eb98a9a1643535cc5490b218deeab048590c3e7615142c868eb98a8a1643695c75450b218dcec2a28590d4d7315142c86573b0a8a1643635cc5450b21a5cec2a28590e2e7615142c8787398a8a16434b5cc5450b21e1ae62a28590d0d7315142c8792b88a8a16434b9c05450b21a58e8a9a8590d2c7550d42c8786a9a86a1643335cc6150b219d2e030a8590ccd73d8142c861fbb2a821643879516310b21c3aa8b188590e8d6350842c8752a12c2216433a5c3648cb21a5ae829c6590c6f7558232c86373b6a899643531cd544cb21b8ae3a9a6590c6e7614d32c8696ba0a699643339d8534cb21b1ae829a6590d4e7614d32c87273b0a699643c39d0534cb21a9ae829a6590f0d7414d32c8686ba0a699643d15c4534cb21a9ce029a6590d4c7590d32c86a63aa8699643c3551434cb2195ae830a6590ce97018532c8656ba6c09964387592530cb21c3ac8a986590e8d644c832c8762992c2196438b550625072199ae63128390c5e7399250c862eb9cc9286430f9d2639432187ae931ca190e2e6450a50c872731a65286431edd950143218bee6b06a910c5c73583548861fbb2a82a443875516315221c72a8b00a910e1e6458c548872731ac42a4439358d6215221cb4c7300a910e59639805488734b14c02a4438e9916015221cb4c6b00a910e59635805488734b12c02a4430fdd160d4e21878e8b06a710c5f7654c538870eb22a629c439654d6014e218f4e032e8710c7970197438863db82caa1c431e1c16550e218f4e032a8710c7970195438868e39aa8a1c43471d15350e21c3ecaa188710e1d6550c4388746a1ac421c43a358d4210a21d1ac89906510d1d73153418869cb80a9a0c430f9d85450621a3ae62a28310d3970151418861fbb2a820c43879516310621c3aa8b188310e2e545884188716aa2c420c438e9516010621c72a8b008310c5e73992508862eb9cc9284430f9d2639422187ae931ca110e3970191508870fb26c6a8443871936354221c3ec831aa110e1c6418d5088717b2642a
  | 19 => 0xb32264a0cb970991325071632a84992831edc1650c9418f0e0b2864a0e2d64d483250716b20a419283535cc520c941a9cea99064a0d4c754c83250726b2a6419283a3591320c94195ee4b0482a0c7b7654050506b4392a0282834e5c34214141a76e0a10a0a0d397090450506a739ea529083535cf5294841ad4e1a94a420d6970d4a52106b5386a7290835a5c35394841a9ce6324a420d4d7319252106973a0c7290839358c6394841a9ce630ca420d4d7318652106b5380c3290835a5c06194841a5ce9b04a420d4e73d8252106a6b9ec129083179cf60548418bae7b02a420d6a70d4d52106b4b86a6a90834b1d16354841a5ce831aa420e4d6318d52106a7398c2a9083535cc6154841ad4e030aa420d697018552106a6b9882a90834b9d36054841a9ce7b02a420d4d73d8152106963a2c0a9083175da53148418beeca98a420e4e539885210726a9cc4290831bdd95214841c9cc6a90a420e4d63548521072d29cc0290839654e6014841cd2a5300a420e5a53580521072ca9ac0290839a5496014841ccaa4b0e8420c5d7598c421062fbaac621083175da53108418beeca988420e4e639484210726b1ca4210839398d5210841c9ac6a908420e8d63508421078729a8421083c354d4210841ccca4b088420c7a70996321063cb84cb190831e9c0654c8418f2e032a6420c3d75d913210717b22a4990838b191524c841a98e6a926420c7a70994321063cb84ca190838b992520c841c5ac92906420d4d739483210717322a4190838b591520c841a9eea9906420d4d754c83210727b2a641908393595320c841d1ac89906420f0e5354b4110786a9aa5a08838b54a60d044187aed2a48220c75769524110717b2ca4a08838bd955250441e1ca6a928220f0d535494110716a90c0a088399d965250441ccecaa928220f2654549411072731ca5a80839358e52d4041c9cc6a96a020e4d6354b50106b5396a1280835a5cb50940418bce7314a020c5d7398a50106ad39ea528083565cf5294041e94a7294a020f4a5354a50107a4a9aa528083ca1915294041ab4e6294a020d597314a5010794a9683280834edd54194041e52a4a0ca020d7375506501069d3a4c528083569ce6294041ab2e7314a020d5a7310a50106acb988528083ca5084294041a74e8194a020d39740ca50107a499065280835a9c86194041ad2e430ca020d3a70d05501069c38282a80831e9db5254041ab4e7a92a020d5973d4950107a529ca4a8083ca1925254041e94a6a92a020f49535495010794322a4a80831e9d85254041ab4e6292a020d5973149501079529682a8083ca54b4154041ec2a520aa020d3b75505501079529282a8083ca5494154041ae6eaa0aa020f615250550106b5394c8a80835a5ca6454041a74e9312a020d5a7398950106acb9cc4a80834e1d16
  | 20 => 0xd54151320cb86aa6c299065535d6614c832e1aa930a641954f75585320cac7ba2c299065631d1614c832e1aa8b0a64195cb70585320cae4382c299065639d0614c832b1ae830a641970d54185320cae5380c299065725c0614c832b1ce9b02641958d74d81320cb86aa6c099065535d6604c832b1ce9302641958d74981320cb86aa4c09906553dd5604c832e1aa8b02641970d54181320cb64b00c09906533dd932d4432d1cc8996a21968d644cb510cb872a265a8865c355132d4432e1aa8994a21943f74582510ca1e3a2c128865c39513254432e1aa8992a21964f764c9510cb263b264a886593d913254432e8ee2992a219744714c9510ca1f3a0c0a88650f5d06054432c9a64302a21943d76950510ca1fbb2a82886533dd93214432d1cc8990a21968d644c8510cb86aa264288651ddd95114432c74a9300a21963954980510cb64994c0288658e9516014432c72a8b00a2196c932580510cb38a8ac02886533dd932d4032d1cc8996a01968d644cb500cb86aa265a8065c39513294032e1aa8994a01964f764ca500cb263b26528065935913294032e96e0994a019748704ca500ca1fba2c3280650f1d16194032c9a64b0ca01970d544c9500ca1f3a0c2a80650f5d0615403287aed2a0a01943f76550500ca67bb26428065a39913214032d1ac8990a01970e544c8500cb86aa264280658d9526114032c6aa9308a0196c532984500cb1b2a2c2280658d5516114032d8a64b08a01947b76540500cb38b0aa028065179cf6054b418bae7b02a5a0c6f7654852d0726b1aa4296830fdd560d0b41a58e4a9a85a0da571d4942d06573b0a4a1683635cc5250b4193ae630a85a0cb97018542d064eb9ec0a16839358e5210b41c9ac6a9085a0e8d6350842d0752a12c2216831e9c3658cb418f2e1b2c65a0cb97099132d06a639aa4996838b195424cb41e1aa6a1265a0e4f654c832d0726b2a6419683a3591320cb418bce7314a1a0c5d7398a50d071731285286831edd950143418deeca90a520e4d635485290734a92c029483a358d4210a418f6e0b2a6520c7870595329063d380ca994831e5c0654ca41a98e6a926520e4f654c83290726b2a6419483a3591320ca418bce7314a120c5d7398a5090727b1ec4a848393d8c6254241c98c6312a120e2f62d05509069d38682a84831edd95014241cd2c4a80a120c5f73583525062e39ac1a92831bdd95214941a98e6a90a4a0e4d6354852506b4382a429283475cc52d0941a9ae629484a0d4d7314942506973aec4a1283475cc5250941b1ae629284a0d2e7614942507173b0a4a1283c39cc5250941a5ae629284a0f0d731494250686b98a4a12834b9c0525094193ae630a84a0cb970185425061f3aec0a1283275cf6050941d1ac6a1084a0d4d7214e325071632a8519283c3d4d428c94187ce
  | 21 => 0xb86b98a8a14654b5c45450a32a5ce02a2851968c6350d428ca1fbb2a821465879516310a32c3aa8b18851968d63508428ca75386c9994650fdd16094632878e8b04a31962c64509518ca3bbb2a228c654e9d35094232c5cc8a14a11943e74185508ca1eba0c2a84651edd95014232c76a8b04a89966962982544ca3d380c2aa2651e5c0615513287eecaa0a89953970990544cb26b1ac42a2658715163d0932ad4e12a484995ca70d8e424caa73a8c721265331cd619093299ce7304849952e75d91424ca973a4a8a12655a9c254509328dcec2a2849952e76151424cb173b0a8a1265c35cc5450932a5ae22a2849952e70151424ca673a8c6a1265939d4635093299ae231a84994ce7018d424cb1632e86a1265a318f4350932c98cb21a849958d7490d424cb862a486a12654b1d54350932c58caa1a849964c6550d424cb87b2a86a1265c31954350932c18caa1a849968d43d85424cb46a18c0a1265a358d42109329b4e1b24649968d6490a324cb47b2285192651e9c264d45328f2e1326a29970d4350b514ca1f3a4c1a8a650f5d260d45328eeeca88a29963a64980514cb1cb24c028a658e9916014532c72c8b00a29966b72580514cb34392c028a658e5c264d4132c72c9a84a09947b76540504cb86a1a84282650fdd16114132878e8b08a09952e72186540ca9d380c32a0654e5c06195032a5ce5b04a81963960182540ca3d380c2aa0651e5c06155032a74e1312a81953970989540ca96392c2aa0654edc16155032a70e0b0aa81952e72185540ca9d380c2aa0654e5c06155032a5ce5b02a81952e72981540cb1cb00c0aa0650fdd95415032c3aa931c841945f7558e420cb0eaa2c721065875526310832c3ca8b18841961d5458c420cb17b2a84210658b5954210832d1ac6a10841946d7694e320ca373b6a8990654b5d6544c832c5ecb2a2641962f65551320cb8739aa899065c31cd544c832c5aa9b1a641970d5494d320caa6bae8699065c3553434c832e1aa921a641970d5450d320caa6ba88699065c3550434c832c9aebb2a641964e76d95320caa6ba6ca99065535c7654c832a9ce1b2a641954d75991320cae5384c899065725c2644c832a9eeab22641968d64191320ca673b6a899065539db544c832c9cedaa2641954d71d51320caa7386a899065535d6544c832b1aeb2a2641950d75951320cb47b2ca899065c3d96544c832a9cecaa2641954c76551320cb87ba2a899065c3d91544c832e18c8aa2641954f71551320caa6382a899065c3dd5544c832d1ecaaa2641970f65551320cb87bb2a899065c39d9544c832e1aecaa2641970c76551320cb87b8aa899065c39c5544c832e1ae2aa2641970c71551320cb87b82a899065c39c1544c832e1ae0aa2641970c70551320ca673b0a899065539d4544c832b1ce82a2641970
  | 22 => 0x885965806054c428beeca98a62164d5358b4310b2729ac4218850f5da54908428daed2a4842161f6594d4210b0fb2aa6a1085c39c95350842e18e4a9a842164f6594d4210b27b2aa6a1085c39515350842e1ce8a9a842170f6454d4210b86a9e86a10854b5d64350842e1aa721a842170d5310d4210b16baecaa10858b9db6550842a5ae7b2a842152d71d954210a97386caa10854b5d66350842b54e131a84215a97098d4210a97baac6a1085a358c635084295ceda9a842158d7594d4210b47b2ca6a1085c3d965350842a5ceca9a842152c7654d4210b87b1aa6a1085c318d5350842a5ee2a9a842152c7054d4210b87baaa6a1085a3d955350842e1ecaa9a842170f7654d4210b873b2a6a1085c35d95350842e18eca9a842170f7154d4210b8738aa6a1085c35c55350842e18e2a9a842170f7054d4210b87382a6a1085c35c15350842e18e0a9a84214ae7614d4210ac7398a6a1085c354c5350842e1aa7b0a842152d759854210b86a9cc2a10854bdd56150842b1ee6b0a842158c735854210b86a9ac2a10856adc16150842b50e0b0a842158e731854210ac6b98c2a1085c354c6150842b54e030a84215a9701854210ac739ec0a1085635cf6050842e1aa7b02842152d759814210ac739cc0a1085635ce6050842e1aa7302842152f755814210b86a9ac0a1085c354c6050842d52c030284214af7650b5110b4731a85a8885a358d42d4442e1ca6a16a22170d5350b5110b86a9a852888517dcd60944428b8e6b04a22170e535095110b86a9a84a88858bdd94254442c58eca12a22162f635095110b93b8a84a8885c91c542544428bce6302a22145d731815110b16a10c0a8885175da53144428beeca98a2214af765085110b4731a8428885a358d4214442e1aa6a10a221477765445110b2d29cc0288859654e6014442d5285300a22165a535805110b2ca9ac028885aa5096014442ce2a2b00a2214af7650b5010b4731a85a8085a358d42d4042e1aa6a16a02170e5350a5010b86a9a85280858bdd94294042c58eca14a02162d6350a5010b95b828528085ca1c142940428bee6b0ca02145c735865010b16a12c328085c354d42540428bce630aa02145d731855010a2ebb4a62808517dd9531404295eeca10a02168e635085010b46b1a8428085c394d4214042e1aa6a10a021656539845010b2aa9cc228085a950a6114042caca6b08a021655535845010b52a12c2280851edd95014042ce2c2a80a02164d6398b548cb2cb1cc1aa4659a98960d5232cd0e4b06a91953a70d52548ca9d386c8aa4651e9c061552328f2e030aa91943f76550548cb26b1cc42a4658b5506250e32d1a86b10871953a70d53428ca9d386a8a14650f9d85450a32b1ae7aa285195aa70d51428ca373b0a8a14652b9d85450a32a5cec2a2851962e76151428c
  | 23 => 0x600100080600040010040000010001000002400c00d000001800600600080b80020030000000006005001004800400100d80000020050008000000000002800800c00f006802c000002002002000400d000000800e00000700100000010008028000000000803000200300100040000000000028014002009800c00601800c800000e02d011002000002a0020000002005006002800200b00180340040000068004002003003000800c014006000c004000000001800a0030020004002000001002400c0000040008000002000000801e00400b80000360000010008002017000000c00a003002802000400000380c800000300e0030000007004000000001c002800001c00600000240000020018004010000000000c0080030008000020003000800000200f00000000600000008060002001000802400e007003803802400d001003c00c00b001002001200400180000020020000018000000004800003e01100100a0008002009800000001200f0000002037003801000001600280040000000018000014014000807c00e0000050000008000000001000600000f800000000100180040260010040000002000001800800600000880280140020000000006003002001c036000000005c000009000001c0140030048018008005002800c0000320028004000001001800400e003000800400000000080b8012000002803000a001002002400600800d000800200b002801000a04a00180240260020060030004001000002800000c004000000f569c35394f428f4e030aa7a14797018553d0a2fbb2a629e8517dcd60947428b8e6b04a3a14777654451d0aad39ea128685179cc61543428bae630aa1a147b7654050d0aad386a729c851e9c06154e428f2e030aa72145f7654c5390a2fb9ac128c85171cd60946428eeeca88a32155a73d425090a2f398c2a8485175cc61542428f6eca80a12165b535825350a2fbb2a629a856a9c362d0d42a5cea31686a14ac725874350a57394c1a1a85a34c86250d4295cea31286a162e751894350a56b88c4a1a852b9c06250d42d1ac7a1e84a147a7098f5150a3cb84c7a8a85179ce60d45428bae7306a2a1477765445150b2d31cc028a859658e6014542cb4c6b00a2a1659635805150b1dba2c028a858e1d16014542cd6e4b00a2a1668725805150b2cb1ea1282851edd950141428bee6b08a0a145c735845050a8f3a0c329885539c86194c42ab4e030ca621559701865310a8f3a6c129885539cb6094c42cb2c0304a62147a701855310a3cb80c2a9885569c26454c42ab2e1322a62155a709895310aacb84c4a9885471d16154c42a98e4b0aa62155b705855310aac382c2a9885479d06154c42a9ce430aa62155a701855310aacb80c2a9885479d36054c42a9ce5b02a62151e749815310aa7394c0a9
  | 24 => 0x2c00400100100000100010008008006004000000002c001000001400200201a80000020000000000000003009000000c000001801400000c0000004012004002000c00e00d000001c00000c0038008004008000000003a000000005804c000003800400c000000001000004c007802000600100180240000060020000008022002001c00a0000050000000001001800000c000000000c00000700b800400800e0030090008000000803c0320010008018002000004000801c004009800000200000a8004002001002000000000600000040000000068018002008000806003600000d800005003001300000280010000000012031003000400a006000001400000100200200420050048000000004000001000000400180040060030020004004003000000000200200080200040020038008014001008002000e0010018034000005000801000600b000800000400000100000220080008010012000000005c000000002800000400c0030000004005009000c0020010008000002001008800800a02000a0020016000007001400000000100180180000060008014001001803000600000100d40020070010008046002000001c00e021006001c00e004003800000a001001002000e00000a0004000000000000400000a00000000100010018000008001001802c00c0270010018000002006000800000400000040000020070000008009001807c00c001009002c002002008000000a014001000000a005000004803000200800000040070018000002005008000000e006000000808a004000005000201e001000400400600280e80000000020004002001000007802a001000801c00a00000500340020010010034000000009800c004009001003805c000004800400a00300600000000220078028006000000000c00e01200b000000a0040020000020000001003800000600000040020000000024040007003000400a001000809800600000b801400000a0000074008004000803400000100280080000080000000000003000002800800000280340000050018008010000000000000800a0000010002001000800000401100d803400000100d8004012000001001c00c000001800800a011021800400200000100000160040088000002000004803401e002002800c012005000000c0000000000008018008000800c03e00000100640080000008020002000003800000600400580040040010008008054005008800c0040030008004004005001008c00005b00b000400e0000048004002011001802402a002000805801a0000110014000003001001c04c000000000c00e00d003800000200400300500040080038000000002002800801c0030008000004000001001c0040110008008000004000807800c024006000800000700400000
  | 25 => 0xaa517e0001938256b9b7454b700004b78f5e2d78d8e72142293173c81bbfc1ec9cfd7bc3924487b557cc266602ce9400064432400018f25a500000000008180001d2dcfe0003d6a08dd80b5800000011120000001a616668ef0130b1999a0000000a08009000000000c001001004400200000400180020000008078000000000005000001a000009000200100a8090006012000000c00e007000000c00000000b805801c000002802400000700600180080010008024008001002800c032001000000400000200b800000c000000800c04000000b00140080000008000002010002001c01c003000000003a00a0008028000001001800000a002000004000c0080000000000000000006c00c00e00780040480010018000000007000800400e01e0030064018009005000400a00000080200000110008000002000000000c00e00100280000020010008000004000000000003201300000380080000080008000007000000000000600a0004006011002007800a007002000401a002000000800600500280000000050000004000002000003c00400900b000800000b001800000400000000040040060058014004001001000800000e005001c002000004000c002003000801c000024006800000600000480000040130098000000014009000000000700880040100040000000000003005000c0020270008000000002000000000e0020000018038002000803c01200000b802c03200f0020000006000001000c00401000100c400a0070010004042002001804000a001000001006a0000008034002004000000400600200e805400a00600a0004002001000806802c02f0000038000000003000c01800900500100100050028004000003000802401c004006800400e002000002c000001002000c0000000030020010002007801c01a001000001c00c0030038000012000006800000600600c8018000002000004400800700180400040000010044000000000000000200100500400080040248054000001000805c00a00200180cc000017000000400000b006800000201300080280000000080014006000001800c00000000000100000040098000002010000004800001d00a80180080000000040008003002800000000c000000001a002003000400200100980180040000010048000004000000000a005000800400c0000010004002005004800800000b000803c014000004800800401700000040080000000054002003005803c0020040008000000008013801403c0010028024006000001001801e0050000000014002000001c0020000040000000001004000c0140010008014014000000800000000c0020090000005001000c02c000002000000200f002003400000700000040100050030004008013007000400000000900280060020
  | 26 => 0x1c18b486e1b678a548a641a8dac198c656984d6113ea30022f36c0000000c4dcf8000cfa02304fde9257b79cab200000000f5a44d1410d24d51149c6f0001f03cc25a424a0000000055630152834b32e0003fd000000069b5c2b0f5c26a640290dec6fe0bc29563b34681856508e300009f400009c265700000000009ca00007180000000001832a680000000000001ad801d46d2407e063fa41800000000000001a44639dbc48a837ce3635a560bbc5d1ee3a72241f0eac5dc01d6bd00007bd536606ab4bbdb000284c10b00000012559504ab74a3145c7161f39102052ee0000d4aeed01a0006e309b0228bb8a9f095c0430002fb8000000dac000000032600000000d8000ea13ce8001979b950980fb570200000000014830006a6812c00000042f80000001bfb7e000000000065a40000000005a3deec0001d30000001c4200000000000000005c1302730a0f93b08103c660d66426da17dc53760d201000080f0001b59ad238100031640000000000c3cc86d9a0001b400000002934d3c00032443100009365a622a924d8e600000031c000000000000006f7e40145d85d06670000031c800018a44b658dbb225800000009040f2775b4afce8abed4bb749874ea000377547f21c380a91c55682746f256aca7885453993f454f1dcf7b22f8852693d475c4d5d24905d00001b725855f42e6c5784e62b40b7d8e885d0422894bf2000000246000081b739aa100006b0555207137a64f3c280007f60dc8000000e987ee291b121a023f40000000000b7d38e0610c740002df3521de44ba0001654564cf431293344680001c5d5e854c0002e0a2ccf2c00000000014a800010b8000709000000000021d32f00004d40000006f4c0640000000000000a4e0989f5000142e8491c7b3d8fb878200010dadc20000000000a625786890000000ce455245e80000000706bdc000eec00323493460001a5b14e2aa0004d8247c5ce67843817613f61e520b0a4c6685da4f606d073eb0d74f8e096f637864c84f5b140004c89f0d23cc4e31a0e18f2eb838001803aca18100000e760e503390a2d0c36d501c8981d340395217340cc8c295472b29ed460fc38d24e19bae2f2c6342b15055c377a050234d8f55a876d0fbdf0332ba2c51a789739738536c6966e1357c000471e971dd400000044a863c00050a93a91b40007a88a89b9dc72cc938c8001a72ae20002c6570600053d92bf42200041eadafa34e423fb389845a0001ef919195d00070886a982876f598aa396705c6126a3c8a7b4da49a07fcf50aa576cac281106e51e9adb45f674055c179135e4abebb9085764a57874ad157c6195244187162283c425329200065a0000dbe8ec3ee00000000006590000c1ce0800001fdbf89b0a56d5b12c03cec9e63427ac81fb8e000031dbdb2b471e3
  | 27 => 0x1c35e2a0005cf9c053580000e2d86143784f80027e8000000093a345e0095241d8000888f4c14e80000000000074000c3c0003e010d45ee9ba2e605e03b22390000f50b583760000000000025800000034615c00000012fc00071f476e0006f4000000049dcd26fc04c4ebc66100024fd69cf4e3b400000002858002c3db360000003d1800074700000000000004ac0000ba0a3200006b078a0002d380014486a62f19715afe61300022bc0b400000028fd1725b580029285e0b9e05d831400021819e0000726000021f1252000b32282d540000001278f5472e00034f8001080ba16292ea90c2d018000ca976634c16e899c9630861e92a0c000a9c48713b03c30003848000f9c00073cb74c86617c0000000c7224536ab5c06628603400000634acc18f800000003ccb81328f068f875300019d0eb9000295d92a586282000104ccf804f0f5c86ec549dd1e4c00026a57401057e0a531e806640002b641524a0ba623100032e5147e5256c2ed0db400020280012600005483081a9672c1dcdde400070380000000004a78003b58000ba1e61924a000d925b2a3f85068f96090dd5002c83073c1da76c7495b1a1dd866f2555180000000002fa00009547591c35e48dd200029a35ac6f20000000001a6adc128ec000000479000213c0009a9000000000000040580003a027e00000000001750000000000b1f000000055aca301680002d2b5b6c38000e5a0005fea922c24e45326a030000b770000001cbe000478083800035739b31f8f74e281771fb02b2819a449c142e836311f3894000ec624b297043ad56447abb11bc1394b3964c9dab0c76522219901f777aa94160c5fe0001a120caaa900021e9c3aa45737fa914360004091ad00008c000024480003279fe875cccc1875e68000000dfbcd320c80fae8861e18a982238d4f09f980a091880000000000003451ce872901e56890492ac63e3338e512920002900000c37001cc12880000ade69e95dd805bd26371c940007b237bbb3c9164601399c798de221ab1b6340000006ba92b927400006d82ad2bc3506e02f652060004148b3cf681e61778a64aaa00042ff3e60007e162a22b506cf0a60c9e0429a1b300014fc0001894332d7d8cebef47a2be557609780039317aa000103f9299456cc0002409e4282000028e96c4a670002f2c00011923c011c0007910000c8be9000556e02f8000cec0002114ae87cf0ce0bfcce80001c293e59c6a4900525a943cbad7892cb0000ba70001a05e9a05829c88d57749980000000d548028001bb4850909e09adeb7c400038927491300000002c9400000018f000000012a41fa18b18a8fa3443cdae469545e38000000c5e44aefc9262e961ff9a79b6276a1c94000000000627ea6406805d0000000abd0610002ca4d240006c88000000000259c000000
  | 28 => 0xdf217580000000004d9b0600000001020da0000b6f5908000092ca04d68fb1a1e0005bc8139ccf0001927cf400099a52909c90b28c9000385a0767c533402653f01e807e6a88c4e3e15492ea4bbe00000000000002464698001ac87a376131f15621cf87028e57ae0000ed0001282f290039b153bad57d5d20bb6685f020c1d9c4a283400009881ae4b300014b1b48290f1f1dc91e10006a2af3000000006c000081200000000000000000001e680000000000001b0c000250bbe40ced5d7170636000bc064d0a5197c0004f1ba6c00094711e6168b200002de80000005b400000000000000a6000000047f6fb8a3f7da00071ed300faaadf65bd344000a7a80016a400051cb29056d02039cd6aa3f11b8c6b1aa0704e3e6c274c1e6c9ae5541008681444ef82343784b48284d910f1617e14425780011788675e41fed24a6cb6c625306f5c554121fb47329232ddb5e961c8ea8657c18ca88500d6fcb066dc4044be01545e40c00004041260001f7a7b46cc00041799a9926ad263c2840610000285c000616de000039900003c329810f4647c45716665893951850a8000a0fd0d342c0000000000001e7c000ac19d80000a98307e81d3a800000065c0948ea6a769c3c1ac00097349700000000006f67761adc00000000000406715478e570f804a32bcb00fbe4d500000000a20003d14000d42c320000896c064ee000027200019a0001f04000afd00035cc0001243bb80005d8d2e89bb4e83f46ad6e591048cac50d930000000eee56500007148f98002899b288f357aa96e000e1b60b8001d70000017b5600009c45bb3bd00002140ef0001709c0929b0001d6600008c1b4c00028e72eb75c1b200026a17bed76c0e5ce067d80fdf95b3362c674cac49b800116c1c60b21078006b8610315d80004dfab364a822acd980000005353124c69e1a00000000000000003890f620e134a36c62193a5d76def429800113dec900003c0000000000000000018c7968001c55000329c0001daacd1d100019c400024281fc00000000039a800011100000009b67ff0003218e5435600021ea1060006d58e697e25ae057ad5700c00059e800167e0a348958c9b3e0000002f454185a05da97755507766258e32f4c3b24491d45c9c017601025ab023f14a00000000c16e323571c8ccf35d734c40000005ac87f27212f32f7201c0000004ed9e3c8acc8200006500001fb0002e1068e00031d7481bf6ddd685a2145500956f300008e4d1500027b897221b41681bcdfac0613788ada250002db0cd400000000000000366a385200000002ce0003b90f7892762dc60cdc8658ae3b3ace780680001ce00006b213185283f000026f891e4501cf13a4000000126299219e3da00063f9900000afc00029054ba8ed2792bc09084911ba0001d3a067e979db016de24800
  | 29 => 0x28000df29b229e94900006902eb9b18089ab076b893e6fc246acb00000000000000001d205cb5c8000029c0004d8b8b0000000000166000000000000003570002679d808b42c4046000045c00000002b93e091c4318a79170a6d0000000034170325000176c436000111c00010a6e8800040605e000104c000cf00001c2967f3e42b6a664bce20a4cf38c600033d70a8000000a516862728c6241f1934000ffa0000c00000fa86790000a3248800038403980005a8295816db7c00027c29e719c0000001b5023e000000000026400054041e80000001373bf16b491d1eb1d49887b56696a3a0236c960000000000a3725f01432a6c57ef600880000004e087b8000ca9087863413a93600000000000000003ab47d20000000001c3cd0980013f000042558000000168c2000113ccb61ba0002bd9b66446000000086855600038c487000032f0f388b8a778b5000097e49d00024bfb7e4c948d0a8c0001906c7345ccec389d3b1abce56330663106c0003a00000374b78b493ac2d1a78465291f4b1c2082230001ed4000000568c001688052d19a279d64711000000000000008bc00000000047e40008748eb00039ece60aa704d30407d6d48ee69568018a2d36e9fef5882d36388ae9c44d53148cd216c80cd62d2651d34dcf79c68187883434788021414b7b83f3621c0ce564ed0870f9a07600facf3aecc26710256c127d29652e1b55cc0003b7d7a0b2800032e3c0957900005902404d6c751cf2087a866b34f221a07163be17e1674ab21f249e36600008413c331e8900018c39a02855c56ce609e94000037e0256bc36e86a1a106f06e6707e88a49800067b0858001888b408000000000ac53fe34b1bd27f300022636ff3673c5aa80ec600066800000000004bd8500000c4a0001588d9a42f23d800122900031aa9a503a000743900887100006e1d940002300000000fc800000000000006d90000815c1a7280002983b2e000000000056e3a92970920f0000074886b400000034380006d4000721b2508a2ae54a2bba90e20005ea0f6807b00c8df1af957e9870d336bdcb694d00022713729a80b0bcd0f327af1c18c24b1e60b21d527149e3ae5ebc8ccba2d30304b1a8a3d47a0000001ac01af1ff3057db402e490b957dc61631c754ff5a6d14550e63991a0002040c959febac000230ca16d1f5682ec0f7c0003ffc964372c1f294a33c08d000000336502f62d0000d00b16000470379a0000a0800196166a000620a564ed20002228b55c6d00071e7bf9be3ab721f82f40cc3e643790c4000b612893d2c9e005400014d4a0cec707cea05aa200000023b00000000ab85f80001a25e70000c845384c20391676eab21e00ceb724c7000309400037a000000000000000002000004b75342402d1600000000001ee35c00003e814e4d00002acc00
  | 30 => 0x83a2b67038b43c01125a12f4c3b8000572000000000064480fba1c9713b33b41a562b813e0480d2e00045920646669396e2a8faa94292aa32b64000f24278b7f40000000000000000e1f7463b700000000001815288754592302d7ac000648c0e0b1a4f31fa8b44124ae5cdd862c26c9572908895808f31e1340000000c000032f7a9400056138b6fd4f1e5f0000039600000000011c20001862e21ca855707d95f09702af3e98ef494e5b009a02b005207004a3c4c00024d8000b60000e55284800090632d00888c800028b18a00007c43db1139b89836f10125bd0952a003a2bbb602d67de0313d1ccab0004df98b1b088ea3c3fcd9368000000040d57c0005b3aa0000025f6ff4001a8c52ef2557c4b1cc534c4b825cec6ca0e4c0019440f3171000097a0005883b7c13e000123a7e45d41065591bc816ae081049db83d4f3a0000a59ae85aa0003b451f19df2740008511ba46840001c04083a6eb7f07768c80f7800192d0000000001624000797000000041088e0000f4016e05de1319f858a000000000067700000c0000e6614b83500001f01320001b6acd747f6c24000000037000000000069a1261bc4425b0116c7ac45c247fa310cdc4c6615045d7f6cdf2b63a8d2ec93d14fb4d96389dc58f09fcd921c32ce58582500000e04000000000300fac0ab07ae353b00c848bb805cb1700002f50002994828f080000001848a4827d33dc90e60a00022ac23a0eb0e400013809ef01f38160002e56172d236089e93a3087d9d423d943395ce620e20002b9d9480000d5800000000062ea41c8c23c62fd000000074129100000000002f25a5599600004e25991a88eb80002c115c6ae000000000000029dcf13bf5c773cc2c4d120c9f800168c0000005152109994190a700000a500003123b78000178d388000000000000389f0070005af2069c880005202a245519b700018801044ef77325e80003b7291c0019169d578b36d9980dae19610112d0c576ad02581a63a62ceeda85f289969c2af60372566f851c19842500e4a5184ab255328883435f5ed110abcd77ae6252c96b49ee8873aab2f1a4ce511c015c545114969b8bf91c8396251b2d146c58000031a45aeba81beb001aae470eb887f02d352db9722f43b01f65a593d9d544430002e98de213b0000c00beac2c0002e1c1d7193ce62330000b8f674e281d964248e13bb40e40d511323ec692c473e8000000073b740a258ae093e18c25b549c1792cd814d41600000000000000004f0000165cad76260f30ee812e54a360d09a3f85c2fbd21bb3595162b84f1318bc3600005c2d251f3b8a40000002d90001872c4d70800000000000000a818440004990001cd88ee00000002580002c8b1857eeba68000000000553344f7f91608e27028000e68f2762f9bd515272600037d39740002b
  | 31 => 0x661e5568e9786990000cd2c1e5ff380ac1a7480e92b1cd7e0000b6b6a43a77e064e8000cfe3f073d0001ce15450ef544559e0ce1100000000a0100451acf44dce6dd9ae02cae28d6a05b60005a480000b1106deb205176c000253800291c0002072514c05c76000000259400000077f968800000000006edd3c8d600015d52faf196ef33bc84600016d37400000000000000480000777935865610b80017e0000d6a525c001123000734800147a00073880008800006802e593a850e5dca2191e3334f34340953e6ec452000000015e19729990f278771f9468000000449eaa2470d895e08001114c385f08000000000000041400048c65ac00000067e483229c0002b9000000000082f81bb398948d811af80002663040002c05cfc47727f32774426e60003c05a1b03c00000000002223e939e0e94211000238cae44264ae91207b8094b42b160486000323b6f4e5ed3b557136430400079bad719f67ca53f00019a80004682d440c574f0000e6c04d63369f39bc0006dc77480004ad00045b80017d47a1e8b0d8562a7b6752800058166003c8da53441bd1a51388000000052800010e0005e18d114880256ef8826000be470b0a4e0004b448ca8e1bea8c6717d5f99bc7c20003ad0000db24a1178559298a7a2851c1c525dbd58695be644224bb79d8f660005b1268adc0005258d54a59b306a914210f915d00031564b32a748554e8b7499d5ab9539ca08cd5e493785604fe80019f59ca47e66e6b00a2aaef6a3950165ea7d0002450000000361800106e0002620001174000000000000010d000000199c81e000000000076405401200007143c71ea80008e63ed15fc8020004158000d65afb393800005d00061580011b65d90000001d380000b8813ab2e0de6e48ecd55e6e0450aca88cc4595b48f069b82085170dc8afa0005c98b24000000000359800f00004440000005c30000000000768da92fcd80d0000001a80000c6dc74b69532a00025e2a6d778ed23608dc607a0f800030c40000d8e8200000d890d00000000000a9502c000c1e86b71357a80000006d1003c0000001618f56cbe5219d7bcf8000e41132b369bac00040c5e400a38521e01789412d077a500846448f71fb9749572e6d4238000b42bb14c833f485a0c90001a955ba22c7058bf513aeae5cbb511b5000013d8000efe4272a880000000001ddf5e054d019c07013cb326ac4e38f5f52cd4c189891330c2b1000116d7fe76b61d6c600000388000000000e8d00003674308fd409940bd8a55b74200007ec63c0003b7458248159f00000000000000000000000000000050e8a223a895e34200048d800177c2cd6a09af09c600008100000000000000728000000338000000000000011258ac000502800000000062783200008fb8210000000686647e4a400000007423290
  | 32 => 0x1d7897278e00000000000000000cde1d6a8c8000a022bd653000000062f00000000002db0000001951b4028637b800062153f405fd865068000c0800063b00027fa00059f0488000cc8d80046b896184000526c6bb7cab5338e9a2e362f0d66380000000002afb2b5d32864000000004e0d5adaa45e838f231272dd49a4b4a11481e0d88dff0055524482d79488cd7846c9ea2b3320ee4098f011912c0d23d84f416fd29c5e57990c6cf585de2548001902db70000ca550445e2dbc1d5e342150843c6cce6b6b2f3232c51b6383fc00000000000000001744000000000000004300000000001e10002875b4690b6385ac29c39be67392298e7935174958446e672a94c74406951f2b52a44738c970a080000003c81fe15e51b0a3b7828b512d200000011a966c4c84e9a1198cc29df879a4c0000334ad1130efc81761400004260005ec2cac0dae5e0000000000c7480b000039c0000001ff800000075b37318520002a8078903776200000010390ad7268040a6784322692955f02700753d3c00000000000016f984823600002781980003a5c000c018002984000717386159d74a724573626c0001cd000000147c00000019400000000000000000179800310800062e496909acdae61506ba55bc621e12e1e796a0c9e8e14e8c0003700000001c542490000000000000721c000cd80001964001530ac300023d980a00017218400f32f862da0b000045d0644ad400000049740010ea01200003055141fd650cdca000000178800000006380000000008aa1ceaa904a51546f3f08dc64382aa43c310ae20b13b3a9d42cb025378a4152675c3bdb6b44a82ac63de1fb3363511b01cd5ce4ebd0f492180008ed8b54000000589543b3b83db8220f8ac8c00002b2088163bc88ac30211bc928055b258a060009de0bd85f4000000725bbecf880b43e4800175e7d80000000c6c40356580015e24a60001a720006fb800000000077140f529a00000000000700006a200000017f00000000001728000140052c0007f45e28d6c1d53d39b127c4000e3800000003f7e8640490c9c249c952f1f5dc1cee107780b721896b2e413857d607167c4d749763bc09683b19647f9617b578b296ce207800092423f00030c153aada05c3c4481ac6c2dba3a69f60b168c17d741009744086c8ba85a98e39b217125ca6b6b93c8603284f1097b71a0004e88001b6800000011f43e90005cc8cf848b97f0e54000b1032ed93800096527a3c6250dbf189a2b9a809c06c79b2b8000858b4f782006a91e00014414da00000033d00000009f34c5a9c07870002b20000800d22513c00047680009f0000b436010002374000000754132c000a5b43d988da2037c30eba0150c0000003248000911000030d7be9172c9000129e49e43c439c5444eb3758d4c0004a26
  | 33 => 0x1a869061ce935c60e852511c470d2d133f8c6d66b00002864f5427048c613414b5d000079640e76400c4000f3021018dd7163bf30400000cd3d2a39e8118a554f1d20000000e8576994a2832aebcff2cc9de075d46c87ff4981fe062107400054468f0000bec00034200000000000000ee5ae400004c32cd356000401800166e8720000a046da27161f9fc00003453780e1c0002d0117800000000065c4001c1d1671303a240001928003a485cc3a843f9c58d040000001aacc18e344461c60f1428c4c08440083e0444a2d055c6b54165865766d09bbe39fbd004f1453bb059cf87cc28b10ac14c7db71a8cdf3e4c9c87709f4478a538003980d1b7f6f9ab1d82ec0000002e44cd6e6723732a8950ddb68d86483a800054f335493e0000000000ebe168711afa400000037d80000000f8b3be19562ed850000438aebda139e83f53ceabc1421f94bddb7426ee4b0b3424227a0c3401f0002a90100000d4200019539470000000001a4825d560660d93e1962f98a272760001908f1c000000500000000047400016095f400066dfd0d099499604383c67e5fc53f9854c34298579161d11f9646be0b70dfea791ef00013268c16e415bd8b10000b912b56f436f1dc306609f0fb87a8ec4000584eb196797840640000424529e7071bb028a260005e78b814b91257700046f7e000000000138ac01258b09c00022a1b89e34d060000001bcd78c50053905c204848e3e8b890e9c0000434c64fc47b153c26d40000397510001a7e0006374385d82317799bb6dcb085e28daba983a000794022d86870e2374000dbe0000000000d6c0006e2252c66e68880000019f20000a900000006940002daa00037090b14cdbec96bb60204431cced3f59b78000000724a57028aae054683f8000b60000018151000061b183918e820c7b6ab4bff1974326f43486c8742b3c2c611a4c96b2dfcfea1cc6f412d455629a0003729050cc4000083a00000032e80019ea0000003484661000000382921720f48480009c88840002e2811cb051993d1000000000000009a34150eb26e20004c21883b38a6b00075ba6848a63f202f9fe233aa0e000028020e7c6636436ea8e98828a00000006722bf70f800085b5360aa40005678003c74000e7d6950000abf0145be06c0000c1c1da80000b8000199e81c000cb717a01a920a50d2e006535dc08a70c1cc954f6e84f30afbafa2f25f3abad4f81134040d49ab69e55bc000000051d044930c11b0562d8a110000b28192cb8d2f89101e15f2000086e6078000270d9357fb4756e60dfba1394d75669a3fd483112e4aa934a7f4eda1bf5188034fb2277308a412dc62c559e1be8f4eee2344942993683910072ac31f129381bbe852203f071c5fc1a9bd980027fd94a08f00032ed04254d705efe97d80745300c80ca66752310f3c
  | 34 => 0xf1621b56429e2e00063cfa09aa1a9c6db798a09c5420005859c2c98a0000b9bcbfc289b78a7a9d4e881500221366df04e700032b82442bb79001ddb4097978fb9dc782b6e4e79a30ef4b46367ab6d03e0ba51a821e00034e65827d400029c42c3221e1c5fd3d4c6aa4f21862095206000517603804b208ad66ee0137bd4000675552d3181464a884e800015a509000000041a00036c0fac7e3638fce11ea08f9451409ab2e6519db140feef2a044e850b9a97434e8d0539ab1a1c9c001dd000012dbc06872000000219632251e0001ea4154000000000000026d015c000f0867c3be88e800079400017c9d6ad33710f05557fdda134094d8180000000000c4400000000019b800063afbdc3100000000001e784101ee9755ace0006c12690bfe8df7000000a864b6287aa15e2e18cda60ca20009336f8b9d563a15300014b574690a3a6a75c7e6d6f700b0dd2400006fae1d81df70f1d51ee5d624545fb208b0d2e172dc23540006d747d7210000148331353c1b4de887640000591dd4b098fc000f0965057b102c0003bc00008b0e3054580040006d83999e20064efd7138c44193e15ab58b21e4c5e91d63b35afcc8f17d0eb5dcea740d672fd9184072c227ddb4e58364800000001f577961f8bf6975002f964794a6f959adc0e86d995968d95478383a7fb2b33a01f90e0371cddc9c208f37e88ce36e15f33c40000001e6aaac71ca4d473a89b57a1f3022a588000c7d000000095896f0000a9064c000347aefda12aa60001edc5d088d23e02339228a180033a400055d0c473f96fc507000024ba806293aba457a5000072d5f2c00022465e8000000000000000105c5100002765837a5500c15e6000b8021f3970000b3950e056000043b412635cd1c000246b52451e00078c078da781b60e284580c6a5d8b60c2988c64500000000000005e5032c0002bf03d8000000100524e0f9d06000495b9ac000090dc92bf8a384cc5b8b796f1b7155460b302ee4730d413fe69a9cb22517af3004b4a828bb41ecc35731940e4bc8a31b9ddae9405e06aa8e21d7ea6b22704bdd58000346b65865b56055628a4da2b722349b1d33869c6b0804d104cb1068b3c8d32278693ad7463a59c6310e16b92000000375066b56973705bca8496063e431800000079100a8000e2b5ed0968512055000027e7ca00000014ec9820004978c55788b4d1dfc00000099f49100018c6000418859e72084b002381c0008a53dc0000decf02c5ab270edd1dae8c90d65846a94de36740008a7f6600e80005eb43c1ba837052f07887ce0006490001fa41e800053d0000fce085590071a000e2b8000024000b140000000000f2f12618f559c9164400001b54a62000000016e0000000000000000000000000000000000016d900002ca0940000000000000000c803880328000000
  | 35 => 0x1864e0495000025b0c980004eb0f8d17605cc0540000000000000000bab64e3be0aa97bad0a0000b78fd05c41e88484a4a7f244580000000000001d4000026100000000000004a4252800048a9194000f606b51d5b34585a0a1000071f95eda643b51b7674a232736c6cf486ffcd3bd00c829b82e71addbca663783ae06768a6e79f8036000dffdb6246efe2d9065b37af495bdc6f54922d48a2744896cc670a0350c877cc283c970c905d9299016fa195447a7070ea486435c1f425910876067704fb341548c296954f2612480000002bb5d5e75b7241b4850aebe6628755ea08742eb348d21e010f412e9e2c0b9a2846738c5662814db6e82bed9c2b8d18dd1c292531a154ee62105cc224c6535eadfaaedc1fee3d014102d4b4e4700023ba00004c6dc2720000ef35a1c00000000010026b80003770b10d18000cb506780013b0057165286973a0d053e7cd7542eba0cf257c62c42a00035ecbdeb16203295800042241d0c0d0a2d68000000001c000683000034e00000000000001e46471ca400000007298980004ce1b20393210bd03ee8fa05ecac611d400000015600000014b000000000012073230000000000d54086334c000000000117dd146bd33340009a6c8a000080809a9c30002c20000c0d0000000000a286a3fcec000f2b1d3a9a9cb40000000000abc0000000000c0c00040a9ecd11c000073400000000050f8cd8f4233190d026d324a0f0e84c158c00007623b940e69553ad028999e7376f6b44cd7265600027194be0004b56fe43ab38443e88482cc706358b29c638c210003361da80003ce387195354116c80004b5d1c5fa04ad876000000365548419b0c546fb211b431cc000000085c19c822
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x542c8640a8880591320c940a2581195424c840a0d831894254440a0d831915248440a0d831954248440d21725444190040a25821855150040c32765474150040a0d839516210f20a0d8494d6210f20a0f8550d6210f20a0d8550d6210f20a0f8558d4210b20a0d8694d4210b20a0f85591320cb20a0d86951320cb20c0d735ca64d4e20a0d821cd6494e2081e879954310e20a0d839516210e20a0d8494d6210e20a0f8550d6210e20a0d8550d6210e20a0d8395162d0620a0d83d9542d0620a0d8494d62cc620a0d84d9532cc620a0d839516210220c89431c16210d2090d839cb5450820d05739c45450820c26765c45450820d06735c45450820d05735c45450820d21719c05450820925811d74350820925811d54350820a0d825516310820d05749c4534c820c46765c4534c820d06745c4534c820d05745c4534c820d41719c0534c820945811d6434c820945811d5434c820c0d645c9530c820a0d831914254420a0d8418d3254420c0d545cc6250420a0d831954250420c0d7454c624c420a0d84195324c420a0d839914294020a0d8498d3294020c0d545ce6290020a0d831954210020c0d7454e628c020a0d84195320c020d21745442188020d41735442188020a25841855148020a45831855148020c6276547214802090d831c95450b1090d831d15250b10a0d83d954210b1090d841cd524cb10a0d84d95320cb1090d839cb5450a1090d839d35250a10a0d831954210a1090d849cf524ca10a0d84195320ca10c0d73d8a62d5110c0d735886215110c25625c46215110c0f645ce64d4910c0d74d8e63d4910c0d645cc6414910c25645c46414910c0d7458c6314910c45635c4631491090d839cb545091090d839d35250910a0d821516310910c0d7458c5210910a0d831954210910a0c8558d4210910c0e7558d4210910c0c7558d4210910a0f86d4d4210910a0d8614d4210910c24755096110910a288550a601091090d849cf524c910c0d645cc520c910a0d84195320c910a0c85591320c910c0e75591320c910c0c75591320c910a0f86d51320c910a0d86151320c910c44754c9610c910a48854ca600c910aa1821854150110aa1841852148110ac1831852148110c0d735886295010c0d735886255010c0d645cc6494810c0d7458c6394810c0d645cc6454810c0d7458c635481090d831c9545081090d831d15250810a0d829516310810c0d7458e5210810a0d83d954210810a0f8558d4210810c0f7558d4210810c0d7558d4210810a0d8694d4210810a0d8654d421081090d841cd524c810c0d645ce520c810a0d84d95320c810a0f85591320c810c0f75591320c810c0d75591320c810a0d86951320c810a0d86551320c810a28865506244010e095418c6244010c28761915244010c487618d5244010e086418d5244010
  | 1 => 0x2d09701c1535084290e8754d615084290c8754d6150842d0953dc16150842d09531c1615084290d859cc615084290f8754c6150842d09539c06150842d09535c0615084290d859cf605084290f8754f605084290f8754e605084290d8754e6050842e09535806050842a0d831d94254442b21801c54254442c0d735086054442a0f8654d4214442c0f7654d4214442e095350a6014442e09535096014442c0f7654d42d4042a0d83dd94294042c0f735096194042a0d8694d4214042e055350a6114042e06535096114042e05535096114042b0a80d954350932a8a80d91428c932b0a809cd544c832b09809cd544c83290f845c7654c83290d849c3654c83294a809d9544c832b0a80dd9544c832b0980dd9544c832b0a809d9544c832b09809d9544c832c0d761d9544c832a0c865c5544c832b0b805c5544c832b08805c5544c832a0e861c5544c832b0a801c5544c832b09801c5544c832a0e86dc1544c832a0e869c1544c832d09701c1544c83290e87551614c83290c87551614c832d0954dc1614c832d09541c1614c83290d859d0614c83290f87550614c832d09549c0614c832d09545c0614c83290d859d3604c83290f87553604c83290f87552604c83290d87552604c832e0954580604c832a0d841d93254432b41801c53254432c0d744c86054432a0f865513214432c0f765513214432e09544ca6014432e09544c96014432c0f7655132d4032a0d84dd93294032c0f744c96194032a0d869513214032e05544ca6114032e06544c96114032e05544c96114032a0d839894294341c49631c15214941c0d645cc520c94184c87595320c941a4880595320c941c0e75591320c941a0f8558d4210841a0d8694d4210841c0d645ce520c841c0f75591320c841c0d75591320c841d09735084294041d09744c83294041d09735084254041d09744c83254041c0d545cc6250721a0d839914294321a0d8498d3294321a18805516315121c0d735c86454d21c19641c15314d21a0d821cd6414d2181c875954310d21a18805954310d21a0d831516210d21a0d8414d6210d21a0e8550d6210d21a0c8550d6210d21a0c8654d4350921b088054d4350921b0880551434c921a0d8315162d0521a0d8414d62cc521a0d839516210c21a0d8494d6210c21a0f8550d6210c21a0d8550d6210c21a0d83d954210821a0f8558d4210821a0d8694d4210821a0d8654d4210821a0d84d95320c821a0f85591320c821a0d86951320c821a0d86551320c821d09435c84394021d09735084294021d09744c83294021d09435c84354021d09735084254021d09744c83254021a0f8558d4210b40a0d8694d4210b40c0d645ce520cb40c0f75591320cb40c0d75591320cb40c0d645ce520ca4084e87995320ca40c0d75591320ca40c0d645ce52c8640a0d83d9
  | 2 => 0x126646c4325809174c40cd120007a18aa290400000b335400010f723cd642d04048539589c08c8280069414d43f852820ed1d26d0007caac6e148c9264b70000000000000a2470982e4272830c0bc00000a80d000278003f0f12b295000000f0482b4869942d28e47006871ce590004523006000711fea4118033eca8800880000f068970000000000284ab80098b94e24582e128a32d88e41cde2a8da000243c8002b8b8060dd2190a000000c000328890000005000000001d87e80000340003300006ca9398003351d16000308ce000e800000170eb1aa000005300000000000002a2402209400ac0541e0e73cc29468e0434ff2c90200000064610286300017444ac24c4f2d4003483b19c9a3e8c031c0029d2200000000c10149f800bf1540e36c000010600103204a639040210000812312435000832e913070718d82c37d081a09f0a0a00780737000480003a4b1110d932c003f4003b80024839144bb2744d3d8743c70e07c000007e31800000023bc313cad12504c000003a86c33c801dd1e00000385092f011229004611938c261ec323c11700000001012940014000188000005e004c50000c00000034ec000001d437000792149cc505b0008d4404217c00000f8206001427f47c7d054571c8003207c0006b990002448b0001d084381bcf41a8c30fc1634c2b0f870484af3601f8004b2f44e0e8821683d35cbe180733e4000006b454102d00002c1343cf526caa82c0603070540005000700405000040201000240a04008081800070045e060000400110000000000400c44020580000000000806080180000000000004050400800080283c24040281012020082002010380802020084408070207804020500008060600800000001004000501c000c008000802088002004b0a809c95350842b09809c95350842b0a809d15350842b09809d1535084290f835c7655084290d839c3655084292a809d95350842b0a80dd95350842b0980dd95350842b0a809d95350842b09809d95350842a0c865c55350842b0b805c55350842b08805c55350842a0e861c55350842b0a801c55350842b09801c55350842a0e86dc15350842a0e869c1535084
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 27
  | 6 => 1098
  | 5 => 6068
  | 4 => 3921
  | 3 => 292
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (i*5) 5
  | 7 => packedAt gbK7 (i*16) 16
  | 6 => packedAt gbK6 (i*27) 27
  | 5 => packedAt gbK5 (i*38) 38
  | 4 => packedAt gbK4 (i*49) 49
  | 3 => packedAt gbK3 (i*60) 60
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (6+((h/1+packedAt gbK8 (5+(h % 1)*1) 1) % 2)*1) 1
  | 7 => packedAt gbK7 (510+((h/13+packedAt gbK7 (432+(h % 13)*6) 6) % 49)*6) 6
  | 6 => packedAt gbK6 (35646+((h/500+packedAt gbK6 (29646+(h % 500)*12) 12) % 2898)*12) 12
  | 5 => packedAt gbK5 (265752+((h/2512+packedAt gbK5 (230584+(h % 2512)*14) 14) % 16018)*14) 14
  | 4 => packedAt gbK4 (212201+((h/1544+packedAt gbK4 (192129+(h % 1544)*13) 13) % 6117)*13) 13
  | 3 => packedAt gbK3 (18483+((h/107+packedAt gbK3 (17520+(h % 107)*9) 9) % 426)*10) 10
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfc1ff0f83fe1f0f1ff0fe1fc387f0e1ebbc793
  | 1 => 0x7fe1ffffc3fffffe07f0fe1fff87ffff4478ff
  | 2 => 0x7ffe00fffc01ff1ff800ffe03ff80fe1878f1c
  | 3 => 0x800000fffffe001fffff00003ffff001f80fe0
  | 4 => 0xffffff000000001fffffffffc0000001fff000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x54461098942a1005b0160249809225c19c391
  | 1 => 0x8000010000000000010020800820400001026
  | 2 => 0x50c8aaa290d54836a888b5412d5049c5868d18
  | 3 => 0x429d4cc522906a5b35aa11023664e089e80ec0
  | 4 => 0x631188863b198c9dc6ccd99384408111f76000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xeeececc8eeececc8eeececc8eeececc8eeececc8eeececc8eeececc8eeececc8eeececc8eeececc8eeececc8eeececc8eeececc8eeececc8eeececc8eeececc8, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_16185
namespace PEqualNP.Outside.L_meta_16185
open PEqualNP.Outside.L_meta_16185.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bgb_3_192 : Interval gbAtlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_224 : Interval gbAtlas 3 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_256 : Interval gbAtlas 3 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_288 : Interval gbAtlas 3 288 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 292 := (concat (concat (concat bgb_3_0 bgb_3_32) (concat bgb_3_64 (concat bgb_3_96 bgb_3_128))) (concat (concat bgb_3_160 bgb_3_192) (concat bgb_3_224 (concat bgb_3_256 bgb_3_288))))
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
theorem bgb_4_3904 : Interval gbAtlas 4 3904 17 := block_range (n:=17) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 3921 := (concat (concat (concat (concat (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat (concat bgb_4_96 bgb_4_128) (concat bgb_4_160 bgb_4_192))) (concat (concat (concat bgb_4_224 bgb_4_256) (concat bgb_4_288 bgb_4_320)) (concat (concat bgb_4_352 bgb_4_384) (concat bgb_4_416 bgb_4_448)))) (concat (concat (concat bgb_4_480 (concat bgb_4_512 bgb_4_544)) (concat (concat bgb_4_576 bgb_4_608) (concat bgb_4_640 bgb_4_672))) (concat (concat (concat bgb_4_704 bgb_4_736) (concat bgb_4_768 bgb_4_800)) (concat (concat bgb_4_832 bgb_4_864) (concat bgb_4_896 bgb_4_928))))) (concat (concat (concat (concat bgb_4_960 (concat bgb_4_992 bgb_4_1024)) (concat (concat bgb_4_1056 bgb_4_1088) (concat bgb_4_1120 bgb_4_1152))) (concat (concat (concat bgb_4_1184 bgb_4_1216) (concat bgb_4_1248 bgb_4_1280)) (concat (concat bgb_4_1312 bgb_4_1344) (concat bgb_4_1376 bgb_4_1408)))) (concat (concat (concat (concat bgb_4_1440 bgb_4_1472) (concat bgb_4_1504 bgb_4_1536)) (concat (concat bgb_4_1568 bgb_4_1600) (concat bgb_4_1632 bgb_4_1664))) (concat (concat (concat bgb_4_1696 bgb_4_1728) (concat bgb_4_1760 bgb_4_1792)) (concat (concat bgb_4_1824 bgb_4_1856) (concat bgb_4_1888 bgb_4_1920)))))) (concat (concat (concat (concat (concat bgb_4_1952 (concat bgb_4_1984 bgb_4_2016)) (concat (concat bgb_4_2048 bgb_4_2080) (concat bgb_4_2112 bgb_4_2144))) (concat (concat (concat bgb_4_2176 bgb_4_2208) (concat bgb_4_2240 bgb_4_2272)) (concat (concat bgb_4_2304 bgb_4_2336) (concat bgb_4_2368 bgb_4_2400)))) (concat (concat (concat (concat bgb_4_2432 bgb_4_2464) (concat bgb_4_2496 bgb_4_2528)) (concat (concat bgb_4_2560 bgb_4_2592) (concat bgb_4_2624 bgb_4_2656))) (concat (concat (concat bgb_4_2688 bgb_4_2720) (concat bgb_4_2752 bgb_4_2784)) (concat (concat bgb_4_2816 bgb_4_2848) (concat bgb_4_2880 bgb_4_2912))))) (concat (concat (concat (concat bgb_4_2944 (concat bgb_4_2976 bgb_4_3008)) (concat (concat bgb_4_3040 bgb_4_3072) (concat bgb_4_3104 bgb_4_3136))) (concat (concat (concat bgb_4_3168 bgb_4_3200) (concat bgb_4_3232 bgb_4_3264)) (concat (concat bgb_4_3296 bgb_4_3328) (concat bgb_4_3360 bgb_4_3392)))) (concat (concat (concat (concat bgb_4_3424 bgb_4_3456) (concat bgb_4_3488 bgb_4_3520)) (concat (concat bgb_4_3552 bgb_4_3584) (concat bgb_4_3616 bgb_4_3648))) (concat (concat (concat bgb_4_3680 bgb_4_3712) (concat bgb_4_3744 bgb_4_3776)) (concat (concat bgb_4_3808 bgb_4_3840) (concat bgb_4_3872 bgb_4_3904)))))))
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
theorem bgb_5_6048 : Interval gbAtlas 5 6048 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 6068 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 (concat bgb_5_192 bgb_5_224)) (concat bgb_5_256 (concat bgb_5_288 bgb_5_320)))) (concat (concat (concat bgb_5_352 (concat bgb_5_384 bgb_5_416)) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))) (concat (concat bgb_5_544 (concat bgb_5_576 bgb_5_608)) (concat bgb_5_640 (concat bgb_5_672 bgb_5_704))))) (concat (concat (concat (concat bgb_5_736 (concat bgb_5_768 bgb_5_800)) (concat bgb_5_832 (concat bgb_5_864 bgb_5_896))) (concat (concat bgb_5_928 (concat bgb_5_960 bgb_5_992)) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088)))) (concat (concat (concat bgb_5_1120 (concat bgb_5_1152 bgb_5_1184)) (concat bgb_5_1216 (concat bgb_5_1248 bgb_5_1280))) (concat (concat bgb_5_1312 (concat bgb_5_1344 bgb_5_1376)) (concat bgb_5_1408 (concat bgb_5_1440 bgb_5_1472)))))) (concat (concat (concat (concat (concat bgb_5_1504 (concat bgb_5_1536 bgb_5_1568)) (concat bgb_5_1600 (concat bgb_5_1632 bgb_5_1664))) (concat (concat bgb_5_1696 (concat bgb_5_1728 bgb_5_1760)) (concat bgb_5_1792 (concat bgb_5_1824 bgb_5_1856)))) (concat (concat (concat bgb_5_1888 (concat bgb_5_1920 bgb_5_1952)) (concat bgb_5_1984 (concat bgb_5_2016 bgb_5_2048))) (concat (concat bgb_5_2080 (concat bgb_5_2112 bgb_5_2144)) (concat bgb_5_2176 (concat bgb_5_2208 bgb_5_2240))))) (concat (concat (concat (concat bgb_5_2272 (concat bgb_5_2304 bgb_5_2336)) (concat bgb_5_2368 (concat bgb_5_2400 bgb_5_2432))) (concat (concat bgb_5_2464 (concat bgb_5_2496 bgb_5_2528)) (concat bgb_5_2560 (concat bgb_5_2592 bgb_5_2624)))) (concat (concat (concat bgb_5_2656 (concat bgb_5_2688 bgb_5_2720)) (concat bgb_5_2752 (concat bgb_5_2784 bgb_5_2816))) (concat (concat bgb_5_2848 (concat bgb_5_2880 bgb_5_2912)) (concat bgb_5_2944 (concat bgb_5_2976 bgb_5_3008))))))) (concat (concat (concat (concat (concat (concat bgb_5_3040 bgb_5_3072) (concat bgb_5_3104 (concat bgb_5_3136 bgb_5_3168))) (concat (concat bgb_5_3200 (concat bgb_5_3232 bgb_5_3264)) (concat bgb_5_3296 (concat bgb_5_3328 bgb_5_3360)))) (concat (concat (concat bgb_5_3392 (concat bgb_5_3424 bgb_5_3456)) (concat bgb_5_3488 (concat bgb_5_3520 bgb_5_3552))) (concat (concat bgb_5_3584 (concat bgb_5_3616 bgb_5_3648)) (concat bgb_5_3680 (concat bgb_5_3712 bgb_5_3744))))) (concat (concat (concat (concat bgb_5_3776 (concat bgb_5_3808 bgb_5_3840)) (concat bgb_5_3872 (concat bgb_5_3904 bgb_5_3936))) (concat (concat bgb_5_3968 (concat bgb_5_4000 bgb_5_4032)) (concat bgb_5_4064 (concat bgb_5_4096 bgb_5_4128)))) (concat (concat (concat bgb_5_4160 (concat bgb_5_4192 bgb_5_4224)) (concat bgb_5_4256 (concat bgb_5_4288 bgb_5_4320))) (concat (concat bgb_5_4352 (concat bgb_5_4384 bgb_5_4416)) (concat bgb_5_4448 (concat bgb_5_4480 bgb_5_4512)))))) (concat (concat (concat (concat (concat bgb_5_4544 (concat bgb_5_4576 bgb_5_4608)) (concat bgb_5_4640 (concat bgb_5_4672 bgb_5_4704))) (concat (concat bgb_5_4736 (concat bgb_5_4768 bgb_5_4800)) (concat bgb_5_4832 (concat bgb_5_4864 bgb_5_4896)))) (concat (concat (concat bgb_5_4928 (concat bgb_5_4960 bgb_5_4992)) (concat bgb_5_5024 (concat bgb_5_5056 bgb_5_5088))) (concat (concat bgb_5_5120 (concat bgb_5_5152 bgb_5_5184)) (concat bgb_5_5216 (concat bgb_5_5248 bgb_5_5280))))) (concat (concat (concat (concat bgb_5_5312 (concat bgb_5_5344 bgb_5_5376)) (concat bgb_5_5408 (concat bgb_5_5440 bgb_5_5472))) (concat (concat bgb_5_5504 (concat bgb_5_5536 bgb_5_5568)) (concat bgb_5_5600 (concat bgb_5_5632 bgb_5_5664)))) (concat (concat (concat bgb_5_5696 (concat bgb_5_5728 bgb_5_5760)) (concat bgb_5_5792 (concat bgb_5_5824 bgb_5_5856))) (concat (concat bgb_5_5888 (concat bgb_5_5920 bgb_5_5952)) (concat bgb_5_5984 (concat bgb_5_6016 bgb_5_6048))))))))
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
theorem bgb_6_1088 : Interval gbAtlas 6 1088 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1098 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224))) (concat (concat (concat bgb_6_256 bgb_6_288) (concat bgb_6_320 bgb_6_352)) (concat (concat bgb_6_384 bgb_6_416) (concat bgb_6_448 (concat bgb_6_480 bgb_6_512))))) (concat (concat (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640)) (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 (concat bgb_6_768 bgb_6_800)))) (concat (concat (concat bgb_6_832 bgb_6_864) (concat bgb_6_896 bgb_6_928)) (concat (concat bgb_6_960 bgb_6_992) (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 27 := bgb_7_0
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

theorem boundgb (cert : Complete gbAtlas) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 5 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero]
def fullWord : Sig := 0xeeececc8aaa8a888eeececc8aaa8a888eeececc8aaa8a888eeececc8aaa8a888eeececc8aaa8a888eeececc8aaa8a888eeececc8aaa8a888eeececc8aaa8a888
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 0 32) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,6,38)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,6,38)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (3941264072 * 2 ^ 32 + 3939027080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_16185.Model.Repr at out
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

def mono : List Gate := [⟨.and,[3,4]⟩,⟨.or,[3,4]⟩,⟨.or,[5,6]⟩,⟨.and,[0,7]⟩,⟨.and,[8,9]⟩,⟨.and,[0,1]⟩,⟨.or,[5,7]⟩,⟨.and,[1,2]⟩,⟨.and,[12,13]⟩,⟨.or,[10,14]⟩,⟨.or,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941264072 * 2 ^ 32 + 3939027080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941264072 * 2 ^ 32 + 3939027080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_16185

open PEqualNP.Outside.L_meta_16185 in
theorem PEqualNP.Outside.L_meta_16185 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941264072 * 2 ^ 32 + 3939027080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941264072 * 2 ^ 32 + 3939027080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
