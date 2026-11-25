import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_15135.Model
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


end PEqualNP.Outside.L_meta_15135.Model

namespace PEqualNP.Outside.L_meta_15135
open PEqualNP.Outside.L_meta_15135.Model
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

def SBf (j : Nat) : Nat := [3, 2, 2, 4, 4, 6].getD j 0

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

end PEqualNP.Outside.L_meta_15135

namespace PEqualNP.Outside.L_meta_15135
open PEqualNP.Outside.L_meta_15135.Model
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
  | 3 => 0xffffffffffffffffffffffffffffffffffffff
  | 4 => 0xffffffffffffffffffffffffffffffffffffff
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffff84b7
  | 2 => 0xffffffffffffffffffffffffffffffffff895b
  | 3 => 0xffffffffffffffffffffffffffffffffff926d
  | 4 => 0x238e
  | _ => 0
def s0Atlas : Atlas := ⟨2,rawDecor 30 s0Pos s0Neg, 0xc0000000c0000000c0000000c0000000c0000000c0000000c0000000c0000000c0000000c0000000c0000000c0000000c0000000c0000000c0000000c0000000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_15135
namespace PEqualNP.Outside.L_meta_15135
open PEqualNP.Outside.L_meta_15135.Model
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
  | 2 => 0xffffffffffffffffffffffffffffffffffffff
  | 3 => 0xffffffffffffffffffffffffffffffffffffff
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffff8b
  | 2 => 0xffffffffffffffffffffffffffffffffffff95
  | 3 => 0x26
  | _ => 0
def s1Atlas : Atlas := ⟨1,rawDecor 13 s1Pos s1Neg, 0xa000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_15135
namespace PEqualNP.Outside.L_meta_15135
open PEqualNP.Outside.L_meta_15135.Model
def s2K1 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 1 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 1 => packedAt s2K1 (i*3) 3
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 1 => packedAt s2K1 (4+((h/1+packedAt s2K1 (3+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 4 => 0xffffffffffffffffffffffffffffffffffffff
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffff8b
  | 1 => 0xffffffffffffffffffffffffffffffffffff95
  | 4 => 0x26
  | _ => 0
def s2Atlas : Atlas := ⟨1,rawDecor 19 s2Pos s2Neg, 0x88880000888800008888000088880000888800008888000088880000888800008888000088880000888800008888000088880000888800008888000088880000, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_15135
namespace PEqualNP.Outside.L_meta_15135
open PEqualNP.Outside.L_meta_15135.Model
def s3K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s3K3 (i*5) 5
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s3K3 (6+((h/1+packedAt s3K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0x5be0ffc1ff801ffffc01ff00ffff0063f8
  | 4 => 0xffffefff07ffffffe00fffffffff00fffffc3f
  | 5 => 0x73fff801fffffff00001ffffff00007fc0
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xffff802210882592a492c5245b4b4b4b6aaddb
  | 1 => 0xffff804421104aa4c9254a48ad959595b356ed
  | 2 => 0x249e423a937691c9931d37c0e6e61a6378
  | 4 => 0x1108f4211c471d8e2391c6e6c0f8dc7836
  | 5 => 0xe1087bde0781e0fc3e1f8f8f8c0e07f80
  | _ => 0
def s3Atlas : Atlas := ⟨3,rawDecor 55 s3Pos s3Neg, 0x88888080888800008888808088880000888880808888000088888080888800008888808088880000888880808888000088888080888800008888808088880000, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_15135
namespace PEqualNP.Outside.L_meta_15135
open PEqualNP.Outside.L_meta_15135.Model
def s4K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s4K3 (i*5) 5
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s4K3 (6+((h/1+packedAt s4K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0x5be0ffc1ff801ffffc01ff00ffff0063f8
  | 2 => 0xffffffffffffffffffffffffffffffffffffff
  | 3 => 0xffffefff07ffffffe00fffffffff00fffffc3f
  | 5 => 0x73fff801fffffff00001ffffff00007fc0
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xffff802210882592a492c5245b4b4b4b6aaddb
  | 1 => 0x245e213a4af689a54b1cafc0d5d51a62f8
  | 2 => 0xffff808442109324d14992493595a6a6b3576d
  | 3 => 0x1108f4211c471d8e2391c6e6c0f8dc7836
  | 5 => 0xe1087bde0781e0fc3e1f8f8f8c0e07f80
  | _ => 0
def s4Atlas : Atlas := ⟨3,rawDecor 47 s4Pos s4Neg, 0xa080a080a000a000a080a080a000a000a080a080a000a000a080a080a000a000a080a080a000a000a080a080a000a000a080a080a000a000a080a080a000a000, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_15135
namespace PEqualNP.Outside.L_meta_15135
open PEqualNP.Outside.L_meta_15135.Model
def s5K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x4018024424c728000b8ef32de32dc32ec32cc32f741be41bc41f441b441
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x80038140014880180000069080000014e528cb8865a0e30ca419b28c838c32107886420e9cc841cb190839432107486420e10c841
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x286628c841
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 10
  | 3 => 11
  | 2 => 1
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (i*5) 5
  | 4 => packedAt s5K4 (i*16) 16
  | 3 => packedAt s5K3 (i*27) 27
  | 2 => packedAt s5K2 (i*38) 38
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (6+((h/1+packedAt s5K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s5K4 (172+((h/3+packedAt s5K4 (160+(h % 3)*4) 4) % 15)*5) 5
  | 3 => packedAt s5K3 (312+((h/3+packedAt s5K3 (297+(h % 3)*5) 5) % 22)*5) 5
  | 2 => packedAt s5K2 (39+((h/1+packedAt s5K2 (38+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xffff00ffffffffffffffc0ffffffffffc3ffff
  | 1 => 0xc3ffff007fffffffe03fff03ffffff803c7ff8
  | 2 => 0xffffffff803fe03ffffffffc0fc01fffff8e3f
  | 3 => 0xffffffffffc0003ffffffffff0001ffffff03f
  | 4 => 0x3ffffffffffffc0003fffffffffe0003fffc0
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x804bd40a9149228a248ac02cb2d5a5b541b6db
  | 1 => 0x349515da259345144395cb015569ca8d1c5b78
  | 2 => 0x11264653752289a689275554098c9359ae8e2d
  | 3 => 0x2238989c463b16391239a69a60311c6e377036
  | 4 => 0xbbc0e0e0783c183e1c3e38e38e3e00703bed80
  | _ => 0
def s5Atlas : Atlas := ⟨5,rawDecor 31 s5Pos s5Neg, 0xe888a000e888a000e888a000e888a000e888a000e888a000e888a000e888a000e888a000e888a000e888a000e888a000e888a000e888a000e888a000e888a000, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_15135
namespace PEqualNP.Outside.L_meta_15135
open PEqualNP.Outside.L_meta_15135.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x200084903c140076008c8e320c7066127240002848625c026a747e30000000440000002a1c16500e006454001000006c780688422c220000380000005e00008600000000004a008a185800926046345a0a000052266e2e804c6800080000000000007c4e005600007a82361e04243e1a3a0000100c0000e004000000084004800a0034180022008000ffd50017f54007f95001fd54005f55003fc5400ffd4c017f53007f94c01fd53005f54c03fc53007fd0c01fe43007f50c01fc4300ffd4801fe52005f94801fd5200ff148017c52007fd0801fe42007f50801fc42007fcc801fe3200778c801fd32007f0c801dc3200ffd4401fe51005f94401fd5100ff144017c51007fd0401fe41006f90401fd41007f10401bc41007fcc401fe31007f4c401fc31007fc8401fe21007f48401fc2100ffd4001fe50005f94001fd5000ff140017c50007fd0001fe40007f50001fc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x204000dfd5020006faa810002ff63080017f3184000bf58c20005f8c6100037f5308001bea984000bf98820006fca4100037c5208001f7a104000fb10820007de6410003de3208001ee1904000fb0c820007986410002fe61080017eb084000df94420006f8a210003be4108001de2084000fb88420007d84210002fe6008001bf2804000df14020007f68010003f84008001f79004000fe88020007da4010003f920080017fb2e2001bf99710006fccb880067e65c40017eb2e2000df59710004facb88006fc65c40017fb262000bf99310005fac988002fc64c4001bfaa62000df55310005fec788002fe63c40017eb1e2000bf18f10006fea7880037d53c40017fb162000bf98b10005fac588002fc62c4001bf2962000df14b10007bc6588003dc32c4001bf28e2000df147100077c8388003bc41c4001bf2862000df14310007f66188003f830c4001fd9062000fe08310005fecb08006fe6584001bf32c20019f99610005facb080037d65840013eb2c2001bf19610005fec908002fe6484001df3242000af99210005fac908003bd64840015eb242000bf19210006fea9080037d54840017fb1c2000bf98e10005fac708002fc6384001bfa9c2000df54e10005fec508002fe62840017eb142000bf18a10006fca5080037c5284001ef1942000f70ca10005fac3080037e5184001be28c2000fdd06100077c8308003bc4184001fa20c2000ed10610007ee6308003f43184001fb90c2000fd08610005fcc1080037e5084001be2842000fdc4210007f62108002ff6544001bfb2a20009fd951000dfcca88002fd65440037e32a2000df1951000cf8ca88002ff6444001dfb222000afd9110005fcc888002fd64440017e3222000ef1911000578c8880037f5444001beaa22000bfd8d10007bec688002df63440017f31a2000bf58d10005f8c688003dc63440016e31a2000dfd4d10006faa688002ff6244001f7b122000bbd8910005fcc488002fd62440017e3122000fb18910005d8c4880037e5244001be2922000f78c910007b864880037e5144001be28a2000ef905100077882880037e5044001be2822000fec4110007ec2088002ff6504001bfb2820009fd941000dfcca08002fd65040037e3282000df1941000cf8ca08002ff64040017f3202000bf59010005f8c8080037f5404001beaa02000bfd8c10005fcc608002fd63040017e3182000dfd4c10006faa608002ff62040017f3102000bf58810005f8c4080037e5204001be2902000f78c810007b86408002fe6104001bf2882000df14410007ee8208003be4104001de2082000fd10410007688208003f73104001fa1882000fdc8410007e84208002fe6004001bf2802000df14010007f66008003f83004001fd9002000fe08010007ee2008003fa1004001fa8802000fe44010
  | 1 => 0x37f654c0013fb2a6001bf99530005faca98006fc654c001be32a60019f19530005fec898003bf644c0015fb226000bf99130005fac898002fc644c001de3226000af19130006fea8980037d544c001bfa9a6000df54d30005fec498003ef624c00177b126000bf18930007d8c498002ec624c001bf2926000df14930007bc6498003dc324c0017fb0a6000fdd8530005eec298002fc614c001fa30a6000bd18530006fca2980037c514c001df20a6000ef10530006fca0980037c504c001fd9826000f78c130005feca18006fe650c001bf32860019f99430005faca180037d650c0013eb286001bf19430005fec818002fe640c0017eb206000bf19030006fea8180037d540c0017f3186000dfd4c30006faa618003df430c001ee2186000bf98830005fac4180037e520c001be2906000f78c830007b86418002fe610c0017eb086000df94430006f8a218003be410c001de2086000f78c430007b86218002fe600c001bf2806000df14030007be6018003fa300c001ee9806000fe4c030005fecb90006fe65c8001bf32e40019f99720005facb900037d65c80013eb2e4001bf19720005fec990002fe64c80017eb264000bf19320006fea9900037d54c80017fb1e4000bf98f20005fac790002fc63c8001bfa9e4000df54f20006fca5900037c52c8001ef1964000f70cb20005fcc390002fd61c8001bf28e4000df147200077c8390003bc41c8001bf2864000df14320007f68190003f840c80017fb2c4001bf99620006fccb100067e65880017eb2c4000df59620004facb10006fc65880017fb244000bf99220005fac910002fc6488001bfaa44000df55220005fec710002fe6388001ef31c4000b798e20005fac710003dd63880016eb1c4000bf18e20006fea7100037d53880017eb144000df94a20006f8a510003ef4288001f62144000fbcca20007bc6510003dc3288001f61944000f30ca20005fcc310002fd6188001bf28c4000df146200077c8310003bc4188001f710c4000fb08620005fcc1100037e5088001be2844000fbc8220007f64110002ff6548001bfb2a40009fd952000dfcca90002fd65480037e32a4000df1952000cf8ca90002ff6448001dfb224000afd9120005fcc890002fd64480017e3224000ef1912000578c8900037f5448001beaa24000bfd8d20007bec690002df63480017f31a4000bf58d20005f8c690003dc63480016e31a4000dfd4d20006faa6900037e5248001be2924000f78c920007b86490002ff6148001fbb0a4000bdd8520005f8c290003f461480017a30a4000df94520006f8a290003be4148001de20a4000df94120006f8a090003fb2048001f71024000bfd9420006feca100027f65080037f3284000bf5942000df8ca100037c65080033e3284000bfd9020005fcc810002fd64080017e3
  | 2 => 0x50006f862280037f2114001bf108a000df48450006f842280077e60140013f300a001de98050005fecba0006fe65d0001bf32e80019f99740005facba00037d65d00013eb2e8001bf19740006fea9a00037d54d00017f31e8000bf58f40006fea7a00037d53d00017f3168000bf58b40006fca5a00037c52d0001ef1968000f70cb40005fcc3a0002fd61d0001bf28e8000df147400077c83a0003bc41d0001bf2868000df14340005fecb200037f65900013fb2c8001bf99640005facb20006fc6590001be32c80019f19640005fac9200037f5490001beaa48000bf98e40005fac7200037f5390001bea9c8000ef90e40007788720002fe62900017eb148000df94a40006f8a520003be4290001de2148000f78ca40007b86520002fe61900017eb0c8000df94640006f8a320003be4190001de20c8000bf98240006fca1200037c5090001dfa048000fed0240005fecaa00037f65500013fb2a8001bf99540005facaa0006fc6550001be32a80019f19540006fea8a00037d54500017fb1a8000f7d8d40005bec6a0002fc6350001ee31a8000b718d40006fea6a00037d53500017fb128000fbd8940005dec4a0002fc6250001f63128000bb18940006fca4a00037c5250001ef1928000f70c940005fec2a0003f761500017bb0a8000bf18540007e8c2a0002f46150001bf28a8000df145400077c82a0003bc4150001bf2828000df14140007f680a0003be40500017fb288001bf99440006fcca200067e65100017eb288000df59440004faca20006fc65100017f3208000dfd5040006faa820002fe63100017eb188000dfd4c40006faa620003be4310001de2188000bf98840005fac4200037e5210001be2908000ef90840007788420003de3210001ee1908000bf98440005fac2200037e5110001be2888000ef90440007788220002fe6010001bf2808000df140400077e8020003fa4010001dea008000fe50040005fecb98006fe65cc001bf32e60019f99730005facb980037d65cc0013eb2e6001bf19730005fec998002fe64cc0017eb266000bf19330006fea9980037d54cc001bfa9e6000df54f30005fcc598002fd62cc001bf2966000df14b30007bc6598003dc32cc0017f30e6000bf58730006fca3980037c51cc001df20e6000ef10730006fca1980037c50cc0017fb2c6000dfd9630004fecb18006fe658c0017eb2c6001bf19630006f8cb180067c658c0017fb246000bf99230005fac918002fc648c001bfaa46000df55230005fac7180037f538c001bea9c6000f7d0e30007b88718002fe628c0017eb146000df94a30006f8a518003de328c001ee1946000bf98630005fac3180037e518c001be28c6000ef90630007788318003de318c001ee18c6000bf98230006fca1180037c508c001ef9846000fecc230005feca9800
  | 3 => 0xe3224200dfd5121006faa890802ff6348401efb1a4200b7d8d21005fcc690802fd63484017e31a4200f718d21005b8c6908037f5348401bea9a4200df94921006f8a490803de3248401ee1924200df94521006f8a290803be4148401de20a4200fdc8521007dc4290802ff6048401fdb024200bed8121005f8c090803f860484017c3024200bfd9421006feca108027f65084037f3284200bf5942100df8ca108037c65084033e3284200bfd9021005fcc810802fd64084017e3204200dfd5021006faa810802ff63084017f3184200bf58c21005f8c6108037f5308401bea984200bf98821006fca4108037c5208401f79904200f78c821007b86410803ec3208401e61904200bf98421006fca2108037c5108401fba084200ef90421007788210803f44108401da2084200fbc8421007ec4210803ed2108401fa9084200bf98021005fac010806fd65940017f324a000bf5925000efea9280037e5494001beaa4a001df15250005fcc728002fd6394003bfa9ca000df94e50006faa7280077c53940017f314a000bf58a5000efea5280037e5294001bea94a001df14a50007bc6528003dc32940017f30ca000bf5865000efea3280037e5194001bea8ca001df146500077c8328003bc41940037f304a001dfd425000ff6a128007f85094001bfb24a000df99250006fac9280027d6494001be324a000dfd8e50006fcc7280037d63940013eb1ca000df18e50006fe87280037e4394001bea1ca000df10e50006fec5280037e62940013f314a000df58a50006f8c5280037f4294001bf214a000df50a50006f885280037f3294001bf194a000d78ca50006fa65280037c3294001ae194a000dfd8650006fcc3280027e6194001beb0ca000df18650006fe83280037e41940019f20ca000df50650006f883280033c4194001bf98ca000df8c650006fa63280037c3194001bf90ca000df88650006fa43280037c21940033f304a001bfd9550005fec8a8002fc6454003bfaa2a000df55150005fec6a8002fc6354003bfa9aa000df54d50005fec4a8002fc6254001bf292a001df14950007bc64a8003dc32540017fb0aa000bf18550006fca2a80077c5154001df20aa000ef1055000dfec0a8007fb5054001bf282a001df1415000ff0a0a80077f6414003bf320a001df59050004fac8280077c6414003bfb18a001df98c5000efac6280027d6314003be318a000dfd0c50006fc86280037d4314001be218a001dfd885000efcc4280027e6214003beb10a001df18850006fe84280037e4214001bea10a000df10850006fe64280037e3214001af190a000df4c850006f864280035c3214003bfb08a001df98450004fcc2280077d6114003be308a000dfd0450006fc82280033e4114001bea08a000df104500067882280037f3114001bf188a000df4c4
  | 4 => 0x8037f53cc401bea9e6200bf98b31005fac5988037e52cc401be2966200f78cb31007b865988037e51cc401be28e6200ef90731007788398802fe60cc4017eb066200bfd9631006fecb188027f658c4037f32c6200bf5963100df8cb188037c658c4033e32c6200bfd9231005fcc918802fd648c4017e3246200dfd5231006faa918802fd638c401bfa9c6200df54e31005fcc518802fd628c401bf2946200df14a31007bc6518803dc328c4017f30c6200df94631006f8a318803f7418c401df20c6200ef10631007e88318803b4418c401ef98c6200fdcc631005fcc118802fd608c4017fb2a6200dfd9531004feca98806fe654c4017eb2a6201bf19531006f8ca988067c654c4017fb226200efd91310057ec898802fe644c4017eb226200bf1913100778c898802bc644c401bfaa26200df55131006fea6988037d534c4017fb126200fbd8931005dec498802fc624c401f63126200bb18931006fca4988037c524c401ef1926200f70c931006fca2988037c514c401fba0a6200ef90531007788298803f4414c401da20a6200fdcc531007bc6298802ff604c401fdb026200bed8131005f8c098803f8604c4017c3026200bfd943100dfcca188037e650c4033f3286200bf59431006faca188027d650c4037e3286200bfd9031005fcc818802fd640c4017e3206200dfd5031006faa818802fe630c401bfa986200df54c31005fcc418802fd620c401bf2906200df14831007bc6418803dc320c4017f3086200df94431006f8a218803be410c401de2086200f7cc431007ec6218803dd310c401fa9886200bf98031005fac018802ff65c84037f32e4200df9972100cfccb90802fd65c8401beb2e42009f5972100df8cb90802ff64c84017f3264200ef993210057cc990802fd64c8401deb264200af59321005f8c9908037f54c8401beaa64200bfd8f21005fcc790802fd63c84017e31e4200dfd4f21006faa7908037e52c8401be2964200f78cb21007b865908037e51c8401be28e4200fdd07210077c8390803bc41c8401fa20e4200ed10721005fcc190802fd60c84017fb2c4201bf99621006fccb108067e65884017eb2c4200df59621004facb10806fc65884017fb244200bf99221005fac910802fc6488401bfaa44200df55221005fec710802fe6388401ef31c4200b798e21005fac710803dd63884016eb1c4200bf18e21006fea7108037d53884017eb144200df94a21006f8a510803ef3288401ef1944200f70ca21007d86510803cc32884017f30c4200df94621006f8a310803be4188401de20c4200fbc8621007ee4310802fe60884017eb044200bfd9521006feca908027f65484037f32a4200bf5952100df8ca908037c65484033e32a4200bfd91210077ec890802bf64484017f3224200bf59121005f8c890803bc64484015
  | 5 => 0x964100cf8cb20802fd6490401bfaa48203efd52410067ea920803be5490401beaa48200ef552410067aa92080fbc54904017f31c8200bf58e41006fea7208037d5390401dfa1c8200ef90e410077a8720803bc43904017f3148200bf58a41006fca5208037c5290401dfa148200ef90a410077a8520803bc4290401ef1948200f70ca41005fcc3208037e5190401be28c8200efd0641007ee8320802fe60904017eb048200efd96410067ecb2080fbe6590401deb2c8203ef1964100678cb20803bf6390401df31c8200ef58e4100778c72080fbf53904019fa9c8200ef94e410077aa7208033d5390407de29c8200efd8a410077cc520803bd6290401de3148203efd4a410077ca5208033e5290401dea948203ef14a4100678a520803bf3290401df1948200e78ca410077a6520803bc3290401ce1948200af9864101f7ea320803be51904019f28c8200ef5464101f78a3208033c5190401dfb048200ef982410077ac120803bc6090407dfa848203ef14241005fecaa08037f65504013fb2a8201bf99541005facaa0806fc6550401be32a82019f19541006fea8a08037d54504017fb1a8200bf18d41006fea6a08037d53504017fb128200bf18941006fca4a08037c5250401ef1928200f70c941006fca2a08037c5150401fba0a8200ef90541005fec0a0802fc60504017fb288201bf99441006fcca208067e65104017eb288200df59441004faca20806fc65104017f3208200dfd50410177ea8208033f5410401df2a08200df550410077aa8208033d5410405de2a08200bf98c41005fac6208037f5310401bea988200efd0c410077c8620803bd4310401de2188200bf98841005fac4208037e5210401be2908200efd08410077c8420803bd4210401de2108200f78c841007b86420802fe6110405fba888200df94441006f8a22080bf45110401ba2888200efd0441007ec8220803bd4110401faa088200bf98041005fac020803bf6510405df3288200cf994410077aca208033d6510405de3288200efd8c410077cc620803bd6310401de3188202efd4c410067ea620803be5310401dea988200cf54c4101778a620803bf6210401df3108200ef5884100778c42080bbf5210401df2908200cf948410077aa42080bbc52104019e2908200efcc8410077c64208039e3210401de9908200ef0c841007386420803be61104015f3088200ed984410177ea22080bb75110401df2888200cf944410077aa22080bbc51104019e2888202ed1444100668a220803bf6010401df3008200ef5804100778c02080bbf5010405de2808200bfd973100dfccb988037e65cc4033f32e6200bf59731006facb988027d65cc4037e32e6200bfd9331005fcc998803be64cc4015f3266200bf593310077ac998802bd64cc4017e3266200dfd5331006faa998
  | 6 => 0x1bf2906400df1483202fd8a4190036c520c801f72106400fb50832007be6419003ee320c801ee9906400fb4c832005fcc219002fd610c8017f3006400bf58032007beca19017de650c801af3286400f759432006baca19017dc650c801efb206400f799032007bac819003dc640c80befaa06400d7d5032007bca819003dd540c801aeaa06405f715032007bcc419002de620c801e73106405f7d483202f9ea419003de520c801af2906400f75483202fb8a4190035c520c80be62906400d314832007be8419003de420c801e72106400f7508320079a8419003dc420c801efb086400f798432007bac219003dc610c80befa886405f714432007bec019003de600c801eeb006400f71803202fbea019017dc500c8037eb2ca200bf99251005fac9288077f5494401bf2a4a200df5525100ef8a928802fe63944017eb1ca201dfd4e51006fca7288037d5394403be29ca200bf98a51005fac5288077f5294401bf294a200df54a5100ef8a528803de3294401ee194a201bf9865100efea328807f75194403fa28ca200bf98251005fac1288077f5094403be284a200dfd9251006fcc9288037d64944013eb24a200df19251006fec7288037e6394401beb1ca2009f58e51006f8c7288037f4394401bf21ca200df50e51006f887288037f6294401bf314a2009f98a51006fac5288037c6294401bfa14a200df90a51006fa85288037c4294401bf994a200df8ca51006bc65288037d3294401be194a200d70ca5100cfcc3288037f6094401bf304a2009f98251006fac1288037c60944037fb2aa200bfd91510077ec8a8802bf64544017e322a200ef1915100578c8a88077f5454401beaa2a200bfd8d51005f8c6a88077f5354401bea9aa200bfd8951005f8c4a88037e5254403be292a200f78c951007b864a8806ff6154403fba8aa200df9455100ef8a2a8807f451544017fb02a200bf1815100ef8a0a88077f6414403bf320a201df59051004fac8288077c6414403bfb18a201df98c5100efac6288027d6314403be318a200dfd0c51006fc86288037d4314401be218a201dfd885100efcc4288027e6214403beb10a201df18851006fe84288037e4214401bea10a200df10851006fe64288037e3214401af190a200df4c851006f864288035c3214403bf308a2009f9845100eecc2288077f6014403bf300a2009f9805100efac0288077c60144017fb2e8201bf99741006fccba08067e65d04017eb2e8200df59741004facba0806fc65d0401bfaa68200df55341005fcc7a0802fd63d0401bfa9e8200df54f41005fcc5a0802fd62d0401bf2968200df14b41007bc65a0803dc32d0409fba8e8200df94741006f8a3a0813f451d0401ba28e8200bf98341005fac1a0802ff6590401bfb2c82009fd964100dfccb20802fd65904037e32c8200df1
  | 7 => 0x21003bf4290801f7a148400bf98642005fac321002fe60908017eb048400bfd9542006fecaa10027f65508037f32a8400bf5954200df8caa10037c65508033e32a8400dfd5142006faa8a1002ff6350801efb1a8400b7d8d42005f8c6a1003dc63508016e31a8400dfd4d42006faa6a10037e5250801be2928400fbd09420077c84a1002ff6150801fbb0a8400bdd8542005f8c2a1003f461508017a30a8400bfd8142007f6c0a1002fb60508017e3028400fe18142005f0c0a1002ff65108037f3288400df9944200cfcca21002fd6510801beb2884009f5944200df8ca21002fe6410801bfaa08400df55042005fcc621002fd6310801bfa988400df54c42005fcc4210037e5210801be2908400efd0842007dc8421003bd4210801f6a108400bf98442005fac221002fe60108017eb008400bfd973200dfccb990037e65cc8033f32e6400bf59732006facb990027d65cc8037e32e6400bfd9332005fcc999002fd64cc8017e3266400dfd5332006faa9990037f53cc801bea9e6407fbd4b32006fca5990037c52cc80ff62966400db14b32007dc8599003ed42cc8017f30e6400bf58732005fcc199002fd60cc8017fb2c6400dfd9632004fecb19006fe658c8017eb2c6401bf19632006f8cb190067c658c8017fb246400bf99232005fac919002fc648c801bfaa46400df55232005fac7190037f538c80defa9c6400d7d4e32007bca7190037d538c801eea9c6400d754e32037b8a719003df438c801ef21c6400f750e32007b88719002fe628c801bf2946400df14a32007be6519003ef328c8017f30c6400bf58632005fcc119002fd608c801efb2c6400d7d9632037bccb19003dd658c80dee32c6400d719632007bec919003de648c801eeb246400f719232037bea9190035f548c801ef2a46400f755232006baa91901bdc548c8016f3146406f7d4a32007bca5190035e528c801eea946406f714a32006b8a519003df428c801ef2146400f750a32007b88519003df618c801ef30c6400f758632007b8c31901bdf518c80dee28c6400f7d8232007bcc119003dd608c801ee3046406f7d4232037b8a119002ff654c801bfb2a64009fd953200dfcca99002fd654c8037e32a6400df1953200cf8ca99002ff644c8017f3226400bf59132005f8c8990037f544c801beaa26400dfd4d32006faa6990037e524c801be2926400fbcc932007bc6499002ff614c8017e30a6400bfd8132005f8c099002ff650c8037f3286400df9943200cfcca19002fd650c801beb2864009f5943200df8ca19002ff640c8017f3206400bf59032005f8c8190037f540c801beaa06400bf98c32006fea619017df530c801afa986400f794c32006faa619003dd530c801aea986405f714c32007be8619003de430c801eea186400f710c32005fcc419017ef520c80
  | 8 => 0xb98b43005dcc5a1802fd62d0c01f6b168600bb58b43005fcc3a1802fd61d0c017f3068600bf58343005fecb21806fe6590c01bf32c86019f99643005facb218037d6590c013eb2c8601bf19643005fac9218037f5490c01beaa48600bf98e43006fea7218037d5390c01dfa1c8600f7d0e43005fcc521802fd6290c017f30c8600fd98643005ecc321802fd6190c01fab0c8600bd58643005fcc121802fd6090c017fb2a8601bf99543006fccaa18067e6550c017eb2a8600df59543004facaa1806fc6550c01bfaa28600df55143006fea6a18037d5350c01efa1a8600ef90d43005fec4a1802fc6250c017fb0a8600bf18543005fec0a1802fc6050c017fb288601bf99443006fcca218067e6510c017eb288600df59443004faca21806fc6510c017f3208600dfd5043006faa821802fe6310c01bfa988600df54c430077e8621803de4310c01dea188600f750c43005fcc421802fd6210c017f3088600bf58443005fcc021802fd6010c037eb2ca400bf99252005fac9290077f5494801bf2a4a400df5525200ef8a929002fe63948017eb1ca401dfd4e52006fca7290037d5394803be29ca401bf98a5200efea529007ef5294803f6294a400bf98652005fac3290077f5194803be28ca400bf98252005fac1290077f5094803be284a400dfd9252006fcc9290037d64948013eb24a400df19252006fec7290037e6394801beb1ca4009f58e52006f8c7290037f4394801bf21ca400df50e52006f887290067e6294801bfb0ca400df98652004fcc3290037d6194801be30ca400dfd8252006fcc1290027e6094801beb04a400df1825200dfecaa9002ff64548017e322a401dfd5152006faa8a9002ff6354801efb1aa400b7d8d52005f8c6a9003dc63548016e31aa401dfd4d52006faa6a9006ff6254803f7a92a400df9495200ef8a4a9007ec52548017fb0aa400bf1855200ef8a2a9002ff60548017e302a401df1415200efec8290077e6414803beb20a4009f5905200ef8c8290077f6314803bf318a401df58c52004fac6290077c6314801bfa18a400df90c52006fa86290037c4314803bf310a4009f9885200edcc4290077f6114803bf308a4009f9845200efac2290077c6114803bfb00a401df98052004fcc0290077d6014803be300a400bfd974200dfccba10037e65d08033f32e8400bf59742006facba10027d65d08037e32e8400dfd5342006faa9a1002fe63d0801ef31e8400b798f42005fac7a1003dd63d08016eb1e8400dfd4f42006faa7a10037e52d0801be2968400bf98742005fac3a1002fe60d08017eb068400bfd9642006fecb210027f65908037f32c8400bf5964200df8cb210037c65908033e32c8400bf59242006fea9210037d54908017f31c8400bf58e42006fea7210037d53908017f3148400df94a42006f8a5
  | 9 => 0x801001403c00003800000400401c00400000000012402402400000003c01801000001800002000000001001c0580700042ec0140ac00802003c00800000005802c00000400000001005401c00000800404c02806401802c00000400010800800403400000000403400002c04c01401803bfb1ea801df98f5400efac7aa0027d63d5003be31ea801dfd8b5400efcc5aa0027e62d5003beb16a801df18b5400efec3aa0077e61d50013f30ea801df5875400ef8c3aa0077f60d5003bf306a8009f9835400efac1aa0077c60d50037eb2ca8009f5965400dfcc92a0077f5495003dfaa4a801cfd525400f78a92a002fe63950017eb1ca801dfd4e54005fcc52a002fd6295003be294a800bf98654005fac32a0077c51950017f304a800bf5825400ef8a12a006ff65550037fb22a801efd5154006fca8aa0077c5455003de2a2a800bfd8d54005f8c6aa0077f5355003be29aa800bfd8954005f8c4aa0077f5255003be292a800bfd8554007eec2aa002f761550017e30aa800fd18554005e8c2aa0077f5155003be28aa800bfd8154005f8c0aa0077f5055003be282a801dfd915400cfec8aa0073f6455001bfb1aa8009fd8d54006fcc6aa0037d6355001be31aa800dfd8954006fcc4aa0037d6255001be312a8009f18954006fec2aa003776155001bf30aa800df58554006f8c2aa0027c6155001ba30aa8009d18554006fec0aa0037e6055001beb02a800df18154004f8c0aa0077f64d4c03bf326a601df59353004fac9a98077c64d4c03bfb16a601df98b53004fcc5a98077d62d4c03be316a601dfd875300efcc3a98027e61d4c03beb0ea601df1875300efec1a98077e60d4c013f306a601df5835300ef8c1a9806fd6594c013eb2ca600bf99253005fac9298077f5494c01beaa4a601bf98e5300efea729807df5394c03ee29ca600bf98a53005fac5298077c5294c017f30ca600bf5865300ef8a329802fe6094c017eb04a601df1425300dfecaa9802ff6454c017e322a601dfd5153006fca8a98037d5454c03be2a2a601bfd8d5300fbea6a98037e5354c03be29aa601f714d53005fec4a9803ef6254c0177b12a600bf18953007d8c4a9802ec6254c03bfa92a601df14953005fec2a9802fc6154c03bfa8aa601df14553005fec0a9802fc6054c03bfa82a601df14153006fec8a98027f6454c01bf322a600df59153006f8c8a98077f6354c033fb1aa601d7d8d53006fec4a98036f6254c01bf312a600df58953006f8c4a98027c6254c01b6312a6009b18953006fec2a98037e6154c01beb0aa600df18553004f8c2a98037f6054c01bf302a600df58153006f8c0a98027c6054c017fb2e8601bf99743006fccba18067e65d0c017eb2e8600df59743004facba1806fc65d0c01bfaa68600df55343006fea7a18037d53d0c017f3168600f
  | 10 => 0x518e5000015628e054829400000009e80000000000000000000000000065414d0000a4cdf632827c004c00000001c00002000c01400000001004000400001400000c00c01404c06402400400000000c01000001800400002c00001c0480b000c00800005000c00000c03800000000406400806400001401c01402000400001400406000400000801800003800801000400800c0b002002000406c00002002000000402004003800803001000400000801800002000401002401800000401403802400801c00000000400402800000000000000006401000801401802c00801c02800801401000401400000009c00006c0280200040200240800100380080140080040040040140000a802400803803000000000800000c01800c00400000800809000800000c00000800401c05c04400c04400801400003c00001400c0e80180100a40000040000000000040000140d000c05000000002800401401800400400000001000800401c00804c00400c02001c07002401001001007800c00000003401801000c03c00001000000007c00000000c05400003c0000000040000000000240080040000000100000280000140140140040080080280000500080040000b400c01c03800400000000c00400c01400400000800400000c0080141ac0100200000000040000000000000f80000140ec00008809000c00000003401c0200040000e800803803003000c01806401800402c0b801800400c01001004000c02401400402c00800804802401400002402401c03800004800000400c01c02400001000001c01400400001806800401800000400005002800400000000400001c01401802400c01801800804c01400c00003402007803401404003402800002408402400805400000000402c00000800404400401800406002c0400340c000801000400803401800000001000800801001c02801401c00400000000401400001000400001000002000c04c00c00c0040080880100000000d80680b001000800000002401400c00400400000001c00c00800002000004400401c00404000000c00400000001000800c0080840280200040041640380040000a000004005403004000000000803800402000006001c00000004000c02005800c0040000040500440e401c0b000000c0280c400000403002001001003800002c02400800c00001801800c0080000300040000040000080300c40080180280000240040041340000040000180040000200740ec00003000000c00c00000000000006c04406801000002802c00000402c00001c01401c00005c0080080000080040540d000000000005400400801000801400800800402400800000002001000800400005c00400000c08c04c06c00400001403800c0100040040080000b404800005800404000403c01000
  | 11 => 0xb663bc00017bc59e30c0000000fc021241380008160a000014d480070e37b8fa4f8e25c1690274d4a81f04d0bdc7143f217e04304703d409200004ea00030a80000000001dd96280000aa1db800052883d43b000000000000000001263190fd0d7c63c8261f382e48184aa09c93280001830298000d421ab2c701142aa7711730b5cd3e75039b00000005181ee80000001c20ac9d240960601bc03f83b419a2848460cac6c13949d382cc5780001be42a86cf1e421042a054b1d286f82c43d61fa0aacffc00000000000000000002090000000000000000000000021f0a220cc1a91394ffa5d400000003300001c91de800070338221448927b800002f000049100013f45581f62e716e8bca7f70e71584e1468741d138887a3a238304a8ec20002a400000000002721b5446a21813a1b60d066ff176978c11429002c96b804600600006cc1246930330dc46d069124200003f613312080007b635a14d8808e720003480000e2c2170740ce441a0a21f81cf874c00015212ecba03380000000b3231a1a79954e2432544580006002d041c019000005e148853cd5e527180983002c4b234b80001ce2cb40d16905900293c601ec00223033e1f386e432312f800007e4782588cc84b01cc0001ddccf030a00000000000000729f34a166361718d6c00000017f128c4aa3020f98000ae6000000000000074f00015e8000000000022c0000000000000bd686e1dc00000007603591e80c962e03ee9e2cc020001a080004fe0003f613a036c22e13600001ec00043a0194a5474229d84506d46001428000000103000149800060802908902e456e1d49e7c23e4be04490dc32a0001d8977056a8613e800000004800000000fc82f900000002a2000395955456c6c2000000058600000000000000000001c68692000100000000004900000000004ab3f822084020f43ea80006d258f2e921c46ca5391fd837c00e1582e50b740005fa3e200000004e6000194834429815b800000000043280000000000001360000000000149419620b27a0748d342360e88a540c63aa314189445a32210d1c1caca16f09f800020c66437e96b0e4e3832dca1ec00022a0940230e1073734c82201b832e0c40000ce41b13038724b8020e1c291fc9d43600000f30d6a74d09881dc8563ab3f3881892664116f2028ce02833e880003b00bd1570d382525b03ca80989162cd3b816710e425d24b1ad01586fa21d044c2127530fe0a10ee45de1221d50dc231b23d8ee4fa41991280a087de27c299811822246312886b8a0000031596609480ba2f302d0edc3c909e00009be3b60a317a89de4884168dc044247729080005626620689c806b23b240980000000040f29fc8eaa1103318c544ce6bb0f70d4c08652f32706e080e7c81e99c64d2a0b73800038f2e000139135caa00001
  | 12 => 0x548ce80000000000dacd380000ea800000057931c8fe40004ce0078610c42622324a0889960000000000d3c7df3879d7000061f00014fc4100443150000d9062924d000000000000008a4f5e6262f21ae428a00018300000006be2390eb41b071d0000000c1200000000002ec000000000063a2872480171042000378127812000005389a0a340000001dd83f20002891b4462647643f83990d42f522391341484f0117912905c2b21e58fb860e4ba1cd8298aa409e2bd872098012d2cf800023685900000005740000000000b9825a39a000000082a00005cc000196090129803a00030680000002d125b96110c00000001aa0b6805d000019cf060bf1300bc45c28193ae800102c0581638f8000000000000000003dc14091d000000001908a000000000000004e65d600018d48ba60231b96300003d91c00c24eb47990001f3085e57e0ce040800000000000000000002a0000036872d19f11903e424f1ce1cc0baa00000000000007ad32400002927b100000009c02611b11b800003a7000000000008300006e84441001ce8000f604832040000000000155000000052e00000000003a830d80003f0000018a1680000513f6954484e0001bc9024f10000000007083055920e000000079d000000087246e00000000000003d590889e48080000be854c41714b16c800053c2a107100000002faa234f580000000b54e2a38e35306c094484b15f096c9383f31028e20f4e2bd3631b34cc27b6035954c4944452ab899901e8732088f98a2c37f11d849446e2ce05a86dcc2e00237a09945a85373a895707d63a143c8438ad816800013e429000013b93cc3cc7381e68fa88d87ef00014d91065e122185a49d210b31013dc7326ae40a8c2c09e01e04f9fb831e00021681a820a214249036c0aa72f17387047465900ed9f3ca10671263952800005f3798000000000000151c55e0000000bd0000461000000000003942482e091a28e00000007f87c10878eb90460250001d0400000035213440007d64271b280005e91a6937477485b2cb0e6800060b41880000008360000000000000000002c0004303eb800040809510c80008587aa0002148a3a82c0000000e1200015a15380000000001b687d84280001a500005d71ea8000000886000087c7942df36b915c68e5ab00008fcb7839f1490000dd28420a98b300e083319e8d4497a45c19a115400000000001bc7c45cf26b1418000000000140905629c3200b4ca1a56716d0000d882260719cf047c71b07782ac4680c73d40d30000000000181055200028f10980000000001cec0007a928f997c60a71f161000058200024311680fc00033f0a204f65e80da8050db61bf0c88bd8e044ff0bf00000005290710000000000000000077e4530dd8000cf400023a9f84a8c57d0b5986497e4012901838
  | 13 => 0x29c5931b18420ee86a3000000058c5d9000007c0000003898000fe22a000ba21c0004b60001be10900002e68ddc0b6000000174d06e67b0280000d922ef3f98cd4cec6b32990bc02440f22c09c5d0da2b03178f845165db2af9fd40600001388b90dbc1eb00020c000057c0a180000002470001180000000000000051a4d30e2800000023c237972c2f212b25a80009721a0126865c2424150ba05c40006e300602c4d5600014f1a200005ed0001d1000011e00013480001942660fb470c03c32c1158a5848e29c206000046941780a8000560334943800000035610680005050001a3892a6810000000a4600013c1b0c0000000411354f380792912190f7e5af2290000eca7810af163442618d16498e09dc8203c02050da80682a09c7030e41b23695d84ac78742f069c6b85f428a1e9878438d1f88a648a212317da00c05044b00000009a800000007787ca0003ec20180006d33cc11640005f20000920bc000042b8df40007780000264b6e79e27b0000f041ff2df8000e6200000000010f0000404800000000028503fca687b52fb80008fc66a23883e08d636c067056c0007be1f2000082087d2d1800000000000000000000b31ef0e80a867bb00021b04c4000147800102416a0000000c881c7283800003000009d888cff85c7318800005a6a22e880000003331df00010cc0002581c950ee48a0389668b541c005b13e80001ec3960db46ea1e70408a303200c23861bc89661d300021008f25690751928d804981fd0790ad47643ac8000194010000000056604e1c080008be60a2cb800000054500000008622bb27a9fd0cd800010e0e90000098098170800a00011580f400000001600000745d823380000001d626202ec9424440ce9334a8853e31e108c9040001a4000006e0002ab000000056b42e8cad0a8000000000000000000016c447200020121a4000000000200000000000000001c80001c5800000034b000176908e00024c92f02ce4f10000384000000280800000014400000000000be2aa1db0b4c59128a99780000000cd800000000020f00003722f2000000058a58b00011310f44ed1da13f800000032800007662532b11cc877a00032e03e40b477f1cc1d20b8671e000041000000000000000000d2000076400000038a03c09360c83d280000f041643f023d02200000010cc18a6f5050a02c73c1bc07690d4000504000000061e0003c4800000067f0c70f7c4da01531e80640001d01b715b40002200a599b80000000de8604ebc0002db00000000fd0000dd000000038c00448680004429e4085c59217711050c60003ac16248cc1e115c80000000002dd8000000000000009c2fa0004310a9406600028c9a348e62a71621afc7a26f609c1ce898c3300d506082c80730000e3c0002a204880008321013f309483ee3f8
  | 14 => 0xd2b8000000000009f20f0ed066800006bd0184484420d18e860002e216750b82ff15420fc39684a000145cd2c0001078ae038c85f29419f40006730001f1434c1e231d04706f667424a080c5b834523e0cb03860003c69a0067e06d120000096800028999e47b474c3c918b0dce50c2cf1cf4fd67e83420cbcd6215f3b181284fc00025297b8f804382b217c4ece0c10761914e4254f41f04d0cea00020e89e478203513704590ea66718690140003c0342a1c08d42761ec1ee83d25c123e92b027a2453d0961872279300491c0a0622c4340df090215d3551ef03c06923e98454efa8803b7980c62018a0c01ef425e58504b8bb0e667e30d49ee43fa63e1ff201d00a24b27d95fd07624c2f9a2242b43170019f8825c7c9015a0346226510bb88e8e8a5f029d10902fe6ad0d42094c644e7374049833c0001ca9d580001ed20680000005c900009c00006d9000160c00062e31194401ea55e3a50fdc06820c051938c9b40001b78eb000010a00019941d62bf1740000dac0c0408000000061c00005040003540000b58e162150d685ec7ae000000000018807233b9f780ec0002611dacab40ad1da8f3807c68f2ca85b878c00017c0020eb615722120e4000000000021c4365a20370000b9015c0ba8ba83de07a06f1c8865a8283ff969ccd60003918ca43fc7d42d4206c42c84425682a01926bd2f38238eae48c1f19bb45ca35037e0000ff05c60a6161d08a4ae244850843a0ae1a0000000054c0001bc4b7a0000001d480000000000000128747203205cab05dd25c1c90dd41dd00000000d85a92150e3066c65b19007d09d829d2989e446084033e598610046341c9a22895e63f428034c5c43890f890ecae244f32308400000002148ffc1f465a302960011a6823c78000ec46333e52118ac64d937f0000c261ea0f411a0dbe60600000000001f000004d400079621913f031863b212a134b401370001bac0340413fb0de8fb200014f8d744120241218120cba6e4000049c30c66d3c7129c0fe835000015c5341df1fe867c2f04580239f9418637e04204e855a7f90000dccecc68900017b06302331e7800000029700000ec4b20000c2800000004c3950c50b706c50430028d9c61e3261f0c8780003458b64bf00001e195d000018b198927cb8a2eb01117e400026a0000d60efc6242ae83747ea0003db8000bfe8042ff1ed099e4870000d7839e00022d8000c4e1172fe22203ae69b00007507ec16544080000000001bb000046242104d8000d9800040f0000f4856f06b0000d7816307e02141005f63a300007880000001e1908643e1a103681aa0b224e8c841d251b19d9a8066e5be3451ae05d21a432a1f180360f707d81580004360001b2c00044e37300801b20cd2b30cf0a606a90000a1800000000000000004971c2137009a000369000
  | 15 => 0xb1084f36e846834a0383210000fb80000001b1c2240000c989bce804140b68000ad03b01190000d186430000a280007db03e91000006ec0068000bbe0000000d98dc452d35b000000009c40709ac0000000000c98f667693181cb80e83d23d19150f5c7c23729c0464e3d03c2936c0f85a118b1e6cdb86162618d58ef261a30ea130c1e85826081509507fb3089dec44e1703f51650cde0a52079e284c673f0e508444143e83c220c86881893081314f3479426f1fa4d3076d40e1fe84840612050ebce207a240e8b6040e5fd15084d8aee5a505783b843c5fb112a19c18c10d32c95c8d4e0421cb9ec84d26d03828f14ca61190d181a463864742b21ac1e616c0c903807041613278d549520132310d28c241071320c480244e131682c081c4a017e8f1c58011d1a189f480876a1cb111849c48f1c8107c0000000000770b3600032b9534a7a23d0e6858005c3240000000a481400311bbc35875f3be10808f44eb00000003640000001cd40004d00000350e220f10001bb800000014000006062f333000003c60000678978d6e7da24280002640002f1035c00000000000000005490000af0e1a4c9333000099000000007d470e855000051c12c0004148a24610000017800000030e0000000ab643f16520d008058222800006ce0000001dd44ae5b518f99342f457522f0340d747731b200d80000000000924042412393223025800023280005b61a10000d84c280004009a182f8000287a1bc48c6b012a1d2ca5600034ea14c00072803a904c6ae5a
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc6390510006af6290510006ac6290510004be76105100063f65105100163c65105100069f63105100069c6310510006af6210510006ac62105100073451105100047e76941100063f64941100063c64941100065f63941100065c63941100066f62941100066c62941100047e76141100063f64141100063c64141100065f63141100065c63141100066f62141100066c6214110006d863c4110006e862c4110006b46484110006d46384110006e462841100047d74d94100047d73d94100047e72d94100047e71d94100067671d94100047e70d94100067a70d94100055d731941000c7e75990100047d75990100047f755901000c7c755901000c7e75190100047d7519010004de7319010004dd7319010004ee7219010004ed72190100047e76d501000c7c76d50100057671d50100047e76550100047c765501000574715501000c7e7598c100047d7598c100047f7558c1000c7c7558c10004bf7458c10004bc7458c10004ef7258c10004ec7258c1000c7e7518c100047d7518c100047e76d4c1000c7c76d4c100057671d4c100057a70d4c100047e7654c100047c7654c100065e6354c100065d6354c100056c7254c10005747154c10005787054c1000c7e75d88100047d75d8810004de73d8810004dd73d881000c7e75988100047d75988100047f755881000c7c7558810004bf7458810004bc7458810004df7358810004dc73588100047e76948100047c76948100047e761481000c7c76148100065f658c8100365c658c8100065f650c81002e5c650c810006cf620c810006cc620c8100074c520c81000c7e75984100047d75984100057a70944100057a70144100267465d04100063f659041001e3c6590410005b671904100063f65104100163c6510410007365110410007345110410004f57610410016746510410007375410410007355410410005f17010410006b67610410006b57610410007367510410007357510410007376510410016b66510410016b46510410007346510410016346510410006b76310410006b56310410007375310410007355310410006b66210410006b46210410007365210410007345210410007963210410007943210410007b27010410007b17010410005b674cc410004f5760c410005b674c8410004f57608410007c4320841000c7e75980100047d7598010004be7498010004bd7498010006b441980100057671940100073441940100047e761401000c7c7614010005767114010007344114010007b041cc010004f9760c010007b0410c010007d0310c010007b041c8010004f97608010007c83208010007b04108010007e0210801000cf97684010007b04184010004f77644010005b47444010005d47344010005e47244010004fb7644010005d87344010005e87244010007b24144010
  | 1 => 0x9110004dc7359110004ef7259110004ec7259110004f7715911000c7e75191100047d7519110004be76191100063f65191100063c65191100063e75191100063d751911001cbe7119110014bc71191100047e76d511000c7c76d51100063f64d51100063c64d51100047e76551100047c76551100063f64551100063c64551100057471551100065f65d8d100065c65d8d100069f64d8d100069c64d8d100065f75d8d100065c75d8d100065f54d8d100065d54d8d10004de72d8d1000c7e7598d100047d7598d10004be7498d10004bd7498d10004de7398d10004ee7298d10004ed7298d100047f7558d1000c7c7558d10004bf7458d10004bc7458d10004ef7258d10004ec7258d10004f77158d10004fb7058d1000c7e7518d100047d7518d10004de7618d100065f6518d100065c6518d100069f6418d100069c6418d100065e7518d100065d7518d100065f5418d100065d5418d10004de7218d100047e76d4d1000c7c76d4d100063f64d4d100063c64d4d100065f63d4d100065c63d4d100047e7654d100047c7654d100063f6454d100063c6454d100065f6354d100065c6354d100056c7254d1000c7e75d89100047d75d8910004de73d8910004dd73d89100066f65d89100066c65d8910006af64d8910006ac64d8910006cf63d8910006cc63d89100066e75d89100066d75d89100066f54d89100066d54d8910006ce73d8910006cd73d89100066f53d89100066d53d891000c7e75989100047d7598910004be7498910004bd7498910004de7398910004dd7398910004ee72989100047f755891000c7c7558910004bf7458910004bc7458910004df7358910004dc7358910004f77158910004fb7058910004ee76189100066f65189100066c6518910006af6418910006ac6418910006cf6318910006cc63189100066f75189100066c75189100066f54189100066d5418910006cf7318910006cc73189100066f53189100066d53189100047e76949100047c76949100063f64949100063c64949100065f63949100065c63949100066f62949100066c62949100047e761491000c7c76149100063f64149100063c64149100065f63149100065c63149100066f62149100066c6214910004de768c910004dc768c9100065f658c9100365c658c9100069f648c9100069c648c910006cf628c910006cc628c910004de760c910004dc760c9100065f650c91002e5c650c9100069f640c9100069c640c910006cf620c910006cc620c9100074c520c9100047e76945100063f64945100063c64945100065f63945100065c63945100066f62945100066c62945100047e76145100063f64145100063c64145100065f63145100065c63145100066f62145100066c6214510004be76905100063f659051001e3c65905100069f63905100069
  | 2 => 0x57a70947100057a701471001e3e65907100063d65907100163e65107100063d6510710007345110710007c83208310004be74d9610004bd74d96100047f74596100047f73596100047c725961000c7e75d92100047d75d921000c7e75992100047d75992100063e65992100063d65992100063e75992100063d75992100063e65592100063d65592100063e75592100063d7559210006b7715921000c7e75192100047d751921000c7f76d52100047d76d52100063e64d52100063d64d52100057671d52100047f76552100047d76552100063e64552100063d645521000574715521000c7e75d8e100047d75d8e10004be74d8e10004bd74d8e10004ee72d8e10004ed72d8e1000c7e7598e100047d7598e1000c7e7518e100047d7518e10004be7418e10004bd7418e1000c7f76d4e100047d76d4e100063e64d4e100063d64d4e100057671d4e100047f7654e100047d7654e100063e6454e100063d6454e100056c7254e10005747154e1000c7e75d8a100047d75d8a10004be74d8a10004bd74d8a10004de73d8a10004dd73d8a100047f7558a1000c7c7558a10004df7358a10004dc7358a1000c7e7518a100047d7518a10004be7418a10004bd7418a100047f7694a100047d7694a100063e6494a100063d6494a1000c7f7614a100047d7614a100063e6414a100063d6414a100365e658ca100065d658ca100069e648ca100069d648ca1002e5e650ca100065d650ca100069e640ca100069d640ca10006ce620ca10006cd620ca100074c520ca100063e64946100063d64946100063e64146100063d64146100267665d061001e3e65906100063d65906100163e65106100063d6510610007365110610007345110610016766510610006b56410610007375410610007355410610005b57610610006b57610610007367510610007357510610016b66510610007366510610016366510610007356510610016b46510610006b76310610006b56310610007375310610007355310610006b66210610006b46210610007365210610007345210610007963210610007943210610005b674cc610005b674c8610006b664c8610006b66408610007c4320861000c7d76942100063e64942100063d64942100057671942100073441942100063e64142100063d641421000576711421000734411421000c7e76d95100047d74d95100047d73d95100047e72d951000c7e71d951000c7c71d951000c7e70d951000c7c70d9510004bf7459510004bc7459510004df7359510004dc7359510004ef7259510004ec72595100047e76195100063f65d91100063c65d91100063f75d91100063c75d911000c7e75991100047d7599110004be7499110004de7399110004dd7399110004ee7299110004ed72991100047f755911000c7c7559110004df735
  | 3 => 0x4715902000c7e75190200047d75190200047e76d502000c7c76d50200056e72d50200057a70d50200047e76550200047c76550200063e64550200063d64550200056c725502000574715502000578705502000c7e7598c200047d7598c200047f7558c2000c7c7558c2000c7e7518c200047d7518c20004be7418c20004bd7418c20004f67118c20004f57118c200047e76d4c2000c7c76d4c200056e72d4c200047e7654c200047c7654c200056c7254c2000c7e75988200047d75988200057a70948200057a7014820005ce73d0820004ed761082003e6c65cc8200065f658c8200365c658c820005ce728c8200065f650c82002e5c650c8200074e520c8200074c520c820004ed760c82002e6c650c8200074f530c8200074d530c820005e9700c820006ce760c820006cd760c8200074e750c8200074d750c8200074f650c82002ece650c82002ecc650c8200074c650c82002e4c650c820006cf640c820006cd640c8200074f540c8200074d540c820007ca700c820007c9700c82000c7e75984200047d7598420006cc32984200047f755842000c7c7558420004bf7458420004bc7458420004df7358420004dc73584200047e76944200074c32944200047e76144200074c32144200063f659042001e3c65904200078c32904200063f65104200163c65104200078c3210420007345110420005ce7388420007a4410842000c7e75980200047d7598020004de7398020004dd7398020006cc32980200056e72940200074c32940200047e761402000c7c76140200056e72140200074c3214020007c832d0020004f97610020007a84210020007c83210020007c83288020004ef7648020005ac7448020005cc7348020005e471480200076a5048020004fb7648020005b874480200076a5248020007ca3248020005f071480200047f74597100047f73597100047c725971000c7e75d93100047d75d9310004de73d9310004dd73d9310004ee72d9310004ed72d931000c7e75993100047d759931000c7e75193100047d751931000c7f76d53100047d76d53100047f76553100047d765531000574715531000c7e75d8f100047d75d8f10004be74d8f10004bd74d8f10004ee72d8f10004ed72d8f1000c7e7598f100047d7598f1000c7e7518f100047d7518f1000c7f76d4f100047d76d4f100057a70d4f100047f7654f100047d7654f100056c7254f10005787054f1000c7e75d8b100047d75d8b10004be74d8b10004bd74d8b10004de73d8b10004dd73d8b100047f7558b1000c7c7558b10004df7358b10004dc7358b1000c7e7518b100047d7518b100047f7694b100047d7694b1000c7f7614b100047d7614b100365e658cb100065d658cb1002e5e650cb100065d650cb10006ce620cb10006cd620cb100074c520cb1000c7d7694710
  | 4 => 0x8d200065f54d8d200065d54d8d2000c7e7598d200047d7598d20004be7498d20004bd7498d20004de7398d20004f67198d20004f57198d200047f7558d2000c7c7558d20004bf7458d20004bc7458d20004ef7258d20004f77158d20004f47158d2000c7e7518d200047d7518d20004de7618d200065f6518d200065c6518d200069f6418d200069c6418d200065e7518d200065d7518d200065f5418d200065d5418d20034de7218d2002cdc7218d200047e76d4d2000c7c76d4d200063f64d4d200063c64d4d200065f63d4d200065c63d4d200047e7654d200047c7654d200063f6454d200063c6454d200065f6354d200065c6354d200056c7254d200047e76949200063f64949200063c64949200065f63949200065c63949200047e76149200063f64149200063c64149200065f63149200065c6314920004de768c9200065f658c9200365c658c9200069f648c9200069c648c920004de760c9200065f650c92002e5c650c9200069f640c9200069c640c9200074c520c92000c7e75d85200047d75d8520004be74d8520004bd74d85200067765d85200067465d8520006b764d8520006b464d8520006d763d8520006d463d85200067675d85200067575d8520006b674d8520006b574d85200067754d85200067554d85200067753d85200067553d85200067652d85200067452d8520006d632d8520006d432d8520006776518520006746518520006b76418520006b46418520006d76318520006d46318520006777518520006747518520006b77418520006b47418520006775418520006755418520006775318520006755318520006765218520006745218520006d63218520006d432185200047e76945200047c76945200063f64945200063c64945200065f63945200065c63945200067761945200067461945200047e761452000c7c76145200063f64145200063c64145200065f63145200065c6314520006776114520006746114520004be7690520004bc76905200063f659052001e3c65905200069f63905200069c6390520006b76190520006b46190520004be7610520004bc76105200063f65105200163c65105200069f63105200069c6310520006b76110520006b461105200073451105200047e76941200063f64941200063c64941200065f63941200065c63941200067761941200067461941200047e76141200063f64141200063c64141200065f63141200065c6314120006776114120006746114120006b864c8120006f061c8120006ac6488120006cc6388120006e461881200047d74d94200047d73d94200047e72d94200066e72d94200047e71d94200047e70d94200067a70d94200053d741942000c7e75990200047d75990200047f755902000c7c7559020004df7359020004dc7359020004f77159020004f
  | 5 => 0x4dd73d9220004f671d9220004f571d922000c7e75992200047d759922000c7e75192200047d7519220004de7319220004dd731922000c7f76d52200047d76d52200056e72d52200047f76552200047d76552200056c725522000574715522000c7e75d8e200047d75d8e2000c7e7598e200047d7598e200065e6598e200065d6598e200065e7598e200065d7598e200065f5498e200065d5498e200065e6558e200065d6558e200065e7558e200065d7558e200065f5458e200065d5458e20006cf7258e2000c7e7518e200047d7518e2000c7f76d4e200047d76d4e200065e63d4e200065d63d4e200056e72d4e200047f7654e200047d7654e200065e6354e200065d6354e200056c7254e200065e6394a200065d6394a200065e6314a200065d6314a20005ce73d0a2003e6e65cca200365e658ca200065d658ca2002e5e650ca200065d650ca200074e520ca200074c520ca2002e6e650ca20006cd630ca200074f530ca200074d530ca20005cd760ca20006cd760ca200074e750ca200074d750ca2002ece650ca200074e650ca2002e4e650ca200074d650ca2002ecc650ca20006cf640ca20006cd640ca200074f540ca200074d540ca20006cc32986200047f755862000c7c7558620004bf7458620004bc74586200047f76946200047d76946200065e63946200065d63946200074c329462000c7f76146200047d76146200065e63146200065d63146200074c321462001e3e65906200063d65906200069e63906200069d63906200078c32906200163e65106200063d65106200069e63106200069d63106200078c3210620006b66110620006b56110620007345110620005ce7388620006ce6388620006ce6308620007a4410862000c7d76942200065e63942200065d63942200056e72942200074c32942200065e63142200065d63142200056e72142200074c321422000c7e76d95200047d74d95200047d73d952000c7e72d952000c7c72d95200047e71d9520004bf7459520004bc7459520004df7359520004dc7359520004f77159520004f471595200047e76195200063f65d91200063c65d91200063f75d91200063c75d9120004be71d912000c7e75991200047d7599120004be7499120004de7399120004dd7399120004f67199120004f571991200047f755912000c7c7559120004df7359120004dc7359120004ef7259120004f77159120004f47159120004fb705912000c7e75191200047d7519120004be76191200063f65191200063c65191200063e75191200063d7519120004be71191200047e76d512000c7c76d51200063f64d51200063c64d51200047e76551200047c76551200063f64551200063c64551200057471551200065f65d8d200065c65d8d200069f64d8d200069c64d8d200065f75d8d200065c75d
  | 6 => 0xf659053001e3c6590530006af6290530006ac6290530006b76190530006b46190530004be7610530004bc76105300063f65105300163c6510530006af6210530006ac6210530006b76110530006b461105300073451105300047e76941300063f64941300063c64941300066f62941300066c62941300067761941300067461941300047e76141300063f64141300063c64141300066f62141300066c6214130006776114130006746114130006f061cc1300069c648c130006cc628c130006d4618c1300047d769943000c7f76594300047f745943000c7f735943000c7d73594300047c72594300047c715943000c7e75d90300047d75d9030004f671d9030004f571d903000c7e75990300047d759903000c7e75190300047d751903000c7f76d50300047d76d50300055d73d50300047f76550300047d76550300055f735503000574715503000578705503000c7e7598c300047d7598c300047d76d4c300047f7654c300056c7254c30005ce72d0c30004dd7610c300047f755883000c7c75588300047f76948300047d769483000c7f76148300047d76148300365e658c8300065d658c83002e5e650c8300065d650c830006ce620c8300074c520c8300047f755843000c7c7558430004bf7458430004bc7458430004ef7258430004ec72584300047f76944300047d769443000c7f76144300047d761443001e3e65904300063d65904300163e65104300063d6510430006b66110430006b5611043000734511043000794418c4300047f769403000c7d76940300055d739403000c7f76140300047d76140300055d7314030004df764c0300059c744c030005cc724c030005d4714c030004fb764c030005f0714c0300047f74597200047f73597200047c715972000c7e75d93200047d75d9320004de73d9320004dd73d9320004f671d9320004f571d932000c7e75993200047d759932000c7e75193200047d751932000c7f76d53200047d76d53200057a70d53200047f76553200047d765532000574715532000578705532000c7e75d8f200047d75d8f20004be74d8f20004bd74d8f20004f671d8f20004f571d8f2000c7e7598f200047d7598f2000c7e7518f200047d7518f2000c7f76d4f200047d76d4f200047f7654f200047d7654f200056c7254f2000c7d7694b200057a7094b200057a7014b200365e658cb200065d658cb2002e5e650cb200065d650cb200074c520cb200047f755872000c7c7558720004bf7458720004bc74587200047f76947200047d769472000c7f76147200047d761472001e3e65907200063d65907200163e65107200063d6510720006b66110720006b56110720007345110720004de73d9620004dd73d96200047f74596200047f73596200047c715962000c7e75d92200047d75d9220004de73d9220
  | 7 => 0x46300047e76146300063f659063001e3c65906300063f65106300163c651063000734511063000794418c6300055d73942300055d731423000c7e76d95300047d74d95300047e72d95300047e71d9530004bf7459530004bc7459530004ef7259530004ec7259530004f77159530004f471595300047e76195300063f65d91300063c65d91300063f75d91300063c75d9130004be71d913000c7e75991300047d7599130004be7499130004ee7299130004ed7299130004f67199130004f571991300047f755913000c7c7559130004df7359130004ef7259130004ec7259130004f77159130004f4715913000c7e75191300047d7519130004be76191300063f65191300063c65191300063e75191300063d7519130004be71191300047e76d513000c7c76d51300063f64d51300063c64d51300047e76551300047c76551300063f64551300063c64551300057471551300047e76d4d300063f64d4d300063c64d4d300057a70d4d3000c7c7654d300063f6454d300063c6454d300056c7254d30005787054d3000c7e75d89300047d75d89300066f65d89300066c65d8930006af64d8930006ac64d89300066e75d89300066d75d89300066f54d89300066d54d89300066f53d89300066d53d89300066f65189300066c6518930006af6418930006ac64189300066f75189300066c75189300066f54189300066d5418930006cf73189300066f53189300066d53189300047e76949300047c76949300063f64949300063c64949300066f62949300066c62949300047e761493000c7c76149300063f64149300063c64149300066f62149300066c62149300065f658c9300365c658c9300069f648c9300069c648c930006cc628c9300065f650c93002e5c650c9300069f640c9300069c640c930006cf620c9300074c520c93000c7e75d85300047d75d8530004be74d8530004bd74d85300067765d85300067465d8530006b764d8530006b464d8530006e762d8530006e462d85300067675d85300067575d8530006b674d8530006b574d85300067754d85300067554d85300067753d85300067553d85300067652d85300067452d8530006d632d8530006d432d8530006776518530006746518530006b76418530006b46418530006e76218530006e46218530006777518530006747518530006b77418530006b47418530006775418530006755418530006775318530006755318530006765218530006745218530006d63218530006d432185300047e76945300047c76945300063f64945300063c64945300066f62945300066c62945300067761945300067461945300047e761453000c7c76145300063f64145300063c64145300055d73145300066f62145300066c6214530006776114530006746114530004be7690530004bc76905300063
  | 8 => 0x6e862d01400069c6390140006ac6290140006b461901400047d769944000c7f765944000c7f745944000c7d74594400047f73594400047c72594400047c715944000c7e75990400047d75990400047d76d50400047f765504000574715504000c7e7598c400047d7598c4000c7f76d4c400047d76d4c400053d74d4c400047f7654c400047d7654c400053f7454c400056c7254c40005787054c40005b67190c400047f755884000c7c7558840004df7358840004dc7358840004f77158840004f471588400047f76948400047d769484000c7f76148400047d76148400365e658c8400065d658c84002e5e650c8400065d650c840006ce620c840006cd620c8400074c520c8400078e420c8400047f755844000c7c75584400047f76944400047d769444000c7f76144400047d761444001e3e65904400063d65904400163e65104400063d6510440006b661104400073451104400047f769404000c7d76940400053d749404000c7f76140400047d76140400053d7414040004bf76500400059c7350040005ac7250040005b47150040004fb7650040005e872500400047f74597300047c72597300047c715973000c7e75d93300047d75d9330004ee72d9330004ed72d9330004f671d9330004f571d933000c7e75993300047d759933000c7e75193300047d751933000c7f76d53300047d76d53300047f76553300047d76553300057471553300057870553300056c7254f300047f7558b3000c7c7558b300047f7694b300047d7694b3000c7f7614b300047d7614b300365e658cb300065d658cb3002e5e650cb300065d650cb30006ce620cb30006cd620cb300074c520cb300047f755873000c7c7558730004bf7458730004bc74587300047f76947300047d769473000c7f76147300047d76147300055d731473001e3e65907300063d65907300163e65107300063d6510730006b66110730006b56110730007345110730004ee72d9630004ed72d96300056e72d96300047d74d96300065d73d96300047e72d96300066e72d96300046e72d96300066d72d96300047e71d96300067a70d963000c7e75992300047d75992300047f755923000c7c7559230004f77159230004f4715923000c7e75192300047d7519230004ee7219230004ed72192300047e76d523000c7c76d52300055d73d52300047e76552300047c76552300055f73552300057471552300057a70d4e300056c7254e30005787054e30005ce72d0e3000c7e7598a300047d7598a300047f7558a3000c7c7558a300047e7694a300047e7614a300066e6214a300066d6214a300065f658ca300365c658ca30006ce628ca300065f650ca3002e5c650ca300074c520ca3000c7e75986300047d75986300047f755863000c7c7558630004bf7458630004bc74586300047e769
  | 9 => 0xf7359540004dc7359540004ef7259540004ec7259540004f77159540004f471595400047e76195400047e76d51400057a70d514000c7c76551400057471551400057870551400065f65d8d400065c65d8d400065f75d8d400065c75d8d400065f54d8d400065d54d8d40004de72d8d4000c7e7518d400047d7518d400065f6518d400065c6518d400065e7518d400065d7518d400065f5418d400065d5418d40004de7218d400047e76d4d4000c7c76d4d400065f63d4d400065c63d4d400047e7654d400047c7654d400065f6354d400065c6354d400056c7254d4000c7e75d89400047d75d8940004de73d8940004dd73d89400066f65d89400066c65d8940006cf63d8940006cc63d89400066e75d89400066d75d89400066f54d89400066d54d8940006ce73d8940006cd73d89400066f53d89400066d53d89400066f65189400066c6518940006cf6318940006cc63189400066f75189400066c75189400066f54189400066d5418940006cf7318940006cc73189400066f53189400066d53189400047e76949400047c76949400065f63949400065c63949400066f62949400066c62949400047e761494000c7c76149400053d74149400065f63149400065c63149400066f62149400066c6214940004de768c940004dc768c9400065f658c9400365c658c940006cf628c940006cc628c940004de760c940004dc760c9400065f650c94002e5c650c940006cf620c940006cc620c9400074c520c94000c7e75d85400047d75d85400067765d85400067465d8540006d763d8540006d463d8540006e762d8540006e462d85400067675d85400067575d85400067754d85400067554d85400067753d85400067553d85400067652d85400067452d8540006d632d8540006d432d8540006776518540006746518540006d76318540006d46318540006e76218540006e46218540006777518540006747518540006b77418540006775418540006755418540006775318540006755318540006765218540006745218540006d63218540006d432185400047e76945400047c76945400065f63945400065c63945400066f62945400066c62945400067761945400067461945400047e761454000c7c76145400065f63145400065c63145400066f62145400066c62145400067761145400067461145400063f659054001e3c65905400069f63905400069c6390540006af6290540006ac6290540006b461905400063f65105400163c65105400069f63105400069c6310540006af6210540006ac6210540006b761105400073451105400047e76941400065f63941400065c63941400066f62941400066c62941400067761941400067461941400047e76141400065f63141400065c63141400066f62141400066c6214140006776114140006746114140
  | 10 => 0x4500071e32904500071c32904500153e71904500063e619045001f3a60904500047f765045000c7c765045000c7e76104500047d76104500063d64104500163e76104500063d76104500063d63104500063e62104500071e32104500071c321045001d3e71104500073671104500173761104500063e61104500173461104500173a601045000c7e76cc4500047d76cc4500053e74cc4500053d74cc4500065d63cc4500047f768c45000734418c4500047f764c45000c7c764c4500053f744c4500053c744c4500065d634c4500056f724c4500056c724c45000734414c4500057b704c45000578704c45000c7e760c4500047d760c45000c7e76c84500047d76c84500053e74c84500053d74c84500073441c845000c7e76884500047d76884500055e73884500055d73884500074c32884500047f764845000c7c76484500053f74484500053c74484500055f73484500055c73484500057b70484500057870484500047f76084500074c32084500073441084500065e32980500065c32980500063e41980500063c419805000e7a70980500047f73597400047c72597400047c715974000574715534000c7e7598f400047d7598f4000c7f76d4f400047d76d4f400047f7654f400047d7654f400056c7254f40005787054f400047f7558b4000c7c7558b40004df7358b40004dc7358b400047f7694b400047d7694b4000c7f7614b400047d7614b400053d7414b400365e658cb400065d658cb4002e5e650cb400065d650cb40006ce620cb40006cd620cb400074c520cb400047f755874000c7c75587400047f76947400047d769474000c7f76147400047d761474001e3e65907400063d65907400163e65107400063d6510740006b66110740006b56110740007345110740004f671d9640004f571d96400057671d96400063d74d96400047d73d96400047e72d96400047e71d96400067671d96400047671d96400067571d96400067a70d96400057a70d524000574715524000578705524000c7e7598e400047d7598e400047f7558e4000c7c7558e40004ef7258e40004ec7258e400047e76d4e400053d74d4e400047c7654e400053f7454e400056c7254e40005b67190e4000c7e7598a400047d7598a400047f7558a4000c7c7558a40004df7358a40004dc7358a400047e7694a400047e7614a400065f658ca400365c658ca400065f650ca4002e5c650ca400074c520ca400078e420ca4000c7e75986400047d75986400047f755864000c7c75586400047e76946400047e76146400067661146400067561146400063f659064001e3c6590640006b661906400063f65106400163c65106400073451106400053d74942400053d74142400073a50d02400073954d024000c7e76d95400047d73d95400047e72d95400047e71d9540004d
  | 11 => 0x67661d06500047f76906500063d64906500063f76906500063c76906500063d63906500063e62906500071e32906500071c32906500063e61906500047f76506500047c76506500047e76106500047d76106500063d64106500067661106500063e76106500063d76106500063d63106500063e62106500071e32106500071c32106500073671106500063e61106500073661106500063661106500073561106500047e76cc6500047d76cc6500053e74cc6500053d74cc6500047f768c65000734418c6500047f764c6500047c764c6500053f744c6500053c744c6500056f724c6500056c724c65000734414c6500057b704c65000578704c6500047e760c6500047d760c6500047e76c86500047d76c86500053e74c86500053d74c86500073441c86500047e76886500047d76886500055e73886500055d73886500074c32886500047f76486500047c76486500053f74486500053c74486500055f73486500055c73486500057b70486500057870486500047f76086500074c32086500073441086500063f64551500057471551500065f6354d500056c7254d50004de73d8950004dd73d89500066f62949500066c6294950006cf620c950006cc620c95002f4c520c950004be74d8550004bd74d8550006776194550006746194550006b76110550006b4611055001734511055000e3f74590500047f73590500047c72590500067771590500047c71590500067471590500047471590500047f7458c5000e5f7358c500066f7258c500047c7258c500066c7258c500046c7258c500047c7158c5000c7e76d0c500047d76d0c500056e72d0c500056d72d0c5000c7e7690c500047d7690c50005767190c50005757190c500047d7650c500057b7050c50005787050c5000c7e7610c500047d7610c500047d74988500047d739885000e6e72988500047e719885000c7e76d08500047d76d08500063d64d08500055e73d08500055d73d08500047f76908500047f765085000c7c76508500063d64508500055f73508500055c73508500057771508500057471508500057b705085000578705085000c7e76108500047d761085000c7e76cc8500047d76cc8500047f768c8500065d638c8500065f768c8500365c768c8500065d648c85002d5e728c8500065e628c8500375a608c8500047f764c85000c7c764c85000c7e760c8500047d760c8500065d630c85002e5e760c8500065d760c8500065d640c8500355e720c8500074e720c85002f4f620c8500065e620c85002f4c620c8500074e420c8500074d420c85002f5a600c8500047d74984500047d73984500047e72984500065e32984500065c329845000e76719845000c7e76d04500047d76d04500047f76904500063d64904500063f769045001e3c76904500063d63904500063e629
  | 12 => 0x432d04210063f659042101e3c65904210078c3290421005b671904210063f65104210163c65104210078c3210421007365110421007345110421004f57610421016746510421007375410421007355410421007c43210421006b67610421006b57610421007367510421007357510421007376510421016b66510421016b46510421007346510421016346510421006b76310421006b56310421007375310421007355310421007a67210421007a57210421006b66210421007365210421007345210421007a73210421007963210421007943210421007a43210421007843210421007a441c8421007c43288421004ef7648421005cc7348421005e87048421004f77648421005b47448421005f0704842100c7e75980210047d7598021006cc3298021006b441980210047f755802100c7c7558021004bf7458021004bc7458021004df7358021004dc73580210063d64952500057970952500063d64552500057771552500057471552500065d6354e500056f7254e500056c7254e50004df7358a50004dc7358a500066e6294a500055f7354a500055c7354a500057b7054a50006ce620ca50006cd620ca5002f4f520ca5002f4c520ca50004bf7458650004bc74586500067661946500053f74546500053c7454650006b66110650006b561106500173751106500173451106500057671d92500057571d92500057a70d92500047f73592500047c72592500047c71592500063d64192500057a70192500056e72d8e500056d72d8e500057a70d8e500047f7458e500047c7258e500047c7158e500057a7018e500047e76d0e500047d76d0e500056e72d0e500056d72d0e500047e7690e500047d7690e50005767190e50005757190e500047d7650e500047e7610e500047d7610e500055e73d8a500055d73d8a500057a70d8a500047d7498a500047d7398a500047e7198a500055f7358a500055c7358a500057a7018a500047e76d0a500047d76d0a500055e73d0a500055d73d0a500047f7690a500047f7650a500047c7650a500055f7350a500055c7350a50005777150a50005747150a500057b7050a50005787050a500047e7610a500047d7610a500047e76cca500047d76cca500066e62cca500047f768ca500065d638ca500065f768ca500065c768ca500065d648ca500065e628ca500047f764ca500047c764ca500047e760ca500047d760ca500065d630ca500066e620ca500065e760ca500065d760ca500065d640ca500074e720ca500065e620ca500074e620ca500064e620ca500074d620ca500074e420ca500074d420ca500053e74d86500053d74d86500057a70d86500047d74986500047d73986500047e72986500065e32986500065c32986500053f74586500053c74586500057a70186500047e76d06500047d76d0650
  | 13 => 0x4d210047c7654d210063f6454d210063c6454d210065f6354d210065c6354d210056c7254d210047e76949210063f64949210063c64949210065f63949210065c63949210047e76149210063f64149210063c64149210065f63149210065c6314921004de768c9210065f658c9210365c658c9210069f648c9210069c648c921004de760c9210065f650c92102e5c650c9210069f640c9210069c640c9210074c520c9210047e76945210063f64945210063c64945210065f63945210065c63945210047e76145210063f64145210063c64145210065f63145210065c6314521004be76905210063f659052101e3c65905210069f63905210069c6390521004be76105210063f65105210163c65105210069f63105210069c6310521007345110521006b464c8521006cc638852100c7e75d81210047d75d81210067b65d81210067865d8121006bb64d8121006b864d8121006db63d8121006d863d81210067a75d81210067975d81210067b54d81210067954d81210067b53d81210067953d81210067a52d81210067852d8121006da32d8121006d832d81210067a51d81210067851d8121006ba41d8121006b841d81210067b6518121006786518121006bb6418121006b86418121006db6318121006d863181210067b75181210067875181210067b54181210067954181210067b53181210067953181210067a5218121006785218121006da3218121006d832181210067a5118121006785118121006ba4118121006b84118121006f32118121006ea21181210047d74d94210047d73d94210047e72d94210066e72d94210047e71d94210067671d94210047e70d942100c7e75990210047d75990210047f755902100c7c755902100c7e75190210047d75190210047e76d502100c7c76d50210057671d50210047e76550210047c765502100574715502100c7e7598c210047d7598c210047f7558c2100c7c7558c2100c7e7518c210047d7518c210047e76d4c2100c7c76d4c210056e72d4c210047e7654c210047c7654c210056c7254c2100c7e75988210047d7598821004be7498821004bd749882100576719482100576711482103e6c65cc8210065f658c8210365c658c821005ce728c8210065f650c82102e5c650c8210074e520c8210074c520c821004ed760c82102e6c650c8210074f530c8210074d530c821006ce760c821006cd760c8210074e750c8210074d750c8210074f650c82102ece650c82102ecc650c8210074c650c82102e4c650c821006cf640c821006cd640c8210074f540c8210074d540c821007c6710c821007c5710c82100c7e75984210047d7598421004de7398421004dd7398421006cc32984210056e72944210074c32944210047e761442100c7c76144210056e72144210074c32144210267465d0421007c
  | 14 => 0x4dd731922100c7f76d52210047d76d52210047f76552210047d765522100574715522100c7e75d8e210047d75d8e2100c7e7598e210047d7598e210065e6598e210065d6598e210065e7598e210065d7598e210065f5498e210065d5498e210065e6558e210065d6558e210065e7558e210065d7558e210065f5458e210065d5458e21006cf7258e2100c7e7518e210047d7518e2100c7f76d4e210047d76d4e210065e63d4e210065d63d4e210056e72d4e210047f7654e210047d7654e210065e6354e210065d6354e210056c7254e210065e6394a210065d6394a210065e6314a210065d6314a2103e6e65cca210365e658ca210065d658ca2102e5e650ca210065d650ca210074e520ca210074c520ca2102e6e650ca21006cd630ca210074f530ca210074d530ca21005cd760ca21006cd760ca210074e750ca210074d750ca2102ece650ca210074e650ca2102e4e650ca210074d650ca2102ecc650ca21006cf640ca21006cd640ca210074f540ca210074d540ca2100c7d76946210065e63946210065d63946210056e72946210074c32946210065e63146210065d63146210056e72146210074c321462101e3e65906210063d65906210069e63906210069d63906210078c32906210163e65106210063d65106210069e63106210069d63106210078c3210621007345110621006cc32982210047f755822100c7c755822100c7e76d95210047d74d95210047d73d95210047e70d9521004bf7459521004bc7459521004df7359521004dc7359521004fb7059521004f870595210047e76195210063f65d91210063c65d91210063f75d91210063c75d912100c7e75991210047d7599121004be7499121004de7399121004dd7399121004fa7099121004f970991210047f755912100c7c7559121004df7359121004dc7359121004f77159121004fb7059121004f8705912100c7e75191210047d7519121004be76191210063f65191210063c65191210063e75191210063d75191210047e76d512100c7c76d51210063f64d51210063c64d51210047e76551210047c76551210063f64551210063c64551210057471551210065f65d8d210065c65d8d210069f64d8d210069c64d8d210065f75d8d210065c75d8d210065f54d8d210065d54d8d2100c7e7598d210047d7598d21004be7498d21004bd7498d21004de7398d21004fa7098d21004f97098d210047f7558d2100c7c7558d21004bf7458d21004bc7458d21004ef7258d21004fb7058d21004f87058d2100c7e7518d210047d7518d21004de7618d210065f6518d210065c6518d210069f6418d210069c6418d210065e7518d210065d7518d210065f5418d210065d5418d210047e76d4d2100c7c76d4d210063f64d4d210063c64d4d210065f63d4d210065c63d4d210047e765
  | 15 => 0xe75990310047d759903100c7e75190310047d751903100c7f76d50310047d76d50310047f76550310047d765503100574715503100c7e7598c310047d7598c31004be7498c31004bd7498c310047d76d4c310047f7654c310056c7254c310047f755883100c7c75588310047f76948310047d769483100c7f76148310047d76148310365e658c8310065d658c83102e5e650c8310065d650c831006ce620c8310074c520c8310047f769443100c7d76944310055d739443100c7f76144310047d76144310055d731443101e3e65904310063d65904310163e65104310063d6510431006b66110431007345110431004df764c431005cc724c43100756514c431005d8704c431004f7764c43100755534c431005f0704c4310047f755803100c7c7558031004bf7458031004bc7458031004ef7258031004ec7258031004be74d9721004bd74d97210047f74597210047f73597210047c705972100c7e75d93210047d75d932100c7e75993210047d75993210063e65993210063d65993210063e75993210063d75993210063e65593210063d65593210063e75593210063d7559321006b7715932100c7e75193210047d751932100c7f76d53210047d76d53210063e64d53210063d64d53210057671d53210047f76553210047d76553210063e64553210063d645532100574715532100c7e75d8f210047d75d8f21004be74d8f21004bd74d8f21004fa70d8f21004f970d8f2100c7e7598f210047d7598f2100c7e7518f210047d7518f21004be7418f21004bd7418f2100c7f76d4f210047d76d4f210063e64d4f210063d64d4f210047f7654f210047d7654f210063e6454f210063d6454f210056c7254f2100c7d7694b210063e6494b210063d6494b21005767194b210063e6414b210063d6414b21005767114b210365e658cb210065d658cb210069e648cb210069d648cb2102e5e650cb210065d650cb210069e640cb210069d640cb210074c520cb210063e64947210063d64947210063e64147210063d64147210267665d072101e3e65907210063d65907210163e65107210063d6510721007365110721007345110721016766510721006b56410721007375410721007355410721005b57610721006b57610721007367510721007357510721016b66510721007366510721016366510721007356510721016b46510721006b76310721006b56310721007375310721007355310721007365210721007345210721007963210721007943210721006b441983210047f755832100c7c7558321004de73d9621004dd73d96210047f74596210047f73596210047c705962100c7e75d92210047d75d9221004de73d9221004dd73d9221004fa70d9221004f970d922100c7e75992210047d759922100c7e75192210047d7519221004de7319221
  | 16 => 0x51310047c76551310063f64551310063c64551310057471551310047e76d4d310063f64d4d310063c64d4d310057671d4d3100c7c7654d310063f6454d310063c6454d310056c7254d31005747154d3100c7e75d89310047d75d89310066f65d89310066c65d8931006af64d8931006ac64d89310066e75d89310066d75d89310066f54d89310066d54d89310066f53d89310066d53d89310066f65189310066c6518931006af6418931006ac64189310066f75189310066c75189310066f54189310066d5418931006cf73189310066f53189310066d53189310047e76949310047c76949310063f64949310063c64949310066f62949310066c62949310047e761493100c7c76149310063f64149310063c64149310066f62149310066c62149310065f658c9310365c658c9310069f648c9310069c648c931006cc628c9310065f650c93102e5c650c9310069f640c9310069c640c931006cf620c9310074c520c9310047e76945310063f64945310063c64945310066f62945310066c62945310047e76145310063f64145310063c64145310066f62145310066c6214531004f676d05310267465d0531006e462d0531004be76905310063f659053101e3c6590531006af6290531006ac6290531005b67190531004be76105310063f65105310163c6510531006af6210531006ac6210531007365110531007345110531016746510531006b76410531007375410531007355410531006e46210531005b67610531006b67610531007367510531007357510531007376510531016b66510531016b46510531007346510531016346510531007375310531007355310531007a76210531006b46210531007a46210531006a46210531007365210531007345210531007963210531007943210531005b674cc531006cc628c53100794418c53100c7e75d81310047d75d81310067b65d81310067865d8131006bb64d8131006b864d8131006eb62d8131006e862d8131007b041d81310067a75d81310067975d81310067b54d81310067954d81310067b53d81310067953d81310067a52d81310067852d8131006da32d8131006d832d81310067a51d81310067851d8131006ba41d8131006b841d8131006b441181310067b6518131006786518131006bb6418131006b86418131006eb6218131006e86218131007b041181310067b75181310067875181310067b54181310067954181310067b53181310067953181310067a5218131006785218131006da3218131006d832181310067a5118131006785118131006f34118131006ba4118131006b84118131006f04118131006b04118131006f33118131006da31181310047d769943100c7f76594310047f74594310047c72594310047c705943100c7e75d90310047d75d9031004f671d903100c7
  | 17 => 0x63d755933100c7e75193310047d751933100c7f76d53310047d76d53310063e64d53310063d64d53310055d73d53310047f76553310047d76553310063e64553310063d64553310057471553310063e64d4f310063d64d4f310063e6454f310063d6454f310056c7254f310047f7558b3100c7c7558b310047f7694b310047d7694b310063e6494b310063d6494b3100c7f7614b310047d7614b310063e6414b310063d6414b310365e658cb310065d658cb310069e648cb310069d648cb3102e5e650cb310065d650cb310069e640cb310069d640cb31006ce620cb31006cd620cb310074c520cb310063e64947310063d64947310063e64147310063d641473101e3e65907310063d65907310163e65107310063d65107310073451107310047f755833100c7c7558331004ee72d9631004ed72d96310056e72d96310047d74d96310065d73d96310047e72d96310066e72d96310046e72d96310066d72d96310067671d96310047e70d963100c7e75992310047d75992310047f755923100c7c755923100c7e75192310047d7519231004ee7219231004ed72192310047e76d523100c7c76d52310057671d52310047e76552310047c76552310057471552310057671d4e310056c7254e31005747154e3100c7e7598a310047d7598a310047f7558a3100c7c7558a310047e7694a310047e7614a310066e6214a310066d6214a310065f658ca310365c658ca31006ce628ca310065f650ca3102e5c650ca310074c520ca310055d73946310055d73146310267465d06310063f659063101e3c65906310063f65106310163c6510631007365110631007345110631016746510631007375410631007355410631006b67610631006b57610631007367510631007357510631007376510631016b66510631016b46510631007346510631016346510631007967310631007957310631007375310631007355310631006b66210631007365210631007345210631007963210631007943210631005b674cc63100c7e75982310047d7598231006b441982310047f755823100c7c755823100c7e76d95310047d74d95310047e72d95310047e70d9531004bf7459531004bc7459531004ef7259531004ec7259531004fb7059531004f870595310047e76195310063f65d91310063c65d91310063f75d91310063c75d9131006b571d913100c7e75991310047d7599131004be7499131004ee7299131004ed7299131004fa7099131004f970991310047f755913100c7c7559131004ef7259131004ec7259131004fb7059131004f8705913100c7e75191310047d7519131004be76191310063f65191310063c65191310063e75191310063d75191310047e76d513100c7c76d51310063f64d51310063c64d51310055d73d51310057671d51310047e765
  | 18 => 0x471148410053e70148410153e75cc8410053d75cc8410072c52cc841005b671cc841005b571cc8410053f758c8410153c758c8410071f538c8410071d538c8410071f758c8410071c758c8410071e658c8410071d658c8410059e728c8410071e528c8410071c528c84100797718c84100794718c84104f97518c84104f94518c8410053f754c8410153c754c841005b7714c841005b4714c8410153e750c8410053d750c8410071f530c8410071d530c8410072c520c841005b6710c841005b5710c8410071e750c8410071d750c8410071e650c8410071d650c8410059e720c8410078e720c8410078e620c8410078d620c8410478f520c8410071e520c8410071c520c8410478c520c8410070c520c84100796710c84100795710c84104797510c84104794510c84101e3e65984410063d65984410063f759844101e3c759844101e3f53984410063d53984410063e529844101e3c52984410069e32984410069c3298441006b67198441007377598441015b67598441015b47598441007347598441007366598441007356598441005b57398441007375398441007355398441005b67298441007365298441007345298441007963298441007943298441005b67098441015b671944410053f76944410053d76944410053d73944410053e72944410071e32944410071c32944410153e71944410153671944410063e61944410073661944410053e709444101cbf7654441015b771544410173451544410153f76144410053d76144410053d73144410053e72144410071e32144410071c32144410053e711444101736711444101e3e61144410073661144410053e70144410173776144410153776144410173676144410173576144410053576144410173476144410173773144410173673144410173573144410053573144410173473144410073763144410073663144410073563144410073463144410173772144410173672144410053672144410173572144410173472144410073762144410073662144410073562144410073462144410073732144410073632144410071632144410073532144410073432144410071432144410173770144410173670144410053670144410173570144410173470144410153e75d80410053d75d80410073451d80410073451980410053f75580410153c75580410059f73580410059c7358041005af7258041005ac72580410073451580410153e75180410053d75180410059e73180410059d7318041005ae7218041005ad7218041007345118041004be74d9731004bd74d97310047f74597310047c72597310047c705973100c7e75d93310047d75d933100c7e75993310047d75993310063e65993310063d65993310063e75993310063d75993310063e65593310063d65593310063e7559331
  | 19 => 0x841005b571d08410053f75908410153c75908410053f75508410153c75508410059f73508410059c7350841005b77150841005bb7050841005b870508410153e75108410053d75108410365e658c8410065d658c8410071f548c8410071d548c84102e5e650c8410065d650c8410071f540c8410071d540c841006ce620c841006cd620c8410074c520c8410078e420c8410078d420c84101e3f54984410063d54984410047f769444100c7d76944410053d749444101576719444100c7f76144410047d76144410053d74144410167676144410057576144410167576144410047576144410173674144410057574144410173574144410267664144410057573144410073743144410073643144410073543144410073443144410057672144410073742144410073642144410073542144410073442144410075632144410075432144410057670144410153e75d04410053d75d04410073451d0441015747590441007375490441007355490441004bf76504410053f75504410153c7550441007345150441004f776504410157475504410073754504410047f755804100c7c7558041004df7358041004dc7358041004ef7258041004ec72580410163e65d9441005b671d94410053d76994410053d73994410053e72994410173771994410173471994410053e7099441015b471594410173451594410153f76594410163f76594410053f73594410053c72594410173771594410073471594410053c70594410153e75d8c410053d75d8c41005ae72d8c41005ad72d8c41005b671d8c410153e7598c410053d7598c410153e7518c410053d7518c41005b67118c410153f76d4c410053d76d4c410053e72d4c410173771d4c410053e71d4c410173471d4c410053e70d4c410053d7594c41005b67194c41005b57194c41017345194c41005af7254c41005ac7254c41005b77154c41005b47154c41017375154c41017345154c410053f7654c410053d7654c410153f7354c410171f7354c410072f7254c410053c7254c410072c7254c410052c7254c41007377154c410053c7154c41007347154c41005347154c410053c7054c410153e75d88410053d75d88410059e73d88410059d73d8841005b671d88410053f75588410153c75588410059f73588410059c7358841005bb7058841005b870588410153e75188410053d7518841005b67118841005b67194841005b571948410173751948410173451948410053f76948410053d76948410053d73948410153e72948410053e71948410073671948410053671948410073571948410053e70948410059f73548410059c7354841005b77154841005b471548410173451548410153f76148410053d76148410053d73148410053e72148410172e72148410173771148410053e71148410173
  | 20 => 0x53f758ca4101d3c758ca410071f538ca410071d538ca410071f758ca410071c758ca410071f658ca410071c658ca410071e528ca410071c528ca410053f754ca4101d3c754ca4101d3e750ca410053d750ca410071f530ca410071d530ca410072c520ca410071e750ca410071d750ca410071f650ca410071c650ca410078e720ca410078f620ca410078c620ca410578f520ca410071e520ca410071c520ca410578c520ca410070c520ca4101f3751946410053d73946410053e72946410071e32946410071c32946410053e7094641014bf76546410053d73146410053e72146410071e32146410071c321464101f3671146410053e701464101d3e75d82410053d75d82410059e73d82410059d73d8241005ae72d8241005ad72d824101d3e75982410053d75982410053f755824101d3c755824100c7e76d95410047d73d95410047e72d95410047e70d954101cbf7459541024f771595410047e76195410047e76d51410057671d514100c7c765514100574715514100c7e7518d410047d7518d410047e76d4d4100c7c76d4d410047e7654d410047c7654d410056c7254d4100c7e75d89410047d75d8941004de73d8941004dd73d89410047e76949410047c76949410047e761494100c7c76149410065f658c9410365c658c9410065f650c94102e5c650c941006cf620c941006cc620c9410074c520c9410047e76945410047e76145410267465d05410063f659054101e3c659054100c7e75d81410047d75d81410163f54d94410047d7699441014bc7459441014f4715944100c7f76594410163f74594410063c74594410047f73594410047c72594410167771594410067471594410047c705944100c7e75990410047d75990410047d76d50410053d76d50410163d76d50410053d73d50410053e72d50410173771d50410173471d50410053e70d504100cbd76950410053d759504100e3e6595041005b571950410173451950410047f76550410153f745504100e3e6555041005b771550410173751550410173451550410053f76550410063f76550410053f73550410053c72550410073771550410073471550410053c705504100c7e7598c410047d7598c4100c7f76d4c410047d76d4c410053d74d4c410047f7654c410047d7654c410053f7454c410056c7254c41005747154c410153e75d0c410053d75d0c41005ae72d0c41005ad72d0c410153e7590c410053d7590c41005b57190c410153e7550c410053d7550c410153e7510c410053d7510c41005b57110c410047f755884100c7c7558841004df7358841004dc7358841004fb7058841004f870588410047f76948410047d76948410053d749484100576719484100c7f76148410047d76148410053d74148410153e75d08410053d75d08410059e73d08410059d73d
  | 21 => 0xc75583410063d74d96410047d73d96410047e72d96410067671d96410047e70d964101e3f54596410055d73196410057671d524101e3e76d524101e3d76d52410053d73d52410053e72d524101f3671d524101f3571d52410053e70d524100e3c659524100574715524100cbf765524100e3f765524100e3c76552410053f73552410053c72552410073771552410073471552410053c705524100c7e7598e410047d7598e410047f7558e4100c7c7558e41004ef7258e41004ec7258e410047e76d4e410053d74d4e410047c7654e410053f7454e410065e6354e410065d6354e410056c7254e4101d3e75d0e410053d75d0e41005ae72d0e41005ad72d0e4101d3e7590e410053d7590e4101d3e7550e410053d7550e4101d3e7510e410053d7510e4100c7e7598a410047d7598a410047f7558a4100c7c7558a41004df7358a41004dc7358a410047e7694a410053d7494a410047e7614a410053d7414a4101d3e75d0a410053d75d0a410059e73d0a410059d73d0a410053f7590a4101d3c7590a410053f7550a4101d3c7550a410059f7350a410059c7350a41005bb7050a41005b87050a4101d3e7510a410053d7510a410065f658ca410365c658ca410071f548ca410071d548ca410065f650ca4102e5c650ca410071f540ca410071d540ca410074c520ca410078e420ca410078d420ca410053d74946410053d741464101d3e75d06410053d75d06410073651d06410267465d06410073554d064100c7e75982410047d75982410047f755824100c7c7558241005b671d96410053d73d96410053e72d96410053e71d96410073671d96410053671d96410053e70d964101e3c655964101e3e761964101f1e73196410053d731964101f1d73196410051d73196410053e72196410053e711964101f3671196410053671196410053e7019641005b671d8e4101d3e7598e410053d7598e410053f7558e4101d3c7558e41005af7258e41005ac7258e4101d3e7518e410053d7518e41005b67118e410053e76d4e4101d3c76d4e410053e72d4e410053e71d4e410053e70d4e41005af7254e41005ac7254e410053e7654e410053c7654e4101f1f7354e410071e6354e410071d6354e410072f7254e410053c7254e410072c7254e410052c7254e410053c7154e410053c7054e4101d3e75d8a410053d75d8a410059e73d8a410059d73d8a41005b671d8a41005ba70d8a41005b970d8a4101d3e7598a410053d7598a410053f7558a4101d3c7558a410059f7358a410059c7358a41005b67118a410053e7694a410053c7694a410053d7394a410053e7194a410053e7094a410059f7354a410059c7354a410053e7614a4101d3c7614a410053d7314a4101f2e7214a410053e7114a410053e7014a4101d3e75cca410053d75cca410072c52cca41
  | 22 => 0xca510065d760ca510065d640ca510074e720ca510065e620ca510074e620ca510064e620ca510074d620ca510074e420ca510074d420ca510047d74982510047d73982510047e72982510065e32982510065c32982510063f75d915101e3f53d915101e3c52d915101e3c51d915101e3c50d91510163e75191510163f53191510163c5219151016b751191510163c5119151016b451191510163c50191510063f64551510063c64551510057471551510063f6454d510063c6454d510065f6354d510056c7254d51004de73d8951004dd73d89510063f64949510063c64949510066c62949510069f648c9510069c648c9510069f640c9510069c640c951006cf620c951006cc620c95102f4c520c9510063f64945510063c649455100e3f74590510047f73590510047c72590510067471590510047c70590510047f7458c5100e5f7358c510066f7258c510047c7258c510066c7258c510046c7258c510047c7058c5100c7e76d0c510047d76d0c510065d63d0c510056e72d0c510056d72d0c5100c7e7690c510047d7690c51005767190c51005757190c510047d7650c51005777150c51005747150c5100c7e7610c510047d7610c510065d6310c510047d74988510047d739885100e6e72988510047e709885100c7e76d08510047d76d08510055e73d08510055d73d08510047f76908510057671908510057571908510047f765085100c7c76508510055f73508510055c73508510057771508510057471508510057b705085100578705085100c7e76108510047d761085100c7e76cc8510047d76cc8510047f768c8510065d638c8510065f768c8510365c768c8510065d648c85102d5e728c8510065e628c85103756618c8510047f764c85100c7c764c85100c7e760c8510047d760c8510065d630c85102e5e760c8510065d760c8510065d640c8510355e720c8510074e720c85102f4f620c8510065e620c85102f4c620c8510074e420c8510074d420c85102f56610c8510065e32984510065c329845100e7671984510047d74980510047d73980510047e72980510065e32980510065c329805100e7a70980510267751597410047f73597410047c72597410067771597410267471597410047c705974100574715534100c7e7598f410047d7598f4100c7f76d4f410047d76d4f410047f7654f410047d7654f410056c7254f41005747154f410047f7558b4100c7c7558b41004df7358b41004dc7358b410047f7694b410047d7694b41005767194b4100c7f7614b410047d7614b410365e658cb410065d658cb4102e5e650cb410065d650cb41006ce620cb41006cd620cb410074c520cb410057576147410267576147410057574147410057573147410057672147410075632147410075432147410057670147410047f755834100c7
  | 23 => 0x55d75d08320074c52d08320055f759083202d5c75908320074e52908320074c5290832005cf7690832005cd76908320074f759083202dce759083202dcc75908320074c759083202d4c75908320074e65908320074d6590832005cd74908320078e64908320078d64908320074f54908320074d5490832005ce7190832005ce7090832004df76508320055f755083202d5c75508320074e52508320074c5250832005d77150832005d47150832005db7050832005d87050832005cf7650832006cf76508320074f755083202dce755083202dcc75508320074c755083202d4c75508320074e65508320074d65508320078f74508320074f54508320074d5450832007c77150832005cc7150832007c47150832005c47150832007cb7050832005cc7050832007c87050832005c8705083202d5e75108320055d7510832005ce72108320074c521083202d5e75d84320055d75d84320059e74d84320059d74d84320074c52d84320074c52984320055f755843202d5c75584320059f74584320059c74584320074c5258432005db7058432005d8705843202d5e75184320055d75184320074c521843202d5e75d80320055d75d80320074c52d80320074c52980320055f755803202d5c75580320059f74580320059c74580320074c5258032005d77158032005d4715803202d5e75180320055d75180320059e74180320059d74180320074c5218032005d67118032005d571180320063d64952510057571952510063d6455251005757194e510065d6354e510056f7254e510056c7254e51004df7358a51004dc7358a510066e6294a510055f7354a510055c7354a51005777154a51006ce620ca51006cd620ca5102f4f520ca5102f4c520ca510057671d92510267661992510047f73592510047c72592510047c70592510063d64192510057671192510056e72d8e510056d72d8e510057671d8e510047f7458e510047c7258e510047c7058e51005767118e510047e76d0e510047d76d0e510056e72d0e510056d72d0e510047e7690e510047d7690e51005767190e51005757190e510047d7650e510047e7610e510047d7610e510055e73d8a510055d73d8a510057671d8a510047d7498a510047d7398a510047e7098a510055f7358a510055c7358a51005767118a510047e76d0a510047d76d0a510055e73d0a510055d73d0a510047f7690a510047f7650a510047c7650a510055f7350a510055c7350a51005777150a51005747150a510057b7050a51005787050a510047e7610a510047d7610a510047e76cca510047d76cca510066e62cca510047f768ca510065d638ca510065f768ca510065c768ca510065d648ca510065e628ca510047f764ca510047c764ca510047e760ca510047d760ca510065d630ca510066e620ca510065e760
  | 24 => 0xd76148320056d741483202f4e73148320056d731483202f4d731483203e6e63148320074f43148320074e43148320074d43148320074c43148320056e71148320056e7014832004ed769083202d6c75908320074f53908320074d539083202d6c7550832005cf73508320074f53508320074d5350832005e47150832005e8705083202d5e75cc8320055d75cc8320074c52cc83202d6c758c8320074f538c8320074d538c832004df764c8320055f754c83202d5c754c8320074c524c832004ef764c83202d6c754c8320074f534c8320047f755843200c7c7558432004bf7458432004bc7458432004fb7058432004f870584320047f755803200c7c7558032004bf7458032004bc7458032004f77158032004f47158032005ce72d94320055d76994320055d749943202f4f729943202f4c72994320055e71994320055e709943202dcc725943202f4c525943202d5f765943202e5f76594320055f745943202f4f72594320074c72594320055c71594320055c705943202d5e75d90320055d75d9032005ce72d9032005d671d9032005d571d903202d5e75990320055d759903202d5e75190320055d7519032005ce721903202d5f76d50320055d76d503202f4f72d50320055e72d503202f4c72d50320055e71d50320055e70d50320055d759503202f1f5495032005ce7295032005cd729503202f4c5295032005cf7255032005cc725503202f4f525503202f4c5255032005d77155032005d471550320055f76550320055d765503202d5f745503202f1f74550320074f72550320055c72550320074c72550320054c72550320075771550320055c71550320075471550320055471550320055c70550320365e65988320065d65988320065f75988320365c75988320365f54988320065d5498832006ce72988320074f759883202dce759883202dcc75988320074c75988320074e65988320074d6598832005cd74988320074f54988320074d5498832005ce7198832005ce709883202dce72948320055f76948320055d76948320055d749483202d5e729483202d4e72948320065e62948320074e62948320055e71948320055e7094832034df765483202dcf725483202f4c525483202d5f76148320055d76148320055d74148320055e721483202f4e72148320365e62148320074e62148320055e71148320055e701483202f4f761483202d4f761483202f4e761483202f4d76148320054d761483202f4c761483202f4f741483202f4e741483202f4d74148320054d741483202f4c74148320074f64148320074e64148320074d64148320074c641483202f4f711483202f4e71148320054e711483202f4d711483202f4c711483202f4f701483202f4e70148320054e701483202f4d701483202f4c7014832004dd76d083202d5e75d0832
  | 25 => 0x52320071e64552320071d64552320055c72552320075771552320055c71552320075471552320055471552320055c70552320055d7494a320055e7194a320055e7094a3202cdf7654a320055d7414a320374e7214a320055e7114a320055e7014a320355e75d0a320055d75d0a320055f7590a320355c7590a320055f7550a320355c7550a32005d77150a32005d47150a32005db7050a32005d87050a320355e7510a320055d7510a320355e75d86320055d75d86320059e74d86320059d74d8632005da70d8632005d970d86320355e75986320055d75986320055f75586320355c75586320059f74586320059c74586320355e75d82320055d75d82320059e74d82320059d74d8232005d671d8232005d571d82320355e75982320055d75982320055f75582320355c755823200c7e76d95320047d74d95320047e71d95320047e70d9532034df735953203cef72595320047e761953200c7e75991320047d7599132004dd7399132004ed72991320047f755913200c7c7559132004df7359132004f77159132004f47159132004fb7059132004f8705913200c7e75191320047d75191320047e76d513200c7c76d51320047e76551320047c76551320057471551320047e76d4d320056e72d4d3200c7c7654d320056c7254d320047e76949320047e761493203e6c65cc9320065f658c9320365c658c93200c7e75d85320047d75d8532004be74d8532004bd74d853200c7e75d81320047d75d81320047d769943202cdc735943202cec725943200c7f76594320047f745943202e5f73594320065c735943202e6f72594320066c72594320047c71594320047c705943200c7e75d90320047d75d9032004f671d9032004f571d903200c7e75990320047d759903200c7e75190320047d751903200c7f76d50320047d76d50320055d73d50320047f76550320047d76550320055f73550320056c725503200574715503200c7e7598c320047d7598c320047d76d4c320055d76d4c3202e5d76d4c320055d74d4c3202f4f72d4c3202f4c72d4c320055e71d4c320055e70d4c3200cdd7694c320055d7594c32005cd7294c3202f4c5294c320047f7654c3202d5f7354c3200e5e6554c32005cf7254c3202f4f5254c3202f4c5254c320055f7654c320065f7654c320055f7454c320074f7254c320074c7254c320055c7154c320055c7054c3202d5e75d0c320055d75d0c32005cd72d0c32004dd7690c3202d5e7590c320055d7590c32005d67190c32005d57190c3202d5e7550c320055d7550c32004dd7610c3202d5e7510c320055d7510c32005cd7210c320365f53988320065d53988320047f769483200c7d76948320055d739483202d6e729483200c7f76148320047d76148320055d731483202e6e76148320056d761483202e6d76148320046
  | 26 => 0x47d75990420047d76d50420047f765504200574715504200c7e7598c420047d7598c4200c7f76d4c420047d76d4c420047f7654c420047d7654c420056c7254c420047f769484200c7d76948420053d749484200c7f76148420047d76148420053d7414842004bf7650842005b47150842005b87050842004ef7650842005e870508420047f755844200c7c75584420047f755804200c7c7558042004df7358042004dc7358042004f77158042004f471580420047f74597320066f725973203e6c72597320047c71597320047c705973200c7e75d93320047d75d9332004f671d9332004f571d9332004fa70d9332004f970d933200c7e75993320047d759933200c7e75193320047d751933200c7f76d53320047d76d53320047f76553320047d76553320056c72553320057471553320056c7254f320056d7614b3203e6d7614b320056d7414b320056d7314b320056e7114b320056e7014b3203d6c7590b3203d6c7550b32005e47150b32005e87050b320047f755873200c7c7558732004bf7458732004bc74587320047f755833200c7c75583320047d74d96320065d73d96320066e72d96320047e71d96320047e70d96320053d741963200c7e75992320047d75992320047f755923200c7c7559232004f77159232004f4715923200c7e75192320047d75192320047e76d523200c7c76d52320055d73d52320047e76552320047c76552320063e64552320063d64552320055f73552320057471552320056e72d4e320365e76d4e320365d76d4e320055d74d4e320374e72d4e320374d72d4e320055e71d4e320055e70d4e320056c7254e3200cdf7654e3200e5f7654e3200e5c7654e320055f7454e320074f7254e320074c7254e320055c7154e320055c7054e320355e75d0e320055d75d0e320355e7590e320055d7590e32005d67190e32005d57190e320355e7550e320055d7550e320355e7510e320055d7510e320055d7394a320055d7314a320355e75cca320055d75cca3203e6c65cca3200c7e75986320047d75986320047f755863200c7c7558632004bf7458632004bc745863200c7e75982320047d75982320047f755823200c7c7558232005ce72d96320055d74d96320055e72d96320074e72d96320054e72d96320055e71d96320055e70d96320365e76196320371e74196320055d74196320371d74196320051d74196320055e72196320374e72196320054e72196320055e71196320055e7019632005ce72d92320355e75992320055d75992320055f75592320355c7559232005d77159232005d471592320355e75192320055d7519232005ce72192320055e76d52320355c76d52320055e72d52320055e71d52320055e70d52320371f5495232005d77155232005d471552320055e76552320055c76552320371f745
  | 27 => 0xd7558f420065f5458f420065d5458f4200c7f76d4f420047d76d4f420053d74d4f420065e63d4f420065d63d4f420047f7654f420047d7654f420065e6354f420065d6354f420056c7254f420065e6394b420065d6394b420065e6314b420065d6314b420047f755874200c7c75587420047f755834200c7c7558342004f671d9642004f571d96420057671d96420063d74d96420047d73d96420066e72d96420047e71d96420067671d96420047671d96420067571d96420047e70d96420056e72d52420056c725524200574715524200c7e7598e420047d7598e420047f7558e4200c7c7558e420047e76d4e420056e72d4e420047c7654e420056c7254e420053d7494a420053d7414a420072e52d0a420072d54d0a42005ce73d0a4200c7e75986420047d75986420047f755864200c7c755864200c7e75982420047d75982420047f755824200c7c755824200c7e76d95420047d73d95420047e71d95420047e70d9542004df7359542004dc7359542004f77159542004f47159542004fb7059542004f870595420047e76195420047e76d51420056e72d514200c7c76551420056c72551420057471551420065f65d8d420065c65d8d420065f75d8d420065c75d8d420065f54d8d420065d54d8d42006cd72d8d4200c7e7518d420047d7518d420065f6518d420065c6518d420065e7518d420065d7518d420065f5418d420065d5418d420047e76d4d4200c7c76d4d420053d74d4d420065f63d4d420065c63d4d420056e72d4d420047e7654d420047c7654d420065f6354d420065c6354d420056c7254d420047e76949420065f63949420065c63949420047e76149420065f63149420065c6314942005ce73d094200c7e75d85420047d75d85420067765d85420067465d8542006d763d8542006d463d85420067675d85420067575d85420067754d85420067554d85420067753d85420067553d85420067652d85420067452d8542006776518542006746518542006d76318542006d46318542006777518542006747518542006b77418542006775418542006755418542006775318542006755318542006765218542006745218542006b6421854200c7e75d81420047d75d81420067b65d81420067865d8142006db63d8142006d863d8142006f361d8142006f061d81420067a75d81420067975d81420067b54d81420067954d81420067b53d81420067953d81420067a52d81420067852d81420067b6518142006786518142006db6318142006d86318142006f36118142006f061181420067b75181420067875181420067b54181420067954181420067b53181420067953181420067a5218142006785218142006eb4218142006ba42181420047d769944200c7f76594420047f73594420047c71594420047c705944200c7e7599042
  | 28 => 0x95430067870595430047870595430055d73d51430055f73551430057471551430053d74d4d4300c7f7654d430047d7654d430053f7454d430056c7254d43005ce72d0d43005b67190d4300c7e75d89430047d75d894300c7e75189430047d751894300c7e75d85430047d75d854300c7e75185430047d751854300c7e75d81430047d75d814300c7e75181430047d75181430047d769944300c7f76594430047c72594430047c71594430047c705944300c7e75990430047d75990430047d76d50430047f765504300574715504300c7e7598c430047d7598c430047d76d4c430047f7654c430056c7254c43004bf7650c43004df7650c430047f755884300c7c75588430047f755844300c7c75584430047f755804300c7c7558043004ef7258043004ec7258043004f77158043004f471580430063d64952520056d72952520063d64552520057771552520057471552520065d6354e52004bf7458652004bc74586520056e72d92520057671d92520057571d92520047f73592520047c71592520047c70592520063d64192520056e72192520056e72d8e5203e6e6298e520047f7458e520047c7158e520047c7058e520056e7218e520047e76d0e520047d76d0e520056e72d0e520056d72d0e520047e7690e520047d7690e52005767190e52005757190e520047d7650e520047e7610e520047d7610e520053e74d86520053d74d86520047d74986520047d73986520047e70986520053f74586520053c74586520047d74982520047d73982520047e71982520063f64551520057471551520065f75d8d520365f54d8d520065d54d8d520365c52d8d520365c51d8d520365c50d8d5202e5e7518d5202e5f5418d520065d5418d5202ecf5218d5202e5c5218d5202ecc5218d5202e5c5118d5202e5c5018d520065f6354d520065c6354d520056c7254d520065f63949520065c6394952004be74d8552004bd74d855200e3f74590520047f73590520067771590520047c71590520067471590520047471590520047c70590520047f7458c5200e5f7358c520066c7258c520047c7158c520047c7058c5200c7e76d0c520047d76d0c520056e72d0c520056d72d0c5200c7e7690c520047d7690c520063d6490c52005767190c52005757190c520047d7650c520056f7250c520056c7250c5200c7e7610c520047d7610c520063d6410c5200e6e72988520047d74984520047d739845200e7671984520047e70984520047d74980520047d73980520047e719805200e7a7098052004de73d9742004dd73d97420047f73597420047c71597420047c705974200574715534200c7e7598f420047d7598f420065e6598f420065d6598f420065e7598f420065d7598f420065f5498f420065d5498f420065e6558f420065d6558f420065e7558f420065
  | 29 => 0x56f72591530056c72591530057771591530057471591530057b70591530057870591530066f64d89530066d64d89530074d73d895303e6f63d895303f4f63d89530056e729895302e5f63189530066d62189530047d741895302e5f73189530047e71189530047e70189530056e76189530066e76189530066f64189530066e64189530066d64189530066c641895302f4f731895302e6f631895302f4f631895302e4f63189530066f74189530066e74189530066d74189530066c741895302e6f731895302e4f73189530066f71189530066e71189530066d71189530066c71189530066f70189530066e70189530066d70189530066c70189530053e74d85530053d74d85530066c62d85530056e72985530056d72985530066f62985530066c62985530053f74585530053c74585530056f72585530056c72585530066c62585530057b70585530057870585530066f62185530066c62185530047d74185530047e72185530047e70185530066c62d81530056e72981530056d72981530066f62981530066c62981530053f74581530053c74581530056f72581530056c72581530066c62581530057771581530057471581530066f62181530066c62181530047d74181530047e72181530047e7118153004ee72d9743004ed72d97430047c72597430047c71597430047c70597430057471553430053d74d4f4300c7f7654f430053f7454f430056c7254f430066e6598b430066d6598b430066f7598b430066c7598b430066f5498b430066d5498b43006cf7398b430066f5398b430066d5398b430047f7558b4300c7c7558b430066e6558b430066d6558b430066f7558b430066c7558b430066f5458b430066d5458b430066f5358b430066d5358b430047f755874300c7c75587430047f755834300c7c7558343004f671d9643004f571d96430047c72596430047c71596430047c70596430055d73d524300c7f76552430055f73552430057471552430056c7254e430071d53d0e430071d54d0e43005ce72d0e430047f7558a4300c7c7558a43006766598643006756598643006777598643006747598643006b77498643006775498643006755498643006775398643006755398643006b743986430047f755864300c7c75586430067665586430067565586430067775586430067475586430067754586430067554586430067753586430067553586430047f755824300c7c7558243004ef7259543004ec7259543004f77159543004f47159543004fb7059543004f870595430056c72595430057471595430057870595430047f74595430063f74595430047f73595430065f73595430066f72595430047c72595430066c72595430046c72595430067771595430047c71595430067471595430047471595430067b70595430047c705
  | 30 => 0xe72983540047e719835400e7a709835400e3f7459654004df7358a54004dc7358a5401e3f549865400e3f6495154004de73d8954004dd73d89540267675d8554026b574d85540267753d85540267452d85540267450d8554006777518554016767518554016b77418554016b75418554006765418554016745418554016b454185540167753185540167453185540167752185540167452185540167750185540167450185540047e72d8d540047e71d8d540047e70d8d54005767198d54005757198d540056f7258d540056c7258d54005777158d54005747158d540057b7058d54005787058d540055e73d89540055d73d89540057671989540057571989540055f73589540055c73589540057771589540057471589540057b70589540057870589540047d73189540047e71189540047e70189540073574d85540267764d85540273764d85540067763d85540067563d85540067662d85540067462d85540057671985540163f64185540067561185540163f74185540047d73185540047e72185540047e70185540057676185540067676185540173774185540167764185540173764185540163764185540067763185540067663185540067563185540067463185540067762185540067662185540067562185540067462185540167774185540163774185540067773185540067673185540067573185540067473185540067772185540067672185540067572185540067472185540067770185540067670185540067570185540067470185540067461d81540057671981540057571981540067761981540067461981540055f73581540055c73581540056f72581540056c72581540057771581540057471581540067461581540067761181540067461181540047d73181540047e72181540047e711815400e3f74593530047c72593530067771593530047c71593530067471593530047471593530047c70593530047d7498b530065f7398b5300e6e7298b530047e7198b530047e7098b530047d74987530047e729875300e7671987530047e70987530047d74983530047e72983530047e719835300e7a709835300e5f73596530063d6455253005747155253004bf7458653004bc74586530063f64951530063f645515300577715515300574715515303e6e75d895303e6f54d89530066d54d895303ecd73d895303e6c51d895303e6c50d89530066f751895302e6e751895302e6f54189530066e54189530066d541895302e6c541895302ecf731895302ecf53189530066e531895302e6c531895302ecc531895302e6f511895302e6c511895302e6f501895302e6c5018953004be74d8553004bd74d85530047e72d91530047e71d91530047e70d91530063f64991530055d73991530056e72991530056d72991530055f7359153
  | 31 => 0x20060018008002000000800003800100500000380030000000000006002002801000f000000800e00100100000000050018008000001001000000000100180180000000060000000004002806001600000000040020220000000000003000000c00600100480040000070020000012000000800c02a002003800001a005001004c00000800180080000000008024000000010000000200200100000220000000000000036000002004a004003000c00000d003002c0460070018000006004000000400000f01c0000024000000000000000600000000180030008000014002004803c00200b003800400200000280000080000080000000002000000000200200100200000010000010002000000005800000b000000800001e002000000000400580080000000010010004000001800c0040000008000006012001003c00800000080040020010020000004002000800000800000980040260000000014008004000000000200e0018008000018000800c002002003000c00000000000200100080078004004004000002800601000000040000000008004002000000000403a00100b000c00600f0038010028000001004400000000380140160010008004016009001801c006003001800000200300200000000010018004004000001000800c004000800000200300c0014012000000000000e00c0000000000001001001c0000040008018000000001803801600f00180140260010010008016007001000801401d0020000006000008001800a00c000001400c0060008034002003000004000a002001800c000002004802000200000480000040000000008002006002800801201d001005400a004001801400200100080000060000078000004000000000001a0010010000000000000000c000000000807400000a0000004014004002801000c001000001401600000a00000380030060018004005002800400400200000040180020000004006001001800002c00000d8008002000000800801800a00000080240060010004000022000001400c001003802400200700000000060040040010004002000801802e004000001401601b003803400c0000040000002002000001800200100180180040020000020008000000000400a0000040000020002000000000a0140020008038001000000000200a00000000020020000000002002002002000000a0000088000000000000400a00a009800000000300000440000000018024006000000000000a001001000000c00100e5f7358f540066f7258f540047c7258f540066c7258f540046c7258f540047c7158f540047c7058f540047d7398b5400e6e7298b540047e7198b540047e7098b540063f74987540047d73987540047e729875400e7671987540047e70987540047d73983540047
  | 32 => 0x100180000000090000030000000018808400800200000000020010028008022000001001c00001100100000040070000000002000000800800000100680000060000000000000008002000000000900080100040000020000000000000800800a000003000800401700500400000010020004000002006001c00000f001000c0080000008000000004001001c00000000200380000060008004020000000800000002f006800001e000000000000c000000001c012003000002800e009005005400e0000010004004003000000c002002001800000200500000040040010138000002000000000800800100100240160010038000000004000000000000200100000020190078000002003003003c0260020000010016000000001c000001000000c00000f0040024000002000000801c00100380000020020010014000005000809400a00400100280060000028028008001000000c008005001001000000400180080080000000004000002000001800000200100000000030000004000004001800000c000001000000c0000010010000000000000c000008003801000e0020010010004003000000c000005001001400a0060000014002013001000c0080000008000000011000002001200200000500020000010024000011001001c000000004000000a0000000004000005000007c00c0000000004008000000000c006002000800400000100080040000060000010006001002000400a005000000c0220010000000004002003001800c0000000004006001000001000800300b00000060060008000002001000001c000009001001001000400d000800e001000001800a00500a00340340000000020006004002002c0000110060008006002006801800000e000000000e0000030004002001000003c002007001001c00000b00900500020010000068008000000001000a0020090088000005000000c0120000000014002000002000c018004001001000400000100140000000000030002000001800001400000100080020010078008008002008002400c000003800001a002000000001400300480040020120088004008000000000400c00100b801c00400c0000000020005000000000200100000080020000038000004001004000000200000e800c00200500100000000000020004014004000000000800b0000008000011000001800e0010068000004002000000000601b0028004004009004801c00400000000540000040000018002003000800000e003001800800600700000140020010000000024004000000000600100000080100040088000000003000000003c005005000000000f0080020000003006800400200100300140000000090004022003000801003200a000000400e0020000004008000000000c00400c000000
  | 33 => 0x45240000000d1d2f405e73940beb0614c012b7853e0001314000088f4934ab400000000960000000000048300003a109d23db46ab000035a1c4516b000129b1e6400035f00004644b454f70a26388c874280ccdc0d0836d2b28004000000000200600000000080010010014004004008801400600500b000000400c000003c0080010010000002000000000c00c00300c80000000030028008002002000001000000800000040000000010024004003002000800400c0008000006000000000805401900800000000020000018018006008000400200000180280000000000004008007001000801400200180000120000000020000000002800c000010000000400201400180180000040010000002002004001001402500000040040040010004000000001000800000b0000018000000000000400000f001807401601100000000040010068040018001000000c00e0010000004008007000000c00c00700000000040020000018006011001800c0020000008000012005008800c00000000b800000000100000040040010010010000000002800802600e00000340060000028030012008000006c00000000000500000010000034002000000001c000000006800800c010001000c004000000806800600e00000180020010088008008003008800c000009000000c00004100100040000040000004000000000000400801d0038000000002000800c0000000018014006006001000000000200000080000000000000002001000002401600000400000100070028000008011001000403800200000000160000008004016000002800c02000b0030000000005001001c01800a000803000600a0000034024000001001000800d00300000000000020000030000001000000000a003000400c000000000000e0010018008004000002004802c002002800800c000002005402200100b800c0000000000024008008000000400600200100040000010038004008000001000000a0030030000012000005004400800b00400040000010018010000009000000c00000400100000020010000000026000000000800800300100000180010008004000000000800001e00100b800000401600a00000080000070020008001002800000a01200480400000020000014006003005800000600300200000040000000004000009001800800c00a0018034000000000002801800800300100000130000018000003001000800c02c004800400000c0048000006000005000000000000b0024002000000000000c0030010000000009000800000c0010038010002000000000405e001004000400a005000000c0000080010038000001000000400800b000002c01000000000000000030008000002000014800c00a000007800c010000000000000000
  | 34 => 0xe09ce17b0000375c7600e50000269c00032ac977238ca4d29854a045a822316640351524976008d2123a08b004ab8e124500a2a054537300005f52c94a203edc898000105c1c5000051c4a2d32d847743d44ca2704af31b74dae48ec00019f04e205810f1083d18c1ef903e04ccda0182c5301d60270000000009340001bb400024d50a422d888234bc0000000fea07ccb3800000960000000000076e000000005b800032c047d2528c9400000004d300000000dc21228ffd40880002e7c8b04d44bbc00000004d0800000005e20ee40001a1451600008cb07c0d09243d4ae0da87d002a01fb30cc74d3bb90c63fe0000000000000011b900000003000a68000115300004e4000000012012bb24d8cff2c78000520430c467c0004f586c614787730000000001cedb05780002dc829d26a14302cf4c1c2bf80000c7486d4c6cbc801540002b6c393252cd2500004ef3c2d02545b4000313c78126909953590a543c6400000002022a94217000140a27e400016d4d000d2000022f89e9475cbef3b200a400005e9000000040a8097000000000008050000000113c3db000006652c40000000d7f14bd296000142b4114000000000000008152aa949a3be12043048054198018f0000994000000017700000000bca31394803bfcd77000104f2af80002fd0ced09d8b4d3044f420e0059c038c64d12d5000117c2ef07c40003c18000000058000000000f0c1593435213293c0000000e0b0ffc00904b08cf0a2c00033bc00040f0cf409bc00049cd15e0000f592d84000500463c130c0001da00001a8c81c2b24af013240000b2c000000087f2284a280818f64127cc83042c3b640285773a400003974ffc0000ed41550000515c00000000004bc00002b880002e000004ee40000ae0b8150800002e781a71ec0afc4ea52cb00006d200004671d4c0000000e9f10a0cee09045d60000000000062e078cb3907580002ac527000000000000000483c0000000000000111700000000001426000146800582c60c8ca303c6053649e800000000b64f6ca871588a9738dc0001cc52a3000092300010d423f429a5090f74245402c0c580d606110984c940000000000384400052cc00000008c3000000000000002718000017c000084c000000000000000000000000000000000001464b8035111640001db40000001105000091741680a300001e600000000000000000000042f0eb5000000044884760ab93be197800000006064b581f54c490c9000058f00000000000598366c00000011670000000483800000010ea000060700013820000974000000038a51b54b600003864c6e02c8be70000029033116c015d3844109466443834542946a44354e2019ccd37241419727145a321dd20a293000000000000000000000037d15ec00000000003b18000051000
  | 35 => 0x13d4742000024b39447c80000a8930880001aa8d4901b42ba000146b521c1363388f1147e80002cd05f6000071c3ee4000512878d00011a7193c6b2000000043b8c38068c26941e861c239427c2784e003e28712171948a1e148731c602e2195c37f3d5d02820e92c307bd1dd2e5d04c34b8c954d94000000000000000001a54c2a0000000152c000000000050c816c4f4c0004100ecc000139d4ba4369000000003800000000000058872d12f80000000ba23d489e3459800000000001e3800035791280e2071d44a5253188080c0000b220000000000134a40a4000237c5d000000003bb42d94228000082c31e02a400000000003480a9500000000000aa30bfc00039343e80e6c76a2940dfa3058f0d000000028111cf0000000000121f0000000457400000000001005437202801f4b0000000000004584000000060907d11cc0001482266c0000000d190000858000100200008ae00000001a200000000b0c000000000953f200002a646b021e1138000000070c00000000000ac000000001e1c000151830a259c0000000000000022139c85b14ed40000000700000069900010031f706f70988e650f2d3f100014344dfc000526c39d054c2a53c10000011c33200000002d040003d7095944bc0004d8c08d0348ac230f800000006931aa489126789b814647e514809923bd00000000d6c4f4003c00002980d505e104040000ddc4640000bcc04087e7108070f3ca08710000af7000094900000000000000000000039ec0001bfce53496821000000000000d850000000364d36e41e0771043800030acfce01b80000000c5400001b50000f7800006d700000000000000000092b000075d0000cf60cb8e9d211cc632f252234c3c7074250092251128e016400049fc00000008244dc038710c50f742887ed23b00004e70d432f1c0001b3922731346e850bc0003cd50db42ad2b32434c9b12c8515422521b229c59300010830d7091946d147f471419a034d13e07805f1238461b50e04aa00009aa1b807f21b202e90d6057815840000000f2202dc00000000001ed0000279069401a8042487053d281ca01000103700000000c9d19625606763fe40d70000000462000024b000000000000744f2f00000000000bd40000dab3b580003d10000270c0002fd93ca27b479d2624d043898d5f4e68000161c20a3a280002b5c000142467a31c00004be47fc3ed0000385c00000000002f5400000001a613ec6790bec00e4a30000209cf20362142d07b8d4b3691148257482b00001b8000000018f40001cd82ed49e53320c1458133792a101f4f680000a7d00010b00000b92000000041252a006801b147d85841e9d189485c38322e929710dd12d023c36240e13f60e9ca7e48c845a00013da37940003d000003a6c0000000803000076630d442b28
  | 36 => 0x10a80002d8045c455800029085ba51dc434155c91e0870000446cefa39fc68d503c93c4a9540c044cdfe0e313c6032cc0635c8d360000b6b00008902e38a18220416b2168d4251ec54002d00000000aff08947692f840000000ddc4cd11f32f88f8d216c1c135c45954a24ca9368c7e646891ae000099a18952313eac84d000000052bca101c1000043453c90000000000000000312164e6c98118c000023205df00001ad3ecc0000fec00021140000000c1b00000001b0cf4300004ee000000000000000b702934a08f470ecca49000025d0000000510c2b011800831929088094c48b1fc08f12b702191158e4b073442e397c0004c346fb0c48000121c6e123d0e4627589b7184d1810ab400017b80004c640000001194500cab7316000029984e152d8d0b40e4ca71dbcaee01fce55168096e319caf617247e21b983251c2433d1ce854312240001b606f000006750000eb02821019443d26b17c0c805260caa37600f32e0ce99369494544cc9ca000011100012a2496c2ac000126c06742673090000000079e50f0a33000091d24ec00033151e22378e8b00014630000795000011600008ca0000187000000003ec4e72c40ad212680eb00000004eb40004210b3a05004d1261c000000103219140000000de70fe49cc4888ddf1d0d41500000004b9117435ac000347800000014b951812c12c7d3af0000946519400000000003b1c45e27240a537dd0ce263c55d01c8000000000000000002e1d175271d4790c0000000000000000000217ccf94f102343d18419000000048a4000113439c246901e3cad3f4398c0000001288253800004bd10706d8465094837c00000000374000044932e30800000b6c77e51584cc00014390d6544813f8f664da07ec191d18f09152861e502c20001414000122b024d45101c014910353572fb11e703e000012592b52c8400037a93a740143b0189804612d07fd11b05c4050479a184400000013eb522c08449950dc4b680003cdc0002bbcebf38e0ceb37b06411b700740000e860000000000000000000003e540003ec109100007df000117f48b80004424f58000000000013cc4c744750dd82591b2c0cd00012b006f480e0000ce03ce930a00001cc492482f0688000000000000008d44794000000000000006223a4c780341caf94c2d3ef3e4c7412a207742f64e420efc830010caa44d9c00005d14100c54aba355800000005da24e503449a0d842568b9021081153e94ee51f6cdf00984b1b421c00044fc69f2b2c000000000032246f83aac9cd00000004d340000000251000017b17e49ae52e84002abc00016a410c053400041640004a98f1a242c00000000000000b31033870a2744f973ddd3fd396867437d0000000000030dd22451d0cf100012fb2b952bf000138d1e2000000006e52e140
  | 37 => 0x165264c52b514800009e470b5154000109c2264d60a4e4128a5c287026526843a3180000006010463a2127e17cc70d34ec0001f8c6ac000121806345713ea4a6d000000022d41c50000a791a449f221247f40000f5651e000011c8cb700010da00000000000090404428d0d48fdf11240002b302d4000147e201832a156011940b80000000f6a000121a00005730a4914f25c804a00006ad000138c076c00000000004a1d3a61468fd217f8a6b294932c0000d7a47809a6218400000012351d400002118a5e492043c203c00041fc000000074545106b80eb8d922a044a909e000000013560690663000044027b0000000095021e4ded00007a60000000310945304a03d22ab00002ed800020b40002e98a8500000004f8c9b937ec000315530c241ca9b46dca782ea800000004c71ef00000000a2100007a5257054d2ab43e13b445b02318c723e7c62945040003984d6002bc28900000001ccc0002a10bf146e089900000000000e9820040003d78666000080b06ad1e84e9047f00000003f283893b5400000000003e2075400000000e38ae60c3848822e4951407400008585b93734bb301910a724202d60e113912d68000000000028c46483fb8cb3000000004240000000a0d163400000dd0631598aab0ad88a82db400000003c4000000023f80000000a4042d400001e489a3e780000000b370000ce31ebd32d25d49bd2d700000000ea546686692bc4cd700213e70000ac841dc00008e499642a4d2c18ac00000006230d3000000003ad00014760d840004c5518d40f413507f12d73c6c00000008444c683721b1c34f51005560f44fbe00013b23d4d49e031140e0000000180519816985bd00000000000000085133047b061635cc00000012ac000146c000123049013c01078fbc00000003ae00000000a7f51a8698523c4f6000000033a463a33e000017e91d2253c0a700008c11f253bb00009fc1120c0a0bd40000000457236527233687c200009201f4c8b733f091622fd0d01520000000104304e80004dc81900000bb80f1493e22f4eb30e84b40000000000000000000000027d136333023e05c002e214000000004140000b14050c00032b400000000000c242eb07dcfc3000000011b40000001271012c00031889fd000000000000001facab34758c920ca40000000daf0e600000cf00de23400b3000000000003f400008c00000928000000026b00001e813b7000000000000004a600002c6837518d0df31438b020a801c016ac0002f3c0002ec82870090e1a359cf6e0000d1207511a622e02fd000000052ec74b000100c355d20b0b980003384c5e0b9080803890b40f70dc900080002e34c56334c6a819a0000443432238e4e2f033c2f100000002bd000025bc5fc11c103b0000000000028e000000000000002bc842946cc5ae0
  | 38 => 0xbbf0000d902e248530c905be00012002a5896c2a60000185c0000000000143000000010613fecc7c271000000000003b48725000000019c8782000000000012200000d1c0098fda3f7122d000000037fc6bc01f8f8131b02a10000b17498d064433449450a0d6842fc89b3024f910e40f7521c84952ba0fc134e53050000000000000047c51ce3440b2d00008e2262c0000000000000000000002f037680002ff000000002da171ca724145425007034b414c8da2498c4605e8ac5000000000013a11d100000000000000000017a800042c40003b840000ed07862674e9e228c0004a9c000000000000012fa1af460400000001d240000000000000000044180004188000185000000000004b184a20000bce52883ea005c80d000066f1a3010321c04853b9c911423c831048800f358c00d1eb0818000003f0a281d50000ac10000000000000052901a80f8c0b00fbc2e151880000e949270001187056c62f1ca12600000b6500000004d3d2921938f65514000017e0f0708fcbd24d38de04a150331dc0cdb1a0c43817f40712ec00002094b593215362348ccc80000000000000000000000001060000000000000000000f87351c0002ebc6b9000000008ac0001150000000000000011e400000000e3c7b5000000000006be3bf800000000004744bdb055c000386c0000000000000003200000001f78637000055a000000018d883647b80004dbcfe100000002e9cc7f4268000189cef904ace3321a0c48000000000006b30000000067800036381d231b40002620000295400000000002c3402219901cf0cd000049ecb0600000004ca40000000e1000009fe3fc81aa0000cc00000d7000000004b240bc1a111cd00012210f9136d00007133e6538328aca0f2b74b18000002d219800000008af0f740000000a1300008870000f4f4070cc608c4b2e000000000005040df80003884a36374800000000000000c0c23a07ba1eb84352cec2c437d80000be0e06154cc650000e3a0e90c31000044428240003bc400019dc9302b8c0002e74c9805bd134000000020993601be84421629118480cdb40000000123000009c8000423400020b03ed4ddc00016fc0a13e248ac0620cd14eacd184570be628d4af82990cc340c40001ac0db0000000000002fe000061905e4000000132141ace7032e4d620afcf3c0624c0d1360000516081f1de43f3058c13048fc2054b6d381389432d0000e4418e00fc04fc00030e8c230000931000130e38340000000ed32a7c43a0abc5de000000051c033e190070e46a435348e5142357034d14e08404a900002a8117343c928f0e05178000000000411f73e681e933a8ee306c01004654d1b39f09cf00002f75245160397146749f4000000142a14744da10f4ab939a531f06f83e72c8ca003510000000096a2398
  | 39 => 0x325cc81332c98e1cd00003164d054ae051141980003c4c00000002f215d400045e441f000084b49e044750440002f4c00025e54ad4c9c9543268f0e433cdeb00cc1204f3cf101958dd900011fd0a653e406e886907b000011f92b44fa844310cd0bd00001e24ef00003ca85aa1e3c11e2500d4a000000000000000000ad30000e0e03080000bd0bc21de008c0cc479f437c0000e5d398000000000002d3303c0000000317389c000458c0001bb901a0001310000116f1594c1a4a78000173400026d840b04b800000001480000da24da8b24000000000009210000c84387800043e40003c082564b085900000000449456000007f118c52bd20480001d891993df0a110c04bfa3d413f501e13871ec841c4f44772106d067000135b1f3000045c4000187800047b4000000145d15e80000000f2d00000005118121045c65211cc000213d49300000000000a2e18ccdc00001081435c7c634c0b191a2541b00010ba00000000000436000056d19c401b00007d73ebd23412608330cc04a64e646fd2a18f8414e800038c40400000d7e0a040d50000000476c00030d05230b1400044dd1f5366130800008042e84000000145e0184e323234602214800037e515f3af83d000000000000000475000000000000000000174cb62120c00032e82b9448c75e00000000f4c2c71ee0000000078b000000000000004fa0e58000122a31c486c3504bd81afc0002170409162cbc4000000011553e608a4a1a324c5ce1cd544b3bcca53355000000008f7197c7d4000012a07401182fa400000000001794cfd12ec56c4d98000000000038c00000c6cd8110911b64d4c0000000d3800000000060dfc047c75727dc000372d24c21d453f07c91c24991057444c57648e800039145943298000185400000000c5135cfcb50a43742de800031a0fd04568f4528f428f1c84000000000000011f4230851813e85280af8e5e48f868620d0db30001339043415d28393283310416143524e2e643561d54ee23a9910b286c4230ad48163c5c1b71ba91ba0a905bb42bca623fb46cd403c16d471d1c13c144e82224a8a133c5c840c023700003cf218d09e525d2f50b440a214cc00040aceca213026b19085cc2dfc6f3000000000000000000a740000851410514b3d8115532785af39a0c7b37c4000000013d1a38000445516900000003c8c7da4df000008a0000000000000004e0447c6c1304000000000002150b58507c000000000000004b70000000168400000004bf0000777000064619103824ccd1de16480002cc82f60000fc01eac000134c000000074e51bcf8602240000000bdc36e40003d346cf206400040341f632c457436500001c64000000000035753551fbcb9c0000a220000d4c00000003eb0030000000043900000d2800000000003dd882e
  | 40 => 0x22908604918c3b434d21900005a50a412fe2dd431100001ca068418e0000c3929dc134112820c28bc52647e517d06300001fd89f80000fe946f4000000000050d80ee00001b24c705ac16740004ee0000447428c0000000000095e00012421a709220000000039c4d236840003f8cfd907e8d2a41d00000ef528321d80000000dbd18d45314e94000000000039bd01600003a806580c1000037150d527c1e440360000000125d3a30000de900001c80a9cf494b7c000474d262000000000000001b640002e20000000000000000000000faa519095652a470851f4f5a2f3547c4154a5600010dd0000ffa1074bc62cc0000367125e0000963000047c46b417f0000c763cb13920000e6a000000021540000001236231d2aa4d0c88d45ec0000000000066c000000000000012cc43580001e6c00000005ff0590dd63d740822bb50c8484006f00005270000c7a2d98a712c9c0000000def00000003dec00049d800000006a200003d548e0eba0f2800000012c5208ca7a00009571b091df495800052e02e3345cf8532180000000f961394ee8000097c4ff009b000029e3a840000880c7320dc7ee0000f8b0f98c2c00008fa25a501f1cf0c9042d93090000cd025ac000453506f000000000006874dd948d250c8f0401d06c00014a30aa493d4bfcf6c247d48600008c410ec0000000b6434e80004bdd3460a18209000000028647ce0000e7d32fd24710c00003fd4ff317a023c0000b6e42e0c3600002de3a1d1101a4049300000000000db14e2c76b36090794add275258400000010ac000124529100e641380000000aa200006a7166813b0001170110456422b40004fecfff0000c1335b400000013d8208000023c8000000000009388dd2d40ca233b0000502c00004b400015c10fa529c30d00000000cac6d529640000000000008503652a1361000000031acfae42650c40f50c43000000000005474d7c00002d548502804a4241000005602400a4435e00007cb08c89ff4fc097a23d8000000000023d400018746f200003fc4b1c6a5183cbb72b1901b1ba43e020080001df065d2ed449c265c22f11148a9166d2b94c1c57f000094100003b5351806c4060d1a1204000037cd02019c7c1241848f3358f1e0968eb45230bfb26c8c400000000000000022c4d9939c400000000000000e07000000000003e94a4110c0644b2f0000bea15c8e80387013c34cc0000000b7100000410000e954464b2833dc96000000001ce04fc0b5544700003aa3fc000022a86d104a474a1b140004dd000029ec0003128d31424c32f00007653d211243a38abc362856723f00f041d82aa0908000175c0000000000000128b17980000000000000000000007cd4274000000000000009dd2400a6a00007c725f435d02b42c8000128125e00622a640441e613473ee
  | 41 => 0x846c939b0bdf2be8e57135000020841bf0000acd24480000000ecb000000000000000000e3615106fe06b000000010b74ed0b1600000001c140000000d8f1cdc7d80000000000000000004d60000000000000000004c52cb000000007dd2610b8b4c9088e000000012349650414000000061f371000000001c30000ac74cd486f19891720000000426c0000000e3c00000000000000000108241a0000307c07714d512023fc971014511a365c426495c0e5416ce9744211c32e610ff3b7062c3534b7e3fb023b0000283000040f059c8481cf90c305dc9a30fdd13b4de4b131c54fde36c873d000048612f0fd72d2912c33600004aa499f458887d17087c34240c050aa0c990e7c55122ecef7400403a2640caf3808a3711a88f80000b734decfd6000000013386da22cc4462da0012116cb5200002120d553b3445879c000000000002bb000000012d80000000000000000000000002b9c0005294dc548f000006ec40507e4e09000000028e84c131dcba51bac2660000000356461222207840000a14517c0004518f2447540004a100000f7800000000000000f3402f800000000000000000000000000000004cf5071000000020880000000ce732f4000000000021e92bc000000000010ca000046f000000020a000000003cd26886fc39cc9f500000003998000000000000011f800000000000000302000044b8dca28e4f700000d9e00f800002190583d300001c1910234300000d04d5100002a244c4028000134b39e05db3ac40004a7000040402553f98000238110a0f58d692628000000034e00000000000514081c10400000001efcead30940000e780002ec4d89518400032c8d8700007cf000000000000000e652d000000004bb40000000a1e1eec000161800010f91a000000000000dac19a841200002ec0000296219c000000135c3198000022ccdf000000000000004964e8c3980cd43f4c92f000000036e908019e074f3c04d48000117c0000432000000000005c34d04ae4409ce3d349855f369800000005b3021d37d2f0466e00004df00007d10000be53bed25500000001ad400006053484548d751cfca6c47c8000360cb4b0000402404c45d0db8000322089251140003a34aa84ac84a10784756141ceeb000115003f50060cccb7625551a1327cc493d7c3a900010a616591c646ec6c048f50e539accbe391d16e000071a13d044b2d4cf9b03e85f739004a33888b3322d0cae4364001387c9e63d28de400006cc311c000074c0003754e814b893e219fca9116240000000de30300000348800000000001884d3f20e09982c2858252d40003ac829f000074640484ec000046b0fd8a1203c53540270dc31de812700000000d1c00011a4e92399d3b146c0b7b0b38db607acf6b05d8ce54ea0ba939646f404c800016305d4000000
  | 42 => 0x2fe096d331d1210bcc0003b04720411c000013400024044792a0865800000000000fdb2d58ebb10b42480dc125c3ba8b9434f4841500119e000024332f0f7e46bc0001088000000145a00012ea2b3cd76114c00012a00002db05030000ed80000000000023811b879021ec2ca0d1148308a8142508545b274028450b87b32f592ce0860b0b2e581bc2ee800000013bf000090300006322df4ca0093cc3d0d24d4542302e827009f11d708a615491572eac3c22230bb91d7d06530b4f820cfc2d723586e200e0b4838a83260ff43b124e12431039408091c373000000000000002bb02570001406318111e2a4146903a894d12384b33b244820000000424815206b8000000000018280000000654210c0000000000301c00027e8fc517d000000012cf0000b7801d40000000a43000000023600002634f90172874722f08d526083f100013ee504c0002bec0004471139356860d460c0000be842f14a80000f7c0004600ad900012e14ce050b43bc8074dace4f00005ef00000480000d504f0817d4be017c2d74a4a32380030c2c0732d1c6960000000000000002fc06b0f602882a0d130004c78952dc6bb0be42771d9000029f11143ca43201e3000000000000000ec015f000000004150000d0f00008320c1c00000000003d044ed00000004fe0ed0000014a12b92b6000141d086800000007ca34d49bf083800000002b200000003f880000000c5f367c0004e5400049600bd00000000000b0933c012427700004e191f047a53883dfc114239c0f624dc83f046d2d22b44dfd02b92de00646f61440b9b3fdc61000000532974ea820f04b92530fb101f000040b4d014e5d3023a9cecf4e141a52b54ede2df04e632b00004e28d3400000004b44f61000000013e000001ecf94328c1ea300930300002242ad50b300000000000bf02f800000000000000000029d479300141c40000e770c50c4c0c3c0001264f123e844bd0000d790b9d24435ec8ab2fd468f0aacb123b5d0b92f0027e3adc14c47f132a03d02d236b4a060c0d4090cd80002fb80000000f261d48d402d78de12ad8ef53cc0df2196c0003830e7900011003bd92e7190d274364451700000000000000000000000003f00fb892509d4a8e07612691f81494246c5684d480000000d781fd4fa82cfc00050fc4a52ba45554c885d10001190000083b3740000000000038a0f8e00001d73f50000147c00015b94072200aa93f8099103c800050b000013ac0001f853940a8cee640984c8194c7835150f1f0001159212800000003a000009ef41c105d4700c6a00000000001252000144c0000000000004c05d4c5a3e8cc2e3d6cc690000edf0000e080fd4000077c7922470dbc0000c150000ff430600001e580000e4400043a045200001311a801611e84a0b2024ef23148cb421a8bb449
  | 43 => 0x25820000005cf03a070300000000001301428000000000004b34d8c2d5d3fe46750d809180004304000465c68a07b52ec20a8000000000041c8d6a00014172e4486b00000000c4cd7422c8efd52c0c9c2e3c34000003cc522000020f4a2702793f70000f33333524a1b4ce4c0b0400025ec4db02a80001c7c00050f92d400000000af40002a9d359140400000000000000000451c7e4195429b000125402e400007185a4101800000009424b701980000000481495f133420100011ef2e6800021740d90000fc4000000000001fe36a899c15f806902152370001182140853717b438a21f0b200000db54300183472d2fd39589e804201dc4629103408c0e9088892a0f0533f00012fc1abd2950d5c7760000000000085900005391a047fb2c9928d00009e0467081a00000000000e5400003da000000000013ac0000000000027a00000002294000096d1430000c8a4fe8000000000041a40000000fc614184ac00000004c014b40000b4238f863e148501431d02b100007f700004b83a4400050c41e730a447843840003abc92e047400026d105045902822dbc7241a2c0001b7800013dc7a3521106d00000804f350563600d6e40907d900010442754ae01f490850000dbf0000f0a1984e85000085615a51931b6c71e2a78da7451400000000002680ee42a7069d00012070000a482f0cb2a4b200003fc4491000072f2dd000000000000000cc90a5c0000000000000129443300000000000000055b4e7c00002988fb428400000010e70000000000000013000000000000000000000000000000000322c310000000000014a649dc0000940a3f50651ca138ce0f000026e2d8d24b0370bd141482c000013a2234c00002e0f3b43a422d4ec03430000f09097c3d9312c0000ee00004cc51860000abd1ad8b0700000004218e15000000003605d9000000016a0000333ceb6321c000000129a0000000000125d0000c3008ccbed0b6000000009eb00000004238bfd33d4dc6000000016f0d0a2194000000002707393d90000fe51bb0000000000000011ea00000000000a0a00009b107640003f300002d25165000052d25a0bbb30bc0000000000292ce340c2058e15f52d92f1431a3348000000000000000000000c0b09800002d512d537e00002d311be183144f4348ca44638338000131303b451c10606b73f200000a000000000f553dc8000079001d3774cf3438000003280000000000000033500007d600000002050000000000026300000c700000000000513883914ec9e20000c640000e351a008ee2d0c2350e194590d6cf1400009be0390000524049e0000c0e37880000e5800000000004399499276d4221774d11160c3e20cec00000007324db00003c94000260c00000000004e4cfb520745c008f4f1536e09b50d9802000000002a480
  | 44 => 0x2135393750000000231405629b8e4e487400031040002fcc00023240004845369374d33c00006e72bf4000000000014b8b8c42c827f0b74000025400036f943a330904b3d501b308d86a144e109c2ea000014910e34e3cf732f5d4720000cfa3c0c95b14d09ad28d147505c800000f400000000000000edd2138be800000c63a911ff19b4000000000000005e300000000000000000122f10e4f9210209d92b69441298137a00000003fa0e64000000000000004d005914c5cb4e2cf0fc24bd800041f0000000112b000000025980000000000000126f0eb10bb000000000011a3246000041340001a080000000b6a4cdd0084770a8f2c051b111ed0fc0f202e527940002cf8395041c83551243fa00004900000c5c03dce7600000fe000000001d800047840000000d1542b4aeb0000000272cd241044eae2e094a13810f6f000000000004130558c17000000050f4a2c0000d0e0d183ab4e780d400011d01d2008e026518538b80004ab44500000e0a0000f790140f0f4c7906a1b100001924d534854d281bbc000298d20613fc7630d9414f487852c51104c22e913bd33650de31f432127d05323f34cd52e28c7e37a0df501944ea315c9484834195452850f24405fb02202bc35bc0114ba09730c60eda3c7528a16dc2110000a5b2c1015a4eb800000000000000000373cfef299c1fd19c000024504210001020000000000007b9165c00000000000d8c00000008ea19f4d4f0000fbb13113230e48000000009400009d847ac42552380681c40d21000000046c80001a492eb46ad0eb34f85a227d81dd5108a250000000221489e3bf00004aac8110001132000100900000000bb8000000039a2c3c7e8000066b35f4c750000e52449929f16d80c8425c93a4bcc031067c8cc00aca23052d3b631e0f674d1038b0da002f1edc0ab00280002a4c00036a41713a5126e0794b460000244137401427213d730c8378227054f0000bbe3ce0d5800000000000aae0000e4a00012093f551544aa0039297c9da3924b4f0000000000000017ac0000000e890928e4808100003c200002ffc8a24d780002eb47a200ed32f30506f50000e14167c9472a680003634e2d000062d08b80003eb42b731743c00f384f2307517a1ea400028a460e2b5000024fd0ec3548fcf44f53c300000004d400003e7469e00004a70dbc7232cd93e5089c0000275176066488b2858f4b28311bf3e70e1831140c944480002a34f634254000000000000000003858c8c000146e000000000000000000adf000087e24912e30000ba00000000000030200000001ef507d04e000009300000000000000000000000000001054507805e1144a3246a8ce8065081b3e3c54a405cf3f4120cca2d7ca1f1780ece23e4f2e2250dc125880004b943d73c58a41287488644100003ef40003
  | 45 => 0x67e10b00004dc4403341890209b029c40380002d9c0003a7000024313dd52c826d0000000285488a18a8000000056f09713df2a74b5151b4b6927781c70000000000126a2aed20200000001bc46670d80000000000000012f132849bb427c37a000038d1df4b032000006472400000005133b1000027a8abf34acecd0000d291d440c700000000000000000000020400000000000000000024c800004e40000000e6d2c38000219026828f08d2508ca3e3904dee1a987304ac435f2b4072600004b00000b7700007e926cc21b0000651422c00000008db4850c790000c3c000000014140002b8441037300000000000000067b00000000ad0000489549c0000c273e00000000102f000000018908ed00000000000c5b00000000eec7ff4c1000000000005170cbb34b4ab00b7d14c1274e624fb027300012dd0c6513c323cb1d4f1d41a0ba82710cb01a9048d0f42e54f833b809530b24f3d2d6c09a24280e13c31405347d3643facaa610fc32800013aa00001551c6c77518ec00008c0000000056345f80000344cce00013451cac000291905e372000034c833a11d11840000000098c000000097f00001823df415c14487390000ff630852af00000000000585432ceb9000000008e8000462c00013713960bf000018a0ab23a3c56b2708000000012500000000000e740000000269549540e80003e9c00033ec0003e6072a000075b19940000000a76000020846a0bda000000000003c90000d3c00001af0000000000000026194ac3ab08290000000000000035540003d44178000000000000004f200002eb8db73890000000077f000000000d11d92fc88e452584f1296047113c076c277c2492e4c0000000817279c65900000000000a801188000000143300008a015e40002d54000000000043e000001393c115381de2c4501500000003dc400000012f442a8000101c14e05f85222548c28000000000009092d109f00e8850804289804e409bc4a74fba000133a1ea129300007172b58ca5146d4022f8c1681c9cec202048d1051c27d4f389d33efc7aa00a8295000022c25f8fdd1f100000fe02cd000000039f8000000000000000004bbc06318e4dc72944000000000000000002b609ee14286d611e9320000044c000005a1f00dd13f90b7900000001210ca80c101664ae83ba00000002b1000000006e34f800004fb455e3bc0d032ef40d02fe4c51000144d11981c21ca4f3641ccc043594e1d1dec00009510c702293180000f3214a4d9a42b915b0c18c440000eec3420cb530fc3fe1f144ba00012ca00004ad0000716064941c000000003e507b43f40000000fa24c58ddb13e5192192c1b42438f3931bc7fa4b100004fe400013553d2049815f000019c503532607690f00edd0fb43cc0000000000000000028ec4ab041800026a5
  | 46 => 0x53f303fc0000000000000000002443a6046800048b0a242274d1644a84c63a682743f453490ded416000000000000ba362d0e2220c3ec4e390c2493c01e11a00004f2d2f238ec63f05151c40000e0515a8a451fe00000000000000092d00007b60368000356c33749b49ab41f8ffe2dc1267072d280132c7f31a5cd9513cd3ff3d3836c0000000456114e0068dce417c5ad000028536ecb8400008ef275cb08030ca5a080cb294cf87403a80ea230787970000e7a3c840004d745c100000004690350428cc192f743f21d64eef0d9cdd43a59489062cc2600001b912c41f800010a80b0cbde02c40000724000361800041b8f7a0b40f6900000523f1d25f365800016e06d04cece6e000000045dc5251ec43be00008f33e8000000000000f9400004411e300003bc06181e800007d541d489748a000002ec608036d31113a4be40160000000021f000018a479911113642152254f0025c00000000e5b1d8429444d4000000143b00006f921b8000224c17301e8c5348041375248fc900000002750264291c6b429cc6033274e832338f27380ce131c0474c4d6819343145b23af0000167854108340000000ee91ab8f310de52992cd425e10102b300010f633743c70000000000021d42591fe1cb08960054000169cc91227c0000000cf247612be0000000494513a00013a04a440004f153d500009640000aea0000000016cfb200004fd0c7c000000000000000001570c50000137819b0cc126e83af2a8400026c149f0ce461a4f8441a1ff8d61509c0ef40d52501340ab852746b1377881e28140004e00e0114011fb0540a701e2846100011a5172c8621b914041b7c72251e8bfe000000009a8ea90010c8200014aa504919b00000000000de600000004f78ace0dac00052ac4a019400004cacb86300cd272a3040a00000001754fa650608dc2c54f62000102c000000043b40004010000000091300000003b14b2b449d1bc2c140001620000171400000003c6118ce3f0000f8c3b64bac29949991540af500001ff10313892a5000045442cf3cf888417c804f1eb47a432e05451ae8eaa39d410f4cd8ce442f80000000000000000043f800b24d016a2c7100b0000000000000000000ac0000000204c8d70b813ba3450000000093316d137e1a68ba3476875a23acd9d0470492000000000000002614fa43c70ac30000000344c0000000fb6000130629a4ea32f2c13e20f800000000000000a6f0000000000000000000002a2c85e0181101295c0001fe45e400000000ec8000490520800000000000364000000033f9168000005d000005c1d9c0f5197054223a4bf70550000126c000026000000009f3000000000000004b4c27b00000000000a02186000017600001cecc611b50da83b0c000000065a116000000008780000ce638b0fe74720fd8
  | 47 => 0x1fa87021b284af51cc69b285d2e64bb88cd03b004924a45590b308570fac64c18140000000e2b1378045390c53c153103f48cc9af4f501690000000489926635985d200004170e1472e27ecebd00000004fa
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xbc0815c0320800b89cea194c2100020f6127694420006273b065288400ae0c650ca410800146d03b2882100238319432104200051b430a22084000f0432144410800b89cea194c010017131d8321402000664bb0642004000d28749412008001ac0e328240100034a1d25248020004e543c649004000d88748c92008001ac4a438a4010003708c8714802000436412eca9e2000a4c8259432c400b4990ab10658801693e18520cb1000526c30a41962000a1d839d5648400186ac938ea9080030d99071552100061ab20e2aa4200086c825d9538400185cc8392a7080030b5907254e100061b320e2a9c2000a4c82594328400b4990ab10650801693e18520ca1000526c30a41942000e0e641483284001c1ac8290650800a8de1b54106100051bc32a820c2002a37869d4418400546f0cba8830800a8da17631061000553416c620c2002a3786d4c418400146f0ca988308002c920953106100151b428c420c2000a3586948418400546f0c29083080278599632106100470b3286420c2000e86620c84184001e08a41908308003a199032086100061b324e32842002c357610650840050e9023b2a8880030dd9071551100061a320e2aa22000a4e82dd763440014a902aa6c6880021b2097518d1000526412ea31a2000a548155063440010dd053b2a6880021ba187254d1000617b20e4a9a2000c2c641c9534400189ec6392a6880031318c7254d100053240aa9b122000c4e759cf62440010df0ea9ec488002992055418910006263a8e6312200086c8754c624400149d05b18a48800293a0f621491000527416ca1922005a4e85d88324400149d0c290648801693218520c910006273b0a41922000c4c761483244001c1ec8290648800383190520c9100151b40eca20a2000a36861444144001c2ec628882880038518c511051000713b10a220a2000e2462144414400129904b98ca080021da0676550100042ec18ecaa0200086e829d953040030b90eb1aa608002932096354c1000627318e4a982000c4d631c953040010bb073b4a40800293a0b650c81002d2742ec41902000a4e86148320400b4990c29064080028da076510410004e841ae020820009e0825c041040054690abb0820800a8d21a75104100051a432ea2082000b3280d94410400162b063288208002cca0065104100151a42ac62082000aa48258c41040054690da988208002cca0353104100051a432a62082000e156354c410400164904a988208002cc20153104100151b42cc42082000a368694841040054690c29082080278519632104100470a328642082000e84620c84104001e08a41908208002e420d7010410005d0412e02082002c36751066004005868ec208a0080032c5d8410c010007c01908210020009b2879051004001b20e720a2008003681ca4144010
  | 1 => 0xec8290649800383190520c9300061b3ace9b0a600087787553614c0014c904a9ec2980039114832d85300052ac18ea30a6000c34751d0614c0010e90eaa0c2980029ca03531853000532412a630a6000a708054c614c001c88a4190c2980028da0764145300060e322e628a600094c825cc514c00189ae6310a2980028da1361145300062ab98c228a6000a3681d94414c00546d0bb0882980028da1851105300151a430a220a6000c3676144414c001868ec2888298002c560c511053000713b10a220a6000e2462144414c00129904b9ea8180021b20976550300043a40aecaa06000879861c1540c00149904b28641801693e18520c8300051a40aca2086002a3485584410c00154904b08821800a8de1851104300051ac30a2208600094c825cc500c0010e902bb2a9900028d20565107200151a42ac220e4002a378614441c800146b0c28883900021d205765522000526412a931c4000a5481552638800143b093aac710002952055458e2000626b1ce5a9c4000c4e631c9538800189ac6392a71001693e1b530ca2000527c32a61944005a4f869d4328800b49f0cba8651001693a17640ca200056340ec81944005a4f86d50328800149f0caa06510002d1205540ca2000626bb06528c4005c4f760c85188015c1cca19483100028d2056510620047073286420c4000e843298441880054690ab08831000a8de1851106200051ac30a220c4000e16631444188001c2ac62888310003c10c85110620007433188210c4000c4e639ca508800b89aec194a1100028da0775d91200043a40aea3224000a34815d464480010ed033b2a8900021da1871551200061bb20e2aa24000c34641c554480014a902aa6c690002952055418d2002c36410eca9a4000c2f641c95348001858c8392a69000313d8c7254d2000626318e4a9a4005a4e82d94324800149d0c290649000383d90520c92000706320a41924000c36759d361480010ef0eaa6c2900029920953d85200072229065b0a4000c34751d061480010e90eaa0c290002992095318520007222906430a4000a3681d90514800146d09b08a2900028da0765105200151b42ec220a4000a368614441480054690c28882900030d9d851105200061a3b0a220a4000e17631444148001c28c628882900024d20574194200043b40cecaa0400183c87591540800146902b22a8100030d99071550200061ab20e2aa0400086e829d9530800107b083b2a61000293a0b650c820004d4422e019040009e0815c0320800b4990abb064100169321a750c82000526432ea1904000b4a80d94320800161b083286410002d2a00650c82002d2642ac81904000ac481590320800b4990daa06410002d2a03540c82000526432a81904000e0d64550320800168902aa06410002d2201540c820005c4422e01904000
  | 2 => 0x5761045000516412c6208a000a348158c411400146d0331082280029320963cc45000437416ed188a000a4c8258d311400189ac6392622800b0d1d8414c4500070ab1882988a000d247210531140018b2c638262280034c104704c4500161b3b083908a005c4e760ca2114001e086420842280021b2097654f400049a40ae82968000a4c8259432d000b4990ab1065a001693e18520cb4000526c30a41968000b0d8414832d000146902b2883a000a8d21561107400151bc30a220e8000a358614441d000186ae938ecb200030de1271d96400043b40ceda9c8000934815d353900010ed033b0a52000295a07658ca4000527416ca1948000a5681d94329000149d0c29065200028da0765906400051b40eca20c8000934815d050900010ed0c38aa8a000293a0b75d8d400052a40aa9b1a800086c825d4635000149904ba8c6a0002952055418d400052c402a831a800086e829d953500010dd0c392a6a000313d8c7254d4000626318e4a9a8000a6481553625000189ceb39ec4a00021be1d53d894000516c20ea3128000a6a80d5062500014c902aa0c4a00029a2015418940006263a8e6312800086c8754c625000126902ba0a4a000293a0b63149400060eba0c62928000a4e83d88525000185ae8310a4a000293a0b650c94002d2742ec41928000a4e86148325000b4990c29064a0003139d8520c940006263b0a41928000b0d8414832500050ef0eaa6c2a00029920953d85400072229065b0a80028748755061500014c904a98c2a00028d6105218540007222906430a8000a3681d94415000546d0bb0882a00028da1851105400070bb18a220a8000e14631444150001c4ec428882a00038918851105400049a40ae9a98800086c825d953100010e902bb2a62000293209650c84002d2642ac41908000ac481588321000b49f0c290642000293618520c8400051a40aca2088002a3786144411000126902ba0a0200021d205765533000526412ca1966005a4c8558832cc00b49f0c290659800293618520cb30004a6412e628e6000a348159441cc0054690ab08839800a8de1851107300051ac30a220e6000b158314441cc00189ae7396cb1800313e0e72d963000437414edaa4600094c825cf548c0010dd053b2a9180021da06765523000527416cb1946000a4e82d94328c0010dd053b0a3180028ba0b659063000517416ca20c6000a3681d94418c00146d0c28883180025320973142300051b40eebb226000874815d4644c00146902ba8c8980021da0676551300043b430e2aa26000c37641c5544c001868c838aa8980021ba187254d3000617b20e4a9a6000c2c641c9534c001870c8382a6980029920554d893002c37c3aa7b126000a6481550624c00b0d90ea98c49800293a0b650c93002d2742ec41926000a4e86148324c001c1
  | 3 => 0x220a4200e146314441484014e102aa6c0908029a20953d81210072429065b024200e305110760484014e102aa0c0908029a209531812100724290643024200e305110460484010ed033b2a8108021ba0a7654c2100527416ca1904205a4c855d8320840b4990d3a8641080293219750c821005a340eca1904200b4681194320840b4990ab2064108169321b540c821005a340ea81904200a4c86550320840168902aa06410802e1211710c821005e0402e21904205c4e750ca610840b898ec190a2108339119432d042105706328652084200a3681d944108411c18ca1908210803c10ca511042100782190a22084200cc5760c84108411c88ca1908210803c1d50321042100782aa0642084202a34855d841084054690d3a882108028d219751042100593416ca2084200b268219441084054690ab18821080a8d21b531042100593416a62084200a348654c410840164904a988210802e120d7210421005d0402e42084202a368598841084054690c290821082f89197321042104f0a32c642084200b86828c84108411c28ca1908210803c1948321042100782290642084200aa5860c84108411c48ca1908210803c1d4c321042100782a98642084200e86860c84108401d0b0c1908210803a19d8321042100742bb0642084200f06850c84108401e0b0a1908210803c19d4321042100782ba8642084200f07650c84108411d0cca1908210823a1194321042100782328642084208e04650c8410840b89cea194c01080b0d9d4419802100742190833004200c35641c5549400189ac6392a7280021ba0b73592500043b40ee8b1ca000874815d2629400107b09bb4652800287613768ca5000527416ed194a000a4f87988329400149b09310652800293a06620ca5000527c3484194a000a4f86508329400168902a106528002d2201420ca5000436412e730ca00085d83dda419400143b07bb483280028da077690650007073106520ca000e0e620c8419400146f0f30883280028d60e61106500051b414c220ca000e16329844194001c286530883280030ddd8418c6500061bbb08298ca000d24721053194001a608238263280030d5d841c865000626bb06510ca000c4f760c8219400186eec2084328003c10c841086500061bb20e2aa2a000c4f631c9535400586ee838ac82800b0de10715905002e27b98e4b18a005c4f831c963140010d904bb286280021d2057650c500042ec1ce3310a000a348159342140010ed03bb484280028d20564508500061ab20e2a10a000c39641c1421400149d05bb4642800295205648c85002d26412ec190a000a4c8259032140014a902b20642801693219420c85000706b2284190a000b4481508321400169100a1064280020f61272984500062739065308a000a3681dda411400145904b1c822800a8d20
  | 4 => 0x24c40b49d0bb10649880293a18520c93100707b20a41926200e0c64148324c40146d0d28882988038918a511053100713b10a220a6200e2462144414c4054690daa08298802c560f54105310051a432a820a6200e2754188414c401c4aa8310829880a8d21a75105310058ac1cea20a6202a34865d4414c40546d0db28829880a8d219531053100592412a620a6200e2465d88414c401c4eca310829880389194621053100713c28c420a6200e2485188414c401c4cea3108298803895d4621053100743c18c420a6200e2753188414c401c4aa631082988028da1a521053100712314a420a6202a3486148414c401c48c42908298827851963210531007423146420a6208e14650c8414c401e08a41908298803a1188418c5310071832883b026200ea062107604c4014e102aa6c0988029a20953d81310072429065b026200e3051107604c4015650c208c0988038cd94411813100718328823026200ea362104604c401d40c4208c0988029660c75181310052cc1ea83026200a7281d50604c4014e102aa0c0988029ca07531813100534412a63026200a708154c604c401c90a4190c0988038c944411813100718288823026200e3354104604c401c62a8208c0988038ca14411813100718c28823026200e3375104604c401c60ea208c0988038cd4c411813100718a98823026200e3252104604c401c60a4208c098803a48c8411813100748190823026200ab284cc4604c401d2083188c0988021d618715503100526412ca1906205a4f86148320c40129904b98a21880a8de1851104310051ac30a22086200b1583144410c401aa4a238262188035454c704c4310050ec1ceab264200c35649c754c840186cc838aa9908030d590715532100617320e4a9e4200c2d641c953c840186cc938ca59080383990520cb2100706b20a41964202a3786d5041c840146f0caa0839080a8de1a75107210151bc32ea20e4202a3685d8c41c840156501b18839080a8de1b53107210051bc32a620e4200b248254c41c840546b0d29083908278599632107210470b3286420e4200f04520c841c84014a902aa4c710802876127558e210052a40aa8b1c4200c4d639cb538840189cc6392a7108031358c7254e2102d27c36a61944200a4f8654c328840b49f0d3a8651081693e19750ca2102d2742ec81944200aca80d90328840b49f0daa0651080293e19540ca21005a240aa81944200c4e639ca518840b89aec194a31082b839943290621047073286420c4200e16631444188401c2ac62888310803c10c851106210061bb20e2aa24200c34641c554484014a902aa6c690802952055418d2100617b20e4a9a4200c2c641c9534840189ec6392a6908031318c7254d2100527430a41924200e0f641483248401c18c829064908028da1851105210070bb18a
  | 5 => 0x803c114832984410149b42ce1308820293681dda5110401a1ce4194a22080f0d5da619444100496412e62888200c3576984511040526f0cbb0a22080b0de1976144410049bc32e62888202d17835cc5110401a4f04b98a2208024d209731444100692412e62888200924825cc511040126900b98a22080a4da1f63144410049ac3ec62888200d1573d8c511040164d05b18a220802c960b63144410049ac3cc628882009358758c511040526d0e318a2208024d61c63144410068ab98c62888200935869c8511040126b07390a22080b49a0a72144410049b404e4288820293687d88511040126b0fb10a220802c5a0f62144410058ac1ec4288820093787988511040126f0eb10a220802c5e0d62144410058a41ac42888200b3380588511040166100b10a22080a4da1c62144410049ac38c4288820293687cc8511040126b0f990a2208024de1e32144410068ab9c642888200d17878c85110413a290f190a22082745dda32144410068abb464288820eb16828c85110401a2ce5190a2208024de1d32144410149a43a642888202936870c8511040126b0e190a220803455cc32144410468b438642888200d15870c85110411a2eec190a220803455d8321444106d8b410642888200f06820c85110411e0ee4190a220803459c8321444104782390642888200f06620c85110401e0ac4190a2208024d61a70144410049ac1ce02888200936829c05110401a2c65380a220803450ca701444101699404e0288820093687146601040126d0e28ac02080345dcc51580410068a398a2b008200d27721456010401a48e428ac020803459cc51180410068ab98a23008200d26721446010401a4ae4288c0208030759173d5331004a6412e7aa66200c36641c554cc40186ac838aa9988030b9907254f3100616b20e4a9e6200a4c8259432cc40b4990ab10659881693e18520cb3100526c30a41966200e0e6414832cc401c1ac82906598803135ce72d963100627c1ce5b2c620086e829db548c4010dd053b2a9188021ea02765523100527416cb1946200a4e82d94328c40129904b98a3188028ba0b659063100517416ca20c6202a34855d8418c4054690d3a883188028d21975106310058ac1eca20c6200b2682d94418c40162b063288318802c920953106310151b42cc420c6200a3686948418c401c4cc42908318827851963210631007433146420c6208e14650c8418c401e08a4190831880b0d9d441982310050ec18ebb22620185c865cf544c40183ec8b9ea8988025320973d51310061bb24e3aa26200c37641c5544c401868c838aa8988021ba187254d3100617b20e4a9a6200c2c641c9534c401868c838aa6988029920554d893102c37c3aa7b126200a4d83d50624c4014cd03aa0c49880299205541893102c3643aa63126200a4e82d943
  | 6 => 0x586c38a41948200b0e8614832904156190c2906520802c3a04520ca4100587400a41948200d0e720ca519040125904b98a3208021ba0a7654d4100527416ca1928205a4e85d88325040149d0c29064a081693218520c9410161bba0e2b288202c34741c5651040125904b9ea8208030ddd871550410143a40aeda98820086c825d953104010f100bb2a62080a4d2157190c4100496412eaa188200938805d543104052690ab88862080a1d20576148410149a42ae3a10820293685dc5421040149904b286420802c3209540c84102d2642ac41908200ac880588321040b49f0c290642080293618520c84100586c20a41908208b0c8590832104116190aa106420802e2201420c8410243bc32e82888200937845cc51104012c904b98a220803455cf431444100593416862888200b2582d0c511040126b0f218a2208024d61c43144410068ab98862888200935849c8511040126b0fa10a220802c5a0f42144410058ac1e84288820093787508511040162f06a10a220802c520d421444100599c02842888200b308050851104018aaed190a220803155d8321444100783210642888200f05420c8511040126b09380a2208028d61b549044100496412e73288200934815ce651040126d03394ca208024da0670994410161bbb0e2b288200934815d6631040526902bb6a6208024da0672d4c410049b40ce1a98820bd2451dc95310411a4ea2392a620823491447254c4100496412eca988200938805d95310411a1ee6392a62082343e0c7254c4100693c08e4a988200d24811c95310401a48e5b8aa62080349dc87154c4100692390e2a988200935861c5531040126d0438aa6208024da007154c410049b40eeab108200935869c6521040126b0738ca4208024da02719484104e8a28ee6a908208d14511cd521040526902bb0a4208024d20573148410049b40ce02908200934815d732104052690ab8e64208024da07758c8410058a40aa71908200b0e82dd6321040162d03bac642080287618758c84100587410eb1908200b168194a321041362d0bb8c6420802e4a03718c8410049b40eea990820293685dc5321040126902ba86420802c5205530c84100496c38a41908202934855c4321040136100b886420802c5205750c84100586412ca1908208b0c85588321040171100b106420822c3a0a520c8410058b40ca41908208b0f87148321040161b0e2906420822c3e18520c84100586c30a41908208f0781148321040161d022906420823c1204520c84100587400a41908200f04529c432104116290ab886420803c1149710c841005c8402e21908200a2c8254e6110415c18a4194c220802c560c75984410149a42ae730882009a4825ce61104012690ea9cc220803455cd539844100592412a73088202936859ca611040126d0f294c22
  | 7 => 0x87841c5420c801a8ea838a8419003515507150832006a43aee0a106400dc071dc1420c801996ec382841900352dd47050832006a43a8e0a106400d8b741c1420c801b86e23828419003701c47050832006a5c28e0a106400d48851c1420c801a94ca3828419003525947050832006a5aa0e0a106400d49541c1420c80b29f0e29084190025361c521083200586c20a42106400d0e7414b610c801a1ae8296c21900253a1c5298432004a7438a4b086400d0f74149610c801a18e8292c2190035214b7058432006a4290e0b08640094e8714a600c80129d0e292c01900343dd05258032006863a0a4b006400d4452dc5600c801a88a438ac019003439d0521803200686ba0a43006400d44529c4600c801a88a4b88c0190031358c7254e5100437416e6b24a20083d84dda329440143b09bb4652880293a0b768ca5100527c3cc4194a200a4d84988329440149d01310652880293e1a420ca5100527c3284194a200b4481508329440169100a1065288021b20973982510061bb20e2aa2a200c2f641c95354401858c8392a6a880313d8c7254d5107f06296c8192a20ee0c52190325440b89ee6392c62881713e0c7258c5100526412c7a18a200c4d639cb43144010d904bb286288021e2017650c5100526412c6218a20085f835d262144010bb07384c42880293a0b768c85102d26412ec190a200a4c82590321440168d03210642881693219420c851005a240a84190a200b488050832144010bf06ba4c028803139c8329805100436412eca9e8200a4c8259432d040b4990ab1065a081693e18520cb4100526c30a41968200964825cc51d040186ae938ecb208025320973196410162b30ae632c820092c825cf549040586eec38aa920802932096354e4100627318e4a9c8200c4d631c9539040125904baa87208024e2017550e410042ec1ced2948200a4e82d94329040161904aa0652080293a18520ca4100586c20a4194820ab0c8590832904156190aa106520802e2201420ca4100496412e632c8202c36615cc6590401a1f04b98cb2080247209731964100686412e632c820090c825cc659040583cc2b98cb2080b0598573196410161b30ce432c8202c36619c0659040126d033b6a7208024ba0a7654e410049b40ceca9c820093a809d9539040126d023b2a72080e4721d6354e4100586412c6a9c820ad0f731c95390415a1f06392a7208034398c7254e4100686b18e4a9c820091d839da529040126d033b4a5208024da047694a410049b40cec2948200b0e82dd6329040143d0c3ac6520802c3a08758ca410058b40ecb194820091e87196329040162d0232c6520802c3a0b650ca410058b40eca194820091d87194329040162d02328652082ac3a17620ca41005c340ec41948200b8a80d88329040170d02310652082ac3e1c520ca410
  | 8 => 0xc5380cb1900253a0a76d5232004a7414ecaa46400956819d9548c8012b5013b2a91900253a0876552320348e43ac8aa46400b1481591548c81ba2ee838aa91903745e1071552320068b320e2aa46400d15641c5548c8012a902ba0a51900255a077590a320043b40cecaa26405c4f731c9650c80b898e6392ca190161b20976d50320043a40aecaa06400878805d9540c8010db0c392a8190025520574d4c3200627bb0e4a98640594c855cb430c8012a902baa8619002562017550c3202ca642ae4218640094f835d0520c8012c902ba0a41901e1be197314832004a6c3e862906400d0d7490c520c80168d03218a419002d16064314832004a6c38862906400d0d7410c520c80129b07388a4190025360e701483202ca643ea6a106400b0d84d4d420c8012990ea9a841900351d4c7150832006a2a98e2a106400d4b531c1420c801a92a63828419002532097499432004aa40ae9328640094e829c6650c80129d05384ca1901713dd87259432004a6412eb320640594c825db540c80129d0538ea81900253a0a70d5032086a2296e2aa0640ed47521c5540c81da88a438aa819002552057655032004ac402ecaa0640094d861c9540c80129d02392a81900253a007255032006a2396e2aa0640ed17741c5540c801a8ee438aa819003511c871550320768bc20e2aa06400d47821c5540c801a890438aa819002c3610759883202ca642ae931064009c4815d2620c8012990eaa4c419003435d15498832005a240aa9310640594e859c6620c80b29d0b384c41901653a0b769483203626bb4c52906400954815d0520c80189aed310a41901653e19761483202e27c32ec290640094f865d0520c80ba1f08ba0a41900351e057414832004a640ae82906400d44815d0520c80128902ba0a41900253201741483202ca743ec8290640094d87d90520c801a1ae9b20a419002d1a076414832005a2c0ec8290640094d87990520c80129b0eb20a41901653a1c6414832004a6c38c82906400d0d74190520c80129b0d388a41900253612711483202ea340ce2290640094e809c4520c80129b0d380a419002536127014832004a740ce02906405d4a809c0520c8012ad03bac841901653215769083200586c26eb2106400b4681dd6420c80161b083ac84190165321e6590832004a643acb2106400b4481552420c80b29d0b38c841901653a167090832004a743ca4a106400d4452dc5420c801a8ca438a8419003511487150832006a4296e0a106400d4a521c1420c801a90a4382841901653a1f755083202ca643ccaa106400b0d84995420c80b2990eb2a84190165321d5450832005a240aa8a106400d4475dc5420c801a8eea38a8419003511d47150832006c3ba0e2a106400d47851c5420c801a890a38a8419003519947150832006a2b28e2a106400d
  | 9 => 0x741895300535c02e8312a600a68805d06254c0145d09b88c4a98028b613711895300526c1ce2312a600a2f845c46254c0145908b88c4a980293e0d711895300535c02e2312a600a68805c46254c0149b07380c4a98028be11701895300516422e0312a600a4f835c06254c014cf02b80c4a980299205701895300517420e0312a600a2d841c06254c0185ce8316c2a98030b5d062d855300437438c4b0aa600c2f741896154c01858e8312c2a98031a18b705855300634310e0b0aa60086e871896054c0185ee8312c0a98030b1d0625815300632316e2b02a600c64621c56054c010d904ba0c0a98021d20574181530049a40ae9a9e860086d861c953d0c014c902aa4c5a1802992055458b4300516c26a6b16860586c8754d62d0c0129904b9ea9218021d618715524300532412a730c8600a5583d516190c050e90eaa2c32180299209535864300627b98e4b2a8600c4f831c96550c018c8e5b8acaa18030ddd0715954300633b90e2b2a8600c64721c56550c0186f0838acaa18031a1cb70595430063838ee0b2a8600c3b741c16550c018b6e6382caa18031adc8705954300634390e0b2a8600c73711c16550c018e0e2382caa18025320973d51430049a40ae9a9a8600c35641c554948010ed03ba2c7290021d20574982520061bb20e2aa2a400a548155363548014a902aa0c6a900313d8c7254d520161bba0e2b20a402c37841c5641480146902b2486290030d5927190c520043a40aeca18a400878805d9431480146902b2086290020fe1173984520041ec24e1308a40083f845ce60148014a902aa4c7a1002952055458f420049a40ae9a9e8400c1d7458f53d080189cc6392a7a10031358c7254f420061aba4e3b2c8400c37849c765908010ed033b6a7210024d2057414a420043b430e2aa28400a1d841d763508014a902aa6c6a1002932095418d420052a40aa831a8400934815d3535080183ae9b1ea6a100313d8e72d4d4200627b18e4a9a8400c4c631c953508050ef0eaa6c2a10029920953d85420051ac26a630a8400a6682d4c61508014c904a98c2a10029c20554d814200534412a7b028400a39841d460508014d505aa0c0a10029a20954181420053840aa83028400a3984d4c60508014d505a98c0a10029a20953181420056541e843028400934815d052108010e902bb2a999002592057414b3200626b9ce5b2c6405c2e625d0658c80126902ba0cb190021da0676552320043d404ecaa4640183c87591548c80146902b22a9190030d99071552320061ab20e2aa46400954815d3538c80b89eec392a719002552057550e32004ac402eaa1c6405c4e625d0658c8012a902ba0cb1901707989741963202e07312e832c6400d17815d0658c80123902ba0cb190034520574196320048a40ae832c6405c4e629c4658c80b89c
  | 10 => 0x80000000000180200000000080000300080000000280080100000100000300180280000000000000080100180080180100000000380080000000000100000000000080000000000000080000080080180080000000080200480300180000100080000000000000000100080000080100100180000300000080080080100180080200100080100000000000280200000000100000180000080100080080000000100000080000000180000000000080000000080080100000000680000000200100080000080080000080100000000280000000000000000080180000200200000200000000000080000080000000180080200000000200000000080080000000080380080180000000000080100600180000000000080000080200080080180100000600180000000000000080100380180000180000180100000000000080180000000000100000080200000180000000000080000100400200200000000100000000100000200000180000080300000080000080280100000000100000000180100000000000080080000000080200000000000180000000080000000100000080100080080000100080080080000400000080000000080300080580080180080000000100000180200000180000000080100000000200000000000280000280000000000180081713dcc7258f5402e27c18e4b1ea80085d839c662d500546d03ba4c3aa0029920963d855400538402c7b0aa80086c825cc61550010f100b98c2aa0021d61e631855400533c12c630aa800a648258c61550014e700b18c2aa0029c20163185540052b41ec430aa800a5583d8861550010ef0eb10c2aa00295e0d62185540052a41ac430aa800a738058861550014e100b10c2aa0028d61273185540051bc22e630aa800a67825cc61550014c904b98c2aa0029ce01731855400538402e630aa800a5683dc861550014ab07b90c2aa0028d61272185540051bc22e430aa800a57835c861550014a906b90c2aa0029ce01721855400538402e430aa800a35849c0615500146f08b80c2aa00295e0d70185540052a41ae030aa800a67825c061550014c904b80c2aa00295a0c70185540052ac18e030aa8008768718560550018aee630ac0aa003151cc615815400633b90c2b02a800c647218560550010d904b98c0aa0021d20573181540161bba0e2b26a602c37841c564d4c0b49d05b9cc5a98020f61272987530061ab20e2aa4a600c37641c55454c014c902aa6c4a980299e0554189530053240aa8312a600a64815936254c014d100b26c4a98021d20574189530043c402e8312a60086d879906254c0149b07320c4a980293e0d641895300533c0ac8312a600a64815906254c014d700b20c4a98029a201641895300526c1ce8312a600a4f835d06254c014cf02ba0c4a980299205
  | 11 => 0x200000002bb00000015e57445d0000000000000005b30003974774370b20000b000013424c2863650000000000000000000000000000000001960002190001631860000000002ab0002560b100017600043e0000d50000000000000003190003422d900032603d0003e60000004fa2d50000004b800000059f0000000000000005a54b74ed5440000000000000003a80000000000000000001471e10000000000000004805520004870a60000000000000000000000000940000005970002be10559546031f09541600000000000000000036a41508f5a83b30000002690004af00012c00009c4f55380000000000003d000000000035f00057d1411a550300030654f0e40a405800000000000000037a2440150000461d100039400023f0002740004975020064b33641740004560002730080000000000000000000000001931f300018956f0252551e20000000004e90004080000000000000004bc0004330000000691ab2f10670000000000000000000005750000000003ca00000000045b3c21402c630d0005450000000230000bc5aa00000000046a00039c0000000000002510002e24900000f32ed2970000000003f62ea29014300000010f0001c109200009300000038438c5603834bd15c0000003482f92b50ad13d0001380000000002890000000000001c400005f22e0002540000000003010522370000000000000000ff0004492150f70004d80000af47b0000000003135064960003e30005583b11b43e14352ac00000000033811c1f80000000000003fe2a444a0003b000029205c56342a10451445144f1a212d0001dc0002af0000220000004a725d4f70603731dd30b1c30000000000004ac46656e4182f70000000000000000000005190002ef5780000000a000000000000000001c0c520200000000000000000048600000000000000000014b42d0002b200000000014c4290000000000d02c100000021200000022b5720005994e21252e642e00000030f0004a400035200000020c0000004db00035849933e02946700000000002d0000000005040000001c700000003400000017e00029a0004f2000800000801001001001000000000002000000000000000800800001001000000801000000000001800800000800800000001000000002800800001000800800801000001800002000000000003000801801000001800802000800800001800801001000000001002000800800800800000800000000002000000800801800002802000000000000000800800000000800800800800000000803003800002000001003000000000800002000000801002801000001801003001000800000802003001800800000001000002000000000800000000001000000000803000001000000000000800004800003000003000000
  | 12 => 0xf0e300026f0de55000023a4a62580000000000000000003431d90000423250000000000d20004925490000000fa0000000000005350000000000000003cb03a0000003761ff00016b4460004c500000000000000043f31000000000000059e00016000052304e0781c60000000000000000000000000000003a510933900000000056900000000002051e0003ba0000001b30000002cd00008c3b82aa10709a2ba0004130000000000000002630001d32a82c705600025f00000000000000013b00000000000000000035000017c1d737b00029d00000000000000017f4ad0000000000000634bb5a03442f22490000002d800053f50e0001870000000005430000003c000000000000000044458200000000000000000043d2b61550000005120000003b60000000000004a30001eb0000874a800000000046300003845200000000007300000033700000033d2c50001b100000010c4e45421644470002fe3880000002880000000000000000000000001b800000000000005e0000000004e10000000000000000000002f51815870000100005a703c07b0e80000002320003950001a600000000000000030900000000016e0002910ba00000000000003700031205113700000000000000000048c0003670000002c834d41a0852523153b73141291ba4ab1ad3f719700000000000008b0ef4dd1ed58f00000037132f0000000000000001cb11956634000000053c0000000004f35243863180003cd00f00046c0cd32400000012a0005840004e71543fa00000006b51300023830e3d343810330200004300001d08314e1940000004aa5a22c058b0cf00000056d1bb00000034e3b21b600000000000000000000000000000000000033b00000000000000000000000000000000000000000000000000000000000000021400034b4c30000000000000003e425c31c0002de00045802826119d2ee48b0000004fb0a108e0000000003cc57f2172940000000e50000003350000000000005700000003775ae58d00014800011b4782a500025700124d3dd5314c100045c00000006100000032d4ce2044c60000e111a05a55d15300000018818a1e746957a0000000004940000f853420b10000000016f4b100000005b1712960000000fd44d4c900000055c39a0000003461fd00013e0fb0000072a100000000036f3623df47300a3f00000000000005770000000000001984591650000001510fc00058100041b0000000000003f300000000025300000022d0001804985853362360000005882cb0000000000005080000000000000002db02c15f53a0002e81e537438100000000011327221629b00000000026d00024e0c82200004e61284b930542032b0001e01c523c1670f00005ad00021e10d4315092400c740457e0001e41a308a0000002333
  | 13 => 0x4cc20a0b437f1d200038032e0002d30000004710000000004a51685af21f00000056b0000000000d11a04fe00013500046538f1e30000002b846d0003c14ff0000001490005531792030cb00010155a51a2b40000002ca00018b00019900000000037551c45a0d40000000620001cd0000000000001a40003f40900005a60000000000000004df0f10002704e33301db2302620000e95920fe0004935980000000002b10004d50005894cd0040000980000000000000bb1b93c90004b00000000003da46f1b53b40004da00028b00013138243b0002b33315b028d1700001ea34a2c20000004f111e4c045401600059a0002dd0003de46e0003e70be4a215200050f16d0000f206600034f46b00007036e2b035400000000037c2d40724141272e000000000000007c1330770000005550000002ec3bd0000b62b700d3600003a31100001f40000000000842450a30000000000000000000000000002a04dc00035942200000000030c0001fc0002e400000011f0000000000000000005b40d845e1d500000000000000026527900000000000000006500000051b00043c00000006f2df00000058a29e00000000000000000000058300000000000000000000059000000004a0000000002e35930135764254a125e2ad0004cf0c638900041e20d0000001570320003eb0000000000000003be0b30000003ef00002100028f00000045500000000000031e0000000004be00000032c53001e5395360000000004485590000170000003f90000000000000000000003a709600032815b00031a37900000000000000000001900000021352f37e00020100048d0000000000000000002f051f00047500000000000000054b00000029300000000000000035e0005474d209b0020540b510b41240d2344790001f21840000000000000185481920000414b40001f000000027a0002832ff00000009f1ef0c03030000003a60003d700000000000052e15000014d3a93491bf00045317700000011420503303e33a0000002783071210000000000000b800017d0000000004403530c33d100000000000022f1ec00034c0000000000000000000000000000001830000000000000911a100057900007e0000000000000000000000003510990ee1b00ed00035d00016c19a1bc0004c80002eb0001ce3d40003d941f0e011807f4060002ce02f00014a4233b51150004d60001cc1242d627e1220000002844610000000003a10000002a90000001124ef0000002f600000035a1c000052600021832100000000025a4910000004c200000000000036902700000000000000040a48e4114ec5332a30bf00000000025b00000000000000000036c0002603fb00026c00000000000000000033400000049a0000000ae00057c39f3ec3171d800055600001
  | 14 => 0xc44d000000054c21d00000000000000000000543a00000006a00051730456a08022300000000000000021c0392a23ae2255003dc10e4e800049c2080000001440000000000000004d30001a700036627f00017804d00000e00000000000021a4f61fb4880000004a923900000020e1e80000003330000a20000000000000f40000000002fd3ed4070eb1df4ee00038752b0000000000000004362fb0000000003e00000003560351390001590642113bb00005053d00054d2280000004420ea1d60001ae0000000000000000004ea36d0ca0002e14f846850714213c2e93702cc19b00000000039200039900000012e00041c00051054100000000002e2b92680000820000000e600000018500018e47d3fc37243000903b3ea0003cf00000050100000035b0002421d400000000035c00000000000008800048200000015a05d0003c60004f904c00056829c0000002480000004830002fa2062ae39600000011700016618c2c900000000000000000002b0000000000000000004410000000001b74d947c39b0002710000000000000000000000000001da59d4740000001a84640000003bf0002cf0002c300028e2bd0000000bd4280000004c400041901a3d823b0a900000036b00013a3ac0001323fd07500006e50b00000038b0000000000000002670002a70143db19051600000037823e0000004d147e28a00000000000000000000023d4340000000000000004b240c0004100003e800040e39318d00039802a13f00000000033f25900049b00055f0d300000000037d00052c3a444300027d3bc4fc0890003450000000dc4272810000001a90001450000000000000000005183c50713af36800000013000000000000019500000049d14642600000000010659454a0005650000000000000000000000000004620000cc1ee59b00041d0b900000000000000022700000000000000000000022900000021000000000000000000000012b59c00000045700000000000000002600000000000028c0ec0000300d924f0000000003410002bf4d400000049e00000000054042c00016200000000000050a00000000000000022100000000000018f06d3220002d10000000dd00005907427c0003ee0000000db00000000000017256c5a11aa0002800000004cb00000024b00000000000058c3901f51110000000000000002470000000004ae0001f10a800b00000000026e2955a30002870000000000000000000002d23ff3d50000000000000000000000000003aa30a0000000002a600022c3e226600033c0b700006c00000000000000022a0c24ba0000000000003a250d38d0000000000000a557335704445f4eb00051100000000019100000000000004006808d0000002090000000000001b20f50f600042100027500015814f000529000
  | 15 => 0x53b0000da04f00000000019e00000000052d2990e70004094ca0002da0003c70000000811e900000000000053e00019f0000005220000005282f32dc0002fc4241c811d5800004e515d40255400000000000000000000000045038e0001e60860f90003d22c40000d600000000022200004b0000000000000000005514841200c10003630000001af26409d07956400000003100012f4390000000001c200000000000000000023117501200055b00000000000009e00017a0000005910000002434b60000000003a000000058e0000000000004b50ac0000000000000000000002460003610003470000003e957147a26a5ac20f00047f00048500000000000000032a00032353700000000000000044b0aa5a400000000000000000000007a00000005554600039d2e52f40000000000000000000000004320000000005213f20000ce3553f810800022400000000042f40131600000042b1f60004703c33d61d00df3850ab1233ce24a51d0000570004720000000000450000000000000005270000004450000000000000000000000000000000001cf00000000057b00016129800000048a44c3290004030000000005610000000000003c44d700000000000000000000000000000044e05300000004700017b0000000004f00000000000000003f500040f5ab00000000000050c10a0242d700040030048f0000001ac0000000000002e700000000000339e50539100000000000040b0002411c91561160000484175670a70000000e22bc28200009700000052a4de4bf3f12070001de19c0001bd2f83c82850110000003110004815860003e50005b10000004f40000004fd00000031b18200000000000020000051500003f5b249549f27700030800000010255e07d25040516926b00052027b1fe0000001262d000000000000023500013621b0000000000000000000001fa0000000000000000000000000760004760000000000493b90d700000000052500000017300033200000000000000000000056231d4a00000000003ab5a938a0360002265961f70005570000000c91be00000054e2764e03ad0001ca32700000053200048900c4c71f929f00001b16a0000
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x40170090508321444100445e4d849c0511040111593a067299441076039c9861d6321041321491618758c841044c124586148321040130691a00520c841006c0148805c432104013049260c7598441005412497354e61104019057320953984410044564e8794a611041190783209731444104641e4c825cc5110401504925cf6314441006415ce82d8c51104011249261d63144410044c2418758c5110401504925cc631444100445e4d869c8511040111593a02721444100541a4b878c8511041d5049261c3214441005c0241620c851104011179361a701444100641a08329c0511040180d6420973d5331004c124983194418c40120c9260c75d913100603d90825cf544c40b04c9760f5418931004c124983d50414c40160593d50621053101485259839d4414c4013049260e75105310058164e75188414c41d2249854c621053100492249831d4604c4012489260f54181310058464f54104604c40161193a1441181310058464c75104604c4016209254c41181310078014832104604c4013049260c511043100483249839d564c84058147160e755932102e031c9849d56388401214916127558e2104581255860c84108411604955d832104210458125a850c841084016049661432104210458125a750c84108401604965d4321042104581a5b650c84108411c06750c841980210040d24584dda329400121491613768ca500048365387988329400124491612620ca500041324983dda419400120c9260f76906500048564f8798441940012249260e611065000701dd832104219400143091590705085000581245645083214001a0564205420c8500068259080508321400140d949c832984500048564e8198841140016049258c414c4500070158c7210531140014489258c704c4500070458c411c1311400130491610520cb4000491a4686148329000122491610751894000503650751cc6250001414915d063149400050924574188525000180c76610520c940004c1245841483250001605941483218540004c12498314441cc00122692a18511063000491249831d4614c001415931d4741853000603190825cc514c001444925cc6114530006051d983144414c0013049260c51105300068160c62144414c00b80c726127558e2000485245849d56388011a07860c851106200040d245841d9530800120d94219750c820004c124584194320800b20c98591540c82000581245645503208001a0564205540c8200140d245849da510800140d949d8329442000483249839d564840058147160e755921004581e58520c8418400104c9260c765501002c13249839da5204001215932197510410004c12498319441040052149858d5310410005812496354c4104001a056320953104100048564e869484104011604961483210410
  | 1 => 0x1c00072001a8660042801607755a8c7eaa1c27800000c9ac005f5a000e82e001801049330a14e3b2509516424e9d934a94d84d040e112b822a1438f02a1e001a0dc4e1017454810f8c4204f1096d2264000c868840b8bce27b1aa3002ac130b0b0451680914304aac416a546a3846001ea9132033a8113e694494c480014801400a4e10d107d3e1107c4004ad8b255001340000062dcac0000001505c0010498003180000003d0ac00005680000002819c000048000c41b289f8004659a88003a49000f2005aa011ea61b00000482b92ce6123c2c81a542f0183a96078dc006d0e05000940d0000005002180000138015e002380000524981c0039001bcca0036000b4610c26000830b00000000025cfe0101030c02040001000306020004010006010c050802000007040200001f021101011f050d0100000213000c08032e010e0f050403242a14011604000000491249831c061550012249161070189530048924584d4d62d0c012449260f54586430040da47845ce6014801414915d163d4f4200485245841d76350801414915d363d4d420048c245841d4605080123091613531814207609988815d0658c81d8466220574196320870198b815d0658c81d80e62205741963207701988815d0658c81d81662205741963207601988815d0658c801504915d24314832006415d28190c520c801504915d0431483200443e51839c4520c80110f9460e7014832004c124584d4d420c80150594d4c715083200542653531c1420c80110d94a0a7199432004c1245841d6620c801504915d15498832006415d081552620c81d90784205741483207641e50815d0520c801504915d36414832006415d281d90520c8011449161d64148320045224187590520c801504915d0641483200443e51869c4520c80110d94a02711483200443e51869c0520c80130491610759083202c4325d84995420c80130491612655083200541652651c5420c80150994214705083200542652651c1420c801540915507050832004c124584148420c80503491613768ca510048365387988329440104e92e0d749805104611984825cc659041182661209731964105f01987825cc659041181661209731964104701984825cc659041180e61209731964104601984825cc659041f80e72a18758ca4104e0598687196329041f10c9261c650ca410460598587194329040130691a18520ca4104491245861483210401504925cf4314441006415ce82d0c5110401504925cc431444100445e4d849c85110
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x49c98a01eb14a2e020032900016a8600069003000060e88c102207143000000000108350f28c1ce0290640094028594d4c705083200420d43ca30d380a419002500a1650851c1420c80128050b29328e0a106400841a8b93612701444100420d45c9b0d380a220802600a264f54104604c40130051327428823026200980289931d44118131046008e2493073aac99083b00472245849d5638840110250b29c3cc4194a00088128993e1e611065000540142b2100a106428002c00a258c411c1311400120250b283a8e63128000c011d891610520c94000480944c98ea3a0c2980030047624983144414c01d80239122c24eab1c400088128594219750c82004480942ca4ec194a21002300471249839d5648400110251326432ea208200e88128993a1a5210410
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x6
  | 2 => 0x28e
  | 3 => 0x148e
  | 4 => 0x184e
  | 5 => 0x3ce
  | 6 => 0x15ce
  | 7 => 0x170e
  | 8 => 0x3c296
  | 9 => 0x15c296
  | 10 => 0x3d496
  | 11 => 0x170296
  | 12 => 0x3d856
  | 13 => 0x295d6
  | 14 => 0x283d6
  | 15 => 0x1483d6
  | 16 => 0x1843d6
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 74
  | 6 => 2190
  | 5 => 5308
  | 4 => 1461
  | 3 => 184
  | 2 => 26
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
  | 7 => packedAt gbK7 (2092+((h/24+packedAt gbK7 (1924+(h % 24)*7) 7) % 116)*8) 8
  | 6 => packedAt gbK6 (89790+((h/730+packedAt gbK6 (81030+(h % 730)*12) 12) % 2891)*13) 13
  | 5 => packedAt gbK5 (277781+((h/1769+packedAt gbK5 (254784+(h % 1769)*13) 13) % 7707)*14) 14
  | 4 => packedAt gbK4 (92043+((h/487+packedAt gbK4 (86199+(h % 487)*12) 12) % 3104)*12) 12
  | 3 => packedAt gbK3 (13368+((h/61+packedAt gbK3 (12880+(h % 61)*8) 8) % 243)*9) 9
  | 2 => packedAt gbK2 (2154+((h/8+packedAt gbK2 (2106+(h % 8)*6) 6) % 35)*6) 6
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffffffffc00ffffffffffffffc3ffffc3ffff
  | 1 => 0xff800fffffff007ffffffffc003c7fe3fc7ff8
  | 2 => 0xffffffffffffff803fc003ffffff8c7fff8e3f
  | 3 => 0xfffff003ffffffffc00003fffffff07c3ff03f
  | 4 => 0x3fffffffffffffc00003fff803fffc0
  | 5 => 0xfffffffc0000000000000000003fffffc00000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x2db4b52cac0065b2d2dab52db541b5adc1b6db
  | 1 => 0x578c0b555dcb0055656d3b540d1c5ae2dc5b78
  | 2 => 0x9ad95e9a76d5aa803981929ad9ae8c576e8e2d
  | 3 => 0xe36e63039b66d379800623e36e377078377036
  | 4 => 0x700c03e3b8fc6e3e37c000703bef003bed80
  | 5 => 0xfc7f8fe003c0e07030380303803fffff800000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xe888a080e888a000e888a080e888a000e888a080e888a000e888a080e888a000e888a080e888a000e888a080e888a000e888a080e888a000e888a080e888a000, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_15135
namespace PEqualNP.Outside.L_meta_15135
open PEqualNP.Outside.L_meta_15135.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_1_0 : Interval s1Atlas 1 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_1 : Interval s1Atlas 1 0 1 := bs1_1_0
theorem alls1 : ∀ k ≤ 1, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_1 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_1_0 : Interval s2Atlas 1 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_1 : Interval s2Atlas 1 0 1 := bs2_1_0
theorem alls2 : ∀ k ≤ 1, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_1 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 1 := bs3_3_0
theorem alls3 : ∀ k ≤ 3, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 1 := bs4_3_0
theorem alls4 : ∀ k ≤ 3, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 1 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 11 := block_range (n:=11) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 11 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 10 := bs5_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 1 := bs5_5_0
theorem alls5 : ∀ k ≤ 5, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_2 i (by omega) hi
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 26 := block_range (n:=26) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 26 := bgb_2_0
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
theorem bgb_3_160 : Interval gbAtlas 3 160 24 := block_range (n:=24) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 184 := (concat (concat bgb_3_0 (concat bgb_3_32 bgb_3_64)) (concat bgb_3_96 (concat bgb_3_128 bgb_3_160)))
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
theorem bgb_4_1440 : Interval gbAtlas 4 1440 21 := block_range (n:=21) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 1461 := (concat (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 (concat bgb_4_96 bgb_4_128))) (concat (concat bgb_4_160 (concat bgb_4_192 bgb_4_224)) (concat bgb_4_256 (concat bgb_4_288 bgb_4_320)))) (concat (concat (concat bgb_4_352 (concat bgb_4_384 bgb_4_416)) (concat bgb_4_448 (concat bgb_4_480 bgb_4_512))) (concat (concat bgb_4_544 (concat bgb_4_576 bgb_4_608)) (concat bgb_4_640 (concat bgb_4_672 bgb_4_704))))) (concat (concat (concat (concat bgb_4_736 bgb_4_768) (concat bgb_4_800 (concat bgb_4_832 bgb_4_864))) (concat (concat bgb_4_896 (concat bgb_4_928 bgb_4_960)) (concat bgb_4_992 (concat bgb_4_1024 bgb_4_1056)))) (concat (concat (concat bgb_4_1088 (concat bgb_4_1120 bgb_4_1152)) (concat bgb_4_1184 (concat bgb_4_1216 bgb_4_1248))) (concat (concat bgb_4_1280 (concat bgb_4_1312 bgb_4_1344)) (concat bgb_4_1376 (concat bgb_4_1408 bgb_4_1440))))))
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
theorem bgb_5_5280 : Interval gbAtlas 5 5280 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 5308 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 bgb_5_192) (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)))) (concat (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 (concat bgb_5_416 bgb_5_448))) (concat (concat bgb_5_480 bgb_5_512) (concat bgb_5_544 (concat bgb_5_576 bgb_5_608))))) (concat (concat (concat (concat bgb_5_640 bgb_5_672) (concat bgb_5_704 (concat bgb_5_736 bgb_5_768))) (concat (concat bgb_5_800 bgb_5_832) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)))) (concat (concat (concat bgb_5_960 bgb_5_992) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088))) (concat (concat bgb_5_1120 (concat bgb_5_1152 bgb_5_1184)) (concat bgb_5_1216 (concat bgb_5_1248 bgb_5_1280)))))) (concat (concat (concat (concat (concat bgb_5_1312 bgb_5_1344) (concat bgb_5_1376 (concat bgb_5_1408 bgb_5_1440))) (concat (concat bgb_5_1472 bgb_5_1504) (concat bgb_5_1536 (concat bgb_5_1568 bgb_5_1600)))) (concat (concat (concat bgb_5_1632 bgb_5_1664) (concat bgb_5_1696 (concat bgb_5_1728 bgb_5_1760))) (concat (concat bgb_5_1792 (concat bgb_5_1824 bgb_5_1856)) (concat bgb_5_1888 (concat bgb_5_1920 bgb_5_1952))))) (concat (concat (concat (concat bgb_5_1984 bgb_5_2016) (concat bgb_5_2048 (concat bgb_5_2080 bgb_5_2112))) (concat (concat bgb_5_2144 bgb_5_2176) (concat bgb_5_2208 (concat bgb_5_2240 bgb_5_2272)))) (concat (concat (concat bgb_5_2304 bgb_5_2336) (concat bgb_5_2368 (concat bgb_5_2400 bgb_5_2432))) (concat (concat bgb_5_2464 (concat bgb_5_2496 bgb_5_2528)) (concat bgb_5_2560 (concat bgb_5_2592 bgb_5_2624))))))) (concat (concat (concat (concat (concat (concat bgb_5_2656 bgb_5_2688) (concat bgb_5_2720 (concat bgb_5_2752 bgb_5_2784))) (concat (concat bgb_5_2816 bgb_5_2848) (concat bgb_5_2880 (concat bgb_5_2912 bgb_5_2944)))) (concat (concat (concat bgb_5_2976 bgb_5_3008) (concat bgb_5_3040 (concat bgb_5_3072 bgb_5_3104))) (concat (concat bgb_5_3136 bgb_5_3168) (concat bgb_5_3200 (concat bgb_5_3232 bgb_5_3264))))) (concat (concat (concat (concat bgb_5_3296 bgb_5_3328) (concat bgb_5_3360 (concat bgb_5_3392 bgb_5_3424))) (concat (concat bgb_5_3456 bgb_5_3488) (concat bgb_5_3520 (concat bgb_5_3552 bgb_5_3584)))) (concat (concat (concat bgb_5_3616 bgb_5_3648) (concat bgb_5_3680 (concat bgb_5_3712 bgb_5_3744))) (concat (concat bgb_5_3776 (concat bgb_5_3808 bgb_5_3840)) (concat bgb_5_3872 (concat bgb_5_3904 bgb_5_3936)))))) (concat (concat (concat (concat (concat bgb_5_3968 bgb_5_4000) (concat bgb_5_4032 (concat bgb_5_4064 bgb_5_4096))) (concat (concat bgb_5_4128 bgb_5_4160) (concat bgb_5_4192 (concat bgb_5_4224 bgb_5_4256)))) (concat (concat (concat bgb_5_4288 bgb_5_4320) (concat bgb_5_4352 (concat bgb_5_4384 bgb_5_4416))) (concat (concat bgb_5_4448 (concat bgb_5_4480 bgb_5_4512)) (concat bgb_5_4544 (concat bgb_5_4576 bgb_5_4608))))) (concat (concat (concat (concat bgb_5_4640 bgb_5_4672) (concat bgb_5_4704 (concat bgb_5_4736 bgb_5_4768))) (concat (concat bgb_5_4800 bgb_5_4832) (concat bgb_5_4864 (concat bgb_5_4896 bgb_5_4928)))) (concat (concat (concat bgb_5_4960 bgb_5_4992) (concat bgb_5_5024 (concat bgb_5_5056 bgb_5_5088))) (concat (concat bgb_5_5120 (concat bgb_5_5152 bgb_5_5184)) (concat bgb_5_5216 (concat bgb_5_5248 bgb_5_5280))))))))
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
theorem bgb_6_2176 : Interval gbAtlas 6 2176 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2190 := (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224))) (concat (concat (concat bgb_6_256 bgb_6_288) (concat bgb_6_320 bgb_6_352)) (concat (concat bgb_6_384 bgb_6_416) (concat bgb_6_448 (concat bgb_6_480 bgb_6_512))))) (concat (concat (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640)) (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 bgb_6_768))) (concat (concat (concat bgb_6_800 bgb_6_832) (concat bgb_6_864 bgb_6_896)) (concat (concat bgb_6_928 bgb_6_960) (concat bgb_6_992 (concat bgb_6_1024 bgb_6_1056)))))) (concat (concat (concat (concat (concat bgb_6_1088 bgb_6_1120) (concat bgb_6_1152 bgb_6_1184)) (concat (concat bgb_6_1216 bgb_6_1248) (concat bgb_6_1280 bgb_6_1312))) (concat (concat (concat bgb_6_1344 bgb_6_1376) (concat bgb_6_1408 bgb_6_1440)) (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 (concat bgb_6_1568 bgb_6_1600))))) (concat (concat (concat (concat bgb_6_1632 bgb_6_1664) (concat bgb_6_1696 bgb_6_1728)) (concat (concat bgb_6_1760 bgb_6_1792) (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888)))) (concat (concat (concat bgb_6_1920 bgb_6_1952) (concat bgb_6_1984 bgb_6_2016)) (concat (concat bgb_6_2048 bgb_6_2080) (concat bgb_6_2112 (concat bgb_6_2144 bgb_6_2176)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_32 : Interval gbAtlas 7 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_64 : Interval gbAtlas 7 64 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 74 := (concat bgb_7_0 (concat bgb_7_32 bgb_7_64))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 28, 30),(inputs.getD 2 zero, 26, 30),(inputs.getD 3 zero, 22, 30),(inputs.getD 4 zero, 14, 30)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 2 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 2 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19),(inputs.getD 1 zero, 17, 19),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 4 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19),(inputs.getD 1 zero, 17, 19),(inputs.getD 2 zero, 35, 39),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 7, 39)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 4 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 37, 39),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 5 zero, 7, 39)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 6 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 17, 19),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 17, 19),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 7, 39)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xe888a080e888a000e888a080e888a000e888a080e888a000e888a080e888a000e888a080e888a000e888a080e888a000e888a080e888a000e888a080e888a000
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 9 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 50 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) (SBf 2) :=
    slice_correct (ms:=fixRows 44 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (3901268096 * 2 ^ 32 + 3901267968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_15135.Model.Repr at out
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

def mono : List Gate := [⟨.and,[2,5]⟩,⟨.and,[1,4]⟩,⟨.and,[1,6]⟩,⟨.and,[2,3]⟩,⟨.and,[7,9]⟩,⟨.and,[0,7]⟩,⟨.or,[10,11]⟩,⟨.or,[8,9]⟩,⟨.and,[0,13]⟩,⟨.or,[12,14]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,15⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 9) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3901268096 * 2 ^ 32 + 3901267968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3901268096 * 2 ^ 32 + 3901267968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_15135

open PEqualNP.Outside.L_meta_15135 in
theorem PEqualNP.Outside.L_meta_15135 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3901268096 * 2 ^ 32 + 3901267968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3901268096 * 2 ^ 32 + 3901267968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
