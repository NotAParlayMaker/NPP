import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_12829.Model
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


end PEqualNP.Outside.L_meta_12829.Model

namespace PEqualNP.Outside.L_meta_12829
open PEqualNP.Outside.L_meta_12829.Model
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

end PEqualNP.Outside.L_meta_12829

namespace PEqualNP.Outside.L_meta_12829
open PEqualNP.Outside.L_meta_12829.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x280123815400125939a0e98a20369000c1a0001e00840004608a83321149f100059700600001e38e80008898022188014a0000450000430820c244bff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x41fe20083f440107f48020f690041f920083fea9885fd5310ff2a6217e54c437ca9884f95310feaa6217d54c437aa9884f55310fe2a6217c54c43fea7885fd4f10ff29e217e53c43faa7885f54f10fe29e217c53c43fe87887f90f10fea1e21fc43c43fea5885fd4b10ff296217e52c43faa5885f54b10fe296217c52c43fe85887f90b10fea1621fc42c43fe65887f8cb10fe99621fc32c43fe83887f90710fea0e21fc41c43fe63887f8c710fe98e21fc31c43fe43887f88710fb10e21fd21c43ea43887f08710ffa0621fe40c437c81887f50310fe20621bc40c43fe61887f8c310fe98621fc30c43fe41887f88310fe90621fc20c43fea9085fd5210ff2a4217e54843faa9085f55210fe2a4217c54843fea7085fd4e10ff29c217e53843faa7085f54e10fe29c217c53843fe87087f90e10fea1c21fc43843fea5085fd4a10ff294217e52843faa5085f54a10fe294217c52843fe85087f90a10fea1421fc42843fe65087f8ca10fe99421fc32842faa3087fd0610ff20c21fd41843f883087fcc610fb98c21fe31843fa63087f0c610fa18c21ff21843ee43087f88610fe90c21fc21843e843085f94210ffa0421fe408437c81087f50210fe20421bc40843fe61087f8c210fe98421fc30843fe41087f88210fe90421fc20843fe21087dc4210fd88421ff54442fea8886fd51109faa221fe54442fca8887f55110beaa221fc54442f8a8886f151109e2a221ff53442fea68877d4d10afa9a21fe53442fca6887f54d10bea9a21fc53442f8a6887714d10ae29a21ff43443fc86887f50d10fe21a21ff52442fea4887bd4910b7a9221fe52442fca4887f54910bea9221fc52442f8a4887b14910b629221ff42443fc84887f50910fe21221ff32443fc64887f4c910fe19221ff41443fc82887f50510fe20a21ff31443fc62887f4c510fe18a21ff21443fc42887d88510fe90a21f521443f842887fd0110ff20221be40443fa80887f10110de20221ff30443fc60887f4c110fe18221ff20443fc40887f48110fe10221ff10443f620887f84110fb08221ff54042fea8087f95010bf2a021fd54042faa8087f15010be2a021ff53042fea6087f94c10bf29821fd53042faa6087f14c10be29821ff43043fc86087f50c10fe21821ff52042fea4087f94810bf29021ee52042dca4087f54810bea9021ed52042daa4087f14810be29021ff42043fc84087f50810fe21021ff32043fc64087f4c810fe190217e51043fe82087f90410fea0821fc41043fe62087dcc410ff18821fd31043f862087d0c410ff90821f721043fc42087f48410fe10821f421042fca0087fd0010ff20021be40043fa80087f10010de20021ff30043fc60087f4c010fe18021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0xe510c3faa2185f54430fe28861ff410c3fc82187f50430fe20861ff310c3fc6218778c430fe98861fc310c3b862187fc8430ff10861fd210c3f842185f94030ffa0061fb400c3fc80186f90030fea0061fc400c37880187e10030dc20061ff300c3be60187f8c030fd18061fd300c3ba60187e4c030ffaa6417f54c83fca9905f95320df2a6413e54c83faa9905f55320deaa6413d54c83f8a9905f15320ffa9e417f53c83fca7905f94f20fea9e417d53c83f8a7905f14f20ffa1e41fe43c83fa87907f10f20ffa1641fe42c83fa85907f10b20ff99641fe32c83fa65907f0cb20ffa8e41fe51c82fca3907f54720bea8e41fc51c83fe83907f90720fea0e41fc41c83fe63907f8c720fe98e41fc31c83fe43907bc8720ff10e41fd21c83da43907f08720ffa0641fe40c837c81907f50320fe20641bc40c83fe61907f8c320fe98641fc30c83fea9105fd5220ff2a4417e54883faa9105f55220fe2a4417c54883fea7105fd4e20ff29c417e53883faa7105f54e20fe29c417c53883fe87107f90e20fea1c41fc43882faa5107fd0a20ff21441fd42883f885107fcca20f799441fe32883fa65107f0ca20f619441ff51883fca3105f94620fea8c417d51883f8a3107fd0620ff20c41fd41883f883107fcc620ff18c41fd31883f863107fc8620ff10c41ee21883fa43107f08620f610c417e50883fe81107f90220df20441fd40883f881106f10220ff98441fe30883fa61107f0c220ff90441ef20883f641107fd5120bfaa241bf544827ea8907f95120bf2a241fd54482faa8907f15120be2a241bc5448278a8907fd4d20bfa9a41df53482bea6907f94d20bf29a41fd53482faa6907f14d20be29a41dc53482b8a6907fd0d20ff21a41fd43483f886907fd0920ff21241fd42483f884907fcc920ff19241fd32483f864907fd4520bfa8a41f751482eea2907f94520fea8a41fc51482f8a2907d14520ba28a41ff41483fc82907f50520fe20a41ff31483fc62907f4c520fe18a41ff21483de42907f88520fe90a41ed21483f842907fd0120ff20241be40483fa80907f10120de20241ff30483fc60907f4c120fe18241ff20483f640907f88120f710241ff54082fea8107f95020bf2a041fd54082faa8107f15020be2a041ff53082fea6107f94c20bf29841fd53082faa6107f14c20be29841ff43083fc86107f50c20fe218417e52083fe84107f90820fea1041fc42083fe64107bcc820ff19041fd32083f864107b0c820ffa8841fe51082fca2107d94420bb28841fd51082faa2107d54420baa8841fc51083fe82107f90420fea0841fc41083fe62107f8c420fe98841fc31083fe42107f88420f710841fd21083f842107b08420bf28041ff40083fc80106f90020fea0041fc400837880107fcc020ff18041fd30083f860107fc8020f790
  | 2 => 0x2fca8207fd4c40ff298817e53103faa6205f54c40fe29881ff431037e86207f90c40df21881fd431037a86207f10c40de21881ff52103fca4205f94840fea90817d52103f8a4207fd0840dfa1081fe421037c84207f50840dea1081fc421037884207fcc840ff19081fd32103f864207fd4440ff288817e51103faa2205f54440fe28881ff411037e82207f90440df20881fd411037a82207f10440de20881ff31103fc62207f4c440fe18881ff21103fc42207f48440fe108817e50103fe80206fd0040ff20081fa40103fa80206f50040fca0081bf531037ca6206f54c40de29881bf521037ca4206f54840de29081bf321037c64206f4c840de19081bf511037ca2206f54440de28881bf311037c62206f4c440de18881bf211037c42206f48440de10881be501027ca0206e94040ffaa6617f54cc3fca9985f95330df2a6613e54cc3faa9985f55330deaa6613d54cc3f8a9985f15330ffa1e61fe43cc3fa87987f10f30ffa9661fe52cc2fca5987f54b30bea9661fc52cc3fe85987f90b30fea1661fc42cc3fe65987f8cb30fe99661fc32cc3fea3987f94730bf28e61fd51cc2faa3987f14730ffa0e61fe41cc3fa83987f10730ff98e61fe31cc3fa63987f0c730ff90e61fe21cc3fa43987f08730ffa0661fb40cc3fc81986f90330fea0661fc40cc37881987e10330dc20661ff548c2fea9187f95230bf2a461fd548c2faa9187f15230be2a4617d538c3fe87187f90e30fea1c61fc438c3fea5187f94a30bf29461fd528c2faa5187f14a30ffa1461fe428c3fa85187f10a30ff99461fe328c3bc65187f4ca30fe19461dc328c3fea3187f94630bf28c61fd518c2faa3187f14630ffa0c61fe418c3fa83187f10630ff98c61fe318c3bc63187f4c630fe18c61dc318c3fe43187f88630fe90c61fc218c2fca1187fd0230ff20461be408c3fa81187f10230de20461ff308c3be61187ecc230ffaa2617f544c37ea8984fd5130ff2a2617e544c3faa8985f55130fe2a2617c544c378a8984f15130ffa1a61fe434c3fa86987f10d30ffa92617f524c3dea4985bd4930ff29261fd524c3f8a4985f14930f6292616c524c3fe84987f90930fea1261fc424c3fe64987f8c930fe99261fc324c3fea2985fd4530fba8a6177514c3fca2987f54530fe28a617c514c3e8a2985d14530ffa0a61fe414c3fa82987f10530ff98a61fe314c3fa62987f0c530ff90a61fe214c3fa42987f08530ffa0261fe404c37c80987f50130fe20261bc404c3fe60987ecc130ff18261de304c3fea8185fd5030ff2a0617e540c3faa8185f55030fe2a0617c540c2fca6187fd0c30ff21861fd430c3f886187fd4830ff290617e520c3faa4185f54830fe29061ff420c3fc84187f50830fe21061ff320c3fc6418778c830fe99061fc320c3b864187fd4430ff288617
  | 3 => 0x8710df54a21ffa1443fe42887fa8510ff10a21ff99443fe32887fa6510ff0ca21bf28c43ff41887fc8310ff50621fe20c43ff31887ee6310ff8c621fe98c43fc31887e86310ffc8621f790c43f721887fea110ff94221bf28443fd50886faa110ff14221ffaa2437f54487fca890df95121feaa2437d54487f8a890df15121ffa9a437f53487fca690df94d21fea9a437d53487f8a690df14d21ffa1a43fe43487fa8690ff10d21ffa1243fe42487fa8490ff10921ff99243ef32487fc6490ff4c921fe19243ec32487fe8290ff90521fea0a43fc41487fe6290fdcc521ff18a43fd31487f86290fd0c521ff90a43f721487fc4290fb88521ffa82437f50487fca090ff54121fe282437c50487fea810dfd5021ff2a0437e54087faa810df55021fe2a0437c54087fea610dfd4c21ff298437e53087faa610df54c21fe298437c53087fe8610ff90c21fea1843fc43086fca410ffd0821ff21043fd42087f88410ffcc821ff19043fd32087f86410df94421ffa0843fe41087fa8210ff10421ff98843fe31087fa6210ff0c421ff90843ef21087fc4210fd88421fe90843ed21087ea4210f948421ffa8043fe50086fca010ff54021bea8043fc50087fea7a07f94f40bf29e81fd53d02faa7a07f14f40ffa1e81fe43d03fa87a07f10f40ffa9681fe52d02fca5a07f54b40bea9681fc52d03fe85a07f90b40fea1681fc42d03fe65a07f8cb40fe99681fc32d03fea3a07f94740bf28e81fd51d02faa3a07f14740ffa0e81fe41d03fa83a07f10740ff98e81fe31d03fa63a07f0c740ff90e81fe21d03fa43a07f08740beaa481ff53903fca7205f94e40fea9c817d53903f8a7207fd0e40dfa1c81fe439037c87207f50e40dea1c81fc439037887207fd4a40ff294817e52903faa5205f54a40fe29481ff429037e85207f90a40df21481fd429037a85207f10a40de21481ff32903fc65207f4ca40fe19481ff51903fca3205f94640fea8c817d51903f8a3207fd0640dfa0c81fe419037c83207f50640dea0c81fc419037883207fcc640ff18c81fd31903f863207fc8640ff10c81fd21903f843205f94240ffa0481bf40903f681206fd4e40df29c81bd5390378a7206fd4a40df29481bd5290378a5206fcca40df19481bd329037865206fd4640df28c81bd5190378a3206fcc640df18c81bd319037863206fc8640df10c81bd219037843204f94240ffa9a817f53503fca6a07f54d40fe29a817c53503fe86a07f90d40fea1a81fc43503fea4a05fd4940ff29281fd52503f8a4a05f14940ffa1281fe42503fa84a07f10940ff99281fe32503fa64a07f0c940ffa8a817f51503fca2a07f54540fe28a817c51503fe82a07f90540fea0a81fc41503fe62a07f8c540fe98a81fc31503fe42a07f88540fe90a81fc21503fe80a07ed0140ff20281be405
  | 4 => 0xff50d41dea1a83fc43507fea4a0dfd4941ff29283fd52507f8a4a0df14941ffa1283fe42507fa84a0ff10941ff99283fe32507fa64a0ff0c941ffa0a83f741507fc82a0ef90541ffa82837f50507fca0a0ff54141fe282837c50506fca820ffd4c41ff298837e53107faa620df54c41fe29883ff43107fc8620ff50c41fe21883ff52107fca420df94841fea90837d52107f8a420ffd0841ff21083fd42107f88420ffcc841ff19083fd32107f86420df94441ffa0883bf41107fc8220fd90441fea0883bd41107ea8220ffd4041ff280837e50107faa020df54041fe28083ff54cc6fea998ff95331bf2a663fd54cc6faa998ff15331be2a663ff43cc7fc8798ff50f31fe21e63ff52cc7fca598df94b31fea96637d52cc7f8a598ffd0b31ff21663fd42cc7f88598ffccb31ff19663fd32cc7f86598ffd0731fba0e63fe41cc7fa8398ff10731fa20e63ff50cc7fca198df94331fea86637d50cc7f8a198ffd5231bfaa463fe548c6fca918ff55231beaa463fc548c6f8a918df54e31ffa1c63fe438c7fa8718ff10e31ffa9463fe528c6fca518fb94a31b729463fd528c6faa518fb54a31b6a9463fc528c7fe8518ff90a31fea1463fc428c7fe6518ff8ca31fe99463fc328c6fca318ffd0631ff20c63fd418c7f88318ffcc631ef98c63f7318c7fea118ff94231bf28463fd508c6faa118ff14231ffaa2637f544c7fca898df95131feaa2637d544c7f8a898df15131ffa1a63fe434c7fa8698ff10d31ffa92637f524c7fca498ff54931fe292637c524c7fe8498ff90931fea1263fc424c7fe6498ff8c931fe99263fc324c7fe8298ff90531fea0a63fc414c7fe6298fdcc531ff18a63de314c7fea098dfd4131ff28263fd504c7f8a098df14131ffaa0637f540c7fca818df95031df2a0633e540c7faa818df55031deaa0633d540c7f8a818df15031bf29863ff430c7fc8618ff50c31fe21863ff520c7fca418df94831fea90637d520c7f8a418ffd0831ff21063fd420c7f88418ffcc831ff19063fd320c7f86418df94431ffa0863f7410c7fc8218ff50431fe20863f4410c7fe6218f7cc431ff18863f6310c7fa6218f74c431fa98863ff500c7fca018df94031fea80637d500c7f8a018ffd5321bfaa643fe54c86fca990ff55321beaa643fc54c86f8a990ffd4f21bfa9e43fe53c86fca790ff54f21bea9e43fc53c86f8a790ffd0f21ff21e43fd43c87f88790ffd0b21ff21643fd42c87f88590ffccb21f799643fe32c87fa6590ff0cb21f619643ff41c87fc8390ff50721fe20e43ff31c87fc6390ff4c721fe18e43ff50c87fca190df94321fea86437d50c87f8a190ffd5221bfaa443fe54886fca910ff55221beaa443fc54886f8a910ffd4e21bfa9c43fe53886fca710ff54e21bea9c43fc53886f8a710ffd0e21ff21c43fd43887f8
  | 5 => 0x242ffa9c85fe5390afca7217f54e42bea9c85fc5390bfe87217f90e42fea1c85fc4390afca5217fd0a42dfa1485ef4290bfea3217f94642bf28c85fd5190afaa3217f14642ffa8485fe5090afca1217f54242bea8485fc5090bfea6a15fd4d42ff29a85fd5350bf8a6a15f14d42ffa1a85bf4350bfc86a17f50d42dea1a85fc4350bfe84a17bd0942ff21285be4250bfea2a15fd4542ff28a85fd5150bf8a2a15f14542ffa82857f5050bfca0a17f54142fe282857c5050afca8217fd4c42ff298857e5310bfaa6215f54c42fe29885ff4310bfc86217f50c42fe218857e5210bfe84216fd0842ff21085ee4210bfa84216f50842f6a1085ff5110bfca2215f94442fea88857d5110bf8a2217fd4042ff280857e5010bfaa0215f54042fe28085ff54ccafea9997f95332bf2a665fd54ccafaa9997f15332be2a665ff43ccbfc87997f50f32fe21e65ff42ccbde85997f90b32fea1665fc42ccbd885997fd4732ff28e657e51ccbfaa3995f54732fe28e65ff50ccbfca1995f94332fea86657d50ccbf8a1997fd5232bfaa465fe548cafca9197f55232beaa465fc548caf8a9195f54e32ffa1c65fe438cbfa87197f10e32bf29465ff428cbfc85197f50a32fe21465ff328cbbe65197bcca32ffa8c65fe518cafca3197d94632bb28c65fd518cafaa3197d54632baa8c65fc518cbfea1197f94232bf28465fd508cafaa1197f14232ffaa2657f544cbfca8995f95132feaa2657d544cbf8a8995f15132ffa1a65fe434cbfa86997f10d32ffa1265fe424cbfa84997f10932ff99265ef324cbfc6499778c932ffa8a657f514cbfca2997f54532fe28a657c514cbfea0995fd4132ff28265fd504cbf8a0995f14132ffaa0657f540cbfca8195f95032df2a0653e540cbfaa8195f55032deaa0653d540cbf8a8195f15032bf29865ff430cbfc86197f50c32fe218657e520cbfe84197bd0832ff21065fd420cbf884197b10832ff99065df320cbfc64197b8c832fe99065dd320cbda64197fd4432ff288657e510cbfaa2195f54432fe28865ff500cbfca0195f94032fea80657d500cbf8a0197fd4f41ff29e837e53d07faa7a0df54f41fe29e83ff43d077e87a0ff90f41fea1e83bd43d07f887a0ffd4b41ff296837e52d07faa5a0df54b41fe29683ff42d07fc85a0ff50b41fe21683ff32d07fc65a0ff4cb41fe19683ff50d07fca1a0df94341fea86837d50d07f8a1a0df55241ffa9c83fe53906fca720ff54e41bea9c83fc53907fe8720ff90e41fea1c83fc43907fea520ff94a41bf29483fd52906faa520ff14a41ffa1483fe42907fa8520ff10a41ff99483fe32907fa6520ff0ca41bf28c83ff419077e8320fdd0641ffa8483fe50906fca120ff54241bea8483fc50907fea6a0dfd4d41ff29a83fd53507f8a6a0df14d41ffa1a83bf43507fc86a0
  | 6 => 0x4c00a00000001a00000202802800001200800001403601200e00200001600600001e01401a00401400400000000c00600000200000c00400600000200000205000200806c02c02200600002a00204000000201e00200000e01001400c00c00200400001000000600600004c00201200600601200800201000200400600803c02200200c00000203000201601000e00800000200600200a00000000c00403001400200600600c00402000000400002201c00000c00601000400a02e00800602200200000400800002a00400400400e00001c00201800e00201000e00601400000202600800000202e00200808800800000200000200600000001c00600200800e00000200c00200002802400a00200400202400000400400400a02000400e00c00000402200400000003000200201600200000000200a00e00401e00000200403000400e00000200200000001e00a00002000001200200800000600801c00200600600000600000200c00a01001a00601600000200400000401600200200600c00200400000000000a03600000400000200c01e00c00200200001800000001c00000601c00600600800800401400a00401200002200400e00200600200203c01000200800200200000200000000000800e00200400000a00002801400a00200800a00401c00800800400002800002600c00000a00000a02a00c00000000801000601800000600200000800200000001400a00e00200600e00600000201200200c01800001000200200000000401002c00000400800601801201200400402601000200600600000202e00000000000a002000010003ff52d0ffca5a1df94b43fea96877d52d0ff8a5a1ffd4743ff28e877e51d0ffaa3a1df54743fe28e87ff50d0ffca1a1df94343fea86877d50d0ff8a1a1df55243bf29c87ff4390f7e8721f7d0e43ffa9487fe5290efca521ff54a43bea9487fc5290ffea321ff94643bf28c87fd5190efaa321ff14643ffa8487fe5090efca121ff54243bea8487fc5090ffe86a1f7d0d43ff21a87be4350ffea4a1dfd4943f7a92876f5250ffca4a1ff54943fe292877c5250fd8a4a1db14943ffa8a877f5150feea2a1ddd4543ff28a87fd5150ff8a2a1df14543fa28a87745150ffea0a1dfd4143fda82877b5050ffca0a1ff54143fe282877c5050ff0a0a1de14143bf2a0877e5310ffe8621efd0c43ff21887de4310ffa8621ef50c43eea1887ff5210ffca421df94843fea90877d5210ff8a421ffd4443ff288877e5110ffaa221df54443fe28887ff5010ffca021df94043fea80877d5010ff8a021ffd4f42ff29e857e53d0bfaa7a15f54f42fe29e85ff43d0b7e87a17f90f42fea1e85bd43d0bf887a17fd4742ff28e857e51d0bfaa3a15f54742fe28e85ff50d0bfca1a15f94342fea86857d50d0bf8a1a15f55
  | 7 => 0xa400064144c0012fc634c64b60739cf40447281ed14555ca3c2dcfe82e0000000d15b440008d8000e2400107c000c4c0000019d0bbdb24000364e982a94240017dcf601e844d9cc2b1ad13f8ebde1dbbdc5d1312ad4b12080003acee9b789fc254cf8000000dacb3c001ac9860760619af800000000000198d259b4dd6000174c000e65279ce8001a6c23c001831690d246c4db1c194700003e88ac700b0c3b93580000b0c080003280019b0c8458000065d5cc654000805a880000013b4da40017f4001528b140017fd8d147c000000e088c03c1a617b04c8000000001d246996b93d8eb468cef86b59280000005cc31c8740007219512e00012dc000000a0c96850800025cac1d6400018ceb937c89cf0d659a50621b61bac001de41884d4a44f580a4000c1196d2289ecd6d3fc0014b40010e40006dc4dc000a78010000f941a55b14440001fd43026cdfcfa1720d84180338001be8b94001475d010a0f3c084081b1dc6441cd44eec31184d149c0cec84301b5e11c395f8a40001ab9819294d0ce6c000000be47c98a88a821d22c00164c0009d492410c8e5174f01429ba0e91b8d42c2ec0345c40000000002f001400000082c0000195b49bc0006747e9b40d7d7d90a4e68459b21b2c199289a8139c56cca5b84671e089dcb896c969800000000162000000041181c001bd8000000dd10b82a1574001251c6c0019f9d3cc7c280284e800012816b1014000001e48561785d54b4dd480019f000000000001c000000c959383f40000000fc000000001c500013a1421110651114214001b495dcf08fb5559c25330041c20a04f4055c0eccb170c9f8000000001931c2c000b388a59e4c2008c288000734ccda083b16f88e1d1928c1a11d0dbc42dda13c9dc409c5d9a7151000c01200600000600200200600000c00000000601600600400600a00200000000a00e00000c00000001600000200202600000000e00600200802002002a01600200800200a00000400400600000600800202000000000800000000801800000a03000800801c01e00200400600800000000400801600000000400000000000200400800001c00000c00805000200200e00a03e00002000600400200000a07000800400000000600000002201a00600200a02002c00800800000600000000001000000000204a00000600a00000400000000000e01a00a01000001400000000800001005000e00600400001a00000602000400400e00000000a01200000000602600200000000400202c02a00404e00000600200200800600001000e00000001c00000a00e01400200200a00000600000800401200200e00200a00207c00001400000000000400002a00000a00000000000600000000a00000800200000600401800600000202000600000c002004012000004002000002036
  | 8 => 0xc000001999670468538b2dbfc5305783d40000000016383d9d90afc000a841500005a5455285be423800000067c000b49388001029cfd881320b202d44a03f10783cd451dc8370dc42d88b96c090950c0001f8e29108001aa0000488d198c8b580e40f4278ea1ba5038e9d1011c1494401368341aa8c04000680000000001c844f9c7800098c00012cd60fec0010816a0078000a992cc83179489400000132dd95a785104b400073c0012309d0cbc001354000000b344e800197dcf11fc35096ce207fcfc09b03e4d55855dcc8fc00127cd75bdc83920d5e05210204850ad6855010c0ad9b55b91589c019880017e00000000000000002e5e5c00125d064000aad2c8d91119838001599764da8809088000001adc0014e17491f916de15bb4e414e4bc098400175c9e40015d0000504811941800450ca18fc0015d5ad5da9798001060a20a9c1795853cc8d493c6e40acfdc0005d10a8d68114e859953a43787700a8d34bb0b413707d4da0f4c0017351203ed6d09106a9a5c0016d4001bf1e201d5410f6db10cdd381968000000a5843c001a58e10adcfac000980319b00584001a28315e44d48a50000230f14bc9344e48000000fe40013156547c4d31d2d714885dac0000003953b800063812936daa56510bd5942048d157ccc951850c0000000c0000000000b457b40001d8d714a8df8000ef0029cc0b8dc41e64c15ab424cb9156595436077d1b8d055fd5300014ec00000041903d8505dc00182533968cb68c280018f4000000000414000000000c0d468000ac52100000014f800087890515979d72400000189c5fc000d09a10001480c38a5c2952548ec0e959d23ca54d000000000017e5804000768b7167508d4e8a30569a24000844130e0552dd215ec375d15a007e424533c05da840585650cc000001de97ac71c444000000ecd709c70e88a08dc9c04c1c000000001b6c46daec001844dc000178034514c00000080079c000a109f01543a5754cec858ba1acd4ac00177c5282c82c40000019340000006a19a0ee53b1384e59cec2c192cf9d1d46bc000b7400112db0d30c000000000000000000d40cc4591324000000c994019480004a400146dccd7c59856f41b92b0000a69895afdbf50488e9be07a1871b316f18a0a7048c9204c08dd0fc054000000b295bc0003d01185a92c400000172c0000000019e8c24a8c97c00000000080c0018e548de1945889015c9a5695ba87b9a4c0000000018680f000000000084c0000000014fda54000df000000000153d89800093037c03000017c870dcc2253512991a46ed2a10d8fe1d29a751a0001ab10740004284f4974098e2c00034ceb0ea460d034074a74e8c0000700000000009a8000000a81c9c000a6c848649169404624f1d8d8d5c8c568003d8e18e829cc686d5970ca8601134000f
  | 9 => 0x498cb9c1d810000a4de4c550139ae41a865800066166c00180c00071956d24c9d80b800000165c00062d53943c9c8000001438b18c19c8dd50000001a0c0000000012603c40015c8fb06b8000001919011a68d953944940008f9a99cbcbf0228ae4164e75391de0828478b981483249485bd7a40008b12d41e469c76d8cc421990000000000001334a186f4deccfd66084000081c6e1cd9300861d99e41db8000914000000c8c001e2c7980004e19bdb04000000000f75c14001b9c91c0005b56a9b188516196d80011c41f0000ee1b75cb452cf8cb9ccd94a1cf900414daf4534be0570000c79e3442478c00110510c000af00d5e60464024e3c0005e97ec000000171890dd8c55a20f2550820d290789c61128259ac1c48000aa0834d2d5041b1d9d0414d8001788000475790ec0000001ded7c800000193c668f8599c1bc24197917d0f913829036c0000000005740000952f09a00000000000010f0000001520690750000000000000898001858bd13dc0009f50b1241a194407bcde01ace35885ca4000fd80016fd87400000012085c6f98a50ed02400178c70911c30002d7316410d10f400063c6456e0001179945741759db026000163d5d8af5ad94a483c3a00012340017cd6052680015619acaa499591400004c0c93e400186c000ff8000000000001c694cd8dc2980004a9d0472d700a257111702715e4f50610001164b5c0018c4958000fc40004b9c111b50c4200404e30ce0000481a9d73d69c9c00002b93d0c01124f351e0a397d51e583cb1ddb44fca1ddf93a8945b154c1d69964c48ec5dd0f81d70c708f46946d090141871541c220168a490507a8880598cc03a9c90f286b11bdc09d38e4dc88759434000cf51b0000000ab1aac87c524e60780d5101cad16014640015695f00007d98f18281c00003c8000bd99d9e38e44d8db50000000001c55da4bacd993bc0000013098b4a2c7f021800000176976049de3c8f176cc74e707544393ed1ac4c400000135dd6c00160dd7400000000000115400014587c8ccd9c0d8000000000000ce8001dbc0011514b89195244adc292249c40019dc4e400000153519496161ce5400000109c90d7e8264d4dc30001cb9d116dcefcac95ad8d4988000ab50080000000011a8f19485218000ad527047c000000001bd0cd195c190f91834061c44194001ddc000ff18148bc001d7d1c96ad2e8050a34fbcaf9bb0e0cb64e1d19170495c07c000001c3c391bb9cd50e9215e5000151c0014140007cd40ced1490d299b40002cc0000005c00000019800008215a070c090f880017c0cf00000013980000011f1090000b6c0000009902e91f55c0001e252495c40012ece5d4bc2bc4407ec1248c9b718098ac5f957858c0008240bc785581cdc5b800138daf00002fc06d05ca880681dc0007b4c3
  | 10 => 0xe0ed97f09380007417f8f201ccb54ed45ac00162c00129db5d6652f80003fc0001c90d4001630b7c9544f0001ae060800000000092db88000408f68c6c000000001554000a288a00000cdc80e01d5d2a5ca80018ec9647d00013187a4234000f7d9d5b29379a05ca04d8b50f5db812a803800057d9741f5b647b03f833118c111e547dc554f9851cce5e6800000000000033dbf8000868815ae8275bc1a8c7c0d89bec00d571264000000000940e506e99c81e0000000b847497a854d9a47f4c60f480001580a0ffcdb534d82ddd8000888d3d94c0000018c02a40013d4688518615771a45188f71a3cc2c0019a80f80000000013040000017a0000001b3d9c4000000105649bc8ef571cd1d0705e0d81b7d4f430c1014d4000000000000001a7c0009cc000de8b096c56cc001910000000be838888c61c355340edc4352e40016e562400115c000001688185e040008656783b40005eda2d01800079400000175094cb8000027c000000001dc1d407900dc5f47e0001a34000000001878cd400000006445c0018b8000000000000000cacae840d668000f790016bcc45310000bc58b1328a00490001c58000000001c7c30588c000454000001b680004d11612d95449785c8c500018880000000012440011ed0300000000002d0001044000000bf954800147822cc915f45d4001b940000000000000012012b40005592b899c950becc35b35d4500c9706790580000000000006fc134998e78b78000588c5926cd20db991d1dc35c2119e0b3158da94bdc384a14fd1d34461dfd068aed775184fc8ba9609c4ce197bd614c89bc50b4ff4f043dc3e06c0021d89d811d8c316a41607640d0fb8a91d78470000000000000000854000779b393e00019580013c400000136400066c00155000149819c9ac0002096e904c00073145ca6028c000e38bcc00173918131c16c250dd5df0929cad374000000000549961a900005007f97280003345400016b46280016280001740012397d0a94000000ea8000fd5cc800102c000f55d84d64000001d8c0012f5460ab99c113c8195e84edb08000e7c1091e92c13e90c86f0368bb4a645e5920001a1da485a1a41b98000ddd2d06a439dcc49358400018200000000000000000014dd7445940005b0b059040000010ddd0d054eac00000119c000248001dd4f45610001a140006d94d1ce47752bd49c64c1d0001bcd4f0de4000000c409b40009e80e0000f64c5c00000000000004838c0013ac4b0001ac4c9c7ad90db5800185c001220abc00411d274001a38c81c99198b248b5a30705cd05f18490840080b4f2cae0000000684d38b0186536121d3491cc0013c00002b4001bd58f8bd46319fcaa8d58cb55a93f19ede0c7455a58bc1c40c50999f5a646c8665540711e58f100000015b909414032013c0014c49b8
  | 11 => 0x1d4dabc0014485149e074ca7d9242ad778bf4724349141c354085454c8fa9e2853d54d2042f886dcb0acc4bdc94000bfd901634d7808875cba400167de000000000000013f43099b8fcdd1d0e1719c744ccd11514449488e1432c359e30398269591df4e946cd6456edd59d0906cbb8df5d30380f380017b8f30b1059c6040003bd9086ac2f5c
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xa40043ae5290010cb94a400433d5290010eb54a400432d5290010cf14a40043b66190010ed586400433e5190010edcc640043b43190010edc8640043b42190010af982400433e50900109fd95400436e5250010db549400427f65100109f994400427d65100109f194400433e5410010cf550400436e5210010db54840042f66110010bd584400433f6510010cf994400433d6510010cf194400433f5310010cf94c400433d5310010cf14c400433f5210010cf94840043ae5210010cb948400433d5210010eb548400432d5210010cf14840043b66110010ed584400433e5110010edcc440043b43110010edc8440043b42110010af98040043ba6010010cf940400427d65cc010af99330042bd64cc010db94b300436d52cc010ee103300427f658c0109f596300435e538c010d754e300436e528c010db54a30042f6618c010bd58630043d4318c0109fd9530042bf644c010af19130042ef624c010bb189300436e524c010db54930042f7614c010bd185300427f650c0109f994300427d650c0109f194300435e530c010d754c300436e520c010db54830042f6610c010bd58430043d4310c010ee100300427d65c8010af99320042bd64c8010db94b200436d52c8010f9c8720043b840c80109fd96200427d6588010db94a200436d5288010bd98620042f56188010f9086200427f6548010afd9120042bc6448010b7d8d20042dc6348010db949200436d5248010bdd8520042f46148010f9c85200427f65080109f994200427d65080109f194200436e5208010db54820042f66108010bd58420043e42108010ee10020042be64c4010af593100436e52c4010db54b100437565c4010ed99310043b564c4010bd98f10042f463c4010bd98b10042f462c4010ddd4b10043e652c4010dd54b10043e552c4010d954b10043b640c4010ed103100436e5284010db54a10042f56184010dd94610043ba4084010ee10210042f96584010de59610042796584010fa94a10043e95284010be586100437a5184010fc94610043f33184010fc0c610043f32184010fc086100427f6544010afd9110042bc6444010b7d8d10042dc6344010bbd8910042ec6244010db949100436d5244010ee90110043b84044010bdd95100437765440109dd9510043b76444010ed19110043d76344010bd98d10042f46344010f518d10042d46344010f9d8910042f66244010bd18910043e46244010b918910043775244010f994910043755244010f954910043655244010bdd8110043765044010fcd0110043b64044010ed10110043f04044010ec10110042fb6544010ded95100427b6544010eed9110043b86444010f6d8d10043d86344010fad8910043e86244010fa94910043e95244010bed8510043f36144010de94510043f25144010fcd0510043f04144010
  | 1 => 0x427c6510810db948420436d52108109fd97320427e65cc8109f597320427c65cc810db94b320436d52cc810bd98732042f561cc8109fd96320427e658c8109f596320427c658c810db94a320436d528c810bd98632042f5618c8109fd95320427e654c8109f595320427c654c810db949320436d524c810bdd8532042f4614c810bed8132042f8604c8109fd94320427e650c8109f594320427c650c810af99032042bd640c810db948320436d520c8109f992510433e64944108f992510427d6494410cf592510423d64944109f98e510427d63944109f98a510427d62944109f597410433f54d0410cf153410436e52d0410db54b410427f65904109f596410433e5490410cf552410436e5290410db54a41042fa6090410be582410427f6550410cfd51410433c5450410db949410436d52504109fd94410427d6510410cf950410433d5410410db948410436d5210410be98041042f960104109f597310436e52cc410db54b31042f565cc410dd597310437654cc410dd153310437753cc410dd54f31042f662cc410ddd4b31043e652cc410dd54b31043e552cc410d954b31042f560cc4109fd96310427d658c410d794e310435d538c410bb98a31042ed628c410db94a310436d528c410bd98631042fa608c410be582310427f654c410db949310436d524c4109fd94310427d650c410af99031042bd640c410d794c310435d530c410db948310436d520c410f54c431042fa600c410be5803104375650c4109d59431043b6640c410ed5903104376540c410dd15031042f6630c410f598c3104377530c410f594c3104375530c410f554c31042f6620c410ddd4831043e6520c410dd54831043e5520c410d954831043f2600c410bd58031043f1600c4109f597210436e52c8410db54b21042f565c8410dd597210427565c8410bd98f21042f463c8410ddd4b21043e652c8410dd54b21043e552c8410d954b21043e732c8410f90cb21042f560c84109fd96210427d6588410db94a210436d5288410bd98621043765188410be98221042f960884109fd95210436e5248410db549210437651484109fd94210427d6508410db948210436d5208410f948421042fa6008410be580210437565084109d59421042f66308410bd18c21042f66208410f998821043775208410f994821043755208410f954821043655208410fc98021042f56008410fc580210427e64940109f592500427e63940109f58e500427e62940109f58a500427d6194010ddcc650043743194010ddc86500437421940109f597400436e52d0010db54b400427f65900109f596400433e5490010cf552400436e5290010db54a40042f66190010bd586400433f6590010cf996400433d6590010cf196400433f5390010cf94e400433d5390010cf14e400433f5290010cf94
  | 2 => 0x63150109758c540427e6215010db988540426e62150109f588540436d62150109b588540427e6115010dd984540427e6015010de98054042ee62d4c10bb58b530427e64d4c109f593530427e62d4c10db98b530426e62d4c109f58b530436d62d4c109b58b530427e61d4c10dd987530427e60d4c10de983530427d6594c10d7d4e530427e6494c109f592530427e6294c109f58a530427f6454c109f191530435f6354c109fd89530427c6254c109fd85530427d6154c10dd185530427f6054c109f58153042be6414c10af590530435d5314c10bb98853042ed6214c109f990530433e6414c108f990530427d6414c10cf590530423d6414c109f98c530435e6314c109f988530436e6214c109b988530427d6214c10db588530426d6214c109f98453043766114c109f980530437a6014c109fd97430427e65d0c109f597430427c65d0c10cf953430433d54d0c10bd98743042f561d0c109fd96430427e6590c109f596430427c6590c10d794e430435d5390c109fd95430427e6550c109f595430427c6550c10cf951430433d5450c10d794d430435d5350c10bbd8943042ec6250c10bdd8543042f46150c10bed8143042f86050c109fd94430427e6510c109f594430427c6510c109f993520427d64d48109f98f520427d63d48109f987520437661d48109f983520437a60d48109f596520436f52948109f992520427d64948109f98e520427d63948109b596520436f5494810db952520436d5494810db152520436f5394810db94e520436d5394810db14e52043e46194810dbd92520436e6494810db592520436c6494810dbd8e520436e6394810db58e520436c6394810dbd0e520436e4394810db50e520436c4394810db986520436c6194810db982520436c60948109fd91520427c64548109fd8d520427c6354810dbd89520427f61548109f585520437461548109fd81520427d6054810dbd95520436f5454810db951520436d5454810db151520436f5354810db94d520436d5354810db14d52043e46154810dbd91520436e6454810db591520436c6454810dbd8d520436e6354810db58d520436c6354810dbd0d520436e4354810db50d520436c4354810db985520436c6154810d9185520436e6054810db181520436c1054810bb988520436d52148109f990520427d64148109f98c520427d63148109f988520436e62148109b988520427e6114810dd984520427661148109f980520437a60148109fd97420427e65d08109f597420427c65d0810db94b420436d52d0810bd98742042f561d08109fd96420427e65908109f596420427c6590810db94a420436d52908109fd95420427e65508109f595420427c6550810db949420436d5250810bdd8542042f46150810bed8142042f860508109fd94420427e65108109f594420
  | 3 => 0x1109f595404427c6550110cfd51404433c5450110d7d4d404435c5350110dbd49404436c5250110bdd8540442f461501109f994404433f5410110cf950404433d5410110cf150404435f5310110d714c404436f5210110db14840442be6510110cf994404423e6510110cfd4c404439f5310110c7d4c404433e5310110cf54c404433c5310110e714c404431c5310110cfd4840443af5210110cbd48404433e5210110cf548404433c5210110eb148404432c5210110ed88440443b52110110af98040443ba60101109f99730442be64cc110af593304433f54cc110cf153304435f53cc110d714f304436f52cc110db14b30442f661cc110bd58730443b840cc1109f996304433f548c110cf152304435f538c110d714e304436f528c110db14a304427f654c1109f595304427c654c110afd9130442bc644c110cfd51304433c544c110d7d4d304435c534c110bbd8930442ec624c110dbd49304436c524c110bdd8530442f4614c1109f994304433f540c110cf150304435f530c110d714c304436f520c110db14830443b8400c1109f99720442be64c8110af593204433f54c8110cf153204435f53c8110d714f204436f52c8110db14b20442f661c8110bd58720443e521c81109f996204433f5488110cf152204435f5388110d714e204436f5288110db14a20443e62188110ee102204427f65481109f595204427c6548110afd9120442bc6448110cfd51204433c5448110b7d8d20442dc6348110d7d4d204435c5348110dbd49204436c5248110bdd8520442f46148110f948520443b840481109f994204433f5408110cf150204435f5308110d714c204436f5208110db14820442f66108110bd58420443e62108110af99310442bd64c4110cfd53104433c54c4110d7d4f104435c53c4110dbd4b104436c52c4110ee90310443b840c4110ee99310443b964c4110eed5310443b854c4110f6d4f10443d853c4110fad4b10443e852c4110fc88710443f121c4110cfd52104433c5484110d7d4e104435c5384110dbd4a104436c5284110edd5210443b45484110f5d4e10443765384110dd14e10443d45384110d514e10442f76284110bd58a10443e75284110dd94a10443745284110f914a10443645284110fcd4210443b64084110ed10210442ee62d5010bb58b540427e63d50109f58f540427e62d5010db98b540426e62d50109f58b540436d62d50109b58b540427e61d5010dd987540427e60d5010de983540427d6595010cfd52540427e63950109f58e540427e62950109f58a540433f64550109fd8d540427c63550109fd89540427c62550109fd85540427d61550109fd81540427d6055010cf55054042de6315010b758c54042ee6215010bb588540427e6415010cf990540427e6315010d798c540425e63150109f58c540435d
  | 4 => 0xf596324427c658c910cfd52324433c548c910d7d4e324435c538c910dbd4a324436c528c910bd98632442f5618c9109fd95324427e654c9109f595324427c654c910cfd51324433c544c910d7d4d324435c534c910dbd49324436c524c9109fd94324427e650c9109f594324427c650c910af99032442bd640c910cfd50324433c540c910d7d4c324435c530c910dbd48324436c520c910bd98432442f5610c910be98032442f9600c9109f997414433f54d0510cf153414435f53d0510d714f414436f52d0510db14b41442fa60d0510be583414427e6590510cfd52414433c5490510d7d4e414435c5390510dbd4a414436c52905109f195414433f5450510cf151414435f5350510d714d414436f5250510db14941442fb6050510be181414427e6510510cfd50414433c5410510d7d4c414435c5310510dbd48414436c52105109f997314433f54cc510cf153314435f53cc510d714f314436f52cc510db14b31442fa60cc510be583314427e658c510cfd52314433c548c510d7d4e314435c538c510bb98a31442ed628c510dbd4a314436c528c5109f195314433f544c510cf151314435f534c510d714d314436f524c510db14931442fb604c510be181314427e650c510af99031442bd640c510cfd50314433c540c510d7d4c314435c530c510dbd48314436c520c5109f997214433f54c8510cf153214435f53c8510d714f214436f52c8510db14b21442fa60c8510be583214427e6588510cfd52214433c5488510d7d4e214435c5388510dbd4a214436c5288510bd996214437665885109d99621443b75488510ed15221443d75388510dd94e21443745388510f514e21443545388510bd58a21443e75288510dd94a21443745288510f914a21443645288510bd982214427c6548510cfd51214433c5448510d7d4d214435c5348510dbd49214436c5248510bed8121442f86048510dd19521442746548510edd5121443b45448510f5d4d21443765348510dd14d21443d45348510d514d21443e76248510f9d4921443765248510dd14921443e45248510d914921443e73248510f90c921443f36048510bd18121443f060485109f994214433f5408510cf150214435f5308510d714c214436f5208510db14821442f66108510f9484214427e65d0110cfd53404433c54d0110d7d4f404435c53d0110dbd4b404436c52d0110bd98740442f561d01109f996404433f5490110cf952404433d5490110cf152404435f5390110d714e404436f5290110db14a40442be6590110cf996404423e6590110cfd4e404439f5390110c7d4e404433e5390110cf54e404433c5390110e714e404431c5390110cfd4a40443af5290110cbd4a404433e5290110cf54a404433c5290110eb14a404432c5290110ed88640443b52190110af982404427f6550
  | 5 => 0x434427e6510d109f594434427c6510d10cfd50434433c5410d10d7d4c434435c5310d10bd98443442f56110d10cfd53524433c54d4910d7d4f524435c53d49109f993524427d64d49109f98f524427d63d4910dbd5352443af54d4910cbd53524436e54d4910db553524436c54d4910eb153524432c54d4910dbd4f52443cf53d4910d3d4f524436e53d4910db54f524436c53d4910f314f524434c53d4910f9d87524436f64d4910db993524436d64d4910db193524436f63d4910db98f524436d63d4910db18f524436f43d4910db90f524436d43d4910db10f524436f61d4910db587524436f60d4910db58352442be6494910af592524433f5494910cf15252442de6394910b758e524435f5394910d714e524436f52949109f992524433e64949108f992524427d6494910cf592524423d64949109f98e524435e63949109798e524427d6394910d758e524425d63949109f98a524426e62949109f586524437561949109f58252443796094910afd9152442bc6454910cfd51524433c5454910b7d8d52442dc6354910d7d4d524435c53549109fd91524433f64549108fd91524427c6454910cf191524423c64549109fd8d524435f635491097d8d524427c6354910d718d524425c6354910dbd89524427f6154910ddd85524427761549109fd81524437b60549109f994524433f5414910cf150524435f5314910d714c524436d52149109f990524427d64149109f98c524427d6314910db988524427e6114910dd584524427c61149109f980524427c6014910bb994524436e65149109b994524436f5414910ebd50524432f5414910db950524436d5414910db15052443ac5414910cb150524436f5314910f3d4c524434f5314910db94c524436d5314910db14c52443cc5314910d314c52443e56114910dbd90524436e6414910db590524436c6414910dbd8c524436e6314910db58c524436c6314910dbd0c524436e4314910db50c524436c4314910dbd84524436d6114910d9584524436f6014910db580524436d10149109fd97424427e65d09109f597424427c65d0910cfd53424433c54d0910d7d4f424435c53d0910dbd4b424436c52d09109fd96424427e65909109f596424427c6590910cfd52424433c5490910d7d4e424435c5390910dbd4a424436c5290910bd98642442f56190910be98242442f960909109fd95424427e65509109f595424427c6550910cfd51424433c5450910d7d4d424435c5350910dbd49424436c52509109fd94424427e65109109f594424427c6510910cfd50424433c5410910d7d4c424435c5310910dbd48424436c5210910bd98442442f561109109fd97324427e65cc9109f597324427c65cc910cfd53324433c54cc910d7d4f324435c53cc910dbd4b324436c52cc9109fd96324427e658c9109
  | 6 => 0x33f5495110b798e54442dd6395110bb98a54442ed62951109f992544423e64951109f98e544435e63951109798e544427d6395110d758e544425d63951109f98a544436e62951109b98a544427d6295110db58a544426d62951109f586544437561951109f58254443796095110b7d8d54442dc6355110bbd8954442ec6255110cfd91544427f6355110d7d8d544425f63551109f18d544435c63551109718d544427f6255110dbd89544426f62551109f189544436c62551109b189544427f6155110ddd85544427f6055110ded81544427e6515110cf550544433e64151109f98c544427d63151109f988544427d62151109f984544427c61151109f980544427c6015110af994544433e65151108f994544433f6315110cf98c544433d6315110cf18c544433f6215110cf988544433d6215110cf188544433f6115110cf584544433f60151108f980544433d60151108f180544433d1015110cfd53534433c54d4d109f993534427d64d4d109f98b534427d62d4d10d7d53534439f54d4d10c7d53534435e54d4d10d7553534435c54d4d10e7153534431c54d4d10d7d93534435e64d4d10d7593534435c64d4d10d7d8b534435e62d4d10d758b534435c62d4d10d7d87534435d61d4d10d7d83534435d60d4d10af99253442bd6494d10cfd52534433c5494d10d7d4e53442ee6294d10bb58a534427e6494d10cf992534423e6494d109f592534433d6494d108f592534427e6394d109798e534427e6294d10db98a534426e6294d109f58a534436d6294d109b58a534427d6194d10dd586534427d6094d10de58253442bf6454d10af191534433f5454d10cf15153442ef6254d10bb189534427f6454d10cfd91534423f6454d109f191534433c6454d108f191534435f6354d109fd89534436f6254d109bd89534427c6254d10db189534426c6254d109fd8553443776154d109dd85534427f6054d10ded81534427e6514d10cfd50534433c5414d10d754c534427e6414d109f590534435e6314d109f988534427d6214d109f984534427c6114d109f980534427c6014d10b7994534435e6514d1097994534435f5414d10e7d50534431f5414d10d7950534435d5414d10d7150534439c5414d10c7150534435f6414d10d7990534435d6414d10d7190534435f6214d10d7988534435d6214d10d7188534435f6114d10d7584534435f6014d10d7580534435d1014d109fd97434427e65d0d109f597434427c65d0d10cfd53434433c54d0d10d7d4f434435c53d0d109fd96434427e6590d109f596434427c6590d10cfd52434433c5490d10d7d4e434435c5390d109fd95434427e6550d109f595434427c6550d10cfd51434433c5450d10d7d4d434435c5350d10bbd8943442ec6250d10bdd8543442f46150d10bed8143442f86050d109fd94
  | 7 => 0x4d0610cf55341842fa60d0610be583418433f5490610cf152418433e5450610cf55141842fb6050610be181418433f5410610cf150418435e53cc610d754f31842fa60cc610be583318437565cc610dd953318437454cc610ddd4f31843d653cc610dd54f31843d553cc610bd98b318437752cc610dd54b31843f260cc610bd58331843f160cc610d7d4e318435c538c610bb98a31842ed628c610d794d318435d534c610bed8131842f8604c610af99031842bd640c610d7d4c318435c530c610f54c431842f5650c610dd59431843b6640c610ed5903184376540c610dd15031843d6630c610ddd4c31843d7530c610dd54c31843d4530c610bd9883184377520c610dd54831842f5600c610db94b218436d52c8610be98321842f960c8610dd59721842f663c8610bd18f218437752c8610f994b218437552c8610f954b21843e732c8610f90cb21843f260c8610bd58321843f160c8610dbd4a218436c5288610db949218436d5248610bed8121842f86048610dbd48218436c5208610f948421842f56508610dd59421842f66308610bd18c21843e66208610ddd4821843e75208610d9d4821843755208610f914821842f56008610cf952408433d5490210bd98640842f56190210cf996408433d6590210cfd4e408433e5390210cf54e408433c5390210cfd4a408433e5290210cf54a408433c5290210ed98640843b56190210edcc640843b43190210edc8640843b42190210cf950408433d5410210bd98440842f56110210cf994408433d6510210cfd4c408433e5310210cf54c408433c5310210cfd48408433e5210210cf548408433c5210210ed98440843b56110210edcc440843b43110210edc8440843b42110210ee98040842be64cc210af59330843b840cc210d794e308435d538c210bd98630842f5618c210f50c630842bf644c210af19130842ef624c210bb18930842f7614c210bd185308435e530c210d754c30842f6610c210bd58430843d4310c210ee10030842be64c8210af593208436f52c8210db14b20843e721c8210db94a208436d5288210bd98620842f56188210f908620843b84088210afd9120842bc6448210b7d8d20842dc6348210dbd49208436c5248210bdd8520842f46148210f9c8520843b84048210db948208436d5208210bd98420842f56108210f908420842be64c4210af59310843ba40c4210ee10310842f565c4210dd59710843b664c4210ed59310842f663c4210bd18f10842f662c4210bd18b108437752c4210dd54b10843b640c4210ed10310842f965c4210de59710843ba64c4210ee593108427e63d51109f58f544427e62d51109f58b544433f63d5110cf98f544433d63d5110cf18f544433f62d5110cf98b544433d62d5110cf18b544433f61d5110cf587544433f60d5110cf5835444
  | 8 => 0x10afd9130c42bc644c310cf95130c433d544c310d794d30c435d534c310bbd8930c42ec624c310bdd8530c42f4614c310cf95030c433d540c310d7d4c30c435c530c310ee10030c42be64c8310af59320c433e54c8310cf55320c436e52c8310db54b20c42f661c8310bd58720c43e521c8310ee10320c433e5488310cf55220c436f5288310db14a20c43e62188310afd9120c42bc6448310cf95120c433d5448310b7d8d20c42dc6348310db94920c436d5248310bdd8520c42f46148310f948520c433e5408310cf55020c436f5208310db14820c42f66108310bd58420c43e62108310ee10020c427e63d52109f58f548427e62d52109f58b548437561d5210de983548433f54952109f98e548427d63952109f98a548427d6295210cfd91548427f63552109f18d548427f62552109f189548433d5415210cf990548427e63152109f58c548427e62152109f58854843756115210de980548427e64d4e109f593538427e62d4e109f58b538437561d4e10de98353842be6494e10af592538435f5394e109f992538433e6494e108f992538427d6494e10cf592538423d6494e109f98a538427d6294e10bbd8953842ec6254e109fd91538427c6454e10d7d8d538427f6254e10dbd89538426f6254e109f189538436c6254e109b18953843776154e10d754c538427e6414e109f590538435e6314e109f988538427d6214e10dd584538437a6014e109fd97438427e65d0e109f597438427c65d0e10cfd53438433c54d0e10bd98743842f561d0e109fd96438427e6590e109f596438427c6590e109fd95438427e6550e109f595438427c6550e10cfd51438433c5450e10bbd8943842ec6250e10bdd8543842f46150e10bed8143842f86050e109fd94438427e6510e109f594438427c6510e109f993528427d64d4a109f98f528427d63d4a10dd587528437a60d4a10dbd4a528427e6494a109f592528427e6394a109f58e528427f6454a109f191528427f6354a109f18d528436f6254a10ddd85528436d5214a109f990528427d6414a109f98c528427d6314a10db98852843756114a10de980528427f65d0a109f997428427d65d0a109f19742842f661d0a10bd587428427f6590a109f996428427d6590a109f19642842fa6090a10be582428427f6550a109f995428427d6550a109f19542842f76150a10bd185428427f6510a109f994428427d6510a109f194428427f65cca109f997328427d65cca109f197328436f52cca10db14b32842f661cca10bd587328427f658ca109f996328427d658ca109f19632842f6618ca10bd586328427f654ca109f995328427d654ca109f19532842f7614ca10bd185328427f650ca109f994328427d650ca109f19432842be640ca10af590328436f520ca10db14832842fa600ca10be580328433e5
  | 9 => 0x54852c427e6414b10cf99052c423e6414b109f59052c433d6414b108f59052c427e6314b109f58c52c436e6214b10dd98452c43796014b109fd9742c427e65d0b109f59742c427c65d0b10cf95342c433d54d0b109fd9642c427e6590b109f59642c427c6590b10cf95242c433d5490b10bd98642c42f56190b109fd9542c427e6550b109f59542c427c6550b10cf95142c433d5450b10bed8142c42f86050b109fd9442c427e6510b109f59442c427c6510b10cf95042c433d5410b10bd98442c42f56110b109fd9732c427e65ccb109f59732c427c65ccb10cf95332c433d54ccb10db94b32c436d52ccb109fd9632c427e658cb109f59632c427c658cb10cf95232c433d548cb10d794e32c435d538cb10bd98632c42f5618cb109fd9532c427e654cb109f59532c427c654cb10cf95132c433d544cb10bed8132c42f8604cb109fd9432c427e650cb109f59432c427c650cb10af99032c42bd640cb10cf95032c433d540cb10d794c32c435d530cb10db94832c436d520cb10bd98432c42f5610cb10cf95341c433d54d0710cf95241c433d5490710be98241c42f96090710cf95141c433d5450710cf95041c433d5410710be98041c42f96010710cf95331c433d54cc710cf95231c433d548c710d794e31c435d538c710bb98a31c42ed628c710be98231c42f9608c710cf95131c433d544c710af99031c42bd640c710cf95031c433d540c710d794c31c435d530c710be98031c42f9600c710cf95321c433d54c8710dbd4b21c436c52c8710cf95221c433d5488710db94a21c436d5288710be98221c42f96088710dd59621c43b65488710ed55221c43765388710dd14e21c43765288710f994a21c43e55288710dd14a21c42f66088710fc98221c43f16088710cf95121c433d5448710dbd4921c436c5248710bdd9521c43776548710ed95121c43b55448710dd94d21c43745348710f9d8921c43e75248710dd94921c43745248710f914921c43645248710f9cc921c43e43248710bd18121c433e5408710cf55021c436e5208710db54821c43e52108710be98021c42f96008710cf95340c433d54d0310bd98740c42f561d0310cfd5240c433e5490310cf55240c433c5490310af59640c433d6590310cfd4e40c433e5390310cf54e40c433c5390310cfd4a40c433e5290310cf54a40c433c5290310ed88640c43b52190310cf95140c433d5450310bdd8540c42f46150310cfd5040c433e5410310cf55040c433c5410310af59440c433d6510310cfd4c40c433e5310310cf54c40c433c5310310cfd4840c433e5210310cf54840c433c5210310ed88440c43b52110310ee98040c42be64cc310af59330c433e54cc310cf55330c435e53cc310d754f30c42f661cc310bd58730c43b840cc310cf95230c433d548c310d7d4e30c435c538c3
  | 10 => 0x83755148020ee90120083b84048020bbd95200836f65480209bd9520083af6448020eb19120083cf6348020bb98d20082ec6348020f318d20082cc6348020f9d8520082ec6148020f918520082e46148020f9945200836d5148020f954520083655148020bbd81200836e5048020fad0120083ae4048020eb10120083e84048020ea10120082fb6548020ded95200827b6548020eed9120083b86448020f6d8d20083d86348020bed8920083eb6248020de94920083ea5248020fad0920083e84248020fcd8520083f06148020fc94520083f151480209f98f54c427d63d53109f98b54c427d62d5310dd98754c437960d5310cfd5254c427e63953109f58e54c427e62953109f58a54c433f6395310cf98e54c433d6395310cf18e54c433f6295310cf98a54c433d6295310cf18a54c433e6195310cf18654c433f6095310cf58254c433f64553109fd8d54c427c63553109fd8954c427c6255310cfd9554c433f6355310cf98d54c433d6355310cf18d54c433f6255310cf98954c433d6255310cf18954c433e6155310cf18554c433f6055310cf58154c433d5415310cf99054c427e63153109f58c54c427e62153109f58854c43766115310de58054c42be64d4f10af59353c433e54d4f10cf55353c42ee62d4f10bb58b53c427e64d4f10cf99353c423e64d4f109f59353c433d64d4f108f59353c427e62d4f10db98b53c426e62d4f109f58b53c436d62d4f109b58b53c437661d4f10de58353c433e5494f10cf55253c435f5394f109f99253c427d6494f109f98a53c427d6294f10cf95153c433d5454f109fd9153c427c6454f10d7d8d53c427f6254f109f18953c42be6414f10af59053c433e5414f10cf55053c435d5314f109f99053c433e6414f108f99053c427d6414f10cf59053c423d6414f10d798c53c427e6214f109f58853c43766114f10de58053c427f65d0f109f99743c427d65d0f109f19743c433e54d0f10cf55343c427f6590f109f99643c427d6590f109f19643c433e5490f10cf55243c427f6550f109f99543c427d6550f109f19543c433e5450f10cf55143c42ef6250f10bb18943c42f76150f10bd18543c42fb6050f10be18143c427f6510f109f99443c427d6510f109f19443c433e5410f10cf55043c42f66110f10bd58443c42be64d4b10af59352c433e54d4b10cf55352c42de63d4b10b758f52c427e64d4b10cf99352c423e64d4b109f59352c433d64d4b108f59352c427e63d4b10d798f52c425e63d4b109f58f52c435d63d4b109758f52c437661d4b10de58352c433e5494b10cf55252c436f5294b109f99252c427d6494b109f98e52c427d6394b10dd98652c433e5454b10cf55152c427f6454b109f19152c427f6354b109f18d52c436f6254b10af99052c42bd6414b10cf95052c433d5414b10db
  | 11 => 0x7551cc4209fd96310827e658c4209f59631082ee628c420bb58a3108376518c420dd546310827f654c4209f595310827c654c420bbd8931082ec624c420dd9453108375514c420bed8131082f8604c4209fd94310827e650c4209f59431082be640c420af5903108376510c420dd544310836e52c8420dd947210837551c8420be98321082f960c84209f59621083755188420bb596210836d65884209b59621082ee6388420bb18e21082ee6188420f9946210836d5188420f954621083655188420f9cc621083e43188420bb582210827f6548420db94921083765148420dd94421083755108420f948421082fa6008420be58021082ee6308420bb18c21082ee6108420f998421083e65108420db54421083e55108420d954421083ea6008420bb58021083e960084209f992500827d64940209f98e500827d6394020dbcca500836c3294020db886500836c21940209f597400837651d0020dd547400827f65900209f596400833e5490020cf55240082ee6290020bb58a40083765190020dd546400833f6590020cf996400833d6590020cf196400833f5390020cf94e400833d5390020cf14e40083ae6290020eb58a400833e5290020ebcca40083ac3290020cf94640083b65190020cd946400833d5190020ed54640083355190020eb88640083ac2190020af982400833e50900209fd9540083765150020dd545400827f65100209f994400827d65100209f194400833e5410020cf55040082ee6210020bb58840083765110020dd544400833f6510020cf994400833d6510020cf194400833f5310020cf94c400833d5310020cf14c40083ae6210020eb588400833e5210020ebcc840083ac3210020cf94440083b65110020cd944400833d5110020ed54440083355110020eb88440083ac2110020af98040083ba6010020cf940400827d65cc020af99330082bd64cc020dd947300837551cc020ee103300827f658c0209f596300835e538c020d754e30082ee628c020bb58a30083cc328c020dd9463008375518c0209fd9530082bf644c020af19130082ef624c020bb18930082f7614c020bd1853008376514c020dd545300827f650c0209f994300827d650c0209f194300835e530c020d754c30082ee620c020bb58830083cc320c020dd9443008375510c020ee10030082be64c8020af593200837651c8020dd54720083ae64c8020eb59320082ee63c8020bb18f20082ee61c8020f9947200836d51c8020f9547200836551c8020eb90320083ac40c8020bb58a200836e5288020dd94620083755188020ee90220083b84088020be58a200837a5288020fa94a20083eb3288020fa0ca20083f25188020fc54620083ea2188020fa086200827f6548020afd9120082bc6448020b7d8d20082dc6348020bdd8520082f46148020dd9452
  | 12 => 0xd0c20cf953430833d54d0c20bb98b43082ed62d0c209fd96430827e6590c209f596430827c6590c20d794e430835d5390c209fd95430827e6550c209f595430827c6550c20cf951430833d5450c20d794d430835d5350c20bbd8943082ec6250c20bdd8543082f46150c20bed8143082f86050c209fd94430827e6510c209f594430827c6510c209f992520833e64948208f992520827d6494820cf592520823d64948209f98e520827d63948209f597420833f54d0820cf153420827f65908209f596420833e5490820cf55242082fa6090820be582420827f6550820cfd51420833c54508209fd94420827d6510820cf950420833d5410820be98042082f960108209f59732082ed65cc820db597320836e54cc820db153320836f53cc820db54f32082ee61cc820bb583320827f658c8209f596320835e538c820d754e32082ee628c820bd98632082f5618c820be98232082f9608c8209fd95320827f650c8209f59432082be640c820af590320835e530c820d754c32083cd320c820be98032082f9600c820db594320826d650c820eb99032083ad640c820db950320836c540c820bb98c32083ce630c820dbd4c32083ce530c820db54c32083cd530c820bb98432083ea600c820bb58032083e9600c820ddd46510827e64944209f592510827e63944209f58e51083775494420dd95251083755494420dd15251083775394420dd94e51083755394420dd14e51083e46294420f9cca51083e43294420ddd9251083766494420dd59251083746494420ddd8e51083766394420dd58e51083746394420ddd0e51083764394420dd50e51083744394420dd18a51083774294420dd90a51083754294420dd10a51083773294420dd8ca51083753294420dd0ca51083766094420dd182510827f64544209f191510827f63544209f18d510836f3254420db0c951083776554420ddd5151083765454420dd55151083745454420ddd4d51083765354420dd54d51083745354420f918951083e73254420f90c951083776454420dd99151083756454420dd19151083776354420dd98d51083756354420dd18d51083774354420dd90d51083754354420dd10d51083766254420ddd0951083764254420dd50951083744254420ddcc951083673254420dd8c951083753254420dd0c951083643254420dd98151083746054420dd08151082f66114420dd544510827f65d04209f997410827d65d0420bb98b41082ed62d0420dd947410837551d04209fd96410827e65904209f59641083765190420dd546410827f65504209f595410827c6550420bbd8941082ec6250420dd94541083755150420bed8141082f860504209fd94410827e65104209f59441083765110420dd544410827f65cc4209f997310827d65cc420bb98b31082ed62cc420dd94731083
  | 13 => 0xcf950404833d5410120cf150404835f5310120d714c40483775110120dd14440482be6510120cf994404823e6510120cfd4c404839f5310120c7d4c404833e5310120cf54c404833c5310120e714c404831c5310120cfd4440483b75110120cdd44404833c5110120ed14440483345110120ebc8440483ad2110120af98040483ba60101209f99730482be64cc120af593304833f54cc120cf153304835f53cc120d714f30482ee62cc120bb58b304837751cc120dd14730483b840cc1209f996304833f548c120cf152304835f538c120d714e3048377518c120dd146304827f654c1209f595304827c654c120afd9130482bc644c120cfd51304833c544c120d7d4d304835c534c120bbd8930482ec624c120bdd8530482f4614c120ddd453048374514c1209f994304833f540c120cf150304835f530c120d714c3048377510c120dd14430483b8400c120af99320482bd64c8120cfd53204833c54c8120d7d4f204835c53c8120ddd47204837451c8120ee90320483b840c8120ee99320483b964c8120eed5320483b854c8120f6d4f20483d853c8120fcd4720483f051c8120fac8720483e921c8120cfd52204833c5488120d7d4e204835c5388120ddd4620483745188120ebd5220483ac5488120f3d4e204836e5388120db14e20483cc5388120d314e20482ed6188120f9d46204836c5188120f914620483645188120fad4220483ae4088120eb10220482f661d5020bd587540827e63d50209f58f540827e62d5020db98b540827e61d5020dd987540827661d50209f587540837561d50209d587540827e60d5020de983540827d6595020cfd52540827e63950209f58e540827e61950209f586540833f64550209fd8d540827c63550209fd89540827d62550209fd85540827c6155020cf55054082de6315020b758c54082f66115020bd584540827e6415020cf990540827e6315020d798c540825e63150209f58c540835d63150209758c540827e6215020db988540827e6115020dd984540827661150209f584540837561150209d584540827e6015020de98054082f661d4c20bd587530827e64d4c209f593530827e62d4c20db98b530827e61d4c20dd987530827661d4c209f587530837561d4c209d587530827e60d4c20de983530827d6594c20d7d4e530827e6494c209f592530827e6194c209f586530827f6454c209f191530835f6354c209fd89530827d6254c20db189530827f6154c209f18553082be6414c20af590530835d5314c20bd98453082f56114c209f990530833e6414c208f990530827d6414c20cf590530823d6414c209f98c530835e6314c209f988530836e6214c209f98453083766114c209d984530827d6114c20dd58453082756114c209f980530837a6014c209fd97430827e65d0c209f597430827c65
  | 14 => 0xc51483764314520dd50c51483744314520ddd8851483774214520dd90851483754214520dd10851483773214520dd8c851483753214520dd0c851483776014520dd580514837520145209f997414827d65d05209f197414833f54d0520cf153414835f53d0520d714f414837751d0520dd147414827e65905209f596414827c6590520cfd52414833c5490520d7d4e414835c5390520bb98a41482ed6290520ddd4641483745190520be98241482f960905209fd95414827e65505209f195414833f5450520cf151414835f5350520d714d41483775150520dd145414827e65105209f594414827c6510520cfd50414833c5410520d7d4c414835c5310520bb98841482ed6210520ddd44414837451105209f997314827d65cc5209f197314833f54cc520cf153314835f53cc520d714f314837751cc520dd147314827e658c5209f596314827c658c520cfd52314833c548c520d7d4e314835c538c520bb98a31482ed628c520ddd463148374518c5209fd95314827e654c5209f195314833f544c520cf151314835f534c520d714d3148377514c520dd145314827e650c5209f594314827c650c520af99031482bd640c520cfd50314833c540c520d7d4c314835c530c520bb98831482ed620c520ddd443148374510c520be98031482f9600c5209f997214833f54c8520cf153214835f53c8520d714f214837451c8520bb997214836e65c85209b99721483af54c8520eb15321483cf53c8520db94f214836c53c8520f314f214834c53c8520f9d47214836c51c8520f9147214836451c8520bb983214833f5488520cf152214835f5388520d714e21482ed6288520ddd4621483745188520be98221482f96088520cfd51214833c5448520d7d4d214835c5348520ddd4521483745148520bed8121482f86048520ebd5121483ac5448520f3d4d214836e5348520db14d21483cc5348520d314d21483e76148520f9d45214836c5148520f914521483645148520f9cc521483e43148520fad8121482ec6048520fa181214827e6508520cfd50214833c5408520d7d4c214835c5308520bb98821483775108520f9484214827e65d0120cfd53404833c54d0120d7d4f404835c53d0120bb98b40482ed62d0120ddd47404837451d01209f996404833f5490120cf952404833d5490120cf152404835f5390120d714e40483775190120dd14640482be6590120cf996404823e6590120cfd4e404839f5390120c7d4e404833e5390120cf54e404833c5390120e714e404831c5390120cfd4640483b75190120cdd46404833c5190120ed14640483345190120ebc8640483ad2190120af982404827f65501209f595404827c6550120cfd51404833c5450120d7d4d404835c5350120bbd8940482ec6250120ddd45404837451501209f994404833f541012
  | 15 => 0x4825e6514d20d7d50534839f5414d20c7d50534835e5414d20d7550534835c5414d20e7150534831c5414d20d7d90534835e6414d20d7590534835c6414d20d7d88534835d6214d20d7d84534835e6114d20d7584534835c6114d20d7d80534835d6014d20d7480534827f65d0d209f997434827d65d0d209f197434833f54d0d20cf153434835f53d0d20d714f434827f6590d209f996434827d6590d209f196434833f5490d20cf152434835f5390d20d714e434827f6550d209f995434827d6550d209f195434833f5450d20cf151434835f5350d20d714d43482ef6250d20bb18943482f76150d20bd18543482fb6050d20be181434827f6510d209f994434827d6510d209f194434833f5410d20cf150434835f5310d20d714c43482ee6210d20bb588434827e65d0920cfd53424833c54d0920d7d4f424835c53d0920be98342482f960d09209f996424833f5490920cf152424835f5390920d714e424827c6550920cfd51424833c5450920d7d4d424835c5350920bed8142482f860509209f994424833f5410920cf150424835f5310920d714c424827e65cc920cfd53324833c54cc920d7d4f324835c53cc920be98332482f960cc9209f996324833f548c920cf152324835f538c920d714e32482f6618c920bd586324827c654c920cfd51324833c544c920d7d4d324835c534c920bed8132482f8604c9209f99432482be640c920af590324833f540c920cf150324835f530c920d714c324833f54d4520cf153514835f53d4520d714f514827e64d45209f593514827e63d45209f58f514837754d4520edd53514833754d4520dd953514837554d4520dd15351483b454d4520cd153514837753d4520f5d4f514835753d4520dd94f514837553d4520dd14f51483d453d4520d514f51483e762d4520ddd93514837664d4520dd593514837464d4520ddd8f514837663d4520dd58f514837463d4520ddd0f514837643d4520dd50f514837443d4520ddd8b514837742d4520dd90b514837542d4520dd10b514837732d4520dd8cb514837532d4520dd0cb514837760d4520dd58351482be6494520af592514833f5494520cf15251482de6394520b758e514835f5394520d714e51483775194520afd9151482bc6454520cfd51514833c5454520b7d8d51482dc6354520d7d4d514835c5354520cfd50514833c5414520d7d4c514835c5314520dd544514827e64145209f590514827e63145209f58c51482f66514520dd99451483775414520edd5051483375414520dd95051483755414520dd15051483b45414520cd15051483775314520f5d4c51483575314520dd94c51483755314520dd14c51483d45314520d514c51483e56214520ddd9051483766414520dd59051483746414520ddd8c51483766314520dd58c51483746314520ddd
  | 16 => 0xe5110220cf54440883ae2110220eb08440883ba6010220af99330882bd64cc220ee103308835e538c220d754e30882ee628c220bb58a30883cc328c220afd9130882bc644c220bbd8930882ec624c220bdd8530882f4614c220d794c308835d530c220bb98830882ed620c220f30c830883b8400c220af99320882bd64c8220ee90320883b840c8220bb597208836d65c8220eb99320883ad64c8220bb98f20882ec63c8220bb987208836d51c8220eb90320883ac40c8220be597208837965c8220ee99320883b964c82209f98f544827d63d51209f987544827d61d5120cfd8f544833e63d5120cf58f544833c63d5120cfd8b544833d62d5120cfd87544833e61d5120cf587544833c61d5120cfd83544833d60d5120cfd5254482de6395120b758e54482f66195120bd586544827e64951208f992544827e6395120d798e544825e63951209f58e544835d63951209758e544827d6295120db58a544827e6195120dd986544827661951209f586544837561951209d586544827d6095120de58254482df6355120b718d54482f76155120bd185544833f64551209fd8d544835f635512097d8d544827c6355120d718d544825c63551209fd89544836f62551209fd85544837761551209dd85544827c6155120dd185544827461551209fd81544837b60551209f994544833d5415120cf990544827e63151209f58c544827e62151209f188544827e61151209f58454482be6515120cf994544823e6515120cfd8c544833e6315120cf58c544833c6315120cfd88544833d6215120cfd84544833e6115120cf584544833c6115120cfd80544833d6015120cf480544833f54d4d20cf153534827e64d4d209f593534827e61d4d209f587534835f54d4d20e7d53534831f54d4d20d7953534835d54d4d20d7153534839c54d4d20c7153534835f64d4d20d7993534835d64d4d20d7193534835f62d4d20d758b534835f61d4d20d7987534835d61d4d20d7187534835f60d4d20d758353482be6494d20af592534833f5494d20cf152534835f5394d20bd98653482f56194d209f992534833e6494d208f992534827d6494d20cf592534823d6494d209f98e534825e6394d209f58a534836d6294d209f98653483766194d209d986534827d6194d20dd58653482756194d209f58253483796094d20afd9153482bc6454d20cfd51534833c5454d20bdd8553482f46154d209fd91534833f6454d208fd91534827c6454d20cf191534823c6454d20d7d8d534827f6254d20dbd89534826f6254d209fd8553483776154d209dd85534827c6154d20dd18553482746154d209fd81534837b6054d209f994534833f5414d20cf150534835d5314d209f990534827d6414d20d798c534827e6214d209f188534827e6114d209f58453482de6514d20d799453
  | 17 => 0x4e209f986538827d6194e20bdd8553882f46154e209fd91538827c6454e20d7d8d538836f6254e209fd8553883776154e209dd85538827c6154e20dd18553882746154e20d754c538827e6414e209f590538835e6314e20db588538827e6114e209f584538837a6014e209fd97438827e65d0e209f597438827c65d0e20cfd53438833c54d0e20bb98b43882ed62d0e209fd96438827e6590e209f596438827c6590e209fd95438827e6550e209f595438827c6550e20cfd51438833c5450e20bbd8943882ec6250e20bdd8543882f46150e20bed8143882f86050e209fd94438827e6510e209f594438827c6510e20cf953428833d54d0a20be98342882f960d0a20cfd52428833c5490a20cf951428833d5450a20bed8142882f86050a20cfd50428833c5410a20d794f328835d53cca20be98332882f960cca20db597328836e54cca20db153328836f53cca20f394f328836d53cca20f354f32882ee61cca20fa98332882ed60cca20fa583328835f538ca20d714e32882f6618ca20bd586328835e534ca20d754d32882fb604ca20be18132882be640ca20af590328835f530ca20d714c32883cd320ca20bb594328836d650ca20eb99032883ad640ca20db950328836c540ca20f398c328836f530ca20f3d4c328836d530ca20f314c32882ee610ca20bb580328837751946209f992518827d64946209f98e518827d63946209fd91518827c64546209fd8d518827c6354620dbcc9518836c3254620dd544518827f65d06209f997418827d65d0620bb98b41882ed62d06209fd96418827e65906209f59641882fa6090620be582418827f65506209f595418827c6550620bbd8941882ec62506209fd94418827e65106209f594418827f65cc6209f997318827d65cc620bb98b31882ed62cc6209fd96318827e658c6209f59631882ee628c620bb58a318827f654c6209f595318827c654c620bbd8931882ec624c6209fd94318827e650c6209f59431882be640c620af59031882fa600c620be58031883765188620dd54621882fa6088620be58221882ee6388620bb18e21883e65188620db54621883e55188620f9cc621883e43188620fa98221882ed6088620fa58221883765148620dd54521882fb6048620be18121883e52108620bb594218836d6508620bb98c21882ec6308620f998421883e75108620db54421883e45108620bb580218833e5490220cf55240882ee6290220bb58a408833e6590220cf596408833f5390220cf94e408833d5390220cf14e40883ae6290220eb58a40883af3290220eb0ca408833e5190220cf54640883ae2190220eb086408833e5410220cf55040882ee6210220bb588408833e6510220cf594408833f5310220cf94c408833d5310220cf14c40883ae6210220eb58840883af3210220eb0c8408833
  | 18 => 0xcf55151c827f64547209f19151c827f63547209f18d51c82be6414720af59051c833e5414720cf55051c837551147209fd9741c827e65d07209f59741c833e54d0720cf55341c827f65907209f99641c827d6590720cf95241c833d5490720bb98a41c82ed62907209fd9541c827d65507209f19541c833e5450720cf55141c82fb6050720be18141c827f65107209f99441c827d6510720cf95041c833d5410720bb98841c82ed62107209fd9731c827e65cc7209f59731c833e54cc720cf55331c837651cc720dd54731c827f658c7209f99631c827d658c720cf95231c833d548c720d794e31c835d538c720bb98a31c82ed628c7209fd9531c827d654c7209f19531c833e544c720cf55131c82fb604c720be18131c827f650c7209f99431c827d650c720af99031c82bd640c720cf95031c833d540c720d794c31c835d530c720bb98831c82ed620c720dd94431c8375510c720cf95321c833d54c8720dd94721c837551c8720be98321c82f960c8720eb95321c83ad54c8720db94f21c836c53c8720db94721c83e651c8720f954721c82ee60c8720fa98321c83e960c8720cf95221c833d5488720cf95121c833d5448720bbd9521c836f6548720eb95121c83ad5448720db94d21c836c5348720f9d8521c83e75148720db94521c83e45148720f9cc521c83e43148720bb18121c833e5408720cf55021c83765108720dd54421c83e52108720be98021c82f96008720cf95340c833d54d0320bb98b40c82ed62d0320cfd5240c833e5490320cf55240c833c5490320af59640c833d6590320cfd4e40c833e5390320cf54e40c833c5390320cf94640c833d5190320ebc8640c83ad2190320cf95140c833d5450320bbd8940c82ec6250320cfd5040c833e5410320cf55040c833c5410320af59440c833d6510320cfd4c40c833e5310320cf54c40c833c5310320cf94440c833d5110320ebc8440c83ad2110320ee98040c82be64cc320af59330c833e54cc320cf55330c835e53cc320d754f30c82ee62cc320bb58b30c83b840cc320cf95230c833d548c320d7d4e30c835c538c320afd9130c82bc644c320cf95130c833d544c320d794d30c835d534c320bbd8930c82ec624c320bdd8530c82f4614c320cf95030c833d540c320d7d4c30c835c530c320ee10030c827e63d52209f58f548836d62d52209f987548827d61d5220de983548833f54952209f98e548827d63952209f986548827d6195220cfd91548827f63552209f18d548827f61552209f185548833d5415220cf990548827e63152209f58c548836d62152209f984548827d6115220de980548827e64d4e209f593538836d62d4e209f987538827d61d4e20de98353882be6494e20af592538835f5394e209f992538833e6494e208f992538827d6494e20cf592538823d649
  | 19 => 0x9300c2ec624c030bdd85300c2f4614c030ee901300c3b8404c030b7d95300c35f654c03097d95300c39f644c030e7191300c3cf624c030b7189300c3cc624c030b3189300c3d7614c030b7185300c3d4614c030b5185300c2df604c030d7941300c39e404c030e7101300c2fb654c030ded95300c27b654c030eed91300c2fa644c030be191300c3b8644c030ae191300c2fb634c030f6d8d300c37a534c030f694d300c3eb624c030fa189300c3f3614c030fc185300c27e63d53209f58f54c836e62d53209f98754c827d61d5320de58354c833f54953209f98e54c827d63953209f98654c827d6195320cfd8e54c833e6395320cf58e54c833c6395320cf98a54c833c6295320cfd8654c833e6195320cf58654c833c6195320cfd8254c833d6095320cfd9154c827f63553209f18d54c827f61553209f18554c833f6555320cfd8d54c833e6355320cf58d54c833c6355320cf98954c833c6255320cfd8554c833e6155320cf58554c833c6155320cfd8154c833d6055320cf55054c833e64153209f98c54c827d6315320db98854c827e61153209f58454c83796015320af99353c82bd64d4f20cf95353c833d54d4f20bd98753c82f561d4f209f99353c833e64d4f208f99353c827d64d4f20cf59353c823d64d4f20db98b53c827e61d4f20dd98753c827661d4f209f58753c837561d4f209d58753c837960d4f20cf95253c833d5494f20d7d4e53c827e6494f209f59253c827e6194f209f58653c833e5454f20cf55153c827f6454f209f19153c835f6354f209fd8553c827c6154f20af99053c82bd6414f20cf95053c833d5414f20d754c53c827e6414f20cf99053c823e6414f209f59053c833d6414f208f59053c835e6314f20db98853c827e6114f209f58453c83796014f209fd9743c827e65d0f209f59743c827c65d0f20cf95343c833d54d0f209fd9643c827e6590f209f59643c827c6590f20cf95243c833d5490f209fd9543c827e6550f209f59543c827c6550f20cf95143c833d5450f20bbd8943c82ec6250f20bdd8543c82f46150f20bed8143c82f86050f209fd9443c827e6510f209f59443c827c6510f20cf95043c833d5410f20bb98843c82ed6210f20cf95342c833d54d0b20cf95242c833d5490b20be98242c82f96090b20cf95142c833d5450b20cf95042c833d5410b20be98042c82f96010b20cf95332c833d54ccb20cf95232c833d548cb20d794e32c835d538cb20bd98632c82f5618cb20be98232c82f9608cb20cf95132c833d544cb20af99032c82bd640cb20cf95032c833d540cb20d794c32c835d530cb20be98032c82f9600cb20af99351c82bd64d4720cf95351c833d54d4720b798f51c82dd63d4720cf95251c833d5494720ddd4651c827e64947209f59251c827e63947209f58e51c833e5454720
  | 20 => 0xc2de610c430f5984310c3d6510c430d7544310c3d5510c430f5d04310c3d4410c430f6980310c2dd600c430f6580310c27f65c84309f997210c27d65c8430b798f210c2dd63c8430db94b210c36d52c8430f30cb210c27f65884309f996210c27d6588430b798e210c2dd6388430dd946210c3755188430f50c6210c27f65484309f595210c27c6548430b7d8d210c2dc6348430db949210c36d5248430f30c9210c3765148430dd545210c3d43148430bed81210c2f860484309fd94210c27e65084309f594210c2df6308430b718c210c3e521084309f992500c27d6494030d78ca500c35c3294030d78c6500c35c31940309f597400c2f965d0030de597400c37b54d0030de553400c2f963d0030de94f400c3da32d0030f60cb400c3da31d0030f60c7400c27f65900309f596400c33e5490030cf552400c2de6390030b758e400c2fa6090030cfd96400c33e6590030cf596400c33c6590030e798e400c39d6390030cf94e400c33e5290030cf54a400c39e3290030e70ca400c33e5190030cf546400c39e3190030e70c6400c2be6090030ae982400c33e50900309fd95400c27f65100309f994400c27d65100309f194400c33e5410030cf550400c2de6310030b758c400c3b94010030cfd94400c33e6510030cf594400c33c6510030e798c400c39d6310030cf94c400c33e5210030cf548400c39e3210030e70c8400c33e5110030cf544400c39e3110030e70c4400c2be6010030ee980400c33e5010030be594400c37965100309e594400c2fa6410030ee990400c37b5410030ee950400c3795410030ee550400c3da6310030be58c400c3d96310030de94c400c3bb4310030ee90c400c3b94310030ee10c400c3bb4210030ee908400c3b94210030ee108400c3da3210030f60c8400c3bb4110030ee904400c3b94110030ee104400c3da3110030f60c4400c3ba6510030ce994400c3b96510030ce594400c3bb6310030ee98c400c39a6310030ee58c400c3996310030ee18c400c33a5310030eed88400c3ba6210030ee588400c3b86210030eed48400c3ba5210030ee548400c3b85210030eecc8400c3ba3210030e68c8400c3b93210030ee0c8400c3983210030eed84400c3ba6110030ee584400c3b86110030eed44400c3ba5110030ee544400c3b85110030eecc4400c3ba3110030e68c4400c3b93110030ee0c4400c3983110030eec84400c3ba2110030ee484400c3b82110030af993300c2bd64cc030ee103300c39e64cc030e7593300c2de62cc030b7987300c3db40cc030e7903300c39c40cc030f6103300c39840cc030b758e300c35e538c030ee902300c3b8408c030be992300c2f8648c030be58e300c37a538c030f694e300c3da328c030f60ca300c3da318c030f60c6300c27f654c030afd91300c2bc644c030bbd8
  | 21 => 0x60d5030de983540c27d6595030cfd52540c27e62950309f58a540c27e61950309f586540c33f64550309fd8d540c27d63550309fd89540c27c62550309fd85540c27c6155030de181540c33d5415030bb988540c2ed6215030bd984540c2f561150309f990540c33e64150309f98c540c35e63150309f988540c36e62150309b988540c27d6215030db588540c26d62150309f984540c37661150309d984540c27d6115030dd584540c27561150309f980540c37a60150309f992530c33e6494c308f992530c27d6494c30cf592530c23d6494c309f597430c33f54d0c30cf153430c27f6590c309f596430c33e5490c30cf552430c2fa6090c30be582430c27f6550c30cfd51430c33c5450c30bbd89430c2ec6250c30bdd85430c2f46150c30bed81430c27f6510c309f594430c33e5410c30cf550430c2fa6010c30be580430c36f52948309f992520c27d64948309f986520c27d61948309fd91520c27c64548309fd85520c27c6154830af990520c2bd6414830db548520c2f66114830bd584520c27f65d08309f997420c27d65d0830cf953420c33d54d0830b798f420c2dd63d08309fd96420c27e65908309f596420c36e5290830db54a420c2fa6090830be582420c27f65508309f595420c27c6550830cf951420c33d5450830b7d8d420c2dc6350830db949420c36d5250830bed81420c2f860508309fd94420c27e65108309f594420c36e52cc830db54b320c2fa60cc830be583320c27d658c830bd986320c2f5618c830b7596320c35d658c830b798a320c35d528c830b7986320c3d6618c830b5986320c3d5618c830b7582320c27f654c830af990320c2bd640c830db948320c36d520c830f34c8320c2fa600c830be580320c39e640c830e7590320c2de620c830f3988320c3ce520c830d7548320c3cd520c830f3d08320c3cc420c830b7984320c3da600c830b7580320c3d9600c830ddd46510c27e64944309f592510c27e62944309f58a510c27f64544309f191510c27f62544309f189510c2be6414430af590510c2ee6214430bb588510c37551144309fd97410c27e65d04309f597410c33e54d0430cf553410c2de63d0430b758f410c27f65904309f996410c27d6590430dd946410c3755190430be982410c2f960904309fd95410c27d65504309f195410c33e5450430cf551410c2df6350430b718d410c3765150430dd545410c2fb6050430be181410c27f65104309f994410c27d6510430dd947310c37551cc430be983310c2f960cc4309f596310c2ee628c430bb58a310c2dd658c430d7596310c2de628c430f398a310c2ce628c430f358a310c2de618c430d7546310c2dd608c4309fd95310c2be640c430af590310c376510c430dd544310c3d5310c430be980310c2f9600c430e7990310c39d640c430b7988310
  | 22 => 0x5309f196414c33f5490530cf152414c36f5290530db14a414c3775190530dd146414c27f65505309f995414c27c6550530cfd51414c33c5450530dbd49414c36c5250530ddd45414c37451505309f994414c27d65105309f194414c33f5410530cf150414c2de6310530b758c414c36f5210530db148414c3775110530dd144414c27e65cc530cfd53314c33c54cc530dbd4b314c36c52cc530dd147314c33f548c530cf152314c2ee628c530bb58a314c36f528c530db14a314c377518c530dd146314c2fa608c530be582314c33f544c530cf151314c36f524c530db149314c377514c530dd145314c2fb604c530be181314c27e650c530af990314c2bd640c530cfd50314c33c540c530dbd48314c36c520c530ddd44314c27e65c85309f597214c27c65c8530cfd53214c33c54c8530dbd4b214c36c52c8530ddd47214c37451c85309f996214c27d65885309f196214c33f5488530cf152214c36f5288530db14a214c3775188530dd146214c27f65485309f995214c27c6548530cfd51214c33c5448530dbd49214c36c5248530ddd45214c37451485309f994214c27d65085309f194214c33f5408530cf150214c36f5208530db148214c3775108530dd144214c3e52108530be980214c2f960085309f997404c33f54d0130cf153404c2de63d0130b758f404c36f52d0130db14b404c37751d0130dd147404c27e6590130cfd52404c33e5490130cf552404c33c5490130dbd4a404c36c5290130ddd46404c3745190130af996404c33e65901308f996404c33f5290130ebd4a404c32f5290130cf14a404c3ac5290130cb14a404c33f5190130edd46404c3375190130cf146404c3b45190130cd146404c2be60901309fd95404c27d65501309f195404c33f5450130cf151404c2df6350130b718d404c36f5250130db149404c3775150130dd145404c27e6510130cfd50404c33e5410130cf550404c33c5410130dbd48404c36c5210130ddd44404c3745110130af994404c33e65101308f994404c33f5210130ebd48404c32f5210130cf148404c3ac5210130cb148404c33f5110130edd44404c3375110130cf144404c3b45110130cd144404c2be6010130ee980404c2be64cc130af593304c33f54cc130cf153304c36f52cc130db14b304c37751cc130dd147304c3ba40cc130ee103304c3ba64cc130ee593304c3bb54cc130de953304c37854cc130ee153304c33854cc130fad4b304c3e852cc130fcd47304c3f051cc130cfd52304c33c548c130dbd4a304c36c528c130ddd46304c374518c130e7d52304c39c548c130f3d4a304c35c528c130f314a304c34c528c130f5d46304c35c518c130f5146304c354518c130f6d42304c39e408c130e7102304c27e63d5030d798f540c27e62d50309f58b540c27e61d50309f587540c27e
  | 23 => 0xf151524c2f76154930bd185524c33f5414930cf150524c36d52149309f990524c27d64149309f984524c27d6114930bb994524c36e6514930dbd50524c3af5414930cbd50524c36e5414930db550524c36c5414930eb150524c32c5414930dbd90524c36e6414930db590524c36c6414930dbd8c524c36f4314930db90c524c36d4314930db10c524c36f6114930db984524c36d6114930db184524c36f6014930db580524c36d30149309f997424c27d65d09309f197424c33f54d0930cf153424c36f52d0930db14b424c27e65909309f596424c27c6590930cfd52424c33c5490930dbd4a424c36c52909309fd95424c27e65509309f195424c33f5450930cf151424c36f5250930db149424c27e65109309f594424c27c6510930cfd50424c33c5410930b798c424c2dd6310930dbd48424c36c52109309f997324c33f54cc930cf153324c36c52cc930cfd52324c33c548c930dbd4a324c36c528c930bd986324c2f5618c930be982324c2f9608c930cfd51324c33c544c930dbd49324c36c524c930bed81324c2f8604c9309f994324c2be640c930af590324c33f540c930cf150324c36f520c930cfd53514c33c54d4530dbd4b514c36c52d45309f993514c27d64d45309f98b514c27d62d4530ddd53514c3b754d4530cdd53514c37654d4530dd553514c37454d4530ed153514c33454d4530ddd4b514c3e752d4530d9d4b514c37652d4530dd54b514c37452d4530f914b514c36452d4530ddd93514c37664d4530dd593514c37464d4530ddd8f514c37743d4530dd90f514c37543d4530dd10f514c37762d4530dd98b514c37562d4530dd18b514c37742d4530dd90b514c37542d4530dd10b514c37732d4530dd8cb514c37532d4530dd0cb514c37760d4530dd583514c2be6494530af592514c33f5494530cf152514c2ee6294530bb58a514c36f5294530db14a514c3775194530afd91514c2bc6454530cfd51514c33c5454530bbd89514c2ec6254530dbd49514c36c5254530cfd50514c33c5414530dbd48514c36c5214530dd544514c27e64145309f590514c27e62145309f588514c2f66514530dd994514c3775414530edd50514c3375414530dd950514c3755414530dd150514c3b45414530cd150514c3775214530f9d48514c3675214530dd948514c3755214530dd148514c3e45214530d9148514c3776414530dd990514c3756414530dd190514c3776314530ddd0c514c3764314530dd50c514c3744314530ddd88514c3766214530dd588514c3746214530ddd08514c3764214530dd508514c3744214530ddcc8514c3763214530dd4c8514c3743214530ddd80514c3756014530dd4c0514c27e65d05309f597414c27c65d0530cfd53414c33c54d0530dbd4b414c36c52d0530ddd47414c37451d05309f996414c27d6590
  | 24 => 0x218c27d65486309f195218c2df6348630b718d218c36e5248630db549218c3cc3248630dd945218c3755148630f50c5218c27f65086309f994218c27d6508630b7d8c218c2dc6308630f9484218c2fa6008630be580218c33e5490230cf552408c2de6390230b758e408c33e6590230cf596408c39e6390230e758e408c33e5290230cf54a408c39e3290230e70ca408c33e5190230cf546408c39e3190230e70c6408c33e5410230cf550408c2de6310230b758c408c33e6510230cf594408c39e6310230e758c408c33e5210230cf548408c39e3210230e70c8408c33e5110230cf544408c39e3110230e70c4408c3ba6010230af993308c2bd64cc230ee903308c3b840cc230b7597308c35d65cc230e7993308c39d64cc230b798b308c2de61cc230e7903308c39c40cc230be597308c37965cc230ee993308c3b964cc230de953308c37854cc2309f98b544c27d62d51309f987544c27d61d5130cfd8f544c33d63d5130cfd8b544c33e62d5130cf58b544c33c62d5130cfd87544c33e61d5130cf587544c33c61d5130cfd83544c33d60d5130cfd52544c2ee6295130bb58a544c2f66195130bd586544c27e64951308f992544c27d6395130d758e544c27e6295130db98a544c26e62951309f58a544c36d62951309b58a544c27e6195130dd986544c27661951309f586544c37561951309d586544c27d6095130de582544c2ef6255130bb189544c2f76155130bd185544c33f64551309fd8d544c35f63551309fd89544c36f62551309bd89544c27c6255130db189544c26c62551309fd85544c37761551309dd85544c27c6155130dd185544c27461551309fd81544c37b60551309ed81544c27e6515130cf550544c33e64151309f98c544c27c63151309f988544c27d62151309f984544c27d6115130af994544c33e65151308f994544c33f6315130cf58c544c33f6215130cf988544c33d6215130cf188544c33f6115130cf984544c33d6115130cf184544c33f6015130cf580544c33d30151309f997434c33f54d0d30cf153434c2fa60d0d30be583434c27e6590d30cfd52434c33c5490d309f195434c33f5450d30cf151434c2ef6250d30bb189434c2f76150d30bd185434c2fb6050d30be181434c27e6510d30cfd50434c33c5410d30e750c434c33f54d4930cf153524c27e64d49309f593524c27e61d49309f587524c36f54d4930ebd53524c32f54d4930db953524c36d54d4930db153524c3ac54d4930cb153524c36f64d4930db993524c36d64d4930db193524c36f63d4930dbd0f524c36e43d4930db50f524c36c43d4930dbd87524c36e61d4930db587524c36c61d4930dbd83524c36d60d4930af992524c2bd6494930cfd52524c33c5494930dbd4a524c2f66194930bd586524c2bf6454930af191524c33f5454930c
  | 25 => 0x26e62d52309f58b548c36d62d52309b58b548c27e61d5230dd987548c27661d52309f587548c37561d52309d587548c37a60d5230cfd52548c27e62952309f58a548c27e61952309f586548c33f64552309fd89548c27c62552309fd85548c27c6155230cf550548c33e6415230d758c548c27e62152309f588548c27e61152309f584548c37a6015230cf953438c33d54d0e30be983438c2f960d0e30cfd52438c33c5490e30cf951438c33d5450e30bbd89438c2ec6250e30bdd85438c2f46150e30bed81438c2f86050e30cfd50438c33c5410e30af992528c2bd6494a30dbd4a528c27e6494a30cf992528c23e6494a309f592528c33d6494a308f592528c27e6194a309f586528c27f6454a309f191528c27f6154a309f185528c36d5214a30bd984528c2f56114a309fd97428c27e65d0a309f597428c33f54d0a30cf153428c2de63d0a30b758f428c36e52d0a30db54b428c27f6590a309f996428c27d6590a309fd95428c27d6550a309f195428c33f5450a30cf151428c2df6350a30b718d428c27f6510a309f994428c27d6510a30db948428c36d5210a30db94a328c36d528ca30bd986328c2f5618ca30be982328c2f9608ca30f394a328c35d528ca30f354a328c2de618ca30f5986328c2d6618ca30f5586328c3da608ca30b7582328c3d9608ca30db949328c36d524ca30bed81328c2f8604ca30af990328c2bd640ca30f34c8328c2dd650ca30d7594328c39e640ca30e7590328c3ce620ca30f3d48328c35d520ca30f3148328c3cf420ca30f3108328c2de610ca30b7580328c2be6494630af592518c37751946309f992518c33e64946308f992518c27d6494630cf592518c23d64946309f98a518c27d62946309fd91518c27c64546309fd89518c27c6254630bb988518c2ed6214630dd544518c27f65d06309f997418c27d65d0630cfd53418c33c54d0630b798f418c2dd63d0630dd947418c37551d06309fd96418c27e65906309f596418c27f65506309f595418c27c6550630cfd51418c33c5450630b7d8d418c2dc63506309fd94418c27e65106309f594418c3765110630dd544418c2ee628c630bb58a318c376518c630dd546318c2fa608c630be582318c2de628c630f398a318c2ce628c630f358a318c3d6518c630d7546318c3d5518c630f6982318c2dd608c630f6582318c376514c630dd545318c2fb604c630be181318c2be640c630af590318c3d5310c630b7594318c35d650c630e7990318c39d640c630b7988318c3d6610c630f5d44318c35d510c630f5144318c3d7410c630f5104318c2dd600c6309fd97218c27e65c86309f597218c2de63c8630b758f218c36e52c8630db54b218c3cc32c86309fd96218c27e65886309f596218c2de6388630b758e218c3765188630dd546218c3d431886309fd95
  | 26 => 0x40cb30db94832cc36d520cb30be98032cc2f9600cb30af99351cc2bd64d4730cf95351cc33d54d4730bb98b51cc2ed62d4730cf95251cc33d5494730bb98a51cc2ed6294730ddd4651cc27e64947309f59251cc27e6294730db98a51cc26e62947309f58a51cc36d62947309b58a51cc33e5454730cf55151cc27f64547309f19151cc27f62547309f18951cc2be6414730af59051cc33e5414730cf55051cc37551147309fd9741cc27e65d07309f59741cc33e54d0730cf55341cc27f65907309f99641cc27d6590730cf95241cc33d5490730be98241cc2f960907309fd9541cc27d65507309f19541cc33e5450730cf55141cc2fb6050730be18141cc27f65107309f99441cc27d6510730cf95041cc33d5410730b798c41cc2dd6310730cf95331cc33d54cc730dd94731cc37551cc730be98331cc2f960cc730cf95231cc33d548c730bb98a31cc2ed628c730cf95131cc33d544c730af99031cc2bd640c730cf95031cc33d540c730dd94431cc375510c730be98031cc2f9600c7309fd9721cc27e65c87309f59721cc33e54c8730cf55321cc37651c8730dd54721cc27f65887309f99621cc27d6588730cf95221cc33d5488730db94a21cc36d52887309fd9521cc27d65487309f19521cc33e5448730cf55121cc2fb6048730be18121cc27f65087309f99421cc27d6508730cf95021cc33d5408730db94821cc36d5208730dd94421cc3755108730f948421cc33e54d0330cf55340cc2de63d0330b758f40cc2f965d0330de59740cc37b54d0330ee95340cc37954d0330ee55340cc3da63d0330be58f40cc3d963d0330cfd5240cc33e5490330cf55240cc33c5490330af59640cc33d6590330cf94a40cc33d5290330cf94640cc33d5190330cf95140cc33d5450330b7d8d40cc2dc6350330cfd5040cc33e5410330cf55040cc33c5410330ee50040cc2bd6510330cf59440cc33e5210330cf54840cc33e5110330cf54440cc3ba6010330be59440cc3796510330ee99040cc37b5410330eed5040cc3ba5410330de55040cc3b95410330ce55040cc3b85410330be58c40cc3bb4310330ee90c40cc3b94310330ee10c40cc3bb4210330ee90840cc3b94210330ee10840cc3bb4110330ee90440cc3b94110330ee10440cc3b96510330ae59440cc3396510330eed8c40cc3ba6310330ee58c40cc3b86310330eed8840cc3ba6210330ee58840cc3b86210330eed4840cc3ba5210330ee54840cc3b85210330eecc840cc3ba3210330ee4c840cc3b83210330eed8440cc3ba6110330ee58440cc3b86110330eed4440cc3ba5110330ee54440cc3b85110330eecc440cc3ba3110330ee4c440cc3b83110330eec8440cc3ba2110330ee48440cc3b82110330bb98b548c2ed62d5230bd987548c2f561d5230d758f548c27e62d5230db98b548c
  | 27 => 0x40ae98021102bd6008440ee58021102b96008440af98e50102bd6394040cf94e501033d5394040af98a50102bd6294040cf94a501033d5294040af98650102bd6194040cf946501033d5194040cf98e501033d6394040cf98a501033d6294040cfcca501033e3294040cf4ca501033c3294040cf986501033d6194040cfcc6501033e3194040cf4c6501033c3194040cfc86501033e2194040cf486501033c2194040ce98250103b96594040eed8e50103ba6394040ae98e50103b96394040ee18e50103bb5394040ee94e50103b95394040ee14e50103bb6294040ee98a50103b96294040ee18a50103bb5294040ee94a50103b95294040ee14a50103bb3294040ee8ca50103b93294040ee0ca50103bb6194040ee98650103b96194040ee18650103bb5194040ee94650103b95194040ee14650103bb3194040ee8c650103b93194040ee0c650103bb2194040ee88650103b92194040ee086501035e63d53309f98b54cc27d62d53309f98754cc27d61d5330de58354cc33f54953309f98a54cc27d62953309f98654cc27d6195330eed8254cc33e6395330cf18e54cc33f6295330cf98a54cc33d6295330cf18a54cc33f6195330cf98654cc33d6195330cf18654cc33f6095330cf58254cc33f64553309fd8954cc27c62553309fd8554cc27c6155330ded8154cc33f6555330eed8154cc33e6355330cf18d54cc33f6255330cf98954cc33d6255330cf18954cc33f6155330cf98554cc33d6155330cf18554cc33f6055330ced8154cc33d6055330cf55054cc33e6415330d798c54cc27e62153309f58854cc27e61153309f58454cc3796015330cf95343cc33d54d0f30cf95243cc33d5490f30be98243cc2f96090f30cf95143cc33d5450f30bbd8943cc2ec6250f30bdd8543cc2f46150f30be18143cc33e5410f30cf55043cc39d4310f30be98043cc2f96010f30af99352cc2bd64d4b30cf95352cc33d54d4b30bd98752cc2f561d4b30cf95252cc33d5494b30dbd4a52cc2f66194b30bd58652cc27e6494b309f59252cc27e6194b30dd98652cc2766194b309f58652cc3756194b309d58652cc33e5454b30cf55152cc27f6454b309f19152cc27f6154b309f18552cc2be6414b30af59052cc33e5414b30cf55052cc36d5214b309fd9742cc27e65d0b309f59742cc33e54d0b30cf55342cc27f6590b309f99642cc27d6590b30cf95242cc33d5490b30be98242cc2f96090b309fd9542cc27d6550b309f19542cc33e5450b30cf55142cc2fb6050b30be18142cc27f6510b309f99442cc27d6510b30cf95042cc33d5410b30b798c42cc2dd6310b30cf95332cc33d54ccb30db94b32cc36d52ccb30be98332cc2f960ccb30cf95232cc33d548cb30bd98632cc2f5618cb30cf95132cc33d544cb30af99032cc2bd640cb30cf95032cc33d5
  | 28 => 0x18532102bf604c840eed8132102bb604c840af18132103b8604c840ae18132102bf650c840af994321033e650c8408f99432102bd650c840cf594321023d650c840af19432102be630c840af98832103af520c840eb148321039f320c840eb8c8321039d320c840eb4c832102be610c840af58432102be600c840af58032102be63d4440af58f511033f53d4440cf54f51102be62d4440af58b51102be60d4440ee98351102ba60d4440af59651102be6394440af58e51102be6294440af58a511033f5194440edd4651102bf6354440af18d511033f5354440cf54d51102bf6254440af18951103b75154440cf94551102be6314440e798c511029e6314440af58c511039d6314440a758c51102be6214440eb98851102ae6214440af58851103ad6214440ab58851102be6114440cfd4451103b65114440cf54451103b55114440af98051103ba6014440ae98051102bf65cc440af99731102bd65cc440af197311039e53cc440e754f31102be62cc440af58b31103b751cc440ed14731102be60cc440af58331102bf658c440af99631102bd658c440af19631102bd638c440af98a31103ae628c440ab98a31102bd628c440eb58a31102ad628c440af98631103b6518c440ed546311039f318c440edcc631102be608c440ee98231102ba608c440af58231103b9608c440ae58231102bf654c440af99531102bd654c440af195311039e534c440e754d31102bf624c440af18931103b6514c440ed54531103b7314c440e78c531102bf604c440eed8131102bb604c440af18131103b8604c440ae18131102bf650c440af994311033e650c4408f99431102bd650c440cf594311023d650c440af19431102be630c440af98831102bd620c440af98431103b7510c440ed144311039f310c440ed8c4311039d310c440ed4c431102be600c440af58031102bf65c8440af99721102bd65c8440af19721102bf63c8440af98f21102bd63c8440af18f21103ae52c8440eb54b21103af32c8440eb0cb21102be60c8440af58321102bf6588440af99621102bd6588440af19621102bf6388440af98e21102bd6388440af18e21102bd6288440af98621103b65188440ed54621103b73188440ed0c621103af2188440edc8621102be6088440af58221102bf6548440af99521102bd6548440af19521102bf6348440af98d21102bd6348440af18d21103ae5248440eb54921103af3248440eb0c921103b65148440ed54521103b73148440ed0c521103b72148440eb88521102bf6048440eed8121102bb6048440af18121103b86048440ae18121102bf6508440af99421102bd6508440af19421102bf6308440af98c21102bd6308440af18c21102be6208440af98421103af2108440ed88421103ad2108440ed48421103a52108440af98021103ba60084
  | 29 => 0x1102bc6448440db949211036d5248440dd94521103755148440bed8121102f860484409fd94211027e65084409f59421102bf6408440af99021102bd6408440af19021103e52108440be98021102f96008440cfd0e501033e4394040cf50e501033c4394040cfd0a501033e4294040cf50a501033c4294040cfd06501033e4194040cf506501033c4194040af98f40102bd63d0040af98b40102bd62d0040af98740102bd61d0040af592401033e5490040be592401037a5490040ee95240102fa6390040eed0e40103ba4390040ee50e40103b84390040eed0a40103ba4290040ee50a40103b84290040eed0640103ba4190040ee50640103b841900409fd9540102bf6550040cfd95401023f6550040afd8d40102bc6350040afd8940102bc6250040afd8540102bc6150040afd81401033e5050040bed95401037b65500409ed9540102fb6450040eed91401037a5450040ee95140102f86350040ee90d40103b84350040af98b53102bd62d4c40af98753102bd61d4c40af98353103ba60d4c40ae98353102bd6594c40cfd4e531039f5394c40af98a53102bd6294c40af98653102bd6194c40ee182531039f5354c40cf94d53102bf6254c40ebd8953102af6254c40af18953103ac6254c40ab18953102bf6154c40edd8553102b76154c40af18553103b46154c40ad18553103b86054c40af98c531033f5314c40e794c531033d5314c40e754c531031d5314c40af98853103ae6214c40ab98853102bd6214c40eb58853102ad6214c40af98453103b66114c40ad98453102bd6114c40ed58453102b56114c40af98053103ba6014c40ae98053102be63d4840af58f521033f53d4840cf54f52102be61d4840af58752102be60d4840ee98352102ba60d4840af59652102be6394840af58e521033f5294840ebd4a52102be6194840af58652102bf6354840af18d521033f5354840cf54d52103af5254840cf94952102bf6154840af18552102be6314840e798c521029e6314840af58c521039d6314840a758c52102be6214840cfd4852103ae5214840cf54852103ad5214840af98452103b66114840ad98452102bd6114840ed58452102b56114840af98052103ba6014840ae98052102bf65cc840af99732102bd65cc840af197321039e53cc840e754f32103af52cc840eb14b32102be61cc840af58732102be60cc840af58332102bf658c840af99632102bd658c840af19632102bd638c840af98a32103ae528c840eb54a321039f328c840ebcca32102be618c840ed98632102b6618c840af58632103b5618c840ad58632102be608c840ee98232102ba608c840af58232103b9608c840ae58232102bf654c840af99532102bd654c840af195321039e534c840e754d32103ae524c840eb54932103af324c840e78c932102bf614c840af
  | 30 => 0xbd6190840af582421027f6550840afd95421033f6550840afd8d42102bc6350840cf54d42103af6250840cf94942102bf6150840af18542102bf6050840af990421036e5210840db54842102fa6010840be58042102be6310840af58c42102be6210840eb98842103ae5210840cf54842103ad5210840af98442102bd6110840ee98042102bd6010840ee580421027f65cc8409f997321027d65cc840afd9332102be64cc840af59332102bc64cc840d794f321035d53cc840ebd0b32103ac42cc8409fd96321027e658c8409f59632102bf648c840af99232102bd648c840af192321036e528c840db54a32102f6618c840bd58632102fa608c840be582321027f654c8409f595321027c654c840afd9132102be644c840af59132102bc644c840d794d321035d534c840db949321036d524c840bed8132102f8604c8409fd94321027e650c8409f59432102bf640c840af99032102bd640c840af19032103af420c840eb108321037751944409f98e511027d63944409f98a511027d62944409fd8d511027c6354440cfd0d511033d43544409fd89511027c6254440b798c51102dd6314440bb98851102ed6214440dd544511037651d0440dd54741102fa60d0440be58341102be63d0440af58f411033d53d0440af98b41102bd62d0440cf94741103b651d0440ed54741103ba60d0440af58341103b960d04409f59641102bd6490440af596411033d6590440af98e41102bd6390440af98a41102bd6290440af986411033d5190440af582411027f6550440afd95411033f6550440afd8d41102bc6350440cf54d41102bf6250440af18941103b76150440cf94541102bf6050440af99041103765110440dd54441102fa6010440be58041102be6310440af58c41102be6210440af58841102be6110440ed98441103b65110440cf54441103b55110440ee98041102bd6010440ee580411027f65cc4409f997311027d65cc440afd9331102be64cc440af59331102bc64cc440d794f311035d53cc440edd0731103b441cc4409fd96311027e658c4409f59631102bf648c440af99231102bd648c440af19231102ee628c440bb58a3110376518c440dd54631102fa608c440be582311027f654c4409f595311027c654c440afd9131102be644c440af59131102bc644c440d794d311035d534c440dd9453110375514c440bed8131102f8604c4409fd94311027e650c4409f59431102bf640c440af99031102bd640c440af19031103b7410c440ed104311027f65c84409f997211027d65c8440afd9321102be64c8440af59321102bc64c8440db94b211036d52c84409fd96211027e65884409f59621102bf6488440af99221102bd6488440af19221103765188440dd546211027f65484409f595211027c6548440afd9121102be6448440af5912
  | 31 => 0xd45409f58f515027e62d45409f58b51503775194540b7d8d51502dc6354540bbd8951502ec6254540dd544515027e63145409f58c515027e62145409f588515027e65d0540ddd4641503745190540be98241502f96090540ddd4541503745150540bed8141502f860505409f994415027e65cc5409f597315027c65cc540ddd47315037451cc5409f996315027d658c5409f196315035f538c540d714e31502ee628c540bb58a315027f654c5409f995315027c654c5409f994315027d650c5409f19431502be640c540af590315035f530c540d714c3150377510c540dd144315027e65c85409f597215027c65c8540ddd47215037451c85409f996215027d65885409f196215036f5288540db14a215027f65485409f995215027c65485409f994215027d65085409f194215036f5208540db14821503775108540dd14421503e52108540de14f405033f5390140cf14e405033f5290140cf14a405033f5190140cf14640503bb5090140d7d4e531027e6294c409f58a531027e6194c409f58653102ef6254c40bb18953102f76154c40bd185531027f6254c40dbd89531026f6254c409f189531036c6254c409b189531027f6154c40ddd8553102776154c409f18553103746154c409d18553103786054c40d754c53102ee6214c40bb58853102f66114c40bd584531035e53d0c40d754f43102fa60d0c40be583431033e53d0c40e794f431039d53d0c40af98b43102bd62d0c40af98743102bd61d0c40ee98343102bd60d0c40ee58343102b960d0c409f59643102bd6490c40af596431033d6590c40af98e431033d5390c40af98a43102bd6290c40af98643102bd6190c40eed8243102bd6090c40ee182431027f6550c40bbd8943102ec6250c40bdd8543102f46150c40bed8143102bf6550c40cfd95431039f6350c40cf94d43102bf6250c40ebd8943102af6250c40af18943103ac6250c40ab18943102bf6150c40edd8543102b76150c40af18543103b46150c40ad18543102bf6050c40eed8143102bb6050c40ee18143102be6410c40d794c431035d5310c40be98043102f96010c40af98c431039e6310c40e794c431033d5310c40e754c431031d5310c40af98843102bd6210c40af98443102bd6110c40ee98043102bd6010c40ee580431036f52948409f98e521027d63948409f986521027d61948409fd8d521027c6354840cfd0d521033d43548409fd85521027c6154840b798c52102dd6314840db54852102f66114840bd584521036e52d0840db54b42102fa60d0840be58342102be63d0840af58f421033d53d0840cf94b42103ae52d0840eb54b42102be61d0840af58742103ba60d0840af58342103b960d08409f59642102bd6490840af596421033d6590840af98e42102bd6390840af98a421033d5290840af98642102
  | 32 => 0xcfd4d519033d5354640afd8951902bc6254640edd45519033e5154640af98c51902bd6314640af98851903ae6214640ab98851902bd6214640eb58851902ad6214640cfd4451903b65114640cf54451903b55114640af98051903ba6014640ae98051902bf65cc640af99731902bd65cc640af19731902be62cc640af58b31903b651cc640ed54731902be60cc640af58331902bf658c640af99631902bd658c640af19631902be628c640eb98a31902ae628c640af58a31903ad628c640ab58a319039f318c640edcc631902be608c640af58231902bf654c640af99531902bd654c640af19531902bf624c640af18931903b7314c640e78c531902bf604c640af18131902bf650c640af994319033e650c6408f99431902bd650c640cf594319023d650c640af19431902be620c640af58831903b6510c640ed544319039f310c640ed8c4319039d310c640ed4c431902be600c640af58031902bf65c8640af99721902bd65c8640af19721902bf63c8640af98f21902bd63c8640af18f21903ae52c8640eb54b21903af32c8640eb0cb21902be60c8640af58321902bf6588640af99621902bd6588640af19621902bf6388640af98e21902bd6388640af18e21903b65188640ed54621903b73188640ed0c621903af2188640edc8621902be6088640af58221902bf6548640af99521902bd6548640af19521902bf6348640af98d21902bd6348640af18d21903ae5248640eb54921903af3248640eb0c921903b65148640ed54521903b73148640ed0c521903b72148640eb88521902bf6048640af18121902bf6508640af99421902bd6508640af19421902bf6308640af98c21902bd6308640af18c21903af2108640ed88421903ad2108640ed48421903a52108640af98021902bd60086409f98b535027d62d4d409f987535027d61d4d40d7d4e53502ef6254d40bb18953502f76154d40bd185535035d5314d409f988535027d6214d409f984535027d6114d409f997435035f5390d40d714e43502fa6090d40be582435035f5350d40d714d43502ef6250d40bb18943502f76150d40bd18543502fb6050d40be181435027e6510d40e750c435027e63d49409f58f525027e61d49409f587525036f5294940b7d8d52502dc6354940bdd8552502f46154940db548525027e63149409f58c525027e61149409f584525027e65d0940dbd4a425036c5290940be98242502f96090940dbd49425036c5250940bed8142502f860509409f994425027e65cc9409f597325027c65cc940dbd4b325036c52cc9409f996325027d658c9409f196325035f538c940d714e32502f6618c940bd586325027f654c9409f995325027c654c9409f994325027d650c9409f19432502be640c940af590325035f530c940d714c325036f520c940db148325027e63
  | 33 => 0x9231902bc648c640bb98a31902ed628c6409fd95319027d654c6409f19531902bf644c640af99131902bd644c640af191319027f650c6409f994319027d650c640afd9031902be640c640af59031902bc640c640dd9443190375510c640edd0431903b4410c6409fd97219027e65c86409f59721902bf64c8640af99321902bd64c8640af193219036e52c8640db54b219027f65886409f996219027d6588640afd9221902be6488640af59221902bc6488640dd946219037551886409fd95219027d65486409f19521902bf6448640af99121902bd6448640af191219036e5248640db54921903765148640dd545219027f65086409f994219027d6508640afd9021902be6408640af59021902bc6408640f948421902bd65d0240cf59740902be63d0240af58f40902be62d0240af58b40902be61d0240af58740902f965d0240de597409037a53d0240af98b53903ae62d4e40ab98b53902bd62d4e40eb58b53902ad62d4e40af98753903b661d4e40ad98753902bd61d4e40ed58753902b561d4e40af98353903ba60d4e40ae983539033f5394e40e7d4e539031f5394e40af98a53902bd6294e40af98653902bd6194e40e7d4d539033e5354e40afd8953902bc6254e40afd8553902bc6154e40cfd4c539039e5314e40cf54c539039d5314e40af98853902bd6214e40af98453902bd6114e40af98053903ba6014e40ae98053902be63d4a40af58f529033f53d4a40cf54f52902be61d4a40af58752902be60d4a40ee98352902ba60d4a40af98e52902bd6394a40cfd4a52903af5294a40af98652902bd6194a40afd8d52902bc6354a40cfd4d529033d5354a40ebd49529033e5254a40afd8552902bc6154a40af98c52902bd6314a40cfd4852903ae5214a40cf54852903ad5214a40af98452903b66114a40ad98452902bd6114a40ed58452902b56114a40af98052903ba6014a40ae98052902bf65cca40af99732902bd65cca40af19732903ae52cca40eb54b32902be61cca40af58732902be60cca40af58332902bf658ca40af99632902bd658ca40af196329039f328ca40ebcca32902be618ca40ed98632902b6618ca40af58632903b5618ca40ad58632902be608ca40af58232902bf654ca40af99532902bd654ca40af19532903af324ca40e78c932902bf614ca40af18532902bf604ca40af18132902bf650ca40af994329033e650ca408f99432902bd650ca40cf594329023d650ca40af19432903ae520ca40eb548329039f320ca40eb8c8329039d320ca40eb4c832902be610ca40af58432902be600ca40af58032902be63d4640af58f519033f53d4640cf54f51902be62d4640af58b51902be60d4640ee98351902ba60d4640af98e51902bd6394640af98a51902bd6294640cfd4651903b75194640afd8d51902bc635464
  | 34 => 0x9035e5350e40d754d43902ef6250e40bb18943902f76150e40bd18543902fb6050e40be181439039f6350e40cf94d439039e5350e40c794d439039d5350e40afd8943903af6250e40abd8943902bc6250e40eb18943902ac6250e40afd8543903b76150e40add8543902bc6150e40ed18543902b46150e40afd8143903bb6050e40ee18143902bd6510e40cf594439039e6310e40cf54c43902be6210e40af58843902be6110e40af58443902bd6010e40dbd4a529027e6394a409f58e529027e6194a409f586529027f6354a409f18d529033f4354a40cf50d529027f6154a409f185529036d5214a40bd98452902f56114a40af597429033d65d0a40af98f42902bd63d0a40cf54f429033e52d0a40af98742902bd61d0a40af583429036e5290a40db54a42902fa6090a40be58242902be6390a40af58e42903ae5290a40cf54a42903ad5290a40af98642902bd6190a40ee98242902bd6090a40ee582429036e5250a40db54942902fb6050a40be18142902bf6350a40af18d429033d5350a40ebd89429033e5250a40eb94942903ad5250a40afd8542902bc6150a40afd8142903bb6050a40ee18142902bd6510a40cf59442902be6310a40af58c42903ae6210a40cf54842902be6110a40af58442902bd6010a409fd97329027e65cca409f59732902bf64cca40af99332902bd64cca40af193329036e52cca40db54b32903af42cca40eb10b329027f658ca409f996329027d658ca40afd9232902be648ca40af59232902bc648ca40bd98632902f5618ca409fd95329027d654ca409f19532902bf644ca40af99132902bd644ca40af191329027f650ca409f994329027d650ca40afd9032902be640ca40af59032902bc640ca40db948329036d520ca40ebd0832903ac420ca40ddd46519027e63946409f58e519027e62946409f58a519027f63546409f18d519033f4354640cf50d519027f62546409f18951902ee6214640bb58851903755114640af597419033d65d0640af98f41902bd63d0640cf54f41902be62d0640af58b419033e51d0640af58341903765190640dd54641902fa6090640be58241902be6390640af58e41902be6290640af58a41903b65190640cf54641903b55190640ee98241902bd6090640ee58241903765150640dd54541902fb6050640be18141902bf6350640af18d419033d5350640afd8941902bc6250640edd85419033e5150640ed94541903b55150640afd8141903bb6050640ee18141902bd6510640cf59441902be6310640af58c41902be6210640af58841903b66110640cf54441902bd60106409fd97319027e65cc6409f59731902bf64cc640af99331902bd64cc640af193319037651cc640dd54731903b741cc640ed107319027f658c6409f996319027d658c640afd9231902be648c640af5
  | 35 => 0xe63940219f58e50086bf6454021af19150086df6354021b718d50087e521540219fd91500873f64540218fd91500867c6454021cf191500863c64540219fd8d500875f635402197d8d500867c6354021d718d500865c6354021dbc8550087762154021db48550087752154021d948550087e52114021de54050086ee62d4f40bb58b53d02f661d4f40bd58753d035f5394f409f98a53d027d6294f409f98653d027d6194f409fd8953d027c6254f409fd8553d027c6154f40ded8153d035d5314f40d794f43d035d53d0f40be98343d02f960d0f40bbd8943d02ec6250f40bdd8543d02f46150f40be18143d035e5310f40d754c43d039d4310f40be98043d02f96010f40b798f52d02dd63d4b40bd98752d02f561d4b40dbd4a52d027e6394b409f58e52d027e6194b409f58652d027f6354b409f18d52d027f6154b409f18552d036d5214b40db94b42d036d52d0b40be98342d02f960d0b40db94842d036d5210b40be98042d02f96010b409fd9732d027e65ccb409f59732d036e52ccb40db54b32d027f658cb409f99632d027d658cb40d794e32d035d538cb40bd98632d02f5618cb40be98232d02f9608cb409fd9532d027d654cb409f19532d02fb604cb40be18132d027f650cb409f99432d027d650cb40af99032d02bd640cb40d794c32d035d530cb40db94832d036d520cb40b798f51d02dd63d4740bb98b51d02ed62d4740ddd4651d027e63947409f58e51d027e62947409f58a51d027f63547409f18d51d027f62547409f18951d03755114740dd94741d037551d0740be98341d02f960d0740dd94441d03755110740be98041d02f960107409fd9731d027e65cc7409f59731d037651cc740dd54731d027f658c7409f99631d027d658c740d794e31d035d538c740bb98a31d02ed628c740be98231d02f9608c7409fd9531d027d654c7409f19531d02fb604c740be18131d027f650c7409f99431d027d650c740af99031d02bd640c740d794c31d035d530c740dd94431d0375510c7409fd9721d027e65c87409f59721d037651c8740dd54721d027f65887409f99621d027d6588740db94a21d036d52887409fd9521d027d65487409f19521d02fb6048740be18121d027f65087409f99421d027d6508740db94821d036d5208740dd94421d03755108740f948421d02fa6008740be58021d02ee62d4e40bb58b53902f661d4e40bd587539035f5394e409f98a539027d6294e409f986539027d6194e409fd89539027c6254e409fd85539027c6154e40d754c53902bd65d0e40cf597439033e53d0e40af98b43902bd62d0e40af98743902bd61d0e40af583439035e5390e40d754e43902fa6090e40be582439039e5390e40cf54e439039d5390e40af98a43902bd6290e40af98643902bd6190e40ee98243902bd6090e40ee58243
  | 36 => 0x4c21d754c53086fa6014c21be580530867e6414c21cf990530863e6414c219f590530873d6414c218f590530867e6314c21d798c530867e6214c21db988530867e6114c21dd984530867e6014c21de980530867a6014c219f58053087796014c219e580530867f65d0c219f997430867d65d0c219f197430873e54d0c21cf553430867f6590c219f996430867d6590c219f196430867f6550c219f995430867d6550c219f195430873e5450c21cf55143086ef6250c21bb18943086f76150c21bd18543086fb6050c21be181430867f6510c219f994430867d6510c219f19443086ee6210c21bb58843086f66110c21bd584430867e64948219f592520867e63948219f58e520867d65d08219fd96420867d6590821cf952420873d5490821bd98642086f561908219fd95420867f65108219f594420873e5410821cf55042087ad4210821bd98442086f561108219f597320876e52cc8219fd96320867d658c821d794e320875d538c821bd98632086f5618c8219fd95320867f650c8219f59432086be640c821af590320875e530c821d754c320876e520c821f34c832086f6610c821bd584320867e64944219f592510867e63944219f58e510867d65d04219fd96410867d6590421cf952410873d5490421bb98a41086ed62904219fd95410867f65104219f994410867d65104219f194410873e5410421cf55041086ee6210421bb58841087b541104219f597310877651cc4219fd96310867d658c421d794e310875d538c421bb98a31086ed628c4219fd95310867f650c4219f994310867d650c4219f19431086be640c421af590310875e530c421d754c31086ee620c421bb5883108776510c421f54c4310876e53c8421db14f21086ee60c8421bb58a210876e5288421dd94e21087745388421bd58a21086e56288421dd94a21087e65288421bd982210867f6548421bbd95210876f65484219bd95210876e5348421db14d21086ef6148421db94521087e74148421f990521087e54148421f910521087e73148421f98c521087e53148421f90c521086ec6048421bdd95210877765484219dd9521087765348421dd14d21086f76248421f9d8921087765248421f994921087e74248421f990921087e54248421f910921087e73248421f98c921087e53248421f90c921086f46048421f9d9521086e76548421d9d9521087e76448421f999121087e56448421f919121087e75448421f995121087e55448421f915121087e76348421f998d21087e56348421f918d21087e75348421f994d21087665348421f954d21087e45348421d914d21087e74348421f990d21087e54348421f910d21087e76048421f998121087e56048421f918121086e46048421af99350086bd64d4021f948750087e52194021ded42500867e64940219f592500867
  | 37 => 0x9f997424873f54d0921cf15342486f661d0921bd587424867e65909219f195424873f5450921cf15142486f76150921bd185424867e65109219f997324875f53cc921d714f32486f661cc921bd587324876e65cc9219b997324876e54cc921db153324876f53cc921f3d4f324876d53cc921f314f32486ee61cc921f998732486e661cc921f958732486ed60cc9219f99632486ee628c921bd986324867c654c921d7d4d324875c534c921bdd8532486f4614c9219f99432486be640c921af59032486ee650c921db99432487ae640c921eb590324876e540c921db15032486ee630c921f398c324876f530c921db54c32487e7610c921bb98432487e4610c921bb580324867e65d0521cfd53414873c54d0521bb98b41486ed62d05219f996414867f65505219f595414867c6550521cfd51414873c5450521bbd8941486ec62505219f994414867e65cc521d7d4f314875c53cc521bb98b31486ed62cc521bd997314877665cc5219d997314877654cc521dd153314877753cc521f5d4f314877553cc521f514f31486f662cc521f998b31486e662cc521f958b31487e732cc521f90cb31486f560cc5219f99631486ee628c521bb58a31486f6618c5219fd95314867d654c5219f195314875f534c521d714d31486ef624c521bb189314867e650c521af99031486bd640c521bd9943148776650c521ed99031487b5640c521dd9503148774540c521bd98c31487d6630c521ddd4c3148775530c521f9d8831486f6620c521f918831487e7320c521f90c831486f5600c521bd98f21486f463c8521f9ccb21487e432c8521bd58321486ee6388521bb18e21487e75188521f9cc621487e43188521bb58221486be64d4121af593504867e64d4121cf993504863e64d41219f593504873d64d41218f593504867e63d41219f58f504877b5094121afd9150486bc6454121b7d8d50486dc6354121de540504867e64141219f590504867e63141219f58c504876f3214121db0c850487773114121dd0c450487772114121db88450486fa60d5021be583540867e63d50219f58f540867e62d5021db98b540867e61d5021dd987540867e60d5021de983540867a60d50219f583540877960d50219e583540867d6595021cfd52540867e63950219f58e540867e60950219f582540873f64550219fd8d540867c63550219fd81540867c6055021cf550540867e6415021cf990540867e63150219f58c540867e6215021db988540867e6115021dd984540867e60150219f580540867e64d4c219f593530867e62d4c21db98b530866e62d4c219f987530877661d4c219d987530867e60d4c219f583530867d6594c21d7d4e530867e6494c219f592530867e6094c219f582530867f6454c219f191530875f6354c219fd81530867c6054c21af99053086bd641
  | 38 => 0x732886f561cca21bd586328875e534ca21d754d32886f7614ca21bd18532886be640ca21af59032887cd320ca21cf952418873d5490621bb98a41886ed6290621cf950418873d5410621bb98841886ed6210621bd597318877565cc621dd953318877454cc621ddd4f318877553cc621bd98b31886f560cc621d794e318875d538c621bb98a31886ed628c621af99031886bd640c621d794c318875d530c621bb98831886ed620c621bd5943188775650c621ed99031887b5640c621dd9503188774540c621f598c3188777530c621f594c3188775530c621f554c3188755530c621bd98831887e6620c621f958831886f5600c621bb597218876d65c8621db94f218876c53c8621bb98321886f565c8621dd59721886f663c8621bd18f21886f560c8621af99350886bd64d4221b798f50886dd63d4221ded42508867e64942219f592508867e63942219f58e50887773194221dd0c650887772194221afd9150886bc64542219fd91508873f64542218fd91508867c6454221cf191508863c64542219fd8d508867c6354221dbc85508877950142219f98f544867d63d51219f983544867d60d5121cfd52544867e64951219f98e544867d63951219f58a544876d62951219f586544877561951219f982544867d6095121b7d8d54486dc6355121bed8154486f86055121cfd91544867f6355121d7d8d544865f63551219f18d544875c63551219718d544867f6255121dbd89544867f6155121ddd85544867f6055121ded81544867b60551219f181544877860551219e181544867e6515121cf550544873e64151219f98c544867d63151219f980544867d60151219f993534867d64d4d21db58b534877561d4d219f983534867d60d4d21d7d4e534867e6494d219f592534867e6394d219f58a534876d6294d219f58653487756194d219f982534867d6094d21afd9153486bc6454d21bed8153486f86054d219fd91534873f6454d218fd91534867c6454d21cf191534863c6454d21d7d8d534867f6254d21dbd89534867f6154d21ddd85534867f6054d21ded81534867b6054d219f18153487786054d219e181534867e6514d21af99053486bd6414d21d754c534867e6414d21cf990534863e6414d219f590534873d6414d218f590534875e6314d219f980534867d6014d219fd97434867e65d0d219f597434867c65d0d21cf953434873d54d0d21d7d4f434875c53d0d21bb98b43486ed62d0d21bd98743486f561d0d219fd96434867e6590d219f596434867c6590d21cfd52434873c5490d219fd95434867e6550d219f595434867c6550d21cf951434873d5450d21bbd8943486ec6250d21bdd8543486f46150d21bed8143486f86050d219fd94434867e6510d219f594434867c6510d21cfd50434873c5410d21d7d4c434875c5310d21
  | 39 => 0x867d6590f219f19643c875e5390f21d754e43c867f6550f219f99543c867d6550f219f19543c873e5450f21cf55143c875e5350f21d754d43c86ef6250f21bb18943c86f76150f21bd18543c86fb6050f21be18143c867f6510f219f99443c867d6510f219f19443c86f66110f21bd58443c873e5490b21cf55242c86f66190b21bd58642c873e5410b21cf55042c86f66110b21bd58442c86ed65ccb21db59732c876e54ccb21db15332c876f53ccb21db54f32c86ee61ccb21bb58332c875e538cb21d754e32c86f6618cb21bd58632c86be640cb21af59032c875e530cb21d754c32c86f6610cb21bd58432c876d650cb21eb99032c87ad640cb21db95032c876c540cb21f398c32c876f530cb21f394c32c876d530cb21f354c32c874d530cb21bb98432c87e6610cb21f958432c86ed600cb21cf95341c873d54d0721bb98b41c86ed62d0721cf95141c873d5450721bbd8941c86ec6250721ed50441c875e53cc721d754f31c86ee62cc721bb58b31c86ee628c721bb58a31c875e534c721d754d31c86ef624c721bb18931c86be640c721af59031c87d5310c721af99350c86bd64d4321b798f50c86dd63d4321ded4250c867e64943219f59250c867e63943219f58e50c876f3294321db0ca50c86bf6454321af19150c867f6454321cfd9150c863f64543219f19150c873c64543218f19150c867f63543219f18d50c877950143219f98f548867d63d5221db58b548877661d52219f983548867d60d5221cfd52548867e63952219f58e548867e60952219f582548873f64552219fd8d548867c63552219fd81548867c6055221cf55054886de6315221b758c548873e64152219f98c548875e63152219798c548867d6315221d758c548865d6315221db588548877661152219f980548867d60152219f993538867d64d4e21db58b538877661d4e219f983538867d60d4e21d7d4e538867e6494e219f592538867e6094e219f582538867f6454e219f191538875f6354e21dd185538867f6054e219f18153886be6414e21af590538875d5314e219f990538873e6414e218f990538867d6414e21cf590538863d6414e21d798c538876d6214e21dd984538867e6014e219f580538867f65d0e219f997438867d65d0e219f197438873e54d0e21cf55343886f661d0e21bd587438867f6590e219f996438867d6590e219f196438875e5390e21d754e438867f6550e219f995438867d6550e219f195438873e5450e21cf551438875e5350e21d754d43886ef6250e21bb18943886f76150e21bd18543886fb6050e21be181438867f6510e219f994438867d6510e219f19443886ee6210e21bb588438873e54d0a21cf55342886f661d0a21bd587428873e5450a21cf55142886f76150a21bd18542887ad4210a21d794f328875d53cca21bd98
  | 40 => 0x6294431db58a510c67d65d0431cf953410c73d54d0431bd597410c77565d0431ddd53410c7b654d0431dd553410c7b554d0431cd553410c6f563d0431dd94f410c7b743d0431ed50f410c6f562d0431bd983410c67f65904319f596410c73e5490431cf552410c6de6390431b758e410c6f661904319fd95410c73e5450431cf551410c67f65104319f994410c67d65104319f194410c73e5410431cf550410c6de6310431b758c410c6f56510431dd594410c6756510431bd990410c7b66410431ddd50410c7b65410431dd550410c7b55410431f598c410c6f56310431f558c410c6d56310431dd94c410c6f56210431bd980410c73e54cc431cf553310c79e54cc431e7553310c7d741cc431f5107310c6de60cc431cf952310c73d548c431b758e310c75e538c431bb98a310c6ed628c431bd992310c6f4648c431ed952310c7b5548c431bd58e310c776538c431f594e310c7e6628c431bd58a310c7e5628c431b958a310c6f6608c4319fd95310c73e544c431cf551310c6df654c431d7d95310c65f654c431e7951310c79d544c431b7d85310c75e514c431f5905310c7d5414c431b7181310c6f7654c431ddd95310c677654c431bd991310c6f4644c431ed951310c7b5544c431bdd8d310c7d7634c431dd94d310c7d6534c431f590d310c7d5434c431bdd89310c7d6324c431f50c9310c6f4604c431af993500c6bd64d4031cf953500c73d54d4031cf952500c73d5494031ded42500c73f64940319f992500c67d6494031cf192500c67e62940319f58a500c6bf6454031af191500c73e5454031cf551500c6ef6254031bb189500c67f6454031cfd91500c63f64540319f191500c73c64540318f191500c67f6254031dbd89500c66f62540319f189500c76c62540319b189500c6be6414031af590500c73e5414031cf550500c6ee6214031bb588500c77950140319f98f54c867d63d5321db98b54c877561d53219f98354c867d60d5321cfd5254c867e63953219f58e54c867e60953219f58254c873f64553219fd8d54c867c63553219fd8154c867c6055321cf55054c86de6315321b758c54c873e64153219f98c54c875e63153219798c54c867d6315321d758c54c865d6315321db98854c877561153219f98054c867d60153219f99353c867d64d4f21db98b53c877561d4f219f98353c867d60d4f21d7d4e53c867e6494f219f59253c867e6094f219f58253c867f6454f219f19153c875f6354f21db18953c867f6054f219f18153c86be6414f21af59053c875d5314f219f99053c873e6414f218f99053c867d6414f21cf59053c863d6414f21d798c53c876e6214f21dd58453c867e6014f219f58053c867f65d0f219f99743c867d65d0f219f19743c873e54d0f21cf55343c86ee62d0f21bb58b43c867f6590f219f99643c
  | 41 => 0x531cfd53414c73c54d0531b798f414c6dd63d05319f996414c67f65505319f595414c67c6550531cfd51414c73c5450531b7d8d414c6dc63505319f994414c77654cc531dd153314c77752cc531bb98a314c6ed628c531f398a314c7cd628c531f5d46314c6be64d4131af593504c67e64d4131cf993504c63e64d41319f593504c73d64d41318f593504c67e62d41319f58b504c77b5094131afd91504c6bc6454131bbd89504c6ec6254131de540504c67e64141319f590504c67e62141319f588504c7773114131d78c4504c67e63d5031d798f540c67e62d50319f58b540c67e61d5031dd987540c67e60d50319f583540c67d6595031cfd52540c67e62950319f58a540c67e60950319f582540c63d6595031ed186540c6be6095031cf98e540c73c6395031cfd8a540c73e6295031cf58a540c73c6295031cf986540c73c6195031cfd82540c73e60950318f982540c73d6095031cf182540c73f64550319fd89540c67c6255031dd185540c67f60550319f181540c73f6555031ed185540c6bc6055031cf98d540c73c6355031cfd89540c73e6255031cf589540c73c6255031cf985540c73c6155031cd185540c73c3155031cfd81540c73e6055031cf581540c73c60550318f181540c6be6415031cf550540c67e6415031cf990540c63e64150319f98c540c75e63150319f988540c67d62150319f984540c77661150319f980540c67d60150319f992530c67d6494c319f597430c73e54d0c31cf553430c67f6590c319f596430c73e5490c31cf552430c6f66190c31bd586430c67f6550c31cf951430c73d5450c31bbd89430c6ec6250c31bdd85430c6fb6050c31be181430c67f6510c319f594430c73e5410c31cf550430c79d4310c31bd984430c6f56110c31af993520c6bd64d4831cf953520c73d54d4831cf952520c73d5494831dbd4a520c67e64948319f592520c77661948319f982520c67d6094831cf951520c73d54548319fd91520c67c64548319fd81520c67c6054831af990520c6bd6414831cf950520c73d5414831db548520c6fa6014831be580520c67f65d08319f997420c67d65d0831cf953420c73d54d08319fd96420c67e65908319f596420c73e5490831cf552420c6f66190831bd586420c67f65508319f595420c67c6550831cf951420c73d5450831b7d8d420c6dc6350831bdd85420c6f461508319fd94420c67e65108319f594420c73e5410831cf550420c6de6310831b758c420c6f66110831bd584420c73e54cc831cf553320c76e52cc831db54b320c6f661cc831bd587320c67d658c831cf952320c73d548c831bd586320c67f654c831cf951320c73d544c831af990320c6bd640c831cf950320c73d540c831db948320c76d520c831f34c8320c6f6610c831bd584320c67e64944319f592510c76e
  | 42 => 0xb548528c67f65d0a319f997428c67d65d0a31db94b428c76d52d0a31bd987428c6f561d0a319fd96428c67e6590a319f596428c76e5290a31db54a428c67f6550a319f595428c67c6550a31b7d8d428c6dc6350a31db949428c76d5250a319fd94428c67e6510a319f594428c6de6310a31b758c428c76e5210a31db548428c76e52cca31db94a328c76d528ca31bd986328c6f5618ca31db949328c76d524ca31bdd85328c6f4614ca31af990328c6bd640ca31db548328c7cd320ca31cfd53418c73c54d0631db94b418c76d52d0631cf952418c73d5490631b798e418c6dd6390631db94a418c76d5290631cfd51418c73c5450631db949418c76d5250631cf950418c73d5410631b798c418c6dd6310631db948418c76d5210631db94b318c76d52cc631b7597318c75d65cc631f394b318c7cd52cc631b7983318c6f565cc631dd597318c77654cc631dd153318c7e652cc631dd54b318c7e552cc631d954b318c6be64d4231af593508c6ee62d4231bb58b508c76e52d4231db54b508c76e5294231db54a508c77b50942319f992508c67d64942319f98a508c67d6294231ddcc6508c6bf6454231af191508c76e5254231db549508c67f6454231cfd91508c63f64542319f191508c73c64542318f191508c67f62542319f189508c6ee6214231bb588508c76e5214231db548508c77950142319f98b544c67d62d51319f983544c67d60d5131cfd52544c67e64951319f58e544c75d63951319f98a544c67d62951319f586544c77561951319f982544c67d6095131bbd89544c6ec6255131bed81544c6f86055131cfd91544c67f6355131d7d8d544c67f6255131dbd89544c66f62551319f189544c76c62551319b189544c67f6155131ddd85544c67761551319fd81544c77b60551319ed81544c67c6055131de181544c67860551319f994544c73d5415131cf990544c67e62151319f588544c67e60151319f580544c67e65d0d31cfd53434c73c54d0d31bd987434c6f561d0d319f996434c67c6550d31cfd51434c73c5450d31bbd89434c6ec6250d31bdd85434c6f46150d31bed81434c6f86050d319f994434c67e64d49319f593524c67e60d49319f583524c76f5294931afd91524c6bc6454931bed81524c6f86054931db548524c67e64149319f590524c67e60149319f580524c67e65d09319f597424c67c65d0931b798f424c6dd63d0931dbd4b424c76c52d0931bd987424c6f561d09319f996424c67d65909319f196424c73f5490931cf152424c67f65509319f995424c67c65509319f994424c67d65109319f194424c73f5410931cf150424c76f5210931db148424c67e65cc931dbd4a324c76c528c931bd986324c6f5618c931dbd49324c76c524c931bdd85324c6f4614c9319f994324c6be640c931af590324c67e65d0
  | 43 => 0x43cc73f5450f31cf15143cc6ef6250f31bb18943cc6f46150f31bed8143cc6f86050f31cf95043cc73d5410f31bd98443cc6f56110f31dbd4a52cc67e6494b319f59252cc7756194b319f98252cc67d6094b319fd9152cc67c6454b319fd8152cc67c6054b31af99052cc6bd6414b31db54852cc67f65d0b319f99742cc67d65d0b31cf95342cc73d54d0b31b798f42cc6dd63d0b319fd9642cc67e6590b319f59642cc76e5290b31db54a42cc6f66190b31bd58642cc67f6550b319f59542cc67c6550b31cf95142cc73d5450b31db94942cc76d5250b31bdd8542cc6f46150b319fd9442cc67e6510b319f59442cc6f66110b31bd58442cc76e52ccb31db54b32cc6f661ccb31bd58732cc6f6618cb31af99032cc6bd640cb31db94832cc76d520cb31bd98432cc6f5610cb31cf95341cc73d54d0731b798f41cc6dd63d0731bd59741cc77565d0731ddd5341cc7b654d0731dd55341cc7b554d0731f598f41cc6f563d0731f558f41cc7b743d0731ed50f41cc6f562d0731bd98341cc73e5450731cf55141cc6df6350731b718d41cc6f56510731dd59441cc7b66410731ddd5041cc7755410731bd58c41cc6f56210731bd98041cc6be64d4331af59350cc6ee62d4331bb58b50cc77b50943319f99250cc67d64943319f98a50cc67d6294331afd9150cc6bc64543319fd9150cc73f64543318fd9150cc67c6454331cf19150cc63c64543319fd8950cc67c6254331de54050cc6ee62d5231bb58b548c6fa60d5231be583548c75d63d52319f98b548c76e62d52319b98b548c67d62d5231db58b548c66d62d5231dd987548c67e60d5231de983548c67a60d52319f583548c77960d52319e583548c73f54952319f98a548c67d62952319f982548c67d6095231cfd91548c67f62552319f189548c67f60552319f181548c73d5415231bb988548c6ed6215231cf990548c75d63152319f988548c76e62152319b988548c67d6215231db588548c66d6215231dd984548c67e60152319f580548c73e54d0e31cf553438c6f661d0e31bd587438c73e5450e31cf551438c6ef6250e31bb189438c6f76150e31bd185438c6fb6050e31be181438c79d4310e31dbd4a528c67e6494a319f592528c67e6094a319f582528c76f5494a31db952528c76d5494a31db152528c76f6494a31db992528c76d6494a31db192528c76f6394a31dbd0e528c76e4394a31db50e528c76c4394a31db986528c76c6194a31dbd82528c76e6094a31db582528c76c6094a319fd91528c67c6454a319fd81528c67c6054a31dbd95528c76f5454a31db951528c76d5454a31db151528c76f6454a31db991528c76d6454a31db191528c76d6354a31dbd0d528c76e4354a31db50d528c76c4354a31db985528c76c6154a31dbd81528c76e6054a31db581528c76c6054a31d
  | 44 => 0x6f461509419f994425067e65cc9419f597325067c65cc941af99332506bd64cc941dbd4b325076c52cc941bd98732506f561cc9419f996325067d658c9419f196325075f538c941d714e32506f6618c941bd586325067f654c9419f995325067c654c9419f994325067d650c9419f19432506be640c941af590325075f530c941d714c325076f520c941db148325077453d0541edd0f41507b543d0541af58e41507b75190541af982415067e63d41419f58f505067e62d41419f58b505077b5094141b7d8d50506dc6354141bbd8950506ec6254141de540505073f64141419f98c505067d6314141cfd0c505073d43141419f988505067d6214141cf90450506ee62d4c41bb58b531075f5394c419f98a531067d6294c419f982531067d6094c419fd89531067c6254c41dd185531067f6054c419f181531075d5314c41cf953431075e53d0c41d754f43106f661d0c41bd587431067d6590c419fd95431073e5450c41bbd8943106ec6250c41bdd8543106fb6050c41be181431075e5310c41d754c431079d4310c41bd98443106f56110c41b798f52106dd63d4841dbd4a521067e63948419f58e521067e60948419f582521067f63548419f18d521067f60548419f181521076d5214841db94b421076d52d0841bd98742106f561d08419f596421067f6550841db948421076d5210841eb50842106f66110841bd584421067f65cc8419f997321067d65cc841db94b321076d52cc8419fd96321067e658c8419f596321075e538c841d754e32106f6618c841bd586321067f654c8419f595321067c654c841afd9132106bc644c841bdd8532106f4614c8419fd94321067e650c8419f59432106be640c841af590321075e530c841d754c321076e520c841db548321073d53d0441af98341106bd6490441cf95241106f56490441dd95241107b65490441bd98e411067f6550441afd95411073f65504418fd95411073d5350441afd85411073e5150441af18141106f76550441ddd9541106776550441bdd9141107b76450441dd95141107b65450441bd18d41107b64250441ed109411077b5094041cf192501067e63940419f58e501067e62940419f58a501073f4194041cf506501067f63540419f18d501067f62540419f18950106de6314041b758c50106ee6214041bb58850107795014041d798f54cc67e62d53319f58b54cc77561d53319f98354cc67d60d5331cfd5254cc67e62953319f58a54cc67e60953319f58254cc73f64553319fd8954cc67c6255331ddd8554cc67f60553319f18154cc73d5415331bb98854cc6ed6215331cf99054cc75e63153319f98854cc76e62153319b98854cc67d6215331db58854cc66d6215331dd58454cc67e60153319f58054cc73f54d0f31cf15343cc73e5490f31cf55243cc6f66190f31bd586
  | 45 => 0x1d0b41db94842d076d5210b41bd98442d06f56110b419fd9732d067e65ccb419f59732d06be64ccb41af59332d075e53ccb41d754f32d067f658cb419f99632d067d658cb41db94a32d076d528cb41bd98632d06f5618cb419fd9532d067d654cb419f19532d075e534cb41d754d32d076e524cb41db54932d06f7614cb41bd18532d067f650cb419f99432d067d650cb41af99032d06bd640cb41b798f50d06dd63d4341bb98b50d06ed62d4341ded4250d073c64943419f98e50d067d6394341cfd0e50d073d43943419f98a50d067d62943419fd8d50d067c63543419fd8950d067c6254341de54050d06ee62d4e41bb58b53906fa60d4e41be583539075f5394e419f98a539067d6294e419f982539067d6094e419fd89539067c6254e419fd81539067c6054e41d754c539075e5390e41d754e43906f66190e41bd586439075e5350e41d754d43906ef6250e41bb18943906f76150e41bd18543906fb6050e41be181439079d4310e41dbd4a529067e6394a419f58e529067e6094a419f582529067f6354a419f18d529067f6054a419f181529076d5214a41be98052906f96014a41db94a429076d5290a41bd98642906f56190a41db949429076d5250a41bdd8542906f46150a41eb508429067f65cca419f997329067d65cca41db94b329076d52cca41bd98732906f561cca419fd96329067e658ca419f59632906f6618ca41bd586329067f654ca419f595329067c654ca41afd9132906bc644ca419fd94329067e650ca419f59432906be640ca41af590329076e520ca41db54832906bd65d0641cf597419073d53d0641af98341906f565d0641dd597419077653d0641ded42509073f64942419f98e509067d63942419f98a509067d6294241cfd06509067f63542419f18d509067f62542419f18950906ee6214241bb588509077950142419f98b535067d62d4d419f983535067d60d4d41d7d4e53506ef6254d41bb18953506fb6054d41be181535075d5314d419f988535067d6214d419f980535067d6014d419f99743506be65d0d41cf997435073c53d0d41af98743506be60d0d41af592435075f5390d41d714e43506f66190d41bd586435075f5350d41d714d43506ef6250d41bb18943506f76150d41bd18543506fb6050d41be181435079f6350d41e7d4d435073c5350d41e714d435071c5350d41ebd8943507ac6250d41edd8543506bc6150d41ed18543507bb6050d41af18143507b86050d41ae181435067e6510d41af990435067e63d49419f58f525073f43d4941cf50f525067e60d49419f583525076f5294941b7d8d52506dc6354941bed8152506f86054941db548525067e63149419f58c525067e60149419f580525067e65d0941dbd4a425076c5290941bd98642506f56190941dbd49425076c5250941bdd854250
  | 46 => 0x32b798e420cadd6390832bb98a420ca7f6550832cf951420cb3d54508329fd94420ca7e65108329f594420ca7c6510832cf950420cb3d5410832b798c420cadd6310832bb594420cb6d65108329b594420caee6410832eb990420cb6f5410832eb950420cb6d5410832eb550420cbce6310832bb58c420cbcd6310832b358c420cb6e5310832bb584420caee6010832cf953320cb3d54cc832e7953320cb9d54cc832f3d0b320cbcc42cc832b7983320cb3e548c832cf552320cadd638c832d794e320caf6618c832bd586320caee648c832bb192320cbae548c832eb552320caed638c832db94e320cbce538c832f9986320caed618c832f9586320cae5618c832bb982320ca7f654c832cf951320cb3d544c832b7d95320cb5f654c83297d95320cb9e544c832e7551320cadf624c832d7949320cbce424c832f3509320cadc604c832bbd95320cb6f654c8329bd95320caee644c832bb191320cbae544c832eb551320caef634c832f3d8d320cb6e534c832f394d320cbce434c832f350d320caef614c832bb181320cabe64d4432af593510cb3e54d4432cf553510cb3e5494432cf552510cb7751944329f992510ca7d64944329f982510ca7d6094432cf951510cb3d54544329fd91510ca7c64544329fd81510ca7c6054432af990510cabd6414432cf950510cb3d5414432dd544510cafa6014432be580510cabe64d4032af593500cb3e54d4032cf553500cb3e5494032cf552500cb7b5094032cfd92500ca7e64940329f592500cb3c64940329f986500ca7d6194032afd91500cabc6454032cf951500cb3d5454032bdd85500caf461540329fd91500cb3f64540328fd91500ca7c6454032cf191500ca3c64540329fd85500cb7761540329dd85500ca7c6154032dd185500ca746154032af990500cabd6414032cf950500cb3d5414032bd984500caf56114032de540500cb5f5394f419f98a53d067d6294f419f98253d067d6094f41bbd8953d06ec6254f419fd8953d076f6254f419bd8953d067c6254f41db18953d066c6254f41ddd8553d067f6054f419f18153d075d5314f41bb98853d06ed6214f41d794f43d075d53d0f41bd98743d06f561d0f41cf94f43d079e53d0f41e754f43d06be61d0f41ed98743d07b561d0f41af98343d06ef6250f41bb18943d06f46150f41bed8143d06f86050f41afd9543d073f6550f41e7d8d43d073e5350f41ebd8943d07ac6250f41edd8543d06bc6150f41ed18543d06b46150f41eed8143d06bc6050f41ee18143d06b86050f41d794c43d075d5310f41bd98443d06f56110f41dbd4a52d067e6394b419f58e52d067e6094b419f58252d067f6354b419f18d52d073f4354b41cf50d52d067f6054b419f18152d06de6314b41b758c52d076d5214b41db94b42d076d52d0b41bd98742d06f56
  | 47 => 0xd91544ca7f6355132d7d8d544ca7f6255132dbd89544ca6f62551329fd85544cb7761551329dd85544ca7c6155132dd185544ca7461551329fd81544cb7b60551329ed81544ca7c6055132de181544ca7860551329f994544cb3d5415132cf990544ca7e61151329f584544ca7e60151329f580544ca7e65d0d32cfd53434cb3c54d0d32bb98b434caed62d0d329f996434ca7c6550d32cfd51434cb3c5450d32bbd89434caec6250d32bdd85434caf46150d32bed81434caf86050d329f994434ca7e65d0932cfd53424cb3c54d0932b798f424cadd63d09329f996424ca7f65509329f595424ca7c6550932cfd51424cb3c5450932b7d8d424cadc63509329f994424cb6e54cc932db153324caf6618c932bd586324cbcf528c932f5986324cbd5618c9329f993514ca7d64d4532dbccb514ca7e60d45329f583514cb775194532afd91514cabc6454532bed81514caf86054532dd544514ca7e64145329f590514ca7e60145329f580514cabe64d4132af593504ca7e64d4132cf993504ca3e64d41329f593504cb3d64d41328f593504ca7e61d41329f587504cb7b5094132afd91504cabc6454132bdd85504caf46154132de540504ca7e64141329f590504cb6f3214132d78c8504ca7e61141329f584504ca7e63d5032d798f540ca7e62d5032db98b540ca7e61d50329f587540ca7e60d50329f583540ca7d6595032cfd52540ca7e61950329f586540ca7e60950329f582540ca3d6595032eb18a540cabe6095032cf98e540cb3c6395032cf98a540cb3c6295032cfd86540cb3e6195032cf586540cb3c6195032cfd82540cb3e60950328f982540cb3d6095032cf182540cb3f6455032db189540ca7f61550329f185540ca7f60550329f181540cb3f6555032eb189540cabc6055032cf98d540cb3c6355032cf989540cb3c6255032cb189540cb3c3255032cfd85540cb3e6155032cf585540cb3c6155032cfd81540cb3e6055032cf581540cb3c60550328f181540cabe6415032cf550540ca7e6415032cf990540ca3e64150329f98c540cb5e63150329f988540cb6e62150329f984540ca7d61150329f980540ca7d60150329f992530ca7d6494c329f597430cb3e54d0c32cf553430ca7f6590c329f596430cb3e5490c32cf552430caee6290c32bb58a430ca7f6550c32cf951430cb3d5450c32bbd89430caf76150c32bd185430cafb6050c32be181430ca7f6510c329f594430cb3e5410c32cf550430cb9d4310c32bb988430caed6210c329f992520ca7d6494832dd986520cb7561948329f597420cb3e54d0832cf553420caed65d0832db597420cb6f54d0832eb953420cb6d54d0832eb553420cb2d54d0832bb58f420cb6e53d0832ebd0f420cbad43d0832bb587420caee60d08329fd96420ca7d6590832cf952420cb3d54908
  | 48 => 0x1cca7e60947329f58251cca7f64547329f19151cca7f60547329f18151ccabe6414732af59051ccb755114732af99350ccabd64d4332bd98750ccaf561d4332ded4250cca7e64943329f59250cca7e61943329f58650ccabf6454332af19150cca7f6454332cfd9150cca3f64543329f19150ccb3c64543328f19150cca7f61543329f18550ccb795014332bd987548caf561d5232be983548caf960d5232d758f548cb6e62d52329f987548cb7661d52329d987548ca7d61d5232dd587548ca7561d52329f983548cb7a60d52329e983548ca7d60d5232de583548ca7960d5232cfd52548ca7e61952329f586548ca7e60952329f582548cb3f64552329fd85548ca7c61552329fd81548ca7c6055232cf550548caf66115232bd584548cb3e6415232d758c548cb6e62152329f984548cb7661152329d984548ca7d6115232dd584548ca7561152329f980548ca7d6015232cf953438cb3d54d0e32bb98b438caed62d0e32cf951438cb3d5450e32bbd89438caec6250e32bdd85438caf46150e32bed81438caf86050e32e750c438cb3f54d0a32cf153428cb3e5490a32cf552428cade6390a32b758e428cb3f5450a32cf151428cb3e5410a32cf550428cade6310a32b758c428cadd65cca32d7597328cade60cca32bb597328cb6d65cca32db953328cb6c54cca32ddd46518ca7e64946329f592518ca7e60946329f582518cb775494632dd952518cb755494632dd152518cbd73294632f9cca518cb776494632dd992518cb756494632dd192518cb776394632ddd0e518cb764394632dd50e518cb744394632dd18a518cb774294632dd90a518cb754294632dd10a518cb773294632ddd82518cb766094632dd582518cb7460946329fd91518ca7c6454632dbcc9518ca7f60546329f181518cb776554632ddd51518cb765454632dd551518cb745454632f5cc9518cbe73254632ddd91518cb766454632dd591518cb746454632dd58d518cb774354632dd90d518cb754354632dd10d518cb766254632ddd09518cb764254632dd509518cb744254632ddcc9518cb673254632ddd81518cb766054632dd581518cb746054632dd544518cabe64d4232af593508caf661d4232bd587508cb7651d4232dd547508cb765194232dd546508cb7b50942329f992508ca7d6494232dbcca508ca7e61942329f586508cabf6454232af191508cb765154232dd545508ca7f6454232cfd91508ca3f64542329f191508cb3c64542328f191508ca7f61542329f185508caf66114232bd584508cb765114232dd544508cb7950142329f987544ca7d61d51329f983544ca7d60d5132cfd52544ca7e64951329f58e544cb5d63951329f58a544cb6d62951329f986544ca7d61951329f982544ca7d6095132bdd85544caf46155132bed81544caf86055132cf
  | 49 => 0x1c5350d42ebd894350abc6250d42eb1894350bb76150d42ed1854350bbb6050d42af1814350bb86050d42ae1814350a7e6510d42af9904350b6c53d0942ebd0f4250bad43d0942af58e4250baf5290942af9824250a7e63d45429f58f5150b3f43d4542cf50f5150a7e60d45429f5835150b775194542b7d8d5150adc6354542bed815150af86054542dd5445150a7e63145429f58c5150a7e60145429f5805150a7e63d41429f58f5050a7e61d41429f5875050b7b5094142b7d8d5050adc6354142bdd855050af46154142de5405050b3f64141429f98c5050a7d6314142cfd0c5050b3d4314142cf9085050a7e61141429f5845050af661d4c42bd5875310b5f5394c429f9865310a7d6194c429f9825310a7d6094c42db1895310a7f6154c429f1855310a7f6054c429f1815310b5d5314c42cf9534310b5e53d0c42d754f4310aee62d0c42bb58b4310a7d6590c429fd954310b3e5450c42bbd894310af76150c42bd1854310afb6050c42be1814310b5e5310c42d754c4310b9d4310c42bb9884310aed6210c42cf54f4210abe60d0842af5924210b3e5490842bb5924210b6e5490842eb9524210aee63908429fd954210abf6550842cfd954210a3f6550842cf54d4210abf6250842cf9494210abc6050842bbd954210b6f65508429bd954210aef6450842ebd914210b6e5450842eb9514210aec6350842b798f5110add63d4442ddd465110a7e63944429f58e5110a7e60944429f5825110a7f63544429f18d5110a7f60544429f1815110b755114442ded425010b3c64940429f98e5010a7d6394042cfd0a5010b3d42940429f9865010a7d61940429fd8d5010a7c63540429fd855010a7c6154042b798c5010add6314042bd9845010af56114042de5405010b5e63d5332db58b54cca7e61d53329f58754cca7e60d53329f58354ccb3f54953329f98654cca7d61953329f98254cca7d6095332cfd9154ccb6f62553329fd8554cca7c61553329fd8154cca7c6055332cf55054ccaf66115332bd58454ccb3e6415332d798c54ccb6d62153329f98454ccb7661153329d98454cca7d6115332dd58454cca7561153329f98054cca7d6015332cfd5343ccb3c54d0f32cf95243ccb3d5490f32bb98a43ccaed6290f32cfd5143ccb3c5450f32bb18943ccaf76150f32bd18543ccafb6050f32be18143ccb3e5410f32cf55043ccaee6210f32bb58843ccb3e54d0b32cf55342ccade63d0b32b758f42ccaed65d0b32db59742ccb6f54d0b32eb95342ccb6d54d0b32eb55342ccbce63d0b32bb58f42ccbcd63d0b32ebd0f42ccbad43d0b32bb58742ccaee60d0b32cf95142ccb3d5450b32b7d8d42ccadc6350b32bb59442ccb6d6510b32eb99042ccb6f5410b32db55042ccaed6310b32bb58442ccaee6010b32ddd4651cca7e64947329f5925
  | 50 => 0x548439fd815210e7c6054843db5485210eee62d4443bb58b5110f7751944439f98a5110e7d62944439f9825110e7d6094443cfd0d5110f3d43544439fd895110e7c62544439fd815110e7c6054443dd5445110f7b5094043cf1925010f3f4394043cf50e5010e7e62940439f58a5010e7e61940439f5865010e7f62540439f1895010e7f61540439f1855010eee6214043bb5885010ef66114043bd5845010f795014043d7d4e53d0a7e6194f429f58653d0a7e6094f429f58253d0af76154f42bd18553d0b6f6254f429fd8553d0b776154f429dd8553d0a7c6154f42dd18553d0a746154f429fd8153d0a7c6054f42d754c53d0af66114f42bd58453d0b5e53d0f42d754f43d0aee62d0f42bb58b43d0b3e53d0f42e794f43d0b9d53d0f42af98b43d0bae62d0f42eb58b43d0abe60d0f42bb18943d0af76150f42bd18543d0afb6050f42be18143d0abf6550f42cfd9543d0b9f6350f42cf94d43d0baf6250f42af18943d0bac6250f42ab18943d0bb76150f42ed18543d0bbb6050f42af18143d0bb86050f42ae18143d0b5e5310f42d754c43d0aee6210f42bb58843d0b7751947429f98e51d0a7d63947429f98251d0a7d60947429fd8d51d0a7c6354742cfd0d51d0b3d43547429fd8151d0a7c6054742b798c51d0add6314742dd54451d0ade63d4342b758f50d0af661d4342bd58750d0b7b5094342cf19250d0a7e63943429f58e50d0b3f4394342cf50e50d0a7e61943429f58650d0a7f63543429f18d50d0a7f61543429f18550d0b795014342bd9875390af561d4e42be9835390af960d4e42d7d4e5390a7e6194e429f5865390a7e6094e429f5825390a7f6154e429f1855390a7f6054e429f1815390b5d5314e42d794e4390b5d5390e42bb98a4390aed6290e42d794d4390b5d5350e42bbd894390aec6250e42bdd854390af46150e42bed814390af86050e42e750c4390abd65d0a42cf5974290b3d53d0a42af9834290aed65d0a42db5974290b6e53d0a42ddd465190a7e63946429f58e5190a7e60946429f5825190a7f63546429f18d5190a7f60546429f1815190b755114642be9805190af96014642ded425090b3f64942429f98e5090a7d6394242cfd0a5090a7e61942429f5865090a7f63542429f18d5090a7f61542429f1855090af66114242bd5845090b7950142429f9875350a7d61d4d429f9835350a7d60d4d42d7d4e5350af76154d42bd1855350afb6054d42be1815350b5d5314d429f9845350a7d6114d429f9805350a7d6014d429f9974350abe65d0d42cf9974350b3c53d0d42af98b4350abe60d0d42af5924350b5f5390d42d714e4350aee6290d42bb58a4350b5f5350d42d714d4350aef6250d42bb1894350af76150d42bd1854350afb6050d42be1814350b9f6350d42e7d4d4350b3c5350d42e714d4350b
  | 51 => 0x3dd94b5150f7552d4543dd14b5150fe452d4543d914b5150f7764d4543ddd8f5150f7743d4543dd90f5150f7762d4543dd98b5150f7562d4543dd18b5150f7760d4543dd9835150f7560d4543dd1835150eee6294543bb58a5150f6f5294543db14a5150f775194543be9825150ef96094543bbd895150eec6254543dbd495150f6c5254543bed815150ef86054543dbd485150f6c5214543dd5445150e7e62145439f5885150e7e60145439f5805150ef66514543dd9945150fb56414543f5d0c5150fb64314543ddd485150fe75214543d9d485150f765214543dd5485150f745214543f91485150f645214543ddd905150f776314543ddd0c5150f764314543dd50c5150f776214543dd9885150f756214543dd1885150f776014543dd9805150f756014543dd1805150f6f52d4143db14b5050f7751d4143dd1475050e7e62d41439f58b5050e7e61d41439f5875050fb964d4143f6d0f5050fba43d4143ded4b5050feb52d4143dad4b5050f7a52d4143de54b5050f7852d4143fa14b5050f6852d4143ded475050ff351d4143dcd475050f7a51d4143de5475050f7851d4143fc1475050f7051d4143ded935050f7b63d4143ded0f5050f7a43d4143ded8b5050f7a62d4143de58b5050f7862d4143ded875050f7a61d4143de5875050f7861d4143bb98a5050eed6294143dbd4a5050f6c5294143bd9865050ef56194143ddd465050f745194143ded425050eef6254143bb1895050f6f5254143db1495050ef76154143bd1855050f775154143dd1455050f6f5214143db1485050f775114143dd1445050f795014143cfd905050f3e43141439f9885050e7d62141439f9845050e7d6114143be9945050f7a6514143eed905050fdb4314143ee90c5050f7b5214143fad485050f6b5214143de9485050f795214143de1485050fe85214143da1485050f7b5114143fcd445050f735114143de9445050f795114143de1445050ff05114143dc1445050f7b6414143ced905050f7b6314143ded0c5050f7a4314143ce90c5050f794314143ded885050f7a6214143de5885050f786214143ded845050f7a6114143de5845050f786114143af9834310ebd6490c43cf9524310edd6490c43d79524310f9e5490c439fd954310eef6250c43bb1894310ef76150c43bd1854310efb6050c43be1814310ebf6550c43cfd954310e3f6550c43afd8d4310f3e5350c43ebd894310fac6250c43edd854310fb46150c43eed814310ebc6050c43ee1814310eb86050c43b7d954310f5f6550c4397d954310edf6450c43e7d914310f5e5450c43e79514310fcf6250c43f31894310fd76150c43f51854310fdb6050c43f61814310ef661d4843bd5875210f6f52948439f9865210e7d61948439f9825210e7d6094843cfd0d5210f3d43548439fd855210e7c61
  | 52 => 0x70014002000000b00000000000003000800e00000030014000000000a00140040000006001401a001c0020034005002000f000400100040120010002003400b0048001000000300180000008003000000300580070014000000400700d4004001c0070004023000000c0000000001000200040000000002001801a000400d0008007002400f001000300240440000001000000100000070008003003c0120048002000401d00000000010010000400c001c0000004010007000e000000200100000018003001c00b0004000005800800000000004000000001100040000008000000400600140040008009000c000000400100100030028005000000100000000010001000000700080070000000008c009000800000440060000003002000000280000000007001c0000004002000c001001c000000401000000040024006000c0000004000000401d000000d003f6f5294b439f98652d0e7d6194b439f98252d0e7d6094b439fd8552d0e7c6154b439fd8152d0e7c6054b43db54852d0ef66114b43bd58452d0f7751947439f98a51d0e7d62947439f98251d0e7d60947439fd8951d0e7c62547439fd8151d0e7c6054743bb98851d0eed6214743dd54451d0eee62d4343bb58b50d0ef661d4343bd58750d0f7b5094343cf19250d0e7e62943439f58a50d0e7e61943439f58650d0e7f62543439f18950d0e7f61543439f18550d0f795014343af5974390f3d65d0e43af9834390edd65d0e43d75974390f6f5294a439f9865290e7d6194a439f9825290e7d6094a43cfd0d5290e7f6154a439f1855290e7f6054a439f1815290f6d5214a43ddd465190e7e62946439f58a5190e7e60946439f5825190f3f43546439fd895190e7c62546439fd815190e7c6054643dd5445190f7b5094243cfd925090f3f43942439f98a5090e7d62942439f9865090e7d61942439fd895090e7c62542439fd855090e7c6154243de5405090f9f5390d43af58a4350ebd6190d43af9824350e7e61d49439f5875250e7e60d49439f5835250faf64d4943f3d0f5250fae43d4943dbd935250f6f63d4943dbd0f5250f6e43d4943dbd875250f6e61d4943db5875250f6c61d4943dbd835250f6e60d4943db5835250f6c60d4943dbd4a5250ef66194943bd5865250efa6094943be5825250ef76154943bd1855250efb6054943be1815250f6d52149439f9845250e7d61149439f9805250e7d6014943bb9945250f6e6514943eb5905250fcf4314943eb90c5250f6f6414943dbd8c5250f6f4314943db90c5250f6d4314943dbd845250f6e6114943db5845250f6c6114943dbd805250f6e6014943db5805250f6c6014943dbd4b5150f6c52d45439f98b5150e7d62d45439f9835150e7d60d4543edd935150fd743d4543ed90f5150f7752d4543f9d4b5150f6752d454
  | 53 => 0x28008002c01a001c0000010000000003100000000004000000000c002c00000100000010002001800000180010000021000000501c000600240190008001000000300140050010004000c005000c01d0014000002c000000402800000040000000000400900000000008000000001b004c00100040020004004005800e0074000000000a002c000002800100080000000001005400300040050018002001004e000400900000000004001000400d00000010010003000000400000020008000000c003002400300140000018003002c003000c00600040040004001000c0020000027000800000000030008007000000b001c011000400100100000024000000002c00040000004000001800500000020008001000400a00240010000000000c000003c0020000001002000b000800000200000000002000000f0040005000000300100000000007000000100040050000006005c0040000015000000400340010000000004800300140140000000001c00900080040000002000000b0020004000c00000340010020000000c006000000300080000010000001400100000000000003004c003003800d0014012002c00c000800400340170014007000000000200150014001003801200000170048002000400a0000000006c003003400000880000000005002000700f400f00000020008000006800c003002c00000010018002000000001080020000000001c00100000000008027001c003000c00000140040004002004800100000060010001000c002002000d000c0000000002000400e0024007000c0050000004000001e00000000000006000c00700580000000001000800300040010010005000c000001800200040010000000000000200440000014009000001100a001c00040010014001000401000040030004004000c000000800000340050000005000c0020030005005400b00080000024001001c00300100030024002000c00000000020014009000400800000000000001000400000100240000001001400e002001c005c005001800e000400e000c00600000020054003000c00a0004011002800a002c016000c000001000300100000024002006400a001800a0004002002c00c001000100000040000000000000600fc0050000002002400a006403900400120038003000c008002c018000000700000080000001000400200180190000001000800200040060028000002c001000400000000570028001000000f0004005000800f000c00e0014001003000000000020008002005c00000180020004000004c004000000000380010018018005c004000000d001001b0000000007c00f0068009000c03b0008004005c0180014004000000f000000100000000018003000400000000070000001001000000280080024000000c
  | 54 => 0x40060020008000c00900000200050009000c03a001c004003c0000000020000000000b8003002c000000c0070000002004c006000002400200000004007002c00f00540030008011001400000380000004004001800b002c015000c00900000000020003000c00e001c00700000050054009001800a00040050000008000401d0004001000c0060000000000000000140040034013001400000040000000000000c00200180020010009000402b00200070008006001c013000000300140000004000007000500440140000007000000000000010044000002000100e000800940010034002000c0000014001006800000140000000003004000600c400a0020005000400100000080024000000001f000c0000004002002400000040010000019004c0050014005006c00e0040000000c00100240010008000000800500000010004003000000500040060070001000000500080000010006000000300040080000002000400100340060004009000000000100100000015002400a00140130000000001000500000050008000000400b008800100580030000000000c00b003800400240020000011000400000100040008000001800900000100008000005000d001800100100000028003002400700040000004000004800200280000044002000000a00340090070000000000300180040008000000800e015c0010008005001000100780010000004000c00000880020058001000000200000030028000001c007001c000000000b00040190004002007c00000000000008003000c0010000003000000300000010004000000000700000030000007000400800280030038001000000c00040010000000000c0000014008001000000000030034006000c006001000f00280000034023000000000140050054008000000a001c00600040050004008000c0080010000000000000000030000004000c005000400c008c012000800600040000000002003c000000800200300010000003000801d00180000000006000000f0000000014c00600000000004004000000100000010048006000000400080060000000001000500040270000001000400e00000110000001000c016001000700a403d000801100580080000004008400000040000070000000000100400010010002000000b000002c0048018001000300000080000001000000000180000008003001000000100000000022000c0010008001008003a00000010000000000800a001000200040020028000000800000400000004005000800600240000004026000000b0010000000400c00080080044002000c00100040010004000000800500180030010001003000000600000034001000400a000001f000400000040000004002004800200080010000000000000000380050000000
  | 55 => 0x2000c006002400d00100000010000004001c000000100140070000000001c00a0014001000c00400000080034001001400a000c00100000100008000000c0000004000001400200340060008000000c00c0020000001800f000000200000000028002000c00000000150050001000800300140030080002000800000ec000000c0000010006002c000000401f000c003000800e0004002002c0040004000000000a000400200000010000001001c001000c0060024002002c005001c00200080030004001000000000540000010033001400000300010008003000000300000010000000003c00000000250000001001000000300000000000001c003004000100b8001000000000040010008018000000100040160000004001800000000000004000000c00000040000010001001c0020000009000001800000030000002000800000100000004000000c00100880000074000001c00c0000000001c01300040020000002003801200000000020000000c0260004000001c00200140030004000004400300140000030013002c00300100090004003005c00200100000000000000800f00080050000000002800a0044000000000000040070000011001c00400040070004005002000200100030000021000800200400020008005000000600000000004000001000200080030000003001c00300000130028001000000500900000000000000000200000290004001001800000340020038007000c00c00140000000005004801e00000000020007000c001000c0000024001000000200080010008000002400100380100024000000400700c000600040080000000001000b0010003000400100d000600280010008004001c00000000020004016000000000580030010000000000900000020010000000400600040050004003000c00200b80190018003000c002000000000000030008001000c001000000000100010000005002001700080000000003000401f001c001001000400040000008001001c00f00000010000003003000900000050004000002400000240000004001004c00000000020000003000000a0028001007800e000c008000c0020000011000800100bc005001400000c40090004001000c014000c000000c0010000004000000400040030000015000800000040040000016000000000300030000002000000800640020054000001c00200000000048021000c008003800c001c001000800100100000078000001402a000000600b40030000005000000000640000008013010800b00500000038000000000a000c00d001000e00ec00400000000030003000400300000170004001000800100000000008002000800b002800000080080008003000c009003400c002400b005c0020000000006800a00340200044001000
  | 56 => 0x40060014004000000c0010005000000f000c0020000007000000000800040000002000c004000400000240000020000000c0030000000001400000fc0010020006001400b008c00000040000058007000c00c00000000004009001400200040040014000000c003000c00000040000000007001800c00380030004001000000100000010000006004000400100000018000001000b000c0090010000002c00000a4009000000300380010000000000000500000000024032000400b0000008001001800000060000000000000a0008000000000000300030004004000000000000060038001001000300e8013001c00200000050018000000401a00000150008000007400a00080000004001001800b0008000001002000000000018000004c00a005c000000800b001c004001800000100180024000000c000000c003001c00000000070054007000800b001000100040020004004000400d001400200000030000000006c0030000000000c0190020008000400900100060000000001400a0000003000800c00040000040004000c001000000100040020018000000c0010000000002c004000000700000010000000000000f003400700000050000006001c003001c00500080000000002000c00b00000000000000000000b001401100080070000000000400c000c001003000200080020014000001800600040000000000001c00000000060000001001400700300050000000003c000000001e0020000004c000004c002000c007001400000080000010001000002c0018001001800a00240110064001003003500080080000000003000a001400900300000000021000c00000000030018002008c023002400300040060004011000000e00000130034000000c0010038003000c0010004000000400e0034001009000a005c00100040030004004000000000440110000005001c00000000030000000001c000005c0030044008000800c0024008000000100080050028002000c000002c0000000009002800000380000050000000c00300000050018000004400100040000008001006400e000400100080000000012001001200140050000001004000200000040014000002c00800000020008000000000200040050040007002800300040030000019002400200000060010000000000e000800400000000018005000c0000018001000001600000000048006000400a00080010028001000800b00180130040002002400100b000c0008002000c003001401f0008001000c00c0000000001000e0018000001000400000020014012000c000000c00000180060004002001000100000000030004001c006000c00c002c01e005c0020044009000403a0000008003c006001400000040000000004000000e005000300040000004000000400
  | 57 => 0xb00440010028006001c0070004000000800200040020000000002400900040000000000003800a004400300080030000008007400700000030000000002c0000048004000c006004400400000110040013000000100480010020006000400000000050010000004c001005400400100000020004002800d002000000080060010000000000a0010000006c00000200050000067000000000640080018000000400f002400500000000010000002000000000010024010001c00400580020028001000c00000080000014001001000900380010000000000001300040000008005000c00100040040010003003c00900400000008004000000400240080010005000c00200000020008002002400100000070018000000800000440050030006000000100040000000004000000900000120000004001c00b0004000000400b001800100140000050002001800000000000004000000401c000000a000c000000c007008400000240030024000001401000000090000000000000c00000100004001001400200040000000000000000f00040030004007003c000001c0000074000000000000000080030004000004b0004017000001d002000100080010008004001000500380020004004003800000200010000000000c0020000002000000d00000030004006002c0110030002000400a000c002003c00f00000010000014000000500000230000012001c00000180000000000000c0030018005000c000002c00100200080010001007800000080060000003000c0000018001000000000000050010003000c00200280000070007000c0090038002000400d000801700000230084026009800700040010008005000400c003405e008000b00040030074000000c001000000000180010028001000c00000200010004000000400400500010008000000400b000000c00640010028002001c001002000a0010001001000000280000000007000000100340050034017001801300080040004004001c00b000c00000000080000008000000a000400300100170030001000002b0004006007800300080070030001000401600040040014003000800b0030000000000200500040014002000003a000800000000050010004003c00200180130004008000c00300240000038001001c002000000000000000004001000000e000c00100040000014005000c004006000c0000003002c0010004007002402b0000002000800200640130004001002c00200380030000005002000200040010014001000800000000130034003001000e003002c001800000000090024001000000100000030000004002c00200000000004001002000d00200250004009000c00000000060000007000c0000000008002000000000000038003000c0050004000000400300
  | 58 => 0x200080030038000001800100040000078000000000000440030018001000800b000c001005c00500080010020013000c01d0010002001000000140020004000000000300740040024000001000a0014005000400c0018000000000900140000000000000000000040070034000000c00000000000004003000800e0004000003000200240000000000000000900180230004007001c004001c002001c000000c00000280030000002000400a001c00200000030000000002c0020000000000c0030008000000400100040080008009000000a0000000000000f00a400000100030004004000000c0024003000c0000000006000800a000000500000000000013000000400300140020002000000000100000010002000000000080050010008000400000c00030000002000000b000400400380010080022001402e0000001002c0000004000003401d000000600080050008006001c001001400900000020004006002c004004000200080200004000000c0050000000000400300000000058000000001e00140020000009000c0000048001000800a002c0070060000000400100000060018001000c000000c0010000002001c026000c010001400000c400a000000600f00050018019000003b001c01c0010008000800a006400200100000008005000c009005c00000dc00000280020028003000c003001c0070000002003400300040020038002002800000000000008012000000000bc00a000c00000000000000015000000000080020014000004801800240040004001000401c00200090018009003c000003c008000800200240030008000001c001000800b003400b0028001001800c00000030024000000c0080008015001801c0000000006800900080040048004000800000080150010002000c0090004000000c003002c0010040005003401e00040020000002000c0060000002000c00400a400100000000000012004800b00580020020028000000000000010000000006c0020004001001c000000400000040000038011000801800a40000048002014000800140120000005005400200080000038005000c0080008006000400e0004000001800300040100044000000000500200030000003000002600080040024006000c000000400000400000000011001000300040050000000000800700000100004000001801f0018024000c0050014012003800e00100000010000000000000000000008001008400d001800000040000000008002400100600000018001001801e000000a000c000004c0010008007005000000180040068004000000f005400200180000018003001400100140010038004000c019000800c00040000020001003000a001000900100190038000000c00b0004013005c0010004001000000400000
  | 59 => 0x8250ca2b0ff72bd355ec485812b10be524a61a50d68a863d8e7db444e10010aa23f8cd17857d3dd613d45859ccc05488fd49b023ca32ac17fc27f80670a8c421c85c08553db039f4465ac2357849f681fb8107000065bc00000000b889c48e5f0000523c782cd7083501bac8b540001497138c000000000000000000000000003ab86c2c00004873e705f7d2bb1d10110c284532d2a9b41bc64ccace929c51282910eaf046725da74c0f7c80000000000000024c4221000005ac00000000000054c19e53d083eac00028f0183ead70000067714c05a59279a17526ea725c00010743f1e409c0001f2125f032801b59c8a423a3b6c5ae0bba2c582b80000031c00008d9d563271d13f6469151617164a329afd0459dba29e42c000001132057001640000c332722000000000001d280000000000000009d40f3480004ba08b10ce481ea0000acfc9588a5a1a4c9bb8000113f1db21450000224648a42b7096a13780db00000000000000001a49310088b02d43cc42e9842051180001427a69613ac0d3131580000e70646c4a100004ff0000045f8000030c52cd0dfa5b2000011bc1eea5410000395ce83000017c626154b7895d54fa2414826254000005ae84c985e502e24bc523f0000139615153f106a732ae000108486b70f6e0001121120d00000000000000000000000e978c0648b60000564aafd484243600000c1b42b05518a251708000034881dd932e05e6a8c0d45a83a2a82115482580004fae000025283a4000000015e88c981642567c4a5884f09b295e800008052a0a18bc0000b040ba2300c000000017c0000024520a13110814d2fea0e900007eb061ba2d6299c5ab0efd80000000595c000000050a000000001b5b0a7ea1380001297342200010431d3300003dd814600001c140000b4f185d57e8a37c8448da510060f945a2a6df2d280000bd7839218dc21b818b23e0000081180d11b024b147bb80001a73231a0000d7d80000000000027092af1e309450c3788fe15fa06090178d5c4f6e2dc40002b350000a3a83f5800007c02b180000000000054fc204ab5d333e2de4524829d3a9408b075e0bd31aca0000000000000000000d84a85f129c3ef14868000000051503268000059646200002a77327e41b40ad23ea544a00000000e6e00000000de400004b6000000001a4110702ab0000000000000000ec3000012740000000000045ae0000daf9dc8355a00140020008002008c00300000190000000000800c0010004001c0010018003001000000100030020001000000200280010000001000400e00000210000005003c0090020002000400000000000004001001400a001c0030000028000000700300310000000000000000000000000001007000c000c00000080000000001000800200a000000380040084000006801a0
  | 60 => 0x153c9800028aaa040698aa9928728e88d18830f08ae1a2000025500000000016c8a5926b8000000004da2ecc2ca8a2580000b5c22b44cc8aa5034273348f4a88930a82f54e5180002a32109433a9cf00b4e9a34a0da2813226124c70c837413c013983d41cb00000619c000079e366e209c02fa21f1ea8ab882b89d6a4adeb134000168121aa08d531a000033740a7d36a1e4b223c30b0fd515dd000090c00001a92052ea5d00000f3d00007664f0d0000084400014ec1bc740c00000919825155ea7f3c47b0cd7000075e47d1002b506a5594c15800000005edd09c24bb4f40000118e86480000000106706c500003da9234000018ca5f4471e04c03c52000075d1b3d0000977c00005a800000000000200a4c281e243bb9f544aa277283778000063000004481b642344ab0412082c200086a140001f3210a006b4000289900000000b2f800044d800002c30000585c4c9814017560dd88ea0887215411fa813d5ad023e314a1bb93ce1592282206352f206864904543161d88af32eab05d0110c922b4a9fe5031295620e271c501a03bc1a5c0960b94a2b43ede000052b04e504b473a81b022a73c9c49889f8069a109088e43d893a32f84521c23eab0c08529cf06ec983c24ce63e045491342510000047fa617015e7bec0ec1711031808a54d98000411800013e800001bdc54bc0001bf10000324d50b8d3414d80000e06abd22acc000000017ce331ca518000215135509cec92cab9500000000ff9a79854720000000000000006c100001b160000a92c71ba5d4000000008a611e402127b0c557a547336c98554000000495e000000001a404ce4e78000000037649d0c00014db31bc494800006f900002fec62787430000000000027a30e489198000000000000001416a0b442f648fcb1ea5f9516225140001e39518a716c00009e945926620218000000002b109c0243e40d217744be83a23bba7eb871719264436561148e2af9356835614978000000000000000000000052881ff80000ee000000000000193815650bd1e63269a000094f18170be64518588800015408268000293c2dcc2fdc992087849362fcc20f08b51dcc1180fda96ae018c000125e9a181efe78ac72a0c133ee608ec000216800007cc0000204a5042217800003a152be65049a780001a760ba561a11a011a065ac756a00b3da691c0c0196c73f3865913b422d0000000007ec12233ad200000002338196c86883b4800000000000797861f185a5f6927a00000000000134f9f95432a18f8ca48c5121c03c1cabd80000bf4518447313b5359854183870000000090a000006da48dc00000000000178609cc67428064140947800026f900000000ef100003efc0000000126e202c0f00ad6000000000000066081341c000009e180000000000000027a701a0498cafea23
  | 61 => 0x130e31700000d93512486acd8ca5724370a934c960e2052aa9a44313a1a600004f640001fed4bce756c0000ba9000004340bc9a3b00000001252262d0000a5940001832000077909b28000000078080000bee561a0001590800000003adc0000c1647987b7c3ffaa2d2f9e562d29aa94300004184ff7a902288c0000dc8027011d800000000fd32bc466c800027c254fc7b78a069320437c8990f6481f23bb02ac0b1a9b1f4b8aa4a0777000045de56044b4aba7435c19612362c3e09fa2b008b098b12e88a1c8e2c865c1fc40000dc3943141920da0ad121411e8659b0cb0811a495a42fcc23800017125a406698b9007f40e9537d27c100000068de22c22000069d90691b89064a290c00000001fbe277800000000b0e6d8870e98381a5a04d40000e8f517c72d025e0000000007845989688000058ac0001658000010849ed85020000000020014a000009b2c6af800000582ce8e0429d7262e00000000eda1df209f8a2f84e024ea0ed891d129b15de04849651b9303f601e8d140000000050f801c83d525baa6394ae11533aa03980736010f41260000e3e8e4c212a5c9923f80003d3c3ec404d84611b7ca5d4e221c3b2ac8612c6f097fa4f7e53988d928842df6568c47c9e30542c8fb84b89d751242819c00028c12ce66a9cfb5918900005d240b39b4a368c44bc8e70e4708ea8c1c29b82713af071440001b5315a4000000000000000556d2fbabdd21506d58355079703e85488afa063f0fd2a508cec87451c0e6b255560ca9415e57108d3866c13669ecce251d3d1ecc8c6133125ea125a1b9522d281b01d4502c03e89fc44a2a9511a00000183200000001fe30000975800000000b22aeb076791b8085a7d8cddd000025985ddcbcf22530000748d27484fa23927a6400024d822ca17d4000084e000000000818aee00005e0800002f2327867bcd8321c40b6600000000000091c51a86c09b41393e862960b1cd8000000000000ca22d868b48141a0f922d40001291899b00005d480001bf70000000000000000000a7f8c17800000000000000000000008228fb0988b000015b031da4db4f804d1cae188c900001604000059c53e619a8000000047aa00009ad29833cc87e4c96401940000000000007e22f9000002f88000151e31580001c9a02bc2ddc0002224589e0e4c6528ce50000614018f2b693cc014e45960fd92a305adc197a89b157000000000000000066ec0001213000072051a21deb000c0c4c00018b4198600011c78b434e8e8178253a74f38f416e8e542b6a35607ee063b88f009ba2b84d6e2bb91ae83160379a64d154eb0c134d8000000024d4bd1008800000788526120a1be2078d1ef12ae40b28ab03ae9dc4154cac18ed7092e43781c683a8800000000000d7b000037500000000000007bc032400008a027e237
  | 62 => 0x887a6883ca4513127d0000000000000001e0c0000000000000651bcc5b4c000000015e299d400011633640ac4492b92fd4e4631116029002552aa3281b517a600006fb8a589cd301662220170173b000049f01e480000000366c000000000000000000000044d2000000026dc4c26aae04f90b0c21ea186480e00000000162914f13e8000001440000f5d000042083d8000055d2afb0c87000020900000fe00cf900000000000161a4e5a78590dd285205ba00000001a8714c2000009f068e2134a690e2f1b4f00001eb0000051e3eec14d090e00001fea0000bc31366346e00007e418d60ec4708910a8cea306e27d8fed113e0f76325c0db8d754b7e9c34000272c292c74e82860000305a7ad000016954ca418c8659240547be174033d0e141f2800000002b072d7662dc2cb8315277a76f009c82c1403a0000000254f4b7a0000d378154342804b400000001a3a0000a5791ab404c09d8fdd243d3ae06180688220a425a1814e8100002b68000089700001d4e58243ec11f64e96a3092742ad20b5a133137e000000000bfd1d8000000000000000255f00007364000297351663954eba26b039ca00011a58000249e000009b8000385046b41980ffd0000000133308bb173e014006c263931703ce502a053e163caef4f74a2fc38042f3905e2bc738e6749400008a8006638a8d258000049628f0a7d80000000000054f22a8199400004f6800000003b58c1ca6a82f8c10f0000000021d04dc00000ac73a3e445c0000a6831889b154ecac0f18409fc80000b1b2e0e6c54f83000000003ef400000002f7a00011071c2d00007c2082300004d0e1b2001800000000000100e188c5692000000029a7000026b00f593b20c1aac7955b00b9528e2dbd2f7aa8c52600c401539204244200011df83cd239e000141500002f6658ec00019254518a61066b00002d9ea11495b80002b181d685838000000010bcafc8000389a0aec000067645ca00007ce14ba416463bc0000000433a32180001a2c44be2268333960e42de0000ce68000042400008ef00004b680400000000029ec9490774000012c4000046f26b325fe69502531be0361a1ef80002929000086640001bd60e16026936a8e75107a2a8cc8480004fc07c790b29a1f172c010000020c1000085f800028bb2ae2a9201e91363363c082c21514184d5a3035294172416a21ba4d579b6f20069c5049484430d148434ea31103189054b00001d3c29e88068b1c8ec83cc4a9000000000000000000000000542a25d4000005e43f67f6151e25a90000182864f80003e401060fc48c64165a7f300001927000006c4ed696533c6e00011ae07e8273e63c0e7da1b700002a040001f0d26469ae87c084650d945a9c4b38d764b4a0efcbd902f022daaa790719fd71a1e00002ee12cf2d3e5c7059400
  | 63 => 0x752000133a20900fac34f821599be0000000096b28b5114c264412e91bf276e5a9836f1a23478a70dd527985e00824854a92ac4429725040374000021ca5dec529977636f2000000023d62ea04fb01158de84dc65560b810bc70000a0a4826a98c4c4c6b015e400000000487c000206d44020e98591aa492ed864c8ea2843d00008de0c511f75553800014a78000197aa4000000bec000047d0726800020ea12a80000000526493c0001000040ca17b8f50800054fe000068b02a500000000e0e91d438cea700d251ad72e608170f3582d41ad0664d241a38e44189a98d47000018f67fe54b126f236fe00015f720ae338c0000000000053d6000000023bc14160000000000000009958292800000007a0015a800000000000c861cdd52fa6a4c00000004572628c00000000000000099ca2073e8c1a700f80c3448160000fce92102332000000010c13cd4000000025dc05dc3da526ba3815302519c7980e5908f231bcee4ab1b53620000c9e800033063761388926d44f032d066c0e634e94523d1ff07c316822d1054916451afc31c9495211c460a701898985fb44aa000000000004baa000048114781aaa95084df8b8f00008a60b0689ec33f09e5cd75a2ab30148d742d280003c4ca80c0ee0d9f00000f4c84b8e061f706b488ac0d854e9200000001c620000624529d86b0000074d532500000000949c00012a44f960000d05195f06ca67a45520fe6408295381b494f1518c913487c1d5700005a955740a4144043d3448c801b54840000bdd0e0c30a419c47d69ee638be000130d29ec000000000002b083cec3c80eac90071e3811b400000003ece239c000000000001dcd2ba245400e6053154c0000445240ac000105130d8ac814248d4230600000f21820d1da0a160a920bd408d403981ae0caf52768b0c4cf141a3fe890613148a1e217293d48760ce7308629dc6419cdc21fca8c8c652c35047e9b6c8372bd91f3e45103dea40d51d60000000000052b6a7146ce800000003baccf4049a0684943c7d4aaab000000006900f58000097880002112559e7e140000eb343e2707c0001816284400014b8800000004cacb318e661a4e46780000931276c0000c4c223a47767e4122210960d305e7400c12f3000087285d822e8235e89a118e0000000078d00001d8202c2630c44d886701fc757470b13c6001600000000000474a56512e504b71106000000000001946005c5c6032609e87e1ceb980000c2000000000ff300007f447182763069e71ac7ab8b691fd083a0961016400002d8825e885b56e63e91150081b01a28620756050357342cf44af00080e0a9c904450298076257b44ca07ae50580000000202b2aec000000006f74174a174b2628ae25ce65551c292c752c84171066033544ca8d3c65da940000061d516a2855510a0
  | 64 => 0x8c4cb29000040f697c929c273f000000000002052429c0000c6c8aab33b8000073586b6045e932000000002de0000000000001e7c3afc00015283634a7bc000000049ac987c7b0ab59079072c40000e8544fc0d9d19a24eb316a29011000bf01900545cbb821f42e3a7f1940e93c0376638d0c9a8b56000084b0000133d11443a0cf2c2a55580e0000000270b0000000081d12a219ea714800020b7066e698551d80000000000000005ea000096a05480a7d32746b593f3800001b672f00001884420e6c2000000000a985ee0b95920810f8a7d100d976a4da48be0c32951d538c873cb1a0f2209c64ba4123003602f0ac0c2a101553c1c18b4e73800032e69c710b58b392e644265135938c02e054e54938eb03ee21a253959c69515259fc23594723e92a8709faabc618a074248e806b231981c948598ddd0b000cf156f990f440ca0684cfa3014446743024299e402d247b51e39afc30a2ac6840a010c13f025180ab09ad40603f35159a4df30269ef025897bc24007cb506f8bdb47c8ad98aaa174036b25e2122f04be2e4416409e216b620200000000200200006f2d2d1000007c800000000dd54f488db4c98160452f638eca05000015ae000138000002fdc39611e08d993e6e90bcf2d8ce12580009400010b623fe99ccfa884f92a522470246894027c6034cf8a2b98387264513649cf633884dc464aabdc42a00d48000000047ca7690000126c18d4000000000000000ad6c00028e637460000000000028d83745624a6271d3611d00a50c0e2afa0b289fc93022a24afa45421110573619b89469247304656e0e608cb33a1c801d1640308427c73d44f0a88d4da03bd403885780bbc42492bc1f0a04d043848f0ab0a348c73e8c14286c025c038d0d1a7de0a9a0948d5c86dd4288a4b0cd796d62b6204fcfad07d7519a4fb8cd08f684392a8044db0adb413216d48b886fb51604efca8a90ac4096779c0001dd90aa600005000000536000000002b6e2588662cfe400003b0e0000a090c8c494a73bd38c827d40f4000088ea9ed000018ad38c0fb22efe0000396800018786cd000024ec00d4241c000131017d234f1242955100007cfc96900000000809c93c91b51596158400000bf34fa3de460b82aa4c0c1ae4a4a0000559a4c1000017203ffe098c3fba3ad5298397828f800054547e502df0b9a51b657287a9a582371e00000959ee72806000102695df04d846156160a620fa624540c396c64488133d5d7a7d51c3434e08c980000000000013a0269348e3148a6b92b80000000106999b3248a77a400025562ec43d285da01c806e4155c0000c4700000000ebf92784908538161b0b653b40993c49f8b364f58105d11b80002b5a9090faf937c00002684000131520baaca40000000000063ec00023421b2a84940002467578aa674c2a8
  | 65 => 0x8000155017694df00001bb827293e6203510306ca4e300a13293e592c821a209124e00002c680003d6697a53d48d625862877c80d2c453e367544b59284c000019e43c899951a9a01b80000bbe37425938aa519464c8c0000c530608341212490af95d519c43178d681a9928da39f881ca8dc417208189a41e5d2ff853b946b000031569c5c000000041b680dc0001c7f38aea2208688000000097b826b264548988714dd825c23552056cfd8969241b472506b595093008461880785ab4622956cc0c04324fba72b4a6fa3c41ee26df053394380000000130188b20436b164328000055040b4c30e0a8502ea8df000000000000000000000002f82847853d09dc34f6840cad700001834000000016d000006f5c8cd81494f04000003f1f8216244e10a1000002762b038e74a65427201568782ac371b5e7b8133008ea000022550cb83d450c6000047a00004ffa00015f4102100000001059a92d577409ac00000001e2c0000bc280000000000064a00000c40878854f8b34153a0290c57a094139c190448b91684462335556202a82ce496acf910000000000002cf244a19e89b2941b0b70488277c49619060000065b93bb0000000084652b89d964bd6969c00000000668a7302569ef2508834a013289c13a8620d4133000045d48ca41e1244e48baad84bf7960c384e8b8c54e160a3adc0abd2988f414ae038990f626e200004ea47c4a0f800007d00b970b2251a2000000016262300356c00000000000256c00000740000a5204d89b1b175e7c24fc700002080000023180004262000142b87d4302a47088db8ff040124c4897b2a134da61cd4f6b95741dda89d449b942f18f021c149a9a4d15be1fc400000002d3200000001e53551087ad008073657124010a008000000026a43a3000f17b4000000021981f7e0000226800036801dac3938000223230d8ab98000486c9038a8a09f72c6c54d939b0d7d1a6484114649cd04c805740375913d1fac84fc00025c92014564400018cb20b200005bf92a51b1600015d30000058cb065030ab992f5237286770ecd42145b39253227f527063dc76126053a24778c3fa8c7f0000000023700000000000135c054a0000ac640001e8f0000766d5b2a30c418a0000000000024e8383c836000041b29d3800016a025f41d9471f27fc56da00000001b81000000012b6000000008ad80000000000000000001b710000a340000192d22f09c3028b1b50301265c0fac9b691920ac2d1fe27e546107ab885d00000966ab640ed0055397a9f34bc7a1db01f61c290d28ae73ce28cdc4fa8a8738ec12e80000b3c49f0aa9c9d2926b2a162c9d207865600000bbcdd892e300006f4c00000003d0c00008c813cc51704ef00001d5a2f56000136e80000000450c7259423102c9aa8c8500000000861400000004710
  | 66 => 0x43ad8000000050a801480001280232885145ca066d3eb669dcc7d201924120ab0d3286164f20ae1d2b1a152532800000001dc71bfe20bc97e0a7f000023cc000229d16303c4d3e890a34dd88ce52ac192f26823fb01598781484c20e898f15c90a169c0410e1c932c22425107e25330786572d230a69d08b661105ff88e90000944833e13a410e887705d029f5018e2e0d5fe0d0500000000a399d172462259000001193a6e0000000085f1256ab8400013cd53b457186658d242fda000150a25fe00004764000217052a09a70c4e175e493014650ff8099000000000000c28100c20d80c089b43c7aa9e0000000058200000000000000008d440001bda4d3405ec7d604f3427a3a006e720ca49c888f919193fe364219bc0000000000085fc0001dcd2246000000008e229381ad000000000000af8cb1b80000000b0cc00000000000000144800002e080000fea0000000000013359bfb2b487bc00000bbd29704a8560680001a3800000b02c1c1a0446d829e115255f80000000230243a06ae0000000023f084d4a6a884000867854839a1563aca34653d8189a000000003468ba13fa68388381a6ef07c2000000005a91802acc8ed093fc0000873899487dd00006160ff89df40d2e4b84c7516431b9ea164de321d5205aaf94f7410b22c0c3e8c28b94aa0b8a8aec36faa26112622ad53789ba11b2aa95179124339fe0001006a7841efc5000bac80924f5e4c70cd0281929089f591099e73428636d5559174f550a3d64d1690380c742a20ce10d6c18204d0c6c51f9f13043ba95c401de02de78bc4930e1e0592543d5f829f80216a72c0000a7b49a2000157300003e2e00001bc106304304df8e171af305444f1411e278d04024b0400000001cc236890bb1f81377c04d00000dd2422281f40deab2a27d66534277972c05e2221c199998222240ee159b182717a216645091e4c282820ecbc506ce418c7be80000c25332000000001c801e2e49501ba9cda48263de11571683156441fce469a5f48048fd8fc005c711280000d150000175498740001a270196000120e18f3162c9620bf80000000000001d7894d0000affc1191d36297813a83b6134c1ef62a6ccf619df0cb29cc4a4999073b960a40a959b49515e8a5c6450a1f43ac1350aea01f841c87c042cf800006347a4021219443af670501620c2730925fdcf1b000000000000699800019da553047418f20d36000000006c3038e36e93b99a2b00003350000026217147e9848d208000007b1896b83c63c9a5160e75893609361d911b70000203a0000a6d218b3ecc8cac0000000571c4f749c9000020528f6401f062a087c604512ba6e9000000015e1800018529460000277200000000000000032a49bfc00025fc000053501cf000005166b68d4fa9994b0cb0e84cc01ce0b2a1f2c2bd
  | 67 => 0xf9174000089380000bae000000000000000000052fc1a314ff239a046095b25e5076039294f8950322047378064000019725b740002b4a2fac22496291ddc5856363cce4026a3d040790000000000004e70749228f4a5c3fc4822956128ac36706ab1a59485a94152638d641f425bbd2eea4a83648178161f9ae456f40258da21d7206727cf4d1f9015007058488770000501c1d1ccee857541e0a8651f88bdf048a151cd200bb644168ac80d49f3517aca14405da6213778101480894f7000012c8a5800002bb40000099800000009a5032589141574a1f8d449c350f248ae11e711dc3dfe72d52238000000024811e8993b0bf837e00191f4302b08fb40d80000579ab1401428000303e0000da9090a08040000000157f0ade40512951fdd246a070c0000000329e0854b578ff400000000000000357c4a384a1b000000009da82ec91f3015c2d480000fe000f0478c000112400005b640001915000059f80000000165e000000000000a5c00000000f2e0000254000000003d48a29000017de405c000000015a800007c4418d831f2b0020a40000ad3394e0000bbf0dc0356434848cb205700000b1529a00002c2e8a148180bf91da667ec0610a4232bc8cd8d9380b704b22b680000cc8380a00008a00f7508349188f71000049127d5c5f3a3cb00000000b8f1d070c5054ed523932d4130756043d8e763360358000025d90ede9458000122a34181588000000008aca740d0780003d7c5780be2236c4d426bc4f4c150838660000fe3a2fd0000000000000003e1e76680001d4d07d4000000001d04eeea7c09d7800030fa000000000003664000072088c2000000000000a3033a22d20000112b000000016208ae2000055b50d4800000001e300c00af345e259ec0000000000000bc962800054dc72c8b3a80003a2c0000000000000009fbcd46ab9624e007f00000a8e00006970000213b0000899c66110c70e7c82b038400003fc29a28000164f31045b54ccca815037098e004e9a972ee880fcf6d18c734e41c050b1082145ce5bb86228df6207ea238e5295d64ec08cc879429c1335294752b522734ac064000002aa61fd600000000000000093bcf80147a00000000000000008660000000118a23085d28e5504f0522c800c000109c24d477848e380001c4887f8f190db31c866c44c710daa181e788961523cf2fea1f64af28cfe3ac400000000d720000a938bb00fce009475bd5618b7d0000442503f822a1f247de40001bff476600008498082512a4cfcc8c24ab2f2e000000000000c6000000000a8030be6b7d02c17b100000000a5215ce00009fa0000000000006bfc0000000000050d0666116b16320000a1e29a900ac000089a9b2828a4a1ed3cd900e03de681495e27cf34c0b0f465b8a5d057a3c6ccf1a3c318a81ac447a968f425
  | 68 => 0x3e062159100001472a0e013221870664a8200000524244400000000122000021e80000ef1238c000000029b944f82f047609eea4fc65db52d98eae0f5a6b101022746309c6be037f00000836a62d34c9e951ada9f2074d0000195a497808e8aa23768000000010d400000000000000000000000bc08ac5583646684b9a23500009784cb8922c000000000000000000076146958000220c8c909ea1d76000000012849af70000a438aba8000554662b800008ac123c00000000b5501c2000056880000000a76d46d000020d289b800005234ce0af98c3f08681ec400006f000c5081c856800007bf0000990c4832c43000000015d69e20000000eccd10a3857046218ca59d2051a619d0f95272f53ca43ccd4d9a5810fc91946f597712df0337465c00004b8e7a8000024d056ae0000f3d80000000000000009601f4e000000019f600000000205a1ef000000009a30000138a98889340b0d3806a260dcb21e50000000000004f7000069411d48ea957ac1bb415a2048218800012b226893f2e00009fda3f9556a802039587b6034e69690810f4f4b80325899d8d92490c8b38000017300005344ae9185956a215a8ab0000001d86ff0ec41ec5176a2cc077c1ed9163e8ec40000dbb00000000bcb12ac000000010c226c30dd40039116967c1edc000007a99fa000083754f0000000003bd072b00004c14000000000001088000082920a62f2897b400000002fb2000000000003e8a141c0002a232a0400000002c5a20ec2ff84b680000fb4000161403200000000000019941a722d811ba000035560000c6d80003e504214c1d1bcd26947174000000a00005a749e400004aba7028d418ab64dcc0000df303cb1e106fb0b20a50b0354000000020f2315811d8436800026fa434cfab196c565e81a00001bcc04de28d54bd1d4b27404ead1de85185524775158a1c0733c42ad0684822116ea74c91b4103d179a537031992e23f0874a0a10aba01bfc9fd955219ce25bc39745188f47014e70c40a09e1d464a9f6498da52c50c000008bb00001f860eb52ed9d4f570a77e037903f951ec1f3d124a42309581894df48dfa4a4c87b8d5719e000002f28ee1a8ad12205bd50fea25046785b492eb8351499a6020fbc134e13347344f10933732f02a08f5c909f4e9077050079ade37826a415c30be42eaa8af0fac217205be108ceef96872fec55f1114287401b457e0e6111ee2ece2cd43ce063d17da6ebc0001a8255f053100000c464ee071503fc908326e480ed0aba632501e247c00016fd00001db95299fd9431a565cee6106649ee0000000000004f69eb49348000000069751eba08825240000a6e8a743e4ea428d009c2f0000288cb4526a41c16789d2fa9b3e539ea6f514407b400000d54000171f4fea8edc2a823c0336a00011d594080000000104
  | 69 => 0xeb262e366c0000ef300e92a9c3d080000000496c0d28dfeaa120d0e0d749cc8f4c266c11f8b3e81063f169f98e96a0b83ec070a80000000149e7ed0f7a072321e80000e8d9dfc00de00003f921e40598465d17c8f7c4b1e0000b388000000000006188000000000000002b182c5a162d2648000000041940000000000000003fd00002cd614a42eb26803c9058851bfa5870a768ca1019974d31d6a6a9575a24127286c3d1821b8e57981595154856746368d18000000000000000000072a00d2000086f800000000001137800041087170000080b343a013490c16e30000553c7cc9d0000000f30000000000003ed11e817ae4b723e6d1fe800000000000cd60000000036a55aa000000004cc0000003100004f900000000229c15509cd917353aa53a8000064300003ea00000000060816492c2800036ec73c4000000000000000de50000000000000000000244aa6b4ddfa5fa3b5e557531e1a0225340b3c87f800000009328f778801000000007518e18445e3c548de26ed370cad4104386d5000000013ab800000000000180906a0ba8123cf72800006748b880000c2f323800004ecab6807ac000000000000600a8791ee24dc514a16110b31daa462878a800021614db028f4e24000036f65c9c64115b5110a0000be29a742664a52ce571d0a00002f088c7000000002db46ef2a224b3e7fdcab3800058a8680c00014d92d541aa507b2b2739e631f400017cd0e4c1f900001b7429f2000014c800023e0000012701c5032a8630c8b800000005308000000000007e0c00000002c5c2fd43b40f14000000012aa0000000000000001d9f4f122c401d7083100000000000000010c07f988731b9700000000a9a80004f102b5800000001b3c188923904890000000000000b01eb696f8c3e21ed55a05c60088a83e1fc29630f34002400002b04214082655ac0000d7620a80fe621d8c8f8e392da867c8bbe232e55ba0000852ac0a414e040423fa1904b3464f95d800000c8e0001505096600006768b18800015b200000000000219e000016b00be086a88680d6000000000000f8c8c3900000000ec6a3a30000a844ee7108145ec5a0909483a8000000003e40c62000099c800020312cf41f495bc000007d245051f5941d20e415b4aca878b485c0000ffe0e9126305a1094484c7411e0000000021148280c480000000086819003cd800016ae8b28f6b0efe000036ac000005d28860bd85a30fff0000295090e9e1737de47bd5bd800050f802b0cbba60100003a245898e0d49f61ff4d4f1d1c0000000102f81d1000000010f3000006a87bb452c0000255a00010d4000011b400012db0000000000000001ed5000037dc000249f2b0eac540002a7500000000b7d000040a24a2c00026282ca860882648f721dec8ddc7602bef40ba0000000010820
  | 70 => 0x9900000a9e80004a5200000001689145a0df948a2b763b666bf8b5407423cda6f0c68da14b09c4000159e80004ece78f87dd8d513c4a2a65495a55a07120000bf3a2c63fb67c691ac800056383469373a56810180000000113746e69fb058b81472db883d00000a6f58b05bcd18b1af2000025c9544a2e917b200000002ae0478417c9038963021b208386e811a64cbe7840000210f3e4a3168719223343c618480000de757183b1c0f700002dfe856d35f035951420e7553d263e48ee000081a07ba21b60000eea800048c000015b80c6d1e566eb00001f0509ce008145b1fa100000000000085808f80000f41a68e0000432d33500002a84486c7fe0cde03a87b4880980003cf86b080a809953c50ad912e9231f1df8000112cac1506ac8d1c000296c000001f0c31823d504e068c9bd267a4a3854cc2e580001e3e000000000001186791c00000001414b13800000000afc15e416bac21275a0000d450000000025313ff877d0000a08c000000013d64298f99932840e41a595c580001cda60800000c26023c0e8c0000000000000000000000000000001f40000000000013f50000331851340000944246c3a9534f00003d700000313017a0000870000013ae0db26ce0b898d7c58960000ce2884741223f180e794a54ec22130c8191bb000000000001cca390a00000000abf1f72021095aa77b000000000001d9c19162be4c6307e1403e18dcdf9a48c4bbc73f8ccc00001ff227a133d9bdd32a2b069115a602000083200000000573e00012842a7400000000000224b20485ed80001155000082a5481800026a21ee103caadb11601b9152eaac8041496608ee9bb7501826c043918bf4c90584c8be136f309400000048a4e352800000000000286e000000017fd3a080000b6880004fd6000008d8000000000001c88f851d5e0000e100fcf00000000dce8000280a0000000027915540000000000046a88e340001c842fc2000000000000faa00002fc1e700e806dc0e379ca656a659d00002a7248da00010f0092f0000add4b9985e35870637d436a2964cec353902b0aff3fd27d4c000159c47122f0076b8000000077d42cd16cb45342d9d528a41716e670b0e712375000016595a5966232f834f515f8e9511884d4d1fd8e5c23e2449c368a3574dc2500877e800010864f980002b4f00000198bba87fc1f2a989126ca867304a08d84c08eb83b300b780000b5314f03a08000168b000075500001a152eba00000001ded2bd8a3b0cac1e3f090200003b1800011e20190c7880001c880070de7221c056470643a4a53f159a501c371000025be532d51080000000000009e000042360000d8e03e60ee8000000000001b220000000000035ca8534ef600002f96000000007ca2c3800014dd0ff6543628dc75c8f82414652f40001ac31376ade54
  | 71 => 0xc9b9a7030c200000000000451c441427711a91c0200015aa8000491a73100000072503c5fd00000000103833c800014242200786c0cfa401254e452c999800020de89b54d1869444ac0a1144f0331000000014c68000070008880001db6368a0000000299e0000992cec7000016f00000d11000039744a742608000000094040000000559490a8000034900000000bad80000fec313892d8bf124e6000072d17781e4e934ce31886309ec3fe0c91013824b0ae751aa9b23000034a47c61e5600000000a798cef000000000000a6543984ddc00000000000a1ad31e95300000a0c84460000000000000002bdb21789b1880c80005722a7d80001148011ea808000225d000000015f895c10000000075d84011b6e25e46ad000025e46048f33a37605140b4526923700000a21d5c22579284ca42483e8000505c0000e27000007f070540a190f2000039fd184a38a1d5487a853caa6049aa058d49a0000007a8ed951f17f9441a045421323a1183000010cd0377422663b094f951e4b1a52c800007ed3d90166c3b0832756980db5037819b2e7a27494cc02282156659cdea00000174668d273905e03f42e381da9e0137443edc00008ca033200000001170032600003a6a4030000b02c000114237ceabc4000000056e20000c7698f9000080609d8090d0dce0000819954d252c000045c00004ada000000000004c0e2dac6da0000000069c40000000009c0000365a4fd2dca296d2128000527400011cb00000000715503a0d77000003c45bf04d32e62965c1f3a87d2c405aa53c78fae02ba88d8e1224752f92000000021aa1758a658ce01765000012580002a3d1942000076a8e7a0000416c00022c50000000046a994337d40c5d12e1f3b1e88a5e03dc8000103a43ec294000025b220ac00000003eaa000005b00003e68000162ba78e11c65f5000000004da2000000026333b200000e4804ce059a7d9502d808d134e87749580b9512661c550da0b7a26d4a47d4098447036c9f0d4dc06173976541c8eaabca0130080c6f5234d314ea07c45e0281470667c045e9cd437527625440249d0a804dccc74122f519e0e9c025a9d401de859137224c22d483844ebba0380acc0000b7488912ec60000a47227b0ef26eb82220000000000000001ecb00000000000138300000000e2d0d0609b61d4000010e90000a16c0000a15000041a00000000000068580000000000000000000af8068a000068000000000000063004a2206e0c74b1190d700007a30e1f99391f1c5b880000131000085e0c6280000bd8000091a0000347a760c0000fdd1094000000019923f8a923c67812c60ba44590fcd0afe3d9e92c834090d006704ac806722943ba600001c619d42df80000b7babb53b6804bd4711d7100000000000000000003c909dc00003f24000154000420
  | 72 => 0x42aaa4b8f0e00003df83d180002b8052e096bc000146f4b6a44d90511f6c527a048c000157e110821187a5a6ea000000013be1dee558a51209af1bf2025897fd11e800043e60f8c042827a54660000000253e50de5520ee295e814e07a952e4150d1c701721102183d58100000b8780005056ae284e200000000279800000000f4600005dc219c156aaa686aca8564ffc493054a1d80118076440c484d142b259c04411dc058aa72555670000149421fc46980cf000099f462497b5343629700000fd748f459dce76130a38347224194947d2b0a99dd5039e1e10660df4e460c004d2e8294af9a0bd0000000000000004eb298d4f9302892a40360d5e78000261eaef0399a960585eaf90c5681e811a2938c20880003a429ad80001b664e0431a46cba9ce00005d3813f894f20103c2c0001e8d513a690800024a00000000067580000000000030f146b4f6295f55209fd50c72000000011cc4f0019c868519d52d6224580002b9223a600f0000161b238843ac2dc82ad00004e04000027800000000000208247b03b952488ca60000000000028bd000043f51e9000000000000000000000008d980001f7712e80000000064c00002990d2b2b9e53e4122152d0c7646de6eac000001300002f4141e941c0000243c00018bd30981978c22895834a40f140f3936729c65e4450ea3955022000010800000000000083d8f031ec69240000098d0d8c20407420000424007dc0001cd53dfc00011139ebc0000000000022a610c4a22c1b70000426644c518f26710f08536000026de1a6000008d296291e7800009838d12204c0c2400000000b849a4878501d20000000000019f156765900b0a2c24000062cc0000000018667fcef8292215ca1ab88768000391e000000013f20384a8d86058e53000000000d41d3900006308ca00dd300000000c210000107e952088e000000009a3ce61ac4a567c08e4907008c24aa04ec0000e62522a0000a5300480000000132497ca2936893c0002b83264a0000f5429ca00005bd095300002c4a8140000000046b470981cc298855421804000172300000ae8dc211b122e4000093e8000364cafe00002bc019a405ac89400000000000000028083f467984b7510c9558068495b797e846169bac0000f45000000015221be10788b0010219de5466a907c000111f404aaaed308925d00000000afd897b000040ed49b9a6442e681b05dca3e900002d840000000309e256452f104a4c6c00010830ed241f482480000000291090fc4f985b712aa000029b0000000074551cd88a4000000014a69e871de06704be3957a28d260d55da2a6623f494882bf92853bfc4b2c432046c42462038c33053813ba8984f0c0eb2264e39481b89ca2217624c800c98064cfe0e0d5e588242f7e8a4cc060ed13ff01c0926095a000007f40
  | 73 => 0xc17d2931431c5ae457d9a8c2568000008280001a1c591954b80004d7a7084e920cc71bda48484f2001e000061b4000000000001684f4a0dbd320a97c0e438000168000000000000162a000031b166a2354000000008ce000000000002a2b089600011018e1005ee492cd1a800000000de93be97a10000000000000000000000000600001e0285782e0000000000000f332bb14a341c0000006e00fbe088c0419b83282e2750a2d8c8f4c58000000000003ff6a1e40000000240458bc7890000106407fc5c8813d0000891c8239abd2cdc000107a8aad4ef48e69548a047579c00000001650334e9cdcdfa0f2300002bb5529093042cea82d4e8a60f189828fc5f1000007dc2fe000013ce04da7a280000a8d26dc0000a5722b5321a200000024ce0a0ca9d800000000000000000000004c6e00009fd0ee4116600000002a5721ce88d0000091854c800000001e544c0000000c58b0f0000000039629874e7200004378000169c3014000000023be456c00002e147201c500000f6d00000000adf067b06ec0000000000007d69ba0000075335a82b600a2a2ee31120000d3107a1000000002d51fb74f8a0000734895700005b1508a9ebd000006d0d7509b7076400005cb80003a76970c0000000477c00002fc8ab739109be127308020de025e0f3a224852c217252e89c04000050b4000000006fe651d55126534432297c61d02ed41ae503117d17123e0400000000c7046424f4048400001d6a0298ea9281c37c80000b2e24fc0c3a2a5d59c000009a4a915204882d3626abed4caa6b52a80176c00000002c8e4c442fb942a53862ea057b99d82efa669400000004b3a00010071e06299eb098de4a9fb0e2c1da800026e050e000011042459033a958800000000504000101d000015f8000000000000000b04c00008790df81d287c40b1a000036c523a08cd3d340000c5f1c82000011448f50e2f1d3a6728ebe91fe4d58000093219f7143600012a321d229249584a508f34313e0000d2ba6c455c69830d0c8b3e36543f44bff21c20000974c964a3f40000598427d80000ae8624c749800050862d6c1a09b050000426cc3d0cd0089c05a05c4211726180000a0700343d5a67f06a080004c2038a0000000000000001579000032f6000000020dc184400010829c3a0000a298a71025b544e3cecb650000000083943599c1c2864534000002f53f7c0d20ed1000032d4acf071b00000000000153296eb31c00001232183400001e3d4ac1e2c1b201448045057a0000177c0002b1747680000bed99c71814035c34a8000427878ec0002959000000000000e49196a7aa812a2394506e21ac295930626f24e25507040402da0eb00001c3e0000348c00009c944585c304348bbb000067b4f79842700000000a4e94ca25284b342ae96011e1c549c000005a
  | 74 => 0xb00000000d9d800002dc69b0416000048620000462800000005230b66800000000000bcd000023461b100000f984f28504cbd014600a7a0c0c0000000137a6f78e4eaab7531449bd2ed13ba2b66214c3c406bb111e88c8d1f17422d30a524f9b15d34d1897a0f378a22037823483de05af31cc6fb448d9ebf12a499b4c1b278b00000001321000031606894e6f89393fbe8fb0000181b202ead1900b21a707104814295138a216e8bb0c0a08c6000000000000a1c000028a9167800026be684000000004c74000000000002f1c0000000000000009dacf8393a233fa2890ac79b5d40645d1c1002a5f00000000cbb26f12f2a0000f189b7500003a60103800007685b795101086252a000000029f7566800013668d1f24705628000000000000000d21800030f2aa3c3000000000065b434592a00a2086d41d5126600000bd058089280d7e57440002c040e3881ac118abdf00002820ade9ee10e7e2a3075024ed00000000000000022923ca5616a9ac0000509c5cc0000429047292570e6532907278b85048400000000c3d803531aa7cf004b9afa274ea32d5dd97360bec87a025da78126123c64c38233001f21f14d67000036d00000000104f00000000000288a000036244c32aa8000065fc0000e74398085e46c700d5000000000930b74000000011251cbf1bf69fa4c4912aa1be07648b4309532382879d2bf2bf6000042c42dc094800008154aa9239c18e8784512685eb3c46207d538105346c0760557714c748ac1e1c86f266343f814683f190350a4c0ab9474124a28f2459851786a621867a3870f80000000736d2259de0109276dc000048000004e082210c4319fe43344f394eb119e1dd525a800044760000cbd161e46ac1bd8ba8a0d4337e0000b7699cf52d686cc7ef0bab000000015d0a44919be583d0a7a35f277c13783679e7d0000a9b000000002aae698d2978ea1210040d8ed823b828fe1164dbc163200007c9000019871d1c0000000000037546d540a40000259c90b156a8f1e4e087fa812f80000b4c9638000121a4280000000011620000000090588122b3600000001bb84b26421085a8fb00000000015b16db06545890559aa0c42446ed49cb1848377230c821600002242000000002a00000000054b2b3900001e390260000115c000056509db0126179842a1c9841ce42c0fbd8a272f7c6e9cb51a43945740000e2585114b40735c35686d400005c04e0b000014ae5b0920d18ee04184f5c00005760eaa0000000000000008bcc32928e0000000008c3a2e026d25c2cac30706296831e4cde862917d65fc8771010a412e104d1b21ce81b46016c44baa2e22fe0098efb92284ec88beca2107ec18a6a00850302fe219447ed0ca09ab066c7c1055ea10c00d85b8400082a631f81035599941e5804959917a8b9e0ccc9df
  | 75 => 0xb5fa13654628eb00002a9f283e0000000000008380000000175c32845ba0000000045443ca94b4a08127da301c00029570a5e931552805e240226cbc7540d7a141a0000000002e00000000ad09122000000014e6800017387d480000c1256a45100b5f0000000053f40000b3246946350000203c00008a100001b733f7841048539fb657e636b089984a9166e99a420400000000149d0b5009c4ede796822d29bc23ce7434893170e240e44a4519a812385232c12a1a51500001bf4e9300002d98a46400002a94c828b045672a2410726c50e26197d000000008bf2ae74256a54c8642c0c000041f86f7a8ab578287d8ab8000022367c40e3d98643d4c826d2459fec2f08000000026a2240c6c1cd76a9e81d1050b85b621f03f7e467c0eca4515080360109c93ef145800007a8114d25d0137d0a3829a3fb8000000f80000f2c0bf4918000030ac0000040902803ba78d43d52458104a00b5219800024187bf411c2913000080500001314470ca71088692ee000000015df00001628044ce9f80752a080000000226216ba23c800009f4383684980001bd92d6000011a096073eba929c5618f6408989c8069b91163c8458a88b495db18baa31cf5d09cc048084d0f680d4900003fb90fd0000103c9d04766098c19a296e8000174543820e7cdbea2220000abb0cd71962044e3079437000000000000d968000346696b400b19de00001c6caa59e6e0000307052880001ede07e40001e380a9c9318000115118fcb15938780000ca6a28c0f4a25a20ac4db07e514e41190acb4d92856e2e8231841cb08d4340c263c1210fc752d4b04415c8a341df6444cc592a79411c4c58af8955600b0694cde911f900000b9caafaad10000925827415c20a963718fe5038725e01cc05e32a834c167914b9c0b4c400a6d200000000000099b000000000000000000000000000872d19117dc453ea798e200c5747e028640000ba451b00000d6280002c9aa2f000024374eac88a820916bd3fc46af003f95cc14d404a8a2785200000511c2d0064424ca0fd4000000d41c2000000000001bd80000bf491a10000aac43278d5d54085c6d41110fa3dd84514b5c0c5b25d81e549871a68400287a4857033e20f456f09e59d6c4e1c02a86670fba47309d54bf31b6c11b6973014e0c2e0e50063cd5f929805b052b01f9166910ba796470aa25e331e22d836b26b72cdea5dd3589253208824ecd0e0000170caefd4540e3323048a5534304cd44800000c31281431200000525a5071112496894600000f3a00011781dd7096064108f58cb104a6295477088153f329bf4ffa97f356fe4ae516fa99c4b96a688695291a1c9c063947b81b246c437f101b2795329835509008eb43d22764cea0840305c451a0402120f4e3e9bd8eed95820284028c94797ad1348918d01508e
  | 76 => 0x6c10129029148800010c23e350fb8f6700000000bb594862278000139e80003cbe70c108b192339f26b8154e94b6471823ec1fd8ce432402f3d2c49f7a067e22c419d9a4829c20c08817045f09f0a7a52bb965116b41d5c39d80d91474a6ec26b8b4f2546a2883bda2900d048f2000027712c8492b00001c414eb0000160a12b3426000009d5054f061418d400019cb000000006eb8000028000000001b9100001f115029521359445e551b800008b87ac40fb000000008a844b400000180000047c0f520000aabc334953236fc2cac000000021e29154000037353348a64de79b1053bc8ac4cdb947c00003cd4a3d918b0000a9a80000f5f000084400000d1300007b743d4a6574dee9b3934a977a000071b04538fb5000042d000000002e5a16b1403800055400001249a43c15e05cbc12aabd41d96000027904fe00000a6c4b0aa68000074a52cb1725473200010a300002b200000a0a93c91af040f868a974825501818bd81ced2b6079e8ab41ab300003370268047b3c3e49c559580003e46a444e39000000004c889ac8a2902643b28fa6121434d42bd85948005497e35212871579000000007338000133800000000000051e0000790a6af000000005a51938000015dc000000049968898055800000004a4d1d9000035421118f538c0434aa0000a20800039c629c4c5d27542d8800004fe8e2b56fa426000022db00005dcd48913e23b0855e101f04b4000036e433e80005764173085e8000000003b87af009106be000077f9b631ba82d9021b26cf0e88322404a95833b1864c525e2924107889e89c2a877000050a0d998a173c8286f48a398d81578000123e000000f64f4432e97191f840d006b380dd466600000000e8711826e2000899aa30d437c8fa700001e6485c44818000000000002f3a91b236009f098283dc3d9c128461f942b0000a29c96d896545b8aac0309aaaa491c93c87888d3a31c8719056aa16d0c5800006ed05b156bc8b0898d0f9711027a243f300002c164f0838ba59207169e0cd4317a743b007c46c11a32235881dcccd990157286b6c82f802a22de5b7d1be927a357c658d23ea254461e45680000f4e07b200000000000000000000000df34f549b0060a07a72dae7910d5600002cc074e141d8000029e7ff4ae426f3000043740001e33000049d8000128356867f08b01074b159055b8c0090a94a1488c000000001e0859a14db8dbf312840187e58c9e0ffc24a957796d83e743a900000fe500000000cf3a668044800001d5911a4aaa0000f0796104b3c699847798e7452410748dd1a2656b019880000a0e0f660000a40835800000000317070448e6000084e80002f183690cd89c36000040a80001fbb43b22260d35a40400000000a42848208180758a078f51381ca8d40b3151a155c02c88eb961536b000
  | 77 => 0x8c07df05430000000020a0000000000015b3800000003c3c00006f5266a00004daa74257a0674caf809f956d626380002a1f0000a6a054aa3e31f980864330a62f19025554056800054c200012230a46302000000001ef100002fbd2c20e31000000000000000000012790419ccb00000000000032e000059e47d2999c1e6632f800011fd000011c1130248833a483990122a1a0d920000aeb80000cc0397cb82933a111c5bf834e89920a1a000065e10f94c383fa48e5a70300004d5005e88a317fa0000e5b97464bf000000001df30000afac092032b3048120c12600f612b84f693020000037ea4993e30e0e032e8e4c0000000095e000061204990000a0d0a4d145e34fc77bc9cb8f9e3300a79d2cd830e03da00012030f7438cc966525f02be00000000000224c30b882fc0001e2e3c94a3d09ee151020ee8400531980711be27a928896495180685c1858144000075314d010c2323455a49ae821d00001a10e088a7c248848e4be19cc82f6856e400010494f7c0000000161d1c0400003b90000010007341239e880000689000029200000aa4c000071839581df80000a5200009c9c9b100001ec01100e8891ae37407da918b95a7224a63fc060a8fa46548860e9a261929ac0b70ea227bd4f8eac055c800a20000a1280000caa4c127d9000000001c2470ac714892200000000000053240ec2c0cd3a9c920000ac24f2e202110d4635c670267e1c8c909c0f027e402e47b00f3f25ae412c262400009af48321a0000018c9366a32a0ca52a1d255200007e280000000000141c9e72500800004259ab6431263f94be13de37b8000000027322b8aa9640001f2b0000539400020ed4f1400000000cba301a00000001bf01a980000bea9f743f664391474a9804a4a6000000000016f80000bc3ab7424f6000000821d3000000004e1000055984f615178a2000000000000277536e49dd000023ae00000000d778000283200006ca096b22c00000930a8e7530c84600000cfa000046f40001d3100002168f9ca92156fc2f111c0123e32688d78af508ee052a0e08e81836c002a047c0000000368eaea8d338d5051ae0000000000048840000000000000007d7863d11e61e80994400000000000000000000000de20000f97000000002f6000000001f2200000d78ebd034caa283c528d216c698a83bb15aa54200e5d05d9a983c7862f0d4e9840171633993f9a713473a6698f8a8d473c5a7e6d2fd801d4bec40603d92705000000003af13a606f233114c812e639dc1d9cff00e5139f077f4f4ea34514d2b0803e112321cf0361018395262e0063a542f21ac40504e4d5d9a0f13cd851404dc135b390c1ebd27f03b90000a024000188e06507b446648f00504884c86521b3a0260af781ff29b40aaa1e8158e800000009cf8e11800043a882909758c
  | 78 => 0x4a044ce93d5345c00007ae2993000072580a58be8000044a92618c9941d6000129b0bcb36020000000108800006e7157a0f7700000fb4000000046409440bc6a2891b889650bf897573a569f24b73a1bb112c000000011014cb806ed1758e3544e42f5c1e885bb247697b101c895a512217b4000057c00000000e34170600004878ccb000000009718c0e21920c3400000000000445c75a000024450466000000000004cb600001b0800000007e340000000000068e40002aba079c77400000bb200005acc0000000380029b9613a7a84e605e481ec239700000000d44188a51e6000000025ce323260c4f61267c18ea6624daf0000129205f8764800035740000fff000033d41a8ca469db821b848b51b49c8b516e763ca8d80003dec56dc0000668359a12fc08200002c32589c857a2bd06cc94dccfc800008c49ec84e1a03d00009940b029e124b42a67c8210d2f00005e4d0cda6793d4650ed254a7400ad2955c4e8abc920185da046c1ba637b636c955c95724e208f9877d2c1f313a807935e27f72fba43c155fac1e57260e5407ba70741aa98ecf4e12e413c69ca10602ade42988d8546a0dbc51fcae5cf328e6a15341140f039a0d3b7a1128bd504a84b4c10188d41ad9333465140f29f1f3edcaf6098e98771a18aff43210f5656007108ac716445390ac904a0844513fe9c181be04c32794276095fa9063ef87694fc61a200db600005020324349c578d1f38bcc00003a1904499b80356765059f8d6a22300c84f6a111103fc44b425ca0ec35229a04280a5d834520ee8947260e0b9c2e4c2af061545ee5ad54328d0b000090c89ac000028881d30c4d8000287a60a53cb00002e420cf40001d55000018c42cc07d10000000003406a558642ce09e911f257f4847d35d9f7246b02f2036820b11e4a0610b1d04a0574699bc8102a63365601b554a2bb63b46076ce631ef7098412512832abe39c8a2c91890d0456262bac82a117d568463704ed04d811f887454fe254c2bfe388409b00b53fceb018660131f2fd65d501c50bea3b2a06f80000000305c00000000e04102e00000002017499e00006f4800000000000000256b2d7818f1140283c402a000125c00e506bca74c36e27e110b20001215800003eaa504137166d000039c11439db11e588c54b9c8e8b536c9e9836b910b569c00003f0000031761104339885750ec2c087c599362a38b07479f8000399e3c69138055200004b700279a4c50ea00002f0864951547339152ac46000000000002b283aac0000a3286182ede2f70acd145933e62814463897f4f4a6f7c0001f701766000124f000007e231355d208080f823460a7802e323721c482f808e506ae7d08a9ba9a6000063200000c873c120710f4f8a071dc0693c6c691b3319a6a98dde9faf2cba7d049b209c700000
  | 79 => 0x26f09fb86a808cc68d9024a3d34aca63013dc8ece3ed2933113e9376148e6ba50ebaa00273a9858b3289960f3e6f600bf80003cf24cf0c3c0b4d1ed8000000000004d68000000029332bc2a14d1978be61552000000025950000000067b0407000032fd16c25c448f02d24bc480000eb056ece36a7b80000000000000000000000000022c009e26e6000022832bce1a781a7270a1344ab50e0490a23fac4c042eb80000000000000001df0000aacc00000000000393cd510e2c000000000000c1d000000000001bc0000000014348f8300007cb10d794ef00c034206f1a4b734a235bc00020cb3a3c818c716a5b857ae0000db3883406967e44edf9498000000000000000000000000000000000098c0cae1b6a0000ad00c23000000004e8439d00772a2602940799181000000000000b0e4a3e000149f82ec0000000143200004a08000000006a2000054046108bf42bf4191400028e43d02370ca319a0b3a92170c000179f52cc42285390dfd25a20000388059d00009aacb0400000000032948b800002ee2e9c32a80000000000000000002b56a2fc00000000000054d35704c500008b690fc985a00006bb8e4e02e438a088504140d5e48e22701046a98f12c67820000136d00009878366202d40d40ac08da0c2a215409210e30e3a093057a4c4f090150849e7828ea41b00000000000000017440001180000032a02e080000f2d2ab80000000110449e29849426840f00002999390943f0000000057522cb127800000001d9e00009df888a8b8724901fd00000000199e42800000000581200004d3016249f200014d584780052322076f00004f0a988c8861df60f1a8690c90800042d85b040000220000079240002a673e940000a6980000a1e4d8534127384ec481c0c0709cd093a54f0686800003ae2c70000256916a00000b55a64725a67f391fba8c800005378c0f0454000000000001b3c000054b93bc194e17080a48642275100a8000001196480000338d4bc87de4b627978fd417581c7a03a092b28f22bea3de8000151f20ae7ac8c831d135502000156486093308000014b27ce2fb01b983a9000027ac0be41c097ec0000092800000000e3a000074b159900000aac40c9e960876a3f400004b6000085f124b83df0a10ae705730000000000000000000000011cc0000000023800011ad800027d403c949b102c00001b34c5207932d189fe8fcc0000373e176000016161d8c00000000711057e29d84d51249042e10e037a09df44d437d48c6182c513851912bfa5b74d465e0c50c000008f492053c908a1194e9bd4b338dcb277600000000a0922948420000000055fe000000024a152dc27e9547020900006b3ced301744a407c60cc300000d7c1a40567800036a2457ce21800057021f18000174c00000000000000014567bd55fc8
  | 80 => 0x188d00000000ed48c9a1d7cae34f5a88dc528a14cc5df9beb013e769d47c103c325c3478403896e33dc4f7cf899618472440bc7f204d552306925068ab6c00008fc88c903ec2b7e7c7036088e14d8e00011ff8000000000000001b2e0000621489c0f09000006d4e7900000000000000011980116000014f1c1258307ead6149491008e1040148969c0000497c000000020c4000000000001d143f04000007619f04fd800027990e1a000008706f80f320000cc5000000004bd44a500000da60000000000033fc00000000000000000008118000000000000000000489e6bd00000ee907381f7142e112c0000168cd8c0db8377659e02a40000000072e400028280000b11c10b1fd23bac0000da60c3d2f361d20cb9253a000000014b680000398000000000002bec1728000000000006594000000000000000d7a800033ac0000000000000000000000000056c4af1013920ab2b5200009ab000017ca520c0001db24edc2444000000034b630e0621249552d025588fb80002b4c6d685130a8b22dc6f400000721330200002b922ed356200002849dcf0088a748291020558721e18ccb80494aea476915f2769357600014ee00000000373400000002036620c8f0000000009db524a044f0000000067980001f40000000000002fd45d7d01195894b9e4fe060aab051e046f880c8077800000a4c1fa2b37530a06780002a5e000089155780000000049806748000398a000000027df00000000604a581453800015f08b060000a38d3db0b7200000000000119d568248acfdc95b600009534ea11fa00ca23661296864e127094f4d8b83051c26144c2db02a14b38000128982eb2aa0000135c8000000070d00000b543a8e5764073a0fd1e702c200000df42e8665a10681a7a0000000000000001b6071f9402abf2247a8894cb0000035a62e34000170d25ca1844e55aac20cb42868ab112fe05d05e0094100000cd668007aa8000244854a8c941a9545bc00014a50f8a191a389ca64a8d93c289c6ceb300002b9e687800000002606000110ba1a143c274f8e7091670000ac942389d6d419e77183329545173a493435e919c3a902b4144188b9488052ec66308ba1320741459029ff47b4000088a1aaa556873f0360186802284ce0000155e000000002c7a7ca000071d4a3a1af91f887c0c00000004ab800011870a89372a45dc94380000000a550dfa87820000240106b0000201a00003c8162834feaa2c519286a21c661fca5f212835fa000030380001cf2000095e900b046eaa349fa20441506a77c000123c2f4a3f242461e0d34743aacd2f1120430c7ef446b282042dc22dc96a8469374880484af804c22b27fa1601ab12447800010b00e484a968e440e329911ffc4fccbf1a9721a7e82140000000520e3bccab18007497472a43690cdb1286
  | 81 => 0x5a8897d9a3425569268fa400003d362b915658634000000006b72bfe000000001b823f84ebc9248000183b48d60000c8e91e52d9063490bb88654d824550b4284ed432200000001edb00006420b9f80003ac0917cdbd0000359000000001c784b76876923d8a2100004ecd41f907833cc0000d818363423412d40000000000093d828aa9ea28dc867d2f18d361fa4986c9d4072e06a6a9706a32818124600004e80bde00009f60383965b4e344348b1107ef1fdeacc02518b421c100c19345862354f690ed32205e4430066b522e29e145cc0000029a1534052197caa20c6b000011dc9f29e190dc6849c000188f000000009c5a0cd44ee453c0000845257c68681c69c8325740000000182a4084000074ba69318e20001281289600000000000231a19b2968d143073d0abe00007f68127000084e8a8880004e5c00014af00000000198ceef1b003cee00000000f061fd40000cb3000016d4908820f930001a86e09306a9972edc982128b901e188266a14410588000000000000000333a20f8e8098f50ebe2ef0aff00b41526ad58d518d730d8e0000dcda18f303a5314ea72982178a4291092127733485bc88480cf70b8203102ca23a407b6a2d07881c9134f843bc3e380df000000004bbaa621ac24570779028d35484f9c124a37b06b424f8265000000000000b49a48a00004d083b8800000000000000000000004e34c551d2210403044a53ab4d512e00006e607d000001244e07aaae00000000bb48e173936000053a800040fc3e6919ea5442a6800006b4910a0d40000157d2583336882b53d112da25a07b300000000000000000000cc537f29264d1099b9000092880509cf4036655b09e0898b2ccca8fcd8522c700005cf128188fa2b64aee157ba1833f8282700000c5f2d681e50043a450244c000061822214f0ea5f923b173428eea9cc7d3000045c2654c00000003ac66ce4eff9553000000014cd80002bdc000119d09e2434032b00000bb700008570850891d00001754599a7084ff66ff801091d62f3075f0d3480000000083cc9480000f6a354c6e0a90f29eaa3e497c909e13e208683ab15cd05f03f706ef908d1c8a8dc4e690734332200dd0978d8820c82e003f29516000000000000604000099e07ce8585034a5c0c00021de00005eb000000001f2000014770000000000011b505b238dc38247398ccd00002234ecb908b31ba8c6492800000a82227d51410f60000022400000000000000000000000b124ee46d008be0fe06f440001bc537d028d90db1b4315c66d5cb322331426e8f34b8d23b522ea634c92724b300007d1000000004f1877c87588b0503d89c8800000000000571c07f997e0e3c4dacc2d92e0081413115548000524609dc9f00e223a34759d2e0a6c24b581b0800028fc000000013cea7b50d3ea188000
  | 82 => 0xb80004326283000000004e2c684cf62198548d46b54370800000000000000227156ee9c94000000000001a90f94830d4b22000043ea33b2866158c9a0108e337839ed3a9019a1f540d6c63414e923b60549270ab5f0e400c64be822430bfa10dc161918300006c3800005350000000113b05e8000000000000000000000006d417643bf2000000015000000044874e142c0b9a3528bfd800052a48bf84870b4b3ca00000c881f16000000006b3000006283794000257c000000000001a7855c80b000000000528839013a600001a4a8138000000029126fe80000000000079549481f5c00006b0547f98870000000129c8000000047a09d603994b549e853f88000000017d0d1c280d38f80000c26889d37000000eaf800038780e1137a00000000808000012f70000000000000004a78423c92320f70000a8e15db80003fe00000f719d0f0000000079b1fcb4ab2000160080000e643fc8a4f000001da9e7c00028ce11ae0000000000000000000000000000008d4ce70000000004c20bc829dd00009b955d292f4000072e0000220500000000eb080002bd61fa8593050e487071dc00021b9095c60084360f37008c7500a45986b2e209bc0d041ebb17ba45e89ff843104286d092991821289c300833f800051ba000099f29c9000000012b980003cfea5754f114e731a22fd8ce6060b1f00a4e43a71c322e1239a04bb00002b2c000024b800007e610550ba00003e160000e2c00220f920001572a006388c00003aa122900000000000165a0000000000000004968070421705bf000081cc00017613c48369d058084200008e98928800000000000000000030e2000043980004548a790ec5a43404680000bd420d800007fd91f088aa39329f48910137b34782d7c81896f958800000efd0000284a396c00000002432a094f7c000000009b20a76000022766e35591978b2d8000003fc0bd250c208e856600003d6e53482f48c591b8e954cfbf800034da7cbd56c14c1142003351578e6f461a9f71332904e18cc000007e2aed000094c0bd183fd0f3424f400027ee490e6d2d108953e0fce711c0c51cfd10602fc81e0856b4a426264b01a56715e8a6c8f548e99000059295a215de4f0c0000dcf07ab2e2a26f8ff2837b10a27284657028e04c2000033c264e113c7a140002c4c511e782925c845e00000000fe200000000000000000000e9ea30d4340000321696909fe83be22f61830dca0d633d58910c0000a6d30ec602d27700000000762800000003d600000bfc068c134600009210000467c9f500001ee4000000007128000050e07003be1633114a0000000067e0f446ba0a769d64416c15c13591add000032ac0001d1825b000000001fb00000843800000004b78000000021210c4243148c7800035003d684eb875932e811200000000310
  | 83 => 0x804ed14fe80000000704062594511b900000d780c2353c603f4b47195452189d740cc0e772482015c1cda8f1000000011dc9d144eb805f5295a75345046784828149043f01a14ab7800038ac11613f6a5f320e016f0833809e200024940002b7c1c0a517400018531a2200e800000000dfe6d340000afa0f4816f44f2a94e10a490780000731059c000000001ae12169f4c000000014d6000000000002db47114e5780000c8ca59c0000983000079d400021b224b85a6c07599eb00004318000192a42020000a7d13340000644400011d810e21688b4b98050000579800000001a020000000097a0b6021347739b54206450d557f000046900001061932c000000009202b1f1ee69931628948000000ef40000699272a6cc01919453000003e838f858344405a0032b8db60e320001413000000000000901aa6d09700000188a9c70000000000000000000a56828012272986353cb569c1e29fc97d10550d441c3828a1075000045b200005012a0d00003a893bc800006c832140000000000000012f020c700005e710a110da4962352c00024082654a7b856a28031b0c858c0001a441d3e0001433000000006e6857900000000000000026a71490670c4be000011ba8b45155019207b421d4acf24690728a6bc000273a43624aecbb90045575075f8fcb28ef56e40b1c5fd00000000244d424000045fe0000c8b273545ba00000001fb247f47674000000000005f4c3320000296ea0c084620b5029a0000df2812051bc265c00000004fe83dc000000e200001f300000000000000000000000469258f000000000892000139a076d00000000a5580004db4620561e000055a66409523228a070c79442d20000482a233000022101d0250c0d0387412f72183d0a522e420249d7cafe242037f003580470df90b1c704cb951eca000091e4d860000298c132c0b29c653e1c73251dd09cf45981390cfa000032d26cc4e85a8732c7e50a5366287a26d09f105a39dc20a428278c71a9051fce2cb80e4ab4704ea038058ea36300000000d6c0bfc0bfc70310000000000030ac2459da81b9200000000edd271003900000000030a2c250c107db4b203908489293e4e3c1c30d6894163784324425209ee238a14b0000092c15143c348ae86703802b0488111f3e00000000edc8d7b10ac00011668b2420aa1ad4883aa0f356a19511a717d23f528c2956b8f93174a3b0c0000000071c69e4ce8159343028f180000286065a04940001ca000006a580001e053150ac400481dbb2b5e27bc5af00d232b239c4add1f9e0d1e000158b0ec4358c000000028ba0d229c9932c0da100005f8903a856800003b50000000003720000000000041fc0000000096f1f0c6e4920b127f35cc2e653d597ff0000735800024a300000adc67600001f0800008f10000093e5228be
  | 84 => 0x3b28f53f4400000b608e00000597936b800003221d6c47b800005781190d738000000029cce3813e93d241ca4f499eaf007e5700fc31a042bb80564561030c13fc3e5923784dc3714afd400000001ce400000001be31afea96c00023063c8c0000b9f241157b48cb03c2800000007fe80000000000058f8d6580f82e7400006cb0151000034b0d4e0fc045163ce89f08ed853242ba0700130b0000000012180000a38a9c5129077f02be0a2121d061b22d81e9413002a323d800003f709090000ac0920820661ff4914c00028013e968d4800000002a8e52a4a38959800005334000000032ba000152c09344be2009c000014e0396000126f0000242e6384349aa6b46fc164c517229b465a0b941278f6b000000000002a34456026e400000005494aaf07bea41d00002eb417d99ab1402ac390770129486a31cc35c000000006a05556a8811c06aa10b4d22d3270c00001280a3b3a3a0000000049000000001466226302ec2e4800000000000000049200000c280000c681150000015611d380002d420b6c000283100003238cc6a85a3f1449c8a248e3f47c413f15262a09351e000064d800000004c34dc6068346ca0000948a8474d0685a51a619db4a1a2aec00024d415ea15915d5a0951c3689e4edaa9bf40260001181a4e223f8000000001a01a060000000098800003b8c00000003e9e0000000191e2ab200009a4a685015018380000000473c0000000000052a2a90c1c818742e6a86587fb9191513e44e94d7000000005760abb8000394810e800026d9000036b51b5877a36b83ebc39c800000008ab4000138e106e00002988000376c705d2581c3d20d60fbd07980000000000100200de000000000000000147c00004b50000000063d04b82274417c887947da7912e5052b53529470000000015fb800026fe2ec4ed60000043c47d483e1fa70000262800014621bc43500000000057ce0000000070f0d5863d88e01b85000000000000b760c069a110a49130000083ec000221600006cfd1d500000000000020c8d172cac0edc0000000575c520855f01e639cc00001fe220f00007a88e0c14574dac870cc0d07800a92aba87db0e230f4c000062a800000007c300000d79071e8d0c67d80003d160001384a0642bde84b815894cc3efaa31151480004cb2998545ca97f3ea04f3c20b00003a54416010f97532a863f5035e080d387011752a52841000000000002b2e354a00015879dab2812ad20746238207a000013dd84c647a80e14ff208234188912000000000000731d543000001400000000000000000000b7027291572a1fca4a8000268a77440000000000077a882d25520000000000016e408a4000131297e454f80001476960018ce000148201d34fb60ecd56d000057aa474887b800000002088dd68edf00000001272880a21
  | 85 => 0x9bece3500003a10ac980fe9b650d74192939503f63e9a7d1d03e239f3fe416d0e972b6310b86259425800000000000edf000016cc000000000000000470d61294fc0a08713d2e6800000008f2400026671ae052647c784eb36c027204a3821305a40d10620271500e033f07e824c003aa3a7875315883db80000d911344348a57c80000f4914fc00003e01a301b4c00015d4a2b731fa00000000a454c6281e00001e031614376c472000026a064ad30c1fa500002410e308c0c00000000bad29c24c7e61cd0e403f01faa66794fd000000003368d5ba6a036c200009cd00003c260000f3c10ce00007da07282a18000000008df0c3b000044e4ceb800026426ddcc208000164a0000000010200005010000000047d000015639156374a0000000000007ae20454388000000025b000027f0064450e8bf010fc000051693dd23724a363d953da276c2696060ce058000000000000001bd509561d806042b6000008d40000000005d49578282800000000000000000040b46368c2b884105cc0001193a4aa02f88f6cdfb16f1000000000000000000000000001cb3315206e8ab5076647e62ac444ca9f95014196ce12882a26622e8c3e70954000053e000009511e4c000000000000000a9587ed1f12000000000000b81000000008af2886304c0000501800004b88a353a2029415bc000016d1f62000000005b71dd250f07fac6f21e04319e904920600000c0499900e523dd32f200000001f31068e01ad19f9b992508000008b0000462094000002816232a0000000000014a00000000000000000000db684530a7437094058000000002500000f1d53420000000025700000000b9b80000d5e53a146a9659307e0000000274d0000a281399815c0e2671d05c293981100519800000000000037029680002f320000e96000026aa00010229872470808092a2a98957da7900cad0a9149b462d944d2b3110ee8ebd51d0fb316f65f94d71909108d064907468edc317200000000a160e5e16082c60000179211c932f2ba201520000298000043ea000007a27ae4d52528c0000000105c900000000002a149d988028e7c49c00910a2e17a42bc83450d422c424bcca24c1131a6e3a327f7824e0c634eca60cc00004951ae2000000024dd4e8a0000e4710250000842d0200ffb05a05c50be61fc3485202f067ea79a1a866d3864e93c71308455d2a49c7942fa712548095231dde3bdd472836f265eafa8b648f4852163b1474803ca12fca118ab5843f502e0cb09e9a58009d85114c50022e0f067ad80000000069a8e1c0000012078e000097528332a741e60b7b0146396c1aac0882c53044a0d0c1b120ef010c73dc80489d50a362430a5406a135403548b761ecd1a8a203d5481dda301eaaf494518970170a6944d71fcd000049f9286000000000000a
  | 86 => 0x46f20000a5a94c0521080300000000073426a01640a253d8201e42ae0c3e2d1a2b7400a1e4f00004a646ab8a0f016260f90cf10d6000001848569b120e6e000077621142a7093a80000000000000000002b8f4caa26c8000000018f800015962a964eb60000afb8486154278011f791c8134a8a8c000000040dc0000000135713004dd007813872c70625537f04390000a58c0002a8713e051d4a3f21cd1a6a9a4061a8000000000006d7000000000000000248044b6000083c800000000000f1d1de802ae6b88c371fc943e483fd3ad025e55b828502b9a3a0000080b00000c4a1b0e0001133000000007e9000000000bde0000f8e8f0c57c01be80cb22122c3e26807eda1b049380170c891b8b0000000000000000000a0bcd4d07fb174ca4412bdac4824220000aad232615d85a44104000000006db8a98855b13a6000000014c8025000015fd870926a40e807c39e9700000000000225800c40000000056000005de50ae965532b60000a96971700005438a030000271e000127f8b680000552408b9c530a889974f55819c4cdc749c1f111d10f9a63945749f88049a4c64d072b3a21d41d70be0237a413a6c7428500280e442934c608000540c08b44332b04173675ad0e3a56e3cae2f8534c19f5443a3630917000019e22d6427486242cec00011c5a2f4079e22d0660a4572f76000017e10e252ec0000000000000000000000000000006338000013a36d61558ba5a58b0e7800004769b2c0000ad1553480001cc84bbc0f9aaf33f5a173d203881a3032366859d9237219818e148e958d31426b1c2e320c2536a88fc0319d53000075e816a8d070
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x864f63549200432631aa4900219994b6148010ccaa5b0a4008666521852004332a90c290021399db2148010acaeb90a400866765c85200436231e42900211d5c56508010ccaa53084008666525842004332a92c210021595d42108010ccaca1084008639651002004394a908010021ac5844008010f4042200400862e6494b1004316b24a5880218b99152c4010c5ac8a96200863565993100431ab2ac9880211d5d463c40108eaea316200847576d4b100423bbb2a5880219998952c4010cceeca9620086647654b1004393322a588021c959152c4010cccc6a9620086646354b1004392a948188021c954840c40108eaed28c200872952102100431dba2cb080218e1d16584010cd2cb29420086696554a100423cbb4a3080211b9da52440108d8ed292200862f649491004316324a48802193d8e5244010c98c7292200846e7654910042363b2a4880218bd915244010c58c8a92200864f63549100432631aa4880218ed964044010c76ca20220086986310110043543108088021ca5484044010ccee5b2a200866472d95100431bb2ec8880218dd946444010caecbb1a20084757598d100426b39cc688021399ca6344010caeca31a20086976418d100434a320c68802199d976244010d88c7b12200847575989100426b39cc488021399ca6244010cceca31220086a7641891004352320c488021b1d8c6244010d88c6312200866575189100423b3b6a4880219518f5244010cc8c5a9220084e47694910042b2baca48802199d965244010d88c7292200847476549100432a31aa4880219918952440109c8eca92200866765549100436231aa48802199dd95244010acceca9220085647654910043323b2a488021191d95244010e4ec8a9220087246454910043a3b1aa4880219998d5244010cc8c6a92200874463549100432231aa4880219954b6044010ca8c7282200866462941100436831e8088021b818b4044010ec2a5a0220084b676901100431bb2c8088021a518e4044010d48c520220087255290110042d938480880212d9d84044010c6eca20220086946310110043523108088021c95484044010da0c620220086e06210110043b0a9080880216c9d84044010d64ec20220086b3651011004399b288088021e4d8c4044010d64c620220086b06310110043c83188088021a418c4044010f46c420220086b26210110043583108088021e81884044010d40c420220087335210110043d12908088021cc5484044010f42a42022008721521011004335b96ca880219a1cb6544010c76cbb22200863b65191100432db2ec68802196d946344010d30c831a200866b65d891004335b28c488021aa1906244010d90c6312200866b659491004335b2aa488021b418f6144010dc0c5b0a200847a7694510042d93a4a288021d854a5144010
  | 1 => 0x210421eba6ca10821595c55208410cceca9084208665654842104335292c0108211d5d463084109e2e03184208565759882104332b2cc410821595d652084108eeeca9042086666254821042b3bb2a41082199dd95208410cccc6a90420866463548210423bbaac010821351cd6008410ccaa4b00420843e7498e500421eba4c7280211bdc963940108d8e4b1ca00843f74586500421e3a2c32802117dcd61940108b8e6b0ca00846f725865004236392c3280211d5d82194010ccaa530c800866552586400428f39ccb20021475ce6590010a5ce532c800852d729964004297390cb200214b5c86590010a74e032c800852e72d4e4004296b96a7200210f9d8539001087aec29c800852e7214e4004296b90a720021c91c55290010a6ce22948008725529864004392a92c3200210f5da5190010e4aa598c80084b5760c6400429aba86320021c95483190010a6aeb90c800872552c86400429aba84320021c954821900108dce5328800846d72994400422f398ca20021175cc65100108dce4328800846d721944004332a94c220021995496110010a5ce5328800852d72994400428f398ca20021475cc6510010a5ce4328800852d72194400429d380ca200214b9cb5310010a5ae5a98800853a70d4c400429db82a6200210f9d8531001087aec298800852e7214c4004296b90a6200214b5d65210010e48e2a908008728705484004297390a4200214d9c45210010a74e02908008725529844004392a92c2200210f5da5110010e4aa598880084b5760c4400429aba86220021c95483110010b62e0188800853575c844004392a9642200214d5d42110010e4aa410880085b1700844004317294c0200218b54a6010010a72eb3008008639659804004395294c020021ca54a6010010b62e3300800862e6494b3004316b24a5980218b99152cc010c5ac8a96600872a521033004394a9081980219954a618c010ccaa4b0c6008555750c630043a2a9063180211ddc7654c0108dced292600846c769493004317b24a4980218b192524c0108dceca92600846c765493004317b22a4980218b191524c010ccca5b0a600866552d853004333290c29802199548614c0108dce5328600846d72994300421f3a0ca180210f5d0650c0108dce4328600846d721943004332a94c21802199549610c010aaaea1886008745520c4300431cb288018021c694c400c010e54a42006008729521003004358b088018021e40c4400c010c5cc9296400862d6494b2004317322a5900218b59152c8010acaeb90e400866565c87200431cb288190021ca54840c8010f4642206400866552986200423bbaac310021995496188010acaea10c400866765086200423bb8eca900218bd925248010c58c9292400864f63949200432631ca4900218bd915248010c58c8a9240
  | 2 => 0xc0a9021171cd60548108dcedaa2a40846e7615152042a7398a8a9021535cc54548108dceda9aa40846e7614d52042973a0a6a90214b5d05354810acce3322a40854f7359152042a639ac8a9021591c56454810ad0e0b22a40856671d8d52042b338cc6a90214bdd16354810a58e8b1aa4085647158d52042b4382c6a90214b9d06354810a5ae831aa40864d6318d52042b338e86a9021595c743548108deeca1aa40846c7650d52042b3b8a86a9021591c54354810ad6e0a1aa4085687050d52042973a4c2a90214b5d26154810a9ce730aa40854d7398552042b3398c2a9021991866054810cc8c2302a40846f76548520422f398cba1021175cc65d08108eaeb30e8408665529874204332a92c3a10211d9c465908108f4e032c840845f73595420422e39acaa10219954b61508108eaea30a8408665521854204334a96c0a10211e5d46050810cd2a4302840845e73194420422eb98ca210211d9c4651081087ce832e640843d74197320423abacc3990219954a61cc810ccaa4b0e640847571596320423b388cb190211d5d6618c810ccaa530c6408666525863204332a92c3190210fdd1654c810878e8b2a640854c735493204332a96c2990211d5d4614c810ccaa430a640866952d81320423cba8c0990210f9d3650c81087ae9b28640843e74194320421eba0ca190211d9c4650c8108f4e032864084b8705903204317324a4190218b592520c810a9ae7290640862e645483204316b22a419021475cc54d0410cd2a5304820866952582410421f3b0a8a0821475cc545041087eecaa082084757615331042aab98a998821595c854cc410acae5a9e62084777654b3104333312a5988219959552cc410cceeca9662087477354b31043a239aa5988219954960cc41087ce9b2c620843d74d963104237396cb188211b5cb658c4108daeb314620846f7558a3104237bb4a5188211b5da528c4108deeca94620846d7654a310421f3a6ca188210f5d3650c410c3ac9298620861d6454c3104317324a4188218b592520c410c5cc8a90620862d6454831043a329262188219a54a600c410cd2a4b00620863565990310431ab2ac8188211d5d8540c410aaae62a062085657215031042b2b96a6188211ddd9530c4108eaeb310620847576d4831042aab9ea418821595d6520c410e8aa729062086666254831043a329aa41882199dd9520c410cc8eca906208726645483104392b22a4188219998d520c410e8cc6a90620876152980310423bbaac018821391c9600c410ccaa4b0062086b26458031043b0a92c018821999c965c84108eaea31e42086656594b210433331aa5908219918d52c8410ccacb9964208565750cb2104332b2865908219954960c841087ce9b2c420843d74d96210422f39ecb10821175cf6588410cd2a4b04420843e74d94
  | 3 => 0x8f5248110c98c7a92408862f641492044316320a49022193d8c5248110c98c6292408863754d85204431a2a6c29022195d4f6148110ca8a7b0a408866452d85204431baa0c2902218d1506148110caea630a4088654531852044333a90c290221991486148110ac8ea90a408866465485204436231a4290221d114d2148110c70ca202408869863101204438c2988090221ca1484048110d60c220240887a121101204431baa4c2102218d1526108110caea73084088654539842044333a94c2102219914a6108110c6ea8b08408863454584204432ba9ac2102219514d6108110ccea4b084088664525842044272bb44210221599d62108110ccccb108408874453884204430f326a7882218759353c4110c3cc829e208861d6414f1044317326a5882218b59352c4110c5cc8296208862d6414b104438c2988188221ca14840c4110e30a829e20887285414b10443a4298a588221599ca5384110e2ea829c20887145414e104432a29ec5082219514d6284110e88a7a9420885567394a1044332b10a508221c9d505284110e48a829420887475314a10443a2298a508221999d85284110ccaec294208853675902104438a29c8108221c914a4084110a6cea204208871453102104439229081082219958a61d5010cd2c5306a80846f7258e5404236392c72a0210fdd95415010c3aa8b18a80861e6458c540432a38ac62a0219398e6215010c9ac7310a80864e635885404326b1ac42a0219558e6115010ccac5308a80843e74987530421eba4c3a98219958a61d4c108dee4b24a60846c72592530423b38cc5298210f9d36054c1087ae9b02a60843f74581530421e3a2c0a98211bdc96054c108d8e4b02a60845f7654c530430eb22a629821875926314c10c5cc9310a60862d649885304317322c4298218b5916214c10c6ac9308a608665629845304334b14c0298211b9ca65d0c108dae532e860846e721974304236b90cba18211d5d661d0c108dce532c860846d729964304237390cb218211b5c86590c108dce532a860846d72995430423b38ccaa18211e9c26550c108dee4b2a860846c72595430423bb8acaa18211edc16550c108dce432a860846d721954304236baec4a18211b5d46250c108eaea30a860863654185430432b298c2a18211e5d46050c10c74a8302860863954181430432d298c0a18211b9ca6510c108dae5328860846e721944304236b90ca218211d9c46510c10a9ce62a4a40854d7315252042973a0a7290214b5d05394810acce3b1ca40852e7418e5204296ba0c7290219358c63948108deeca1ca40846c7650e52042b3b8a8729021591c54394810ad6e0a1ca4085687050e52042973a0c3290214b5d0619481087ce831aa40843d7418d520421f3a6c0a90210f5d3605481087ee8b02a40843c74581520422fb9a
  | 4 => 0x1ea7a90808870c53d48404421ebb4a420221479ce5210110a3ae7290808852e72948404421fbb2a42022147dcd5210110a38e6a90808853771548404429db82a4202214b9d45210110c5cca290808870f531484044386298a420221c95c45210110e52e0290808853675884404431b32c4220221c514e2110110e48a5108808853475484404431b32a4220221c514d2110110e48a490880885b070484404430fa9cc0202218714e6010110c5ea5300808862c52980404438da9cc020221c614e6010110e56a5300808872852980404421f3acc9982210f1d564cc11087eedaa6608843d76d53304421fbb0a9982210f5d854cc110c3cc9a9e608861d64d4f304430f320a7982218759053cc110c5cc9a96608862d64d4b3044317320a5982218b59052cc110ca8a730e60884e5729873044332294c3982219514d61cc110cc8a4b0e608863a65103304438c2988198221cad4840cc110e50a420660886b261103304421f3a6ca982210f5d3654c1108dce5b2a608846d72d95304421fba2ca982210f1d1654c1108dee4b2a608846c72595304421f3aec8982210f9d4644c11087cedaa2608843c76d51304421f3b0a8982210f1d8544c110c3ec9a9a608861c64d4d304430fb20a69822187190534c1108dcebb12608862f54d8930443162a6c49822193d4f624c110c98a7b12608846e751893044317aa0c4982218b150624c110c9ea6312608864c5318930442373b6a4982211b1db524c110c5ec9a92608862c64d4930442373b0a4982211b1d8524c110c5ec8292608862c64149304431baa6c2982218d153614c110ca8a7b0a608866752d853044332296c2982218dd50614c110c68a830a608865753185304432a298c29822199d48614c110cc8a430a608853870150304438da988018221c614c400c110e56a4200608872852100304421f3acc9902210f1d564c811087eedaa6408843d76d53204421fbb0a9902210f5d854c8110c3cc9a9e408861d64d4f204430f320a7902218759053c8110c5cc9a96408862d64d4b2044317320a5902218b59052c8110ca8a730e408866452987204432a29ac3902219914961c8110ac8ea90e40887445348720442b33ac4310221999962188110e88a710c408863a65102204438c2988110221ca1484088110f4442204408843e74d95204421eba6ca90221179cf65481108bae7b2a408843f74595204421e3a2ca9022117dcd65481108b8e6b2a408843e75d91204421f3a8c8902210f9db5448110878edaa2408843e76151204421e3b0a890221179d76348110c3ea9b1a408861c54d8d204422f3a8c69022187d506348110c38a831a408845e76d4d204422e3b6a69022187d935348110c38c9a9a408845e7614d204422e3b0a69022187d905348110c38c829a408862f64d492044316326a49022193d
  | 5 => 0x846d76d4a3144237bb0a518a211b5d8528c510c70a9b02628866852d81314431c2a0c098a2196d4c604c510cd0a430262884b870590314421fbb6a818a210f5db540c51087eec2a0628843d76150314430f326a618a2187593530c510c3cc8298628861d6414c3144317326a418a218b593520c510c5cc8290628862d641483144334294c190a2199dca6588510c6ccbaa4428863665152214432b32ea710a211d5da5388510acce529c42886566514e214438baa0a710a21c51505388510ccccba94428874453d4a21442ab39ca510a21c9d505288510e48a829442887475314a21443a2298a510a219514e6088510cc8a5304428863854d81214432c29ec090a218e1506048510cb0a6302428866b52181214423b3b4a690a21559ce5348510acce529a42887175414d214438a2a0a690a21d1dc85348510e88e429a428856675d89214433232ec490a21d114f6248510e88a7a9242885567394921442b3394a490a211d9d85248510e4ea829242887245414921443a3a98a490a21d114c5248510accec29242886667614921442b3398a490a21599d73248510cc8cb992428874453cc921442b23a86490a21991943248510e88a619242885e1700c921443a829ec090a219514c6048510cc8a4302428875053181214432a29cc210a219914a6108510ac8ea90842887275448421443922a24210a21d1d4d2108510e88a6908428863454987404432a29cc3a02219914a61d0110ca8a6b0e808866452587404428f39ca920221475ce5490110a5ce52a4808852d72952404428fb9aa920221471cd5490110a5ee4aa4808852c72552404430f32ea7202210f5da5390110a5ce529c808852d7294e404421fbb2a7202214bdc95390110a58e4a9c80885377154e404430f328a7202218b9975290110e1ea7a94808870c53d4a404421ebb4a520221479ce5290110a3ae7294808843f7654a404428fb9aa520221471cd5290110a6ee2a94808862e6514a4044387a98a520221c314c5290110e4ae2294808853675886404431b32c4320221c514e2190110e48a510c808853475486404431b32a4320221c514d2190110e48a490c808845e73d95404422eb9ecaa02211b9cb65501108dae5b2a808845f73595404422e39acaa02211bdc965501108d8e4b2a808843e76151404432a29ec2a02219914b6150110c6ea830a8088654531854044332290c2a0221479ce5410110a3ae72a0808852e729504044296b94a8202210fdd95410110a3ee6aa0808851c735504044297b92a8202214b1c95410110a70e1328808861e65d4c404438cb86a6202210f5da5310110a3ce7298808852e7294c4044296b94a6202210fdd95310110a5ee4a98808852c7254c404429bb8aa6202214edc15310110a3cea298808861e6514c404438db80a6202218b9975210110e
  | 6 => 0x2442a6b9cc4292218b99754149108daed2a0a48854e7395052442a6b9ca8292211bdd95414910a9ee6aa0a48854c735505244317328a829221939975314910e1ea9a98a48870c54d4c5244236bb4a6292214b9d25314910a5ae9298a48846f7654c5244297ba2a6292214b1d15314910c9cca298a48870f5414c52443862a0a629221c9d516114910e48a8b08a4887475358452443a229ac229221595c76414910ad2e1b20a4885657119052442b2b8ec6292214b9d06314910a5ae8318a4885657118c52442b4b80c6292211bdd943149108d8eca18a4885677150c52442b238a86292215adc14314910ad0e0a18a4885667110c52442b2b8886292219998d6114910cc8c6b08a48852e74d805244296ba6c029221995876014910a5ee8b00a48852c7458052442a7b9ac029221531cd6014910ccac2b00a48852f7444052442963a2202922153dcd1014910a98e6880a48845e73d97424422eb9ecba12211d5c765d09108bee6b2e848845c73597424422f39ecb21221175cf65909108bee6b2c848845c73596424431baa4c3212219514e6190910cc8a530c848847475586424432a29ac321221991496190910c76a93048488658539824244334294c1212211e1d56090910cb0a6b04848866852582424422f39ecaa1221175cf65509108bee6b2a848845c73595424423bb8acaa12211edc165509108bce7b28848845d73d94424422fb9aca21221171cd6510910c68a93088488654539844244332294c2212211d1d56110910ca8a6b08848866452584424421f3a6cb992210f5d365cc9108eae3b2e648843f74597324421e3a2cb992210f9d3658c91087ae9b2c648847571d96324421fba2cb192210f1d1658c9108ece232c648863754986324431a2a4c31922195d4e618c910ca8a730c6488667529863244332294c3192211d1d5618c910c6ea8b0c648863454586324432a29ac31922199d49618c910cc8a4b0c648843e74d95324421eba6ca992210fdd1654c910878e8b2a648847771595324423db82ca992210f9d3650c91087ae9b28648843f74594324421e3a2ca192211ddc5650c91087ce8328648843d74194324421f3acc8192210f1d5640c91087eedaa0648843d76d50324421fbb0a8192210f5d8540c910c3cc9a98648861d64d4c324430f320a61922187590530c910c5cc9a90648862d64d483244317320a4192218b590520c9108eceb3086488654539843244332294c2192211d1d5610c910ca8a6b08648866452584324432c29cc0192219a14a600c9108f0eab00648863854983414432c29ec0a0a219a14b6050510c76a83028288658531814144334290c0a0a219614e60cc510c5ea9314628862c5498a3144327a9cc518a219314e628c510c5ea8b14628862c5458a3144327a9ac518a219314d628c5108deeda94628
  | 7 => 0x229a211b5ca6114d1087ce8308a68843d74184534430f32ea829a21175da5414d10a9ce52a0a68854d72950534422fbb2a829a2153dc95414d10a98e4aa0a68861e6515053442a7b92c829a21531c96414d10aaee2b20a68855b7059053442aab88c829a21555c66214d10a3ce8310a68851d7418853442aab88c429a21565c06214d10a3ce9b00a68851d74d80534428fba2c029a21471d16014d10a9ee4b00a68854c72580534428fba22029a21471d11014d108dce5b2e868846d72d97434423ab8ecba1a211bdc965d0d108d8e4b2e868846e72d964344236b96cb21a211bdc96590d108d8e4b2c868846e72d954344236b96caa1a211b9ca6550d108dae532a868846f725954344236392caa1a211ddc56550d108f6e0b2a868847471195434423c380caa1a211b9d76250d10c5ea9b12868862c54d894344327a9ec4a1a219314f6250d108dcea312868862f5418943443162a0c4a1a2193d4c6250d10c98a6312868847675d85434431baa6c2a1a218d1536150d10ca8a7b0a868863754185434431a2a0c2a1a2195d4c6150d10ca8a630a868847a75d81434431c2a6c0a1a219614f6050d10c76a8302868863854181434432da98c0a1a219614c6050d108dce5b28868846d72d944344237b92ca21a211b1c96510d10c68a9308868865453984434423a3aac221a219514d6110d1087ce931ea48843d7498f524423bb8ac7a9221539ce54d4910a9ae72a6a48854f7355352442a639aa9a9221c3d5353d4910e18a9a9ea48852e7494f5244296ba4a7a92214bdd153d4910a58e8a9ea48870f5414f52443862a0a7a9221d114f61d4910a5ce931ea48852d7498f52442b3b8ac7a92211bdd943d49108d8eca1ea4885677150f52442b238a87a92215adc143d4910ad0e0a1ea48852e74d835244296ba6c1a9221539cf60d4910a9ae7b06a48852f7458352442963a2c1a922187d526394910c38a931ca48861f5458e524430e2a2c729221879935394910c3ac9a9ca48861e6414e524430eb20a7292218b9935294910c5ac9a94a48864e63d4a5244326b1ea529221879926394910c3ac931ca48861e6458e524430eb22c7292219598d619491087ee8b04a48843c74582524421f3b6a8a92210f9d85454910c3ea9b1aa48861c54d8d524430faa0c6a92218715063549108bceda9aa48861f64d4d524430e326a6a9221179d85354910c3ec829aa48861c6414d524430fb26c6a9221871936354910c3ec831aa48861c6418d5244317b26c4a92218b1936254910c9ec7b12a48864c63d89524431bb26c2a92218d1936154910caec7b0aa48865463d85524421f3a6c0a92210f5d36054910c70c9b02a48865863d815244237bb2a4292214bdd15214910a58e8a90a48854f7354852442a639aa4292214b9d26214910a5ae9310a48854e739885
  | 8 => 0xa52486108daeda9043084f17018c218423abb6a410c21395db5208610bc4e1a90430856576d482184332bb6a410c219998f5208610cc8c7a90430876270d4821842f1380a410c21351cd6008610ccea4b00430843d7694e4084297b92a7204214b1c9539021096aec18c810872752086408421ebb4a6204214bdc95310210a58e4a9881084b5760c44084393a9042204216c5c02110210a98e4a9c610854c7254c308438d2988018421c654c400c210f206220061087a021102208432631ea4904211b9d85248210c98c629241086645218520842733b64290421b118f2148210d30c620241087285210120843583088090421e8c8440482108deeca904108666525842084332a92c210421391c965c4210acee4b2e210863565993108431ab2ac9884219918b52c42108eeeca9621086666254b108431cb2cc9884218e59564c4210a5ce5b1ea88852d72d8f544429ab8ec7aa2214e5c363d5110a6ae2316a8885397018b544430faa4c72a22187d516395110c5ea9314a88862f5458a544432731cc52a2219358e6295110c9cc6b14a88864d6358a544432b31ac32a221999896195110c3ec9b1aa88861f6418d5444317b26c4aa22193d8f6255110c98c7b12a88862f641895444327b18c4aa2219318c6255110ca8c7b0aa88866462d85544432c31ec0aa2219a18b605511087eecaa0a88851f73550544428e39aa82a2214bdc95415110a58e4aa0a88851e73990544428eb9cc82a2214b9ca6415110a5ae5320a88846f7258c5444236392c62a2211ddc56315110a5ee4b18a88852c7258c544429bb8ac62a2214edc16315110a6ae2318a88853571188544421f3a4c5a9a210f5d262d4d10a9ce52a6a68854d7295353442a7b92a9a9a21531c954d4d10a9ce5b26a68854d72d9353442aab8ec9a9a21565c364d4d10a3ce9316a68851d7498b53442aab88c5a9a21479d360d4d10a3ae9b06a68854e72d8353442a6b96c1a9a2147dd160d4d10a38e8b06a68861e64d4e534430eb26a729a218bd526294d10c58a9314a68864f5398a5344317aa2c529a218b1516294d10c9ea6b14a68862e6498a5344316b24c529a21995c66294d10c5cc8b14a68862d6458a5344333312c329a210fdd16094d10878e8b04a68843e76d51534421f3b0a8a9a218bd536254d10c58a9b12a68862f5418953443162a0c4a9a2187d936354d10c38c9b1aa68862f64d895344316326c4a9a2193d8f6254d10c5ec8312a68862c641895344327b18c4a9a218dd936154d10c68c9b0aa68866762d855344332316c2a9a210f9d36054d1087ae9b02a68863864d815344334316c0a9a2117dd95314d10a3ee8a98a68851c7454c53442a7b92a629a21531c95314d108dee4b20a68846c72590534428f3a4c629a21475d26314d10a9ce5318a68854d7298c5344237394c
  | 9 => 0xcec29243887267414921c4392ba0a490e21599cc5248710ec2e0292438856675cc921c42b23a86490e21d194c3248710cc8a4302438846f7654821c43932a24210e21c95512108710c74a9300438863a5458021c437090ac010e218d95161d031087aeda9c818852e72d4e40c4296b96a7206210f5d8539031087aeda94818851e73d4a40c428eb9ea5206210f5d85290310e48a490c818843e7695140c431aaa6c2a06210f5db541031087aeda98818852e72d4c40c4296b96a6206210f5d8531031087aeda90818851e73d4840c428eb9ea4206210f5d85210310e48a490881885b07048440c421ebacc9986210fdd564cc31087aed2a6618843f7655330c4272b94c398621c694c40cc310a9ce5a9c618843d75d9130c421eba8c8986210f9da544c310878ecaa2618845e7694d30c43172a6c4986218b553624c310c5ca8312618862d5418930c4327298c4986219354c624c310c6ca9b0a618863554d8530c431b2a0c2986218d550614c310caca630a61886555318530c422ebb6a618621539cb530c310e30a6200618843d7599320c421fbaac9906210f5da54c831087eecaa641887a12110320c42a739ea5106210f5d7644831087aea322418843e7695120c421e3b2a890621879536348310c3aa9b1a418861e5418d20c430eaa0c6906211b9da5248310c98c7292418864c6354920c431b2a6c2906218d5536148310c6ca830a41886355418520c4333290c290621995486148310d88c690a418846d76d4820c42a739ea4106218d9526108310c6aa930841886365458420c431aaa2c21062199d4961083109caed108418872b5210020c4358b088010621e88844008310ce2c3306a90843f765505484237b92c62a4211b1c96315210a70e0b24a70863771592538431a38ac929c218edc16494e10c70e0b24a70866762d855384332316c2a9c2117dd95314e108dce5b2e870846d72d974384237394caa1c211b5ca6550e108dee4b2a870846c72595438428f39ea8a1c218d1506150e10c76a83028708638541814384237390ca21c211b5c86510e1087ce931ea50843d7498f5284237bb2a429421179cf65d0a108bae7b2e850845e73995428422eb9ccaa1421179cc6510a108bae6328850843e74d97328421eba6cb9942199d4a61cca1087ce932a650843d74995328421f3a6ca194210f5d3650ca1087ce8328650843d7419432842a6b98a4194213c1c5600ca1087ced2a2830843d76d5041842b3b92a798c211d5d662cc610cccc5a96630845e7694d318425c382c818c21175db530c6109c8e4b28630856772594318431ab2ac818c216c1c1640c610aaae72a0630847576150318423abb6a618c21355db530c610ba4e1a9863085677254c31842e9380a618c211ddd9520c610aaee6a9063084e47258031842f0b806590c211b9d
  | 10 => 0x46c7258e54c4297b92c72a6214b1c96395310a68e2b1ca98853b7058e54c430eb18c72a6214b9c86395310a5ae431ca9885367118e54c428f398c52a621475cc6295310a6ce2314a98851e7318654c428eb98c32a6214b9c86195310a5ae430ca98851e73d8254c428eb9ec12a6214b9cb6095310a5ae5b04a98852f7258d54c4296392c6aa6214d1c56355310a76e0b1aa98861d6318d54c429b38cc4aa6214edc16255310a5ce530aa98852d7298554c428fb9ac0aa621471cd6055310a5ee4b02a98852c7258154c421fbb2a82a6218b95262d4f10c5aa9316a78862e5458b53c4316aa2c5a9e218b99262d4f10c5ac9316a78862e6458b53c4316b22c5a9e218d99261d4f10c6ac930ea7886666298753c4332b14c3a9e218e99160d4f10a9ce5a9ca78854e72d8d53c421f3a0c4a9e210f5d06254f1087aed2a0a78843f7655053c422fbb2a629e21595ca6114f108dce432e878846d7219743c4237394caa1e211b5ca6550f108dee4b2a878846c7259543c428e39aa8a1e218b9536250f10c5aa9b12878862e5418943c4316aa0c4a1e218d9536150f10c6aa9b0a87886365418543c431aaa0c2a1e218e9536050f10c74a830287886395418143c4237396ca21e211b5cb6510f10a3ae72a087886365458443c430f2a4c7a96218755263d4b10c3ca8b1ea58861d5458f52c430f324c7a96218759263d4b10c3cc8b1ea58861d6458f52c431b324c3a96218d59261d4b10cacc730ea5886556398752c42a739ea5296210f9d06354b1087ae831aa58854e73d8952c421ebb4a8296210fdd95414b108deeca90a58863a6458052c422f398cba1621175cc65d0b10c6aa8b0c858845e7399542c422eb9ccaa16218e5506050b108bce7b28858845d73d9442c431b2a2c2216210f9d265ccb1087ae932e658843e7419732c421eba0cb996210f9d2658cb1087ae932c658843e7419632c421eba0cb196218d952618cb10c6aa930c65886565398632c432aa9cc3196218d951618cb10c6aa8b0c658843e7499532c421eba4ca996210f9d0654cb1087ae832a658863a54d8132c431d2a0c0996210f9d3650cb1087ae9b28658843e7499432c421eba4ca196210f9d0650cb1087ae8328658843d7599032c421fbaac8196212e1c1640cb1087eed2a0658843d7695032c421fbb2a8196210f5d9540cb10c72a9304838863a5498041c43172a4c518e218b552628c710c9ca7314638864d5398a31c43172a2c518e218b551628c710c74a9304638863a5458231c421ebacc818e210fdd5640c71087aed2a0638843f7655031c42a739ea590e21539cf52487108dcec29243886376595121c431bb2aa890e21599ca53487108ecec29a43885c673d4921c42f0b86a490e211d9d852487109ccec29243887265414921c4392aa0a490e21599d85248710cc
  | 11 => 0x8392192a220041cc1c15110020a5aeb1088010725518844008392a8842200416a5c02110020a72eb30080106396598040082d4b94c020041cc9466010020e62a3300801063664947300831ab24a3980418d99151cc020c6ac8a8e6010732511033008398a888198041535d4328c020cccc4a8c60106656254630083a2192a3180411d9da514c0208e8ed28a601063764945300831a324a29804199d8a514c020cc8c528a601047676545300823a3b2a2980418dd91514c020c68c8a8a6010667625453008332312a2980410f9d0650c02087ae8328601054d750c83008333312a21804199589510c020e8864a88601063965100300838d2988018041aa588400c020f10642006010732511003008398a8880180418d99251c8020c6ac928e401063664547200831ab22a3900411bdd951c8020cccc2a8e4010667765472008393322a390041c959151c8020cccc6a8e4010664635472008392a8c8190041c954440c80208daed294401073151102200823cbb4a5100411d1da5148020c6ec928a401063464945200832bb1ca2900419518e51480208ececa8a401063764545200831a322a29004195d8d5148020ca8c6a8a401063b65901200831db288090041a618c4048020d60c22024010731511012008333b8eca90041991c76548020c5ecbb22401062f651912008327b2ec6900411b5d6634802099ce731a40104e67198d2008327b28c690041a3d906348020d18c831a401066765d85200836231ec29004199d946148020d4ec830a40106a4641852008363b18c290041b118c6148020ccaea30a40104e4769452008333b2ca290041b118e5148020c98c6a8a40106646154520082723b2a29004199d955148020d88c6a8a40105667654520082b23b2a290041991d95148020e4ec8a8a40107246454520083a3b1aa2900419998d5148020cc8c6a8a401074463545200832231aa2900419318e5048020d90c7a0240106e061d0120083b0a8e80900412b9da4048020c5ecb202401068c63901200835230c8090041c95464048020b54e120240104ae761012008317b288090041a318c4048020d48c220240107255110120083643188090041b81844048020ec2a220240105aa7610120083553b08090041aad944048020e56ca202401078b6310120083553188090041aa18c4048020f10c620240106886310120083d1b088090041aa1844048020f40c220240106a06110120083d12888090041ca5444048020f42a22024010721511012008339b8eca900419c1c76548020c76cbb22401063b65191200832db2ec69004196d946348020d30c831a40106c863d8920082d53a4a4900419cd976148020ce6ca30a40106b0641852008368318c290041b8d886148020ce6cb28a40106736554520083b1292a2900419c98560d53108dee4b1ca988
  | 12 => 0x2884159dc94394420ac8e4a1ca2105737050e51082b838287288414d9d06294420a6ae8314a210475768ca510829b3a065288414d5d03294420e8a64194a21043e7418d510821eba0c6a8841599c73254420acce2192a21047676d51510823b3b0a8a8841559cc5454420aaae62a2a21047676d4d510823b3b0a6a88414d9d05354420a6ae829aa21056575cc951083a329864a8841599ca6454420aaee6b22a2105547359151082b2392c8a88415c1c16454420acce5b1aa2105667298d510829bba2c6a88414d1d16354420ac8e4b1aa2105707058d510829b3a0c6a88414d5d06354420caac631aa21056672d0d51082b2b9686a88411ddd943544208e8eca1aa2105677250d51082b239286a88415cdc14354420ae0e0a1aa21053674989510829aba4c4a8841559ce6254420aaae7312a2105727090951082b8b8484a8841599db3254420e8ec7992a21074463cc951082b2b8664a88411d9da3254420a6ce8192a210535740c951082b938064a88415c5c03254420accec192a210726740c95108392ba064a8841d19cc3254420ec4e0192a210565700c951083b0b8064a88411ddd95114420cccc4a8e821066562547410822fb9acaa0841171cd6550420ccec4a8a8210664625454108338a8ec0a08419c5446050420cccc4a8e6210665625473108332b14a31884199989518c420ccac4a8c621043f74595310821e3a2ca98841551cd514c420ccec4a8a6210664625453108338a8ec0988410f9d3650c42087ae9b2862104b870590310831b324a2188418d592510c420aaae7288621063664544310831ab22a2188419c54560c8420ccce2b2c421046d7518e2108332b2ca3108419998d5188420cc8c6a8c421066565cc621082b2ba86310841995943188420ccaa2b044210672515802108274b80c610841595d66108420aceeca88421066776544210833331aa2108419918d5108420998e6b00421043e7498e500821eba4c7280411b5d82194020cccc4a8c801066562546400828f39ccb20041475ce6590020a6ce332c801053571996400829b388cb200414d5c46590020a74e032c801053671d4e400829ab8ea7200410f9d8539002087aec29c80105367114e400829ab88a7200410f5da529002095aec194801052d750ca4008393312a320041c95895190020e4e64a8c8010724325464008296bac4320041c95462190020e4aa210c801045e73194400822eb98ca20041999895110020ccac4a88801053671994400829ab8cca20041479cc6510020a3ae6328801053671194400829ab88ca200414e9c06510020a6ce3a98801053571d4c400829d386a6200410f9d8531002087aec29880105367114c400829ab88a6200410f5da521002095aec190801052d750c840082d4b806420041c99895110020e4ac4a8880107273254440
  | 13 => 0x544c120878edaa2609043e76151304821e3b0a89824187d93534c120c38c9a9a609061f6414d304830e320a6982418bd53624c120c58a9b12609064c53d893048317aa0c4982418b150624c120c9ea6312609064c53189304823b3aec2982418dd53614c120c68a9b0a609065753d85304832a29ec2982411d9d4614c120c6ea830a609063454185304832ba98c2982419514c614c1208eceda8a609063764d45304831a326a29824199d8b514c120cc8c5a8a609047676145304831bb20a2982418d190514c120ccec428a609066462145304838da988018241c614c400c120e66a2200609073051100304830f326a7902418759353c8120c3cc829e409061d6414f204831b326a3902418d59351c8120c6cc828e409063564147204838c2988190241cc14440c8120e30a829e40907305414720483a8298a390241599c65388120e1ea829c409070c5414e204832629ac310241d114f5188120ccac228c40907275414620483922a0a310241d1d4c5188120e88a628c40906657614620482973ac8110241c314e4088120e48a3204409052e7510220483862988110241c91444088120cccc4b0ea81067161983540823bb8ac72a0411d1c5639502087eecaa0a81061d5458c540830f322c62a041931c96315020c9ac7310a81065663984540832ab1cc22a0419598d6115020caac6b08a81066662584540821f3a4c5a98410f5d262d4c20cccc4b0ea61047771592530823a38ac92984117dd95314c20c3ac8a98a61061d6498c5308316b24c4298418d9926114c20c6ac9308a61063664584530831ab22c229841999896114c20ce2c3300a61047671997430823ab8ccba18411d9c465d0c208eae232e861046d7598b430823b38ccb218411d5c66590c208ece232c8610475711964308237394caa18411d9c66550c208eae332a861047a709954308237b92caa18411ddc56550c208e8e2b2a861047671195430823ab88caa18411b5d46250c20c5ca8312861064e53189430823abaec2a18411d5d46150c208f2ea302861063a54181430831caa0c0a18419694c6050c208ece33288610475719944308237390ca218411d9c46510c208eae2328861051d73153420821f3b0a8a1041475cc545082087eecaa0841046d7615332082a6b98a999041595c454cc820acae3a9e641043e74d96320821eba6cb190411d5d6618c8208eeeab0c641043e74d94320821eba6ca1904187592530c820c3ac8a98641062d659903208316b2ac8190411b5d8540c820a9ae62a064105657115032082b2b8ea6190411bdd9530c8208daeb308641046f75580320827238ac019041aa991600c820aace62a4a21055573152510829b3a0a7288414d5d05394420e8aa6194a21056672d8e510829b3a0c7288414d5d06394420caac631ca2104777650e510823a3b287
  | 14 => 0xed29e42905667194f2148327328a790a41c3d5053c8520e18a829e429066665d4721483a229ea390a41c9d5051c8520e48a828e42907475314721483a2298a390a419314e60c8520cc8a3306429067051982214831c2a6c090a419614f6048520c70a83024290658531812148339a88c090a41539ce5348520acce329a429070f5414d21483862a0a690a41d1dc45348520e88e229a429056675d8521483a229ec290a41d114f5148520e4ea828a42907245414521483a3a98a290a41d114c5148520accec28a42906667614521482b3398a290a41599d73148520e88a798a4290564750c521483a22986290a41785c03148520e90a7b02429064c5318121483a4298c090a419314e6208520e4ea890842907245448421483a3a9a4210a41d114d2108520c58a9316809064c5398b404832629ac5a02419998851d0120ccac428e809051e73952404828eb9ca9202414d9c65490120a6ae32a4809051f73552404828e39aa9202414ddc55490120a68e2aa4809061e65d4e404821ebb4a7202414d9c65390120a6ae329c809043f7654e4048297b92a7202414ddc55390120a68e2a9c809061e6514e404831b32ea320241c5d4f5190120e28a7a8c809063665146404838ba98a320241c514c5190120a5ceb90c809062e65c86404838629e4320241c91472190120c5cca90c809070c53486404839228a4320241179cf65501208bae7b2a809045f73595404822e39acaa02410f9d85450120c98a7b12809062f541894048326298c4a024199d885150120cc8c428a809051e73950404828eb9ca8202414d9c65410120a6ae32a0809043f76550404828fb9aa820241471cd5410120a6ee2aa0809053471550404830f32ea620241c65c3531012087aed298809051e7394c404829b38ca6202414d5c6531012087eeca98809052f7254c404829bb8aa6202414d1c55310120a76e0a98809051e7514c404830f328a620241c6dc05310120c6ccba88809071753d44404838a29ea2202418d9945110120e2ea62888090714531444048398b80a2202414b9d72110120c5ccb908809070c53c84404839228e42202418b9952110120e18a690880907245148440482d4382422024187d4e6010120c38a7300809071b53980404838c29cc020241ccd466010120e60a3300809043e75993304821e3aac9982410fddb54cc12087aedaa6609043f76153304821ebb0a9982418799353cc120c3ac9a9e609061e6414f304830eb20a7982419314e62cc1209cae3316609064c5358b304831b326a3982418d59351cc120c6cc828e6090635641473048333310a3982419958851cc120c74ca20660907185310330483553108198241ccd4440cc120e60a2206609043e74d95304821eba6ca982410fdd1654c120878e8b2a609043e75d91304821f3a8c8982410f9db
  | 15 => 0x647250f51482b9b8287a8a415c1c143d45208eced196a290536740cb514829aba065a8a414d9d360d4520a6ae9b06a29055673d8351482aab9ec1a8a414ddd160d4520a68e8b06a29061f5498e514830e2a4c728a4187d516394520c38a8b1ca29061e64d4e514830eb26a728a41879905394520c3ac829ca29063664d46514831ab26a328a419598f5194520caac7a8ca29043e76d51514821f3b0a8a8a4187d536354520c38a9b1aa29061f5418d514830e2a0c6a8a41179db5354520c3ec9a9aa29061c64d4d514822f3b0a6a8a4187d905354520c38c829aa29047776544514829bba2a228a414d1d15114520aaee6a88a29055473544514831b32ea828a411d5da5414520aace72a0a29055573950514823bbb2a828a4155dcd5414520aa8e6aa0a29063665150514832b32ea628a41c5d535314520e28a9a98a2904757694c514829b3a4a628a414d5d253145208eeeca98a2905377454c514829a3a2a628a41959945314520e2ea8298a2907145414c5148393aa2c428a41c91516214520e8ea6b10a2907445358851482b2b96c828a415c5c36414520acae4320a29056572d8c514829b3a0c628a414d5d06314520acae4318a2905717018c514823bbb28628a411d1d94314520acee4a18a2905647250c51482b9b828628a415c1c14314520acce4218a2905657210c51482b9b828428a415c1c142145208eced190a290573704c851482b83826428a414d9d03214520a6ae8190a29053674d80514829aba6c028a414ddd16014520a68e8b00a2905577358051482aa39ac028a414ddd12014520a68e8900a2905577348051482aa39a4028a4117dcd65d05208b8e6b2e829045f73596414822e39acb20a418bd526290520c98a7314829064c5358a4148333310a320a41995885190520c76a9304829065853982414833828cc120a419614d6090520ce0a2b04829045e73d95414822eb9ecaa0a4117dcd65105208b8e6b28829062c54988414832629cc420a419314d6210520cccc4288829066562144414821fba2cb98a410f1d165cc52087ee8b2c629043c745963148317aa4c518a418b152628c520c9ea7314629064c5398a3148317aa2c518a418b151628c520c98a6b14629066662d463148332b16a318a4199988518c520ccac428c629043e74d95314821eba6ca98a410fdd1650c520878e8b28629043e74194314821eba0ca18a410f9d6640c520878eab20629043f76d50314821ebb6a818a410fdd8540c52087aec2a0629061e64d4c314830eb26a618a4187990530c520c3ac8298629046e75988314832629cc418a419314d620c520c6cc9a88629063564d44314831b320a218a418d590510c520cccc4288629066562144314832c29cc018a419c146600c520ccee332e429062e65d532148317328a990a419399753c85208da
  | 16 => 0x832ba9ac329a418d9926194d20c6ac930ca690665629865348332b94c329a418d9916194d20c6ac8b0ca69043f74582534821e3a2c129a410f9db5454d2087cec2a2a69063754d85534831a2a6c2a9a418dd506154d20c68a830aa69061f64d8d534830e326c6a9a418bd936254d20c58c9b12a69063764d85534831a326c2a9a4195d8f6154d20ccec5b0aa69063764185534831a320c2a9a4195d8c6154d20ccec430aa69043e74d81534821eba6c0a9a418e1936054d20ce0c3b02a69045f7654c534828fba2a629a41471d15314d20aaee2a98a6905547154c534823bb8ac829a411d1c56414d20a3ce9318a69051d7498c53482ab38cc629a41555c66314d2087ce8310a69043d74188534830f32ea829a41175da5414d20aace32a0a69055571950534822fbb2a829a4155dc55414d20aa8e2aa0a69061e6515053482a7b92c829a4155dc56414d20aa8e2b20a69055b7059053482a6b90c829a41535ca6114d20a3ce8308a69051d7418453482a6b90c229a41565c06114d20a3ce9b00a69051d74d80534828fba2c029a41471d16014d20aaee2b00a69055471580534828fba24029a41471d12014d208dae5b2e869047671d97434823ab8ecba1a411ddc565d0d208e8e2b2e869047671d96434823ab8ecb21a411ddc56590d208e8e2b2c869047671d95434823ab8ecaa1a411d9c66550d208eae332a869046f72595434823bb8acaa1a411d1c56550d208f6e0b2a869046c7219543482373aec4a1a418bd536250d20c58a9b12869064c53d894348317aa0c4a1a418b1506250d20c9ea6312869064c53189434823b3aec2a1a418dd536150d20c68a9b0a869065753d85434832a29ec2a1a411d9d46150d20c6ea830a869063454185434832ba98c2a1a419514c6150d208f4ebb02869063854d81434832c29ec0a1a418ed506050d20c70a8302869065b53181434832c298c0a1a411d9c76510d208eae3b28869047771594434823a38aca21a418b1526210d20c98a7310869046c75588434832629ac421a418e15260d0920cb0a7b02849063b54181424832c298c0a12419614e60cc920c6ea930c649063454986324832ba9cc3192419514e618c920c6ea8b0c649063454586324832ba9ac3192419514d618c920c70a9b02649063854181324832da98c0992412e1c1640c92087eedaa0649043d76d50324821fbb0a8192410f5d8540c920c3cc9a98649061d64d4c324830f320a61924187590530c92087ce931ea29043d7498f51482ab39ca9a8a41555ce54d4520aaee6aa6a29055473553514838baa6a7a8a41c515353d4520a6ce929ea2905357494f514829bba2a7a8a414d1d153d4520e2ea829ea2907145414f51483a229ec5a8a414d9d263d4520a6ae931ea2905677258f514823bbb287a8a411d1d943d4520acee4a1ea2905
  | 17 => 0x8641179da534c320c5ca9b12619062d54d8930c83172a0c4986418b550624c320c9ca6312619064d5318930c831b2a6c2986418d553614c320c6ca830a61906355418530c832b298c2986419554c614c3208baeda98619055671d4c30c838c29880186419a58a60d522087eecaa0a9104777158c548823a38ac62a4414e1c16494e20c5ee4b24a71062c72592538831db82c929c418e1c16494e20ccec5b0aa71066762185538822fbb2a629c411d9c765d0e208eae3b2e871047671995438823ab8ccaa1c411ddc56550e208e8e2b2a871051e73d5143883162a0c4a1c418ed506050e20c70a8302871047671194438823ab88ca21c410f9da5450a2087aedaa085105677154f3288236bacc399441179da534ca20970e0b20651045d76d4c328827238aca1944159dc5650ca20c5acab2065105a87059032882a6b9ca8194411b5d8540ca208daeda9865104cd76d4c32882e5386a61944159dc5530ca20b94e029865104e4715803288327b1864a8c411ddd951146208bce7b2e831045d73d97418821f3a6cb98c410f5d365cc62087ce9b28631043d74d943188274392c018c41785c031886209d2e031843104e576d4421882f1386a210c41789c05108620998e6b00431043d7694e408829bb8aa7204414d1c5539022095aec194811043d7694c408829bb8aa6204414d1c5531022095aec19081105a97008440882aa38aa718441551c5530c220e34a620061107195310030883c41908018441391c565c8220acee2b2e411062d659932088316b2ac9904419998551c8220c72cb3264110639655932088296b96c7aa2414d9c763d5120a6ae3b1ea89053970d8f5448296b90c3aa2414e5c061d5120c3ea931ca89061f5458e544831baa4c32a2418dd516195120c9cc6b14a89065663986544832ab1cc32a2419958a6195120cacc6b0ca89065563586544830fb26c6aa24187d906355120c98c7b12a89063764d85544832bb1ec2aa2419518f6155120c6ec830aa89065763185544832a318c2aa24199d886155120cb0c7b02a89067061d81544821fbb2a82a24147dcd5415120a38e6aa0a89053771550544829a38aa82a241479ce6415120a3ae7320a89053671990544829ab8cc82a2411bdc963151208eee2b18a8904747158c5448297b92c62a2414ddc56315120a68e2b18a89053b7058c5448296b90c62a2414b5c8611512087ce930ea69043d7498753482ab38ca9a9a41555c654d4d20aaee2aa6a6905547155353482a6b96c9a9a41559c764d4d20aaae3b26a69055970d93534828f3a4c3a9a41475d261d4d20a9ae430ea69051e74d83534828eba6c1a9a41559c760d4d20aaae3b06a69051f74583534828e3a2c1a9a41879935394d20c3ac9a9ca69063754986534831a2a4c329a4195d4e6194d20c6ea8b0ca69063454586534
  | 18 => 0x395320a76e0b1ca99061d6318e54c8297390c72a6414d9c46395320a6ae231ca99051e7318a54c828eb98c52a6414d9c46295320a6ae2314a99051e7318654c828eb98c32a6414b9c86195320a3ce7b04a99051d73d8254c829b38ec12a6414d5c76095320a58e4b1aa9905377158d54c829a38ac6aa6414edc16355320c3ac631aa9905367198954c829ab8cc4aa6414b9ca6155320a76e0b0aa99051f7358154c828e39ac0aa6414ddc56055320a68e2b02a99043f7655054c831b2a4c3a9e418d55261d4f20c6ca8b0ea7906355458753c8317324c5a9e418b59262d4f20c6cc930ea7906356498753c8333314c3a9e418d99161d4f20c6ac8b0ea7906666258753c831d322c1a9e41559c75394f20aace3b1aa79043e7418553c821eba0c2a9e410f5da5414f2087eecaa0a79045f7654c53c82b2b8cc429e411d9c465d0f208eae232e87904767199543c823ab8ccaa1e411ddc56550f208e8e2b2a879051c7355143c83172a6c4a1e418b5536250f20c5ca8312879062d5418943c831b2a6c2a1e418d5536150f20c6ca830a87906355418543c831d2a6c0a1e418e9506050f20c72a8302879047671d9443c823ab8eca21e41475ce5410f20c5ca8b1087906395498242c831d2a4c0216418d952618cb20c6aa930c65906565398632c832aa9cc3196418d951618cb20c6aa8b0c659063a5498232c831d2a2c1196410f5d6640cb2087eeab20659043d7695032c821fbb2a8196418795263d4720c3aa931ea39061e5458f51c830eaa2c7a8e41559cf519472087ce831aa39043d7418d51c821ebb4a828e410fdd954147208eeeca88a39062d5458a41c831caa0c0a0e41179cf65107208bae7b28839062e5458841c821f3a4cb98e410f5d265cc72087ce932c639043d7499631c83172a4c518e418b552628c720c9ca7314639064d5398a31c83172a2c518e418b551628c72087ce832a639043d7419531c831d2a6c098e418e950604c72087ce9b28639043d74d9431c821f3a4ca18e410f5d2650c72087aeb320639043f7559031c825c382c818e410fdda540c72087aed2a0639043f7655031c821ebb2a818e418bd965448720c5ecaaa243905667194d21c82373b0a690e41719cf5148720bc2e1a8a43904e67614521c83932a0a290e41c95505148720acceb98a4390746530c521c83932a24210e41c95512108720c74a9300439063a5458021c837090ac010e418b95162d032087aeda9c819053671d4e40c829ab8ea7206410f5d8539032087ced2a2819062d54d8940c821ebb6a8206410f5db5310320a6ce3a98819053571d4c40c821ebb0a6206416a1c1211032087aeb326619043f7559330c821ebb4a9986410fdd954cc3209cae3316619071a5310330c82ab38ea7186410f5d7644c32087aea322619043e7695130c821e3b2a89
  | 19 => 0x7b10801863965588400c2cdb9ac420061661cd6210030a74ea310801853975188400c2cd398c420061665cc6210030b64e231080185b171188400c25cbb0a420061ca5485210030b64e229080185b171148400c29cbac64200616c9c63210030b62e3190801859b768c8400c2ccbb46420061665d63210030e32eb190801859a728c8400c3c53146420061e258a3210030b34e31908018792718c8400c2c938c6420061e45c63210030a76ea99080184ba760c8400c25cbb06420061e24c83210030b36ec190801869a760c8400c2ccbb06420061a65d83210030b34e4190801878a720c8400c3c5b106420061e21883210030f14a41908018789520c8400c2cd38864200614e9d76110030a72ebb08801859a73d84400c2ccb9ec2200618e5956110030b36e6b08801859873584400c29d3a8c2200614e5d46110030b34e6308801859973184400c2d5390c2200616a5c86110030972ec28880185aa72144400c2d4b90a220061cc5445110030a72eb18880185aa728c4400c2d4b94622006166dda3110030b32ed1888018599758c4400c38cbac6220061669ca3110030f14e5188801858a728c4400c3c4b946220061669c63110030f24c31888018791618c4400c29dbaa62200612e9d83110030972ec1888018791310c4400c2cdbb06220061a69d83110030b32ec1888018699760c4400c2cd3906220061669c43110030f24e21888018793610c4400c3c83086220061e49443110030f22a2188801859a73c84400c2ccb9e4220061e20cb2110030b34e7108801859973884400c3c818c42200614edd52110030a70ea908801859b73484400c2cc39a4220061e20c92110030f2062908801853a75084400c29cba8422006166dcc2110030b30e610880187a121084400c26b38cc598061339ca61cc030b32ec206601869976103300c34d3108198061a698440cc0308baed29c60184797694e300c2e938c6518061729ca318c030974ed202601863b65901300c31db288098061aad88404c030d50c420260186b361101300c358308809806187d97644c030c3eca322601864f65d89300c327b28c498061a3d90624c030d18c8312601865765d85300c362316c29806195d94614c030d2ec830a601869464185300c363b10c298061b1188614c03093ced202601861f65901300c3463148098061a5186404c03093cec202601861f65101300c3463108098061a5184404c030d36c0202601863b65d91300c23cbacc8980612e9d2644c030c76ca32260186386494d300c34c324a6980619ad97624c030d50c9b12601866b65189300c354320c498061b2d8c624c030ce6cbb0a60186b064d85300c339b28c298061ac190614c030da6c630a60186e062185300c335312c1aa6411ddc563953208e8e2b1ca99052c7258e54c829bb8ac72a6414d1c56
  | 20 => 0xf76550430c237bb2a4290618b5915214830ccaa4b08a4184d47158f420c23bb8acaa10611d1c565508308ece232a841847571195420c30eaa0c6a10619a5486050830970e8b06641862d64948320c316b22a4190612e1d1600c830b30e0b2064185c571988320c2a6ba88419061351c5600c830b30e8b00641847776544510c31ab22a228861995895114430998e4b1e821846f72595410c236392caa08611b9c865504308dae432a821861d5418d410c338a88c0a08612e1d160cc430c6ac9288621863564544310c25c3a2c018861661c1640c430b8ae5308621855575104310c266392c018861661d1600c430c9aca1964218655650c6210c21fba2ca908610f1d1654843087ce832a421843d74195210c32631aa490861591c55248430ca8c6a8a421856472545210c25d3a6c090861b20c86048430da06230242184ce72d8c210c26b38ec61086199d952108430ccaca90842186c463484210c2f03824210861559c63294030a9ce518ca0185d2718cb400c2e539463a0061875526390030a5ce5b2c801852d72d96400c29b38ecb200614d5c76590030a5ce532c801852d72996400c29b38ccb200614d5c66590030a74e032c801861f6598e400c21ebb4a720061659c6329003093aec194801858e728c6400c24ebb06320061331c963100309a8e2b18801852e72194400c296b90ca200614d9c46510030a6ae2328801853a70194400c30e32ac620061631c96310030b28e2b18801843d7694c400c2cb38c6420061665c2321003093aec190801858e728c4400c2ccb846220061275d83110030a72eb300801863965980400c23dbb2a8200611edd56310030b90e4b1880185d07158c400c29cba4a6200614e5d74310030c72cb218801853b7550c400c2d5b9286200616a1c94310030b66e2a1880185b07150c400c31cb2886200618e5974210030b34e7a10801859973d08400c31cb2a842006166dcd4210030b30e6a1080185d2718c8400c3c5a106420061e21083210030c72cba08801859a73d04400c2ccb9e82200618e5954110030b36e6a08801859873504400c2e53946220061e4d043110030f2082188801859a73994400c29d39cca20061c69ce6510030c76ecb28801853975d8c400c31cb2cc620061665da6310030d36cb31880186996598c400c2cd394c620061669c66310030a76eab1880185ab7258c400c2d4392c6200616cdc56310030b60e2b18801869b7658c400c2cdbaac620061c6dd56310030f16e4b1880185987258c400c3c4392c620061621c96310030f26e2b1880185987158c400c3c838ac620061641c56310030a74ea31880186396518c400c2cd398c6200616a9c86310030b52e431880185b27118c400c2d8b88c6200614e5da5310030c72ed298801853a75d88400c29cbaec420061669cf6210030b32e
  | 21 => 0x29a3a26028a6159dc93014530ac8e4980a29846f72597414c236392cba0a611bdc965905308d8e4b2c829846e72d95414c236b96caa0a611bdc965105308d8e4b28829861c5498c414c327318a420a619358c5210530cacc6288829865563144414c2373acc518a618bd52628c530c58a9314629846c7558a314c317aa2c518a618b151628c5308daeda94629846d7614a314c333316a318a619958b518c530cccc428c629866562146314c31c2a4c118a619c146608c530c70a8b04629863854d81314c334296c098a618e150604c530cd0a4302629867351181314c21fbb6a818a610f5db540c53087eec2a0629843d76150314c317326a418a618b593520c530c5cc8290629862d64148314c31b326a218a618d593510c53087ee8b2e429843c74597214c21fba2cb10a610f1d1658853087ce9b2a429843d74d95214c2b338ea490a61599cb514853087ee8b28429843c74594214c2b2b88a410a61595c85108530accea908429856475484214c33332a4210a61991952108530e4ea8908429872454484214c31c2a4c010a619a14a6008530ce0a3300429863854580214c37090ac010a618715263d0130c9cc6296809864d6314b404c32b318a3a02619558c51d0130a5ce52a4809852d72952404c29b38ca9202614d5c65490130a5ee4aa4809852c72552404c29bb8aa9202614d1c55490130c5ccba94809862e6514a404c31b32ea320261c9d4b5190130e48a5a8c809863665146404c393a90a320261c9148519013087cec2a2809861f5418d404c327b18a4a02619318c5250130caec628a809865463145404c297394a8202614b5ca5410130a6ce32a0809853571950404c29cb84a8202610fdd95410130a5ee4aa0809852c72550404c29bb8aa8202614d1c55410130a76e0aa0809862e65d48404c317328a4202618d9975110130e4ea5a88809872452d44404c31b328a220261c9d485110130e48a4288809872b52980404c394294c020261ccd466010130e60a3300809862e64d4b304c316b26a5982618b99052cc130c5ac8296609863664d47304c31ab26a3982618d99051cc130c6ac828e609872b52103304c3942908198261ccd4440cc130e60a2206609872854d4b304c3942a0a598261cc15351cc130e60a828e609876052147304c387aa0a518261c3150528c130e88a5a8c609871754146304c38a2a0a318261d1d48518c130e88a428c609851e75902304c3862948118261c5146408c130a3cea204609870c52102304c38a28881182610fdd95415030c5aa8b10a81863554584540c317322c42a0619398d6215030cccc5308a81866562984540c31b322c22a0619598d6115030cccc4b08a81866562584540c31db82c9298614b5c854d0c30a6ae22a6861851e73d51430c21f3b0a8a18614b5c85450c30a6ae22a2861843
  | 22 => 0x2618d15061549308deeca90a49852f74548524c2963a2a42926159dc55214930ac8e2a90a49862e65d50524c236bb4a829261599c65414930acae32a0a49846f76550524c2b3b8aa829261591c55414930c5cca2a0a49854d73190524c2b338ec629261595c763149308deeca18a4985677150c524c2b238a86292615adc14314930ad0e0a18a49870d4310c524c332b08c2292615a5c06114930a5ce9b00a49852d74d80524c297ba2c0292614b1d16014930acee2b00a49856471580524c297ba260292614b1d130149308eee2b2e849847471597424c23bb8acb212611d1c565909308ece3b2a849847571d95424c23bb8aca212611d1c56510930c38a9318849864e63148424c326b18a4212611d9d6618c930c6ea930c649863454986324c333a94c3192619914a618c9308e8eab0c649863754586324c31a2a2c31926199d49618c930cc8a4b0c649863854982324c334294c1192618e151608c930c70a9b02649863854181324c335a90c0992610fddb540c93087aedaa0649843f76150324c21ebb0a8192618b993520c930c5ac9a90649856672953514c2b2b94a9a8a6159dc954d4530ac8e4aa6a29872754d4b514c3922a6a5a8a614d9d252d4530a6ae9296a2985377454b514c29a3a2a5a8a61c9d5052d4530e48a8296a2984777650f514c2b3b9287a8a61591c943d4530ae6e0a1ea2985707050f514c333b14c5a8a611d5da32d4530a6ce8196a298535740cb514c29b3a6c1a8a614d5d360d4530acce5b06a29856572d83514c29bba2c1a8a614d1d160d4530c5ea9314a29862c5498a514c317aa2c528a618b1516294530c5cc9a94a29862d64d4a514c317320a528a618b5905294530c6cc9a8ca29863564d46514c333316a328a619958b519453087cedaa2a29843e76151514c317aa6c4a8a618b1536254530c5ea8312a29862c54189514c2373b6a4a8a618bd935254530c58c9a92a29846e76149514c317b20a4a8a618b19052545308eeeca88a29853774544514c29a3a2a228a6159dc95114530ac8e4a88a29863665d50514c23abb4a828a61599ca5414530acae52a0a29847776550514c2b3b92a828a61591c95414530c6cca2a0a29866665d48514c393aa6a428a61c915352145308eaed290a29853674948514c29aba4a428a611ddd95214530a6ee8a90a29853474548514c333328a428a61c9d505214530e48a8290a29855573190514c2b3396c628a61595cb63145308eeeca18a2985677250c514c2b23928628a615cdc14314530ae0e0a18a2987154310c514c332b10c428a615c5c06214530aace6210a29855573108514c23abb46428a615cdc13214530ae0e0990a298536740c8514c29aba06428a614d9d36014530a6ae9b00a29853774580514c29a3a2c028a6159dc96014530ac8e4b00a298537744c0514c
  | 23 => 0x8ca30c3acab2065185c571988328c266bb6a419461729c3520ca30b8ae229065185ca70148328c2a73a88419461351c5600ca30c68e2b24a31847776544518c332b12a228c611b9cb65d06308dae5b2e831846e72997418c236b94cba0c614d9c754d0630998e4b1e831853574947418c30faa0c6a0c619958a518c630ccac4a8c63186ca62982318c30eb2ac818c61715ca610c6309aaeda8863185d270d44318c2e2b90a218c61749c0510c630aacea20863184cc72580318c21f3a6cb90c610f5d365c8630c9ac7296431864e650cb218c21f3a6cb10c610f5d36588630caac728c4318656650c6218c21f3a6ca90c610f5d36548630ac8e2a92431856472545218c21f3a6ca10c610f5d365086309b2e0318431866765484218c332b2a4210c61b118d21086309b0e6b0043186e121580218c21ebb4a520461659c6329023093aec194811843d76946408c2c73946320461275d83190230c3ca8b1881184cc7258c408c26a38ac6204614b9ca6510230a5ae5328811853671994408c29ab8cca20461631c96310230b28e2b18811843d76948408c2cb38c6420461275d8321023087aed288811858e728c4408c24ebb062204618759664cc230c3acab2661184d67198b308c267394c3984618e59664cc230c72cab26611852e72d8f544c296b96c7aa2614d9c763d5130a6ae3b1ea89862f5498a544c317aa2c52a2618dd526195130c6ea8b0ca89864d6398a544c32ab1cc32a2619998a6195130ccac530ca89866662586544c332b12c32a2618bd936255130c5ec8312a89864f63189544c31bb26c2aa26199d8b6155130cc8c5b0aa89863764185544c32bb18c2aa26199d886155130cc8c430aa89866b62d81544c334316c0aa2619cd876055130ce0c3b02a89843f76550544c297b92a82a2614b1c95415130a6ee2aa0a89853471550544c297394c82a2614b5ca6415130a6ce3320a89853571990544c297b92c62a2614b1c96315130a6ee2b18a8985347158c544c28eb98c42a261475cc6115130c70a9306869863854583434c2373aec4a1a618bd536250d30c58a9b12869846e75189434c317aa0c4a1a618b1506250d308ecebb0a869863754d85434c31a2a6c2a1a611d9d46150d30c6ea830a869863454185434c31c2a6c0a1a618ed506050d30c70a8302869851c7550c434c2b338ca9a9261595c654d4930acee2aa6a49856471553524c237bb287a926159dc543d4930ac8e2a1ea49856b7050f524c2b438287a926199d8661d4930a5ce9b06a49852d74d83524c2b338ec1a9261595c760d4930a5ee8b06a49852c74583524c317326a5292618b5935294930c6ea930ca49863454986524c333a94c3292618dd516194930c68a8b0ca49866752586524c21f3b6a8a92610f9d85454930c6ea9b0aa49863454d85524c31baa0c2a9
  | 24 => 0xb0c659843d7599032cc21fbaac8196612e1c1640cb3087aed2a0659843f7655032cc2b2b8ca4196612e1d1600cb30c5ca9316a39862d5498b51cc3172a2c5a8e618b55162d4730c5ca9314a39862d5498a51cc3172a2c528e618b5516294730acce5a8ca39866562d4651cc21ebb4a828e610fdd954147308eeeca88a39846e72d9641cc236b96cb20e618e5526090730c72a8302839846e72d9441cc236b96ca20e61879516310730acae528e63984b87458331cc3172a4c518e618b552628c730c5ca8b14639862d5458a31cc21ebacc818e610fdd5640c730970e0b20639843d7695031cc21fbb2a818e61595ca510c730970e8b00639843e7499721cc21eba4cb90e61595ca51c873087ce932c439843d7499621cc2b2b8ca510e610f9d0654873087ae832a43984ba74d8121cc31d2a6c090e618e950604873087ce9328439843d7499421cc2b2b8ca410e61595ca5108730aceea90843985657548421cc33332a4210e61c99512108730e4aa890843985e07048421cc30f2a2c7a06618e59654d0330a6ce329481985357194a40cc297394a3206614b5ca519033087ced2a2819861d54d8d40cc21ebb6a8206614d9c65210330a6ae3290819852e7294440cc296b94a2206611e5db5410330972edaa0819859a73d5040cc31cb2ca820661669cc5410330b56e4a1881985a87250c40cc2d9b8a86206616c1c54310330d32c6218819853975d0840cc29cba88420661669cc4210330a72eba0881985397510440cc2cd39882206618e5966310330b56e4b1881985a87258c40cc2d9b8ac6206616c1c56310330c72ca31881986996318c40cc2d5390c6206616a5c86310330b64e231881985b17118c40cc29cbaec4206614e5d46210330b34e631081985997318840cc2d9388c4206616c5c46210330972eda9081985b271d4840cc2d8b8ea420661cad4a5210330b64e329081985b17194840cc25cbb0a4206616c9c63210330b62e319081984ba760c840cc25cbb064206614e5d76110330a72ea308819859a7318440cc2ccb98c2206616a9c86110330b52e430881984b976d4440cc2d5396a2206616a5cb5110330b54e528881985a97294440cc399a8ca2206612e5d85110330b54e518881985a9728c440cc25d3b062206612e5d83110330a76ea90881985387548440cc29d3a842206614e5d42110330f4242108819866662987548c332b14c3aa4619998961d5230ccac4b0ea91866a62983548c334b14c1aa4619c98660d5230ce2c3306a91843f76550548c21f3b4a8a1c618e9506050e30c72a8302871843d76d50438c316392c9294611bdd95214a30ccaa4b08a51847671d97428c23ab8ecba14611d9c665d0a308eae332e851852e72d53428c26a38ac7a14614b5d252d0a30c3ea831a851866652586328c332a92c319461b498660
  | 25 => 0x701942110257396c6108812d9c76308440974e1b1842204b970d8c211025db82c6108812e1c1630844087cea318422043d7518c211025d380c6108812e5c06308440b4ae510842204af7648421102d438242108812ddd92108440b60e090842205a7764842110353bb24210881a9d952108440d4aca90842206a663484211035231a4210881e8dc12108440b48e090842207a07048421102d03824210881e84866008440972eb30042204ba73980211024fb9ac010881271cd6008440d4a42b0042205987358021103d090ac0108812edd56008440c76eab00422069b73580211025c39ac010881a61cd6008440930e6b0042206ab21580211035910ac010881aa4856008440d6242b0042206a121580211030f31aa7280814bdc95394040a58e4a9ca0205377154e501029a38aa7280814d9c63294040a6ae3194a02043d760ca501029739463280814b5ca319404087aec18ca0207252108650102d5396c7280816a5cb6394040b64e3b1ca0205b171d8e501034d31ca728081a698d5394040b56e4a9ca0205a87254e50102d9b8aa7280816c1c55394040b54e429ca0205a97214e50102d9388a7280816c5c45394040d52c4314a0205b27118a50102d8b88c528081669cc5294040b32e6294a0205b27114a50102d8b88a5280812e9da3294040972ed194a0205b2718ca50102d8b8c65280812edd93294040970ec994a0205aa7218650102d4b90c328081ac5846194040b34e628ca0205997314650102d5390a3280816a5c85194040974ed18ca0204b9768c650102d539463280816a5ca3194040976ec98ca0204b8764c6501025dbb243280812e1d92194040974ec10ca0204b97608650103d090843280814b9c86395330a5ae431ca9985367118e54cc29ab88c72a661479cc6295330a6ce2314a9985357118a54cc28f398c32a6614b9c86195330a5ae430ca99852e72d8254cc296b96c12a6614d9c76095330a6ae3b04a9985367198954cc29ab8cc4aa6614e5c26255330a76e0b12a99852e7298554cc296b94c2aa6614e5c26155330a76e0b0aa99852f7258154cc296392c0aa6614ddc56055330a68e2b02a99843f7655054cc31caa4c121e618b9536250f30c5aa9b12879862e5418943cc316aa0c4a1e618d9536150f30c6aa9b0a87986365418543cc31aaa0c2a1e618e9506050f30c72a830287985987050c43cc31d2a4c021e618d95261d4b30c6aa930ea5986365458752cc31aaa2c3a9661599c75294b30c6ca930ca5986355498652cc31b2a2c3296618d5516194b30ccea4b0ca59843d7695052cc21fbb2a8296611bdd95214b308ece3b2c859847571d9642cc31caa4c1216618e5506050b308ece3b28859847571d9442cc30f2a2c621661595c652ccb30970e8b0665986365498632cc31aaa4c3196618d951618cb30c6aa8
  | 26 => 0x4731cc428881a358e6214440d1cc6b10a22068d63588511030eb1ea228881a558e5114440d4ac5288a22043f76544511030eb1aa2288812ddd95114440d2ac6a88a2206a562544511034d31cc028881a658e6014440d54c5300a2206a962980511025d39cc028881ac9466014440d62a3300a2204ba709973110257390cb988812b5c865cc440974e032e622061c6554f31102ca38aa7988812e9c262cc440972e1316622071553d4731102d9386a398881655cc51cc440b4ae428e62205b2701473110257396cb188812b5cb658c440974e132c62204ae721963110256b90cb188812e9c0658c440d4ac528c62206a5625463110352b166318881aa98a608c440d52c530462204b975982311035928cc118881ac546608c440d666330462206aa625823110354b12c1188812edd5608c440c76eab0462204ba709953110257b92ca988812b1c9654c44096ee2b2a62204ae721953110256b90ca988812e9c0654c440c38caa9a62204b676945311038aa9aa2988812e5d7604c440c72ebb0262204b975181311034d298c098881a654c604c440d64a230262206b1511813110359988c098881a68c4604c440974e1328622043d76994311031d384ca188818d1c5650c44095ce432862204ad72194311025d380ca188812edc1620c440970e0b1062204b576d44311031ab2ea2188816c9c3510c44096aec28862206356514431102cab98a218881695c8510c440b64e0288622061d65cc4311031ab2c6218881695ca310c440b64e1188622049f764c4311030eb2a6218881661c1310c44096eec9886220635654c431102d838262188812bdc9600c440958e4b0062204ba70997211024f398cb90881275cc65c8440974e032e42204ba70d8f211025cb86c7908812edc163c8440970e0b1e422043e7518f211021eba8c7908814b5d432c8440d1ac619642204ba70996211024f398cb10881275cc6588440974e032c42204ba70d8e211025cb86c7108812edc16388440970e0b1c422043e7518e211021eba8c7108814d5d43188440d2ac618c42204ba70995211024fb9aca90881271cd654844093ce632a422049d73195211025d380ca908812e9c36348440972e1b1a42204ba7098d211025cb84c6908810fdd56348440878eab1a42204bb7058d211025c382c6908810f9d4634844087aea31a422062c6554921102d238aa4908812b9db3248440b4ce3992422052d750c9211031a32aa290881691c9514844096ced98a42205a672cc5211029aba862908812e5d76048440c72ebb0242204ba73d81211025cba8c0908812e9cc6048440d54a430242206a9521812110355990c090881aa0c86048440d64a230242206b1511812110359988c090881ac0c46048440d664230242206aa21181211025d384ca10881279cc650844093ae632842204ba
  | 27 => 0x81aa1886054c40d66c2302a6206b061181531021fbb2a62988127dd95314c40a3eeca98a62061f7654c5310387b92a629881c31c95314c40e2ee2a98a6207147154c531038c382a629881c354e6214c40c3aa6b10a62070d535885310317a9ac429881a394d6214c40c5aa6b10a62068d535885310306a9ac429881c554e6114c40d4cc5308a6206a562984531030ea9ac229881c554d6114c40d4cc4b08a6206a562584531031ba9ac229881a594d6114c40c6aa6b08a62069553584531030aa9ac2298818754e6014c40e32a7300a6206aa629805310354b14c029881ac9866014c40d62c3300a62069a53980531034ca9cc0298812ddc563d4840968e2b1ea42052c7254f521025d39cc1a90812e1c16394840b54e1a94a4204b870586521025d386c6a90818718d5354840b54e1a92a4204ba70185521034c384c629081a31c96314840d30e0b18a42061d63d485210346b1ca4290810fdd95214840c3ac6a90a4204af765485210346b1aa429081a598e6114840d2ac7308a42069663584521034ab1ac229081a99496114840d4aa4b08a42069a63980521034cb1cc029081ac9866014840d62c3300a4204ba739805210355294c029081aa54a6014840974e132e64204b671197321025ab88cb990812e9c065cc840c38caa9e642058c7254f3210386a9ea5990816a9c352cc840b1ae629664205a57114b32102d5380a5990812e9c261cc840972e130e64204b671d96321025ab8ecb190812e9c2658c84096ce232c64204b571196321025d380cb19081a9949618c840d4aa4b0c64206a732586321035930cc119081ac586608c840972eb30464206aa529823210354a94c119081aacca608c840d64c2b0464206b161582321025dbaac1190818edd5608c840974e132a64204af72595321025bb8aca990812d1c5654c84096ce232a64204b571195321025d380ca9908187195534c84095ced292642070d53549321025cbaec0990818e5d7604c840972ea302642069a53181321034ca98c099081aa948604c840d52a430264206ab32181321034d190c0990812e9c2650c84087aed328642063a709943210316392ca190812d9c4650c84096ae232864204ba701943210256bb6a4190818b597520c840b54e1a9064204ad761483210316b28a419081635cc520c840b4ae229064205aa70148321030eb2e64190818b596320c840b4ae319064205aa708c8321024fbb2641908187595320c840b30e099064204af764c83210316b2a64190816a1c1320c840976e0b0864204b870584321025bb8ac0190812d1c5600c84095ee4b1ea2204ac7258f511029a38aa7a88812e9ce60d4440970e0b1ca2204b87058a51102d9386a3288812e9c36354440c38c6a9aa2204ba7018951102d9386a2a8881a61c26314440d28e2b18a2206987058c51103
  | 28 => 0xc40a72ebb04862062d751894310353b16c2a1881a918b6150c40d4ec430a86206a462185431031aba8c2a1881aad8b6050c40d50c5b0286206b361d81431035830ec0a18818ed946050c40d56c430286206a8621814310359b08c0a1881ac1846050c40a3aeb318862051f7654c431030fbb2a621881c3dc95310c40e18e4a9886207177154c431038a38aa621881c61c15310c40c3aa6b10862061d53584431030e31a86a90811bdd95214840c9ac6a90a42066552584521025bb8ac7a10812d1c563d0840976e0b1e842052c7254f421025db82c7210812e5c36350840c38c6a9a84204bb7058c421025b388c9990812d5c464cc840c38c8a9e642054c7254f3210386a9e85990811d9c7658c8408eae3b2c64204b671d92321025ab8ec9190812e5c3648c84096ce232464204b571192321025cb80c91908199949618c840ccaa4b0c64204bb74582321023bb8aca990811d1c5654c8408ece232a642047571195321025cb84c8990812bdc9644c84096ee2b2264204b471591321025db82c89908187191534c840972e9b02642043d75d903210316b2e84190812b5d8420c840c5aca210642058d73108321030e31a86a88811ddd95114440caac6a88a220665625445110257b92c7a08812b1c963d0440976e0b1e82205347154f411025db82c7208812e5c36350440c38c6a9a82204bb7058c4110257390c9988812b5c864cc440c38c8a9e62205547154f311038aa9e83988811b9cb658c4408dae5b2c62204ae72d923110256b96c9188812e5c3648c44095ce432462204ad72192311025cb80c9188819958a518c440ccac4a8c62204bb745823110237b92ca988811b1c9654c4408dce432a622046d72195311025cb84c8988812bdc9644c440958e4b2262204b771591311025db82c89888187191534c440972e9b02622043d75d90311031ab2e82188812d5d8410c440c6aca208622059573104311024f398c990881275cc64c844093ce6324422049d73192211022fb9aca90881171cd65484408bce632a422045d73195211025cb84c89088127dcd6448440938e6b2242204bb705912110316322a490881591c55248440c68c8a8a422056472545211025cba6c0908812e5c36408440972e03204220667654842110332b2a4210881781c12108440976e8b0042204d873580211037090ac0108814bdc94394040a58e4a1ca0205377150e501029a38a87280810f5da54900408f2ed2a4802069a6390e40102d5b9287200816a1c94390040b66e2a1c80205b07150e401034c31c86a00812e9d84350040b34e1a9ca6204b67198a531025ab8cc5298812e9c26294c40970e0b14a6204ae729865310256b94c3298812e9c26194c40970e0b0ca62059a70d4d5310353b16c2a9881a918b6154c40d4ec430aa6206a4621855310355b10c0a98
  | 29 => 0x9065205a5718c8329024fbb264194812bdd9320ca4096ee2b0065204b471580329030f31ea7a8c816c9c3519464095ce5b1aa3204ad72d8d519029b38ea6a8c814e9c35354640b64e1a8aa3206a562944519021fbb2a228c812ddd95114640d4ac4a88a3206aa629805190354b14c028c81ac9466014640d62a3300a3204ae72d973190256b96cb98c812b9ca65cc64095ae532e63204ba70997319025d380cb98c812b9cb658c64095ae5b2c63204ba709963190257390cb18c812b5c8658c640974e032c63206a562cc63190257394ca98c812b5ca654c640974e132a63204ba70195319025d384ca18c818d9c6650c640c74e132863204ae721943190256b90ca18c812e9c0650c640c6ccb288632059573944319031b32aa218c81695ca310c64093eec98863204b7764c43190257b92c018c812b1c9600c64093ce7b2e432049d73d97219025d384cb90c812e9c065c864087cea31e432043d7518f219031732ca590c814b5d432c8640d1ac6196432049e73d96219024eb9ecb10c812e9c26588640974e032c432043e7518e219021eba8c710c818d9965188640a6aea18c4320695630c6219024f39cca90c81275ce6548640974e132a43204ba70195219021fbaac690c810f1d56348640976e0b1a43204b87058d219021f3a8c690c810f5d46348640b48e2a9243205a671cc92190296ba86490c81691c95148640b4ce598a4320535750c5219025d384ca10c812e9c0650864087cea318432043d7518c219025d380c610c812e5c0630864095eec90843204b77648421902d3bb24210c81a9dd92108640d4eca90843206a565484219035331a4210c81a918d2108640b48e0908432049f73580219024e39ac010c81a948560086408beeca98a6a054c7254c53502aa38aa629a8193d4c6250d40c98a631286a065753185435032a298c2a1a819614f6050d40c3ccaa1886a04777158f525023a38ac7a92811bdd95214940a98e6a90a4a056471548525023b388cb192811d5c4658c940caea730c64a065453986325023bb8aca192811d1c5650c94087ceb32064a061d64d4c3250316b26a4192811bdc963d45408d8e4b1ea2a04777654451502aa39aa228a81591c951145408dce432c62a046d721963150327a9cc518a819314e628c5408dee4b2862a046c72594315021f3acc818a8187593530c540c6ac9a8862a045f73594215022e39aca10a81595c45208540acae428842a05667548421502b23aa4210a811d9c66294c408eae3314a62046e729865310236b94c3298818b9d06254c40c5ae8312a62066762d855310332316c2a988199d886154c40cc8c430aa62063674185531031aba0c2a98819ad886054c40cd0c4302a620673611815310338308c0a988117dd95314c40c9aa6b10a62065553584531025dbaac1a18818edd560d
  | 30 => 0x194821d02b2b94a210e8159dd52108740acaea90843a05e07048421d026c39ac010e81b848560087408ece3314a7204757198a5390237394c329c811b5ca6194e408beeca98a72065a53181439028f3b4a6a1c81879da5350e40e1ca7b12872070e5318943903173a8c4a1c818b5d46250e40e2ca7b0a87206a762d854390352316c2a1c81c594c6150e40d4ec430a87206a462185439031b3a8c2a1c818d5d46150e40e34a7b02872071a531814390355b10c0a1c81aa1886050e40d66c230287206b061181439023b38ec6a94811d5c76354a40a58e4a1aa52046f765485290332a92c2294812ddc563d0a40968e2b1e852047671d97329023ab8ecb994811d9c665cca408eae332e65204b671193329025ab88c9994811d9c7658ca408eae3b2c65204b671d92329025ab8ec9194812d9c4648ca4096ae232465204b771591329025a38ac8994818b592520ca40a9ae7290652062d6454832902c6b9884194811b9cb63546408dae5b1aa3205347150d519023bbb2a228c8199589511464095ee4b1e83204ac7258f4190237396cb98c811b5cb65cc6408dce532e632046d729973190257390c998c812b5c864cc6408dce5b2c632046d72d963190257396c918c812b5cb648c64095ce432463204ad721923190257b92c898c812b1c9644c640c6ac9288632055573944319031ab22a218c81655cc410c6408bce7b2e432045d73d97219024f398c990c81275cc64c8640c5ac9296432045e73d96219022eb9ecb10c81279cc648864093ae6324432063564946219024fb9ac890c81271cd6448640ac8e2a924320564725452190333b2a4210c81995952108640d4cc530ea7206a5629875390353312c3a9c81a958961d4e40d54c5306a7206a962983539035930cc1a9c81ac58660d4e40a74e1a9ca72059a70d4e539028ebb6a729c81875db5394e40e1ce5a9ca72070d72d4e539038b38ea729c81c55c75394e40a3ce1a9ca72071a70d4e539028d386a729c812d9c66294e4096ae3314a7204ae729865390256b94c329c81669c35354e4087eeca98a72049f7654c539034d29cc029c81a654e6014e40c3cc7a9ea5205aa70d4a529025b38ec6a94812d5c76354a40a5ce5a9aa52053a70d4d52902d5386a4a94810fdd95214a4095eeca90a5206a6525845290352a92c229481ac9866014a40d62c3300a5206aa529805290354a94c0294812d9c765cca4096ae3b2e65204b671997329025ab8ccb994812e9c265cca40974e032e65204b671d96329025ab8ecb194812e9c2658ca4096ce232c65204b571196329025d380cb19481a9cc9618ca4096ce332a65204b571995329025d384ca994812e9c0654ca40974e1328652062e72994329031d384ca194812d9c4650ca4096ae232865204ba70194329031732ca419481635ce520ca40c5ccaa
  | 31 => 0x729cc5188430f9d3650c42187ae9b286210c3e74194310861eba0ca188431bdd5620c421aaae72886210d57754c431086b4b80a7908431b5da5288421ae2e029c4210c757694a21086373b0a6908435a5c05348421acaeb18a4210d67754c521086d33a06290843695d03148421e8ca618a4210c767614d21086b8b80a690843595d63248421aceea9924210da6740c921086d2ba06490843d194c3248421ccaebb2a4210ce670d9521087333b6ca90843599cf6548421acae1b2a4210d657599121086b3baac89084371dcd6448421b88e6b224210de37059121086f0382c890843a959064484219ccedaa24210de270d5121086f0b86a890843399d85448421acaeb31a4210d677558d21086d3ba2c690843691d16348421bc6e0b1a4210de07058d21086d33a0c690843695d06348421d8ac631a4210ce676d4d21086b33b4a690843591da5348421acce729a4210f476394d21087a231ca690843595c253484219ccec29a4210da67414d21086d2ba0a690843789c05348421bc2e029a4210d667614d21087333b0a690843c99d05348421e4ae829a4210d667314d21087a3398a690843d89c05348421acae029a4210f617014d21086b0b80a690843599d74348421acaeba1a4210ce77650d21086723b2869084359dd54348421ac8eaa1a4210de37050d21086f03828690843399d843484219caec21a4210da674d8121086d2ba6c090843595d66048421aceeab024210da77458121086d23a2c09084371dcd6048421b88e6b024210e65751812108733298c0908439914c60484219ceec90ea010ea6644875008752b2243a8043391d92194021bc0e090ca010d3a74d42500861f3a4c7280430f5d263940219c8ec90aa010ea764485500875232242a8043b1d8d2154021d88c690aa010de070485500871cb86c8a804387d936354021c38c9b1aa010e1f6418d500870e320c6a8043965c06354021c98c790aa010d6a70c85500872a31c42a80435c9c22154021c98c690aa010d6870485500872a31a42a80435c1c12154021cceec90aa010d647648550087323b242a8043c9d912154021e48c890aa010f4763485500873231a42a8043d118d2154021c88c690aa010f637048550086b238242a8043d81c121540219ceec908a010c7b7654050086a7396a729e81559c75394f408beeca98a7a054e73d4a52d02b338ea5296811d9c76354b408eae3b1aa5a046f7654852d023b38ecb196811d5c7658cb40caca730c65a06555398632d023b38cca196811d5c6650cb40c3cc8a9865a062e6454832d02ab39ea328e81599cb51947408dce5b1aa3a046d72d8d51d023bbb2a228e811b9cb658c7408dae5b2c63a064e5398a31d0326a9cc518e811b9ca650c7408dae532863a061e6454c31d031b322a218e81179ce65087408bae732843a05657
  | 32 => 0x30e1c16414d2187ee8b00a690c3c74580534863d386cba1a431e5c365d0d21a38e6aa68690d3870553434868eba0a7a1a431b1d562d0d219c8e2b168690c74755874348672392c3a1a431e9c36590d218f2e1b2c8690c7a70995434863cb84caa1a431bdc96550d218eee2b2a8690c7b70595434863c382caa1a430f9da5450d21878ecaa28690d1c73551434869c382a8a1a431b9d76250d219cce3b128690c7675d854348673396c2a1a438e9506050d21c72a83028690c6d72d94434863ab8eca21a431edc16510d218f0e0b288690c3e74194434861ebb6a821a438d15161d0921ca8a6b0e6490c6d7695332486963a2a7992435a1c153cc9219cceb30e6490e66759873248672b84c3992431b1d560cc921c5ccab206490c6d7695032486a6b98a8192431bdd9530c921a58e8a986490d687054c32486b33a8c219243a9990610c921d4ac83086490de170184324867238ac0192438b15162d05218bee6b2a8290c5c73595414872629ac598a431d5da54cc521a68e8a9e6290d707054f31486733acc598a43999d662cc5219cae13166290d6675ccb314873332e6598a439999432cc5218e8eab066290c3f74595314861e3a2ca98a438d995640c5218eaed2a06290d5573150314863bbb2a618a434d1d1530c521ae0e0a986290d66751883148753320c418a43a9590620c521bc2e03106290d6675cc831487a2a986418a43391c9600c521d8cc61964290ec6630c6214871db82c9a82431edd95014121a70e8a80a090d5873540504861fba2c6282430f1d16314121acce3990a090d6672cc450486b8b8642282435a5c22114121c76e9306a810e6a62583540873930ac1aa0434e9c354950218d8e4b1ca810c747158e540869d386c8aa0430fdd9541502187ee8b06a610c3c74583530863db82c9298431e1c16494c2187ee8b04a610c3c74582530861f3a6c0a98430f5d36054c218beeca98a610c3e70990530861e382c8298438e9926014c21c72c9300a610e3b74980530871c3a4c0298430fdd16014c21878e8b00a610e3a64580530871cb22c0298439a9896014c21ce4c2b00a610e3b74580530871c3a2c0298439a1c96014c21ce0e2b00a610c7a70997430863cb84cba18431b9c865d0c218ece232e8610c7a70196430863cb80cb218431b9ca6550c218ece332a8610c7a70995430863cb84caa18431edc16550c218f0e0b2a8610d1c735514308636ba8c4a18438b9506250c219cae23128610c7575185430871b2a0c2a1843395c86150c21c74a83028610e3954181430863d380ca218431e5c06510c218daeb3108610ce571988430863abacc221843395ca6110c218bce7b288410c5d73d94420872b29cc3190430f9d3650c82187ae9b286410d4d7394832086a7baa64190431ddd5610c8218bce7b288210c5d73d94410872
  | 33 => 0x321cccc4b0ea790c3f7458353c861e3a2c1a9e430fdd16094f21878e8b04a790c3e74d8153c861eba6c0a9e4317dd95314f21c3ac8a98a790c3e7099053c861e382c829e43875926314f21c5ac9310a790e666258453c861fba2c029e430f1d16014f218f4e132a8790c797099543c863db82caa1e431e1c16550f21c5ca83128790e2d5418943c8727298c4a1e439354c6250f21c6ca9b0a8790e5653d8543c871d2a0c0a1e438e5506050f21cb4a63028790e595318143c8636bb0a999643535cc54ccb21caca6b0c6590e1d6494c32c870eb22a6196438b596640cb21c5acab206590d4d7315032c8637bb2a61964353dd9530cb21c9eeca986590f0e6454c32c8786b22a619643531c1530cb218deeab006590ce47158032c8716aa0c4a0e439354c624c72187ce931ca190c3d7498e50c863dbb2a0286439958a61d522187eecaa0a910e1d5458c548870f322c62a443951c56315221c9cc6b10a910e55639845488732b14c22a4439958a61d4e2187ee8b06a710c3c74583538861fba2c129c430f1d16094e2187ce9b02a710c3d74d81538862fbb2a629c43875915314e2187ce1320a710c3c70590538870eb24c629c438d5926114e21ccac5308a710c3f74580538861e3a2c029c431e9c26550e218f2e132a8710c7b70595438863c382caa1c438b9536250e21c9ca7b128710e3654185438871aaa0c2a1c439594c6150e21caaa630a8710e3a54181438871caa0c0a1c439694c6050e21cb2a63028710e3554185428872aa98c2994431d5d854cc621aaae62a66310e4e5358a318870eb24a618c4387591530c621c6acb3206310e356559031886aab98a818c431ddd9530c621aaeeca986310e577654c318878b322a618c43c5591530c621aa8e0a986310c77755803188672392c018c430f9d2639422187ae931ca110d7170c8650886b538642a84431edd95014221c3ec831aa890e4c63d89544872a31ec2aa24396d8f6055121cb0c7b02a890e3b64181544872db18c0aa2439618c6055121cd6c4302a890e7361181544871dba0c0aa2430fdd95415121a38e6aa0a890d3870550544863db82c62a2431e1c16315121ccac4b0ea690c3f74583534861e3a2c1a9a430fdd16094d21878e8b04a690c3e70d91534861f380c8a9a43871936354d21c58c9b12a690e3464d85534861f3a6c0a9a430f5d36054d21c76c9b02a690e3864d81534871d3a6c0a9a438e5d36054d21c76c8302a690e3864181534872db18c0a9a439ad886054d21ce6c2302a690e3b74181534871c3a0c0a9a432e1c16414d218beeca98a690d1c7454c53486ac382a629a430f9c26414d218f6e0b20a690c7870590534869c382c829a43871cd6414d21c5ee4b20a690e2c72590534871bb8ac829a438d1c56414d21c76e0b20a690c3c70590534871c382c829a4
  | 34 => 0xa8698e3b54181434c71c2a0c0a1a630fdd160d4931878e8b06a498c6f76548524c6963a2a4292635a1c1521493187ee8b00a498c3c74580524c63db82ca212631e1c16510931ccea4b0c6498e1c5458f414c71db82c9a82631edd95014131a70e8a80a098d6872540504c61fba2c4282630f1d16214131b4ae430ca818d2e7218e540c696b90c72a063479cc6295031a6ce2314a818d2e72186540c696b90c32a063479cf6095031a5ce5b04a818d2d72d82540c69b38ec12a0634d9c66255031a38e6b12a818d3471589540c69db82c4aa0634e1c16255031a5ce530aa818d2d72985540c69d384c2aa0634e5c26155031a6ce3302a818d1c73581540c697b92c0aa0634b1c96055031a68e2b02a818e3461181540c61fbb2a82a0638d5516190c31c5ca9b128618e2d54d89430c7172a0c4a18638b5506250c31c6ca9b0a8618e3554d85430c71d2a6c0a18638e5536050c31c74a83028618e3954181430c70eb2a8621863661c14310c31c6ca8b088618e9543584430c61fba2c1290630f1d1609483187ce9b02a418c3d74d81520c61ebb4a8290630fdd954148318deeca90a418e3a54980520c71caa4c0290638e9516014831c72a8b00a418e6952580520c66ab9cc3210638d55161908318f6e0b2a8418c7870595420c70eaa6c6a1063875506350831c6aa9b0a8418e3554185420c70f2a2c6210638d9516110831c6aa930e6418e3554587320c71b2a2c3190638d551618c83187aeb3206418c3f75590320c61ebb4a8190630fdd9540c831e1aa89906418e3565953410c673b92c7a08634d5d743d0431a6eeaa1e8218db07050f410c66bb9ac5a0863875516390431c3ca8b188218e3565990410c71ab2ca8208631ddd95410431c6cc8aa08218e3565550410c63bbaac62086335dd56310431caeeab188218e965458c410c74aaa2c620863351c163104318baed29c6218e2e5498a310c716aa4c5188638b951628c431c5aa8b146218ce572192310c63abb4a718863a9951628c431d4aa8b146218ec65358a310c70fb2ca89886387d95544c4319aced20a6218c7575991310c71bb2ca8988638dd95544c431b8ce5b1a6218cd47650d310c74a3228698863711c9434c431ba0e0a1a6218d95740c9310c69d386c9280634e9c0649403187ce9314a018c3d7498a500c61fba2c5280630f1d16294031a74e12a2a018d3870551500c7172a6c4a80638b5536254031c5ca8312a018e2d54189500c717b26c4a80638b1936254031c5ec8312a018e2c64189500c733388c4a8063995c4625403187aed2a0a018c3f76550500c7172a4c4280638b5526214031c5ca8b10a018e2d54588500c63dbb2a0280639a5895014031cccc4b0ea990c3f7655054c870eaa2c62a643879916315321c98e4b18a990e4d6398854c872b31ac22a643999896115
  | 35 => 0x952411063abb4a9208830f9c365504418dee4b1ca020c6c7258e501062fb9ac528083171cd6294041a74e1a0ca020c3c76506501069c38283280831edd9501404187eecaa0a998e2d5458854cc717322c42a6639398d6215331cacc6b08a998e666258454cc696b90a9a1e630f9d85450f31a5ae42a28798e3b5418143cc71c2a0c0a1e630fdd95410f3187ee8b04a598c3c7458252cc61f3a6c0a96630f5d36054b318deeca90a598e2d6454852cc66a38ac7a16631e9c36590b318f2e1b2c8598e665258642cc716b24a4196638b591520cb319cee4b1e8398db07050f41cc70eaa0c6a0e631d5db541073187ce9314a198c3d7498a50cc63dbb2a0286639998a61d5231ccac530ea918e6a62983548c734b14c1aa4639c98660d5231c76e9306a918e6a62583548c734b12c1aa4639c98560d5231a74e1aa4a918d3a70d91548c61fbb2a82a4639358e6215231caac7308a918e6562984548c636baec4a1c631b5d46250e31c6ca830a8718e3a54181438c71caa0c0a1c63661c14310e3187ee8b04a518c3c74582528c6b5386a9294635a5c35494a31a9ae6324a518c6f7650e528c6b3b8a8729463591c54394a31ad6e0a1ca518d687050e528c786a1887294634b9d06194a31a5ae830ca518d6a70186528c6b4b80c3294634b9d36094a31a5ae9b04a518d4d73d82528c697ba2c1294634b1d16094a31a9ee6b04a518d6471582528c6b3388c1294630f9d36054a3187ae9b02a518c6e76d51528c6b5386a8a94635a5c35454a318dcec2a2a518d6671991528c6a7b9ac8a94634bdd16354a31a58e8b1aa518d6b7058d528c6b4382c6a9463599c74354a31acae3a1aa518c6c7650d528c6b3b8a86a9463591c54354a31ad6e0a1aa518d687050d528c6973a4c2a94634b5d26154a31a5ce9b02a518d2d74d81528c697ba2c0a94634b1d16054a31a9ee6b02a518d6471581528c6b3388c0a94631bdd95214a31ccaa530e8518e6552587428c72631aa4a14639398e5210a31c9ac72908518e6552986328c733292c3194639954b614ca31c5cc8a906518e2d64548328c69d386a9a0c634e9c3545063187cec2a28318c3f76550418c72731ca420c639358e5210631c9acb2966318e4d6554b318c6b2b90a998c639959652cc631ccacaa966318e2e6494b508c716b24a5a84638b99152d4231c5ac8a96a118d3a74d42508c717b24a4a84638b1925254231c5ec8a92a118e2c64549508c71cb86c8a84631b5da52142318deeca90a118c7b76540508c717b20c4aa26393d8c6255131ccec5b0aa898e6462d85544c735b16c0aa2639a18b6055131ce6c3b02a898e3b64181544c72db18c0aa2639ad886055131cd0c4302a898e7361181544c71dba0c0aa2630fdd95415131a58e4aa0a898d3870550544c717aa0c4a1a638b1506250d31c68a9b0
  | 36 => 0xb88c9190651b5da538c832d4ca8b0c64196a554586320cb6329ac31906587d96544c832c3ecaaa264194ce76909320ca36bacc8990658bd96544c832c5ecaaa264195c671d8d320ca663b28699065a3191434c832b88e2a1a64195c87050d320ca1fba2c1288650f1d1609443287ce9b02a21943d74d81510ca1ebb4a8288650fdd954144328eeeca88a21963a54980510cb1caa4c0288658e9516014432c72a8b00a21967151580510ca9d386c9280654e9c0649403287ce930ca01943d74986500ca1fba2c3280650f1d16194032a74e12a2a01953870551500cb1b2a6c2a80658d5536154032c6ca830aa01963554185500cb1bb26c2a80658d1936154032c6ec830aa01963464185500cb33390c2a8065995c8615403287aed2a0a01943f76550500cb1b2a4c2280658d5526114032c6ca8b08a01963554584500ca3dbb2a0280659c58550140328dee4b04a7a0c6c7258253d07173a0c4a9e838b5d06254f41ccec5b0aa7a0e6462d8553d062fbb2a629e839354d6214f41c5eca31287a0e3765d8543d0753b10c2a1e83a91886150f41d60c3b0287a0e3b6518143d0755b10c0a1e83aa1886050f41d66c230287a0eb06118143d071dba8c0a1e838e94c6050f418bee6b04a5a0c5c7358252d070e31a86a96834e1c14354b418deeca90a5a0e4d6354852d06a6392a79968399949618cb41ccaa4b0c65a0d1d7319250d070f31a87286834d1c54394341a70e0a1ca1a0c7b7654050d062fbb2a629c839594c6150e418deeca90a520e6952580529063d384cb994831e5c265cca41ccaa530e6520d4d739483290716b22a4194831bdc963942418d8e4b1ca120d3a70d06509063dbb2a0284839a58950142418beeca98a6a0d4c7254c53506ac382a629a831bdc96014d418d8e4b00a6a0e4f531894350726298c4a1a839514f6150d41cb6a630286a0e5853181435068f3aec6a1a83479d85350d41c3cec29a86a0f0c53d894350786298c4a1a83c514f6150d41e28a630a86a0ea462185435078c29ec0a1a838714c6050d41e30a630286a0eab621814350754310c0a1a83acd846050d41d60c230286a0e3b75181435071c3a8c0a1a83a6d4c6050d41c70a630286a0e9853181435070c298c0a1a834e1c143d49418deeca90a4a0d4c7354852506b4382a42928317dcd60149418b8e6b00a4a0e5453586325063db82ca192831e1c1650c941c3ac9a9864a0e1d6414c3250716b26a4192838b590520c941b60e0a1e82a0c7b7654050506ac39aa0282835a1c950141418dee4b18a0a0c6c7258c505069d38686282834e1c143141418bee6b10a0a0c5c73588505069d3848228283539cb5394c418beeca98a620d4e73d4a5210637bb2a4290839594e618c841caaa730c6420c7b70595321063c382ca9908387991530c841c5cc8a906420c3d76
  | 37 => 0x595d73294632aaae6324a3194777650e518cab3b928728c65591c94394632ae6e0a1ca3195707050e518cb8aa188728c654d9d06294632a6ae8314a3195727018a518cab8b80c528c65559cc4294632aaae6214a31953674d82518ca9aba6c128c65555cf6094632a6ee8b04a31953474582518caabb9ac128c65591c96094632acce4304a31943e74d81518ca1eba6c0a8c651d9db5454632ae4e1aa2a31957170d51518ca3b3b0a8a8c65555d73254632acaeb992a31956672991518caabb9ac8a8c654ddd16354632a68e8b1aa3195737058d518cab8382c6a8c65599cb4354632acae5a1aa3194747650d518cab3b9286a8c65591c94354632ae6e0a1aa3195707050d518ca9b3a4c4a8c654d5d26254632a6ce9b02a31953574d81518ca9bba2c0a8c654d1d16054632aaee6b02a31956472581518cab3390c0a8c651ddd95114632c6cc928ea11963564947508cb1b322a3a84658d59151d4232a74e9a84a11963764945508cb1a324a2a84658dd915154232c68c8a8aa11963970d91508ca3abb4a2284651ddd951142328f6eca80a11966762d85544cb1bb20c2aa26595d8c6155132ccec430aa89966b62d81544cb39b0ec0aa2659c1876055132c76c8302a89965b63181544cb35b10c0aa2659cd846055132ce0c2302a89963b74181544ca1fbb2a82a2654d1c55415132a70e0aa0a89962c54d89434cb1baa0c2a1a658d1506150d32c76a8302869963854181434cb0e2a2c7a12650fdd160d4532878e8b06a29947776544514ca9a3a2a228a655c1c1511453287ee8b00a29943c74580514cb1db82c9a82651edd95014132a70e8a80a09957071540504ca1fba2c2282650f1d16114132b4ae2314a8195367118e540ca9ab88c72a0654d9c46295032a6ae2314a81951e73186540ca97390c32a065479cf6095032a5ce5b04a81953671d82540ca9ab8ec12a0654d9c66255032a6ae3312a81953a70989540ca9cb84c4aa0654b9ca6155032a38e6b0aa81952c72585540ca9db82c2aa0654e1c16155032a5ce5302a81951c73581540ca96392c0aa0654ddc56055032a68e2b02a81962c62181540ca1fbb2a82a0658b5516290c32c5ca9b12861962d54d89430cb1b2a6c2a18658d5536150c32c6ca830a861963554185430cb1d2a6c0a18658e5536050c32c74a8302861963954181430cb0eb2a8621865661c14310c32c5ca8b10861968d43588430cb16b2ca9a106539dc563d0832a5aeba1e841952f7550f420cad438287a106533dcd61d0832c3aa8b1c841961e5458c420cb16b2cc8210658b59654108328deecaa0841962e64550420cb16b2aa8210651bdd5631083299eeab18841964f7558c420cb472a2c621065a35516310832998e0b18841945d7694e320cb1b2a4c3190658d552618c832c6ca8b0c641963554586320ca72
  | 38 => 0x43a74e1a1ca021c3c7650e5010e9c38287280871ddc562940438e8e2b14a021c6f725865010e36392c3280871edd950140438eee2b04a7a14747158253d0b33b16c2a9e8599d886154f42c6ce830aa7a16357418553d0a2fbb2a629e859554d6114f42c5ecbb1287a16a462d8543d0b1bb28c2a1e85a91886150f42d50c5b0287a163b6518143d0b55b10c0a1e85aa1886050f42d66c230287a16b06118143d0b1dba8c0a1e858e94c6050f428bee6b04a3a145c7358251d0b0e31a86a8e854e1c143547428eeeca88a3a16556354451d0a8eb98c9286858798d4394342a58e4a1ca1a15387050e50d0a3dbb2a02868517dd95314e42c9ca63128721477765445190b38a8ac028c851ddc563942428e8e2b1ca12153a70d0a5090a3dbb2a0284859c58550142428beeca98a6a15547154c5350aac382a629a851ddc56014d428e8e2b00a6a164c53d894350b2ba98c2a1a859514c6150d42cb6a630286a1658531814350a8f3aec6a1a85479d85350d42c3cec29a86a170c53d894350b86298c4a1a85c514f6150d42e28a630a86a16a4621854350b8c29ec0a1a858714c6050d42e30a630286a16ab621814350b54310c0a1a85acd846050d42d60c230286a163b751814350b1c3a8c0a1a85a6d4c6050d42c70a630286a1698531814350b0c298c0a1a856a1c143d0942a70e0a1ea2a1477765445150aaa39aa228a855c1c151145428bee6b00a2a145c735805150a3dbb2a028285561cd5014142ae0e2a80a0a14777158c5050a3a38ac6282854e9c34314142a70e0a18a0a153a709085050a2fb9ac228285171cd6114142aace3a9ca62145f7654c5310a1ebb4a9210851b5da549084287ce1b2a842155673d465110a3bbb2a2288851ddc563940428e8e2b1ca02153a70d0a5010a1e3b285280854e1c142940428bee6b0ca02145c735865010a3dbb2a0280850fdd95415332c6aa8b08a99964e6358854ccb32b14c22a6658d9916115332cacc6b08a9995357115343cca1f3b0a8a1e654d5c45450f32c76a830287996385418143cca1fbb2a821e6539dc563d0b32b50e0a1e859961d5418d42cca36bb6a8216650fdd16094732878e8b04a39943e74d8151cca1eba6c0a8e651ddd95114732c6ac8a88a39943e7498650cca1eba4c3286651edd95014332cccc530ea91966662587548cb35314c1aa4659c98660d5232ce2c3306a91963b74983548cb35312c1aa4659c98560d5232ce2c2b06a91953a70d52548ca9d386c8aa4650fdd95415232c9ac7310a91965563984548cb33312c22a4658b9506250e328eaebb0a871947575185438cb1d2a0c0a1c658e5506050e32b30e0a18871953a70d53428ca9d386a8a14650f9d85450a3287eecaa0851956571153328ca1fba2c128c650f1d16094632ae4e1aa4a31957170d52518caaabae6528c65
  | 39 => 0xa0a1c6d729875050f94b26a5a82875c9c652d4143ae2e3296a0a1d737154b5050eb838aa5a8287ca5d052d4143e52c8296a0a1f6352d475050fb0296a3a8287cc59351d4143ad4e528ea0a1d69729475050eb5b92a3a82875a1c951d4143ec6a428ea0a1f60521475050f98ba0a3a8287cc59051d4143ad4e5b1ea0a1d6972d8f5050eb938ec7a82875c5c763d4143a72e9b16a0a1d5973d8b5050eb938ec5a82875c5c762d4143ae4e3316a0a1d717198b5050e9cba0c5a82874e5d361d4143ab2e7b0ea0a1d6a72d875050eb4b96c3a82875a9ca61d4143ad2e530ea0a1d39741875050f33a94c3282879914a6194143ccea4b0ca0a1e64525865050f33316a3282879958b5194143cccc428ca0a1e65621465050f35316a1282879a58b5094143ce4c3a84a0a1e7161d425050e373b6a4a82871b9d85254143ccea5b0aa0a1e6452d855050f33a90c2a82879914861541438eceda8aa0a1e6762d455050f32316a2a82871d9d85154143ccec428aa0a1e64621455050e3dbb2a0282875adc95014143ad0e4a80a0a1d73715405050eb838aa0282874e9c243141438eee2b10a0a1c74715885050e37b92c2282871b1c96114143cd4cba90a0a1f2b74d485050f95b26a428287ca90f52141438f2ed290a0a1d72719485050eb8b8ca4282871edd95214143ae6e2a90a0a1d70715485050f35328a428287ca5d05214143e56c8290a0a1f4b431485050f95218a4282879c9975114143ec6a5a88a0a1f6052d445050f99ba6a228287ccd935114143e6487a88a0a1c79769445050eb5394a2282875a5ca51141438f6eca88a0a1d6b725445050eb4392a2282879c9945114143ec6a4288a0a1f60521445050f98ba0a228287ccd905114143ea686288a0a1f32431445050f8d39ec8282874e5cb6414143a72e3b20a0a1d397290c5050e9cb8c86282875adc94314143ad0e4a18a0a1d737150c5050eb838a86282874e5d26214143a76e8b10a0a1d5b735885050eb9b8ac4282875c1c56214143a72e8310a0a1d59731885050eb9388c4282875c5c46214143a72e9308a0a1d3b745845050eadb9ac2282875adc96114143ad0e4b08a0a1d39741845050eacb98c2282875a9c86114143ad2e4308a0a1c3d769524310e2ebb4a9218870f9c36550c43c5ecbb128621e2f651894310f1bb2ec2a18878dd946150c43d48c430a8621e3b65d814310f1db28c0a1887aad886050c43d50c43028621eb3611814310f58308c0a18878edd46050c43c9ecbb128621e4f651894310f2bb2ec2a188795d946150c43d88c430a8621e5b65d814310f2db28c0a1887a6d906050c43d90c43028621ed0611814310eb338ea5290874e1c143548438ece2302a421c75711815210e37bb2a429087599cb5194443a70e0a1aa221c6e721815110e36b90c0a88871ddd951144
  | 40 => 0x1000c0010002006000400680000000002000800000080000000000001000a002800a004000600100020010006001000000180000000000000800400000180018008000800000000060000004001000000080000018004000800600280000008002000001200100040008002001800200180120000000000000000000020010000000000c0018020002000000200000048000002000c0060000001001e0000000003000c00080060040004001000200100080000004000800000000120008000000800000180040000000000800a000800400080020008000001800e003000000000040008004001800e00100000078000000c777158252d0e3a38ac1296871bdd95214b43ccaa4b08a5a1c6f7258251d0e36392c128e871ddd95114743ccac4a88a3a1d2d7219250d0e9ab88c9286871d9c462543438eae2312a1a1c6e7218550d0e36b90c2a86871edd950143438deeca90a521c77765445190e9d38687284871edd950142438ece3306a4a1c75719835250f33b0cc3a92874b5d061d4943a9ae630ea4a1d2d74d835250ea6b9ec1a9287599c760d4943acae3b06a4a1d66719835250eb2b8cc1a92874bdd160d4943ccea530ca4a1e67525865250f35a94c1292879ad4960949438deeca90a4a1d67715485250eb238aa4292875adc15214943ad0e0a90a4a1c77715805250e3a38ac029287599c76314943acae3b18a4a1d2d74d845250ea6b9ec2292874b5d06114943ccac2308a4a1d2d74d805250e97ba2c02928753dcd6014943acee2b00a4a1d64715805250e96ba0c029287535cc6014943acce2300a4a1d65711805250e37394c1a8a871b5ca60d4543ae4e1296a2a1d717094b5150eb9b82a5a8a875c1c152d4543e4ae8296a2a1e676298b5150e9aba0c5a8a87555cc62d4543a6ae9b06a2a1d5573d835150eb3396c1a8a87595cb60d4543acce5306a2a1d65729835150e9bba2c1a8a879998b5194543ccac5a8ca2a1e6b529825150f34294c128a879cd466094543cd6a4b04a2a1e68525825150f39a8ac128a871b9db52545438dcec292a2a1e6b52d815150f34296c0a8a879ad486054543cd0a4302a2a1c77765445150eb3b92a228a87591c95114543ae6e0a88a2a1d70705445150e37b92c028a871b1c96014543ccccba90a2a1f2564d485150e3abb4a428a875c9c25214543ae2e1290a2a1c77765485150eb9b82a428a875c1c15214543cccca290a2a1f25741485150f92b20a428a87d1d0c5214543e4c86290a2a1d6672d8c5150eb2b96c628a8759dc94314543ac8e4a18a2a1d3574d885150eaab9ec428a874d5d06214543ccac4310a2a1d3574d805150e9bba2c028a8755dcd6014543acee4b00a2a1d64725805150e9aba0c028a87555cc6014543acce4300a2a1d65721805150e3b38cc5a82871d5c662d41438dce530e
  | 41 => 0xc0000000002800a0030008002000c0018000000800400000000000002004804400000000030010005800000180040008002000000000000000020006000000a000000200080020010042005000200300000018006001800000080020010004000000c001000000100020008008003001800000000000000002000000000020000024001000000200080020004007800400080000000006000001c001800c0018008000000000180020000000000000400000140010006000800a000000000100000000002002002400100060000000003001200000040028006001000800a8000002800a0008000003800000000000040010002000e00080040000010001000000300000020008001800c00100000038000000800000080060088000008001e0000002006802400180000000010003000600080000048006002000000000000010000001001c000000200180000008002002000600100020020006000800c002000000100080000006003800200000060018000005800000000080008000000000200000000000002002000800000020010002003000000080060008000000000c001000200100020028004000000c0020006000000000380080000000004800800e0006004001600080160020002000000a000800a00000020000002004000800180080018002001800800000000000002000000200780000080002000000600c800200380080028000000800600180040000016007800400700000030008002800e001800600180020000000000000800000000048000003801200080020028000005000a001800a0010000001000e005800000180000000002000800200000020000002002800a000000000080080000000005800000200060000000000000000f00040060010000800000900000000026004000a00080120018004003000c0040002002800200a80060000000000000c000000800400040008004000000200000020008002000800000000000038002000000c000000400400000030000000801e000800800080020000006001000000000000020000000000400000060008000000001e0000000000800000000080000006005004600000060008006001000a0070000000000000180000028008000800c001000c001800400300000000000000801c0000002000000000100000008004000800200e8004000001000000040008002008800200300000000002003000c0008000002800400100000010002000000400500020040000005000000000000000000001000400480160000002000800000000000010000000801a000800a00000020030000000800000180040008010002800200580000020000000000000080060020016009000200280160030000004800200000020000002000000400100040000000000800e005000000
  | 42 => 0xc000000200280020050000008001a0000002000800800000000058004003800000000000040000000000600180000020000000000000300020138000002800000000040018002002000400000020000004001800600200200018002001800e00780160000000000800200100040038010000000000000020028000001800400080000008000004002800080060040000003000c00000040000000002000400000080068014003800000180080018000001000000580020078042000000200280040000000002800000000040000006000800000400060098032000000200200020000000000000200000040008000002000000200060050000002800e0010000001000200100020008000003000600000080018008000800800280040010004001800600180020000000000800000100000028002002800200080100008022000800000180000000006000000000000040000000003000a00000060000006001000000100020018006001000000200020000000000800e004800000480060068002003000600d80000018006000802c0028000000000000000040008004000000000000040010000001001000080000000006000000200280000030002000800000200040000000001000800480000028002001000000d0004001800000000020030000000800200200120000000000000000300000000002002800000300040000000001000000100060000010001000e00100040008008000000000180000018000003800400a8004000002200000040000006000800400600060000000003800000580060020000000000800080080000000000000000080020018000000800200680040008008000800000280020040006000003400000020000000006000000380080010002000000000180000008002001800800000000000008001000600000040000000000800c00280040008000000000a000000a0000002003000000a0002000801000000060038002000800600b800200500000000000005001e00000060038000000001000480000048008000800000c80040000006000000000380180010006000000e00080020010006002001c0068008000800000000060018012000000000180020000012001000000080000028002001800e004800600100140000010001000c000000600100020010000000000000000040010008000800a00080000008004000800a000800400280040008000000000200100020000000001000000f000400100000060010001800600180060010012000000a00000020008004000000000300000020000007000200300000000000000000a0008000001000200000340008006001001c002800800080020000006000000200280000018002000000000000000008002000800000380000000006000000600080
  | 43 => 0x140000002000000a000001c0068000000000000000120010002000000000500000010002000000a00700000000000000000200280140028004000000200300020008000004000a00280080008002000000200100020028002000000400100000018004001000000000040000006001800c003000000000020020002000000000580000020008002002000080000000004002000c002001c000000000500000000000003800a0008000000000000300060030002007000e00000060020004000000000080080010002003000000180040000000001800000380000010000002001600000020018002000000000200020018004000801000180080000002000800e00000180018002000000600180020010002000801000080000028002000800000100000010002000800e0010004001000400000060000006000000400580000000002001000000000020010002000000a00000100030002001800c0008012000800c000000200380000018002002000a0018006001800000000000008002000800200000100058010000000800300000000004000800e0008022001000a000000200000000008002000000200500020000006000000e00080000040004002000000000000038004000001200180000018000000000e00000040048054001800a0010000002000000000060018004000000c0000000000800000200040010002004000a000801000000040028006000000a0008004000000a00080020000000000001200000040000002001000000000120018000000801600000000008004001800000200040000018004000400080100000000000001200000000038000000002200380160000006000800000000020010008000000000100060000002001000a002002200900100000004002800a000800400180000010006007800c000801a0088006002000000300000020012000000c000001a00000040000008000000c00180140048012000000400200000000006002000a0008000000000000000040028004001800a005800200080020008010001000000080200008006003000a0000000001000000000000000006000800200000020018004003800c001000600000000048000000800200000180000046002000a0020002001000400580020008006000000e00100140000002002001c003000000200060108000001000e00000000000004000800e0018000000000000200080008022000001a00080020008012000000000080000008016000000e00700120008000002800400200060008002000000000180060000016001000000580000048008001803a000800000080000010000003000e000800000a000000000000020000002800c001000e001000001280080000002000000a00200000000018000800c0010000001000000000060
  | 44 => 0xd6712647e01684000190000023198b2232c00000017bc281400000000002a40caf17200000000000000000048c90ef513d5324abda7c067c06700014f105a4875412536a5b205d60440b8d000000000007a7000014900004374ecc80b69b53a41a118060c3c34b3508e6d53e14d3132830b1a0d5d240695b256a8af71e2d4b9615855e462848401e400023ac0001f74d5400000000000000000000043ac75b3800894000000037c0e881e3ccd2000000000005963974bac43940005e00848150d5f100003ac448cf0400e4293068800000000003ef8000000000009d073400000000000000146817700007d90000b793b6ca0118558db600d1d50000000000170b127cd0b00000004da505106a00002abc000145800008a966d6429259511cd910db400033fd7e918d035e55100002da4163303cec615d55e137b0f861e58a2d3d6954d20c83dd57603681cb400060f97b6000000000006084604cb0000191b565d40c0000a754dec0001958000000800280040020008000000c0010008001801400080000008004000000000200020000006001000000100080010008002000e0010002000000600580000000000000801c00000000000018007800000000060040000000800000080000008002001000000180020020000000800000100000000008000800000a8004000000c0040004000000200000040008006002000000380080000000003000400000020000006000001c00180020008000000800c00a000200000020010000000800200000000010004000000000080000000002000800000000020000000000000400000180008000000001c0000018001000400300000048004000800e0010014001800000100060028000002800000000000068004001800200000000000000000000000000000020002000800600000020000004005800600000120020010000800000200000000004003800e012801400380160008016000004e000800000100000020002004001600000020060002000000000080000028006001000000000140000000009801600000060010002000000000100060018000000800800080060020004003000c002800800100000008004001000000000040000000005800200000020000000000002a00280000008002003000000000040000000003001a002000200000000008000004000c000802e00000000000008002800000000020000000002800600100000018000000000200000020010008006000400380040000008001000a0020000000800200380000000004000000000380020008000001801c001800400000120000000000000000080060000004002800c000800e0030000001000e00200040000006001800a000000c0010014000000800180020000000000000a00200020000000001000200000040000
  | 45 => 0x4320000c310000b9a000036b00003772d040000000000000000033dd0623e307e8527000015f556b00000000000000000032c21717de0000143000000000000003e3800000003ed000069800012ba000000052188ba2cd00000000000000172d000000000009e200000000000e0c0000d0e00000002fad5e900000a9359800058d8a4f42a000000000003fe8000307800000000002c7d01c0000c3e2cfc0000000000362c000244800054a512000000003f78000138ca740001209000017b000000000000000000e2d40c4000294124253715a400002ec690c0003f1c0002e7800015e89ec47581c45c50cb9136934e00016ba00019493c0800043880004038ccd4de400031e49d461340000000302000000000008d95bacc28547845e09b819561cd2960000000181000032d4a9d1a6522d000000019c000800005a44f5800063895280a180000000000000142c026c97c00003c51e2827138d55230001675000000050194200000dd7271c8b95fc00000000000000000017a1a2c5aa80000000000237400044f169f29e1330000000000000004775a5800000004e580000000000323c0000000d140dc410d5890b4c00009d3000000024880002fa400000000002cc4000176998e000032600012d300000000df800062a5979064024f0000fb13464f7b068139e59cc7bc5a4039047cc4ff0000a3f000123a000034f39dc0005ff00002adc09415c57875028d6b4f14bfd0000e0e50591414a94000667906e38c588922a853f00004760cf01980d485390000a8b0001253000043a16e000023f0612071400000006ed0518191238053631f400000013db0000f6a69c4566000032a49f0a3a000092d36dc00000000005e84000366890c01593320994cb74db0000531c00000016523060af60cbc0000000000494039344e000040d00001d200002ff800000001b60d6000000005ba4e054da03515f224b0efa00010ed00002354c7c000000109200006af2834000504477300000006810000000161600000003d50000531400000000001358f3b00000005600397000000000010e0000000000008b35228f2000003f82478f6f03c1757414d92e563800000015c600013274ff536d00012ac000148c1504c4735a102807ec00000bd0d4192c0002b980000fe80005ba467c0000b2010b902a2cd8000149474746dc000000000000000000000000000086200a80005f54000000000000000002e64000000000019fc000000000000ec26100007663969794000163400000720b540000000b4a4cfd19e25c9133000117f0000ce1000000024a0000000015b0000b8909a00000000000000143618e124b1d4c000000000038ac00039b800069bd8e50000e6500f8000000041300019ea37c846637d54544f387c1661d8770c780002f650fa00000000000
  | 46 => 0x13b54024a023f3455c0ce00000ca000000000003868d62456889800000002d0c000089066b07a151061d90bb0b780004ffc0004f080580f496b3000005b0000000000140800000000000c680de4000563571c4a8c6cc238d9e151580001864cf4222c6be356929f0080c6b00006174fa000023b80000000000000000000000000001612000066a1409866000000050a0000000000000000001b440000dbca770000000518d15600000c51da80002299038000000000007a5375000059c582301795bc64f8a2c48300000cc0090000084328218a00becfeb0000c8b000000000000003308000109400000000000000000000000000015b100000002f280000000e3d183800000000000001747259000066557605664d76391132004600003fc5a05000131300004c33ddc0001a082bf1ec04e6251400052652630b593ee32a4a700fe56cf39410bc26956ac000000069e08de5524b6c00000004ac400029c514d13113725e446550000f871ba8030654c1831e0579f0bf000064a8dbe00000f248e0000000039a3230ca40000000000000000004100000000677400000006e22c347e500017a700006f54d6c00000000000000000000000015600003d0c0006a0cfb500000005ded7bf000000000015f500003c20000000000079150fd24565f800052a98a230447622be0e01670c26956a56f02ab174c2744cba3834000000000028cc00000009e5000000020f473850e80c8491d7fd00000000764c385f4cc943660000000000065dd60b000127a000064f34f4000000000000010c200014814a358b100009210001a7327f50ba18012be0000f7200000000001702000000061f0000541c00023d03123ff836300002790e113f600005f6390400000014a419b00000968000688c9b434b56572b240000000000000000054e40001fe4000503c73b0c402d31b6d707663030d2fe0f1c176400010c000000006915b3928e0000d250000d934cd053d2a0473f1370dc62bc400039640000001035137d49429bc0005e9400029e8fd1000000000000000000000000000011ac0004298000000000055fd41c62b12210000b354f652bc61fc79f532c49b5974bc05fe846c00010b83dc525f312c0005a3503a0000fb300019ff00000001dd096a19b8893673d9df5530eab3ca0e050298c6f6044b554150d110a9da602da169e04003af2dac2966868f45000000008b4000483d3900490b7a0000ec560340002d187440000fdc0000000000000000000005f81415655829e651c8cc00000002fd40ee38c8000000019c334c000000000012158ee000000027c000000001dd5758000000109f0000a4e000000035bc000000000060dc0000d7c0001de8ab139a4000000000012310022b390da0b1c0004b040004c48000368c3f53b3cc3d0000000000000055e4000
  | 47 => 0xd0000e0900000003f1071c00000002c611b34d31a476a10b324588000000024e000000000000000000000000000000000003d3091d5d508350000c36034401a00017ad29cce5c4f8c0000000aff15b000000500000001115502d9c1653d1f65e180006330b6d4a610f80200a14072800026a886a000000033e12ff684c000000000059b000000019e923ccffd0000b230000000035cf8f461800014881a162fc7e10000000590cf610000fd202e800047f00000000d4c0c3000048ac00000000000000be000000003f30000000100b1378000540800059a80005d487260000aca0000efe2c286ca3c9c7094de068b33a08f901046f82d618f64becac05e9000054883005cdc30500003b1000127e61643b3454852e27240ad00000000000000000146e000000069895140000f936a6928f5a2d96813c0000000107900016dc0000000607800000000000000f3800000000000000000000013d085569a13705a147e70000000021800000000000000000085c00000013e7000028c0000000469544524d00003f90cf212386e636b132131a40000ea52e30ee882033c0117261800002ac00011545d53a295f931b00000000000000000019a4ca644b867e00012e84dd0ec107dcc2f00000002cdc00069d4a634a9800041ed1951d38f94446525114ac099337c6b668a40c0482168045ac00000000002fcc0005034b78576530d5bc989548a4000000000062399500001098088c1055bed02b3408f3600008591d3da3600011d14ea19785ed08050fd800031c03de285972e12d932f01d15a34c380002c0cfc1000023e0db0a1934d4fe8255110d2ca81de12b4000051400000007b6000000066bd9f00000d323cf4000113000025cd5ac447da273ccd62212b800065d8df3216000035cd9cd0a2804f00000002350000000117d5520e6600000002ed80003d2000000000004a2439600002c924c15ff5ad89f72b6800000940000000e2f47a40003054fb200014b61d8413106196f811fc00000015fb00000000001111000064451a065e6938bd74a503690000000685d475000104c1b70e57444d46c4e2c0000000000000193122c157b50d04a33cc446320896700000d43187c00000019de000026c393d9d54fd400000000006608a680000e290c50f442cb09564f284d460699011e34c4d00000000000fc6580c0001474000459087d525546500010a100000004074c0141f40005cd495b52582a5000000b106c000015c14d1f5cc7b35e84b3156400008453c1107169366848ff3ba090e1fe15ee00000002d1c000000070b000193956792810000b0f644cb0b00000004ff1a310000000000000000000001d3583b6994000000156d51e0b67000021642302a2429000045d00001d14000000131900003c834cca9b00018605200cad09100005f74a5f000
  | 48 => 0x8c0000c38a4b11c59576448bc2079400000011f72f2c000000145018c8000541000000000000000000468c0002a94000000000000000000000cac000050400f52933be4ff8000151d16a00000000000000000000015b300016790000000000000000000000000000000000000017811d0c7de00000000000d561bbc00026f112c3ae400001bc000000055300000000000ae8180c00010b4815000000000000006a081d056fcf153f84fb94ae444d0000000210000042d191a5d08000000185e0fdc00036d0ee9000005020f8000000000000000000000000000167b69e49af33114dd58312b265486a1365cbed00002cd0000f9d37f8a2603b1419350035c00005e400006cb00011e65b0c1333f8134600015ed13e400021a4d5c0bd538e0768000219160503dc0000000000000c0000000000559943300015890000f1000000002688984000000000002b44e440002c5c08d1e3916e00017b0212533602bd749277d6ef124096b6a2c0b11ae031803994ee4ad15db627424a3f8987467d40000000bab5b541b746fcc303990e46380800030640002038c3716743ca0e7100c17845fe3424b655d2c000637d954164cc530000000017ce365f907fb614921134110081ed0fbb24d56e01f440000000ba3000000000012a148380000000000074881026e40000b91726000063100015870000fea0000f8000000000000c8d0000ac13aece8f40405b10424d1860480000c9d854482d4580000bf1000000005b01ce0000c2b16399eb0f340004cdd635000195c63c093f17888266610e3811e4ac25cf400001f00002c6c0002d742003a457fe000044500016a6000169b000000006fc907616006816f4fa50000f2135a800029640000185a5e54d98d56621121523d89e19e4ee312e46284d2064a4db9178562067657310753fd478600015c7551800000014ea00004ba00002450000ced59dc00000000000000ef8000000050b57f300000001c100000000cde15fc0002e413b6590138a4bf00000dc000000000004f21128173400046080000000000000002b00003253ae000014300000000000000000000013da1d0000069181e71c840cf00009196728d6e36b80002f759d1000000000007e32df400000012ec0000f39109d7673708e0b05307ae000194622f5a1b197c5ad00000000000c000000a3e000185a2a200000001460000107c000092327f935a2b74000000078927cd35465603030000084000000037dc31513b46bb47c8f6600002d821f964d62e89dd1ce547e000033400004004638000000000000010170001a4020342d2033129d20084830000000000084b00000000788000000000052bd9b500000003cc97711dbd942000001324f9277000000000018ec000000033e8a950000000000153e000179826ad9592f34dd2000094c0000b1
  | 49 => 0xc400000000a60fc511dd4e25dac98d0001649000170c46b8044695439e04b4b4051698a4000000067e16140018b973db95e8000178251c0ddd00005df000109401f40004f4800000000000194000618c000000189200000000000000000000000000000000ac3000000005cce4c00016454f980006a1d4a75b64bef0000000000189b5d14ce944ad72b55bcc5f37116f666987673a4c00046e959d000000057cc5f446800000000000160020608bc438000189759795700000bba3f2c1ba000000000015da00000000000e520000000328508300009652830a0430ec35500009a30000ed2000199b216c0000000000000000000000001f3447c410803111f5241527815d2e547054f3416821b861a00007974aa92f605857c20000000374c000000040a0000a1a00019fa00001d4000000057bc7fe3c74a6a2d35482000042669ed6b2539986267b07d35a3da6439ed429000000000011c02b5c94a5608d90152cb0200010050000000000000001dc000000000065c57a2000009f0000000000000000003d70000000383c000564cf0c0b5c0000000f750000000000000000000001a38cc31d180000dcc00068b892b00000000000000000000046413f90c64fae438442a2a1c03300000005ef80002fed8af313c0001d940005b480000efd27425bd9001c4894924544b0104550914f02d40be83a839d91ce322822256f8000000000020b07985d7c0000000000000056436c45dd000027c0199a020001116400c28869f93733e7c00020758c864f50b100000000664000000016f000000000009cd00000004688000000015800000000bb80003f8d85b54d44c5000014e11a80000000e5633880e4347d3870000000000150e00010c80204000000000000000001ec400036ed79a03bc2326a7574d00000000000b7154000002581446000062f49985772f480890000000194800000000000000000000000044d80006010fda000061404294e90001012000000000014c40000b8b013800021dc0000000000463400064cc000000000000006dd41d97b8040400000007e655c80000000dea124925a64d4d9500000000c259ac17140000258000000000031893ec00007ee00000b500000004900d0600000000000000116817812980005ac4be50000cc030284cf324d8f500000005f383bc000000065a4b0600011df00016ad4791350000000013400000c04000633c52c129c80400000003194000000000000018240f951b80000000000043e00002c422947da363c00000000002c1d96f000000000011d00000f9127e5421581827500013d80000bcf4474d410000000000000000008d31c1d0fd13ccde80a3996056601b04d2820449f467536a00000000f9765540000000000000000000010182981963000000000008c832c966748f800043286d318
  | 50 => 0x165a0000000000000000000004238000000000063580003adc0006738000000000017a80000001623000045f3f288a958aca240e200000ed0f42510da19645cc610000000659506400000000000a252df060509f80003030000000000000013aa27f17154648bc11fb400038f1a492e754bd4a1499d46f4104455caf2000000027153b7000091100000002d6800065d0000545819d00000004b7000013a83d12dd46a40fc99b053e462b56288394288000000000000000003f0c000086812831300000ccd9d707a99f600010390000000262c18800000000598f6d06000003338a86145c1a900000000bc4000000000000016a9000130100005840000803000000034c400064b4885228111b1cdda702c841a50000b3b23480004d58dd10000000000042232f00000001a4f0000ec3000184a4895a1d2720a1e1678ee1000000000000000001898647800000000002ca00d03e7800000019324268c242e6015753598b500006c1000160e0001993435859400000002b6c00014259fb0000000309487b000000003e1a9743490f506294ba09ac7f600014410000fa10871105000000039389bd08a471a3b89764290071d6384b422bacbd6606537e069852a00013cc5d691305a182c538a80000a35a201390f8b28d89bf2ae00002e113e94f890fc625106f30fc000225d93a3ab86975354d0005f0dbd080c5b944f84f66930f263bdc3a65909629000140352a400000015d7535c0002a24b39299400041840005b780005c7c00035148fa000000017ccf7d093400037fcb630000548149086111d53a311258c319d11b006c93f354c0a4165f54b21e645a50a453dc21cc89a4f550801d41188000057c00003371fe90b567183403980a9f524153d4b847eb1d08000473400053f950100015150000000000000000014a3685400000000004b98dfa000000061152952e18b5634c19e03a2c75a38e52434b6d34d3a0cbf60000d884e30ec2370400000007154c70000141cf46229c0001cb926d40ec00011cc46e000000000000000000d0832880005025a5a1bec2180b2c00000011aa2bb400e00001152d718880e456cb000018226680000000c7804c80006190000087c0002b500004f759e561f54402bcd3a200011b433d46aa00006f900000004a103f4572000000013862da8def0000e971c617cc00005ff00014de1b1d6884168fe558f526400015eb43c02b0000151c360800000104af000104434a0993441c0005ffc0000c5800020952d944ed3620000225622925506249c22f4453004d98ca60e4f9013b18cb3fa4f5e08347ea495c0000171013390c5d45ea48d65d0504121049d70000d01162188742400001fbc643237c16d36a5774094039d2950fba3df8b7b31cd43744040005ad400031419704c286f1082817544d1a571c3ccbe0c859
  | 51 => 0x3aa5af036a4dfd5dd46c808b000000000014552f6c75765a94840001132046942e000000000010560000b9f2e851536a29a540000000438c00023bc000249800040bd6ed266c00000000000000000000000000009665c913924624cab3c48c5816dd1f12860c2d467d9181dacf08000037c46982db466093240f400011618e3341c8b52a8c0000001315507d0654fa83593a1116f1128b6e3e1559a0060106000181f674088e68e8d44000034666ac00008f400038400004fd0ed400000000001908416400000000005834d3f000000065cc00000008d70e6c00042042a300007df4b5058b000053b584c000000107700000000000ecd000066700004821bb80000000a1d5eec000000096d44bc2e713ec0004d795601a05773325c5260445066235400068f01d55bfd8b4597da1e4364d465cb01f900015b650c806208fd5125fbc000000000059800023d3c18f2664755418170e00018293560e080000000000080c00000000000f0333bda96078cb0e00004931bac0003b658051158000422da5c3e692ed48c133c000000036e400000000000000ad01251a331e48678666000050e42af000000000007e263988782538d55082080155380523bd823b000081834e07fc0000ae93ac10c1000000034bd15e12280002a81a801e8000028c80002a845af000000000000000904000000067d00002c000019280000d0316a807f000000000010b34b1c0000000000000000023240000001489594cca006d434e000107000001d30000cc84eed9f40f9d594166495300000001f18d750000000000000063e4000405000064fd70d68dcb5712b128648d800069200000000000057c00000000000000000449000000014e500012a9369c887449c61b63e16d1515cac668008fe5eb88e82be909d49fd2c4000000035ec0000000000055400009d863b000082360cd8cd2c4800000009370000a7b3768000440c0f563c54f319dc0001874eef27b40fe63a00000000f670000c4e000000000000005f20ea00000000000000044380003bc038b0000e035e5c000000107e0000d4d5d700002dbd1041eacec742a592c668d785000000026a40000000dad4e693d46a64e610000000501400000008da000021421980a5000000000018fe11a114951a80003de800000003a33e21736000000000007f100016071b14d3c3070b2d5e2cb9122712701354e4a5a559fc256897910ad40048817aa12dc9f126d40382aecdd82b4926c0000e2800000000000c16155537d2d7c69602f071703fd2ca336c00000000001dec0005e341ad000000000000000000000311400029200000000000246800041143bd0001a440f6cc432d103172ac00000b695fe389506d624463500016f500010374154a842ea0b4b4f843be66c8fad00010fe00000004df0000000000048584dd0
  | 52 => 0x691457060f0f8a31040005dc000000011673fc0fbf000000060740001a7caf500009d90e1c000000108f00016a367b99b10000da0408d4c119805862fa0837260594a5a955bb0a7000014840001e9146700000a70000c721c40f5d00000004989299223c00005280003b7d8ea3a580000000000354da610000f650000f2d25a178300000000000a314d4938d17c400011898b90000350484d98d00008ae0000dfc00017393f38000000191c3abd55a24cc00002918c52385343000160f2ee087945e400040944032be588c58f8c634728cc71aa012212805a630e42ab09e087a246ca5b32c4c212ac806e14a155357814cf4d087564fdcf17559c25935f800048b05b3000000000012cb59644a156411970000e8c486400000007761a9c0000000000000000060a80000000cf6000192251dd07836a80003d34000000062900003562d1532217005b011740003f5c00013650f60958902419d4104be5a560000d52633869231280001624e1c02b1183387d17c215d69c00489a64ad4c8954b01df13e02f45e249485f1541a0001050392d08d000000021a0d5d1ccd2005d789ca45c4042299054613957a31bd163840f8e990edc91362b89d2000074b00000000000000044934153ecdb05da48a20f658c2460043300000000000000000127b08f19c038645e7318095d00000005f5c60d00000000324ed100011630001a0800001bc684819a38901792c599612e3c85100000000000000000032e2a390820000a9e2e0d0fb0001a350944000452c83857d906900005a9435c308000000063c89ff64ac0000000000000000000000000000000000037a0000000000176c09f400052e00005d44000000164e0000bbd0000000000000059292100000000049961f3a057cd281888a125d13a000058508dc00047c105800010e7000180b00000005fec0003124e8e000150a0154f0b0000000000049806d10c3157590d5b943ec660d11010bc32029e57b90000b3e0000fd5324945953bcd4810548821ab878c395456247fc0000a057a800000003e60d74000000000008ed2e9971317bcde30c4454e00000004004cfb0000000000000000000001a702bc0000833000188b227449a00000004d800000000955000000046a1a1f000000007f05cb0000a27000000000006851ce84be0000d3b30b950842b129247e890a2a085322e882496a0510a3f0000035955a0055112d243c3eb0001217000000006917343bd4123416cb0c64a4000000000067bc00023b000000000000000000000011f34d8c8e00000006174000000156400000002b7cf4a14f8fc93cd0000000191920ec0000000a6b0001a283e248ac000026f000000067f84c839fcd9b05c0a6c102d2fa00000000000000369947f0b38b50000000053e88f75f9511400000002a3c0000000000218c
  | 53 => 0x14a1000000004fc5372f30edc57992b0649cc9c22b42100f1d45e598c00018914e102f4a450570f7c15ec36e00000002585692000040131fca5d1b9d21c466c25400015510000000343000052a02c20000cd649800001ba000064847634b140002e596db0001a06000097e5bb825200017630000000000000000000001ea0ea823c000021180000634000000195a0000000376d91d0bdc591022800008c1637114d7c9000024037400000000000140463001cca9900000000000000671d1a703b44800000f695344ffc12a88f50730e3a32059b600014a01f58e9f0001a16000162100001be407c00059d00000174cf310ec1d844c47c951f4b54115c00061d490112ad5a552680914fe84a8570cbb40000d5034780001a2521a335c000000195b000168262dc81637ac000269000030340003f5898312a43131ac86de1740266584400059f587a28a8d590af599c0fbc1480000000000073135c883134980004fc98322510c105b184434c8c0004a9144e00016460000e58151cd0a00000000ae00004d4c000000000066b80003c6c6ac00018fb1cb0ae258b4f9500006f30000fc8487d9c80000aa40e640001df8000000010314646c8607157400011610338a550e240000000000000000000010df00000001af544c03e506309b4da2000175600005a200008800000000198c5570000000662800000000003fec0006409843431066500000006934000279d8f42fb0d22012c625685072537ec0001d7400029f07a3000072a0000000574c000000000000000002ec477f68e193000011c75c593333c598c700000005e8197c36d400000000001c30000593ce820000000263c534000078700000000000e2e67e40000000000000056300017f21f605f72f2400041a83fb0000000000000000019d335b40004360bc600014c6000038e00000000cd81ee4848a2863dc12a000196b0b740000d10aaa4c0c0000000d9e00001c800019381f154be5148f84408000059b800000005d20ba4000605125e07ac01d5a249e00164607523400009c87d400016be00000000000f810000000000013d087864c0000faa000086c28d00000000e3e33ac7aa000000000013b8265554b314468d112c322000131a134948e0000000000000015ad9240000bf008845150000000000019e00012340be510937909f218817d9000000053c00b800000000000000401000003089e8517c0000000000276c0005604ce5000056810b00003a54000000142a0a543ae31dc0001448000211c73d57e1a722c99448000000000000000001966091c00013f46c02218b9b070450f3b104c100000000000000000000025f47fd00010e40000a942c787ff00004c2000104d3e8c0000000000612cc2639c400069440f10d91a6c45d80003b6050d2ef895c615c1470f913985b59a3d
  | 54 => 0xa39f92d00d1485f273da3b608408e25dd1d7530975b00010d502540000000e680000000000124c69b8e1119c56510000afb5fb509e0000000000000000004ee000000021ac15e3fb400000000000f2587e0000000000162e47840000000853000000000000000000000000000000000000000000242400000009f40000000587400000000000000000551c00068fc8d00000000000000000000004920c4649387ce03a935c575400000000005dd80000dd48a1216800026800000ab02dc4d845b2256442446e4cb80000f3e000000000000000000000192000000017e300000004d24000595811c0000000006d9cc345ca9627840003f997c3501c00000000000000cfc4c600003a6c92400006b10fc40005ecda18609839f00000001b240005c283dc304cc5d24d80000c1d1f9624157e086c0004518702434d4b10b80a30300d05d1f28c2928493b40000e3340554db213c9f84d3c2eb271840410485514bcd5d108759b9000000000003245e5400021400004918d12000064261a8cd03344000615400000000000001a0d3e494df5b1002649e19e741280000000b8864180000000d2c53c91cb52b9a690409555604d4b3000179600000d32cc0000000161926144bf00003b941cc0001ee410c0000ea7031d040000000000004c00aec00000007bb0000000476c0000f84e16046400000000b6534193402c000000009874ddd6c200009ce47d015907f436213840001f54a1f00013164b3d4923eac6fd0b980eb0ac99dc1a18cd8027594d5d94732645000021140851af00003dcc00000000003b308302b31329000015a0000000000002c00000000000c6400000002bf80005aecc22421d1d4341424b00000005b30f4023f400043000002eb8448000000000001f53e700d960d14614970000264406000019e6178c0de5c854870000ee65b0059a20fc2134f0ce1200000000001a4a000000002c8000000025d0000a76275400060f48e40000000000183f0001578000137600011c100000006370cc91d65479000000000000004e994d8000000000002775e78efb24ecb94231475c0000000506c0001f48b7f5788bf228240005fad1a40000000000000000000005aad9f745600000000ade5c691000000000282800000016e25bdc6f600000003cad71b000194b3aa90f100019ed0588cec45a038c6424cdd46d5762608000050880005eb000d00007ac0000ad861c40000000fbc142c27b0000d942a4542333e539c1471583032c20e00000000971569000000045ed5541c29095000000054ac0510000000000191636740b735b15fa5ca0fdb21c05600000000000000000003b2000000012c8000000087c1ab558f66500000001746000000000013e43bb18bb352cdf14d4537a1a8907f1c644fe000083c0001748000098833f40003a8c000000
  | 55 => 0x258c00000004f50001a2b001d46400002ba4a9cb7646147f23a14000000000004511ac00000002979683362800053f000001280000000000000071300019f300001a720e80000000fb018dc36511808523bf499c00002f825b98ab56dd27500000002bf40000001a3e00000005da11c255140db065000057c08bb0000000000000000000000bf8b8055ccad907a40000a100000000d3717c017a0000a9c000000000015ec00000001cd40005f68d81000155638889e960d4f501c8c54964986265a5c81300000fd0000000000025700000002f1d22f00008244a5c00018194e71d7d01b42b400024c4e4d4b7441a06c42600000000000160954fc784690400011bd9855e107a6680cb15042c7f007f9518453d3a051ccd1b07c973c45a951a07fc09c2970000147969456e05be06f511a2628e344d6403659c99050000cbb097c00001a400015e000000000000001a096310611194c0005444000000133d000000000017f16618c9500011934ab40000000acf0000b4e433c0000780dfd360000012240000630ed000007c7000000000012693cb09ad28dc0005fb16b8000000053d8000355d5a7020ced70000000000000027ac00049b80005334000098d79900000000000e6a1a6800000000000000000412c0000000000000131b0000e450000a6600000000e94000000000000000002544000000111249340000000e305d385613bd120626f8af441d00000000000000102700017f64ba9483000000000000001eb4000555c00028e155e696d4623c297781c5130f2fa8fdd04dc4b8000098c52dcd2e000000056105f80f3059f3cfd9e400012c6000142f28bcaa2000113f19694ca0ff8baa1c044024f44233000117361e4950398c255000124900019a800005ca00011eb0000000387950b0000b081e201f000000000000000000000000003413bc800000e8c9900015c45f6c000315c0004aac00060000001c3471e45a46330000e9829181165d64f7812900056410c85657c7f348ed7172fe48c200000002b5400000004cb000000019eccea00009b1150853800000002c645733a94c1a2b1c4a516b902c5d7527200000980000e6f44700005a6457e0064242000032d0000fa9381016a643070336e8a851bc0e70689093c0a1c076025c0002d48000426577e6a14000039c000000000000000000001a6723950323ae80000eec0004b0d29a070d61000009c100002464ff8eb60000bfc099c000000000059400000000000000113742c03670001214107419b29b48194aa194804387a93a017c0053c00017e800000000000000f2400018800001701049469564540000000c17514da0a52207224718e5446b46fc22a10b7245cb244d00b5b372802849957cf1b3582b173054d63bc2974b080e946ad5a253d448719bcc5
  | 56 => 0xb229341cd1d298b6101496940b9148000092e41e800040fd6a70b206185c9d08651c8000000129c000082a0000d0d1e88b7700000000000000176c000396c000000104e0cc8eff25c55cd00000000000000662c00000000000001089000000028801ec00449250000000000000000000643b688894d9028365d4662549c13b5954000000000000018c6590494025fc60b00014695a6122300d0ee50000000270d704479d3880000bad0b042a400006490ffd14c63b43c1082c0002234fe7326947b47140ca000000062e000042bc0000000000089c0bb000167a0000000071c14b19719a7000000000000005cc50ea01ecbe100000003630d343c3da252dc939750c4000136d8b33de5a2100002995a742b51ddd86958e819700000002ce8ff611ec15066651da0000228000000058e49de000000000fd35f0001a6645500006688000228c0000ad80004c2d54f42e400045d400058cc00000000004c98000038400000011a1000109754188cd000000000000000000000000001600006a900006e0215985f00000001cc000000000001fb0000000000054a962a000010732a1a9401300000000000000081111700000000000000130700000000000000000000066d000000019bf694c0004c40000132400000007951f20e1b2a982190000000343c000357800066a92ae10a433944a4ca5195c5d1587896700b940e3734ff402d0772236c000505cfbd434505c304989a00000002560000254800000000004dbc0001460e720a24ba069496623eb162c4ee80005ca84cd0000f0054c4bbb2415309290c000471155d144d7e66768000000000047786e5070173201c4c3c1655425008466600000005b280000000000000000000000001ed4000446000000008e705006390ec000000000000000000000051b47b89b0000000000000005c940000000000000000000000004514000000000062580000000000000185c0000f30472064100011e250914eb2edd3c65bd139555840001c580005e3c0000000a8353d14b500016fc00000000d0c000000008c000100d0000e17000040e37e5244000022059701ac57f18411704000000076d5f4000047300542e918810000000000109300b563000000000000d4e000000000000004b456fd000009e00003a0000000000013676300cdc26d88213e0c0001b55442000000046692870e50aba403cddf0000962000069e30180000c8c6ce16040bf000144a000000008e8000226c0000aa400035e1596000132a2bf06461020b5125d56fa000120300000005b350d03e65a595bc400061a00002b4c55a2dcd0de40cc0006294331462c00000000002e700470000764000000000006cf000002755280003e340006a4d62549619810000000000065b22dd0160f3c000399cf1813c8dc003102b953fd86e000028b00
  | 57 => 0x118000242106c0b449903d44000000174a00000001d44d1c02a04bb000126f000184800006ec0000881000098065143e32700e6c37b4ea412747e40a6d98f09c0d9659ac1f300004e012f00004a4400000000000000b2b3cdd4e33c7843f16ec000433077900003c6250c000205177a19c955b08ac1525338000197400000012f5000000036e0abc2f718090000edd640c00000000000f00ebe000172000000004eb95921df165417b0b2e0479155000054c1f6c91c29f87b3076cd7d2acc2a857a800048f0000000000059a400034e400022317f70000f230000000000000049740005f506c43758478682c0004af40005320d210dfda953c9400000006a6000149100000005560c675b045824adcdc80bc0f6220708885c243a428e43471400da55ccd5954ba40003200000274014400005c452f0db300014183110e7c00000005a10000000000000000005cbc00018f0000000084c66e93f04b816043108000614c914512c8dc164843456718eb00009470f7cf5c2678000428da0e27ed2e51bfd0cd1030ce633f800000000000000000064c00008243950000000564400052d000010180e25b400000000353000000057d062e04f966800000000000000000046d0000d1d285c000000178e48a8b662ea400000007363b2d088000000054cc0000000000456400000000001e6c000000000056f58d161ec46932d800000000003e580006788f2e0000470000000000007cf476039800003b50000d7f54bc00000000000000fb600000000000000000054400000004f9400043a0000000192520b43c3000000017ed70515400000000fd8000000049cca6e00009da3bf0000081c92723e01a30001a9200000004efcc8200009960ba8000000000000002e11628a3b00002903e890cb00011665ef4000113c000344c8f12dc19a500003d52ad8b5962100004a417c70000000000000000000004f4c0000000ba50000000122c59700011b11d3012145b0ebf077028265fd00a00000000a1594e00003ab000123366e0000000000050e0f090e843ce66ccea600011a952ac50600000000c7c6e4012000000015ab1060ff700011ef0ab400000000000000000362479c5dfd3580000c5500000006748000000000004a4e0a5594cf16870aa828a40000000000000122800012050000000530c000000024357081b918b15a84d2d0c961bca42163c0000000000000060129fc00000000005de4ed30000a2e00000000001a0100dcb1052945ee000006a000000000000005b9d43c00010070000000000000000000003780e13028800016ac000000000053b505f206d6173aa494b41ac82704d40002930bc31bc979000010dc123d0aa35f11990508ad100005541ec83d41b5860a609c3a70eb48990000d695098e234b54294000180100000004f240000000b
  | 58 => 0x7bf00000000000fa600000000000000544c0002d800005e74d9c43d01c6044c00000000004644000000000045c128b36fc90d00012eb13a00005b8c11d2c011af42ac8e600000004bc400037246540000000547c6e90000174489c2ed1fa400010640004f8000067258de000000055d588d00000930000be33ba8c863d540001680fa00f101c23a418e400000002a6000000000fc1b8d5b00001816000120111197930000b7422f80005f8400008e59a4000084a0000000614000064f00000b8cbe40000ff901154442481a5f2608450294539312791f80000459371d45b0001011000000000019c2481102200009000000000000080f45700000001792000085e2a9c00000004d767c932d5c40545000000000012fe000064e1a4c00000003cb000000000012802578e751e740000001a2f589d61856e8a6900013471da404900000000000000000060200000001c4477d00016df1ae98611440daf000022c6681498038c0000000000000000000000000000cc50ba00000000e21000000000000000000809000000029592f820210f25b2545100011fb586ceca000136300012bb0f4da6b5004176000177c000052925c061c0000000000000000018e0000069d327928a0000360000000069dc97a1878000474d2a000000004cc40000000f4164d918f3c7c56a3ad18c95414906072549d000000000003490dd8000000182c000000034a4c351e00cd44090000264981b00004440af87dc0ab93680000000000000040c04402c110264294f5b4fe0f5f69fc0001338bda00003570000000079800000000000000e1465b0000000040908557dc1c6c37233550ae1f4071f0b300001e4058c0000ccc0000000000000022c800000017004890000459559f0000000486c00000000000000000689849566f400045818082aa4bff3690000000000000008d800000000000000000000017700004cb9a10160c00000000002ab509b348d53400007be0d4549b18593a5349cd633b5991128d460900d41605b4cacd00000000000ff3000118c231cc56028004d37a468c124550304e00004ce52ee54987c4000143e4ec40003b3850e5c750962278f7400019624c44bc500004b525b00000000000000054a32f47681b6130c4bf400019604cc2254000000000000012390c1142b3480000000081a5d5400000000000a7c0002b8164c00011771450088000000061100a300000001a4162f000193b1cf000053dc0000000fd300018384e0000065011226a20000295c82f30a838541498bc0000000000000000008e94a208ce4bdc000391c0003c0412b61c09b70000000000000000006100000000000143504e957d00000004e64f3560b840d0000000000020f320c5b4207960a3a50000257d5ce2fb8000000000000000003d5c0000000000000000000000006
  | 59 => 0xd856af00000000e0800031780003a2551900009d80000000000000034e92351cbc000548400030111be0e046d738b09412e4d5c906ad2b668b4eb142f838d00009f504f000000007c30000017000000013c4000636466d0000407000000000000000000db6000056f0b295df0000153073d14e167115d09200222f50d1008c57e8010c0004fec8b11944a8000017ee2c70c5c6a4419200010e6170c10f1cf92073908d6446d97b5000172900015e7000000006bc0002a5d29e5fd000000000002ccc89f0000a930000000000000000000004a6d15b5ac000047b565b15d08b400000005f459d616d84d31f3053a35c14c022f0000000008755a80000aa800002cc201000166f1104be64494a7d5a5800000000002e08eee0cd40004d747284c749e420d0b25224574f2650775284400030815176624e4967640000d30c3a49ac0dd148c000000000015c800038980002cf074132740004228c7a46750434e2429d04e40fa0f580f3000170f445cfb4000196d0544000000179c00000000000000000000032a8000020800000006f70000000000000000008bf00008a45b74aea5050abe315012f3bcc00051253f12d2501e4e3c64d63fc01f3e900003b8043d107d1475ee837d5700b2231b932b4ec800000002fd000066800000002bb0dde1d2400000010002e29a3410d4bf7634c0000000d3e12219233b906c645112f41724b270ced7f800011c334900005db40000d354bb00015ca53900000000f0e659c000079123f65e80005c8c0000000a4700000aa000000052c00000001550650d21800000000000000000000029484310000000000000023ec000000121d000000043194fd4f2c33f55081f415b8f600000e3f000097b000075800000000fa05350000a5300000004a08a1b0000a2b5f58000000000000000006a396482d4d867000000058ecfa864380003770156000123d46510a732fcead00000000000000000000000012cc00000000000000000000000000000001a5d20ac9390000000000149757dc00047711430000dcb356d1f500000003dfc474000148b00000000c7184e54ed2670f893c031d97b26940000000028000000000000d51000000042c863d00017582d780000000ce433645eb00003293880000321000000000000000000000132537b800000000005f48d8403ec68859f00001dc4c5b1fd06d0000006d13ac68f3b200005078904326cc6a000000025e0a07000000000000000000000000000066580000000890119cf2a3fb80dc38753444eb50bf00016d700257c665c8c0703054bf54e017d4cf92f000012560000000023c64500017ca23c80002f20000000000040b40001b085f500009b200008cf52b4aee18f96bd49480000318f2f36340001760d2a4e104f718a81ef000000000004c700000000bcc0003684
  | 60 => 0xc000000000021750a05fd5520140c5ce000000000002cf00010f7000171e00000000000000000000050c164b4c9189f03d81340e180c360bc00000010680001314527c6b70000cc14e7c00000000000001142639cf76201800034540004834000557cf191e4c07866b4000000000000000000dec0003a8800000016e4513521556853de3a718d831d0f1a1d799bc2a48000504d5403020000000031a000000000000000001744000000000001ae000000000000005bcd82d0000bd005950f94f3cc1b00017df07e800006a86fe026968a27d96785aa000039ac00000000634bc800061e0000000000062a80004b397503ee000063f0c6d68318dd28417121c201d1000000000013663d4800000010290000f3a64bce92603c00051b40000000e270000ede3a685cf65b920239798a83ac8e9e543510f302cae4149c12e681c0000000f0543b17883c4526a0000e873acc000381cfef04800000000000010000000000000001552000000060e800024f40001e683ee000167e00001410000c9f62c1151000047a000000026b00000000ae501f8a1519cd0215170812000000000000000000ebd329d5fd05b8d8564dd53759fca61496c5a73580196370ca9a4b68000189c727000000005aca441a5090b105169a53500002f38000000000c00001854a3000000000003d8cf59000084400000700000829000000000004d1442d6ec3da017f01691fd3edc00042f47a13af15cf00000002ad05875c4400023000000000cb300002c300003a21fd45ac39888605fa80001db000000019074f7d5e54b6000041180002d900000000000000054f10a00001964dcc3d2553c000000020005e9000000000000000000000509c7820001632000166655898a32e1c18e6590d6136382f614ccfd02311703357d00613e8bb54fac0e844a84644d142363198000433800037649b300002d9624d8300000000000150c601d8474b3563c0000c2348dd84937e12c944082e25a043e626e03e05ddd9be3f50ce704209420a84447000000000000002518000157c00068440002e14af000013714765a7d59843fc0000000000000000004e200006a30000b1101ac976000000054e8d2b50f5822105946b24e9a9b1b640001e1400055700000000f0751d898955b80005a3000026e926100000003fb00003a7527117b44e700002e54e0da3904c00004540d871144b3838540001ee19fd0000442000179b1888000572d7c10000000000000000013bd27b800000005c60000000084856747a00000f4059b44317a62c2517e63a591f4b00c332d898364a88a8d02495af27589165330000000056d1a295d03468aab301589c05c86b348895dc4bbc8b613f13b921340000d693a135e4b8c000000000000002ab80000000baf00006df4b7d3a76a7084e3d3950f532576e22101b8
  | 61 => 0x648b80005ec4e7a1c38c482c058d7037cbbf62155d46600b1a630448151d00001218b14309da8600018fd0a48b8e0000eb50000000000111e000081f14282383ebd54321c547a65ec0000119a8f0001687179400000013c700009c458005d361b55ae00009bb5da800066a4e51003c000561400000000000000000000000000008af000141d50ec0004498000619584200000002b1486748c56e8580480a0d74dbc00000005a380003795071351c6b9000000069d904f2ee57f93ca524f300914a5714187000000045b427346f0f47105cbb065754120000bd369d031b05c4f6c22ac29a246188263696d804b092933192bf5b68bb30d509570001620000000000000001778000036000015a4000549467a2d208b82a2981700000005e3041e01b05a366dc00000009dc03480000000e8611507603b2532800000000ff561c000000000006b40d9801e0000a1c23d82b1000000000000000000000000000000000002f788830000de10b7cfcf5364000000068000006c300005f90bbd9e3282cc8800f00000b407cb000000050080004dd4e7d47b00003c4c00000010e9000156c00000001e516a05d4d47100018720000a213daca00367c00006cd31748780001ca584f08d077000017c44c14000000000030b000000015de0000fdf00017722fe94930e3c30a603048d247c8965bf800013a53ef00001841830127000000054b80000000b0500016315c618be3164c9000000001aada42147cf220000a8c02f93d71b4800000011e0072cf643b00c7c00011cf6038348563038061000105ead7611c1800000015b40001466284c000000099855c400028f4000000178a0000ed539d05400001a892ae40004b7847e1f0800045c80005ab8ad60000e7855f0000664001c00000006a60000411caef58fd1fe118527661ac0cd171d57a0000b3d00001f84cd4d714ef800011940004e517b700010b60000d4a1634c982afcc142b1199150100155adcc912838d922731283578d58b00004a2000000021fc00066480004748000549028f00000000000000000000000000000000000000000000000000000000000085400018fa000199f18d8000000049c4cb051117f0ee70dd0c1d21d1730321c63f6a30000000000058540d53fc89a8602946f00001e100004bd1db8508000173e534915f26397d80000d490000fd900010ee32b850542704b13d61140000000000016e138dc000046c565103c69b54b43f025d052d253d3ab5afcc963818f5300000006284c32546c00055dd9bb479427a07d834a00009a158689a70f6892a2b706b06888000461000017080000ed8000000113d683c25b00010570001a2a13188c30758000643c00000006645a446a0183c00000013ac461d802075d25400019205cfc000081400000000001ef4f700000f561084378280
  | 62 => 0x31f91395f2cea15be400031480005ced6a2000174349e400000009e6000045b00009ef4ebc61300000000000b61244186c1b856a400000000000000570400000019db2af41ed1de00e016406da3c19563000000036c9a6a00000001ad4d991259a9020d919633698a6406416419840005d0026a1a1c24c1c0062d03d0000265cdab1d515861edc00000018a72b9cba74c216b42e48d86000043c06ed7080001268373c17e00000000000000000000021bc000591c00027a800000000001548f141c9000000013d0000000000000000000de663495e4000000043fcdc52534e8d3e6cb81000000000016584e6d2e2000507200005561a9400033815ad0000000288800000016285df400002b945d0acc00000012e748290db00019413860fa70000000000000000011bb00000005b1c0000c1863a2d3c0000000dd55808000000000000000005dbc99f000000059100e562640003038000000033e17f40000d0800064418314d940006a34c3424bd33b272c35b2c4cccf0adc00000007f75c193ed0cf41811e0c202191c0533bc43834c005d75d99a7a10e52b341208173788df62988be73c34bd8550400000003d800000000000000621800000008c1000000000000004e7599765780000ee0024599000000018d00000000000000000007ba00c8eac5b14000000031d000000000000001080c4009883921afd2b82ca4d77437599d0001665000110653800000fcd722000000062f4000000000000003e90000000000000000000000000d1600000002b2c0000001a32373886d00014ec307cce30000b2f392160820a00003d2c00039e400000000a15dd4b7e4b20e40156c0001ebc000000000000000d600000005ba93576144bdf4e14ab508b99cb467173853a105e000195123884234d545762fd0000000199a000000000009ae00016e64244000000000014c59d400004726a793b00000e730000579000018b000000000a44523ffc000431400014800000000000000000000006fa096130400004b413612d744219d84c08000421400030240000fa8000240c000000000051f0000000000000015b50001825000131e4dac00000004ef52148ca00000001cac00000000004b580000000a49201c00000000000000eeb00000002969a4b0000000431c0000000000379ca0f0000f82000133a0000621036800000000000000000589844e642d94c0000d4f01d5a3007c594400008765298000059c0000000d830000865620cc7500000b9299c0001d489fa00016d4478c7c00bc8000000000001e8000000000000000000000a3c0000000008c00000000004f104364e097e20000000000000014bc00000013065ae400032d0eed0000000328c8725ebd7e722498d4472584c2ef000a2f5400000011ea097988f000000000014ac000082e55a02a
  | 63 => 0x38a278c0003cf0e5f000000043cc5e640d8000000000042100000a80000000000016f11350000fc20bfcae300005b5394c0000b188d100013a933b9559000103c000000000000004b9000000019f10000a58000000024e0bc4094d5b91780c711e78720000022600006d423a80000000000000027f0001576000000000000004928cca0cad67656980002b8400017c93bc0000ac80000a72332c2640ce800000005bf52898284ce12d221080000830000288d6a10000000000117a000000000000005c640000000a4a0001810606065062b400063cc0001661a630000000000000000000004898000566c00037d173a60559e82f899c50000e3b00
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x44048020e00635444048020b22849495148020c0d635c86395310a18835506050f10d22745c05248710e22544856008710a25861492190310a25861492110310d20521c12110310a4683d496108310b0a83d484008310e23525844008310aa1868844008310c33711c16494e10a1a83d506050e10c31651c1640c6108e3865c032c8610a618018f5208610c4473d496008610990835c02110210d23525c02110210b088254c400c210e08631484048210e20521844048210aa286c844048210e8063c844048210a618018d6114910c44735856014910a1880590530c510a2880590520c510b41801c85348510960855c03248510b08835c05210110d21715c05210110d10531c12110110d20521c12110110c44535ca61cc1108658714a61cc110e105398440cc110aa18298440cc110e205298440cc110b22858844088110e22658844088110f00538844088110c447518d2148110a448614d2148110a188614c4048110e08631484048110e10531844048110e20521844048110b20854844048110e20654844048110e80634844048110f00534844048110c457614e2108110838805d06354810928805d06354810a0c8458c6354810a488058c6354810a2880591520c81086487549600c410e2264549600c410a618018d5208410c44735496008410c25765483190010d20711c15210010c257654831100109a0825c03110010d21525c03110010990835c02110010d21525c02110010d21525c66010010e2152584400c010991870c4400c010f01520c4400c010b2185c8440c8010e2165c8440c801086787d972148010c457518f2148010e21525844008010b21850844008010e21650844008010a28865484044010e08635484044010a4683dd95244010866869d95244010c2476d915244010c24761915244010c4476d8d52440108668798d5244010a468398d5244010c467618d5244010c447618d5244010e076418d5244010e046418d5244010a608654b4044010e406354b4044010a248654a4044010c267654a4044010e046354a4044010a24865484044010c26765484044010e04635484044010a60865484044010e40635484044010a928398c4044010aa28298c4044010e136518c4044010e8063d884044010a92839884044010aa2829884044010e83631884044010e80631884044010e21851884044010e1063d484044010e2062d484044010aa0869484044010b21859484044010e80639484044010a30865484044010e10635484044010aa0865484044010e80635484044010e23865484044010b22865484044010b20865484044010e20865484044010a20865484044010d22765484044010e22765484044010f03635484044010e22635484044010e20635484044010f00635484044010e00635484044010d227454a5144010
  | 1 => 0xe23754856008440e83734856008440ca0734856008440e80734856008440c80734856008440ca1625c46294040ca1725846194040ca1764842194040866879952108730d22541c12108730c89635c86310330c91635c46310330b2281d4a5210330d23525c65210330b2282d465110330d2172d465110330b23854842110330d22754842110330ac18018d2108630cc0734856008630c61615c06114930c61625c06214530a60854856008530e20544856008530cc0631c12108430a0d821956310030a15811956310030990815cf4210030c19651cd4210030988825cf4110030c19651cd4110030a1a83dd96510030992819ca631003098a829c66310030d8072dc56310030d83721c56310030d80721c56310030c29655c86310030c31655c46310030990815cf6210030c19651cd6210030c29765485210030d21525c4521003099281dda3210030c89769c83210030b81819c8321003098987d883210030989871883210030c89761883210030b09851883210030b81811883210030988825cf6110030c19651cd6110030c31765445110030d2172544511003098a82dda3110030c91769c43110030b81829c4311003099187d843110030991871843110030c91761843110030b11851843110030b8182184311003098a82dcc211003099281dcc2110030899861cc2110030d21754842110030d80734842110030a928198840cc030a8a8298440cc030c15635c46395320a18835506050f20e22544856008720c2b721c16494e20a1a83d506050e20c29651c1640ca208e3865c03188620988835c02110220b108154c400c220a1880590530c920930805d03214520b41801c45348520b10835c05110120d08531c12110120c44535c662cc120e085398840cc120aa18198840cc120e226214440cc120930805d06354420a148458c6354420a508058c6354420d22745c03254420a3080591510c420a25860c951900209a0815c03210020a25860c95110020b21800c95110020988835c02110020d21725466010020989870c8400c020e2162544400c020f0032544400c020e10635444048020c2476d915148020c24761915148020c4476d8d5148020c467618d5148020c447618d5148020e076418d5148020e046418d5148020e40635474048020c26765464048020e04635464048020c26765444048020e04635444048020e40635444048020a8a8398c4048020aa28198c4048020e0b6518c4048020e8063d844048020e83631844048020e80631844048020e21851844048020aa0869444048020e80639444048020e08635444048020aa0865444048020e80635444048020b22865444048020b20865444048020e20865444048020d22765444048020e22765444048020f03635444048020e22635444048020e20635444048020f006354
  | 2 => 0xc16414d21c33711c16414d21c30711c16414d21a18835506050d21948805cc540c921ca2645c0610c921ca1645c0610c921950805cc540c521ca2645c0620c521ca1645c0620c521b048454c320c521b408054c320c521a18835506050c21a84835906448421aa08059064484219a0805d06348421a848458c6348421ac08058c6348421d22745c05348421d21745c05348421c60865c05348421d23845c05348421d20845c05348421961809d743484218e0805d84348421ca0641c12154021cc0631c12154021a18845c06354021c48631c12154021c50631c12154021a4683dd92154021c2476d912154021c24761912154021c4476d8d2154021c447618d2154021e076418d2154021e046418d2154021e418018d2154021b2284dc12154021e4063dc12154021c44631c12154021e40631c12154021a63854856008740cc0734856008740e06531886150e40e0a53d886050e40e0a531886050e40e1253d846050e40e12531846050e40d06729c75394e40d0a729c35394e40d09729c35394e40d12719c35394e40d11719c35394e40a2a80995520ca40a3280995510c640a258518d2108640aa18018d2108640c84734856008640aa0804856008640d04721c55310c40d08721c15310c40d10711c15310c40a158119153cc840c0d655cc420c840a0d8219153cc440c15655cc410c440c61651c12108440cc0734856008440d04721c55314c40c1b761c15314c40d08721c15314c40d10711c15314c40c0f8754d6214c40c0c8754d6214c40e078154d6214c40e048154d6214c40e088054d6214c40e055358a6114c40e05539896114c40e05535896114c40c178754d6114c40c148754d6114c40e078254d6114c40e048254d6114c40e108054d6114c40c88721c16314840a158119553cc840a1581195534c840e0953548604c840c0d655cc520c840c25655c4520c840c25655c6320c840c29659c2320c840c19651c1320c840c29651c1320c840c90711c16314440a0d8219553cc440a0d82195534c440e1153544604c440c15655cc510c440c25655c8510c440c25655ca310c440c31659c2310c440c19651c1310c440c31651c1310c440c0d7558c32c8440a888058c32c8440c157558c3188440a908058c3188440a0d8319552484409a1809c73248440a158319551484409a1809cb3148440aa0815486048440aa281cc86048440aa0825446048440aa282cc46048440a258518d2108440aa18018d2108440ca1861c12108440ca3651c12108440ca1651c12108440ca2631c12108440ca0631c121084409a0874866008440c847348560084409a0874856008440d80734856008440c8873c856008440c90738856008440c88734856008440c90734856008440ca3874856008440aa0874856008440ca0874856008440ca375485600844
  | 3 => 0xcd882801cc23262002d457800ac2d2058ce0000040800000006f09a9fb3460b1c4a300810006b2daa70446830ea7a32000003021c00000b7a8c59886bd8b62a936002be001b889000050988d33c001c85a0ba62aecce2c0c21fa4e21661ab699b3abe88a2ca562410c2c2e2000a600092868be44000781d0169ec97aa69b8a29d04cbd06600000850c4888a8000000012c8080000000002266529a4980c001ee4f000000009513a0031a78ac4000003e19000282cbb1e029a6a2270c98c200000c1000820e2658005d8f21a000cf944002a8ba2d61600053aae92842ad0b4000004c80000000a60d27283e25306520d0000369e8008431431a96bb83a099420017a8e8005e0006d8ee0009ca912215974000008f06456352b18180000013b646a20eb90a08ba685fb4a8a12071af82902e9e04a9714c000000c8f0000b800000c422c00000d1962aa80052800478008d9882385cca2ba91164cc9da77ab214b60b09fc550c86b800519d21a8841e800d7a941183c8e356d98009c800c59560000000034278000004000000d0070a1adcd42b800000001aad311a00000b42ea07800000ca0000000344dab02c8358d68007a9c449000da28a41000000507c000948007f800c4800bc93e54a5864a0a03a902000098180373425c0000010e068004c12aaf0007a24ec8b182f1f2632c86ea0c6380245000b302cc322a000601da468815a472301f280419347928e96a1e612e0cb054ab0fc900001799e0019c6606e08b629416e6cafe1e1a4d50002b0e600118920d4001003e800000205416cd20001f888002847e030001d49d800000cc771084b8000010a001be5f0000032a570009b0003f9127d800000722b9d600140380d6000020000c004160041001400000000000300c0901c050200b0300003001008030040000400014090000a0080600000008040580500400004000000301416008030182e014120000f0040a00405030040000a010000180000400010010080a000080001100c000000002c010180801c0800003008000000100c08008000100a0540100000034020140000c07018030bc030640f000090000004c0b008060000a00002018000000100000004050041c018090000400003c18631c14354742c1a631c14394342e04531886150d42e0853d886050d42e08531886050d42e1053d846050d42e10531846050d42a31811506050f32b108050c4394632a888050d6210c32c84641c5434c832c88641c1434c832a30805506154032c18631c14354b41c1a631c14394341e04531886150d41e0853d886050d41e08531886050d41e1053d846050d41e10531846050d41a29821506050f31b088050c4394a31a908050d6110c31c84641c9434c431c90641c1434c431a28805506254031c18731c16414d21c2b721c16414d21c28721
  | 4 => 0xa80f6010000723e3780000000860001d2920900000330738000a24c000eab9a126d324908f43b2ca1b00604af0669a270172b38005827cd39f4b60626c2a2042643a0483600000038c282a0035c020969a800bf1c23696a819e6760e4458
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x62c007180000008800c0001254000080038b0020813803a0838a5e98c174aa4a805a0000b42a009a126469f46b821b1eac0033c14000289000044009800f1a000010278000000800400040608218845c05348421a204bb0031a42a80436009460063485500874050831ee090aa010e10e14734856008740c403990090ac010c818048720553588531030110e402a6b10a6206802048054d6214c40c0243904a9ac22988181087201535845310340104402a6b08a6206025d48058c32c8440c08ba900b1863108814219518c704842110290527c3a42b00422062021f734856008440c40438e690ac010881122989d52108440cc3102ecc0ce419080186025d9851883210030c40bb30231064200618817660a710c4400c3022ecc28c218880186205d9821843110030a40cb0e69084220061a00536066210330482a032e192a2200601068021b635444048020d01430c6a888090041a008618d51101200828432c290e09088188580a4f525844008310c8041ea4b804220421900835c57014840443400a6c14c220660884886605298440cc110d00428c690880902216009614d211012044224130a92e0188800864020d525c02110010c80c3aa4188801802160293e1952101100424452d432a4202200868021b6354840440109114c4c6a9080880216029398d52101100434050c31aa42022008680218635484044010
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
  | 5 => packedAt gbK5 (484480+((h/3785+packedAt gbK5 (431490+(h % 3785)*14) 14) % 14989)*15) 15
  | 4 => packedAt gbK4 (365729+((h/2271+packedAt gbK4 (333935+(h % 2271)*14) 14) % 10884)*14) 14
  | 3 => packedAt gbK3 (27740+((h/146+packedAt gbK3 (26280+(h % 146)*10) 10) % 578)*10) 10
  | 2 => packedAt gbK2 (3591+((h/16+packedAt gbK2 (3479+(h % 16)*7) 7) % 70)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffffffff80ffffc0ffffffffff80ffc7ffe3f
  | 1 => 0xe03f01fffff01ffff03f07e07ffff07fa31fc7
  | 2 => 0x3ffe03ffffe03fffc007ff81ffff83c3e3f8
  | 3 => 0xffc00003fffffffffffff80001fffffffc03ff
  | 4 => 0xfffffffc0000003ffffffffffe000003fffc00
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0xa181142808e2448402cb09628a5842940d6e1b
  | 1 => 0xca924c519121c91cb01542aa6cab5259a316c5
  | 2 => 0x9524289aa24483ad554084db29356b12c3a368
  | 3 => 0x630b1634489123269a6d01041c68c637401b6
  | 4 => 0x1838c183870e1c3b8e38e71c70070843fad800
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xeaa8e800eaa8e800eaa8e800eaa8e800eaa8e800eaa8e800eaa8e800eaa8e800eaa8e800eaa8e800eaa8e800eaa8e800eaa8e800eaa8e800eaa8e800eaa8e800, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_12829
namespace PEqualNP.Outside.L_meta_12829
open PEqualNP.Outside.L_meta_12829.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 5 zero,inputs.getD 3 zero,inputs.getD 4 zero]
def fullWord : Sig := 0xeaa8e800a8a80000eaa8e800a8a80000eaa8e800a8a80000eaa8e800a8a80000eaa8e800a8a80000eaa8e800a8a80000eaa8e800a8a80000eaa8e800a8a80000
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 0 32) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,11,43)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,11,43)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (3936921768 * 2 ^ 32 + 3892314112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_12829.Model.Repr at out
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

def mono : List Gate := [⟨.and,[0,5]⟩,⟨.and,[3,4]⟩,⟨.or,[6,7]⟩,⟨.and,[0,2]⟩,⟨.and,[6,7]⟩,⟨.or,[0,2]⟩,⟨.and,[1,11]⟩,⟨.or,[10,12]⟩,⟨.and,[8,9]⟩,⟨.and,[8,13]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3936921768 * 2 ^ 32 + 3892314112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3936921768 * 2 ^ 32 + 3892314112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_12829

open PEqualNP.Outside.L_meta_12829 in
theorem PEqualNP.Outside.L_meta_12829 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3936921768 * 2 ^ 32 + 3892314112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3936921768 * 2 ^ 32 + 3892314112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
