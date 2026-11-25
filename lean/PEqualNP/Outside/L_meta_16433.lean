import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_16433.Model
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


end PEqualNP.Outside.L_meta_16433.Model

namespace PEqualNP.Outside.L_meta_16433
open PEqualNP.Outside.L_meta_16433.Model
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

def SBf (j : Nat) : Nat := [5, 4, 7, 5, 8, 7].getD j 0

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

end PEqualNP.Outside.L_meta_16433

namespace PEqualNP.Outside.L_meta_16433
open PEqualNP.Outside.L_meta_16433.Model
def s0K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (i*5) 5
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (6+((h/1+packedAt s0K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0x7fff00ffffffffc03fff80fffffff807f8ffc7
  | 3 => 0xffffff00ff807fffffffff01fc03ffffff18ff
  | 4 => 0x83ffffff00007fffc03ffffe0003fff80fe0f8
  | 5 => 0x3ffffffffff8000003ffffffffc00000fff00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x104b092124851444848a8b162d545b4a936b5b
  | 2 => 0xa095d84a4d4a28a3a915c0ab569aa8c5a8b5c5
  | 3 => 0x412652e88a534d293227558198c335974d18ae
  | 4 => 0x76389c8cec6c723223b9e6cd0313c6e18ee0f0
  | 5 => 0x7bc0e0f0f0707c3c3c3e78f1e3e207060fde00
  | _ => 0
def s0Atlas : Atlas := ⟨4,rawDecor 62 s0Pos s0Neg, 0xccc0c0c0cc00c000ccc0c0c0cc00c000ccc0c0c0cc00c000ccc0c0c0cc00c000ccc0c0c0cc00c000ccc0c0c0cc00c000ccc0c0c0cc00c000ccc0c0c0cc00c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_16433
namespace PEqualNP.Outside.L_meta_16433
open PEqualNP.Outside.L_meta_16433.Model
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
  | 2 => 0xf807f01fe01fe03ffc0fc0fe07e0fc07f66267
  | 3 => 0x7ffffffe0003ffff000ffffff0007f87f87
  | 4 => 0xfff8001fffffffc07fffff0007fffff81f83f8
  | 5 => 0xffffffe0000000007ffffffff80000001ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x830104222424404085149164861453222acab
  | 2 => 0x5552aace51d48d693e0ad8aac5a8e857566265
  | 3 => 0x46a4c9949491d1b256b820cd96da20a5985786
  | 4 => 0x64c68d1919191923672cb281071cb2c11d0350
  | 5 => 0x87070e1e1e1e1e3c7bcf3cf1e410c3061ff800
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xaaaaaa00aaaaa000aaaaaa00aaaaa000aaaaaa00aaaaa000aaaaaa00aaaaa000aaaaaa00aaaaa000aaaaaa00aaaaa000aaaaaa00aaaaa000aaaaaa00aaaaa000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_16433
namespace PEqualNP.Outside.L_meta_16433
open PEqualNP.Outside.L_meta_16433.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x2cd202c000232800025001c000006412444200000070012006c000589831f3ca559800bd509140068022b800e18a01904eb4b9d1e842000254005260608000020008f1a000020e00711ff43bf43fe43fd43bd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x69184a0034800007a0000104750012000002e1dcfa2e001d87685029c060501013c183d25000be74350006c42330000011001bc7c2d001b4ca53039742c2b0000088543f0b078591081102292c0788e4126190200037000f21f33800c60211018e24d3595400513d800343500000683900050006c401a0ac4300048c2842d0dc4e311400c925e17988165b29114e67c050381e381992c2a133906c3019151803a171d15cfe083c09846324190038011f9384800048183c00003c247c8c0000000008180400180c0c902404000034000000004c403c3400688828042068085008567ca5a1cf547439f286873d5490edea4a1db14943cfa9a87af5250e78a4a1eb1494396292873f5150e78a0a1cf950439ea9c853e5290a7aa3214f942429ea98853e5210b5ca4214f544429f280853e54cca7aa9996b10b32bb28e657551cca7ea9194f152329faa2653c544ca7ca8194f55032d6210653d53d067ca5a0cf943419eaa4836f52506d8a4a0cfd4d41d7a92833c5250758a4a0cb14941dba8a833c505067ca820cf953319eaa6636e52cc6daa598cf952319eaa4636e528c6daa518cf951319eaa2633e540c67aa818f54c4319faa6433c54c867ca910cf55221af29c435d53887588510cfd51219e2a2433e540867aa810eb10821b7294816d529027aa7204f94a40d7294812e529035aa5204f546409f284813d531027ca4204f544409f28081ba501027ca9984f553309faa4613c548c27ea8984f15130b7a92616c524c2eea2985d145309f2a0613d540c2dca4185b54830bb2886175510c27ca9904f55320d6216413e548827aa9104fd51209e2a2415f53482b8a6906b10920bba8a4174514827ea8104f150209f2a6213d54c427ea9084f152109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x20018b8e90000c73200ab04c0800001002651e1a20a86aa0160121001130050008b18951d0e2e6294343c910a51cca3561152328b594420ca8d63108328b18953d062e62943418b189544c63860551318b189540c61d6315321c394c428862d6510821a9584420862c6254c408b189511022c62553308b98b548c30c5310920c9108514822e62d50208758c540823561150208b18954c422e62d5210
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 134
  | 3 => 26
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
  | 5 => packedAt s2K5 (880+((h/16+packedAt s2K5 (768+(h % 16)*7) 7) % 69)*7) 7
  | 4 => packedAt s2K4 (3970+((h/44+packedAt s2K4 (3618+(h % 44)*8) 8) % 161)*9) 9
  | 3 => packedAt s2K3 (1036+((h/8+packedAt s2K3 (988+(h % 8)*6) 6) % 35)*6) 6
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffff83fffffffc0ffffffff81fffffe3ff1ff
  | 1 => 0xe0ffffc0fe0fffff0783e0fffe1e07ffd23e4f
  | 3 => 0xff03ffff000fc1fff803ff07ffe00781e3cf8c
  | 4 => 0x3fffffff001fffffc0007fffff801fc0ff0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x20080888240200002904a108802290a404d095
  | 1 => 0x4a3191064894b0cb02a148d332142558d2264a
  | 3 => 0x865aa2921d29135558427a45d540560d634b8c
  | 4 => 0x14a344249181a5a694e8108669996011b80d60
  | 5 => 0x18c38738e1ce39f8e7739ce071118461ffb000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaaa88eeaa8888eeaaaa88eeaa8888eeaaaa88eeaa8888eeaaaa88eeaa8888eeaaaa88eeaa8888eeaaaa88eeaa8888eeaaaa88eeaa8888eeaaaa88eeaa8888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_16433
namespace PEqualNP.Outside.L_meta_16433
open PEqualNP.Outside.L_meta_16433.Model
def s3K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0xac42
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (i*5) 5
  | 3 => packedAt s3K3 (i*16) 16
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (6+((h/1+packedAt s3K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s3K3 (17+((h/1+packedAt s3K3 (16+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xe07fffffffffffc0fffff01fffffffff1f8fff
  | 1 => 0xfffffc0fe03fffff0781fffff03e07ffe4fe4f
  | 2 => 0xff81fff0003f03fff801ffe0ffc007c0f8f38c
  | 4 => 0x1ffffffc003fffffe0000fffff800ff03f0
  | 5 => 0xfffe0000000003ffffffffff00000000fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x29044482440840802912520914429452098495
  | 1 => 0x421888648952914b02a0a4b2623422ac643a4a
  | 2 => 0x852d5121d5a456d558513ac8be905706b8d38c
  | 4 => 0x1651a24919069b6694e40c90cb396208f60360
  | 5 => 0x1861c38e1e38e3b8e779cf1c0c218430dfec00
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xeaeac8c8aaaa8888eaeac8c8aaaa8888eaeac8c8aaaa8888eaeac8c8aaaa8888eaeac8c8aaaa8888eaeac8c8aaaa8888eaeac8c8aaaa8888eaeac8c8aaaa8888, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_16433
namespace PEqualNP.Outside.L_meta_16433
open PEqualNP.Outside.L_meta_16433.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x600000002c4800000813224844a25005d380007c0891c68008463c987183450000700003c6ca80000058000002003a000000000c8004002a12060180000020101000c08e001408eff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0xe817d51d037e83a06f50740beaa4817e53902faa7206fd0e40dea1c817e52902faa5206f90a40de214817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037c86a06f10d40bfa92817c525037e84a06f50940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881bf431037a86205f94840f7290816e52102faa4207b54840b6a9081be421037884205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330bf296617d52cc2fca3985f54730ef98e61dd31cc2fea9185f95230df2a4613e548c2faa9186f552309eaa4617c548c2faa7187790e30eea1c617e528c3dca5185b94a30bea9461ed528c2daa518778ca30ee194617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130bfa92617c524c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c2faa8185f15030bf29861de430c3ba86185f94830bea9061de320c3b864185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c83de65907b0cb20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20f721241ed42483de64907b0c920bfa8a41f751482eea2905f14520fa28a417451483de42907b48520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20bea98417c53082fca4105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fd98621f830c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2087dc8410fa108217e50043f660087e0c010fb88021fa10043ea20087e44010
  | 1 => 0xd5190afca1215f54242bfa9a85df5350abea6a15f14d42ee29a855c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42bea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332f7a1665ec42ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa71977d0e32ee21c657e528cbbe65197bcca32bf28c657d518cafca1195f54232bfaa265bf544ca7ea8995f95132beaa2657c544cb78a8994f15132f799265de324cafea2995f14532bfa82657c504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca61977d0c32ee218657e520cbde84197b10832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef50f41bf29683ee52d06dca5a0df54b41f6a96836d52d077c85a0ef10b41bf286837d50d06faa920df94e41bea9c83be43907788720df94a41bea9483bf429077a8520df94641dfa0c83f741906fca120df54241bfa9a837c535077e86a0ef50d41bfa92837c525077c84a0ef10941fba0a83be41506fea0a0df14141bf2a0837e53107bca620d794c41bea9883dd53106baa620ef90c41de218837e52106faa420efd0841dea10837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331ef21e63dd43cc6fca598df54b31ef19663dc32cc6fca198df54331bfaa4637e548c6faa918df15231bea9c637e528c6faa518df94631ef98c63f7318c6fca118df54231bfaa263bf544c67ea898df95131beaa2637c544c778a898cf15131ef21a63dd434c6fea498fbd4931b7a92637c524c7d8a498db14931ef19263dc324c7ee6298f78c531bfa8263fb504c6f6a098df14131fc2826378504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618df94831bea90637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c86faa790df14f21bf286437d50c86fea910df95221df2a4433e54886faa910ef552219eaa4437c54886fea710df94e21ef29c435e53886faa710f754e21aea9c437c53886faa510fb90a21f6a1443ef32887d86510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21fb90a43ee21486fea090df14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf29043ee42087da8410fbcc821f6190437e51087de4210fd88421f690843f521086fca010df54021bf29e81de53d02bca7a05f54f40eea9e815d53d037c87a06f10f40bf296817d52d037e85a06f50b40bf28
  | 2 => 0xb162670869c51080004a0003627f0450001ba000e99844ea94c5314b000930198000000000028a17490c268000009e0b100039c914ba90e3f62a8002032ac0800005d000111170fc3509d13f93c3884f4069540a2a30941d60324ccc8000000128df00021080035a7637292087936482554a292e1164c00017a298214048fa000824511df1907b50f95c23e000e61aa4d45a03916b1ae5c078a8822a6880000a1c65850381f2f8000b60b5106934b4a800da18c561f30000bd369b60fa2d93ea584e610c000002521e8139640007c0001b73e8948000000ca5d85b80023c3a8000d94fc3e472a3705aa24001d04be000350a80728e1430571405eca801b000a4c851214103cca399a0422ed028550840a8000003c86eccd8000b600000015000048d393f49c5807e82b506238f392b0061388205612a7e0228000760013e12d03a3086800032a698089033061f0cc8004b8769100ef0000000027b4163844b0f83821fcb6a6f2e47b12c89b0007ad07800000000af87845631c3702e1461d92f0000000010704b000000fc800000200c91583563480023a44aa385997400053cdf8cc000070e02220ce450eb89a3ec6f00008c0e20a10b8701700202e1e24aa878f313b3d40f8651b04ce2ad43986494000ad92c4cc650e780744e0007387526a2f85483d0008fcf02690000dc621fd3ba17cc2a710003613b959046a54bba3947c458248dc17a6d0d7052060358f90994182c01e25a1e8a08760003d022400000000624c5000000000ef0040040502c070180401c000042c0000302c00030130080300801010040240201000018060180107c08010000100100c0000002004030000904c000041300404000010000202c040040504000020000040b0001400c0f124050100402016010020000201c0000c030000503c0101c0001c040180201001000090080000820000140040502c020080501400018050100200801010020500f00c0c00009010030040900c0205400014020a01900003020000440307011040010180c0000907c0201c0c0300a004080000500c0702809008060880602c090000e00c1e0003a014150401c000050d40500c0d0100001807008010c00601809008010041000007010080100302c02008000040000803054080000107800bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1fbd4943b7a92877c5250fd8a4a1db14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857e5290b7e85217bd0a42bf28c857
  | 3 => 0xb190c00078d232400006d4000000008701d0ce0006cc000612700013200010e2bc780910007dd009ad0bc0586d9e12f011849a961ec88c209274768a0ab99d20a1988004010c8690b0a5348018020d31ee2f0cf05809e64c8883435e8502610b50a8d01895307e3c8b2a924a232cde85409076c0022d000350e32351921ec000000484f9198004048f00007900068ca6a6c0fc0000014400086407218000925178362dc71ce6a4f52e000af12f00046c89a0d24c4d02825d284818c42940d87e8a714000014ca528d1c82908809802e27c5f8002a47c53001a212840748a7232a04c69324585e4008ae3fe5207597e3005a87716622e234b9a362de8c4b393a19a5f52b15d2549409194651e96c2c9e515a98d3d0b9342000ea00b10450c8e89c1fea2c839c81b47d4600001bc84ce198b0041cd3819f5225c4341814244184b92011e2d007a2444265cbf80018a63934000384660e58d13fc8f4d00001da745420c64881d049000026000e4800000854001d84140000000048e000c78cf2484dd131121424c434996000088dd000202304700000c8000c127239486d358350ee2402391c3d2950e90d50006b0ad0fb1c40c8910c300a95cf702c1025044e9490b41806f8e6000030000000de0007a8623708a40000004a495191512342201326e4846c8c8a1d13c98414a1123000000279000694080fe3b88a9020b2000000ea81800061c1c0005203a09c8142048c1310004ca7640f1ef318000d4a4
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x53c82cc6350b20ab59032c823e64947208f59251c825e63947209758e51c82ad64c87209798f548825d63d52208f993538823d64d4e208f992538823d6494e208fd91518823c64546208f992544825e63951209758e544827661951209d586544825f63551209718d544827761551209d185544823e6515120cb588544831f54d4d20c7153534834d62d4d208f992534823d6494d209798e53482766194d209d586534823f6454d208f19153482776154d209d185534825e6514d20c7d50534831c5414d20cb152424826c6550920b318d424826e65cc920cb15332482ad640c920cb150324834f530c920cdd53514833454d4520d5d4f514835453d4520cdd5051483345414520d5d4c51483545314520d990851483654214520d9cc8514836432145209b99721482ad64c8520d914721483645148520d9146204823d65950208f990540826e62150208f993530823d64d4c209b98b530823e6414c208f59053082766114c209d584530826d6588420cb552210832d5408420cb553200826f6548020cb55120082e461480209ed95200826e62953109b58a54c425e63153109758c54c423f6454f108f19153c426f6254f109b18953c423e6414f108f59053c423e64d4b108f59352c425e63d4b109758f52c423e6494b108f59252c425e63952109758e548426e62152109b588548423e64d4e108f593538426e62d4e109b58b538423e6494e108f592538423f6454a108f191528425f6354a109718d528423e6414a108f590528423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d109ed81534425e6514d10c7d50534431c5414d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524427761549109b994524432f5414910cb150524434f5314910d314c524435853c4110d914a104425e63d50109758f540426e62d50109b58b540423d65950108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c10d6181530423e6414c108f590530425e6314c109b988530426d6214c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520436461548108f990520423d64148109798c520425d63148109b988520436552c84109d594210435953cc0109e594300427965840109dd9510042e462440109ed9510042d86344010
  | 1 => 0xc63e64951319b98a544c66d62951319e982544c67960951319bd89544c66c62551319ed81544c67860551318f994544c71d6315131c7152434c65c6550d31b3189434c72f54d4931cb153524c72f5414931cb150524c71c548c931a7590324c71c540c931d3d48324c73b54d4131ce153504c76b52d4131da14b504c73b5414131ce150504c76b5214131da148504c75a4314131d650c504c75a3214131d60c8504c75a31141318f596540c63e64150319798c540c71d54cc43197d95310c71d544c431b6181310c677654c4318f99353c863d64d4f219e98353c867960d4f218f99053c863d6414f219798f548865d63d5221cb58a548865e63152219758c548863e64d4e218f593538871e5494e21c7552538871e5454e21c7551538874f6254e218f990538863d6414e21cb95242886cc6350a21cb95332886ad640ca21cb950328874d530ca21ab593218866d629512197d8d544865c63551219ed81544867860551218fd91534863c6454d219bd89534867b6054d219e181534863e6414d218f590534863e64141218f590504865e63150219758c540867a60150219e580540863f6454c218f191530863e6414c218f590530867a6014c219e580530863e64948218f592520866d6590821b318d420866d650c821ab59032086e5610c8218f992510863d64944219798e510865d6394421ab593210866f65484219dd95210863f64540218f191500865f63540219718d500866f6254f409b18953d034f6254f40d318953d031d5390f40c754c43d031d53d0b40a718d42d031d5350b40c754f41d02ad62d0740c754d41d02ac6250e409bd89519026c6254640a758c419029d63d02408f994435023e65d0940a718d425025e63145409758c515023e65d0540ab58b415023f6550c40ab189431025f63548409718d521034f6354840d318d521032f4354840cb50d521023d6590840cb54a421032d52108408f596411032d5290440a758c411032d5210440a758f401032d52d00408fd95401032d52500409ed95401031d54cc730c755131cc2d8604c7309b98b548c26d62d5230c758e548c26e62152309b588548c31e5490e30b3189438c32e5494a30cb552528c32e5454a30cb551528c31e548ca30a7590328c31e540ca30d3548328c29d640c630a7593308c25d63951309bd89544c26c62551309dd85544c27461551308f990524c23d64149308f990514c23d641453097997314c2d8604c5309b988540c26d62150309d984540c27561150308f992530c23d6494c3097596430c2cc6250c308fd91520c23c6454830a7590320c2d9600c8308fd91510c23c64544309bd89510c26c625443097596310c29d640c4308f992500c23d6494030a7593300c25f654c0309ed95300c25e63153209758c54c823f6454f208f19153c823e6414f208f59
  | 2 => 0x52fa0009e9cd2566a06019028e3540001b3be340499b53560007986021e440010000be2bc1c2053da0001c8eb29e59cbc043408000419ee0006b86492a1c2414000000006e90609c04e2747b87b1fe548548000005e40ca023e4468ea0072d21703f9d5066068b307637e28c042130aa0005a12f4324888e0e407a5905296c19a000000fb00002cd9800000000000952244dc6901e0004440018c1d0000001ff0004cccc93b31c3d82083e0ca430000000006484f1db2a819c000003fa000e3800000000a61080000c50b0aa2c4000a4000000054a693a1bc3c82d90d1d8000001600927645a9732e05f02d0003762f00298f1ea000531590500b4c380016c824bd9142da1c8618ce038044f515c18a78c068000005083080007e3300004a000004090081300c08008180000a0000f01c0f0000e0000007803004050280300c0700024000000001c0080400008000020000002c00000020180201007000040540800c0400005000150440b0040001405000000040100c0e0100d0040a06805020000080201004004010000500407004020640b000030400001400018080780000c0700000044010600500003018010182f0100700400004000100000002000050081401003028050200000c0300000010050080d0180404c020081100c0000417000000040b00c050140100c0303000024010140201c010180000805018030326f62546439b1895190e6e62942439b58a5090f4f4314943cb90c5250e3f6550c43ab1894310e5f6550c43b31894310eac6250f429798e5190a5d639464297d8d5090a5c63542428f9974350b1c53d0d42c714d4350aac6250d42d314f4250b1c53909428f5964310a3f6550842a718d4210a6f6550842b318d4210a7661153329d58454cca3f64547328f19151cca3e64943328f59250cca7a60152329e580548ca3e64946328f592518ca3f64542328f191508ca3e649513297d8d544ca6f62551328f994544cb2c54cc932c7152324ca3d6595032c718d540cb2c62550328f990540cb1d54d0c3297594430cb2d54d0832e3d0f420ca6d6510832e310c420ca5f654c832a7191320ca6f654c832ab191320caac6250f4197d8d52d065c6354b41d3d8d52d074c6354b41cbd0d52d072d4354b41cb54a42d072d5210b41a718d42906ad62d064197d8d509065c63542418f99743506ac6250d418f994425066e62141419b588505066f6254c419b189531074f6254c41d3189531063d6590c41c754e431071d5310c41c754f421063f6550841a718d421071d5350841c754f41106ad62d04418fd95411071d53504419dd95411066e62153319b58854cc6cc6250f318fd9152cc63c6454b31a759032cc63e64943318f59250cc66e62943319b58a50cc66e62d52319b58b548c63e6494a318f592528c63f64542318f191508
  | 3 => 0x749681d400010800382000001cc3b8860cf15a0002a0cb0000001783e000000000f81001322390380013034ca080005e0c84002930c08cb880012c000431d20d87380005024c000000871907cc639b222c27cfc0570a67dc59a110ba2b400094310318771941428542692e2a0190e11ec3d66b4000002b60501b177134038af0542320000000006a6f42b000054000001a900000000000000000050001128683a801000090d8800196000001c31c03e4081810000009c03a0f085c0000038847c4b800414244340000001880000015c0600195f0e61301a1b8344398899981740000000000000000000000000000003145fc001d61ae6d0fe214000000b08a43de8180011e35e74000000000000ff0000a2000b916f1ac800001e21e25d4c007427c4c8949581a86144106f3ea07cec0002920006898b3d222c83816312000db19d17a1a4021741be000000000a45f90782020c778e40003e2374bd1d1000514091462963943719a420098fa10210a000a51a012050c719830005b80019321c074000002ca42400130000000460001024a05d9aa0f4574ee8460007d88b9273081dcaaa0e0f248c5b8003ca12c7d12038a6dcd800000029cd28000004d4fd9150004d8d08001b082c4d93c2064c40014e2ae23c220000806f0d30001fc328001e8000474001ac08e46c679be0fc4282406a0001c4d186b0000f0000001082b0160db3361608594000065c380001f04d0ab1b932269c061cf2023880002525a39c0008d09e4fceb800000108f380041a0000008a1407903e8b20da0010900000072c00006380634920fc0cc310000ab0004945c982012000a20ed1843bd018a21b4728000fd1e87249c96b0006900983b09c2c0319213c07182c9da1702f8000302a28206c99c05c3045f9041b805ccaa013a6460bb03712458cfd02233e0ac000b13c254c9616a3cc000078001e0220fc84
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x60000735600000254e44901200800f0005130403045ca2c31404001818400e4000098318c6255032a18e6a9085a0d0c7254c4310706a9ac5a0883431c9631513183aec2a06498d487250c504c68cba0642826386550604c431a18e6b14a910c2d769503288686392a621e818354d62d0740a18e6a90842060d635484110306b1aa5a008186550604c730a18e4b1ca91841d76950328c28639ac42a2410b5d8540c920a88e6a10a290525740c85148312b20a390a41895506148020
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x5a080c8754d62d044180c8754d62d074080c8758d521044080c8758d52d0040
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
  | 2 => 4
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s4K7 (i*5) 5
  | 6 => packedAt s4K6 (i*16) 16
  | 5 => packedAt s4K5 (i*27) 27
  | 4 => packedAt s4K4 (i*38) 38
  | 3 => packedAt s4K3 (i*49) 49
  | 2 => packedAt s4K2 (i*60) 60
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s4K7 (6+((h/1+packedAt s4K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s4K6 (731+((h/13+packedAt s4K6 (640+(h % 13)*7) 7) % 69)*7) 7
  | 5 => packedAt s4K5 (20138+((h/221+packedAt s4K5 (17928+(h % 221)*10) 10) % 797)*11) 11
  | 4 => packedAt s4K4 (22272+((h/179+packedAt s4K4 (20482+(h % 179)*10) 10) % 711)*11) 11
  | 3 => packedAt s4K3 (1273+((h/8+packedAt s4K3 (1225+(h % 8)*6) 6) % 37)*6) 6
  | 2 => packedAt s4K2 (243+((h/1+packedAt s4K2 (240+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xe07ffe07ffffff81fffff81ff83ffffcfe31ff
  | 1 => 0xfffffff81ffffffe07c0ffffffc1ffff23fe3f
  | 2 => 0xff80ffffe03f83fff800ffe0fffe1e03c3cfcc
  | 3 => 0xffffffc003ffffff0000ffffe003fc0ff0
  | 5 => 0xffff0000000003ffffffffff00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x290a22310489208059492909281232a84e10d5
  | 1 => 0x42144440c9124116029052325241455120e62a
  | 2 => 0x8526a89243a426aaa8289d489cb4181ac34b4c
  | 3 => 0x1658d12492074b4d34f20610e7298063b40db0
  | 5 => 0x1860e1c71c3873f1c73ce79c06311183fbb000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xeac8eac8e888e888eac8eac8e888e888eac8eac8e888e888eac8eac8e888e888eac8eac8e888e888eac8eac8e888e888eac8eac8e888e888eac8eac8e888e888, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_16433
namespace PEqualNP.Outside.L_meta_16433
open PEqualNP.Outside.L_meta_16433.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x3e38e8a00a0b1c061c08d005001e22005a330193822a008292410caa4c3cd1342900250a2002b4425000006cb8c000c001d043002050000040ff43fe43fd43fc43ff42fe42ee42fd42ed42fc42ff32ef32fe32fd32fc32ec32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x2ba90a9caa000018a3000d800900000a1b99870e00001a00000013868027000500132000012ca48320800b001580181000021080081e1d24000000038026a380229d801600151c002b21802a878012889f2597148280260004801e800c8000000001802100059680001b2800002c0c0f8004288000250000000e860000919217800b89801fa99911221a80140d278f0041004000808140000203408000018000000180008040000000008000c02dca5a1db54b43bb28e877551d0edea4a1db14943b7290876d5210edaa9215b94e42afa9a855c5350b5ea8a173d4d42b629a85cc5350a98a6a16bd0d42d6a1a856e5210adea9995b55332b7294653e540ca7aa8195bd5032d72a0656d540cb5aa8194b55032b729865ce530cb9e86197310c32af29e835d53d06dca5a0db54b41d6a1683ad42506dca420db548419f2a4633d548c6dca518db54a31e6194636f524c6d8a498f30c831afa9a435c534867ca810cf55021b7296816d52d035a85205794c40aea98816e52102daa4206b50840bb2888175511039865985b94a30b6a94613f544c278a8985bd4930b629261cc324c2eea2985d145309f2a6413d54c82bca7105754e209faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x22780b20c121ae62a58442401a5000023a822600028c7005025004270c53d0d42a95874350a2d6595032c318d540cb0d54d0c32b1987430ca4d6510c32a318d42d070d5350b41a318d425064c6354841a3590328c70e540ca318b590524c68d640c8319318d52d028c6350a40a318d421030d5350840c9509511028d640cb308b592528c28d640c930c3150324c3443214530
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x864200a070229ac3a1a858155261d0c3281aed2a06518d04735095110206bb0a819261415d03214530
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 90
  | 3 => 25
  | 2 => 6
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
  | 5 => packedAt s5K5 (788+((h/14+packedAt s5K5 (704+(h % 14)*6) 6) % 53)*7) 7
  | 4 => packedAt s5K4 (2670+((h/30+packedAt s5K4 (2430+(h % 30)*8) 8) % 143)*8) 8
  | 3 => packedAt s5K3 (990+((h/8+packedAt s5K3 (950+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s5K2 (300+((h/2+packedAt s5K2 (294+(h % 2)*3) 3) % 8)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xffffffe07fffff03fe0fffffff07fffc8ff1ff
  | 1 => 0xe07f07ff83fffffc1ff0f0781ff87fff724e3f
  | 2 => 0xff8007fffc0fc3ffe000ff801fff8f03838fcc
  | 3 => 0x7fffff003ffffff00001ffff003fc0ff0
  | 4 => 0xfffff800000003ffffffffffe0000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x220a00230020800062011088c50091280490d5
  | 1 => 0x49144a441945212c0c9064510a482ad132462a
  | 2 => 0x8526d68928ea2755a188bd4253d50c1b838b4c
  | 3 => 0x1658a51252838a9ad72a08049ca64062dc0db0
  | 4 => 0x1860c61c630c33e319ccce6700c40883eb6000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xeeaae888eeaae888eeaae888eeaae888eeaae888eeaae888eeaae888eeaae888eeaae888eeaae888eeaae888eeaae888eeaae888eeaae888eeaae888eeaae888, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_16433
namespace PEqualNP.Outside.L_meta_16433
open PEqualNP.Outside.L_meta_16433.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c381821404000040850002380850000001017fd5005fe54017f55005fc5401ffd4c01fe53007f54c07fc53017fd0c05fe43017f50c05fc4301ffd4803fe52007f54803fc52017fd0803fe42017f50803fc42007fcc803fe32007f4c803fc3201ffd4401fe51007f54407fc51017fd0405fe41017f50405fc41007fcc401fe31007f4c401fc3100ffc8401fe21007f48403fc2101ffd4001fe50007f54007fc50017fd0005fe40017f50005fc40007fcc001fe30007f4c001fc3000ffc8001fe20007f48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a2000dfd9510004feca88033fe65440077f32a2000ff59510005faca88033fc65440077e32a2000df1951001cf8ca8802fff64440177fb222000efd91100057ec88802ffe64440057f322200bff5911005dfac88802ffc64440057e322200bef1911001578c88802fff5444017ff2a2200bff5511005ff8a888003ff63440017fb1a2000f7d8d10005bec688003fe63440017f31a2000ff58d10005fac688003fc63440017e31a2000f718d10005b8c688033ff5344001ff29a2000ff54d10067f8a68802fff4344017ff21a200bff50d1005ff88688003ff62440017fb122000fbd8910005dec48802bfe62440037f3122000ff58910005fac48802bfc62440037e3122000fb1891000dd8c488033ff5244015ff2922000ff54910057f8a48802fff4244015ff212200bff50910057f88488003ff3244015ff1922000ff4c910057f86488033ff5144001ff28a2000ff54510067f8a28802fff4144017ff20a200bfd9051005ffa828802ff54144017fe20a2000ffcc510007fc6288003fd3144001fe18a200affc8510007fc4288003fd2144015fe10a200cffd4110007fca088003fd5044019fe282200bffd011005ffc808802ffd4044017fe2022000ffcc110007fc6088003fd3044001fe182200affc8110007fc4088003fd2044015fe1022000ffc4110007f62088003fe1044001fb0822004ffd9410005feca0801ffe65040077f3282000df9941001cfcca08003fd65040017eb282000df59410004faca08013fc65040077e3282004ffd9010035fec80801bfe64040057f3202006ef990100157cc80801bfd640400d7eb202000ef590100057ac808013fc64040057e3202006ffd5010037fca80801bfd540400dfe2a02004ffd8c10005fec608003fe63040017f3182000f798c10005bcc608003fd63040017eb182000f758c10005bac608013fc63040017e3182007ffd4c10007fca608003fd530400ffe2982006ffd0c10037fc860801bfd430400dfe2182004ffd8810005fec408017fe62040037f3102000fb9881000ddcc408003fd62040017eb102000fb58810005dac408013fc62040037e3102007ffd481002ffca408003fd520400bfe2902006ffd081002ffc840801bfd420400bfe2102000ffcc81002ffc6408003fd320400bfe1902009bf9841003ffea208003fe5104001fea882007ff14410037fe820801bfe410400dfea082006ff10410007fe6208003fe3104001fe9882000ff0c41002ffe4208003fe2104001fe9082005ff08410045fcc00801fff5004009ff2802000ff54010027f8a00801bff4004009ff2002006ff50010027f88008003ff3004009ff1802000ff4c010027f86008017ff2004009ff1002000ff48010027f84008003ff1004001fb8802004ff84010007f42008003fd1004001fa8802000fe44010
  | 1 => 0x3fe5148001fea8a4012ff1452008ffe8290047fe4148023fea0a4011ff10520007fe6290003fe3148001fe98a4000ff0c52000ffe4290007ef2148003ff10a4001ff48520007da4290007fc21480037fb024012ffd4120007fca090003fd5048025fe2824011ffd012008ffc8090047fd4048023fe2024000ffcc120007fc6090003fd3048001fe1824001ffc812000ff64090007fe2048001f71024001ff0812000fd84090007f82048001ffb2e2000bfd9710087fccb8800efe65c4001feb2e2000bf59710087f8cb8800efc65c4013ffb262009bfd931004ffcc98800afe64c4013feb262009bf5931004ff8c98800afc64c4013ffaa62009ff9531004ffaa988027fc54c4001ffb1e2000bfd8f10007fcc788002fe63c4001feb1e2000bf58f10007f8c788002fc63c4021ffa9e2000ff94f10007faa788043fc53c4013ffa1e2009ff90f1004ffa8788027fc43c4001ffb162000bfd8b1007ffcc588006fe62c4001feb162000bf58b1007ff8c588006fc62c4021ffa96200fff94b10007faa58803ffc52c4013ffa16200fff90b1004ffa858803ffc42c4001ff996200fff8cb10007fa658803ffc32c4021ffa8e2000ff94710007faa388043fc51c4013ffa0e2009ff9071004fec8388027fd41c4013faa0e2009ff10710007fe6388003fe31c4001fe98e2000ff0c71007ffe4388003fe21c4001fe90e200fff08710087fea188003fe50c4001fea862010ff1431004ffe8188027fe40c4013fea062009ff10310007fe6188003fe30c4001fe9862000ff0c31007ffe4188003fe20c4001fe906200fff08310027fecb08002ff658401dff32c2003bf99610007facb08002fd6584009fe32c2003bf19610027fec908022ff6484011ff3242002bf99210047fac908022fd6484009fe3242002bf19210047fea908023fe5484011feaa42008ff15210027fec708002ff6384001ff31c2000bf98e10007fac708002fd6384009fe31c2000bf18e10077fea708003fe5384001fea9c200eff14e10047fe8708023fe4384011fea1c2008ff10e10027fec508002ff628401bff3142001bf98a10007fac508002fd6284009fe3142001bf18a10077fea508037fe5284001fea94200dff14a10047fe8508037fe4284011fea14200dff10a10007fe6508037fe3284001fe994200dff0ca1005dfac30803bff5184001ff28c2000ff54610077f8a308023ff4184011ff20c2008ff50610047f88308003ff3184001ff18c2000ff4c610007f86308037ff2184001ff10c2000ff4861006ff8430801afe608401dffa842004ff94210007faa108013fc5084011ffa042004ff90210047fa8108013fc4084001ff9842004ff8c210007fa6108013fc308401bff9042004ff88210007fa4108013fc2084001ff8842000fdc4210007f62108003ff65440017fb
  | 2 => 0x300b7fc861805ffd430c02dfe2186004ffd88300affcc418006fe620c001feb106000bf58830027f8c418006fc620c031ffa906015ff94830007faa418057fc520c02fffa106015ff908300bffa8418057fc420c02dff9906015ff8c830007fa641805bfc320c009ffb086000ff98430005fcc218003fd610c0017eb086004ff184300c7fea218003fe510c001fea886018ff144300bffe821805ffe410c02ffea086017ff104300b7fe6218003fe310c001ef1886000ff4c4300b7f86218003dc310c02bff9086000ff88430007fa4218057fc210c0337f3006018ffd4030027fca018003fd500c009fe2806017ffd0030027fc801805ffd400c009fe2006016ffcc030007be6018013fe300c001fd1806000ff4c030007ba6018003f9300c02bff9006004ff08030027fecb10002ff6588029ff32c4003bf99620007facb10002fd6588009fe32c4003bf19620027fec91004eff6488027ff3244002bf9922009ffac91004efd6488009fe3244002bf1922009ffea91004ffe5488027feaa44013ff15220027fec710002ff6388001ff31c4000bf98e20007fac710002fd6388009fe31c4000bf18e200a7fea710003fe5388001fea9c4014ff14e2009ffe871004ffe4388027fea1c4013ff10e2000dfac510007ff5288003ff2944001ff54a2000ff8a510007ff4288003ff2144001ff50a2000ff88510007ff3288003ff1944001ff4ca2000ff86510013ff6188001ff30c4000bf98620007fac310002fd6188009fe30c4014ffd4620007fca310003fd5188029fe28c4013ffd062009ffc831004ffd4188027fe20c4000ffcc620007fc6310003fd3188001fe18c4001ffc862000ffc4310003ee2188003fe90c4001ff0862000fd84310006fe6088029ffa844004ff94220007faa110013fc5088027ffa044004ff9022009ffa8110013fc4088001ff9844004ff8c220007fa6110013fc3088003ff9044001fbc822000ff64110013fc2088003fc1044000ffd9520005feca900037f65480013fb2a4012ff9952001dfcca90003fd65480017eb2a4012ff1952001df8ca900037c65480073e32a4011ffd912008dfec890047fe64480057f3224011ff5912008dfac890047fc64480057e3224011ffd512008ffca890047fd5448023fe2a24000ffd8d20005fec690003fe63480017f31a4000ff58d20005fac690003fc63480017e31a4012ffd4d20007fca690003fd5348025fe29a4011ffd0d2008ffc8690047fd4348023fe21a4001bfd892000ffea490007fe5248003f72924001ff54920007daa490007fc5248003ffa124001ff9092000fdc8490007fd4248023f6a124001ff1092000ffe6490003ef3248003ff1924001ff4c92000ff86490007ec3248001ffb0a4000bfd8520007fcc290003fd6148001fe30a4000bf18520097fea29000
  | 3 => 0xe10e6021ffd4330007fca198003fd50cc043fe286601affd03300d7fc819806bfd40cc035fe2066020ffc8330107f84198013ff658c0017fb2c601fff9963001dfccb180037e658c0073f32c6000ff59630005facb180037d658c0013eb2c6004ff1963001df8cb18013ff648c0337fb246019ff99230015fcc918067fd648c0337eb246004ff19230015f8c918067ff548c033ff2a46019ff552300cff8a918072fd638c03fffa9c6000ff94e30007faa71807ffc538c033ffa1c6019ff90e300cffa8718067fc438c009ffb14601eff98a3000dfcc518003ee628c003773146000ff58a30005fac518003ed628c00176b146004ff18a3000df8c51807fff528c03dff2946000ff54a300f7f8a518067ff428c03dff2146019ff50a300f7f88518003ff328c03dff1946000ff4ca300f7f86518013ff618c001ff30c6000bf98630007fac318002fd618c009fe30c601fffd4630007fca318003fd518c03ffe28c6019ffd06300cffc8318067fd418c033fe20c6000ffcc630007fc6318003de318c001fe98c6000ff0c630007b8631807bff218c001ff10c6000ff486300f7f8431805efe608c03fffa846004ff94230007faa118013fc508c033ffa046004ff902300cffa8118013fc408c001ff9846000f7cc230007f6611807bff208c009fe1046000ffd9530005feca98077fe654c0077f32a6000ff59530005faca98077fc654c0077e32a601cffd91300e5fec898003bf644c0015fb22601cff99130015fcc898073fd644c0397eb22601cff19130015f8c898073bc644c0055e322601cffd51300e7fca898073fd544c039fe2a2601dffd4d30007fca698003fd534c03bfe29a601cffd0d300e7fc8698073de434c039fea1a601cf750d300e7f88698003ff624c0017fb12601bff9893000dfcc498003fd624c037fe3126001bf189300effea49806ffe524c001fea92601bff149300e7fe849806ffe424c039fea12601bff10930007fe649806ffe324c001fe992601bff0c930007fec298002ff614c001ff30a6000ff58530007f8c298002fc614c03bffa8a6000ff94530007faa298077fc514c039ffa0a601cff905300e7fa8298073fc414c001ff98a6000f7cc530007fc6298003fd314c001ee98a6000ff0c5300dffe4298003fe214c001fe90a601bff085300effea098003fe504c001fea82601dff141300e7fe8098073fe404c039fea02601cff10130007fe6098003fb304c001ff1826000f78c1300dffe409806ffc204c009ffb286000bfd94300c7fcca1800efe650c001feb286000bf59430027f8ca1800efc650c009ffb206017bfd90300bffcc81800afe640c02ffeb206017bf59030027f8c81800afc640c02fffaa06017ff950300bffaa81805ffc540c0357f3186018ffd4c300b7fca618003fd530c02dfe2986017ffd0c
  | 4 => 0x6fe6294001feb14a000bf58a50027f8c528006fc6294007ffa94a003ff94a50126fca52800ffd5294007fe294a003df14a5012ffe8528093fe429404bfea14a024ff10a50007fe6528093fe3294001fe994a024ff0ca50027fec328003fe61940017f30ca000ff58650005fac328013fc6194007ffa8ca003ff94650006fca32800ffd5194007fe28ca003df1465012ffe8328097fe419404bfea0ca025ff10650007fe6328003fe3194001fe98ca000ff0c650127fe4328003fe2194001fe90ca024ff0865001dfcc12800fff5094007bfa84a003fed4250027f8a12800ff8509404bffa04a004ff9025012ffa8128013fc4094049ff904a004ff0825001dfecaa808fff64540477fb22a023ff99150015fcc8a808ffd64540477eb22a023ff19150015f8c8a800fff5454007bfaa2a003ff9515001ffaa8a808f7d5454007fe2a2a000ffd8d50005fec6a8003fe6354001feb1aa000ff18d50005f8c6a800fff5354007ff29aa000df94d5001ffaa6a800ffc5354007be29aa023ffd0d5011ffc86a808ffd4354047fe21aa000ffd8950005fec4a808bfe62540037f312a000ff58950117f8c4a8006fc6254007ffa92a003dfd495001ffca4a800ffd5254001bea92a003ff1495011ffe84a808bfe4254047fea12a022ff10950007fe64a808bfe3254001fe992a022ff0c950007fec2a8002ff6154001ff30aa000ff58550007f8c2a8002fc6154007ffa8aa003dfd455001ffca2a800ffd5154001bea8aa003ff1455011ffe82a808ffe4154047fea0aa023ff10550007fe62a8003fe3154001fe98aa000ff0c550117fe42a8003fe2154001fe90aa022ff0855001dfec0a800fff5054007fda82a003ff94150006fca0a800ffc5054007be282a003fe1415011ffe80a808ffe4054047fea02a023ff10150117fe40a808bfc205402dffb2e6000bfd973010ffccb9800efe65cc001bf32e60039f99730007facb98002fd65cc001beb2e60009f597300b7f8cb9800efc65cc02dffb26601abfd93300d7fcc99800afe64cc035feb26601abf593300b7f8c99800afc64cc035ffaa6601aff953300d7faa99806bfc54cc043ffa9e6016ff94f30007faa79805bfc53cc035ffa1e6016ff90f300d7bc879806bfd43cc035eea1e6016ff10f300b7fec598083fe62cc0037f3166000ff58b30005fac59805bfc62cc0037e3166021ffd4b30107fca598003fd52cc041fe296601affd0b30107fc859806bfd42cc041fe2166016ffccb30107fc6598003fd32cc02dfe1966016ffd8730007fcc398002fe61cc001feb0e6000bf587300b7f8c398087ff51cc001ff28e6000ff5473010ff8a39806bff41cc035ff20e601aff507300d7f8839805bff31cc001ef98e6000ff8c730007fa6398003dd31cc02dfe18e6020ffc8730007fc4398003fd21cc041f
  | 5 => 0x84310b7fec018803fe600c4017f3006200ff58031005fac01885bfc600c459ffa80622cff1403115ffe80188affe400c457fea00622bff10031157fe40188abfc200c401ffb2c4200bfd962114ffccb1080efe6588401bf32c42039f99621007facb10802fd6588401beb2c42009f5962114ff8cb1080efc6588451ffb244228bfd9221147fcc91080afe6488451feb244228bf59221147f8c91080afc6488451ffaa44228ff95221147faa9108a3fc5488401ffb1c4200bfd8e21007fcc710802fe6388401feb1c4200bf58e21007f8c710802fc6388453ffa9c4200ff94e21007faa7108a7fc5388451ffa1c4228ff90e21147fa87108a3fc43884037eb144201ffd4a2100ffca510807ee5288403fea944200fb54a2100ff8a510807ff4288403ff2144201fb90a2100ffa85108a3ed4288403fe2144201ffcca21007de6510807fe3288403fe9944201ff0ca2100fd86510806fe6188453ffa8c4200ff94621007faa3108a7fc5188451ffa0c4228ff90621147fa83108a3fc4188401ff98c4200ff8c621007fa6310803fc3188403ff90c4201fbc862100fee4310807fc2188403fa10c4200ffd8221007fcc110802fe6088401feb044200bf58221007f8c1108a7ff5088453fe2844228ffd0221147fc81108a3fd4088451fe2044201ffc822100ff84110807ec2088401ffb2a4200bfd952113ffcca9080efe6548401feb2a4200bf5952113ff8ca9080efc654844dffb224226bfd9121137fcc89080afe644844dfeb224226bf59121137f8c89080afc644844dffaa24226ff95121137faa89089bfc5448401ffb1a4200bfd8d21007fcc690802fe6348401feb1a4200bf58d21007f8c690802fc634844fffa9a4200ff94d21007faa69089ffc534844dffa1a4226ff90d21137fa869089bfc43484037fb124201ffd492100ffca490807fd5248403fe2924201ffd092100ffc8490807fd4248403fe2124201ffcc92100ffc6490807fd3248403fe1924201bfd852113ffea290803fe5148401fea8a4227ff14521137fe829089bfe414844dfea0a4226ff10521007fe6290803fe3148401fe98a4200ff0c52100ffe4290807f72148403ff10a4200fb8852100ff84290807ec2148403fa10a4200ffd8121005fec090803fe6048401feb024200ff18121005f8c09089fff504844ffe2824226ffd0121137fc809089bfd404844dfe2024201ffc812100fde4090807fc20484077eb2ca004ffd925012dfec928097fe64940057f324a025ff5925012dfac928013fc64940057e324a003ffd525001ffca92800ffd5494007fe2a4a004ffd8e50007fcc728002fe6394001feb1ca000bf58e50027f8c72800fff5394007bfa9ca003ff94e5001ffaa7280037d5394007fe29ca025ffd0e5012ffc8728097fd439404bfe21ca004ffd8a50127fcc528
  | 6 => 0xb7eb246200ef592310057ac9188b7fc648c4057e324622dffd523116ffca9188b7fd548c45bfe2a46230bf58e3119ffea718803fe538c401fea9c6233ff14e3116ffe87188b7fe438c45bef21c622dff50e3116fba87188b7fc438c401ffb146232ff98a3100dfcc518803fd628c4017eb146232ff18a3100df8c5188cfff528c465ff2946200ff54a31197f8a5188b7ff428c465ff214622dff50a31197f88518803ff328c465ff1946200ff4ca31197f865188aefe618c467ffa8c6200ff94631007faa3188cffc518c45bffa0c622dff9063116ffa83188b7fc418c401ff98c6200f7cc631007ee63188cbff218c465fe10c6200ffd8231007fcc118802fe608c401feb046200bf58231007f8c1188cfff508c467fe284622dffd023116ffc81188b7fd408c45bfe2046232ffc8231197f84118803ff654c4017fb2a6200dfd9531004feca988c7fe654c4077f32a6200ff59531005faca988c7fc654c4077e32a6200df1953101cf8ca988c3ff644c4617fb226230ff99131015fcc8988c3fd644c4617eb226230ff19131015f8c8988c3ff544c461ff2a26230ff55131187f8a8988c7ff534c401ff29a6200ff54d3118ff8a6988c3ff434c461ff21a6230ff50d31187f88698803ff624c4017fb126200fbd8931005dec4988bffe624c4037f3126200ff5893117ff8c498806fc624c401f63126201bb1893118ffea4988bffe524c401fea92622fff14931187fe84988bffe424c461fea12622fff10931007fe64988bffe324c401fe992622fff0c93118ffea298803fe514c401fea8a6231ff14531187fe82988c3fe414c461fea0a6230ff10531007fe6298803f7314c401ff18a6200f78c53117ffe42988bffc214c401ffb026200bfd8131007fcc098803fd604c401fe3026200bf1813118ffea0988c7fc504c461ffa026230ff90131187fa80988c3fc404c45fff902622fff081310b7feca18802ff650c459ff3286203bf99431006fcca1880e7e650c401feb286200bf59431006faca188027d650c42dfe3286203bf194310b7fec8188aeff640c457ff3206202bf9903115ffac8188aefd640c42dfe3206202bf1903115ffea8188affe540c457feaa0622bff15031175fcc6188b3ff530c42dff2986200ff54c310b7f8a6188afff430c42dff218622bf790c3115ffa86188afdd430c42dfe2186216ffd8831157fcc418806fe620c401feb106200bf588310b7f8c418806fc620c459ffa90622aff94831007faa4188abfc520c457ffa10622aff9083115ffa84188abfc420c42dff990622aff8c831007fa641885bfc320c45b7f308622cffd4431007fca218803fd510c459fe288622bffd043115ffc82188affd410c457fe2086216ffcc431007be6218803fe310c401fb1886200ff4c431007ba6218803f5310c455ff908622aff0
  | 7 => 0x288037e5394407fea9ca203ff14e5101ef8a7288e7ff4394473ff21ca239ff50e511cff88728803ff6294471ff314a201bf98a51007fac528802fd6294471fe314a201bf18a5101ffea52880f7f5294407ff294a203ff54a51006faa52880ffc5294473ffa14a238ff90a511cffa85288e3fc4294401ff994a238ff8ca51007fa65288e3fc32944077f30ca203ffd465101efea32880ff75194407fe28ca203fd146511cffe83288e7fe4194473fea0ca239ff106511c7fe43288e3fc2194401ffb04a200ff98251005fcc128803fd60944017eb04a200ff1825101ffea12880ffc5094407be284a239ffd02511cffc81288e7fd4094473fe204a238ffc82511c7f8412880eff655446fffb22a237bfd91511bffcc8a880afe645446ffeb22a237bf591511bff8c8a880afc6454407ffaa2a203ff9515101ffaa8a880ffc5454401ffb1aa200bfd8d51007fcc6a8803fd6354401fe31aa200bf18d5101ffea6a880f7f5354407ff29aa203ff54d51006faa6a880ffc535446fffa1aa237ff90d511bffa86a88dffc4354401ffb12a200bfd89511b7fcc4a8806fe6254401feb12a236ff1895100df8c4a880fff5254407ff292a236df9495101ffaa4a880ffc5254407be292a237ffd09511b7fc84a88dffd425446dfe212a200ffcc9511b7fc64a8803fd325446dfe192a203bfd855101ffea2a880ff75154407ff28aa200df9455101ff8a2a880f7c5154407fa28aa237ffd05511bffc82a88dffd415446ffe20aa236ffc85511b7f842a8803ff60544017fb02a200ff98151007fac0a8803fc60544017e302a203ffd415101efea0a880ffc505446fffa02a237ff901511bffa80a88dffc405446dff902a236ff081510b7fecb98802ff65cc46bff32e6203bf99731007facb98802fd65cc42dfe32e6203bf197310b7fec9988baff64cc45dff3266202bf99331177fac9988bafd64cc42dfe3266202bf19331177fea9988bbfe54cc45dfeaa6622eff153311affea79885bfe53cc401fea9e6216ff14f31177fe879885bfe43cc45dfea1e6216ff10f310b7fec5988d3fe62cc4037f3166200ff58b31005fac59885bfc62cc4037e3166235ffd4b311a7fca598803fd52cc469fe296622effd0b311a7fc85988bbfd42cc469fe2166216ffccb311a7fc6598803fd32cc42dfe1966235ffd4731007fca398803fd51cc46bfe28e622effd0731177fc83988bbfd41cc45dfe20e6234ffc87311a7f8439885bff60cc401ff3066200bf98331007fac198802fd60cc42dfe3066235ffd43311aff8a1988bbff40cc45dff206622eff50331177f881988d3ff20cc469fe1066200ffd9631005fecb188cffe658c4077f32c6200ff59631005facb188cffc658c4077e32c622dffd923116dfec9188b7fe648c4057f324622def992310157cc9188b7fd648c45
  | 8 => 0xfd495201fdea4a9007fe5254803bf292a401ff1495200ef8a4a9007ec5254803ffa12a401ff9095200ffa84a9007fc4254803ff192a401ff0c952007fec2a9002ff6154801ff30aa400ff58552007f8c2a9002fc6154807ffa8aa403ff1455201ef8a2a90fbff415487dff20aa43eff505521f7f882a9007ff2154803fe10aa401fb08552007fec0a9002ff6054801ff302a400ff58152007f8c0a9002fc6054807ffa82a403dfd415201ff8a0a90fbff405487dff202a43eff501521f7f880a9007ff2054803f7902a401ff081520b7fecb99002ff65cc87bff32e6403bf99732007facb99002fd65cc82dfe32e6403bf197320b7fec9990f2ff64cc879ff3266402bf993321e7fac9990f2fd64cc82dfe3266402bf193321e7fea9990f3fe54cc879feaa6643cff1533200dfcc7990f7ff53cc82dff29e6400ff54f320b7f8a7990f3ff43cc82dff21e643cff50f320b7f88799006fd62cc803ffa96643dfbd4b3200ffca599007fd52cc803fe2966401fb14b3200ffe8599007fe42cc803fea166401ff10b3200ffc6599007de32cc803f71966401ff0cb3200fb8659905bff61cc801ff30e6400bf98732007fac399002fd61cc82dfe30e643dffd47321eff8a3990f3ff41cc879ff20e643cff507321e7f88399007ff21cc803fe10e6401fb087320b7fec199003fe60cc8017f3066400ff58332005fac19905bfc60cc87bffa86643dff143321e7fe81990f3fe40cc879fea06643cff1033200ffe4199007ef20cc803fe1066400ffd9532005feca990037f654c8013fb2a643bff9953201dfcca99003fd654c8017eb2a643bff1953201df8ca990037c654c8073e32a643affd91321d5fec8990ebfe644c8057f322643aff591321d5fac8990ebfc644c8057e322643affd51321d7fca8990ebfd544c875fe2a26401bfd8d321dffea699003fe534c801fea9a643bff14d321d7fe86990ebfe434c875fea1a643aff10d3200dfec499007ff524c803ff2926401ff5493200ff8a499007ff424c803ff2126401fb9093200ffa84990ebed424c803fe2126401ffcc932007de6499007fe324c803ef1926401ff0c93200fb86499007ec324c801ffb0a6400bfd8532007fcc299003fd614c801fe30a6400bf185321dffea2990effc514c875ffa0a643aff905321d7fa82990ebfc414c803ff90a6401ff08532007fec099002ff604c801ff3026400ff58132007f8c099002fc604c877ffa82643bff141321d7fe80990ebfe404c875fea02643aff1013200ffe4099007fc204c8077eb2ca239ffd92511cdfec9288e7fe64944057f324a239ff592511cdfac9288e7fc64944057e324a203ffd525101efea92880ffe5494407feaa4a239df5525101ff8a928803ff6394401ff31ca200bf98e51007fac728802fd6394401fe31ca203ffd4e5101ffca7
  | 9 => 0x6800000a00400600000a02600600000600000200400000e00400808201200600200003000400200000200000a00c0bc00006400402201200000000a02600001205a00203800000600003c00400202000a00405400002c01000001a07c00201201c0180080b800000200601000000200200001c07600800000003200600600001200000000a00000a00200a01e00202601000000000000e00001c00000000c01401200404e01e0a001400201400001001200e00c00600001e00205603bf596530b7fec92990aff6494c85ff324a602bf99253217fac92990afd6494c2dfe324a602bf1925301ffea92980ffe5494c07feaa4a603ff1525301dfcc72980fff5394c07bfa9ca603f7d4e5301ebea72985bfc5394c07ee29ca642ffd0e530b7fc872990bfd4394c2dfe21ca616ffd8a5320ffcc529806fe6294c01feb14a600bf58a530b7f8c529806fc6294c07ffa94a603ff94a5320efca52980ffc5294c07be294a642ffd0a5320ffc852990bfd4294c83fe214a641ff8ca530b7f8652985bff6194c01ff30ca600bf98653007fac329802fd6194c2dfe30ca603ffd465301ff8a32980f7c5194c85ffa0ca642ff90653217fa832990bfc4194c83ff90ca641ff086530b7fec129803fe6094c017f304a600ff58253005fac12985bfc6094c07ffa84a603dfd425301ff8a12990bff4094c85ff204a642ff50253217f88129907ff2094c83fe104a603bfd9553207fec8a9902ff6454c81ff322a602bf99153207fac8a9902fd6454c81fe322a602bf1915301ffea8a980f7f5454c07ff2a2a603ff55153206faa8a980ffc5454c077fb1aa603ffd4d5301fbea6a980ffe5354c01bf29aa603ff14d5301ef8a6a980fdc5354c81ffa1aa640ff90d53207fa86a9903fc4354c01ffb12a600bfd8953007dec4a9802ef6254c7fff312a601bf98953007fac4a98fffc6254c037e312a600fb1895300dd8c4a980fff5254c07bfa92a603ff9495301ff8a4a9903ff4254c7fff212a640ff509531fff884a98fffe3254c7ffe192a600ffd8553005fec2a9803fe6154c01feb0aa600ff18553005f8c2a980fff5154c07bfa8aa603ff14553207fe82a9903fe4154c81fea0aa640ff105531fffe42a98fffc2154c01ffb02a600bfd8153007fcc0a9803fd6054c01fe302a600bf1815301ffea0a980ffc5054c07be282a640ffd0153207fc80a9903fd4054c81fe202a63fffc81531fff840a9806ff655487dffb22a43ebfd91521f7fcc8a900afe645487dfeb22a43ebf591521f7f8c8a900afc6454807ffaa2a403ff9515201ffaa8a900ffc5454801ffb1aa400bfd8d52007fcc6a9003fd6354801fe31aa400bf18d5201ffea6a900f7f5354807ff29aa403ff54d52006faa6a900ffc535487dffa1aa43eff90d521f7fa86a90fbfc43548037fb12a401f
  | 10 => 0xa8000067a60c2158000e3c7ba0df075800000029f9a387d27502f600008340821c599a40005f5106086c68074a29700000000002b921247928651d6822cf9269009597a00004ba0000b780002601f88cdc41a7210000000c520000e694046ce86a3ea0fec3960e62a9800090000034788d890e36200000000000001089d1400207800000602a00600000600200200201200200004200600604e00600c00800a07400000400401201201600a00200c00200202000000600000000200a01a00002e00a00001600e00000400000c00402600c01407801200206a01600c03a00000000401c00a00401600400000801202c00600800c00800e02c01401800802800600000000001600c01600403602201c00e01400e00600200800000e00000201606400200000a01e00000a00600000202004e01200200000800201000408605c00000403e00000000000400000000000400400e01000200400c00000001c00a00806800002c00e00200000001800000002805a01800000000000600a00000c00000c00001600e00400c01c01603200000601000a01c02800202001400401800a01201a00007803a00601800200400c00800a03400a01c02c00800402e01000600800203400600600400000c01600200000a04200e00000c00c00000403001a01400001001a03c00402400200602e01a01600800603201801400a00207402400c04600403c00200400000800000001e00000200409600e00000000c00000c00601000400a04a01e0000040020620120640640040460dc00001a00200400e04000600200600801000a00004406800000c04000c00001e00402801a00001200e00200000a00001800201c00202001a01400000a00200600400800201a02e00200a00000000a01a00200000200003400800801c02400001a00000c01c00200000200600002200600e03404800000000204400001800e00000800200a00003200400000601400c00401614200000203a00202402600400400205600000600000000000000004c00e00001209c00200600a02200800000201a08a00200a00200800201e00600c00800000000000405400a00400a00400600800000000400802e00201800206a0180380000220000e402000e00001e00800400c0760060080ac00001204001c00601200000000400200000200000000200204c00001000001c00e00600400001804400000002a01200002800400403000a00600203a00800001800001000406c00001a04201004000000c01201a04800202000200801a01808e00200000400002400402401a00601802203400000001c01a00005803a00400600000000400000600001600400001a00003403001204000400003c03401000600000400203400c00c01600201c02000400000400601600800a00000200a00c0000000040
  | 11 => 0x300db64bc00010a0fe467612f80d018e4f329580000005c843e09340246551108fd878c6043980640b4816941193dc9da2e42a69ae015e23d0a395ccf966a438aa0d836c59c0490be0ca469d33a973cb5041430fa02c34e66239a0e1cb3c5273d3920d0688761511a9416680c0000970f2417c3a097d00000003e088b45ce00034c8be88187ab1dfa1b03ae6a30d40c28358000000030400080700015a4ece00042d1fc00004b80001be80000001812010b3000013b000054e46328d80908d026842e14749de6fd0f8078c75c15a3d19408c6431412b131810e53d15e98d4bf603e0c387b10e85d413393a4e6e61e36496650aa0b63a883f87042c719917dd01050f31e8a5c23000025a8e80abe0c805a04d00008181fc8c402382200038e9855a63f3e91cd41145953f68910f2a2a802f800451e2fb09e09ad0200001c41acc0004be155178026e4ab0f3976cb803cc30e21587b408f3e79c4c780303291000000000000000007ba7363a10000e241a121702340000000000bf816a5d215a90d07fe83e2398cc09b03ce11490581845ca2908848e9a76207a88a8e6606f1bb82c848a3d131c800023e0001d48000eb60003f21398d9601b05599cc4845fe12a881ccde00919392286f600007c062c27c6be00018e8aea11d3ad053c74e0000000a8070018f361835c9f64d10e18984338318305087c89e16f1718000a621b93d920500800000000c3c5760fc10a93c80927ca21f83810367ce0e083ec68c2d73bb0230b586361bf88cc23c4f03cb0c640003a80001e440000002ac1838de83601a6147ce380000000c7082059b000046c05e1ff0e70f20d521d21d2800000000025ba02800000034a981c78838a40f91350cc4210000000b462820b200000002592668000e9c6d40299734b025cc0001a506b827900000000005480e40d1c8c44d71e1a180e1c28c27a8c68fa01351671f4c6aa8580560be475e7b818912a8e1a50625000e08f057e2e11fb86123651bf03601f43e838818540cc280322901c10a59d4179e205144d420491a8ed03890e5210060000018097582ba3de00006505643c11040000bce0760cb9f34e9e78d324809cf605e33b780002d879a02a91c507600021a92ec3880003d78000f5263c32c934cd987493e88000000000000060850c54133d05f8e3a5403798fc0be276d09c13ac8e00003b9985c9204fe3c49190ace86d2b00fcd0f06d02f7892ce1e11432105802d641c3aa8c3805628702b0ccc058588112083c0200d30269cf018c3750798d5d0422b10d702402c22c30a28ca87d85841019b44b1e82033813840f2544289093c89c02614181403064fa17e9bd4c460e32a280184d25eb2b09ad83327fb29291c88a62ee0d012d827463e0c6185000081a02c8070db85ab00010f0cbe0000ae0cec7da0002d78000e960
  | 12 => 0x1cf1ee09004b600018a8000ec615104a05dc6d0785010978800a8380c89648dd261335f8374d8a46103594e404068624e130c6c20bf2ae1baca6851a4389ec4d880470ab182c4da72004b9e08e060780aa091c0764230be9470a746343410f082543ac2251314ca01780000110b8c70a00000000007690001df8e3445d0751064b9636d2dc040c32483315804c8aba1751da8f8cdcc00029614390060001010ca4ab41cc00017e455e00039591e471a00004f96fc00000005c9f3000043e22d18dcc7049e3101cb41427e31f0121800030d0661f64b923b315a0e7040028114a0180aa87c33289bec59a6f70820da87a601f40b9a8022e4cb12d1f141ca36c0f011ecd42153080026ce4a0cd1058baca700000000e105e200000012c4af8633000176800000010b8a74fd65200601144c3200006f005d01e28833c960c0000000000000f6e5fd1bd1bf83ca1f42070e5ceb83bc0dd9c9d07800034b84301383953ee0894c220703858420000688000000014e433000000000010e22a80000008393b087e01304d03cf87e80006580000000d785c400011645aa2c200000005ca3ee257a00463c00000c000000006d17a08100000001b180001746443d3123c72214c2f680000004c20e396f8f541c52d10bc89446c23209e5c00004a163079850a58028f13103445302b70d0894c27b00019a80107e121506f053c83f3cf0b2c5e63cd0f51ef0f167c7165033827a1092428e48a0a2321be9538d166210dd1380a5445e2e09f1884e58a377082400010503e06c00e41334010e38d3c4600000ba105c0002f290b46720000000bc0dc005802a163899c45b1f09fe81502842069978ac64fc14f8000c0a7c41a195fc9820c92449a6c30a4a90cd85c04c41f639890c416000b3f79be00004bd052800087a0002d6800094e15721800008b84b00a01d490384d51de92344f484d10e9b690903eb0000a44e5445400000007ce7be04f18a0e5017a1f517a44de45841e80000000002690b2481e48c32e0bf03fc3be0d1805032a3c53c717a8f7e0e93cda19cb9c772360983c658606435818c3c44a8228000003c16d2f200006a614914987f06085823bc14307be70833c000105a3a242c800097200004092947a815234b05fc0004c908ca16c0000000501464e585361fc1a680008291ad200007287b2da800085e0000000cd4c5e0ca2bd00000006ad000094062600012921bced43363f48e5021600000015c00000000001890b746ac000012c00035433f02989160000308000de000d09b0b00b284e841b92b8c944c81aea1c903c3cb00008885480000a1000009c7230001bfc656000131863465c21413e95e49c683102d10e86e269f0cf12fc0006dd19003b8d22869000128430077d3dc80000008054299fa0cc010d34e209472c0003ab964400065a3cc1
  | 13 => 0x20c8000668321951864c0cf1cc9b0089020a16a00b882213004c90989f003c3d71c880005d519282684607241a6915c91c0001a810a47ae1240b19774e7466b38280000fc0c41dc0000da602a235800902c59f407112c16e4a408101d000057d0000bdc06a7ec0af951c81409523d0e183f600036787843261280000ea80002b843c80004d456a000000000000000000000ce6b9044950c00000042e80000000000f40000b54000000000000000036b8e3c20c0002f989f0d4412641d104cf803062de0000ac8000000120400019d39f93888445372338c90a223d008390787200001d5902c4940003da800000000000704a4b200eb37e0f900082d81b70b3c0005c315980000000000000000ff87192de97640005502bc00000001c237103400000e10a18e1498e780080887096830830d9b2034c37915088d06a400023a95b01ee000000094ca120003f98b880841b219888e0c800b81288b80000622127212cd260003bb9f9c00041d21b05cc92a3490001100dc8223037145c58a54f3490edc0607da3de8a9800007f33b8000e0c31b236955c0004121099d0106a5a10e880000005d310b13d0aec165000102077212f1cd106ccd86d52a49820ffa08e28211d09b22dc0988fd04cc47e3ac1fdc82a6e72248ee8d7419f34c0d14ef418811d98589226271af89c85d22ac3188f3c24a7db00995bc8986892c38a3815a4ad0001e8099e4f911c81743de0321f282a42900690000b74fc468c1cf8c306ac21a32b9b602ce32d16c87250240ec3049bbc0000bb24e927c88852843d01e800035b0f58dbcdc221941380000007d82a5800108a3d6000074cc3a1711a400000001a411d09b908400000000009e212712f175c0000001640000000000000000000000038499c8d504453d41ed905823724c9dc40003663a19d740006713330000b347ff0bd96990120db0000000c1a0910001104106714000117ce7a78f12b8000ca800000000000000001da02b87426ea0000190a5e7320000c5cb720000000000934518000099051a0000421d981ce49615b8000edc00019198a8efe85700002c4c5861831286e00000861241e0c43002300002a8ed603a3ff19947647a42aa81049ca1ee3409e850608704289428a2a1593f001146b02ed0ef20982ec6c742f8dd02e47870d48458a786e31fa9ba00984562d983c08f83811cd97d80c45931b99c0478e5d00cc17c81fa0bc38013a8ab63fc18f8c1cb8e2df2b889fce8823e1829bc43807862560eec74884f3451b780344ec3cc965c486764251a1301e227802d9e94d1a63b365142ce760dc06284689940f43f301206ec85439f1e1030259602887f40fa7f52d3884100c7043d600008300000a720a03e42bc342811803a1792da15ec9c819a223832cdd87ea12c11f435e2e1185a18c67c33f3c99368abc
  | 14 => 0xe4ff26d96c8cba5a93f2a0900007ad0de80006702e60000000ebe4372dd800052c0003571be4c9800016b105cd62036223137ceac1a533d8cd0d9a07b2d81378c4c00000000001de0001b911a400050030d00003a074c2c698c00220681be0fbd0dc5fc07c8a24d6064806a8b44ff251027e8000ff003d09c85180001ed0c30bd4cac6b724d9630cc856b0df88190447262d88ff848c1dd4291848a645032931cb86d20002120000cdc15508a996cc8e0000511d801000003ee96b903a46f3f88000e0e84710700000002ff200a1dc4ca00016d8000cda0004230000aca2da1f11c6cbdc50814590e400000c23283a06220001248b4c0000730000bd8f281c626e8ae4a2c7463309680c9e33a09d87c50d045210f050436e22641500000003ca000089c6e012c2ab0d2cf3a58b20fa1d45a03b0249880503257432688fcce800021d8b109640002219544ada10f35e8fc831c7162e89bb431444223f9d9417a0933ef1f5892839d1cc0754c5c8410ea17c08cc36415703b4fae1d9088008802a16e06b1bc8c5a759138a0448707470001938d8c0030901ecc9084981178528f027c20ac0930cc623101f925c00011306f95dc0000a31a08058c964d600014ec0ea702216210c96623c02180008ec67c000052c03218902f090400006a3438c58fec0003729aec52a17400009dc29a33c11580000005862490000a520000001a1035a40400015643b80000000ae85320002440000b4a00000003fc706000355000000081500000000000000001d7800000011600006881da00018403620000000000f2003700021790880001fe9aac0007a23c50f6c0002a53e40d284fc1df04402f8a1a7114280dac4505e123606d40ee7542fd1eec1c440202b800024400006c81941a267f00006d03b626c2129d20d4c000427061064400f30001c45386f63ea96d800082b0000000acc00000000000000a434010805341440ec1588bb01f30000000d6a00028a000000080d13800005d800029204b42d400039787dc3c87701bc00003f24e74398ca0c563e639c1e30d067530ada1884e872912e8f484ea35904e800080c02923b999c9b876c005057827e3a31c603d8d4e77c1a703905367b41028ec4fe86031fb809473c1213bd8f54d68861088900c0001b30000a8cd9c2d22838000b1281312a14f853000030083c8ef252333e8000e185421af000000000027b0f6409e2be0f488d40002cc01400000b832f3ce00c4d642b614800007b00d20001b58bbe585019836880a5e629694d40a44823ef994ce2e2bf0b3100032c5de18e9b6445c2ef0b40d44c048642e29dd05d410a04b0e4c246292160830c8dc54a39c8aaca262732a614cc55284a01697fc69e3b636f954835632121907d40005b70001c7c9983fa0001918000000036058835477527704b8da45f838c
  | 15 => 0xbb800000000000000d42b40448d5
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe6488410006bd6488410006de6388410006dd638841000eee6288410006ed6288410025fa7088410005f9708841007cff764841013e7e65484100067d6548410136be6448410006bd6448410006de6348410006dd634841000eee6248410006ed6248410074ff765401001e7e65540100067d655401011ebe6454010006bd6454010006de6354010006dd6354010116ee6254010006ed6254010004fd76cc01003d7e75cc0100057d75cc01010e7e65cc0100067d65cc0100d6be64cc010006bd64cc0100b6de63cc010006dd63cc010106ee62cc010006ed62cc010004ff764c0100ee7e654c0100067d654c010005bf744c010035bc744c0100e6be644c010006bd644c010006de634c010006dd634c0100deee624c010006ed624c01006cff76480100057f754801003d7c75480100967e65480100067d654801008ebe6448010006bd6448010006de6348010006dd634801000eee6248010006ed62480100867e65c40100067d65c401004ebe64c4010006bd64c4010006de63c4010006dd63c401007eee62c4010006ed62c401007ef576c40100277665c40100277565c4010026f764c4010027b664c401023ef564c4010027b564c4010006b564c4010027d663c4010027d563c4010027e662c4010027e562c4010025f570c4010026f660c4010025f97684010026f9768401000cf976840100277a6584010027796584010027ba6484010027b96484010027da6384010027d96384010027ea6284010027e96284010235f9718401022efa6184010027f26184010004ff76440100057f754401003d7c75440100667e65440100067d6544010005bf7444010035bc744401005ebe6444010006bd6444010005df7344010005dc7344010006de6344010006dd6344010005ef724401002dec7244010056ee6244010006ed6244010025f77644010006f77644010004f77644010007777544010007747544010027766544010027756544010007b7744401021fb47444010026f76444010027b6644401021ef56444010027b56444010006b56444010007d77344010007d47344010027d66344010027d56344010007e77244010007e47244010027e66244010027e56244010025f77044010026f66044010027f25044010007f1504401021ff34044010027f04044010027f23044010007f13044010005fb7644010006fb7644010004fb76440100077b75440100077875440100077a6544010007796544010007bb744401021fb8744401021fba6444010007b96444010007db7344010007d87344010007da6344010007d96344010007eb7244010007e87244010007ea6244010007e96244010025fb7144010027f37144010226fa6144010007f26144010007f25144010007f1514401021ff3414401021ff04144010007f23144010007f13144010
  | 1 => 0x8810006ed7558810006ec7558810006ef7458810006ee7458810006ed7458810006ec7458810006ef5458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef5358810006ee5358810006ed5358810006ec5358810006ef4358810006ee4358810006ed4358810006ec435881002eef7158810006ee7158810006ec7158810006ef5158810006ec5158810006ef4158810006ee4158810006ed4158810006ec415881002eef7058810026ee7058810026ec7058810006ef5058810026ee5058810026ec5058810006ef4058810026ee4058810006ed4058810026ec4058810026ee3058810026ec3058810026ee1058810026ec1058810004ff7654810024fe7654810004fd7654810024fc765481001e7e65548100067d65548101f6be6454810006bd6454810006de6354810006dd635481000eee6254810006ed62548100b4ff76cc810024fe76cc810004fd76cc810024fc76cc8101ee7e65cc8100067d65cc8101e6be64cc810006bd64cc8100b6de63cc810006dd63cc81000eee62cc810006ed62cc810004ff764c810024fe764c810004fd764c810024fc764c8100057f754c81003d7c754c8101de7e654c8100067d654c8101d6be644c810006bd644c810006de634c810006dd634c81000eee624c810006ed624c810005f7714c810005f4714c810084ff7694410024fe769441001cfd7694410024fc769441001e7e65944100067d65944101cebe6494410006bd6494410006de6394410006dd63944101c6ee6294410006ed629441003f775194410025fa7094410005f97094410084ff765441001e7e65544100067d65544101bebe6454410006bd6454410006de6354410006dd63544101b6ee6254410006ed6254410004fd76cc4101ae7e65cc4100067d65cc410176be64cc410006bd64cc4100b6de63cc410006dd63cc4101a6ee62cc410006ed62cc410004ff768c410004fd768c41019e7e658c4100067d658c410035be748c410005bd748c41016ebe648c410006bd648c410006de638c410006dd638c410196ee628c410006ed628c410025fa708c410005f9708c410004ff764c4100057f754c41003d7c754c41018e7e654c4100067d654c410186be644c410006bd644c410006de634c410006dd634c410005ef724c41002dec724c41017eee624c410006ed624c4100b4ff760c410024fe760c410004fd760c410024fc760c41003d7e750c4100057d750c4101667e650c4100067d650c41015ebe640c410006bd640c4100b6de630c410006dd630c410156ee620c410006ed620c410007d5310c410025fa700c410005f9700c41007cff7688410024fe768841000cfd7688410024fc768841003d7e75884100057d758841014e7e65884100067d6588410146b
  | 2 => 0x4fd7518c100267d7518c100047d7518c10024fc7518c10024ff7418c10014fe7418c10026be7418c10014be7418c10004fd7418c10026bd7418c10004bd7418c10024fc7418c100b4fe7318c10026de7318c10004de7318c1000cfe7218c10026ee7218c1000cee7218c10004fd7218c10026ed7218c10004ed7218c10024fc7218c10004fe7118c10026f67118c10024fe7018c10026fa7018c100b4ff7694c10024fe7694c10004fd7694c10024fc7694c1001e7e6594c100067d6594c10216be6494c10006bd6494c100b6de6394c10006dd6394c1003f5f5394c1020eee6294c10004ff7654c10024fe7654c10004fd7654c10024fc7654c1001e7e6554c100067d6554c10206be6454c10006bd6454c10006de6354c10006dd6354c10005ef7254c1002dec7254c101feee6254c10005f77154c10005f47154c1001cfe75d88100267e75d881001c7e75d8810004fd75d88100267d75d88100047d75d8810024fc75d8810024ff74d8810014fe74d8810026be74d8810014be74d8810004fd74d8810026bd74d8810004bd74d8810024fc74d88100b4fe73d8810026de73d8810004de73d8810004fd73d8810026dd73d8810004dd73d881002cfd72d881007cfe71d8810026f671d8810024fe70d8810026fa70d8810004ed7698810026ef6598810006ee65988100276e65988100066e6598810006ed65988100276d65988100066d6598810026ec6598810026ef6498810006ee6498810027ae6498810006ae6498810006ed6498810027ad6498810006ad6498810026ec6498810026ef6398810006ee6398810027ce6398810006ce6398810006ed6398810027cd6398810006cd6398810026ec6398810026ee609881000cff76588100067e65588100067d6558810006be6458810006bd6458810006de6358810006dd6358810026ec6258810004ff755881001cfe755881001cfc7558810004ff7458810014fe7458810004fd7458810014fc7458810004ff73588100b4fc7358810026ef7258810006ef525881002eee525881002eec5258810006ef425881002eee4258810006ed425881002eec425881002eee325881002eec325881000cff715881000cfd715881002cfc715881002eec215881000cff7058810024fe705881000cfd7058810024fc7058810026ee2058810026ec2058810025ef765881002eef765881000cef7658810026ef6558810006ee65588100276e65588100066e6558810006ed65588100276d65588100066d6558810026ec6558810026ef6458810006ee6458810027ae6458810006ae6458810006ed6458810027ad6458810006ad6458810026ec6458810026ef6358810006ee6358810027ce6358810006ce6358810006ed6358810027cd6358810006cd6358810026ec6358810006ef7558810006ee755
  | 3 => 0xe3098c10026dc3098c10004dd7698c10026df6598c10006de6598c100275e6598c100065e6598c10006dd6598c100275d6598c100065d6598c10026dc6598c10026df6498c10006de6498c100279e6498c100069e6498c10006dd6498c100279d6498c100069d6498c10026dc6498c10026df6298c10006de6298c10026dc6298c100b6df7598c10006de7598c10006dd7598c100b6dc7598c100b6df7498c10006de7498c10006dd7498c100b6dc7498c10006df5498c10006de5498c10006dd5498c10006dc5498c100b6df7298c10006de7298c10006dd7298c100b6dc7298c10006df5298c10006de5298c10006dc5298c10006df4298c10006de4298c10006dd4298c10006dc4298c10006de7198c100b6dc7198c10006df5198c10006dc5198c10006df4198c10006de4198c10006dd4198c10006dc4198c10006df2198c10006dc2198c10026de7098c10026dc7098c10006df5098c10026de5098c10026dc5098c10006df4098c10026de4098c10006dd4098c10026dc4098c10006df2098c10026de2098c10026dc2098c10026de1098c100067e6558c100067d6558c10006be6458c10006bd6458c10026dc6358c10004ff7558c1001cfe7558c1001cfc7558c10004ff7458c10014fe7458c10004fd7458c10014fc7458c10026df7358c10006df5358c10006dc5358c10006df4358c10006de4358c10006dd4358c10006dc4358c10004ff7258c1000cfe7258c1000cfc7258c10006de3258c10006dc3258c100b4ff7158c1017cfd7158c100b4ff7058c10024fe7058c100dcfd7058c10024fc7058c10026de3058c10026dc3058c10025df7658c10006df7658c10026df6558c10006de6558c100275e6558c100065e6558c10006dd6558c100275d6558c100065d6558c10026dc6558c10026df6458c10006de6458c100279e6458c100069e6458c10006dd6458c100279d6458c100069d6458c10026dc6458c10026df6258c10006de6258c10026dc6258c10006df7558c10006de7558c10006dd7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c10006de5258c10006dc5258c10006df4258c10006de4258c10006dd4258c10006dc4258c10006de7158c10006dc7158c10006df5158c10006dc5158c10006df4158c10006de4158c10006dd4158c10006dc4158c10006df2158c10006dc2158c10026de7058c10026dc7058c10006df5058c10026de5058c10026dc5058c10006df4058c10026de4058c10006dd4058c10026dc4058c10006df2058c10026de2058c10026dc2058c10026de1058c10026dc1058c1001cfe7518c100267e7518c1001c7e7518c10
  | 4 => 0x94100267e50594100267c50594100257f765941003e7f765941001c7f76594100267f64594100067e64594100273e64594100063e64594100067d64594100267c64594100267f63594100267c63594100267f62594100067e62594100267c62594100067f74594100067e74594100067d74594100067c74594100067f73594100067e73594100067d73594100067c73594100067f43594100067e43594100067d43594100067c43594100067f72594100067e72594100067d72594100067c72594100067f42594100067e42594100067d42594100067c42594100067e32594100067c325941003e7f71594100067e71594100067c71594100067f41594100067e41594100067d41594100067c41594100067f21594100067c215941003e7f70594100267e70594100267c70594100067f40594100267e40594100067d40594100267c40594100267e30594100267c30594100067f20594100267e20594100267c20594100267e10594100267c1059410025bf7659010036bf7659010014bf7659010026bf6559010006be65590100273e65590100063e6559010006bd65590100273d65590100063d6559010026bc6559010026bf6359010026bc6359010026bf6259010006be6259010026bc6259010006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf5359010006bc5359010006bf7259010006be7259010006bd7259010006bc7259010006bf5259010006be5259010006bc5259010006be3259010006bc3259010036bf7159010006be7159010036bd7159010036bc7159010006bf5159010006bc5159010006bf2159010006bc2159010036bf7059010026be7059010036bd7059010026bc7059010006bf5059010026be5059010026bc5059010026be3059010026bc3059010006bf2059010026be2059010026bc2059010026be1059010026bc105901001cfe75d8c100267e75d8c1001c7e75d8c10004fd75d8c100267d75d8c100047d75d8c10024fc75d8c10024ff74d8c10014fe74d8c10026be74d8c10014be74d8c10004fd74d8c10026bd74d8c10004bd74d8c10024fc74d8c1000cfe72d8c10026ee72d8c1000cee72d8c10004fd72d8c10026ed72d8c10004ed72d8c10024fc72d8c10004fe71d8c10026f671d8c10024fe70d8c10026fa70d8c10004fd7698c100067e6598c100067d6598c10006be6498c10006bd6498c10026df6398c1001cfe7598c10004fd7598c100b4fc7598c100b4ff7498c10014fe7498c10004fd7498c100b4fc7498c10006df5398c100b6dc5398c10006df4398c100b6de4398c10006dd4398c100b6dc4398c1000cfe7298c10004fd7298c1000cfc7298c10006de3298c100b6dc3298c10024fe7098c10024fc7098c10026d
  | 5 => 0x106ec62cc110005f671cc110005f571cc110004fe768c1100657e758c1100057d758c1100067f658c1100fe7c658c110006bf648c1100cebc648c110006df638c110006dc638c110055ee728c110005ed728c110006ef628c1100f6ec628c1100b4ff764c110004fd764c110004fc764c1100067f654c1100ee7c654c110005bf744c11005dbc744c110006bf644c1100e6bc644c110006df634c110006dc634c110006ef624c1100deec624c110005f7714c110005f4714c110004fe760c1100067f650c1100c67c650c110006bf640c1100bebc640c110006df630c1100b6dc630c110006ef620c1100aeec620c11007cfe76881100067f65881100a67c6588110006bf648811009ebc6488110006df6388110006dc6388110006ef628811000eec628811000cff7648110054fd764811000cfc76481100057f75481100657c75481100067f65481100967c6548110006bf644811008ebc6448110006df6348110006dc6348110006ef624811000eec6248110005f77148110005f471481100067f65c41100867c65c4110006bf64c411004ebc64c4110006df63c4110006dc63c4110006ef62c411007eec62c41100077b65c41100077865c4110007bb64c4110257b864c4110007db63c4110007d863c4110007eb62c4110007e862c4110257f241c4110257f141c41100067f65841100767c6584110006bf6484110046bc6484110006df6384110006dc6384110006ef628411006eec6284110055f67684110007776584110007746584110025f7748411024df57484110007b76484110247b46484110007d76384110007d46384110007e76284110007e46284110007f3608411003cfd75d9410024ff74d9410014fe74d9410026be74d9410014be74d9410004fd74d9410026bd74d9410004bd74d9410024fc74d94100b4fe73d9410026de73d9410004de73d9410004fd73d9410026dd73d9410004dd73d941000cfe72d9410026ee72d941000cee72d9410004fd72d9410026ed72d9410004ed72d9410024fc72d9410084fe71d9410026f671d9410024fe70d9410026fa70d94100047d76994100267f64994100067e64994100273e64994100063e64994100067d64994100267c64994100267f63994100267c63994100267f62994100067e62994100267c62994100267e609941001cff76594100267c6559410006be64594100267f7559410004ff7459410014fe7459410004fd7459410014fc745941003e7f54594100067e54594100067d545941003e7c5459410004ff73594100b4fc735941003e7f535941003e7c5359410004ff725941000cfe725941000cfc725941003e7f52594100067e525941003e7c525941001cff715941001cfd715941003cfc715941003e7c515941001cff7059410024fe705941001cfd7059410024fc705
  | 6 => 0xc6418910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc6318910007e64118910007e54118910004ff7654910004fe7654910004fd7654910004fc76549100067f655491001e7c6554910006bf64549101f6bc6454910006df6354910006dc6354910006ef625491000eec62549100b4ff76cc910004fe76cc910004fd76cc9100b4fc76cc9100067f65cc9101ee7c65cc910006bf64cc9101e6bc64cc910006df63cc9100b6dc63cc910006ef62cc91000eec62cc910004ff764c910004fe764c910004fd764c910004fc764c9100057f754c9100657c754c9100067f654c9101de7c654c910006bf644c9101d6bc644c910006df634c910006dc634c910006ef624c91000eec624c910074fe76945100067f659451001e7c6594510006bf64945101cebc6494510006df6394510006dc6394510006ef62945101c6ec629451001cfc76545100067f655451001e7c6554510006bf64545101bebc6454510006df6354510006dc6354510006ef62545101b6ec6254510005fb7054510005f87054510004fe76cc5100067f65cc5101ae7c65cc510006bf64cc510176bc64cc510006df63cc5100b6dc63cc510006ef62cc5101a6ec62cc510005fa70cc510005f970cc510004fe768c5100067f658c51019e7c658c51005dbe748c510005bd748c510006bf648c51016ebc648c510006df638c510006dc638c510006ef628c510196ec628c510004fc764c5100057f754c5100657c754c5100067f654c51018e7c654c510006bf644c510186bc644c510006df634c510006dc634c510005ef724c510055ec724c510006ef624c51017eec624c510005fb704c510005f8704c510004fe760c5100657e750c5100057d750c5100067f650c5101667c650c510006bf640c51015ebc640c510006df630c5100b6dc630c510006ef620c510156ec620c51006cfe76885100657e75885100057d75885100067f658851014e7c6588510006bf6488510146bc6488510006df6388510006dc6388510006ef628851000eec628851000cfc76485100067f654851013e7c6548510006bf6448510136bc6448510006df6348510006dc6348510006ef624851000eec6248510005fb7048510005f87048510084fe76941100067f659411001e7c6594110006bf649411012ebc6494110006df6394110006dc6394110006ef6294110126ec629411001cff7654110064fd765411001cfc76541100067f655411001e7c6554110006bf645411011ebc6454110006df6354110006dc6354110006ef6254110116ec6254110005f77154110005f47154110004fe76cc1100657e75cc1100057d75cc1100067f65cc11010e7c65cc110006bf64cc1100d6bc64cc110006df63cc1100b6dc63cc110006ef62cc110
  | 7 => 0x4d1001e7c6554d10006bf6454d10206bc6454d10006df6354d10006dc6354d10005ef7254d10055ec7254d101feec6254d1000cfe76d89100067f65d89100067c65d8910006bf64d8910006bc64d8910006df63d8910006dc63d8910056ee62d891001cfe75d8910004fd75d891001cfc75d8910004ff74d8910014fe74d8910004fd74d8910014fc74d89100b4fe73d8910004fd73d8910006ef52d8910056ee52d8910056ec52d8910006ef42d8910056ee42d8910006ed42d8910056ec42d8910056ee32d8910056ec32d891000cfe71d8910054fd71d891000cfc71d8910056ef21d8910024fe70d8910054fd70d8910024fc70d8910056ef20d8910055ee76d891000cee76d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d8910007e641d8910007e541d8910006ef75d8910006ee75d8910006ed75d8910006ec75d8910006ef74d8910006ee74d8910006ed74d8910006ec74d8910006ef54d8910006ee54d8910006ed54d8910006ec54d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d8910006ee53d8910006ed53d8910006ec53d8910006ef43d8910006ee43d8910006ed43d8910006ec43d8910006ef71d8910056ee71d8910006ed71d8910006ef51d8910006ec51d8910006ef41d8910006ee41d8910006ed41d8910006ec41d8910006ef70d8910056ee70d8910006ed70d8910006ef50d8910006ec50d8910006ef40d8910006ee40d8910006ed40d8910006ec40d89100057f75589100657c75589100067f65589100067c6558910005bf745891005dbc7458910006bf6458910006bc6458910005df7358910005dc7358910006df6358910006dc6358910056ec6258910004ff75589100067f75589100047f755891001cfe755891001cfc75589100067c755891001c7c7558910004ff7458910006bf7458910004bf7458910014fe7458910004fd7458910014fc7458910006bc7458910014bc7458910004ff7358910006df7358910004df73589100b4fc7358910006dc7358910004dc7358910054ff7258910006ef725891006cff7158910006f7715891007cff7058910006fb7058910005ee7618910056ee7618910004ee7618910006ef65189100076f65189100066f6518910006ee6518910006ed6518910006ec65189100076c65189100066c6518910006ef6418910007af6418910006af6418910006ee6418910006ed6418910006ec6418910007ac6418910006a
  | 8 => 0xb4ff7498d10014fe7498d100b6be7498d10014be7498d10004fd7498d100b6bd7498d10004bd7498d100b4fc7498d100b4fe7398d10004de7398d1000cfe7298d100b6ee7298d1000cee7298d10004fd7298d100b6ed7298d10004ed7298d1000cfc7298d10004fd7198d100b6f57198d10004fd7098d100b6f97098d100057f7558d100657c7558d100067f6558d100067c6558d10005bf7458d1005dbc7458d10006bf6458d10006bc6458d10005ef7258d10055ec7258d10004ff7558d100067f7558d100047f7558d1001cfe7558d1001cfc7558d100067c7558d1001c7c7558d10004ff7458d10006bf7458d10004bf7458d10014fe7458d10004fd7458d10014fc7458d10006bc7458d10014bc7458d10006df7358d10004ff7258d10006ef7258d10004ef7258d1000cfe7258d1000cfc7258d10006ec7258d1000cec7258d10004ff7158d10006f77158d10004ff7058d10006fb7058d10004fe7618d100067f6518d100067c6518d10006bf6418d10006bc6418d10006dd6318d1001cfe7518d10004fd7518d100b4fc7518d100b4ff7418d10014fe7418d10004fd7418d100b4fc7418d100b6de7318d10006df5318d100b6dc5318d10006df4318d100b6de4318d10006dd4318d100b6dc4318d1000cfe7218d10004fd7218d1000cfc7218d10006de3218d100b6dc3218d10194fe7118d100b4fc7118d10024fe7018d10024fc7018d10005de7618d10006de7618d10004de7618d10006df6518d100075f6518d100065f6518d10006de6518d10006dd6518d10006dc6518d100075c6518d100065c6518d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d10006de6218d10006dc6218d10007d64118d10007d54118d100b6df7518d10006de7518d10006dd7518d100b6dc7518d100b6df7418d10006de7418d10006dd7418d100b6dc7418d10006df5418d10006de5418d10006dd5418d10006dc5418d100b6df7218d10006de7218d10006dd7218d100b6dc7218d10006df5218d10006de5218d10006dc5218d10006df4218d10006de4218d10006dd4218d10006dc4218d100b6df7118d10006dd7118d10006df5118d10006dc5118d10006df4118d10006de4118d10006dd4118d10006dc4118d10006df2118d10006dc2118d100b6df7018d10006dd7018d10006df5018d10006dc5018d10006df4018d10006de4018d10006dd4018d10006dc4018d10006df2018d10006dc2018d10006dd1018d100b4ff7694d10004fe7694d10004fd7694d100b4fc7694d100067f6594d1001e7c6594d10006bf6494d10216bc6494d10006df6394d100b6dc6394d100675f5394d1020eec6294d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100067f655
  | 9 => 0xf7159510006f77159510084ff7059510006fb70595100057e76195100667e76195100047e76195100067f64195100067e64195100067d64195100067c64195100073c64195100063c64195100067e62195100067c621951000776411951000775411951005dbe76d911005ebe76d9110014be76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006be62d9110006bc62d9110007b771d911005fb471d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bc52d9110006be32d9110006bc32d9110006bf71d911005ebe71d911005ebd71d911005ebc71d9110006bf51d9110006bc51d9110006bf21d9110006bc21d9110006bf70d911005ebe70d911005ebd70d911005ebc70d9110006bf50d9110006bc50d9110006bf20d9110006bc20d911005ebd10d91100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d1001cfe75d8d10004fd75d8d1001cfc75d8d10004ff74d8d10014fe74d8d10004fd74d8d10014fc74d8d10006df53d8d10006dc53d8d10006df43d8d10006de43d8d10006dd43d8d10006dc43d8d1000cfe72d8d10004fd72d8d1000cfc72d8d10006de32d8d10006dc32d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d10006de62d8d10006dc62d8d10007d641d8d10007d541d8d10006df75d8d10006de75d8d10006dd75d8d10006dc75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d10006de52d8d10006dc52d8d10006df42d8d10006de42d8d10006dd42d8d10006dc42d8d10006df71d8d10006dd71d8d10006df51d8d10006dc51d8d10006df41d8d10006de41d8d10006dd41d8d10006dc41d8d10006df21d8d10006dc21d8d10006df70d8d10006dd70d8d10006df50d8d10006dc50d8d10006df40d8d10006de40d8d10006dd40d8d10006dc40d8d10006df20d8d10006dc20d8d100657e7598d100057d7598d100067f6598d100067c6598d1005dbe7498d10005bd7498d10006bf6498d10006bc6498d10006df6398d10055ee7298d10005ed7298d1001cfe7598d100b67e7598d1001c7e7598d10004fd7598d100b67d7598d100047d7598d100b4fc7598d10
  | 10 => 0x461001e7e65546100067d6554610005fb7054610025f870546100b6de63cc610006dd63cc610025fa70cc610005f970cc610045be748c610005bd748c610006df638c610006dc638c6100057f754c6100757c754c610006de634c610006dd634c610005ef724c61006dec724c610005fb704c610025f8704c6100757e750c6100057d750c610006df630c6100b6dc630c610007d5310c610054fd76886100757e75886100057d7588610006ef628861000eec628861000cff7648610024fc764861000eee6248610006ed6248610005fb7048610025f8704861003cff76542100267f65542100267c65542100757e75cc2100057d75cc210026df63cc210026dc63cc210005bf744c210045bc744c210026df634c210026dc634c21002cff76482100057f75482100757c7548210026ef6248210026ec6248210025f576c4210006f576c4210026f764c421025ef564c4210005f976c4210006f976c421001cfe76d95100667e65d9510006bc64d9510004ff74d9510014fe74d9510004fd74d9510014fc74d95100667f54d95100067e54d95100067d54d95100667c54d95100b4fe73d9510004fd73d95100667f53d95100667c53d951000cfe72d9510004fd72d951000cfc72d95100667f52d95100067e52d95100667c52d951001cfe71d9510064fd71d951001cfc71d95100667f51d9510024fe70d9510064fd70d9510024fc70d95100667f50d95100657e76d951001c7e76d95100067f64d95100067e64d95100067d64d95100067c64d95100073c64d95100063c64d95100067e62d95100067c62d95100077641d95100077541d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067e42d95100067d42d95100067c42d95100067e32d95100067c32d95100067f71d95100667e71d95100067d71d95100067f41d95100067e41d95100067d41d95100067c41d95100067f21d95100067c21d95100067f70d95100667e70d95100067d70d95100067f40d95100067e40d95100067d40d95100067c40d95100067f20d95100067c20d95100667c6559510005bf745951005dbc7459510006bc6459510005df7359510005dc7359510005ef7259510055ec7259510064ff75595100067f7559510004ff7459510006bf7459510004bf7459510014fe7459510004fd7459510014fc7459510006bc7459510014bc7459510004ff7359510006df7359510004df73595100b4fc7359510006dc7359510004dc7359510004ff7259510006ef7259510004ef725951000cfe725951000cfc7259510006ec725951000cec7259510074f
  | 11 => 0xb4fc73596100767c5359610004ff725961000cfe725961000cfc72596100767f52596100767f51596100267e50596100267c505961001cfe75d8e100267e75d8e1001c7e75d8e10004fd75d8e100267d75d8e100047d75d8e10024fc75d8e10024ff74d8e10014fe74d8e10004fd74d8e10024fc74d8e1000cfe72d8e10026ee72d8e1000cee72d8e10004fd72d8e10026ed72d8e10004ed72d8e10024fc72d8e10026f571d8e10026fa70d8e10004fd7698e100757e7598e100057d7598e10026df6398e1001cfe7598e100b67e7598e1001c7e7598e10004fd7598e100b67d7598e100047d7598e100b4fc7598e100b4ff7498e10014fe7498e10004fd7498e100b4fc7498e100b6de4398e10006dd4398e1000cfe7298e10004fd7298e1000cfc7298e10026de3098e10026dc3098e10005bf7458e10045bc7458e10026dc6358e10004ff7558e1001cfe7558e1001cfc7558e10004ff7458e10006bf7458e10004bf7458e10014fe7458e10004fd7458e10014fc7458e10006bc7458e10014bc7458e10026df7358e10006de4358e10006dd4358e10004ff7258e1000cfe7258e1000cfc7258e10026de3058e10026dc3058e1001cfe7518e10004fd7518e10024fc7518e10024ff7418e10014fe7418e10004fd7418e10024fc7418e100b4fe7318e10026de7318e1000cfe7218e10004fd7218e10024fc7218e10026f57118e10026fa7018e100b4ff7694e10024fe7694e10004fd7694e10024fc7694e1001e7e6594e100067d6594e100775f5394e10004ff7654e10024fe7654e10004fd7654e10024fc7654e100067f6554e1001e7c6554e10005ef7254e1006dec7254e10005f77154e10005f47154e1001cfe75d8a10004fd75d8a10024fc75d8a10024ff74d8a10014fe74d8a10004fd74d8a10024fc74d8a100b4fe73d8a10004fd73d8a1006cfd72d8a10026f571d8a1006eec21d8a10026fa70d8a10026ef20d8a1000cff7658a100057f7558a100757c7558a10026ec6258a10004ff7558a100067f7558a100047f7558a1001cfe7558a1001cfc7558a100067c7558a1001c7c7558a10004ff7458a10014fe7458a10004fd7458a10014fc7458a10004ff7358a100b4fc7358a10026ef7258a1006eee5258a1006eee4258a10006ed4258a1006eec3258a1006eef2158a10026ee2058a10026ec2058a10004ff7654a10024fe7654a10004fd7654a10024fc7654a1001e7e6554a100067d6554a1000eee6254a10006ed6254a100b4ff76cca10024fe76cca10004fd76cca10024fc76cca1000eee62cca10006ed62cca10004ff764ca10024fe764ca10004fd764ca10024fc764ca100057f754ca100757c754ca10005f7714ca10005f4714ca10064fd76946100067f659461001e7c659461007777519461001cff7654610024fc765
  | 12 => 0xd7654f10004fc7654f1001e7e6554f100067d6554f10005ef7254f1007dec7254f100857e75d8b100057d75d8b1007eee62d8b1001cfe75d8b100067e75d8b1001c7e75d8b10004fd75d8b100067d75d8b100047d75d8b1001cfc75d8b10004ff74d8b10014fe74d8b10004fd74d8b10014fc74d8b100b4fe73d8b10004fd73d8b1007cfd72d8b1007eee52d8b1007eee42d8b10006ed42d8b1007eec32d8b10006f671d8b1007eef21d8b10006f970d8b1007eec20d8b1000cff7658b1007eec6258b10004ff7558b1001cfe7558b1001cfc7558b10004ff7458b10014fe7458b10004fd7458b10014fc7458b10004ff7358b100b4fc7358b10006ef7258b1007eec2158b1007eef2058b10004ff7654b10004fe7654b10004fd7654b10004fc7654b100067f6554b1001e7c6554b10006ef6254b1000eec6254b100b4ff76ccb10004fe76ccb10004fd76ccb100b4fc76ccb10006ef62ccb1000eec62ccb10004ff764cb10004fe764cb10004fd764cb10004fc764cb100057f754cb100857c754cb1001cfd769471001e7e65947100067d6594710005fa7094710005f9709471003cff76547100067f655471001e7c6554710006df63cc7100b6dc63cc71004dbe748c710005bd748c710006de638c710006dd638c710005fa708c710005f9708c7100057f754c7100857c754c710006df634c710006dc634c710005ef724c71007dec724c7100857e750c7100057d750c7100b6de630c710006dd630c710005fa700c710005f9700c71000cfd76887100857e75887100057d758871000eee6288710006ed6288710005fa7088710005f9708871002cff7648710006ef624871000eec6248710064fd76943100067f659431001e7c65943100877b509431001cff765431001cfc765431001e7e65543100067d6554310005f77154310005f471543100857e75cc3100057d75cc3100b6de63cc310006dd63cc310005f671cc310005f571cc3100857e758c3100057d758c310006df638c310006dc638c31007dee728c310005ed728c310005bf744c31004dbc744c310006de634c310006dd634c310005f7714c310005f4714c310006df630c3100b6dc630c310054fd7688310006ef628831000eec628831000cff764831000cfc76483100057f75483100857c754831000eee6248310006ed6248310005f77148310005f47148310074fd75d9610024ff74d9610014fe74d9610004fd74d9610024fc74d96100b4fe73d9610004fd73d96100767f53d961000cfe72d9610004fd72d9610024fc72d96100067e52d96100767c52d9610026f571d96100767c51d9610026fa70d96100267f50d961001cff76596100267c65596100267f7559610004ff7459610014fe7459610004fd7459610014fc74596100767f54596100067d5459610004ff7359610
  | 13 => 0x412000cfe76cc12000cfc76cc1200957e75cc1200057d75cc1200067f65cc12010e7c65cc120006df63cc1200b6dc63cc12000dee72cc120005ed72cc1200acfe768c1200957e758c1200057d758c1200067f658c1200fe7c658c12000dee728c120005ed728c1200b4ff764c12000cfe764c1200dcfd764c12000cfc764c1200067f654c1200ee7c654c120005bf744c12008dbc744c120006df634c120006dc634c120005ef724c12000dec724c1200f4fe760c1200067f650c1200c67c650c120025ec720c120025ef7588120005ed75881200076f65881200076c6588120025ef7488120265ed7488120005ee7388120025ec7388120005ed7188120006ec6188120025ee7088120027ea7088120026ef608812000feb60881200867e65d9710084fd75d9710004ff74d9710014fe74d9710004fd74d9710014fc74d97100867f54d97100067d54d97100b4fe73d9710004fd73d97100867c53d971000cfe72d9710004fd72d971000cfc72d97100867f52d9710006f671d97100867f51d9710006f970d97100867c50d971001cff76597100867c65597100067f7559710004ff7459710014fe7459710004fd7459710014fc7459710004ff73597100b4fc73597100867f5359710004ff725971000cfe725971000cfc72597100067e52597100867c52597100867c51597100867f505971004dbe74d8f10005bd74d8f1001cfe75d8f10004fd75d8f1001cfc75d8f10004ff74d8f10014fe74d8f10006be74d8f10014be74d8f10004fd74d8f10006bd74d8f10004bd74d8f10014fc74d8f10006de43d8f10006dd43d8f1000cfe72d8f10004fd72d8f1000cfc72d8f10006f671d8f10006f970d8f10004fd7698f10006df6398f1001cfe7598f10004fd7598f100b4fc7598f100b4ff7498f10014fe7498f10004fd7498f100b4fc7498f1000cfe7298f10004fd7298f1000cfc7298f100057f7558f100857c7558f10005ef7258f1007dec7258f10004ff7558f100067f7558f100047f7558f1001cfe7558f1001cfc7558f100067c7558f1001c7c7558f10004ff7458f10014fe7458f10004fd7458f10014fc7458f10006df7358f10004ff7258f10006ef7258f10004ef7258f1000cfe7258f1000cfc7258f10006ec7258f1000cec7258f100857e7518f100057d7518f10006dd6318f1001cfe7518f100b67e7518f1001c7e7518f10004fd7518f100b67d7518f100047d7518f100b4fc7518f100b4ff7418f10014fe7418f10004fd7418f100b4fc7418f100b4fe7318f100b6de7318f100b6de4318f10006dd4318f1000cfe7218f10004fd7218f1000cfc7218f100b6f67118f100b6f97018f100b4ff7694f10004fe7694f10004fd7694f100b4fc7694f100067f6594f1001e7c6594f100875f5394f10004ff7654f10004fe7654f10004f
  | 14 => 0x1eeee65cc9201eeec65cc9200076c65cc9201ee6c65cc92027def74cc92027ded74cc92000dee73cc92000fce73cc920006ef63cc920007cf63cc920006ed63cc920007cc63cc920005ed71cc920025ee70cc920007ea70cc920007e970cc92000eef60cc92000feb60cc9200067f65d85200067c65d852001cfe75d8520004fd75d852001cfc75d8520004ff74d8520014fe74d8520004fd74d8520014fc74d85200b4fe73d8520004fd73d8520006f741d8520006f441d852006ef621d852006ef521d85200957e75985200057d75985200067f65985200067c6598520006f76198520055f970985200057f75585200957c75585200067f65585200067c6558520005bf745852008dbc7458520005df7358520005dc735852007dfb70585200067f65185200067c651852008dbe7418520005bd7418520006f5611852001cfe7518520004fd751852001cfc7518520004ff7418520014fe7418520006be7418520014be7418520004fd7418520006bd7418520004bd7418520014fc74185200b4fe7318520004fd731852002eee5218520006ed521852002eee4218520006ed4218520006ef321852002eec3218520006f74118520006f4411852002eef211852002ef6211852002ef5211852002eec2018520004fe7694520004fd7694520004fc76945200067f659452001e7c659452000dee7294520005ed72945200076d5294520004ff7654520004fe7654520004fc76545200067f655452001e7c655452000dee72545201b76e5254520004fe76cc520004fd76cc5200b4fc76cc5200067f65cc5201ae7c65cc52000dec72cc520006f761cc520006f461cc520004fe768c520004fd768c520004fc768c5200067f658c52019e7c658c52008dbe748c520005bd748c520006df638c520006dc638c52000dee728c520005ed728c520004ff764c520004fe764c520004fc764c5200057f754c5200957c754c5200067f654c52018e7c654c520005ef724c52000dec724c520004fe760c520004fd760c5200b4fc760c5200957e750c5200057d750c5200067f650c5201667c650c520006df630c5200b6dc630c52000dee720c520005ed720c520006f7610c520006f4610c520005fa700c520005f9700c520005ef7548520005ed75485200076f65485200076c6548520275ef7448520275ed7448520005ee7348520005ec734852000def714852000fe77148520007e76148520006ec6148520007e46148520007eb7048520025ec7048520007e8704852000eef604852000feb604852026cfe76941201267f659412001e7c6594120025ec72941201276e52941200977b5094120027e8209412001cff765412000cfe7654120114fd765412000cfc76541200067f655412001e7c6554120005ef725412000dec72541200076d5254120117e8205
  | 15 => 0xf7159520004fc715952028cff7059520006fb70595201257e76195200967e76195201247e76195200067f64195200067e64195200067d64195200067c641952026f6e72195200976d721952026e7f621952026f6e42195200076d421952026f6c321952026f6f211952026e7f601952026f7b201952026f6c201952026f7820195200067f65d8d200067c65d8d2001cfe75d8d20004fd75d8d2001cfc75d8d20004ff74d8d20014fe74d8d20004fd74d8d20014fc74d8d20006df43d8d20006dc43d8d20024ff72d8d200f4fd72d8d20006ed72d8d200f6ee42d8d20006ed42d8d200f6df32d8d200f6dd32d8d200f6ec32d8d20004fe71d8d20004fd71d8d200957e7598d200057d7598d200067f6598d200067c6598d20006df6398d200ddf97098d2001cfe7598d200b67e7598d2001c7e7598d20004fd7598d200b67d7598d200047d7598d200b4fc7598d200b4ff7498d20014fe7498d20004fd7498d200b4fc7498d200b4fe7398d20104fd7298d200b6ed7298d20004fe7198d20004fd7198d200dcfd7098d200b6f97098d200057f7558d200957c7558d200067f6558d200067c6558d20005bf7458d2008dbc7458d20005f77158d20005f47158d20105fb7058d20004ff7558d200067f7558d200047f7558d2001cfe7558d2001cfc7558d200067c7558d2001c7c7558d20004ff7458d20006bf7458d20004bf7458d20014fe7458d20004fd7458d20014fc7458d20006bc7458d20014bc7458d20006df7358d200dcff7258d20006ef7258d200deee4258d20006ed4258d200deec3258d20004ff7158d20006f77158d20004f77158d20004fc7158d20006f47158d20004f47158d20104ff7058d20006fb7058d200f4fe7618d200067f6518d200067c6518d20006dd6318d2001cfe7518d20004fd7518d200b4fc7518d200b4ff7418d20014fe7418d20004fd7418d200b4fc7418d200b6de7318d20006df4318d200b6dc4318d20024ff7218d2000cfe7218d200acfd7218d2000cfc7218d200b6df3218d200aedd3218d20004fe7118d20004fd7118d200b4ff7694d20004fe7694d20004fd7694d200b4fc7694d200067f6594d2001e7c6594d200975f5394d2000dec7294d2020f6e5294d20004ff7654d20004fe7654d20004fd7654d20004fc7654d200067f6554d2001e7c6554d20005ef7254d2000dec7254d20095ec765492001eec765492001cec765492000def755492000f6f75549200076f655492001eee655492001eec65549200976c6554920285ef7454920285ed7454920005ec73549200976f53549200076d5354920005ef71549200976c5154920007eb7054920025ec7054920007e8705492000eef605492000feb60549200976f5054920006ee76cc920004ee76cc920005ef75cc920005ed75cc9200076f65cc920
  | 16 => 0x8620056ef2058620026f61058620026f41058620004ff7694620024fe7694620004fd76946200067f659462001e7c6594620004ff7654620004fd7654620024fc765462001e7e65546200067d6554620005ef725462000dec72546200b4ff76cc620024fe76cc620004fd76cc6200b6de63cc620006dd63cc62000dee72cc620005ed72cc620004ff768c620024fe768c620004fd768c62009dbe748c620005bd748c620004ff764c620004fd764c620024fc764c6200057f754c6200a57c754c620006de634c620006dd634c620005ef724c62000dec724c6200b4ff760c620024fe760c620004fd760c6200a57e750c6200057d750c620025fa700c620005f9700c6200076e75886200076d7588620006ef6588620006ed6588620296ef6488620296ed6488620006ee6388620006ec638862000dee718862000fe67188620007e66188620006ed6188620007e56188620007ea7088620005ed7088620007e9708862000eee608862000fea608862028cff76542200267f65542200267c6554220117eb20542200dcfd76cc2200a57e75cc2200057d75cc220104ff764c220005bf744c22009dbc744c22001cfe76d95200967e65d9520004ff74d9520014fe74d9520004fd74d9520014fc74d95200967f54d95200067e54d95200067d54d95200967c54d95200b4fe73d9520004fd73d95200967f53d95200967c53d9520024ff72d952000cfe72d9520124fd72d952000cfc72d95201267f52d95201267d52d9520004fe71d9520004fd71d95200967f51d95200967c51d952000cfd70d95200967f50d952026d7e76d952001c7e76d95200067f64d95200067e64d95200067d64d95200067c64d95200076f72d95201276c72d95201276e42d95200076d42d95201276c32d95201276f21d95201277b20d95201276c20d95201277820d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d95200067f43d95200067e43d95200067d43d95200067c43d95201267f72d95201267e72d95201267d72d95201267c72d95201267f42d95201267e42d95201267d42d95201267c42d95201267f32d95201267e32d95201267d32d95201267c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f41d95200067e41d95200067d41d95200067c41d95201267f21d95201267e21d95201267d21d95201267c21d95201267f70d95200967e70d95201267d70d95200067f40d95200067e40d95200067d40d95200067c40d95201267f20d95201267e20d95201267c20d95200967c655952028dfb7059520124ff75595200067f7559520004ff7459520014fe7459520004fd7459520014fc7459520004ff73595200b4fc7359520114ff7259520006ef7259520004f
  | 17 => 0xa67f53d9620026ed72d96201267e52d96201267c52d9620004fe71d9620004fd71d96200a67c51d9620126ec21d9620024fe70d9620026fa70d96200267f50d9620026ef20d962001cff76596200267c65596200267f7559620004ff7459620014fe7459620004fd7459620014fc74596200a67f54596200067d5459620004ff73596200b4fc73596200a67c53596201167f52596201167d5259620004ff7159620004fc71596200a67f5159620116ec2159620024fe7059620024fc70596200267e50596200267c5059620116ef205962001cfe75d8e200267e75d8e2001c7e75d8e20004fd75d8e200267d75d8e200047d75d8e20024fc75d8e20024ff74d8e20014fe74d8e20004fd74d8e20024fc74d8e20026ed72d8e20004fe71d8e20004fd71d8e20024fe70d8e20026fa70d8e200dcfd7698e200a57e7598e200057d7598e20026df6398e2001cfe7598e200b67e7598e2001c7e7598e20004fd7598e200b67d7598e200047d7598e200b4fc7598e200b4ff7498e20014fe7498e20004fd7498e200b4fc7498e20006df5398e200b6dc5398e200b6de4398e20006dd4398e200b6df3298e20106dd3298e20004fe7198e20004fd7198e20106ec2198e20024fe7098e20024fc7098e20026de3098e20026dc3098e20106ef2098e20026dc6358e20004ff7558e2001cfe7558e2001cfc7558e20004ff7458e20014fe7458e20004fd7458e20014fc7458e20026df7358e20006df5358e20006dc5358e20006de4358e20006dd4358e200dedf3258e200dedd3258e20004ff7158e20004fc7158e20024fe7058e20024fc7058e20026de3058e20026dc3058e2001cfe7518e20004fd7518e20024fc7518e20024ff7418e20014fe7418e20004fd7418e20024fc7418e200b4fe7318e20026de7318e20026ed7218e20004fe7118e20004fd7118e200aeec2118e20024fe7018e20026fa7018e20026ef2018e200b4ff7694e20024fe7694e20004fd7694e20024fc7694e2001e7e6594e200067d6594e200a75f5394e20004ff7654e20024fe7654e20004fd7654e20024fc7654e200067f6554e2001e7c6554e20005ef7254e2000dec7254e20026f7619862001cfe7598620004fd759862001cfc7598620004ff7498620014fe7498620004fd7498620014fc74986200b4fe7398620004fd7398620006f64198620006f5419862007ef6219862007ef52198620024fe7098620026f61098620026f410986200057f75586200a57c7558620026f46158620004ff75586200067f75586200047f755862001cfe755862001cfc75586200067c755862001c7c7558620004ff7458620014fe7458620004fd7458620014fc7458620004ff73586200b4fc7358620006f64158620006f54158620056f62158620056f52158620056ec2158620024fc705
  | 18 => 0xd6254830104ff764c8300057f754c8300c57c754c830026f7619843001cfe7598430004fd759843001cfc7598430004ff7498430014fe7498430004fd7498430014fc749843000cfe7298430004fd729843000cfc7298430006f64198430006f541984300b6f731984300b6f43198430026f61098430026f410984300057f75584300c57c7558430005ef72584300adec7258430026f46158430004ff75584300067f75584300047f755843001cfe755843001cfc75584300067c755843001c7c7558430004ff7458430014fe7458430004fd7458430014fc7458430004ff7258430006ef7258430004ef725843000cfe725843000cfc7258430006ec725843000cec7258430006f64158430006f541584300b6f731584300b6f43158430026f61058430026f41058430004ff7694430024fe7694430004fd76944300067f659443001e7c6594430006f66194430006f56194430004ff7654430004fd7654430024fc765443001e7e65544300067d6554430005df73544300b5dc7354430006f66154430006f56154430004fd768c4300bdbe748c430005bd748c430005dd768c430006dd768c430004dd768c4302d79e748c4300079d748c4302d6df648c4302d6dd648c4300b5de718c430006dd618c430005dd708c4302cede608c430004ff764c4300057f754c4300c57c754c4302c6de634c430005ef724c4300adec724c4300b7d4314c4300b75e750c4300b75d750c4300b6df640c4302bedd640c4302b5de710c4300b7d6710c4300b7d6610c430006dd610c4300b7d5610c4300b7da700c430005dd700c4300b7d9700c4302aede600c430004ff7688430024fe7688430004fd76884300c57e75884300057d758843000eec6288430006f66188430006f56188430004ff7648430004fd7648430024fc7648430005df73484300b5dc734843000eee6248430006ed6248430006f66148430006f561484300fcff76540300267f65540300267c65540300b75e75cc0300b75d75cc030026df64cc0302a6dd64cc030005de71cc030006dd61cc030025dd70cc030026de60cc0300277a758c03002779758c0300b5f9738c0300b6fa638c030027da638c030027ea728c030027e9728c030007da318c0300b7d8318c030004ff764c030005bf744c0300bdbc744c030025df764c030006df764c030004df764c0300079f744c03029f9c744c030026df644c03029edd644c030005dc714c030006dd614c030025df704c030026de604c0300b5fb764c030006fb764c030004fb764c030007bb744c03029fb8744c030025fb734c030027db734c0300b6fa634c0300b7da634c030114fd75d9620024ff74d9620014fe74d9620004fd74d9620024fc74d96200b4fe73d9620026de73d9620004de73d9620004fd73d9620026dd73d9620004dd73d9620
  | 19 => 0xc5300ddec724c530006f7614c530006f4614c530005fb704c530005f8704c5300075f754c5300075c754c530305df744c530305dd744c5300079f644c5302ff9c644c530007cf724c530007cc724c530007d7714c530007d7614c530006dc614c530007d4614c530006d4614c530007db704c530025dc704c530007d8704c530004fe760c5300ed7e750c5300057d750c530006bf640c53015ebc640c5302f5de730c530004fe7688530004fd7688530004fc76885300ed7e75885300057d7588530006bf6488530146bc6488530005de7388530005dd7388530006ef628853000eec6288530004ff7648530004fe7648530004fc7648530006bf6448530136bc644853010cfe769413001e7e65941300067d6594130006bf649413012ebc64941300ef7b509413001cff76541300ecfd765413001cfc76541300067f655413001e7c6554130006bf645413011ebc6454130005df7354130005dc73541300ed7e75cc1300057d75cc130006bf64cc1300d6bc64cc1300b77a75cc1300b77975cc130007bb64cc1302efb864cc1300b7da43cc1302efd943cc1300b7db31cc130007d931cc1300ed7e758c1300057d758c130006bf648c1300cebc648c1300ddee728c130005ed728c1300275e758c1300275d758c130025df748c1302e5dd748c1300079f648c1302df9c648c130027ce728c130027cd728c130005dd718c130006dc618c130007db608c1300c4fd75d9430024ff74d9430014fe74d9430004fd74d9430024fc74d94300b4fe73d9430026de73d94300b67f53d943000cfe72d9430004fd72d9430024fc72d94300067e52d94300c67c52d9430004fe71d9430004fd71d94300c67c51d9430024fe70d9430026fa70d94300267f50d943001cff76594300267c6559430024ff75594300267f7559430004ff7459430014fe7459430004fd7459430014fc74594300c67f54594300067d545943001cff73594300b4fe735943001cfd73594300b4fc73594300b67e53594300b67c5359430004ff725943000cfe725943000cfc72594300c67f5259430004ff7159430004fc71594300c67f5159430024fe7059430024fc70594300267e50594300267c505943010cff7654c300b67f6554c300b67c6554c30005ef7254c300adec7254c3000cff76588300057f75588300c57c7558830026ec6258830004ff75588300067f75588300047f755883001cfe755883001cfc75588300067c755883001c7c7558830004ff7458830014fe7458830004fd7458830014fc745883000cfd73588300aeee52588300aeee4258830006ed42588300b6ef32588300b6ec3258830004ff7158830004fc71588300aeef2158830026ee2058830026ec2058830004ff7654830004fd7654830024fc765483001e7e65548300067d655483000eee6254830006e
  | 20 => 0xe6be70d91300e6bd70d91300e6bc70d9130006bf50d9130006bc50d91300e6bd30d9130006bf20d9130006bc20d91300fcfe7694d3001e7e6594d300067d6594d30006bf6494d30216bc6494d300ef5f5394d3001cfc7654d300067f6554d3001e7c6554d30006bf6454d30206bc6454d30005ef7254d300ddec7254d30005fb7054d30005f87054d3000cfe76d8930006bf64d8930006bc64d89300deee62d893001cfe75d8930004fd75d893001cfc75d8930004ff74d8930014fe74d8930004fd74d8930014fc74d893000cfc73d8930006ef52d89300deec52d89300deee32d8930004fe71d8930004fd71d89300deec21d89300deef20d89300057f75589300ed7c7558930005bf74589300e5bc7458930006bf6458930006bc64589300deec6258930005f77158930005f47158930004ff7654930004fe7654930004fc765493001e7e65549300067d6554930006bf64549301f6bc6454930005df7354930005dc73549300f4fe76cc930006bf64cc9301e6bc64cc93000eee62cc93000cfc764c9300057f754c9300ed7c754c930006bf644c9301d6bc644c930006ef624c93000eec624c9300dfcc324c930005fb704c930005f8704c930006bf64d8530006bc64d853001cfe75d8530004fd75d853001cfc75d8530004ff74d8530014fe74d8530004fd74d8530014fc74d853000cfe72d8530004fd72d853000cfc72d8530006f751d8530006f451d8530006f721d8530006f421d85300e5be7498530005bd7498530006bf6498530006bc6498530006f761985300057f75585300ed7c7558530005bf74585300e5bc7458530006bf6458530006bc6458530005ef72585300ddec72585300ed7e75185300057d7518530006bf6418530006bc6418530006f5611853001cfe75185300067e751853001c7e7518530004fd75185300067d75185300047d751853001cfc7518530004ff7418530014fe7418530004fd7418530014fc7418530006de4318530006dd431853000cfe7218530004fd721853000cfc7218530006f75118530006f45118530006f72118530006f42118530004fe7694530004fd7694530004fc76945300067f659453001e7c6594530006bf64945301cebc6494530005de7394530005dd7394530004ff7654530004fe7654530004fc765453001e7e65545300067d6554530006bf64545301bebc6454530004fe76cc530006bf64cc530176bc64cc530005de76cc530006de76cc530004de76cc5302f5df74cc5302f5dd74cc5300079f64cc53030f9c64cc530006dc61cc530025de70cc5300b6df60cc5300e5be748c530005bd748c530006bf648c53016ebc648c530305dd738c530006f7618c530006f4618c530005fa708c530005f9708c5300057f754c5300ed7c754c530006bf644c530186bc644c530005ef724
  | 21 => 0xd650c630156ee620c630006ed620c630007d5310c630005dd760c630006dd760c6300075e750c6300075d750c6300075e650c6300075d650c6302aedf640c6302aedd640c630007ce620c630007cd620c630007d6710c630006dd610c630005dd700c630004ff7688630024fe7688630004fd76886300fd7e75886300057d758863014e7e65886300067d658863000eee6288630006ed6288630004ff7648630004fd7648630024fc764863013e7e65486300067d6548630005df7348630005dc734863000eee6248630006ed62486300c4ff765423001e7e65542300067d6554230116ee6254230006ed62542300fd7e75cc2300057d75cc23010e7e65cc2300067d65cc230106ee62cc230006ed62cc230025dd76cc230006dd76cc2300075e75cc2300075d75cc2300275e65cc2300275d65cc230026df64cc230316dd64cc230027ce62cc230027cd62cc230005de71cc230006dd61cc230027da50cc230007d950cc230005f976cc2300b6f976cc2300b77a75cc2300b77975cc2300077a65cc2300077965cc2300b7da53cc230007d953cc230007ea62cc230007e962cc23001cfe76d95300ee7e65d9530006bc64d9530004ff74d9530014fe74d9530004fd74d9530014fc74d95300b4fe73d95300ecfd73d95300b4fc73d95300ee7f53d953000cfe72d9530004fd72d953000cfc72d95300067e52d95300ee7c52d9530004fe71d9530004fd71d95300ee7c51d95300ecfd70d95300ee7f50d95300ee7c6559530005bf74595300e5bc7459530006bc6459530005ef72595300ddec7259530005f77159530005f471595300ecff75595300067f7559530004ff7459530006bf7459530004bf7459530014fe7459530004fd7459530014fc7459530006bc7459530014bc74595300ee7f54595300067d54595300fcff7359530006df73595300ee7c5359530004ff7259530006ef7259530004ef725953000cfe725953000cfc7259530006ec725953000cec72595300ee7f5259530004ff7159530006f77159530004f77159530004fc7159530006f47159530004f471595300ee7f515953010cff7059530006fb70595300ee7c50595300e5be76d91300e6be76d9130014be76d9130006bf65d9130006be65d9130006bd65d9130006bc65d91300079f73d91300e79c73d9130006be62d9130006bc62d9130006bf75d9130006be75d9130006bd75d9130006bc75d9130006bf73d91300e6be73d91300e6bd73d91300e6bc73d9130006bf53d9130006bc53d9130006bf72d9130006be72d9130006bd72d9130006bc72d9130006bf52d9130006be52d9130006bc52d9130006be32d9130006bc32d9130006bf71d9130006be71d9130006bd71d9130006bc71d9130006bf51d9130006bc51d9130006bf21d9130006bc21d9130006bf70d9130
  | 22 => 0x8a30026ec6558a30026ef6458a30006ee6458a30006ed6458a30026ec6458a30026ef6158a30026ec6158a30006ef7558a30006ee7558a30006ed7558a30006ec7558a30006ef7458a30006ee7458a30006ed7458a30006ec7458a30006ef5458a30006ee5458a30006ed5458a30006ec5458a30006ed7358a300f6ec7358a30006ef5358a30006ee5358a30006ed5358a30006ec5358a30006ef4358a30006ee4358a30006ed4358a30006ec4358a30006ef7158a30006ee7158a30006ed7158a30006ec7158a30006ef5158a30006ec5158a30006ef4158a30006ee4158a30006ed4158a30006ec4158a300f6ef7058a30026ee7058a30026ec7058a30006ef5058a30026ee5058a30026ec5058a30006ef4058a30026ee4058a30006ed4058a30026ec4058a30026ee3058a30026ec3058a30026ee1058a30026ec1058a30004ff7654a30004fd7654a30024fc7654a3001e7e6554a300067d6554a3000eee6254a30006ed6254a300dcfd76cca301ee7e65cca300067d65cca3000eee62cca3000cff764ca300057f754ca300fd7c754ca301de7e654ca300067d654ca3000eee624ca30006ed624ca30005fb704ca30025f8704ca300067e65986300067d6598630006ee6298630006ed6298630026f7619863001cfe7598630004fd759863001cfc7598630004ff7498630014fe7498630004fd7498630014fc749863000cfe7298630004fd729863000cfc7298630006f64198630006f54198630026f61098630026f410986300067e65586300067d6558630006ee6258630006ed6258630026f46158630004ff755863001cfe755863001cfc7558630004ff7458630014fe7458630004fd7458630014fc7458630004ff725863000cfe725863000cfc7258630006f64158630006f54158630026f61058630026f41058630004ff7694630024fe7694630004fd769463001e7e65946300067d65946301c6ee6294630006ed6294630004ff7654630004fd7654630024fc765463001e7e65546300067d6554630005df7354630005dc73546301b6ee6254630006ed62546301ae7e65cc6300067d65cc6301a6ee62cc630006ed62cc63019e7e658c6300067d658c6300cdbe748c630005bd748c630196ee628c630006ed628c630006f6618c630006f5618c630025fa708c630005f9708c6300075e658c6300075d658c6302cf9e748c6300079d748c6302cedf648c6302cedd648c630007ce628c630007cd628c630007d6618c630006dd618c630007d5618c630007da708c630005dd708c630007d9708c6300057f754c6300fd7c754c63018e7e654c6300067d654c630005ef724c6300f5ec724c63017eee624c630006ed624c630006f6614c630006f5614c630005fb704c630025f8704c6300fd7e750c6300057d750c6301667e650c6300067
  | 23 => 0x4fd74d9630024fc74d9630026dd73d963000cfe72d9630026ee72d963000cee72d9630004fd72d9630026ed72d9630004ed72d9630024fc72d9630004fe71d9630004fd71d9630026fa70d96300047d76996300267f64996300067e64996300067d64996300267c64996300267f62996300067e62996300267c62996300267f61996300267c61996300267e609963001cff76596300267c65596300267f7559630004ff7459630014fe7459630004fd7459630014fc74596300fe7f54596300067e54596300067d54596300fe7c54596300fe7f5359630004ff725963000cfe725963000cfc72596300fe7f52596300067e52596300fe7c5259630004ff7159630004fc71596300fe7f51596300fe7c51596300267e50596300267c50596300257f76596300fe7f765963001c7f76596300267f64596300067e64596300067d64596300267c64596300267f62596300067e62596300267c62596300267f61596300267c61596300067f74596300067e74596300067d74596300067c74596300067f73596300067d73596300fe7c73596300067f43596300067e43596300067d43596300067c43596300067f72596300067e72596300067d72596300067c72596300067f42596300067e42596300067d42596300067c42596300067e32596300067c32596300067f71596300067e71596300067d71596300067c71596300067f41596300067e41596300067d41596300067c41596300067f21596300067c21596300fe7f70596300267e70596300267c70596300067f40596300267e40596300067d40596300267c40596300267e30596300267c30596300067f20596300267e20596300267c20596300267e10596300267c10596300ecfd7694e3001e7e6594e300067d6594e300ff5f5394e3020eee6294e3001cff7654e30024fc7654e3001e7e6554e300067d6554e30005ef7254e300f5ec7254e301feee6254e30005fb7054e30025f87054e30026ef6598a30006ee6598a300276e6598a300066e6598a30006ed6598a300276d6598a300066d6598a30026ec6598a300f7ae7498a300f7ad7498a30026ef6498a30006ee6498a30006ed6498a30026ec6498a30026ef6198a30026ec6198a30026ee6098a3000cff7658a300067e6558a300067d6558a30026ec6258a30004ff7558a3001cfe7558a3001cfc7558a30004ff7458a30014fe7458a30004fd7458a30014fc7458a30006ef5258a300f6ee5258a300f6ec5258a30006ef4258a300f6ee4258a30006ed4258a300f6ec4258a300f6ee3258a30004ff7158a30004fc7158a300f6ef2158a300f6ec2158a30026ee2058a30026ec2058a30025ef7658a300f6ef7658a3000cef7658a30026ef6558a30006ee6558a300276e6558a300066e6558a30006ed6558a300276d6558a300066d655
  | 24 => 0xf71597300067e71597300067d71597300067c71597300067f41597300067e41597300067d41597300067c41597300b67f31597300b67c31597300067f21597300067c21597300067f70597300067d705973010e7c70597300067f40597300067e40597300067d40597300067c40597300b67f30597300b67c30597300067f20597300067c20597300c4ff7654f3001e7e6554f300067d6554f30005ef7254f30105ec7254f3000cff7658b300067e6558b300067d6558b300b6ec6258b30004ff7558b3001cfe7558b3001cfc7558b30004ff7458b30014fe7458b30004fd7458b30014fc7458b30106ee4258b30006ed4258b300b6ef3258b300b6ec3258b30004ff7158b30004fc7158b30106ec2158b30106ef2058b30004ff7654b30004fd7654b300b4fc7654b3001e7e6554b300067d6554b30005df7354b300b5dc7354b300acff764cb300057f754cb3010d7c754cb301de7e654cb300067d654cb300b7cc324cb300067e65987300067d65987300d5be7498730005bd74987300b6f7619873001cfe7598730004fd759873001cfc7598730004ff7498730014fe7498730006be7498730014be7498730004fd7498730006bd7498730004bd7498730014fc7498730006de4398730006dd439873000cfe7298730004fd729873000cfc72987300b6f731987300b6f431987300067e65587300067d65587300b6f46158730004ff755873001cfe755873001cfc7558730004ff7458730014fe7458730004fd7458730014fc7458730004ff725873000cfe725873000cfc72587300b6f731587300b6f43158730004ff76947300b4fe7694730004fd769473001e7e65947300067d65947300b5de7394730005dd7394730004ff7654730004fd76547300b4fc765473001e7e65547300067d65547300b75e65cc7300b75d65cc7300b5df74cc730325dd74cc730006de61cc7300b7d661cc7300b7d561cc730025de70cc7300b7da70cc7300b7d970cc73019e7e658c7300067d658c7300d5be748c730005bd748c7300057f754c73010d7c754c73018e7e654c7300067d654c730005ef724c730105ec724c730005df764c730006df764c7300075f754c7300075c754c7300075e654c7300075d654c73031ddf744c73031ddd744c730007cf724c730007cc724c7300b7d7714c730006de614c730025dc704c730004ff76887300b4fe7688730004fd768873010d7e75887300057d758873014e7e65887300067d65887300b5de7388730005dd738873000eee6288730006ed6288730004ff7648730004fd76487300b4fc764873013e7e65487300067d65487300ecfd769433001e7e65943300067d659433001cff76543300b4fc765433001e7e65543300067d6554330005df73543300b5dc73543300fcfd75d9630024ff74d9630014fe74d9630
  | 25 => 0x855003e7c531855000cfe7218550004fd721855000cfc721855003e7f52185500067d521855003e7f511855003ef6511855003ef5511855003e7c50185503357f74545503357d74545500057c73545500067f63545500057f72545501b67e62545501b67c625455001d7f715455001f7771545500077761545500067c61545500077461545500077b70545500257c705455000778705455001e7f605455001f7b6054550004fe76cc550004fd76cc5500b4fc76cc5500057f75cc55001d7c75cc550006f761cc550006f461cc550004fe768c550004fd768c550004fc768c55001d7e758c5500057d758c55011dbe748c550005bd748c550006df638c550006dc638c550004ff764c550004fe764c550004fc764c5500057f754c55001d7c754c550005ef724c550115ec724c550004fe760c550004fd760c5500b4fc760c55001d7e750c5500057d750c550006df630c5500b6dc630c550006f7610c550006f4610c550004fe7688550004fd7688550004fc768855001d7e75885500057d7588550006ef628855000eec62885500076d5288550004ff7648550004fe7648550004fc764855001d7e75485500057d75485500257f749415032d7d74941500057e73941500067f63941500057d72941501267e62941501267c62941500057d71941500067c61941500257e70941500277a70941500267f609415001f7b609415010cfd75d97300b4ff74d9730014fe74d9730004fd74d97300b4fc74d97300b6de73d973000cfe72d9730004fd72d973000cfc72d9730004fe71d9730004fd71d97300b6f970d97300047d76997300b67f64997300067e64997300067d64997300b67c64997300b67e63997300b75e43997300075d43997300b67f62997300067e62997300b67c62997300b67f61997300b67c619973001cff76597300b67c65597300b67f7559730004ff7459730014fe7459730004fd7459730014fc745973010e7f54597300067e54597300067d545973010e7c54597300b67e53597300b67c5359730004ff725973000cfe725973000cfc725973010e7f52597300067e525973010e7c5259730004ff7159730004fc715973010e7f515973010e7c515973010e7f50597300b57f765973010e7f765973001c7f76597300b67f64597300067e64597300067d64597300b67c64597300b75e43597300075d43597300b67f62597300067e62597300b67c62597300b67f61597300b67c61597300067f74597300067e74597300067d74597300067c745973010e7f73597300b67e73597300b67c73597300067f43597300b67e43597300067d43597300b67c43597300067f72597300067e72597300067d72597300067c72597300067f42597300067e42597300067d42597300067c42597300b67f32597300067e32597300b67c32597300067
  | 26 => 0x1d7c758c65012dbe748c650005bd748c650004ff764c650004fd764c650024fc764c6500057f754c65001d7c754c650006de634c650006dd634c650005ef724c650125ec724c6500b4ff760c650024fe760c650004fd760c65001d7e750c6500057d750c650004ff7688650024fe7688650004fd768865001d7e75886500057d758865000eec62886501276e5288650004ff7648650004fd7648650024fc76486500057f754865001d7c754865000eee6248650006ed6248650004ff74d8d50014fe74d8d50004fd74d8d50014fc74d8d500fe7f54d8d500067d54d8d500fede53d8d500fedd53d8d500fe7c53d8d5000cfe72d8d50004fd72d8d5000cfc72d8d500fe7f52d8d50004fe71d8d50004fd71d8d500fe7f51d8d500fe7c50d8d50006df6398d500edf97098d50005bf7458d5011dbc7458d50005ef7258d50115ec7258d50005f77158d50005f47158d5010dfb7058d50006dd6318d500b4ff7418d50014fe7418d50004fd7418d500b4fc7418d500b6de5318d500c6dd5318d5000cfe7218d50004fd7218d5000cfc7218d50004fe7118d50004fd7118d5034d7f7494d5034d7d7494d5001d7e7394d5001f5e7394d500067f6394d500075f6394d500065f6394d500075c6394d500057d7294d5020e7e6294d5020e7c6294d500057d7194d500257e7094d500077a7094d50007797094d5001e7f6094d5001f7b6094d5000cfe76d8950116ee62d895000cfc75d8950004ff74d8950014fe74d8950004fd74d8950014fc74d89500b4fe73d8950004fd73d8950116ee52d89500a6ed52d8950116ee42d8950006ed42d8950116ec32d8950004fe71d8950004fd71d8950116ec21d895001cfd70d8950116ef20d8950116ec6258950345fb70589501157c765495000e7c765495000c7c765495033d7f745495033d7d74549500057c73549500067f635495001d7f725495001f6f72549500076f625495000e7e625495000e7c62549501176c62549500057f71549501176c21549500077b70549500257c705495000778705495001e7f605495001f7b60549501176f2054950004fe76cc950004fd76cc9500b4fc76cc9500057f75cc95001d7c75cc950006ef62cc95000eec62cc9501ef6f52cc950004ff764c950004fe764c950004fc764c9500057f754c95001d7c754c950004ff74d8550014fe74d8550004fd74d8550014fc74d85500b4fe73d8550004fd73d855000cfe72d8550004fd72d855000cfc72d8550076f651d8550076f551d8550006f76198550065f97098550005bf745855011dbc7458550005df7358550005dc7358550005ef7258550115ec7258550085fb7058550006f56118550004ff7418550014fe7418550004fd7418550014fc741855003e7f54185500067d54185500b4fe7318550004fd73185500067e531
  | 27 => 0xd5398e500b6de4398e50006dd4398e5000cfe7298e50004fd7298e5000cfc7298e500067e5298e5010e7c5298e50006de3298e500b6dc3298e50004fe7198e50004fd7198e5010e7c5198e50024fe7098e50024fc7098e5010e7f5098e50026de3098e50026dc3098e50026dc6358e50004ff7458e50014fe7458e50004fd7458e50014fc7458e500eede5358e500eedd5358e50006de4358e50006dd4358e50004ff7258e5000cfe7258e5000cfc7258e50006de3258e50006dc3258e50004ff7158e50004fc7158e50024fc7058e50026de3058e50026dc3058e5035e7f6454e5035e7d6454e5001d7f7354e5001f5f7354e500b67e6354e500075e6354e500075d6354e500076f7254e501257e7254e501257c7254e500076c7254e501256c7254e500057c7154e500057f7054e500077b7054e50007787054e5001e7e6054e5001f7a6054e5000cff7658a5001d7c7558a50026ec6258a501276e5258a50004ff7458a50014fe7458a50004fd7458a50014fc7458a50004ff7358a500b4fc7358a500967f5358a500067d5358a501267e5258a50126ee5258a501266e5258a50096ed5258a501267c5258a50126ee4258a50006ed4258a50126ec3258a50004ff7158a50004fc7158a500967c5158a50126ef2158a50024fe7058a50024fc7058a500967f5058a50026ee2058a50026ec2058a500b4ff76cca50024fe76cca50004fd76cca5001d7e75cca500057d75cca5000eee62cca50006ed62cca501276c52cca50004ff764ca50004fd764ca50024fc764ca500057f754ca5001d7c754ca50026f76198650004ff7498650014fe7498650004fd7498650014fc74986500b4fe7398650004fd739865000cfe7298650004fd729865000cfc7298650086f65198650086f55198650006f64198650006f54198650024fe7098650026f61098650026f41098650005ef7258650125ec7258650026f46158650004ff7458650014fe7458650004fd7458650014fc7458650004ff73586500b4fc73586500667f53586500067d5358650004ff7258650006ef7258650004ef725865000cfe725865000cfc7258650006ec725865000cec72586500067e52586500667c5258650066f65158650066f551586500667c5158650006f64158650006f54158650024fc70586500667f5058650026f61058650026f410586503567f64946503567d64946500057d73946500067e63946501257e72946501257c72946500067d629465001d7e719465001f7671946500077661946500067d61946500077561946500077a70946500057d709465000779709465001e7e609465001f7a60946500b4ff76cc650024fe76cc650004fd76cc65001d7e75cc6500057d75cc6500b6de63cc650006dd63cc650004ff768c650024fe768c650004fd768c6500057f758c650
  | 28 => 0x8d21014fe7498d21004fd7498d210b4fc7498d210b4fe7398d211a4fd7298d210b6ed7298d2117cfd7198d210b6f57198d211a6ec2198d21024fe7098d21004fd7098d211a6ef2098d210057f7558d2113d7c7558d211a5f77158d21004ff7558d210067f7558d210047f7558d2101cfe7558d2101cfc7558d210067c7558d2101c7c7558d21004ff7458d21014fe7458d21004fd7458d21014fc7458d21006df7358d2117cff7258d21006ef7258d21004ef7258d211a4ff7158d21006f77158d21004ff7058d21024fc7058d21194fe7618d2113d7e7518d210057d7518d21006dd6318d2101cfe7518d210b67e7518d2101c7e7518d21004fd7518d210b67d7518d210047d7518d210b4fc7518d210b4ff7418d21014fe7418d21004fd7418d210b4fc7418d210b6de7318d21006df5318d210b6dc5318d210b6de4318d21006dd4318d210b4ff7218d21154fd7218d210b6df3218d21156dd3218d21156ec2118d21024fe7018d21004fd7018d21156ef2018d210b4ff7694d21004fe7694d21004fd7694d210b4fc7694d210067f6594d2101e7c6594d2113f5f5394d21004ff7654d21004fe7654d21004fd7654d21004fc7654d2101e7e6554d210067d6554d21005ef7254d2100dec7254d2136cfe769452101e7e65945210067d659452113f77519452101cff765452100cfe76545211b4fd765452100cfc76545210067f655452101e7c6554521005ef725452100dec725452100cfe76cc52100cfc76cc521006df63cc5210b6dc63cc52100dee72cc521005ed72cc521154fe768c521135be748c521005bd748c5210b4ff764c52100cfe764c52117cfd764c52100cfc764c5210057f754c52113d7c754c521006df634c521006dc634c521005ef724c52100dec724c521194fe760c52113d7e750c5210057d750c521007d5310c5210076e75885210076d7588521006ef6588521006ed6588521366ef6488521366ed6488521006ee6388521006ec638852100dee718852100fe6718852100eef618852100fe76188521005ed708852101cfe75d8121004fd75d812101cfc75d8121004ff74d8121014fe74d8121004fd74d8121014fc74d81210b4fe73d8121004fd73d812107efa20d8121006fb60981210057f755812113d7c7558121005bf7458121135bc7458121005df7358121005dc735812113d7e75181210057d7518121006f9601812101cfe75181210267e751812101c7e7518121004fd75181210267d75181210047d7518121024fc7518121024ff7418121014fe7418121004fd7418121024fc74181210b4fe7318121004fd7318121006ee211812102eec2118121026ef2018121026fa201812102ef92018121026df6398e500b4ff7498e50014fe7498e50004fd7498e500b4fc7498e500b67f5398e500b6de5398e5010ed
  | 29 => 0x67d659462100dee7294621005ed72946210076d529462114f7751946211c7e72194621374ff765462101e7e65546211b67d655462100dee72546211b76e52546211b7e7215462117cfd76cc6211ae7e65cc6210067d65cc62100dec72cc62100cff768c62100cfd768c62119e7e658c6210067d658c621145be748c621005bd748c621006de638c621006dd638c62100dee728c621005ed728c6211a4ff764c6210057f754c62114d7c754c62118e7e654c6210067d654c621005ef724c62100dec724c62100cff760c62100cfd760c62114d7e750c6210057d750c6211667e650c6210067d650c6210b6de630c621006dd630c62100dee720c621005ed720c621007d5310c62114d7e75d82210057d75d82210067e65d82210067d65d82210067e65982210067d6598221006fb609822101cfe7598221004fd7598221024fc7598221024ff7498221014fe7498221004fd7498221024fc74982210b4fe7398221004fd7398221026fa209822106ef920982210067e65582210067d6558221005bf7458221145bc7458221004ff755822101cfe755822101cfc7558221004ff7458221006bf7458221004bf7458221014fe7458221004fd7458221014fc7458221006bc7458221014bc7458221004ff73582210b4fc7358221056ee5258221006ed5258221056ee4258221006ed4258221006ef3258221056ec3258221056ef2158221056fa2058221056ec205822114d7e75182210057d75182210067e65182210067d6518221145be7418221005bd7418221005de7318221005dd7318221006f9601822101cfe76d952113e7e65d9521004ff74d9521014fe74d9521004fd74d9521014fc74d952113e7f54d95210067d54d95210b4fe73d9521004fd73d952113e7c53d95211c4ff72d95211c4fd72d95211c67f52d95211c67d52d952100cfd71d952113e7f51d95211c6ec21d9521024fe70d9521004fd70d952113e7c50d95211c6ef20d952113e7c6559521005df7359521005dc7359521375f771595211c4ff75595210067f7559521004ff7459521014fe7459521004fd7459521014fc7459521004ff7359521006df7359521004df73595210b4fc7359521006dc7359521004dc735952113e7f53595211b4ff7259521006ef72595211b67e52595211b67c5259521374ff7159521006f7715952113e7c51595211b6ec2159521004ff7059521024fc705952113e7f50595211b6ef205952101cfe75d8d21004fd75d8d2101cfc75d8d21004ff74d8d21014fe74d8d21004fd74d8d21014fc74d8d21006df53d8d21006dc53d8d21006de43d8d21006dd43d8d21194ff72d8d21194fd72d8d21196df32d8d21196dd32d8d21024fe70d8d21004fd70d8d21006df6398d2117df57198d2101cfe7598d21004fd7598d210b4fc7598d210b4ff749
  | 30 => 0xe21596211b67d21596211b67c21596210067f70596210067e70596210067d70596210067c70596210067f40596210067e40596210067d40596210067c40596211b67f20596211b67e20596211b67d20596211b67c205962114d7e75d8e210057d75d8e210067e65d8e210067d65d8e21145be74d8e21005bd74d8e21155f671d8e2101cfe75d8e210067e75d8e2101c7e75d8e21004fd75d8e210067d75d8e210047d75d8e2101cfc75d8e21004ff74d8e21014fe74d8e21006be74d8e21014be74d8e21004fd74d8e21006bd74d8e21004bd74d8e21014fc74d8e21006ed72d8e21196ee42d8e21006ed42d8e21196ec32d8e21154fe71d8e21006f671d8e21024fe70d8e21004fd70d8e2117cfd7698e210067e6598e210067d6598e21006df6398e2101cfe7598e21004fd7598e210b4fc7598e210b4ff7498e21014fe7498e21004fd7498e210b4fc7498e21006df4398e210b6dc4398e210b6df3298e211a6dd3298e21024fe7098e21004fd7098e210067e6558e210067d6558e21004ff7558e2101cfe7558e2101cfc7558e21004ff7458e21014fe7458e21004fd7458e21014fc7458e21006df7358e21006df4358e21006dc4358e21006ef7258e2117eee4258e21006ed4258e2117edf3258e2117edd3258e2117eec3258e21004ff7058e21024fc7058e2114d7e7518e210057d7518e210067e6518e210067d6518e21006dd6318e21195f67118e2101cfe7518e210b67e7518e2101c7e7518e21004fd7518e210b67d7518e210047d7518e210b4fc7518e210b4ff7418e21014fe7418e21004fd7418e210b4fc7418e210b4fe7318e210b6de7318e210b6ed7218e21194fe7118e210b6f67118e21024fe7018e21004fd7018e210b4ff7694e21004fe7694e21004fd7694e210b4fc7694e2101e7e6594e210067d6594e2114f5f5394e2100dec7294e2120f6e5294e21004ff7654e21004fe7654e21004fd7654e21004fc7654e2101e7e6554e210067d6554e21005ef7254e2100dec7254e2114def7654a2101eef7654a2101cef7654a2100def7554a2100f6f7554a2101eee6554a2114f6e6554a210076d6554a2101eec6554a21385ef7454a21385ed7454a21005ec7354a2114f6f5354a210076d5354a21005ef7154a21007e77154a21007e47154a2100eee6154a2100fe66154a2114f6c5154a21005ec7054a2114f6f5054a21006ed76cca21005ef75cca21005ed75cca211eeee65cca210076e65cca211ee6e65cca210076d65cca211eeec65cca2137def74cca2137ded74cca2100dee73cca2100fce73cca21006ef63cca21007ce63cca21006ed63cca21007cd63cca21007e671cca21005ed71cca21007e571cca2100eee61cca2100fe661cca21005ee70cca2100cff769462101cfe769462100cfd769462101e7e6594621
  | 31 => 0xc431396de614c431007d6514c431007d5514c43138fd6414c43138fd5414c431005dc704c4310b5f7764c431006f7764c431004f7764c43100777754c43100774754c4310b776654c4310b775654c4310b5f7734c431007d7734c4310b6f6634c4310b7d6634c4310b7d6534c431007d5534c4310b7d6434c43138fd5434c431007e7724c431007e4724c4310b7d7324c431007d5324c4310067e65980310067d65980310b6fb609803101cfe7598031004fd7598031024fc7598031024ff7498031014fe7498031004fd7498031024fc749803100cfe7298031004fd7298031024fc7298031026fa4098031006f940980310b6fb3098031026f830980310067e65580310067d6558031005bf745803115dbc74580310b6f86058031004ff755803101cfe755803101cfc7558031004ff7458031006bf7458031004bf7458031014fe7458031004fd7458031014fc7458031006bc7458031014bc7458031006de4358031006dd4358031004ff725803100cfe725803100cfc7258031006df3158031006dd3158031006fa4058031006f940580310b6fb30580310b6f8305803114e7e65d962136df671d96211b4fd75d9621004ff74d9621014fe74d9621004fd74d9621014fc74d96210b4fe73d9621004fd73d9621006ed72d962136cfe71d9621006f671d9621024fe70d9621004fd70d96211b47d76996210067f64996210067e64996210067d64996210067c64996213776e729962114f6d72996213767d62996213776e42996210076d42996213776c32996213767e61996213776f21996213777721996213777421996213776c209962101cff765962114e7c65596210067f7559621004ff7459621014fe7459621004fd7459621014fc745962114e7f54596210067e54596210067d545962114e7c5459621004ff73596210b4fc735962114e7f535962114e7c53596211b67f52596211b67d525962100cfc715962114e7c5159621004ff7059621024fc705962114e7f505962114e7c50596213757f765962114e7f765962101c7f76596210067f64596210067e64596210067d64596210067c64596211b76e72596210076d72596211b76e42596210076d42596211b76c32596211b76f21596211b77721596211b77421596211b76c20596210067f74596210067e74596210067d74596210067c74596210067f73596210067e73596210067d73596210067c73596210067f43596210067e43596210067d43596210067c43596211b67f72596211b67e72596211b67d72596211b67c72596211b67f42596211b67e42596211b67d42596211b67c42596211b67f32596211b67e32596211b67d32596211b67c325962114e7f71596211b67e71596211b67c71596210067f41596210067e41596210067d41596210067c41596211b67f21596211b67
  | 32 => 0xb67f7559431004ff7459431014fe7459431004fd7459431014fc74594311667f54594310067e54594310067d54594311667c54594310b4fe73594310b4fc73594310b67e53594310b67c5359431004ff725943100cfe725943100cfc72594311667f52594310067e52594311667c5259431164fc71594311667c5159431004ff7059431024fc70594311667f50594311667c50594310b57f76594311667f765943101c7f76594310b67f64594310067e64594310067d64594310b67c64594310b75e43594310075d43594310b67f62594310067e62594310b67c62594310b67f60594310b67c60594310067f74594310067e74594310067d74594310067c74594311667f73594310b67e73594310b67c73594310067f43594310b67e43594310067d43594310b67c43594310067f72594310067e72594310067d72594310067c72594310067f42594310067e42594310067d42594310067c42594310b67f32594310067e32594310b67c32594311667f71594310067e71594310067c71594310067f41594310067e41594310067d41594310067c41594310b67f31594310b67c31594310067f21594310067c21594310067f70594310067e70594310067d70594310067c70594310067f40594310067e40594310067d40594310067c40594310b67f30594310b67c30594310067f20594310067c20594311acff7654c3101e7e6554c310067d6554c31005ef7254c31155ec7254c3100cff76588310067e65588310067d65588310b6ec6258831004ff755883101cfe755883101cfc7558831004ff7458831014fe7458831004fd7458831014fc7458831156ee4258831006ed42588310b6ef32588310b6ec3258831156ec2158831004ff7058831024fc7058831156ef2058831004ff7654831004fd76548310b4fc765483101e7e65548310067d6554831005df73548310b5dc73548311a4ff764c8310057f754c8311657c754c8311de7e654c8310067d654c8310b7cc324c83119cff76944310b4fe769443101cfd76944310b4fc769443101e7e65944310067d65944310b5de7394431005dd739443119cff765443101e7e65544310067d65544310b75e65cc4310b75d65cc4310b5df74cc4313b5dd74cc431005de70cc43119e7e658c4310067d658c43115dbe748c431005bd748c43139ddd738c4313aede638c4310b776658c4310b775658c4313a7b6748c431007b5748c4310b5f5738c4310b6f6638c4310b7d6638c4310b7d6438c4313a7d5438c431004ff764c4310057f754c4311657c754c43118e7e654c4310067d654c431005ef724c431155ec724c431005df764c431006df764c431004df764c4310075f754c4310075c754c4310075e654c4310075d654c43139ddf744c43139ddd744c431007cf724c431007cc724c4310b5df714
  | 33 => 0xe70d8931006ed70d8931006ec70d8931006ef50d8931006ec50d8931006ef40d8931006ee40d8931006ed40d8931006ec40d89310057f755893118d7c75589310067f65589310067c655893117eec6258931005ee761893117eee7618931006ef65189310076f65189310066f6518931006ee6518931006ed6518931006ec65189310076c65189310066c651893117fae741893117fad7418931006ef6418931006ee6418931006ed6418931006ec6418931004ff7654931004fe7654931004fc76549310067f655493101e7c6554931006ef625493100eec6254931194fe76cc9310067f65cc9311ee7c65cc93100eec62cc93100cfc764c9310057f754c93118d7c754c9310067f654c9311de7c654c931006ef624c93100eec624c931005f7714c931005f4714c9311acfe76945310067f659453101e7c6594531006ef62945311c6ec629453118f77519453101cff765453118cfd765453101cfc76545310067f655453101e7c6554531005df7354531005dc7354531006ef62545311b6ec62545310067f65cc5311ae7c65cc531006ef62cc5311a6ec62cc5310077765cc5310077465cc531007e762cc531007e462cc5310067f658c53119e7c658c531185be748c531005bd748c531006ef628c531196ec628c5310075f658c5310075c658c5313bf9e748c5310079d748c5313bedf648c5313bedd648c531007cf628c531007cc628c531007d7618c531005dd708c5310067f65d81310067c65d8131006ef62d8131006ec62d813101cfe75d8131004fd75d813101cfc75d8131004ff74d8131014fe74d8131004fd74d8131014fc74d813100cfe72d8131004fd72d813100cfc72d8131006fb40d8131006f840d813118d7e75981310057d75981310067f65981310067c659813117dee7298131005ed7298131006ef6298131006ec6298131006fb60981310057f755813118d7c75581310067f65581310067c6558131005bf7458131185bc7458131005ef725813117dec7258131006ef6258131006ec62581310067f65181310067c6518131006ef6218131006ec6218131006f9601813101cfe7518131004fd7518131024fc7518131024ff7418131014fe7418131004fd7418131024fc741813100cfe7218131004fd7218131024fc7218131006de3118131006fb4018131026f84018131164fd75d94310b4ff74d9431014fe74d9431004fd74d94310b4fc74d94310b4fe73d94310b6de73d943100cfe72d9431004fd72d943100cfc72d943119cfe71d94310b6f671d9431024fe70d9431004fd70d94310047d76994310b67f64994310067e64994310067d64994310b67c64994310b67e63994310b75e43994310075d43994310b67f62994310067e62994310b67c62994310b67f60994310b67c609943101cff76594310b67c6559431
  | 34 => 0x95310067e52d953118e7c52d953118cfd71d953118e7f51d9531024fe70d9531004fd70d953118e7f50d953118e7c50d953118d7e76d953101c7e76d95310067f64d95310067e64d95310067d64d95310067c64d95310067e62d95310067c62d95310067f74d95310067e74d95310067d74d95310067c74d95310067f73d953118e7e73d95310067d73d95310067f43d95310067e43d95310067d43d95310067c43d95310067f72d95310067e72d95310067d72d95310067c72d95310067f42d95310067e42d95310067d42d95310067c42d95310067e32d95310067c32d95310067f71d953118e7e71d95310067d71d95310067f41d95310067e41d95310067d41d95310067c41d95310067f21d95310067c21d95310067f70d95310067e70d95310067d70d95310067c70d95310067f40d95310067e40d95310067d40d95310067c40d95310067f20d95310067c20d953118e7c6559531005ef725953117dec725953118cff75595310067f7559531004ff7459531014fe7459531004fd7459531014fc745953119cff7359531006df7359531004ff7259531006ef7259531004ef725953100cfe725953100cfc7259531006ec725953100cec72595311acff7159531006f77159531004ff7059531024fc70595310057e761953118e7e76195310047e76195310067f64195310067e64195310067d64195310067c64195310067e62195310067c621953119cfe7694d310067f6594d3101e7c6594d3118f5f5394d3120eec6294d3101cfc7654d310067f6554d3101e7c6554d31005ef7254d3117dec7254d311feec6254d31005f77154d31005f47154d3100cfe76d89310067f65d89310067c65d893117eee62d893101cfe75d8931004fd75d893101cfc75d8931004ff74d8931014fe74d8931004fd74d8931014fc74d8931006ef52d893117eee52d893117eec52d8931006ef42d893117eee42d8931006ed42d893117eec42d893117eee32d893117eef21d8931024fe70d8931004fd70d893117eef20d893117eec20d893117dee76d893100cee76d8931006ef65d89310076f65d89310066f65d8931006ee65d8931006ed65d8931006ec65d89310076c65d89310066c65d8931006ef64d8931006ee64d8931006ed64d8931006ec64d8931006ef75d8931006ee75d8931006ed75d8931006ec75d8931006ef74d8931006ee74d8931006ed74d8931006ec74d8931006ef54d8931006ee54d8931006ed54d8931006ec54d8931006ef73d893117eee73d8931006ef53d8931006ee53d8931006ed53d8931006ec53d8931006ef43d8931006ee43d8931006ed43d8931006ec43d8931006ef71d893117eee71d8931006ed71d8931006ef51d8931006ec51d8931006ef41d8931006ee41d8931006ed41d8931006ec41d8931006ef70d8931006e
  | 35 => 0x16ebc7159231006bf5159231006bc515923116ebe3159231006bf2159231006bc2159231006bf7059231006be7059231006bd7059231006bc7059231006bf5059231006bc5059231006bf2059231006bc205923118cfd7694e310067f6594e3101e7c6594e31216be6494e31006bd6494e3119f5f5394e3101cff7654e3101e7e6554e310067d6554e31206be6454e31006bd6454e31005ef7254e31195ec7254e31005f77154e31005f47154e3119d7e75d8a310057d75d8a3116dbe74d8a31005bd74d8a31006be64d8a31006bd64d8a31196ee62d8a3100cff7658a31006be6458a31006bd6458a31196ec6258a31004ff7558a3101cfe7558a3101cfc7558a31004ff7458a31014fe7458a31004fd7458a31014fc7458a31006ef5258a31196ec5258a31196ee3258a31196ec2158a31004ff7058a31024fc7058a31196ef2058a31004ff7654a31004fd7654a31004fc7654a310067f6554a3101e7c6554a311f6be6454a31006bd6454a31005df7354a31005dc7354a3117cfd76cca311e6be64cca31006bd64cca3100eec62cca3100cff764ca310057f754ca3119d7c754ca311d6be644ca31006bd644ca3100eee624ca31006ed624ca31197cc324ca31005f7714ca31005f4714ca3101cfe769463101cfd769463101e7e65946310067d65946311cebe6494631006bd6494631005de7394631005dd739463119f775194631164ff76546310067f655463101e7c65546311bebe6454631006bd6454631176be64cc631006bd64cc631005dd76cc631006dd76cc6313addf74cc6313addd74cc6313c79e64cc6310079d64cc631007d651cc631007d551cc631005de70cc631005f576cc6310b6f576cc6313c7b664cc631007b564cc6310b7d653cc631007d553cc63116dbe74d8231005bd74d8231006be64d8231006bd64d8231006be6498231006bd6498231006fb609823101cfe7598231004fd7598231024fc7598231024ff7498231014fe7498231004fd7498231024fc749823100cfe7298231004fd7298231024fc72982310057f755823119d7c7558231006be6458231006bd6458231004ff75582310067f75582310047f755823101cfe755823101cfc75582310067c755823101c7c7558231004ff7458231014fe7458231004fd7458231014fc7458231006de4358231006dd4358231004ff725823100cfe725823100cfc7258231006df315823119d7e75182310057d751823116dbe7418231005bd7418231006be6418231006bd6418231195ee7218231005ed7218231006f9601823101cfe76d953118e7e65d9531004ff74d9531014fe74d9531004fd74d9531014fc74d953118e7f54d95310067e54d95310067d54d953118e7c54d953118cfd73d953118e7f53d953100cfe72d9531004fd72d953100cfc72d953118e7f52d
  | 36 => 0xc70597311ae7c5059731164ff7654f310b67f6554f310b67c6554f31005ef7254f311a5ec7254f3100cff7658b310057f7558b311ad7c7558b310b6ec6258b31004ff7558b310067f7558b310047f7558b3101cfe7558b3101cfc7558b310067c7558b3101c7c7558b31004ff7458b31014fe7458b31004fd7458b31014fc7458b311a6ee5258b311a6ee4258b31006ed4258b310b6ef3258b310b6ec3258b311a6ef2158b31004ff7058b31024fc7058b311a6ec2058b31004ff7654b31004fd7654b310b4fc7654b3101e7e6554b310067d6554b3100eee6254b31006ed6254b31154ff764cb310057f754cb311ad7c754cb3118cfd76947310067f659473101e7c659473101cff76547310b4fc765473101e7e65547310067d6554731005df73547310b5dc73547311ad7e75983310057d75983311a5ee7298331005ed72983310b6fb609833101cfe75983310267e759833101c7e7598331004fd75983310267d75983310047d7598331024fc7598331024ff7498331014fe7498331004fd7498331024fc749833100cfe7298331026ee729833100cee7298331004fd7298331026ed7298331004ed7298331024fc72983310b6fb3098331026f830983310b6f86058331004ff755833101cfe755833101cfc7558331004ff7458331014fe7458331004fd7458331014fc7458331004ff725833100cfe725833100cfc72583310b6fb30583310b6f8305833119e7e65d963116dbe74d9631005bd74d9631006be64d9631195ee72d9631005ed72d963119cfd75d9631004ff74d9631014fe74d9631006be74d9631014be74d9631004fd74d9631006bd74d9631004bd74d9631014fc74d963119e7f54d96310067d54d9631006dd73d963119e7c53d963100cfe72d9631006ee72d963100cee72d9631004fd72d9631006ed72d9631004ed72d963100cfc72d963119e7f52d9631006f671d963119e7f51d9631024fe70d9631004fd70d963119e7c50d963101cff765963119e7c6559631006be64596310067f7559631004ff7459631014fe7459631004fd7459631014fc745963119e7f5359631004ff725963100cfe725963100cfc72596310067e525963119e7c525963119e7c5159631004ff7059631024fc705963119e7f505963116dbf765923116ebf7659231014bf7659231006bf6559231006be6559231006bd6559231006bc655923116f9e73592310079d7359231006be6259231006bc6259231006bf7559231006be7559231006bd7559231006bc755923116ebf735923116ebe7359231006bd735923116ebc7359231006bf5359231006bc5359231006bf7259231006be7259231006bd7259231006bc7259231006bf5259231006be5259231006bc5259231006be3259231006bc325923116ebf7159231006be715923116ebd7159231
  | 37 => 0x8d510b4ff7418d51014fe7418d51004fd7418d510b4fc7418d510b67f5318d510b6de5318d51166dd5318d510b6de4318d51006dd4318d5100cfe7218d51004fd7218d5100cfc7218d510067e5218d511667c5218d51006de3218d510b6dc3218d511667c5118d51024fe7018d51004fd7018d511667f5018d513de7f6454d513de7d6454d5101d7f7354d5101f5f7354d510075f6354d510b67c6354d510075c6354d510076f7254d511b57e7254d511b57c7254d510076c7254d511b56c7254d51007777154d510057c7154d51007747154d5101e7f6154d5101f776154d510057f7054d5100cfe76d895101d7e75d89511b6ee62d89511b76e52d8951004ff74d8951014fe74d8951004fd74d8951014fc74d89510b4fe73d8951004fd73d895114e7f53d89510067d53d89511b67e52d89511b6ee52d89511b66e52d895114eed52d89511b67c52d89511b6ee42d8951006ed42d89511b6ec32d895101cfd71d895114e7c51d89511b6ef21d8951024fe70d8951004fd70d895114e7f50d89511b6ec20d8951005df7358951005dc73589511b6ec62589513d5f77158951004fe76cc951004fd76cc9510b4fc76cc95101d7e75cc9510057d75cc951006ef62cc95100eec62cc9511b76c52cc951004ff764c951004fe764c951004fc764c9510057f754c95101d7c754c9513ce7f64945513ce7d64945510057d73945510067c63945511b57e72945511b57c72945510067f629455101d7e719455101f76719455101e7f619455101f7761945510057d7094551004ff74d8151014fe74d8151004fd74d8151014fc74d81510b4fe73d8151004fd73d815100cfe72d8151004fd72d815100cfc72d8151086fa50d8151006fb6098151005bf74581511bdbc7458151005df7358151005dc7358151005ef72581511b5ec72581511b5ee7218151005ed7218151006f96018151024ff7418151014fe7418151004fd7418151024fc74181510b4fe7318151004fd731815103e7f53181510067d531815100cfe7218151026ee721815100cee7218151004fd7218151026ed7218151004ed7218151024fc72181510067e521815103e7c52181510067e511815103e7c51181510267f5018151026fa501815103ef950181511acfd75d97310b4ff74d9731014fe74d9731004fd74d97310b4fc74d97310b6de73d97310b67f53d973100cfe72d9731004fd72d973100cfc72d97310067e52d97311ae7c52d97310b6f571d97311ae7c51d9731024fe70d9731004fd70d97311ae7f50d973101cff76597310b67c65597310b67f7559731004ff7459731014fe7459731004fd7459731014fc74597311ae7f54597310067d54597310b67e53597310b67c5359731004ff725973100cfe725973100cfc72597311ae7f52597311ae7f5159731004ff7059731024f
  | 38 => 0x24fc7418132004fe7118132004fd7118132026fa20181320aef920181321cdbe74d8e51005bd74d8e511c5ee72d8e51005ed72d8e51165f671d8e51006df6398e510b4ff7498e51014fe7498e51004fd7498e510b4fc7498e510b6de5398e511aedd5398e5100cfe7298e51004fd7298e5100cfc7298e51024fe7098e51004fd7098e51004ff7458e51014fe7458e51004fd7458e51014fc7458e5118e7f5458e510067d5458e5118ede5358e5118edd5358e5118e7c5358e51004ff7258e5100cfe7258e5100cfc7258e5118e7f5258e5118e7f5158e51004ff7058e51024fc7058e5118e7c5058e51006dd6318e5119df67118e513f57f7494e513f57d7494e5101d7e7394e5101f5e7394e510075e6394e510067d6394e510075d6394e510065d6394e510057d7294e5120e7e6294e5120e7c6294e51007767194e510057d7194e51007757194e51005757194e5101e7e6194e5101f766194e510057e7094e511c6ee62d8a513edf671d8a5100cff7658a511c6ec6258a51004ff7458a51014fe7458a51004fd7458a51014fc7458a51004ff7358a510b4fc7358a511c6ee5258a5113eed5258a511c6ee4258a51006ed4258a511c6ec3258a5101cfc7158a511c6ec2158a51004ff7058a51024fc7058a511c6ef2058a511c57f7654a5100e7f7654a5100c7f7654a513e57f7454a513e57d7454a510057c7354a510067d6354a5101d7f7254a5101f6f7254a5100e7e6254a511c76e6254a510076d6254a5100e7c6254a510057f7154a51007777154a51007747154a5101e7e6154a5101f766154a511c76c2154a510057c7054a511c76f2054a510b4ff76cca51004fe76cca51004fd76cca510057f75cca5101d7c75cca5100eee62cca51006ed62cca511ef6f52cca51004ff764ca51004fd764ca51004fc764ca510057f754ca5101d7c754ca51006fb6098251024ff7498251014fe7498251004fd7498251024fc74982510b4fe7398251004fd739825100cfe7298251004fd7298251024fc7298251026fa5098251076f95098251004ff7458251014fe7458251004fd7458251014fc74582510667f54582510067d5458251004ff73582510b4fc73582510067e53582510667c5358251004ff725825100cfe725825100cfc72582510667f52582510067d52582510667f5158251066fa50582510667c50582511cdbe7418251005bd7418251005de7318251005dd73182511c5ee7218251005ed7218251006f96018251004ff74d8d51014fe74d8d51004fd74d8d51014fc74d8d5119ede53d8d5119edd53d8d51006de43d8d51006dd43d8d5100cfe72d8d51004fd72d8d5100cfc72d8d51006de32d8d51006dc32d8d51024fe70d8d51004fd70d8d51006df6398d5118df57198d51005ef7258d511b5ec7258d511adf77158d51006dd631
  | 39 => 0xd72d953220e7c72d953220e7f42d953220e7e42d953220e7d42d953220e7c42d953220e7f32d953220e7e32d953220e7c32d95320067f71d95320067e71d95320067d71d95320067c71d95320067f41d95320067e41d95320067d41d95320067c41d953220e7f21d953220e7e21d953220e7d21d953220e7c21d95320067f70d95320067e70d95320067d70d95320067c70d95320067f40d95320067e40d95320067d40d95320067c40d953220e7f20d953220e7e20d953220e7d20d953220e7c20d95321de7c655953240ddf735953220cff75595320067f7559532004ff7459532014fe7459532004fd7459532014fc745953240cff7359532006df73595321fcff7259532006ef72595321ecef7259532004ff7159532004fc7159532004ff7059532024fc705953220d7e76195321de7e761953220c7e76195320067f64195320067e64195320067d64195320067c64195324067f63195324067f62195324076e42195320076d42195324075e32195324075c32195324076c3219532404fe7694d3220e7f6594d3201e7c6594d321df5f5394d320b7cc3294d3201cff7654d3200cfe7654d321fcfd7654d3200cfc7654d320067f6554d3201e7c6554d32005ef7254d3200dec7254d321ffcc3254d320076f65cc9321eeee65cc9321eeec65cc9320076c65cc9321ee6c65cc9320b5ef74cc9323fded74cc93200dee73cc93200fce73cc93200eef63cc93200fcf63cc9320067f65d85320067c65d853201cfe75d8532004fd75d853201cfc75d8532004ff74d8532014fe74d8532004fd74d8532014fc74d8532006f641d8532006f541d85321a6f621d8532024fe70d8532004fd70d85321dd7e75985320057d75985320067f65985320067c65985321d5be7498532005bd7498532006f761985320057f75585321dd7c75585320067f65585320067c65585320067f65185320067c6518532006f5611853201cfe7518532004fd751853201cfc7518532004ff7418532014fe7418532004fd7418532014fc7418532156ee4218532006ed4218532006ef3218532156ec3218532006f64118532006f54118532156f52118532024fe7018532004fd70185320067f65d81320067c65d813201cfe75d8132004fd75d813201cfc75d8132004ff74d8132014fe74d8132004fd74d8132014fc74d8132106ee42d8132006ed42d8132006ef32d8132106ec32d8132004fe71d8132004fd71d8132106fa20d81321dd7e75981320057d75981320067f65981320067c6598132006fb60981320057f75581321dd7c75581320067f65581320067c6558132005bf74581321d5bc7458132005f77158132005f471581320067f65181320067c6518132006f9601813201cfe7518132004fd7518132024fc7518132024ff7418132014fe7418132004fd7418132
  | 40 => 0x973220eef20d973201cff76597320b67c655973200dec72597321ef6f52597320b67f7559732004ff7459732014fe7459732004fd7459732014fc74597321ee7f54597320067d545973200cfe735973200cfc73597320b67e53597320b67c53597321eeef72597321fe7f52597321eeef52597321ee6f52597321fe7d52597321feec5259732004ff7159732004fc71597321ee7f51597321feec2159732004ff7059732024fc70597321ee7c50597321feef205973240cff7654f320b67f6554f320b67c6554f321edef7254f3200dec7254f321ef6f5254f321ffce3254f321e5be7498732005bd74987320b6f7619873201cfe7598732004fd759873201cfc7598732004ff7498732014fe7498732006be7498732014be7498732004fd7498732006bd7498732004bd7498732014fc749873200cfe73987320b6f731987320b6f43198732196f52198732024fe7098732004fd70987320057f75587321ed7c75587320b6f46158732004ff75587320067f75587320047f755873201cfe755873201cfc75587320067c755873201c7c7558732004ff7458732014fe7458732004fd7458732014fc745873200cfc73587320b6f731587320b6f4315873217ef6215873217eec2158732004ff7058732024fc705873217eef20587321ed7e75983320057d75983320b6fb609833201cfe75983320267e759833201c7e7598332004fd75983320267d75983320047d7598332024fc7598332024ff7498332014fe7498332004fd7498332024fc749833200cfe7398332004fe7198332004fd71983320f6ec21983320b6fb3098332026f83098332026ef2098332026fa20983320f6f92098332005bf74583321e5bc74583320b6f86058332004ff755833201cfe755833201cfc7558332004ff7458332006bf7458332004bf7458332014fe7458332004fd7458332014fc7458332006bc7458332014bc745833200cfc7358332004ff7158332004fc71583320b6fb30583320b6f830583320defa205833201cfe76d95321de7e65d9532004ff74d9532014fe74d9532004fd74d9532014fc74d95321de7f54d95320067e54d95320067d54d95321de7c54d953200cfd73d95321de7f53d95320b4ff72d953220cfd72d953220e7f52d953220e7d52d9532004fe71d9532004fd71d95321de7f51d95321de7c51d9532024fe70d9532004fd70d95321de7f50d95321de7c50d95324057e76d953201c7e76d95320067f64d95320067e64d95320067d64d95320067c64d953220f6e42d95320076d42d953220f5e32d953220f5c32d953220f6c32d95320067f74d95320067e74d95320067d74d95320067c74d953220e7f73d95321de7e73d953220e7d73d95320067f43d95320067e43d95320067d43d95320067c43d953220e7f72d953220e7e72d953220e7
  | 41 => 0x4fd7218153024fc7218153004fe7118153004fd7118153026fa50181530c6f9501815300cfd75d8d52004ff74d8d52014fe74d8d52004fd74d8d52014fc74d8d5242ede53d8d5242edd53d8d52006df43d8d52006dc43d8d5201cfd72d8d5240edf32d8d52004fe71d8d52004fd71d8d52024fe70d8d52004fd70d8d52006df6398d521dded7298d521edef7258d52006dd6318d5200cfd7518d520b67d7518d520b4ff7418d52014fe7418d52004fd7418d520b4fc7418d520b67f5318d520b6de5318d52426dd5318d52006df4318d520b6dc4318d520b4ff7218d5201cfd7218d52426ef5218d524067e5218d524067c5218d52406ec5218d520b6df3218d52406dd3218d52004fe7118d52004fd7118d524267c5118d52406ec2118d52024fe7018d52004fd7018d524267f5018d52406ef2018d5200d7c7654d521fe7c7654d5200c7c7654d5241e7f6454d5241e7d6454d5201d7f7354d5201f5f7354d520075f6354d520b67c6354d520075c6354d520076f7254d5200d7e7254d5200d7c7254d521ff6c7254d5200d6c7254d5201e7f6254d5201f6f6254d520057c7154d521ff6c2154d520057f7054d521ff6f2054d5200cfd75d85523767d75d8552004ff74d8552014fe74d8552004fd74d8552014fc74d85520b4fe73d8552004fd73d85523d67f53d85520067d53d855201cfd72d85523d6ed72d85523767e52d85523767c52d85523d6f651d85523d67c51d8552376f621d8552376ec21d8552024fe70d8552004fd70d85523d67f50d8552376ef20d8552006f76198552005df7358552005dc7358552006f5611855200cfd7518552004ff7418552014fe7418552004fd7418552014fc74185520b4fe7318552004fd731855201cfd72185523eef5511855236ef52118552024fe7018552004fd701855200cfd75d8152004ff74d8152014fe74d8152004fd74d8152014fc74d81520b4fe73d8152004fd73d815201cfd72d8152004fe71d8152004fd71d8152346fa50d815228efa20d8152005de7398152005dd7398152006fb6098152006f9601815200cfd75181520267d7518152024ff7418152014fe7418152004fd7418152024fc74181520b4fe7318152004fd73181524167f53181520067d531815201cfd7218152026ed721815226e7e521815226e7c5218152004fe7118152004fd71181524167c511815226eec21181520267f5018152026fa5018152416f95018152026ef2018152026fa201815226ef920181521fcfd75d97320b4ff74d9732014fe74d9732004fd74d97320b4fc74d97320b4fe73d97320b6de73d97320b67f53d97320b6ed72d97321eeef52d973220e7e52d973220e7c52d973220eec52d9732004fe71d9732004fd71d97321ee7c51d973220eec21d9732024fe70d9732004fd70d97321ee7f50d
  | 42 => 0xd70d89531feef20d89531feec20d89531fdee76d895300cee76d89530076f75d89531ef6c75d8953006ef64d8953006ee64d8953006ed64d8953006ec64d89531ef6f54d89530076d54d89531efcf53d89530076e53d89531ef6c53d89531efcc53d89531ef6f51d89531ef6c50d89531eeef75d89531feee75d89531eeec75d8953006ef74d8953006ee74d8953006ed74d8953006ec74d89531eeef54d89531eeee54d89531eeed54d89531eeec54d89531eeef73d89531feee73d89531eeed73d89531eeef53d89531eeee53d89531eeec53d8953006ef43d8953006ee43d8953006ed43d8953006ec43d8953006ef71d8953006ee71d8953006ed71d8953006ec71d89531eeef51d89531eeee51d89531eeed51d89531eeec51d8953006ef41d8953006ee41d8953006ed41d8953006ec41d8953006ef70d8953006ee70d8953006ed70d8953006ec70d89531eeef50d89531eeee50d89531eeed50d89531eeec50d8953006ef40d8953006ee40d8953006ed40d8953006ec40d89531feec62589531edee76189531feee76189531ff6e75189531ff6d751895320eef651895320e6f6518953006ef6418953006ee6418953006ed6418953006ec64189534276f54189530076d541895340eef6318953427cf53189530076e53189534276c5318953427cc53189534276f51189534276c5018953006ef62d8553006ec62d8553004ff74d8553014fe74d8553004fd74d8553014fc74d855300cfe72d8553004fd72d855300cfc72d85531aef651d8553006f641d8553006f541d8553024fe70d8553004fd70d8553205be7498553005bd74985531fdee7298553005ed7298553006ef6298553006ec6298553006f76198553005ef72585531fdec7258553006ef6258553006ec6258553006ef6218553006ec6218553006f56118553004ff7418553014fe7418553004fd7418553014fc74185531667f54185530067d54185530067e53185531667c531855300cfe7218553004fd721855300cfc72185531667f52185531667f5118553166f55118553006f64118553006f54118553024fe7018553004fd70185531667c5018553006ef62d8153006ec62d8153004ff74d8153014fe74d8153004fd74d8153014fc74d815310e7f54d81530067d54d81530067e53d815310e7c53d815300cfe72d8153004fd72d815300cfc72d815310e7f52d8153004fe71d8153004fd71d815310e7f51d815310efa50d815310e7c50d81531fdee7298153005ed7298153006ef6298153006ec6298153006fb6098153005bf7458153205bc7458153005ef72581531fdec7258153006ef6258153006ec6258153005f77158153005f47158153006ef6218153006ec6218153006f96018153024ff7418153014fe7418153004fd7418153024fc741815300cfe7218153
  | 43 => 0x100010000003000000200000080004005000c00b00080000008003000000800000000000001000000000100010000001000800000080010000001000000000000000000002000000000080000000000000000a000400100000000000001000801a000c000000400100040040000000000c002000000700000010000000001800400000010010000001c003000000300000060004004001000200280000008001000400200000010018001002000000000000014001000c0000008002002000000cff7658a5301d7c7558a531df5f5358a530b6ec6258a5320f6e5258a53004ff7458a53014fe7458a53004fd7458a53014fc7458a530b4fc7358a531de7f5358a5320e7e5258a5320eee5258a5320e6e5258a5320e7c5258a5320eee4258a53006ed4258a530b6ef3258a530b6ec3258a53004ff7158a53004fc7158a531de7c5158a53004ff7058a53024fc7058a531de7f5058a5319f5f53986530b6f76198653004ff7498653014fe7498653004fd7498653014fc74986530b4fe739865300cfe7298653004fd729865300cfc729865319ef551986530b6f731986530b6f43198653024fe7098653004fd709865318f5f5358653005ef725865320dec72586530b6f46158653004ff7458653014fe7458653004fd7458653014fc74586530b4fc735865318e7f5358653004ff7258653006ef7258653004ef725865300cfe725865300cfc7258653006ec725865300cec72586530067e525865318e7c525865318ef6515865318e7c51586530b6f731586530b6f43158653004ff7058653024fc705865318e7f50586530ff5f539825320dee7298253005ed72982530b6fb6098253024ff7498253014fe7498253004fd7498253024fc74982530b4fe73982530fe7f539825300cfe7298253026ee729825300cee7298253004fd7298253026ed7298253004ed7298253024fc72982530067e52982530fe7c5298253004fe7198253004fd71982530fe7c51982530267f5098253026fa50982530fef950982530b6fb3098253026f830982530ef5f53582530b6f86058253004ff7458253014fe7458253004fd7458253014fc74582530b4fc7358253004ff725825300cfe725825300cfc7258253004ff7158253004fc71582530eefa50582530b6fb30582530b6f830582530b57f7494d534357d7494d530b57e7394d530b75e7394d530b67f6394d5301f5f6394d5301e5f6394d530057d7294d5320e7e6294d5320e7c6294d530057d7194d530057e7094d5300cfe76d89531feee62d8953004ff74d8953014fe74d8953004fd74d8953014fc74d895301cfd73d89531feee52d8953006ef42d89531feee42d8953006ed42d89531feec42d89531feee32d8953004fe71d8953004fd71d89531feef21d89531feec21d8953024fe70d8953004f
  | 44 => 0x1c00000040040000000000c000000c00000180000000001000400000100000004005000800000000000008001001000100040010004001000400600000000000001000800400140000000002000c00800080020020001001c00000000030000000000400000080010048001000000000040000000001000800000440000000000000001300000000000000000c00100040000008000000800c000000b00080030018000000c001001400100000070008000000400600000010018004002c000000400100000160004009000400000000040000001000c0020004000006c0000024000000800000000030004000000c0030000001000000100000040024006002400c0004000000400400040010004000001c001000800100000020000000000000e000800100400000004002000800100000010004005000400200000000004001000c00100000050000000000c0010000000000c001000400000000000004002000800100080000004003000400400000000014009000400100140000000017000000400240000000000000000000040060008004000800000040050000000000800100100000000003000000800240000004002001000500100040014000001c003000400100240060000000000c0010004000000c0030000000000c00e0008002000400300000000004002000000e000000000100020004000000c000000c0000020002000c00000040000000001000000500040020000002000400100000010000005000000200040060004001004800f00200000000001003000000080030000000000c003000800000080010000001000000200080000000002001c003000c0010000000000c003000000100000020008000001800e001c0010008000001000300140000000000003000000040040004000000000700000070038000000800000000000004000000400000180030000000000c000000000000280050038000000400d00040000018002000000a00000010004001000c0060000000000c0030000000001c0010000004000800600040010010004000800a00080000000000000c0020010004001c00000000000000000001c00800000000000002000c009000000000080010000000000000100000030010000001c00200040000000001000000000000020000000000800000000010000004000c00700000080000000000800100100070000000000000800000000000002000000000000010010000000000300000000004002004000300000040000000001001500040000004006000400100040000000001003000200000020000004000400700040050008000000000300000020028001000000000080010000001000400000000020000003000c00000040010004001005c000000000300140030004006000c00100000000000
  | 45 => 0x100030000000000000c00000020000018000c0000008000000800000000020020001001000100100040018005000400400080010000015001800200000010010000000400f00000000020001000400b002000000000010004001000000400000000004006000c0000000000000c0020004000000c000000000400240010008006000c003001c00000000010000004001400200040000004002001c003000000000040000000001000000200000000000000001000500000000000001000000200000040000000000000300000000004000000400000000010004002001400000240030000000001c0010008000000400000000000018001000000000100010000003002000200000000000002000800000080000010000003800000100040004008001400500080030000000000000000000000000001000000500000000008001000000700000000010000001c001000000400180000000003000000000000000000002000000a000c002000000200000030000003000000000000010000001000000300000010014000000c0010008000001000000000010004001001400500040040004000000000000140020010001000000300000020008001000000100040030000000001c00c00000010028005003c0040008000000400300000010000000000c0010000000000800000040000008000000400b0010000000000300000000000000000000e00040080004000001400b00000120020000000800100040040020001000000300000000014009000000500080000000000000000000080060008005002c0040004004001000600000000018001000800100000000020000000400000000020014002000400300080000008001000000700040000008000000400000080080004002000c00000000000004007000800100000050000001001000100000000000004000000500040020018000000c004000000000040030000004000000000040020000001000000200240000000000000000000000020000000000c00000040010018002000000600180000004001001400200080030030005000c0030008000003c0000004000000400300040000004008000000000000000000002000800600080000030000000000300000010004000000000100180000004003001800000000000000000001c00000000020000002000000300200000000000000000300000000000003001000200080000008003000400100280000000000000400b000c00000000000018001001000200040010008001000000000080010004000001c004000c000000c00900000000004000000000000080010010000000000000140020000003001c0000008001000000800000000004001000c00300080010000001000c00f00000000004002000400000040000004007
  | 46 => 0x7000c000000400100040000000009000c0060004000000000200000000004004000000100000000000000000000100040040000001000800600000060018001000400a0058006001c00a00000020000001000000a00180010004003000800000080000004000001000000000070008003003c000000000000000000014009002c00100000000000000000400500100000000000000c0030000000000000000000050004001001000000000010008000000800c000000000040000004000000000300040000000000000800400000000014001000000000000000004003001000400080000000002000c00500000010024001000400a00100020004000000c0090010000000c001000c00100140030000009000400000100010004005000400000000010040001000c00100080040004002001c0000010002000c000000000100000020008000000000000040020004000001400000000000004004001c0010024000000000000140000000000000800b001400000000060018001000800500000000000001001400800000000008003000000200000050018000000800400000010014001000000000000030000000000000000040070008002000c012000000100100060000001000c001000400200000000000006000c00400040020000000002000300040030000002000400000000000008000000800200080020000000001000000000000000001000000500140000000000000000100080040004000000400200380000010004000400200000010028000000000000040020000000001000000000070010009000c0000000000001c0000004000000400000000000000000000c002000800000040000000000000c001000800a0014001000800000000050024002001c0020000007000000100000060000001000000000000000028004001000100000020018004003c0020000000000c000000800200140030000006003400200000000010000000000100000040004002000800000000000014000000400000000000000002000000100000010024001000000000080020024005000800000040010000000000000100000030000001000000a0008001001c0020000000000400000080000004000000000000040010004000000c001000400000000000004004000c00300040000000000000000300000050000003002c00000000060010000000c000000c0040020000001c00a0000000000000400140020000005000800f001000100040020000000000400200000000000001000000000000020000004000c005000c0000000008000c00000000000000002000c002000000000000020008000000400000100020000000000c006000c00000000010010000000800100080020014000000c00000180150000001000000000000010008002000
  | 47 => 0x40000000001000c001000000300000000008001000800a0004007000000400000000000001000c005000400000080000000002000400300180030000002000000200000030004001000000d001400200140000000003000000400100000004000001c0000000001002000100000000010005000c0000070000000000000040010000000000c00000080020018000000000000000070014000001c00100000020028005000800000280050004000000000a000000000080010000001000000100000030008000000800000400060004003000400200000020000002000000100040030018000000400300000000008000000000100000000008004000000200100000008001000000400000000000002000400000000020000002000c003001c00000000010014000000c00f0004001000000000440050010005000c00b0020000000c001000800200000000024007000c0000008002000c00000000000000000000000000080010008002000000200000000000000000000000140020030000000000300140050000000000000100000010004006000000100040000020002000c000000c000000000000240000000000000000900000000000001000000000000010008001000c0000008000000000100040010008003002000a00180000008001001400200000000004000000800000000040000000000000000040010000000000400300000000004004000000000000000000001001400200000040000001000c0010000000000000c000c0000004002000c001001800000000000004000000400200080010000004000800000100030004000000800100080050000003000000000000020000000000000000140010014003000c0010000000000800100000000004000000c000000000a0000000001400100000010000001000000100000010000003000000200080010008009000400200200040000000000000000100060000003000c000000000600040050004000000c000000000200080070000008000000000040020000001000c0030018000000000100040010004001000000400040000004000000000000180090024002000000500040000000006000c00000000010018001001400100000000004000000000000000000008000000000200040000004001000000d0000000000c00100100000004000000000100100030000003000000300000000000000000000000000000008001000000000080060000002000c000001400200000000004004000400100140000000003001c00300000010004001000000400000020024001000000000000060010005000000100040000008000001c003000000b00000010018003000000100000010000003000000000000000008004000c004000000100040030000000002c001002c002000c00
  | 48 => 0x309000000000001e0800031963c81af69dd8000000000000017da00021bc000000076e139600000000000000634800000021b2937800000000000000ee20002978e0c98868b4849c000089a36039ae9ba0aa081b859c000000000000004c88000846000000020f40001ed69d6091410db4d40e21bc40001284b0000000fb00000000000a0f80005be981e0000000000000000019160000000000000090600000000000000333e00009c20000000000245e000000000000000001eee0002bec00023a069e88860000614000127e3b2018a20580000003502000000000000000002f6691f0c46dafa18aaf68000b198970322800092b2eea000000056b9e9a64e39c443582740001d34393395600001e46b5a8069a2000000000000f58000000166c5be00ae0002b6075a80007ce0000000000055d000000000004ee800000028d4000113c000105e000000087ca3ae96900000000000e5d0000000000060f000000029c40000000179301400020fed2600000002262000265e000000000032a26d60902738850200025fad25188000000000002fe474c000098525ead44a92400000000000000000000000034ea00000005ec0aca0000000000389400035243eeaaf4000042000000001771cf20000000aecb5a806f9abe111264a00000000001ad40000000a3e9d444f080000000cf83cb000079e078a0000000000036c00006c23f92ff400000007dd0000000298c00000000002406ba9348c9868e823aea250137adc051b82ec38ab1d8000035e0000000e5100006c500000000a36b27ab5251f202a49080007620d9e83a943c0120000c3b00008830000000000000000000002b8a318000000037945680a6e00000008da2b9600023d27de388a968000098f0000000000015b8f2800000009b2b16400028180002e8c00035e276f8000000363a0000000000000000000000d800007a000000000000dde15bc0000000cba31f05e80000a1d00008a2206459aaa74e313372e80081257c000084400003720000000000000002f400000000001546a1b00002cc000000007189d705ec0000000e40270a0000000000195e000000069a00000002ae6b6c063a00000002be9be63fda5f8000000034230cc00007e400000008348000e77800016c8000087000069680000000000000000000000000001bb8000000000010fe06501e2bf013340000000000389a9cf8dd80000000492ba4690b8c840000000bda8000be70000a098000d2b8000ab21e36000000000024e60000000d11b3a29118000a3207c2000000014b000000000005c4b58e0000268000226a0004000000000b00040000000002000000100040070004002000000200000000000000000000300040010000000000000c00000000000001000000300140010004000000400300
  | 49 => 0xcb00c288e8000000000000000000000000daf0000287a2d6147243678580002a1b3b237b8000000000000000000000c380002ec6000152ed6f000000024d600003da61fae82168999ed5eaedc000000047a000000025d2000000000004420b02c0c0002f7600004e09a68000c9700000001818918ac3200000000000ce200000000000046000263e0000000e84800000000005ac8514000000004f00004fd883a0000a8a0001d9a00000000000000a8980000000000a9133560000000000254ea6080009738b24a5100000000000e43800000000008b180006bf00ce206a85e2f439c80001baa00034b8000000000000000000000e0f255200016c63fa8000d938000bf3921e075b67a0000000000000000010aea7c91580000000d201e46bdf350600028a0000296a00000000002b3a0000000b2b0872000211623737d8a9096821169f6200013b000014c01500cd8dc28000cfc80005528b2a00008280002544b9f991a00009ae00000000000000d97000000026d0e3ea7c2e45857e43b192e5ec9cd2a2a2460d8c097a92614622070000000000001c80000002b3000005d0000000000000000000000000000033cb4d2611800000023ee000000000015280000a000001364e0b000000011ac0001c0aad6800063fa92c55c836a000339e0002ad2e2a00000001f245540000000000000000002628f16c2e80000003a04e8400000000000000097e2250a9e0000000b3b8eb8cbb800057e9eceb98000090137ba2a000001f200000000000000000000000000000e320002b2a34a8000000000000000000000000ccc0e5800000005938a72968800000030d00000000000213a000000003412600000000000000000000000000000a3897606892a58a28b826000191e000000000000002728000000000000000000000eec7e2800069430c44caaa8c2a7089c00012fa0000000000000000022a00000000000000000000000000f444ad8000000000000028201c6800000027f6a792bfa1f2b35c000221a15080000000000000372647e0000b3e102400000000000000000000059f924e000000000000002bf94f639480000001186d49a0c60210000bb58000aff853844390547109bb46a380006531a1e0a70662000000000000000031ae66750ad2d5f8000000108a56e80000000000175174094b0000779058a0000c12bb031c2656297edec80007ad80005b3000000033d20002b487e18000e120a1c45e8000382a23c7500000000000000032264ad248600000007a6000000000000003578d7b80007ad000000009f8000232c000000000000000002d4a00005482e82b42873acec000000000009120000000000000000037f8b1327184a0ac28000000000000000000000000246600006ae0000000aa180005160000000231ac008000000178000000
  | 50 => 0x33e84c4000085d80005778000000019a000057400023e60003434000000000004a000018980002dce5e88a2009c800096b0b580000a52586098663d00000002daa33a0cd6c83000000031020b780000003010df4b9d2de98594d4d285000036f200016ec0000ba4681b2ea20099cc0001db600000000640000000000000017724e91d727ba378a1b79f18bf9a10800026d20000000361a8d2723000000000000002fc400001648b300000000a1000000009142c80000106c000000000016b40000000000000000000006d3a03c4da00006280000000000072100000000b260001c46b6d9df07f480000003964000310800024740002a56acd00000000000000190200180000000000000000000025c219c80000001d8a8c201501c5b4a0000000054f800000020ae4238000177b47a7ec1ea800000000001eda0001c5e00011d60002d248ae0000cbb000000013720000000a89278a21880000002c20000000000000000000000000000000029423dd000002e800033680000001cb6b99947e00037ea00000000000000b9f0e04000000037d000000000000001104b28b6f47642844000171e000171800000000f28000000282e0000000c4a01a6b330000003800097d0000a238c86556307c00010d000022664c484883d50caa000000043f0000dbfaae80000000000000000000000002da03b58000314084496381c6000000000013e6a1a0000000000004d80007770000000156600000005ce800000000007160000b048000000000000000000001d7009eb82489600000000000d8681bc0002ed8b18383600000000000000000286a12a00006a980009c700000001a10000282a00023f8ad780009380000000000000012a0e03ab9400000000000000000000299e800000037b0e8eb6e687b00000000000b6b8000000000000007924c90cfc67c849200000008f28d820000000000182e0001e0439527780000000000000074f23c60000000d0e00003ab9222e088000d628000d4e9e1c000000000017e40000000000000000019f094327480f226eeaaa284eb740000000028a884b62e14aabc8000000000000000000000e0305760000000cc2b92200006bec54800000000008ed8000e85b4a42958000000000000000000002c883e60000c0a800000000000000000e5a80000002ca0000000097f00000000000d7a85e695a0e4a000051a000000054d000000000000000000000000000015c654727086b080000000000000000000018c86c3a3ce000000090e800063b0000a56b5f88a3b6960001e4edd1000061d28b295cb00a3620000000000000001b43090000000000000000000001bcc94800006cc8000baa00008f92a8e0000ec63c236ee32415042b40000ca80022b65095a5aa8cba8eb2afc2249720a5596d0d723120c5e9376d
  | 51 => 0x80c80d20001cf00000000000000000000000002c560003846a4ba7e20000000c38800000000002ad800000005aa0000c800000000c2393e85063828d84aefc00000000000ec42f6b7842dab49e4b2a324dce00000001c4a207aef0902b6d236527c41f52abe10480000000000b2a0000b389a383e18000000235e000000057280007ddb0c20000df60001d2800003667d0000024ab1820000000000003200000000c7068e000000000008c42e197cc0000000000156479a307a0d89f6e96d0604d1731bce97b77400034420000000d2db3fa5a00da600000004f880000002b5c3ef2962523235800029107d831d42869e1249b2a020000000446800000002e0d3119ae000000000000003ce8000000000013380000ff80007a59240061818e0000000000205e1b62a10000084c00000000002762000000028196e0aa72ad424b1d6c194b996cff135490307588d4102ec89275e0000000000000000000000000000a230000dbd80008358000000000072cb1a2000000056fa4564433166b5900006d886ec1f30000e8f1efed5425960000000000000066480003b513d0cc51b2ad7d949a193b19c4942ae064610f009b058800000002fe34be00028d6b7800000002b9e0002dd400030e056d0000000135e688000038e80003152f5269280005ae8f9621eb14ec8b846800030f600023b254039f477ca4e8c6c136200000002c300006df80000001a58337b2d67b80c28bbcad1aaab800000013c6000000000000000002baa00002ac3d9800000000000001622d61a72c0000000ae8800056e12527daae86dc6b7ee42a1bca0002cfcd2f24326238000a2a8000c558000000000041d330600000000000000679800019d975c441a6be0000642e371ae0000000000033c800116e497900000360000d679c5010a3a640003402000146600000000001b2800000000001708000000000010a613913c0378b768da98000a5480000000000000201400015367a9321a00000004f3800000006600000000587a2241c7800027a26060003200614099e10900005cbad621458000a2bb31e0680000000093a0000f1a00000000000000b91000000030a20000a2400005d2000000000000002a8800045d2c469df9f72000374e300150a06602b45931ce0ac7b68044c03f0e5f0916213800079b15f43548000e839c7c00020f20002afe0000000c490000000000000008ba87b80000000000000019681f37960700000000000000000008791c2e28580000c9088224104c00000000711000000000000000000000000000000000000000c1500000000000000009412b295cb1480000000000000041400000005ab8000a6e000020000000ec8000c1912baace0000000000000000005c890acc958000e8b38e668300000000000afb947a7c6acfa307960861480000000
  | 52 => 0x2dc20000000000000035e29d694080c6b670000c918000000000088c800000000000001d7a0000000be3006c0001b503f89d480b40000000000000000000000000e9a079a0000000000000000000000000000000000017a26c65b700002dd8c760002ff0925b8a00002210535800005005900b180000c6133c0002448cb4800000000000000000000182c0000000d19800088e35a44270ab400000000ed0000916ac4a0f5372e000396c000013e1431096000000000000cc0000d10000329c3b4b0acb2380000000000d3d36980000000bb89948b429fc400007601d0000000000000000fc0000000000021aa6640000000000000000000002b8cc821b9ac4c0000568800099495b0790225a0001316000000000002d60002ec800000bcc6d000000035fe7318000000143400000007cf8000e321f041de800060c2a6c9b500003449daed8e33c40000000579014200012360002d9ee5c000000016e20000000c1880006efaffe0001b203d586540001d5c732064a78929d400000000ac28ec0002882000000000030da0000ed8a3f800073b000008c0000ab3acb8846a92a0002ae2b1b00004871c1800034da0000000000000000001380001faa7bc800077b36820000000b6c8972000274a00003980000000864800006b800052c8f0ae4609a800024c6cc0000016f00000000000e4d909a00019f817eb27838083420a9af860000000018800000000000002aec000000096a10a2be10e6496db4585270d6600021d6000000057880003570000824800063c00000002d6600000000000000397a17a44587b20000000c3510e4b1380005d41ac4000000000018e6670000048300000000000a258000a9421b4000000037c00000000000000000000038b4000226031b8000a1c0000000000000008c2c441a665c0800000000000000dc000000006108000000000000035d80000d56dee0c26371042a000072000033aa10700007730000998000000036360000000000000000000001d133960000000799830293ba5780000000b7c9c720000000000000064338441ed31d600000000000000042800073d0000000000000011b050b0000000000082200002850cc227c226c1900000000000093403bc6811c2452c2204855920400000009f400000002aa4ab12c6894ab1a6c3c29be64fac6abb51b060002e720001d7e000283646d80000001f50000371000000002a60d2e00000000cb1d84458b7e80000000000000000000000000000166202c0000000098175e000000064827f227d0c7a000073600000006c980000000000e18880e6d82630430ac8200000008058c7840700007d30000000000000014840000b66bf4346200009a233900006bd1e6e0003558000000000000000a317a400000000000000704af7e0001288585877050880000000000
  | 53 => 0x78a36501da05fe0001c64bd925889858000b12000084dad4424ba0b26de0de09700f260000000000000000000000000000000000037f8000000116c0ca8de472e3286000000000000000000000e5f9758ab28ddaa97369a7e39232a3f2e14000031e0000b145708aac0000000000045200000000000000d09019e55527a0ce4039c86c3804d3b800000008aa0000000000317cb770000a362a4a493095e0001ea0aa427900c800000000000000000000000000000000000000000000000000000d0b9c387f90000000000073a06b6d040336318a6a237ab30e00022360002bde000000060e368600029a457d8e30c88378eb252fd440f871ce15ac9a134800065f88261acb708000000063900000dfa7de000000000001fc0003530cb38f2469094e61848000000000000000000000000b5d0bd2a2b07aa0000000a1d8000000261c63a88cae99a214061228c0000cbea0cb600697000000000007491af80000000000000000021a60000648c1a8e38aae800000000000003280000276400000000000000a7d255641480000000000740b3ac3ad81a20000000a3d926200000000002e0e6268000000168a0000000b7580000003874098b8fc7af99b0af480007e52346000247e000000000000000000d5a77501ca2af93e00fe0a2eb4b2e2ee0bb780cdd8000cf9ba0881a029800000000000000000000000000000000000e9380000000000d7c919e6c400007c981c88c1076a000200800036c6cec00000000000000019c00029887b080004de000045f28ee0000000000000000000000000a42ac9a5224c79bb23a8aea210b80001f600004360a6a686000000000000741d183bfac260001d80000000000031dadd2800000033100001a92bc597e20000e0c00000000000e5043000000000bdc011215e0001b0000011440003448726000000002ce00000000000000a5f06fea98a51839c01cc36626a68ac9206c8f254660a073e2eb1a8a0001438d8500000af0ac400030b618280004be2f9000000000000000000000018a8000b78800000000002cf00000002c0653f800000030c07148d609900d2c53c8af68fb000047080000001ae81de000086681c28200000aae1784000000000033b6dc180000002f2875400080002310d612db800028520000000000000000000005d301a822805b42010000131b4684c627a8b5080000000000000333c000000050d8000bb30000b8c8000bea3a5c163347639680007d480000000f940e4866e7d2000000006a0000000000021c26beb4e63db0ff45bd80000e30dca63300000000000d673a3200000000000000c620000000000031f00000002da89758be06bb80000000aaa43ea510000000000000ca000000000000000000000000000000000000150000000091e00000001542c3c6220000000307e532
  | 54 => 0x4000000024227920000e08201e1e0a77200000003b2a5c400000000000000000248200000008100000000000000000000000000d05800095f029a27baba00ee2b6444d9afe00015b637998ee0001578000189686015d818735b44cb000000018560001cc4169000000000000002b3c000248c4190000cbf1088da40000000395033b000000000000000000000350ca673580d1ba690000159e9a0979ca1fa278ae2000000000005b6906ab478000520290000000007ab000000000000002db40000000000000000000000002f880000000926b7284ed91684958000b4d16eec149aba600b6240a880004e18b64298395800000007f88000a9682900001388ab19a360001314dd300000002b2e10d000032a00003af00000000000e16118eb8eae060001e7a0003a52dd78000a9211a200000003f38000355056c188b2607f0000043aa6ba502221c000353e000000000000000000000b9c0000656800000036725b12084a4d99082a500000001506d98041e0000000000000073700000000000000000000000000000000000000000003902648000b9380004a6000011b334000037d4000000051300003a680000e2800000000000000000e020000cae8000000333446f80001eda7400ff0000000000000000000000000cf501ee000000000000009c5800000000000003a5a00000001569182c4d946cae000000000000000258a0000000460375c7222b5000000009671dda00000000000000000000023ba62cad1824e000000000032cc1e0225e00000000000000000185a00000008fd000000023200000a76000000000000000000000000000000000000000000000000003717ce82fa2480528000d728000e178000a99800022a0000020295e00023804240000415ac542552d2a0002240000053e8aab6060003304574800003680000000000ab30caead3800025f0000e4080008a50dfad01000000000000000000acfb60c00030962eb80000000000000000000000000f78000ae701626a20000617800056c9d7400035a6b7780004e139e42f91b422c0a45400036aeaf00000c3aa7e4bd0800000017629f48000e8819e47a500000001fa40000000000000032c800072b00001440fe81b52916cdf8b9acd22ce0489000015c0000037800000000000000000000000000030be000000039e0000964ab9ace70d9683800000ca090e000306e0002f0200000000000386000000001d238400013bce8d15cedcd80007458cca450800000020c255a800000000000001fa838536ca467032600000000000000035000000000006549e3000000006aa85cc0000000000000000000000000abc0000000d33800000000000000000c318b740001774a6c23888de2abc31a9da8c27039eb71857224817e00002c3e5af0000a031ed081827d80608000ce08b6
  | 55 => 0x2c620003806000000000000003efb66613325740001c0800000000000000a1e3482989ab3241b9ab4195910ac5b1db230800000000000b261f0c0d400000000beeca611a600033e400032f49ae208a00022a4e20000000034c672c22061550000000000000000004a8833e000326a00009dea3e0000c6f838287f91daa1285960001e5a18400004b1150e70c0000b7bb378aa2b94e1fc000000009bc000000054e3a1a000000000000000002d08000348a0000000d99000088c000069c9ab024d80000000000000366a0000a5e00033920000000000000000028b052a80b0204144a5a80000a872b620000b206913742000000055d80000000f1e0000000000000071b343e7ca1b2e2ba19c4b9b2402b453592000150cafe0000d8f80000002974000127a00017860000000000000000000000000000aacb1262b2000000023d05d58000000000000000000003a267712054946800000004fe0000000000021400000000000e206b28000ae08000000042cc95261edf5b7f60000da0a448ae49d5000000034f600000009c80d0e00009f2000301c53a20a00000000273b6a28fa2670c1da408000000006d800000000001820000000000000030aa0000000bbd80003249f1400000000001a9e9fa8352c6429b6000343c3130000000244cc1c05ce00007f60000000d708000000000006c000000015d40259688c07b3380000a68000112a0d223e000019449350000000000000000004590000000000000000000000000000000000029c8b0780000000000000000044b9216421adecb351d92000000000027e02da3a6000022983350ad611816ca9e68888741952cb41b0b897c3608000025288a00004721ca2633961cac00000d911e900002284000055600001d800000000001bde293a414000000000001b800000000000000000000052980000000000000021e3e6aafa0d600003410b5c0000000000000000000000003966602061a0000000db6000000000001aa8000acd800059e2686d1f31180000000a2614a4000000000000000000f8c0000618000371cabc81aa53683c0c328000000197c99739dc0000000223ab7a0000000d73833200000000000000000158c000040493a8ea42d2067e3128d1843e1c6800027240ef8000bec001000000000001b300000000e8700000000000000164a00009880000000b9a000026c031400039ce58900000002e946ce0000adc80000000000000021a00015880001c0c4a180003e908420001a9c42629f6000000000018360000000000372200000000001a12cea300e0000000000000000039ac0000000000050647b1c1cdb90000000000034680000000000000000000023b05fa9ed414c14b6d2b000000000000f08000000399883f0000e129b5a00000000000000203000000033f8a56000030
  | 56 => 0xc05b03d823d4c82aba6d2880000ec0000053000000000000002e3c0000000aa9843c00000000000000000303a000000071c29d000000002ed909e865332800000000000000212000000025b00000000000000045400000000000db8800000033de0000000499ae48364231e4ea971a91c292669e18620002c1c0000000158000000015480000000000000020e0000000000000000002780000000000027526940000e6239a27eec96b792a8c8000b5b37bec1d0e6a000192c0000000833828e0000000106000000000000000000000000000000000000000a0f11ee0001474b61916a3b999b8d55000063093f427000000000f4200000001a335180000000904800000000000001de200000009cd108c00000003870000000000000000009e50d92000329012cad70e380bd4236a04a00000000003414000235200000000128700000338054f0aea73e99880808adc86314c4be63702bf580000000000000000000037e09810000000343a00000000000000a47800089f28880000a38c3792d659f0000000011c6ef348800022220000000000000000000003e0921229e8000c72a1f0000000000005240000650343000000038d000000000000000000224c00000007bf218405110804710c582598000c002bba00000001ba80008c5005e410900e000000000037ae750800000000004fe8000d9b18c0000000000003b600021124ff22f8000000000038ec000000000000003ebba2800000000000000c588000000020ad6f8bd80002ff65652d0e782a5cc000338c48a8b32000000000000001199f5456109cc04136b6000249c00000000003384000090a9ef84be240000036380004fb8000b3c00001efb4b000000000000000000239e6f60000b92b83a2de89ba4f7ae4cc48800000000000000000584a81c054a0069b6a570000250ac36000000000002fcb92c1a10000c79000000000000000000000000000000000000000000000000027b800000006e180360000b7c00016eaa6ea8dce4cad7e00038d69f684dc2690000bd1000000000000000000109800000030202b500000000000d95000000000008781ab2da700009f300000001bd600000008a5800000038925a896acc79b3c21328000000000096f00000002b7c59121a2de1abd00002ea600000005638000373a7a220b95e8d8811545c431fec0225c66bc81fe5fc80000000000000224a4e6350463584c800012000002e3e7208000e2c36ba0000000000000035bab149ee800052b000000032d4000000000014d06d980000001b1878000000000000000000000029ca00000000000000d9080002332cbc0000000c87255a37480000001a3e0000000768388e00000000001c540002bfca6380003b8000093d2b980000000c6a08d000001d21f4a51c00000000000fb4e34800000000
  | 57 => 0x48d032e00000000000000000000a000000012d000078500003f8075c00031aa8480000000000042910402793a400002472000000000000000000000a0c0000000000000000003d40c3a00000000001fec5c9800000027660002c3a4b1800000000000000000000069800021600000292000378c7e080000000000000000000000009a920e2a0b19809b308ce0000000000000052e1e720001390000000000000000000000000264600000007fb8000000359a000205c0000000a55211e3a10000000000000030bcd748a58000000000026542bbb2e20000000c1336dc48b000000013fe00024347da2efeda52bf400018de9798d3e8642d3ee7b88bc583934ad5b8000000168cca4a58c0000000000000079db47e000000000000000000cb000000000000c2c0000000000060e3dc00000000000b1d80000003564b0b000000000001bd88600002208000000052500008bf1f5cc7a80000001c6a000000000034c056b000082686da64a30445cd2fc611f00008ac0eb4691b180945000012eb9c200000000000ca4000107a0001e2200000000000000d381fa00000000000000000000000000000843a06c6a688be2f38bc411c8000cc60000662800000016b000000004bf995c00000000000d6a0c6800025d1a1600032e00000000cc800002240000a3c000000000008a000008ca94563e41fb8e688000bfaacc4d51000000001e6000196440a8bb83279e0e000000060394de0001e320001804000000000000007700000e028000aebac8a9b8a3a684a0000d740000c0f800000025e200000000000000000000000000003a1b50000002e6c93048200017764dab1cc0000000000205a000000000038e80000000000000059b890620d8000000000036f1ce40000bec0e03860000000000005c092c0000000213e000177c75f19d047d80005f7800000000000000000b4f00000001c8e5e307e669817143a0000000022c40001a800000000bc91d047a109ecaf580000002526000000057b066842519306bc12d490e254ca6ba738000000000001e0b631bf0b7ea77400032de00000003e496280000d20bd7800022d000022db294671a4f800008d80001668000000000003eac0a0000e4980000000000532800057c80000c300000000000853a1640002804000395c97780000000000000180ca660000caa02aa30200000001c020002f82a2d92da786276c00029ea6b480000000000000000000000003770000000204ce54a35a00006a6000000000000000002b28000000021180000001eaeadd80000001004000186ace2933e35400008508000c9b800000000000000000be900b632b1f4e00000000291f9e624800062b00008861754d780000e2086c8000000000039b6000000000000000002c780000000d1100009b030b23e788569393258b
  | 58 => 0x8908bdee7e93b80000b4ab9d80000001ee6c451cca29f00000de0c400001a3200000000000c320000000000000000039e600000000000000000000000000001d7800000000004e8000012317ec86a0000000000000003d00002a781a29e2660025be0000dcc00019b4c8db6e09911db40000000000000000000000000000553aa7284c2e7a8218000024b574959b3f4bf0b1f22e11be4a529ebc000178200017a8be00000000000035d0994525a27e000000039c80000000000000000000023a2d6d9974307368cb108a18afa144ed6c0d72000000051498b0000000087019826fd1f88000086a77bb7d0e502aeebbbb89eb0d00000000000000098400000004ab11fc00000000001cba70583060000c8881d000000037709d480004738000a27a27a4120fca4b602e87a7b3d61ce02be0000000dfb07561ba0000bc4398e547800000000006ff800000024cc00000001b112646681fc60002330d53000000000000000000000320200000000170e08534800000000000001fe00000000000000000000000002ffa1dcad12823a5ba46cb8c0000212200030585aa00000000464000391a63d83ae000273c296b87600000000000e065a986a8000000085696260000b6200000005180000000375030a9030000000000002b81b4104a71d80001ce800000000000000000a810000c4f800000000000000000000000000000003e980003c4a3da00000008a985f400000000000000e619e6a8dd80000000000000000000004f69c1b1c6a428000bad800007381a4972000000033a61dd00000fd80004cc14c200000001d2800000000002833760000000000001dcbd19a0e14d9bdc0000000000000000000005f6000008d0e100000d4487ab86c5e680006e1000000013d400000000002cbe93b0000a74828600001dae271d4e72b86e25fc00000003134c692a3a000283400000008b980000002848099a70400000000000000a2f0e8c0000000284869210c80000000000402000000000007c41fda0000000abc00003f20000000000070f00000000000000000008d80000000ef0ccb8b12a31841a5f70000bfb9dfc65b16e800013427c380000000b8a00000000000000000000071f885eab780000002a38adb044e00000e67f592ecb4401de52e81e89c880008f000000002582ac880000003a240f494320be000000000003ea0948000192a0000000000000000000005a3879000017b400000003d198f28300b940000e340000000d9180000000000000000000024c0000000000000006dd8000000000007531b2000000000000001bc1a96887800000035520000e667298000a461aec00000008b09e44000141a000000069b8076c2c0402000140299b3078000000011eadbed978000000180a77780000b31aa0000000000031b630f874c16b9b7aca58
  | 59 => 0x1cee00011003fb8000cee02780002c924bd80007c89c36019800000000005c0264ce64087e00000002efb8700000b54c66000092c800000023d8000025e6369b94000000000006d2c0c80000000000bc80000000064600000000000000000145c65aae2a04c80000000160aed3082c3f0000c46800095bb812e8b80003eb08c07498000b648000000000000011ea811976600000000002c7ee768dac44e00008b6000051180000000000000127800000000000000d842bea1cb80000001f02758b5f00002a0600000000000000000000000017aa0000000000000000008a200005d600000000000000000000090980000001d4c36a000000000001340c0662f176e8d000004621ba4b2c0e468208040a1c80000000000000335000000003c70000000212a00000000078000564b9a00002eb400000000001be2000000000000002e38000ba200000000000000000000009da000000035180009400b4c00010cacf3381000000009b822b413a00300001412329800000000000000000000000000000000000000d12b1f400004502290000000000000015cc000000083909444a900007519c8a0000000215000087300000003386000025637400005a123dc00000000c480003672a000002d6a42e0000663800000000000000000d5a0728aa6a5766fcaadab29b086000347200000008f8b7725d28000adf80000000000564089e00010140003676cbc26aa210301600017fe9f9b4f02fa1b9e0002f8a36e9120b6626809a5b24227ea91a4bd1662a79b3f6e6f9276a0e000060180000002c7c0000446000170a4aaaa1833e80000003868000000000000000001e1e3bd96decc4800000033a0d5f1970055876200000000001560669a3721710172000000000008980000b82000003cb0583c4000102000000000000000000072266608782e612920551ee45969fce35fa9480bfb5ec3f519a4dc63756000070646e0000ca6800000000004e3ae2c4b794240002a6a000004c802b6c40138d7c2ae23d6509b178d503522bc324c242f00007181b36000000000000003cb8000c2780000000000000241c30d0000000000087d39f8ca318340000fb6d1380000001f5621287641d50000936933200000005600000000201c62cb2fa457199600009a00000000000000000000008ce31ae0a8204405630300000000e5b8000294000000000005038000000310acd80fcc000000000005ac0000000e42000000000000002986abaacd8516a7f057e00000002a7e4cb800075e3a220001a3c000000000000000000000000000089cb1ee9af000000014f844a170c3b400000538000000309a00018c400000007b3000000000000001fa23a495081c49c5ab729ff2b3900000000000000000000011a4bafb90c0000000000000000000003d780007ef0faa3ac0000
  | 60 => 0x38b80000000db000000000000d9f194e28c897631b30a475d800000013dc000000000000000002e6e00000000000000cb200005cb000000000000001aa46f50000000000000016c200011467c800000000000a939b64000000000003a200000000003098644000000009800000000000000000000007cc165400028f2e930000089afb2000000000000007df37f2aa5293c000000000022de0000aa80002de40002b9256a09aa5220b9e1cf0038dad30042cb082a247342c36b800082d80006ad80002ca0dfc2388000080000000009dc39101ead8b17ae1968000000162e8c180000000000000000000000000000000a8b800061a0000000000000026f0a852802907877694d99dac8a97385fa22ec69007dacd69d8e142940088b87a8027845c0002f4800000000aa05f0000000051c80000000000000000000009b60000000b4b800000036709d38ea0521abce5e7a6b60002374cd1957e6b2285429500000000000000274c01e11a087891e00000000000000015e8ae6181834e44890189cda1882f29d6000000000002b0e0000000000000000000000000000cb680000001864aea13a8d6a9b3e26416028e48df2000000079c1428000000084b8000040afe000000000000000000266ae60800031a00000000000000303800000007558000bb0949200032a4000000065d8bc00000000000000014d0000c0f0064b568000000000000000000000000000385a00000003c380000000000000173e00000000000884000000028f0952536000000039fc000000096caff80001ace00035b203019d87beb4060000c0400016d87efa034b6e84a494a272639f0000c5f8632000052200034867fd19e200021d8366984800000002b825980000000dd01a30cc302f23f400000001caa00000006f4000048809688e40000000000000000008ce99ee00039620000000d650000047975a17f1900000000000000000000000464000046d000000000000000000000000000000000001df600000002cd8000a3d00000000000000000000000000001eb0b871c92000000000021d0353800000000000000000000315800010ccdcca64eb3a0f4844caad6648aa3400000000002d6e00029e000019de0002d488a691c68c3050035032c28ee80001d08000b9906e600000006b40e1600015c844209e290695020000000000208c07c000000000000001a7e00000000003426ade0000000000017a820400000000000000000158a00000005f12fda0000000ac12022b6f29b4000259e0000000668800000000000000000000040800000000000000311088abc0000000000000000000e7c199c7b625e86708814c8e218e9fea9300000e1e575800064e80000001be0449879e72400000002a28b4e0000000000000000002bb008600000000000000609
  | 61 => 0x1724757afe800027dc0000000a3000000002f6c00013d2000113ac85aaf84d30000000174e78f17a62c8b6160000000000212c000000000000000000000e1e0458c61afec08586dcbc2800036d05d8000093ededb01a000000066c88a65f2800000000008ed0000cd38000000094e000000044b39060002f30ddb80000000d320000000038366e00000000003602000000094f0000000323200000000000000000000000034d6ab7000000000000000e6c00033984548db66d2800000023f60000000000250400000000000000000000000029c600000000000000000000000000005fd153a271898281cae9800028b800000000000000a02184000000000002b680000d3485bb884000172a00000000000000330000016d800000008c8b9d25d40002b4c3b68bd60000000000291cc4337160000000912800001a000000007dc0000000d298000aa600002a4a3483408cc600039d80000e6ecfc2c7a4c312d0616327a00000000001f128b69b6a43c800000000003f180609e0000000027fe00000000002e9085c98e875a379e7fe2966df281280000d3a00009b20000000736800000026dc2ae8000964111042faf069162c2a00020b80000b180000000000305678180000002226000000095080002090000172a94c000000000000000001e5e000000000007661c400009fb0000d7700006e700003520ecc29c08ec756886600028ce3178000d7780008c0b782c7034ca7bb368833c006ac3cb590b570000000398c877ad4e3fc0000000000060412e600000005db00000000000000000000000000001ec43980000df21d32000000000019ba0000000c5b80000001002a820000000000000000000000c36000000000020ca00000000000bfe14f0052c63800096a816a917000083bb72ae4ab1c40000000000082c0000cce0001d8600000003b3800000009d2b27377ce0d0afc6c0b896000000000000002498000000000000003405ef000030697523a998a6e140ca00001742000000000021c6da780fc4d3aa969ff000000000000002d160001df8000000000000008e3a36427f0dde0001e741e980001411b90bed80002fc000000007d600000007930000000000000039a600000000002eaa91db7540003516b8080000000000544a1b8000350e000148aa2504d60001fdc00006c000000000001b8e0000000e850ada92a8000e4e8cc8c25398017d8000dc1033a4a280000000000a330000d1c1e8e7b280000048e7400000000000cee000167200000008d5973c00013ac000000000036de092ac0e0001dd000000000000000000367e2db8000000000092e88527f980000000f3e0000000b518000719800000015183489d644a70cfe0000000000000000000000000000000117869d800000000000f9000099d0000000000
  | 62 => 0x2a00000000220000d3701fa2cfa30a07d96f40000000000000000000b278698260001ef6000000000021fa000000000000001498fb89eda53400000000000000c3b800000015863e8215c7a8800000037c200000007130c3c0000000000000000007de0001f340fe80000000000000045e73780000000000000133a00001ec4ac1cd6ca380001fb80000000112000269c000049e27fb864000000000028be00000000000000000189002400000000000000000000038f000000004bf0000000080a7758546ddb06fc000000000002949db9c6e0003a62000000000000000000830000164630380000001f9800000004338000000000064517bea5c35140000f6a74424f2282304074316e623d007ea11a8e8ab907ae0818714000395ac371d38a170000000024c000000086197d6834047834d8000000386a00000002c580000000b0abbe8000a4d00a60001a340000000000000000000001d200002c18000b950eaa0000000d4b0316497a57a000209474700000f707f8cbdb1d2000000000008d2bc70000000000000032b2000000020c8000000000000000005a4326677600000000250000054c00016485488000b940c8c1df99fc0eb23000002d600000b0e00000000000000000050e0000000000000000032764d6800076f1bda980000000000000001d82000169a420b90a6db000000006b8e36b2a66e080006dc00000000000000000000017ba000000000000008aa32fe798312c1e600003cc1e546d70000dba8000000187600012ee000000023539c60001f4600022bc000000000000000000000c198000000000018d80006872fdc00000000003960000188c00000000000000000000000000001e5278600000003c100000000000389ab16958aa2a1b310c4b9e2a406a1acceb90800000000000002c8600000000000000c4f000000000000000000a4c8000b7a8000000000000000000001d5200000003da000000000000000e4e00000000000000ac22124000000000000003108000e2620a276e8000c8b00001a19ec870cae6200002a400007c4a9500000000000000206a00026c20ba8000dcc0000b8d00000d916923c600005c380000000000ded25d0bc880006a500005f0338e000225681d800000000000000f847338000b8300008c48a9000036f01f82de89cc00000000000000297aa4080001832ab00000000b3d80008dc000099b8000d70307200000000000000000090c00034ba8f7800009db7ce00024a4000000000012c8a4a00000000000000040cd2a0000000000008300002de0000bce9516c650000e1e85a6792abf0da480007b19c34c44960aa0480008828000000184477482c4ac48cf63611f1e00025b80002cb200028b400000000000000000351078b80009b62540135360e53a800026308ea5900000000000000
  | 63 => 0x29a80000000000000000038cca1600009df135000022685a50b100000000c12b430b3f88fcde68e7e4728f4a60680007c18e4886b00000c419720001092000000000038cec782c2eaeb2f324a3237e15a90269e0a26e9c6894a4c3a800d3086d68400146b502e9626d33ae395b5fa0002f7898400009001b8000025dc2e9b5480c0000050c273a000000000003e00001f161c300000001c620001f7a00000000000000c2100004fc336c03a2d3200032e400000006c7253ec94397678a80009310a5c000000000000000000000a37969e0000fd20002c584c1b9c000000000000000e3cac027e121dad9d0000e390f6221a1244bac140c0271c1a00006bc000000022c80000000d240000000000238a000096e0002f502ff000000000002e30000a340694b6280004c80a643c1800016e0000b2a8000000318c00012e2e0795ea0001dc2dc78000772925800000000000000000023e7d7b9ca47e80008ef00000000000ced000000000007dfae568b21bb000018b6cef0d6800033a4cb70c52bf4ae9c0000000000000000000002161b4024d0000d7500000000000000000000038a28e91e640001634bca8000000000025b09608122968daaa788779a56c0a7800000000000000000151000000000000000000869000000007f4000254a86b8000a058000000000000010d2000399e0000000000142a41a1e820001962673800014e86f2c0d0512afc84a66c107fc00016605830000000000000021c89768000000234adb58000e5e99260000c30a778000000147000000008fea7bc9d18b5623f885a59c04400b90ac20000000000000000000000003766b4a337aa0780005a18000000046a3aa07ec510800000000008e71da40000cb6bd5a672526294692b80141b180000000000b8d876e00000005082a84e360baa00000003d03a06000000093f83f41528000b178000d98800000000000281c8048282f0a9e80000002f4a903a564000319a19c00009b58000bc22d9653e80000000000e579eba00000000000000000191c0001b22000000000000001399532804308c0002c0aa29182a8a8a1caa991d4a8a41a3a53d10aac0b3888989120e1308000c170e2e000000019f00002d780000002e4007d354ec9900006c6b7200001b5ee8d8000bb4030e62e8c74197b29e4e013b24c29406bed000000012c20000a440002098b23000000036aca1e80000002270c3e01f200000000000000c93800000000000000000c4780000001062ad02ef892880006e4a70231f80003208000000000000000000000000000000000000000001dfe0003886ba02d180001b740000000cf1977a3fe9968c72008e12c016c25a80002ea26fe000000000020da0002d840000000dcf869e00018be0000000000000000000004d1800080300000001d
  | 64 => 0xb63800024f0fd6000000042c336e771800000031fa76500000002cf40000000af31656b020000000064466f0b1e95800005e20000000257e0000dec03d8de8ac72b2c000000000002125453234815af1e70a1bba0001bfaa480000000000000008340002b240c11956833000066d8000000376a0000000000233ce3da3360000000000000000000000003212000000031900004f61f2c00000003e8a216581000009600000000000000000041d8000000000000002085e51c14bab06ca0f39f64e6280000000000b7d1e38c779272b5a000047780000df00000002d5e0000000000055e3be000000000002898000ba10000000103c000000036a800067a800023580008e080000000000000003ab970f4c00010f66ab92740000000000095c4460000112000000018820000000000000000000000000000000000042e800000000000002c50220000000027ae0ab96b6c52b6b2d1b32f80000000000000000000000d1b99400011cc0002eec0000000000000000f80000000000d9a04163121abc0000c70000018c74f874e00000000000d7665b80003c5210a8ba00002f2323a00022fa00000000000bba000000018f0000000000001c00000a221140001b966b3187c4ba31ac16f800000000000000000000119600000007420220000000000000000003658b348000571314800000000000000000017e00000005b500000001a2e0000000c22b8ea7f280004e88000d36000044480009281520d3e87846cd1ee293e80e2a85a16cb0400000000000000000015e00000000000caa87503560000000000000000007e7000088092ce3c00d2853bb928b97904697b00000002d8800033084180000b2eb37446a0000000239a0002f3c000000000015100002aac00039e00002e160dd8000a200000bc500004df000000024d200000000000000000000000000000000664000139c26fa3320002e08d3c800000021d4c2ba25cc9c26e6517b94c0000000000350a0dd000000000006362bd43be8000000000000000000002ab66df1c2c000000000027d489d8000124219c3498d8c000105c00000000001b0c1548000000000000000000003556dbf00008272bb07eb922e384ad520001a1400000005f50000d088000000000000000000000000000000000007bc00000000001d9600011d8d471e3aa7602c20000000000191200000000000000000322894200008d70000c5c0a0a414000000000008d880000000f8a36c0000000000000019c8cfa8000000188a8b2a88ab3400000000000000000025585e09ab20de000000000000000000000b96b2c400000000002d760003948000000000000006a61c9c000255c0001e8a92d00002f30000d3893ea00032f20000af4159800000000000003344d07a612000177e10e22f08b8231c740253000000000
  | 65 => 0x1c224a5096200029bc00000000002e9e000000059611fe006266200006b4000001655c000000027e88adb800b4c331a0000000b531e92b170000000000084c8edc3ec2eda00022860001218000000000000b45a600000000704d9000009e9207800000000003142014008c0000000000118a9be800000033d860f800074e80000002d2038b36ce000000083996960000000b5e0000b2d800000000000000000000000000000007d100003de083e4388000000000000000003058d5eb7d8000507940a2ac00000001e5873f00000001e6219a837200034740002ce6000000000000000000000c67800000000002fe80005a91b6800000000002c1a4770000000119a00000005332b0626623fc0002a1e00014b43ab2292271085c01580aabeba55e00030a8514185c000066c000000046ea8ea000165043730fe1e7026a44537dc3171744c4c878ca8300000000000d3f8000000000002a00000000000000263a9b7886c05ba0420000e3e1ab000000021dc000290400000009b10000c4a8000e1522dc0001ede0001e2000011bc000169c0000000000000000000000000000000000000019349a3b73c4eb8000bd32e1a91380000000000269800000000000000000a591bc6cd98000000000000022f4000000000000006132428b49914c000000041f80000000000b16b97800000000000b9098600ac8db800000020bae6200001c230e60002e1e000000000000000000000e0c00000002a60d239f42d712ed23e0225245daea0976353c7fa0dc23e39444dc020aa58e98dcba39e0c28080f4854acb4bbd0e9c339b10e00000000000a78a6b1d980001404000000000000a20002d5800000008522b0a42c800000000007f40000170b1f6000114a00000000000000d9580003ce000000015960000000a700000a218000bc10000b690000e480000a8284fa00000247083326000000000022f6125000000012f000000000001b8c8daa1400001ab8e10b4640000000368a93a9e7113e3a59d2c0000000a86800032515fc176a53800033ec0000122000321400014be000363c000000000000000000000000000000000003d9246ce240000c9884fc0000000401a642945955c77200009e3afc80000e1a0002c180000000697800001e80000002ebc64f00000b88f22000000000000000003354000078e00000000001fc2449000000000000002f9a7a30000c92299a0001e3e9560000084242c00000006b6094c9a625ae00000005c700007010bc60000000000217000010b4000000084d0000000210c0002aaa00000009c51e7c0000000dbb020e8afaac200022540000d640f615dade8b3427cea104060004283c000088d000099f000026b0000000315e0b280002c70000ad58f5250fb27eb800000d94ad36d468000341817485f9cf885600000000
  | 66 => 0x62c6f4a63600002d80000000000068000000000000a84000000069d00006aa211c291b050a768000000119497b9e50000000000022443c08000c7730226252e580003a3003c3984b111360da29416af998fa9c42be0000260ad580498163997858000fe4e332b8ce200000ac80002d380003718000308854e0002d5600031a0a4e000079fb6b003b00002ab88740001a7c17b80001cc80000002a4600000001bd332400025e000000000001b8a00027848e180000000000c3580000000430000000000000ea0000000000000061bb0ce8c6290600000009148b4000000000000000000000099a000000030a0000034445f80001592b868ab2b02265af360002dfc436a0dc000083c11c29504d72f9e0000752000000091e0000000000056680003340000dea2e220000f2a00027b0388afcc8cb8734c5033eee860f7c29f800000018a8000000000019fe0000000000000058500009a3000000a994600035966a100001b90cc403b99aa0001d20b5507a07e58616abdb352b66b31c00000009438f0cc2d28ca21f12a84e52018338000000000001588000b79800078d07968ea2c0400012100000000b6b08de00000000000000d5080000001a627782d047362cc29f5b01200033e200027ac03919361a22fca000000000023c8000178e04303a4b1b8ef4000000000009587308000d931704cc893d6682800000035a2000272e08a26200002fbaad52a9ee75800000000000001986aa027b23f9a6280b5000000000001e88000e911636df980002ec80000000000a6780000000000000000074500000000000cf037de0000ff87971248695b41a5e5b4909960000be9938a022800000021d20000000e1b8000000000000000004b925fe1001ffc000391000000000001148000000000012308528000000000021d80008678d0ae0f9b52a9d80004753954305000000015620000000e7f8000d2480000000000ca1070a00000007350000da380003f700004a68000000310400000007e40000d4aa9fa0de80000002712995800000000006a4000031980000000000000000000000000b68000bc638fe0001bae142229c3ff098e00019e00002df800038ca7c200000000000000000000018ae00015e6dc51f8c0000a220000000000000000000005868000000000000000000000000000000000024b60000000b689bf8a2eae1200032d0d02b9725fe800000035e600000000000000000000099900000002cc06ba800000000000000d1400000008ef800032f345eddd8000b710000000000000032c0000148200000003753582da112e09f380008140000000000000000009a802ee3970000000000030636487f524407feb7a4c4e00000000f6e05980009de92280000000000399200000007f3000099f800005680000000ebe000000000000000002bc2
  | 67 => 0x6108aba4000000005d800000000000000000666965200013c8e7500000000000b899540000296c000000000036c25b00a748350000000000000000000002554000305a416800000021be62914ae00008ac0f996be00012dc0000000e2f82543d68000cd90000b2b8000d6e800000000000000000a772b8e4f298fc00015a400000002062f920001cc02a9812414badf0527a03e00000000000bc200000000000000000017a1f0091a0001ef400000000001bb60002e285280000e7319d63e20a0e71e800000032e6000000000000008c8a4e29da2f620000b00728000097c9c9a9aa2760000044a32e1fea0001a02cee800000000000000000266800000000000000000000017000000009228000000000000028103fb0000d25a30e0000000a6ab8eeaef000092980000001de800029fe000185413b8280000247a00000003bf0000cc0b1ba00000000000000000000000035c64fe0000000000000000000000000000000000005c60000000000387e000000055580000d300002a200000000000e921fa60000000d3a320e13a96d60000000a6800003b90000bd6000018c000000000006f2000000034180002e180a1129627d83e80000e989e7a9e2dfc0864b949ffec8601481f184b600038665f426346e621e818b82ba03e34debe503f26d335e41c38e004d584620000000000000000000000001b3a551000000026849a48000b8c00009a780005c5b87c0000000e4d0000982000000000004af000000018ca92121a0bd032c657426ead02220e000000064c80000000000000000000000008360000000000045000000000000e070568a7a1cbc2758a8ca62b9a823919541368b6c0000a66e7c9300c1180008fa97d2000000000000007d6356c1a900000000000a8f800000000000000000819b75200032bc6a8946a00000004a42d800001e1000000008bbb7fe000200400002385ae0000dfd0000e2c8000000000000000001572972156138200000008a2a6fcaf71674891963e000216acf815aa3628bb01019c0648e89780cc14e2b36a4c8000214400000000002c8400037a0b358be20000000000195000016380000000239a166000000004aa990064b2522c211f05120b5a9d582d20000d3000000000001fb60002b4ad8127006e88000000000000000287bc223e0000000ada8a9a00000000002e8a225839a000000000010d400002960b200009e3000000009100000000000065c00002220000fde29880007b4800000000000000000000344c000262a3d7000000000000000000c29afa2d1e3790e3d0acc000000000000001682fde0002e386b700000000000c5d1f6c28c28221a58000000248e879800094b990400000000000000d5711e2358b37cb641c3add68000e940000000244271d1170a6980004ae0000000000015f0000000
  | 68 => 0x380004dc00000001620628800000000002b6000033493480da2cdc00002b686db3680000000000145400000001890000369248800000000000000125b8b6000000000000005b38000677362600004a2caf8eee0001dfa04e8000dd2143a00000003d61f329fe02fc7292a5246336e843200005bf00000000000000000082f00000000000000066600008506ab00005d1a3280d7046e000349a6fa8000e130000000000000000008b4392edeb00000002c9000000005ff25066ea1a52000000000000009a28000ba49f4a58c000000012ea18000000002fbc1f883c60001be80000000bb118f8d88b6a045580007d6800083d965c1f3a7b41e92ac0b6080000000000bdeba1e4d6000000032b60000b8800029ee7630000e6d0000944a6f8ad100000000000000000074780000000000000000092480007f22b10000000088aa03a00000000000000619959c81fb080b88000058c85bac9f04f02ed000066a0000138800000000000000000e8280004850000743800016680000000000000000085d1bac1fa2058c0310ee8ea8d1c00023445da3146000287c6990000000000000000000001b46000000000000000000000e4500001d6990600000000001d546b19ca88148822e8327ca6c91392000043a29b00000000000032000000000004e78000000000000000000000000000000000000001a0add27fc011400000000002b66000000028b0000000157a00000000002d3a2fda0b00000000000000000000000000000e7a000096000006a3000000000009bd0000d6b8000dae000000026aed2106200003a2a000000018d0000000121a83b285ae490000e5a0000794800000000000000000a58131a0000000a9c04b80001a822a93a5667eb746350802cb811a6ac928af89d69d6e00000007a18000d3900003ba09180000000df0333a72f80006db8e3c717365a8cf9166a5daf74b828000000000000000001930000bee0026000000000020a8e8e015cd8a36da408939a2d48000a038000000270e0000000cd78000000000087e1eaaa501dacb9a80000000000000000000000000000000e378000495000000004d800007d0000354a68ab018e0e11e448f97c2000000000006269f0382a00000008b531540000000000237c00034b2a38000033d00000000000d7580000000000961290e2e49606dbe0000000202600bb9122bca36600000005288ec0000000000013a60001e9c3371dea71583949201d580002a4c41c123861b040a4a38000000038eba69ccc87f2f128e607023891cead5c00000000000c098000cf38a82000000022e00000001f2e608800000000000002f5a2500000cab0000007393e000017800011aac8fb0060001a280002dcc000388c000000000000000000000000101abac8000016315aa190000456b8ba0000000d342bf
  | 69 => 0x440000924a7f39b2d7335f400026320002038a88800000020204df8be61808000909000080b8000000000042db42a53827c6a97800004981060000000000000062a80002dc800000009280000000524023a00000000000000a2120c8d2d0308000262e00031441ae973047c872ca26a9f00000000040360ae5194d48e32bb8000222017200000000000000000000024ca9bdaa8201b8120000000018f859ec400000cff86fa82980009669078d5a9d36202241600000000000000000277000019be0000354773800000037fadd90000000000000011ae8d81326000000000000005c1b77ad569b5400000007a204f40000000000190a0000000d8a834a00000008f300000000000000000000039e200000000421034e31b0d2000000011d8d160000fc40002f2c47414100000a8e00000000000000e38800032d00000000000000313a00000000000690000214cd0824dc00000000000d6c93c1942e2b03960002c24292391c0000000000000000000004cd8000dbe80000000000ac6b75803e8000c3d37988008000e10000000000001c980004ac8000000000000000000d69676000200ec648000000148e000043e58aa106d1483a8510000000001c4000137a000000000000008fc8000a272c700002678e3e000008b33be0e988c6cdc19f4ce688e810413be375b25e40c8384bae0eea6438ca2e2ab2b459e8580ce50592178800000000000cd0000000184a0000b4208a9b087ba800000032ae00037e43d39208000308800006ee0000000000000019e8000767000000028560000000000100033a8000000000000000000000000608000041100000000000e8f800008600004bc935200000000002cde7c28ade5de01ba00000002d4000000000000000000e2900006ff0000d1a83aa0fb84c473983e2e9608f63dcb942b43251e7d9b0fabda0000000000000000000000000cd28000000022e0000000000000053189460000000a7e18b8a39a420d0c8df85fdacc6000206209000000000000000127c00035b80000000000000000022c009215fec1a115ed5d8000000000000003a00000000d6600000002b205e280006580000000284cdaa1d22dd88e880000224d589bc04f9184e00000003dea8c400000000000000000000000038c20000000000000000000000002fd81879f9223e1c3e000000000000000000000a108000274333653b114e0000000d2a80003df80000002a3053f07fe390a3f00002d22a02810e0000000000102c90f39ea6491b1ea4fb15c000000000000006b02cf200039388d50000a8f2ee4000000000008203258000000005a00020b40d580004f680be4a9b2745cd96f0000000000000000000000000000061e294e000282800012aee7409423a2b11c83ea9eca848e28bea92c04d9aee877d00004b300000002ecae1
  | 70 => 0x1c48000377e0003634000222c45802fabcd1202b1c8000281156c0000e8ee4c00000000000000000000000000001b72000340c8e526661218c028c985326cf0d4a07e18164d137c6bae800055487eaa6511840002ab4c73a6ec1e200000000000000000000000000000188beb13f2a8d9832bb3adda14835ac000129e00018e2000000000000000000000727a70c00022ea47000005e43712ab40000000000084e000000000000000000c1794f00002d5091b800000000000002c96e2b8000000000041f0000d15800000000000000000d141c4000000000000000c9a00000000f1039d8000c7a00000000000000000000000002c6a178a70a19800027f4742b57200017ac00000000000000000302e00000000001bec0001c4e67a00007039daa688a464000353628d2b840000000000000000006383032be4d9e0000000000000015ee00017e6000000000035e80000c4e0000000000000069b00004c700000001bf60000000df6800000000000000000c90000000000006f390e65ed89320002f1a72535324078000a4529b240297640001fd860707ac0000c5ab1d1b5600023b80000658a7380000003460cac00008b8a602c391c26000000000002dc000000069500000003454cd326e400009c82cb8ede000286296980002fd370cac6242ac1387b04d0000028a322223825f640da7aa00000000002f3e7e6af0e000000000000000000000000000092f90e800000001d1a0e85468000a24000059799ca00034360000000000000000000000002d7c0000000000204e000000000000004c100d661e8000686827e584355eb1936d0bef95685530fb2b0e0000d4800008ffb802000000000031840003036cc5800000000007eb27c81df183aa18040e0000000bd70000ab62342df3000000000000000000000080600000002e000000000a4cc5a800000000000001f3c0000000000000065e80000000000806b54600039bc000214600032828d3a34c00000000000000000000000020c4a19a86e000364a7e0000004b955e00035a00000000b40800000000007f7b1e2840925ae062f4e0001e4200005185cc9c10000244422b800000026b4b4000000000000c62b3d0507000004b000000000000000000000332a51a2028000198c9e600000000322000000028f8a4ac6e000000013380001d662d1800061caf540001374000000040400000002aa0a488000c7400000cf00000000168a730000000000000000000000f7600000000003528000000000000000000000000000049700000000000440b6a40000000000000000004bc0000c560001f1c000276a3aca1820001d1a00039f6549813092a3508bab80003cc869c000237ab9180000001530242299200000003f096d20001e2c00026483fc8000bdc00000000b380000b
  | 71 => 0xffcb5e8000927919285500004f3163c5bfb81a13cab584a000000000000cf6956e6279cf6000320440a224ed1680000001b160000000af2800068b1ae200006f8000000000037880001e0270023340000000000015ea0eb7c4d4b8e0e0000000000025ab0d9414aa4847e0000000000272a00000000000000d87000035e8000000088c17cb244adc0b0456080000000000af100009521d129d08454000000055f044cc84101211d179200038a6a8b0000bdb9072dc38000809399a000000000000000000000665007c00000002dfa8a660480000000000000000082400006b7800000000006c48c9800000009e580000003a42000000000000000000370cf28000be800008c59d9e4ca099c0000a2ad8789b8a36b5da00007b800000000001a000002036827a6b090415e09619476a65a0acd5991980db976a8bc80009838f9c0001b48121000016a0bbc000312e0000000988800000017b8d4e34fcd6202f6000000008ca09600000000000000390000000000008db1b0a0000082000000014780000000000000000047d252425400000002b7400000000000000aed81ac4c0a13c0000000d270000d8cb400000317600016424031066000033885400002dc373a00016c8e52911e00039aa00001182a595c00001b88bce2f9622c1d2e3860f360c290e039e8000259000000000000001eb2e05b8d47c022ae000000000000005ca00000000000000000000000009ac9542000011652a24d80000000000000023e8000000265a68200000002cca000104e0000000000142e85f00000000000c09000036ca29ebfc80000001246dc9000083e06e0c10b32c6748ef2ca2000040ea638bb7a2647ed14dc66114ce3a78d7069c267691ab9043a40f34e0514bccb639b030293ec7b725ca23c026ea88146487127a64059e5600019669ca0db8bb809e60001884cd897c600000000002908cda9ba028e85f892532ca000011a3cf000043d0000e172a0e9652430c7e00000000000000000000000009bc8000d3e253209f0c2e00003ba00026c812680000000000c87800000006a20000034000000000031720001664d47800002628e4b1011e60000000000000067d8d4c14a000092e0ac0044000000000008b3b9b81eeaa6e6b6800000000000000000000000000000000000bea00000002bc0000000000000000001db1f36c818000d63177012023c40000b34def000005f00000000930000000063400f20002980638000000000000002dd8489b7aa00000005f208f20002aa20000b969240000ca280000002bbec54000000000000000000000078624e02827fd8000097255000036cc00024ce92f0ac6e47989c00000006052c2200000000002cc800012d23f62162000207040e1fb23f6abd8000000033300000000000a61281466b00000000d0000000000
  | 72 => 0x253a00000000000000d32311600007f25e600000001da2e80904c34f0d38000000002e0000000000000020000001c2a65006746d100000002892e6706b09b380000003a540000456000306058b3734d0723964db00008bf92700000c72c7f000000000000000000000000000000000000000000187000009d80000000d04b0c87eeb9a42e880000000000000000000000000002dfe0000e940000000026800000004ec290000091a048e8ae80004f13428000111c19e001ab8901349e480000313852421000073418c6c41adc80000000cccb0e800000000000b9c00005846f0abe2000000000010de53920a444d09ea5bca84048f117200023c200006284749db000000000001da6d330dbe0000000000126e0000000c12290c160b8720002da695a800000000006180000556aee6adb8ace06ca750000000032700000000000000000045bb092a9a306c3b0a12693f000000000002ce80004af8000ae4000000010c67ca802088015a6000000000000000000000000000000000000001ba60000000af184aa0000000000379c000072ae4f1478c5804f80000000d3b1c9654a8ae299400000000000b47000000000009d12e1063521f60910e3609c17f8a5b8586b050264e6eaf720001f70db237e20000000983271e0000c9a323800000000000001eb88048000b29000070780000003272000194a12ba4f6090800089d086e0001ec0000228249a8000e7b18b400021ba000000080c000000000000000000000048a5d20730e2f2732d0399ec85a0d1e0f3000000000000002fe200037fc0002d720000000000000049a000072d1a4e000000000000000002b0c0001a265770000a09069a000000000006ce6cb36d4d863a4a6fb87faa68800000015980001c86bc9a07a000000071e00007a980000000ab2cf7219600000000000000091b26c00000000001a4c0000000692000021c00000000000bd80ffe1c913b4000314c0002f8ec7b000000035fc4160000cd60000000136e00000005491ef8a308000000000000016660000000d100000b3aa2e4a0690a073faa88c5a2f2e5fb89226b9130890f823ca9f0000c8c2
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc9c7458d300400195ee8b1260080032b1d1624c0100943ec36ea9002000c3e64dd520040498dcc5baa40080021fa1d654801003c3e43aca9002000c3f755912004001878eab22400800317dd663480100062e3acc69002000c5f7558d20040018b8eab1a40080031bdd56248010006363aac49002004cb57059310040070f90bbb2200800a2f213764401000c76416ec880200c87d86dd5100400187cc9baa20080031b98b75440100043f43aca880200787c875951004001878e8b2a20080031b1c9654401005c5ec36e88802000c3e65dd1100400187acbba220080032b98b74440100045f43ac888020068bc87591100400187eeab2220080030f1d5644401000656392c88802000c5e65dcd10040018bacbb9a20080032799373440100064eb26e68802000cce62dcd10040018bcca39a20080031759473440100064f320e68802000c9d641cd100400199cc439a200800237a1e63440100b46e43cc68802000c5f7598d10040018b8eb31a200800327dd263440100064e3a4c68802000ccc7298d10040011bd0eb1a20080023721d63440100062fbaac68802000c5c7558d100400193ee8b1a2008003271d1634401000666392c6880200a8ed86dc910040018dccbb9220080031b597724401000657326e48802000cad64dc9100400199cc7b9220080033358f72440100047743ac488020058ec8758910040018deeab1220080031b1d5624401000657ba2c48802000cac74589100400199ee6b122008003331cd62440100065a3a6ec8802000c7785dd910040018e90bbb220080032de1376440100065a426ec8802000cd783dd910040019a907bb2200800339e0b764401000672416ec8802000c7776dd510040018eeec3aa20080032dddb74440100055b43ac88802043ab4875911004001c6eeab2220080038d1d5644401023759c02c88802004eb080591100400996ee0b222008013ac8c164440100066bbb6e68802000e9564dcd10040019aeec39a2008003551d473440100074ab20e68802000ce776dc91004001d4ac9b92200800339dd87244010006d23a0e48802000ea5641c91004001b88e6392200810eec211304401000758b22608802000cba64dd91004001970e9bb220080031ee1776440100063c42eec8802000cbb84dd9100400197109bb2200800336e0f76440100066c41eec8802000ceb82dd910040019d105bb220080031eddb75440100063dbb0ea8802000c7b7699510040018f6ecb2a20080032eddb74440100065dbb2c88802000cdb76dcd10040019b6ec39a2008003661d073440100066dbb4c68802000cdb7658d1004001d32c8b1a20080033addb724401000675bb0e48802000ceb7698910040019d6ecb1220080039a595624401000764b1ac48802000eb16498510040877650918a2008002dce153144010
  | 1 => 0x90eb12a4080123be1d62cc81001c3e42eec99020048ec82dd932040010ff0abb2640800e1f215764c8100043ec36ea9902000c3e64dd532040838dcc5baa64080021fa1d654c8100043e43aca9902000c3f755913204001878eab22640800317dd6634c8100062e3acc699020048dc8758d32040018beeab1a6408003171d5634c8100247643ac49902000c6f7558932040018d8eab1264080032d593714c8100066ab1ee29902000ce562dc532040011eb0c38a64080032d590714c8100071ba8ac92882000e575158e5104001ccea2b14a2080031e59570944100145f426ed18820008bd84dda310400517d08bb462080030f9d1658c4100045fc32e91882000c3e655d2310400187acaba462080032b989748c4100045fc3ac918820008bd87592310400193ce931c6208003275d2638c4100064f3a2c71882000c9d7458e310400195ce8b1462080032b5d1628c4100066cb1ae1188200387c85dd931040031d905bb262080c61f61b754c4100061f326ea9882000c6e62dd531040010fd0eb2a620801e1f21d654c41000636392ca9882000c3f755913104001878eab2262080032b1c9644c4100062fbacc69882000c5c7598d3104001998e531a620800317dd5634c4100062e3aac69882000ccc7258d310405f1db0db9262080031b997724c41000636b2ee49882000cae64dc9310400195ac9b9262080033398f724c41000666b1ee498820008ee87589310400b1d90eb1262080031bdd5624c410006363aac4988200387e855d831040010ff0cba862080030f991750c4100b62f31aea1882000c6e625d431040010ff0eb2862080021f61d650c4100061f3aac81882000c3d755903104009974e0b206208003179d5630c4100062ebaac61882000c6e7558831040018daeab1062080133a9c1620c4100066abb2621882000e55654c43104001d2ac89886208003b1589310c4100065cb22e01882016cda635c031040019d2c4b806208003744c5700c4100043fc32eb1082000c3e645d6210406d8dcc4bac42081ba1fe1d65884101b43ec3acb1082000c3e75592210400187aeab244208003179d663884100062ebacc71082000c5e7558e21040018baeab1c42080123be1d6288410006373aac51082000c6d7558a21040019d2c4b84420800e1fa1576cc0100246ec1aed980202187f865d7300400187cc8bae600805b1798d75cc01000637312eb980200787f8759730040010fb0eb2e60080030f9d564cc0100061ebaac99802000c5e7558f30040018baeab1e60080031b9d562cc01000636baac598020028bc84dd930040091b907bb260080030f1d1654c0100e45ec36e89802000c3e65dd1300400187acbba260080032b98b744c0100045f43ac898020068bc87591300400193ee931a6008003271d2634c0100064fba2c69802000
  | 2 => 0xd4358c100052f42886b182000a5d8510d630400159d0421ac608002b36084358c100246f43c64b182000a5e850c963040014bb0a192c608002a7a103258c100054ec2064b182004e57105956304009caa20b2ac608013a5c416458c100274d082c8b182004e951059163040018beeb3aac608002b3e097558c1000566412eab182000ad4815d563040015b700ba2c608012b62017458c100052f428e8b182000a5d851d1630400159d043a2c608002b36087458c100070faa4a8b182000ace82951630400159b052a2c60800297e157258c100052e42ae4b182000ad4815c963040014bd0a392c608002976147258c100054f420e4b182000a9d841c963040014bd0ba12c608002976174258c100054f424e2b182000a9d849c563040014bd0a38ac608002976147158c1000567416a2b182000acd82d4563040011bd0fa0ac6080023761f4158c100052f42e82b182000a5d85d05630400159d05a0ac608002b360b4158c100256d40082b182000ad98010563040014bd0b90ac608002976172158c100054f42042b182000a9d8408563040095b50010ac608002b66002158c100272d286a0b182000a9e84c81630400153b09902c60800317d4d7694c100243fc3acb2982000a5f835965304001c3ea6b24a60800e97a156394c1000c76416eca9820008ef825d953040031d904bb2a6080121f21d6554c1000636392caa982000cac725915304001998e531aa6080123721d6354c1000666392c6a9820008ed86dc9530407b8dccbb92a6080031b5977254c1000657326e4a982000cad64dc9530400199cc7b92a6080033358f7254c100063ab2ee2a982000cb564dc553040019aac7b8aa6080023d6187154c100065ab20e2a9820009f1801c55304009d4e20b24c408013a944164988100047a40ae8b1020048ee87d4962040091dd0fa12c4080029ba17425881000536c2e84b1020048ec875096204009cd420b2ac408013a9c41645881002752882c8b102004ec71058d6204009d9420b1ac408013b144163588100053742ce8b102000a6d859d162040015cf02ba2c408002b920574588100047743ca8b1020008ed879516204001c5ea92a2c4080029be1573588100053642ae6b102000ae4815cd62040014dd0a39ac4080029b614735881000557420e6b102000aad841cd6204001c9ea729ac4080023be1d53588100047643aa6b1020008ee8710d62040011db0e21ac4080029ba14435881000536c2886b102000a6e859c562040014db0b38ac408002aba10715881000556c20e2b1020058ee87d4562040011db0fa8ac408012baa00515881000574c00a2b1020058ee87d0562040011db0fa0ac4080029ba17415881000536c2e82b102000ace83d05620400159b07a0ac4080139a94350588100243e42eeca90200487c8759552040091d
  | 3 => 0x2982200087e86dd52044001878c9baa40880931b18b754811026c3f43eca902202487c87d95204400187eebb2240880030f1d764481100062fbaec69022000c5c75d8d20440018beea31a4088003171d4634811000637baec49022000c6c75d892044001968c9b8a40880033518f7148110004dac20e29022000cb4641c520440019a8c638a408800339d8871481100074c320c7882200cc7676d9610440078ecec32c208802f2d9db64841100066b3b6c70822016cd67618e1044001ca8ca31c208802b399db628411000e733b0c50822000ea46418a1044001d88c631420880121fa1e54594100061fba4a8b282000a6e8295165040014db052a2ca080121f21d54594100243f43ca4b282000c3f749d165040014dd053a2ca080029b60a74594100062fb9ce6b282000a6f825cd65040014d904b9aca080029d20573594100043f43886b28200087d8710d65040014dd0421aca080029b60843594100043f43e84b28200087d87d0965040010fd0e192ca080021f61c32594100051f42064b282000a3d840c9650400f0fd0fa0aca080021f61f41594100052f41e82b282000a5d83d0565040014dd05a0aca080029b60b415941003c3f43e42b28200087d87c85650400147d0810aca080028f61021594100253d40042b282000a7980085650400147d09902ca080028f61320594100271b884cab202004e35109956404009c6e20b2ac8080138d441655901000557416eab202000aad82dd5640400187eeb3aac808222aee0173590100255c402e6b202000a3e851cd640400147b0a39ac808002aba08735901000556c10e6b202000a3e85dc9640400147b0bb92c80821eade0572590100055a40ae4b2020008be870c9640400117b0e192c8080028fa1432590100051ec2864b202046ab9809c5640400155d05a8ac808002ab60b51590100051f42e42b202000a3d85c85640400117d0e10ac8080022f61c21590100271d286a0b2020068be87c81640400117b0f902c8080123720d7598c1000477c12eb31820018ec825d663040091b906ba4c60805b17dd75398c100043fc2ae5318200387c855ca63040091b906b94c608013a5c416498c100274a882c93182016c5f759d6630400159f04bacc608002b32097598c100070faa4a93182000ace82952630400159b052a4c60800297e157298c100052e42ae53182000a5e85d0a63040014bb0ba14c608002a7a127198c100054ec24e33182000ace82d46630400159b05a8cc60805a37a1f4198c100046ec3e833182000a5e85d0663040014bb0ba0cc608002b3a0b4198c1000566c16833182000a5e85c8663040014bb0b90cc608002a7a102198c100054ec20433182000a9e84c82630400153b09904c6080123e2017458c100246f43ea6b182000c5f75d4d63040091bd0fa1ac6080123721
  | 4 => 0x14401717b0fb246288003279d3638c5100064eba6c718a2000c9e7418e314400193ae831c62880032b9d3628c51000656ba6c518a200387c851d931440031d9043b262880021fa1b754c5100061e326ea98a2000c6c62dd531440010fd0fb2a62880021f21f654c51000636396ca98a2000c3f75d913144001878ebb2262880032b1cb644c5100062fbaec698a2000c5c75d8d3144001998e5b1a628800317dd4634c5100062e3a8c698a2000ccc7218d31440011dd0db9262880031bd97724c5100063632ee498a2000caf64dc93144001958c9b92628800333d8f724c5100066631ee498a20008ee87d8931440011d90fb1262880031bdd7624c510006363aec498a2000cb864dc13144001970c8382628800336d8c704c51001c3e42cec18a202c87c865d43144001878c8ba8628805b1718d750c51000636312ea18a200087f87d9431440190fb0fb2862880030f9d7640c5100061ebaec818a2000c5e75d8c31440018baebb1862880031b9d7620c51000636baec418a202987c865d62144001878c8bac42880db1b18975885100043fc3ecb10a200c87d87d96214400187cebb2442880030f5d764885100062f3aec710a2000c5d75d8e21440018bcea31c4288003175d46388510006373aec510a2000c6d75d8a21440019d6c438242880031dd9771541100066a31ee2a822000c77651c550440019a8c638aa08800e1f21676cc1100043e432eb9822000c3c645d7304402d8b8c6bae60880031b18975cc1100043fc3ecb982200087d87d97304400187cebb2660880030f5d764cc1100062f3aec79822000c5d75d8f30440018dcebb1660880031b5d762cc110004dac24e39822016cd4639c7304402d9a8c6b8e608800e1f216768c11000c76414ed182201f87c865d63044001878c8bac60880031b189758c110026b8082eb182200087f87d9630440190fb0fb2c60880031b9cb658c1100061f3aec91822000c3d75d92304400195ce5b246088003179d7638c1100062ebaec71822000cce72d8e30440018bcea31c6088003175d4638c11000667390c7182201e8ec865ca30440018decab9460880031b195728c11000657b22e51822000cac645ca304400199ec6b9460880033318d728c11000477c3ec5182200a8ed87d8a30440018dcebb1460880031b5d7628c1100043fc2aec982200387c855d9304400117f08bb2608800a2f211764c11000477c12ec98220018ec825d93044005179083b260880030f1d3654c1100045f436e89822000c3f65dd13044001878cbba260880032b18b744c1100045f43ec898220008bc87d91304400193ee9b1a6088003271d3634c1100064fba0c69822000c9c7418d304400195ee9b1260880032b1d3624c1100063a32ee29822000ce462dc530440018e8ca38a608800335d8c714c11000672310e
  | 5 => 0x80023de0574589100045f438e8b122000c3f751d16244001878ea3a2c48805a37a1f73589100062fbaee6b122000c5c75dcd624400193ee9b9ac488003271d373589100062fba8e6b122000c5c751cd624400193ee839ac488003271d0735891000637baee4b122000c6c75dc9624400195ee9b92c4880032b1d3725891000667b9ee4b122000ccc73dc96244001968e9b8ac488003351cf7158910006373b6ca31220008ed8799462440014dd0b328c488002aba12651891000556c24ca3122000ace83994624400159b07328c4880023be1d651891000557c22ca3122000aac84594624400159f06b28c488002b320d651891000537430ca3122000c6e76194624400195cedb20c4880038bd9764189100071632ec831220008ed8799062440014dd0b320c4880029b616641891000557424c83122000ace83990624400159b07320c4880023be1d641891000537c2ac83122000a6c85590624400159f06b20c488002b320d641891000573c0ac83122000aae86190624400195cec320c4880038bd94641891000716328c83122000ea581190624400199cedb18c48800393d9763189100072632ec63122000e8f64d8c6244001d18c9b18c4880023b61e63189100053742cc63122000a6d8598c624400155d09318c488002ab61263189100056741cc631220008ef8758c62440014df0ab18c4880029b215631891000557c22c63122000aac8458c624400159d0c318c488003339d8631891000727b28c63122000e4c6518c6244001d1ec8318c488003a3190631891000573434823122000ea4649046244001d88c7208c488002b9219411891000752322823122000ec46350462440017c100a08c48800a2fa1376549100045ec26eca9220168de83dd952440011bb07bb2a4880021fe1576549100045fc22eca9220028bc845d952440011bf06bb2a48805a3720d765491000477c12eca92200187e87d9552440071dd0fb12a4880021fe1576cc91001c3e42aed99220008bf845db324400517908bb664880063720d76cc91001c3f42eec992200087d85dd9324400517d09bb264880022f613764c91001c3f42cec992200087d859d932440010ff0abb2648800e1f215764c9100045fc22ec99220028bc845d932440011bf06bb264880023de05764c91001c3e428ec992200087e86dd53244001878c9baa64881071b18b754c9100043f43eca992200087c87d95324400187eebb2264880030f1d7644c91000c6f43ec69922000c5f75d8d32440018b8ebb1a648800317dd4634c9100062e3a8c699220168ee87d8932440018deebb1264880031b1d7624c9100063db2ee0a8a2000c7b651c1514402d9b0c7386628800a2f212768c5100061f3a6cb18a202d8bc865d2314400187ecaba462880030f195748c51000656312e918a20008bf87d923
  | 6 => 0x666396c6a9a2000ccc7218d53440011dd0db92a6880031bd977254d101ee3632ee4a9a2000caf64dc95344001958c9b92a68800333d8f7254d100066631ee4a9a2000a6e85d0b62440014db0ba16c48800a3be1d42d891000557424cbb122000aad84997624400159d0732ec488002b360e65d891000557c22cbb122000aac84597624400159f06b2ec488002b320d65d891000717b2ec9b122000e2c65d9362440014dd0b326c4880029b61664d89100056741cc9b122000acd8399362440014df0ab26c4880029b21564d891000567c1ac9b122000acc835936244001c5eca326c4880038b19464d891000752c08c9b122000e4f65d8f6244001c98cbb1ec488003a3d9363d891000746326c7b122000a6e8598f62440014db0b31ec488002aba1263d891000556c24c7b122000a6f8558f62440014d90ab1ec488002abe1163d891000556422c7b122000e4f6518f6244001c98ca31ec488003a3d9063d891000746320c7b122000ea46490762440017c100a0ec4880029ba1474d891000536c28e9b122000ae6811d362440015cb023a6c4880023ba1e54d891000476c3ca9b122000e2f5495362440014dd0bb9ec4880029b61773d89100053742ce7b122000a6d859cf624400155d0939ec488002ab61273d891000727a9ca7b1220008ef8754f62440011d90ea9ec4880023ba1c43d891000476c3887b122000a6e8510f62440014db0a21ec4880029be1571d89100053642ae3b1220008ee87d4762440011db0fa8ec4880023ba1f41d891000476c3e83b122000a6e85d0762440014db0ba0ec488002b3a0f41d891000566c1e83b122000a6e85dc362440014db0bb86c488002abe1170d891000556422e1b1220008ee8714362440151db0e286c4880023ba1c40d891005476c3881b122000a6e8510362440014db0a206c488002b3a0c40d891000566c1881b122000ae68110362440015cb02206c4880031b18b75589100043f43ecab122000c3c74d9562440010fd0e32ac4880030f1d065589100145f436e8b122000c3f65dd16244001878cbba2c4880032b18b74589100045f43ec8b122000c3f75d916244001878ebb22c4880022fa1c64589100061fba8c8b122000c3c7519162440018becbb9ac4880031719773589100064fb26e6b122000c9c64dcd6244001998c5b9ac48800317d9473589100062e328e6b122000c9f641cd6244001938c839ac4880033318873589100046f43ec6b122000c5f75d8d62440018b8ebb1ac48800327dd363589100064e3a6c6b1220008de8718d62440018beea31ac488003171d463589100064fba0c6b122000c9c7418d62440070fd0fbaac48800a2fa1f74589100061fbaee8b122000c3c75dd162440010ff0aba2c48800e1f21574589100046fc1ae8b1220168dc835d162440011df04ba2c48
  | 7 => 0x6f751c963440018d8ea392c6880032bdd07258d10006563a0e4b1a2000ccf731c963440018e8ebb8ac688003391cb7158d100065c3a6e0b1a20008df8758c63440014bf0ab18c688002972156318d100054fc22c631a2000a9c8458c634400159f04b18c688002b32096318d100b46e41aea31a20008ef825d463440031d904ba8c68805a3720d7418d100b62fbaea631a200087f855c863440070f90ab90c688003179db6518d100046ec3cca31a2000a9e84994634400153b09328c688002b3a0a6518d1000566c14ca31a20008df87594634400153f08b28c688002a72116518d1000567c12ca31a2000acc8259463440018bcec328c688003279db6418d100070fb2ec831a2000e1c65d9063440011bb0f320c68800297a166418d100052ec2cc831a2000ace82990634400159b05320c68800237e1d6418d100052fc2ac831a2000a5c85590634400159f04b20c688002b32096418d100064f3b0c831a2000e1f651906344001c38ca320c688003a56046418d100052f42cc431a2000a5d85988634400153d09310c688002a76126218d100072a32c8231a2000e94649046344001ca8caa08c688003a51914118d10005e84028231a2016c5f759d4634400159f04ba8c688002b32097518d100070faa4a831a2000ace82950634400159b052a0c688002b5a065418d100056ac0ca831a2000a5f855c863440014b90ab90c68800297a174218d100052ec2e8431a2000ad681d0863440015ab03a10c68800297e157118d100052e42ae231a2000acf825c4634400159904b88c688002b3a0b5118d1000566c16a231a20168de87d0463440011bb0fa08c68800297a174118d100052ec2e8231a2000ace82d04634400159b05a08c688002b6e014118d100056c4028231a2000e954110463440014bd0b908c688002976172118d100054f4204231a2000a9d84084634400153f08b80c688002a72117018d1000567410a031a2000acd82140634402d1bd0e200c6880023761c4018d100052f4288031a2000a5d85100634400159d04200c688002b36084018d100056b4088031a2000ad581100634400153d09900c688002a76132018d100052f4284031a2000a5d8508063440014bf0a880c688002972151018d100054fc222031a2000a9c8444063440018bea73b4a6880022fe117694d100145e422ed29a20168dc835da53440011df04bb4a6880063b2097694d100052ec1ecb29a2000e1f53d9253440074b90bb1ca68800a2fa137654d100045ec26eca9a20018ee82dd953440011db05bb2a6880063ba0a7654d1000476c14eca9a20008bf845d9534400517908bb2a68800237e0d7654d1000477c12eca9a20018ec825d953440011ef02bb2a6880063b2087654d100b43f43ecaa9a2000c6c72d955344001958e5b22a68800e37a1f6354d100
  | 8 => 0x4b2ec688002b320965d8d100070fb2ec9b1a2000e1c65d9363440014bd0b326c6880029761664d8d1000567414c9b1a2000acd8299363440014bf0ab26c6880029721564d8d1000567c12c9b1a2000acc825936344001c3eca326c6880038719464d8d100074ac08c9b1a2000a5e8598b63440014bb0b316c688002a7a1262d8d100054ec24c5b1a2000e946490763440017a100a0ec688002b3a0b75d8d1000566c16ebb1a2000c5d751d763440014bd0b3a6c6880029761674d8d1000567414e9b1a2000acd829d363440015ad023a6c688002b560474d8d100070faa4a9b1a2000ace82953634400159b052a6c68800297a1772d8d100052ec2ee5b1a2000a5e859cb63440014bb0b396c688002a7a1272d8d100054ec24e5b1a2000a5e85d0b63440014bb0ba16c68800297a1771d8d100052ec2ee3b1a2000ace82dc7634400159b05b8ec688002b3a0b51d8d1000566c16a3b1a20008de87d0763440011bb0fa0ec68800297a1741d8d100052ec2e83b1a2000ace82d07634400159b05a0ec68800297a1721d8d100052ec2e43b1a2000a9e84087634400153b0810ec688002a7a1370d8d100054ec26e1b1a2000a5f855c363440014b90ab86c688002b3a0850d8d1000566c10a1b1a20008de8710363440011bb0e206c68800297a1440d8d100052ec2881b1a2000ace82103634400159b04206c688002b5a0440d8d100056ac0881b1a2000a9e84c83634400153b09906c68800297a1420d8d100052ec2841b1a2016c5c635d6634400187ce9b2cc6880031b9cb6598d100061f3a0cb31a2000c6e72196634400187ecaba4c6880030f1957498d100b64e31ae931a2000c3e75d92634400187aebb24c6880032b9cb6498d100061f3a8c931a2000c3d75192634400195ce4324c688003179d76398d100062ebaec731a2000c9e74d8e634400193ae9b1cc688003339cb6398d1000637b2ae531a2000c6c655ca634400195ec8b94c6880032b1917298d1000667b1ae531a2016ccc635ca63440010fd0fb2ac6880030f1d36558d1000636396cab1a200087e871956344001878e832ac6880031b1c86558d100061fb2ee8b1a2000c3c65dd1634400117d0fb22c6880030fdd76458d100061e3aec8b1a2000cac72d91634400117d0e322c6880030fdd46458d100061e3a8c8b1a2000cac7219163440018decbb92c6880031b1977258d1000657b26e4b1a2000cac64dc9634400187eebba2c6880030f1d77458d100043fc2ae8b1a200387c855d163440011bf06ba2c6880023be097458d1000c76412e8b1a20008fb805d1634400187eea3a2c6880030f1d47458d100062fbaee6b1a2000c5c75dcd634400193ee9b9ac688003271d37358d1000637baee4b1a2000c6c75dc9634400195ee9b92c6880032b1d37258d1000667b9ee4b1a2000c
  | 9 => 0x41d95100043ec3e83b2a2000a5e83d0765440014bb07a0eca880029ba0b41d951000536c1683b2a2000e354110765440010fd0f90eca880021f61f21d95100051f42043b2a2000a3d8408765440010fd0e206ca880321f61c40d95100052f41881b2a2000a5d8310365440014dd04206ca880029b60840d95100053b40881b2a2000a7581103654400147d09906ca880028f61320d95100043f43841b2a200c87d870836544001878cbba2ca880032b1c864595100062e32ee6b2a2000c9c64dcd65440018b8ca39aca880032719073595100063632ee4b2a2000cac64dc9654400517d0fba2ca880030fdd774595100043fc2ae8b2a20008df835d1654402d1b906ba2ca880023be09745951000c76412e8b2a20008be871d1654400187eea3a2ca8800317dd773595100064fba6e6b2a2000c9c74dcd65440018beea39aca8800327dd073595100064e3a0e6b2a20018ee87dc965440018deebb92ca880032bdd37259510006563a6e4b2a2000ccf73dc96544001998e7b92ca880031bdd4725951000657ba0e4b2a2000cac741c9654400199ee6392ca88003331cc72595100066a39ee2b2a200087d8799065440014bd07320ca880029760e641951000537414c832a2000a6d8299065440010ff0eb20ca8800297e0d64195100052e41ac832a2000a6f8259065440014d904b20ca880038d60464195100051f424c432a2000a3d8498865440014bd07310ca880029760e62195100071a3248232a2000a748650465440016e100a08ca880030f9db65d91100045ec3ccbb222000a3e85997644400153d0732ec888002a760e65d911000557414cbb222000aad82997644400117f0eb2ec888002a7e0d65d91100054e41acbb222000aaf82597644400155904b2ec8880028fa1865d91100061f3b0cbb222000a3e8598b644400147b0b316c888002a7a0e62d91100054ec1cc5b22200bab686dc7644408776501b8ec888002abe0975d911000556412ebb222000c3d751d7644400147d0b39ec8880028f61673d911000557414e7b222000aad829cf644400147f0ab96c8880028f21572d91100045f43865b2220008bd870cb644400147d0a196c8880028f61432d911021d5d406e3b222000aae82d47644400155b05a8ec8880028fa1721d91100051ec2e43b2220008be87087644401717b0e10ec88810eada0770d911000557410a1b222000aad82143644400117d0f906c8880022f61f20d91100051f42841b222000a3d8508364440018baeba9ec68800a37e1d43d8d100052f42887b1a2000a5d8510f634400159d0421ec688002b360843d8d100052f42865b1a2000a5d850cb634400153d08196c688002a761032d8d100054f424cbb1a2000a9d84997634400159d0532ec688002b360a65d8d100054fc22cbb1a2000a9c84597634400159f
  | 10 => 0xb1e200087f855ca63c40070f90ab94c78800e1fa1f7558f100043fc2ae8b1e200387c855d163c40011df04ba2c7880063b2097458f1000c7743ee4b1e2000c6f75dc963c40018d8ebb92c7880031bdd47258f10006363a8e4b1e20008df8758c63c40011df04bb4a7880063b2097694f100052ec1ecb29e20028be849d953c400117b093b2a7880063ba0a7654f1000476c14eca9e200087f855d953c40011df04bb2a7880063b2097654f100b43e43acaa9e2000c6c7259553c40070ff0ebaec58800e1fa1774d8b100043ec2ee9b1620168de83dd362c40011bb07ba6c58800a3be1d42d8b1044e373aa85b162002cae7450b62c40010fb0b3b2a58800237e0d7654b100b46e41aeca96200187e87d9552c40071dd0fb12a58800a2fa1276ccb100045ec24ed996200087f855db32c40070f90abb665880f69ba1762ccb1001c3f42cec996200087d859d932c400517d093b265880022f612764cb100043fc2aec996200387c855d932c40011df04bb265880121fa1f65547100046f438c698e20008df8758c31c40091dd0fb1243880026d61271cc3100046f43cc69862000cd5631c530c40011bb0fb1861880026d610714831000636b94a5b2c200487c87551658400517d0fba2c7080022fa1c7458e100164e3a486b1c20048dc8750d63840010ff0ab90c70800e1f2157218e100243fc3acb29c2000a5f83596538400117f08bb2a70800a2f2117654e1000477c12eca9c20018ec825d9538402d0fd0fb2aa7080031b1cb6554e1001c3f43eeab14200087f855d162840070f90aba2c50800237e0d7458a100b46e41ae8b1420048ec8750962841138d8eaa12c50800b2b1d14258a100043fc2aeca94200487c8759552840091d90eb12a5080022fe1176cca100145e422ed99420048ef8758b328407b4d90ab1665080021fe15764ca1001c3e42aec99420008bf845d9328400517908bb2650800237a1e634c6100046ec3ec618c2000ab7845db108400187ae92a6ca880029ba0a54d951000536c14a9b2a2000a758195365440050ff0eaa6ca8800297a0e64d95100052ec1cc9b2a2000a6e8299365440014db05326ca8800297e0d64d95100052e41ac9b2a2000a6f8259365440014d904b26ca880038d60464d95100051f424c5b2a2000a3d8498b65440014bd07316ca880029760e62d95100071a32483b2a2000e346450765440016e100a0eca880030f5d074d951000537410e9b2a2000a6d821d365440014ed023a6ca880029d60474d951000537416e7b2a2000a6d82dcf65440018bae639eca880021fa1c43d95100043ec3887b2a2000a6e8210f65440014db0421eca880021fa1f42d95100043ec3e85b2a200087e870cb65440010fb0e196ca880028fa1032d95100051ec2065b2a2000a6f825c765440014d904b8eca880021fa1f
  | 11 => 0x4802d1b906ba0c6900021fe157118d2001c3e42ae231a4000c6e529da53480014bb07b2ca6900021fe157654d200045fc22eca9a40028bc845d953480011df04bb2a6900023de057654d200047a40aeca9a40018ec821d9534802d0fd0fb2aa6900931b1cb6554d2002477436e4a9a403dc6c65dc953480258d8edb2aa4900065b21d535492000536432a6a924003c6c7654d52480011dd0db8aa4901375add4705492002477436eb992403dc6c655d7324809b4dd0db2e649006e3b61f63cc92000727b2ec799240048ef8758f324807b4d90ab1e6490002b920563cc92000726328c799240008ec865c732480012df0ab8e64900022fe1173d85200145e422e7b0a4000ad683d0761480010fd0fb2ac2900030f1d365585200043f438cab0a4000c3c74195614800187ecbba2c2900030f19774585200062fb2ee6b0a4000c5c65dcd61480018beca39ac2900031719473585200061f3a6ca30a4000c3e74194614800187ecaba0c2900030f19574185200047bc3ac230a4000ab48458461480015a906b08c29000a2fe1d74185200065a40ae830a400087f855cc61480070f90ab98c29000b2b9d1421852000573c0a8430a4000cb574d0461480015ad07a08c290002b960b411852000752a168230a40028be841da514800117b083b4a2900931b9cb659452000cb7c3aa528a4003a6c8654a51480018dca43b2a2900021fe1576cc52001c3e42aed98a400087f855da31480070f90abb4629000a2fa10768c5200045ec20ed18a4000c3e74d96314800187ecaba462900030f195748c5200064f3a6c718a4000c9e7418e31480018d8cab94629000e1fa17764c5200043ec2eec98a400387e859d931480010fb0b3b2629000e1f214764c52000c76410ec98a400087e86dd531480010fd0fb2a62900021f21f654c52012636396ca98a4000c6f65dc931480018d8cbb92629000e1f216760c5200043fc2aec18a400387c855d8314800117f08bb0629000a2f211760c5200043e432ea18a400087f87d9431480010fb0fb2862900063e219700c5200067830ae018a40048ec865d5214800139906baa42900123ba1a7348520004b6c28e690a400f8ee871852148001cceca30a42900931b1cb6554120024b643aa4a824004a6c8654950480096d100a92a0901361f21975cc1201243fc3ecb982400087d87d97304803f0f90cbac60900021fe1f658c1200943ec3ecb1824024c6e72d9630480018decab9460900031b195728c1200061e3a6ca9824000c3f65dd13048001878cbba26090003271d3634c1200064e3a0c69824000c6c65dc930480498dcedb2c40900939ad83658812001e373b0cb102400096d859ce20480012df0ab8c40900063b61c618812000672b88c3102400287f8755365c40018dee5292cb8800b279d243d8f100146fc3a87
  | 12 => 0x5a1fa1f6554e200b52f41ecaa9c4024c6c72d9553880010ff0ab9cc31000e1f21573986200247ac3c8330c400387e87dd561880018d843baac3100031bc8375586200043fc2ae8b0c400387c855d161880091e90ea0ac31000297a0f659462000636b2ee4a8c4016cce635cb318800517d09bb463100022f613768c6200043fc2aed18c400387c855da31880010ff0abb2631000e1f215764c6200062e3acc698c4000c5c7558d31880015a902b1a63100033398f724c6200056741ecb10c4000a6d8598e218801b1df0eb0c43100029be15618862007c77c32e110c4000d69755c2218800187ae92a6ca900029b60a54d95200143fc3aa9b2a40018ec825c765480014bf06b26ca900029720d64d95200053bc0ac9b2a4000a7481593654800169d07b96ca901371b9d942d95200071632285b2a4000c3d741d365480494dd043a6ca900029b60874d952000536c16e7b2a4000c5d731cf65480010fd0e21eca900021f61c43d95201253741087b2a4000a6d8210f65480014df04b8eca900929b20971d95200051f420e3b2a4000a3d841c765480014db0438eca900021fa1f41d95200043ec3e83b2a4000a5e83d0765480014bb07a0eca900929ba0b41d952000536c1683b2a400087e8710365480250fb0e206ca9000297a0c40d95200052ec1881b2a4024a6e8210365480014db04206ca900029da0440d95200053ac0881b2a400087f855d165480011bf06ba2ca9005a3720d74595200047bc0ae8b2a40008f4815d165480010fb0f320ca900029b60a64195200043fc3ac832a4000a5f8359065480014b906b20ca900029de0564195200053a40ac832a404da6e8219065480014d90ca10ca900038bd914219520007163228432a40048ed82dd3634800159b0421ec69000b2b1d142d8d200056641a85b1a4000e8f4350b63480070fd0b38ec6900021f61671d8d200145f424e331a40008bd849c663480010fd0fb2ac6900030f1d36558d200043f438cab1a4000c3c74195634800187ecbba2c6900030f1977458d200063bb2ee2b1a4000c7465dc563480018eeca38ac6900031d1947158d2001c3f43eeab1a40028be87dd1634800187eebba2c6900030f1d77458d200043fc2ae8b1a400387c855d163480011bf06ba2c6900023de057458d200047a40ae8b1a40008be871d1634800187eea3a2c6900030f1d47458d200064e3a6e6b1a4000c6c75dc963480051d90ea12c6902271b1d54258d20016563a284b1a4000c7775dc563480018e8ebb8ac6900032ddd37158d200065a3a6e2b1a4000c77751c563480018e8ea38ac6900032ddd07158d200065a3a0e2b1a4000cd7731c563480019cee438ac690003399087158d2000672a10e2b1a4000ce4321c5634809b8d8e4328c69000237e1d6318d200054e422c631a4000ad48158c63
  | 13 => 0x672390c298a6000cb864dc1314c001970c83826298003531d4724c5300056b436e298a6000e9764185314c001d28c830a6298002b5a1c614c5300066b438c298a6000e5685185314c001cab0a30a629800395dd4614c5300072a3a8c298a6000ec772185314c001d88e430a629800356dd4704c5300061e322ea18a6000c3e75d90314c00187aebb2062980022fe1176885300145e422ed10a600387e851da214c0010fb0a3b442980030f19175885300061f3aec910a6000c3d75d92214c001938c939c4298003271917388530006373aec510a60028be84dd9214c00117b09bb2429800e1fa1476485300043ec28ec90a601687f87596504c0494d904b2ca0980029d20565941300071da86c92826000c5f65dcd504c001878c8bae60980030f9d764cc1300061ebaec99826000c3c645d6304c00187cebb2460980030f5d7648c13000657396c91826000caf645ca304c001958c8b946098073279db648c1300046ec38c31826000cd571186304c0018dae5296ca180023be0971d943000c76412e3b28600487c87551650c0070fd0fbaac4180021fe15745883001c3e42ae8b1060048ec87509620c1138d8eaa12c41805ab320d42588300145f420e2b1060008bd841c5620c0010ff0abb2a4180121f21d65548300247643ac4a9060048f587906610c0010ff0aba2c21800e1f215745843000477c12e8b0860018ec825d1610c0018deebb92c2180031b1d7725843000637ba8e4b086000c6c751c9610c0091e90ea0ac218012bc20141584300053ac0ecb28860048f587986510c0074e90ab0ca2180023be09765443000c76412eca8860048f487585510c0010ff0abb4621800e1f215768c4300064f3a2ed1886000c5f855da310c0018b90abb46218003275d9748c43001c3f42eed108600087d85dda210c0091eb0f30c42180031d5d661884300063abaac31086001ae482586210c0010ff0abb2421800e1f21576484300b66639ac490860048f487585210c0011bf0eb0e6018003359c561cc03001c3f42eec980600087d85dd9300c001938e9bb2601800317a17764c0300062ec2eec9806000c9f76dd1300c0019a8e2b0a60180032e1d3764c0300063d42eec9806000c7985dd9300c001976edba2601805b17a1673d96200062f294e7b2c4000c5c529cf65880018b8a339ecb100033308673d96200262fa84e7b2c4004c5d509cf658800999e4139ecb100133348273d96200243e43aa8b2c40048dc835d6638802d8b906bacc7100031be097598e2000636412eb31c4000c6c215d663880018de40bacc710003175d75398e200145f424e331c40008bd849c663880091bd0fa9ac71000317dd75358e200246e43a86b1c400387e851c563880010fb0a38ac7100021fe157118e2001c3e42ae231c400487f8759653880014bf06b2ca710
  | 14 => 0xf82597644c00155904b2ec898002ade0565d91300055a40acbb22601ca9e86dcf644c00147d0a316c8980028f61462d913000557c12ebb226000aac825d7644c00187aea3aec8980028fa1773d91300051ec2ee7b226000aae82dcf644c00155b05b9ec89814eaea0373d91300051fc2ae5b226000a3c855cb644c00147d0a396c8980028f61472d91300045f43865b22601c8bd870cb644c00147d0a196c8980028f61432d91300051fc2ae3b226000a3c855c7644c00153f06b8ec898072a720d71d913000557c12e3b226000aac825c7644c00147d0a38ec8980028f61471d91302f54f418e3b226000a9d831c7644c00155d05a8ec898002ab60b51d91300051f42e43b226000a3d85c87644c00117d0e10ec8980022f61c21d91300051f42ee1b226000a3d85dc3644c0a753d07b86c898002aba0850d913000556c10a1b2260008be87c83644c00117b0f906c8980028fa1420d91300051ec2841b22600487f87596534c03f4bf06b2ca6981069b2096594d300053a40acb29a6000e1f53d92534c0018d8e5b2aa6980032b1cb6454d3000657b26e4a9a6000cac64dc9534c0018daeba96c49800a2fa1271d89300045ec24e3b12600087f855c7624c0070f90ab8ec4980022fa1f64589300061fbaec8b126000c3c75d91624c00117d0e322c4980030fdd464589300061e3a8c8b126000cb764dc5624c001968c9b8ac4980032dd9071589300065a320e2b126000ce4621c5624c00517d09bb2a4980022f613765493000c3e43acaa926001a6c82595524c0014e902b2aa4980032719373549300064e320e6a926000c3c64dd5324c00187eebb2264980030f1d7644c930006363aec4992600087f855cb614c0070f90ab96c298002b9a0b51d85300053b42e43b0a60028be86dd1614c00117d0fb22c2980030fdd764585300061e3aec8b0a6000cac72d91614c00117d0e322c2980030fdd464585300061e3a8c8b0a6000cac72191614c00195ec9b92c2980032b19372585300061f3aec830a6000c3d75d90614c00187cea320c2980030f5d464185300047bc3ac230a6000a7485584614c0015c904b08c2980031d205751853001c3f42ee830a600087d85dd0614c0015ab03218c2980031d5d7511853000573416a230a6000ad583144614c0014ed0b908c298002b560c21185300045fc22ed28a60028bc845da514c0018becab9ca29800a2fa1376545300045ec26eca8a6036a6c82595514c0014e902b2aa29800e1fa1676cc5300043ec2ced98a6000c9c649db314c0018bd0b3b662980031761676cc5300064f3b6c998a60008bc865d2314c00117b0fb2462980030f193754c5300061fbaec898a6000c3c75d91314c001958e5b2262980032bd93724c53000656326e498a6000c7475d85314c0019c8e5b0a62980031d1d4614c53000
  | 15 => 0xe21ac5180023b61c4358a300053742886b146000a6d8510d628c0014dd0bb8ac5180029b6177158a300053742ce2b146000a6d859c5628c00159f06b8ac518002aba107158a3000556c20e2b1460008ee87d45628c0011db0fa8ac5180023ba1f4158a3000476c3e82b146000a6e85d05628c0014db0ba0ac518002b3a0f4158a3000566c1e82b146004e6a50d41628c0090f90eb2aa5180123b21d6254a300043ec36ea9946041c6e62dd5328c0830fd0eb2a65182021f21d654ca3000637baac49946000c6c75589328c0019d2c5b8265180123d61e419863001c3f42ee4b0c600087d85dc9618c0091e90ea0ac3180029de0565946300243e42eeca8c6000c5d65dcd518c00199cc5b9aa31800317594735463000667310e6a8c6000c3e74596318c00187ccaba463180030f595748c63000657312e918c6000cae7458a318c00195ae8b1463180032d5d2618c6300065aba2c318c6000e4e6598a318c001caacab0c63180021f61b754c63000637316ea98c600087c87595318c0018d8e4b2a63180023b61b724c6300063732ee498c6000c6d65dc9318c0011d90eb1263180031bdd5624c630006363aac498c602c87f865d4318c0018dcc4ba8631807e1fe1d650c630006373aac418c6000c6d75588318c001caaca9886318003b1589310c6300062ebb4ea18c6000c5d765d4318c0018baed3286318003175d9650c63000666bb4c418c6000e4e65988318c00199aecb10631800e1fa1776886300043ec2eed10c600387e855da218c0010ff0cbac43180db1b98975886300043fc3acb10c600087d87596218c0018dceab1443180031b5d5628863002476416ec90c6000c5e65dcd218c0018bcca39a4318003331cd624863010c3fc32eb9846000c6e625d7308c03f0ff0eb2e61180031b9d562cc23000636baac59846000c5d769d7308c0018baecbae6118003359c561cc2300063cbb4cb9846000c7976597308c0019d2ed31661180033a5d962cc23000636b94a5b2a60008ef825c7654c0031d904b8eca980032b1c8645953000656326e4b2a6000cb464dc5654c0018e8ca38aca980032d19071595300145f43ee8b2a60008ef825d1654c0031d904ba2ca980023de0574595300047a40ae8b2a60008be871d1654c0050f90eaa2ca9800b0f1d1545953045636392a8b2a60018ee87dc9654c00195ee9b92ca980032b1d3725953000637ba8e4b2a6000caf741c9654c001958e8392ca980032ddd371595300065a3a6e2b2a6000ce772dc5654c0019c8e5b8aca980031ddd471595300065bba0e2b2a6000cb4741c5654c0019aee638aca9800339dc8715953000672390e2b2a6000c76851c5654c0018eea838aca980031d55071595300063a298e2b2a6000c77521c5654c0018e8a038aca980022f61e65d91300045fc3acbb226000aa
  | 16 => 0x5973000636392caa9e603dc6e65dc953cc0018dacbb92a79805a3b21d4258b3001c3f42ee2b16600087d85dc562cc0030f90eb2aa5980069b2096554b300062eb2ee6a96603b87d86dd532cc0010fd0eb2a65980861f21d654cb300b726192ca9966000c3e7499661cc02d8bce732cc3980030f9d165987300b72b98acb30e6000c3e655d261cc00187acaba4c39800b279d2439873001c3f42ee4b0e600087d85dc961cc00517d09bb4a3980022f613769473000c77416ed28e60008ed82dda51cc0018bacab9ca39805a1f21776547300061f3a2cb18e6000c3e655d231cc00187acaba463980c61f61b754c73010c3e43aca98e6000c6c7259531cc0018dccbb9263980031b597724c7300062fbb6ea98e6000c5f761d531cc0018beed32a639800317dd9654c73000667bb6e498e6000ccf761c931cc001a98ea392639800e1fa1776887300043ec2eed10e60028be84dda21cc00117b09bb4439800e1fa1576887300043fc32eb10e600087f8759621cc0010fb0eb2c43980031759773543300051f424c532c6000a3d8498a658c0090fd0f2a2cb180030fdd2545963000537414a8b2c6000a6d82951658c0090f90eaa2cb180063ba0b715963000476c16e2b2c6000a3e84989658c00147b09312cb180030fdd2745963000537414e8b2c6000a6d829d1658c00147f08b9acb180028f211735963000537c12e6b2c6000a6c825cd658c0014ef02b9acb180029d20573596300fc3f43886b2c600087d8710d658c0014dd0421acb180029b60843596300051f424e4b2c6000a3d849c9658c0010fd0fa12cb180021f61f42596300fc3f43864b2c600087d870c9658c00147d08192cb180028f610325963000537416e2b2c6000a6d82dc5658c0018eee338acb1800297e0d71596300043f43e82b2c600087d87d05658c0014bd07a0acb180029760f41596300053741682b2c6000a6d82d05658c0010fd0f90acb180021f61f21596300051f42042b2c6000a3d84085658c0094f50010acb180029e60021596300051f42640b2c6000a3d84c81658c0018d8e4b2aa7180023b61b7254e301ee3732ee4a9c6000c6d65dc9538c0018f2cbb82a7180038b9d26598a3000716ba4cb3146004e4f30996628c009c9a6132cc5180038b9d16598a3000716ba2cb3146000a6e85d09628c0014db0ba12c5180123b21d4258a30016563a284b14600387e85dc5628c0010fb0bb8ac51800a2fa107158a300045ec20e2b146000a6e859d1628c0014db0b3a2c518002b3e0d7458a300056641ae8b146000cad741d1628c0011dd0f2a2c5180023b61e5458a3000717aa4a8b146000a6f855cd628c0014d90ab9ac518002abe117358a3000556422e6b146000ae7815cd628c0015c902b9ac51800393d4e5358a301ec77c3aa6b1460848ec8754d628c03d1dd0
  | 17 => 0x8ca0018ec825d931940018beeb31a6328003331ca634c6500062fbaac698ca000ccc7258d31940015a902b1a63280031b9497688650004bdc02eb10ca000c6f7558921940011bf0eb18c6a8002b52056318d5000477c12e231aa0018ec825c4635403b0fb0fb1ca6a80769761f6394d500062ec3ec729aa00087c865ca53540010f90cb8ca6a80025be097194d5001477c3a85b12a00187c855c762540010fd0c39aa4a82021fa1f63549500043f436e2a92a0008bf845db325400517908bb664a80121fa1b75cc95001c3e428ec992a0008bf845cf615400517908b9ec2a80023de1d61185500056a41ac230aa0168de83dd061540011bb07ba0c2a80023be09731855000c76412e630aa00087d8794c61540dd0ff0ea90c2a80021fa1873545500043f43ec6a8aa000c5c73d8d51540010fd0db92a2a80db1b18b72545500843f438c2a8aa00487e86dd7315400517d083b462a80022f610768c5500062ebaec718aa0018ee829d931540011db053b262a800e1f214764c5500b43e42cec18aa0008bf845d8315400517908bb062a80023be09760c55000c76412ec18aa000c5d75d8c31540018eaebb0862a80022fe1176885500145e422ed10aa00387e851da215406d8d8c4bac42a800e5be1d528855000d36432a510aa00487c865d521540012b906baa42a800e1f61f63941500062f39ec7282a00387c865ca50540498d8c4b94a0a80025be09719415001c3ec38c3282a000c7571186505402d4bd07324cb9805a1fa1e54597300061fba4a8b2e6000a6e8295165cc0014db052a2cb9805a1f21d545973000c77416e2b2e60008ed82dc565cc02dc3c87322cb9800297e1943597300061fba4e8b2e6016a5e839d165cc0014bb073a2cb980029ba0a745973000536c14e8b2e6000a76819d165cc0014eb033a2cb9805a9720d725973000636b90e4b2e600087e87d0965cc0010fb0fa12cb9805a97a0c42597300052ec1884b2e6000a6e82dc565cc0014db05b8acb980028fa1271597300051ec24e2b2e6016a5e839c565cc0014dd0538acb980029b60a71597300043f43e82b2e600087d87d0565cc02d4bd07a0acb980029760f41597300053741682b2e6000a6d82d0565cc02d4bd0720acb980029760e41597300043f43e42b2e600087d87c8565cc00147d0810acb980028f61021597300b52f41842b2e6000a5d8308565cc00147f08b82cb980028f211705973000537c12e0b2e6000a6c825c165cc0014ef02b82cb980029d20570597300052fc1a80b2e6016a5c8350165cc0430fd0e202cb980021f61c40597300b52f41880b2e6000a5d8310165cc0014dd04202cb980029b60840597300053b40880b2e6000a758110165cc00147d09902cb980028f61320597300b52f41e40b2e6000a5d83c8165cc0430fd0e102cb980021f61c2
  | 18 => 0x840187ccbba2c1108030f59774582210145f43ee8b04420387e85dcd60884010fb0bb9ac11080b2b1d142582210043ec3cca3044200c3e7499460884010ff0eb28c1108030f9d165182210061f32ae83044200c3d655d060884018bccb398c1108031759673182210062f32ae63044200c5d655cc60884011f70eb00c11080a1fe1d54d95210062e328e6b2a42008df835d1654842d1b906ba2ca908023ee0174595210247c402e8b2a4200c5f751cd654842d8bd0a39aca908031794873595210062e290e6b2a4200c5c511cd65484019984239aca9080317d40735952100667900e6b2a4200ccc73dc965484018baeba9ec69080a37e1d43d8d210043fc2ae1b1a420387c855c363484070fd0fbaac6908021fe157458d2101c3e42ae8b1a42008ef825d163484011f700ba2c6908123e2017458d210062e3aee6b1a4200c6f75dc963484018d8ebb92c69080237e1d6318d210052e42ac631a42168dc835d4634842d8b906ba8c6908031be097518d2100636412ea31a4200c6c215d463484018de40ba8c690803175d75318d210045fc22e031a42028bc845c063484011df04bb4a6908029760f6594d210043fc2aeca9a42008df835d953484011df04bb2a69085a1f21d6554d210b52e41acaa9a4236c6c7259553484011dd0db92a6908061fe1d65945210052e41acb28a4200c6f65dc9514842d998c6b966290803171d7634c5210062e3a8c698a4200ccc63dc9314846d8dcecbac429080e3be1d65885210056641acb10a422f8ed8798e21484014db0a31c42908021fe1573d812101c3e42ae7b0242008fb8758060484018d842ba8c0908131bc81751812102636902ea30242018ed8788460484018daeb108c090802ba60221181210043ec3ca531ca0028be849c6639400117b0938cc7280123721d4358e500052ec2864b1ca000a9d840c96394001a98e531aa728003531c96354e50124b743ee4a9ca08bc6c761c953940010fb0c38aa7280761f61b7054e50006b5b96e0a9ca000d68721c153940010f90ea9ac5280929b2095358a500247643a84b14a000a6f855096294005958e8a12c52800a2fa107158a500045ec20e2b14a000c6d7558b32940012f301baa65280023be09739865000c76412e730ca0048f58790661940011df04ba2c3280063b20974586500043e43aa6b0ca000a6c8254d61940018d8a5b92c3280063ba1f72586500063742ee4b0ca000c6d85dc961940018dea7b92c3280031b54f72586500063628ee4b0ca000c6f50dc961940010fd0f292c3280031bdca52586500247a43a82b0ca00087f865ce51940010fb0f31ca328003175ce63946500043fc3ac528ca024c6e7258a519401d0ff0eb0ca3280029be0961946500843fc32e128ca0028be84dda319400117b09bb463280925ba0b758c65000477c12ec9
  | 19 => 0x30f59774580310164e3a486b006200ada80cc5600c4015b10098ac01880b2e1d240580310074d21c80b0062168f887501600c42d1bd07ba6cb108023760f74d96210052f41ec932c4200a5d83d9265884dd4dd04b24cb108029b608649962100537c328532c4200e2e6450a6588401c5ac8a14cb108021fa1e54596210061fba4a8b2c4200a6d8295165884050f90eaa2cb108021fa1f64596210052f41ec8b2c4200a5d83d9165884010fd0e322cb10802d320d725962137637bb284b2c4200e2e64509658840187ee93a2cb108da9ba0a745962100536c14e8b2c4200c5f739cd65884014df04b9acb108021fa1c43596210043ec3886b2c4236a6e8210d65884014db0421acb108a61fa1f41596210043ec3e82b2c4200a5e83d0565884014bb07a0acb108da9ba0b415962100536c1682b2c4200c7b709c1658840147f08b82cb108028f211705962100537c12e0b2c4236a6e821c165884014db04382cb108021fa1c40596210043ec3880b2c4200a5e8310165884014bb06202cb108da9ba08405962100536c1080b2c4200a768110165884014eb02202cb108030f9d265d8e210061f3a2cbb1c4200c3e655d3638840187acaba6c71080e1fe1d75d8e2101c3f42ee9b1c420087d85dd3638840117b0f3a6c7108030f9d674d8e210061ebace9b1c42028bf875d3638840187ceaba6c7108030f5d574d8e21006373aae5b1c42028ef8750b63885138dceaa16c71080b2b9d142d8e210065aba4e3b1c4200a9e84d8e638842d1b906ba4c7109bb1b1ca6558e210054f426e6b1c42008de87d0d638840159b0421ac71080b2b9d14258e210056641a84b1c4200e8f4350963884070fd0bb82c7108021f6177058e210043ec3cca31c420087f8759463884011bf0eb18c7108022fe117018e210145e422e031c4200c6e525da53884014bf06b2ca7108021f6167654e210145f424eca9c42008bd849d9538842d0f90eb2aa7108db1b1c96554e211ee3732ee4a9c4229c6f7659552884032d90ea9aa5108029be195354a2101e37bb2a6a9442368ed86dc552884ddaceebb8aa5108023b6187054a211ee3732aeb994426ea6f86597328847b4dd0bb1e65108039399663cca2119477c3ac79944200e4d6558f32884691df0cb8e65108025be1571cca2100476c34e1994420096d859c3328846d8dce4b2ca3108065be1d529462101d37c32a528c4200b678154a518840187ce8b2c63108030f995748c6210061eb2ae918c4200c9e7498e318840193ce8b1c63108031b995728c62118c3ec36ea98c420087e8759531884530f90eb2a63108db1b1c9654c6210063732ee498c4200c6d65dc931884dd0ff0cba863108021fe1d650c6211b43ec3aca18c4200e55654c4318840117f08b9cc11080a2f21173982210061e3a4cab044200c3c74595608
  | 20 => 0x36396cab02620087e87195604c401878e832ac0988031b1c865581310061fb2ee8b026200c3c65dd1604c4018decbb92c0988031b19772581310047743ec4b026200c6f75d89604c4018d8ebb12c0988032bdd36258131006563a6c4b0262008ee87189604c4018deea312c0988031b1d4625813100657ba0c4b026200cac74189604c4011f70eb00c098802ae21160181310043fc2ae4302620387c855c8604c4015b301188c09885a97a0e64994310b43f43ca8b286200c3f74951650c4014dd052a2ca188029b60a54594310b43e43aa8b286216e1e43991650c4014bf0ca1aca188030fdd274594310b52f41ce8b286200a5d839d1650c4014dd053a2ca188029b60a74594310053b40ce8b286200a75819d1650c42d4b906b92ca188031b5c872594310043f43e84b28620087d87d09650c42d4bd06212ca188029760c42594310051f424e2b286200a3d849c5650c4014dd0538aca188029b60a71594311643f43e82b28620087d87d05650c42d4bd07a0aca188029760f41594310053741682b286200a6d82d05650c42d4bd0720aca188029760e41594310071aa0882b28622c87e87c85650c4010fb0f90aca188028fa1021594310051ec2042b286216a5e83085650c4014bb0610aca188028fe1170594310051e422e0b286216a5c835c1650c4014df04b82ca188029b20970594310053a40ae0b286200a6e821c1650c4014db04382ca1880297e0d40594310b52e41a80b28620087e87101650c4010fb0e202ca1885a97a0c40594310052ec1880b286200a6e82101650c4014db04202ca188029da0440594310053ac0880b286200a3e84c81650c40147b09902ca1885a97a0f20594310052ec1e40b28620087e87081650c4010fb0e102ca188031b1c96554c311ee3732ee4a986200c6d65dc9530c42d1d90ea12c4188061f21d655483100d36412caa906200c5d65dcd520c4770fb0dbaa64188021fa1d654c8311643e43aca9906216e4c32595320c4018bacab9ca2188030f9d1658c4310b72b98acb1886200c3e655d2310c40187acaba462188b72d5d9748c43101c3e42eec988623187d86dd5310c4010fd0eb2a62188b21f21d654c43100636392ca9886200c6e65dc9310c4018dacbb92621880317e17764c4310062e42eec9886200c5f76dd5310c4018beec3aa621880317dda654c4310062fbb2ca9886200ccf76dc9310c40199eec3926218803531d4724c4310066bbb4a29886200cd776545310c4018ef0bbb262188031d217764c4310b66b29eec9886200c7776dd5310c4018eeec3aa6218802e5613734c4310066bbb2a69886200bc78254d310c4019ceedb92621880339dd8724c431005abc2a64988620087f855ca600c4070f90ab94c0188030f1d265580310b62e39ccab006200c3c74595600c40187ccbba2c0188
  | 21 => 0x805d1654c4031dd0fb92ca988031bdd7725953100637ba8e4b2a6200ccf731c9654c4010fb0f320ca988029760e641953100537414c832a6200a6d82990654c4014eb03320ca988021fe1d641953100537c12c832a6200a6c82590654c4014f700b20ca988029e20164195310051f420c432a6200a3d84188654c4634bb07b2ca6988031b1cb6554d3100477436e4a9a6200c6f65dc9534c47b8d8cbb92a6988031dd947154d310053742e85b126200a6d85d0b624c4051df0ea16c49880b2b9d142d89310045fc22e1b1262028bc845c3624c4014dd0b326c4988029b61664d893100537c2ac9b126200a6c85593624c4015d700b26c498802ba20164d89310056741ee9b126200acd83dd3624c40195ee93a6c4988029ba1474d893100536c28e9b1262008ee87953624c4011db0f2a6c4988038bd5254d89310053742ee7b126200a6d85dcf624c40155d09b9ec498802ab61373d893100727a9ca7b1262848ef8754f624c47b1d90ea9ec4988023ba1c43d893117c76c3887b126200a6e8510f624c4014db0a21ec4988029be1571d89310053642ae3b1262008ed87d47624c4011dd0fa0ec4988023b61f41d89310053742e83b126200a6d85d07624c40159d07a0ec498802b360f41d89310053742ee1b126200a6d85dc3624c4014dd0b386c4988029b61670d893100557c22e1b126200aac845c3624c40159b06386c4988023ba1c50d893100476c38a1b1262008ee87103624c4011db0e206c4988029ba1440d893100536c2881b126200ace83103624c40159b06206c498802b9a0440d893100572c0881b126200c6c62dd5624c4010fd0fb2ac4988021fa1c6558931006373b6ca3126200e2e74d94624c401c5ae9b28c4988023b61e65189310053742cca31262008ef87594624c4014dd0c328c4988031b9d86518931007173a0ca3126200e2d74194624c4011db0f320c4988029ba16641893100536c2cc83126200acd83990624c4015cb03320c4988023be1d641893100537c2ac83126200a6c85590624c4015d700b20c498802ba201641893100c3f43ecaa9262038ee87d89524c4010fd0dbaa64989071b18b754c9314043f43eca992624187c87d95324c4018deebb1264988031b1d7624c93100673b10e29926231a7581d96514c401ccea3b14a29880317d97735453100666316e6a8a6200c5f651cd514c401998c439aa2988030f9d3658c5310061fb2ae918a6200c3c655d2314c401958c4ba462988032b9d3628c53100656ba6c518a6200e4c6518a314c401caecbb0c6298802b660c40d813100578c0881b026200c6e72d96604c4018dce432cc0988031bd9572981310063632ae53026200c6e75d8a604c4018daebb14c0988031b9d4629813100636ba8c5302623187c86dd5604c4010fd0fb2ac0988030f1d36558131006
  | 22 => 0x382c9188028f614705923116d4f418e0b246200a9d831c1648c40155d04382c918802ab60870592310055b408e0b24622dab5811c1648c40155d04282c918802ab60850592310055b408a0b246200ab581141648c40117d0f902c9188022f61f20592310051f42840b246200a3d85081648c40156d02102c918802ad604205923120d37416cb29c6200e1f53592538c4018d8e4b2aa7188032b1c96454e3100657326e4a9c6200cad64dc9538c40196ac9b8aa7188032d5907154e310045ec3cc9b146200c3e75993628c40187aeb326c5188022fe1d64d8a310061f3aac9b146200c3d75593628c4018deeba92c51880a2fa137058a310045ec26e0b1462028be841d9528c40117b083b2a5188061fa1f6554a3100d37416caa946200c9e64dcd528c40193cc839aa5188030f993754ca310061fbaac89946200c3c75591328c4018d8eab1265188032d593714ca310065ab20e29946200e3751592518c4018bacab9ca31885a1fa1f65546311b537416caa8c6200c9e645db318c40193aecb2663188032d99176cc6310065abb2c998c620087f855ca608c4070f90ab94c1188030fdd664582310061e3acc8b046200c3f75591608c401878eab22c1188021fe15745823101c3e42ae8b046200ada80cc5608c40517f0cba0c1188022f61e64182310061f3acc83046200c3d75990608c40195ce5320c1188022fe1d64182310061f3aac83046200c3d75590608c40195ce4b20c1188032b991721823100656b22e430462008fb87580608c40187ae92a6ca988029ba0a54d953100536c14a9b2a620287f87553654c4014dd05326ca988029b60a64d953100537c12c9b2a6200a6c82593654c4014f700b26ca988029e20164d95310051f420c5b2a6200a3d8418b654c40187ae83a6ca988029ba0874d953100536c10e9b2a6200a3e84dcf654c40147b09b9eca988029ba0b73d953100536c16e7b2a620087e8710f654c4630fb0e21eca988029ba0843d953100536c1087b2a6200a3e841cb654c40147b08396ca988021fa1f42d95310043ec3e85b2a620087e870cb654c4630fb0e196ca988028fa1032d95310051ec2065b2a6200a6f825c7654c4014d904b8eca988021fa1f41d95310043ec3e83b2a6200a5e83d07654c4014bb07a0eca988029ba0b41d953100536c1683b2a620087e87c87654c4010fb0f90eca988028fa1021d95310051ec2043b2a6200a6e829c3654c4014db05386ca988029760c70d95310043f43881b2a620087d87103654c4014bd06206ca988029760c40d95310053741081b2a6200a6d82103654c4014ed02206ca988029d60440d95310051f42641b2a6200a3d84c83654c4010fd0e106ca988021f61c20d95310063632ee4b2a620087f855d1654c4011df04ba2ca988063b20974595310047dc02e8b2a62048f8
  | 23 => 0x94e510063bc32e329ca200d67825c65394401ac904b8ca7288021f61a7094e51004b6c14e129ca2028ec8750962944010fb0c39aa528a021f21d6354a5113c3ec36e2a94a20087d861c1529440517d093b665288022f61276cca51004bac0eeb994a20097581dd5329440117f08b9cc12880a2f21173982510046fc1ae8b04a2168dc835d160944031dd05b9ac1288023b60b73582510043f43ca6b04a24d87c8754960944011f70eb00c12880a37e1d43d8d510052ec2865b1aa200a9d840cb63544011bf0eb18c6a8802b32096318d510043ec3ca431aa2008bf845c0635440517908b80c6a8803531cb6354d51006a6390c6a9aa23696e87dc953545178deec392a6a8803591cb7154d5119c3f430e2a9aa20087e86dc153544010ff0ea9ec4a88da9b20953d895101477c3a85b12a200a6f8550b625440595ce8a16c4a88022fe1170d89510145e422e1b12a200ccc621cd62544018daebb1664a880e1f61c63945510062eb98c728aa20387d87d8a515446d8dce5b14a2a88023be0973d815100c76412e7b02a2008fb8758060544010ff0ea98c0a88029b209531815100636292e4302a200c6f855c860544018d90ab90c0a88031bd4d721815100636a9ae4302a200c6c515c860544098dea0b90c0a88131b54172181510043ec3ca4302a200c6d7294860544070fb0f288c0a88031b5ca51181510053cc04a2302a200c6d7294b65cc42d0f90eaa2cb9880e1fa1f7558b310043fc2ae8b16620387c855d162cc42d1d90ea12c598a271b1d54258b310b56641a84b1662028be84dc162cc40117b09b82c5988021fe157654b3100c3e43acaa9662168ec8758952cc40195ce5326cb188032b99172d963100c77416e9b2c62008ed82dd3658c40117b0f3a6cb1880a2fe1d74d96310143fc3aa9b2c6202c3e74553658c5158dce4aa6cb188032b9d272d963100656ba4e5b2c62018ef875cb658c40195ce8b96cb188032b5d172d96310065aba4e3b2c6200a6e82dd5658c4018dee5292cb188022fa1f655923100557416cab246200aad82d95648c40117d0e32ac9188b6a7e197359231005cc402e6b246200a3e85989648c40147b0b312c918802aba0b755923100556c16eab246200c3f759d5648c40147f0ab9ac9188028f215735923100557c12e6b246200aac825cd648c4eb56f02b9ac918802aee0173592310055c402e6b246200a3e85dc9648c40147b0bb92c9188028fa1672592310051ec2ce4b24622d8be870c9648c40117b0e192c9188028fa1432592310051ec2864b246200a3e859c5648c40147b0b38ac9189d6a7a0e715923100557416a2b246200aad82d45648c40147d0b90ac9188028f61721592310045f43842b2462008bd87085648c40147f0ab82c9188028f21570592310054fc1ae0b24625aa9c835c1648c40147d0a
  | 24 => 0xaa493a5f8558c635492559f04b18c6a905a3720d7418d520b66a18ae231aa484e4f6218d53548032dd0fb92a6a90ff1b1db7254d523743f430e2a9aa40196c821c5535489b0fd0db82a6a90065b20b7054d5200c3ec2ee9b0aa4038ed82dd361548010ff0ea9ec2a91ba9b20953d855248e3abaec330aa4008f78758461548011f70eb00c0a92429ee1560181520043fc3aa6302a44da6c8254c60548011bf06b88c0a905a3720d71181520b43e43aa8b2e6400a6f8255165cc80517f0eba4c3990021fe15709873201c3e42ae130e640387e87dd561cc8018d843baac3990031bc8375587320043fc2ae8b0e640387c855d161cc8018d842bacc1990131bc81759833202636902eb30664028be87dd160cc8070fd0a38ac1990021f61471583320061eba4a9b2a6400a6d82953654c8050ff0eaa6ca990029da0664d95320053ac0cc9b2a6480c6e7650b654c801c58c8a16ca99002d320d42d95320061eba0e9b2a6441a6e821d3654c8014db043a6ca990021fa1c43d95321dc3ec3887b2a6441a6e8210f654c8014db0421eca990029be0971d953220d36412e3b2a6400c75711c7654c8010fd0fa0eca990021f61f41d95320052f41e83b2a6400a5d83d07654c8834dd05a0eca990029b60b41d953220d37414e1b2a6400a6d829c3654c8018f2e0386ca990021fa1c40d95320043ec3881b2a6400a5e83103654c8014bb06206ca991069ba0840d953200536c1081b2a6400a7681103654c8014eb02206ca990021fe1574595320046fc1ae8b2a64008ef825d1654c91f8beebb9aca990021f61e641953200536c14c832a6400a7681990654c8014eb03320ca990021fe1d64195324752fc1ac832a6400a6f82590654c9014dd04320ca9922e9ba194219532005364328432a6400e2f64508654c80169906a10ca991071b1cb6554d321ee3632ee4a9a6480a6e86d97324c883c9ec7b2e649900a3de1d41d85320061f3a6cb30a6400c3e74196614c80187ecaba4c2990030f19574985320065aba6c330a640087e87d95614c8010fd0e32ac29923717dcc65585320047bc3ac230a6402cae74508614c8051eb0f208c299003a950941185320043fc2ae030a640387c855c0614c80117f08b80c29900a2f2117018532016573a285b02640387e859c7604c8010fb0b38ec09900a2fa1271d81320045ec24e3b02648cc5d73196604c8830f90dbaac0990021fa1f65581320061e3a6cab02640087e87195604c801878e832ac0990030fd9774581320061e32ee8b026400c7765dc5604c8018e8cbb8ac0990031dd9471581320063a328e2b0264008fb87580604c8010ff0ab88c09900e1f21571181320046fc3ac631ca23387f8758e53944674bf0eb1ca72880317e1d6394e510043fc32e529ca23587f865c653944012df04b8ca7288d65de1971
  | 25 => 0x40080000050004000027000001800c004002002c010000003003400e0000018000030001000000000c0040b47643a84b14a600a6f855096294c2d1bd07ba4c32980353d4f725865300477c12e8b0ca6018ec825d16194c018d8a5b92c3298063ba1f72586530063742ee4b0ca600c6d85dc96194c018dea7b92c3298031b147725865300637a86e4b0ca60087e879496194c018dee5292c32980353d4d729825300636292e5304a600c6f855ca6094c018d90ab94c1298031bd4d72982530063628ae5304a604c6f505ca6094c098daa0b94c1298021f61e529825300636b94a5304a6168dc835d16094c070f90cb94a6a99071b1897294d53004b7c12e329aa600c6c625c65354c012db05384a6a98031b18a7094d5300536c2e85b12a6028ef8750b6254c0595ce8a16c4a980a2fa1271d89530045ec24e3b12a6008bf845c36254c0517908b86c4a99071b9db75d89530057340cc9b12a600ae5819936254d158dcecaa6c4a99071b9da53d89531ef27b1ca7b12a600caf749d36254c7b4dd0a3a6c4a98029b61474d89530047743887b12a63f8ed8710f6254c7b4dd0a21ec4a98029b61443d895300557424e3b12a600aad849c76254c014df0ab8ec4a98fe9b21571d895300536c28e3b12a6008ee87d076254c011db0fa0ec4a98f69ba1741d895300536c2e83b12a600ace83d076254c0159b07a0ec4a98029b61770d89531fd3742ce1b12a600a6d859c36254c0155f08b86c4a9802ab21170d89530047743881b12a6008ed871036254c7b4dd0a206c4a98029b61440d89530056741881b12a600acd831036254c015cd02206c4a9802b960440d895300476c3cc8312a600a6d859906254c015cd03320c4a9802b9606641895300477c3ac8312a600a6f855906254d2f59f06b20c4a9a5a9ba14641895345d37432a8312a600a6c865506254c01c5ec8aa0c4a9a1393d8e53189530147bc3a83b0aa600cae74d8a6154c0195ae9b14c2a98032b9d0629855300656ba0c530aa600cb574d866154c011dd0fb12c2a98023ba1c62585534ae67b98c4b0aa66ec6e751886154c011ef0eb08c2a980e3760f741855301c3ec3ca630aa600a758194c6154c051eb0f208c2a98022fe1170185530145e422e030aa6008ef825c06154c031d904b80c2a980e3760f74d815301c3ec3ca7b02a600a7a8094f6054c0517d0938ec0a98022f61271d815300c77414e3b02a6008ed829c76054d2999ae6314c0a98fe3b21b72581530047743ec4b02a600caf74d896054c01958e9b12c0a98023ba1c625815300657ba0c4b02a600cac741896054c019cec5b8ac0a98033918b715815300673b10e2b02a600ce4621c56054c9b8d8ea310c0a98023ee1d601815300477c12e2302a6018ec825c46054c014bb0a21ec6a9002b360843d8d520046fc3ac631
  | 26 => 0x6000001000801203600000040000010050038008000000002801200200100000060000010000006000000802c0180070000000036005000001c000007000000001200f001000c010001001000c008005000800000000300180100280100078034002000000000000400c000000c016001000800400a00800c80000000000030000002008001800c00e0090160024004001000000c006001000000000e00b001802c04c00000080c80080000008000000018000801400c00100000000000170008010000005000004403a01700200000100000000014006001009000800000f0000000000007010000001c024003000004001500400180020080038000000001000800c006001006002400001400200000060010000018020005013002800c00100700240000040000004012013006008c002000002003401200201b003400e000001800000e002002800c006031006800002e003008000c01c001000000000000000480000080000078028000000003804000401b00200380020080060068022007000000400000400500000000020000030012007000805801c001001004c01a0030000000000003000005400c00c003008400600000000080040080058050002009002000400200700880040000110010014004000000000c00a00c000002c0140010040004000001003802000200000580e4008002000002400000b001000000800300000000360000000010000001001000000600e002803000a0030000000002003000000002000b000001c01a012000000400804300f8000008017000001c000015000000401800200c801c0040110048000000002000001c008021001001c046009016802c01e004000801000600b006800405000400c000c000014002000000000d0000010006036001001800200100000a801a008006000000000c009804c000000003801c008000000801805a00c0018024000003002001800c0010000044002000007006400400000c800000000300b000001e0300000004026003002002800e003002000c004005000800000200700000780020000010010030003004001000200300000040260020088000002005000000800a006001803000400c00480000040140010044032000001001002c0100000004002005001801c014000002000c024003000801800200000000100000060008034000002002000001400200280040000000000064000003000006400a00000180040040000020004054017002000c014001000000801801400380000320000040010004004000001000000800200100020000080000006015009002400400101980b000400000400880020070000004002006000006400000c01400040000020008004004011000001c0040030030000002003001803001c007004804c004001001800001a00f00
  | 27 => 0xbb03d1eb8a403b76d02e51ab05b56b190dcf4e0006e49aa562cd690ce8001c165406f1ab307e8a5b3552f219540034f4202c41ca2c6bc9cc45be90b536929497827733a35f844c000079b139b4a0005990d205bc18f2c99364fe872b2001ba000000013ab51103c17100006a458255656c2f285fa38957f80000000a900021e402019f70411280008951a1b1200040010008014003001801400000400000680120070000018002000009000402c01e000000c010001003000c0020010010028006000000800001c005000000c000013000000000a0010050024000004000002c00200100500b0000001000808c05e0010000004002003004003c0060000008028000001000801400c0070020020004000005800000000100100180080000030020006003000800c00c012001001000c011001000400000100000b0002000006000c00600000480000000020000000066003001005801c0000058008004001003802000e004000801400000100a000400a00b00500100020010018024004004022002400a00e004803c006000004000401c0000068000000029000800400e008000000800200f006804400a014000000403600c0010000010011003000801c00200d006c002002000002400000000180a80000010028028000006000000404c00200300080020060008014006004000802c01604000080040260010020004002000000000400200000280100040020098000070000002000000000900200040120090068020004016001000401800800580100040030080020002003007000000c005000000000c0010040014000018001000000c00400880240000030010014002013004800002c01900500080000020008000002002000006c00e0020000024006001000800000600500700000060020198020006003002800000000100080140000020038000002000002800c034000005800400e0000010034000000000001400200500d8000000007002800400200200080000040010010000010006002809000200400b8000000004002009003200c00f8008000003009001c000000001803000000a000001000400200e8014006000003805400a0030030008074000001007c0160010080014012000000000800000800080080040180010018022028000800c000007002000400c004000001801c007000003000000a000000003c001002801c000004000000000402600300240480000000000000003000000c00800000a800400401000200000220000008000000001004800404000000000080060000020040000006001800000000100380040140030018018000021001801400e001002802804c005007800c00000e0028000004004001806000000f0100048006001003000001000100080440000070000028018000001001800200000d00000
  | 28 => 0xe78000afa4ac17a40000005fc258503a2855f1279cad4d9c4819199a80a3d09eb43086298e2b622d915068a0000c5987cc5e6d6068591e1840000001c1841a000000000000035e000000070f00030e400063c0b00d7105cb0a1b38c752840005ad260c9bec655db9638976000000000044a4b268e8001370c6c6788438ca8d8f06192c507ad760002b740005a11e58034000abd4f0245c000b3a13db180efc9b21b180003c00000001fa000000000029d8c1076c33d2f840003e900018e80002900002e3c62400000017b858ca80000151d87ebbf3df800000025f1912c389a00001d229dcf8c7d84a000089ecac763c185c726a55686a5d09360000000000e646444bf800041ac9e4a8a53cb0c03352430980005883ae9ed034466048c07cce7ec524ab26d90322391eb0659a962142a931f0a16a6e5298129b9057b1499badb6208241032ad5680000b62c3060066525f32080003366e331692348e835701580003f22341a38d3e0000000000000000000384d29689c000265c35cd5400003bc3f44365199778ada6c22ec119d59418c57819797ec11c60a0e54edc89f5711210c04c2501a9a8154ccad589a8f8f0002805004c8fca4c5591318407692e6e10c14f6a7d02649c7ca7697e6c9a4102941ea04b8b900000005c40001a2800017e0001338b6700001811fa5e218ab2640004cb3a6103851c39a355aad80006a469a0000714000000146080a1e70000000000a7263f3405b2e0000c19094000c0e22d000148a1306ba26414fc8ed5cb15f84909330000dfc528b744a30bb94360001430000bd484314cb05cf843974d5b1dc932a0f10e0c10000d435a69318e028db5581fd5330c934730e650ccc896a29a5d36e19100d091d7f67bd00000006ec000037a11963ea8a271a3d8ae041865732ec02c08b432112d61604b0002da000064553f80006d26c62b885d8ad600004d000053a00000025640003060001c6800074e0000218000000000193d002ad26f79e740003316e8b3f147270c0002c140006f2000000141c72e5230f80612adf2c1196400043263415fc0009695b884a8906a6a2119399b2c994111a1496ccdad694ac4429a04d2d4a97c5fe29a5fc912555288000026949d800047880f51640251d6a21000000000031344e425e0c4ab40000e054570001694cc32300000718d851288001b824040002748d0e963000127843251c23c000130e5960cf31e58845d063a130d6b61345709ee44da330251b1299360a5185076dade6bf1dab2693e692661007f800065c00007dc000000000000000000c49c8000f5a00000008b4d329da19f9c294cea0b1418074000cbe672a4b00009c615c2a3c0002130003005bb490135bac709386b1045172d2041172f237b08d20d100000000000000001988000b6d2bea2c026c12e5ea9a08b282
  | 29 => 0x2780000000000153308956eb3c000115136852b5ebaa751be57442733f854ecd90000bd40003c5000318c0007021efa2754546f460f80012a65f157d9434d884c14490a0102200012e26988ec000101a1f98780000002d455cc5a417c00000002d70002c9000000039a088400043d000020c12ccde2d607552ae830000000000000060eab0481a000000000000000000000018428a400000019a46851a4a8600000001468000874b490002c000008c553a85a464c3ab090b7dd8aed2402a10d13468484140fc4000208000000130000011581b882ecd660780000000005678adc6520de5788fd8000000000266cc940000002a4586200000000000003c6154ad208d888500000000000003f080000000001fc80016723420000000000a40000284800002e0e525a000012206f8fbc424aab0002524b500006d12464000a3000034b090c0000000a44ed67cf06806f58a0721654357978a56952a22e4d4e3281668450ffc7104391860d8666e548072d3d4845402a3c8b80090143b6e400000000000000000004ff154167c0000000000abc1dc27411900c6dc06b800000003a24a90a884e6d0f0001894e807fa1ec33707068152159b50000d666422d653580005db00018a651f4132f993b054f5793065b3a1ef043a62ce38ce40a91641a109c115e2d4d2446ef2f1ade4000e100902f64d823cd28781a966c0b700037d8b34d0513ea0c4046453000370c5a00000001919b060000000ed17ee05c1c587d034e47918d157085271637c800000048964b038c00003e16480013723e45da013d7e000026700009940004bd268406e0002ff0000e9251753c83097625bb0001438ac600000005cc4864280002ba43e4db755c0000218d3a00000000008e90c11514ace0000001c1800000031f02640000000001ccdabad1a00020000000004918000546c556b917340002dd18197254100000002f943c28510003571136000005b0440009270002458cea93b3c98569bd67706141334ca600060d126800096b00282b97b48290001d08a4a5910000654000dde248a6f82160000000000000000264000021448c6cd182c0b4d3162e0a5c0c806b0ac00000000004ee80019420004a6800008a0000000e34000b820002180a6c8c6577a9c4a5c0471a831b4cf600000030d8dc090e00016e1318b4400000002a600000000000000b11762cfd59c0000001df4000d3b49280003da000669a0400cc0004259eec584000186906400002a0f8163cf085a73aa0ac09aab121e2171cbc064c00005d19b41e60001b8445263600005553d671b15a93d0c6e8161a79c542068495ed800133adc55a933b01729213378a213d80c85ee17c19709cd0002d59a445bf441abd12f290a5bfb3c80ec69c1fd27c56e003268aa2b4000c80499137551a6ec000000106c0f00000
  | 30 => 0x2a0000226468c23a29f990000000020d800000015c000174ce8a00000010b179615952b37897743510001e4400036c00037590ec0000002c6c158c561f680000000a35be813800000026d9880000108053a6ed1460f7354206800062b00000013880791ee221c000000000120460e50302f9ba80006700001d7806c5d14718000000b7c081029114a7410000001be08680a3918d09a6bd000000138e0002750d2d3920000000000adc0006640cf4e5000000034287c2000598aa9c2c2b73413a04857c50800020f8d1630214d96a80004a441e183c0c272d00000000004266c40dec0003d350021f0b604cf00031eca580275409b54da20001e18fd400000000000000005045ef8718abebb2048a359770000000134d2a80000002b7000000007700000000004160000000387000133057400005c000000000000000006de8561a5264800023c0002ce17000725c390c173c6cb1e100019ec74635a93c8dfc3b3000000000009f3b52eac38078e00005e1aa6ca50000000000c951462150000359416a3ad7ac0000001e214fa8582fc15d8000000677853c000c020000afc2461b40000501888cfb52100000007583358519a08000477b04000011d000201000060c00025c88667636092afd748000483800052a7b02b400000006c9328269121000058d175834a6d71a989e47943b04469be0df640c65c917d1c26100002ab55120000001c6077400034a0001c246cf5dd82f8000a62000000036eb400000001a9eddb0001ca40000cf16217c8c5a0b35900400000a4e43c11ed5d44ff000308c02600035f0f640320004550001528000000108400000004a25687dc23800000013dc00031513713220003ee00009d200000032205729b31d188f4dacdb3284800000076d00000000000003b29f04f3404942c9ac9ba802469c1dbc0000000fe8001a7c0806b62578ed200032100000000006f3ac0800007c0001a400080394750000000000000044d1aa0000000000f9a9a21008084a9aac0000000000050623f98ec3e295d0001d4843c000545a360000a703fd9e242d40e60000000376b4c1749a440002636162e2c742c0d1690e9cfe2757401ade054a6955123118000d1215599e426abde1d919f0c8200045da304fda0000000bd17200005540000b32000000244533e20242e0000000a863c1800196a000410b11c0000004558000e585da04aa9418d2ae500000016428132e0800000074b0000000000ced00004c5c003915760000000c2b6be8f41bd293a3690d5d2ca5ff5d8059001437c20883c550aacd4a29e58676d0021c8669b786b84d715087d800055c8ea128688800dab6c664ad71728001048df23ed8384c267c02b02ea0c3e96a15a014d4980dd24b9309a06ad66c0a20484e24c49690499d077137d047dc1ac750002e84484
  | 31 => 0xe9380c900988e22a14368540e4a52267b9524a0ad285471b88fee46f0ab0514a4e74f16d33190bca0d37b9221238a6633f23880000004d430ec5cca4459a83397a42ea4dd2d3cdb2bd020e377cb440006cf0dac0003db1c281613f41c861d1c4c7aa8f00eb3558ed045123f18a02520000218e6c5a66485021878000a7c4d880004e2ce10499ea8000c0927e083017e0003569cf49f253d0fa800003e3703772b9123eb074638f8d620d6a3a3800152e4921af1b3044800066201c0e4420500000019180004e62bdc0000000000d50000230000000000084c00000000000004bda3499c0000000181d7f8b8a61c32497fe47300000014d60000ab8c2d3f8d671c12e35be264d00011f0b9e00000000000000aa0000001ae631062a000145e9db32ea260e06a264b820e0db6000707adc8514d8d54133ccdfe86744f2ae882893130b105974a000082b55cef239c1f303691622b21c332dd79866750f832c7d4bfa429b2156d2cd00e7a4015fcc9013f9f98da02763a68bedbf62ae6ea9311708d186180d85808244586b3040000810cd926000091d5cc366cf94ae822c9ef8f64555000000000000020a800077a2f36038000000ab52c280009740001bd27a400000000006211d80000f700010f40006e9800186431b549aef909eaa40000b9d1442eb6e500015766323bd2ea8dda000000000174c6b30002cc0ac8de500017a00008976c88000a0058d00000000000000000c782bad4c0d80abd7eab6a2e5104c7ce00000031d8d1249d00000009ee63521f8001544a2769e836c9540002b3371c2fc5fa3f9281546c77726c0b00f3818e5418ffc4d80000661cf06fab1748a95dc3287d427112b440e8f7573800034cbc20002819b480000000000000b4e003358000000038f2fb4b56d6556d0efd53e5dd39235f02bc470637a9ecea22586c731c0282c5b3d1874d2eedff30d08f831ad372dc9bc5a9ca87528b5487c473b58aaed4f780740b28f053fe8554ea9d586c001c37e0300c9682f3799214cfa3370652bf10383d16ca0854f2400008c0054faca6803c0001456d7100000000bc00057980011c00415942e2593a9105841ad164c29f6a4845580c3721bcb3e837e0003fb2cb80000001aea55549213f2560000cb00000a8aee40000004c98001814a740000d1191c2cf11100000000000000000000e0705b1a8455aba20002fc45f4c3d000113d1669a700000008e8ccd024377000094a05a80019d4e025d4b19cae445803f070d7a679b22f37f57d26720000a243388c000012001c89624470981a8e0000002b2c18e0002a980001ec00001d34b8db09850001078c4ed872ab80001f87c56b702f4000000000170874c1874c516b4b6e3de32d35400004c06fc0b88a546693d31b99508c8d5b11754000000000000194c000406a728000529000
  | 32 => 0x966dd24e89b0041e000000000012400000002b45b000065880000000000000000000000086a5711c811e49fa22c0000003f5800188681811f923c00000049b0060eecbfd00003f4000d3640d9b74ac418600023d195e0eb028124c1fe2c81b980acf42406613b8100008d959a010158a84207d800000039f3d03828000cff0ed28d40001be3bc0001584c0b000000000000018998440000005b00000000b913720ff40000d3016000030a79849a0880f0a00068701a1830ac83f814440000001a70001632c082f293b800048b0ec34193eeb760001cd4f9875b00000003823210000000f329d0000113000000017180010660006e70000000a250ef328000000000000000008c80003484d248e736f80511bc92f0000000000de00000000e227ec6bf8424000000450a0e80008506e588d0efe0000288001aea000000000100cda613505252e600000000000006865ac2194fc40005f5aeb44804c727f1cbc666ca7371a34cfa2e113ba8a900004ed291b610fd400014b33442de1ec446123919aa3c37282c9558b6338e8d30e6e0b457025b4f9200012c800161e6a61700ea40008a02bc19cce7c7726228e958dc00068397cd630a2d00012b885c00000013bd6ee0002fcb14400053a0002f004f474400016f45ec6ac4eb96c8c4400000016f8000000103094c0000000001e1c000ad108880000000000000000a4200029c0968bcc8d0188b6f839a633448065c5b80001c080010ee0005d9b0ddbc29e5008800119cd77305035d3c42175cb80005aa2e8096b57cb3c3f719291483a29d35a280012280dc0001c80e726ba6432610840000000352827436551f8000458c2a25e8214780000000000103e1d24348d6086a000597875c8482b3062a24400000032f9f3800092a3cab3ac5940f2000998449a6a23efa971b568c95d6000000003067804583f02273e90f1c14459d52e8cbd78eabe2e636652e2c6225794c921e6573af9b357e84e71e7b630d8ac1c51d3308000b2a42db7d00001244be2cece4e2c504eb568b160001878001bba78600000000004f30000001baea641b4000000000000029e16ca652000000000095023ba3454187b706c19fc000d2608900015da00000000003d6b576a88000c7009e4e0285cbee4b9699abf4000000000140894e0000b309380004f81c709ad72a75c45f928800097800b8690d6c00002b801d9280003821ce0c4644d0002a849a21802502635be60735c2ac103745d42f083b5a642d117f16cd29c00003b98184625614caa105bb2d616323165412be813281081d2cca18fb660a480fe0b3b28800084400000013dabfe6e680000009f5000298000000000030b9028000685800000039800010bd74e32c62786e400046d195344c2209e125426580000005290b858e4d6d3e5a2a49681f92a899a02b
  | 33 => 0xf0bea45aa8751740000360000a4c00015ea2990800004498e10a50db83c82dac8061bc2f596bc5046bb49ab67d9603195aa186c302b6447e1561bcc0001e6358920cbc15cc9d9c366ce7204a1fc00080214590f85864463272b8c5b670b2ca8000fcecc700000000000000000000a9800000000001746640048d6d3ac00000027d8fae000526b8189c22cb2de317481e1c53f982eceb4981004362400000007391717e4c4b4048c7163a00069e36b8000c7f510aa79666a6c00032f01aaa2200000007e677b4361088e0a00045f07386ea20000019e0d1885a22b2850d0869666b8cac4c21e56968154de00000470f24aca03f0000000f4a51a08cadb00007a2472b4a926e4e50002cb40000000000b30da670809586655360000b40000a6e00058f000000057565180000000001bbb804640c580c51a345e0b6f386877cbbe0002bc95743d0da169280008100006882e70a181b6688af8000000000028a0000bae00031993400001b893f453c000134a2bd334144331b424c00cc009e000138a000000052c00093e652259c0003d245e068c9f49f00729a780000004ee076468e7664379c01432d1e57580003922165050000000a412fd8000ab600000018c06a40000e21e35af603425aa1eda72000373a6200000002cc0000a5a65b00004bc0001a86dd9f549b4d2000001300000000002a480000e25ceadec65c00000006ac000396525b60000000032aab0d882bc60fd9d844e88ee00000000006b90e812098be539000170dbc80001a2966c3f80001d600008ea00011db7e51585b619f0270e0ec24323907d6a079e6db0000b8c948304aaf110c28124380013fa0e0530951000053e00027e5c065ef1f298fc75ca070609e28a0e8ff12ea92800000067c0948000a316c5a609952bcf00000000008cb5ec000068000066e8cf0b144ab56319b07409284619028000b2b0312d5540614e0002f446468b743ea878942513616af74eaa5c40d024f03301aa6f6a3f88dc99951b94299e85f560d8de094c2b63ed16240fe1484118ce4000d860001681184bd41f5800000000000001ec76c0000000000e6023700000013c64506a11b700006666352cb18984b70000000820d23000000061027c1c40c9d3bcda76d537d505679f29a87882c457c00011110e259c3f489f84500000000df8000256131000000022f68fb554bb22456fd00005a8da3000111418c21865632ccf6c0000000f758182415f18000e6c3f819c00000004f13ec9a613542641f81a9400029c16c9391a2e4726b5963011ea11310b38cffabaf2e7251d2be51d1fdad1c0004f54652a54a7811a21500000000000002c8c970000000100400080f00029bc8700003b994783c60000002a6427c00040b800192200041f800046a8c43a520280b60004a0b399746443000225800026700
  | 34 => 0x258001af03fc0001df1a56bee02e960d5668620ff9fe554a6830a623e9a9a0003d20000f8e3172f602107ae7e0149279805aaf5000272d86a78260287300000005e712a52ecc9c34db2e8e28c160961ca87280f52cf91a8bfa38f1479f904341420bda7d0754889403b0012361f60bb8ef81acc8b1172d2c32626e10f9a3cc5cad91c01dd0000680435296488284712d849d12869d000202170c01e4e180008c498f5518bdda6a00000030cd8d65a32c0800000000059480012dc6774da9b694b45592a325d5bdc90d52b9bd488408c69807091b48d75570c907245fc298b49d55e08828910ecd948254b226b4b8ab46439b4582c60751870039702743137800000000000019c5b9e3740000000000b272a72854024000479800173e00000026bd33c25727580006cc7595f991acc380001082030000d1c00000006dcbe45c1b6a0880be700008cc4d0cbd4980000c0200036429a53787b80d624800000006bd2d785587c353d000080ed1b055a29c0007f800017d80000000188c040003c8318992414c90c42bae4d64a0004920000000a2048f000020c54347c04a000062400006bd5345dc5398000000dfc10880013b20000001d209c00001d8800005200000037a893edb503387a506436a66d9458b006ce09328e153800007c800000000043a081000000000018e53f695b0002e3800023654400009200002dd000000000030c80001d80b00540165b98cd80000ee40006156ff0000000d8a07400016b80440000000000cb454c026c00017d671086c7200005af8001b203354251f7983c40b61484e56f47b11afa90dac87815f601953e4daf0d698a4000a9666480019022f24a6337c23663428d915573489a26a0000b08c731e72ac979a9ce13827503c82492a5a374f74af66d9041c46460e0aa32d90be7ab3068000f90dd063d00012fa0000000000a600c96d821d437010159e9ea02feade514b7114680000b5800145c91252798500001b55dea41400041d15522e0c588cc0b821ac66855a1ea1504f5e48a704b56c000c492c3850c5da0006811440000cee63e8e74a90b5d16b00019a845d5099c380003410001c5cfdc00010580000006de31300000006f62010cb46c40006dd180dad022a38c8001476835092abe000027846a00016c20004efa98c75e00000000004a00c40002aa800035a49ea2d1788b922eb9694a5e9bf43726a48fa5195c61378778c342da1721682c403179ea46c82ce087a4249a44573ee80f092815b29a062ce122f90668365602726415273c4a81b237e828599616d47c91218e213741cb35496091352f25b192eac4643acdd9d2cf5017adf9b7e07d584b3f491abc31862720c7a02201c2b552de2b13ca0fa0af488a3e20000270dbd50109984aac2f42eae8111e4fb23291e9778861519376038e24646780001
  | 35 => 0x1bd0b143c780000003b80000db4878bc9000000000013b22d9e2c0000002aa1b1ccd4a5800016b9ab200000024ad82ab4325f935d312ad3280864000059718c327ca28db40001abc1f45ed34d3520000b6e00034fd3845923442bb8000d920000000000cf90000aa0b62a650000000ff8b9b33b0b1c9aca1c000187400068100003a80e220a4c300001e87d302925106aa17957ca6c000000047a8000d460000000d34cac8632a51ecd48ec135f7a208ec47973a8111da32cc56a32c19964c834f20000e24000099b6a5434b75391925554024a177a7bc2e4ac9104803c1a4ccc302087517a175411285889ca0151180000007e32169454000c8a3a9a84106e00000034bc15e4b60001e305e2b030ea1748208c980000000ca20003498000000000034a0d16842982b78ff8b4c3da66782355a8d953d61848cdacce4de86c48c2c034948350dd26b032194cd2cc0893f785f1a8217a2fa20ed97eab10369d801309f81ab1258628000000176d2c00461422370e741dd70736080007ff3028080ae60001278ce80003bb54602f11f60002f3a03800000000000010e016e00000000007641
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x2c4002aad1e880d80688e203805329065a8712100b9803098c00204401e0910001c0106e981897194d530041b660629c25354c0146990085759833245c9324c86508654c80106d9720953181510051a640515c8605451744c935c8725943145e1320c825d463484dd06f9761463885210051a640215d4604840106e97209535865045d1324d721c965cc00146592a14715953000519648501c5654c001c44751c8614c53045e1320c825d6638800106f97616638862000529650321c5634800106c96614734852026c1b259859ce2048001a50652014118d10006b018c8050462440010b598190714811000724591315c03104001cc1624c5700c410007051d5641cd10040014a497590724401000721590731c910040872b0985913044010
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x5
  | 3 => 0x6
  | 4 => 0x1
  | 5 => 0x4b
  | 6 => 0x4d
  | 7 => 0x4e
  | 8 => 0x124d
  | 9 => 0x138d
  | 10 => 0x94b
  | 11 => 0x94d
  | 12 => 0x94e
  | 13 => 0x124b
  | 14 => 0x124e
  | 15 => 0x138b
  | 16 => 0x138e
  | 17 => 0x98d
  | 18 => 0x98e
  | 19 => 0x128d
  | 20 => 0x128e
  | 21 => 0xcb
  | 22 => 0x4
  | 23 => 0xcd
  | 24 => 0xce
  | 25 => 0x12cd
  | 26 => 0x168d
  | 27 => 0x9cb
  | 28 => 0x9cd
  | 29 => 0x9ce
  | 30 => 0x12cb
  | 31 => 0x12ce
  | 32 => 0x168b
  | 33 => 0x168e
  | 34 => 0xa4b
  | 35 => 0xa4d
  | 36 => 0x134b
  | 37 => 0x134d
  | 38 => 0xb0d
  | 39 => 0xb0e
  | 40 => 0x140d
  | 41 => 0x140e
  | 42 => 0x24b
  | 43 => 0x24d
  | 44 => 0x24e
  | 45 => 0x144d
  | 46 => 0x16cd
  | 47 => 0xb4b
  | 48 => 0xb4d
  | 49 => 0xb4e
  | 50 => 0x144b
  | 51 => 0x144e
  | 52 => 0x16cb
  | 53 => 0x16ce
  | 54 => 0xbcb
  | 55 => 0xbcd
  | 56 => 0x14cb
  | 57 => 0x14cd
  | 58 => 0xccd
  | 59 => 0xcce
  | 60 => 0x170d
  | 61 => 0x170e
  | 62 => 0xd4d
  | 63 => 0xecb
  | 64 => 0xecd
  | 65 => 0x17cb
  | 66 => 0x17cd
  | 67 => 0x94055
  | 68 => 0x95395
  | 69 => 0x125395
  | 70 => 0x4955
  | 71 => 0x138055
  | 72 => 0x124955
  | 73 => 0x95255
  | 74 => 0x138955
  | 75 => 0x139255
  | 76 => 0x99295
  | 77 => 0x14b
  | 78 => 0x98b15
  | 79 => 0x99715
  | 80 => 0x98d55
  | 81 => 0x198b
  | 82 => 0x141295
  | 83 => 0x9c0d5
  | 84 => 0x1680d5
  | 85 => 0x252d5
  | 86 => 0xd455
  | 87 => 0x240d5
  | 88 => 0xb5695
  | 89 => 0x1452d5
  | 90 => 0x1440d5
  | 91 => 0x12c9d5
  | 92 => 0x9d2d5
  | 93 => 0x1689d5
  | 94 => 0x9d6d5
  | 95 => 0xb49d5
  | 96 => 0x9cb55
  | 97 => 0x16c9d5
  | 98 => 0x1692d5
  | 99 => 0x168b55
  | 100 => 0x1696d5
  | 101 => 0xa5355
  | 102 => 0xa4bd5
  | 103 => 0xa4d55
  | 104 => 0x150e
  | 105 => 0xa57d5
  | 106 => 0x14d355
  | 107 => 0xed355
  | 108 => 0x140b15
  | 109 => 0x2cb
  | 110 => 0x19cb
  | 111 => 0x141715
  | 112 => 0x140d55
  | 113 => 0xb4255
  | 114 => 0xb5455
  | 115 => 0x24b55
  | 116 => 0x144255
  | 117 => 0x1456d5
  | 118 => 0x256d5
  | 119 => 0x144b55
  | 120 => 0x16d455
  | 121 => 0x14cbd5
  | 122 => 0x154e
  | 123 => 0xecbd5
  | 124 => 0x14cd55
  | 125 => 0x20e
  | 126 => 0x14d7d5
  | 127 => 0xcd715
  | 128 => 0x5cb
  | 129 => 0x1a4b
  | 130 => 0x8e
  | 131 => 0xecd55
  | 132 => 0x3ce
  | 133 => 0x15ce
  | 134 => 0xed7d5
  | 135 => 0x5555
  | 136 => 0x5695
  | 137 => 0xd0e
  | 138 => 0x104b
  | 139 => 0x44c
  | 140 => 0x5c9d3
  | 141 => 0x5d453
  | 142 => 0x5d8d3
  | 143 => 0x1a57d3
  | 144 => 0x15353
  | 145 => 0x19cbd3
  | 146 => 0x3d716
  | 147 => 0x5d7d3
  | 148 => 0x3c9d6
  | 149 => 0x3d456
  | 150 => 0x1a8b
  | 151 => 0x3d8d6
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 2173
  | 6 => 7477
  | 5 => 3604
  | 4 => 29
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
  | 8 => packedAt gbK8 (1700+((h/20+packedAt gbK8 (1560+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (89089+((h/724+packedAt gbK7 (80401+(h % 724)*12) 12) % 2608)*13) 13
  | 6 => packedAt gbK6 (393784+((h/2492+packedAt gbK6 (358896+(h % 2492)*14) 14) % 14449)*14) 14
  | 5 => packedAt gbK5 (228249+((h/1201+packedAt gbK5 (212636+(h % 1201)*13) 13) % 4757)*13) 13
  | 4 => packedAt gbK4 (2084+((h/9+packedAt gbK4 (2030+(h % 9)*6) 6) % 35)*6) 6
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x7f80ffc03ffffffff01fffffd11f3f8c8ff1ff
  | 1 => 0xffff03ffc1e03e01ffe07fffeee4c8ff724e3f
  | 2 => 0x81fffc0001ffc001ffff87c030f8f0f3838fcc
  | 3 => 0x1fffffffe000001fffff8003f00ff03fc0ff0
  | 4 => 0x1fffffffffffffe000000003fff0003fff000
  | 5 => 0xfe00000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x12000c400228428c50088c52800913840490d5
  | 1 => 0xe48b019a40c23410a52052ad0664483932462a
  | 2 => 0x11d5b406117e90253b5d0701b0b8b0d3838b4c
  | 3 => 0x2166daecb4040049ce9660063b00ed02dc0db0
  | 4 => 0x41f8e33739973970030402083df60003eb6000
  | 5 => 0x78408038201821800c1844303fdffeec000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeac8eeaae888eeeaeac8eeaae888eeeaeac8eeaae888eeeaeac8eeaae888eeeaeac8eeaae888eeeaeac8eeaae888eeeaeac8eeaae888eeeaeac8eeaae888, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_16433
namespace PEqualNP.Outside.L_meta_16433
open PEqualNP.Outside.L_meta_16433.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 1 := bs0_4_0
theorem alls0 : ∀ k ≤ 4, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_4 i (by omega) hi
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
theorem bs2_3_0 : Interval s2Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 26 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_32 : Interval s2Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_64 : Interval s2Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_96 : Interval s2Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_128 : Interval s2Atlas 4 128 6 := block_range (n:=6) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 134 := (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 (concat bs2_4_96 bs2_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 48 := (concat bs2_5_0 bs2_5_32)
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
theorem bs3_3_0 : Interval s3Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 1 := bs3_3_0
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
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 4 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 25 := bs4_3_0
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
theorem bs4_4_160 : Interval s4Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_192 : Interval s4Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_224 : Interval s4Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_256 : Interval s4Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_288 : Interval s4Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_320 : Interval s4Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_352 : Interval s4Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_384 : Interval s4Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_416 : Interval s4Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_448 : Interval s4Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_480 : Interval s4Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_512 : Interval s4Atlas 4 512 27 := block_range (n:=27) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 539 := (concat (concat (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 bs4_4_96)) (concat (concat bs4_4_128 bs4_4_160) (concat bs4_4_192 bs4_4_224))) (concat (concat (concat bs4_4_256 bs4_4_288) (concat bs4_4_320 bs4_4_352)) (concat (concat bs4_4_384 bs4_4_416) (concat bs4_4_448 (concat bs4_4_480 bs4_4_512)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_64 : Interval s4Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_96 : Interval s4Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_128 : Interval s4Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_160 : Interval s4Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_192 : Interval s4Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_224 : Interval s4Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_256 : Interval s4Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_288 : Interval s4Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_320 : Interval s4Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_352 : Interval s4Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_384 : Interval s4Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_416 : Interval s4Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_448 : Interval s4Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_480 : Interval s4Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_512 : Interval s4Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_544 : Interval s4Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_576 : Interval s4Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_608 : Interval s4Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_640 : Interval s4Atlas 5 640 24 := block_range (n:=24) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 664 := (concat (concat (concat (concat bs4_5_0 bs4_5_32) (concat bs4_5_64 (concat bs4_5_96 bs4_5_128))) (concat (concat bs4_5_160 bs4_5_192) (concat bs4_5_224 (concat bs4_5_256 bs4_5_288)))) (concat (concat (concat bs4_5_320 bs4_5_352) (concat bs4_5_384 (concat bs4_5_416 bs4_5_448))) (concat (concat bs4_5_480 (concat bs4_5_512 bs4_5_544)) (concat bs4_5_576 (concat bs4_5_608 bs4_5_640)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_32 : Interval s4Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 40 := (concat bs4_6_0 bs4_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_7_0 : Interval s4Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_7 : Interval s4Atlas 7 0 1 := bs4_7_0
theorem alls4 : ∀ k ≤ 7, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
  · exact alls4_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 6 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 25 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_32 : Interval s5Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_64 : Interval s5Atlas 4 64 26 := block_range (n:=26) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 90 := (concat bs5_4_0 (concat bs5_4_32 bs5_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 44 := (concat bs5_5_0 bs5_5_32)
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
theorem bgb_4_0 : Interval gbAtlas 4 0 29 := block_range (n:=29) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 29 := bgb_4_0
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
theorem bgb_5_3584 : Interval gbAtlas 5 3584 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3604 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)) (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 bgb_5_416)))) (concat (concat (concat bgb_5_448 (concat bgb_5_480 bgb_5_512)) (concat (concat bgb_5_544 bgb_5_576) (concat bgb_5_608 bgb_5_640))) (concat (concat bgb_5_672 (concat bgb_5_704 bgb_5_736)) (concat (concat bgb_5_768 bgb_5_800) (concat bgb_5_832 bgb_5_864))))) (concat (concat (concat (concat bgb_5_896 (concat bgb_5_928 bgb_5_960)) (concat (concat bgb_5_992 bgb_5_1024) (concat bgb_5_1056 bgb_5_1088))) (concat (concat bgb_5_1120 (concat bgb_5_1152 bgb_5_1184)) (concat (concat bgb_5_1216 bgb_5_1248) (concat bgb_5_1280 bgb_5_1312)))) (concat (concat (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)) (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536))) (concat (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632)) (concat (concat bgb_5_1664 bgb_5_1696) (concat bgb_5_1728 bgb_5_1760)))))) (concat (concat (concat (concat (concat bgb_5_1792 (concat bgb_5_1824 bgb_5_1856)) (concat (concat bgb_5_1888 bgb_5_1920) (concat bgb_5_1952 bgb_5_1984))) (concat (concat bgb_5_2016 (concat bgb_5_2048 bgb_5_2080)) (concat (concat bgb_5_2112 bgb_5_2144) (concat bgb_5_2176 bgb_5_2208)))) (concat (concat (concat bgb_5_2240 (concat bgb_5_2272 bgb_5_2304)) (concat (concat bgb_5_2336 bgb_5_2368) (concat bgb_5_2400 bgb_5_2432))) (concat (concat bgb_5_2464 (concat bgb_5_2496 bgb_5_2528)) (concat (concat bgb_5_2560 bgb_5_2592) (concat bgb_5_2624 bgb_5_2656))))) (concat (concat (concat (concat bgb_5_2688 (concat bgb_5_2720 bgb_5_2752)) (concat (concat bgb_5_2784 bgb_5_2816) (concat bgb_5_2848 bgb_5_2880))) (concat (concat bgb_5_2912 (concat bgb_5_2944 bgb_5_2976)) (concat (concat bgb_5_3008 bgb_5_3040) (concat bgb_5_3072 bgb_5_3104)))) (concat (concat (concat bgb_5_3136 (concat bgb_5_3168 bgb_5_3200)) (concat (concat bgb_5_3232 bgb_5_3264) (concat bgb_5_3296 bgb_5_3328))) (concat (concat (concat bgb_5_3360 bgb_5_3392) (concat bgb_5_3424 bgb_5_3456)) (concat (concat bgb_5_3488 bgb_5_3520) (concat bgb_5_3552 bgb_5_3584)))))))
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
theorem bgb_6_7456 : Interval gbAtlas 6 7456 21 := block_range (n:=21) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 7477 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)) (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 bgb_6_416)))) (concat (concat (concat bgb_6_448 (concat bgb_6_480 bgb_6_512)) (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640))) (concat (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 bgb_6_768)) (concat (concat bgb_6_800 bgb_6_832) (concat bgb_6_864 bgb_6_896))))) (concat (concat (concat (concat bgb_6_928 (concat bgb_6_960 bgb_6_992)) (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 bgb_6_1120))) (concat (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216)) (concat (concat bgb_6_1248 bgb_6_1280) (concat bgb_6_1312 bgb_6_1344)))) (concat (concat (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440)) (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 bgb_6_1568))) (concat (concat (concat bgb_6_1600 bgb_6_1632) (concat bgb_6_1664 bgb_6_1696)) (concat (concat bgb_6_1728 bgb_6_1760) (concat bgb_6_1792 bgb_6_1824)))))) (concat (concat (concat (concat (concat bgb_6_1856 (concat bgb_6_1888 bgb_6_1920)) (concat (concat bgb_6_1952 bgb_6_1984) (concat bgb_6_2016 bgb_6_2048))) (concat (concat bgb_6_2080 (concat bgb_6_2112 bgb_6_2144)) (concat (concat bgb_6_2176 bgb_6_2208) (concat bgb_6_2240 bgb_6_2272)))) (concat (concat (concat bgb_6_2304 (concat bgb_6_2336 bgb_6_2368)) (concat (concat bgb_6_2400 bgb_6_2432) (concat bgb_6_2464 bgb_6_2496))) (concat (concat (concat bgb_6_2528 bgb_6_2560) (concat bgb_6_2592 bgb_6_2624)) (concat (concat bgb_6_2656 bgb_6_2688) (concat bgb_6_2720 bgb_6_2752))))) (concat (concat (concat (concat bgb_6_2784 (concat bgb_6_2816 bgb_6_2848)) (concat (concat bgb_6_2880 bgb_6_2912) (concat bgb_6_2944 bgb_6_2976))) (concat (concat (concat bgb_6_3008 bgb_6_3040) (concat bgb_6_3072 bgb_6_3104)) (concat (concat bgb_6_3136 bgb_6_3168) (concat bgb_6_3200 bgb_6_3232)))) (concat (concat (concat bgb_6_3264 (concat bgb_6_3296 bgb_6_3328)) (concat (concat bgb_6_3360 bgb_6_3392) (concat bgb_6_3424 bgb_6_3456))) (concat (concat (concat bgb_6_3488 bgb_6_3520) (concat bgb_6_3552 bgb_6_3584)) (concat (concat bgb_6_3616 bgb_6_3648) (concat bgb_6_3680 bgb_6_3712))))))) (concat (concat (concat (concat (concat (concat bgb_6_3744 (concat bgb_6_3776 bgb_6_3808)) (concat (concat bgb_6_3840 bgb_6_3872) (concat bgb_6_3904 bgb_6_3936))) (concat (concat bgb_6_3968 (concat bgb_6_4000 bgb_6_4032)) (concat (concat bgb_6_4064 bgb_6_4096) (concat bgb_6_4128 bgb_6_4160)))) (concat (concat (concat bgb_6_4192 (concat bgb_6_4224 bgb_6_4256)) (concat (concat bgb_6_4288 bgb_6_4320) (concat bgb_6_4352 bgb_6_4384))) (concat (concat (concat bgb_6_4416 bgb_6_4448) (concat bgb_6_4480 bgb_6_4512)) (concat (concat bgb_6_4544 bgb_6_4576) (concat bgb_6_4608 bgb_6_4640))))) (concat (concat (concat (concat bgb_6_4672 (concat bgb_6_4704 bgb_6_4736)) (concat (concat bgb_6_4768 bgb_6_4800) (concat bgb_6_4832 bgb_6_4864))) (concat (concat bgb_6_4896 (concat bgb_6_4928 bgb_6_4960)) (concat (concat bgb_6_4992 bgb_6_5024) (concat bgb_6_5056 bgb_6_5088)))) (concat (concat (concat bgb_6_5120 (concat bgb_6_5152 bgb_6_5184)) (concat (concat bgb_6_5216 bgb_6_5248) (concat bgb_6_5280 bgb_6_5312))) (concat (concat (concat bgb_6_5344 bgb_6_5376) (concat bgb_6_5408 bgb_6_5440)) (concat (concat bgb_6_5472 bgb_6_5504) (concat bgb_6_5536 bgb_6_5568)))))) (concat (concat (concat (concat (concat bgb_6_5600 (concat bgb_6_5632 bgb_6_5664)) (concat (concat bgb_6_5696 bgb_6_5728) (concat bgb_6_5760 bgb_6_5792))) (concat (concat bgb_6_5824 (concat bgb_6_5856 bgb_6_5888)) (concat (concat bgb_6_5920 bgb_6_5952) (concat bgb_6_5984 bgb_6_6016)))) (concat (concat (concat bgb_6_6048 (concat bgb_6_6080 bgb_6_6112)) (concat (concat bgb_6_6144 bgb_6_6176) (concat bgb_6_6208 bgb_6_6240))) (concat (concat (concat bgb_6_6272 bgb_6_6304) (concat bgb_6_6336 bgb_6_6368)) (concat (concat bgb_6_6400 bgb_6_6432) (concat bgb_6_6464 bgb_6_6496))))) (concat (concat (concat (concat bgb_6_6528 (concat bgb_6_6560 bgb_6_6592)) (concat (concat bgb_6_6624 bgb_6_6656) (concat bgb_6_6688 bgb_6_6720))) (concat (concat (concat bgb_6_6752 bgb_6_6784) (concat bgb_6_6816 bgb_6_6848)) (concat (concat bgb_6_6880 bgb_6_6912) (concat bgb_6_6944 bgb_6_6976)))) (concat (concat (concat bgb_6_7008 (concat bgb_6_7040 bgb_6_7072)) (concat (concat bgb_6_7104 bgb_6_7136) (concat bgb_6_7168 bgb_6_7200))) (concat (concat (concat bgb_6_7232 bgb_6_7264) (concat bgb_6_7296 bgb_6_7328)) (concat (concat bgb_6_7360 bgb_6_7392) (concat bgb_6_7424 bgb_6_7456))))))))
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
theorem bgb_7_1984 : Interval gbAtlas 7 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2016 : Interval gbAtlas 7 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2048 : Interval gbAtlas 7 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2080 : Interval gbAtlas 7 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2112 : Interval gbAtlas 7 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2144 : Interval gbAtlas 7 2144 29 := block_range (n:=29) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2173 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 (concat bgb_7_480 bgb_7_512))))) (concat (concat (concat (concat bgb_7_544 bgb_7_576) (concat bgb_7_608 bgb_7_640)) (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 bgb_7_768))) (concat (concat (concat bgb_7_800 bgb_7_832) (concat bgb_7_864 bgb_7_896)) (concat (concat bgb_7_928 bgb_7_960) (concat bgb_7_992 (concat bgb_7_1024 bgb_7_1056)))))) (concat (concat (concat (concat (concat bgb_7_1088 bgb_7_1120) (concat bgb_7_1152 bgb_7_1184)) (concat (concat bgb_7_1216 bgb_7_1248) (concat bgb_7_1280 bgb_7_1312))) (concat (concat (concat bgb_7_1344 bgb_7_1376) (concat bgb_7_1408 bgb_7_1440)) (concat (concat bgb_7_1472 bgb_7_1504) (concat bgb_7_1536 (concat bgb_7_1568 bgb_7_1600))))) (concat (concat (concat (concat bgb_7_1632 bgb_7_1664) (concat bgb_7_1696 bgb_7_1728)) (concat (concat bgb_7_1760 bgb_7_1792) (concat bgb_7_1824 bgb_7_1856))) (concat (concat (concat bgb_7_1888 bgb_7_1920) (concat bgb_7_1952 bgb_7_1984)) (concat (concat bgb_7_2016 bgb_7_2048) (concat bgb_7_2080 (concat bgb_7_2112 bgb_7_2144)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 60 := (concat bgb_8_0 bgb_8_32)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 5 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 34, 38),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeac8eeaae888eeeaeac8eeaae888eeeaeac8eeaae888eeeaeac8eeaae888eeeaeac8eeaae888eeeaeac8eeaae888eeeaeac8eeaae888eeeaeac8eeaae888
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372936 * 2 ^ 32 + 4004178056) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_16433.Model.Repr at out
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

def mono : List Gate := [⟨.and,[2,3]⟩,⟨.and,[3,5]⟩,⟨.or,[4,6]⟩,⟨.and,[3,8]⟩,⟨.or,[7,8]⟩,⟨.and,[0,10]⟩,⟨.or,[1,11]⟩,⟨.and,[2,5]⟩,⟨.or,[0,9]⟩,⟨.or,[13,14]⟩,⟨.and,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372936 * 2 ^ 32 + 4004178056) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372936 * 2 ^ 32 + 4004178056) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_16433

open PEqualNP.Outside.L_meta_16433 in
theorem PEqualNP.Outside.L_meta_16433 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372936 * 2 ^ 32 + 4004178056) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372936 * 2 ^ 32 + 4004178056) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
