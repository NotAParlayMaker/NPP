import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_12951.Model
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


end PEqualNP.Outside.L_meta_12951.Model

namespace PEqualNP.Outside.L_meta_12951
open PEqualNP.Outside.L_meta_12951.Model
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

end PEqualNP.Outside.L_meta_12951

namespace PEqualNP.Outside.L_meta_12951
open PEqualNP.Outside.L_meta_12951.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x841fe41083fa82107f10420ff98841fe31083fa62107f0c420ff90841fe21083dc42107f48420fe10841ec21082fca0107fd0020ff20041fd40083f880107fcc020ff18041fd30083f860107fc8020f790041fe20083f440107f48020f690041f920083fea9885fd5310ff2a6217e54c43faa9885f55310fe2a6217c54c43fea7885fd4f10ff29e217e53c43faa7885f54f10fe29e217c53c43fe87887f90f10fea1e21fc43c43fea5885fd4b10ff296217e52c43faa5885f54b10fe296217c52c43fe85887f90b10fea1621fc42c43fe65887f8cb10fe99621fc32c43fe83887f90710fea0e21fc41c43fe63887f8c710fe98e21fc31c43fe43887f88710fe90e21fc21c43fe81887f90310fea0621fc40c43fe61887f8c310fe98621fc30c43fe41887f88310fe90621fc20c43fea9085fd5210ff2a4217e54843faa9085f55210fe2a4217c54843fea7085fd4e10ff29c217e53843faa7085f54e10fe29c217c53843fe87087f90e10fea1c21fc43843fea5085fd4a10ff294217e52843faa5085f54a10fe294217c52843fe85087f90a10fea1421fc42843fe65087f8ca10fe99421fc32842faa3087fd0610fba0c21fe41843fa83087f10610fa20c21ff31843fc63087f4c610fe18c21ff21843fc43087f48610fe10c217e50843fe81087f90210fea0421fc40843fe61087f8c210fe98421fc30843fe41087f88210fe90421fc20843fe21087dc4210fd88421ff54442fea8886fd51109faa221fe54442fca8887f55110beaa221fc54442f8a8886f151109e2a221ff53442fea68877d4d10afa9a21fe53442fca6887f54d10bea9a21fc53442f8a6887714d10ae29a21ff43443fc86887f50d10fe21a21ff52442fea4887bd4910b7a9221fe52442fca4887f54910bea9221fc52442f8a4887b14910b629221ff42443fc84887f50910fe21221ff32443fc64887f4c910fe19221ff41443fc82887f50510fe20a21ff31443fc62887f4c510fe18a21ff21443fc42887f48510fe10a21ff40443fc80887f50110fe20221ff30443fc60887f4c110fe18221ff20443fc40887f48110fe10221ff10443f620887f84110fb08221ff54042fea8087f95010bf2a021fd54042faa8087f15010be2a021ff53042fea6087f94c10bf29821fd53042faa6087f14c10be29821ff43043fc86087f50c10fe21821ff52042fea4087f94810bf29021fd52042faa4087f14810be29021ff42043fc84087f50810fe21021ff32043fc64087f4c810fe190217e51043fe82087dd0410ff20821fd41043f882087d10410ff98821fe31043fa62087f0c410ff90821fe21043fa42087f08410bf28021ff40043fc80087f50010fe20021ff30043fc60087f4c010fe18021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0xf414c3fc82987f50530fe20a61ff314c3fc62987f4c530fe18a61ff214c3fc42987f48530fe10a61ff404c3fc80987f50130fe20261ff304c3f660987f8c130ef18261ff540c2fea8187f95030bf2a061fd540c2faa8187f15030be2a0617e530c3fe861877d0c30ff21861fd430c3f886187710c30ffa9061fe520c2fca4187f54830bea9061fc520c3fe84187f90830fea1061fc420c3fe641877cc830ff19061fd320c3ba64187f0c830ffa8861fe510c2fca2187f54430bea8861fc510c3fe82187f90430fea0861fc410c3fe62187f8c430ef18861fd310c3f86218770c430ff90861fe210c3fa42187f08430bf28061ff400c3fc80187f50030fe20061ff300c3be60187f8c030fd18061fd300c3ba60187e4c030ffaa6417f54c83fca9905f95320feaa6417d54c83f8a9905f15320ffa9e417f53c83fca7905f94f20ef29e415e53c83faa7905f54f20eea9e415d53c83f8a7905f14f20ffa1e41fe43c83fa87907f10f20ffa1641fe42c83fa85907f10b20ff99641fe32c83fa65907f0cb20ffa8e41fe51c82fca3907f54720bea8e41fc51c83fe83907f90720fea0e41fc41c83fe63907f8c720fe98e41fc31c83fe43907f88720fe90e41fc21c83fe81907f90320fea0641fc40c83fe61907f8c320fe98641fc30c83fea9105fd5220ff2a4417e54883faa9105f55220fe2a4417c54883fea7105fd4e20ff29c417e53883faa7105f54e20fe29c417c53883fe87107f90e20fea1c41fc43882faa5107fd0a20f7a1441fe42883fa85107f10a20f621441ff32883fc65107b8ca20fe99441ed32883f865107fd4620ff28c417e51883faa3105f54620fe28c41ff41883fc83107f50620fe20c41ff31883fc63107f4c620fe18c41ff21883fc43107b88620fe90c41fc21883d843105f94220ffa0441fe40883fa81107f10220ff98441fe30883fa61107f0c220ff90441ef20883f641107fd5120bfaa241fe54482fca8907f55120beaa241fc54482f8a8907fd4d20bfa9a41fe53482fca6907f54d20bea9a41fc53482f8a6907fd0d20ff21a41fd43483f886907fd0920ff21241fd42483f884907fcc920ff19241fd32483f864907fd4520bfa8a41fe51483faa2907f14520be28a41ff41483fc82907f50520fe20a41ff31483fc62907f4c520fe18a41ff21483fc42907f48520fe10a41ff40483fc80907f50120fe20241ff30483fc60907f4c120fe18241ff20483f640907f88120f710241ff54082fea8107f95020bf2a041fd54082faa8107f15020be2a041ff53082fea6107f94c20bf29841fd53082faa6107f14c20be29841ff43083fc86107f50c20fe218417e52083fe84107bd0820ff21041fd42083f884107b10820ff99041fe32083dc64107f4c820f699041fc32083fea2107f94420bf28841fd51082faa2107f14420ffa0
  | 2 => 0x2faa9207fd4e40ff29c817e53903faa7205f54e40fe29c81ff43903fc87207f50e40fe21c81ff52903fca5205f94a40fea94817d52903f8a5207fd0a40ff21481fd42903f885207fcca40ff19481fd32903f865207fd4640ff28c817e51903faa3205f54640fe28c81ff41903fc83206f90640fea0c81fc419037883207fcc640ff18c81fd31903f863207fc8640ff10c81fd21903f843205f94240ffa0481bf40903f681207fd4d40bfa9a81df53502bea6a07f94d40fea9a81fc53502f8a6a07714d40ae29a81ff43503fc86a07f50d40fe21a81ff52502fea4a07bd4940b7a9281fe52503faa4a07f14940be29281ec52502d8a4a07fd0940ff21281fd42503f884a07fcc940ff19281fd32503f864a07fd4540bfa8a81f751502eea2a07f94540fea8a81fc51502f8a2a07d14540ba28a81ff41503fc82a07f50540fe20a81ff31503fc62a07f4c540fe18a81ff21503fc42a07f48540fe10a81ff40503f680a07f90140df202817e54103fea6207f94c40bf29881fd53102faa6207f14c40ffa1881fe43103fa86207f10c40ffa9081fe52102fca4207f54840bea9081fc52103fe84207f90840fea1081fc42103fe64207f8c840fe99081fc32103fea2207f94440bf28881fd51102faa2207f14440ffa0881fe411037c82207f50440fe20881bc41103fe62207f8c440fe98881fc31103fe42207f88440fe90881fc21102fca0207fd0040dfa0081fe40103f480207f50040dea0081f940103fea9985fd5330ff2a6617e54cc3faa9985f55330fe2a6617c54cc3fe87987f90f30fea1e61fc43cc3fea5987f94b30bf29661ee52cc2dca5987f54b30bea9661ed52cc2daa5987f14b30ffa1661fe42cc3fa85987f10b30ff99661fe32cc3fa65987f0cb30ffa8e61fe51cc2fca3987f54730bea8e61fc51cc3fe83987f90730fea0e61fc41cc3fe63987f8c730fe98e61fc31cc3fe43987f88730fe90e61fc21cc3fe81987f90330fea0661fc40cc3fea9185fd5230ff2a4617e548c3faa9185f55230fe2a4617c548c2faa7187fd0e30efa1c61fe438c3fa87187f10e30ee21c61ff528c3fca5185f94a30fea94617d528c3f8a5187fd0a30ff21461fd428c3f885187fcca30ef99461fe328c3fa6518774ca30fe19461ff518c3fca3185f94630fea8c617d518c3f8a3187fd0630ff20c61fd418c3f883187fcc630ff18c61de318c3fa63187f0c630ee18c61ff218c3fc43187f48630fe10c617e508c3fe81187f90230fea0461fc408c3fe611877cc230fd98461ff544c2fea8987f95130bf2a261fd544c2faa8987f15130be2a261ff434c3fc86987f50d30fe21a61ff524c2fea4987f94930fea9261fc524c2f8a4987fd0930ff21261fd424c3f884987fcc930ff19261fd324c3f864987fd4530bfa8a61fe514c3faa2987f14530be28a61f
  | 3 => 0x6498ff8c931fe99263dd324c7f86498ffd0531ff20a63fd414c7f88298ffcc531fb98a63fe314c7bc6298ffd4131bfa8263fe504c7faa098ff14131be28263ff540c6fea818ff95031bf2a063fd540c6faa818ff15031be2a0637e530c7fe8618ff90c31fea1863fc430c7fea418ff94831bf29063ee520c6dca418ff54831bea9063ed520c6daa418ff14831ffa1063fe420c7fa8418ff10831ff99063fe320c7fa6418ff0c831bf28863ff410c7fc8218ff50431fe20863ff310c7be6218ff8c431fb18863fd310c7ba6218fd4c431ffa8063fe500c6fca018ff54031bea8063fc500c7fea990dfd5321ff2a6437e54c87faa990df55321fe2a6437c54c87fea790dfd4f21ff29e437e53c87faa790df54f21fe29e437c53c87fe8790ff90f21fea1e43fc43c87fe8590ff90b21fea1643fc42c87fe6590ff8cb21f719643fd32c87da6590ff0cb21ffa0e43fe41c87fa8390ff10721ff98e43fe31c87fa6390ff0c721ffa8643fe50c86fca190ff54321bea8643fc50c87fea910dfd5221ff2a4437e54887faa910df55221fe2a4437c54887fea710dfd4e21ff29c437e53887faa710df54e21fe29c437c53887fe8710ff90e21fea1c43fc43886faa510ffd0a21ff21443fd42887f88510ffcca21ff19443fd32887f86510df94621ffa0c43fe41887fa8310ff10621ff98c43fe31887fa6310ff0c621ff90c43ef21887ee4310ffd4221ff284437e50887faa110df54221fe28443ff54486fea890ff95121bf2a243fd54486faa890ff15121be2a243ff53486fea690ff94d21bf29a43fd53486faa690ff14d21be29a43ff43487fc8690ff50d21fe21a43ff42487fc8490ff50921fe21243ff32487fc6490fb8c921fe99243ed32487f86490ffd0521ff20a43fd41487f88290ffcc521ff18a43fd31487f86290ffc8521fb90a43fe21487dc4290ffd4121bfa8243fe50487faa090ff14121be28243ff54086fea810ff95021bf2a043fd54086faa810ff15021be2a043ff53086fea610ff94c21bf29843de53086bca610ff54c21bea9843dd53086baa610ff14c21be29843ff43087fc8610ff50c21fe218437e52087fe8410ff90821fea1043fc42087fe6410ff8c821fe99043fc32086fca210ffd0421ff20843fd41087f88210ffcc421ff18843fd31087f86210ffc8421f790843fe21087ec4210ff48421f690843f521087fea010ff94021bf28043fd50086faa010ff14021ffa9e81fe53d02fca7a07f54f40bea9e81fc53d03fe87a07f90f40fea1e81fc43d03fea5a07f94b40bf29681fd52d02faa5a07f14b40ffa1681fe42d03fa85a07f10b40ff99681fe32d03fa65a07f0cb40ffa8e81fe51d02fca3a07f54740bea8e81fc51d03fe83a07f90740fea0e81fc41d03fe63a07f8c740fe98e81fc31d03fe43a07f88740fe90e81fc21d
  | 4 => 0x7750d32fe21a65ff424cbfc84997b90932fea1265ed424cbf884997fcc932f799265fe324cbbc64997fd4532bfa8a65fe514cbfaa2997f14532be28a65ff504cafea0997f94132fea8265fc504caf8a0997fd5032bfaa065fe540cafca8197f55032beaa065fc540caf8a8195f94c32ffa1865fe430cbfa86197f10c32bf29065ff420cbfc84197f50832fe21065ff320cbbe64197f8c832f719065fd320cbba64197b4c832e699065ff510cbfca2195f94432fea88657d510cbf8a2197fd4032ff280657e500cbfaa0195f54032fe28065ff53d07fca7a0df94f41fea9e837d53d07f8a7a0ffd0f41ff21e83fd43d07f887a0ffd4b41ff296837e52d07faa5a0df54b41fe29683ff42d07fc85a0ff50b41fe21683ff32d07fc65a0ff4cb41fe19683ff50d07fca1a0df94341fea86837d50d07f8a1a0df55241ffa9c83fe53906fca720ff54e41bea9c83fc53907fe8720ff90e41fea1c83fc43907fea520ff94a41bf29483fd52906faa520ff14a41ffa1483fe42907fa8520ff10a41ff99483fe32907fa6520ff0ca41bf28c83ff419077e8320fdd0641ffa8483fe50906fca120ff54241bea8483fc50907fea6a0dfd4d41ff29a83fd53507f8a6a0df14d41ffa1a83fe43507fa86a0ff10d41ffa92837f52507fca4a0ff54941fe292837c52507fe84a0ff90941fea1283fc42507fe64a0ff8c941fe99283fc32507fe82a0fdd0541ff20a83be41507fea0a0dfd4141ff28283fd50507f8a0a0df14141bf2a083ff53107fca620df94c41fea98837d53107f8a620ffd0c41ff21883fd43107f88620ffd4841ff290837e52107faa420df54841fe29083ff42107fc8420ff50841fe21083ff32107fc6420ff4c841fe190837e51107fe8220efd0441ff20883f641107fa8220ef50441faa0883b541107fea020ff94041bf28083fd50106faa020ff14041ffaa6637f54cc7fca998df95331feaa6637d54cc7f8a998df15331ffa1e63fe43cc7fa8798ff10f31ffa9663fe52cc6fca598ff54b31bea9663fc52cc7fe8598ff90b31fea1663fc42cc7fe6598f7ccb31ff19663fd32cc7ba6598ff0cb31ffa0e63fe41cc7fa8398ff10731ffa8663fe50cc6fca198ff54331bea8663fc50cc7fea918dfd5231ff2a4637e548c7faa918df55231fe2a4637c548c6faa718ffd0e31ff21c63fd438c7f88718ffd4a31ff294637e528c7faa518df54a31fe29463ff428c7fc8518ff50a31fe21463ff328c7fc6518ff4ca31fe194637e518c7fe8318ff90631fea0c63fc418c7fe6318f7cc631fb98c63ff508c7fca118df94231fea84637d508c7f8a118ffd5131bfaa263fe544c6fca898ff55131beaa263fc544c6f8a898ffd0d31ff21a63fd434c7f88698ffd4931bfa9263fe524c7faa498ff14931be29263ff424c7fc8498ff50931fe21263ff324c7be
  | 5 => 0x2c00c00c00002800800406400400000004402800400c00000000c00800401403c04401001000000000000c00800000c00000000000c00000800403000400001003001403c01c02800401c003fea5a1ff94b43bf29687fd52d0efaa5a1ff14b43ffa8e87fe51d0efca3a1ff54743bea8e87fc51d0ffea1a1ff94343bf28687fd50d0efaa1a1ff14343beaa4877e5390ffe8721efd0e43efa1c87ff5290ffca521df94a43fea94877d5290ff8a521ffd4643ff28c877e5190ffaa321df54643fe28c87ff5090ffca121df94243fea84877d5090ff8a121ffd0d43efa1a87fe4350f7c86a1ffd4943bfa9287fe5250ffaa4a1ff14943be29287ff5150efea2a1ff94543fea8a87fc5150ef8a2a1ffd4143bfa8287fe5050ffaa0a1ff14143be282877e5410efca621ffd0c43dfa1887fe4310fbc8621ff50c43dea1887dd4310ffea421ff94843bf29087ee5210edca421ff54843bea9087ed5210edaa421ff14843ffa8887fe5110efca221ff54443bea8887fc5110ffea021ff94043bf28087fd5010efaa021ff14043ffa9e85fe53d0afca7a17f54f42bea9e85fc53d0bfe87a17f90f42fea1e85fc43d0bfea3a17f94742bf28e85fd51d0afaa3a17f14742ffa8685fe50d0afca1a17f54342bea8685fc50d0afaa9217fd4e42ff29c857e5390bfaa7215f54e42fe29c85ff4390bfc87217f50e42fe21c857e5290bfe85216fd0a42f7a1485ff5190bfca3215f94642fea8c857d5190bf8a3217fd4242ff284857e5090bfaa1215f54242fe28485ff5350afea6a17f94d42fea9a85fc5350af8a6a17fd0d42ff21a85fd4350bf886a17fd0942f7a1285fe4250b7c84a17fd4542bfa8a85fe5150bfaa2a17f14542be28a85ff5050afea0a17f94142fea8285fc5050af8a0a15f95042ffa9885fe5310afca6217794c42af29885fd5310afaa6217754c42aea9885fc5310bfe86217f90c42fea1885fc4310afca4217fd0842dfa1085fe4210bdc84217f50842dea1085ed4210bfea2217f94442bf28885fd5110afaa2217f14442ffa8085fe5010afca0217f54042bea8085fc5010bfea9995fd5332ff2a6657e54ccbfaa9995f55332fe2a6657c54ccbfe87997f90f32ef21e65fd43ccbba87997f10f32ffa1665fe42ccbfa85997f10b32ffa8e65fe51ccafca3997f54732bea8e65fc51ccbfea1997f94332bf28665fd50ccafaa1997f14332ffaa4657f548cbfca9195f95232feaa4657d548cbf8a9195f15232bea9c65ff438cbfc87197f50e32fe21c657e528cbfe85197f90a32f721465fd428cbda85197f10a32ff99465df328cbde65197fd4632ff28c657e518cbfaa3195f54632fe28c65ff508cbfca1195f94232fea84657d508cbf8a1197fd5132bfaa265fe544cafca8997f55132beaa265fc544caf8a8997fd0d32ff21a65de434cbfa8699
  | 6 => 0x284000000000100b1fa3380004d88129f94100000008e19f24d80011a262a788000b786e80000033f181af888a99994bb320d20530e012e95b2458a63210182a280da9d001a9388329d8ce97823aa2d3010d5ae58000003538001379f500010621db69000000000052b11a64027800333336a2f8001c0365a4f1240003343489359b30002710001e40be9c28002aeae08f9b7d0deab60002e1a320001552171ed81b2ac0001d62e10ac80000000019c0001911b78f71d72fe0002d70001b621baa680022087c000000400800000401400000800c01801c00001c01c00800002800c00c01009400c00000008801006400002000000400001c00002c00000400c03c01c01c00807400000c00000000800402806402400002001400c02403414c01000005800002805003400803800401802804c00401000803001c00800002005802800400805801800800008c02008809404c00000c01001409000801c00800800400801400400000002400800402800814c00400400400001003c00003400001008802002c02804402c00004002409000800c01000401800001402004008000000405c00c01401c01c05c07007000c07400400000006404c00000001800803400400409400400008000000000c00801000c00800000000801000000c00c00000001c03001400800404000400000000400c00000400000800008000800402800001401402802000000000c00000004001005c00000001804002000c01000401c00c00404c00400002000401800000000c01406801800400000809c03c06001002001000004c00000008400000c00000003401c01801800000400400800004c00003c00402402804810c00000400c00001802c00c00800800c00800800000800001000000002400001800001803005801801400000002401403c04400400803803401c01c00400400800400000000401800806401000402001402801801004000802802800000800c00801402400800000001c00000800000000c00000003000401800000000800001800c02400c00000403004005400401800400804802800c00802001400800000400400802402400004801008802400403c02c03000800000009402400400000008c01400405804401c00000400801000800000400c00000001801800400001000803800000802403801001800800c00000002002000c00402400000002c00404400000400800800003400802000800800800000400800c00401400400804400000001800c01000401802c00000003401801c04401000000005800002402000803000802c00002400000000000400002408400000000400002c01c02c0340000240100f800400802400001800401000000000000c00404c00000c03801c00c0140480000100500c00500840400040000480000100080000
  | 7 => 0x5900000004380000018f3201fe00030402aa84960281267a8526f1de96cb652d2aeda5600008b29401a23baa42bc155aa595606c29c1068000022dfad92d6a6d2e29741cd8e6330a1f0001368000e886334608622810b84a1031cea43b2280010717e86aa0700004726fa8b8f030a0001ec1a7a8000f851b3c80008f8000b58001650001c690d8002f80002613501f313f0700a4a0300000025e3089e580001698d8661c11621b89cb2f22038609830149531890c52adb7f18b0e3a6a3742442228f88ef031a6dab690d0b613faf280000000020f0000000002ddb679f88ad00012b2de0000000de1870001da89900e16a9b92211cb9ea11b0000ec8da98680000031396134211d0220002b10001be2a38010af00000037f92a8000003290000aa138156a781bbad313889b0001d900004e1df8770582f713215ea06b409fd26b02bab4a4d25d00031b86390f9c5b811a82908001d5000213a76323af7a5d84f94981d8002a09100000000002bba0b2bb003a9800000028930e0002368000002dbb2f800003066afa90780003718d19897d9248cf9f68000000c60000001a700010e1ae800084044119891951a0930faeeab22ce90e8ad8000d987134c0d78a718087d0000000000c48000fa12c8002c83468a10001a180028d80016db4a00037d8cc0002e30478f58000db9b128635692b90b1bb22b0288000002e002100000017100000017316683100000029200000028b08b8001210a5b619352693521d4aeaa86b81a87000231b6982a2fb8ae22a0150000000000002150003561792afaaa012aa106e0640000f30b330d20c0f480023b24cb558e185608db0b89792920d8002400003540e4a1b3289eaac00769f4318aa81e811e0b2886a81b1d200adeb0f2978001c89be92188f227a143132fc8000000a500036f2b293d01c8c58fa86f95a0003710002e805680028d04c80025a31c91e8000000002df0000002223140000821719c80001432960002b0366a9c80025f00019b8000002a98001af00a80000013e8f233e80004e98537799cb6a23fb1f2e701200014f1e03788d30b814c0fda6627400024e34db5900025800031daae36b164152370b588fea42064b7513990400002facf01f0b480025e8f9007a33317958acc8001659e7acfb10b771ca2c89f92ca00030ab183281a21e0a5f8e200011500000019f9eb29596b1b403db4a8e0a2980000000017b000000226a48b220000300000d624a0bd2620960270001928e784815921d0b391f00000003eb688000001e69aa3671010753480db28e80004d0000dc0000000001268001d28291c91c32ee23629eaa70000000000000849ab14e11c8b136c8a393194426587da00112096989ad88000000002949dd13089280008c00007586cb729bc94e8ffa9a93a2cc2b09bfa931941bc14aadd
  | 8 => 0xd68000000bc9821ac87e31233a128a68b8098eaf6b1480015f2479d89ad8353240000d0859832948a4800020d000000000175a989ff8bc1b218ca02000000000085aa480000030c1f82fa04f1a2a5930211600001d2bc8000002b50b89d216d0451d1a79a04997ad81f98b99f4b3d3580000002f00000002901b18c0b579811038000a080009d25028c1491762f48f2aaaa3507a80597f1840ea240b37a5101780000000007804893297480027e140b512601401980000890002413248c302c0d292f9880eb8000bf8b4000164aeb90c00000000000000036222e00000035c00025785f15d982800223a4b35b8002b98320061d83631c98a7922b0e8002010000298dcb700001f0b1280034d18a8d18ac1b380032700009a8e72d228a218b34a0833bb1600011300ba8ab1c0001bf0921f18002e61298002b180000034300000000007199d8000000000000cdb0680009c0002d78000001c08001e22251bd15a9b2a8c87796fa0e80b037a619a480000000009e1138b08553680000000002d535308eb2f10800036db73800112a7c8158409e12dc06f36289983a3608001159af80035fb1ea830000000002d0296b6110a05f94ca648f10c283ab6e2c799d271b3da7a800267190062b278000000000000000000001258ab3721d427bb5d0003168e59371261f58188f3a4aa880229cfa0500005b16300012f317277ac4888af0a029a3ada80d20a8002f52e20df0f185aa4635c800145321a2d9280000002f10000908ba8002ca80034507ea1fa0883582f2b7a63b02abda7db749639950ea9e39599889d02be300ad104928f96e21781414498615400000c0000000000040001c18001848000c880000036d00000000000017a8001738000001051e980016719ab20a5699480024c0093153251fba650000f50001e283d1918958542fd8620b1aa8b2eb598001111ee00004980000032c2c590200000007492528e00020194704680011bb2d00000000013925b9c70002c40e90000a820a00003389e97b83309895bab70dfa0ba3d000376221b7c0a3349947a2300000027c11199a04c270800000000000260ae412d8808382f1b07185ae89c48001de0a9b44951108b31196b3c09db0c8fc0dd8000000000d48001459c237c8412ce24e9310da22c1090000000500000000001462452889048b72b8079078a7b0198ae80015c05135180003b12e1ce02e00021631a9a103c9cc995a770e98002858dd0000000249eba2c942b0b0b006a1b69b49cf3199f02ea2c9aec1ef0000000000002130ee80009827d291a632181271220000a6800193000350b5e32a96617532989a0ee24bac61a61bdb5d8600948a2826b09340216979b26160836000036800023b3e01026b9019fa37a8000801db0738000912e49abb7180027680001b8d93030203038003158
  | 9 => 0x2cd8bd80000000000000000000016f00000032d80000000019e0001a028980000036c1339a087b2af0000cf0000003642e99d325c034268114a328c208180002d9c6008b4b01fad5ad0a3035f3388001c410c8000000d809517882600013c1169ba1572ef18e0003600002f321c07403f8000000610839170001b080028200037980000014680982b000219aff2d380009f0002398000000c680023a2e90001098c92da0000941f288a2c28e6ac31a8a0c89019628287992a23f2f98000732bab3b299211a10a52b3006b800255382a27183800aa20001f78000fd0f0a571330cb0422efa201a68d51fc0000873439a40000118fe000070a7500022f00007ca9b000057843127b269769628cc8001548002d18c811d9fb27280006829b9420002128001dbab38001b70001e72ba32b8002370fbb7e30180000000017c8c1802b2cb1003b8002ac8002190000619a50001cd00033628f19200038203900005880019b26ca52190972821aad123a49a470002c680a3050000be0f817c0f7b458002d4b6a85e0002cb0002c38000bb8000002380000000000000000571d3a28aa18000000001698a18000c425a80006520798a16a37b8ff2d99d10ce110afe87f00036e8001fda5401c0110002241b9a3eb4400000000000033a8e817031a14da5480005c1002721b82cbaf923c13d8c78a8a9e26ab5e8689202b325b0000000ef99e9678d38fb04597e3192bf212204341ac18002db0400b21fc83c08518f855b05920b4700692d29292315caa90108c99182f3824349177255970a46a35b4c9720f41618208d00bb29f29707b8080e33079303781438d41c79c39b522b918b2305e98797d1191f3830b2e34f1e60173571d09528af8000002598a22c700000025193b069193865a910001c52e38000001b597a1da04b23e0000cb80007f867215aed36f84aaa60000c3a69a95000034a348000001140000000000ec31e3528002110a026c105aa009707613404493b93489cab8b7a0002392100002f41df15e0002c51a9a41800000000102800253a9980010f21e91f9aaa30a3100000000000000000000000008789f8000000000b926e85d0000002c200020580014a21cb5b07a26e000280800000375b5a8002f580001e0003413082e7aa521a21a98b8000000d7141b4f80013a99900eb09a7e8000000ca00005caab34b85a22592c0698aba09825b000f62ff8ba18c0fcb4782500037e94d06781ea429539d98c109b9b014b1e4a87a3435a22aabf80000024327a17780f2e69681f72bd1ca96e9e18b516c00000000027f90aa3d80504600000000000000000000021e0000ca8002a7800000000214b42a7380000000033831b0aab062588e2a731e506b2b92fd0c00070d108825080020f8ed0e105d8a911c0000000e42061dc8000002f600005203980
  | 10 => 0x8c9ad0002b580023780000016b86d028089ac08000828002c91ed0139690cd0001ae0000130000001fe9e88000002eca791f102d13c800376a83a758002dc854b329a583f00029a1dd9a303e2b41e93392a308d1f230db25b4eafb041a5ca38b6600032a22eb7b0000bf02cae517fa70229042b373319481ff13e00000005b8eda4f81606d9fa800000157b2b000000093a7f0e52ababeb730539ac224b04a530eb36399736b8728f6b7904b81ab39b3f8c71d580c9d795fb35ad63339dc27495811aa26244a3c9ee8d89801d6a66ad40000190931689178508231a90388b680000014f9ef9cc0003802eb0001e31ec8722fc0003350000000a400035500000020e311000364b4e24915d1f600495002eb549ba9509360002cd2c1000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x5320427d654c8109f195320435e534c810d754d320436e524c810db54932042f7614c810bd18532042fb604c810be181320427f650c8109f994320427d650c8109f19432043cd320c8109f992510427d64944109f98e510427d63944109f98a510427d62944109f59741042f565d0410dd597410437754d0410dd55341042f560d04109fd96410427d6590410cf952410433d5490410bd98641042fa6090410be582410427f65504109fd94410427d6510410cf950410433d5410410ed50441042fa6010410be580410437565104109d59441042f66410410ed99041043775410410ed95041043755410410ed55041043355410410fc98041042f56010410fc58041042f160104109f597310427f658c4109f596310435e538c410d754e31042fa608c410be582310427f654c4109fd94310427d650c410d794c310435d530c410bb98831042ed620c410be98031042f9600c4109f597210427f65884109f596210436e5288410db54a21042fa6088410be582210427f65484109fd94210427d6508410b798c21042dd6308410db948210436d5208410be98021042f960084109f992500427d64940109f98e500427d63940109f98a500427d62940109f58650043774194010dd106500427d65d00109fd96400427d6590010cf952400433d5490010bd98640042f56190010ed106400427f6550010b7d8d40042dc6350010bbd8940042ec6250010bdd8540042f461500109fd94400427e65100109f594400427c6510010cf950400433d5410010bd98440042f56110010ed104400427d65cc010bb98b30042ed62cc0109fd96300427d658c010d794e300435d538c010bd98630042f5618c0109fd95300427f650c0109f994300427d650c0109f194300435e530c010d754c30042f6610c010bd584300427d65c8010b798f20042dd63c80109fd96200427d6588010db94a200436d5288010bd98620042f561880109fd95200427f65080109f994200427d65080109f194200436e5208010db54820042f66108010bd584200437565c4010bd99310042f464c4010bd58610043765184010be596100437965840109e59610042f96184010de94610043f25184010fcd0610043f041840109fd9510042bf6444010af19110042df6344010b718d10042ef6244010bb18910042f76544010ddd9510042776544010edd9110042f66444010bd19110043b46444010ad19110043d76344010f518d10043e76244010f918910042f76044010dd94110043f24044010fc50110043f33044010fc0c110043f32044010fc08110042fb6544010ded95100427b6544010eed9110043b86444010f6d8d10043d86344010fad8910043e86244010bed8510043f36144010de94510043f25144010fc90510043f14144010fccc510043f03144010fcc8510043f02144010
  | 1 => 0x427d63d50109f98b540427d62d50109f987540437661d50109f983540437a60d50109f596540433f54950109f98e540427d63950109f98a540427d6295010cfd91540427f63550109f18d540427f62550109f189540427f61550109f585540437461550109fd81540427d6055010cf55054042de6315010b758c54042ee6215010bb588540427e6415010cf990540427e6315010d798c540425e63150109f58c540435d63150109758c540427e6215010db988540426e62150109f588540436d62150109b588540427e6115010dd984540427e6015010de980540427e64d4c109f593530427e62d4c109f58b530427e61d4c10dd987530427e60d4c10de983530427d6594c10d7d4e530427e6494c109f592530427e6294c109f58a530427f6454c109f191530435f6354c109fd89530427c6254c109fd85530427d6154c109fd81530427d6054c10af99053042bd6414c10d754c53042ee6214c10bb588530427e6414c10cf990530423e6414c109f590530433d6414c108f590530427e6314c10d798c530427e6214c10db988530426e6214c109f588530436d6214c109b588530427e6114c10dd984530427e6014c10de980530427f65d0c109f997430427d65d0c109f197430433e54d0c10cf553430427f6590c109f996430427d6590c109f196430435e5390c10d754e43042f66190c10bd586430427f6550c109f995430427d6550c109f195430433e5450c10cf551430435e5350c10d754d43042f76150c10bd18543042fb6050c10be181430427f6510c109f994430427d6510c109f19443042ee6210c10bb588430427e64d48109f593520427e63d48109f58f520427e61d4810dd987520427e60d4810de983520427d6594810dbd4a520427e64948109f592520427e63948109f58e520427f64548109f191520427f63548109f18d520436f62548109fd85520427d61548109fd81520427d6054810af99052042bd6414810b798c52042dd6314810db548520427e6414810cf990520423e64148109f590520433d64148108f590520427e6314810d798c520425e63148109f58c520435d63148109758c520427e6214810db988520427e6114810dd984520427e6014810de980520427f65d08109f997420427d65d08109f197420433e54d0810cf553420427f65908109f996420427d65908109f196420436e5290810db54a42042f66190810bd586420427f65508109f995420427d65508109f195420433e5450810cf551420436e5250810db54942042f76150810bd18542042fb6050810be181420427f65108109f994420427d65108109f19442042de6310810b758c420427f65cc8109f997320427d65cc8109f197320435e53cc810d754f320427f658c8109f996320427d658c8109f196320436e528c810db54a320427f654c8109f99
  | 2 => 0x5410510d7d4c414435c5310510dbd48414436c5210510ed504414427e65cc510cfd53314433c54cc510d7d4f314435c53cc510dbd4b314436c52cc510be98331442f960cc5109f996314433f548c510cf152314435f538c510d714e314436f528c510db14a314427c654c510cfd51314433c544c510d7d4d314435c534c510dbd49314436c524c510bed8131442f8604c5109f994314433f540c510cf150314435f530c510d714c31442ee620c510bb588314436f520c510db14831443d5310c5109f997214433f54c8510cf153214435f53c8510d714f214436f52c8510db14b21442fa60c8510be583214427e6588510cfd52214433c5488510d7d4e214435c5388510dbd4a214436c52885109f195214433f5448510cf151214435f5348510d714d214436f5248510db14921442fb6048510be181214427e6508510cfd50214433c5408510b798c21442dd6308510d7d4c214435c5308510dbd48214436c5208510f9484214427e65d0110cfd53404433c54d0110d7d4f404435c53d0110dbd4b404436c52d0110bd98740442f561d01109f996404433f5490110cf152404435f5390110d714e404436f5290110db14a404427f65501109f595404427c6550110cfd51404433c5450110b7d8d40442dc6350110d7d4d404435c5350110bbd8940442ec6250110dbd49404436c5250110bdd8540442f461501109f994404433f5410110cf150404435f5310110d714c404436f5210110db14840443b940101109f997304433f54cc110cf153304435f53cc110d714f30442ee62cc110bb58b304436f52cc110db14b30442f661cc110bd587304427e658c110cfd52304433c548c110d7d4e304435c538c110dbd4a304436c528c1109fd95304427d654c1109f195304433f544c110cf151304435f534c110d714d304436f524c110db14930442f7614c110bd185304427e650c110cfd50304433c540c110d7d4c304435c530c110dbd48304436c520c1109f997204433f54c8110cf15320442de63c8110b758f204435f53c8110d714f204436f52c8110db14b20442f661c8110bd587204427e6588110cfd52204433c5488110d7d4e204435c5388110dbd4a204436c52881109fd95204427d65481109f195204433f5448110cf151204435f5348110d714d204436f5248110db14920442f76148110bd185204427e6508110cfd50204433c5408110d7d4c204435c5308110dbd48204436c5208110cfd53104433c54c4110d7d4f104435c53c4110dbd4b104436c52c4110eed5310443b854c4110f6d4f10443d853c4110fad4b10443e852c4110cfd52104433c5484110d7d4e104435c5384110dbd4a104436c5284110edd5210443765484110dd15210443b45484110cd15210443d75384110f514e10443e75284110f914a10443f350841109f98f540
  | 3 => 0x910b798e52442dd6394910d7d4e524435c5394910dbd4a524427e6494910cf992524423e64949109f592524433d64949108f592524427e6394910d798e524425e63949109f58e524435d63949109758e524427e62949109b98a524427d6194910dd586524427d6094910de58252442bf6454910af191524433f5454910cf15152442df6354910b718d524435f5354910d714d524427f6454910cfd91524423f64549109f191524433c64549108f191524427f6354910d7d8d524425f63549109f18d524435c63549109718d524436f62549109fd85524437761549109fd81524437b60549109f994524433f5414910cf150524435f5314910d714c524436d52149109f990524427d64149109f98c524427d6314910db988524427e61149109f184524427e60149109f18052442ee6514910db994524426e6514910dbd5052443af5414910cbd50524436e5414910db550524436c5414910eb150524432c5414910dbd4c52443cf5314910d3d4c524436e5314910db54c524436c5314910f314c524434c5314910dbd90524436e6414910db590524436c6414910dbd8c524436e6314910db58c524436c6314910dbd0c524436e4314910db50c524436c4314910dbd84524436d6114910dbd80524436d6014910db440524427f65d09109f997424427d65d09109f197424433f54d0910cf153424435f53d0910d714f424436f52d0910db14b424427f65909109f996424427d65909109f196424433f5490910cf152424435f5390910d714e424436f5290910db14a424427f65509109f995424427d65509109f195424433f5450910cf151424435f5350910d714d424436f5250910db149424427f65109109f994424427d65109109f194424433f5410910cf15042442de6310910b758c424435f5310910d714c424436f5210910db14842442f66110910bd58442442fa6010910be580424427f65cc9109f997324427d65cc9109f197324433f54cc910cf153324435f53cc910d714f324436f52cc910db14b324427f658c9109f996324427d658c9109f196324433f548c910cf152324435f538c910d714e324436f528c910db14a324427f654c9109f995324427d654c9109f195324433f544c910cf151324435f534c910d714d324436f524c910db149324427f650c9109f994324427d650c9109f194324433f540c910cf150324435f530c910d714c324436f520c910db14832443cd320c910bd98432442f5610c9109f997414433f54d0510cf153414435f53d0510d714f414436f52d0510db14b41442fa60d0510be583414427e6590510cfd52414433c5490510d7d4e414435c5390510dbd4a414436c52905109f195414433f5450510cf151414435f5350510d714d414436f5250510db14941442fb6050510be181414427e6510510cfd50414433c
  | 4 => 0xf58c544427e62151109f588544427e61151109f184544427e60151109f18054442be6515110cf994544423e6515110cfd8c544433e6315110cf58c544433c6315110cfd88544433e6215110cf588544433c6215110cfd84544433d6115110cfd80544433d6015110cf440544433f54d4d10cf153534427e64d4d109f593534427e62d4d109f58b534435f54d4d10e7d53534431f54d4d10d7953534435d54d4d10d7153534439c54d4d10c7153534435f64d4d10d7993534435d64d4d10d7193534435f62d4d10d798b534435d62d4d10d718b534435f61d4d10d7587534435f60d4d10d758353442be6494d10af592534433f5494d10cf152534435f5394d10bb98a53442ed6294d109f992534433e6494d108f992534427d6494d10cf592534423d6494d109f98e534425e6394d109f98a534436e6294d109b98a534427d6294d10db58a534426d6294d109f58653443756194d109f58253443796094d10afd9153442bc6454d10cfd51534433c5454d10bbd8953442ec6254d109fd91534433f6454d108fd91534427c6454d10cf191534423c6454d10d7d8d534427f6254d10dbd89534426f6254d109f189534436c6254d109b189534427f6154d10ddd85534427f6054d10ded81534427e6514d10cfd50534433c5414d10d754c534427e6414d109f590534435e6314d109f988534427d6214d109f984534427c6114d109f980534427c6014d10b7994534435e6514d1097994534435f5414d10e7d50534431f5414d10d7950534435d5414d10d7150534439c5414d10c7150534435f6414d10d7990534435d6414d10d7190534435f6214d10d7988534435d6214d10d7188534435f6114d10d7584534435f6014d10d7580534435d1014d109fd97434427e65d0d109f597434427c65d0d10cfd53434433c54d0d10d7d4f434435c53d0d109fd96434427e6590d109f596434427c6590d10cfd52434433c5490d10d7d4e434435c5390d109fd95434427e6550d109f595434427c6550d10cfd51434433c5450d10d7d4d434435c5350d109fd94434427e6510d109f594434427c6510d10cfd50434433c5410d10d7d4c434435c5310d10bb98843442ed6210d10bd98443442f56110d10be98043442f96010d10cfd53524433c54d4910d7d4f524435c53d49109f993524427d64d49109f98f524427d63d4910dbd5352443af54d4910cbd53524436e54d4910db553524436c54d4910eb153524432c54d4910dbd4f52443cf53d4910d3d4f524436e53d4910db54f524436c53d4910f314f524434c53d4910dbd93524436e64d4910db593524436c64d4910dbd8f524436e63d4910db58f524436c63d4910dbd0f524436e43d4910db50f524436c43d4910dbd87524436d61d4910dbd83524436d60d4910af99252442bd6494910cfd52524433c5494
  | 5 => 0x428427d65d0a109f197428427f6590a109f996428427d6590a109f19642842f66190a10bd586428427f6550a109f995428427d6550a109f19542842f76150a10bd185428427f6510a109f994428427d6510a109f19442842de6310a10b758c42842fa6010a10be580428427f65cca109f997328427d65cca109f197328435f53cca10d714f328427f658ca109f996328427d658ca109f196328436f528ca10db14a328427f654ca109f995328427d654ca109f195328435f534ca10d714d328436f524ca10db14932842f7614ca10bd185328427f650ca109f994328427d650ca109f19432843cd320ca10cf953418433d54d0610be98341842f960d0610dd597418437754d0610ed953418437554d0610ed55341843f260d0610bd58341843f160d0610cfd52418433c5490610cf951418433d5450610bed8141842f86050610cfd50418433c5410610ed50441842f56510610dd59441843b66410610ddd5041843b75410610cdd5041843755410610ed15041842f56010610d794f318435d53cc610be98331842f960cc610d7d4e318435c538c610d794d318435d534c610bed8131842f8604c610d7d4c318435c530c610bb98831842ed620c610db94b218436d52c8610be98321842f960c8610dbd4a218436c5288610db949218436d5248610bed8121842f86048610b798c21842dd6308610dbd48218436c5208610cf952408433d5490210bd98640842f56190210ed10640842df6350210b718d40842ef6250210bb18940842f76150210bd185408433e5410210cf55040842f66110210bd58440843b44110210ee50040842ee62cc210bb58b308435e538c210d754e30842f6618c210bd586308435e530c210d754c30842f6610c210bd58430842de63c8210b758f208436e5288210db54a20842f66188210bd586208436e5208210db54820842f66108210bd58420842f565c4210dd59710842f664c4210bd19310842f965c4210de597108427e63d51109f58f544427e62d51109f58b544433f63d5110cf98f544433d63d5110cf18f544433f62d5110cf98b544433d62d5110cf18b544433f61d5110cf587544433f60d5110cf583544433f5495110b798e54442dd6395110bb98a54442ed62951109f992544423e64951109f98e544435e63951109798e544427d6395110d758e544425d63951109f98a544436e62951109b98a544427d6295110db58a544426d62951109f586544437561951109f58254443796095110b7d8d54442dc6355110bbd8954442ec6255110cfd91544427f6355110d7d8d544425f63551109f18d544435c63551109718d544427f6255110dbd89544426f62551109f189544436c62551109b189544427f6155110ddd85544427761551109fd81544437b60551109f994544433d5415110cf990544427e63151109
  | 6 => 0x2f56110b109fd9732c427e65ccb109f59732c427c65ccb10d794f32c435d53ccb109fd9632c427e658cb109f59632c427c658cb10db94a32c436d528cb109fd9532c427e654cb109f59532c427c654cb10d794d32c435d534cb10db94932c436d524cb10bed8132c42f8604cb109fd9432c427e650cb109f59432c427c650cb10f34c832c42f6610cb10bd58432c433e5490710cf55241c42fa6090710be58241c433e5410710cf55041c43b54110710be98041c42f96010710d794e31c435d538c710be98231c42f9608c710d794c31c435d530c710bb98831c42ed620c710f54c431c42fa600c710be58031c436e5288710db54a21c42fa6088710be58221c42de6308710b758c21c436e5208710db54821c43e52108710be98021c42f96008710cf95340c433d54d0310bd98740c42f561d0310cfd5240c433c5490310cf95140c433d5450310b7d8d40c42dc6350310bbd8940c42ec6250310bdd8540c42f46150310cfd5040c433c5410310d794f30c435d53cc310bb98b30c42ed62cc310bd98730c42f561cc310d7d4e30c435c538c310d794d30c435d534c310bdd8530c42f4614c310d7d4c30c435c530c310b798f20c42dd63c8310db94b20c436d52c8310bd98720c42f561c8310dbd4a20c436c5288310db94920c436d5248310bdd8520c42f46148310dbd4820c436c52083109f98f548427d63d52109f98b548427d62d5210dd587548437a60d5210cfd52548427e63952109f58e548427e62952109f58a548433f64552109fd8d548427c63552109fd89548427c6255210ddd85548433d5415210cf990548427e63152109f58c548427e62152109f58854843756115210de980548427e64d4e109f593538427e62d4e109f58b538437561d4e10de983538435f5394e10bb98a53842ed6294e109f992538427d6494e109f98a538436e6294e109b98a538427d6294e10db58a538426d6294e109fd91538427c6454e10d7d8d538427f6254e109f189538435d5314e109f990538427d6414e10d798c538427e6214e109f58853843756114e10de980538427f65d0e109f997438427d65d0e109f197438427f6590e109f996438427d6590e109f19643842f66190e10bd586438427f6550e109f995438427d6550e109f19543842f76150e10bd185438427f6510e109f994438427d6510e109f19443842ee6210e10bb58843842fa6010e10be580438427e64d4a109f593528427e63d4a109f58f528437561d4a10de98352842de6394a10b758e528436f5294a109f992528427d6494a109f98e528435e6394a109798e528427d6394a10d758e528425d6394a109fd91528427c6454a109fd8d528427c6354a10dbd89528436d5214a109f990528427d6414a109f98c528427d6314a10db98852843756114a10de980528427f65d0a109f997
  | 7 => 0x410020cf55040082ee6210020bb58840083b940100209f59730082ee62cc020bb58b300827f658c0209f596300835e538c020d754e30082ee628c020bb58a30083cd328c0209fd95300827f650c0209f994300827d650c0209f194300835e530c020d754c30082ee620c020bb58830083cd320c020f64c030082de63c8020b758f20082ee64c8020bb19320082ef63c8020f398f20082ed63c8020f358f20082cd63c8020bb98720082ed6288020db94a20082f96288020de94a20083ea5288020fad0a20083e84288020fa8ca20083e93288020fa88620083e821880209fd9520082ef6548020dbd95200826f6548020bb99120082ec6448020bbd8d20082ed6348020bb18520082ef6048020db94120083eb3048020fa0c120082fb6548020ded95200827b6548020bed8920083eb6248020de94920083ea5248020facc920083e83248020b798f54c42dd63d5310bb98b54c42ed62d53109f98f54c435e63d53109798f54c427d63d5310d758f54c425d63d53109f98b54c436e62d53109b98b54c427d62d5310db58b54c426d62d5310dd98754c437960d5310cfd5254c427e63953109f58e54c427e62953109f58a54c433f64553109fd8d54c427c63553109fd8954c427c6255310cf55054c433e64153109f98c54c427d63153109f98854c427d6215310dd98454c437960153109f99353c427d64d4f109f98b53c427d62d4f10dd98753c437960d4f10d7d4e53c427e6494f109f59253c427e6294f109f58a53c427f6454f109f19153c435f6354f109fd8953c427c6254f10d754c53c42ee6214f10bb58853c427e6414f109f59053c435e6314f109f98853c436e6214f109b98853c427d6214f10db58853c426d6214f10dd98453c43796014f109fd9743c427e65d0f109f59743c427c65d0f10d794f43c435d53d0f109fd9643c427e6590f109f59643c427c6590f109fd9543c427e6550f109f59543c427c6550f10bed8143c42f86050f109fd9443c427e6510f109f59443c427c6510f10d794c43c435d5310f10bb98843c42ed6210f10bd98443c42f56110f109f99352c427d64d4b109f98f52c427d63d4b10dd98752c437960d4b10dbd4a52c427e6494b109f59252c427e6394b109f58e52c427f6454b109f19152c427f6354b109f18d52c436f6254b10b798c52c42dd6314b10db54852c427e6414b109f59052c427e6314b10d798c52c425e6314b109f58c52c435d6314b109758c52c436e6214b10dd98452c43796014b109fd9742c427e65d0b109f59742c427c65d0b10db94b42c436d52d0b109fd9642c427e6590b109f59642c427c6590b109fd9542c427e6550b109f59542c427c6550b10bed8142c42f86050b109fd9442c427e6510b109f59442c427c6510b10b798c42c42dd6310b10db94842c436d5210b10bd98442c4
  | 8 => 0x20cf950420833d5410820b798c42082dd6310820be98042082f96010820db594420826d6510820bb99042083ae6410820dbd5042083ae5410820db55042083ad5410820cb55042083ce6310820bb58c42083cd6310820b358c42082ee6110820fa98042082ed6010820fa580420827d65cc820d7d4f320835c53cc8209fd96320827d658c820d794e320835d538c820be98232082f9608c820db596320826d658c820bb99232082ec648c820dbd52320836d548c820bb58e320836e538c820f394e32083cd538c820db14e32082ee618c820fa98232082ed608c820fa58232082e9608c8209fd95320835f534c820d714d32082ef654c820dbd9532082ee644c820bb191320836f544c820db55132083cf634c820f3d4d320836e534c820db14d32083cc534c820d314d32083ce434c820f350d32082ec614c820bbd81320827f650c8209f594320835e530c820d754c32082ee620c820f34c832082fa600c820be580320837751944209f992510827d64944209f98e510827d63944209fd91510827c64544209fd8d510827c6354420db8c9510836d3254420af99051082bd6414420b798c51082dd6314420dd544510827f65d04209f997410827d65d0420cf953410833d54d0420bb98b41082ed62d04209fd96410827e65904209f59641082ee6290420bb58a41083765190420dd546410827f65504209f595410827c6550420cf951410833d5450420bbd8941082ec6250420dd94541083755150420bed8141082f860504209fd94410827e65104209f59441083b541104209fd97310827e65cc4209f597310835e53cc420d754f31082ee62cc420bb58b31083cd32cc4209fd96310827e658c4209f5963108376518c420dd546310827f654c4209f595310827c654c420d794d310835d534c420bbd8931082ec624c420f34c93108376514c420dd54531082fb604c420be181310827f650c4209f994310827d650c420bb98831082ed620c420dd947210837551c8420be98321082f960c84209f59621082ed6588420db59621082ee6488420bb19221082ef6388420bb58e21082ee6188420db54621082ed60884209fd9521082de6308420b758c21083765108420dd54421082fa6008420be58021082ee6408420bb19021082ef6308420f398c21082ed6308420f358c21082cd6308420bb98421083e66108420f9944210836d5108420f954421083655108420fa98021082ed6008420fa580210827e64940209f592500827e63940209f58e500836f4294020db10a500836e3294020db4ca500836e2194020db086500827d65d00209fd96400827d6590020cf952400833d5490020bb98a40082ed62900209fd9540082df6350020b718d40082ef6250020bb18940082f76150020bd185400827f65100209f994400827d65100209f194400833e5
  | 9 => 0x994314827d650c5209f194314835f530c520d714c31482ee620c520bb5883148377510c520dd144314827e65c8520ddd4621483745188520be98221482f96088520ddd4521483745148520bed8121482f860485209f99421482de6308520b758c21483e521085209f997404833f54d0120cf15340482ee62d0120bb58b404827e65901209fd95404827d65501209f195404833f5450120cf15140482df6350120b718d40482ef6250120bb18940482f76150120bd185404827e65101209f997304835f53cc120d714f30482ee62cc120bb58b304827e658c120d794e304835d538c1209fd95304827d654c1209f195304835f534c120d714d30482ef624c120bb189304827e650c120d794c304835d530c120b798f20482dd63c8120f698f20483d963c8120db952204836c5488120dbd4e204836d5388120db14620483eb50881209f98f540827d63d50209f98b540836e62d50209f987540827d61d50209f983540837a60d50209f596540833f54950209f98e540827d63950209f986540827d6195020cfd91540827f63550209f18d540827f62550209f589540836c62550209fd85540827c6155020cf55054082de6315020b758c54082f66115020bd584540827e6415020cf990540827e6315020d798c540825e63150209f58c540835d63150209758c540827e6215020db988540827e6115020dd984540827661150209f584540837561150209d584540827e6015020de980540827e64d4c209f593530827e62d4c20db98b530827e61d4c209f587530827e60d4c20de983530827d6594c20d7d4e530827e6494c209f592530836e6294c209f986530827d6194c209fd91530827c6454c20d7d8d530827f6254c209f589530827f6154c209f18553082be6414c20af590530835d5314c20bd98453082f56114c209f990530833e6414c208f990530827d6414c20cf590530823d6414c209f98c530835e6314c209f988530836e6214c209f98453083766114c209d984530827d6114c20dd58453082756114c209f980530837a6014c209fd97430827e65d0c209f597430827c65d0c20cf953430833d54d0c209fd96430827e6590c209f596430827c6590c20d794e430835d5390c20bb98a43082ed6290c209fd95430827e6550c209f595430827c6550c20cf951430833d5450c20d794d430835d5350c20bbd8943082ec6250c20bed8143082f86050c209fd94430827e6510c209f594430827c6510c20bb98843082ed6210c209f992520827d64948209f98e520835e63948209798e520827d6394820d758e520825d63948209f59742082ed65d0820db597420836f54d0820db55342082ed63d0820bb98742082ed60d08209fd96420827d6590820cf952420833d5490820bb98a42082fa6090820be582420827f65508209fd94420827d65108
  | 10 => 0x882ee620c220bb58830883cd320c220b798f20882dd63c8220bb597208836d65c8220bb99320882ec64c8220bbd8f20883ce63c8220bb58f20883cd63c8220b358f20882ee61c8220be597208837965c8220f698f20883d963c82209f98f544827d63d51209f987544827d61d5120cfd52544827e64951209f98e544827d63951209f58a544836d62951209f986544827d61951209f58254483796095120b7d8d54482dc6355120bdd8554482f46155120cfd91544827f6355120d7d8d544825f63551209f18d544835c63551209718d544827f6255120dbd89544826f62551209fd85544837761551209dd85544827c6155120dd185544827461551209fd81544837b60551209f994544833d5415120cf990544827e63151209f58c544827e62151209f188544827e61151209f584544827e64d4d209f593534827e61d4d209f587534835f5394d209f992534827d6494d209f98e534827d6294d20db58a534826d6294d209f986534827d6194d209f58253483796094d20afd9153482bc6454d20bdd8553482f46154d209fd91534833f6454d208fd91534827c6454d20cf191534823c6454d20d7d8d534827f6254d20dbd89534827f6154d20ddd8553482776154d209f18553483746154d209d185534827f6054d20ded81534827e6514d20d754c534827e6414d209f590534835e6314d209f988534827c6214d209f984534827d6114d209fd97434827e65d0d209f597434827c65d0d20d7d4f434835c53d0d209fd96434827e6590d209f596434827c6590d20cfd52434833c5490d209fd95434827e6550d209f595434827c6550d209fd94434827e6510d209f594434827c6510d20cfd50434833c5410d20d7d4c434835c5310d20bb98843482ed6210d209f997424833f54d0920cf15342482fa60d0920be583424827e65909209f195424833f5450920cf15142482fb6050920be181424827e6510920b798c42482dd6310920eb508424827e65cc920d7d4f324835c53cc920be98332482f960cc9209f996324827c654c920d7d4d324835c534c920bed8132482f8604c9209f99432483cd320c9209f993514827d64d45209f98f514827d63d4520ddd4651482bf6454520af19151482df6354520b718d514837551145209f990514827d64145209f98c514827d63145209f997414827d65d05209f197414837751d0520dd147414827e65905209f596414827c6590520cfd52414833c54905209fd95414827e65505209f195414827e65105209f594414827c6510520cfd50414833c5410520bb98841482ed6210520ddd4441483745110520ed50441482fa6010520be580414827e65cc5209f597314827c65cc520ddd47314837451cc5209f996314827d658c5209f196314835f538c520d714e314827f654c5209f995314827c654c5209f
  | 11 => 0x5f5394e209f992538827d6494e20db58a538827e6194e209f586538827f6454e209f191538835f6354e209fd85538827c6154e20d754c538827e6414e209f590538835e6314e20db588538827e6114e209f584538837a6014e209fd97438827e65d0e209f597438827c65d0e209fd96438827e6590e209f596438827c6590e20bb98a43882ed6290e209fd95438827e6550e209f595438827c6550e20bbd8943882ec6250e209fd94438827e6510e209f594438827c6510e20bb98843882ed6210e20cf953428833d54d0a20be98342882f960d0a20db597428836f54d0a20eb953428836d54d0a20eb55342882ed63d0a20bb98742883ea60d0a20bb58342883e960d0a20cf951428833d5450a20bed8142882f86050a20b798c42882dd6310a20bb594428836d6510a20eb990428836f5410a20db55042883ce6310a20bb58c42883cd6310a20b358c42882ee6110a20bb580428835e53cca20d754f32882fa60cca20be58332882ed658ca20db59632882ee648ca20bb192328836f548ca20db552328836e538ca20db14e32882ee618ca20bb582328835e534ca20d754d32882fb604ca20be181328836f654ca20bb99132882ec644ca20dbd51328836d544ca20f3d8d328836e534ca20f394d328834e534ca20f354d328836c534ca20f390d32883cd434ca20bb18532882ef604ca20fad8132883e8604ca20f34c8328837751946209f992518827d64946209f98e518827d63946209fd91518827c64546209fd8d518827c6354620db8c9518836d3254620dd544518827f65d06209f997418827d65d0620bb98b41882ed62d06209fd96418827e65906209f59641882ee6290620bb58a418827f65506209f595418827c6550620bbd8941882ec62506209fd94418827e65106209f59441883b54110620be98041882f960106209fd97318827e65cc6209f59731882ee62cc620bb58b31883cd32cc6209fd96318827e658c6209f596318827f654c6209f595318827c654c620bbd8931882ec624c620f34c9318827f650c6209f994318827d650c620bb98831882ed620c620dd94621883755188620be98221882f96088620bb99221882ec6488620bbd8e21882ed6388620f9946218836d5188620f954621883ea6088620bb58221883e96088620dd94521883755148620bed8121882f86048620b798c21882dd6308620bb594218836d6508620bb99021882ec6408620bbd8c21883ce6308620bb58c21883cd6308620b358c21883e66108620db54421882ed6008620cf952408833d5490220bb98a40882ed6290220b7d8d40882dc6350220bbd8940882ec6250220bdd8540882f46150220cf950408833d5410220bb98840882ed6210220bb98b30882ed62cc220d794e308835d538c220bb98a30882ed628c220f34ca308835e530c220d754c3
  | 12 => 0x90f20d794e43c835d5390f209fd9543c827e6550f209f59543c827c6550f20d794d43c835d5350f20bed8143c82f86050f209fd9443c827e6510f209f59443c827c6510f20d794c43c835d5310f20bb98843c82ed6210f20d794f42c835d53d0b20cf95242c833d5490b20d794e42c835d5390b20be98242c82f96090b20d794d42c835d5350b20cf95042c833d5410b20b798c42c82dd6310b20d794c42c835d5310b20eb50842c82fa6010b20be58042c835e53ccb20d754f32c835e538cb20d754e32c82fa608cb20be58232c835e534cb20d754d32c835e530cb20d754c32c83cd320cb20be98032c82f9600cb20af99351c82bd64d4720b798f51c82dd63d4720d794f51c835d53d4720d794e51c835d5394720ddd4651c827e64947209f59251c827e63947209f58e51c835e5354720d754d51c827f64547209f19151c827f63547209f18d51c82de6314720b758c51c835e5314720d754c51c837551147209fd9741c827e65d07209f59741c835e53d0720d754f41c837651d0720dd54741c827f65907209f99641c827d6590720cf95241c833d5490720d794e41c835d53907209fd9541c827d65507209f19541c835e5350720d754d41c82fb6050720be18141c827f65107209f99441c827d6510720cf95041c833d5410720d794c41c835d5310720bb98841c82ed6210720dd94441c83755110720ed50441c827f65cc7209f99731c827d65cc720d794f31c835d53cc7209fd9631c827e658c7209f59631c835e538c720d754e31c827f654c7209f59531c827c654c720d794d31c835d534c720bed8131c82f8604c7209fd9431c827e650c7209f59431c835e530c720d754c31c82ee620c720bb58831c835e53c8720d754f21c837651c8720dd54721c82fa60c8720be58321c835e5388720d754e21c835e5348720d754d21c82de6308720b758c21c835e5308720d754c21c83765108720dd54421c83e52108720be98021c82f96008720cf95340c833d54d0320d794f40c835d53d0320bb98b40c82ed62d0320d794e40c835d5390320cf95140c833d5450320b7d8d40c82dc6350320d794d40c835d5350320bbd8940c82ec6250320bdd8540c82f46150320d794c40c835d5310320ee50040c835e53cc320d754f30c82ee62cc320bb58b30c835e538c320d754e30c835e534c320d754d30c82ef624c320bb18930c835e530c320d754c30c83d9300c3209f98f548827d63d5220db58b548827e61d52209f587548837a60d5220cfd52548827e63952209f58e548827e61952209f586548833f64552209fd8d548827c6355220dbd89548827f61552209f185548833d5415220cf990548827e63152209f58c548836d62152209f984548827d6115220de980548827e64d4e209f593538836d62d4e209f987538827d61d4e20de98353883
  | 13 => 0xf5544310c355510c430f6980310c2dd600c430f6580310c27f65c84309f997210c27d65c8430b798f210c2dd63c8430db94b210c36d52c8430f34cb210c27f65884309f996210c27d6588430b7d8e210c2dc6388430dd946210c37551884309fd95210c27d65484309f195210c2df6348430b718d210c36e5248430db549210c3cd3248430dd945210c3755148430bed81210c2f860484309fd94210c27e65084309f594210c2de6308430b758c210c27e64940309f592500c35f4394030d710e500c35f3294030d74ca500c35e3194030d70c6500c27d65d00309fd96400c27d6590030cf952400c33d5490030b798e400c2dd63900309fd95400c2df6350030b718d400c2ef6250030bb189400c2f76150030bd185400c27f65100309f994400c27d65100309f194400c33e5410030cf550400c2de6310030b758c400c3b94010030bb98b300c2ed62cc030b7993300c2dc64cc030f398b300c2dd62cc030f358b300c2cd62cc030b7987300c2dd638c030d794e300c2f9638c030de94e300c3da538c030f6d0e300c3d8438c030f6cca300c3d9328c030f68c6300c3d8318c0309fd95300c2df654c030d7d95300c25f654c030b7991300c2dc644c030b7d89300c2dc614c030b7d81300c35e504c030bed95300c37b654c0309ed95300c2fb634c030f6d8d300c37a534c030f694d300c3da324c030f60c9300c2de63d5320b758f54c82f661d5320bd58754c827e63d5320d798f54c825e63d53209f58f54c835d63d53209758f54c836e62d53209f98754c837661d53209d98754c827d61d5320dd58754c827561d5320de58354c833f54953209f98e54c827d63953209f98654c827d6195320cfd9154c827f63553209f18d54c827f61553209f18554c833d5415320b798c54c82dd6315320cf99054c827e6315320d798c54c825e63153209f58c54c835d63153209758c54c836e62153209f98454c827d6115320de58054c827e64d4f209f59353c836e62d4f209f98753c827d61d4f20de58353c835f5394f209f99253c827d6494f209f98653c827d6194f20d7d5253c835e5494f20d755253c835c5494f20d7d9253c835e6494f20d759253c835c6494f20d798a53c835c6294f20d7d8653c835e6194f20d758653c835c6194f20d7d8253c835d6094f209fd9153c827c6454f20d7d8d53c827f6154f209f18553c835f6554f20d7d5153c835e5454f20d755153c835c5454f20d7d9153c835e6454f20d759153c835c6454f20d798953c835c6254f20d7d8553c835e6154f20d758553c835c6154f20d7d8153c835d6054f20d754c53c827e6414f209f59053c835e6314f20db98853c827e6114f209f58453c83796014f209fd9743c827e65d0f209f59743c827c65d0f20d794f43c835d53d0f209fd9643c827e6590f209f59643c827c65
  | 14 => 0x8c540c27e6215030db988540c26e62150309f588540c36d62150309b588540c27e6115030dd984540c27661150309f584540c37561150309d584540c27e6015030de980540c27e6494c309f592530c36e6294c30db58a530c27d65d0c30b7597430c35d65d0c30d7d53430c35d54d0c30b758b430c2de61d0c30b7583430c27f6590c309f596430c33e5490c30cf552430c2de6390c30be982430c2f96090c309fd95430c27f6510c309f594430c33e5410c30cf550430c2ee6210c30bb588430c2fa6010c30be580430c35d6510c3097594430c2de6410c30e7990430c35f5410c30e7950430c35d5410c30e7550430c31d5410c30f3988430c2dd6210c30f3588430c2cd6210c30b7984430c3da6010c30b7580430c3d96010c30dbd4a520c27e64948309f592520c27e61948309f586520c27f64548309f191520c27f61548309f185520c2be6414830af590520c36d5214830bd984520c2f561148309fd97420c27e65d08309f597420c33e54d0830cf553420c27f65908309f996420c27d6590830b798e420c2dd6390830db94a420c36d52908309fd95420c27d65508309f195420c33e5450830cf551420c2df6350830b718d420c36e5250830db549420c2fb6050830be181420c27f65108309f994420c27d6510830b798c420c2dd6310830db94b320c36d52cc830be983320c2f960cc830b7993320c2dc64cc830d7d53320c35d54cc830d794b320c3ce52cc830f354b320c2de61cc830f6983320c2dd60cc830f6583320c2d960cc8309f596320c2dd638c8309fd95320c2df654c830d7d95320c2de644c830b7191320c35f544c830d7551320c3cf624c830f3d49320c35e524c830f3149320c3ce424c830f3509320c2dc614c830b7d81320c2de630c830db948320c36d520c830f34c8320c2fa600c830be580320c37751944309f992510c27d64944309f98a510c27d62944309fd91510c27c64544309fd89510c27c6254430d7cc9510c35d3254430af990510c2bd6414430bb988510c2ed6214430dd544510c27f65d04309f997410c27d65d0430cf953410c33d54d0430b798f410c2dd63d04309fd96410c27e65904309f596410c2de6390430b758e410c3765190430dd546410c27f65504309f595410c27c6550430cf951410c33d5450430b7d8d410c2dc6350430dd945410c3755150430bed81410c2f860504309fd94410c27e65104309f594410c3b54110430dd947310c37551cc430be983310c2f960cc4309f596310c2dd658c430d7596310c2de648c430b7192310c2dd628c430b7986310c35d518c430b7582310c27f654c430bb988310c2ed620c430dd944310c375510c430be980310c2f9600c430b7990310c2dc640c430f3988310c2dd620c430f3588310c2cd620c430b7984310c3d6610c430f5944310c35d510c43
  | 15 => 0x4c36f62551309bd89544c27c6255130db189544c26c62551309fd85544c37761551309dd85544c27c6155130dd185544c27461551309fd81544c37b60551309f994544c33d5415130cf990544c27e63151309f18c544c27e62151309f588544c27e61151309f584544c27e65d0d30cfd53434c33c54d0d30be983434c2f960d0d309f996434c27c6550d30cfd51434c33c5450d30bed81434c2f86050d309f994434c39d4310d30bb988434c2ed6210d309f993524c27d64d49309f987524c27d61d4930dbd4a524c2bf6454930af191524c2f76154930bd185524c36d52149309f990524c27d64149309f984524c27d61149309f997424c27d65d09309f197424c36f52d0930db14b424c27e65909309f596424c27c6590930cfd52424c33c54909309fd95424c27e65509309f195424c27e65109309f594424c27c6510930cfd50424c33c5410930b798c424c2dd6310930dbd48424c36c52109309f997324c36f528c930db14a324c2fa608c930be582324c36f524c930db149324c2fb604c930be181324c27e650c930f34c8324c27e64d45309f593514c27e62d45309f58b514c3775194530afd91514c2bc6454530bbd89514c2ec6254530dd544514c27e64145309f590514c27e62145309f588514c27e65d05309f597414c27c65d0530ddd47414c37451d05309f996414c27d65905309f196414c33f5490530cf152414c27f65505309f995414c27c65505309f994414c27d65105309f194414c33f5410530cf150414c2de6310530b758c414c3775110530dd144414c3b54110530be980414c2f960105309f997314c377518c530dd146314c2fa608c530be582314c377514c530dd145314c2fb604c530be181314c27e650c530bb988314c2ed620c530f54c4314c27e65c85309f597214c27c65c8530ddd47214c37451c85309f996214c27d65885309f196214c36f5288530db14a214c27f65485309f995214c27c65485309f994214c27d65085309f194214c2de6308530b758c214c36f5208530db148214c3775108530dd144214c27e65d0130cfd53404c33c54d0130b798f404c2dd63d01309f996404c27f65501309f595404c27c6550130cfd51404c33c5450130b7d8d404c2dc6350130bbd89404c2ec6250130bdd85404c2f461501309f994404c2ee62cc130bb58b304c3ea62cc130fa58b304c35e548c130d7152304c35f528c130d7146304c3db508c1309f98f540c35e63d50309f98b540c27d62d50309f987540c27d61d50309f983540c37a60d50309f596540c33f54950309f98a540c27d62950309f986540c27d6195030cfd91540c27f63550309f58d540c35c63550309fd89540c27c62550309fd85540c27c6155030cf550540c2ee6215030bb588540c2f66115030bd584540c27e6415030cf990540c27e6315030d79
  | 16 => 0x960d0e30cf951438c33d5450e30bed81438c2f86050e30bb988438c2ed6210e30b7594438c35d6510e30e7990438c35f5410e30d7550438c3ce6210e30b7588438c3cd6210e30b3588438c2de6110e30b7580438c36f5294a309f992528c27d6494a309f986528c27d6194a309fd91528c27c6454a309fd85528c27c6154a30db548528c27f65d0a309f997428c27d65d0a309fd96428c27e6590a309f596428c2de6390a30b758e428c27f6550a309f595428c27c6550a30b7d8d428c2dc6350a309fd94428c27e6510a309f594428c2de6310a30b758c428c2dd65cca30d7597328c2de64cca30b7193328c35f54cca30d7553328c35e52cca30b7987328c2dd60cca30db94a328c36d528ca30be982328c2f9608ca30db949328c36d524ca30bed81328c2f8604ca30b7991328c2dc644ca30d7d51328c35d544ca30f3d89328c35e524ca30f3949328c34e524ca30f3549328c3ce424ca30f3509328c2dc614ca30b7d81328c3db604ca30f6181328c3cd320ca30ddd46518c27e64946309f592518c27e62946309f58a518c27f64546309f191518c27f62546309f189518c35f3254630d74c9518c37551146309fd97418c27e65d06309f597418c2de63d0630b758f418c27f65906309f996418c27d6590630b798e418c2dd63906309fd95418c27d65506309f195418c2df6350630b718d418c27f65106309f994418c27d6510630ed504418c2fa6010630be580418c376518c630dd546318c2fa608c630be582318c2de648c630b7192318c2dd628c630f5946318c35d518c630f5546318c3da608c630b7582318c3d9608c630dd945318c375514c630bed81318c2f8604c630bb988318c2ed620c630b7594318c35d650c630b7990318c2dc640c630f3988318c2dd620c630f3588318c2cd620c630f5984318c35d510c630b7580318c27f65c86309f997218c27d65c8630b798f218c2dd63c8630f34cb218c27f65886309f996218c27d6588630b7d8e218c2dc63886309fd95218c27d65486309f195218c2df6348630b718d218c3cd32486309fd94218c27e65086309f594218c2de6308630b758c218c33e5490230cf552408c2de6390230b758e408c2df6350230b718d408c2ef6250230bb189408c2f76150230bd185408c33e5410230cf550408c2de6310230b758c408c2ee62cc230bb58b308c2dd65cc230d7597308c2de64cc230b7193308c3ce62cc230b758b308c3cd62cc230b358b308c2de61cc230be597308c37965cc230fa98b308c3e962cc2309f98b544c27d62d51309f987544c27d61d5130cfd52544c27e64951309f58e544c35d63951309f98a544c27d62951309f986544c27d61951309f582544c3796095130bbd89544c2ec6255130bdd85544c2f46155130cfd91544c27f6355130d7d8d544c25f63551309fd8954
  | 17 => 0x4b30dbd9552cc36f5454b30db95152cc36d5454b30db15152cc36f6454b30db99152cc36d6454b30db19152cc36e6354b30dbd0d52cc36e4354b30db50d52cc36c4354b30dbd8552cc36e6154b30db58552cc36c6154b30dbd8152cc36d6054b30db54852cc27f65d0b309f99742cc27d65d0b30db94b42cc36d52d0b309fd9642cc27e6590b309f59642cc36e5290b30db54a42cc27f6550b309f59542cc27c6550b30db94942cc36d5250b30bed8142cc2f86050b309fd9442cc27e6510b309f59442cc2de6310b30b758c42cc36e5210b30db54842cc36e52ccb30db54b32cc2fa60ccb30be58332cc36d528cb30db94932cc36e520cb30db54832cc3cd320cb30be98032cc2f9600cb30af99351cc2bd64d4730bb98b51cc2ed62d4730db94b51cc36d52d4730db94a51cc36d5294730ddd4651cc27e64947309f59251cc27e62947309f58a51cc36e5254730db54951cc27f64547309f19151cc27f62547309f18951cc2ee6214730bb58851cc36e5214730db54851cc37551147309fd9741cc27e65d07309f59741cc36e52d0730db54b41cc37651d0730dd54741cc27f65907309f99641cc27d6590730cf95241cc33d5490730db94a41cc36d52907309fd9541cc27d65507309f19541cc36e5250730db54941cc2fb6050730be18141cc27f65107309f99441cc27d6510730cf95041cc33d5410730b798c41cc2dd6310730db94841cc36d5210730dd94441cc3755110730ed50441cc36e52cc730db54b31cc37651cc730dd54731cc2fa60cc730be58331cc36e528c730db54a31cc36e524c730db54931cc2ee620c730bb58831cc36e520c730db54831cc376510c730dd54431cc3d5310c730be98031cc2f9600c7309fd9721cc27e65c87309f59721cc36e52c8730db54b21cc27f65887309f99621cc27d6588730db94a21cc36d52887309fd9521cc27d65487309f19521cc36e5248730db54921cc2fb6048730be18121cc27f65087309f99421cc27d6508730b798c21cc2dd6308730db94821cc36d5208730cf95340cc33d54d0330b798f40cc2dd63d0330db94b40cc36d52d0330db94a40cc36d5290330cf95140cc33d5450330b7d8d40cc2dc6350330bbd8940cc2ec6250330db94940cc36d5250330bdd8540cc2f46150330db94840cc36d5210330ee50040cc35d63d52309f98b548c27d62d52309f987548c27d61d5230de983548c33f54952309f98a548c27d62952309f986548c27d6195230cfd91548c35f63552309fd89548c27c62552309fd85548c27c6155230cf550548c33e6415230d758c548c27e62152309f588548c27e61152309f584548c37a6015230cf953438c33d54d0e30be983438c2f960d0e30d7597438c35f54d0e30e7953438c35d54d0e30e7553438c2dd62d0e30b7987438c3da60d0e30b7583438c3d
  | 18 => 0xb758c51102ee6214440bb58851103755114440dd947411037551d0440be98341102f960d04409f59641102bd6590440cf59641102be6190440cf54641102bd60904409fd9541103765110440dd54441103b54110440be98041102f96010440af98441103b66110440ed944411033d5110440ed54441103355110440ee98041102bd6010440ee58041102b960104409fd97311027e65cc4409f59731102be64cc440af593311035e53cc440d754f311027f658c4409f996311027d658c440dd9463110375518c4409fd95311027d654c4409f19531102bf644c440af191311035e534c440d754d3110376514c440dd54531102fb604c440be181311027f650c4409f994311027d650c440bb98831102ed620c4409fd97211027e65c84409f59721102be64c8440af593211036e52c8440db54b211027f65884409f996211027d6588440dd946211037551884409fd95211027d65484409f19521102bf6448440af191211036e5248440db54921103765148440dd54521102fb6048440be181211027f65084409f994211027d6508440b798c21102dd6308440cf906501033c4194040af98740102bd6490040cf95240102f96490040de95240103ba5490040ee90640103b841900409fd9540102df6350040b718d40102ef6250040bb18940102f76150040bd18540102bf6550040cfd95401023f6550040e7d8d401039c6350040ebd8940103ac6250040edd8540102bc6150040ed18540102b46150040afd81401033e5050040bed95401037b65500409ed9540102fb6450040eed91401037a5450040ee95140103db6350040f618d40103ba4350040ee10d40103eb6250040fa18940103ba4250040ee10940103f36150040fc18540103bb4150040ee50540102ee62d5330bb58b54cc2f661d5330bd58754cc35e63d53309f98b54cc36e62d53309b98b54cc27d62d5330db58b54cc26d62d53309f98754cc37661d53309d98754cc27d61d5330dd58754cc27561d5330de58354cc33f54953309f98a54cc27d62953309f98654cc27d6195330cfd9154cc27f62553309f18954cc27f61553309f18554cc33d5415330bb98854cc2ed6215330cf99054cc35e63153309f98854cc36e62153309b98854cc27d6215330db58854cc26d62153309f98454cc27d6115330de58054cc33e5490f30cf55243cc2fa6090f30be58243cc33e5410f30cf55043cc39d4310f30bb98843cc2ed6210f30be98043cc2f96010f30dbd4a52cc27e6494b309f59252cc27e6194b309f58652cc36f5494b30db95252cc36d5494b30db15252cc36f6494b30db99252cc36d6494b30db19252cc36c6394b30dbd0e52cc36e4394b30db50e52cc36c4394b30dbd8652cc36e6194b30db58652cc36c6194b30dbd8252cc36d6094b309fd9152cc27c6454b309fd8552cc27c615
  | 19 => 0x641502fa6090540be582415035f5350540d714d415036f5250540db14941503775150540dd14541502fb6050540be181415027e6510540d7d4c415035c5310540dbd48415036c5210540ddd4441503b541105409f997315027d65cc5409f197315035f53cc540d714f315036f52cc540db14b315037751cc540dd147315027e658c5409f596315027c658c540d7d4e315035c538c540dbd4a315036c528c540ddd463150374518c5409fd95315027e654c5409f195315035f534c540d714d315036f524c540db1493150377514c540dd145315027e650c5409f594315027c650c540af99031502bd640c540d7d4c315035c530c540bb98831502ed620c540dbd48315036c520c540ddd443150374510c540be98031502f9600c5409f997215027d65c85409f197215035f53c8540d714f215036f52c8540db14b215037751c8540dd147215027e65885409f596215027c6588540d7d4e215035c5388540dbd4a215036c5288540ddd46215037451885409fd95215027e65485409f195215035f5348540d714d215036f5248540db14921503775148540dd145215027e65085409f594215027c6508540af99021502bd6408540b798c21502dd6308540d7d4c215035c5308540dbd48215036c5208540ddd4421503745108540be98021502f96008540d7d4f405035c53d0140dbd4b405036c52d0140ddd47405037451d0140f6d4f40503d853d0140fad4b40503e852d0140fcd4740503f051d0140d7d4e405035c5390140dbd4a405036c5290140ddd4640503745190140e7d4e405039c5390140ebd4a40503ac5290140edd46405033c5190140ed14640503345190140eed42405035f5394c409f98a531027d6294c409f986531027d6194c409fd89531027c6254c409fd85531027c6154c40d754c53102ee6214c40bb58853102f66114c40bd584531035e53d0c40d754f43102fa60d0c40be583431027d6590c409fd95431035e5310c40d754c43102ee6210c40bb58843102fa6010c40be580431036f52948409f98e521027d63948409f986521027d61948409fd8d521027c63548409fd85521027c6154840b798c52102dd6314840db54852102f66114840bd584521036e52d0840db54b42102fa60d0840be583421027d65908409fd9542102de6310840b758c421036e5210840db54842102fa6010840be580421027f65cc8409f997321027d65cc840d794f321035d53cc8409fd96321027e658c8409f596321036e528c840db54a321027f654c8409f595321027c654c840afd9132102bc644c840d794d321035d534c840db949321036d524c840bed8132102f8604c8409fd94321027e650c8409f59432103cd320c840ddd46511027e63944409f58e511027e62944409f58a511027f63544409f18d511027f62544409f18951102de6314440
  | 20 => 0x2f76154940bd185525035f5314940d714c525036d52149409f98c525027d63149409f984525027d6114940bb994525036e6514940dbd4c52503cf5314940d3d4c525036e5314940db54c525036c5314940f314c525034c5314940dbd90525036f6314940db98c525036d6314940db18c525036f4314940db90c525036d4314940db10c525036f6114940db984525036d6114940db184525036f6014940db580525036d40149409f997425035f53d0940d714f425036c52d0940d7d4e425035c5390940dbd4a425036c5290940be98242502f96090940d7d4d425035c5350940dbd49425036c5250940bed8142502f860509409f99442502de6310940b758c425035f5310940d714c425036f5210940eb508425027e65cc9409f597325027c65cc940d7d4f325035c53cc940dbd4b325036c52cc9409f996325027d658c9409f196325035f538c940d714e325036f528c940db14a325027f654c9409f995325027c654c940d7d4d325035c534c940dbd49325036c524c9409f994325027d650c9409f19432502be640c940af590325035f530c940d714c325036f520c940db14832503cd320c940d7d4f515035c53d4540dbd4b515036c52d45409f98f515027d63d45409f98b515027d62d4540ddd4f51503d753d4540d5d4f515037653d4540dd54f515037453d4540f514f515035453d4540ddd4b51503e752d4540d9d4b515037652d4540dd54b515037452d4540f914b515036452d4540ddd93515037763d4540dd98f515037563d4540dd18f515037743d4540dd90f515037543d4540dd10f515037762d4540dd98b515037562d4540dd18b515037742d4540dd90b515037542d4540dd10b515037732d4540dd8cb515037532d4540dd0cb515037760d4540dd58351502de6394540b758e515035f5394540d714e51502ee6294540bb58a515036f5294540db14a51503775194540b7d8d51502dc6354540d7d4d515035c5354540bbd8951502ec6254540dbd49515036c5254540d7d4c515035c5314540dbd48515036c5214540dd544515027e63145409f58c515027e62145409f58851502f66514540dd99451503775314540f5d4c51503575314540dd94c51503755314540dd14c51503d45314540d514c51503775214540f9d4851503675214540dd94851503755214540dd14851503e45214540d914851503776414540ddd8c51503766314540dd58c51503746314540ddd0c51503764314540dd50c51503744314540ddd8851503766214540dd58851503746214540ddd0851503764214540dd50851503744214540ddcc851503763214540dd4c851503743214540ddd8051503756014540dd500515027e65d0540d7d4f415035c53d0540dbd4b415036c52d0540dd147415035f5390540d714e415036f5290540db14a41503775190540dd14
  | 21 => 0x6394a40b758e529036f5294a409f98e529035e6394a409798e529027d6394a40d758e529025d6394a409f986529027d6194a409fd8d529027c6354a409fd85529027c6154a40db548529036e5290a40db54a42902fa6090a40be582429036e5250a40db54942902fb6050a40be18142902de6310a40b758c429027f65cca409f997329027d65cca409fd96329027e658ca409f596329027f654ca409f595329027c654ca40afd9132902bc644ca409fd94329027e650ca409f59432903cd320ca40ddd46519027e63946409f58e519027e62946409f58a519027f63546409f18d519027f62546409f18951903755114640dd94641903755190640be98241902f96090640ed946419033d5190640ed54641903ba6090640af58241903b96090640dd94541903755150640bed8141902f86050640ed50441902bd6510640cf59441903b66110640edd44419033d5110640ed14441902bd60106409fd97319027e65cc6409f59731902be64cc640af593319027f658c6409f996319027d658c6409fd95319027d654c6409f19531902bf644c640af191319027f650c6409f994319027d650c640bb98831902ed620c640be98031902f9600c6409fd97219027e65c86409f59721902be64c8640af593219027f65886409f996219027d65886409fd95219027d65486409f19521902bf6448640af191219027f65086409f994219027d6508640b798c21902dd6308640be98021902f96008640af597409033d65d0240af98740902f965d0240de597409027e62d4d409f58b535027e61d4d409f587535035f64d4d40d7d8b535035e62d4d40d758b535035c62d4d40d7d87535035e61d4d40d7587535035c61d4d40d7d83535035d60d4d40d7d4e53502ee6294d40bb58a53502f66194d40bd58653502ef6254d40bb18953502f76154d40bd185535035d5314d409f988535027d6214d409f984535027d6114d40b7994535035e6514d40d7d90535035f6214d40d7988535035d6214d40d7188535035f6114d40d7984535035d6114d40d7184535035f6014d40d7580535035d4014d409f997435035c53d0d40d7d4e435035c5390d40be98243502f96090d40d7d4d435035c5350d40bed8143502f86050d409f994435035f5310d40e750c43502ee6210d40bb588435035f53d4940d714f525027e63d49409f58f525027e61d49409f587525036f53d4940f3d4f525034f53d4940db94f525036d53d4940db14f52503cc53d4940d314f525036f64d4940dbd8f525036e63d4940db58f525036c63d4940dbd0f525036e43d4940db50f525036c43d4940dbd87525036e61d4940db587525036c61d4940dbd83525036d60d4940b798e52502dd6394940d7d4e525035c5394940dbd4a52502f66194940bd58652502df6354940b718d525035f5354940d714d525
  | 22 => 0x421dbd95210866f6548421dbd4d21087ce5348421db54d21087cd5348421d354d21086ef6148421db94521087e74148421f910521087e73148421f90c521086ec6048421bdd95210877765484219dd9521087d65348421f554d21086f76248421f9d8921087765248421f994921087e74248421f910921087e73248421f90c921086de63d4021b758f500875e53d4021d754f500875e5394021d754e500877b50940219f992500867d64940219f98e500867d6394021d794d500875d53540219fd91500867c64540219fd8d500867c6354021af99050086bd6414021b798c50086dd6314021d794c500875d5314021de540500875f5394f409f98a53d027d6294f409f98653d027d6194f409fd8953d027c6254f409fd8553d027c6154f40d754c53d02ee6214f40bb58853d035e53d0f40d754f43d02fa60d0f40be58343d035e5310f40d754c43d039d4310f40bb98843d02ed6210f40be98043d02f96010f40dbd4a52d027e6394b409f58e52d027e6194b409f58652d027f6354b409f18d52d027f6154b409f18552d02de6314b40b758c52d036d5214b40db94b42d036d52d0b40be98342d02f960d0b40b798c42d02dd6310b40db94842d036d5210b40eb50842d02fa6010b40be58042d027f65ccb409f99732d027d65ccb40d794f32d035d53ccb409fd9632d027e658cb409f59632d036e528cb40db54a32d027f654cb409f59532d027c654cb40d794d32d035d534cb40db94932d036d524cb40bed8132d02f8604cb409fd9432d027e650cb409f59432d02be640cb40af59032d03cd320cb40b798f51d02dd63d4740bb98b51d02ed62d4740ddd4651d027e63947409f58e51d027e62947409f58a51d027f63547409f18d51d027f62547409f18951d03755114740dd94741d037551d0740be98341d02f960d0740dd94441d03755110740ed50441d02fa6010740be58041d027f65cc7409f99731d027d65cc7409fd9631d027e658c7409f59631d035e538c740d754e31d027f654c7409f59531d027c654c740bed8131d02f8604c7409fd9431d027e650c7409f59431d02be640c740af59031d035e530c740d754c31d02ee620c740bb58831d027f65c87409f99721d027d65c87409fd9621d027e65887409f59621d036e5288740db54a21d027f65487409f59521d027c6548740bed8121d02f860487409fd9421d027e65087409f59421d02be6408740af59021d02de6308740b758c21d036e5208740db54821d035f5394e40bb98a53902ed6294e409f98a539036e6294e409b98a539027d6294e40db58a539026d6294e409f986539027d6194e409fd89539027c6254e409fd85539027c6154e40d754c539035e5390e40d754e43902fa6090e40be582439035e5350e40d754d43902fb6050e40be18143902ee6210e40bb58843902de
  | 23 => 0xb98b530867e61d4c21dd987530867e60d4c219f583530867d6594c21d7d4e530867e6494c219f592530867e6094c219f582530865d6594c21d7d52530875e5494c21d7552530875c5494c21d7d92530875e6494c21d7592530875c6494c21d798a530875c6294c21d7986530875c6194c21d7d82530875e6094c21d7582530875c6094c219fd91530867c6454c21d7d8d530867f6054c219f181530875f6554c21d7d51530875e5454c21d7551530875c5454c21d7d91530875e6454c21d7591530875c6454c21d7989530875c6254c21d7985530875c6154c21d7085530875f6054c21d7981530875d6054c21d718153086de6314c21d754c530867e6414c219f590530867e6314c21d798c530865e6314c219f988530876e6214c219b988530867e6114c21dd984530867e6014c219f580530867f65d0c219f997430867d65d0c219f197430875e53d0c21d754f430867f6590c219f996430867d6590c219f196430875e5390c21d754e430867f6550c219f995430867d6550c219f195430875e5350c21d754d43086ef6250c21bb18943086f76150c21bd185430867f6510c219f994430867d6510c219f194430875e5310c21d754c43086ee6210c21bb588430867e64948219f592520867e63948219f58e520867d65d0821d794f420875d53d08219fd96420867d6590821cf952420873d5490821d794e420875d5390821bd98642086f561908219fd95420875e5350821d754d420867f65108219f594420873e5410821cf55042086de6310821b758c420875e5310821d754c42087ad4210821bd98442086f561108219f597320875e53cc821d754f320867f658c8219f596320875e538c821d754e320876e528c821bd98632086f5618c8219fd95320875e534c821d754d320876e524c8219fd94320867d650c821d794c320875d530c821f34c832086f6610c821bd584320867e64944219f592510867e63944219f58e510867d65d0421d794f410875d53d04219fd96410867d6590421cf952410873d5490421d794e410875d5390421bb98a41086ed62904219fd95410875e5350421d754d410867f65104219f994410867d65104219f194410873e5410421cf550410875e5310421d754c41086ee6210421bb58841087b541104219f597310875e53cc421d754f310867f658c4219f596310875e538c421d754e31086ee628c421bb58a310867f654c421d794d310875d534c4219fd94310867e650c4219f594310867c650c421d794c310875d530c421bb98831086ed620c421f54c4310875e53c8421d754f210876f53c8421f394f210876d53c8421f354f210874d53c8421bb983210875e5388421d754e21086ed6288421db94a21087d65388421f554e21086f56288421dd94a21087e652884219fd95210875e5348421d754d21086ef6548
  | 24 => 0x53486fb6054d21be181534867f6454d21cfd91534863f6454d219f191534873c6454d218f191534875f6354d219fd89534876f6254d219fd8553487776154d219fd81534877b6054d219ed81534867c6054d21de18153486786054d219f994534875d5314d219f990534867d6414d21d798c534876d6214d219f980534867d6014d219fd97434867e65d0d219f597434867c65d0d21d7d4f434875c53d0d219fd96434867e6590d219f596434867c6590d21cfd52434873c5490d21bb98a43486ed6290d21bd98643486f56190d219fd95434867e6550d219f595434867c6550d219fd94434867e6510d219f594434867c6510d21cfd50434873c5410d21d7d4c434875c5310d21bb98843486ed6210d219f997424873f54d0921cf15342486f661d0921bd587424867e65909219f195424873f5450921cf15142486f76150921bd185424867e6510921b798c42486dd63109219f997324875f53cc921d714f32486f661cc921bd587324867e658c921bb996324876e658c921dbd52324876d548c921bb58e324876e538c921db14e32486ee618c9219f195324875f534c921d714d32486f7614c921bd185324876c654c9219b195324876f544c921db55132487cf634c921f3d4d324876e534c921db14d32487cc534c921d314d32487ce434c921f350d32487e7614c921bb18532487e4614c921b9185324867e650c921bb98832487cd320c9219f997414873f54d0521cf15341486ee62d0521bb58b414867e65905219fd95414867d65505219f195414873f5450521cf15141486ef6250521bb189414867e6510521ed504414867e65cc521d7d4f314875c53cc521bb98b31486ed62cc521f34cb314867e658c5219fd95314867d654c5219f195314875f534c521d714d31486ef624c521bb18931487cd324c5219f99431486ee620c521bb58831487e632c8521f94cb21486ef6388521bb58e21487e751885219f993504867d64d41219f98f504867d63d4121ded4250486bf6454121af19150486df6354121b718d504877950141219f990504867d64141219f98c504867d6314121db8c8504876d3214121db88450486de63d5021b758f540867e63d5021d798f540865e63d50219f58f540875d63d50219758f540867e62d5021db98b540867e61d5021dd987540867e60d50219f583540867d6595021cfd52540867e63950219f58e540867e60950219f582540873f64550219fd8d540867c63550219fd81540867c6055021cf55054086de6315021b758c54086fa6015021be580540867e6415021cf990540867e6315021d798c540865e63150219f58c540875d63150219758c540867e6215021db988540867e6115021dd984540867e6015021de980540867a60150219f580540877960150219e580540867e64d4c219f593530867e62d4c21d
  | 25 => 0x75e534c721d754d31c86ef624c721bb18931c87cd324c721bb98831c86ed620c721f54c431c86be64d4321af59350c86de63d4321b758f50c877b50943219f99250c867d64943219f98e50c867d6394321db8ca50c876d32943219fd9150c867c64543219fd8d50c867c6354321de54050c867e63d52219f58f548876d62d5221dd987548867e60d52219f583548873f54952219f98e548867d63952219f982548867d6095221cfd91548867f63552219f18d548867f60552219f181548873d5415221cf990548867e63152219f58c548876d6215221dd984548867e60152219f580548867e64d4e219f593538876d62d4e21dd987538867e60d4e219f583538875f5394e219f992538867d6494e219f982538867d6094e219fd91538867c6454e21d7d8d538867f6054e219f181538875d5314e219f990538867d6414e21d798c538876d6214e21dd984538867e6014e219f580538867f65d0e219f997438867d65d0e219f197438867f6590e219f996438867d6590e219f19643886f66190e21bd586438867f6550e219f995438867d6550e219f19543886ef6250e21bb189438867f6510e219f994438867d6510e219f19443886ee6210e21bb588438873e54d0a21cf55342886f661d0a21bd587428873e5450a21cf55142886f76150a21bd18542886de6310a21b758c42887ad4210a21d794f328875d53cca21bd98732886f561cca21d794d328875d534ca21bdd8532886f4614ca21f34c8328873e5490621cf55241886ee6290621bb58a418873e5410621cf55041886ee6210621bb58841887b54110621d7d4f318875c53cc621d794e318875d538c621bb98a31886ed628c621d7d4d318875c534c621d794c318875d530c621bb98831886ed620c621bb597218876d65c8621dbd4f218876d53c8621bb98321886f565c8621dd597218877b50942219f992508867d64942219f98e508867d6394221b7d8d50886dc63542219fd91508867c64542219fd8d508875f635422197d8d508867c6354221d718d508865c6354221de540508867e63d51219f58f544867e60d51219f583544873f54951219f992544867e63951219f58e544867d6295121db58a544867d6195121dd586544867e60951219f58254486df6355121b718d54486fb6055121be181544873f64551219fd8d544875f635512197d8d544867c6355121d718d544865c63551219fd89544876f62551219fd85544877761551219fd81544877b60551219ed81544867c6055121de181544867860551219f994544873d5415121cf990544867e63151219f58c544867e60151219f580544867e64d4d219f593534867e60d4d219f583534875f5394d219f992534867d6494d219f98e534867d6294d21db58a534867d6194d21dd586534867e6094d219f58253486bf6454d21af191
  | 26 => 0x2cc431f354b310c74d52cc431b7983310c6dd638c431d794e310c76e528c431db54a310c6f5638c431dd94e310c7d6538c431f994a310c7e5528c4319fd95310c76e524c431db549310c6df654c431d7d95310c65f654c431f3949310c75d524c431f3549310c74d524c431b7d85310c75e514c431f5d05310c7d4414c431b7181310c6f7654c431ddd95310c677654c431bdd8d310c7d7634c431dd94d310c7d6534c431f5d0d310c7d4434c431f9949310c7e5524c431f58c9310c7d4324c431bb98b500c6ed62d4031db94b500c76d52d4031db94a500c76d5294031ded42500c67e64940319f592500c67e62940319f58a500c76e5254031db549500c67f64540319f191500c67f62540319f189500c6be6414031af590500c6ee6214031bb588500c76e5214031db548500c77950140319f98f54c867d63d5321db98b54c877561d53219f98354c867d60d5321cfd5254c867e63953219f58e54c867e60953219f58254c873f64553219fd8d54c867c63553219fd8154c867c6055321cf55054c86de6315321b758c54c873e64153219f98c54c875e63153219798c54c867d6315321d758c54c865d6315321db98854c877561153219f98054c867d60153219f99353c867d64d4f21db98b53c877561d4f219f98353c867d60d4f21d7d4e53c867e6494f219f59253c876e6294f219f98253c867d6094f219fd9153c867c6454f21d7d8d53c867f6054f219f18153c86be6414f21af59053c875d5314f219f99053c873e6414f218f99053c867d6414f21cf59053c863d6414f21d798c53c876e6214f21dd58453c867e6014f219f58053c867f65d0f219f99743c867d65d0f219f19743c873e54d0f21cf55343c867f6590f219f99643c867d6590f219f19643c875e5390f21d754e43c86ee6290f21bb58a43c867f6550f219f99543c867d6550f219f19543c873e5450f21cf55143c875e5350f21d754d43c86f76150f21bd18543c867f6510f219f99443c867d6510f219f19443c86ee6210f21bb58843c873e5490b21cf55242c86f66190b21bd58642c873e5410b21cf55042c86de6310b21b758c42c86f66110b21bd58442c875f53ccb21d714f32c875e538cb21d754e32c86f6618cb21bd58632c876d658cb21dbd5232c876d548cb21db94e32c87ce538cb21f354e32c876c538cb21bb98632c87e6618cb21f958632c875f534cb21d714d32c86ef654cb21dbd9532c876f544cb21db55132c87cf634cb21f3d4d32c876e534cb21db14d32c87cc534cb21d314d32c87ce434cb21f350d32c86ec614cb21d794c32c875d530cb21f34c832c86f6610cb21bd58432c873e54d0721cf55341c86ee62d0721bb58b41c873e5450721cf55141c86ef6250721bb18941c87b54110721d794f31c875d53cc721bb98b31c86ed62cc721f34cb31c8
  | 27 => 0x31cf151414c6df6350531b718d414c67e6510531ed504414c7d732cc531f54cb314c6dd628c531f5d46314c67e64d41319f593504c67e62d41319f58b504c77b5094131afd91504c6bc6454131bbd89504c6ec6254131de540504c67e64141319f590504c67e62141319f588504c75f3214131d74c8504c75e3114131bb98b540c6ed62d50319f98f540c75e63d50319f98b540c76e62d50319b98b540c67d62d5031db58b540c66d62d50319f987540c77661d50319f983540c67d60d50319f596540c73f54950319f98a540c67d62950319f982540c67d6095031cfd91540c67f62550319f189540c67f60550319f181540c73d5415031bb988540c6ed6215031be980540c6f960150319f990540c73e64150319f98c540c75e63150319f988540c76e62150319b988540c67d6215031db588540c66d62150319f984540c77661150319f980540c77a60150319e980540c67d6015031de580540c67960150319f992530c67d6494c319f597430c67f6590c319f596430c73e5490c31cf552430c6f66190c31bd586430c67f6550c319fd94430c67d6510c31cf950430c73d5410c31e750c430c6ee6210c31bb588430c6f66110c31bd584430c76f52948319f992520c67d64948319f982520c67d6094831dbd52520c76e5494831db552520c76c5494831dbd92520c76e6494831db592520c76c6494831db18e520c76f4394831db90e520c76d4394831db10e520c76e6194831db186520c76f6094831db982520c76d6094831db182520c67f64548319f191520c67f60548319f181520c76f6554831dbd51520c76e5454831db551520c76c5454831dbd91520c76e6454831db591520c76c6454831db98d520c76f4354831db90d520c76d4354831db10d520c76e6154831db185520c76c3154831dbd81520c76e6054831db581520c76c6054831bb988520c76d52148319fd97420c67e65d08319f597420c76e52d0831db54b420c67f65908319f996420c67d6590831db94a420c76d52908319fd95420c67d65508319f195420c6df6350831b718d420c76e5250831db549420c6f76150831bd185420c67f65108319f994420c67d6510831b798c420c6dd6310831db948420c76d5210831d794f320c76e52cc831db54b320c6f661cc831bd587320c67d658c831db54a320c67f654c831d794d320c76e524c831db948320c76d520c831f34c8320c6f6610c831bd584320c67e64944319f592510c67d65d0431db94b410c76d52d04319fd96410c67d6590431cf952410c73d5490431b798e410c6dd6390431db94a410c76d52904319fd95410c76e5250431db549410c67f65104319f994410c67d65104319f194410c73e5410431cf550410c6de6310431b758c410c76e5210431db548410c7b54110431db94b310c76d52cc431f394b310c75d5
  | 28 => 0x553438c6f661d0e31bd587438c73e5450e31cf551438c6f76150e31bd185438c79d4310e31bb988438c6ed6210e31dbd4a528c67e6494a319f592528c67e6094a319f582528c67f6454a319f191528c67f6054a319f181528c76d5214a319fd97428c67e65d0a319f597428c67f6590a319f996428c67d6590a31bd986428c6f56190a319fd95428c67d6550a319f195428c6df6350a31b718d428c67f6510a319f994428c67d6510a31b798c428c6dd6310a31db94a328c76d528ca31bd986328c6f5618ca31db949328c76d524ca31bdd85328c6f4614ca31f34c8328c73e5490631cf552418c6de6390631b758e418c73e5410631cf550418c6de6310631b758c418c7b54110631b7597318c75d65cc631d754b318c6de60cc631bd597318c77565cc631ded42508c67e64942319f592508c67e62942319f58a508c6ef6254231bb189508c67f64542319f191508c67f6254231dbd89508c66f62542319f189508c76c62542319b189508c77950142319f98b544c67d62d51319f983544c67d60d5131cfd52544c67e64951319f58e544c75d63951319f98a544c67d62951319f586544c77561951319f982544c67d6095131bbd89544c6ec6255131bed81544c6f86055131cfd91544c67f6355131d7d8d544c67f6255131dbd89544c66f62551319f189544c76c62551319b189544c67f6155131ddd85544c67f6055131ded81544c67b60551319f181544c77860551319e181544c67e6515131cf550544c73e64151319f988544c67d62151319f980544c67d60151319f997434c73f54d0d31cf153434c6f661d0d31bd587434c67e6590d319f195434c73f5450d31cf151434c6f76150d31bd185434c67e6510d31bb988434c6ed6210d319f993524c67d64d49319f983524c67d60d4931dbd4a524c6bf6454931af191524c6fb6054931be181524c76d52149319f990524c67d64149319f980524c67d60149319f997424c67d65d09319f197424c76f52d0931db14b424c67e65909319f596424c67c6590931cfd52424c73c5490931b798e424c6dd6390931bd986424c6f561909319fd95424c67e65509319f195424c67e65109319f594424c67c6510931cfd50424c73c5410931b798c424c6dd6310931dbd48424c76c52109319f997324c6de65cc931d7997324c75f54cc931d7553324c75c52cc931b7987324c6dd638c931dbd4a324c76c528c931bd986324c6f5618c931dbd49324c76c524c931bdd85324c6f4614c931d7d51324c75d544c931f3d89324c7cf524c931d7149324c7cc524c931d3149324c7ce424c931f3509324c7d7614c931b7185324c7d4614c931b5185324c67e650c931b798c324c7cd320c9319f997414c73f54d0531cf153414c6de63d0531b758f414c67e65905319fd95414c67d65505319f195414c73f54505
  | 29 => 0x1106f46050441edd9541106b76550441cdd9541107b76350441ed98d41107b56350441ed18d41107b75350441ed94d41107b55350441ed14d41107b76250441ed98941107b56250441ed18941107b75250441ed94941107b55250441ed14941107b73250441ed8c941107b53250441ed0c941107b76050441ed98141107b56050441ed18141106b46050441ed50750107b54194041ded42501067e63940419f58e501067e62940419f58a50106df6354041b718d50106ef6254041bb18950107b541540419fd8d501075f635404197d8d501067c6354041d718d501065c63540419fd89501076f62540419bd89501067c6254041db189501066c6254041b798c50106dd6314041bb98850106ed6214041ed50450107795014041d798f54cc67e62d53319f58b54cc77561d53319f98354cc67d60d5331cfd5254cc67e62953319f58a54cc67e60953319f58254cc73f64553319fd8954cc67c62553319fd8154cc67c6055331cf55054cc6ee6215331bb58854cc73e6415331d798c54cc67e6215331db98854cc66e62153319f58854cc76d62153319b58854cc77561153319f98054cc67d6015331cf95243cc73d5490f31bd98643cc6f56190f31cf95043cc73d5410f31bb98843cc6ed6210f31bd98443cc6f56110f31dbd4a52cc67e6494b319f59252cc67e6094b319f58252cc67f6454b319f19152cc67f6054b319f18152cc6be6414b31af59052cc76d5214b319fd9742cc67e65d0b319f59742cc73e54d0b31cf55342cc67f6590b319f99642cc67d6590b31b798e42cc6dd6390b31db94a42cc76d5290b319fd9542cc67d6550b319f19542cc73e5450b31cf55142cc76e5250b31db54942cc6f76150b31bd18542cc67f6510b319f99442cc67d6510b31b798c42cc6dd6310b31db94b32cc76d52ccb31bd98732cc6f561ccb31d7d5332cc75d54ccb31d794b32cc7ce52ccb31f354b32cc6de61ccb31f598732cc7d561ccb31b7d9532cc75f654cb31d7d5132cc75d544cb31f3d8932cc7cf524cb31d794932cc7cc524cb31f390932cc7cd424cb31b718532cc76e520cb31db54832cc7cd320cb31bd98432cc6f5610cb31cf95341cc73d54d0731b798f41cc6dd63d0731cf95141cc73d5450731b7d8d41cc6dc6350731ed50441cc6be64d4331af59350cc6ee62d4331bb58b50cc77b50943319f99250cc67d64943319f98a50cc67d6294331d7cca50cc75d32943319fd9150cc67c64543319fd8950cc67c6254331de54050cc75d63d52319f98b548c67d62d5231dd987548c67e60d52319f583548c73f54952319f98a548c67d62952319f982548c67d6095231cfd91548c67f62552319f189548c67f60552319f181548c73d5415231cf990548c75d63152319f988548c67d6215231dd984548c67e60152319f580548c73e54d0e31cf
  | 30 => 0x7950142419f98b535067d62d4d419f983535067d60d4d41d7d4e53506ef6254d41bb18953506fb6054d41be181535075d5314d41bb98853506ed6214d419f988535076e6214d419b988535067d6214d41db588535066d6214d419f980535067d6014d419f997435075f5390d41d714e43506f66190d41bd586435075f5350d41d714d43506f76150d41bd185435067e6510d41bb98843506ed6210d419f98f525067d63d49419f983525067d60d4941dbd4a52506df6354941b718d52506fb6054941be18152506de6314941b758c525076d52149419f98c525075e63149419798c525067d6314941d758c525065d63149419f980525067d60149419f997425076f5290941db14a42506f66190941bd586425076f5250941db14942506f76150941bd185425067e6510941b798c42506dd63109419f997325067d65cc9419f197325076f52cc941db14b325067e658c9419f596325067c658c941d7d4e325075c538c9419fd95325067e654c9419f195325067e650c9419f594325067c650c941d7d4c325075c530c941dbd48325076c520c941f34c832507b751905419f98f505067d63d41419f98b505067d62d4141ded4250506df6354141b718d50506ef6254141bb189505077950141419f98c505067d63141419f988505067d6214141ddd04505073e4114141d7d4e531067e6294c419f58a531067e6094c419f582531067f6254c419f189531067f6054c419f181531075d5314c41bb98853106ed6214c41be98053106f96014c41d794f431075d53d0c41bd98743106f561d0c419f596431067f6550c41d794c431075d5310c41e750c43106ee6210c41bb58843106f66110c41bd584431076f52948419f98e521067d63948419f982521067d60948419fd8d521067c63548419fd81521067c6054841b798c52106dd6314841db54852106fa6014841be580521076e52d0841db54b42106f661d0841bd587421067d65908419fd9542106de6310841b758c421076e5210841db54842107ad4210841bd98442106f561108419fd97321067e65cc8419f597321075e53cc841d754f321067f658c8419f996321067d658c841db94a321076d528c8419fd95321067d654c8419f19532106bf644c841af191321075e534c841d754d321076e524c841db54932106f7614c841bd185321067f650c8419f994321067d650c841af99032106bd640c841f34c832106f6610c841bd58432106be60d0441af592411073e5490441bd59241106b56490441dd95241107b65490441bd982411067f6550441afd95411073f65504418fd9541106bf6150441cf94541106bc6050441bdd95411077765504419dd9541106f76450441edd9141107765450441ed95141107b74350441ed90d41107b54350441ed10d41107b74250441ed90941107b54250441ed1094
  | 31 => 0xd4432f34cb510cbcd3294432ddd46510ca7e64944329f592510ca7e60944329f582510cbcd32544329fd91510ca7c6454432d7cc9510cb6e3254432d74c9510cb6d3254432d34c9510ca7f60544329f181510cbcd3214432dd544510cbcd32d4032f34ca500cb7b50940329f992500ca7d6494032d7cca500cb6e3294032d74ca500cb6d3294032d34ca500ca7e61940329f586500cbcd32540329fd91500ca7c64540329fd85500ca7c6154032af990500cabd6414032f34c8500caf66114032bd584500cb795014032d7d4e53d067e6294f419f58a53d067e6094f419f58253d067f6254f419f18953d067f6054f419f18153d075d5314f41bb98853d06ed6214f41d794f43d075d53d0f41bd98743d06f561d0f41d794c43d075d5310f41bb98843d06ed6210f41bd98443d06f56110f41dbd4a52d067e6394b419f58e52d067e6094b419f58252d067f6354b419f18d52d067f6054b419f18152d06de6314b41b758c52d076d5214b41db94b42d076d52d0b41bd98742d06f561d0b41b798c42d06dd6310b41db94842d076d5210b41bd98442d06f56110b419fd9732d067e65ccb419f59732d075e53ccb41d754f32d067f658cb419f99632d067d658cb41db94a32d076d528cb419fd9532d067d654cb419f19532d075e534cb41d754d32d076e524cb41db54932d06f7614cb41bd18532d067f650cb419f99432d067d650cb41f34c832d06f6610cb41bd58432d06de63d4341b758f50d06ee62d4341bb58b50d077b50943419f98e50d067d63943419f98a50d067d62943419fd8d50d067c63543419fd8950d067c6254341de54050d075f5394e419f98a539067d6294e419f982539067d6094e419fd89539067c6254e419fd81539067c6054e41d754c53906ee6214e41bb588539075e5390e41d754e43906f66190e41bd586439075e5350e41d754d43906f76150e41bd185439079d4310e41bb98843906ed6210e41dbd4a529067e6394a419f58e529067e6094a419f582529067f6354a419f18d529067f6054a419f18152906de6314a41b758c529076d5214a41db94a429076d5290a41bd98642906f56190a41db949429076d5250a41bdd8542906f46150a41b798c42906dd6310a41eb508429067f65cca419f997329067d65cca41d794f329075d53cca419fd96329067e658ca419f596329076e528ca41db54a329067f654ca419f595329067c654ca41afd9132906bc644ca41d794d329075d534ca41db949329076d524ca419fd94329067e650ca419f59432906be640ca41af59032907cd320ca41af597419073d65d0641af98341906f565d0641dd59741906de63d4241b758f50906ee62d4241bb58b509077b50942419f98e509067d63942419f98a509067d6294241ddd06509067f63542419f18d509067f62542419f18950907
  | 32 => 0x2db996424caed6490932db952424cb6c5490932f3d8e424caee6390932f318e424cbce4390932f350e424caed6190932bb982424ca7f65509329f595424ca7c6550932cfd51424cb3c5450932b7d8d424cadc6350932bb195424cb6c65509329b195424cbaf6450932ebd51424cb6e5450932db151424cbac5450932cb151424cbcf6350932bb18d424cbcc6350932b318d424cbce4350932f350d424caef6150932bb181424ca7e6510932b798c424cadd6310932bb988424caef64cc932bb593324cbce43cc932f350f324caed61cc932bb983324cadf648c932b7592324cbcf528c932f390a324cbcd428c932b7586324cade608c9329f993514ca7d64d45329f983514ca7d60d4532ddd46514cabf6454532af191514cafb6054532be181514cb7551145329f990514ca7d64145329f980514ca7d60145329f993504ca7d64d41329f987504ca7d61d4132ded42504cabf6454132af191504caf76154132bd185504cb7950141329f990504ca7d64141329f984504ca7d6114132bd987540caf561d50329f98f540cb5e63d50329f98b540cb6e62d50329f987540cb7661d50329d987540ca7d61d5032dd587540ca7561d50329f983540ca7d60d50329f596540cb3f54950329f986540ca7d61950329f982540ca7d6095032cfd91540ca7f61550329f185540ca7f60550329f181540cb3d54150329f990540cb3e64150329f98c540cb5e63150329798c540ca7e6215032db988540ca6e62150329f984540ca7d61150329f980540ca7d60150329f992530ca7d6494c329f597430ca7f6590c329f596430cb3e5490c32cf552430cb5e5390c32bb98a430caed6290c329fd95430cb5e5350c329fd94430ca7d6510c32cf950430cb3d5410c32e750c430caee6210c32bb588430ca7e64948329f592520ca7d65d08329fd96420ca7d6590832cf952420cb3d5490832b798e420cadd6390832db94a420ca7f6550832db949420ca7f65108329f994420ca7d65108329f194420cb3e5410832cf550420cade6310832b758c420cbad4210832d7d53320cb5d54cc832b758e320cb5e538c832dbd52320cb6d548c832bb58e320cacd638c832db94e320cbce538c8329fd95320cadf654c832d7d95320ca5f654c832d7d51320cb5d544c832b7d89320cb5e524c832f3d09320cbce424c832f3509320cbcc424c832bbd95320cb6f654c8329bd95320cb6f544c832db551320caef634c832f3d8d320cb6e534c832f394d320cbcf434c832f390d320cbcd434c832f310d320cbcf654c832b3d95320cb4f654c832f3d91320cbce644c832f3591320cbcc644c832f3d51320cb4f544c832f3951320cbcd544c832d3551320cbcc544c832f3d85320cbce614c832f3585320cbcc614c832f3d81320cbce604c832f3581320cbcc604c832af993510cabd64
  | 33 => 0x8843ccaed6210f32cf95342ccb3d54d0b32b798f42ccadd63d0b32cf95142ccb3d5450b32b7d8d42ccadc6350b32b798c42ccadd6310b32eb50842ccb7751947329f99251cca7d64947329f98251cca7d60947329fd9151cca7c64547329fd8151cca7c6054732dd54451ccb7b50943329f99250cca7d64943329f98650cca7d61943329fd9150cca7c64543329fd8550cca7c6154332de54050ccb5d63d5232db98b548ca7e61d52329f587548ca7e60d52329f583548cb3f5495232db98a548ca7e61952329f586548ca7e60952329f582548cb3f64552329fd85548ca7c61552329fd81548ca7c6055232cf550548cb3e6415232d758c548cb6e62152329f984548ca7d61152329f980548ca7d6015232cf953438cb3d54d0e32bb98b438caed62d0e32cf951438cb3d5450e32bbd89438caec6250e32e750c438caed6210e32cf952428cb3d5490a32b798e428cadd6390a32bb596428cb6d6590a32db952428cbae5490a32eb552428cb6c5490a32bb98e428cbce6390a32f358e428caed6190a32bb982428caef6550a32dbd95428cbaf6450a32db951428cb6c5450a32bb18d428caef6150a32bb181428cb3e5410a32cf550428cade6310a32b758c428cadd65cca32d7597328cb5f54cca32d7553328caed65cca32db597328caef64cca32bb593328caed61cca32bb983328cb7751946329f992518ca7d64946329f982518ca7d60946329fd91518ca7c6454632d7cc9518ca7f60546329f181518cb755114632ded42508ca7e64942329f592508cb5f32942329f986508ca7d61942329fd91508ca7c64542329fd85508ca7c6154232de540508ca7e61d51329f587544ca7e60d51329f583544cb3f54951329f992544ca7d6395132d758e544ca7d6295132db58a544ca7e61951329f586544ca7e60951329f582544caf76155132bd185544cafb6055132be181544cb3f64551329fd8d544cb5f63551329fd89544cb6f62551329fd85544cb7761551329dd85544ca7c6155132dd185544ca7461551329fd81544cb7b60551329ed81544ca7c6055132de181544ca7860551329f994544cb3d5415132cf990544cb5d6315132db588544ca7e61151329f584544ca7e60151329f580544ca7e65d0d32cfd53434cb3c54d0d32bb98b434caed62d0d329f996434cade6590d32d7996434cadd6490d32d7952434cb5c5490d32f3d8a434cade6290d32f318a434cadd6190d32b7982434ca7c6550d32cfd51434cb3c5450d32bbd89434caec6250d32d7195434ca5c6550d32e7d91434cb9f5450d32d7951434cb5c5450d32e7151434cb1c5450d32f3d89434cadc6250d32f3189434cacc6250d32b7d85434cadc6050d329f994434cade6310d32bb988434ca7e65d0932cfd53424cb3c54d0932b798f424cadd63d09329f996424caee659093
  | 34 => 0x50baf52909429f98f5150a7d63d45429f9835150a7d60d4542ddd465150adf6354542b718d5150afb6054542be1815150b7551145429f98c5150a7d63145429f9805150a7d60145429f98f5050a7d63d41429f9875050a7d61d4142ded425050adf6354142b718d5050af76154142bd1855050b7950141429f98c5050a7d6314142dbd085050a7e61141429f5845050b5f5394c429f9865310a7d6194c429f9825310a7d6094c42d71925310b5e6294c42d718a5310b5f6194c42d79865310b5d6194c42d71865310b5f6094c42d79825310b5d6094c42d71825310a7f6154c429f1855310a7f6054c429f1815310b5f6554c42d79915310b5e6254c42d71895310b5c4254c42d7d855310b5e6154c42d75855310b5c6154c42d7d815310b5e6054c42d75815310b5c6054c42b798c5310b5d5314c42d794f4310b5d53d0c42bb98b4310aed62d0c429f5964310b5d5390c429fd954310b5e5350c42d794c4310b5d5310c42e750c4310aee6210c42bb5884310b5e53d0842d754f4210b9e53d0842e754f4210abd6490842cf9524210b5e5390842d754e4210aed6490842db9524210bae5490842f394e4210b6d5390842f354e4210b4d5390842bb9824210a7f6550842d794d4210b5d5350842afd954210b3f65508428fd954210b9e5350842e754d4210abf6250842cf9494210aef6550842dbd954210a6f6550842bbd914210baf6450842db9514210bae5450842f394d4210b6d5350842f354d4210b4d5350842eb90d4210bac4350842bb1814210ade63d4442b758f5110b5e53d4442d754f5110b5e5394442d754e5110b7751944429f98e5110a7d63944429f9825110a7d6094442d794d5110b5d53544429fd8d5110a7c63544429fd815110a7c6054442b798c5110add6314442d794c5110b5d5314442dd5445110afa6014442be5805110ade63d4042b758f5010b5e53d4042d754f5010b5e5394042d754e5010b7b50940429f98e5010a7d63940429f9865010a7d6194042d794d5010b5d53540429fd8d5010a7c63540429fd855010a7c6154042b798c5010add6314042d794c5010b5d5314042bd9845010af56114042de5405010b5e63d5332db58b54cca7e61d53329f58754cca7e60d53329f58354ccb3f5495332d798e54cca7e61953329f58654cca7e60953329f58254ccb3f64553329fd8554cca7c61553329fd8154cca7c6055332cf55054ccb3e6415332d798c54ccb6d62153329f98454cca7d61153329f98054cca7d6015332cf95243ccb3d5490f32bb98a43ccaed6290f32d759643ccb5e5490f32e795243ccb9d5490f32d715243ccade6290f32f398a43ccbcd6290f32b758643ccade6090f32b7d9543ccb5f6550f32e7d9143ccb5e5450f32d715143ccadc6250f32b7d8543ccadc6050f32cf95043ccb3d5410f32bb9
  | 35 => 0xc6494843db18e5210f6f4394843db90e5210f6d4394843dbd865210f6e6194843db5865210f6c6194843dbd825210f6e6094843db5825210f6c6094843d790d5210f5d43548439fd855210e7c61548439fd815210e7c6054843dbd955210faf4354843f390d5210fad4354843f350d5210f6e6454843db98d5210f6f4354843db90d5210f4e4354843db50d5210f4d4354843db10d5210f6f6154843db9855210f6d6154843db1855210f6f6054843db9815210f6d6054843db1815210eee6214843db5485210eee62d4443bb58b5110f6e52d4443db54b5110f6e5294443db54a5110f7751944439f98a5110e7d62944439f9825110e7d6094443db9495110f6d52544439fd895110e7c62544439fd815110e7c6054443bb9885110eed6214443db9485110f6d5214443dd5445110efa6014443be5805110eee62d4043bb58b5010f6e52d4043db54b5010f6e5294043db54a5010f7b50940439f98a5010e7d62940439f9865010e7d6194043db9495010f6d52540439fd895010e7c62540439fd855010e7c6154043bb9885010eed6214043db9485010f6d5214043bd9845010ef56114043de5405010f5f5394f429f98653d0a7d6194f429f98253d0a7d6094f429fd8553d0a7c6154f429fd8153d0a7c6054f42d754c53d0b5e53d0f42d754f43d0aee62d0f42bb58b43d0b5e5310f42d754c43d0aee6210f42bb58843d0b7751947429f98e51d0a7d63947429f98251d0a7d60947429fd8d51d0a7c63547429fd8151d0a7c6054742dd54451d0b7b50943429f98e50d0a7d63943429f98650d0a7d6194342b7d8d50d0adc63543429fd8d50d0b5f635434297d8d50d0a7c6354342d718d50d0a5c63543429fd8550d0a7c6154342de54050d0b5f5394e42db98a5390a7e6194e429f5865390a7e6094e429f5825390a7f6154e429f1855390a7f6054e429f1815390b5d5314e42bd9845390af56114e42d794e4390b5d5390e42bb98a4390aed6290e42d794d4390b5d5350e42bbd894390aec6250e42e750c4390aed6210e42af5974290b3d65d0a42bb5974290b6d65d0a42bb58f4290b7751946429f98e5190a7d63946429f9825190a7d60946429fd8d5190a7c63546429fd815190a7c6054642b798c5190add6314642dd5445190ade63d4242b758f5090af661d4242bd5875090b7b50942429f98e5090a7d6394242dbd0a5090a7e61942429f5865090a7f63542429f18d5090a7f61542429f1855090b7950142429f9875350a7d61d4d429f9835350a7d60d4d42d7d4e5350af76154d42bd1855350afb6054d42be1815350b5d5314d42db5885350a7e6114d429f5845350a7e6014d429f5805350a7e65d0d42d7d4e4350b5c5390d42bb98a4350aed6290d42d7d4d4350b5c5350d42bbd894350aec6250d429f9944350aee6210d42bb58f42
  | 36 => 0x540000004000000c0010008002002c004000000200000020000001000800400180030004003002c00a000000300100060014002002c0000048004000c000000c004002402a0004008000400600000030000009001400f000c00100000110050008000c00300640020010001001400c00180020004003001c001002400e000000b003c00100200000038002000801b001400400040010000003000c001000c00500800060000001001400a001000000380000008006000c02d0004002000801200000370000007000c00c001400200040060000001000c0000010000000000700040030008001003800f00000000000000000c001002800000100020000000000400000200060000000000c00d00040020000008000000400000010000000002000000136f5294b439f98652d0e7d6194b439f98252d0e7d6094b439fd8552d0e7c6154b439fd8152d0e7c6054b43db54852d0f7751947439f98a51d0e7d62947439f98251d0e7d60947439fd8951d0e7c62547439fd8151d0e7c6054743dd54451d0f7b50943439f98a50d0e7d62943439f98650d0e7d6194343bbd8950d0eec62543439fd8950d0f6f62543439bd8950d0e7c6254343db18950d0e6c62543439fd8550d0e7c6154343de54050d0ebd65d0e43cf5974390edd65d0e43d75974390edd62d0e43dbd4a5290e7e6194a439f5865290e7e6094a439f5825290e7f6154a439f1855290e7f6054a439f1815290f6d5214a43bd9845290ef56114a43ddd465190e7e62946439f58a5190e7e60946439f5825190e7f62546439f1895190e7f60546439f1815190eee6214643bb5885190f755114643bb98b5090eed62d4243bd9875090ef561d4243ded425090f5f43942439f98a5090e7d62942439f9865090e7d61942439fd895090e7c62542439fd855090e7c6154243de5405090edd62d0d43e7d4e4350e7e61d49439f5875250e7e60d49439f5835250f6f5294943bdd855250ef46154943bed815250ef86054943db5485250e7e61149439f5845250e7e60149439f5805250e7e62d45439f58b5150e7e60d45439f5835150f775194543bbd895150eec6254543bed815150ef86054543dd5445150e7e62145439f5885150e7e60145439f5805150e7e62d41439f58b5050e7e61d41439f5875050f7b5094143bbd895050eec6254143bdd855050ef46154143de5405050f5f43141439f9885050e7d62141439f9845050e7d6114143af5924310f3e5490c43b75924310f5e5490c43e79524310ede6090c439fd954310ebf6550c43cfd954310e3f6550c43afd8d4310f3e5350c43b7d954310f5f6550c4397d954310edf6450c43e7d914310f5e5450c43e79514310edc6050c43dbd4a5210e7e61948439f5865210e7e60948439f5825210faf4394843f390e5210fad4394843f350e5210f6
  | 37 => 0x1007800a00a40030030002008c00d00000030000000001000000000000008002000000300000030038009002400000100000068001004400900240030000000001c00e00180000028005000c00500280050010007002400000680000000002009000300040040010001000c00200000090050000003800100100170004004000c00200340040004001003c000000000500040160000000000c001004c0010004004000400f0018001006400600000050034000000000f0008001001000a001c00000140040048005003c0000000012000c0130030014000400b00100030000000004c0030000000002400e00240010000003004c00100300050000005000800f00080000004004000000100300050000000000000e003800c000000200480030000001000c028001c002001400600080050014002002c00f00040060000006000000b002c00100040170014001000001e00b8000000c0140018000000000a00080050000006002401700000020000002001000200000010008008000c000000800900100180028009007400b000c00000140010008001001c00000b4002000400600240020010000000000e002c00500000010040004000001400080090004000000001401000090034002000000400a80440000003000c00200100060000001000000100000030000002001c0050014014000000b001400e00000040008005000c000001401800080170000003000c0030004001001c0560034000000c01f000800000100000014003000c0020000002000c000001800000000000004002000c011003800000540030000005002c00600000050000000003400700040000000001001c0000018001000800800c800000040010004017000003200040030010001001000d0008010001400f0004000004000e001c00000040010000006000400000100050030003004c004002c001001000500140020004000000c0000000007000c001002c0000000001002001000140160000007002c028000c0030004006000000400000000010002001c001001800e00640020060012002c000000000100100000014010002c00100000020008043002c00000080090030007005c00500580090004002000000e0000003001c00000080100000004000002a001001c0004000002c001002c00900000050000006004000500140010000000003c00400000050004000000000200400040004000000c00100000040010000002c004000001c00040070000000000400b001c00000140000004000002400300000030010005000000100040010000014004800d00080000044001000001c0040000000000a000000c000c000000000600040010030000001c010000c002001000d000000d00000000004000000000000180010000017000c0110040000001000800000010
  | 38 => 0xc00300840000004012000400300140070000008000800a0028016002400e001000c0000000002c01b00140020000001000400000240040000000000c006005400000000070020001000000b003402200000010008005000c00300240130000000005801f000000b001000000000010008006000000100000000014001001c0040120001000000000040030030005000400300000000008009001400c00200010008006000400900000000098001000000900000060014004000000100000050004002000000a0004009001c00900040000004002000000100000170054000000000c00180060004009000000b0000003000c000000c0030000003002c0010014000001c01e000400400040000058001000000500000000074003003c00f004400000000010000000002000f002c0000018001002c00000000050000004002400000140050000004003401f0000003000c00300000020038002000400100380010020001002c0170000000006000b000000700080000010000001c00000380020000000000c000006000000080010004000000c00100040000004006000c00d001c001003400a0020003000c00300000010010002002c00b000c028002c0100000000000800e00340130014000002400500040050000005001c00800740030000005001000e0068004000000200040000000001004400100000000040014000800400000010000004000c001004800000080000010000000400a00100170028003001003300180010018000000000100140080018000003401500440100000010002c00200000070004000004800f000c0030008002000000a00200140000006000000200140000008001000000f0030000000800e001400d00140040060021003400c00280040018000001c0000028000001c00100000010150000000001900000020008002001c026002000000180110008002000800d00000040008000004000e0000009002c000001c000007800b000000100100010004014000000b002000b00540040000021003000c0028000001800200540000000014000c00000000040014006000c000011c00100280060008003000402a001800200300000010000004c01c000800100200010000000000400e00380030008000001000100500040014001000c00100140080068004001c003002800000000040000000000000600000020000003000000100940030000005002c00000340060014001001c001000800600180160024000000000400000010000001004400400180030000000004c00100000000030000001000a0088000001401000400050000000001800a00140000004011001800400000040000000005c0000000001002800400000060000000001000000040000004015000801a00040060008001002000000000020014
  | 39 => 0x400100200040060002000c000000c002002800000040030000002003c000002c00100100020060001000c0010000002000000100640250000008001800f00180040004002001000100000090038000003c003000000000000010004001001400100480010004004000800100340020000026001c0010008001005c00500300000000001001400900000140030005000000600280050000003001400a000c0020004000000000f000800100000030008002000000000040000060000000000000000050014005000c00000040060000000000000200080000060000000c01c000000c0038019002000000080080008017001c0050008000000000000140000000001001400000a400300180000018001002000e0000007003c00000000050004003001800000000000010004001400300200000048000004001c001800c001c00000600000028000000000d000001a000c00000000010004000000c00a0000000000400000000010004000007000300000000008001001400400a4000003c0000004009000000700180050004015000003b00040020020002001c001002c03600440090068001000c009000c00b0010001000c009000800d001401b00140000004023000000200000010010004000400e000c00100340140000005001c00000140020000002001c000000001500c8006000800400000020018000000c008000c0050008000004001600000010000000002400500080060008015002400000500040004002003c0000008002003000000100020008000003400300040000004002000c0020004001003000100040020004000000000600080000000000000400000a0004001c01c000000500100090018004001000000040450004000001800500080000000000002000400080060000000000c0110000000001c008003800e0000000000000100240090000000000c00100080000000000004c0020048000000000000080010000001006000000080000004000000400000140000000004002000500040000024000002c01c0000003008c0000004004001c00000380000000001000c00000140070004000003400000000000008012003c0320000009001001b0020000000c0020000002000800d0004002005801300000010000000000000900380030044000000000000040060014012001c00000040050010002000800000100000034000002400b0014008000c0070028009000000000000100010000001001e004000000080340004000002c008000400c0018000000c00300000030034000000c0080024004001c000000400500140020004000004800500040130008003001800000280010048002000800c0030002005c0020024002000401a000400100540160018000000400000000010010015001c001000000200680280000000
  | 40 => 0x50034006003c01800080050018003000c01b00c80010098000000c00000140190044000006c001000400000300040000000005c00000e000400000160004006000c0080000010000000000000010058000000000900480000034004000c000000000500040010004008000c00500000010014001001c00c001000000000030004007015402c0154000003c00300040000060003002403c000000c002c0000018014004800a0074000000800100000040004006000c000000c00900000010010004001c002000c00400000000014001000000000140010020011000000c000c0240000001001c006001000100100040004013000800000040090090000008c0000000005000c002000c000003400b000000a0018005000c00100300040000001000000100100000014002000800e0010012001c00400000040000001003001a001c002002800200000020000003000000100000000014001000401e002c003000000a0000001000000000040000004002000c002000400000240020004007003c01800440140000002000c003000000300300000010000001c00100000010008000001400f0004001001400d00000150004002000000000000030068001000000100000070024004001000000940010008001000c0020000000001c0000004001003400200440030008003000400f0014001000c006001800800000000098000002400d003c00600a80010000003000c01700000020000001002000200040000000001000c001000000100000080030020000000c0004002008400200880040000004002802e0004000001800c0014000000800c00200000004005000000000000040000000004400700140120000002000c017004c01400100040018002000400a005c0000000004000800d000000c00100000000019000000600000010040002001c0070020001000801300380010010004000000d00100000000006000000a0054001001c00200100070028001000803100300150008002006801f0000008000400d0008009004c0000008000000400b000c0010000002001000b00000080000004000400000000000000000000c01a0010001001400200380000000008004800c002c0020000008000800700080020010001000401300000050004003000c00100000000020043003c0080024000000000d000400000200160010005004800400240000004003008c007000000200040000060004000000d0000001000c0020000004000800c0004007000c000000000000e80140080006000000a000000200000000014001000400e0020001000400100040010004000000400000000000010000000000d0000007001801800040000004011001802000000020000000000000800000050000007000800000000010008008000000100000010028008000
  | 41 => 0x3d86000014e0000000cfc0e3214c000006180007478000000328e0000b6e000055e000277a0002a020001d00c0f0000a50bdc470e14ec93e192ecae32e87b18000d92864e0000ac6d33881a038800025d0d94000152c5df93f8f01931e0002c342ee00000470bb6f1684e48c91d9a1191b8ab1084465e080465402fbe000010875c1946ea53dced5e93fc1c3294e9a7bb3a7a489f01c80000d9c16eebbbad7c7f4b290be787760609cfc53c36260002ffa00000000d009aa43c237600007cc0001cae000000000000002893a1a000000010b020018b1ab67a29b4e00007ec06d96b09eb35f4000000074c1b5ceac05047338c54c540d18af59a5a00024cadc3a664aa40cf0849181844d33ca55e0de66d52060378199cb7520a86700000bb52c886ff034af108000000000000038f676427faf62a1866829cb800000000000000616000064c9314261ac4aed704caefe249e937b63ee583cb264d884203d23166d2af1a04934acaacaf003bbaaf2a2d3afe9c814d02409f881cc045200000001f4000000000006660000000011ea55a688db1000000000c40000000b2bb638cd9000000030ae000000039589ae00028549ec8000b290a9abd5a9c600004fa6f935ec000078400001920002f6a00000000002f28a0930f20000000000366a00000000000000c5580008e8b6327188ba451200000002cbc000000000003b800008c4ab707ca98cb87841402d807c229061a8000c430682e319c22f6985d00000000f70092227b330040239740002a14eaa000000000000000000e0a05a8dd49580e811902000000091c8a64cf508965e62e120003b7e80308c659000004bc8cd875e1f2e0000a5459a99fa9f18d248d580002ae23a8bb98000000274aed2899635a8054b8680008a10000f57000060385f27dea5ead69316477b9bac1fa00000002bb6000000006a8a7ebc497fad369e2c46310940002ac6a588000d6100000000000f14b24ef0f80000000ea45c9800002a80005d3304c00032ba3ea8000000000000006889b7128acb88e22e190000ea61ad600000001378000397923e00000005cba38af6500000000a4800000000000ea2ee880009730000000000300140050090009000000800140030008000000400b005000000080030014000001000100000050000000000801100040080014014000800a000000600000020000013000400c0008003000002100000030004000000000400680000000000003c018000c0060010001000000d0000005000000000000010000017002c003003000000480010014005002800300080000000003002800900080010000001000800c000c003001800100100040004006000c0210000000001c00000180020010007003c0020014001000400000b40060024007000003e000400100100000004000000000
  | 42 => 0xd85afb340c358062936b612ebf2e7c007000ab453aaea7e8d7856c1f6c66a0f7060490ea9ac33040be35eaa0a23b0c27000000000002cc87e2d920000a408000000025078100000000000a1694ceb3f06fc2a380ce0db90cc15c85d89768000d8800beb171438012b4aa4aa12cec3e2fe204c00ee569285297580ac61491a6dabba80f102e5e49739e8ee09eae0a79a20e65ac386f8ad608020c4ab5d275e4b52dac0cd8fa6796b2704f497e42b81c4c1708d3e70f0000c2a80009371254c031de0ede800011c33a686030940ddb816943b614da627cc806a4d00920db07fc0ba600012a4000000000013047ad3a640003984d72013a7bdb2d0a3e0000121000019a10b80000000d681d7e7b297f286e3ca479019a233eae668632eb4cca27825dd00000003a7c0000f3cc240000c34281400015a6000000060fb4c8c7195c0c5e80008bb1c8000002fc71d000098797a8f4280000000b8e0000000000000011200000002a20035b88400006a4de124c02a40fb21208aa497f0f36815812853f2a4e4ab8f30a54bd8474105204ab113ece22e3cd810000f3e0000e960ef833580006a71c76e4d3166b0aa54ee5a8000c4e97b819100001112372f6c9ac8a5cbc6a14f0000f39a63ce63234e91e35508481e1c0c90000adf291684a3b660ca2a8ae1b9492b2880001101afc000000000000000000000d2118ba39989ba2b502685a4000000033fcde38000000357c923228c4b08000cc4b26ac4aaa9ec200000e5a38247f29ff218a0204ba7071686bb3d0c878e90000017400013ae00000001559ad80001a980001bfe83f9cb428011162660000bdea680e0f8000e92a87cd6f311c3cb04c08e00000a2b1068bed1b7e5f714b4a75895cbd989006c895262a8a27c1ba8e725ff0c661299abc05108020001a9a3549d969a70000260926c0003286dc8b71469aa92c768135083d198c39380000000a2644789e8f46000000013747e7000013e00004091cd4b721a824fba2744e7ac58000000000000000e6385448a015e9b60000000000000000001f62a5a620800000000000000000d3ab9b6077b8b87b01ba8c6a80004433a1e0000000e3918047c2800000000000001f9ec8e00000003c500000000e9f860c8dfb4360c4058256d9f805dab51892f91d0169adb482f1fa400010e400018d2041000079192fc000086e1f18000dac0000000156e55f000000031eebea18d055a182ac5a2a10d4ba1dee5ca04416e368c0002382000314801b8136a0e8052b6f8b18b1e8000851176c3f912204311c2419d358ef0aac320000e880002454426a698e85b1e40000000c7da416000270a2a7b72e5cd1172baa82e600025b8000037c82e1a4eb7900004f8a67240e35dabe5158e4c29cacbe300000003c980000000cd88000e2300007a60000ce80d2ef211dec00
  | 43 => 0xabb8deaf923fe1241e289f8ac6a18d8000126adaa0000000a48111cec4090e47c00000000d0ae98800000000000000000e308000eb6a22c7b88824bae2bbc3221c10a000314d04bbb80000000c57215eaa92f7e62c08a0cd114fa00033cee4a36b4e911ca89be9dae9d200005058000000306ca6e80000cd37b271216e213315ba4690000917bc204f00d82e491c94e17ac6ea063396b0f95724eb315a68a9198068375ec6e393a97a1a66ba687d291a14d478d9aa841eaeae2c112b0524377aa9233fe000000086fb41c80a00009e69ea2896215a81d800093d0000000103a8b186b80003dae00006d226c1c40d7180000d680000000db4cb10a2c4d200001841d86843800000000006a50000060201269000168ab299c591147cccc27ca3fca2e63973852d7328a200000001838d6c64d00008e5b17e0002f3456080000002df0d5a8000d5280000a400004ec2ef09faa9943f989e2b1f0000627bd0cc3808ec1a8255e38b80004873b8400034560003be800000002322b18b0f31a4af6afc6e3e8000d6ebb0cb3a18786699834441a4100000000f1db360b4d91485eb35280da92dedb1a36ad392d082bf247ed3f2196d9085bc1e580002fa029af1a000081e30067dbbbf030c0000c2e846a1fe2b868a510560003464d4e1180000299e7361c9e62e0000ca5800000036d600004b42430b0e873b6e0f118ac207690eeb35047abbd27d863b800064a8000be4150a000000000015b4000085ed67987e7898000000314000009b2178abb83dc983ccbb9712e3493aaba32eb61f79c420d8a0c2205a87623880000c00000f423bd63290188c221912db63b76a340000c2b24b24bfbd467dd800061eb46a77a8000cf086d8000193a00018f2000224464701e2000302c0000000c3684eca348000e4b0000000000000000000002c2c419b62c7e800000ab24f600000007521496a789fe6e5480000000f882c0137007126ce14e81589280f6e50b0000eb980000000000000000000020102a200002268000193186ef5f80000640000eac800000029708a3800069c9390241129800000ea000000037284961a4800010d310ea3600000003db8cd5800054485a000030cc0001bd889b800027f00007b71c2c0000000eba000000013820000476c049d7654a8000c448e52c110000000392e9b29876d1695f231e01c6dd89a3c695ba8ce853bba0003940adfa27e21b0000ac322be48300000002dccce480005390000d499ba00000000000000000009e6bc10000c99323000006ec83e000062f19ea17d2a3e00016b200000000002eea73480005f624e69cf395e00011b8bf8296e000234a0a000007feae6e5e5012e0000d3024a8000f28914e68b340e6041f081d51212292a89000008d4e0b800094db44a0000000821b3aab3a9748a453d983be9524df1ab
  | 44 => 0x3be00024049b5257cc20bacc00016f60ce9e9a4f90cb202caf3234f03b2d9a25580001ee01dd37a8583a2b69f7156416a84869f3863aec1b978e6700001d02b2c9a0aedac180fe205f8f922c5a27800024301531f4c0e18600787a13ac1200000002d8a82d930872100007f689dc000214e4fe8000f468000000211801832a2c7f869637b81640002f407208000dbc8000a8a0e624ca29120a116dc02b9d680000000ae7a7c08c88000db5000000008ca0001f44000000000000005318bd41c500000001a48c7d090a00038fc7c48c6aef0087687c1398046a0d6163040225600bc7b2038edd5374294e9948d18071c5b434a6bd6226284b0baa73e2e647da8f9816b29987591630000000000000009f9a2d400000005330602e341ddca6137d645a245800037a60d7250090000000002392062883273da7d222197d21bc3b6ad3336521df20664d2b1ae00010a8255367c00015ce0000000d441ab40652c8aa4da8a0b1106320003a2c0002cb846d8000000000000003ecb8f800000000000000000000076e62000000003a08bee881cdfd3d282d7ba7000017c4b9518b6dd92aee5e42d7853780000000454d8f0000000365e00017a2c0412d800039c83ad0000000080400038cc20637d053da0ccf56000000010b236fae6896900006d23d9cdd4000091f18cca6f3b74000280c00000000002b3e75a80005b4851279d80a0f71abc8c4b000057bac2e0001f86cb019963a391acb87915648cb472e0c3b524fc3c44c218c40d42a1d04b58068048abd465d016828c2474000000000039e25da0a1e7a0235a96f31e200014e22720000117111478618d6dae000000006c400012bef13aa98635000060b00008c6b70ab620fd220e28620001fae2aa0000983a53877db8120001cd000008cca5a8026000260859a0d1400000000c48000a6d8000d1f2fd23368f1c3b9acc6c6483d4b3696840001fe40001510b67a5a6e03a884023b8e0000330202e15ae8f28000425a9a652c91e06f296f8b0383585310000bf11c58ceb22cc34a14500703988000072c12cb98a3d80262f44a58e32c00008162a7277ea6122bcab64f49a5f655fb6f80dfa6d655730224c930a4000113c80e36887a22c9a21131d24d31f82ec3ac96195b6241d0941a8178000cd62a3ae57000000038a4b1e1e6ebcc2d267f40552000017c0bb21121b000006982fd0cbe38d87110a6c6c50d4a47f0e302a2b466b9eafe4abb172af58b1f2bfca92a314bb56c2823d88a037fcee00b9e685ae2831c9c5c92b3b26c84b31836300005d0014200017caf520000a1380001e5025600007d4711ada453a016677f071a80b0000cb480000002234d0b9eb2a8b288c6990e6e7a30400d3283502140e1c48b0394d8200005c8242a9b8a0fcd1518a8134000087b2d380fc2b085560ec6b509e34c
  | 45 => 0xb3db9e68c1b4d01b51a5e755a170000374c9c10000000175cc4c28fc00000000001538b618070c22a9fc00019be9a82cde2f094b681aa60a00002ce00035f2a72a802000160a00000000003b927f000004e998661d699cc69197d0556b942ca633789ab12ca8cf869409c1e947d5a2a69181f3ab4c875cf3d254cd78b9a0ad384ac00008aa01da16c4f599ac0000000b9880000000000cb0ad5e7faabec00000002359c4a04533740001da4000151688c244c000000091c00000000000000000000012181da0000bbf30b2302a2da7f300002e800fa3348000dfa08b0ec680000001f3657b2b8457fa72a2139b9c8e680006230000000246a5f59eb60f919146c7bb38e1da5ac9209bf0a8f2b80d54adfaadd8b061828c42c6d19e479503ac9e424fcc75800047d334a0000000b8205b4000207c0002d1cc9700007b99af8000288837f8000eeb000032d0420000000000002cab598f6656420c6056843c000144408f00009859588d64038453fa99a0000000000000000032ca4a887b49bcae769862bcc0002d4a9b980000001d6628515ac65380000000000a64000066838e2492264cc0aaecaf551f1492c33faddd0cfe6b3387a470230c52c279660ea6920000000000000042f1c5495e949a00025107ecb2808fabd92e42a5aaec0974a3b6b932907ae580002efa64f94c21628c201028bded02b5ca2c491f68920000c91b53ef229da6c09963e00000008e51184f60800024181d463e0000e2426f600000000000e9e5f3800048bb47400002dc0fe271e3f6306a8c219602732d721b984f21260000570a38404d336cada185a0002bea2c88000201a808f15a96c30e0c4c3d0006413d3abe0000000000026c0000000a26b94c1f6961210ea2ea0c892bac05adc02761806e01a8460000000f2c27f00003c9ae44a62600000000003a864d082aebc2273a000145830032e00003222000137a8488000922bc863fe16a0a0b80004211e580000928442300a921902a7b085a293b129a68097b0efc8000000276e93abbe6000231400021a6a81b48867c0a3a788193031396869ca188ea57800000000004ef140e3811cbe4db323e0138332a05800038336a00270cce5728000f489a6854380004b887560000000d80000097c3860ac480005a2001e0000feaa6d0cac6492950e7b35580000000ef91758b610a9c1908000000045a00000000000000d93a1a2cc581f6c3515700000000000000016531e800000000002d24d70aa1200030c8506000000000000003292b5bab8a000000066d3a3c00000000001618489907026200000000000a4180000002064b738670db71388adc16bc0f4870615c1fdec069b92451bcfc778a614000351458b0000e440000000000072928fad602f0edb22b9c85885c48470000e7b8a0a0f9928430daa7e21f84728769
  | 46 => 0x147a1610fbc88735863672ad0320000000000000000000b8300000001802f5e000007d25de0001d2636b08f455eb7ee85e9340000093ad8e8000000133aa580cb656180009149896c2dae003fd0170486b562a38982e1e312f42daae5c73f980a62809363eb06b203a17f431b1c2ec3db6f6252b9660d1171826804801e1b696b551e5653bb930738169cc1539a66b9a272ec815e606897b4000279cd60b1706e692b204b1dc0a468fda2d39820b17800075b3b9a87505964f60000000000062c9ade2c432e46e3151c9fa109c6960000e6f33f87a3887a4cb00000000000000000000039143cd2630aad000000000000000f862d48932c30b49600000d0000088200000000002deee3c3d3e00036fe43e00006d331021b223b4e498bb06b6b9002bd97566bd00000000a5c77e28ba000000000035a6ef100000000000eb3bdc2666833ebfd8000d868e36bcb00007b78b500000000ec00000a29aec069b80f6416374e99f9cea0f0a8da96704c28563b1246500ba741800069c0000000122270000000003daa14886980001c96e6f94e672193f49b191b050d000069f9fba03991fa75bae80e6897d4ecf000000034866ea822e6aa800068f80000002b1a0000000c7e0c84ea08000b4000003919a6c074800045f23be3519d3e0002a040002996d47bd0445ba1480002a00cbe89a476886dc46eba3a82280007d92744970000000026ee90980000002166000000000031b000000003932caa0110000e3580f8bcead0600000006d9150c3a60000328a1e4000106201d07288ea9c1ccac353419f041e7a0afae54833229138156c6124080003db400025c20463424ad68000368116429ea65014d865899c00006f1a8321ee000094fba4cdef0554d0e00fe850052c50200003a28e1a55aabf0f29878e3a98becf541e64ad7231ef669a000002348e8f90ecc1daaf01661d2e5ba30029a580000002c20c32a4bcec109ac0000000000000050500000001dba3b9000004cbaa05e70000000000085e00001b0bcb80001ae8a8a80008799724bb493942291c5271e0a503e128e6f1204080a8923a5d52362be68000bcf800000025420fd9562000164cf728c5c0e58efe9809776bb7000000015840001d1c9140000305297850800008072f8079f8000000000059d00004e38000f5f18f400000000003cc6000000092a000092d000000026b81af000000021f2aed1e66b1c8000823b4340001faa20bb8ac2a00000008bcec41018d82fe289200000000ba97f62030000000132ae8e00007440a3434680000000000d8597b600000000000000cfa2264000000019b03de9d885da5d40000bd300000000000000355417c31a80000000e2d00007039bd49d08a362b931be73200008fc2a1a0000baebe080006c10000d0f22dead8abc4bf30000532943ad101b5a
  | 47 => 0xc6f9873aca7a1a08d1913276b0000da5399e00023d61418000000207e000303e5c21df0b6820a08622e708418abeaaa800034491385b6a5d4f23249086e800000000005f800000000000000305cd7e000000000002d90000b56800017327bea1326c20002fb0f2d07c2000074a59f800061400004d723c89f8283ca5eb7f039b2a542df9536a2a3a463e715440003b704b41c66c420d5e4a980005678000f74220a000000000037980001eeedbe800000000000001da800007ae0000000bc080000003aa2b7280000000eb206ca1c450110d2f479b0e58f0828ba6062a0ea0ed00928354058291cdffa242c51181ab12000034e211600010600e80000c0a0ac4d773a0a5102d2ebe593e6ac7a1fe5bea32c00b8ad04ba800000028c697b000000000000002d9a000354c00033a477c9c880000000000000000039b8c3f800000036440000000000229e0d23d0e00005929e33576626a3009ad9356e9238663d9198449880008d9a0e0952381a0003b68b92127855d80001a011266ee0bba000000000004da00039d80000000000000000000000002652000048a000044296d800000020f0e23a8047140d50eeb800000000000002be00001de48000d6200033863c79692cf1800000020dc00033b446aa2fc0003a7870a0f38c8d255000000000001e5c00000f0cc38000760000050cbad04c80000588019e0000f9600000003208000c6ca456ea6b75c599b21000023e61f5a62a1c78006371a0ec0000000d38a3ecbaf194ae2b80003158f4800000002bb1dbcde50000000332adb69e4c47ca286c1c8ecc159800000006de000000000000002b7a90e00036c225786cac4f9ee49389ffe8d72d3c6fd0fa29390d5a7010238028a524c19000074a284aced800000011aeb3219f80002660630000000004aebe200000f01d0869280b6cfd0c8abb59f2800000000000bd8ceb859eda6b3a225eb5c0a7c8a0800002e000000000000000000146ccd2209051380000002b906f6a2280001190abe8000a6b1f9661c8e2090e34f2316287865b0fde2fc0944ba20de8b2705026fd9316000080a0000000000000053e0000e46948630a8000b44000086108a2143329c0001f24ea9000000000000503a1000000000002fc200021c6eb532ce29ab06e000314631236b25450d7044ead52d67000001ea22478e18da3ca83b4d2016c0d362f760001caa5b5b6ac82e9a76d0190e24d509a620397c0edb145684036e435d80001d8298a3980fcced40526a0a86784b32afcde032aa93390d4e13aedea09988a8bc2cba27ea9a03bd2b0e8fd9cfaf54b17835382b2000000000032260000e2833b800023e1b582e5297e0001f70c3a000039092469a8a9c85a50000683ad280000000d2a00000368196cf60000000379edfb000000000005190f16000167af2d876c334
  | 48 => 0x1aabc27d2580000129ceb2ae3a0a30000f32003a1aebd661473132d6d0f6a2ed0000000000029799ca00000005508000134800078919b800012608a896fcf25800017ab5740003d3ccd69828000000082d1454563363455d2d4c0002ba40db00008deaa706e5a1268ab868e0002b4ce4380004e82f5a0001372dd634de3760b3ca382c606428b5c7270000857000058a8000f173666a478000d45a61c0f82206b7116a6cda0202f328b1c00016f200015403cca66200017325b8181453610f4cf82d7e00000000000d3463fb3c82a0a64a219214ca3728c27500c945b12dd858d3a02a85a38cecc9396d6b368abf3b858d798a222ce3056029af0a8a49d4ae1b32506a2a16a51896569e22068acf0380f6a0cd4ac81d3800005fe87d8bdab7584a25598000223afc0e18b1ea000000054680009713512e1316ca671966e000256a366346200000000001312e4f00001bd39863479e10e75814c265304ac188bc0aae13b4eb21fc23df2c460a0ae8e44b89f8a3c80006d8b45800000007cd1268b011b1ae838000b7680000498f4616180003e6b33225c245c34a991e64224e8a411ef0a88b3b80002e7200000006a000000001e7426d80000ee9f7c000052e5e4b194e12000054f944c6abb5706aebd72cf480000001b90000135e5e6b1cc00000000000000cbdaf1e68a00000f2000075087802c81346000000085d8000000000003000002fd039a453283470c3ae456c8d405abafeedf3800033080008868000d310000000000098f90a2b92a87ea6f9aa40001a1266233f2ae0acc47de0d0c3f29bce8013a127d9946a38f38024071b3ad4200005e9ab02f1e8dd00001ae2bc8227a6f5a030069b4d20001f42bed84ba00000000003882000057ac61867e597198ec58ba909b79a1e67084d800037d2a6bbc3a3400000d1197461af8000160028a38d02404b4aa36e4a912864680343c409d4ed80aeef33964e0002594435932e5fb8f3e8038000df28c1ac05010cbc70000897b08c000000000027f2a088000000318a6fa2cd800026360002870000000091ea8726458548f3a84566ca0a1c0000000444b65400f2610e8306900820000b01bc4a25a0000b40a2880000000870820c2958000672323a0000000f5b38f22252f488b2bc9067a2f545e1a42417ba5eec7685602ada04e5b229b8bd2a7760002d0400008fc62ab16a2ef169e00000000003aba0f39864da1ac026fe800000000002d226f8d2907bcb93056c3ae96f42d13d9e67423e445c1332e28000000026c00ed8000471b08eaca80008428f1400028563edb99a5ea8b4cc999eb000030c435931b6017048cdaf800081e8000674a8c000000006e8ae780001f8a00000000000ef093480002c500005e819ec74f060400020500001aec000000037e236e22d9cdcb0886f825e25e4ea58a4
  | 49 => 0xde8fe28ccbde11b4c48151877280000000d9ab5aa23acb7ba06000063452887640003a301fcba6e00029c03b7968a8468000a4d0000000265e0003b5868903a2000260492eb1debb8a93049ea378c46af9200000003789d4478594d6356263479880000003b16906354e4b6b31c883a77e7b523dccbb07483c01f8c021bcf60ad820ab8c00009622436565209a4b90360ae9a3c6f6d8bdcc4910d069f2b103f3b8ba000353600039ccd77800098a25c6000332ec2880009ffa7b84249fe2b58b12e156adae42c000000000007c09bc2830352447faef6e8ca344cd98000993b5aa9e523a446380006221e7c7a180008b90000000164a9818000ddb3bb099580003043a1c8940000d6c00000003838c403dcc67f000098b11ea222908e000051aca926687f204e8d57bd80d5e0e1404aa2d6f1bb0425252c809e01330f4b1ff427685e4a1b2690742b83c9ebb482230b47ebe3897678c82943aa036405288de4710d2c3842b8858b9602bb611c215a0862b6cb856004b768607b3be1052208b002ad490f9cb0f3512f810c3b9e24c0000f56a94c93fabee7ef38da661a6b25888a62c2980000000deac38af3c6ef1488e6088e87242c1e87a1bc8ebdae0201f8110924a6860003202b7d13e8c0c37380003452bef1b104a538960000aac24f173a3af22b8b6500000000000000000054e9b36105b34cf44196a87e00005aa800067d3cde0000000000313c0002a8e00000008c72d209c9800032336e607f9004000136600025f8000273679a04a000000002168bca9a680000000000a069b2a2efb2b40009136722b6a42d536f40002cd6688850ea9a143ef40bab40000000801834ce99b84a4d93450c07aaa0a6080000000000072000000000002e2000000038f80001cc42880000c11800000008da000065c0003cc20002be843800000000000000349cc278304d3c0000000040405239367b307e6000076af2fb26c0000466603000000000006ce0000caca65c4b11412dcd8ef20000000d10841af0bb9980fca52600005d400017c27d2bcd80002f608a28000e1700005b7ad963d600007d01964c851a2e4801cbc0000d44a8e194cebe2d0c84f80009b48000454177c583235e8fd1f726bb88487cc16ec22f2a56b2d39162240ab0ee18b9c04e27c291b0000822000039931ce6a2000084c09f20003b540003cc00000000000171600000000000000654b6c06e91feeefeb0b00003660dba000054d3400000000005e3470b0705745b637e63800f684c08092f0b110264f33c41c21f4825900988d5181c9428bcc0000000a87aa78000000007833e63e42de0380a14650f14ae7e52414000000000008f62cb3ceeec28a5a00018be8ac97badc18660000173c2e68286ee380000002e2ab778000dea995af330eb8d68a752e48222e3679e9c8d0bd2e04
  | 50 => 0x320000b130f7e0001b060002986ebc239800032bc90a0bd29a124443571d82400b38c0002dec000000064818fc1319af20000800d0586ce33f002a85b9ce887bbd38000025e97607a200000001f815220003224dc41b7041b8000ce280000000000000131c00019d800031fccf0000013f101a5d13734cd79f5e8a689604f2a3526d18f947e407fac0106fe3a19f0c0002cd2631835200000006503a28c31aafe0001f380001242a691be000000006650a92b428814cec9b3cbfd1a3a3d580008411d206a80000e64bbce3f59174000397a59d96ac46cbd3a458ac16d62bc084f12af4d28195606b833c1871dc67ff0914aef827e0673428481ab6034eafa6b3900000000c9a16bbb648d6000000023c00000a0c000355c82004e05c0000020a800000026ec00015ea66f14a46640d609f6800078b8000df700000002a86000381c0001b000002c4025411e6015bc785ca00006ec133e0000000000000000000008062572f4c1b3499f2d505e1000006e3bd8e70bd746bea8d4f380d54000000000005e0ab9af8431a0000c0e1560c1a3caeef5118ad74bbdc60e20aa4b20000000037a1cfa27017781e699d00009d61e02000000000038e815f00000000000cf920243f1266a756a6ae9eda798ca12f2260d8000f20800000000002d6000080ea66e35080000001402a0d80000003716bbc91e2207a30af5a00007f700003d1000037d0908becb5066f72e1487ebd44a170d4861d1f68081800088e0dd41441fe082c00006388000c9eb09828584e600011be3e080000ef0000479000006f38988b889420001770061000000000008970000c6887104be9bbae2c139a70a9b0c00018e800015be8670acc2e30000d522bdc5c7b596cc319728369160e0999f243a072454788f0a6316a22260a3ccf790ac8540000f088dd210b954c0bc1c6800c34c065988c0b64a0ea0000eca0000b2e00015a87fe28aa0000000c8b0412000271cecb25908aa81d0022373c9922baa30eab96b2a3cd200032523ea000023aaf4e0002ffe0000be69d01c6e5c28ae6f5c237000027062d98000455286e0000000e1129f0dc798420938b1a29033805669236ab6034e79229a87b121a400a2adeef684c8825a98e0002f689c097605628e1617d98466b107021cd32427be85dc1d3000069ebac048107be961b28adc639dc18fa4020001928cc92f2a87497065088000c33ba20c1680000003a6c0003d32c0700005adb9440968af0d2d000000000009629e50f0c0980cb710c2451095a7d52bfcb89800000033f62c78000192ad440000ff6aa6af5e000145a7c8afd600020ca0003922e328000000000077d000023830c037000000000000b09800013b80000000000ed12216000292617499d4189b02027427f60b939caf1b025cc9d9b169322e6ae7d982600005fad7db9
  | 51 => 0x63a996b4780002c144a8218a627000000000000000000000000071f00000000000000288a00000004a20b0c0a58000dc222828cd1030000219000009c6000091a3ff920e0000000cad95c6aab92b4d3a30fc185115e9e29296762965009d2c82261369c45e336eab8a7e40228d02c162b408a5aa6ec1425e6b149334e73a8b821c843ef002f867803788a2f853e951b836bea894ccaa2f4430a2e2054c361c7178000e1025922b29a9224d1dd00000494d81800000024c63d4aefea0396d400000008278000c953bb60000000ec2293e0000000c25a488c583a8e8e98000031800059c8f4a96d2f36421bda000030dc1863d3600000007ea0000000000008933e22202252e0412560001e7233b0438cb68000000000029839f871ab9c03952026f0f38c458e901e38f83fee40a45a0001b664e907ce71eb9d07d39f1056f0d08e352d700290000000379c5a90000866000003f15d6000373ab798462000079c0f33592a1a84102e2b7e4ace1d34bac000059f256e33c8000000352ac1e85b200026e813da7a410710c825f361018b8000c8d857e2cdb948ce60ca6501b8dc802a7084061c8e9aaaa46ab5802c25fa8d600000008ba00001d480000001b98000240e05d921601094e000000003e02644d7f02c0000000005b801ad6a20be30187f6d30a7646251f060000000d6b8000f3e8a9878396480003074095300080500004fc8b86263b426e8d05a40b1acaccd7000000000000003ae247b2b16491000019404d41e0941ed9e8dba50aabe63fb152ec48a1427f18436244abf20000000b9d111ab938000f3427922ffa640e6a80504429c3293c1efe4b0138635a2f72649868494b0a847b401ce673b1881cf1c14d9c902003725624d885c0b63adc26db3a76e2a30e473280000001d84c9888d0f58046e3a0808273003780001cb6f591d0238b363640b31900002a0828e00006afb476c8a2fd8629803200025a0d969f6011f800000000001f20d7c6a9a7ec00000000001ac62e11ef46842b56580000000029283090000921091cb88aebe48233b09fb8000c602e5234720b2000252a044bc38b4ab24cba5b8740002af65a38ae8215a8b0d668d0686db346a91311494a17624689bbeccea73200015ccd9f9ba6e569b18adc800033d2cf8adaa8ee0002e86c2faaea4c3b4fa41cb24a6e21628d8c08e46cb9338ede0ab22f4027a00017e8000093e6862d486d428f051ca3684209592d9706cc2f5800042222200be81ea1130aba60c987c63985ec0002d804fd8000cee82600000372667b6822520c22aa5a1b270312ee18e30de0000eb60000bee0000000cc40f8e00007ea9e381dc00019423ec14280001cf4b068ae2df8251666aaeccafe80000001992a7e37b6aa03a263271c0a40036e29e99e22ae3904455386227e13b220000c3c1cb9274a
  | 52 => 0x95b1098a219c12e752f389273ae05baaf067671014b1d2b94cddb71adf21c08dc01378b4480000518000000056a575000011d000016c37e2509000035c8000000270e0000000000106c000357e6b49f0475629aa00008a606b289e0000000a120f780003dbed2637022759d5c00015289dca0a4a8700000000000aa48a04df5005800000002db00000000c76d3d0738b8e178a00013ea0000000899ac12d6315086db9f52000065a1e834f66da04b65f785164d4a714e299ace3d69afe941a72c8e1ba1800017cced3a7aa0000000b6a000000003a4000364657d0000d37206e97d18f68f4bdb00000000d581074019800009e06545ae83ca0002adaa2500000000000000240a1ea8000000000027f9b9e2c0855000018ac0003d2a000005e00008ce4dd90aa92dbc9cdcfab44a488e3a53d06765030d7a84401bad06b260679a0dea0f832687d184800000003c9866e1f916cea7a27f400000005952d1e0003c1ecbf800059e32e69ce29a2ba51d5e0002298e323c949528000657b82a1c4a2feee626a680836d2e1c8c3214e0000026949e321a5546a32fec5de00000e4baecdb38d8ac530ddc6ed0000581af7c1c99b0aed6b25e5dbba2ee7680003d0bbde0002bd08be9e7812720eee01108c9b6aaace28af141248000216134e73c0d04eff19d69749ac255400001aa19e03008dbc2e08e58ebd1dc266909b8ef0acf48ee2152cbc21745812ba8c83b9080002b7498bb20c0003d88361b2940002a7631b8f0c7169ab80000df00000000a83a05200000000000000596800000034080002c10e0e868ce9aa7b0ce700000001daa6d5929251d0608e891306000260c6a40736d9d00000000000a37800000000000000000000224e541b5d0000000000000000000000b2f8000339ade223bb16ebb800006fc9f5ce2fa3ba39e030a0000d9000000000000750aadb8ece5d8f125d90a580000ec8d660d924a0909e514998271c26bea290000b7a894eb4680007c9800000029b2c77259600632883a800009dd323ce2292aa967a2c4a04202e9d70c160000000abe1b4416699b25eca226da880004608000da3b1c00000dccead8000f47000000fafa40002a2e56880000000000a5f338e45614269c413227849cd6b5a05467452a888f80ab4273901600023fa6e0b9d2d760000824b53c339307e5ef2016e8a9f98d513ca0d73a2c0a9d0096ed330f476cbd8ca1a30a8e33869c3c180003ddabca3b105be414a50811b092451b847c032996eb6e9eda382b796bd901d854c915c2458f5044928200a6271800009e45981b60ec7800000021949f7803600028fe461800000000000000000c4a2988afdb51c3a30a7c0002e160c202720002e4634daf520003842000129e6178edcc09240cbacb370b5dadd0b68b326ec5044a000000000021c80002
  | 53 => 0xafe749007c0003ac21bd9c920001fb6b4fa24693c9d3668c9010000000009180008ac2d900002e8a17f0eac0001dda000000022ba1b0ded0ece00000003818000000258200000007280000640299200000009c900009d5343eeea2d1600000004e49012030800056a97660000000e6a1fd8527207000024a40002cb200039f227dac36000000088fa91831f09b492012f696c8000839a7d6da1377c77511660002aba0000000a42805adf10000b3c2cfa2cea7848253aea80d98c4940ac0ad55b4b8e478c7043290a65bc2200b0a13c639a8e7ab6c02e8a4f00ec0001e6c637170c0000c12c538000000367800016c28c4bbee0002e2e0912f5c00027a20000000000029ca019bd0c86aa18daf045eadb20e4b4d0000c9e0000000341000001520000000d1b018e0000c3e0fbafca000067a0000000ad49f50a50021849680000000000368a864069131a96f8d7eefd3532d7c125000000000000000000000000000008c400000000c0e1d61ed607bbcd6dbb16b8b0235ee5413256bf6a5f2918800077fa2ba00000006c083da6512fde13127bc0000000ae480006d7b6562dc1c640000648c862a7a2ea17daac716c600016fe4f40bc8000377e80c84b000000900003a9e079000000000007543c0e3c10beae7c04e2acd8330820891e00003b0b3b8aa60002e0ebf2362a1949f5ad240af800015a0ee41ad48fa0000d863282a9f209c2e00744e2533349580810dcb0cf83fe80000000000a070e444d6054e4620e50000000000000000001f4600000000000c9ec608000e7fad563e7842a0253786270000088db1545671a043a4b9a47b380000000ffcd790000172010200034aeea9aa6c0848000f2a23d025b80005f980000000292409b5e04932a82e783152ee90cba338b0d8a5514687c5b30a3c206720000000000362ed6f8000000351a0001548000100e2cc251a00003909881b24b1588521dc8daa113b4920001cccf368000dee000000021600000000d2f00000b6817a000380c8ccbb7ce1a279e040020ea5220d4000389a000000000000002f1b564c0625c8184b9705f8b7260001b08cd500000003a00b4c3ad868c0000000275031138149da2f1612a0000f042f468b4a74e00000000001a86c41bc7e3439bc0ef490ba08a800000000000003abc40f000007f00000000000386120a59796243328caa739000000020d0a991b2625aa882f49222276c1f0e3d31d523321c185713dd449c8f025b32ba2594aa0aab480b4dc118e06308000cf30a8617396082630000e5522ce01a9c3a8e810e63838b5a0000b78000394e000333e4ee000065400000002556ab209c40000000a8984fe00000000cb80000003a7a0002ac469e148eb6f00000000000000210800033500002c70000281eeed00000aea522923a15619a8000bae8000c3b8000
  | 54 => 0xd5b9658c2d22a01ec00007cc95d0945099a626169635d2c941089aea00015e2c7e8000f6b1d60e9a0f2eb398cbc3181bb614aaa2406303820000e760000222f22051408405b6b2380008f3a30ef50a90c0002b04032303400008e600000008ca20ae0000000000191897f9ce2b1437ac70980083c81a4400000000001bde2729ed21f715da8e780002dc9cf2b571d62000267a6a795d2973aae800000009de000091900007710000ecd000000018a269400000000588b330e9a6150000000000000000000000000dba8fc8c50a18e6de1698000040c78f9252e302406e06000076f8000283800000010b44240000bd0b1a60001f9a9ea2bf426a34e099b06200002ea60febcf0e96941c0000000b51bc020000000c87000058e000074aa52e0000f220002f18e6c00002362b461ad8d4cdee985cb29a94aee3200200037aeec7352029bbc34c6f00003d739040000000000117accf0ed4808800087628b6af0bc7cf04b43282115e8000000000007fe78aa1a86fe33421ab81b45000fd45518da400001f8c039c4e0000000d0880000000000dc3196231ebaac1b6af9869d1b74a23b42c07b0feedc92932417a2027a5b19c5c69fc4a9a82a018c0000cdc8000f530000dd207700000f8cb060000ad52e5ad12360e39234a24da2c0c7850000d65000081d2bf80c31e3adef815ce27acfe000089e0000ca807a000074480007e9995c00024b8972800032fb8222e480000000000e4e0000c6797be7c6828e116295a8ff00004f500000d18ee276d0000cc68910ac28000000130cacd0a1095e000000010f600018ca0dd00008dd1ae03300000000374a589800045b000000038ea5859cee000000039000000001a149a50f0ee41b2320000000e6c9cecbb082ee8678000947a11e000376e2debba08ed83d093333060001e4a0000000087acec00000001ec8000ac5000000011cc00000004f214604b830b89358000464800078203e8677100a9a30544a270338c4614dc66b8e74a311d0c7f3b3dcb812d3aa42124a6000a7000003ae03902265298000af79980b24a968e021ef8000100cc429d883168000a2006d000010dc7633d90746026498000000002bb094c1264000000049780000001cba00027fc00034b2d35a0fa38783885f237fa7a998fa62d1dcebb426d02b01beac103d6ec21122ae6eb308ccda7123a03ade7749d4e0000000000224c00000003db0000e888cea0002276c750000edb8000dd9997ebb9000065ea552bc40000000000045080007c8239c8168d56000030e6a59436aa1035e8450c6428bb918a6c058e2f88f3a0001fb000000000000000d138db85eb8dc8878891815010d825b1b2c70784be0001646000000022a0a280002350000000000010aeb7c954ab38318c18780001b58ee8ab8000066e86663f7171400037a4ce5
  | 55 => 0xa2a62bf7387ef3f9adc159343a24b9d9268d178000030927721ab25871ea48cda3cc3dea534aafa5a86a8a0f61e787c40002256791382c6e3b402a70938cc7217045cda3d449ba04a34832a0224990e210232e118000000003c46b413cc00019065c0882664e11caa6023aca7d0af43f1b6ccde83c24156021aa9091c89918920a442cb6bc935724173a548529c162c99682ea4b60ac2f1f744758c46a4e2318ef2b07cf3a0320a770df693b8276066b29ab0eacc04751a1ca490884b5910483ac18902a51152c7603dc7319e60eb18000375bc0c00033209d5947839295569d8050a22b000092600006090000197800002c2fe89f436920c6aacc0c1800086080000000000ee580006212b3221a903e7af1976d08270c08b282cd5184182502cb070d90ce7663b181c10c1801305280dc2c9e1d188b2ac9b9b4c3499589bfabba3a514ea20f9bd29daa4ae0001118254bce23178a18000175a2da00007c71de66d4a59ace43832a948000000000090f12bc0000000000048e3bf0d96000000045280000002fe66392c54a3d203424b0b46000394a4668000000217e1e6a532872938a84f15988bbaaca00014da9df02cc4938072037bd56411a93a00034fe77622047a795f6e2d8c745de80003ab8b4a13c121e8770000101a9d2b81af74d942a58a7ba38ec19ac640428b2803638861eeb50e00026fc33d935a00009ea0fd083ad03145c8118000c4d979e57e36fcd40059c3c6b41406a24a67553c16ae61816c6b208c81891405fa8000d751862000000000006b4e3fa9d4000000000000004b98aa02a58aea090a73074e8000a798e840000afae4f8fe800029ce0000606577161469500000000000c8b80d458400000001af6a7400008fbae2400037320051214000119600000486b02446477a17200000000002b6e00000000002f8ae220000c020000000008c0003b2aee70000dd6b27ceae00003610000e2f00001a7800000000000000000000173e2908e9c000000040d0000ad2808058d8000000009e0000000aff82343f02e9062bb39e9380000ef18000f201f3c000084c21285ba96c302e4db82b4f45023ed35000042d98600000000437921063b08f20002ea058680004c40000b6708fe9ed19de11a285007ea746bfc14aa9fe0da8944b1102e8b36ac66ac663b598ea22e1c34cea172cbee03a65d3825200000000000b42bfa8834000123800026c400021367ee047800000003e291d866c00000003be0d27b9582fda4220002326000220c0003d766022420a1623b2ecf971c3d50f1885a36a82b49ff6f18042823ea8f6326343043f9738b2836aa3712be20000f0aa0c3b36ba8b2ac00003e2de6a3bc5a0150206fbb2e00000003fc0956786a2540000000000000000019ee00027c89460000000000012e0000ae3089c3638abca99800
  | 56 => 0xe246a000000039560000da6103a496eb100008d902b80002a347233cbc1ba25d0d9da0ac83cab9a65f369e87ab32ced21c026fba072b5b3268730b3380ff3216e9437f61a1926a8be057813702bea3ab2580000c9296612b657c26bac8aa2bc55533822b73a36000000000036020480000e51ace2ba7b96e085ac84f57b104d488d222df1a84f68ae7e6b2a8e4bd408087e3831c4f802c491280005658c2e345afa26e526cc3379e6a3ca3712d170ad67eb00000002e60502aa4cd8a184461a00000000f24cd49968a780dda01e0c96f53ae10c4d0df2eaab2fce168000bb180a8c3a8a52875b97c0002ee8ddcb4ba736b2f41de00007a800008fc8ed88362c76c1e0790b8c800058c800047b800000036f0c6e823627085623ef80000000000000223cad99f2ace12d189cfb98e1a9a1c0d8883160000000000000000028ec517978c83a1a0c6eba4342dd80002fcaac2671104a4438000000222ad6d83bed7100004138000d269e0a45d92760000a32000000000000000000000743a4c253036eeb1887c0f15304e000000e69322321eb24aa02102a636010549ad000086f327ef6eb7d8333272e75f1e7ad0137b037f12c6b5000000001d1a0001772000054a00028ca0003274eb48eaa1dfb9e47f5156c6dda9ecd131d9e2c9072a08832088db234c14203eac882df64bb12669d6aa9ca792d2215711f89bd233c00401d63b489ee8b238503f4226044b0c26df31f0052a24c42aa8822adeb4c686b1b7ccb313ce9db261ae9d2ef841f8a4e00018c8000148c9353bf690bb032f312e347c78000d5690fc00026bc49614705779ca20e300002232bce0b880006cc863c2d01b309771e062d880004d81bece2a838a0000000e588228988b7460000000c920f4e5aa244828a887c75188beea72c6c5e90000534affc0000874000026eaf4a71657623300c08d1052e9a5c1893756000102290b0836aca00001a68d66e6000000002b5ed96000028f81c2e0d039e2a30542d22a6a400000002e60000d5b0000dae8590e24948415b93b2a59364030d107c00009381bc937c5780fa4b343afa2b626761ff13b63dd14800b08e246432584ab03b5e1e925689570c6241db20a52e2734b663d06ee5106a2b22658608b6a69f11d16ba93880c900700ea225ae48d29460b2205c77588b41b8815472621b4ce6b11ef0a01980002ace5988000777905a00000002b69ab048f0000b090fe0a97a68af27b9c62180bb24670000b1f97304410004a832cdc0002e4206c35fe0002b30f06aaa60000000f178000e9480003708000718000000000001ed8000f2ab78a2348a748102544c17ad82b5629def69000050ba844331af0cc8110dad2fa3dab6e0c5008e86aa2f91b7a4771eea18591da05b128c8f09d3200000007269384ef20000d1120cedd029fe000000029
  | 57 => 0xbf074e42fa26ab69bbd0a981de881300006c7139c9e80bc41b900000588000c6387982cd2566ee2309a71fb37edc70000000000000007f049026540000000926ba420d594465b9a9661221eba6cfb4ec39a39f4b240fa0b338878b958c2c2c2800032b9af0a571b200001eb835bb8461ea1c6c1d7b96c08cb116efa998a7081326baa3a84bdb8962925314aa3a30ec0003c92765010ec3e885c4da8b2a89a342a7530000db40000b8b013cc9682b0172bc7443c9e70d1b8fb87cf86faba131760728000377a3de65e0e5a2678000f6f00000000000c712ddc7d61300d831bcc30729d80001c724ba0000dca9904dca287a89b1910d9b106400009d2328192cb7f98de000219a00035b8bcbb6622780000522b50200033da204b87c7aa34b024980009410000ed08000f16000052f9ef2d7e9d7af400000ad600004df80000003a7270f883c19932c6ec9209815db17200004d6e95a46e21a000084b886600026e4b3cbbaad9300000000eea0000000000000000038e6f02a53ca94000000019e2859337a07300007978dae4bc09de2372bac1d9826644a8c042518000ad200007c60000cfb09bc6d080000000a76c1c352c8150000000350c6da888884a8c0c0001ebe0001d2246f148251f828801b0d8800000000101db80001a36291021ca0e09664d1082000010c03b005c600000009908b740002898828b730401ba5c00032d85d7b90c57eb7f2c68346800032448ce13dc2672e0a00018ced2305e8df026c88b63cba5f1a8bc9d98368c39a10cca980000002132b910f5e90e8116ad40d265c3af6c682397e37b14303311b840003c36f74b800c4e00000002c98a19bc14000053200039acc81984a0af0fba49f800000002d6000015000002aa000111000015e422ea5e2000387000003aa8e40000edc800048c369000013c2000000000021380000000e9780005108000855133c00006a2e081c1adf0800000000000000000f65800000010320001ce6f18a412d9b80000000000448b3ee0b7b6b6d4e87f4000116a887800000000000000000000376a42826a8000000097e82d05d480000000000f4800009b80000b71877a8b080001e49cb200039ae1bbaec43afaa3208c2638885195461b250cf458e38a7a824c43ea9cc80f34e68408e7c0b480005fb378200000008e22e827ab032c109000000000006e1bc320b53d6a95fa37cdfe0e70f4d000000000009d32ab09bc3a4ecdf3a600f6000000031c2ef8b19861002a8f198000c801ed800037a2793baee05c94ac2e59ae40000000df78000690b49478c1d2c587988651d99f60d08870c5786e0186b7207ef91a08c08534456800000019702d8271a3d880006dc839c9109e0c00000008648000bb38000ade0ce00ca87180000972000316ce5420e20003c0400012dc000000080a800084d23
  | 58 => 0x4bcd503314884aba0a9728ce2c22d7a000102e7a4000000034ee1c3b7ea373842678f0000000144a63c17fe0001eaa1c880006a38a1a4c600cc37ea56489002f2de33d7a49c153c7d8b1ca4e039fab23285e8b82c68715b2c8b30a770422ba405578432d07b3ea0000000000128e1e2b504a7d8000140000000027860001fe836c9dcc0002ccaed18000ee2969a3820000a5d8be00c629dab630000b9b0000cb5b5420000000e27224ad87b31e5fc0000a1d184e61306ac0002a4ada02e50a71120296e80004a42bb290680003848a028b722a8dddb56842005245721fa2dd80ef6e7f2aa28a7049e198bd409eebb30d75800000025a291013ec000000000000001e217f868e35301cc8000cf580001c2a32066d8000000000059b13da6ab2048f52b1ec75d0000e642c86a028000c3c0000698a218686800000000001a28000737800037935e88a91b8020b127c389800026498a46948020cef34f80001280bdc3ad60001ee8f373c26947381e0001bb200025e00001bc41fb80005ad1120b7a2bc60000a46b4b0000ef313fe000000021539ea8d822f6474876295c21aa00000000003b4067f8c8e5c420c8de48000cd385d661c3bb20000c0845faa949631130ea2bcac00024320002fac19184ce57f26eaa25985681b000033a20428d02eac5198000eef84bc000386a0000000489000009602fee71000000000002f3adf887800000030000000000053236647cb00003ed0000eca2b2e5282ae4c499d8ebfe2f620002f9cd23bc8eeef00007948c7ede4217ccbab91c83128ae0001db600000002eb347a60c203e000104c0f5b7449890b901e9b26e28484aaa902fa03b82b00ac914f20003ce4a183994000328cc14ab3a7fb000000022b40000000e02800000021fccbcbdc838a82f6211a25aebcbc705b90d32c0d8990429230430789a29c8800008523c4526045095db03a19027d4ac19788950292e00013360000000b8d9b12aa3000047394100000ec2299826a4a1a520000000000e255a0002a307bb051ef3c968c000098a8ceaeeccaf80005e3827ccb5000000000d2c5622f27298b3ea0497424eeae920002c304ae0aae41e0000834a4d87a13c4c4401042f060000179919e8caa210ac88e969a38366000000029e15520000000c7800000000000bb22700e3d0000d6ca466eb72bc000022d00383c7200036ca0002f2699e0a0629c95b81ac000000000000003d8eb6db566b16a840aeb8e7ec7c2d0eb903c6405ab8ee0001664000000026fb5880f1a1cc32e000040da8420000fc20bd266600016420003770324189268986c6b53a41c03c85f8e2cbba68bd1670a5613a8ad0b45e4e88000000000047a00008eb9028701b196d2da0a612929442ff0cdc93e9f92e591fd604fadd200000000003b62b139e42b8601f27dfb7dac5d08307
  | 59 => 0x91d800000031d06d013de9288000c9c82a4efb31e62b39722eff9d72648afd495d2900f0717960c7b17c6819fb4db78faea5d10c61462dfca2cae1c36db778676aaa83bb0bfa807b4182d584ea0091
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x863554185430432aa98c2a18211e5d46050c10c72a8302860846e72d944304236b96ca218211b9c86510c108dae4328860847671194430423d380ca21821179cc64548108bae6322a40845e73d81520422eb9ec0a90211bdd95214810c5ac8a90a40864d63548520430f324c629021875926314810c3cc8b18a40861d6458c5204316b24c4290219358e6214810c6ac9308a40865563984520431cb24c029021179cc65d08108bae632e840845e73196420422eb98cb210211d5d661908109e2e130c840845f73595420422e39acaa1021179cc65508108bae632a840847575185420431aaa0c2a10219954861508108f2ea302840863954181420422f39eca21021175cf65108108bce6328840845d73194420423b388ca210211e9c0651081087ce832e640843d74197320421f3a0cb190210f5d0658c81087ee8b2a640843c74595320421f3a0ca990210f5d0654c810a98e4a9a640854c73549320423aba8c2990219554c614c810ccaa430a640847975181320432ca98c0990219a548604c81087ce8328640843d74194320423b388ca1902193d95320c810c9aca990640845e73d96410422eb9ecb208211b9cb65904108dae5b2c820863954982410429ab8aa8208214d5d66410410a6aeb2a0820847776550410429bbb2a8208218ddd954104108eeeab0082084f3755804104339baac020821b4dcd6010410da0e6b0082086e3725804104370392c0208211b9cb650c4108dae5b28620864e535883104326a9ac418821179cf65084108bae7b28420864d639482104326b1aa4108211b9ca63940108dae531ca00845e7398a500422eb9cc5280210fdd16194010878e8b0ca00845f73586500422e39ac3280211bdc961940108d8e4b0ca00863554986400429aba883200218dd944190010b62e020c800847771d95400422f398ca20021175cc65100108dce4328800846d72194400429aba882200218d5944110010caaa730c600843e74194300421eba0ca180211b9c8650c0108dae4328600866552986200421f3a0ca100210f5d065080108bce6328400845d73194200423aba8c9880211d5da51840108f2ed28c200863765d91100423abacc8880212d9d26444010c6eca32220086b170191100432bb2ec688021a51936344010caeca31a20086946418d1004333b2ec488021a91936244010cceca31220086a4641891004362318c4880218d1925044010d60c920220084f07650110042e839a8088021781c94044010d60c998220085e272cc110043583206088021ac1932044010ba4e790220086b064081100431db2ec8880218ed946444010cb6cbb1a200865b6518d100434c320c6880219ad976244010cd6ca31220086a8641891004364318c488021ac19361440108f4ed28a20084f27690510042f13906288021749cc2144010
  | 1 => 0x404431a2a2c3a0221179cf65501108bae7b2a808846e72d954044236b96caa022117dcd65501108b8e6b2a808846f725954044236392caa0221179d76350110c3ea9b1a808861c54d8d404422f3a8c6a022187d506350110c38a831a808845e76d4d404422e3b6a6a0221179d853501108b8ec29a808846e75d894044317aa6c4a02218b1536250110c9ea7b12808864c53d8940442373a8c4a02218bd506250110c58a8312808864f531894044326298c4a02211b9db52501108d8eda92808864f63d49404432631ea4a02211b9d852501108d8ec292808864f631494044326318a4a02218d1536150110caea7b0a808865453d854044333a96c2a02219914b6150110c6ea830a808863454185404432ba98c2a02219514c6150110ccea430a808866452185404429c3aa8020221c614d4010110e50a4a00808846e7598b3044317aa4c5982218b15262cc110c9ea7316608864c5398b30442363aac5982218bd5162cc110c58a8b16608864f5358b304432629ac5982211bddb52cc1108daeda96608846f7614b3044236bb0a5982218d15261cc110ca8a730e608863454587304421f3a6ca982210f5d3654c1108dce5b2a608846d72d95304421fba2ca982210f1d1654c1108dee4b2a608846c72595304431a2a6c2982219914b614c110c68a830a6088657531853044332290c298221179d663c8110c3ea931e408861c5498f204422e3aac79022187d5163c8110c38a8b1e408845f76d4f204422ebb6a79022117dd853c81108baec29e408864e63d4b2044326b1ea5902219398c52c8110c9ac62964088634549872044332294c3902218d15161c811087ce9b2a408843d74d95204422f39eca90221175cf654811087ee8b2a408843c74595204422fb9aca90221171cd6548110c68a9b0a408865453d85204431a2a0c2902219514c6148110ccea430a40887185414f10443942a0a588221d214c52c4110e28a9a9c20887145414e10443922a6a508221c91505284110e88a6294208846e7218d5404236b90c6aa021179cc62550108bae6312a80845f73581540422e39ac0aa0211bdc960550108d8e4b02a80843f76550540430eaa2c62a0218b5516215010c3cc8b18a80864e639885404326b1cc42a0218b9916215010c9cc6b10a80864d63588540432ab1cc22a0219958a6115010cb2c7300a808669629805404237390c8a98211b5c86454c108dce5b02a60846d72d81530422fbb2a629821875915314c10c9aa6b10a60861d6498c5304317324c4298218b5926214c10c5cc8b10a60862d64588530432731ac4298218d5926114c10ccac5308a608639649805304237390cba18211b5c865d0c108dce432c860846d72196430423abacc3218213c5c26190c108dee4b2a860846c725954304237390caa18211b5c86550c108eaea30a86
  | 2 => 0xa829221539ce5414910a9ae72a0a48846f7655052442a7b9aa829221531cd5414910c5cca2a0a48864e65d4c5244387aa6a629221c315353149108daed298a48852e7494c5244296ba4a6292211bdd95314910a5ee8a98a48852c7454c5244327328a629221c3d505314910e18a8298a48854e7319052442a6b98c829221595c46414910ad2e0320a48864d6318c52442b2b88c6292211b9d843149108daec218a48854e73d8052442a6b9ec0292214bdd11014910a58e8880a48854f7344052442a639a2029221179cf65d09108bae7b2e848845f73597424422e39acba1221179cf65909108bae7b2c848847571d96424422fb9acb21221171cd65909108bce7b2a848845d73d95424422fb9acaa1221171cd65509108eee2b2a848847b70595424422f39eca21221175cf65109108bee6b28848845c73594424422f398ca21221175cc65109108bceb318848861f5498c424430e2a4c621221171d56310910c3ea8b18848861c5458c424422fbb6a621221175db53109108beec298848845d7614c424432731ea4212219358f5210910c9cc6290848864d63148424431a2a4c2212219914a61109108e8eab08848863454584424431c2a4c0212219a14a60109108f0eab00848843e74d97324421eba6cb992210fdd165cc910878e8b2e648843e74d96324421eba6cb192210fdd1658c910878e8b2c648843e74d95324421eba6ca992210fdd1654c910878e8b2a648847771595324423db82ca99221539cb534c910a9ce7a92648843e74d94324421eba6ca192210fdd1650c910878e8b28648854d7214c32442a6b98a419221539d5320c910a98ea990648864e654c8324432632a6419221c3d51320c910e18a8990648863454984324432a29cc2192219914a610c9108e8eab086488634545843244362992c2192213c1c1610c910c70a9306828865853d814144334296c0a0a218ed506050510cb0a6302828866852181414429a3aa8220a21c5d4d4110510e28a6a0882887275250441443922928220a219614e60cc510c70a9b02628866852d81314431c2a0c098a2196d4c604c510cd0a4302628862f5498831443162a4c418a2193d4e620c510c98a7310628862f5458831443162a2c418a2193d4d620c510c98a6b10628846f76d483144236bb6a418a211bdd8520c5108daec2906288554754c4314438a2a26218a21b1589310c510e88a498862885d0704c43144334294c190a218e1536048510cb0a7b02428863854181214432c298c090a219ad486048510c3ea9318428861c5498c214430faa2c610a218715163085108beeda98428845d76d4c214422fbb0a610a21175d85308510c9cc7a90428864d63d482144327318a410a219358c5208510ac8ea9084288724544842144362b1a4210a21d114d2108510bc0e0908428863454987
  | 3 => 0x516294d10c58a8b14a68864f5358a5344317324c529a218b5926294d10c5cc8b14a68862d6458a534431b322c329a210f9db5454d1087cec2a2a68862f54d8953443162a6c4a9a218bd506254d10c58a8312a68861f64d8d534430e326c6a9a218bd936254d10c58c9b12a68864f63d895344317b20c4a9a218b1906254d10c9ec6312a68863464d855344332316c2a9a218e1936054d10cd0c5b02a68845f7654c534428fba2a629a21471d15314d10a9ee4a98a68854c7254c534428f3a4c629a21475d26314d10a9ce5318a68854d7298c5344237390c229a211b5c86114d10c3ccbaa0a68845d7695053442a7394a829a21535ca5414d108beecaa0a68854f7255053442a6392a829a21879945414d10a9ce4320a68854d7219053442aab88c829a21565c06414d10c9ac4310a6885557118853442a7396c029a21535cb6014d10a3ee8880a68851c744405344237396cba1a211b5cb65d0d108dee4b2e868846c725974344237396cb21a211b5cb6590d108eae3b2c868846f725964344236392cb21a211b9cb6550d108dae5b2a868846f725954344236392caa1a211ddc56550d108f6e0b2a868846e72d944344236b96ca21a211bdc96510d108d8e4b28868846e721944344236b90ca21a211b9d66210d10c5ea9310868862c549884344327a9cc421a219314e6210d108d8eab10868862f5458843443162a2c421a2193d4d6210d10c98a6b10868863454984434432a29cc221a211d1d56110d10c68a8b08868863854980434432c29cc021a211e1d56010d108bce7326a48845d7399352442a739ca9a9221535ce54d4910a9ee6aa6a48854c735535244387aa6a7a9221c315353d4910a5ce929ea48852d7494f5244297ba2a7a92214b1d153d4910e1ea829ea48870c5414f52442a739cc9a9221535ce64d4910c9ec731ea48846e7610f5244236bb087a922153dcd60d4910a98e6b06a48861f5498e524430e2a4c72922187d516394910c38a8b1ca48861e64d4e524430eb26a729221879905394910c3ac829ca48862e64d4a5244316b26a5292219398f5294910c9ac7a94a48861e6498e524430eb24c729221879916394910c3ac8b1ca48863664586524421f3b6a8a92210f9d85454910c3ea9b1aa48861c54d8d524430faa0c6a92218715063549108bceda9aa48861f64d4d524430e326a6a9221179d85354910c3ec829aa48861c6414d524430fb26c6a9221871936354910c3ec831aa48861c6418d5244317b26c4a92218b1936254910c9ec7b12a48864c63d89524431a326c2a92219518f6154910c70c9b02a48865863d815244237bb2a4292214bdd15214910a58e8a90a48854f7354852442a639aa4292214b9d26214910a5ae9310a48854e7398852442a6b9cc429221179cc61149108bae6308a48862e65d505244236bb4
  | 4 => 0x9eca990658864d654c832c4362992c2196218e9516010710c9ca6b10638864d5358831c4362b126218e219358e5208710c9ac6a9043886c56348421c421f3b4a8a06218d9506150310c6aa830a818843d76d5040c432729ac5986219354d62cc310a9ae429c618845e7694d30c422ebb6a618621535c8530c310c9ac7296418864d6354b20c42a6b98a5106211b9da52483108daeda90418854d7314820c4237394c7aa4211b5ca63d52108bce7316a90845d7398b548421fbb2a82a4219c5866015210ce2c3306a70864f5358a538422fbb2a629c21535ca6314e108dce5b2c870846d72d964384237394caa1c211b5ca6550e108dce5b28870846d72d944384237390ca21c211b5c86510e10ce2c3306a50864d63d4a5284237bb2a429421535ce6214a108bce7b2c850845d73d96428422f39ccaa1421175ce6550a108bce7b28850845d73d94428422f398ca21421175cc6510a1087ce932a650843d7499532842a7396a699421539cf524ca10caea630a650866752185328421f3a0ca194210f5d0650ca10c9cca990650864c654c8328421f3b4a8a0c210f5db54106108eaedaa083084b576d5041842d9386a820c214d5db5410610c6aedaa0830873270d5041842d9380a820c21535ca53cc6108bced29a630854d7294d318422ebb6a618c2193d4d620c610c98a6b10630854d7394b21842373b4a490c21535ce52486108daeda90430864d63d482184326b18a410c218d9516110210b62e020881085b07150040842a6b94a718421535ca530c210caca6b08610854d7394a20842a6b9ca4104219994961082108dce531ea88846d7298f544422f39cc5aa221175ce62d5110a5ce531ea88852d7298f544428f39cc5aa221475ce62d5110a3ce7b06a88851d73d835444297396c1aa2214b5cb60d5110c3ea931ca88861f5458e5444317aa4c52a2218bd516295110c9cc7314a88864d6398a544432731ac52a2219358d6295110c3ec9b1aa88861f6418d5444317b26c4aa22193d8f6255110c98c7b12a88862f641895444327b18c4aa2219318c6255110caec7b0aa88865463d855444333b16c2aa2219918b6155110cb0c7b02a88866862d81544421fbb2a82a22147dcd5415110a38e6aa0a88852f725505444296392a82a221479ce6415110a3ae7320a88852e729905444296b94c82a2214b9c86315110a5ae4318a8885357118c544429cb80c62a221479cc6215110a3ae6310a88853571188544429cb80c42a22147dcd6015110a38e6b00a88852f725805444296392c02a2211b9ca64d4d108dae5326a68854e7295353442a6b94a9a9a2153dc954d4d10a98e4aa6a68854e7299353442a6b94c9a9a2193d8a62d4d10a9ee4b06a68854c72583534430f326a729a21875935394d10c5ea9314a68862c5498a5344327a9cc529a218bd
  | 5 => 0x54e72d4d320822f3b0a699041475d0534c820aaae229a641046c765513208316322a899041531cd544c820b94e1a9a641046e7614d3208296ba0a699041595c4534c82099cec29a641058d7414d32082e2b88a699041539d8534c820c9cec29a641070e7414d32082a6ba0a699041c35d0534c820a1ae829a64107467114d32082a6b88a699041d15c4534c820a8ae229a641054e7014d32083a5380a699041531d6434c820998eca1a641054c7550d32083463228699041c3551434c820b90e0a1a641045f7654c32082a6b92a619041b24ca600c820c98c6992a210564714c9510823bbb2a2288418d5915114420caac6a88a21045f73595410822e39acaa0841179cc65504208bae632a8210534715514108316aa0c4a0841335cc6250420a68e8a8a821066462545410831bb2a82208418d5954110420b60e0a08821043f74595310821e3a2ca988410f9d0654c42087ae832a621064d53189310832632a6498841711c5324c420cc8c4a8a6210745325453108364990c0988419c544604c4208daea32442104eb7058e2108267b9ac1108419558e5108420caac6a8842104cd731902108274b80c8108413a5c3630842099aed3184210565759842108362b1ca2108419358d5108420d8ac6a884210567765442108333bb2a21084199d8d5108420e8cc6a8842106656354421083a2b1aa2108419158d5108420d92c730042106ca6358021082a6b9885280419398d3294020a9ae610ca01062d5498a4008266b9cc520041179cc65100208bae632880105b0715004008326a9cc5180410f9d0650c02087ae8328601064c654c83008266b98c9900411b5da5288020a9ae729440104797694a20082e4b9ca510041725cc4288020b92e610c401046d759912008237baac6900412b1d163480209c8e2b1a40104cd73d8120082753b66090041b258c3048020b94e729240104ea760c9200832731cc5aa6219358e62d5310c9cc6b16a98864d6358b54c432b31cc3aa6219558e61d5310cccc530ea9886656298754c4237390c6aa6211b5c863553108bce6312a98845d7318954c421fbb2a82a6219c9856015310ce4c2b06a78845f7654c53c4326a9ac429e219398d6214f108dce532e878846d7299743c4237390cb21e211b5c86590f108dce532a878846d7299543c4237396ca21e211b5cb6510f108dce4328878846d7219443c428eba4a621e219394d6210f10c9aa6b1087886726158352c4237bb2a4296219358d5214b10c9ac7310a58845e7399742c422eb9ccba1621179cc6590b108bae632c858845e7399542c422eb9ccaa1621179cf6510b108bae7b28858845e7319442c422eb98ca216214b5d25210b10c9ac7290858864d6354842c421f3a4ca996210f5d2654cb10a98e4a9a658854c7354932c421f3a6ca196210f5d3650cb10c
  | 6 => 0x44832bb18c2aa2419518c6155120ccec430aa89065863d81544833830ec0aa2410fdd95415120a38e6aa0a89053471550544822f398c42a241175cc6215120c38c9b1aa69062c64d89534831bb26c2a9a418d1936154d20c6ec830aa69063464185534832bb18c2a9a4199d886154d20c70c9b02a69067061d81534822fbb2a629a41471d15314d20aa8e2a98a69047671d97434823ab8ecba1a411bdc965d0d208dae5b2c869047671d96434823ab8ecb21a411bdc96550d208eee2b2a869047471595434823db82caa1a411b5cb6510d208eee2b288690474715944348237390ca21a411b1d56210d20c5ea8b10869064f53588434832629ac421a418e15160d0920cb0a6b06649064e654c8324823bbb2a228a414d1d15114520aa8e6a88a29045f73594414822e39aca20a41179cc65105208bae632882905357115041482373acc420a414d5d05110520a6ceaa08829053475504414831c2a2c020a419c145601052087ee8b28629043c745943148327a9ac418a419314d620c520ccac5a88629045f73595404822e39acaa024187d506350120c38a831a809062c54d89404831baa0c2a02418d1506150120c9ea6b16609064c5358b30482a6b94a718241471d1538c120aa8e2a9c609043f74595304821e3a2ca98241179d8534c120a9ae529860905597094c304822fbb2a618241471d1530c120aa8e2a98609052c7454e20482b238aa710241179ce62d50208bae7316a81054d7398b540821fbb2a82a041875516315020c6aa8b08a81061e6458c5408326b1cc42a0419598e6115020caac7308a81063664584540832b31ac22a0419558d6115020cccc4b08a81067161980540822fbb2a629841875915314c20caaa6b08a61061d6498c5308316b24c4298418d9926114c20c6ac9308a61063664584530831ab22c2298419598d6114c20cccc4b08a61047671197430823ab88cba18411d9c46590c208eae232c861046d7598a430823bb8acaa18411d1c56550c208ece232a8610475711954308236ba8c4a18418b5506250c20c9aa6312861047975181430831caa0c0a18411b5c96510c208dce4328861047671194430823ab88ca218411b5d66210c209d6e0b1e84104cf73583420822f39ecb21041175cf65908208bce7b28841045d73d94420830f2a2c621041875516310820a5aeb320841052d759504208237bb2a8210414bdd95410820c5eecaa0841064d6598c4208386aa4c6210418b5516310820c9acab18841070d5458c4208327aa2c621041a39516310820c9aa8b18841068d5458c4208306aa2c621041b258e60108208deeab0084106ca63580420828eba0a799041555c453cc8208daea32464104e9701923208236bb6a9190418b191548c820a5ae829c64105657114e3208237baac1190413add5608c820cd6eab04641
  | 7 => 0x42a6419a98960d4f20aace3aa4a79055571d5253c830eb20c929e41539c86494f20a3ce8314a79051d7418a53c82ab388c529e41555c46294f20a9ce430ca7906556118653c822f3b6a8a9e41559c75454f20aaae3aa2a79045e7615153c82adb82c8a9e41875906454f20a9ce4322a79055b7058553c82a7390c2a9e41955846154f20a3ee8b02a79051c7458153c82abb8ac0a9e41551c56054f208beeca98a7904767119643c823ab88cb21e411d9c66550f208eae332a879051c7454d43c832ca98c0a1e41475d25310f20c9aa7310879064e5358843c8326a9ac421e41175d66310b208beeab18859045d7694c42c822fbb2a621641c394d4210b20cb2a7304659065a5398032c830f324a7a8e418759253d4720c3cc8a9ea39061d6454f51c829b3a6a328e41175da53147208beeca98a3904777654451c822f39ccba0e41175ce65d07208bce732c839045d7399641c822f398caa0e41175cc6550720cb4a7b02839065a5318141c822f39cca20e41175ce6510720a6ae32a0839064d5398841c8326a9ac420e414d5d25110720a6eeaa0883905357550441c838b29a8220e41c554d4110720b60e0a0883905547154d31c832ca98c098e41555c6530c720c9aa7310639064e5358831c8326a9ac418e41175d663087208beeab18439045d7694c21c822fbb2a610e41d194d2108720c9aa7316819064d5358b40c822ebaec6a0641175d463503208bced29a819045c7654d40c832729ec4a06419354f6250320c5ca8312819064e5318940c8326a98c4a06419594f6150320caaa7b0a81906365418540c831aaa0c2a06419594c6150320caaa630a819071a5350040c82d838a80206419354e62cc320c9ca6b16619064d5358b30c8326a9ec4986419354c624c32087eecaa0a91066962983538822fbb2a629c411d9c76590e208eae3b2c871047671995438823ab8ccaa1c411d9c46510e208eae232887104cf73583428831caa0c0a14411b5db5410a20c9acab18851064f5458c4288326aa2c6214411bdd9548ca20cb2a6302651062c64d5132882a739ea8994411b9da534ca20a9ced29a651064e7694d32882a6ba4a699441535c6534ca20a9eeb21a651054f7550d328834632286994411ddd951146208bce7b2e831045d73d97418822f39ecb20c41175cf659062099ae631283104e872580418821f3a6cb98c410f5d365cc620c9eca996631064f654c931882e238a6498c4133dcd608862099ae632043104e9701902188326b2ac610c419358d510862099ae7314811062e54588408832729ac418441335cc64c8220c9acb31e411064d6558f208832cb2cc7904419659563c82208dae531ea89045f73582544822e39ac12a24187d906355120c9ec7b12a89064c63d89544832bb1ec2aa2419518f6155120ccec5b0aa890637641855
  | 8 => 0x565109308e8e2b28849861f5458c424c326b1ea4212619358c5210930c9cca990649847776544514c29a3a2a228a61591c951145308dee4b28829846c72594414c237390ca20a611b5c86510530a6ae22a0829845e7598c414c29aba0a220a614d9d54110530a68eaa08829863854580414c33828ac020a610fdd16508530878e8b28429864d63d48214c326b18a410a619558f5108530c38a9b1a809862f54189404c3162a0c4a02618dd506150130c68a830a809854d7298f540c21fbb2a82a0618b5516215030c6aa8b08a81862e64588540c32731ac42a0619998a6115030ccac5308a81863664584540c32b31ac22a061999896115030ccac4b08a81867161980540c26db82c5a186133dc960d0c30c5ca8b10861862d54588430c28ebacc821861475d65410c308beecaa0861851f76550430c30fbb2a821861935966210c30e1aa9310861861d54588430c326b2ac421861c35516210c30c9ea8b10861868e54588430c326aa2c421861a35516210c30c1aa8b1086186c962980430c22fbaac021861b29896010c308deeca90a41862d64548520c332a92c2290611ddc565508308e8e2b2a841847671195420c23ab88caa1061875506350830c98c6a92841863954181420c26cb80c9990618719154cc8309b6eab06641865b75583320c22e3b2a89906187191544c830a98e4aa264185ca70d49320c2673b0a499061635d0524c830b8ae229264184cc76509320c2a63aa8499061a3191424c830e1aa8a1264185c870509320c364994c019061931893254430aa8e2992a21847776544510c31ab22a2288619958951144308dee4b2a821846c72595410c237390caa08611b5c86550430a68e2aa2821861d5418d410c266b90c6a08614d1d15150430ca8c6a8a821863765504410c31ab2a82208616c1c141104308baea32462184db7058a310c267b92c1188619958a510c430ccac4a8862184cd72190310c26cb80c818861555d6610c430d8ac5288621864d62544310c362b12a21886155dd9510c430caeeca88621874662544310c32ab12a218861d1589510c430c8ac4a8862186c962980310c365312c018861365c06388430ca8c6a8c421843f74595210c21e3a2ca908610f9d0654843087ae832a421864c63549210c2663b26490861931953248430b88e2992421865463545210c3a2992a290861b24c86048430ce2a2302421854d7210e500c2a6b90632806187552639003099ae531c80185b071500400c266b90c998061175da538c0308f2ed29c60185c97294e300c2e4b908718061725c8318c0308baeb32260185ca7294d300c26d3b064980619398e62d5320c9ac7316a9906566398754c832ab1cc3aa6419998a61d5320cacc6b0ea9906556358754c8333312c3aa6414d9c75495320a6ce3b22a99043f7655054c8326b1cc
  | 9 => 0xcc530ea9986656298754cc32b31ac3aa6619998961d5330ccac4b0ea99853671d5254cc29b38ec8aa6610fdd95415330c9cc6b10a99846d7598843cc237baac421e61599c75494b30acae3aa4a59862d6419252cc2a7398c9296614b9d06394b30a5ae831ca5985667118e52cc2b2b88c7296611b5d84394b30e1a8621ca59854e7318652cc332b08c3296611b9db5454b30acce3aa2a59856571d5152cc2373b0a8a96615adc16454b30c5ac8322a59854e7319152cc2373b086a96615adc16154b30a9ce630aa5986656118552cc297ba2c0a96614b1d16054b30acee2b02a5985647158152cc237bb2a4296614b1d15250b30cd2a4302859852d7494842cc326b1ca4216619398d5210b30c9ac6a9085986695298332cc335294c0196618b99252d4730c5ac9296a39862e6454b51cc316b22a5a8e614d9d351947308daed290a39846f7654851cc23bbb2a228e611b9ca65d07308dae532e839846e7299641cc236b94cb20e611b9c865507308dae432a839866a52d8141cc335290c0a0e611b9ca65107308dae532883985357195041cc32731aa420e619358d5210730a6ae928883985377550441cc29abaa8220e61c99494110730e4aa4a0883985b07050441cc236bacc418e611bdd5620c7308daed290639846f7654831cc3a32926218e61591c55248730cd2a4302439864d6394821cc2b2b8ca410e619398d5208730c9ac6a90439864e6354b40cc326b1aa5a06618795063503308daebb12819846d7518940cc2373b4a4a066193d8e5250330c98c7292819846c7654940cc327b1aa4a06619318d5250330ccca5b0a819866552d8540cc31b2a0c2a06618d5506150330ccca430a81986655218540cc39529280206616c1c5401033087eecaa0a9184cf72583438c31caa0c0a1c61175db5410e30c9acab10871864f54588438c326aa2c421c611bdd95214a308ece3b2c851847571d96428c22fbb2a99946187193544ca30a9ce5aa2651854e76949328c3273b4a499461535d2524ca30a9ae3292651854f75909328c2a7baa8499461a3191424ca308eeeca88a31846e72d97418c236b96cba0c611b9cb65906308dae5b2c83184cd7218d418c26c39ac020c6133dc9608c63099ae432063184d970190318c326b2ac418c6193589510c63087ce9b2e431843d74d97218c327b2a6590c6193d953248630b88e299243184cd7298e408c30f2a2c620461335c864cc230c9acb316611864d6558b308c334b2cc5984619a59562cc230c9ec7b12a89862f64189544c327b18c4aa26195d8f6155130ccec5b0aa89866462d85544c31bb20c2aa26195d8c6155130ccec430aa89866462185544c334316c0aa2619c187605513087eecaa0a89852c72550544c29a38aa82a2618e15160d0d308deeca90a49852c74548524c2b238aa4292611ddc
  | 10 => 0x65853d814150334296c0a0a819614c6050540cd0a430282a067351181415038ba9a8220a81c514d4110540e4ea4a0882a0724525044150237b92cb98a811b1c965cc5408dee4b2c62a046c725963150237396ca98a811b5cb654c5408dee4b2862a046c725943150237390ca18a811b5c8650c540c3cc829862a046e759883150327a9cc418a819314e620c5408d8eab1062a064f53588315032629ac418a811bddb520c5408daeda9062a046f761483150236bb0a418a819998b510c540ccac5a8862a063664144315031ab20a218a8199988510c540ccac428862a065853980315033828cc018a8117dcd65c85408b8e6b2e42a045f73596215022e39acb10a81179cf65485408bae7b2a42a045f73594215022e39aca10a81179cc65085408bae632842a045e7598c215022e3aac610a8117ddb53085408baeda9842a045f7614c215022ebb0a610a819398f5208540c9ac7a9042a062e641482150327318a410a819358c5208540cacc7a8842a065563d44215031b320a210a818d5905108540cacc628842a0655631442150334294c010a819c1466008540e90a629680a07505314740503b0290a3a0281c314c5290140e2ea628c80a0714531464050393a90a320281c914851901408dce430aa62046d72185531022fbb2a6298819354d6214c40caaa6b08a62064e535884310326a9ac421881179cc61548408bae630aa42046f765485210326b1aa429081995496114840c9ac7290842064d63548421023bb8aca990811d1c5654c8408ece232a642047571195321030e322a699081531c9534c840c58c8a92642054c73549321032ca98c0990819a548604c840c9eca990642064d654c83210237390c6a88811b5c863544408bce6312a22045d73189511023bbb2a2288819558d5114440ccac4a88a22053575984411029bbb2a2208818ddd95110440976eab00822063b75580411034db9ac020881a61cd6010440d56e4b0082206a872580411025cb84c9988811bdc9654c4408d8e4b2a622046e721953110236b90ca9888187191534c440c68c8a8a6220671511813110237396ca188811b5cb650c440972e1326422045f73595211022e39aca90881179cc65484408bae632a422062c64549211031a322a2908819c54460484408bce7b28422045d73d94211021ebb4a9200811e5da5490040c3ecbb1a802061f6518d4010317b2ec4a00818bd946250040d18c6312802063765d85401031bb28c2a0081a5d8c6150040d28c630a80206a7621854010352310c2a0081ac5c06150040cb6cbb1a802065b6518d40102d539086a00819ad976250040cd6ca31280206c86318940102cd39884a00819cd976150040ce6ca30a80206b3641854010368318c2a0081b81886150040974eda0a802064e6398b54cc32731ac5aa6619598e61d5330cc
  | 11 => 0x5032a298c2a92811bdd95214940a9ee6a90a4a054c7354852502b3b8aa429281591c55214940c9ccba98a4a046d7694c52502b338ca629281595c653149408deeca98a4a05677154c52502b238aa629281939945314940a5ae8318a4a064d6318c52502b5b8286292815a1c143149408dcec218a4a070d4310c5250296ba0c229281539cc6114940a9ae6308a4a05697018452502a739ec029281535cf6014940a9ee6a00a4a054c735005250334294c1212819614f6050940cb0a630284a066b52181425022fbb6a62128117dd85310940c9cc7a9084a064d63d484250346b1a8421281c314d4210940b50e0a1084a047771597325023a38acb992811ddc5658c9408e8e2b2c64a047671d95325023ab8eca99281539cb534c940a9ce7a9264a047771594325023a38aca192812e1c1640c940c3cc829864a054d7214c3250317320a419281535cc520c940a9cea99064a054c754c8325032732a641928193195320c940d1ac899064a046e7298f5150236b94c7a8a81179ce62d45408bae7316a2a05667294f51502b2b94a7a8a8159dc953d4540ac8e4a9ea2a074753d4b51503a229ea5a8a81559ce52d4540aaae7296a2a05577354b51502aa39aa5a8a81d1d4c52d4540e88a6296a2a05667298f51502b2b94c7a8a81599c843d4540acae421ea2a05567398b51502aab9cc5a8a81559cc42d4540aaae6216a2a0745320cb51502ab39ec1a8a81555cf60d4540acce5b06a2a056572d835150327a9cc528a819314e6294540c9ea6b14a2a064c5358a515032731ea528a819358f5294540c9cc6294a2a064d6314a515032b31ea328a819558f5194540cccc5a8ca2a066562d46515022f3b6a6a8a81179d85354540c9ea7b12a2a064c53d895150327a98c4a8a819314c62545408dceda92a2a064f63d49515032631ea4a8a811b9d85254540c9ec6292a2a064c63149515023bbb2a228a8155dcd5114540aa8e6a88a2a05677254451502b2392a228a819599753145408eaed298a2a05667294c51502b2b94a628a811ddd95314540acee4a98a2a05647254c515032b328a628a81999975214540e8ea7a90a2a074453d48515023abb4a428a81559ce5214540aaae7290a2a04777654851502abb9aa428a81551cd5214540cccca290a2a07475314851503a2298a428a814d5d06314540acce4318a2a05657218c51502b8b80c628a815cdc14314540ae0e0a18a2a07154310c51502b33908628a81595c84314540a6ae8310a2a05567318851502aab98c428a815c5c06214540ae6e0a10a2a05707050851502ab3988428a81555cc4214540e4a84210a2a0536740c8515029aba06428a81d14c83214540aaee6b00a2a05547358051502b3b92c028a81591c96014540aaee6a00a2a05547350051502b3b928028a81591c94014540ce0a330482a0
  | 12 => 0x2104317dd953108218baeca988410f0e53508420872aa9ac3190430f9d3650c82187ae9b286410e4f654c83208726b2a64190439594d610c821c9aa73148210e4d5358a410862f39cca20843175ce65104218bce63288210c5d731944108726a9cc4208439354d6210421e2ca6a088210f15535044108726a9cc5188431bdd5628c421c9aa6b146210e4d53988310872729ac4188439354d620c421caaca9886210e4d539832108636bb4a5108431d5da52884218dceda9a4210d4d7594d2108727b2ca69084393d955348421e88e2a9a4210e4d53d8521087a2a9e8290843d154c4148421e8aa798a4210d65750c52108726a98c09084395d965348421caecaa9a4210f455394921086e33988490843595d732484218bee6b24a010c5c73592500862ebb4a628043879925314021c3ac9298a010c5f7654c500870f322a6280438759153140218f6eca80a010e3964540500862fbb2a629e819354d6214f40c9ca6b1087a064d5358843d0346a1ac421e811bdd95214b40c9ac6a90a5a064d6394842d0326b1aa421681a358d4210b40a98e4a9a65a054c7354932d023b38eca196811d5c7650cb40c9eca99065a064d654c832d0346b2264196811b9c863547408dae431aa3a045e7318951d022eb98c4a8e811ddd951147408dce532c63a046d7299631d0237396ca18e811b5cb650c740aaae329863a064e5358831d0326a9ac418e81179ce65887408bae732c43a045e73d9421d022eb9eca10e819358e5208740acae329043a064d6354821d0327a9ac529c8117dd95314e40a9ae529c872054d7294d4390326b1ea5294811bdd95214a40a9ae7294852054d73949429032732a64194811ddd9511464096aeda8883205b270d4441902d9380a220c811b9cb65cc6408dae5b2e632046e72d943190236b96ca18c81179cf65c86408bae7b2e432045e73d94219022eb9eca10c811b9ca61d4d408dae530ea6a064f6298b53502a7394c3a9a81535ca61d4d40a9ee4b06a6a054c725835350327a9cc529a8193d4d6294d40caea730ca6a065753586535022fbb2a629a8153dc95314d40a98e4a98a6a05577154c53502aa38aa629a81475d06214d40c9ac4310a6a051d7418453502a7390c229a81535c86114d40ab2e0308a6a054e72d8053502a6b96c029a819614e6090d40cb6a630286a05987050c4350327a9cc421a8193d4d6210d40d1a86b1086a045e73987525022eb9cc3a9281599c653d4940acae329ea4a05677154f52502b238aa7a928193d8e63d49408dcec21ea4a054e7398752502a6b9cc3a928153dcd60d4940a98e6b06a4a064e63d4a5250326b1ea52928195d4e6194940ca8a730ca4a066752986525032ba9ac3292819514d6194940ccea4b0ca4a045e76d4d525022f3b0a6a928195d4f6154940ca8a7b0aa4a06575318552
  | 13 => 0x5314e218f4e132a8710c7970995438863d380ca21c431e5c06510e21c6aa830a8510e5553185328862f3b0a698c4317dd9530c621c9ca6b106310e4d53588318863dbb2a02844387d906355121c9ae431aa890e4c63d89544872a31ec2aa24396d8f6055121cb0c7b02a890e3b64181544872db18c0aa2439618c6055121cd6c4302a890e7361181544861fbb2a82a243471cd5415121a70e0aa0a890c5f73580544862e39ac02a243871936354d21c58c9b12a690e3464d85534871db26c0a9a438e1936054d21c76c8302a690e3864181534872db18c0a9a439ad886054d21ce6c2302a690c5f7654c534868e3a2a629a43561c15314d218f4e1b2e8690c7970d97434863d386cb21a431e5c36590d218d8eab148690c74755864348637b92caa1a431ddc56550d218f6e0b2a8690c78705954348636b96ca21a431edc16510d218f0e0b288690c6c755884348717aa2c421a438b1516210d21c9ea6b108690e4c53588434867238ac421a438d15161d0921ca8a6b0e6490c6f7655232486a639aa9192435a1c1548c9218d8ecaa26490d4c7355132486b4382a899243539d7634c921a9ce729a6490c6e7614d32486a73b0a699243939d8534c921a9ae829a6490d4e7014d32486a63ac8699243c3d52434c921b8ae321a6490d4c7550d32486733a8c299243999d4614c921c58a8b168290c5f73595414862e39acaa0a43335cc6250521c98a6b166290d4c754cb31486e238a6598a430fdd1654c521878e8b2a6290d4c754c9314872632a6498a431edd95014121a70e8a80a090d5873540504862fb9ac828243171cd6414121ac8e2990a090e4d6398b540872ab1cc3aa04317dcd60950218b8e6b04a810c6e7218d540861fbb2a82a0438e5516015021c9ac7310a810e5a63980540872cb1cc02a0438e9916015021cb4c6b00a810e59635805408735312c02a0439c9856015021cd0e4b00a810d5a7015253086acb80a929843875906494c21a9ce4324a610d1e7418a530868eba0c529843539cb6094c218bcedaa2a610c5e7615153086ad380a8a9843565c05454c21a98e4b22a610d547159153086adb82c8a9843561c16454c21c3ac8322a610d4e7219153086a7396c0a984347dd16054c21a38e8b02a610d4c7258153086aa38ac0a984317dd95314c218f4e032e8610c79701974308637390cb218431d9c46590c218f6e0b2a8610c7870595430868e3a2a6a18439354f6250c218daea3128610e4d53189430872aa9ec2a18431d5d46150c21caaa630a8610c6e72194430863d380ca218431e5c06510c21a3ae92988610c6d759884308726a9cc421843395c66210c21c9ca6b108610e4d53588430871aaa4c3210439554e6190821caaa6b0c8410c5e73d94420862eb9eca21043175d663108218beeab188410c5f7694c420862ebb4a6
  | 14 => 0xe4aa26498d5870551324c6a73aec499263539d8524c931c9cec2926498d4d74149324c6a7380a499263531d6424c931e1ea92126498dc571909324c6a63aa8499263359d4614c931cacea30a6498e1c5458f414c666b90c6a0a631edd95014131a70e8a80a098d6872540504c637b92c8282631b1c96414131aa8e2990a098e4e6358b540c732b14c3aa0631bdc960950318d8e4b04a818c3f76550540c71caa2c02a0639398d6215031cd4c5300a818e6962980540c71d322c02a0639698d6015031cd4c4b00a818e6962580540c73930ac02a063961cd6015031c6aa930c8618c6d75988430c637baac4218635a9c05494831ad2e02a4a418e2d64192520c6a7398c9290634b9d06394831a5ae831ca418c6d7610e520c786a188729063539cf60948318dcedaa2a418c6e76151520c6b5380a8a90635a5c05454831a98e6b22a418d6471591520c6b5b82c8a90635a1c16454831c5ac8322a418d4e73191520c6b338c86a9063595c643548318dcec21aa418d4e73d81520c697ba2c0a90634b1d16054831a98e6b02a418d6471581520c637bb2a4290631edc165508318f0e0b2a8418d2c74549420c727b1aa4a10639318d5250831ccaa5b0a8418e6552185420c66ab8cc6210634b5d25210831c9ac72908418e4e63548420c726b1aa4210639954961cc831ccca4b086418e4e6354a410c726b1aa5208639398d5210431c9ac6a908218f2652504410c792a9282208639354a60cc4318baed29c6218c757694e310c727b2ca49886393d95524c431e88e2a926218f4552d05310c7a2a90829886393548604c431b8ce421a6218e6765949310c733b2aa498863d194d524c431aaaeb1926218c6f72592500c636392c9280631b5da5214031c5cc9290a018e2d64948500c637bb2a4280638b9915214031c5ac8a90a018c7b76540500c71cb22a028063535ce62d5321cccc4b0ea990c5f7358254c862e39ac12a6430fdd95415321c3aa8b18a990e1e6458c54c8726b1cc42a6439998961d4f218beeca98a790e1d6454c53c870eb24c629e438b5926214f21c6cc8b08a790c7a7099543c863cb84caa1e43879516310b21c3aa8b188590e365458442c868eba0a7996434b5d0538cb218bcec29a6590d1d7414d32c86373b6a899643531cd544cb21b8ae3a9a6590c6e7614d32c8696ba0a699643339d8534cb21b1ae829a6590d4e7614d32c87273b0a699643c39d0534cb21a9ae829a6590f0d7414d32c8686ba0a699643d15c4534cb21a9ce029a6590d4c7590d32c86a63aa8699643c3551434cb21b8ee2a1a6590c5f7654c32c8762992c2196438b550625072199ae63128390e4d5318931c86e238a6498e43b1589310c721c9cc6994a190c7b7654050c8732b14c3aa4430fdd954152218bee6b00a910c5c735805488732b14c3a9c4317dd9
  | 15 => 0x5953580531072729ac4218839354d6210c41d1a86b108620c6f765485210726b1aa4290839a5496014841c9ac72908420e4d635484210746b1a84210831edc1654c8418f0e0b2a6420c7a70195321063cb80ca990832d5c4644c841c38c8a9a6420d4c7254d3210716322a499083531cd524c84196ae830a6420e55531853210732a90c2990832d5c6640c841c9eca9906420e4d654c83210746b2264190832d5d2610c841d8a64b086420c3d76952411063abb4a920883699c84350441b4ae421a8220d967310941106cab9884a08838d5d7655044196ce1b2a8220e3676d95411069abacc6a08834ddd56350441b4ee4b1a8220da47258d41106d9b82c6a08836c1c16350441d2ac631a8220da67218d41106d2b90c6a08832d9db535044196cec29a8220da67214d41106d2b90a6a08836c9c05350441b62e029a8220d3575989411069bbaac4a088365dcd6250441b28e6b128220db37058941106d8382c4a0883659cc6250441b2ae63128220ea562189411065b3b6a4a08832d9d85250441b2ce62928220d957314941106d9380a4a08836c5c0525044196eec9928220cb4764c9411065b3b064a08832d5d83250441f0a641928220d3575981411069bbaac0a088365dcd6050441b28e6b028220da77258141106d2392c0a08832ddd941d4041968eca0ca020db0705065010637394c7280831b5ca63940418bce7314a020c5d7398a501065a3b282a8083a5d8d4154041d28c6a0aa020ea762505501075231282a80836c1c14154041c9ec7b12a020e4c63d895010727b18c4a80839318c625404196eeca08a020e9663504501074ab1a8228083a99894114041d4ac4a08a020c7b76540501072cb1aa0280839a5895014041e6282a80a020d4d7298f54cc72b31ac3aa6631bdc960953318d8e4b04a998c3f7655054cc716aa2c42a6638b9916215331c9cc6b10a998e2e5458843cc716aa2c421e638d9516110f318deeca90a598e2d6454852cc62f3b6a899663531c9544cb31b8ae3a926598cce7614932cc6c6ba0a499663531d5424cb31e1aa8a126598dc77150932cc762992c21966387550635073199ae431a8398e4e624ca50cc63dbb2a0286639558e61d523187eecaa0a918c6f72580548c636392c02a4638d5506150e318deeca90a518c7b76540508c717b20c4aa26393d8c6255131c9ae6312a898e6462d85544c735b16c0aa2639a18b6055131c76c8302a898e5b63181544c735b10c0aa2639a1886055131ce6c2302a898c3f76550544c696392a82a2634e1c154151318dee4b00a898c6c72580544c71a2a2c3a1a631bdd95214931a58e8a90a498d6870548524c63db82ca212631e1c16510931c3ea8b188498e1c5458c424c66a38ac6212639358f5210931c9ac62908498c5f76553324c6a6392a999263561c154cc931a98
  | 16 => 0xca9b38ec8aa0650fdd954150328deeab14861962d54988430ca2fbaac721065875526310832aaae3aa6641945d7694e320cab2b8ea9190651b5da538c8328bcedaa2641955571d51320caa6bae8499065c3552424c832a9aea212641946e76d51320cab2b8ea899065535d7434c832e1aa921a641954d7510d320cb26baeca99065939db654c832a9ae9b2a641954d71d95320caa7386ca99065535d6644c832a9eeab2264195c771591320cae238ac89906572dc1644c832b90e0b22641968d64191320ca673b6a899065719c7544c832b8ae3aa2641954e76d51320cb273b6a899065d19c7544c832a9ae3aa2641974571d51320caa2b8ea899065539c3544c832a9aeb2a2641954e76551320caa63b2a899065c3dd1544c832e1ec8aa2641970c64551320caa7b8aa899065531c1544c83299cec2a2641954e75151320caa6bacc29906553dd5614c832b1ee8b0a641958c74585320cae5b82c299065721c1614c832d8ac230a641954d75981320caa7baac09906563dd1604c832b18e8b0264195c771581320cae238ac099065b2580604c83299eec996a21968e644cb510cb46b2265a88654d9d35194432c9eec992a21964c764c9510cb27b2264a8865d1dc53254432e88e2992a21964d32181510ca67bb264288651ddd9511443299eec996a01947771592500ca3a38ac92806593dd93294032c98ec994a01964d644ca500cba5b826528065d21c1329403287ee8b0ca01943c74586500cb26992c32806533dd93214032d1cc8990a01968d644c8500cb62994c228065b14c961140328f6eca80a01946e72d8153d0636b96c0a9e8317dd95314f41c9aa6b10a7a0e4e5358843d0726a9ac421e83179cf6054b418bae7b02a5a0c6f7654852d0726b1aa4296839358e5210b41c9ac6a9085a0d4c7254d32d06a639aa49968393d95320cb41c9aca99065a0ec53258432d0637394c7286831b5ca63943418bce7314a1a0c5d7398a50d063dbb2a0286831b9cb6054e418dae5b02a720c5f7654c5390726a9ac429c83a350d6210e418bce7b02a520c5d73d815290637bb2a4294839358d5214a41d1ac6a108520d4c7254d32906a639aa49948393d95320ca41c9aca9906520e8d644c83290637394c7284831b5ca63942418bce7314a120c5d7398a509063dbb2a0284831bdc960d4d418d8e4b06a6a0c5f7654c53506a6392a629a83561c15314d41c9aa6b10a6a0d4d7214e43506a6b90a6a1a8317dcd60d49418b8e6b06a4a0c6f7654852506a639aa4292839358d5214941ad0e0a90a4a0d4d7314a42506a6b98a4a1283535cc52cc941a9ae429c64a0c7b70594325063c382ca19283535c8530c941a9ae629064a0d4e754c832506a63aa641928393595320c9418f6eca80a0a0d587354050506b4392a02828317dd95314c41c9aa6b10a620e
  | 17 => 0x80879954a6114043ccca4b08a021e65525845010e3dbb2a0280879c58550140438beeca98a7a164d5358843d0a3bbb2a228e851edd950143428beeca98a721655535845390b46a1ac421c8517dcd60946428b8e6b04a321477765445190b2ab1aa228c851edd950142428beeca98a6a15547154c5350aac382a629a851ddd95114542aa8e6a88a2a1570705445150a2fb9ac028a85171cd60145428f6eca80a0a1558735405050ab838aa02828517dcd61141428b8e6b08a0a15567118a5310aaab88c529885539c86194c42caac230ca62154e72d825310a8e3a2c2a9885531c96154c42ab6e0b0aa621558705855310aa7390c2a9885955846154c42a9ce5b02a62151c745815310aa6392c0a988555dc56054c42aa8e2b02a62145f7654c5310b26a9ac5a18859354e6210c42c9ca6b10862143d769524210a36bb4a9210859354e6090842c3ecb29a842161f6554d4210b27b2ca6a108593d955350842e1ec8a9a842170d5390d4210b26a98c0a108517dcd60944428b8e6b04a22145d7694c5110a2fbb2a6288851ddd95114442cb4a7300a221659539805110b2d29ac0288859654d6014442ce2a2b00a22145f735865010a2e39ac328085175da53140428beeca98a021656539845010b2aa9cc2280859594d6114042caaa6b08a02147b765405010b38b0aa0280859398d62d533287eecaa0a99964e6358854cca2f3b0a8a1e658b5516210f32c3aa831a85994777654451cca3dbb2a0286659358e62d523287eecaa0a91964d63988548cb16aa0c4a1c651b9d85450a32c3aa8b18851947776544518ca3dbb2a0284658dd906155132caec630aa89966762185544cb39b0ec0aa2659c1876055132c76c8302a89965b63181544cb35b10c0aa2659cd846055132ce0c2302a89943f76550544ca9a38aa82a2654e1c15415132c9ac6b10a89947771580544ca3a38ac02a2658b15162d0d32a9cea31486995c57118a434ca66392c321a65339ca6090d32a3cebb22869951e74951434ca2f3b0a8a1a65479d85450d32c3cec2a2869970d72151434ca673a8c4a1a65939d46250d3299ae231286994ce70189434cb0e2a0c0a1a658715163d0932a9cea31c84995c57118e424caa63aa8721265c31514390932998e6b0c84994ce73982424ca973aec8a12654b9d254509328dcec2a2849952e76151424cb173b0a8a1265c35cc545093299cea31a849964e7518d424ca66b88c6a1265339c06350932c98cb21a849970c5490d424caa63aa86a1265931954350932c58a8302849968d6490f324cb46b2485192651ddd95114532a68e8a88a29957070544514ca1fba2c028a650f1d160145328f6eca80a09953874540504cab838aa0282651ddc564141328e8e2b20a09943f74584504ca1e3a2c2282659598d61d5032cccc4b0ea81953671d52540
  | 18 => 0x200000600a02200200200004801200801803000e00000000202200800000000000e01000000c00001001202600004400604600000000001a00000004600000200200000200000601200001000600401200e00001c00001a00200200a02800600200000400200600000200001401200001000e00200000000800203604000200000000e00800001005000800001602200000001600a04800004c00200202600000a00200001800200001200800e00203400400000c00000001a00200000a00600000800400800000403200602c00800400a00200e01000600a00200200000000001001c00200600200800400600a00200c00000601200400000000001a00002200001401600204800a00a00601205a01400e00400400002000400601c03601002600000000400200a01400801800201000a00801600001600002402600c00002801a00c00600200200200000003003001800600000000e00c01e00600600a01400000405000a00802401200801800000200600000e00800200600000e00001200800000e00000400201000006200000200200a00003800c01403801201c00200200000800800c00000000600c00400e04c00000200800e01200001801200000200000600200400c01002400202200000202801800402000a00200c00001400000400c00001c03200000200000600600200200600800000400e04403600800200600201400400c00200c00a00200203000001c00400000c05200c03001800800200400000800a00600400c01201800000402000400200200006401200a01000e00000400800400400a00000c02000000000000000801600003801c00000000a02a00e00000200000001c00200a00c00c01800001a00200200801b1bdd95214b438eeeca88a3a1c7b7654050d0e37bb2a429487995496114a438dee4b04a321c6c725825190e3bbb2a228c879958951146438f6eca80a121c6f765485250eb238aa4292875a1c152149438eeeca88a2a1d64725445150eb8382a228a871bdc960145438d8e4b00a2a1c7b765405050eb4392a0282875c1c550141438dee4b08a0a1c6c725845050e1ebb4a921887175da5490c43a5eeaa1ca421d4f7550e5210eb3388c729087595c46394843a9ce630ca421e65611865210ea739ec1290874bdd54354843a9eeaa1aa421d4e7090d5210f87ba286a9087531c14354843a58e8b0aa421d4c735855210eb5b82c2a90875a1c16154843a9ce630aa421e65611855210ea739ec0a90874b1d16054843a98e6b02a421d67715815210eb238ac0a90871bdd952148438dee4b04a221c6c725825110e36bb4a4288871bdd952144438eeeca88a221e6a529805110f34a94c0288879a9496014443cd2a4b00a221e71515805110e37b92c3280871b1c961940438daed290a021c6f765485010f33294c22
  | 19 => 0xa2c43e2040c58a0644e8074ffa73c00000000000000e5826d49c00000027600000000002f840003651c880000002130000000e86a9d1d0a3548f20372a8a784b7c0f8000136000000000028e80003b80ca8e88dfa0000000dd4c6e98d43b9fc4af083750100007ba0e50000080260349374a1814e66b649cac7c00a00001200001000004000000000401a00200401e00000000400804200c00001e03401c00400000001401400c00600600602400204000200c01000000000200200801000809600000a02800600000801200000603600002200c00401600600800000e00c00201000000201e00001400000600a00000000803c00400001200200a00600000e01e02602200000000e00000a00a00400200400000401000000800000200a02600600200001000002600200600c00801003000000401000000204a00002c00000200400000601002000200a00800c00000001404400000c00000a00001400600a00000000203e00200400400200400800000005c00c00401800601a00000a01e00000202200201e00e00000000000000200002005400800000c00000800e00001202000600400000200200001601200001200001000200a00c00c00600c00001200001a00000800601000000002800e00200401201201800800003600000000200a02c01a00002e02a00000200404e00201000400a01400001a00601800601600402e00a00602000000000200402004600400603a00002400a00002000000200001e00000e00a01000000000a00400600c00c02e00000002000a00200401800a00801200600c00000000c01000c00602201401400000e00000a00c05801a02400201201000001000000200003802400000200801202c00000001000200000600c00400000000200a01000400000001000000401200000602e00800002201400000200400401602600200000603c00000800001200801600600000200a08c00201400000200200000200201000a00001200c00800000800000000400e00001400e01000000200200000000600000000000200000000c00400a00801400000002a00a00000400000e01600001600200000600c01201600000200600e00001200600200e00e00202c00000e00c00406000000400000000001000404800200201000000a00000601600000a00002200200204e00600200e00800003403200600a00a00a00e00400a00000000000600201000002800202002602a00c02600200600600000000000200000000600c00800a00000400400a00000800000400e00000000201602600800a03004800400000c01000000400800200200000000001000001a00200800001003800200800400a02000001a00000000600800001800200c00000000000600600400000000000007a00201800c00800a04600c0180100100000060
  | 20 => 0x9d5438226400000000000e157c8000b981a02d60000d940001d180015980001ed015d1d82821a5257400061c1df043000012000017bd7e69d244d83f000060352a900d1a45bb29209fc3465b006bad5d33c3575da07782b62ce263038c00063c0461c8926e6ce35725a07ca4165fd055094c92720607cc8c600055921604187b052129d16f456c53a88646082a04c21b8c9fa0a338500949e056f1f7a8a03aca8407cabf47003bb5c680a81220ea0000000e945031c82fb412c6333b404d504c84900015d44084a00001a613c03c95180bec19478f000000000000052928d10daa313658f3c2b011253d20ac8ae2730ceaf48f9461d4ce0dc473a2f20e629203ae79d3c12e384b62d2000164163651300013b0da2af44b020840002090d80d14b70936000219d41206b2c78aa8f6e5703ed994c00037a5e591451462ef20f8b401307f0014aa7022644b0091428cc88150001cdcec48c10002d48cce1032fc00788ba2a90d91d2175e0005ce87f4670000316a4680009882298904d4000000024c04ca3e12b494991f04af41fac5c9940001d5a5e88e42fd00022f85748b123f196c1e05db344ad2950e78d0000000d1c8831711a011f88e34010c181da2ab208800003e00058598e4e3c2b94590988000000109210ca72ba926ba79cbbc14323b08851405e500028e49a6aa70000000000247393a5ad4d649451c00000004f30588000000aa004a80000009010000000000b0d51b80014b400007b0f0000000040c80000909bb30f00012a8ba04b291cc85256b000000100c7c03150744eb83c20851fcc4c606d26d0959424000214289ca5cbee012046c3141870001c1800006a5b4175056824b562002465e000000047d1d400028d80009320001c7800064e61b1da963072c00033a8d981743e21e08000aa6267476a168cfa00000000000006b00000001080a011129cb84168eb0002b0c00042500013a92dc382000178cb649694f195e43a000000500a00000002878000df00002900000ace9000f61d7962a0000d700016ba71340e800000077b2bba58d38cb970632b8c74c000491800104e00020a1cd8f366ee3a094714ce36d4ea94fd5b6a630dba5110e0500482ac4511e37d4e700000b45fd090912031e4d93e324ad0ae60942522f035e7dd586257ca3043f55821386f0bf41aaa934bee22c421171969eb0140890b1542593145000126a25f2ce80014ac5470002cb95107b6203b000f0e34008a9f4c00046600002b046600046c15cc1160925c4048800058d00000006bc6d74310cf111801c5d0945469e6120220000a18838575933c000000000179859a5860000000cf874e3be0a940000d83d40a4517661f1db169000032d0002e291e8000013a7e800080900021447ec4a212e81f974a4805042334e526592b91bc569658a25fac247e6
  | 21 => 0x498027480000000000001a0c00000000000000005350002e2cfe80000002a9071a228291aef949e56109985807f20004f99e900007644d4000000036926b0000000a4718e9b7d066a5c3200001626412000000165e8450000000e804cb0000ba4a509522caa4457ba73d433023c1826f92a78f2d0d86f633ba0a02b499a2be97d80e21d41570ff0f726080260ffd5a0a5451f2220fc20e05f8836caac253409a3a171825030a8a9ceee6e40000ad495832a4fe89610f24c51cc9f042160000000000000000000213c86895e0ba1378cde65803300000000000002328f7a2990951660f541882d4ae00d581fc0000eb00000000c8838880c0000002b9175c6b81100bd47182da03d1e8c62230d15e86843500005b60000ce000000007650d60000000000000bfb34918a45ae1751b180000006a50b224bd67491f0000000430000043843c00000000000000008ac00020ec000a9e0002d382c43ad2a5a4880000000b300004bc6853640000e6200000016780006d9000037492cb100000d7d5780004b6a3bcd3c00042f99f95700360ea92f54289990a0000000020253500c8000ad320e25fcc8c27c27b9c940009b100000000002fe32598c80000005ad02e53300003682fd918c5c100014c40009470000a30000acf0001d693660a6088800000087a1eb1c8cec643618c27a534a32e38013c958a0fe088065c9200003360000f582d900000005e00004b62fac0680f326229117280000002c3ca9c2ad1bb17616546d80002c8c09ab8f13aaa1800000049a1c448f400056703395b0274114a7c90aa3d547e800098ebe200028d5030b454e6243936c64f4ed00001fe0005ba2d9c000a8f11698957cc2e540694b49fca8303481f50d03de484000059e00000021754b0a714ff8000aba1c83d000f92ae0002192f5807eb540000f98ef409e38415040003d2145800127400025204200007e321980000009e53a580015f40000000bd0000368557afb037c0000000841138000000037c41e8cb00000006c000000026417b29141bf000064a0be2b880016c800000025f12900003ee00b4000a2d000238156e00000003bd24834634f8000000b632f08490ee203c1819eb460ab8119da53d6ca754467adb90646315481c6cc9445247c8529116ba409f2bb53840003b5a65c000bbf4b9273d784a6d554220520e0000cc8000000626000117c0004b25f20c6d27e1ca30005253480005259d340000000000000e503df399812800000000000009a40002c1800000000052180000004600000000446b823498c0934678e0001cac62e7eb1fa2b5d49877f051119c9603394a08ff83c262b0d39940cb44fa2bb01cd0bc00054d8e6006263d549816054654924a9df963cafc59484e40004c2000039c8867fc14b078cd642364e380000000b80000ee55ac607299
  | 22 => 0x98bb89986c74de0e20f761c922221050604014a4a0693eca465070c28000b0e0c28e7d45ea7625412d155411c0fa29157f800000000000009285fa800065233d0a7acfca4e6e200690f52a638107211a05da3b125c28d80004884f684a000022f000000161003d4f114888f698605008fd722ac0369826863444e5831e303520970162de01ee73b359ad642ac52f09480ac00038a4c11b0c0a423c0311bbc000adf0762cd47d870920581d093c1dc1e1941c3dc1c300029c0262a692588d3800000000027705a600010baed80007834cb0a680000840002dc9594628000197885c9d00001db400000000029848804742e1a4c8fd48d316889e091408a26e00009242b30002f30ba22d83baa430e3210000000000005ca5d3086d0e29910f7800134e00000013d8c709c94c7000066e26c255a6e00006c52ec8a6ce7c00049f00010523332728ed00000002070000c2800000000000000000002734000469387800000000003417b874a0000000000d4249d1b626a54dc89e05b1e514a60004dc80003e20001a120e41b44ed4b80818368b1d4d72704d2e8c824306cc4e20005e20000000a6214380016f275d57b1aecff47e723205703be4265b483c855e17315d858cb963894d500007ea000067800000000000000000002312468000e9e59c2f689c06b81613e28ec800000008c8000b1234c2ac9dc17d246e4d007a17662dc383aa58a0467b1cf2bdc87228f06e285ccb86811029e98dd421e266977433439c30984bc13a6634e52bd5124848063a2d50dc38e2311bc13b61cf44a833090e8a1100a7e477400048e0a7d10e8d04d1271449eb20028ae184801b14b319387481830db24e0cc24dd3cb9915226000000000072858400000000006715db898166e0003e8a64cbaa00000000002ce00038100000008dc13489d80000001e8051410c0005080dd077834810a006132843a5cb2db43fe1d31f1a0396501ba26f8cac6480004320000000ab9032abcc64600000009e40007851940000fda31f00029bc27859a35798600700fa18e2cc02e05f01801c802be1535ff9bed3e88e7185a4c493e35a0772b9895200058a08e068ea8a1a9ada97641e72fd95e8b9c8de1622d6d6c200039912f82f46201cd0bdc67412c0002e48b7a00000007c094a5e035d0000e209f700000016067014f22f7c00000000007748aa6a40b895b487697100013e4b0e17c48c00009364ef24ba0bd492bab1d41cbcd46000512000000000000000001286900002ded7aa7bf223227d0fe00038d16d809c6f41f3a36d4cc5f20959ebc5f80502a522b40000005a1983164430909922606e67571932a9518a3582dd2cf078c98b4be8d0c5d8a155fc0000000331468800031285406c83a571210d00007992144610001ca912200000000000004ee248a22910000050b2b6949
  | 23 => 0x8c00f184012cabe5145ab283ca584b64849b3086a94a144871802c97e2d4287c97482d09c01545847ee1419e28f160545772b449760c25791d80fee18141706b00005c90bb800000000048e8000000000105000019695c56e800017622b59c81bcd227b21d7942c00017b00002a00009c85ae0ae12f0b750209fec00000015f9f604dc3fa28400cc4e421a43c165c7064713b60000aa400032900000006e50001f2578a4312eb991000036e4972888000565460090cece00058394f00004e138c0a3485e81f03b00000000002f10748ca800000027f8ef200058014480000005cf8000f7c000144141935e1262d090097a667f17b0000e3800009723b83da0005ca9d100002225ac000000068738bacb441a80739d05f423a5010002f413566bd00000003209331ec995c0000000381a596485294f814c0100ba74e580507c87bc3330f50aaa8b62ee000000059157f25608948724ef80010a03f114c1cb112080531f9a3168c00045c88b8000820000000066463a40d800168e6d4000191d7ee00044d2f0431813a00180000000005c9a7451081461c204f42460450000b246c82510f50ef40001e500000c07d04c800025d00ce00055580004f44174a680000002921cb8000a3453b11323dca9016c545ae0c79c31e4d620f000000000000014d800056aa7d4cac0002d01b100a643800015b866a03a000096405c6a8544a4582aa2c50000000e8e000528258400000016f00008e00994da80000000000000508d4c000227a5cc0000002280000000000000250d3b253e0000000c68000000071c0029850d121107d6b4d000000000031642600000000002d980000000000001f6400014d25080000000000e28d891ca0000000000f6a45a3b30e18000000000000004481c0df9f416844db5ff169486004003aa88c86ea8c13f24b4dce1c01e3960887860e3ff1439744372242aad51846a229b8c508203e94fe2ba54263d152f0fe1478b161d52f0c5d465f00014345488b313316008f01065a00a54dd84d536e880c6445c017096a86ce60b30694243304c035e0000c2c000336a31c8d82463051570d4eab44730358f70a034d0953545649c00015f85c67e522087e424ab4959616ac83c02605b8320e2c8a65e30f14590b6b4712ef0cf25f30231a6416447f56f14e13885a638721bceac98737fa1d13bc1f72d129901e25542de1c9009214b4c784ec4940002b5105416616e52f8000dfc694069908145c0000002cd808467355f06e0daa0000001e58000a6015403348007cd4a58d6c0003fd54a80017e45450001bc820400055312d56908da308805c0008cc256988cc2074500016d0000000554aa614f85fe503800017ab992a220a8f002eb22d88c8a802e402191142de4d14090af81eab4109399a85820001580000ba000017f8adc00091017
  | 24 => 0x8887d579e83506a8cfc0000000fdad81208a7234a87ac0009b400023500c000000000000000003eba514b0a0005988c8143a4ae1151268688bf9393067135a20e25396dcf4ab0a0499aac47a52a0c9116552488e57119d09f88650539eacbd0b3811396c53607e61ed9b713cc6692d69e48be24493eb28691be1483b9a9fc986a684aa8f114647c72328b30000000520000000000000019a000011e00006acd0412d0002c9c0005af3fb110977248904f8f3426c4b30000000000000561274c33c0780001390aae00005228fd7ce0003e580016de5da0000000026089000000058e82500000000006423110a04000000000102800000000000015340000002f2828826f44b8ad937c6f52e20000d140af4160d5055800047d000008e0000001e1144a3a9135281524a06e3a89fbc0003590002f2166669c4e1a448000534000067cb100004bb2f606fe1c45d51599254a994fc2288cec00035a28451d252118a85480003b300023c000056225180007da2bc54000013f69ef4410000000421000000124c42706180011e25c5000000000000042da00c0000e60a0aed551ab1200022a800000000028300f200027188ec0004580000a000fe54200017fd0f60002e4034000088d0000204c9019b3a600680003a02eb21f827e000000079036a00033100005287393f0000170abfd05a80012040001740350c9205657d8414a744e85f813fc658b252710000ca20004ac90647b8bac1290a14798aa25cc286007200024611d400000000d800000018b2f22864b2475820e82a80001470000c854768bd464ae78dcca7d0410b2d67c00047f17a57803d3080ab180000001cd80009c08b74c6000092600000022a00000003a98000000ae1564acf40003705ed8ded4b6aac45d069915200008d2f380000003820000d921e05de98b959a0003f41f38dd61963c98000e0abe5505a9e058c0000002bfc000b5f36d00000007381120000b72104216977c4103f000000004c28a518090152ac2e752c8b0061c95b000000000c37c38a9638c9805b50223fc000746000295d0002b10002bc0e3a1d815300d4954bea0002540d628164f706f49a066e54703d0526b66434953000000045a1210000750000185d2c835d11a895166837953f1dd91e660536b1ed000e72d2d38000000568494818d17000008a181952eae8556837915e9e854f800000000055d2338d8c51d1c28cd037223a237a35d6f80ad0001adc0000000000c40000b040d28000d82b550001bdc0002112068970000b7e57399e00002d500019353d8000500000048a0000ff0000c320005d8a4ec1109dd0691ee96a0137223a9ec812bbb00000005a879a0002b650fa00007580002d20003b797acd7c40f00017d4000ae000010900005990002c980005505f79e4000028e0088001312b711d808d12
  | 25 => 0x6c40002ca147879072135c85a9438a263ea2c7017eac75a992e515c8f23ff9cd573600b0001e440008754d9041c70e38b00000004387d546b1e24000000000000118800028b2c84e920005b98001008abd4721e7c7ae35002f00016e066b00022fcf5255a23681913a8b190872974b3e63e4db9eb8af699d000156177400c53ca14c0d87144a72364c4e0040848270c7600051e9fa49e876a3b08000c8280800018c106c45e00800005f233610a99e82d04d4000029418a1bb3f213e0000000000000000088500000006d670c5bb00007dc000000173c1f678800000012f2268000076c0007b300000003f069b3fc80000003ae27300000002db00017e960a5172fa000000000000000000005ea10b0000472a7756e01642f03075c200000000000001be80000005751a216566cd44b0a191c21aa0bf000000000000000009ce47d57c165800021d000000137408354a1b78d1e3515af05c943c000379a7ac72675f00000010c20004c09c7d02800056900000f6abb3d38000000bdc36d97f098217944ca7c467c26d1b786b50620004e0000121a0003d0800114e80f0001f7cb465d235500003283415f02f44e680001860da945458120208dc7c0a330002ab815c3523548fc800086a3601d940000005f40000000992000000052ea1b5e48000c6c00021511dc000186000000009e150000000030000000003a00b843e0a729948363611bbaa8cf98bcd08b800011a96700007a5242bc700000002ae5ae000133853a88941100008261340000000000624000126032648b226913175a66051480000000b40000000fb447c29b245ccaa24d0012ee118677d00c8000d5a919000202d2a22a22118f28b7e3ea1ca80010481183b480000002a124780000000000de120d76029e3caaa0461e6cf0b597b12b47c455f8000000000000000000000047d800173897700025bd0a42441890000c6a23e48a81c95e258b4522ad80000002af23d94a224e135800083493d426aa14000000000000031c0002da80011567f800019752160000000000000a0d22b18689eaba31980184c865e70001e61240000247288400073f0000000594b770a600003e45320482b0474eb90339205cf6293c21115182ec02f42e20f4f3c0003a90284d340001789a7443e2005cd05b51ea0000002bbca0a15e0000a100006ed0001151440b513c320283c497505820e87b000544a2418ee86d225b9fc8188940599034400083e5c39b080005643b70000f024c930094f4c080001fb95d0000bda0000000000000215ac602ca0000a880013acb3b0002c68d7e3133f62078000acb00000000000000002d300008563108000c1e68b0001f88afe0000000000f447c32880c6430891e000250819200e03ba12c46099f43b1d6438400012a9f780007421df97357c646b3faa08cf9e8012
  | 26 => 0xa91000000000000038580003044bc46e80000009033741c352d40003701494a3200003e120400034b58112080008b00bf950c02a000000017c00087334680013d400008b0000eb60000000d5908e08e1c900844f688600000000000004d300003ec5044ca8000ac00a912b89210686b52e987e90c60003bc199400029c57280004840bc01d98bc9d62dd3818be80000ab22e0738000000126156d5900fd2e3a588d080082b18fec2b27720c6800039a2df52093ec00002313eaea00007c22fc947d4140c01dba5ecf380002cd95f05f00000d22f5c0007d2000000108c00000009244b4bd41a691a95a8aec000000010a6fc0ae9708f902e616190216fa00039810605ac4f13cca66c000712343000000092c0002f7912680c4c1a6f556291b55994ad2982b213ba1656fe2073010b800009d70ed243cdc20004c52d1137e29002eaa09
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x1544c832a8484584614c832ac080584614c832a8884580604c832ac081580604c832a47815913294032c0f744c96194032a488054d6214d41c49631c1521494184c87595320c941a4880595320c941a848258c6350441a908058c6350441c85635c86350441a84835886250441c85735886250441aa08058862504418b0805d83250441a84864c83250441c85764c83250441c90631c14154041ca0621c14154041e11635055014041e21625055014041a458298d61d5331c0d545c86350731c0d7650c4394831a28805906454831c0d7458e5210831a458198d5210831945859c8434c431a458398961d5321d06745c4534cb21c0d545cc6250721944855c6434c921a18805906454c21c45535c66210c21a0d8494d6210c21a0d8694d4210821a0d84d95320c821945859cc4248421a4581d95320cb40a458194d620c740c45635c65208740c0d745886214d40a888050d6210d40c0d7458c6314940b088050c4314940c89631c14210940d08531c14210940c0c75591320c940a8880591320c940b108050c4314540d05435c84314540d05735084214540b20805084214540930805d03214540d05744c83214540c88731c96010440a90835c06150040aa0825c06150040c0d7650c4394b30c0d7458e5210b30d22521c14110730a4586949310c730c45635c65208730d22521c5401033094581dd6424ca30a0d84d9532c8630945811d5424c830a0c86551424c830c0c76551424c830c88641c1424c830d09541c1424c830c0d545c86350430a458218d5150430c31651c14110430a0d841953248430ac0814c86048430e41325446048430c0d545ca6390030a0d8494d6210f20a0d8694d4210b20d12531c14110720a458194d620c720a458694d2108720d12531c5401032094581dd6434ca20a0d84d9532cc620d05749c4534c820d06745c4534c820d05745c4534c820945811d6434c820945811d5434c820a0c86551434c820c0c76551434c820c88641c1434c820d09541c1434c820c0d545cc6250420a45831895150420a0d84195324c420ac0814c8604c420e4132544604c420c0d545ce6290020a0d84195320c020a888458c3048020ac08158c3048020a0d8494d6210f10c0d7458e5210b10a0d84d95320cb10a0d84195320ca10a458294d610c210a45839496108210c45625c46214d10c45635c46314910a44854c9610c910c44754c9610c910e04544c9610c910c30541c1610c910cc1321c1610c910c4475589310c510e0454589310c510a4586149310c510d10541c1310c510cc1621c1310c510d40521c1310c510c447558d2108510e045458d2108510a458614d2108510d20541c12108510cc1631c12108510d40531c12108510cc0731c96010410a90835c06444010aa0825c06444010ca0649cb3044010c90649cf2044010
  | 1 => 0x1c800020000000000000000c60000088b27508820d07600000603500000763f160546c8c2f00000044322d002f100009c1a3d1308409068c41e1200170b000000988c003a0cca8244701c00000000000612f8000050001b0004300000000035000f64a1e1c0e42317064ba290a08400000000c0000001f400693003800004209c5a6b3b800003e0c1f864051a2350a000306cac7f3c070a441338009a25000010e00001cc004b09800000000124c43a0b8001664001bd120028a0d147941110806d0514c3c0c241b89e473e20400452b8a8e2023319420370016c7a1d0b220001f1580000382d0a0aa01231003030200000000001e01080e000a050503001e060100001e010000000e0402000103040103000a0116020a0ca60805846154843a50805846154c42947815d3654c83290f845c7654c832a8481590644c832a8880590644c832b0681dd
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x40001a32a406721e75900c504102427a40482c6b90c6a088388173201621894110610930bb2641928220d20241764c83250441c043a900b2264192815009050d7210c51503202e640284210a2a0540241744c83214540a044b2a83828499061408965507050d320828812a990e0b086488700151321c1610c910e002a2c43826218a2144196148704c431443800a8b18e09084288510658531c12108510
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 40
  | 6 => 1798
  | 5 => 7915
  | 4 => 3073
  | 3 => 143
  | 2 => 16
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
  | 6 => packedAt gbK6 (55734+((h/599+packedAt gbK6 (48546+(h % 599)*12) 12) % 2373)*12) 12
  | 5 => packedAt gbK5 (337702+((h/2638+packedAt gbK5 (300770+(h % 2638)*14) 14) % 10448)*14) 14
  | 4 => packedAt gbK4 (162865+((h/1024+packedAt gbK4 (150577+(h % 1024)*12) 12) % 4056)*13) 13
  | 3 => packedAt gbK3 (8956+((h/47+packedAt gbK3 (8580+(h % 47)*8) 8) % 207)*9) 9
  | 2 => packedAt gbK2 (1161+((h/5+packedAt gbK2 (1136+(h % 5)*5) 5) % 20)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffe03ffffffffff03ffc1ff83ffffff238ffff
  | 1 => 0x7ffc07ff80fffffc0ffe1ffc3fe0ffdc71e3f
  | 2 => 0x7ffff80fff01fffff0001fffc7ff0fe07e3c7
  | 3 => 0xf8000000ffffe03ffffffe00007fff0ff803f8
  | 4 => 0xffffffff0000003fffffffffff80000ffffc00
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x3029850a092244800b2c025804961110186cdb
  | 1 => 0x5142931410e48912c054a0a9412a8aa4c3162d
  | 2 => 0xa5850a26a241d23555029135a84da8ce05a346
  | 3 => 0xc5162c58c48903b9a69ad4052071cc8f6803b0
  | 4 => 0x6183060870e1c2e38e319c63201000bb6d800
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xeee8a880eee8a880eee8a880eee8a880eee8a880eee8a880eee8a880eee8a880eee8a880eee8a880eee8a880eee8a880eee8a880eee8a880eee8a880eee8a880, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_12951
namespace PEqualNP.Outside.L_meta_12951
open PEqualNP.Outside.L_meta_12951.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 16 := bgb_2_0
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
theorem bgb_3_128 : Interval gbAtlas 3 128 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 143 := (concat (concat bgb_3_0 bgb_3_32) (concat bgb_3_64 (concat bgb_3_96 bgb_3_128)))
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
theorem bgb_4_3072 : Interval gbAtlas 4 3072 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 3073 := (concat (concat (concat (concat (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat bgb_4_96 (concat bgb_4_128 bgb_4_160))) (concat (concat bgb_4_192 (concat bgb_4_224 bgb_4_256)) (concat bgb_4_288 (concat bgb_4_320 bgb_4_352)))) (concat (concat (concat bgb_4_384 (concat bgb_4_416 bgb_4_448)) (concat bgb_4_480 (concat bgb_4_512 bgb_4_544))) (concat (concat bgb_4_576 (concat bgb_4_608 bgb_4_640)) (concat bgb_4_672 (concat bgb_4_704 bgb_4_736))))) (concat (concat (concat (concat bgb_4_768 (concat bgb_4_800 bgb_4_832)) (concat bgb_4_864 (concat bgb_4_896 bgb_4_928))) (concat (concat bgb_4_960 (concat bgb_4_992 bgb_4_1024)) (concat bgb_4_1056 (concat bgb_4_1088 bgb_4_1120)))) (concat (concat (concat bgb_4_1152 (concat bgb_4_1184 bgb_4_1216)) (concat bgb_4_1248 (concat bgb_4_1280 bgb_4_1312))) (concat (concat bgb_4_1344 (concat bgb_4_1376 bgb_4_1408)) (concat bgb_4_1440 (concat bgb_4_1472 bgb_4_1504)))))) (concat (concat (concat (concat (concat bgb_4_1536 (concat bgb_4_1568 bgb_4_1600)) (concat bgb_4_1632 (concat bgb_4_1664 bgb_4_1696))) (concat (concat bgb_4_1728 (concat bgb_4_1760 bgb_4_1792)) (concat bgb_4_1824 (concat bgb_4_1856 bgb_4_1888)))) (concat (concat (concat bgb_4_1920 (concat bgb_4_1952 bgb_4_1984)) (concat bgb_4_2016 (concat bgb_4_2048 bgb_4_2080))) (concat (concat bgb_4_2112 (concat bgb_4_2144 bgb_4_2176)) (concat bgb_4_2208 (concat bgb_4_2240 bgb_4_2272))))) (concat (concat (concat (concat bgb_4_2304 (concat bgb_4_2336 bgb_4_2368)) (concat bgb_4_2400 (concat bgb_4_2432 bgb_4_2464))) (concat (concat bgb_4_2496 (concat bgb_4_2528 bgb_4_2560)) (concat bgb_4_2592 (concat bgb_4_2624 bgb_4_2656)))) (concat (concat (concat bgb_4_2688 (concat bgb_4_2720 bgb_4_2752)) (concat bgb_4_2784 (concat bgb_4_2816 bgb_4_2848))) (concat (concat bgb_4_2880 (concat bgb_4_2912 bgb_4_2944)) (concat (concat bgb_4_2976 bgb_4_3008) (concat bgb_4_3040 bgb_4_3072)))))))
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
theorem bgb_5_7904 : Interval gbAtlas 5 7904 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 7915 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat (concat bgb_5_224 bgb_5_256) (concat bgb_5_288 bgb_5_320)) (concat (concat bgb_5_352 bgb_5_384) (concat bgb_5_416 bgb_5_448)))) (concat (concat (concat (concat bgb_5_480 bgb_5_512) (concat bgb_5_544 bgb_5_576)) (concat (concat bgb_5_608 bgb_5_640) (concat bgb_5_672 bgb_5_704))) (concat (concat (concat bgb_5_736 bgb_5_768) (concat bgb_5_800 bgb_5_832)) (concat (concat bgb_5_864 bgb_5_896) (concat bgb_5_928 bgb_5_960))))) (concat (concat (concat (concat bgb_5_992 (concat bgb_5_1024 bgb_5_1056)) (concat (concat bgb_5_1088 bgb_5_1120) (concat bgb_5_1152 bgb_5_1184))) (concat (concat (concat bgb_5_1216 bgb_5_1248) (concat bgb_5_1280 bgb_5_1312)) (concat (concat bgb_5_1344 bgb_5_1376) (concat bgb_5_1408 bgb_5_1440)))) (concat (concat (concat (concat bgb_5_1472 bgb_5_1504) (concat bgb_5_1536 bgb_5_1568)) (concat (concat bgb_5_1600 bgb_5_1632) (concat bgb_5_1664 bgb_5_1696))) (concat (concat (concat bgb_5_1728 bgb_5_1760) (concat bgb_5_1792 bgb_5_1824)) (concat (concat bgb_5_1856 bgb_5_1888) (concat bgb_5_1920 bgb_5_1952)))))) (concat (concat (concat (concat (concat bgb_5_1984 (concat bgb_5_2016 bgb_5_2048)) (concat (concat bgb_5_2080 bgb_5_2112) (concat bgb_5_2144 bgb_5_2176))) (concat (concat (concat bgb_5_2208 bgb_5_2240) (concat bgb_5_2272 bgb_5_2304)) (concat (concat bgb_5_2336 bgb_5_2368) (concat bgb_5_2400 bgb_5_2432)))) (concat (concat (concat (concat bgb_5_2464 bgb_5_2496) (concat bgb_5_2528 bgb_5_2560)) (concat (concat bgb_5_2592 bgb_5_2624) (concat bgb_5_2656 bgb_5_2688))) (concat (concat (concat bgb_5_2720 bgb_5_2752) (concat bgb_5_2784 bgb_5_2816)) (concat (concat bgb_5_2848 bgb_5_2880) (concat bgb_5_2912 bgb_5_2944))))) (concat (concat (concat (concat bgb_5_2976 (concat bgb_5_3008 bgb_5_3040)) (concat (concat bgb_5_3072 bgb_5_3104) (concat bgb_5_3136 bgb_5_3168))) (concat (concat (concat bgb_5_3200 bgb_5_3232) (concat bgb_5_3264 bgb_5_3296)) (concat (concat bgb_5_3328 bgb_5_3360) (concat bgb_5_3392 bgb_5_3424)))) (concat (concat (concat (concat bgb_5_3456 bgb_5_3488) (concat bgb_5_3520 bgb_5_3552)) (concat (concat bgb_5_3584 bgb_5_3616) (concat bgb_5_3648 bgb_5_3680))) (concat (concat (concat bgb_5_3712 bgb_5_3744) (concat bgb_5_3776 bgb_5_3808)) (concat (concat bgb_5_3840 bgb_5_3872) (concat bgb_5_3904 bgb_5_3936))))))) (concat (concat (concat (concat (concat (concat bgb_5_3968 (concat bgb_5_4000 bgb_5_4032)) (concat (concat bgb_5_4064 bgb_5_4096) (concat bgb_5_4128 bgb_5_4160))) (concat (concat (concat bgb_5_4192 bgb_5_4224) (concat bgb_5_4256 bgb_5_4288)) (concat (concat bgb_5_4320 bgb_5_4352) (concat bgb_5_4384 bgb_5_4416)))) (concat (concat (concat (concat bgb_5_4448 bgb_5_4480) (concat bgb_5_4512 bgb_5_4544)) (concat (concat bgb_5_4576 bgb_5_4608) (concat bgb_5_4640 bgb_5_4672))) (concat (concat (concat bgb_5_4704 bgb_5_4736) (concat bgb_5_4768 bgb_5_4800)) (concat (concat bgb_5_4832 bgb_5_4864) (concat bgb_5_4896 bgb_5_4928))))) (concat (concat (concat (concat bgb_5_4960 (concat bgb_5_4992 bgb_5_5024)) (concat (concat bgb_5_5056 bgb_5_5088) (concat bgb_5_5120 bgb_5_5152))) (concat (concat (concat bgb_5_5184 bgb_5_5216) (concat bgb_5_5248 bgb_5_5280)) (concat (concat bgb_5_5312 bgb_5_5344) (concat bgb_5_5376 bgb_5_5408)))) (concat (concat (concat (concat bgb_5_5440 bgb_5_5472) (concat bgb_5_5504 bgb_5_5536)) (concat (concat bgb_5_5568 bgb_5_5600) (concat bgb_5_5632 bgb_5_5664))) (concat (concat (concat bgb_5_5696 bgb_5_5728) (concat bgb_5_5760 bgb_5_5792)) (concat (concat bgb_5_5824 bgb_5_5856) (concat bgb_5_5888 bgb_5_5920)))))) (concat (concat (concat (concat (concat bgb_5_5952 (concat bgb_5_5984 bgb_5_6016)) (concat (concat bgb_5_6048 bgb_5_6080) (concat bgb_5_6112 bgb_5_6144))) (concat (concat (concat bgb_5_6176 bgb_5_6208) (concat bgb_5_6240 bgb_5_6272)) (concat (concat bgb_5_6304 bgb_5_6336) (concat bgb_5_6368 bgb_5_6400)))) (concat (concat (concat (concat bgb_5_6432 bgb_5_6464) (concat bgb_5_6496 bgb_5_6528)) (concat (concat bgb_5_6560 bgb_5_6592) (concat bgb_5_6624 bgb_5_6656))) (concat (concat (concat bgb_5_6688 bgb_5_6720) (concat bgb_5_6752 bgb_5_6784)) (concat (concat bgb_5_6816 bgb_5_6848) (concat bgb_5_6880 bgb_5_6912))))) (concat (concat (concat (concat bgb_5_6944 (concat bgb_5_6976 bgb_5_7008)) (concat (concat bgb_5_7040 bgb_5_7072) (concat bgb_5_7104 bgb_5_7136))) (concat (concat (concat bgb_5_7168 bgb_5_7200) (concat bgb_5_7232 bgb_5_7264)) (concat (concat bgb_5_7296 bgb_5_7328) (concat bgb_5_7360 bgb_5_7392)))) (concat (concat (concat (concat bgb_5_7424 bgb_5_7456) (concat bgb_5_7488 bgb_5_7520)) (concat (concat bgb_5_7552 bgb_5_7584) (concat bgb_5_7616 bgb_5_7648))) (concat (concat (concat bgb_5_7680 bgb_5_7712) (concat bgb_5_7744 bgb_5_7776)) (concat (concat bgb_5_7808 bgb_5_7840) (concat bgb_5_7872 bgb_5_7904))))))))
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
theorem bgb_6_1792 : Interval gbAtlas 6 1792 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1798 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)) (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 bgb_6_416)))) (concat (concat (concat bgb_6_448 (concat bgb_6_480 bgb_6_512)) (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640))) (concat (concat bgb_6_672 (concat bgb_6_704 bgb_6_736)) (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 bgb_6_864))))) (concat (concat (concat (concat bgb_6_896 (concat bgb_6_928 bgb_6_960)) (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 bgb_6_1088))) (concat (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184)) (concat (concat bgb_6_1216 bgb_6_1248) (concat bgb_6_1280 bgb_6_1312)))) (concat (concat (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)) (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 bgb_6_1536))) (concat (concat (concat bgb_6_1568 bgb_6_1600) (concat bgb_6_1632 bgb_6_1664)) (concat (concat bgb_6_1696 bgb_6_1728) (concat bgb_6_1760 bgb_6_1792))))))
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
def fullWord : Sig := 0xeee8eee8eee8a880eee8eee8eee8a880eee8eee8eee8a880eee8eee8eee8a880eee8eee8eee8a880eee8eee8eee8a880eee8eee8eee8a880eee8eee8eee8a880
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 32 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,3,35)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,3,35)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008242920 * 2 ^ 32 + 4008224896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_12951.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,1]⟩,⟨.or,[1,2]⟩,⟨.and,[0,7]⟩,⟨.and,[1,2]⟩,⟨.or,[4,5]⟩,⟨.or,[8,10]⟩,⟨.and,[8,10]⟩,⟨.and,[6,11]⟩,⟨.or,[3,12]⟩,⟨.or,[9,14]⟩,⟨.and,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008242920 * 2 ^ 32 + 4008224896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008242920 * 2 ^ 32 + 4008224896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_12951

open PEqualNP.Outside.L_meta_12951 in
theorem PEqualNP.Outside.L_meta_12951 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008242920 * 2 ^ 32 + 4008224896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008242920 * 2 ^ 32 + 4008224896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
