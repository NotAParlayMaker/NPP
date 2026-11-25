import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_16779.Model
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


end PEqualNP.Outside.L_meta_16779.Model

namespace PEqualNP.Outside.L_meta_16779
open PEqualNP.Outside.L_meta_16779.Model
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

def SBf (j : Nat) : Nat := [6, 6, 5, 6, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_16779

namespace PEqualNP.Outside.L_meta_16779
open PEqualNP.Outside.L_meta_16779.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x4400608030d4090081cf2c314e2802d181bf43de43bd43dd439d43be42bc42de32dc32be41bc41de31dc31bf40bd40df30dd30
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x1102031400196300409000a70082047552438e292871c5150e3ea0a1c754c428faa4651d540ca3aa620c7d52318eaa0631d53d023aa9984755130
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x500006085987548ca0e62d523183189544c2146155130
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 17
  | 3 => 13
  | 2 => 4
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (i*5) 5
  | 4 => packedAt s0K4 (i*16) 16
  | 3 => packedAt s0K3 (i*27) 27
  | 2 => packedAt s0K2 (i*38) 38
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (6+((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s0K4 (297+((h/5+packedAt s0K4 (272+(h % 5)*5) 5) % 21)*6) 6
  | 3 => packedAt s0K3 (371+((h/4+packedAt s0K3 (351+(h % 4)*5) 5) % 20)*5) 5
  | 2 => packedAt s0K2 (156+((h/1+packedAt s0K2 (152+(h % 1)*4) 4) % 9)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x3ffff83fffffffc0fffc1fff83fffffe78f1ff
  | 2 => 0xc0ffffc0fff83fff07ffe0fffc1fe07f9f3e73
  | 3 => 0xff03ffff03ffc1fff83fff07ffe0ff81e7cf9c
  | 4 => 0x3fffffc0001ffffc00007ffff0001f80fe0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x4108888209210402948094901292a282850a5
  | 2 => 0x922911064920608b02952092a4124154932652
  | 3 => 0xa4a22121a44031550265204ca409505458b18
  | 4 => 0xacb3c4a49076b5e69cc318c7739c0619f80de0
  | 5 => 0x30c38738e38739f8e73b9ce063181861fef000
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcc0fcc0fcc0ccc0fcc0fcc0fcc0ccc0fcc0fcc0fcc0ccc0fcc0fcc0fcc0ccc0fcc0fcc0fcc0ccc0fcc0fcc0fcc0ccc0fcc0fcc0fcc0ccc0fcc0fcc0fcc0ccc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_16779
namespace PEqualNP.Outside.L_meta_16779
open PEqualNP.Outside.L_meta_16779.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x56530c090200010140390030460bf43bd43be42bc42be41bc41ee21ec21bf40bd40ef20ed20
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x2800006000096292871d531063aa7a05914520
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | 3 => packedAt s1K3 (i*27) 27
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (6+((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s1K4 (212+((h/4+packedAt s1K4 (192+(h % 4)*5) 5) % 18)*5) 5
  | 3 => packedAt s1K3 (112+((h/1+packedAt s1K3 (108+(h % 1)*4) 4) % 13)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x7ffc1ffffffff03ffffc0ff83fffffe7e31ff
  | 2 => 0xfffffe07f03ffffc1e07fffffc1e07ff93fe4f
  | 3 => 0xf81ffff8003f07ffe007ff07ffe00781e3cf8c
  | 4 => 0x1fffffffc007fffff80007fffff801fc0ff0
  | 5 => 0xffe00000000007fffffffff800000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x9044444122084100a4494848812294a4261095
  | 2 => 0x218888324452822c0a8291932414215890e64a
  | 3 => 0x52d51490eaa44d556144ea45cb40560d634b8c
  | 4 => 0x651a21248c06969a5390308672996011d80d60
  | 5 => 0x861c39c70f38e7e39de73ce063118461ffb000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaaf0a0faaaa0a0faaaf0a0faaaa0a0faaaf0a0faaaa0a0faaaf0a0faaaa0a0faaaf0a0faaaa0a0faaaf0a0faaaa0a0faaaf0a0faaaa0a0faaaf0a0faaaa0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_16779
namespace PEqualNP.Outside.L_meta_16779
open PEqualNP.Outside.L_meta_16779.Model
def s2K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (i*5) 5
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (6+((h/1+packedAt s2K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x1ffe07fffff81c1fffff03fe0fffff007e73fc
  | 1 => 0xfffff81f81ffffe0f81ffffff0780fff93fccf
  | 3 => 0xe0ffffe001ffffff001ffc1fff800fffe38f0f
  | 4 => 0xfffffffe001fffffe0001ffffff001fc0ff0
  | 5 => 0xff00000000001fffffffffe000000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xc22231451041240529272126048a690c26315c
  | 1 => 0x444450c8229208a05a09464a9050a25490d4c5
  | 3 => 0x8aa8a2035525154b0512a9152d014ca9630b0a
  | 4 => 0x14d1049260365a729640c219ca658031d80ea0
  | 5 => 0x18e1c71c79c79f9ce79cf3818c4608c1ffe000
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xeeaacc88eeaacc00eeaacc88eeaacc00eeaacc88eeaacc00eeaacc88eeaacc00eeaacc88eeaacc00eeaacc88eeaacc00eeaacc88eeaacc00eeaacc88eeaacc00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_16779
namespace PEqualNP.Outside.L_meta_16779
open PEqualNP.Outside.L_meta_16779.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x6485674080a0000419400283bf43bd43bf42bd42df32dd32be41bc41be40bc40de30dc30
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0xd004009a28a851d531066ca3205354830
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (i*5) 5
  | 4 => packedAt s3K4 (i*16) 16
  | 3 => packedAt s3K3 (i*27) 27
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (6+((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s3K4 (208+((h/4+packedAt s3K4 (192+(h % 4)*4) 4) % 16)*5) 5
  | 3 => packedAt s3K3 (111+((h/1+packedAt s3K3 (108+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x3fff83fffff07e0ffffc1ffc1ffff03e79f3f3
  | 1 => 0xc1fffc0f83ff87f0f83fe1ffe1e07fc1a67d9c
  | 2 => 0xfe1ffff003ffffff003ffe1ffe007fffc78e1f
  | 4 => 0x1ffffffc0007ffffc0001fffff8001f80fe0
  | 5 => 0xffe00000000007ffffffffe000000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x840088a200808002284c02240229109408b0b1
  | 1 => 0x9449186425240a505a15214d21432584a25594
  | 2 => 0x89221014a4844a50422541254044a29450a0a
  | 4 => 0x295c4249606d57399683111b99960309f00f40
  | 5 => 0x3198738e738e67cee73b998311180c31ffe000
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeaeae8e8eaeae0e0eaeae8e8eaeae0e0eaeae8e8eaeae0e0eaeae8e8eaeae0e0eaeae8e8eaeae0e0eaeae8e8eaeae0e0eaeae8e8eaeae0e0eaeae8e8eaeae0e0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_16779
namespace PEqualNP.Outside.L_meta_16779
open PEqualNP.Outside.L_meta_16779.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x600000002c4800000813224844a25005d380007c0891c68008463c987183450000700003c6ca80000058000002003a000000000c8004002a12060180000020101000c08e001408eff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x437d50087f2a010de54021bf29e817d53d037e87a06f50f40bf296817d52d037e85a06f50b40bf28e817d51d037c83a06f10740beaa4817e53902faa7206f90e40de21c817e52902faa5206f90a40de214817e51902faa3206fd0640dea0c817e509037e81207ed0240bfa9a817c535037e86a06f50d40bfa92817c525037e84a06f50940bfa8a817c515037c82a06f10540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea9881be431037886205f94840bea9081be421037884205f94440bea8881bf411037a82205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30ef99661dd32cc2fca3985f54730ef18e61dc31cc2fea9185f95230beaa4617c548c2faa7185f94a30bea94617e518c2faa3185f94230fd20461f9408c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130ef21a61dd434c2fea4985f14930ef99261dd324c2fea2985f14530ef18a61dc314c3f480987e50130fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca6185f94830bea90617e510c2faa2185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83f681907e10320fd18641f930c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5105f94620bea8c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a417e53482faa6905f14d20bfa8a417c51483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20bf290417e51083eca2105d94420bea8841f551082eaa2105f94020fda0041f840083f460107e4c020f790041fa20083da40107e48020bfaa6217e54c437ca9884f95310beaa621bd54c427aa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb10e21f521c43f641887e08310bfaa4217e548437ca9084f95210beaa421bd548427aa9085f15210bfa9c217e53843bca7085794e10bea9c21dd53842baa7085f14e10bfa94217e52842faa5085f14a10bea8c217e50843f681087e10210fd18421f930843f441087e48210fb88421fb10842fea8885f95110beaa2217c54442fea6885f94d10bea9a217c53442fea4885f94910bea92217c52443ec42887d48510fda0221f840443f460887e4c110fd10221f920443f620887d84110bfaa0217e54042faa8085f15010bfa98217e53042faa6085f14c10bfa90217e52042faa4085f14810bf288217e50043f640087e08010fb88021fa10043ea20087e44010
  | 1 => 0xe5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a857c5350b7c86a16f10d42f7a1285be4250afea2a15f14542bfa8285fb5050af6a0a15f14142fc28285785050afca8215f94c42bea9885bf4310b7a86215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccb7ca9994f95332beaa665bd54cca7aa9995f15332efa1e65dc43ccafca3995f54732bf28665fa50ccaf4a1995f54332fca86657950ccafea9195f95232df2a4653e548cafaa9196f552329eaa4657c548cafaa7195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbbe86997710d32f799265de324cafea2995f14532bfa82657c504cafea8195f95032beaa0657c540cafca6195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef50f41bf296837d52d077e85a0ef50b41bf286837d50d06faa920df94e41bea9c83be43907788720df94a41bea9483be42907788520df94641dfa0c83f741906fca120fe94241bd284837d50907f2a120de54241bfa9a83df53506bea6a0df14d41ee29a835c535077e86a0ef50d41bfa92837c525077e84a0ef50941fba0a83be41506fea0a0df14141bf2a0837e53106faa620ef90c41de218837e52106faa420ef90841de210837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331bf296637d52cc7be6598f74cb31bf286637d50cc6fea918df95231beaa4637c548c6faa718f7d0e31ee21c637e528c6faa518f78ca31ee194637e518c7be6318fdcc631bf284637d508c6fea898efd51319faa2637e544c6faa898df15131de2a2633c544c6fea498df14931ef99263dd324c7ee6298f78c531bfa82637c504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618f7d0c31ee218637e520c7dca418db94831bea9063ed520c6daa418f78c831ee190637e510c7be6218fd8c431ee98863f5310c6fca018fe94031bd280637d500c7f2a018de54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21f719643ed32c86fca190df54321bfaa4437e54886faa910df15221bfa9c437e53886faa710df14e21bea94437e51887de4310fdc8621bf284437d50886fea890efd51219faa2437e54486faa890df15121de2a2433c54486fea690f7d4d21afa9a437e53486faa690df14d21ee29a435c53487dc6490fb4c921fb90a43ee21486fea090fed4121bda82437c50487f0a090de14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf290437e51087de4210fd88421f690843f521086fca010fe94021bd28
  | 2 => 0x638e000000000006800023e000028c622e0e06548908710c2404aa2200000000000030000000ec0c2000000e33ee5bd01800106a48fa20c13c7352d8315105c11e8f04c837882000000710000000003d8ca11d470a58000001000001a0000000a02a9290362c8e40004404bc0000031408c000005040c0000003d49d88c1b82f08e8000003cc1a40000000007c0018d4aa204000000009cc000574d40ec3281a192138858000a07c40008f000a340000038a0000019d47270000000284000d98d63b09940003d000958bb09243459d0ea531a60009f209422000d6a4309a0005028b24c39cd29fc35c11c6722748809c410fa1d06fd3911a4687f8fca932be8fc8426e22a62d3b9b24900000009441e4b82c8f13462643f8be45e9643f18e23830c5081c1569149d0e537c8593f9b000073d3d00008a0011200020c1b0000413068640028a244828d588c4f2000c21130d0980a78a71d279c001615005540000049e000b019f2e200072000190000000641da6f0a2214000170ae8540007553f00d086000be0003c60003d8884960000004c000408fb15412c32c000000000845d9a23e66a00000021e328000390004c85210028c000001230007d44686b00091cc92121a85a85702d18e0149294e3d6780870d737681c6880000037cd20003f40000001715a4c42e9874a87b49e03200052000000000000000cd000a148f9274f05f4548243748100028f4b84a000000000000000583620002d8000004b4002710000013aa9400069cf28080080f01004000020000000801004020000400000000010000002c00004000040500c250040405c0001400000060080000c0000000004040380b0140303c0401008034030000500c03004000000000001008030000200001000010041000008000000140c000000000104c100080701c04008020540a0280000c2c0180102003000000083300001004000000200402020010040602c020140a0940301001018000700101002004000040300401000030040201c0c0040001c00000030280808c000040100c000040602c000800201400000040080300c040000300404028020540000806010040000200000004030000801c070000205402014120100800000030020000a010000003b00009000050000501c08bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021fe94043bd280877d5010ff2a021de54043bf29e857d53d0b7c87a16f10f42bf28e857d51d0afca1a15f54342beaa4857e5390bbca7215794e42bea9c85dd5390abaa7216fd0e42dea1c857
  | 3 => 0x4a81860a2a1d62d873000000000000cf3ba04c0788a0029280000609082c0121700019c00149266168552351362cd4216b1f2048000004800000015e20e6a4cb1502b40cc7f8003969445c0e23321805611b4267248691630c4d82900012e5450f2181a4380e19fb0288391b9e116a9249b8000008ad199520005e548a3c0006e4000004d6000001902cc4ec318ba07e000378fe2d80005f8a63540000e80036c8d817921000310bd8743d2660c8a5d3bc000bd2635202c0ba8a23a40008c86e000000000194be5701a86226058d4087327e000b20db0005f8ad8002a6670cb8000d40000011e0a60001f0c63a81085ca210a2000002740002f40002000000000000000001209f80002140000034276d041a64601e400000000000000000945fcd600051c000bba1b44c70490210000308001344b466800141220000600000000013e8e1000834a5800000529368000000000015936e0441d2860003e00010a3b288cd78b705274514026484100a19ca0003d4b28f21dc679160000fa000ab000000000a38384985305a1ef0000008b800000718000000f82449c86d3ae000f72690000008a2250000000023b3b8000000001fa608001804c2788b10000002c400109000000ff8000000000000000000000145000030000000000000016800028c4487600049000078000001189350007b11483c1ee8140000005877c860004bc000392013c874c6e80001c0001b8002e4000000004000002f0f349c368458000006d00b1400007383d0001aa000de8003985cc0009f4cc8c805a620001c4001850060000018f000000680dc3e41249e8ef0000004c0000007a0000442e89a0ab8005060000005614a808660000007587e2874a0268038000004452b8ea0002a000246000000ed0000007f4a6a1f2585a4470000be0100402b310a2423000000a5c000d94e03d116a6c2da24c1100042a000e126703c0005e07513a40c000fb00004082981518000150000cc13ce80d8326a550e0000000012c08420212ccda7b2545612696e4f8314959f036a624002522700245780002a1dc4e00005c9bc0003
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x2434c25c6550d30a7593324c31c54cc930b6983324c31c544c930d3149324c31c548c530a7590314c31c540c530b3588314c2da600c530ce152404c39a43901309e195404c39943501308f596540c23e64150309798c540c27a6015030c7553300c339548c03097d95300c31d544c0309ed95300c339544c0309798f54c825d63d53208f99353c823d64d4f208f99253c823d6494f208fd9151c823c645472097d8d51c825c6354720b658c40c82b8644c3209798c548825d63152208fd91538823c6454e208f990538823d6414e208f992518823d64946208f992544827b60551208f994544823e6494d208f59253482796094d208fd91534823c6454d209dd8553482746154d20ce153204825e63d50209758f540827661d50209d587540823d6595020ce181540823e64150209798c540825d63150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530835a6094c20c7951530831d5454c208f990530823d6414c209798c53082766114c209d58453083365494420cd55251083565394420d554e51083365454420cd55151083565354420d554d51083706054420ce553400837151d00209e59440082d96310020dc5444008279658c020ce5523008371518c020ae1913008339544c020d694d3008371514c020dc546200826f65480209ed9520082b86448020dc545200823e64d4f108f59353c423e6414f108f59053c426e6214f109b58853c423e64d4b108f59352c423e6414b108f59052c425e6314b109758c52c42f06048710ce95320c433a5408310bc58420c425e63d52109758f548433860552109798c548425d63152108f993538423d64d4e10c7952538431d5494e10d6982538431e5454e10c7551538423e6414e108f590538423e64d4a108f593528425e63d4a109758f528423e6414a108f590528425e6314a109758c528433954d0210b658c4084339548c210ae1913084339544c210d694d30842b86448210ae993108425f63551109718d544426f62551109b189544423f6454d108f191534426f6254d109b189534423e6414d108f590534423f64549108f191524425f63549109718d524427b60549108f990524423d64149109798c524425d63149109d195214427a65d0110b658c4044278654c110ae19130442f0614c1109e99620442786548110ae19120442ba64c41109e983540425e63150109758c540426e62150109b588540423f6454c108f191530423e6414c108f590530426e6214c109b588530427a6014c108fd91520423c64548108f990520423d64148109798c520425d63148109d984520427a60148108f992510423d64944108f992500423d64940109798e500425d63940109e59720042796508010bc584200427965840109dd95100427b6544010
  | 1 => 0x69e63908418fd95411069c63504419dd95411067a60153319e58054cc63e6494b318f59252cc63f64543318f19150cc67a60d52319e583548c6d96010e318fd91528c63c6454a319ed81528c6786054a31a7992328c63e64942318f592508c63e649513197d8d544c63e651513197997324c71c54cc931c7151324c71c548c5319b98b540c66d62d50319e983540c67960d50318f596540c71c63550318f990540c66e62150319b588540c67a60150319e580540c71d54d0c3197594430c6d96010c31cb952520c72d5494831cb951520c72d5454831d3d0d520c74c435483197596320c69e648c831d354a320c74d520c831d354b310c65f654c431a7191310c74d524c4319dd95310c73a5494031ce552500c76a5294031da54a500c73a5454031ce551500c76a5254031da549500c65e63d53219758f54c867b60553219e18154c863e64d4f218f59353c863e6494f218f59253c867a6094f219e58253c863f64543218f19150c867a60d52219e583548865f63552219718d548863f6454e218f191538863e6414e218f590538867a6014e219e580538863e64942218f592508865e63942219758e508863e64951219798e544865d63951219e9825448679609512197d8d544865c63551219ed81544867860551218f994544871f54d4d21c7153534863e6494d218f592534865e6394d219e98253486796094d218fd91534863c6454d219ed8153486786054d2197994534871f5414d21c7150534874d6214d21d314e324866c654c921ced53504873854d4121d6d4f504875853d4121ced5050487385414121d6d4c504875853141219798f540865d63d50219e983540867960d50218f596540863e64150219798c540865d63150219e980540867960150218f993530863d64d4c219e983530867960d4c2197596530871e5494c21c7552530871e5454c21c7551530863e6414c218f590530865e6314c219b988530867a6014c219e580530874d53c84219bd95210874d53484219dd95210873a5494021ce552500875a5394021d654e500873a5454021ce551500875a5354021d654d50087722154021dc485500865e6394b409758e52d02b86050b4097d8d51d025c6354740ae98241d02b96010e40a798e429029c63506408f997435023e65d0940ae18142502ba60905408f994415023d6590c40c754e431031d5310c40ae580431023d6590840a798e421031d5390840c754c421031d53d04408fd95411029c6350440c754d411031d53d0040d654e401023f6550040c754d401027b6550040d654d401026e62d53309b58b54cc23e6494b308f59252cc29d64ccb308fd9151cc23c6454730a759031cc2cd620c7309d987548c27561d52308fd91528c23c6454a308f992518c23d64946308f992544c23e6515130c758c544c3396015130c715
  | 2 => 0x62ea1141f00032a0000017d1fa7200000036a1740e1d213c118cea01350000a40aa0983645b91b3107643e02e3a283c2218e11e0010592f096000561020e6590000000a47385792e37a000000f12b4844619cf1b4000fb81823c000b50fb2aa815040511e000047115000104000001f40140021a21a78ca21d431800c439a110a0004a19732279ca980027e72c000bb142588611c331a84c1807a1ca51cff98a000184db1ee3e03e0821831c853c0014b0d04200c8003841802815b23e0c4719de332170b29ba1804b0e00673785f8001960ca4dcff0c702c1c43189d2987843da0e432000eb1781067b41e87700037c4d9b1120000001390000009116c00006c0001a1fc80103117000000f49a4122614000f31ee000848be2543a868a1513200000000120000501c08008020103500401028561480300003060000000001400064050000200000000010bc0501c01010050140000031004100201000805000090f8290901c008010100301c010100101c0100c070000108817010090003f0100500000000030080600c0e00c090002d0101e01c03008010340108c0301800124000000001c000000901c01034030141f0080c008020000b00002024000282d0ac00000040141200800044050001d00802008010000f074280441101c0400c1204001040060000801002098140b0000580000000000000a00000c030300500e7b6054b439e18152d0e7a60947439e58251d0e3f6550c4397d954310f3b4354043d690d5010f394354043d650d5010eb96010f429e98251d0a7960947429e9825390a796094e42d69825390b596094e42c794f4390b1e5350e42c794f4290a3e6510d42ae5804350a9e63909429798c5050a5d6314142d698c5050b596314142ce90c5050b384314142ce9085050a3f6550c428fd954210ab860508429bd954210a5f63544429718d5110a7a60d53329e58354ccb1c63553329e98054cca796015332c755343ccad96010f32ce95250ccb395494332ce95150ccb395454332c7953328ca7761551329d185544ca7b60551329e181544ca5e65d0d32b6580434ca9e648c9328f990514ca3d64145329e980514ca7960145328f990504ca3d64141329798f540ca7661150329d584540ca7a60150329e580540ca3e6494c328f592530ca3e64948328f592520ca5f654c8329bd95320ca3f64544328f191510ca3f64540328f191500ca5e6394b419758e52d06b86050b41ae580439069e6390a419798e509065d6394241d698e50907596394241ce90e50907384394241ce90a50907384294241ced06509067a6014d419e580535075a6014d41d6580535063e65d0d41c714f435071c5350d418f997425071c53d0941c714d42506b86050941c714e41506ba60905418f59643106b96010c419ed81521067860548418f596421
  | 3 => 0x9e182012000740000087d4e0800000768bd00000033d03a12300828680ab06e044a302f31e00000047000000ac950330000001233e844ca50001b025c6316f0aa6fcb81a929c000ea8f21a6000000e02ce000b08000007a8ae0760502c0421dd04c67cb587f260610dc1361ac2a4571d83cc5ccd793340613c11a0d1d264880956200254f00c505658c038ce01a7908d0b41ba4c41c16d1445482f84a3d06d0f895f0582f09a96e0b06b8a19b31400d0190660841201f8102a2688bf85e2a83e48c879024840d290f256448d188836076c83a09018020b305b28436d0b0c43b82048c0de39a670e28cc1825f0828fc2ba6509f1ac3400000a01e3a661cd50000003985898b0005d0e2138248230368622822008e9ec1121d10b83b0000b4001bb000100000001d63704902124a678778271902a0fd981052000900490002080a80006c0005f8752f25c8fb1c70020005c8220003d8761863d60005380b2d21bc93149320150e48e2264095011b221c3487a85625a0e50a09a34c1c0bb80f326190bd916026028f10331661a44f8d50fa2709383c34e2e0739f8192000eb9fd0001387680035a8300014033600000171372450521603e47f0659fa16c668a286a252000000ca20c3fc298000e4484121d00541f8f988a000000ef80000c000000000003b8bb0f40004300005a1644a02695e2d00000010a000000c49be000001020a30000745e9ef02e3342b93d268000360e113007c100ba2742342c83a0007e50c000356298528d720642ca69ca00424c889583981e0f28350001b85a8ad276000000d4000000db9572207180008b0002188e00e0860003589
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0xd0103c02571c05560014980004ca14018200000e2c43144400032000000000c00038210b465c25350e42a34e7210a0a15197018d54cca8d39c8528483465c05350d41c30a630284a0e1853982415068cb80c6aa063525c04354831c1cc8a946418e0c64549310c64cb98c0a1281265ce6090540c32c6b00a89841d76153324c20ebb0a818a6183151620c530a32e6302a81065163544400821c3b2a8980418c191514c020c60c8a8a40106325458420c428cb98c0aa4210e1d9544c210
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x20190819869ce4214142819869ce42942418198714c60509418198714e6090541
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
  | 5 => packedAt s4K5 (20138+((h/221+packedAt s4K5 (17928+(h % 221)*10) 10) % 963)*11) 11
  | 4 => packedAt s4K4 (22272+((h/179+packedAt s4K4 (20482+(h % 179)*10) 10) % 647)*11) 11
  | 3 => packedAt s4K3 (1273+((h/8+packedAt s4K3 (1225+(h % 8)*6) 6) % 40)*6) 6
  | 2 => packedAt s4K2 (243+((h/1+packedAt s4K2 (240+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x83fff81ff87e3e1f0f878ffe3fc0e0fe21f793
  | 1 => 0xfc0fffe0ffffc3e00ffff0ffc3ffff003e79fc
  | 2 => 0xfff0ffff007ffffff007ff0ffc00ffffc78e1f
  | 3 => 0xffffff8003fffff8000fffff0003f80fe0
  | 5 => 0xffff0000000003fffffffff000000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xa86288c62494620583c189962646225a20b391
  | 1 => 0x920114240200440048a902240924a080a50b4
  | 2 => 0x10842208114800aa10042208880894a0c50c0a
  | 3 => 0x52cac490940cab33a950088d332c0433700f40
  | 5 => 0x630c871ce67133dcce674cc0223018c3bfe000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfce8fce8ece0ece0fce8fce8ece0ece0fce8fce8ece0ece0fce8fce8ece0ece0fce8fce8ece0ece0fce8fce8ece0ece0fce8fce8ece0ece0fce8fce8ece0ece0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_16779
namespace PEqualNP.Outside.L_meta_16779
open PEqualNP.Outside.L_meta_16779.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d02fca5a05f54b40dfa1681bd42d02fca3a05f54740beaa4817e53902faa7206f90e40de21c817e52902faa5206f90a40de214817e51902faa3206fd0640dea0c817e509037e81207ed0240bfa9a817c53502fea4a05f14940dfa1281bd42502fea2a05f14540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea9881be431037886205f94840f7290816e52102faa4207b54840b6a9081be421037884205f94440fb288817651102faa2207d54440baa8881bf411037a82205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30ef99661dd32cc2fca3985f54730ef18e61dc31cc2fea9185f95230beaa4617c548c2faa7185f94a30bea94617e518c3eca3185d94630bea8c61f5518c2eaa3185f94230ef98461fb308c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c3bc86987750d30bfa92617c524c3be6498774c930bfa8a617c514c3bc6298770c530fd98261de304c2fea8185f95030beaa0617c540c2fca6185f94830bea90617e510c2faa2185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c82fca3905f54720fda0641f840c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5105f94620bea8c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a417e53482faa6905f14d20f721241ed42482fea2905f14520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4105f94420fb288417651082faa2107d54420baa88417e50083f680107e10020f790041fa20083da40107e48020bfaa6217e54c437ca9884f95310beaa621bd54c427aa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43ee63887d0c710fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10ef29c215e53842faa7087754e10aea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fda0421f840843f461087e4c210fd10421f920843ee21087ec4210bfaa2217e54442faa8885f15110bfa9a217e53442faa6885f14d10bfa92217e52442faa4885f14910fb20a21f541443ee62887d0c510fb10a21f521443f680887e10110fd18221f930443f440887e48110fd88221f610442fea8085f95010beaa0217c54042fea6085f94c10bea98217c53042fea4085f94810bea90217c52042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xe5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7c87a16f10f42bf28e857d51d0afca1a15f54342beaa4857e5390bbca7215794e42bea9c85dd5390abaa7215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42df21a85bc4350bde84a16f90942bfa8a857c5150afea0a17ed4142bda82857c5050bf0a0a15e14142bf2a0857e5310afaa6215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332efa1e65dc43ccafca3995f54732bf286657d50ccafea9195f95232df2a4653e548cafaa9196f552329eaa4657c548cafaa7195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbbe86997710d32f799265de324cafea2997dd4532bba8a657c514cbe8a2995d14532bfa82657c504cafea8195f95032beaa0657c540cafca6195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef50f41bf296837d52d077e85a0ef50b41bf286837d50d06faa920df94e41bea9c837e52906faa520df94641dfa0c83f741906fca120fe94241bd284837d50907f2a120de54241bfa9a83df53506bea6a0df14d41ee29a835c535077e86a0ef50d41bfa92837c525077e84a0ef50941fba0a83be41506fea0a0df14141bf2a0837e53106faa620df94841bea90837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331bf296637d52cc7be6598f74cb31bf286637d50cc6fea918df95231beaa4637c548c6faa718f7d0e31ee21c637e528c6faa518f78ca31ee194637e518c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c6fea498df14931ef99263dd324c7ee6298f78c531bfa82637c504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618f7d0c31ee218637e520c7dca418db94831bea9063ed520c6daa418f78c831ee190637e510c7be6218fd8c431ee98863f5310c6fca018fe94031bd280637d500c7f2a018de54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21f719643ed32c87ee6390fd0c721bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a43df53486bea690df94d21bea9a437c53487b8a690d714d21f719243ed32487ee4290fb88521bfa82437c50486fea810df95021df2a0433e54086faa810ef550219eaa0437c54086fea610df94c21ef298435e53086faa610f754c21aea98437c53086fca410df94421fb98843f431087de4210fd88421f690
  | 2 => 0x1ed198004da7c41b8380000001408c4a25307e9330009993421015621c3508a28a784c588f22a4613180030052927a0526071c9e04a1942e12fa550006d0fca213dc494151433d27652b9103224908010e24694caf1962b2780d80e32e42f5208ed2521d4c60000000005a0b02f836c000774906b4b70d82767000017503e83c430000c2624078522de1f9120012065a024a732686a4b803e46c208340bb2da11d231c106a5d0550002164bc631543209ac8685416e4d8fe00033a511378004700003594b00056c96a294122a07102027c9400025b364000000001862489ea6c2ca0ad3b0002c2138001aa00028d23a01000000f3a223bc1146d2171fe78d1a9ec4404e44980c00000004000042000b49a017e9844e244000730e48044ea00000042000088118001be0001e02d22c408a09ac000518d72080005000007324c0000000000000026a5c1ba0e800000098310970f511a6710c1a74b22453295a1c060d200883783b04589f47e8dc310002280010a08419c024a723c270298b122c4389743c0b31c86e02f9281345c42d87d0cc7442b94231c5d8472251b89b82b1a32cc10cee1d0212050321811a2754de8c81e20000a9cd4223e12d17a33e000aea314a86a04a11931e3d8000004a46d4fd15f08c855171eb2f02d52103d24e8345905a242654ff9732d461cc111c2a40bc4081c1ac164038d930c54c678f02223541721d1f2684c422b1365544f0fb1e61e40313a3d48785624d2926490b2674c05fcca1ed01a348e90e81781bc709773b076cb010f3363241f880184570b19e41ee51c5781e38a560fba4b4047cca69ab3082b8380511f86f8ef8893e839c0ba4c27e475392030f82f81a04112a4c42a99820c6bc2221f434768259a50ec90ccf1b6006430ee85c02c6145b16b2fa178962193e088c3291e2f67088d197120698d890748a03c0500c570dc25004020800e1e8020bc1900c020d00003800000000000405c0003c0a0000500000000192a006020000040200405024000542c0001e00009000000080b08840104010140001c00044030000d01c07000120000c008020000100c050402a0001101c07008230001d0000000001008220380c0400004c0002805008060040c00000058000c070008060000000404000000100308438000010000a00800000070000000803000000880200400000460340300c850140000c09024010100900c260201a0140d18c0500011004030000f01001074a500026000920000c024030000001c06024020080704007004000200201803000030000b034050240d0b00101001bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877
  | 3 => 0xd98003940c48d8f41de9dc6a09d00a075130a225470c7d097426041249bf40c3b81b1c409e06c000000008e4cc80006020c9b86c0b00000023b00000103871372100699d43c4334000002261408906d1bc9a4f4234396838fb00000082c098b10007f45682700062801000000000000004e88c00000019814c639483cc3940024a0000005225604c6ec910d014e1a4a78744bc060bf2124c4284001ba3e4404bc8002ce001350000242606288501c32c0018d0000b0000000000000000020a000aba2a3ae000000002640007f0000004d40016c39c410000002a00012c0ba00042805896000831271fb1520c91e8670228bc3d00a45a9c4fc1e52c8000128f2076304f780047464d320630003ac3f99a000295051c800006519000348264e300017247c0023e0ba3a839039000000001a23a6000000000000008b8003ac81000000034000000480004ad0da702407f8000002a2000148004007d48415636e3a5140e6140300120600661b9139cf1ae
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x831cc27661d52309d587548c26e62152309b588548c27661152309d584548c23e64946308f592518c3366494630cd592518c3726094630d5947308c23e64951308f994544c31d6315130c7152434c25c6550d30c7153324c31c544c930d3149324c2d4614c930c7152314c29d640c530c7150314c2cd620c530b6980314c2d6618c1309798c540c26e62150309b588540c27661150309d584540c25f654c0309ed95300c25e63d53209758f54c823e64d4f208f59353c82776154f209d18553c82e86050b2097d8d51c825c6354720ea50b40c82e96210320ea90840c825e63152209758c548827661152209d584548827661d4e209d587538823f6454e208f191538823e64946208f592518823e64951209ed81544823e6515120cb588544823e6494d208f592534823f6454d208f19153482776154d209d185534832c54909209b195424833854c81209798f540825d63d50209d987540827561d50208f596540833860550208f990540825e63150209758c540826e62150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530831e5454c20c7551530823e6414c208f590530825e6314c209d98453082756114c20cd95251083355494420d594e51083555394420cd95151083355454420d594d51083555354420ce553400837151d00209e59440083715110020cb553200837151880209bd95200832d54480209ed9520082b86448020dc545200833661953108f99353c423d64d4f108f99053c423d6414f109b98853c426d6214f108f99352c423d64d4b108f99052c423d6414b109798c52c425d6314b10cd95141c42d46350710ad59031c42e5620c710b518d21c425e63d52109758f548425e63152109758c548426e62152109b588548435a6094e109798f528425d63d4a108f990528423d6414a109798c528425d6314a10b658c40842e96210210ae191308435a534c210ae191208435653c4210ae993108425f63551109718d544426f62551109b189544423f6454d108f191534426f6254d109b189534423f64549108f191524425f63549109718d524423e64149108f590524425e63149109758c52442f260905109d19541442d463505109d99731442b5640c510b958831442f2600c5109d19521442d463485109e99740442d96310110ba58840442f26110110ec50440442f2618c1109e19530442b8644c110f40c530442786548110ae19120442ba64c4110b598e104427a60d50109798c540425d63150109b988540426d62150109d984540427661d4c108f990530423d6414c109b988530426d6214c109e980530423e64148108f590520425e63148109758c520427661148109e980520423e64944108f592510425e63940109758e500427965840109dd95100427b6544010
  | 1 => 0xca3d64145329e980514ca796014532cd990514cb356414532d5d0c514cb544314532d58c8514cb726014532dc580514ca5e63d50329d984540ca7561150329e980540ca7960150328f992520ca3d649483297d95320cad4614c8329bd95320ca3f64540328f191500ca5e6394b419758e52d06b86050b419798e509065d6394241d698e50907596394241ced06509071c53d0d41c714f425071c5350941cb14942506b86050941ae982415063f65504419dd95411063e6494b318f59252cc6d4614cb318fd9150cc63c64543319e983548c67960d5231a7992328c66e62951319b58a544c65f635513197997324c6d4614c9319b98b540c66d62d50319e983540c67960d50318f596540c71c63550318f990540c66e62150319b588540c67a60150319e580540c71d54d0c3197594430c6d56110c31cb952520c72d5494831cb951520c72d5454831d3d0d520c74c4354831d9185520c65d658c831a7992320c74d528c831d3548320c74d52cc43197d95310c74d524c4319dd95310c73a5494031ce552500c76a5294031da54a500c73a5454031ce551500c76a5254031da549500c65e63d53219758f54c867b60553219e18154c863e64d4f218f59353c86e4614cb21f14cb31c86e5620c721f18c831c863f64543218f19150c867a60d52219e583548865f63552219718d548863e6414e218f590538867a6014e219e580538865e63942219758e508865e63951219758e544865f63551219718d544867b60551219e181544865e6394d219dd85534865e6514d21d3588534874c538c9219b195324875453c85219798f540865d63d50219e983540867960d50218f596540863e64150219798c540865d63150219e980540867960150218f993530863d64d4c219e983530867960d4c2197596530871e5494c21c7552530871e5454c21c755153087546154c218f990530863d6414c219798c530866e6214c219e98053086796014c21d554f3108675650c421d354f210866f6548421d354d21086776548421b518d210873a5494021ce552500875a5394021d654e500873a5454021ce551500875a5354021d654d50087733154021dc0c550087722154021dc485500865e6394b409758e52d02b86050b4097d8d51d025c6354740a798e429029c63506408f99742502b86050940c754e43102b96010c40d394e521034d5394840d394d521034d5354840cb90d521032c4354840da181521023d6590840a798e421032d5290840cb54842103565394440d554e51103665294440d954a51103726094440d594d51103555354440d994951103655254440c754f411032d52d0440a718d411031d5350440cb54941103365150440cb54b401023f6550040cb549401027b65500409b98b54cc26d62d53308f99252cc23d6494b30b518532cc29d640c730b358
  | 2 => 0x194001aa538000032c00220e0b68000000000010800001ba9d31aa0b720a000000009e800000fc97a98b69fc000000021c4a8006ba54c2a2e0027e3609a9220ae397a679cc2401812096cf18e9800078b5e3f910cc2e283b7034000000000019c4c000b51be77208dd2c817a4eb38000f89475b78e880000000001ee1e800000000000074332b81c2c49c4d4960002ca7ab6c00000929728506027020001880431ce2b9ce512ce9a96b996ad0000000001011400000d1b0800000003001fadcd5b1055000001f2000ac9b2b25a2b073a8800000001241f222000004dae4001e401000d600000174d403c00000a1000ce00037aa0900b609800002a40000000264de9a2a88000000000000000c47e800c8b96478007527c000000000000000000008e00600000d10e8142065e0000005854250559c0698008c080bbac40029035b4a8f80087800b080000158000000000030000000005f25600000b0102000a2388d2681b002b04001b2ce9f0e02be00000002340000000000000000000000142a30980000c39a443b04a000000000e002280037600000002d81c32661b2ed38c80cb02001440b000000f6000000019200000000000000000000000000035a000c646b900000086266cda2c0e86e0025cc504400000170000008e000a800000000005b2bc8a8a600000b30000023200000cf800001b607210c1998748003739a00000488000035c00212000000015c003a80000000000000722234c001387e09e00000c600020ab61d3a40011c088005180000236000000000000000961000018a9d8007d85200000133a0810fa80b1e002700000000200003aa0000000002db800000000d3549c8007a000e18001a15a719340017000c0801002000000000000400000000300200000000040080000416004000040200401010000000201c030000e0100000000004040540700809008000100001c000080700005004000000500c04004030000100002000020000100416004000040100402000000000801801028100040000401004000000300c030000302002008020000f00c00014000040100800018020040301c020080300817038000000000000018000000101800000020000002000000000000200400000000240000409008000067a60947439e58251d0e7661942439d5865090e3f6550c4397d954310e7a60947429e58251d0b1e53d0a42ab98a4350a9e63909429798c5050a5d63141429d9845050a756114142d698c5050b596314142ce90c5050b384314142ce9085050b726114142dc5845050a3f6550842ae1814210a6f655084297d8d5110a5c63544429e98354cca7960d53329d98650cca756194332c7953328ca7661951329d586544ca7761551329d185544ca7b60551329e181544ca5e65d0d32b398b434ca9e648c9328f990514
  | 3 => 0x933848330cd8224000b4a78006139e0028e7f980bf05a0014aba2aa86b6ac90b2640002e940000006a16ebe01e599bc368000008a000f091bae6e2fa000000017e00000002f6000002e0000000048000df000000002f04ea1976001080000000000cd000ca80059000002a60012641b0e001e0001f4000000013ce2000000004100076b620001a85a9200348b59c8ec2de2a8000a9e657b66531ca000000000000000a5000439a4000000000000000230121992e001b4000764f80000162000009e3163e2a800000000ea6b000000b0668861b038bf800001120026e002b80023cae8e03c800bb000000cc3bad20023a002b46300096800bd05418800bcaac0000002000d0800000f4000000000000000460002128a7780024800a713a1926200014003ac002681a8160029a00226002ae458000c00000280430002f800e30e4003204280000132b4046158a030b92001d800182b180000000d903600000292ea1e0ae548ce000ca908000b8000000094b284a02452000df8007b000350000000000000000000000000000000000026a002f0e619600
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0xb54e05770530f00a0080c05192404c000401160735609b49a1900648c50029a79b4a9ca4314142a34e7210a0a1651635845050aa33968628a65459d23214532c62c8b00a299618531814250714290c0a1283515c44354831ac2e030aa418e0e6454a320c662bb46418e43541cd2154021a52e021aa42056171181521030731aa5210818318d5250440c28a830a649864452185324c20ebb0a818a6183151620c530952ed21081906306454520082c839a8220221a458d4110110d42c4a088088591740c530443483206298221705c8314c110
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x8100000c8073589411011089187190314c110c80645c8314c110
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 632
  | 4 => 473
  | 3 => 29
  | 2 => 3
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s5K7 (i*5) 5
  | 6 => packedAt s5K6 (i*16) 16
  | 5 => packedAt s5K5 (i*27) 27
  | 4 => packedAt s5K4 (i*38) 38
  | 3 => packedAt s5K3 (i*49) 49
  | 2 => packedAt s5K2 (i*60) 60
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s5K7 (6+((h/1+packedAt s5K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s5K6 (718+((h/13+packedAt s5K6 (640+(h % 13)*6) 6) % 49)*7) 7
  | 5 => packedAt s5K5 (19164+((h/210+packedAt s5K5 (17064+(h % 210)*10) 10) % 759)*11) 11
  | 4 => packedAt s5K4 (19544+((h/157+packedAt s5K4 (17974+(h % 157)*10) 10) % 829)*10) 10
  | 3 => packedAt s5K3 (1475+((h/9+packedAt s5K3 (1421+(h % 9)*6) 6) % 35)*6) 6
  | 2 => packedAt s5K2 (184+((h/1+packedAt s5K2 (180+(h % 1)*4) 4) % 11)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfe1ffff03fc7c70f1e3f1fffc7e0707c19f793
  | 1 => 0x1fe078ffc3fff8f01fc7e381f8ffff8066c9fc
  | 2 => 0x1fff80fffc07ffffe007fc01ff007fff870e1f
  | 3 => 0xe00000fffff800fffff80001ffff8003f80fe0
  | 4 => 0xffffff00000000fffffffffe00000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x42431011880888010609048cc1231118085391
  | 1 => 0x44490122890201200a4321144849250822c0b4
  | 2 => 0x88842244109500562004482112044a61850c0a
  | 3 => 0x819654892281929b54900049a4960232d80f40
  | 4 => 0x1118600e332624ec9926927000180c4377a000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeeaece0feeaece0feeaece0feeaece0feeaece0feeaece0feeaece0feeaece0feeaece0feeaece0feeaece0feeaece0feeaece0feeaece0feeaece0feeaece0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_16779
namespace PEqualNP.Outside.L_meta_16779
open PEqualNP.Outside.L_meta_16779.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x111500028d763169d5401b0000ccd1e00817b91285b801e0400a586402600183ae6a219343689480487c5ba0601c302a0022b289493c6240b964660e002639e804e181810110040002a004801008700263c18000ffd50037f5400ff95003fd5400df55003fc54017fd4c05fe53017f54c05fc5300ffd0c03fe4300ff50c03fc43017fd4805fe52017f54805fc5200ffd0803fe4200ff50803fc42007fcc801fe32007f4c801fc32017fd4405fe51017f54405fc5100ffd0403fe4100ff50403fc41007fcc401fe31007f4c401fc31007fc8401fe21007f48401fc21017fd4005fe50017f54005fc5000ffd0003fe4000ff50003fc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x842004ff14210027fe8108013fe4084009fea042004ff10210027fe6108013fe3084009fd1842004ff4c210007f26108013fc3084009ff9042004ff88210027f44108013fd2084001fc9042004ff08210027fe2108013f71084007fd8842009ffd951004dfeca88027fe65440057f32a2009ff5951004dfaca88027fc65440057e32a2008ffd9110045fec888023fe64440037f3222008ff59110045fac888023fc64440037e3222008ffd5110046fea888023fe5444011feaa22008df55110047f8a888003ff63440017fb1a2000ff98d1003dfcc688003fd63440017eb1a2000ff18d1003df8c688027ff5344013ff29a2009ff54d1004ff8a688023ff4344011ff21a2008ff50d10047f88688003ff62440017fb122000ff98910005fcc488003fd62440017eb122000ff18910005f8c488027ff5244013ff2922009ff5491004ff8a488023ff4244011ff2122008ff50910047f88488003ff3244001ff1922000ff4c910007f86488027ff5144007ff28a2009ff5451001ff8a288023ff4144007ff20a2008fd90510047fa8288023f54144007fe20a2000ffcc51001ffc6288003fd3144007fe18a2000ffc851001ffc4288003f62144001fe90a2000fd4851001ff84288027ff5044009ff2822009ff54110027f8a088023ff4044009ff2022008ff50110027f88088003ff3044009ff1822000fe8c110007fa6088003f93044009fe1822000ffc8110027fc4088003fa2044001fe9022000fe48110027f8408800fff1044007fd8822004ff84110027ec2088013ff65040097fb282004ff99410015fcca08013fd650400d7eb282004ff19410025f8ca08013ff64040097fb202004ff9901000dfcc808013fd640400b7eb202004ff19010025f8c808017ff540400bbfaa02005ff9501002ffaa8080177d540400bfe2a02004ffd8c10025fec608013fe630400f7f3182004ff58c10005fac608013fc63040097e3182006ffd4c10037fca60801bfd530400dfe2982005ffd0c1002ffc8608017fd430400bfe2182004ffd8810025fec408013fe62040017f3102004ff58810005fac408013fc62040097e3102006ffd4810037fca40801bfd520400dfe2902005ffd081002ffc8408017fd420400bfe2102000ffcc810007fc6408003fd3204001fe1902003bf9841001ffea20800ffe5104007fea882003ff1441001ffe820800ffe4104007fea082003ff1041001ffe620800ffe3104007fe9882003ff0c41001ffe420800ffe2104007fe9082003ff08410025fcc008013ff5004009ff2802004ff54010027f8a008013ff4004009ff2002004ff50010027f88008013ff3004009ff1802004ff4c010027f86008013ff2004009ff1002004ff48010027f84008013ff1004009fb8802004ff84010027f42008013fd1004009fa8802003fe44010
  | 1 => 0x3fc510801fffa08400fff9042007ffa821003ffc4108001ff9884000ff8c420007fa6210003fc310801dff9084000ff88420007fa421003bfc21080097f3004004ffd4020027fca010013fd5008009fe2804004ffd0020027fc8010013fd4008009fe2004004ffcc020027fc6010013fd3008009fe1804004ffc8020027de4010013fe2008009fd1004004ff48020027da4010003f92008007ffb2e2003bfd971001ffccb8800afe65c4007bf32e20029f9971001ffacb88036fd65c4007beb2e20009f5971001ff8cb8800efc65c4007ffb262003bfd931001ffcc988006fe64c4007df3262001af9931001ffac988032fd64c4007deb262000af5931001ff8c98800efc64c4019ffaa6200cdfd5310067fca988033fd54c4019beaa6200cff1531001ffec78800eff63c4007ff31e2007bf98f1001ffac788002fd63c4007fe31e2003bf18f1006ffea788037fe53c401bfea9e200dff14f10067fe8788033fe43c4019fea1e200cff10f1001ffec58800eff62c4007ff3162000bf98b1001ffac588002fd62c4007fe3162003bf18b1006ffea588037fe52c401bfea96200dff14b10067fe8588033fe42c4019fea16200cff10b10007fe6588003fe32c4001fe9962000ff0cb1001ffea38800ffe51c4007fea8e2003ff1471001ffe838800ffe41c4007fb20e2003ff50710067ea838800ffc41c4007ff98e2003ff8c71001ffa638800ffc31c4007ff90e2003ff8871001fec438800ffd21c4001fa90e2003ff0871006ffea188013fe50c401bfea862004ff14310067fe8188013fe40c4019fea062004ff10310007fe6188013fe30c4001fe9862004ff0c310007fe4188013fe20c4001fe9062004ff08310027fecb08012ff6584009ff32c2002bf99610026fccb0800a7e6584009feb2c200bbf59610026facb080027d6584009fe32c2004bf19610027fec908012ff6484009ff3242001bf99210027fac90802afd6484009fe3242004bf19210057fea90802b7f5484015ff2a4200aff55210056faa90802bfc5484009ffb1c2004bfd8e10027fcc70801efe6384009ef31c2000b798e10027fac708002fd6384009eeb1c2000b758e10027f8c708012fc6384017ffa9c200bff94e1005ffaa70802ffc5384015ffa1c200aff90e10057fa870802bfc4384009ffb142004bfd8a10027fcc508002fe6284009feb142000bf58a10027f8c508012fc6284017ffa94200bff94a1005ffaa50802ffc5284015ffa14200aff90a10057fa850802bfc4284001ff9942000ff8ca10007fa6508003fc32840117eb0c200bffd461001ffca30802ffd5184007fe28c200affd061001ffc830802bfd4184007fe20c2000ffcc61001ffc6308003fd3184007fe18c2000ffc861001ffc4308003fd2184007fe10c2004bf98210027fea108013fe5084009fea
  | 2 => 0x200aff8a510053ff4288029ff2144014ff50a200a7f88510003ff3288001ff1944000ff4ca20007f86510013ff6188009ff30c4003bf98620027fac310002fd6188009fe30c4015ffd46200affca310057fd518802bfe28c4014ffd06200a7fc8310053fd4188029fe20c4000ffcc620007fc6310003fd3188001fe18c4000ffc8620007fc4310003fd2188001fe10c4004bf98220027fea110013fe5088009fea844004ff14220027fe8110013fe4088009fea044004ff10220027fe6110013fe3088009fe9844004ff0c220027fe4110013ef2088001fd9044013ffd952009dfeca900037f65480013fb2a4013ff99520015fcca9004ffd65480277eb2a4013ff19520015f8ca9004f7c65480053e32a4012ffd9120095fec890003bf64480015fb224012ff9912000dfcc89004bfd64480257eb224012ff1912000df8c89004bbc64480035e3224012ffd5120096fea89004bfe5448025feaa24012df55120097f8a890003ff63480017fb1a4000ff98d2003dfcc690003fd63480017eb1a4000ff18d2003df8c69004fff5348027ff29a4013ff54d2009ff8a69004bff4348025ff21a4012ff50d20097f8869004fff5248027ff2924013ff5492009ff8a49004bff4248025ff2124012fb90920097fa849004bed4248025fe2124000ffcc920007fc6490003fd3248001fe1924000ffd8520005fec290003fe6148001feb0a4000ff1852001df8c29004fff5148027ff28a4013ff5452009ff8a29004bff4148025ff20a4012ff50520097f88290003ff3148001ff18a4000ff4c520007f86290003ff2148001ff10a4000ff48520007f8429004fff5048009ff2824013ff54120027f8a09004bff4048009ff2024012ff50120027f88090003ff3048009ff1824000ff4c120027f86090003ff2048001fd9024004ff88120027dc4090013ff65080097fb284004ff99420015fcca100137e65080053f3284004ff59420085faca100137d65080013eb284004ff19420025f8ca10013ff64080097fb204004ff9902000dfcc810013be64080035f3204004ff5902007dfac810013bd64080015eb204004ff19020025f8c81003fff540801fbfaa0400fff9502007ffaa81003f7d540801ffe2a04004ffd8c20025fec610013fe630800f7f3184004f798c20005bcc610013fd63080017eb184004f758c20005bac610013fc63080097e3184010ffd4c20087fca610043fd5308021fe298400fffd0c2007ffc861003ffd430801ffe2184011bf98820087fea41003bfe5208021fea90400eff1482007ffe841003bfe420801ffea10400eff10820007fe641003bfe3208001fe990400eff0c820027fec210013fe61080077f3084004fd98420005ecc210013fd61080017eb084004fd58420005eac210013fc6108021ffa884010ff94420087faa21004
  | 3 => 0xd9826004ff8c130027bc6098013ff650c0097fb286004ff99430015fcca180137e650c0053f3286004ff594300c5faca180137d650c0013eb286004ff19430025f8ca18013ff640c0097fb206004ff9903000dfcc818013fd640c02f7eb206004ff19030025f8c81805fff540c02fbfaa06017ff950300bffaa81805f7d540c02ffe2a06007bf98c3003ffea61801ffe530c00ffea986007ff14c3003ffe861801ffe430c00ffea186007ff10c30027fec418013fe620c0017f3106004ff58830005fac418013fc620c031ffa906018ff948300c7faa418063fc520c02fffa106017ff908300bffa841805ffc420c00fff9906007ff8c83003ffa641801ffc320c009ffb086004ff9843001dfcc218013fd610c0017eb086004ff184300c7fea218063fe510c031fea886018ff144300bffe821805ffe410c02ffea086017ff1043003ffe621801ffe310c00ffe9886007ff0c430007fe4218003fe210c001fe9086000ff08430025fcc018013ff500c009ff2806004ff54030027f8a018013ff400c009ff2006004ff50030027f88018013ff300c009ef9806004ff8c030027f46018013fd300c009ee9806007fe4c030077fecb9005aff65c802dff32e4002bf997200b7facb9005afd65c801dfe32e4002bf19720077fec990046ff64c8023ff3264001bf9932008ffac990046fd64c801dfe3264001bf1932008ffea9900477f54c8023ff2a64011ff5532008efaa990047fc54c801dffb1e4000bfd8f20007fcc79001efe63c8001feb1e4000bf58f20077f8c79001efc63c802dffa9e4016ff94f200b7faa79005bfc53c8023ffa1e4011ff90f2008ffa8790047fc43c802dffa96400eff94b200b7faa59003bfc52c8023ffa16400eff90b2008fdc8590047fd42c8023f6a16400eff10b20007fe659003bfe32c8001fe996400eff0cb20077fec390003fe61c80077f30e4000ff58720005fac39003bfc61c802dffa8e4016ff947200b7faa39005bfc51c8023ffa0e4011ff9072008ffa8390047fc41c8001ff98e4000ff8c720007fa6390003fc31c801dff90e4000ff88720007fa439003bfc21c802dffa864004ff943200b7faa190013fc50c8023ffa064004ff9032008ffa8190013fc40c8001ff9864004ff8c320007fa6190013fc30c8009ffb2c4004bfd9620027fccb1000afe6588009feb2c4015bf59620027f8cb10012fc6588009ffb244004bfd9220027fcc910006fe6488009feb244014bf59220027f8c910012fc6488029ffaa44014dfd52200a7fca910053fd5488029beaa44014ff15220027fec710012ff6388009ff31c4007bf98e20027fac710002fd6388009fe31c4004bf18e200affea710057fe538802bfea9c4015ff14e200a7fe8710053fe4388029fea1c4014ff10e20095fac510057ff528802bff2944015ff54a
  | 4 => 0x7bfc52cc03bffa16601dff90b300effa8598077fc42cc00fff9966007f7ccb3003ffc659801ffd32cc001ee9966007ff0cb3003ffec39801ffe61cc0077f30e6007ff58730005fac39801ffc61cc03dffa8e601eff947300f7faa39807bfc51cc03bffa0e601dff907300effa8398077fc41cc00fff98e6007ff8c730007bc639801ffd31cc00ffe18e6007f70c730007fe4398003fe21cc001fe90e6000ff087300f7fea198013fe50cc03dfea866004ff143300effe8198013fe40cc03bfea066004ff10330027fecb18012ff658c009ff32c6002bf99630027facb18072fd658c009fe32c6004bf19630027fec918012ff648c009ff3246001bf99230027fac91806efd648c009fe3246004bf192300dffea91806f7f548c037ff2a4601bff552300defaa91806ffc548c0337eb1c601cffd4e3003ffca718073fd538c00ffe29c601bffd0e3003ffc871806ffd438c00ffe21c6004ffd8a30027fcc518002fe628c009feb146000bf58a30027f8c518073ff528c039ff294601cff54a300e7f8a51806fff428c037ff214601bff50a300dff8851801fff328c001ff1946000ff4ca3003ff86518013ff618c009ff30c6003bf98630027fac318002fd618c009fe30c601cffd46300e7fca318073fd518c039fe28c601bffd06300dffc831806ffd418c037fe20c6007ffcc630007fc6318003fd318c00ffe18c6000ffc8630007fc4318003fd218c001fe10c6004bf98230027fea118013fe508c009fea846004ff14230027fe8118013fe408c009fea046004ff10230027fe6118013df308c00ffd984601affd95300d5feca980037f654c0013fb2a601aff99530015fcca9806bfd654c0357eb2a601aff19530015f8ca9806b7c654c0053e32a6019ffd91300cdfec898003bf644c0015fb226019ff9913000dfcc898067fd644c0337eb226019ff1913000df8c898067bc644c0035e3226019ffd51300cefea898067fe544c033feaa26019df551300cff8a89806bff534c00fff29a601af794d300d7faa69806bdd534c00ffe29a6019ffd0d3003ffc8698067de434c033fea1a6019f750d3003ff88698003ff624c0017fb126000ff98930007fac498003fc624c0017e312601affd49300d7fca49806bfd524c035fe2926019ffd09300cffc8498067fd424c033fe2126007ffcc930007be6498003fe324c001fe9926000f74c93003ff86498003ff614c0017fb0a6000ff98530007fac298003fc614c0077e30a601affd45300d7fca29806bfd514c035fe28a6019ffd05300cffc8298067fd414c033fe20a6007ffcc530007fc6298003de314c001fe98a6007ff0c530007b86298003ff214c001ff10a6000ff48530007f8429806bff504c009ff282601aff54130027f8a098067ff404c009ff2026019ff50130027f8809801fff304c00ff
  | 5 => 0x9121115fec89088bfe64484037f3224222ff59121115fac89088bfc64484037e3224222ffd5121116fea89088bfe5448445feaa24222df55121117f8a890803ff63484017fb1a4200f7d8d21005bec690803fe634840f7f31a4200ff58d21005fac690803fc634840f7e31a4200f718d21005b8c69088fff5348447ff29a4223ff54d2111ff8a69088bff4348445ff21a4222ff50d21117f8869088fff5248447ff2924223ff5492111ff8a49088bff4248445ff2124222ff50921117f88490803ff3248401ff1924200fb8c921007fa6490803ed3248401fe1924223ffd452101ffca29088ffd5148407fe28a4222ffd052101ffc829088bfd4148407fe20a4200ffcc52101ffc6290803fd3148407fe18a4200ffc8521007ee429080ffe2148407f710a4200ffd8121005fec090803fe6048401feb024200ff18121025f8c09088fff5048447ff2824223ff5412111ff8a09088bff4048445ff2024222ff50121117f8809080fff65084077fb284203ff99421015fcca1080f7e65084053f3284203ff59421105faca1080f7d65084013eb284203ff1942101df8ca1080fff64084077fb204203ff9902100dfcc81080fbe64084035f3204203ff590210fdfac81080fbd64084015eb204203ff1902101df8c81087fff540843fbfaa0421fff950210fffaa81087f7d540843ffe2a04203ffd8c2101dfec61080ffe630840f7f3184203f798c21005bcc61080ffd63084017eb184203f758c21005bac61080ffc63084077e3184220ffd4c21107fca610883fd5308441fe298421fffd0c210fffc861087ffd430843ffe2184221bf98821107fea41083bfe5208441fea90420eff148210fffe841083bfe420843ffea10420eff10821007fe641083bfe3208401fe990420eff0c82101dfcc21080fff5108407ff2884203ff5442101ff8a21080fff4108407ff2084203ff5042101ff8821080fff3108407ff1884203ff4c42101ff8621080fff2108407f79084203ff8842101fec421080ffd2108407f69084200fd4842101ffec01080ffe60084097f3004203fe98021005f4c01080ffd60084017eb004203fe58021005f2c01080ffc6008441ffa804220ff94021107faa010883fc500843fffa00421fff900210fffa801087ffc400840fffb2e6007bfd973003ffccb9800afe65cc00ffeb2e601ebf5973003ff8cb9801efc65cc00fffb266007bfd933003ffcc998006fe64cc00ffeb26601dbf5933003ff8c99801efc64cc03bffaa6601ddfd53300effca998077fd54cc03bbeaa6601dff1533003ffea79801ffe53cc00fef29e6007ff54f300f7baa79801ffc53cc00fffa1e6007ff90f3003fbc879801ffd43cc03beea1e6007ff10f3003ffec59801ffe62cc0017f3166007ff58b30005fac59801ffc62cc03dffa96601eff94b300f7faa598
  | 6 => 0x176b106203ff18831147fea4188a3fe520c451fea906228ff1483113ffe841889ffe420c44ffea106227ff1083103ffe641881ffe320c401ef1906207ff4c83103ff8641881fdc320c4077f3086203ffd443101ffca21880ffd510c407fe2886203ffd043101ffc821880ffd410c407fe2086203ffcc43101fbe621880ffe310c407fb1886203ff4c43101fba621881ff5310c407ffb006203ff98031025fcc01880ffa600c4017d3006203ff58031005fac01880ff9600c4017cb006203ff18031147fea0188a3fe500c451fea806228ff1403113ffe801889ffe400c44ffea006227ff10031077fecb9089aff65c844dff32e4202bf99721137facb9089afd65c841dfe32e4202bf19721077fec990886ff64c8443ff3264201bf9932110ffac990886fd64c841dfe3264201bf1932110ffea9908877f54c8443ff2a64221ff5532110efaa990887fc54c841dffb1e4200bfd8f21007fcc79081efe63c8401feb1e4200bf58f21077f8c79081efc63c844dffa9e4226ff94f21137faa79089bfc53c8443ffa1e4221ff90f2110ffa8790887fc43c844dffa96420eff94b21137faa59083bfc52c8443ffa16420eff90b2110ffa859083bfc42c8401ff996420eff8cb21007dc6590803fd32c8401f6996420eff0cb21137fea39080ffe51c844dfea8e4203ff1472110ffe839080ffe41c8443fea0e4203ff10721007fe639080ffe31c8401fe98e4203ff0c721077fec190803fe60c84097f3064200ff58321005fac19083bfc60c844dffa864226ff94321137faa19089bfc50c8443ffa064221ff9032110ffa8190887fc40c8407ffb2c4203bfd962101ffccb1080afe6588407feb2c4225bf5962101ff8cb1080efc6588407ffb244203bfd922101ffcc910806fe6488407feb244224bf5922101ff8c91080efc6488449ffaa44224dfd5221127fca910893fd5488449beaa44224ff1522101ffec71080eff6388407ff31c4207bf98e2101ffac710802fd6388407fe31c4203bf18e2112ffea710897fe538844bfea9c4225ff14e21127fe8710893fe4388449fea1c4224ff10e21115fac510897ff528844bff2944225ff54a2112ff8a510893ff4288449ff2144224ff50a21127f88510803ff3288401ff1944200ff4ca21007f8651080efe6188407ffa8c4203ff9462101ffaa31080ffc5188407ffa0c4203ff9062101ffa831080ffc4188407ff98c4203ff8c62101ffa631080ffc3188407ff90c4203fbc8621007ee431080fff6088407ff3044204bf9822101ffac110802fd6088407fe3044225ffd422112ffca110897fd508844bfe2844224ffd0221127fc8110893fd4088449fe2044223ffd952111dfeca908037f65484013fb2a4223ff99521015fcca9088ffd65484477eb2a4223ff19521015f8ca9088f7c65484053e32a4222ffd
  | 7 => 0x9880ffe41cc45bfea0e6203ff1073103ffec19881ffe60cc4097f3066207ff58331005fac19881ffc60cc45dffa86622eff94331177faa1988bbfc50cc45bffa06622dff9033116ffa81988b7fc40cc407ffb2c6203bfd963101ffccb1880afe658c407feb2c622cbf5963101ff8cb1880efc658c407ffb246203bfd923101ffcc918806fe648c407feb24622bbf5923101ff8c91880efc648c457ffaa4622bdfd523115ffca9188affd548c457beaa4622bff1523114dfac7188b3ff538c40fff29c622cff54e3103ff8a7188afff438c40fff21c622bff50e3103ff8871880fff628c407ff3146200bf98a3101ffac518802fd628c407fe314622cffd4a31167fca5188b3fd528c459fe294622bffd0a3115ffc85188affd428c457fe2146207ffcca31007fc6518803de328c401fe9946207ff0ca31007b8651880efe618c407ffa8c6203ff9463101ffaa31880ffc518c407ffa0c6203ff9063101ffa831880ffc418c407ff98c6203f7cc63103fee631880fff608c407ff3046204bf9823101ffac118802fd608c407fe304622cffd4231167fca1188b3fd508c459fe284622bffd023115ffc81188affd408c457fe204622affd9531155feca988037f654c4013fb2a622aff99531015fcca988abfd654c4557eb2a622aff19531015f8ca988ab7c654c4053e32a6229ffd913114dfec8988a7fe644c4037f3226229ff5913114dfac8988a7fc644c4037e3226229ffd513114efea8988a7fe544c453feaa26229df5513114ff8a8988abff534c40fff29a622aff54d3103ff8a6988a7ff434c40fff21a6229ff50d3103ff88698803ff624c4017fb126200ff98931007fac498803fc624c4017e312622affd4931157fca4988abfd524c455fe2926229ffd093114ffc84988a7fd424c453fe2126207ffcc931007be6498803fe324c401fe9926200f74c93103ff864988abff514c407ff28a622aff5453101ff8a2988a7ff414c407ff20a6229ff5053101ff8829881fff314c40ffb98a6203ff8c53101fbc6298803ff604c4017fb026200ff98131007fac098803fc604c4097e302622affd4131157fca0988abfd504c455fe2826229ffd013114ffc80988a7fd404c453fe2026203ffd943101dfeca1880ffe650c4057f3286203df99431014fcca1880ffd650c4517eb286203df59431004faca1880ffc650c4077e3286203ffd903101dfec81880ffe640c4037f3206203ef9903100d7cc81880ffd640c44f7eb206203ef590310057ac81880ffc640c4077e3206227ffd503113efea81889ffe540c44ffeaa06227df5503113ff8a81881efe630c40fffa986207ff94c3103ffaa61881ffc530c40fffa186207ff90c3103ffa861881ffc430c407ffb106203ff98831005fcc41880fee620c401773106203ff58831005fac41880fed620c40
  | 8 => 0xfd46321a7fca3190d3fd518c869fe28c6431ffd063218ffc83190c7fd418c863fe20c640effd8232007fcc119012fe608c801feb046400bf58232077f8c1190d3ff508c869ff2846434ff542321a7f8a1190c7ff408c863ff2046431ff5023218ff881190cfff654c8677fb2a6433ff99532015fcca990cffd654c8677eb2a6433ff19532015f8ca990cbff644c8657fb226432ff9913200dfcc8990cbfd644c8657eb226432ff1913200df8c8990cbff544c865bfaa26432ff95132197faa8990cb7d544c865fe2a26433ffd4d3203ffca6990cffd534c80ffe29a6432ffd0d3203ffc86990cbfd434c80ffe21a6433ffd493219ffca4990cffd524c867fe2926432ffd0932197fc84990cbfd424c865fe2126407ffcc93203fde6499003fe324c801ef1926400ffd8532005fec299003fe614c801feb0a6400ff1853201df8c2990cfff514c867ff28a6433ff5453219ff8a2990cbff414c865ff20a6432ff50532197f88299003ff604c8017fb026400ff98132007fac099003fc604c8097e3026433ffd413219ffca0990cffd504c867fe2826432ffd0132197fc80990cbfd404c865fe202640effd943203dfeca1901ffe650c8057f3286407ff59432185faca1903bfc650c80f7e328640effd903203dfec81901ffe640c8037f3206407ff5903217dfac81903bfc640c80f7e320642fffd503217efea8190bffe540c85ffeaa0642fdf5503217ff8a81901efe630c80fffa986407ff94c3203ffaa61901ffc530c80fffa186407ff90c3203ffa861901ffc430c8637f3106430ffd4832077fca4190c3fd520c81dfe290642fffd0832077fc84190bffd420c81dfe2106407ffcc83203fbe641903bfe320c80ff71906407ff4c832007ba641901fed320c81dffb086407ff9843201dfcc21901ffd610c8017eb08640eff18432187fea2190c3fe510c861fea886430ff1443217ffe82190bffe410c85ffea08642fff10432077fec01901ffe600c8097f3006407ff58032005fac01903bfc600c861ffa806430ff94032187faa0190c3fc500c85fffa00642fff9003217ffa80190bffc400c80fffb2e6207bfd973103ffccb9880afe65cc40ffeb2e622ebf5973103ff8cb9881efc65cc40fffb266207bfd933103ffcc998806fe64cc40ffeb26622dbf5933103ff8c99881efc64cc45bffaa6622ddfd533116ffca9988b7fd54cc45bbeaa6622dff1533103ffea79881ffe53cc40ffea9e6207ff14f3103ffe879881ffe43cc40ffea1e6207ff10f3103ffec59881ffe62cc4017f3166207ff58b31005fac59881ffc62cc45dffa96622eff94b31177faa5988bbfc52cc45bffa16622dff90b3116ffa85988b7fc42cc40fff9966207f7ccb3103ffc659881ffd32cc401ee9966207ff0cb31177fea39880ffe51cc45dfea8e6203ff1473116ffe83
  | 9 => 0x200000c00400300000000100400200000300300000300100200000100000600300000400300100200000c00000100000000300000200100200000600700000200100200400200100000100800000000200100100400300c00000000100200300000000000200000000000300a00000100200000100200000000900000300000100000000100000300000301400000000000100100100500400700000600200000100400700100100000000000000200400200000000000200100200000000100000400400000700000200800700300900300100300100000500100100400000300000000400500000800000300100000200200100300400500100200000300000000100400200000300100100300000900000500d00100000000000000400000400000200000000100700200100000500000000000000000000000000400100000200200400200200700000300100000100300200100300000600000400100200100000100000000100000100100000300300000100000100200000000200400300000000000500d00000200000100000100100000300a00200000000200000000200500600000200600e00000100000000d03ffecb9901eff65cc80fff32e6402bf9973203efccb9900a7e65cc80ffeb2e6436bf5973203efacb990027d65cc80ffe32e6407bf1973203ffec99901eff64cc80fff3266401bf9933203ffac9990d6fd64cc80ffe3266407bf193321affea9990d77f54cc86bff2a66435ff553321aefaa9990d7fc54cc80fffa9e6407ff94f3203ffaa79901ffc53cc80fffa1e6407ff90f3203ffa879901ffc43cc86dffa966436ff94b321b7faa5990dbfc52cc86bffa166435ff90b321affa85990d7fc42cc80fffb0e6407ff9873201dfcc39901ffd61cc8017eb0e6407ff187321b7fea3990dbfe51cc86dfea8e6436ff147321affe83990d7fe41cc86bfea0e6435ff1073203ffec19901ffe60cc8097f3066407ff58332005fac19901ffc60cc86dffa866436ff943321b7faa1990dbfc50cc86bffa066435ff903321affa81990d7fc40cc81dffb2c6434bfd96321a7fccb1900afe658c869bf32c64029f996321a7facb190d2fd658c801beb2c64009f59632077f8cb1900afc658c81dffb246431bfd923218ffcc919006fe648c863df3246401af9923218ffac9190c6fd648c801deb246400af59232077f8c919006fc648c863ffaa46431dfd523218ffca9190c7fd548c863beaa46431ff15232195fac7190d3ff538c80fff29c6434ff54e3203ff8a7190c7ff438c80fff21c6431ff50e3203ff8871901efe628c869ffa94640eff94a321a7faa51903bfc528c863ffa14640eff90a3218ffa851903bfc428c80fff9946400f7cca3203fde651903bff618c801ff30c6403bf98632007fac319002fd618c81dfe30c6434f
  | 10 => 0x80008d800001f98b80006f62568fd49de31216d06b48860d91eca0100007eb324000000000000021080000000000000f866050cf00007ee1243ba021879e0f2055928c00021639c80000000000999ff8fe47e8000000000c00000000005005fd00011840000000000000bb881521b9cb436029600000000000001a306d00005b21b184f80c634b272000000000000000004565511d080000007de34e8648a026aa2b107ac6206b00001104efc4c11ea896408825e00000004441bc38707fc5b04c60db916083a26929e08000005b31a380002620000000554f9042b3770000d08306374947474405619381f002e7a9080000000073d1eb18e005a000000021400000038d0000346000000190800000005483300007b6000000000000038181b90704680c300000002f51f4114104478e07400000000000000ff846600034300001f200026a000000000038d802400000022f0000c482672b380000007e400000000000003b68000fa800016e8000f5e00010780000342720d7978800000015597110460003ee0d6803c5c726d801400000000500000200000000200400100100000200300200600200200000100300000700200000100000000300800000200200100000200700000500300700000000000000000000100100000100400c00000100400100300000400301200100000000200100000300300000000000100000700200300300300000200000000300100300300100300100000100100000000000100200100000000100000600700100200200500000200100100300600300000000100000300300400100900300000200100000100000200000000300100400000a00000a00300f00000500200400400000900000000000000400000100000200000100000600900c00200000000300200400600500400000000000200100400100000200f00700600500100200000300000000200200400000000100000800000201100000000300200000000700300100200700000000100000000100100000000400000000000100000100400100100000000300000400100a00300000000000200000000000000400200000200000200800000d00400000000400000000100500400600000000300400000200000500200000000600100000200300100000100200000200000200500000100100100000400000200400000000100600300000300000000000100000000600100000200300000000900200000200100100200500200000000001200000000000000000600100000000200000000800000000000300100000000700300000200000100400000000a00100000100200000200300000000c001002000000000001001000002000006007002001001001000001002005000006003000000001000000003014005000005000000000000000000
  | 11 => 0xf380007880000000000a3e0000000e6062600000013a0f8e000000029c3d00001eb9014f84409031000000026b2fc835c0000000000418000000000000000000000000003200000000000cfe42419180c4b244eb3b387a80000001680000b9800029d0fe45a837b3a998501e806d0fe91fc10070d000000000012f15b800000000000000000de00036b80010480000ff18d40006820000c109480ae218943c00000016e00000643110000438ba26642698b5c0000000000000000000000000000000005b0000000000000000000077a282800000000000000000005f70b40000000000000000000000024600000003c71621b88c4a162068988c4ca7ce135060c0000004030b04c88752000000000000005100000000000000000c52000000000012477f000000044600000000008c600026c82943f2612000000064035f0ed0000b1e00030c80000000002ad000000037800000003f400040c092067c70902716a059e00000000002806b50d71708aec0000000e5c0000003292000000000000000000000000000000cc5fc3f8926908c0000000000b0e0002558f2400000000000000005040001a2c0000000000000eb40000b5800031600000000000002290000000bbe7752ea000061c80e00000000001153be94e000043a0ec888400000000002a800000000000005328030000000f4265e000119849e70819d800056800030f9f046ea3e035c0000fe86063a200009600000ba8c7400056500000000001e10001d40d6641130b824c3420ad3f098f4f7e1b141f1e6000000020380000001e200008f8344479021065065e000000000000059f000000000013d0000d144e85b1000202c00038800013440004df0ac00000303a01131fd800006b2f818c40007820f600000000fe0000000000541000000000000000002b0000691000000090000016b1378e1e1c729901fc8020a10668f1400012907e1dc01060000000be0000756109000000000000000008980003aa989ca940000000448000000020896c3960b525f182c8be00000000008f40000000000ae208d0eb800094079d0439f4044e6f51258000f1e7960001eb904267823708d4e0c7450000000b0600025d94340003dc0000000016028000037000000019d000047852e000190c0366e300010880e25e300010f84e2134032000000000c22310840002a6000000024e0001908000b200000a68630f8028f2bf95c8000659000057c31245b29f0de44386e43e28d840006cb0000000c1868e00001409ce4d80000000e740002ad8770d506880000000000000333000000000025617b8bf007d00001540000000000cd400072e0001694e1600033e17940000002ed800000038e2911d646140002ba1e5046807e0000000e6c00011d073000002c39884a800043c0000000000000180
  | 12 => 0xe800047a27000016a49066ae3ed000034c4ea1f6000000014212e03b0264000000004c7e26672e7800000071c0e41b6ca7600029e88a000036c00018cc0000000001a34606159000000000400013e9bc061848e000000091613502a0000e900000000000000000232000079c71d000000024600003a80000000002a71d8000000021813f0be40000000000c9e41c00000000004b10000ff00001793f00eb01ee00033884c048479c059000000000030680003e60003d89e2cc420003248dc00000001ec03608f85fb0460c9094c1f42fb0d3c000593000000000000000000004f0000000000056237c3c680000000000000000000000000200446200030f0000000000284118800000000006204ec11700000007ca57d3d280000200e50000000d921b50000000a563720000acc5ee75f0e7950cf78000014938c0000003ef80000002901670000b360003499be441000000000006a068918f16d80004330000000e48837000000018a3141d595706ec585000000000000010c800000200032d9aa500e4f5405000012e21d000000068066a2d60000fea000000000000000000013302ce0001268e6800079f00011ac82e000000000045811f3c08a38e6a3f22f880000002253be000000000017b00004400000000f7861e09800009681bc00015e80006727e700005040000e0000123c000000000194cfee00000000000003f820f03cc8e8000000113400e8260000ce041a0000000b4419c2c21038aa8a504dd2300000f5400023d800000001f00000000002c30d380007a800000000c00000003e880009d200005880000001e300012f40000002d59b70fba46f17e000098800000000003c80002998000a0616c0f88c1427658b3a4976808e18f20d800000000010c09a000000000000003761f2082800000000005a00002ee0003d8191400000000019440000000000568dda0000000000000000000000000000000000000001ef2fa99dce9446728c00004c43f62948b9c00000008c80000002a530e09d40002f40001ddc0000000f80000000000123000000000000000000004ee17080000006cc3f1135c0000612a119b8f9e44e0000e9870664b25700000006921248000000000000000000000000000000005e7000066000071800004dc00000000880000001d03fd1408fa40003c2800000000000019580000000000000000000222138853826f000000000000037d0000c5e00038c800000000000000001500000000000eb00000001aec000640241000000043217c8094ad076840d80003a229100010e00003dd02400000f6000000037400000000000000000000001becb1877b00000000007ff3f9887cf360002ae8594ce646a0001aac6902e832f8c584824402da00000000000000c2c00043b0000000cf43a320c9520fcc0003361ff000
  | 13 => 0x7a6a21ac030890a59d00000000000000e011f45720000c70e145c80000001d88000157323875434800000000002ec00000000002220000000000e0874d00000004be82e21c800000079141004b849400022892e819223700019d8e821ca186800000062041384fc6dc0001a480e400000000016d450649e10180000001213799a640003a40001e1cfaa0ed1f680000002b000000000000af1020000000792000155000000000a000047017c0af1b54f7a6a01cb12182a265c0000f00c6c00036415f008a0003368f4c64c0000ea165453e761000000000016d09680000000683738df800000000000001321a036b0000000000000000000000025493f400000000017f80000000000000ad60000000b54000000000132cd7c14b3698ad904a2ed0000a20c4c000000000000026319980f401c47e2cc11d45123eb2d180003ee0000758ed0a6e0cf30d98a806e24c3528e30ab24162151e7857e2730fc04780ee0000b200000000000158000a8a00000019c8000809000125cc7231500000000000000000794000540276858c0000003da80000740000001a40000000156079852a343206030458011427d8e94212000000000000000021f8000000000000067ccba5af000000000029d2938da0af00001cf00009860002b09d2c0006c40001abc7e03d218f850cf8c61a40983c008c0002c70000be600039f8028ad251a000000000072f13f0000d7837700016181aa5122650b20a6240600000000000003b500007b658100000000000db00000004cc3080001210000000196090cf340000001670a9e00000001d048000039300002a664c000000070850038b000000000035b800000041217e929400008f22904687fa03840f80005b63be07c085ccea29a0000000000000328040ccaa78631109542504e620500003046ff0839c5c0003c300014b43340000002008fac1d22b31b94c6400000012205f400035a000000000000000008a60003fd938447e6fc3b48000e0035e29189dca1215d1f3172c00079907300000000003019bc4ff00003bb0ef00000002ca1b98fae1f50000c94a2034a31400000006182a21e8c5c400000004f00006941be80000000000fb00001e21a90000000000000000000000005321016a867e2ee36f04980ce723105948480421a0b503f49ec3993af0a10c760000c500004180000000528bd20002e802100000000000000000570000000000058904b19a00000000001ff4aaa00000011a4f765473d39a850667a00000bbca60000000000049c0000000000d2a5823c18f7c00000000000000000df000202000000030e9f9406650e0001c500001740000000000000000203418c0000000a5000083d00000000000000000000afc60f1fa000075467e3c60c5c69c6ca00000000005e611806040000003021c54f2e5603a
  | 14 => 0xdc80000002e331f80000f20002080b144f610d179176440c5dd000000040227f3b8800028c0350001934dd62130000000aa07a400006f855c5ff3b6048840409027980d0c5a00003480006602e62d00a0828e0001fd8a1c1ec00032a000038a5161ab00007126342de0000000318000000000022a0000f44af43671da8000d8c00000004ac38c0002ac00000001cd22c9918e766a42a98c64000000000053c78469f3d400581a026e000000000000037b8000000000000000000078400000000001a5283800024a00000000000000003ae000000060e1f180001c684108b0160db40000000f9c0000000001a981ce0ca24f800000076b0001ca000043439500010203bd26b13c00007cc20a06c800076e00020b004611c13d08400006612670fbc0003940000130e800ef2fa0fa8c6e00000018040000ea1168000000607000000000000000013c80000000000000f920361cd80009ee0000a280000000003b3000051a2de0cb800075c14e00019881ac71e00000004a67ec00000000005250b90404000000000000000000000000000004ff017000000000000000009f41c30f712740000c800000006680000c28774e3e5a400000000003a8000000038851e264800000083c38886ac71a00f22a0ac83bc0000001ec8d9e0002c21f8c0f03e200000001c42df0000000e2429b370112400073e00000000000003159158392000000000000000025a1f6000019c0001a1ceca70100e19949e20000001bc843c00000019d091417b3c480002f04870001e40a2e67b2ef1c4c0007a618488d80000000001a0000042c0001c080004a20501068d2e0000000000000332140930014607205f0410b4481400000000000000000a880007f9000000075238b15e1edc00035d0001204b945d700017e8aa420900000000003bb4078bc0d3c09100015b869a00000004600005d30000000d820522f580000006d900000000001c10000d4c5f681a00017380004c539385500005b900a92a80001c200016283360001d821146cc0000000dac0000000000e18000000000000096428b1c920d4160000000000079a442165000000002a0000cdc0006703d5969c0000084090000000000000000000051c1f49dbc72031b03603a400042900005990640003bc103c4a221124c14d82180000639d386440d300016440004483041a68d0600041b00000005e82e08de80000003da1b440000001b780000000000000dcc000000414854854800000000000000000000000e846301ac9e0084e5c61a213e4d182242d806a83000000000d440003b7304945495e4721548e7ccde68500000000005b715d9b7c8ec83b0000a1491a81700000000004180000eb4000000000000000053912b80006d40001b8800000016f000155800000000006fc000000000027c58e404196a0141
  | 15 => 0x400000044072600000000001f64bc3bc800000035c0a2000011c5c93d9a0a8af250b0001bd00000200001eb0c2c3ba36290d40e0000000010c00059600000000000000000000240000000000000030015400000ec0b90000000e587321a091145740000000000eb660205f80004a44b826a94305d417006216b478c6630dd00007384cd000000080635202d9f34b7024700000000000b341f8000cb06133b90ebcdd808804a84b058c214000000000000015c0000000000254104c0008190000000000751052046c8da831212a0300006a700000002708440001a6000014915080000000000000000bc809d21720d0fda64109c8b480000003f500000000000001480fd20002b68000e6e25813c9b5010400036000000000000ca9cac0003623dc9490bac79522500000ba1b81070d5c47617f24a06740005bd4140000000000392843c93200000000005d23b627607b4dd40002e900000005770001e281380000001464da42601179844d7400000007ece20342000131c13415b1500000b5c74702c80009420003ab8c1c6ca0241c8922493839d00007f09841d800000000000003a785b881c00000015b0c7410b3c420e80b80000001afc598000383800056a00001d8000d380000000f8400026c25f80004f804903d000037a4570708000c7c000136800105a00000000005ca000170000000000015f0828cae32a1e81534dde00035c8cb80000002e000000000002cf0000a283810d400000000c3000000070e2af0000000000000000017cdba81e1a6000066218d0110d906b60002e402f092408a206842866c00002f16987721733d695ec4c81e902896842046790000e3cec86c70e70000e980000000e2800049322e80000004dc0000000e185800000a483ac000000210cdf000000000007c83690000c7053c15c0000000c940d200003900000400001f280b47051ba18280006c32af144c1a80000001ad800042d0001ab0ad47290001530128000000000036600035e80000000000000000000000000000000052f000009c26c83020a99388e681633004740947b817f1a048ee09b03980f065281127a0000e70000000000c0007632488db41fe148000053070001200000000000002f000000000001539714000000399874ca96000000000103a45c0408a8cd140001fd0e540003bf07a80000c040b0bf0000a4c5bf2b99bf49a0000084055832604d089800048815001795bc000000000124000063c3610a4d0720002259f6cbd449b1658e9c00000001f0000c2a0000d600000000002cd12dc0000000000000f26000000157c2743b23a31fb8a0c0cb11c9b8400000000012e4aea00002b89588466ad0000000798511000165c0004700001c88b1001d39e02ec0000b8000111cbda54612e80000001871028000000000000012c0006100
  | 16 => 0x58086c66b1dc13e0a7e0000000b244c219939012d8b7c28c28520700006000001a3cb9a000000013c4360000000000a584da122809800065a00018b0f960211431a6c0000000000000d9c0000000000dfc00000005847e65993980c0800072100019f40002ec00000000000002ab9d507964551190cf40000000000000d467f0000003400800017980000000000000194000000000000083e000000000000000028d80000000001ed20bcfb2000204000000000006d0000f444b505d14d4000254000094079069600000005a6000217822c00000000000001805d81aa9dccb76000267800000000010a800000000000000000320000000ecc0002974200d80bd83ee00000006507ba000000032c6cd077000092c17d00000005fe22e272958c3220000000dfcdb0000000000036c4713df1194d625c317580003be2f121e80000001db0001fbc0007431e08a603086e800000000000000000000000000000000013c70a264000000000000014d09a44782701f109fc5640f000000003542dd000011200003510980003ca35917540000001d88b35056000000000000000000002dc000000145000000000000000000000000001784b1a5ef39a113c2d233c000129c7fe4b300000002f40fa29500000000000000cac0006d00000000000000000000092a0000000c688b40a61c100000007d30000000a9200021405c4000000000000000084716c8ab40000003348000
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc76481100057f754811004d7c7548110005bf7448110045bc7448110006ef6248110006ec6248110005f7714811001df47148110027f0104811001df87648110006f8764811001cf876481100077b75481101c7787548110007bb74481101bfb874481101bf7b54481101bf795448110005fb7348110005f97348110025fb7248110027eb7248110007eb6248110076fa6248110076f86248110007e862481101bfea42481101bfe94248110007f3714811001dfa714811001df87148110007f07148110026fb6148110027f361481101bff241481101bff14148110007f22148110007f12148110004ff7558c100067f7558c100047f7558c10014fe7558c10004fd7558c10014fc7558c100067c7558c100147c7558c10004ff7458c1000cfe7458c10004fd7458c1000cfc7458c100067f5458c100067d5458c10024ff7358c10026df7358c10006de5358c10006dd5358c10006de4358c10006dd4358c10004ff7258c10074fc7258c1001cff7158c1001cfe7158c1001cfd7158c1001cfc7158c1001ede3158c1001edc3158c10024ff7058c10024fe7058c10024fd7058c10024fc7058c10026de3058c10026dc3058c10026fa1058c1001ef91058c10074ff7598810014fe7598810004fd7598810074fc7598810074ff749881000cfe7498810004fd7498810074fc74988100067f54988100067d549881003cfe7398810004fd7398810024fe7298810026ee7298810076ee5298810006ed5298810076ee4298810006ed429881001cfe719881001cfc719881001eee219881001eec2198810024fe7098810024fc7098810026ee2098810026ec2098810004ff75588100067f75588100047f7558810014fe7558810004fd7558810014fc75588100067c75588100147c7558810004ff745881000cfe7458810004fd745881000cfc74588100067f54588100067d5458810004ff735881003cfc7358810024ff7258810026ef7258810006ee5258810006ed5258810006ee4258810006ed425881001cff715881001cfe715881001cfd715881001cfc715881001eee215881001eec2158810024ff7058810024fe7058810024fd7058810024fc7058810026ee2058810026ec2058810026f71058810026fa1058810026f5105881001ef9105881003cff76cc810024fe76cc810004fd76cc810024fc76cc8100357e75cc8100057d75cc81003ede63cc810006dd63cc810074ff768c810024fe768c810004fd768c810024fc768c8100357e758c8100057d758c81002dbe748c810005bd748c810076ee628c810006ed628c810004ff764c810024fe764c810004fd764c810024fc764c81003ede634c810006dd634c810006ee624c810006ed624c810005f7714c81001df4714c810074ff760c810024fe760c810004fd760c810024fc760c810
  | 1 => 0xc910074fc760c910006df630c91003edc630c910006ef620c910076ec620c91001df6710c910005f5710c910025fa700c910005f9700c910024fe76cc510024fc76cc510006df63cc51003edc63cc510025fa70cc510005f970cc510024fc764c5100057f754c51004d7c754c510006df634c51003edc634c510005fb704c510025f8704c510024fe76c8510006ef62c8510076ec62c8510025fa70c8510005f970c8510005f6768851001ef6768851001df77488510225f5748851021f77548851021f75548851020df57288510076f66288510076f4628851001ff37088510025f67088510025f4708851001ff0708851001ef7608851001ff36088510024fc76485100057f754851004d7c7548510005df7348510005dc7348510006ef6248510006ec6248510005fb7048510025f8704851001ff01048510025f47648510006f47648510024f4764851000777754851021774754851020df7744851020df57448510207775448510207755448510007d77348510007d4734851001df7724851001fe77248510007e76248510076f66248510076f46248510007e46248510007e63248510007e53248510007f37048510025f67048510025f47048510007f0704851001ef7604851001ff3604851001cfe76cc11001cfc76cc110006df63cc11003edc63cc11001df671cc110005f571cc110005fa768c110026fa768c1101f77b548c1101f779548c1101fdf9738c11003efa638c11003ef8638c110005f9728c11001dfa718c110025f8718c110026fb618c110027f3618c1101f7f2418c1101f7f1418c110007f2218c110007f1218c11003cff764c110004fd764c11001cfc764c1100057f754c11004d7c754c110005bf744c110045bc744c110006df634c11003edc634c110005f7714c11001df4714c11001df8764c11003ef8764c11001cf8764c1100077b754c1101ef78754c110007bb744c1101e7b8744c1101e77b544c1101e779544c110025fb734c110027db734c110007db634c11003efa634c11003ef8634c110007d8634c1101efda534c1101efd9534c1101e7da434c1101e7d9434c110005fb724c110007db324c110007d9324c110007f3714c11001dfa714c11001df8714c110007f0714c110026fb614c110027f3614c1101e7f2414c1101e7f1414c1101dfda314c1101dfd8314c110007f2214c110007f1214c11001cfe76c8110006ef62c8110076ec62c811001df671c8110005f571c8110005fa7688110026fa76881101cf7b54881101cf795488110025fb7388110005f973881101d5f97288110076fa6288110076f86288110027f3718811001dfa7188110025f87188110027f07188110026fb6188110027f361881101cff241881101cff14188110007f22188110007f12188110074ff7648110004fd764811001cf
  | 2 => 0x4fd7558d10014fc7558d100067c7558d100147c7558d10004ff7458d10006bf7458d10004bf7458d1000cfe7458d10004fd7458d1000cfc7458d10006bc7458d1000cbc7458d100067f5458d100067d5458d10006df7358d10004ff7258d10006ef7258d10004ef7258d10074fc7258d10006ec7258d10004ec7258d10004ff7158d10006f77158d101dede3158d101dedc3158d10004ff7058d10006fb7058d10004fe7618d1004d7e7518d100057d7518d1003ede6318d10006dd6318d10004ff75d8910014fe75d8910004fd75d8910014fc75d8910004ff74d891000cfe74d8910004fd74d891000cfc74d89100067f54d89100067d54d891003cfe73d8910004fd73d8910006ef6298910074ff7598910014fe7598910004fd7598910074fc7598910074ff749891000cfe7498910004fd7498910074fc74989100067f54989100067d549891003cfe7398910004fd7398910074fe7298910004fd7198910076f57198910004fd7098910076f970989100057f755891004d7c7558910005bf7458910045bc7458910005df7358910005dc7358910004ff75589100067f75589100047f7558910014fe7558910004fd7558910014fc75589100067c75589100147c7558910004ff7458910006bf7458910004bf745891000cfe7458910004fd745891000cfc7458910006bc745891000cbc74589100067f54589100067d5458910004ff7358910006df7358910004df735891003cfc7358910006dc735891003cdc7358910006ef7258910004ff7158910006f77158910004ff7058910006fb7058910004fe761891004d7e75189100057d7518910045be7418910005bd7418910005de7318910005dd7318910006ed6218910074ff7518910014fe75189100767e75189100147e7518910004fd75189100767d75189100047d7518910074fc7518910074ff741891000cfe7418910076be741891000cbe7418910004fd7418910076bd7418910004bd7418910074fc74189100067f54189100067d541891003cfe7318910076de731891003cde7318910004fd7318910076dd7318910004dd7318910076ee721891001cfe7118910076f5711891001cfc7118910024fe7018910076f97018910024fc701891003cff76cc910004fe76cc910004fd76cc91003cfc76cc91004d7e75cc9100057d75cc91003ede63cc910006dd63cc910006ef62cc910006ec62cc910025fa70cc910005f970cc910074ff768c910004fe768c910004fd768c910074fc768c91004d7e758c9100057d758c910045be748c910005bd748c910006df638c91003edc638c91001df6718c910005f5718c910025fa708c910005f9708c910004ff764c910004fe764c910004fd764c910004fc764c91003ede634c910006dd634c910074ff760c910004fe760c910004fd760
  | 3 => 0xc7458a100067f5458a100067d5458a10004ff7358a1003cfc7358a10026ef7258a10006ee4258a10006ed4258a10024fc7058a10026ee2058a10026ec2058a10026f71058a10026f51058a1003cff76cca10024fe76cca10004fd76cca10024fc76cca1005d7e75cca100057d75cca101b67e65cca100067d65cca1003ede63cca10006dd63cca10025fa70cca10005f970cca10074ff768ca10024fe768ca10004fd768ca10024fc768ca1005d7e758ca100057d758ca101a67e658ca100067d658ca10055be748ca10005bd748ca1003ede638ca10006dd638ca10025fa708ca10005f9708ca10004ff764ca10024fe764ca10004fd764ca10024fc764ca1019e7e654ca100067d654ca1003ede634ca10006dd634ca10005f7714ca1001df4714ca10025fa704ca10074ff760ca10024fe760ca10004fd760ca10024fc760ca101867e650ca100067d650ca1003ede630ca10006dd630ca10025fa700ca10005f9700ca101767e65cc6100067d65cc61003ede63cc610006dd63cc610025fa70cc610005f970cc61003cff764c6100057f754c61005d7c754c6101567e654c6100067d654c61003ede634c610006dd634c610005fb704c610025f8704c6101367e65c86100067d65c8610006de63c8610006dd63c8610076ee62c8610006ed62c8610025fa70c8610005f970c86100057f754861005d7c754861011e7e65486100067d6548610005df7348610005dc7348610006de6348610006dd6348610006ee6248610006ed6248610005fb7048610025f87048610025fb764c210006fb764c2100077b754c21024778754c2100277a654c21002779654c210007bb744c21023fb8744c21023f7b544c21023f79544c210027db734c21003efa634c210027da634c21003eda634c210027d9634c210026f8634c210247da534c210247d9534c21023fda434c21023fd9434c210005fb724c210007db324c210007d9324c21001dfa714c21001df8714c2101dfda314c2101dfd8314c210025fb7648210006fb76482100077b75482102377875482100277a6548210027796548210007bb744821022fb8744821022f7b544821022f795448210005fb7348210005f97348210027da6348210027d96348210027eb7248210076fa6248210026f8624821022fea424821022fe9424821001dfa714821001df8714821003cfe76d8d10004ff75d8d10014fe75d8d10004fd75d8d10014fc75d8d10004ff74d8d1000cfe74d8d10004fd74d8d1000cfc74d8d100067f54d8d100067d54d8d10074fe72d8d10004fd72d8d1001cfe71d8d1001cfc71d8d10024fe70d8d10024fc70d8d10006df6398d100057f7558d1004d7c7558d10005bf7458d10045bc7458d10005ef7258d10005ec7258d10004ff7558d100067f7558d100047f7558d10014fe7558d10
  | 4 => 0x8e1003edc7598e1003edf7498e1003ede7498e1003edd7498e1003edc7498e10006df5498e100065f5498e10006de5498e10006dd5498e100065d5498e10006dc5498e1003edf7298e1003ede7298e1003edd7298e1003edc7298e10006df5298e10006de5298e10006dd5298e10006dc5298e10006df4298e10006de4298e10006dd4298e10006dc4298e1003edf7198e1003ede7198e1003edd7198e1003edc7198e10006df5198e1024ede5198e10006dd5198e1024edc5198e10006df4198e1024ede4198e10006dd4198e1024edc4198e1024ede2198e1024edc2198e10026df7098e10026de7098e10026da7098e10026dd7098e10026dc7098e10026df5098e10026de5098e10026dd5098e10026dc5098e10026df4098e10026de4098e10026dd4098e10026dc4098e10026df2098e10026de2098e10026dd2098e10026dc2098e10026df1098e10026de1098e10026dd1098e10026dc1098e10004ff7558e10014fe7558e10004fd7558e10014fc7558e10004ff7458e1000cfe7458e10004fd7458e1000cfc7458e100067f5458e100067d5458e10026df7358e10006df5358e10006de5358e10006dd5358e10006dc5358e10006df4358e10006de4358e10006dd4358e10006dc4358e10004ff7258e10074fc7258e10024fc7058e10026de3058e10026dc3058e10006df7558e10006de7558e10006dd7558e10006dc7558e10006df7458e10006de7458e10006dd7458e10006dc7458e10006df5458e100065f5458e10006de5458e10006dd5458e100065d5458e10006dc5458e10006df7258e10006de7258e10006dd7258e10006dc7258e10006df5258e10006de5258e10006dd5258e10006dc5258e10006df4258e10006de4258e10006dd4258e10006dc4258e10006df7158e101dede7158e10006dd7158e101dedc7158e10006df5158e101dede5158e10006dd5158e101dedc5158e10006df4158e101dede4158e10006dd4158e101dedc4158e101dede2158e101dedc2158e10026df7058e10026de7058e10026dd7058e10026dc7058e10026df5058e10026de5058e10026dd5058e10026dc5058e10026df4058e10026de4058e10026dd4058e10026dc4058e10026df2058e10026de2058e10026dd2058e10026dc2058e10026df1058e10026de1058e10026dd1058e10026dc1058e10074ff7598a10014fe7598a10004fd7598a10074fc7598a10074ff7498a1000cfe7498a10004fd7498a10074fc7498a100067f5498a100067d5498a1003cfe7398a10004fd7398a10026ee7298a10076ee4298a10006ed4298a10024fe7098a10026fa7098a10024fa7098a10026ee2098a10026fa2098a10026ec2098a10004ff7558a10014fe7558a10004fd7558a10014fc7558a10004ff7458a1000cfe7458a10004fd7458a1000cf
  | 5 => 0x1efa1058b1001ef91058b1003cff76ccb1001cfe76ccb10004fd76ccb1001cfc76ccb1006d7e75ccb100057d75ccb101b67e65ccb100067d65ccb101aebe64ccb10006bd64ccb1003ede63ccb10006dd63ccb10074ff768cb1001cfe768cb10004fd768cb1001cfc768cb1006d7e758cb100057d758cb101a67e658cb100067d658cb10065be748cb10005bd748cb1018ebe648cb10006bd648cb10076ee628cb10006ed628cb1001df6718cb10005f5718cb10004ff764cb1001cfe764cb10004fd764cb1001cfc764cb1019e7e654cb100067d654cb10196be644cb10006bd644cb1003ede634cb10006dd634cb10006ee624cb10006ed624cb10074ff760cb1001cfe760cb10004fd760cb1001cfc760cb101867e650cb100067d650cb1017ebe640cb10006bd640cb1001df6710cb10005f5710cb1001df77648710006f7764871000777754871026f74754871001f76654871001f756548710265f77448710265f5744871001fb6644871001fb5644871025f77544871025f755448710007d77348710007d4734871001fe77248710076f6624871001ef46248710007e63248710007e53248710025f67048710025f470487100f67e65cc3100067d65cc3100eebe64cc310006bd64cc31003ede63cc310006dd63cc31001df671cc310005f571cc31003cff764c3100057f754c31006d7c754c3100d67e654c3100067d654c310005bf744c310065bc744c3100cebe644c310006bd644c31003ede634c310006dd634c310005f7714c31001df4714c3100b67e65c83100067d65c831008ebe64c8310006bd64c8310076ee62c8310006ed62c831001df671c8310005f571c83100057f754831006d7c754831009e7e65483100067d6548310005bf7448310065bc7448310096be6448310006bd6448310006ee6248310006ed6248310005f7714831001df471483100067f74596100047f74596100067e74596100067d74596100047d74596100067c74596100067f73596100067e73596100067d73596100067c73596100067f43596100067e43596100067d43596100067c43596100067f72596100067e72596100067d72596100067c72596100067f42596100067e42596100067d42596100067c425961005e7f71596102567e71596100067d71596102567c71596100067f41596102567e41596100067d41596102567c41596102567e31596102567c31596102567e21596102567c21596100267f70596100267e70596100267d70596100267c70596100267f40596100267e40596100267d40596100267c40596100267f30596100267e30596100267d30596100267c30596100267f20596100267e20596100267d20596100267c20596100267f10596100267e10596100267d10596100267c105961003edf7598e1003ede7598e1003edd759
  | 6 => 0xa6248020027ea6248020077ea5248020287e95248020077ea3248020007e93248020027f26148020006f96148020027f16148020006f161480200067f74597100047f74597100067e74597100067d74597100047d74597100067c74597100067f73597100067e73597100067d73597100067c73597100067f43597100067e43597100067d43597100067c43597100067f72597100067e72597100067d72597100067c72597100067f42597100067e42597100067d42597100067c425971001e7f715971001e7e715971001e7d715971001e7c715971001e7f415971001e7e415971001e7d415971001e7c415971001e7f315971001e7e315971001e7d315971001e7c315971001e7f215971001e7e215971001e7d215971001e7c215971006e7f705971027e7e70597100067d705971027e7c70597100067f405971027e7e40597100067d405971027e7c405971027e7e305971027e7c305971027e7e205971027e7c205971001e7f105971001e7e105971001e7d105971001e7c1059710006bf7559310006be75593100063e7559310006bd75593100063d7559310006bc7559310006bf7359310006be7359310006bd7359310006bc7359310006bf5359310006be5359310006bd5359310006bc5359310006bf7259310006be7259310006bd7259310006bc7259310006bf5259310006be5259310006bd5259310006bc525931001ebf715931001ebe715931001ebd715931001ebc715931001ebf515931001ebe515931001ebd515931001ebc515931001ebf315931001ebe315931001ebd315931001ebc315931001ebf215931001ebe215931001ebd215931001ebc2159310066bf7059310276be7059310006bd7059310276bc7059310006bf5059310276be5059310006bd5059310276bc5059310276be3059310276bc3059310276be2059310276bc205931001ebf105931001ebe105931001ebd105931001ebc1059310004ff7558f10014fe7558f10004fd7558f10014fc7558f10004ff7458f1000cfe7458f10004fd7458f1000cfc7458f100067f5458f100067d5458f1001edf7358f10004ff7258f10074fc7258f10024fc7158f1001ede3158f1001edc3158f1001efa1058f1001ef91058f10074ff7598b10014fe7598b10004fd7598b10074fc7598b10074ff7498b1000cfe7498b10004fd7498b10074fc7498b100067f5498b100067d5498b1003cfe7398b10004fd7398b1001eee7298b10024fe7198b1001ef67198b10024f67198b1001eee2198b1001ef62198b1001eec2198b10004ff7558b10014fe7558b10004fd7558b10014fc7558b10004ff7458b1000cfe7458b10004fd7458b1000cfc7458b100067f5458b100067d5458b10004ff7358b1003cfc7358b1001eef7258b10024fc7158b1001eee2158b1001eec2158b10
  | 7 => 0x842003cfc7358420026f77158420006f75158420006f65158420006f55158420006f45158420006f74158420006f64158420006f54158420006f44158420076f72158420076f42158420024ff7058420024fd7058420026fa2058420026f61058420026f41058420006f77558420006f67558420006f57558420006f47558420006f77458420006f67458420006f57458420006f47458420006f75458420006775458420006f65458420006f55458420006755458420006f45458420006f77358420006f67358420006f57358420006f47358420006f75358420006f65358420006f55358420006f45358420006f74358420006f64358420006f54358420006f44358420076f67258420006f75258420076f65258420006f55258420076f45258420006f74258420076f64258420006f54258420076f44258420006f73258420076f63258420006f53258420076f43258420026f77058420026f67058420026f47058420026f75058420026f65058420026f55058420026f45058420026f74058420026f64058420026f54058420026f44058420026f73058420026f63058420026f53058420026f43058420026f72058420026f62058420026f22058420026f52058420026f4205842003cff76cc420024fe76cc420004fd76cc4201767e65cc4200067d65cc42016ebe64cc420006bd64cc42003ede63cc420006dd63cc42001ef661cc420006f561cc42001cff768c420024fe768c420004fd768c4201667e658c4200067d658c42015ebe648c420006bd648c42003ede638c420006dd638c42001ef6618c420006f5618c420004ff764c420004fd764c420024fc764c4200057f754c4200857c754c4201567e654c4200067d654c42014ebe644c420006bd644c42003ede634c420006dd634c420005ef724c420075ec724c42001ef6614c420006f5614c42001cff760c420024fe760c420004fd760c4200857e750c4200057d750c4201467e650c4200067d650c42007dbe740c420005bd740c42013ebe640c420006bd640c42003ede630c420006dd630c420075ee720c420005ed720c42001ef6610c420006f5610c420025fa700c420005f9700c420004fd768842012e7e65884200067d6588420126be6488420006bd6488420006de6388420006dd638842001ef66188420006f56188420004ff76484200057f75484200857c754842011e7e65484200067d6548420116be6448420006bd6448420005df7348420005dc7348420006de6348420006dd634842001ef66148420025fb7648020006fb7648020004fb76480200077b75480202877875480200277a6548020027796548020007bb744802028fb87448020027ba6448020027b9644802028f7b544802028f795448020027da6348020027d96348020025fb7248020027eb7248020076f
  | 8 => 0x4fd7458c2000cfc7458c200067f5458c200067d5458c20024ff7358c20026df7358c20006df5358c20006de5358c20006dd5358c20006dc5358c20006df4358c20006de4358c20006dd4358c20006dc4358c2003cff7258c20074fe7258c2003cfd7258c20074fc7258c20076de3258c20076dc3258c20004ff7158c2001cfc7158c20024fe7058c20024fc7058c20026de3058c20026dc3058c20006df7558c20006de7558c20006dd7558c20006dc7558c20006df7458c20006de7458c20006dd7458c20006dc7458c20006df5458c200065f5458c20006de5458c20006dd5458c200065d5458c20006dc5458c20076de7258c20076dc7258c20006df5258c20076de5258c20006dd5258c20076dc5258c20006df4258c20076de4258c20006dd4258c20076dc4258c20006df7158c20006de7158c20006dd7158c20006dc7158c20006df5158c20006de5158c20006dd5158c20006dc5158c20006df4158c20006de4158c20006dd4158c20006dc4158c20076df2158c20076dc2158c20026df7058c20026de7058c20026dd7058c20026dc7058c20026df5058c20026de5058c20026dd5058c20026dc5058c20026df4058c20026de4058c20026dd4058c20026dc4058c20026df2058c20026de2058c20026dd2058c20026dc2058c20026df1058c20026de1058c20026dd1058c20026dc1058c20004fd76cc8200857e75cc8200057d75cc8201b67e65cc8200067d65cc8201aebe64cc820006bd64cc82003ede63cc820006dd63cc820004ff764c82019e7e654c8200067d654c820196be644c820006bd644c82003ede634c820006dd634c820077cc324c82001ef7759842001ef6759842001ef5759842001ef4759842001ef7749842001ef6749842001ef5749842001ef47498420006f75498420006775498420006f65498420006f55498420006755498420006f4549842001ef7739842001ef6739842001ef5739842001ef47398420006f75398420006f65398420006f55398420006f45398420006f74398420006f64398420006f54398420006f4439842001ef47298420006f75298420076f65298420006f55298420076f45298420006f74298420076f64298420006f54298420076f44298420006f73298420076f63298420006f53298420076f43298420026f77098420026f67098420026f57098420026f47098420026f75098420026f65098420026f55098420026f45098420026f74098420026f64098420026f54098420026f44098420026f73098420026f63098420026f53098420026f43098420026f72098420026f62098420026f52098420026f42098420004ff7558420014fe7558420004fd7558420014fc7558420004ff745842000cfe7458420004fd745842000cfc74584200067f54584200067d5458420004ff735
  | 9 => 0xd74594200047d74594200067c74594200067f73594200067e73594200067d73594200067c73594200067f43594200067e43594200067d43594200067c43594200867f72594200767e72594200867d72594200767c72594200067f42594200767e42594200067d42594200767c42594200767e32594200767c32594200067f71594200067e71594200067d71594200067c71594200067f41594200067e41594200067d41594200067c41594200767f21594200767c21594200267f70594200267e70594200267d70594200267c70594200267f40594200267e40594200267d40594200267c40594200267f30594200267e30594200267d30594200267c30594200267f20594200267e20594200267d20594200267c20594200267f10594200267e10594200267d10594200267c1059420006bf7559020006be75590200063e7559020006bd75590200063d7559020006bc7559020006bf7359020006be7359020006bd7359020006bc7359020006bf5359020006be5359020006bd5359020006bc535902007ebf7259020076be725902007ebd7259020076bc7259020006bf5259020076be5259020006bd5259020076bc5259020076be3259020076bc3259020006bf7159020006be7159020006bd7159020006bc7159020006bf5159020006be5159020006bd5159020006bc5159020076bf2159020076bc2159020026bf7059020026be7059020026bd7059020026bc7059020026bf5059020026be5059020026bd5059020026bc5059020026bf3059020026be3059020026bd3059020026bc3059020026bf2059020026af2059020026be2059020026bd2059020026ad2059020026bc2059020026bf1059020026be1059020026bd1059020026bc105902003edf7598c2003ede7598c2003edd7598c2003edc7598c2003edf7498c2003ede7498c2003edd7498c2003edc7498c20006df5498c200065f5498c20006de5498c20006dd5498c200065d5498c20006dc5498c20076de7298c20076dc7298c20006df5298c20076de5298c20006dd5298c20076dc5298c20006df4298c20076de4298c20006dd4298c20076dc4298c2003edf7198c2003ede7198c2003edd7198c2003edc7198c20006df5198c20006de5198c20006dd5198c20006dc5198c20006df4198c20006de4198c20006dd4198c20006dc4198c20076df2198c20076dc2198c20026df7098c20026de7098c20026dd7098c20026dc7098c20026df5098c20026de5098c20026dd5098c20026dc5098c20026df4098c20026de4098c20026dd4098c20026dc4098c20026df2098c20026de2098c20026dd2098c20026dc2098c20026df1098c20026de1098c20026dd1098c20026dc1098c20004ff7558c20014fe7558c20004fd7558c20014fc7558c20004ff7458c2000cfe7458c20
  | 10 => 0x8520004ff74d852000cfe74d8520004fd74d852000cfc74d85200067f54d85200067d54d852003cfe73d8520004fd73d8520024fe70d8520024fc70d852009d7e75985200057d75985200067f65985200067c6598520095be7498520005bd7498520006bf6498520006bc6498520006f761985200057f755852009d7c75585200067f65585200067c6558520005bf7458520095bc7458520006bf6458520006bc6458520005df7358520005dc73585200067f65185200067c6518520006bf6418520006bc641852001ef66118520006f56118520004fe76cc520004fd76cc52003cfc76cc5200067f65cc5201767c65cc520006bf64cc52016ebc64cc520006f761cc52001ef461cc520004fe768c520004fd768c52001cfc768c5200067f658c5201667c658c520006bf648c52015ebc648c520006df638c52003edc638c520025fa708c520005f9708c520004ff764c520004fe764c520004fc764c5200057f754c52009d7c754c5200067f654c5201567c654c520006bf644c52014ebc644c520004fe760c520004fd760c52001cfc760c52009d7e750c5200057d750c5200067f650c5201467c650c520095be740c520005bd740c520006bf640c52013ebc640c520006df630c52003edc630c520005ee720c520005ed720c520006f7610c52001ef4610c520025fa700c520005f9700c520004fe76c85200067f65c85201367c65c8520006bf64c852010ebc64c8520024fe76885200067f658852012e7c6588520006bf6488520126bc6488520006f7618852001ef46188520025fa7088520005f97088520024fc76485200057f754852009d7c75485200067f654852011e7c6548520006bf6448520116bc6448520005df7348520005dc7348520006f7614852001ef46148520005fb7048520025f87048520004fe760852009d7e75085200057d75085200067f65085201067c6508520095be7408520005bd7408520006bf64085200febc6408520005de7308520005dd7308520025fa7008520004fe76cc120074fc76cc1200067f65cc1200f67c65cc120006bf64cc1200eebc64cc120006df63cc12003edc63cc120005ee72cc120005ed72cc12003cff764c120004fd764c12003cfc764c1200057f754c12009d7c754c1200067f654c1200d67c654c120005bf744c120095bc744c120006bf644c1200cebc644c120006df634c12003edc634c120005ef724c120005ec724c120027e8204c1200067f65c81200b67c65c8120006bf64c812008ebc64c8120025ee72c8120026ef62c8120024fa76c81200077b65c812029f7865c8120007bb64c8120297b864c81202977b54c81202977954c8120025fa72c8120026fb62c8120027eb62c8120077ea42c8120297e942c8120005f971c81200067f74594200047f74594200067e74594200067
  | 11 => 0x6be65d9120006bd65d9120006bc65d91200073c65d91200063c65d91202a7af72d9120097ac72d91202a7ae20d91202a7ac20d9120006bf75d91200063f75d9120006be75d9120006bd75d9120006bc75d91200063c75d9120006bf73d9120006be73d9120006bd73d9120006bc73d9120006bf53d9120006be53d9120006bd53d9120006bc53d91202a6bf72d9120096be72d9120096bd72d9120096bc72d9120006bf52d9120006be52d9120006bd52d9120006bc52d9120006bf71d9120006be71d9120006bd71d9120006bc71d9120006bf51d9120006be51d9120006bd51d9120006bc51d9120006bf70d91202a6be70d9120096bd70d91202a6bc70d9120006bf50d91202a6be50d9120006bd50d91202a6bc50d91202a6be30d91202a6bc30d91202a6be20d9120096bd20d91202a6bc20d91202a6be10d91202a6bc10d912003cfe76d8d200067f65d8d200067c65d8d20006bf64d8d20006bc64d8d20004ff75d8d20014fe75d8d20004fd75d8d20014fc75d8d20004ff74d8d2000cfe74d8d20004fd74d8d2000cfc74d8d200067f54d8d200067d54d8d20074fe72d8d20074fc72d8d2001cfe71d8d20004fd71d8d2009d7e7598d200057d7598d200067f6598d200067c6598d20095be7498d20005bd7498d20006bf6498d20006bc6498d20006df6398d200057f7558d2009d7c7558d200067f6558d200067c6558d20005bf7458d20095bc7458d20006bf6458d20006bc6458d20005f77158d20005f47158d20004ff7558d200067f7558d200047f7558d20014fe7558d20004fd7558d20014fc7558d200067c7558d200147c7558d20004ff7458d20006bf7458d20004bf7458d2000cfe7458d20004fd7458d2000cfc7458d20006bc7458d2000cbc7458d200067f5458d200067d5458d20006df7358d20004ff7258d20006ef7258d20004ff7158d20006f77158d20004f77158d2001cfc7158d20006f47158d2001cf47158d20004ff7058d20006fb7058d20004fe7618d200067f6518d200067c6518d20006bf6418d20006bc6418d2003ede6318d20006dd6318d20024fe76cc920024fc76cc92009d7e75cc9200057d75cc9200067f65cc9201b67c65cc920006bf64cc9201aebc64cc920006df63cc92003edc63cc920025fa70cc920005f970cc920004fe768c92009d7e758c9200057d758c9200067f658c9201a67c658c920095be748c920005bd748c920006bf648c92018ebc648c920024fc764c9200067f654c92019e7c654c920006bf644c920196bc644c920006df634c92003edc634c920005fb704c920025f8704c920004fe760c9200067f650c9201867c650c920006bf640c92017ebc640c9200067f65d85200067c65d8520006bf64d8520006bc64d8520004ff75d8520014fe75d8520004fd75d8520014fc75d
  | 12 => 0xd5458e20026df7358e20006de5358e20006dd5358e20006de4358e20006dd4358e20004ff7158e2001cfc7158e20024fc7058e20026de3058e20026dc3058e20026fa1058e200ad7e75cca200057d75cca2003ede63cca20006dd63cca20025fa70cca20005f970cca200ad7e758ca200057d758ca200a5be748ca20005bd748ca2003cff764ca2003ede634ca20006dd634ca20005fb704ca20025f8704ca20007cd320ca20004ff7558620014fe7558620004fd7558620014fc7558620004ff745862000cfe7458620004fd745862000cfc74586200067f54586200067d5458620004ff735862003cfc7358620026f77158620006f64158620006f54158620026f61058620026f4105862003cff76cc620024fe76cc620004fd76cc62001cff768c620024fe768c620004fd768c62003ede638c620006dd638c620025fa708c620005f9708c620004ff764c620004fd764c620024fc764c6200057f754c6200ad7c754c620005ef724c620005ec724c62001cff760c620024fe760c620004fd760c6200ad7e750c6200057d750c6200a5be740c620005bd740c62003ede630c620006dd630c620005ee720c620005ed720c620025fa700c620005f9700c620025f870c862001ef66188620006f56188620025fa7088620005f9708862001cff76486200057f75486200ad7c7548620005df7348620005dc734862001ef66148620006f56148620005fb7048620025f870486200ad7e75086200057d75086200a5be7408620005bd7408620005de7308620005dd7308620025fa7008620005f97008620025f976c8220076f976c82202b77b54c82202b77954c8220027ea72c8220005f971c822009d7e76d952009e7e76d95200147e76d95200057f74d95200057d74d95200067f64d95200067e64d95200067d64d95200067c64d95200073c64d95200063c64d95200076e42d95200076d42d95202af6e20d95202af6c20d95200067f74d95200047f74d95200067e74d95200067d74d95200047d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d95200067f43d95200067e43d95200067d43d95200067c43d95202ae7f72d952009e7e72d952009e7d72d952009e7c72d95200067f42d95200067e42d95200067d42d95200067c42d95200067f71d95200067e71d95200067d71d95200067c71d95200067f41d95200067e41d95200067d41d95200067c41d95200067f70d95202ae7e70d952009e7d70d95202ae7c70d95200067f40d95202ae7e40d95200067d40d95202ae7c40d95202ae7e30d95202ae7c30d95202ae7e20d952009e7d20d95202ae7c20d95202ae7e10d95202ae7c10d9520095be76d9120096be76d912000cbe76d91200073f75d91200073c75d9120006bf65d91200073f65d91200063f65d9120
  | 13 => 0x8430024fc76484300057f75484300c57c754843011e7e65484300067d6548430005df734843003ddc7348430006ee6248430006ed624843001ef66148430006f5614843001cff7608430024fe7608430004fd76084300c57e75084300057d75084301067e65084300067d65084300bdbe7408430005bd740843003dde7308430005dd7308430025fa7008430005f97008430074ff75d8f20014fe75d8f200767e75d8f200147e75d8f20004fd75d8f200767d75d8f200047d75d8f20074fc75d8f20074ff74d8f2000cfe74d8f20076be74d8f2000cbe74d8f20004fd74d8f20076bd74d8f20004bd74d8f20074fc74d8f200067f54d8f200067d54d8f20076ee72d8f2001cfe71d8f20004fd71d8f20076f970d8f20004fd7698f200b57e7598f200057d7598f20076df6398f20076dc6398f2003cff7658f20076dc6358f20004ff7558f20014fe7558f20004fd7558f20014fc7558f20004ff7458f2000cfe7458f20004fd7458f2000cfc7458f200067f5458f200067d5458f20076df7358f20024fc7258f20076de3258f20076dc3258f20004ff7158f2001cfc7158f200b57e75ccb200057d75ccb20076df63ccb20076dc63ccb20076df634cb20076dc634cb20076f7619872001ef461987200057f75587200b57c7558720005df7358720005dc7358720076f46158720004ff75587200067f75587200047f7558720014fe7558720004fd7558720014fc75587200067c75587200147c7558720004ff745872000cfe7458720004fd745872000cfc74587200067f54587200067d5458720004ff7358720006df7358720004df735872003cfc7358720006dc735872003cdc7358720024fc7258720076f72158720076f4215872003cff76cc720074fe76cc720004fd76cc72003ede63cc720006dd63cc72001cff768c720074fe768c720004fd768c720006df638c72003edc638c720004ff764c720004fd764c720074fc764c7200057f754c7200b57c754c72003ede634c720006dd634c72001cff760c720074fe760c720004fd760c7200b57e750c7200057d750c72008dbe740c720005bd740c720006df630c72003edc630c720075ee720c720005ed720c720025fa700c720005f9700c72001ef461887200057f75487200b57c7548720005df7348720005dc734872003ede63cc320006dd63cc320075ee72cc320005ed72cc32003cff764c3200057f754c3200b57c754c320005bf744c32008dbc744c32003ede634c320006dd634c320005ef724c320075ec724c320004ff7558e200067f7558e200047f7558e20014fe7558e20004fd7558e20014fc7558e200067c7558e200147c7558e20004ff7458e20006bf7458e20004bf7458e2000cfe7458e20004fd7458e2000cfc7458e20006bc7458e2000cbc7458e200067f5458e200067
  | 14 => 0x25fa7088530005f97088530004ff7648530004fe7648530004fc76485300057f75485300d57c75485300067f654853011e7c6548530006bf6448530116bc6448530005df734853003ddc7348530007cd3248530004fe7608530004fd760853001cfc76085300d57e75085300057d75085300067f65085301067c65085300cdbe7408530005bd7408530006bf64085300febc640853003dde7308530005dd7308530006ef6208530076ec6208530006f7610853001ef46108530025fa7008530005f970085300067f74594300047f74594300067e74594300067d74594300047d74594300067c745943003e7f735943003e7e735943003e7d735943003e7c735943003e7f435943003e7e435943003e7d435943003e7c43594300067f72594300067e72594300067d72594300067c72594300067f42594300067e42594300067d42594300067c425943003e7f325943003e7e325943003e7d325943003e7c32594300067f71594300067e71594300067d71594300067c71594300067f41594300067e41594300067d41594300067c415943003e7f315943003e7e315943003e7d315943003e7c31594300267f70594300267e70594300267d70594300267c70594300267f40594300267e40594300267d40594300267c40594300267f30594300265f30594300267e30594300267d30594300265d30594300267c30594300267f20594300267e20594300267d20594300267c20594300267f10594300267e10594300267d10594300267c1059430074ff7598830014fe7598830004fd7598830074fc7598830074ff749883000cfe7498830004fd7498830074fc74988300067f54988300067d5498830024fe7298830026ee7298830076ee4298830006ed429883003eef3298830076ec329883001cfe7198830004fd7198830026ee2098830026ec2098830004ff7558830014fe7558830004fd7558830014fc7558830004ff745883000cfe7458830004fd745883000cfc74588300067f54588300067d5458830026ef7258830006ee4258830006ed425883003eef325883003eec3258830004ff715883001cfc7158830026df3058830026dd3058830026ee2058830026ec2058830004ff7558430014fe7558430004fd7558430014fc7558430004ff745843000cfe7458430004fd745843000cfc74584300067f54584300067d5458430004ff7258430074fc7258430026f77158430006f64158430006f5415843003ef7315843003ef43158430026fa305843003ef93058430026f61058430026f41058430074ff76c8430024fe76c8430004fd76c84301367e65c84300067d65c8430076ee62c8430006ed62c843001cff7688430024fe7688430004fd768843012e7e65884300067d658843001ef66188430006f56188430004ff7648430004fd764
  | 15 => 0xc644c930006ef624c930006ec624c930005fb704c930025f8704c930024dc764c930315df754c930315dd754c9300075f654c93030f5c654c930305df744c930305dd744c9300079f644c9302ff9c644c9302ff5f544c9302ff5d544c93003ddf724c93003fcf724c930007cf624c930076dc624c930007cc624c930006cc624c9301dddc714c930007db704c930025de704c930025dc704c930007d8704c93003edf604c93003fdb604c9300067f65d85300067c65d8530006bf64d8530006bc64d8530004ff75d8530014fe75d8530004fd75d8530014fc75d8530004ff74d853000cfe74d8530004fd74d853000cfc74d85300067f54d85300067d54d8530074fe72d8530004fd72d8530006df32d8530006dd32d85300d57e75985300057d75985300067f65985300067c65985300cdbe7498530005bd7498530006bf6498530006bc6498530006f761985300057f75585300d57c75585300067f65585300067c6558530005bf74585300cdbc7458530006bf6458530006bc6458530005ef7258530005ec72585300067f65185300067c6518530006bf6418530006bc641853001ef66118530006f56118530024fe768c5300067f658c5301667c658c530006bf648c53015ebc648c530006f7618c53001ef4618c530025fa708c530005f9708c530024de768c5301dddf758c5302f5dd758c5300075f658c5302ef5c658c5301dddf748c5302e5dd748c5300079f648c5302df9c648c5302df5f548c5302df5d548c530005dd728c530006dc628c53003dde718c5301dedf618c530007d7618c5301dfd4618c530025de708c5301dfda708c5301dfd9708c530025dc708c53003edf608c53003fdb608c530024fc764c5300057f754c5300d57c754c5300067f654c5301567c654c530006bf644c53014ebc644c530006f7614c53001ef4614c530005fb704c530025f8704c530005de760c53003ede760c53003ddf750c53003f5e750c5302d5dd750c53003f5d750c5300055d750c5300075f650c5302cf5c650c53003ddf740c53003f9e740c5302c5dd740c53003f9d740c5300059d740c5300079f640c5302bf9c640c5302bf5f540c5302bf5d540c53003fce720c530005dd720c53003fcd720c530005cd720c530006dc620c5301ddde710c53003fd6710c5301dedf610c530025de700c53003fda700c530025da700c53003fd9700c530025dc700c53003edf600c53003fdb600c530004fe76c8530004fd76c8530074fc76c85300067f65c85301367c65c8530006bf64c853010ebc64c853003dde73c8530005dd73c8530007cd32c8530006f761c853001ef461c8530004fe7688530004fd768853001cfc76885300067f658853012e7c6588530006bf6488530126bc64885301dddf738853003ddc7388530006ef6288530006ec6288530
  | 16 => 0x95303567f30d953034e7e30d95300d67d30d953034e7c30d953034e7e20d953034e7c20d953034e7e10d953034e7c10d95300cdbe76d91300cebe76d913000cbe76d91300073f75d91300073c75d9130006bf65d91300073f65d91300063f65d9130006be65d9130006bd65d9130006bc65d91300073c65d91300063c65d913033f9f73d91300cf9c73d91300079e53d91300079d53d9130347bb30d913033f9e30d913033f9c30d9130347b830d9130006bf75d91300063f75d9130006be75d9130006bd75d9130006bc75d91300063c75d913033ebf73d9130346be73d91300cebd73d9130346bc73d9130006bf53d9130346be53d9130006bd53d9130346bc53d9130006bf72d9130006be72d9130006bd72d9130006bc72d9130006bf52d9130006be52d9130006bd52d9130006bc52d9130346bf32d9130346bc32d9130006bf71d9130006be71d9130006bd71d9130006bc71d9130006bf51d9130006be51d9130006bd51d9130006bc51d9130346bf31d9130346bc31d9130346bf70d913033ebe70d91300cebd70d913033ebc70d9130006bf50d913033ebe50d9130006bd50d913033ebc50d9130346bf30d913033ebe30d91300cebd30d913033ebc30d913033ebe20d913033ebc20d913033ebe10d913033ebc10d91300067f65d89300067c65d8930006bf64d8930006bc64d8930004ff75d8930014fe75d8930004fd75d8930014fc75d8930004ff74d893000cfe74d8930004fd74d893000cfc74d89300067f54d89300067d54d893001cfe71d8930004fd71d89300d57e75989300057d75989300067f65989300067c65989300cdbe7498930005bd7498930006bf6498930006bc6498930006ef62989300057f75589300d57c75589300067f65589300067c6558930005bf74589300cdbc7458930006bf6458930006bc6458930005f77158930005f471589300067f65189300067c6518930006bf6418930006bc6418930006ed6218930074ff7518930014fe7518930004fd7518930074fc7518930074ff741893000cfe7418930004fd7418930074fc74189300067f54189300067d541893001cfe7118930004fd7118930005de76cc93003ede76cc93003ddf75cc93003f5e75cc930335dd75cc93003f5d75cc9300055d75cc9300075f65cc93032f5c65cc93003ddf74cc930325dd74cc9300079f64cc93031f9c64cc93031f5f54cc93031f5d54cc930076dc62cc9301ddde71cc930025de70cc930025dc70cc93003edf60cc93003fdb60cc930024fe768c9300d57e758c9300057d758c9300067f658c9301a67c658c9300cdbe748c930005bd748c930006bf648c93018ebc648c930305dd738c930006ef628c930076ec628c930025fa708c930005f9708c930024fc764c9300067f654c93019e7c654c930006bf644c930196b
  | 17 => 0x74fc7498a300067f5498a300067d5498a30026ee7298a30076ee4298a30006ed4298a3001cfe7198a30004fd7198a30024fe7098a30026ee2098a30026ec2098a30004ff7558a300067f7558a300047f7558a30014fe7558a30004fd7558a30014fc7558a300067c7558a300147c7558a30004ff7458a3000cfe7458a30004fd7458a3000cfc7458a300067f5458a300067d5458a30026ef7258a30006ee4258a30006ed4258a30004ff7158a3001cfc7158a30024fc7058a30026df3058a30026dd3058a30026ee2058a30026ec2058a30026fa1058a300e57e758ca300057d758ca300ddbe748ca30005bd748ca30076ee628ca30006ed628ca30025fa708ca30005f9708ca30006ee624ca30006ed624ca3003fcc324ca30005fb704ca30025f8704ca30004ff7558630014fe7558630004fd7558630014fc7558630004ff745863000cfe7458630004fd745863000cfc74586300067f54586300067d5458630004ff7258630074fc7258630026f77158630006f75158630006f45158630006f64158630006f54158630024fc7058630026f61058630026f4105863001ef6618c630006f5618c630025fa708c630005f9708c63001cff764c6300057f754c6300e57c754c63001ef6614c630006f5614c630005fb704c630025f8704c630074ff76c8630024fe76c8630004fd76c863001cff7688630024fe7688630004fd768863001ef66188630006f56188630025fa7088630005f97088630004ff7648630004fd7648630024fc76486300057f75486300e57c7548630005df734863003ddc734863001ef66148630006f5614863001cff7608630024fe7608630004fd76086300e57e75086300057d75086300ddbe7408630005bd740863003dde7308630005dd7308630025fa7008630005f970086300d57e76d95300d67e76d95300147e76d95300057f74d95300057d74d95300067f64d95300067e64d95300067d64d95300067c64d95300073c64d95300063c64d953034f5f73d95300d75c73d95300075e43d95300075d43d95303577b30d953034f5e30d953034f5c30d95303577830d95300067f74d95300047f74d95300067e74d95300067d74d95300047d74d95300067c74d953034e7f73d95303567e73d95300d67d73d95303567c73d95300067f43d95303567e43d95300067d43d95303567c43d95300067f72d95300067e72d95300067d72d95300067c72d95300067f42d95300067e42d95300067d42d95300067c42d95303567f32d95303567c32d95300067f71d95300067e71d95300067d71d95300067c71d95300067f41d95300067e41d95300067d41d95300067c41d95303567f31d95303567c31d95303567f70d953034e7e70d95300d67d70d953034e7c70d95300067f40d953034e7e40d95300067d40d953034e7c40d
  | 18 => 0xb5258021076fa5258021006f95258021076f85258021006fb4258021076fa4258021006f94258021076f84258021006fb3258021076fa3258021006f93258021076f8325802101efb715802101efa715802101ef8715802101efb515802101efa515802101ef9515802101ef8515802101efb415802101efa415802101ef9415802101ef8415802101efb315802101efa315802101ef9315802101ef8315802101efb215802101efa215802101ef2215802101ef92158021006f1215802101ef82158021074ff7598b30014fe7598b300767e7598b300147e7598b30004fd7598b300767d7598b300047d7598b30074fc7598b30074ff7498b3000cfe7498b30076be7498b3000cbe7498b30004fd7498b30076bd7498b30004bd7498b30074fc7498b300067f5498b300067d5498b30024fe7398b30024de7398b30076ee7298b30076df3298b3003eef3298b30076ec3298b3001cfe7198b30004fd7198b3003edc3198b30004ff7558b30014fe7558b30004fd7558b30014fc7558b30004ff7458b3000cfe7458b30004fd7458b3000cfc7458b300067f5458b300067d5458b30024fc7358b3003eef7258b3003eef3258b3003eec3258b30004ff7158b3001cfc7158b3003ddf764cb30006df764cb30385df754cb30385dd754cb3037ddf744cb3037ddd744cb303775f544cb303775d544cb3003fcf724cb30076de624cb3024ddc714cb30025de704cb30025dc704cb30004ff75587300067f75587300047f7558730014fe7558730004fd7558730014fc75587300067c75587300147c7558730004ff745873000cfe7458730004fd745873000cfc74587300067f54587300067d5458730024fc7358730024dc7358730004ff7258730074fc725873003edf3258730006dd325873003ef7715873003ef7315873003edc315873003ef4315873003efa305873003ef9305873003ddd768c73024edd768c73024ddf758c73036ddd758c73024ddf748c730365dd748c73035f5f548c73035f5d548c730005dd728c730006de628c73003fd6718c73003edf618c73024edd618c730025de708c730025dc708c730074ff76c873003cfe76c8730004fd76c873003dde73c8730005dd73c8730076ee62c8730006ed62c8730007cd32c873001cff768873003cfe7688730004fd768873024ddf738873003ddc7388730004ff7648730004fd764873003cfc76487300057f75487300f57c7548730005df734873003ddc7348730006ee6248730006ed6248730007cd324873001cff760873003cfe7608730004fd76087300f57e75087300057d75087300edbe7408730005bd740873003dde7308730005dd7308730025fa7008730005f97008730074ff7598a30014fe7598a30004fd7598a30074fc7598a30074ff7498a3000cfe7498a30004fd7498a30
  | 19 => 0x8c21006dc7058c21006df5058c21006de5058c21006dd5058c21006dc5058c21006df4058c21006de4058c21006dd4058c21006dc4058c21076df2058c21076dc2058c2101edf1058c2101ede1058c2101edd1058c2101edc1058c21004fd76cc8211057e75cc8210057d75cc8211b67e65cc8210067d65cc8211aebe64cc821006bd64cc82103ede63cc821006dd63cc821004ff764c82119e7e654c8210067d654c821196be644c821006bd644c82103ede634c821006dd634c82139eee624c82101df77648421006f77648421004f7764842100777754842139774754842101f76654842101f75654842101fb6644842101fb5644842138f77544842138f755448421007d77348421007d4734842101fd6634842101fd5634842101df7724842101fe77248421076f6624842101fe66248421077e65248421397e55248421077e6424842138fe5424842101ff2604842101ff16048421026fb7598021026fa7598021026f97598021026f87598021026fb7498021026fa7498021026f97498021026f87498021006fb54980210067b5498021006fa5498021006f95498021006795498021006f85498021026fb7398021026fa7398021026f97398021026f87398021006fb5398021006fa5398021006f95398021006f85398021006fb4398021006fa4398021006f94398021006f84398021026f87298021006fb5298021076fa5298021006f95298021076f85298021006fb4298021076fa4298021006f94298021076f84298021006fb3298021076fa3298021006f93298021076f83298021026fb7198021026fa7198021026f97198021026f8719802101efb519802101efa519802101ef9519802101ef8519802101efb419802101efa419802101ef9419802101ef8419802101efb319802101efa319802101ef9319802101ef8319802101efb219802101efa219802101ef9219802101ef82198021004ff7558021014fe7558021004fd7558021014fc7558021004ff745802100cfe7458021004fd745802100cfc74580210067f54580210067d5458021004ff735802103cfc735802101ef62158021006f5215802101efb7058021006fb5058021006fa5058021006f95058021006f85058021006fb4058021006fa4058021006f94058021006f84058021076fb2058021076f8205802101efb105802101ef81058021006fb7558021006fa7558021006f97558021006f87558021006fb7458021006fa7458021006f97458021006f87458021006fb54580210067b5458021006fa5458021006f95458021006795458021006f85458021006fb7358021006fa7358021006f97358021006f87358021006fb5358021006fa5358021006f95358021006f85358021006fb4358021006fa4358021006f94358021006f84358021076fa7258021006f
  | 20 => 0x6bf5259021076be5259021006bd5259021076bc5259021076be3259021076bc325902101ebf715902101ebe715902101ebd715902101ebc715902101ebf515902101ebe515902101ebd515902101ebc515902101ebf315902101ebe315902101ebd315902101ebc315902101ebf215902101ebe215902101ebd215902101ebc2159021006bf7059021006be7059021006bd7059021006bc7059021006bf5059021006be5059021006bd5059021006bc5059021076bf2059021076bc205902101ebf105902101ebe105902101ebd105902101ebc105902103edf7598c2103ede7598c2103edd7598c2103edc7598c2103edf7498c2103ede7498c2103edd7498c2103edc7498c21006df5498c210065f5498c21006de5498c21006dd5498c210065d5498c21006dc5498c21076de7298c21076dc7298c21006df5298c21076de5298c21006dd5298c21076dc5298c21006df4298c21076de4298c21006dd4298c21076dc4298c2101edf7198c2101ede7198c2101edd7198c2101edc7198c2101edf5198c2101ede5198c2101edd5198c2101edc5198c2101edf4198c2101ede4198c2101edd4198c2101edc4198c2101edf2198c2101ede2198c2101edd2198c2101edc2198c2103edf7098c2103ede7098c2103edd7098c2103edc7098c21006df5098c21006de5098c21006dd5098c21006dc5098c21006df4098c21006de4098c21006dd4098c21006dc4098c21076df2098c21076dc2098c2101edf1098c2101ede1098c2101edd1098c2101edc1098c21004ff7558c21014fe7558c21004fd7558c21014fc7558c21004ff7458c2100cfe7458c21004fd7458c2100cfc7458c210067f5458c210067d5458c2101cff7358c2101edf7358c21006df5358c21006de5358c21006dd5358c21006dc5358c21006df4358c21006de4358c21006dd4358c21006dc4358c21074fe7258c21074fc7258c21076de3258c21076dc3258c2101cfe7158c2101cfc7158c2101ede3158c2101edc3158c2101eef2158c2101eed2158c21004ff7058c21024fc7058c21006df7558c21006de7558c21006dd7558c21006dc7558c21006df7458c21006de7458c21006dd7458c21006dc7458c21006df5458c210065f5458c21006de5458c21006dd5458c210065d5458c21006dc5458c21076de7258c21076dc7258c21006df5258c21076de5258c21006dd5258c21076dc5258c21006df4258c21076de4258c21006dd4258c21076dc4258c2101edf7158c2101ede7158c2101edd7158c2101edc7158c2101edf5158c2101ede5158c2101edd5158c2101edc5158c2101edf4158c2101ede4158c2101edd4158c2101edc4158c2101edf2158c2101ecf2158c2101ede2158c2101edd2158c2101ecd2158c2101edc2158c21006df7058c21006de7058c21006dd705
  | 21 => 0xd544c921007cf734c921007cf634c92103eee634c92103eec634c921007cc634c921007e7714c92101dee714c92101dec714c921007e4714c921004fe760c9210067f650c9211867c650c921006df630c92103edc630c9213b5ee720c921007cd320c921004fe76cc521074fc76cc5210067f65cc5211767c65cc521006df63cc52103edc63cc521005ee72cc521005ed72cc521007cd32cc52103cff764c521004fd764c52103cfc764c5210057f754c52111d7c754c5210067f654c5211567c654c521006df634c52103edc634c521005ef724c521005ec724c521007cd324c5210067f65c85211367c65c8521006df63c8521006dc63c852101dee72c852101eef62c85210077765c85213af7465c85213a77754c85213a77554c8521007d763c8521007d463c852101df672c852101ef762c852101fe762c8521077e632c8521007e532c8521005f570c85210067f65d81210067c65d8121006df63d8121006dc63d8121004ff75d8121014fe75d8121004fd75d8121014fc75d8121004ff74d812100cfe74d8121004fd74d812100cfc74d81210067f54d81210067d54d812103cfe73d8121004fd73d8121006fb40d8121006f840d812111d7e75981210057d75981210067f65981210067c6598121005de7398121005dd7398121006df6398121006dc6398121006fb60981210057f755812111d7c75581210067f65581210067c6558121005bf7458121115bc7458121005df7358121005dc7358121006df6358121006dc63581210067f65181210067c6518121006df6318121006dc6318121026fa6018121006f960181210067f74594210047f74594210067e74594210067d74594210047d74594210067c74594210067f73594210067e73594210067d73594210067c73594210067f43594210067e43594210067d43594210067c43594211067f72594210767e72594211067d72594210767c72594210067f42594210767e42594210067d42594210767c42594210767e32594210767c325942101e7f715942101e7e715942101e7d715942101e7c715942101e7f415942101e7e415942101e7d415942101e7c415942101e7f315942101e7e315942101e7d315942101e7c315942101e7f215942101e7e215942101e7d215942101e7c21594210067f70594210067e70594210067d70594210067c70594210067f40594210067e40594210067d40594210067c40594210767f20594210767c205942101e7f105942101e7e105942101e7d105942101e7c1059421006bf7559021006be75590210063e7559021006bd75590210063d7559021006bc7559021006bf7359021006be7359021006bd7359021006bc7359021006bf5359021006be5359021006bd5359021006bc53590210febf7259021076be72590210febd7259021076bc7259021
  | 22 => 0x8d21006dd50d8d21006dc50d8d21006df40d8d21006de40d8d21006dd40d8d21006dc40d8d213cedf10d8d213cedc10d8d2111d7e7598d210057d7598d210067f6598d210067c6598d21006df6398d210057f7558d2111d7c7558d210067f6558d210067c6558d21004ff7558d210067f7558d210047f7558d21014fe7558d21004fd7558d21014fc7558d210067c7558d210147c7558d21004ff7458d2100cfe7458d21004fd7458d2100cfc7458d210067f5458d210067d5458d21006df7358d21004ff7258d21006ef7258d21004ff7158d21006f77158d21004ff7058d21024fc7058d21004fe7618d210067f6518d210067c6518d2103ede6318d21006dd6318d21005de7618d21006de7618d21004de7618d21006df6518d210075f6518d210065f6518d21006de6518d21006dd6518d21006dc6518d210075c6518d210065c6518d21006df6418d21006de6418d21006dd6418d21006dc6418d210075f5418d210075d5418d21007cd7218d213efce2118d213efcc2118d2103edf7518d2103ede7518d2103edd7518d2103edc7518d2103edf7418d2103ede7418d2103edd7418d2103edc7418d21006df5418d210065f5418d21006de5418d21006dd5418d210065d5418d21006dc5418d2103edf7218d2103edd7218d2103ecd7218d21006df5218d21006de5218d21006dd5218d21006dc5218d21006df4218d21006de4218d21006dd4218d21006dc4218d2103edf7118d2103ede7118d2103edd7118d2103edc7118d21006df5118d213eede5118d21006dd5118d213eedc5118d21006df4118d213eede4118d21006dd4118d213eedc4118d213eede2118d21006dd2118d213eedc2118d2103edf7018d2103ede7018d2103edd7018d2103edc7018d21006df5018d21006de5018d21006dd5018d21006dc5018d21006df4018d21006de4018d21006dd4018d21006dc4018d213eedf1018d213eedc1018d2101cfe76cc92101cfc76cc92111d7e75cc9210057d75cc9210067f65cc9211b67c65cc921006df63cc92103edc63cc92101df671cc921005f571cc921004fe768c92111d7e758c9210057d758c9210067f658c9211a67c658c921115be748c921005bd748c921006df638c92103edc638c921005ee768c921006ee768c9213e76e758c9210076d758c9210076f658c9213e76c658c9213dfae748c921007ad748c9213df6f548c9213df6d548c9213d5ed738c921007cf638c92103eee638c92103eec638c921007cc638c92103ecc638c92101dee718c92101dec718c921076ef618c9213cfce318c9213cfcc318c92101cfc764c9210067f654c92119e7c654c921006df634c92103edc634c921005f7714c92101df4714c92101dec764c92103eec764c92101cec764c9210076f654c9213c76c654c9213bf6f544c9213bf6
  | 23 => 0x3cff764ca2103ede634ca21006dd634ca21005f7714ca2101df4714ca213eedf630ca2103edc630ca2101df576c8621076f576c86214077754c86214077554c862101fe672c8621077e652c86213ffe552c8621005f570c8621004ff7558221014fe7558221004fd7558221014fc7558221004ff745822100cfe7458221004fd745822100cfc74582210067f54582210067d5458221004ff735822103cfc735822101efb705822101efb105822101ef8105822111d7e76d952111e7e76d95210147e76d95210057f74d95210057d74d95210067f64d95210067e64d95210067d64d95210067c64d95213f76e21d95213f76c21d95210067f74d95210047f74d95210067e74d95210067d74d95210047d74d95210067c74d95210067f73d95210067e73d95210067d73d95210067c73d95210067f43d95210067e43d95210067d43d95210067c43d95213f67f72d952111e7e72d952111e7d72d952111e7c72d95210067f42d95210067e42d95210067d42d95210067c42d95210067f71d95213f67e71d952111e7d71d95213f67c71d95210067f41d95213f67e41d95210067d41d95213f67c41d95213f67e31d95213f67c31d95213f67e21d952111e7d21d95213f67c21d95210067f70d95210067e70d95210067d70d95210067c70d95210067f40d95210067e40d95210067d40d95210067c40d95213f67f10d95213f67c10d952103cfe76d8d210067f65d8d210067c65d8d21004ff75d8d21014fe75d8d21004fd75d8d21014fc75d8d21004ff74d8d2100cfe74d8d21004fd74d8d2100cfc74d8d210067f54d8d210067d54d8d21006df53d8d21006de53d8d21006dd53d8d21006dc53d8d21006df43d8d21006de43d8d21006dd43d8d21006dc43d8d21024fe70d8d21004fd70d8d2103cde76d8d21006df65d8d210075f65d8d210065f65d8d21006de65d8d21006dd65d8d21006dc65d8d210075c65d8d210065c65d8d21006df64d8d21006de64d8d21006dd64d8d21006dc64d8d210075f54d8d210075d54d8d213cfcf72d8d213cfce21d8d213cfcc21d8d21006df75d8d21006de75d8d21006dd75d8d21006dc75d8d21006df74d8d21006de74d8d21006dd74d8d21006dc74d8d21006df54d8d210065f54d8d21006de54d8d21006dd54d8d210065d54d8d21006dc54d8d213cedf72d8d21006dd72d8d21006df52d8d21006de52d8d21006dd52d8d21006dc52d8d21006df42d8d21006de42d8d21006dd42d8d21006dc42d8d21006df71d8d213cede71d8d21006dd71d8d213cedc71d8d21006df51d8d213cede51d8d21006dd51d8d213cedc51d8d21006df41d8d213cede41d8d21006dd41d8d213cedc41d8d213cede21d8d213cedc21d8d21006df70d8d21006de70d8d21006dd70d8d21006dc70d8d21006df50d8d21006de50d
  | 24 => 0x9415803101ef8415803101efb315803101efa315803101ef9315803101ef8315803101efb215803101efa215803101ef9215803101ef82158031074ff75d8f21014fe75d8f210767e75d8f210147e75d8f21004fd75d8f210767d75d8f210047d75d8f21074fc75d8f21074ff74d8f2100cfe74d8f21076be74d8f2100cbe74d8f21004fd74d8f21076bd74d8f21004bd74d8f21074fc74d8f210067f54d8f210067d54d8f21076ee72d8f21076f571d8f213cede31d8f213cedc31d8f21024fe70d8f21004fd70d8f21004fd7698f211357e7598f210057d7598f21076df6398f21076dc6398f2103cff7658f21076dc6358f21004ff7558f21014fe7558f21004fd7558f21014fc7558f21004ff7458f2100cfe7458f21004fd7458f2100cfc7458f210067f5458f210067d5458f21076df7358f2101cfc7258f21076de3258f21076dc3258f21004ff7058f21024fc7058f211357e75ccb210057d75ccb21076df63ccb21076dc63ccb2101ded768cb21076ed768cb2101ced768cb210776e758cb210776d758cb21077ae748cb21077ad748cb2140f6f548cb2140f6d548cb2103eee638cb21077ce638cb21077cd638cb21076ec638cb2101dee718cb21077e6718cb21077e5718cb2101dec718cb213cfce318cb213cfcc318cb21076df634cb21076dc634cb21077cc324cb21005ef764cb21006ef764cb2139f6f544cb2139f6d544cb21077cf734cb21077cf634cb2103eee634cb2103eec634cb21077cc634cb2101dee714cb2101dec714cb2103ede63cc721006dd63cc721075ee72cc721005ed72cc721007cd32cc72103cff764c7210057f754c7211357c754c72103ede634c721006dd634c721005ef724c721075ec724c721007cd324c721076fb6098321026f860983210057f75583211357c7558321005bf745832110dbc7458321076f86058321004ff75583210067f75583210047f7558321014fe7558321004fd7558321014fc75583210067c75583210147c7558321004ff7458321006bf7458321004bf745832100cfe7458321004fd745832100cfc7458321006bc745832100cbc74583210067f54583210067d5458321004ff735832103cfc735832101cfc7258321076fb2058321076f82058321004ff7558e210067f7558e210047f7558e21014fe7558e21004fd7558e21014fc7558e210067c7558e210147c7558e21004ff7458e2100cfe7458e21004fd7458e2100cfc7458e210067f5458e210067d5458e2101edf7358e2101cfc7158e2101ede3158e2101edc3158e2101eef2158e2101eed2158e21004ff7058e21024fc7058e2112d7e75cca210057d75cca2103ede63cca21006dd63cca2101df671cca21005f571cca2112d7e758ca210057d758ca21125be748ca21005bd748ca213cedf638ca2103edc638ca21
  | 25 => 0x883103ecf305883103eee305883103eed305883103eec305883101eef105883101eee105883101eed105883101eec105883103ddd768c831006dd768c831004dd768c83141f5e758c8310075d758c83103f5e658c83103f5d658c8314179e748c8310079d748c83103f9e648c83103f9d648c8314175f548c8314175d548c83103dde728c83103fce728c83103fce628c831006dd628c83103fcd628c831006cd628c8313cddd718c8313cede618c83103fd6618c831005dd708c83103fda608c83103fd9608c831026fb7598031026fa7598031026f97598031026f87598031026fb7498031026fa7498031026f97498031026f87498031006fb54980310067b5498031006fa5498031006f95498031006795498031006f85498031026fb7398031026fa7398031026f97398031026f8739803103efb539803103efa539803103ef9539803103ef8539803103efb439803103efa439803103ef9439803103ef84398031026fb7298031026fa7298031026f97298031026f87298031006fb5298031006fa5298031006f95298031006f85298031006fb4298031006fa4298031006f94298031006f8429803103efb329803103efa329803103ef9329803103ef83298031026fb7198031026fa7198031026f97198031026f8719803101efb519803101efa519803101ef9519803101ef8519803101efb419803101efa419803101ef9419803101ef8419803101efb319803101efa319803101ef9319803101ef8319803101efb219803101efa219803101ef9219803101ef82198031004ff7558031014fe7558031004fd7558031014fc7558031004ff745803100cfe7458031004fd745803100cfc74580310067f54580310067d5458031004ff7258031074fc725803101efb7058031006fb5058031006fa5058031006f95058031006f85058031006fb4058031006fa4058031006f94058031006f8405803103efb305803103ef8305803101efb105803101ef81058031006fb7558031006fa7558031006f97558031006f87558031006fb7458031006fa7458031006f97458031006f87458031006fb54580310067b5458031006fa5458031006f95458031006795458031006f8545803103efb735803103efa735803103ef8735803103efb535803103efa535803103ef9535803103ef8535803103efb435803103efa435803103ef9435803103ef84358031006fb7258031006fa7258031006f97258031006f87258031006fb5258031006fa5258031006f95258031006f85258031006fb4258031006fa4258031006f94258031006f8425803103efb325803103efa325803103ef9325803103ef8325803101efb715803101efa715803101ef8715803101efb515803101efa515803101ef9515803101ef8515803101efb415803101efa415803101ef
  | 26 => 0x74ff7598831014fe7598831004fd7598831074fc7598831074ff749883100cfe7498831004fd7498831074fc74988310067f54988310067d549883101cfe729883101eee7298831006ef5298831076ee5298831006ed5298831076ec5298831006ef4298831076ee4298831006ed4298831076ec429883103eef3298831076ec329883101eee219883101eec2198831024fe7098831004fd7098831076ef7598831006ee7598831006ed7598831076ec7598831076ef7498831006ee7498831006ed7498831076ec7498831006ef54988310066f5498831006ee5498831006ed54988310066d5498831006ec549883103eee739883103eed7398831076ec739883103eef539883103eee539883103eed539883103eec539883103eef439883103eee439883103eed439883103eec439883101eee719883101eed719883101eec719883101eef519883101eee519883101eed519883101eec519883101eef419883101eee419883101eed419883101eec419883101eef319883101eee319883101eed319883101eec3198831076ef7098831006ee7098831006ed7098831076ec7098831006ef5098831006ee5098831006ed5098831006ec5098831006ef4098831006ee4098831006ed4098831006ec409883103eef309883103eee309883103eed309883103eec309883101eef109883101eee109883101eed109883101eec1098831004ff7558831014fe7558831004fd7558831014fc7558831004ff745883100cfe7458831004fd745883100cfc74588310067f54588310067d545883101eef7258831006ef5258831006ee5258831006ed5258831006ec5258831006ef4258831006ee4258831006ed4258831006ec425883103eef325883103edc325883103eec325883103ecc325883101edf315883101edd315883101eee215883101eec2158831004ff7058831024fc705883103edf3058831006ef7558831006ee7558831006ed7558831006ec7558831006ef7458831006ee7458831006ed7458831006ec7458831006ef54588310066f5458831006ee5458831006ed54588310066d5458831006ec545883103eef735883103eee735883103eec735883103eef535883103eee535883103eed535883103eec535883103eef435883103eee435883103eed435883103eec435883101eef715883101eee715883101eec715883101eef515883101eee515883101eed515883101eec515883101eef415883101eee415883101eed415883101eec415883101eef315883101ecf315883101eee315883101eed315883101ecd315883101eec3158831006ef7058831006ee7058831006ed7058831006ec7058831006ef5058831006ee5058831006ed5058831006ec5058831006ef4058831006ee4058831006ed4058831006ec405883103eef305
  | 27 => 0x7714c93101df4714c93101cdc764c9310075f654c93142f5c654c9314275f544c9314275d544c93103ddf724c93103fcf724c931007cf624c931076dc624c931007cc624c931007d7714c93101dde714c93101ddc714c931007d4714c93103edf614c93103fd7614c9310067f65d81310067c65d8131004ff75d8131014fe75d8131004fd75d8131014fc75d8131004ff74d813100cfe74d8131004fd74d813100cfc74d81310067f54d81310067d54d8131074fe72d8131004fd72d8131006df32d8131006dd32d813124ede31d813124edc31d81311557e75981310057d75981310067f65981310067c6598131006fb60981310057f75581311557c75581310067f65581310067c6558131005bf745813114dbc7458131005ef7258131005ec72581310067f65181310067c6518131026fa6018131006f960181310067f74594310047f74594310067e74594310067d74594310047d74594310067c745943103e7f735943103e7e735943103e7d735943103e7c735943103e7f435943103e7e435943103e7d435943103e7c43594310067f72594310067e72594310067d72594310067c72594310067f42594310067e42594310067d42594310067c425943103e7f325943103e7e325943103e7d325943103e7c325943101e7f715943101e7e715943101e7d715943101e7c715943101e7f415943101e7e415943101e7d415943101e7c415943101e7f315943101e7e315943101e7d315943101e7c315943101e7f215943101e7e215943101e7d215943101e7c21594310067f70594310067e70594310067d70594310067c70594310067f40594310067e40594310067d40594310067c405943103e7f305943103e5f305943103e7e305943103e7d305943103e7c305943101e7f105943101e7e105943101e7d105943101e7c1059431006bf7559031006be75590310063e7559031006bd75590310063d7559031006bc755903103ebf735903103ebe735903103ebd735903103ebc735903103ebf535903103ebe535903103ebd535903103ebc5359031006bf7259031006be7259031006bd7259031006bc7259031006bf5259031006be5259031006bd5259031006bc525903103ebf325903103ebe325903103ebd325903103ebc325903101ebf715903101ebe715903101ebd715903101ebc715903101ebf515903101ebe515903101ebd515903101ebc515903101ebf315903101ebe315903101ebd315903101ebc315903101ebf215903101ebe215903101ebd215903101ebc2159031006bf7059031006be7059031006bd7059031006bc7059031006bf5059031006be5059031006bd5059031006bc505903103ebf305903103e9f305903103ebe305903103ebd305903103ebc305903101ebf105903101ebe105903101ebd105903101ebc1059031
  | 28 => 0xca31006ed624ca31005f7714ca3101df4714ca313eddd760ca3103edd760ca3145f5f540ca3145f5d540ca3103fce720ca31006dd620ca3103ddf710ca313eddd710ca3103fd6610ca31005dd700ca31004ff7558231014fe7558231004fd7558231014fc7558231004ff745823100cfe7458231004fd745823100cfc74582310067f54582310067d5458231004ff7258231074fc725823101cfc715823101efb705823101efb105823101ef810582311557e76d95311567e76d95310147e76d95310057f74d95310057d74d95310067f64d95310067e64d95310067d64d95310067c64d95314577731d953144f5e31d953144f5c31d95314577431d95310067f74d95310047f74d95310067e74d95310067d74d95310047d74d95310067c74d953144e7f73d95314567e73d95311567d73d95314567c73d95310067f43d95314567e43d95310067d43d95314567c43d95310067f72d95310067e72d95310067d72d95310067c72d95310067f42d95310067e42d95310067d42d95310067c42d95314567f32d95314567c32d95314567f71d953144e7e71d95311567d71d953144e7c71d95310067f41d953144e7e41d95310067d41d953144e7c41d95314567f31d953144e7e31d95311567d31d953144e7c31d953144e7e21d953144e7c21d95310067f70d95310067e70d95310067d70d95310067c70d95310067f40d95310067e40d95310067d40d95310067c40d95314567f30d95314567c30d953144e7f10d953144e7c10d95310067f65d89310067c65d8931004ff75d8931014fe75d8931004fd75d8931014fc75d8931004ff74d893100cfe74d8931004fd74d893100cfc74d89310067f54d89310067d54d8931006ee42d8931006ed42d8931024fe70d8931004fd70d89311557e75989310057d75989310067f65989310067c659893114dbe7498931005bd7498931006ef62989310057f75589311557c75589310067f65589310067c65589310067f65189310067c6518931006ed6218931074ff7518931014fe7518931004fd7518931074fc7518931074ff741893100cfe7418931004fd7418931074fc74189310067f54189310067d5418931076ee4218931006ed42189313eede31189313eedc3118931024fe7018931004fd7018931005de76cc93103ede76cc931004de76cc93103f5e75cc93103f5d75cc9310075f65cc9314475c65cc93143f5f54cc93143f5d54cc931076dc62cc93101dde71cc93101ddc71cc93103edf61cc93103fd761cc93101cfe768c9311557e758c9310057d758c9310067f658c9311a67c658c93114dbe748c931005bd748c931435dd738c931006ef628c931076ec628c93101df6718c931005f5718c93101cfc764c9310067f654c93119e7c654c931006ef624c931006ec624c93103fcc324c931005f
  | 29 => 0x14fc75580320067c75580320147c7558032004ff7458032006bf7458032004bf745803200cfe7458032004fd745803200cfc7458032006bc745803200cbc74580320067f54580320067d545803203edf3258032006dd3258032004ff715803201cfc715803203edc3158032076fb7058032006fa5058032006f95058032006fa4058032006f9405803203efb305803203ef83058032076fb2058032076f82058032074ff7598b31014fe7598b310767e7598b310147e7598b31004fd7598b310767d7598b310047d7598b31074fc7598b31074ff7498b3100cfe7498b31076be7498b3100cbe7498b31004fd7498b31076bd7498b31004bd7498b31074fc7498b310067f5498b310067d5498b3101cfe7398b3101cde7398b31076ee7298b31076df3298b3103eef3298b31076ec3298b313cede3198b3103edc3198b31024fe7098b31004fd7098b31004ff7558b31014fe7558b31004fd7558b31014fc7558b31004ff7458b3100cfe7458b31004fd7458b3100cfc7458b310067f5458b310067d5458b3101cfc7358b3103eef7258b3103eef3258b3103eec3258b31004ff7058b31024fc7058b3103ddf764cb31006df764cb314775f544cb314775d544cb3103fcf724cb3103fcf624cb31076de624cb3103fcc624cb3101dde714cb3101ddc714cb31004ff75583310067f75583310047f7558331014fe7558331004fd7558331014fc75583310067c75583310147c7558331004ff7458331006bf7458331004bf745833100cfe7458331004fd745833100cfc7458331006bc745833100cbc74583310067f54583310067d545833101cfc7358331004ff7258331074fc725833103edf3258331006dd32583311dede315833103edc315833103efb705833103efb305833103ef83058331074ff7598a31014fe7598a31004fd7598a31074fc7598a31074ff7498a3100cfe7498a31004fd7498a31074fc7498a310067f5498a310067d5498a3101eee7298a3101cfe7198a3101eee2198a3101eec2198a31024fe7098a31004fd7098a31004ff7558a310067f7558a310047f7558a31014fe7558a31004fd7558a31014fc7558a310067c7558a310147c7558a31004ff7458a3100cfe7458a31004fd7458a3100cfc7458a310067f5458a310067d5458a3101eef7258a3101cfc7158a3101edf3158a3101edd3158a3101eee2158a3101eec2158a31004ff7058a31024fc7058a311657e758ca310057d758ca3115dbe748ca31005bd748ca31076ee628ca31006ed628ca3101df6718ca31005f5718ca3146f5e758ca310075d758ca314679e748ca310079d748ca314675f548ca314675d548ca3103dde728ca313cfce628ca31006dd628ca313cfcd628ca313cfd6718ca313cddd718ca31007d5718ca3103ede618ca31005dd708ca31006ee624
  | 30 => 0xd52cca323cdde71cca320067e65986320067d6598632006be6498632006bd6498632076f7619863201ef461986320067e65586320067d6558632006be6458632006bd6458632076f46158632004ff7558632014fe7558632004fd7558632014fc7558632004ff745863200cfe7458632004fd745863200cfc74586320067f54586320067d5458632074fc7258632006df3258632076f72158632076f42158632004ff7058632024fc70586320067e65982320067d6598232006be6498232006bd6498232076fb6098232026f860982320067e65582320067d6558232006be6458232006bd6458232076f86058232004ff7558232014fe7558232004fd7558232014fc7558232004ff745823200cfe7458232004fd745823200cfc74582320067f54582320067d5458232074fc7258232006df3258232004ff715823201cfc7158232076fb2058232076f8205823219d7e758c9320057d758c932195be748c932005bd748c93203dee728c93203eef628c9320775e758c9320775d758c9320779e748c9320779d748c9324875f548c9324875d548c932075de728c932076df628c93203fcf628c932005dd718c932005dd708c932004ff75d8532014fe75d8532004fd75d8532014fc75d8532004ff74d853200cfe74d8532004fd74d853200cfc74d85320067f54d85320067d54d8532006f751d8532006f451d8532006f641d8532006f541d8532024fe70d8532004fd70d8532006f761985320057f755853219d7c755853219d7e75185320057d7518532195be7418532005bd74185323cedf631853201ef66118532006f56118532005fa7018532005f97018532004ff75d8132014fe75d8132004fd75d8132014fc75d8132004ff74d813200cfe74d8132004fd74d813200cfc74d81320067f54d81320067d54d813201cfe71d8132004fd71d8132006fb60981320057f755813219d7c7558132005bf7458132195bc7458132005f77158132005f4715813219d7e75181320057d7518132026fa6018132006f96018132075df764c832006df764c832004df764c83247f5f544c83247f5d544c832075df724c83203fcf724c832076de624c832077ce624c832077ce424c83247fcd424c8323eddc714c832004ff75584320067f75584320047f7558432014fe7558432004fd7558432014fc75584320067c75584320147c7558432004ff745843200cfe7458432004fd745843200cfc74584320067f54584320067d545843203edf325843203eee3258432006dd325843203eed3258432076f77158432006f65158432006f55158432006f64158432006f5415843203ef7315843203edc315843203ef43158432076f72158432076f42158432004ff7058432024fc7058432004ff75580320067f75580320047f7558032014fe7558032004fd7558032
  | 31 => 0x873203eee325873203eed325873203ef7715873203ef7315873203ef43158732004ff7058732024fc7058732004ff7558332014fe7558332004fd7558332014fc7558332004ff745833200cfe7458332004fd745833200cfc74583320067f54583320067d5458332004ff715833201cfc715833203efb7058332006fb4058332006f8405833203efb305833203ef830583320757f76596321a67f76596320147f76596320057f74596320057d74596320767f64596320067e64596320773e64596320063e64596320067d64596320767c64596324a76f32596320776c32596320767f61596320767c61596320767f60596320767c60596320067f74596320047f74596320067e74596320067d74596320047d74596320067c74596321a67f73596324a67e73596320067d73596324a67c73596320067f43596324a67e43596320067d43596324a67c43596321a67f72596320767e72596321a67d72596320767c72596320067f42596320767e42596320067d42596320767c42596324a67f32596320767e32596320767c32596320067f71596320067e71596320067d71596320067c71596320067f41596320067e41596320067d41596320067c41596324a67f31596324a67c31596320767f21596320767c21596320067f70596320067e70596320067d70596320067c70596320067f40596320067e40596320067d40596320067c40596324a67f30596324a67c30596320767f20596320767c2059632075bf765923218ebf765923200cbf76592320073e75592320073d7559232076bf6559232006be65592320773e65592320063e6559232006bd65592320773d65592320063d6559232076bc655923249faf3259232077ac3259232076bf6159232076bc6159232076bf6059232076bc6059232006bf7559232006be75592320063e7559232006bd75592320063d7559232006bc755923218ebf735923249ebe7359232006bd735923249ebc7359232006bf535923249ebe5359232006bd535923249ebc535923218ebf7259232076be725923218ebd7259232076bc7259232006bf5259232076be5259232006bd5259232076bc525923249ebf3259232076be3259232076bc3259232006bf7159232006be7159232006bd7159232006bc7159232006bf5159232006be5159232006bd5159232006bc515923249ebf315923249ebc3159232076bf2159232076bc2159232006bf7059232006be7059232006bd7059232006bc7059232006bf5059232006be5059232006bd5059232006bc505923249ebf305923249ebc3059232076bf2059232076bc2059232075dd76cca3203edd76cca3203f5e75cca3203f5d75cca320775e65cca320775d65cca320779e64cca320779d64cca324975f54cca324975d54cca32077ce62cca32077ce52cca3248fc
  | 32 => 0x400200001c001c000000000003800a002001800401e009003800003200000180940000260028008006003002000801e0000088000000001003002001202101600180100080000000022002003000402a001000002c006005001803001c000006000800800a0010004006000011800c0020110018054000014006806000201600080000040000050004004001000000008600000000180000010080010008000001000007200a00300080180060008000002004003800002600a0000028012000005002c006000000001400200d0000000018000002000001e00100080c80000000000058010012000801000c00f00180540100000020000016001001802c00200600a0010002012001808003400f006805000c01f0018000010000004002001800000180080020000068004016018005000800000800a800001400d00000140fc0080058008002034002800c00c0010038010002018002800801200a0018008008000001800402c01d008000400200100b8048006001000003800200c00000040040050240048028000000001001200000600000060020000000000015002002c000000000000000800e03780740000110038080004001000818c01c007009001c000001001000c000002003001c01200800000340120000000010004000000003c0080170000034004000000003801604e000000001c0060010000008005002000400000d00000740000150120004006009000800400000b0030018010001003000c00000e015002800a000002005804e001000000c004001001000401400200300100020110018098004000001000400c005000000000a00a000001c008008001801401400d0190018000000004800c00c057003800000600000200000040020058118000004009000802800700e80500060020067f74597320047f74597320067e74597320067d74597320047d74597320067c745973203e7f735973203e7e735973203e7d735973203e7c735973203e7f435973203e7e435973203e7d435973203e7c43597321b67f72597321b67e72597320067d72597321b67c72597320067f42597320067e42597320067d42597320067c425973203e7f325973203e7e325973203e7d325973203e7c32597320067f71597320067e71597320067d71597320067c71597320067f41597320067e41597320067d41597320067c415973203e7f315973203e7e315973203e7d315973203e7c31597320067f70597320067e70597320067d70597320067c70597320067f40597320067e40597320067d40597320067c405973203e7f305973203e5f305973203e7e305973203e7d305973203e7c3059732004ff7558732014fe7558732004fd7558732014fc7558732004ff745873200cfe7458732004fd745873200cfc74587320067f54587320067d545
  | 33 => 0x20088010000025003000c08200000280500280050000024002003004801001e003000001000e004006800404c008012001802c001001800c000018001800802000200000140000000010034026001000803c05a00c000800801a0100020014000028007000400e000000000400200c0048014034004001001c04801800c8008000001019000003e01c0128000018007003800800401700000080000030008010000008003802411e00600400100aa00f000801400a0000008018012000000804804600100000340160000018058002000003801801400101e803400600000100040160000008020000000002800801c0050000088004004002801c00001c001805c01c00e00180000040020008024000005000000008000400a000800201c0008034000006000017804a0020068000004000000000c000026003800400200200600000000030098064080011016800000000a0000000000002003813801c00000d00c0094009000002c00e06e001000000600a000000002c003000801c0180a3000802c00600e0028018002001000800c01001b00f000c01200c0078000004016000000400e000001009800000a00000080000020000010000004003000001200500300040020020020048024003012800000200000280800000050208000002002004000001c001005002800000000e8004012001000800400e005006000802e000001008801400100a800806000b001005800c01d004800c026006004002c002004001003c028000004802000200e017000805400200080880260160018000002000005000001a00700c0000024004000000001a007001804c002000002000000602500880040020040030034000003003002000002e0060008006000000000000000e001800401a001000001400200700680840000020008088004006001003c00800900000700000000188004000002000001c03e0000090118002002002800801e00f0000050040001000005000201e0010000004016000000000800000000b00000220020024018002002002002e001002817c03c007024800c0080030048040000005000002804c0080020074000002006801800000000d0000018001006011401e003001000800a00000500400000120058000004000002000c0120050070010076002000803401c00b00a000401400a00f801400000f001800c022000002007000000600080640020140060034000000004000c02400b001000000600d0008010014000001000c00002a00700080ae00000d0008008002000000800801e00100300000000028004004001002801c004003014000002800e004004c02001500000240000150010020000011000000c0020050010000000000007000000800700000140160050000000008005000804400200a0060004006006006800
  | 34 => 0x4401000d0050000000001008007401a001003800c002012000000001600000000b406c00100100080120020028014008009031001000000d00480ec01c00900a000000e0010008010002016007800c022006003000005000000280480120100000034006002012001000200400100cc00000600f802403800c010812c008013000800802000f002000000001600400200040050000018038001006000001a00000780540000000008024000000009002000600400c00100220120000000000000000002c0ac0030000030008009005800000a000000802001200700000a4008000000002800e0050028018026009000804400200000b80440020030020004000004001801c012000008006c000000003800400000300900000000020008034004007000000c00e000001000c00000100000040ae007008802000000801900000060090268000074000002800401201001f001005c0170028000000008001000002e00102300040300000000008000003002801c00404900080080160010090000008000004800805803501c80b80160010198014006006009800c03a01c001002408e0050000000014000001000c002000000000400c030005800000400200c00080000200000000022002000800001400b00000000000040158044010000031800400000b024000c004001001800802e0090020000002011002000c0020110000000012008000000007a004032808000a0000000010000000002000400e042006801004c01300b8000000000000000000000300680b801c000000000000a0250010048000000000003801600600a804c006003000000001801700100100040030050004004000000002000200b000802400e003001802c03a002000001002601d000002400402b004000400e008005802402e0260050004006021005000800a009013002c02a01300100040080020000058018002003806401200b010000c000023000004400a000015008c00402600100100200010048004016003000802801e00100180740000140018010000002000000c00600d0010000012037009006c0000140020000000013000800401000000c800000400401a0004002000004001c00000600580840080170000048002009000000400400000280040000030000044000002006800408c00f004803800000c00f805c00000c006003402800f00000000220070000084034006000003403e001006804403000a00080a00040130098018016004007000000001a00480200140000018004000000006801c00000700480040040020048038012003004002c004005000000400600f00d807c0060180000018006001000000400c001009800000400000001c000000100d0018010004007804c00000d00000040000060000010000000001802002e001001001000c00
  | 35 => 0x3729a340000000739000000028487f6800079d93d27fe00000000000a5180000000000000178a77e800000001da0000a3e0002490301805c6d380001b02a3c000000000019e25c58000a35000000027008c916ac09a841a69e06e83eb22d69bda2380000cca3a71bc261989961d2a8c83352ae24570fe2a1a80002c4858c1dd9b288d281ca1b28ce20de94e094e17868f281ec0e48ea083ea0bc7ed1c2c84a0c6c7a996a25c080da000000044c800067600001ff00000000000139aa2c00015849368000000289041f00004d3800000026dc21d9a6603100000f096ce3f198781ff832c98484fe721089a260005824e84b800002941e728a455291f696a0be60000c121c413166c9a1ae1a8a2ea00010d6378963495526140760f9c00002684450a7c2f89954180160e4670132762995ea87a9e47c0a3d237f9cc22e39970000196030728e4a93800051080000000000000014c8ee04500000e9e4b326b8000072000019286821228a9b9d4ea611188000058400006ac2508c6600027400000f840000f4200000008c723aa80b80003e909d23450d223d52606000000000000001720a78ac782c60000c628d6841c3b1800098a10367068800000277a000000096ba3ce1c983065d2a56000029b012780006dd89e80001874841800093889fe000122a000236486e29723620d52a9f10dc7e4aa6001b0130550203aab581b888580001738e8ea67a3b234907720000f0431c98fe697160c27e10b60000310731844e1b3848253d0e48a7a9e54a638a4e6109a680b2a60e695a37e6fca40815c893e1449d5258e9b4223e800070d00005540d4408e04d6a3d00004b280b00000fc4ab48000a709f827508dac2ae0a18509004200009744739d9a0988df6ac210740be16b014f9a52000000003600000000e5a0000cd80001fec2bb9886897a432910976c934800059c93666420aa600008d07578fa046d08dc5f88e6c627a8d221a15d23c8a1581ac9ea262506ec06c255014a00005419b1e000073228b81880000000016a7c6001001000000f00080000000000020038000007002000000c00d000803800a000000002000c00500000440000040110004000001001000001801600200240200030058000016004000000401a0140020028002004001002400e00c004800c00a0010038000000004000002800600a0000024000006002000000a0030110004002001006000805803b004000000c000000803c010000000000c000001000001002400a0008044000004003009c022001001800400000500400380080030008004028004000002800200b006808400600c000000c016003000005403e01100d8018010000000000c004005017802c00000100000400160000000044008003007002006200900080000000050330030048002002804800200100180
  | 36 => 0x2b185130ac820a80000001084565a39499b9690765800000003be86a85cc65c832843980000a0021e18f953a58116a800019224e186c4181a9ac0238358a3b872e6d9a3bc04a8ad20ae8fba78a08ac97104c2170a5ee741a738000112a350a3dc014076672b80603058ae88a58dd00000bea00005a005916a60000000913a0ce2ea8bb0a1992d89c38bec000000069327a288883021e21328000111e3f3a0720ba0b840000000138844855d9f787c3129030d000021e000065f8000a5e226c4330ebe000000000023c47598000000000020c23e89230fe848900000319b7a00008c000008f8a100000a1b80009800c9c81780000001a9c3ef00b80000000a18177c0000386105267e6a119564180a8e9e38148a5328980e8904a9328000383800011800000bba8e25aca4140889b3c3782ae63a598c828c855c08112927cf25127a0a3347fb9cf87e585e894fa9de874a3d032229360c880003c38a545bb00004c9087e47d1a308919402925091a6f9a6cc9f280a0000000006324701cd9ee4a698e823f314de0a6800000001c873d028886280000bf800067e261ea5d1c4400008064109de474b04e055a02769641f660000000000199c0a38000585021a5259cd6133979a00002d6000000073796e018b270c12c864a2e68aae9131c125fd0ad606e84d40001cd43e4ab0c00000fc290a15c9041fd4a6e97b073d9eee7cea82c78e20e84ac85a481e86f2467a5a61561c2a99f24d607b91f85d59db4750016c7ae17a27630f365d4872ca8606e48a924525b513c06641b0441784b6405a0300a28e9873a85889461b2250128740881ae2427a4a84a6917870c11106c9289c5b0a5f281c08f621691406ba14d84d3240c0a317dc207967483e1b8e7a70d36209113450d97deaac9abc2770ae29180c705f128622ab14fa26804d21718dc68fd2260a0aa5dc71292f0999a0a6aba297a58c151e06d93621640e0204311a04cb0bf000003ae5128d283a515fca9407ea95e80000001e9e9ba146a0860d60a099d7849205929db00000000000000000063c8ed800001620540000000000075b279a0a79444000164020e143c7019ee8903a5c04dd068a00000002e50000905a076271a77c484a7e00001d122fb95105d980005f0a28e9f525ec000253a1a500000968000302800066c8eba87900008308000a0f005e00006645411600000000000025da3408000a768000799a6e02eb1dd2a528630a72978c6009560557a8ea97a27aa0002af28808efe7d31a389cc1818a2892d085da1e8a9780004f305fc00011480eb0de6000009ca49800036795fe4ba18f00000368a30276a000241a66603941aba56898e00007f08000a6ba08c49993aa00019023c2058e000000003f8b2c00008227dd00003378420557172e8a316525268be08f300000000cfea3a0000
  | 37 => 0xe9d781f24f92b0a187800000020dca2d8d1c73a0b104e6818a29e95549270000a609b961820f0a07d80000261b9c5eb8a9c7d126a64f9a240978000071c1b309821b706ada06257808580d6a0ac18309d65699bfe09e1c423118514a0508d683680004728ff400015d61e780000002276000265a5ef01a26bc00000001fd000000002c5046a736901006991c28dd9648019a47c6248adc88f96c800020c89519c084ad179061b14b09c4046e7948968188157227b1c689d19a928be220c7b69e8c4bd12a0464a10800f0b7c3ca161263a265e41d85aa55d00ae98b0d863d2973c92222f21f3212e29617c681d000001280000000000000261a198841e2dc0a028e49a9800b166483108522159848863939685f8ece0ef19c036a0d7085896fc7eea1906b3190a867830e9289aea000271a000069c00010b4a762856684258a2d1161e23f2152a089ed67f3aa9e000127049ba08800014106379ace8bc264a0809cba8e0037600029f84f8000000000002d8000000000000002180a3e89124f221b03721f880000b480000000000000000007ee0f2a720724063c000093284680003801d362c000ac8281a0e7102a745c4201a8e0800000000000000dea00000007be80002bc800039325000001c889961274000000063a891452800003da910e4c406464d40f0200009b0094094449d858a1c692b600785d445da7443d5912c7ee056695685e23760000a150000818000000016461a580009c285bea680406abf961a0b70c7677600004a18160131a3d60000064000000012b1cce0001982000000071b1eb60000000000000000004180b0a84c0000daa5fb000027001e0a9c840c77a18a447c090228f1f4a1c88e9a4fd099852d244688d8000000278200016187e88e9010c94d276f24964cd970c00025e659686bc0001aa0450877800000aa39280000002ab400000007bda9984772a68208292a759213e8df188000010ceac7090445c12be5279c7e00011d65a8106e70308ae1342b1a46e158889a0ea2321a3786e123ae9bc88b488180007c9a32a0000e5c4c706d20000f7408c81c093f92eca870ffe7b31d5c4662ac00000000a0ca62297d803a21d09be65e1c5c7028a84122284e57e26fe8ba0b6c42f191c3371e30474a0d05882a8e39ba0a41fb097c0e7022e31612fa8390000a992194000000097f0a986a501d29ab1a060002ad051398d283000000000ef6183a9285b689d49b78000994800015aaaa400000001270d4c487887c7c726269e91bac230800040b03b6631921ca0618728b697b26638000000000000015861938c541970f2e0000d6ca710000a900a640da8000864a06e000000023f97c866501ea3ea023057e80001b180a2000000000029a89c9a75a00023e0092239656b95ce3fa8bbe152000000019dc0000e1e6300000000
  | 38 => 0x38e20a0c1fb04ee0ce0122a5e256e17a015d214c55093462bb016e2ac08a4460034878300000001f52000230874919445820ce60001e9a02a25942190db81a0000e62725161431e2a00024984c8800002283a84b8a22c62c00006ec000002201fc42f8000000123a00000006ac14d400028de3c6941a37e0000000000000012260000ede7930000000000000027844ab058620480000002924000000000000002389b060001b58000000036390560f30f1280ca968101000072c00007310c22a739288a599c46000000080e02f480700000000000406a44423a038c7e7800033e0000a5a864000028e613d8f1e09b000001f14684929c22331111c15280001e8120409f9c80000204c485153c7ef16067a51bc405a92e0408227229218f69d580902609b4c99218ae3c98000000066057697d04b000007c90a863b018b289992a813025300000d7c47b9d0400000001b594ae00015ba00022b009c0f38924a41e31128ba43802461201c5e3039708000236a68e8000000000099380006148700126a7a8685a31249600008499bc05d88c1049721ca2fe80720049afe00000002ef20ea79f00009b213fc41e80001e48cec77b048c55c243c81f1c4c51900007c000000000000000000000010aaa8f80008930000000007a4bc9f16125078a22001c60001c1e8989ec88c6194e646268a5b8a23c88e97ce8e4222a28784928d5800249a86f0a7217ee2bf1d74268a1d66359c4ea2200ce98d00785eb1fd63c92b1294121fc024800031e000a55aa96454c9376652a258177a35860119a8746177a5dd1ecaaa4a7a65b481869ef2ab02b1163c3231738463115e1f79ffa000021c10580702fe00b649588ec4c9800011f1a720ac8000a8d00004e209940000a1a97e1792166a33c4de1a4e3030cac005128c3431f9a66f9d8e40e9a822ee16f074a83825c3a2ec607a054a75a760696000040922922b6801c8bba8a69a5a2fc00000000001b543dc000090f8000000000006aa2d00000ed69db8f88000204016a09cc00000cc2c91c480000b5e21804720000000682853c00017fc1d71a1c680000066013905da800004f9a0c59ba69460016f615c2a8aa5f1db25510ec40000000000149c4b988d803d26fcaba960a17d19d2a4b00000000b680f1800000000000000000236843642280008d51e0010485046342a7664529bc0548bb2000106c404a1369fc099a000272838c9b322550000000000007500007e5000031214b60f589d04a9241800003ec4dc86f87928b202bea5082b3800093300006d900000000c3082d1e5e7b390648f0000023d19bc30da46ea7d05dc580a52c78f226a0dc05b487185f000000006b40fe02c7a8280fa97140000ca4aa228aea3697fa0000d4634f8acc90720240000e3aa8c84b400002ae17b9d3c4639dd6a0d985c5718da
  | 39 => 0xc800018980001c8e0000000000155800001401b99d8644fa25481183e69501aca00022e2979076a7eba57698e8b1895f0fd04c80e628dc240a459993c70c821415514007fd1efe0a19ec286d28aa1f384ba30224a436c1c940d28b4c7a81476095a76669a93565a503fc622857c3589c6024ba3202d4a9705cd20fe2d511244361b0e4a7929821388e49298c809f897a41cd04cc30f286c9d30934259aabc4d90c7a1f714fe32f1434314a24e5b1269287d901c7820a5e74e96cc26d138a298209278401a88c11556428a62a826081c609826e46a1ad219c862e7ac1c1622a28d035703e448213060fc980c77885468e618069fd19a67c684f0559882e07a02346719d5866307040030f2011c0ade4720f8231d00008a800000000e8015ea4be689000000016500001bae807905c16b0ba4796097a1d803089a08ecc80393de9ff88f26221c9c43e96e6a8ea474a90a3da19e1a7a2c0884cac400000002a445151670446a2ac15f88100001a6200003622bc12ce9e42388409a2e054729dca8583dc1840000abb000000010ba32b8ba09dd22c805a22fe705057666aa0ec928047a95080001361f5c4918000a3380000000000038950e0002a3835c8000a91a0e69b180000000342000000078b84260000000000001a70da4ce6c3000042c000040193d400029522671a1e470017a00025aa4b5a34800005d200000006db162a32419cc99a28e000001822e586fa368981c4da03886ce098495f8fc01fd94ee46f852a28393443ed00001f920ee00000c032daacc0001e3e2858b2e6e9157e00006aa0c128460001f4833d997c81200000309d1e0001cb411611d06479ea42460b623fb9bd83ab2440448a4ec00017a67990b806c09b987098ee60659732a2b27789ed090a4100f7202f89ee21285fe5a31b4a726a9620418bf438e2842342227823303a4a47067413f208a70a00008b186fe05e19360002520828973640ca85e0002050000000034989d89268200a701b500001dbe25b1f18896a4ea795941496f9bbe94d955a8c500004d214a82811f9808f01c43f79a2826900006400a566b718b67b1a92e0939b8231000dc6e79ab472aa290a0321464d287b460b8f5a8ad04906cb0c1e95c9f7212996b83010000247a1a646c993a64927ac3c4109200000000d3053a9d3a81c0e612a282f800000024c4388a00c00000109bc03c85a60aa0ac3a4b01e8964c59f17422d296fe00012fe81608542d08ab407fa71e9c5a1bc6b6077ca2120fc3fd96221b8a7f68d72a488139bde00000006482ae0000234c78700000000f8c7e3192626a84785b283aaa46a38c709290e4ca882810d000099b06d01da0568128a6b22020000870a36620600000001466a2d20563578684ac5166000025c28f501c200016c0000038e26c9d84ac094dc64e162686802a06f
  | 40 => 0x18226629edc60b29fea370cb8962216e53291846f7183a87b0000aa09eec000089c67d974e4bb8d848de800096480000001cfc42a23fc000174672905c04760f7e1579eea000000000015d024e0db200017404788d664d72a90923800059f8000585a7767d413c614d833400013b001d800054ba948919996a7f60e0c39020ca496968014d0f606a780000001f38000243a2d616dc852a1300c98000261a73c548a60209729cc000000000000000000d8c00007d40000000000113800022bc0000ae48c78c942c1a6601e59b6a35393342f79b90aa817d81851f6c9bd00004d78ee032c0db69f38c5c0db0eb00ad9676a0116d83f492bc54500ba329946e35a918291e8b2a568900891e243434d2672a950c1870ea73a67080005be27d20011eaa3341dcc3f218bc432855648410a628a0eec35e86f66cd1ac86a39bd67ff8cc06e31b400001bf891918440000abc5c2a014a641afc1fd11de33900006a40000193288218a8a682e09f567c7836462a183c2ca274a805a1641508e7649ea55e5f80f6c309833650e12f855b98708f91e8e2f2a7043f9213400026fa20100000320e78000097e00f8000719800064c28381041f58097819495e0dba4cc8000665894800000000000cfa8512178a4d212c93f00000c8180835a27b60000000715268e4318c6e5789e2c0d000001fcaa0807887f0a829d163840a6a64f9dda3461dac000063857b07fa000067093d000028d00002aa0000a4191fa61e8000a3d86c201a096ea44063a2299ed44e514463bf159e2baa4f27be236e542258685d2ac86da24766aa0bae2e480004df800048c29f6000000000005827af976098609304900dc0a7a000080f9a8c41f8bc627a96a4ab68a5022d9d0c30c8c5a41e0a5a7c2876c1db8c6a9e6082c8ee966813e0a5c35680004b18a6c0468caa3938c6806b8a961af952638987164719bd41d309fa000115a0000000a1703463d116b4a1900000001046021201246a99ac4c0800011d828207e000004b8ed023800001d100000000f462038c7c45a80006299c1c00000003738e04280044c40629b278812785c125a00001b1a0000000000000000024ee46185fa06b00000fb95be00023e28d880006310000802a5841cf00008eda1426940f7c4c51e2400015b218d920a11d186e92780007c21d883208cb48a50f6432123168ed165c3c71e889caa3a8000279e0001dc8453199a0a60b464868000000000016f0fd613789f06ae8000000015e8d8168a51d00005c18c284b71682026906600000001f6916ea019d820001da2494800000000009cf8000000000020325cc000000087793b200000003f6a72200012c213280000002a96281a9029e598a2000156c06601faa4307460db9cac26b8fd4a46077a1aa24b605d25b264d098c234a1324a2a1f03b2aa0246987
  | 41 => 0x260000125479ea8b20cc2b00859a7367160f6296e999e5e39f865b1849840c1b44a50a1f835906524ef1e469309efc14e083c437a88e76e139e0000e2c0000cc64390000210270848f1ba855e24e89b4197a69d9e6a0329d724460c9a067138ea6aa7c28fca2de5c7a4ac89ba9b47f190f09f421fa2c99ad600026ec97aa4209140466000287c70f099029d13b6800a2867671ac0000015489100002f423721a3a468641000031428b04c01bb86432afc9d892ea2bd9482479a2ca326000020c9e6c31329ec53219e0a2480005d700fa379245a9b08e3c6968bcc336834e878287a8e6a112630a650a0802582e3221a28e005200009c27b8800041699ce60387ca98928be8b38424623995034680002da879888c85d800008843fb1f688c38f8e83d87125232a0665da1ba0f405e60ee0e249ba965e61526547fd96ea2890f3219f80006db80005668bd878d80006ec80002cd19748f600000000efa00019d019a0946755963e0000ef846f08be3280a6e5e798569f6283e23121f45c904aa039914a2a08ed4000189027214322b29a8825000007c4100a6aa99669b3a32c45f1bb69af1a86a57a8786f6842200019880c500003e89d7029f9798000125053990b895117e46dfa2c0493a1145da1b9a3dba9124fe884244a22cc22f092687a8d4a00016323ad1d501e11da86ea80e4413aa4a75a8000a2525b00b819f04c61c8616c213c8b09bea3cf800027c855257103a600001b28a210a0a1117500e0000085200e801aa8ec6f81e508b1023a15e19a073c8f984d4987e35602721eda7587e41e629470ac63d4030c9548d94939959827d99ba300914656707ac53e091608d8a08941a248a2597547a18cce91c9d542ac82649b899ca7b78a529a303cea7c2852478247e3a9a9e28fba1b694c93c230001365248ff286c903e1671b8643e15128a129b88fb127e47a1ce288921ee57d031a2db8454521000066180000001de09229a9a000000042b9ac4a411876a958d7e77e04ec78621602d58b4e77d1896628055092e0000498800000000000000a2c0a1000075fa9b634f007400009ce35407d689fa08200007029871a7c6f8a9be0fe99a49178ee44db17880842938888251a0401b1477080003aa976407c00007aa204a9fb80000000000853854459ea6a237b89ba4f1030aa60123204923366f3194800020087bc00000000b5a2e41d6074296e4000141c196800071b8d8a64b1dc4438812600017221c7a33267e981a7ec8a12854245c0000b5c69f87d83e0066c8500ae045607e63e2a1244790d566921e1252519c483606ea00016780001cdc7441340000000083300000380000000064850a263e63e1168619000019d90ee1482aa29ac010a00000003819d483ea80005cc01668c280006169dae02d1d7a40013603c025741390000a511e600
  | 42 => 0x9f1d6281b15204348de80000000000123474209e40b38000299814a00025ce0000456000239e000000021ca6a80000da4000000077c87c20002514146800034000005f681d01a48000a8aa56a75b83127328b7e00021dc3d7838465a23262850c604f70bb63ef98d808a0ba68fe8d0a522271ca0387aa72812806e01b78a21a4b47c381768382ab8a428114a4580188388a924189fa020fa64462a8b0e6928bb484380004b200002431ae0000104c60d08502570e0a34b24c800015186ab9b52882250e88384f282e0bce848061c5332a12434173a005909806010348aca82e330aa66a5d83b02fc964a156928288498200d4133e48880005950ff800027c800000009539fa800009502c31be4000207808300009c900004b78000000283a8171ed00891f7000013f2000000000000000000b3a186a96e75313708f2229c4da808c25583182cd86cc71d15b057d802654289e055185b235d241215307ba6fd257024a9aa25ab82268110000000000086f9e02777905274b8b7408181beab7215a96f06887ab10f45a19a148b700006ce80004e8a11e9cba29e190957c047a06639d194250584860000ea86bca1c40000e70a2a0e28545a16882394da6d89c647ca874e53d95b600009b61f10dd4a6591047d81dfe8eb279222199e4604a63c677843e00000001941da6a2f14c43ca93049989db6646aa5c46584be38f8a0cab7a6a073012ba4ae154e82a940867a2486000124c35e00006370000343800040e143082d80000000c3a61393926cd800000020c654c0000000148e7001ed259980006129ade0001cb6000062806f1aee0a400003d21e80a5b1b5600000001ce26c495887064dbaaf646c2b22000141892084841d42a305d6a7326bb1f6e000069eac80b9e00000006ca8108937a456000094e52e10fe30b1c7c5ca0000000037c0000dd625c15381cf94ec0001b6000015f273b000000000008e18cc800000002e202aa8a680000000cf200006e068f8f587770826724aad82c120a83a916e845802bc00000001ee24840af9b7ca420cf46d1a91470616ee53411f223221f21a814b29b614789cb050818495c2596050a1e507e01978686323a6da1d880000d8069a22c04dcaa300005af903c3b89b481c3123837c91da22e9fcc420869899d0ed2a0d21c84542714a5800000e5aa7e8440f0c6549aa40001090827aa586ef0000a838f7a00000000001be80001bba52e884454da4fa327989a0000000686147217115f0148a88a6c61c627e016560c784ea43f1f8e54f8abe9f598e20001bb4ac1800062e00001ca800020d000056f00007da9582453800000022e4512220a399000082028c4464206a522a28a14b9dba598956491a81cc93d99c844802f217e10940d4a52e2420c2a33c151a3eb822c0910d9c4cc215e98c1fe879b95c09c48
  | 43 => 0x9b926c725fe118a20080188f00f00446ab287e27230eae8878e8a481814687306349a701380b317a83bc80007f2123e948a3309301840a4f0dc27d0213a6e8147079c9bfaabc255c4ce18ca11680005ea98165158aaa03b8bfe98825b4146106a7a5a8c67b00eea53a172a86a01de4e027ae00007d26b50f2c01327529d500000018000000000099e0000436865400000000000000000079000006da50b268600000000a91c780119d940ae09e6a168c2e0f68764000191638581b44fa9c0e0000756090a70200017cc1419cd05318ffa64aa6f84549dc08b50000147972c0b500d4044000000009fc00000002f6a8761ad80008752a2011fa1c0420217a93c140e98ca1a2000256e2b5000000021a4a798000232a64667d06ee6d7088e4e9881a44208660b7a8167d792b037b00ec72f0000a2e2a700b405a2549276819f29583069f2e675a1869c19f28639a1e288c227086706c899007861d0899eaa6a6a4009075a0558ce85871d4634e0a408efa35e5aa943a24700005eeaaae8658bc40000000a4800000000000a1a092200000006f211060000000147261621c04c8000000000004e89a217d67f000000000f901c703d29718000000222e7299f7aab390881021044181000089f18da0f5291e3ac95e8328996e02f0252000178244080000001d0222096100508fc23770d763640184468898e0001552012096034c8f1451f911612b89a6a04938400008947df21cea9b2ab61a326e400028ca7ef80000000080a268d204f38afe7aba8d879c219849a0f6600000002c68b0a01fa4d80259b8a5289af8000000036580005dc85323ce8b08801138262d070e0b99a743f28da62769b740b9075414c085e0a48000881000057aaa109729e400001c8277c06160e292f699701342f585e00fa117400024bc53906183cf0ee866885eaa671cd89ab8a8000013420002100700845210a26aa000221475105ba74399584e300000001a446c5895e6ab1d687f28ba8a2787d0000056040a24260929f3e00018f481922a277d800049793ae9e011cc39e800030f98e056282167d5000000000007488000748074060a2a5a0002670aa500008cf894c00001923e69c208b6085c98da1720000b6439f25d899d99460000a4a8e29d288ab93a0000023e3601c5280a8000676a40669900003a1000079f800036fa15600020363d7232800001ce49f000094400f800007ae95b132e00016245fa80002dca6d600005d000027c01ae16b69efa642000056c084a6e600da8022f5265614388a25141ccc0ec8e36000000000d255600000ea21ea82425c8a464df2a148098e5476c277e2f7000000009b800028f80001ebc00019ea94a000005f80002ee80000d72932000242c73820b2000212a00003f053380007fca02841ca7ba62e98d45a78000967800099e97c0
  | 44 => 0x1708c4078e68d800060daa9800025faaaa810e0538fb62ad871426222742e18dcc75f293a2cfa3a63941696000000090a8000000000000003e23e5800097c203c000222825d80005e0000046ea53c0000d2ea550992000000069826800ba800066d00320000622aa185b89842aa89a606ba8089f64ab10b220a591a4514839e63e8d1059b292262f80005fe1ab24308e1a4120836947815c00023a428aa35017c922c0001cd261622f60cc800032e968e75d98ee1b6019e28d856496b02a60000df431f9d923668ae621183c43de0158000000011a0f1624f000092e884800010c43c18000000166a71aa94010aa99a000000083ca77025605946c01bf68ce8b9883529e01ef9e84a6908b276787244f614ac2b41dea7e11a6c4a70770a7528fc2f49e0e572009e4c394207b612609691398804246c1cc17967dda2562228b1c17d859e6a00aa21e684960900f942729dc667fa07e56b1d342a29984827022a82b9af440310027f882a8041094a00005ec000029ca4015ca74e02e272617b62cca16c00004c4912a81e9b2a4240001e44222105864b8344782a7e88f180007c80000abe878c4258000a7e800063b2068ab9000000022b60000000a1295dc38ba0207c4a25c3a324aa0bc20f000011b63dd82d200013da423a1188940b76889aa00789924468084fa6afaa22968a6ee89487b00799cfe140a306963935a915140c96d9d008411594000258c4ff94a660c80002cc14bc455800063f2a26000218448397121588be405c8c4250f917a6029a2e4b122984fa00b24aaa7da7f1224a3b699b0a35995c37f259813d2344959a5de9c61a269f9856e516a24270ba0d604480948e7140697489de72a00001d600000001d900000b9c0001164218a9d06e51a2c0002986000147c8aa819033f1460916039a8ce096200023f62a2000042304648c086a400018382f220de9ad17d20de20521f019063d38e1819980008c028c24650000a23140a49b109a000003800013540000ad80000fb867f1810455238ea891dca3449bfc0ffa0869089cb2a5403728a9867a0000056688806e0000000397a6844ab80000000000169a2f468819ae8211d98000000085f0e885de00000000000000130c826a10a5c99b5a37c000084580002cf22b8271109c9e8190e1d4800073c13589a7a93e8488e46a7b8ac00f61ae636d12a63f9800009e81a40020928684931a49ca7881ce914479096928241f7e6e99846396162845c98ccab50596a81046c3cc0eb64c29dee029105023384027d6872834122a84fd824c6f19cee34e933c2a5000054a00001790a10517000093917764291aa69f780de43004a46f403009341d3e0d79eb4341a34ea0423de51e8c563228000aaf89100ab0e2a6e898145d6018e6339590368278c1ef139c7158aa439a99409a685007a4
  | 45 => 0x99daa6cf8c4e32ca2108aea80065b02660409e1a5fc9ce6887184c47b26b640526d454014263bc0ac20298b160ce11ae73203a06fb800049914f0000237458e08907f982c453587f88a08000200a2e655e9d1479d1f14000112613b813c1a097701660fdc466995a9561824a56949858b2a7a7ed8000abb96fa0fd802043d860243213ca4b48e14575013a8da27f841c1086568141e8551a04785252a4fb9bf0205266a291182a1f19e0478585b611724dc3710a9a4b9128e3b083f49fb14c264c95e634a86de160232e75682b424da4007fc0bc047a8d8235506fc7bca19a2e28bc25f52aba6ae281a228142e9ec9ca246b01e45388c4a5161e5a5e11e900d9a9fc45b173e8a01d80000186aa16152c47f9f363521e1e13680006a599125ed19f25d2131e00b8f8651b20ba0b685ae3b207823999004317aa3695920d293e08969ff00f6145a794345a8fe6d79d2653a83de4fe0c649e29f8aa4c00d2196146247516bc00007485c680007d8985030e13ac00007a825480006f289f40000d404fb218256aa3527cd0e60a6210e880605261df8f9e690052c0208be844329f2a9e164423a90b22261dd000025d48f98e523ec97ca07d16844a510f2334833e1c60000000000082c102200000000218dda5e51a8a0000a0a04b0d980ca9fe45ee23a0202ab0466e0fb055223b0191242870400005b40ccc8e88e728d0844a34c1e482ff00000000ebc000000045f87e8010078052a91fc8e1254a4f586dc3c60a8c44f00620002994000000000029d244e80002058000a0202c0981000000c00000bb1b889e180440001e5c00000008ff832e083a03469198626c49fa62d4011856a0f401dd177e8861200000000000014124429ffc9720000874176e7f4994c5ae9c8a10ea4ae262a6d20f8230c00020420000c963da264c83d24387c8a18804709243d489bc38208926b0895a84323404039562564a95684e1e222871da0a9a950c10f1dfc67b80d000a86a6a1c8d9271da5b886b1e4e9ec211c1c221020bea98c60c1e3409527b87e701d69d92a802a7a54824b00000151de690ba02c0a88374a53890e10b80000c914a4a989d1c4f4031c2899c5a04584388be91c44859fdc639042caa1090641513a4618142a33a8dbc85c25802a40c9279e08d42481d3093524302ce174412a09640000a3a1039f2c40ba7cc6c812204ef9a5ea68aaac78c94f20000000553145ea8baa1aab1a60c45880000001236a719a1a7b108c6000066a00006265c720000001b081d794904c215a47e9017c0b617f6a140e7e79a06249fc80006f4800053f05246c413f052016de89eaa0c0cf28f068f088c08227347f79c041bd2ac25c8037e22aa98a91227481a4040aac59c382ae80d644c25f44a5922e93823220000edc94d2870110958c9498dd268c96d648619923fc000
  | 46 => 0x27c487f975e0000fd8abe000072f86b400019ec9dc8ef423980006cb800069500000bf2a4c000164ea8a0c240ac24b25790ba200018680c58cd6000101e29d8000a3c9afa26a054e07720946442096863000000000008fc14c024003f854a9ac63909580a330e3021b1fea3a48122490969c22785ca4cea1da25a9422051250232a234600884308991d1a9fa996461f17be0000c143e9819a387188c3cd1e3a21b95ee71e8cee00000009671f4600022d200004407bd1c729990dfa6bd988400000002888a720000a4c620a3f8000236c6fb0d6e5bd174c72589e25ff95cc67997e6100065615013e2714168843a996200000007528f4c000000098b96365e719d40ed00f29a4250a1e9a7fa2d00a7000a045e12395de43513a81ac18ac2de80004a1299200000007b819b60139f302fd8a2019b883a9741f32aa983907eb23ea00006328169a6e3bb906861789ac5fc1ee64de8a62876250c4628b7873ea6c05bc97e8abd11007ae82f678189780d5969a3ff0af80ce971896094be8c681a000014409aea2be483000000005da5409e8a56d000043b13125638e86965812860fa5240480e347c182c81281f4e21a8b6642b02749829a7058b815a7d08e447f803ba7ac844472785109d088ee22e1da457600005c00e129d724c612c0ddea5fa7e42bd0000aa712d41828a307ea8d1e4809dd4000148688d2a5200007a44bf07b2966a750444a480a2823c26b68e5600005d69009ae440aa95c000243600004bc68aa5d66dca54c72e26be74c93ba000020a7738000590a4624b6835432fa16a03c06d4a1fa79c90115343ae0e687c10c2044d93b41c29a42a201e98237a7dc70f9b0a44ba80a87
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xacc8358862440010ff08ba8c4880030fa1574189100061ec2ae8312200ecaf205d062440050ff0faa0c4880021f61f541891000e1f3a6a83122000c3d74d5062441358bce7aa0c4882671d5c754189104c63cb86a8312200087f8755062440010fb0eaa0c4880070f9d154189100061eba2a83122097c5e73550624412d8eae2aa0c4882571e5c154189100062faa2e63122000c5d545cc624401d99904b98c48803b33c8573189100746f41ced992200eacc8258f324400159b06316648800e3e21970cc9100247a432e319220038f8865c232440010ff0abb2648800a1f215764c9100045fc22ec99220018bc845d932440011ef02bb2648800a1fa14764c9100043ec28ec992200e8dc8758d324401d59904b1a64880021fe15760c9100143e42aec19220008bf845d8324400317908bb064880023761f630c9100247a432e219220038f8865c0324401d9d0c4b8064880ee3761f63cc5103f6b8086ea90a2000ccc73d89214400159b063124288003331cc62485100063a3a8ec90a2000c7476dd521440019a8edb9a4288003351d87348510006aa3a8e690a2000bc58318921440015c90c99242880035cdd470485100043fc2aec982200287c855d9304400117f08bb260880062f211764c11000477c12ec982200e8ec825d930440d58f0edbaa60881a32e1db744c110005acc28c69822000b5985cc93044001ae6ea38a60880036c1d0714c110006f1b94429822000fc13248530440095e10c90c40880021fe1576481100143e42aec90220008bf845d9204400317908bb2408800237e0d764811003c6e41aec9022055d7010dd5204400155b0831240880123da1b71481100063c3a8ec9022000cb8741d920440018f0edbaa40880032e1db744811001c7c432e69022000ba9841892044001ae6ea38a408800f3c1da214811002578432429022003cf076485204401ddc0c490a408800a1fa1f7558c100043ec26eab18206987e871d563040010ff0aba2c60800a1f2157458c100043f43ea8b18200287c87d5163040010fd0eaa2c6080021f21d5458c100162e3aca6b1820048dc8754d63040091b90ea1ac6080070f9d154988100061eba2a93102000e2d5450a62040050fd0fbaac4080021f61375588102ac3f438eab102000a3d841d562040010ff0aba2c40800a1f21574588100247c402e8b10200087e87d5162040050f90faa2c4080021fa1d54588100043e43aa8b102001c3e74551620400187ae8aa2c40800b1b1d652588100247643aa4b1020048ec875096204001c5aa8a12c40801f1798d75cc8100062ebaac7990200ec6e625d6320401d95cc4ba464080031b5d5628c81000656ba2c5190200087f855d932040050f90abb2640800e3d205764c8100246e43ac699020048ec8758932040010ff0abb0640800a1f215760c810
  | 1 => 0x501bb265080123721d634ca1007566412c6994203bcd47158d32840018eccbb8a65080131e9c1650ca100063cb2ae01942007cda635c0328400f9b4c6b8663080021f61b754c6104562f31eea98c208a87e8759531841370f90eb2a630800317dd5634c6100062e3aac698c2000cd963dc131840010fb0dbaa43080021f21d65486100046ec36e690c2000c5e65dcd21840018bacbb9a43080023761873486100062f328e690c2000c5d651cd21840011bd0f31a430800317dd663486100062e3acc690c20008dc8758d21840018beeab1a4308003171d563486100256c41eec984206ae5a63dd530840d1d34c7ba26108002d6617324c2100056dc3264984203bbd0814c93084001970e9bb2410800e7c20573482100247ac0eebb1a200087f855cb63440050f90ab96c6880021f6137558d100045fc22eab1a20018bc845d563440011df04baac68803a3b2097558d100061fbaee8b1a2000c3c75dd1634400187f0bba2c6880030f2177458d100043fc2ae8b1a200287c855d163440011df04ba2c68803a3b2097458d100061fba8e8b1a2000c3c751d163440010fd0faa2c68800a1f21f5458d100061fba6a8b1a2001c3c74d5163440010fd0eaa2c6880021f21d5458d100061fba2a8b1a2001c3c7455163440018deebb92c6880031b1d77258d1000657ba6e4b1a2000cac74dc963440018dea9b92c6880031b5537258d1000637ba8e4b1a2000c6c751c9634400195ee8392c6880032b1d07258d1000667b98e4b1a2000c6f541c963440018daa8392c688003338c47258d1000666188e4b1a20048dd83dc563440019c8e5b8ac68800237e1d6318d1000566412c631a2000c3f745536244003878e8aa6c4880021fe1573d89100143e42ae7b1220008bf845cf624400317908b9ec4880070f9d154989100061eba2a9312200087f855c662440050f90ab8cc48800237e0d719891003c6e41ae3312200087f855c262440050f90ab84c4880022fe11709891000c5e422e1312200087d84dd5624400117f08baac4880062f21175589100046fc1aeab1220078dc835d5624400187eebba2c4880030f1d774589100061fc2ee8b122000c3c85dd162440010ff0aba2c48800a1f21574589100046fc1ae8b1220078dc835d162440011f700ba2c4880030fdd474589100061e3a8e8b12200087e87d5162440050f90faa2c4880030fdd3545891000e1e3a6a8b12209ac5c73d5162440010fd0eaa2c4880021f21d54589100061fba2a8b122001c3c74551624412f8b8e6aa2c48800317dd773589100062e3aee6b122000c9f74dcd6244001938e9b9ac48800317d5373589100062eaa6e6b122000c5f751cd62440018b8ea39ac48800327dd073589100064e3a0e6b122000ccc73dc962440019a8e7b8ac4880032e1d3705891000477c3ac43122000
  | 2 => 0x243596100043f43886b2c200087d8710d65840018dee5392cb080129ea0272596104ed3cc04e4b2c2000a3e841c9658400147b08392cb080021fa1f42596100043ec3e84b2c2000c3d74d09658400187ae8a12cb080021fa1c42596100043ec3884b2c209ca7b805c565840010fd0fa0acb080021f61f41596100061eba682b2c2000c3d745056584133cb4e1aa4c70826b965c35498e104b52ec2ca931c2000e1f549526384001c3f08aa4c70825f879d15498e104bf0eba2a931c2096e5a70552638412fcb2e0aa4c70825b879015498e104b70e202a931c2099a5e85152638400153d08294c708002a76105298e100052f42e8531c2000a5d85d0a6384001c3aa9a14c708003875514298e100052f4288531c2000a5d8510a63840014bd0ba0cc708002976174198e100070eaa68331c2000e1d54506638400187ee8aa2c7080070f1d15458e100246f43ea6b1c2000c5f75d4d63840058bceb29ac7080123721d5358e100246f43e86b1c2000a5e85d0d63840014bb0ba1ac7080123721d4358e100052f42886b1c2000a5d8510d63840050fd0bb92c7080021f6177258e100062fbaceab1c2000a9e849d5638400153b093aac70800297a167458e100052ec2ce8b1c2000a5e851d163840014bb0a3a2c70825a976165458e100070faa4a8b1c2000e1f845516384001c3ee8aa2c708003871d15458e104b70f202a8b1c2096e1c4055163841334bd0a2a2c70800297a177258e100052ec2ee4b1c2000a5e859c963840014bb0b392c708002a7a127258e100054ec24e4b1c2004ada809c963840015af02b92c708003335c87258e100054f420a4b1c2000a9d8414963840095b500292c708002b66005258e100052f42e84b1c2000a5d85d096384001c3aa9a12c708003875514258e100052f42884b1c2000a5d8510963840095b500212c708002b66004258e100052fc2ae2b1c2000a5c855c5638400153f08b8ac708002a72117158e1000567c12e2b1c2000acc825c56384077caca3a8ac70800297a174158e100052ec2e82b1c2000e1d54d056384001c3aa8a0ac7082671e9c35498a1000e1f3a2a93142000c3d74552628412d8f4e0aa4c5080038b5514298a100061fba2a8b142001c3c7455162840050fd0bb9ac5080021f6177358a100247643a84b142000e2d5450962840050fd0abb665080021fe1975cca1003e2f31aeb994200087f8759732840010fb0eb2e6508003179d563cca100062ebaac79942007cda635c332840050fd0abb465080021fe19758ca104a62f31aeb194200087f8759632840010fb0eb2c65080030f9d1658ca100061f32ae91942000c3d655d2328412793cc6ba4650801237e1d638ca100062f3aac71942000c5d7558e328400193ce8b1c6508003275d1638ca100066cb1ae119420048dc83dd932840091f
  | 3 => 0x2900400eee2325852008001dc264b0a40102561f61e74597100061fba4e8b2e2003a76819d165c414d4eb033a2cb880030fe1174597104c43f438e8b2e2000c5f739cd65c414b4ef02b9acb8800e9d20573597100043f43e86b2e200087d87d0d65c40010fd0e21acb880021f61c435971001d3b40ce4b2e20a4a75819c965c400147d08392cb880028f61072597100043f43e84b2e200087d87d0965c400187ae9a12cb880030f5d142597100043f43884b2e200087d8710965c41474ef02b82cb880021fa1f40597100043ec3e80b2e2000c3f759d564c412b47b0f3aac9880030fe1d75593104ae1fb8aeab262095c3d715d564c400187ce0baac9880030f1c175593104c51f428eab262000a3e85dcd64c400147b0bb9ac9880028fa1473593100051ec28e6b262000e1f5394d64c400147d0bb92c9880028f61772593100061ebaee4b262003ab6819c964c409956b03392c9880030f5d572593100055dc02e4b26204eab8805c964c400147d0a392c9880028f614725931000656b90e4b2620008be8714964c400117b0e292c98828aade0570593100045f43ea0b2620008bd87d4164c40091e902baac78800a1fa177258f100043ec2ee4b1e2099c7671d5262c400387ce8aa4c5880030f5d15498b104b63b38aa93162001c3e7455162c400187ae8aa2c58800a1fa177358b100043ec2ee6b1620018be84dcd62c400117b09b9ac58800a1fa1576ccb100043fc32eb9962000c3e645d732c40010ff0eb2e65880021f61d65ccb100061f3aac99962000c3d7559332c40050fd0abb465880062fa11768cb100043fc32eb1962000c3e645d632c40010ff0eb2c65880021f61d658cb100061f3a2cb19620008bf865d232c400187ccaba465880030f595748cb100045fc3ac919620008bd8759232c400187ceab2465880030f5d5648cb1001c6e43ac699620038ec8758932c40078ece2b28658800f2d9c5640cb100063ab2ae21962000cb5645c432c40019aeec39a4388003551d473487100043ec36ea9862000c3e64dd530c40d50fd0eb2a61882861f21d654c3100061e3a2ca98620008bd86dd130c400187ccbba261880030f597744c3103445f43ac898620a08bc8759130c400187eeab2261880030f1d5644c3100043ec36ea9062000c3e64dd520c40010f90eb2a41880030f1d165483100045ec36e89062000c3e65dd120c400187acbba241880022f21d64483100061fbaac89062000c3c7559120c412d0fb0f3a2cb080030fdd274596104fd3dc02e8b2c2004a78805d1658400187f08ba2cb080031ee0174596104b63c402e8b2c2096c3e405d1658412d87880ba2cb082661fa1c74596100061eba0e8b2c2000c5f739cd65840094f50139acb0827a9e60273596100043f43e86b2c200087d87d0d65840094f50121acb080029e60
  | 4 => 0x10800156d0839ac210002ad610735842007573410e6b084004af2801cd6108001caea729ac2100029da1743584200053ac2e86b084004af28090d61080015e30121ac2100029da1443584200053ac2886b08400ee6652d4961080014ed0ba12c2100029d61742584200071aaa684b084000e355450961080014ed0b992c2100029d61732584200776219264b08400287c85dd931080091b907bb262100021fe15764c4200143e42aec988400087d86dd5310800187cc9baa621022b1798f754c42044e3b30eea988400087e8759531080010f90eb2a62100030fdd5644c4200061e3aac8988400ecac7259131080018beeab1a6210003171d5634c42000656b26e49884000ccd63dc931080018eeeab0a62100031d1d5614c42000673b92c2988400287e855d8310800317d08bb062100123760d760c42001c76c12ec18840038f9805d831080010ff0cba862100030f991750c42003e2f31aea1884003c76615d431080010ff0eb2862100021f61d650c4200061f3a2ca188400ec6e7259431080098f4e0b2862100022fe19740c4200061f32ae81884000c3d655d0310800f93cc6ba0621000f2d985740c4200045fc3ac818840008bd87590310800187ceab2062100030f5d5640c42007657392c81884004cba7059031080018bceab186210003175d5630c4200064f3a2c61884000c9d7458c310801d99ce4b186210013369c1630c4200063732ae41884000c6d655c8310800195cc8b9062100032b591720c42003e6731ae41884000ccd635c831080079ccc2b9062100031d9d5610c4200063abaac21884000cb674584310800196ae8b08621003b399c9610c42000672b92c21884004cf27058431080018f4cab8062100031e595700c4200065d322e01884000cb9645c0310800f9b4c6b8062100033658d700c42001e7930ae01884000cf1615c031080091eb02bb4421000a1f21776484200247a40eec908402387d86dd5210800187cc9baa42101fb1d98775484200043f43aca908401087c87595210800187eeab2242100030f1d564484200062f32ee69084000c5d65dcd210800193cc9b9a42100032759373484203ce6b30ee69084000c5e651cd21080018baca39a42100032799073484200064eb20e6908407dcd6611cd21080011bd0f31a421001e3721e63484200062fbacc69084000c5c7598d21080011bd0eb1a42100023721d63484200062fbaac69084000c5c7558d21080018f0ebbb240100032e1d376480200063dc2eec9004000c7885dd9200800197709bb240100032e21376480200063daa6ec9004000c7954dd920080018f6edbaa40100032eddb744802000739baac29004000e70755852008001d66e8b0a4010003ac1d1614802000739aa2c29004000e71545852008009dc6e4b0a401003bb8949614802000770a92c
  | 5 => 0x28f61771590200061ebaee2b204000c3d755c5640814f57700b8ac810012ae20171590200051f428e2b204000a3d851c5640800117d0e28ac8100022f61c51590204b52ec2ca93184000e1f549526308001c3f08aa4c61025b879015498c204b70e202a93184099a5e8515263080014bd0ba14c610002976174298c200070eaa6853184000e1d5450a630800153d0828cc610002a76105198c200052f42e833184000a5d85d066308001c3aa9a0cc610003875514198c200052f428833184000a5d8510663080091bd0fa9ac61000317dd75358c200162f3aca6b1840048dc8754d63080091bd0fa1ac61000297a174358c200052ec2e86b1840048dc8750d63080014bd0a21ac610002976144358c200062fbaceab184000a5e859d163080014bb0b3a2c61000297a147458c200052ec28e8b184096a5d859516308001c3ea92a2c61000387e115458c204b70f202a8b184096e1c4055163081334bd0a2a2c61003b9394b5258c200052f42e84b184000a5d85d096308001c3aa9a12c610003875514258c200052fc2ae2b184000a5c855c5630801d59904b8ac61000297a147158c200052ec28e2b184000a9e841c5630800153b0838ac61003ab3a087158c200256d400e2b184000a9e84145630800153b0828ac61000297a174158c200052ec2e82b184000e1d54d056308001c3aa8a0ac61000297a144158c200052ec2882b18400287e855db320806d0ff0cbae64100030f99175cc82003e2f31aeb990401087f8759732080010fb0eb2e64100030f9d564cc8200061ebaac99904000c5e7558f32080018baeab1e641003ba30c9644c82007566412c69904000e37549526108001c6f08aa4c2102578d9d154984204af1aba2a93084096e3640552610812dc6880aa4c21000395d4e53984200053b42e873084000a7585d0e61080014ed0a21cc2100029d61443984200053b42e853084000a7585d0a6108001c6aa9a14c2100038d55142984200053b42e653084000a7585cca610800387ce8aa2c2100030f5d154584200247b43ea2b0840048f487545610800156d0828ac210002ad61051584200247b43e82b084000a7685d0561080014eb0ba0ac2100038d55341584200247a43a82b084000e355450561080095e100a0ac2100029da1441584200053ac2882b084000ab6841d5610800156b083aac2100029da1674584200053ac2ce8b084000af3805d161080095e100ba2c2100029da1474584200053ac28e8b084099e7220d516108001c6ea92a2c210002bce01545842002578402a8b084000e37845516108001c6ce8aa2c2100038d5d1545842000739c02a8b084096e7080551610812dc6c80aa2c21025b8d10154584204b739102a8b084000a77855cd61080014e90ab9ac21003ab920973584200053b428e6b084000a75851cd6
  | 6 => 0x61fb2ae818a4000c3c655d0314800117f0fb2062900022f61f640c5200061f3aec818a4000c3d75d9031480a9974e1b2062900031bd96720c5200063632ce418a4000caf649c83148001958c939062900031bd95720c5200063632ae418a4000caf645c83148001958c8b90629000333d8d720c52003e6631ae418a4000ce572d8431480018f6cab8062900031e195700c5200065db22e018a4000cb8645c031480019b6c6b8062900033cd85700c52001c7cc04ed90a40ac87e86dd52148001878c9baa42902ae1fa1f65485200061fbaec890a4000c3c75d9121480018becbb9a42900031719773485200064fb26e690a4000c9c64dcd21480018beca39a42900031719473485200064fb20e690a4000c9c641cd21480fb9a8c239a4290003351cf61485200065c326e090a400287c859d82148003179093b042900123e20276085201043e432ea10a4000c3c645d421480010ff0fb28429004e1f61f65085200061f3a6ca10a4055c7a70d94214803f1790cba042900030fd9574085200061e32ae810a40008bf87d90214802517b0fb2042900030f9d764085200061ebaec810a4054cba70d9021480018becb39842900031719673085200064fb24e610a4000c9c649cc21480018becab9842900031719573085200064fb22e610a4000c9c645cc214800135b09396609001f3318d72cc1200043fc2aec982400287c855d9304800117f08bb260900062f211764c1200043f436ea9824000c3c64dd530480d3ad041baa60902861fa1f654c1203543e43eca9824000c3c74d95304800117d0dba260900030fd97744c1200061e32ee898240a08be87d9130480d11790fb2260900030fdd7644c1200061e3aec89824055c7a76d9720480a9974edb26409025a1f61e74594200061fba4e8b2840aaa7b805d165080094f100ba2ca100030fe1174594200063dc02e8b284096c78805d1650812d87c80ba2ca1025b0f10174594204cc3f438e8b284000c5f739cd65080010fd0fa1aca100021f61f43594200253d40486b284000a798090d65080010fd0e21aca100021f61c43594200843f43e84b28400087d87d09650800147d0838aca100028f61071594200043f43e82b28400087d87d05650800187ae9a0aca100030f5d141594200043f43882b28400087d87105650800187eeb3aac81025a8f61e75590204cf17904eab204099e2d209d5640815357700baac810012ae20175590200061fc3aeab204000c3f725d5640800187ae4baac8100038ee0175590204b71c402eab204096c3e705d5640812d878e0baac81025b8bc8175590204b716902eab204099a3e851d5640800147d0bb9ac8100028f61773590200255d404e6b2040a8ab9809cd640800147d0a39ac8100028f61473590200070fa9ca6b20400ee2e52d49640800147d0bb8ac81
  | 7 => 0x7765dc563480018e8cbb8ac6900032dd937158d200065a326e2b1a4000c77651c563480018e8ca38ac6900032dd907158d200065a320e2b1a400087d84dd5634800117f08baac6900062f2117558d200047bc0aeab1a40038f4815d5634800187eebba2c6900030f1d77458d200061fc2ee8b1a4000c3c85dd163480010ff0aba2c69000a1f2157458d200047bc0ae8b1a40038f4815d1634800187eea3a2c6900030f1d47458d200043f43ea8b1a400287c87d51634800187ee9aa2c6900070f1d35458d204c63a38ea8b1a400087e8755163480010f90eaa2c6900030fdd15458d2000e1e3a2a8b1a4095c747155163480018eeebb8ac6900031d1d77158d200065bba6e2b1a4000cb474dc563480018eea9b8ac6900031d5537158d200063bba8e2b1a4000c74751c5634800196ee838ac6900032d1d07158d200066bb98e2b1a4000ce7721c563480011bf0eb18c690002b52056318d205643e432eb9924000c3c645d732480ab0ff0fb2e64900021f61f65cc9200061f3aec99924000c3d75d933248001970c8b86649000a1f216768c92000c5e424ed192403487c865d63248001878c8bac649003b5a081758c9200043fc3ecb192401387d87d96324800187ce9b2c64900c62f219748c9200061fb2ae91924000c3c655d2324800117f0fb24649004a2f61f648c9200061f3aec91924000c3d75d92324800187ee8aa6c2900070f1d154d85200061f3a6cb30a4000c3e74196614800187ecaba4c2900030f19574985200061f3aec930a4000c3d75d92614800187cea324c2900030f5d464985200143f436eab0a400087e87d956148001878e9b2ac2900021fa1c65585200061e3a0cab0a40018be86dd1614800187ecbba2c2900030f19774585200045f43ec8b0a4000c3f75d916148001878ebb22c2900022fa1c64585200061fba8c8b0a4000c3c7519161480018becbb9ac2900031719773585200064fb26e6b0a4000c9c64dcd61480018beca39ac2900031719473585200064fb20e6b0a4000c9c641cd61480011ef0eb08c290002b520d61185200043fc2aed98a400287c855db314800117f08bb662900062f21176cc5200043fc2aed18a400287c855da314800117f08bb462900062f211768c5200143f42eec98a400087d85dd9314800317d09bb262900022f613764c5200143f42cec98a400087d859d931480050f90a3b262900021fa1b754c5200061e326ea98a400087e87d9531480010f90fb2a62900030fdd7644c5200061e3aec898a400287c859d83148003179093b0629000e3b20a760c5200247c404ec18a400087f855d831480050f90abb062900022fe11760c52000c5e422ec18a400087c865d43148001878c8ba862900021fe1f650c5200043ec3eca18a4000c3e74d9431480ab8f4e1b2862900022f219740c5200
  | 8 => 0xe3a2c7100030fdd47458e200061e3a8e8b1c400087e87d5163880050f90faa2c7100030fdd35458e2000e1e3a6a8b1c400087e8755163880010f90eaa2c7100030fdd15458e2000e1e3a2a8b1c4002c5c7594d63880091b90ea9ac710007271d24358e200246e43a86b1c4007c5e635d732880018baeab1e65100030fdd1545862000e1e3a2a8b0c40048f4875056188001c6aa8a0ac3100021fe1576cc6200143e42aed98c40008bf845db318800317908bb663100021fe15764c6200143e42aec98c40008bf845d9318800317908bb2631001f1798d750c62003e4f31ae818c4000c5d7558c318800193ae8b186310013369c1630c62003e6731ae418c4000ccd635c831880010fd0dba6ca9000a1fe1f64d95200061eba6c9b2a400087d8799365480010ff0eb26ca9004e1f61c64d95200061eba0c9b2a4000c3d871936548001c5b04326ca900038b19242d95202ad3643285b2a4000d2f7450b6548001c58c8a16ca900021f61e74d95200061fc22e9b2a400087e871d3654800187ae83a6ca902b69ba0874d95202ad36c10e9b2a4000c5d731cf65480010fd0fa1eca900021f61f43d95200043f43887b2a400087d8710f65480ab0fd0fa16ca900021f61f42d95200061fba685b2a4000c3f7450b65480010fd0e216ca9004e1f61c42d952000716a1085b2a4000a3e849c7654800147b0938eca901569ea0071d95200053cc00e3b2a400087e87d0765480010fb0fa0eca900030fdd341d95200061fba283b2a400087e8710765480010fb0e20eca901429ba0b70d95200043f43e81b2a400087d87d03654800147d0dbaec8900030f9db75d912000697b96ebb224000a3e861d7644800187cec3aec8900030f9db65d91200045ec3ccbb224000a3e85997644800117f0eb2ec8900028fa1865d91200061f3b0cbb224000c3f72dd7644800187ae5baec8900030f9c375d91200061e386ebb224000a3e859d7644800187aea3aec8900028fa1c75d91200061f438ebb224000a3e859cf644800147b0b39ec8900028fe1573d91200051e42ae7b224000e1f5394f644800117d0e296c89004a2f61c52d91200061fbaee3b224000a3e859c7644800147b0b38ec8900028fe1571d91200051e42ae3b224000c3f755c764480a95750038ec890002ae60071d91200045f438a3b2240008bd8714764480a355d05b86c8900022fa1f50d91200045ec3ea1b224000c3e74d96634800187ce832cc6900030fd957498d200061e32ae931a4000c3e75d92634800187aebb24c6900030f9d46498d200061eba8c931a400087e87d956348001878e9b2ac6900021fa1c6558d200061e3a0cab1a4000c3f65dd16348001878cbba2c6900022fa1f6458d200061fbaec8b1a4000c3c75d91634800117d0e322c6900030fdd46458d200061e3a8c8b1a4000c
  | 9 => 0x65085300045e432e810a6000c3f655d0214c001878caba042980022fe1f64085300045ec3ec810a6000c3e75d90214c00187aebb2042981a3279cf640853033e5d386c810a6000c5f655cc214c0018b8cab98429800327d9173085300064e322e610a600eccc625cc214c00199ae7b104298003355cf61085300063db2ae010a6000c78655c0214c001976c8b8042980032e191700853000675b12e010a6000cf3615c0214c0079e0c2b80429826717cc374594304ce2e986e8b28609687d879d1650c00187ee93a2ca180030fe1174594304b61f202e8b286096c3c405d1650c12d8be60ba2ca1825b174c174594304cc3f438e8b286000a3e841c9650c00147b08392ca180021fa1f42594300043ec3e84b286000c3d74d09650c00187ae8a12ca180021fa1c42594300043ec3884b286000a3e841c5650c00147b0838aca180021fa1f41594300043ec3e82b286000c3d74d05650c00187ae8a0aca180021fa1c41594300043ec3882b286001c3e74552620c00187ae8aa4c4180038b55142988300043fc2ae3310600287c855c6620c0091d90ea12c4180038b55142588300247a43a82b086000e3554505610c0050f90bbb242180021fe1576484300143e42aec90860798df835d9210c0010fb0dbaa42180021fa1d65484300043e43aca9086007c5c73595210c0018bccbb9a421800317597734843003e6639cc4908600287e855d8210c0071bb06bb042180021fe1975084300043fc3aca108600087d87594210c00187ce8b28421801f179cd65084300263d382ca1086000c3e655d0210c00187acaba042180031799573084300062eb2ae61086000c7a655c0210c0018f2cab8042180021fe1175d8f200061f42ae9b1e4000c3d855d363c80050ff0faa6c7900021f61f54d8f2000e1f3a6a9b1e4000c3d74d5363c80010ff0eaa6c7900021f61d54d8f2000e1f3a2a9b1e4000c3d7455363c80011ef02baac79000e3d2057558f200043ec26eab0e40008df835d561c800f1b906baac3900028f61075587200043fc2ae8b0e400287c855d161c80011bf06ba2c39001e3720d74587200043f43ea8b0e400287c87d5161c81358b8e7aa2c3900021fa1d54587200043e43aa8b0e4001c3e7455161c800187ae8aa2c39025f171cd54587200062fbaee6b0e4000c5c75dcd61c80018bea9b9ac3900031755373587200062fba8e6b0e4000c5c751cd61c80010ff0abb4639000a1f215768c7200043fc2aec98e400287c855d931c80011bb0fb18639000333d8d720c72003e6631ae418e400eccc7258d30c80050fd0fbaac7100021f6137558e200045fc22eab1c40018bc845d563880d30fd0e3aac7100062fa1f7458e200061fbaee8b1c4000c3c75dd1638800187f0bba2c7100030f2177458e200043fc2ae8b1c400287c855d163880cf17d
  | 10 => 0x9926000ccc71189324c15f8bae632ec2982c3275cc64d85300061fba2a9b0a6001c3c74553614c0771bb0f996c29800237e1d32d85301dd6a40a65b0a6000c3e74d96614c00187ce832cc2980030fd9574985300061e32ae930a6000c3e75d92614c00187aebb24c2980030f9d464985300061eba8c930a600287e86dd5614c0d30f90dbaac2980021fa1f65585300061e3a6cab0a600087e87195614c001878e832ac2980062fa1b745853033c5e436e8b0a6000c3f65dd1614c001878cbba2c2980022fa1f64585300061fbaec8b0a6000c3c75d91614c00117d0e322c2980030fdd464585300061e3a8c8b0a6000c6f65dc9614c0018d8cbb92c2980032bd93725853000656326e4b0a6000c6f651c9614c0018d8ca392c2980032bd90725853000656320e4b0a60a1c7970194614c141972e0320c2980023de1d611853000572412c230a6069c5e76d96314c0cf93cedb24629800257e15728c5300046ec38c518a6000e5765d86314c15f0fd0dbaa62980030f193754c5305743f43eca98a6000c3f75d91314c001878ebb22629801276202760c5302d4ae432ea18a600095f845d4314c0012bb08ba8629800347191750c53003e2fb02ea18a6007d5b605d4314c077ab420ba862980ef56441750c530004afc3eca18a6069d5a70d94314c0b13390cba0629800347a15740c5300068ec2ae818a6000d1f655d0314c001a38caba0629801f27d81740c53003ecdb02e818a603bd9a105d0314c077b3220ba0629800267e1f640c5300068ebaec818a6067d9a70d90314c0019990cb90629800353d95720c530006a632ae418a6000d8f645c8314c001b18c8b90629800353d51720c530006a6aa2e418a603bccf615c8314c07799ac2b90629801f33d81720c53003ee5b02e418a603bdca105c8314c077b9220b906298003335c8620c5300043fc2aed90a600287c855db214c00117f08bb642980062f21176c8530076663b26590a6000ec532d87214c0091bb073b442980021fe1576885300143e42aed10a60008bf845da214c00317908bb4429800333dcc62885300143f42eec90a600087d85dd9214c00317d09bb242980022f61376485300143f42cec90a600087d859d9214c0050f90a3b2429801e3720c76485300043f436ea90a6000c3c64dd5214c0010fd0fb2a42980021f21f65485303562e39eca90a6000c3f75d91214c001878ebb2242981a3271cf64485300062fb2ee690a6000c5c65dcd214c00193ec9b9a429800327193734853003ce643a6490a6000ccc764c9214c0050f90b3b042980062f212760853001c6e41cec10a600087f855d8214c0050f90abb042980022fe11760853000c5e422ec10a600087c865d4214c001878c8ba842980021fe1f65085300043ec3eca10a6000c3e74d94214c0d58bce7b2842981a71e9c3
  | 11 => 0x4c0010fb0e216ca981aa97a0f71d953034d2ec1ee3b2a6000a3e849c7654c00147b0938eca981a69ea0071d95303553cc00e3b2a600087e87d07654c0010fb0fa0eca980030fdd341d95300061fba283b2a600087e87107654c0010fb0e20eca981aa1fa1f40d95300043ec3e81b2a6000a3e86dd7644c00187cedbaec8980028fa1875d91300061f3b0ebb226000c3e76d97644c00117b0f32ec8980028fa1665d91300045fc3acbb226000a3e86197644c00187cec32ec8980038760c65d91300070e32ca7b226067a9c8654f644c00187ce1baec8980030f1c375d91300051f42cebb226000c3d751d7644c0d153d063aec89819ea760c75d913033d5d400ebb226068ab9801d7644c00147d0e3aec8980030fa1c75d91300070f418ebb226000e1d831d7644c001c75003aec8980038e60075d91303470f29ea7b226000c3f75dcb644c0cf57501b96c8981a2ae60372d91300051f42ce5b226000a3d859cb644c00195ee5396c8980028fe1572d91300051e42ae5b226000c3f755cb644c0d153d06396c89819ea760c72d91300045f438a5b2260008bd8714b644c00187eebb8ec8981a2a7a0f71d913033d4ec1ee3b226000a3e859c7644c00147b0b38ec8980028fe1571d91300051e42ae3b226000c3f755c7644c0cf5750038ec8981a2ae60071d91300045f438a3b2260008bd87147644c0d117d0fa86c8980022f61f50d913033f1d286a1b2260078f980dd3624c00187ee8aa6c4980070f1d154d89300061f3a6cb3126000c3e74196624c00187ecaba4c4980030f19574989300061f3aec93126000c3d75d92624c00187cea324c4980030f5d464989300043f43ecab126000c3c74d95624c0010fd0e32ac4980030f1d065589300061fb2ee8b126000c3c65dd1624c00117d0fb22c4980030fdd764589300061e3aec8b1260008be87191624c00187eea322c4980030f1d464589300063bb2ee2b126000c7465dc5624c00196ec9b8ac4980032d19371589300063bb28e2b126000c74651c5624c00196ec838ac4980032d190715893057e2eb98ca31260b0c9d73190624c0011df0eb10c498002b9205621893000e1f3a2a83126000c3d74550624c0010ff0ab88c49800a1f2157118930334ae432eb992600095f845d7324c0012bb08bae64980034719175cc93003e2fb02eb9926007d5b605d7324c0012bf0fb2e6498003475d764cc93057c3e432eb1926000c3c645d6324c0010fb0fb2c64980030f9d3658c9305845e432e91926000c3f655d2324c001878caba464980022f61f648c9300061f3aec91926000c3d75d92324c0d38b8edb2a649819f271db644c93000727b28c49926000e4c65189324c001d1ec83126498003a3190624c93000567438c4992600ecce87189324c001c9ea8312649800393550624c93000566c08c4
  | 12 => 0xa578e50554580214af3910aa8b004200a7b855cd60084014f10ab9ac010802aee1173580210055c422e6b00420eae8825cd60084075e102b9ac0108029ea1473580210053cc28e6b004200e5b5394d60084015e702a9ac01080ebc20553580210053d42e86b004200a7985d0d600841d5d505a1ac010802ba60b435802101d7940e86b004200af181d0d60084014f50a21ac0108029e61443580210053d42e84b004200a7985d096008401c72a9a12c0108038e55142580210775421284b004200a7a85cc960084014f30b992c0108039ce1521580210073842a42b004200e73544856008401ce2a890ac010803b4e0d21580210076841a42b004203ee382485600841ddc4a490ac010803b854921580210777121242b004200ee14248560084010ff08bacc5980030fa157498b300061ec2ae9316600ecaf205d262cc0050ff0faa4c5980021f61f5498b3000e1f3a6a93166000c3d74d5262cc0010ff0eaa4c5980021f61d5498b3000e1f3a2a93166000c3d7455262cc00387ce8aa2c5980030f5d15458b300143f43eeab0e608ac5c73dd561cc0010fb09baac3980123720d75587300051ec20eab0e609bc5c731d561cc0010ff0aba2c39800a1f21574587300246e41ae8b0e600087e87d5161cc0050f90faa2c3980021fa1d54587300043e43aa8b0e6001c3e7455161cc00187ae8aa2c3981263721d325873024d6a40a64b0e600095f855ca31cc0010ff0abb4439800a1f21576887300246e41aed10e600087f855d921cc0050f90abb243980123720d764873003e6639cc490e6007ccc7358921cc00387ce8aa4c5180030f5d15498a3000716aa285314600087f855c6628c0050f90ab8cc51800a1fa1f7558a300043ec26eab146055c5f30dd5628c0ab8ba61baac5180021fe157458a300143e42ae8b1460048f8805d1628c0010fd0faa2c51800a1f21f5458a300043f43aa8b14600087c87551628c0091d90ea12c5180038b5514258a3007657312e91946000cad7458a328c0018eeeba8ac318002ad61051586300247a43a82b0c6000e3554505618c0018e8eab0a63180021fe1576c86300143e42aed90c600087f855d9218c0050f90abb243181e73598773486300063a3aac290c600087e86dd3654c0050ff0fb26ca980030f5d364d95300043ec3cc9b2a600087f87593654c0350fb0e326ca980030f5d064d95300061ec38c9b2a6000e1d83193654c001c38c921eca981a69721943d95300070e32287b2a600087d879d3654c00187f08ba6ca980021fa1c74d95300061eba0e9b2a606aa5e831d3654c0d34bb063a6ca981a61fa1f43d95300043ec3e87b2a6000a3e849cb654c00147b09396ca981aa97a0c72d953034d2ec18e5b2a600087e87d0b654c0010fb0fa16ca980030fdd342d95300061fba285b2a600087e8710b65
  | 13 => 0xc6e43aa6b1842038de87d0d63084014bd0ba1ac610802976174358c210756741686b184203ad681d0d63084071b90ea1ac61080297a144358c210052ec2886b184200c5f759d563084015af02baac61080eb52057558c210052f42ce8b184200a5d859d1630841d59d053a2c610802b360a7458c2101d6b40ce8b184200ad5819d163084014bd0a3a2c610802976147458c214c72790ea8b184298e4d21d51630852b4bb0b2a2c61080387d525458c210070fc22a8b184295e1f41551630852bc3a82aa2c610a5793c855458c214af2690aa8b184298a5e8515163084014bd0ba12c610802976174258c210070eaa684b184200e1d54509630841dd1884a12c61080297e157058c210052e42ae0b184200a9f845c1630840153908b82c61083ab32097058c2101d6a40ae0b184200a5e851c163084014bb0a382c610802a7a135058c210054ec26a0b1842008de8714163084011bb0e282c61080297a174058c210052ec2e80b184200e1d5490163084011bd0e202c6108023761c4058c210052f42880b184200a5d851016308401c3aa8202c61083ab3a084058c2100566c1080b184203ad68110163084015ab02202c61080a1fa1576cc8211b43fc32eb9904200c3e645d7320840f8bcc6bae64108821fe1d65cc8210043ec3acb9904200c3e75593320840187aeab266410803179d563cc8210062ebaac79904200c7475dd921084018ef0bbb242108031d21776484210063baa6ec9084200c7554dd921084019af07bb242108033520f764842107673296ec9084200ce552dd921084018eeedbaa421080335ddb73484210066bbb0e69084200d54751cd2108401c76a92a4c0108038ee1154980214b71dba2a93004296e3874552600852bc7682aa4c010a578e50554980210072da9ca73004200a7a85d0e60084014f30ba1cc0108029ea1443980210053cc28873004200a7a85d0a60084014f30ba14c0108038e55342980210071caa2853004200a7a85cca60084014f30b994c0108030fdd1545802100e1e3a2a8b0042038fa87d41600840157509a82c010802ae613505802101c7c43aa0b004200ada8314160084015b306282c01080e3ea1f40580210053d42e80b004200a7985d016008401c72a9202c01080e3e21d40580210053d42880b004200a79851016008401c72a8202c010802b6a0c40580210056cc1880b00420eaea8210160084075e502202c010802aea1275580210055cc24eab004200ada831d560084015b3063aac0108029ea1674580210053cc2ce8b004200a7a851d160084014f30a3a2c010802b6a0c74580210056cc18e8b00420eaea821d160084015d3043a2c01080ebca04745802100578c08e8b004298e7221d516008401c76a92a2c0108038ee1154580210071dba2a8b004200e3874551600852bc7682aa2c010
  | 14 => 0xc87d9531484018beebb1a6290803171d7634c52100667b18e498a42039cc874c931484075990c992629080ef1205324c5213f733b16cb90a4200e546518f214840147b0832ec0908070f9d154d81210061eba2a9b024200e395410360484015d304206c090802bc60440d81210051ec20cb3024200c5f659ce60484018b8cb39cc09080317d9573981210062e32ae73024200c5e75d8e60484018baebb1cc090803179d463981210062eba8c7302420287e86dd560484fd0f90dbaac0908021fa1f65581210061e3a6cab02420087e87195604840147b0832ac0908030f1d065581210061fb2ee8b024200c3c65dd160484018becbb9ac0908031719773581210062fb28e6b024200c5c651cd60484011bd0fb1ac09080317dd763581210062e3aec6b024200c9f74d8d6048401938e9b1ac09080237a1c63581210062fba8c6b024200c5c7518d604840193ee831ac090803271d063581210051ec20ca30242008fb87580604840157108b00c090a561f61e74594210061fba4e8b284200c3f845d165085310fd0e3a2ca1080317dce735942158d3bc0ae6b284203a74815cd65084010fd0fa1aca108021f61f43594210043f43886b28420087d8710d65084410fd0fa12ca108021f61f42594210771621284b284200a3e84dc1650840147b09b82ca1080297a0c70594210052ec18e0b28420087e87d0165084010fb0fa02ca108030f5d240594210043f43880b28420087d87101650840187ae8202ca1080297a0c40594210052ec1880b28420ea6e8210165084014db04202ca1080e9da0440594210053ac0880b284200c3f759d5640852b47b0f3aac8108030fe1d75590210061fb92eab204200c3d725d5640852b87ee2baac810a570f5c575590214c51f428eab204200a3e85dcd640840147b0bb9ac8108028fa1473590210051ec28e6b204200e1f5394d640840147d0bb82c8108028f61770590210061ebace0b204200a3e851c1640840147b0a382c8108030f5d470590210054f418e0b204200a9d831c1640841d55d04382c81087eab608705902101d5b408e0b20421fab5811c1640840117d0fa82c8108022f61f50590210054f418a0b204200a9d83141640852b4bb0b2a4c61080387d525498c210070fc22a93184295e1f41552630852bc3a82aa4c610a6297a145498c210052f42e853184200a5d85d0a6308401c3aa9a14c610803875514298c210054f426a13184200a9d84d42630840f1bd0e284c6108023761c5098c210052f42e813184200a5d85d026308401c3aa9204c61081e37a1c4098c210046ec38813184200a5e8510263084014bb0a204c610803875504098c2107567410813184200acd8210263084075ad02204c610802b56044098c2101c7a40aeab1842038de87d4d63084018beeba9ac61080b179d65358c2101
  | 15 => 0xaba2c69080237e0d7458d210047dc02e8b1a42048f8805d163484010fd0faa2c69080a1f21f5458d210043f43aa8b1a420087c8755163484018beebb9ac690803171d77358d210063a3aee2b1a4200a3d8419463485578dae4328c69080237e1d6318d210052fc2ac631a4200a5c8558c63484018bcedb28c690802976136518d210046ec3cca31a42008df87594634840153d08328c690802a76106518d210062f3b0ca31a4200b1d841946348401c3d08328c690802976106518d210070ec20ca31a4200a1d8419463484011bb0f320c69080297a166418d210052ec2cc831a42008df8759063484014bf0ab20c690802972156418d210056dc02c831a4200ad88059063484014bd0a320c690802976146418d210052f436a831a4200a5c86d5063484018bcedaa0c69080297a195418d210052e432a831a4200c5e765506348401c3cc8aa0c690803875915418d2100727b2ae431a4200e4c655c86348535c9ce5aa0c690a6b935cb5418d214bd2ec2ca831a4200e1f549506348401c3f08aa0c690a5f879d15418d214bf0eba2a831a4297e4e72550634852fc9ae4aa0c690a6a97a145418d210056bc0aa431a427dad481548634840153d08290c690802a76105218d210052f42e8431a4200a5d85d086348401c3aa9a10c6909f6b5a074218d210056ac0e8431a4200e1d5450863484014bd0a210c690802976144218d210052f42e8231a4200a5d85d046348401c3aa9a08c690802b3a0b4118d2100566c168231a4200e1d5450463484014bf0a908c690802972152118d210054f426a031a4200a9d84d4063484fb5ad03280c690802b56065018d2103c6f438a031a42008dd8714063484014bd0ba00c690802976174018d210070eaa48031a42078de8710063484011bb0e200c69080297a144018d210052ec288031a4200e1d54100634840159d04200c690802b36084018d213ed6b4088031a4200ad58110063485570f90cbae649081f1718d75cc9213f43fc3ecb992420087d87d9732484018bcebb1e6490803175d763cc9210143e42ced192423487c865d632485298b8c6bac64908021fe1f658c92111c3ec3ecb1924200c3e74d96324840187ecaba464908030f195748c92149e4e31ae91924200c5e75d8e32484018baebb1c6490803279d3638c9210064eba6c71924294e4c635d6324840195cecba46490a4fa318d748c92103d67436c71924200cce76d8e3248401c9eca31c649080393194638c9213ce6a38ec69924200c7465dc532484fd8d8edb2a649081f331db734c9213ce663b6c69924207ccc7618d32484f3b8ee638a6490802f8600714c92103d66432641924207ccc639cb31484f339f0e996629080eb321932cc5210043fc2aec98a420287c855d931484010fd0dbaa6290a2b1718f754c5214dc3f43eca98a428a87
  | 16 => 0x4d95210061fba4e9b2a4200c3f845d365484010fd0e3a6ca908030f5d074d95210062eb98e7b2a42b2a6e821cf65484fd4db0439eca908021fa1f43d95210043ec3e87b2a420087e8710f65484010fb0e21eca909fa1fa1f42d95210043ec3e85b2a4200c3f74d0b654840187ee8a16ca908021fa1c42d952111c3ec3885b2a4272a6e82dc765484010fd0fa0eca908021f61f41d95210061fba683b2a4200c3f7450765484014bd07386ca908029760e70d95210051fc22e1b2a4200a3c845c365484fd4ed02386ca908029d60470d95210043f43e81b2a420087d87d03654840187ee9206ca908021fa1c40d95210043ec3881b2a4200c3f7410365484014bd06206ca908029760c40d95210053741081b2a4200a6d8210365484fd4ed02206ca908029d60440d95210051ec20cbb1a4201c3e74553634840187ae8aa6c690803175d753d8d210162e3aca7b1a42028df8754f63484014bd0ba1ec6908029761743d8d2100c6fc3a87b1a4200a5e8510f63484014bb0a21ec6908029761365d8d210054f420cbb1a4200a9d84197634840163b0832ec69080387a1065d8d210052ec20cbb1a4200e1d84197634840143b0832ec69080297a1664d8d210052ec2cc9b1a4200a5f8559363484014b90ab26c690802b6e0164d8d210056c402c9b1a4200a5e8519363484014bb0a326c69080297a1b54d8d210052e436a9b1a4200a5e8655363484014b90caa6c6908038799154d8d210070eb22a9b1a4200c5d751d7634840153d083aec690802a761075d8d210052f42ce9b1a4200a5d859d363484014bd0a3a6c6908029761474d8d210070faa4a9b1a4200e1f845536348401c3ce8aa6c690803875d154d8d210052fc2ae5b1a4200a5c855cb6348401c9ea5296c690802a7a1052d8d210054ec20a5b1a4200a5e85d0b63484014bb0ba16c6908038755342d8d210070eaa285b1a4200a5e8510b63484014bb0a216c69080297a1771d8d210052ec2ee3b1a4200a9e84dc7634840153b09b8ec6909e79594751d8d210052f42e83b1a4200a5d85d076348401c3aa9a0ec6908038755141d8d210052f42ee1b1a4200a5d85dc3634840153d09b86c690802a761370d8d210052f42ce1b1a4200a5d859c363484015ab02386c690802a7a1350d8d210054ec26a1b1a42008de8714363484011bb0e286c69080297a1740d8d210052ec2e81b1a4200e1d5490363484011bd0e206c6908023761c40d8d210052f42881b1a4200a5d851036348401c3aa8206c690802b3a0840d8d2100566c1081b1a4279ad68110363484015ab02206c69081f1718d7598d210051ec20cb31a4200c5e75d8e63484018baebb1cc6908021fa1f6558d210043f438cab1a4200a3d8419563484010fb09baac69080237e0d7558d210047bc0aeab1a420087f855d163484050f90
  | 17 => 0x6295e3b41552600c52bc7282aa4c018a669ea1454980310055d420a53006200ab98414a600c4014f50ba14c0188029e61742980310071caa6853006200e395450a600c4014f50a214c0188029e61442980310061fba2a8b006201c3c74551600c4071f50fa82c018802aea1350580310055cc26a0b0062038f887541600c40f5b506282c01880e3ea1f40580310053d42e80b006200a7985d01600c401c72a9202c01880e3e21d40580310053d42880b006200a7985101600c401c72a8202c01881eb6a0c40580310057541080b006200ae982101600c4075e502202c018802aea1275580310055cc24eab006207ada831d5600c4015b3063aac0188029ea1674580310053cc2ce8b006200a7a851d1600c4014f30a3a2c01881eb6a0c74580310056cc18e8b006200aea821d1600c4015d3043a2c01880ebca04745803100578c08e8b006295a7985951600c401c76a92a2c0188038ee1154580310071dba2a8b006200e3874551600c52bc7682aa2c018a578e50554580314c53d428a8b006200a7b855c9600c4014f10ab92c018802aee1172580310055c422e4b006207ad8835c9600c4075e102b92c0188029ea1472580310053cc28e4b006200aba841c9600c40157308392c01881eb6a0c725803101d79408e4b006207ada83d49600c4015b307a92c018802aea1052580310055cc20a4b006200a7a85d09600c4014f30ba12c0188038e553425803103d6d41e84b006200ad983d09600c4075e503a12c018802bc60742580310071caa284b006200a7a85109600c4014f30a212c0188021fe1175d8f210061f42ae9b1e4200c3d855d363c84050ff0faa6c7908021f61f54d8f2100e1f3a6a9b1e4200c3d74d5363c84010ff0eaa6c7908021f61d54d8f2100e1f3a2a9b1e4200c3d7455363c84f31bf0eb1e63909e673e1d32cc72101ce643a6498e420087d84dd560c840117f08baac1908062f21175583210061fbaee8b064200c3c75dd160c840187f0bba2c1908030f21774583210043fc2ae8b06420287c855d160c840187eea3a2c1908030f1d474583210043f43ea8b06420287c87d5160c840187ee9aa2c1908070f1d354583210043f43aa8b06420087c8755160c840187ee8aa2c1908070f1d154583210143f43eeab1c420087d84dd563885130fd0e3aac7108021fe157458e210143e42ae8b1c420087e87d5163884050f90faa2c7108021fa1d5458e210043e43aa8b1c427d8df8758f328840187ee8aa2c1108070f1d154582210043f436e9b2a420287f87d93654840187ae9b26ca908021f61e64d95210061fba4c9b2a4200a5e8399365484014bb07326ca908021fe1d64d95210061fba2c9b2a4200a5f8359365484014b906b26ca908029ee0164d95210053c402c9b2a422387d87193654840187ae8326ca908021f61e7
  | 18 => 0xc40155b09a84c41881eb3a0c509883100566c18a13106200a6e85d02620c4014db0ba04c4188038b5524098831074774388131062008ed87102620c4014dd0a204c4188029b614409883100716aa0813106207ace83102620c40159b06204c41880eb9a04409883100572c088131062078dc835d5620c40f1b906ba2c418a6b930cb545883100e1f3a2a8b106200c3d74551620c52fc9864aa2c41880e3ba1f525883103d6741ea4b1062038ec87549620c40f59906a92c418802aba10525883100556c20a4b1062038ee87d09620c4014dd0ba12c4188029b617425883100716aa684b106207ace83d09620c4075cd03a12c41880e3b21d425883100716aa284b106207acc83509620c4014dd0a212c4188029b614425883103d6741ceab106200acd839d5620c40159f06baac41881eb320d755883100573c0aeab106203ae4815d5620c40155d083aac418802ab61075588310053742ce8b106200a6d859d1620c40f59d073a2c418802b360e745883101d7340ce8b106200ae5819d1620c40159f06ba2c41881eb320d745883100537428e8b106200a6d851d1620c531c9e63aa2c418a63934c754588314d727986a8b106295a6d85951620c401c5ea92a2c418802b3e0d545883103d6641aa8b106200e2f84551620c401c5ce8aa2c4188038b5d1545883100727c1aa8b106297e4c83551620c52bc5e82aa2c418a578b50554588314af2798aa8b106295e4d31551620c52fc9e60aa2c418a629ba14545883103d6641ee0b106207ace839c1620c4014df0ab82c4188029b215705883100557c22e0b106200aac845c1620c40f59906b82c41880eb9205705883100537428e0b106200a6d851c1620c40155d08382c418802ab610705883103d67418e0b106203ae6811c1620c40155d09a82c418802ab613505883103d6741ca0b106200acd83941620c4075cd03282c418802b9606505883103d67418a0b106200acd83141620c4014dd0ba02c4188029b617405883100716aa480b106207ace83901620c40159b07202c4188023ba1c405883100476c3880b106200a6e85101620c4014db0a202c4188038b550405883103d6741880b106200acd83101620c4075cd02202c418802b960440588310062f3aaed1906200c9e745da320c40f99ce4bb4641880317a15768c8310062ec2aed1906200c9e845da320c40193b08bb4641880317d51768c8310062eaa2ed1906207cce825da320c40f99b04bb46418803175d9758c8310064ebb2e91906200e4e7558a320c401c9aeab146418803a39d1628c83100746ba2c51906200e4f5458a320c401c9aa8b1464189e733dc5628c8313ce66b8ac51906200ccd625c2320c533cb2e7aa4c018a5a9e61654980310071daa4a93006200e3b84552600c52dc76e8aa4c018a5b8e1d154980314b72cb9aa93
  | 19 => 0x21f61f658c9310061f3a6cb1926200c3f655d2324c401878caba4649883b2b189748c93100656ba6c51926200c7465dc5324c5138b8edb2a64988070f9d154d81310061eba2a9b02620287e86dd5604c5130f90dbaac0988021fa1f65581310061e3a6cab02620087e87195604c401878e832ac0988030fd9774581310061e32ee8b026200c6f65dc9604c4018d8cbb92c0988031bd94725813100636328e4b0262008fb87580604c5358be61ba2ca18a561f61e74594310061fba4e8b2862b8a5f835d1650c40f4b906ba2ca188030fe1174594310062fc1ae8b286297c5c835d1650c52f8be60ba2ca18a621fa1c74594315bd2fc1ae4b286207a5c835c9650c56d4ef02b92ca1880e9d20572594310051f420e4b286200a3d841c9650c4010fd0fa12ca188021f61f42594310061eba684b286200c3d74509650c4010fd0e212ca188021f61c42594310051f426e0b286200a3d84dc1650c40f4bd07382ca189669760e705943101d3b40ce0b2862b5a75819c1650c40f4bd06382ca188a29760c70594310043f43e80b28620087d87d01650c40187ae9202ca1881e97a0e40594310052ec1c80b28620087e87101650c4010fb0e202ca188030f5d0405943103d2f41880b286200a5d83101650c4014dd04202ca188029b608405943101d3b40880b286200a7581101650c40187eeb3aac818a568f61e75590314d70f984eab2062b4a9f835d5640c40f53906baac8188030fe1d75590310070fc1aeab206297e1c835d5640c52b87ee2baac818a570f5c575590314bf0f982eab206298a3e851d5640c40147d0bb92c8188028f61772590310061ebaee4b206200c3d755c9640c56753f06b92c81881ea720d72590310051f428e4b206200a3d851c9640c40117d0e292c8188022f61c52590310051f42ee0b206200a3d85dc1640c40187aeb382c81881ea7a0e70590312bd4ec1ce0b206200a3e851c1640c40147b0a382c8188030f5d4705903103d4f418e0b206227a9d831c1640c40155d04382c818802ab608705903101d5b408e0b206227ab5811c1640c40117d0fa82c8188022f61f505903103d4f41ca0b206200a9d83941640c40756d03282c818802ad606505903103d4f418a0b206200a9d83141640c4071d904bacc41880e3b209749883100e1f3a2a93106200c3d74552620c4014dd0ba14c4188029b617429883100716aa6853106200e2d5450a620c4010ff0ab84c41880a1f21570988310045fc22e131062018bc845c2620c4071d904b84c4188029ba16749883100536c2ce93106295a6d85952620c401c5ea92a4c4188038be115498831007173a2a93106200e2d74552620c52bc5e82aa4c418a578b50554988314c537428a93106200a6f855c2620c4014d90ab84c418802abe11709883100556422e13106200aae84d42620
  | 20 => 0x1fba6a8b006401c3c74d51600c8010fd0eaa2c0190021f21d54580320061fba2a8b006401c3c74551600c81dd9040992c01900b1e1d650580320747c43aa0b006401cb874901600c801c72a9202c01903a3e21d40580320043fc22eb3166200c3e855d262cc40187b0aba4c59880a1fe1f5498b310043ec3ea93166201c3e74d5262cc40187ae9aa4c5988021fe1d5498b310043ec3aa93166201c3e7455262cc40187ae8aa4c59880a1fa1f75583310043ec26eab0662008bf845d560cc40317908baac1988062fa1f74583310061fbaee8b066200c3c75dd160cc40187f0bba2c1988030f21774583310043fc2ae8b06620287c855d160cc40187eea3a2c1988030f1d474583310043f43ea8b06620287c87d5160cc40187ee9aa2c1988070f1d354583310043f43aa8b06620087c8755160cc40187ee8aa2c1988070f1d154583310766639264b066201c3e74552628c40187ae8aa4c5188021fe157098a310143e42ae131462008bf845c2628c40317908b84c51880a1fa1f7558a310043ec26eab146200a3d841d5628c4010ff0aba2c51880a1f2157458a310047dc02e8b1462048f8805d1628c4010fd0faa2c51880a1f21f5458a310043f43aa8b14620087c87551628c40387ce8aa2c5188030f5d15458a31006aabaae31946200c3f74551608c403878e8aa2c1188021fa1b74d95310143fc3ec9b2a6200c3d74d93654c4010fb0f326ca988029ba0a64d953100536c14c9b2a620087f87593654c4550fb0e326ca988030f5d064d95310043ec3ce9b2a6200c3f845d3654c4010fd0e3a6ca988030f5d074d953144c3f43e87b2a620087d87d0f654c40147d09396ca988028f61272d95314552f418e5b2a6289a5d831cb654c4018dae4396ca988021fa1f42d95310043ec3e85b2a6200c3f74d0b654c40187ee8a16ca988021fa1c42d95310043ec3885b2a628a87e87d07654c4010fb0fa0eca988030fdd341d95310061fba283b2a628aa5e839c3654c4014bb07386ca988028fe1170d95310051e422e1b2a620087e87d03654c4010fb0fa06ca988030fdd240d95310043f43881b2a620087d87103654c40187ee8206ca98a2a97a0c40d95310052ec1881b2a6200a6e82103654c4014db04206ca98a269da0440d95310053ac0881b2a62018ef8750b624c401c5aa8a16c4988030f9d365989310061f3a0cb3126200c3f655d2624c401878caba4c49883b2b189749893100656ba6c5312620087e87d95624c4010fd0e32ac498abb175cc651893100477c3ac43126201c3e74550624c40187ae8aa0c4988038b55142189310043fc2ae0312620287c855c0624c40117f08b80c4988062f21170189310062e32ced9926200c5f859db324c4018b90b3b6649880317d5276cc9310062eaa4ed9926200c5e76d97324c55d0f90cbac64988
  | 21 => 0x841c5658c8010fd0fa0acb190021f61f41596320061eba682b2c6400c3d74505658c8010fd0e20acb190021f61c41596320051f426e0b2c6400a3d84dc1658c9294bd06382cb190029760c70596320043f43e80b2c640087d87d01658c80187ae9202cb190021fa1c40596320043ec3880b2c6400c3d74101658c9294bd06202cb190029760c40596320753741080b2c6400a6d82101658c8014ed02202cb190029d60440596320051ec34eab246400c3f769d5648c80147f0cbaac9190030fdd975592320061fbaceab246400a3d879d5648c80187f0ebaac9190030fdc975592320061eb92eab246400a3e851d5648c97355f04b9ac91924f8794f535923207717296a4b246400a3e85dc5648c80147b0bb8ac9190030f5d7715923207557414e2b24647baad829c5648c80187aeab8ac919002a7e0d715923249d4e41ae2b246400a3e851c5648c80147b0a38ac9190022fa1c51592320045ec38a2b246400a3e85dc1648c80147b0bb82c9190030f5d670592320051f428e0b246400a3d851c1648c80187aea382c91924ea7a0c70592320054ec18e0b24640eaae821c1648c86355b04382c919002ada0470592320055ac08e0b2464008be87d41648c80117b0fa82c91924ea7a0c50592320054ec18a0b24640ec6e72996618c81d8dce4b2cc31903b99c85659863207657394c930c640ecae72592618c80387ce8aa2c3190030f5d154586323cc6f43e64b0c6479ad681cc9618c8050fd0bb82c3190021f617705863200c5f426e0b0c64008bd84dc1618c80187ee8aa2c1190070f1d154582320143f42ee2b04640087d85dc5608c81db1864ba4649901e37219718c9323ce6a30ae3192640edc7215c6324c8018eaeba8ec299002ad61051d853200c7bc3a83b0a6400e3554507614c8010ff0ab86c29900a1f21570d85320045fc22e1b0a64018bc845c3614c8011ef0eb08c2990029d215611853200e1f3a2a9b026400c3d74553604c8010ff0ab8ec09900a1f21571d81320047dc3ac03026400c5e85dd9320c8018bb0bbb2641900317d53764c8320062eaa6ec990640287e87dd5610c9158b8e7baac2190021f61375584320051ec20eab08649bc5c731d5610c8010ff0aba2c21900a1f21574584320043f43ea8b08640287c87d51610c8010fd0eaa2c2190021f21d545843200e1f3a2a8b086400c3d74551610c8fb1b90e992c2191f6b520532584320776390a64b086402c7475945610c81d1e90ea8ac21903a3d21d41584320071aaa282b08640287e87dd5600c8010fb09baac0190022fe11755803200c5e422eab0064018be87dd1600c80187eebba2c0190030f1d774580320061fc2ee8b006400c3c85dd1600c8010ff0aba2c01900a1f21574580320061fba8e8b006400c3c751d1600c8010fd0faa2c01900a1f21f5458032006
  | 22 => 0xa00080180000010040004000000000803400e008000001c00000400100140000270000024016028003800c01a03b00a000000800c001800c010003005802806c0030038008004002001800000c000002000800400100000e80040090018018000000001800000000100b8014048002001000001200f006800400000000a0078004000005803804a0000138000002003002800c00a01100c8040000000002802801800e0000000004005000001c000009009000000600600300040080000010008000000003004c002000000002c01000b0018018004014001801800a00300000100180040000028000000006001001200a007002000200c00400140140040008038006000001002c00200200000000000000048000014021000000401404e01880040320080050004036001004800404e027000000000200b001800402c003001000401800900000280000000000018008009006000000400200d80100180070030004006005004001002200400080040020060000000042002000800800a00300026b17cc374597324bc3ec3ce8b2e6400c3f749d165cc9774bf06ba2cb9901e9720d74597320061fc22e8b2e6400c5f835d165cc92f8b906ba2cb9925f17cc174597324d43f438e8b2e6491a5f835c965cc8014ef02b92cb990029d20572597320043f43e84b2e640087d87d0965cc80187ae9a12cb990030f5d142597321b43f43884b2e640087d8710965cc80f4bd0738acb992229760e71597320051f420e2b2e6400a3d841c565cc8010fd0fa0acb990021f61f41597320061eba682b2e6400c3d7450565cc8010fd0e20acb990021f61c41597320051f426e0b2e6400a3d84dc165cc80f4bd07382cb991969760e70597320053b40ce0b2e6400a75819c165cc80f4bd06382cb990da9760c70597320043f43e80b2e640087d87d0165cc80187ae9202cb9901e97a0e40597320052ec1c80b2e640087e8710165cc8010fb0e202cb990030f5d0405973203d2f41880b2e6400a5d8310165cc8014dd04202cb990029b60840597320053b40880b2e6400a758110165cc8050fd0bb82c3990021f617705873200c5f426e0b0e64008bd84dc161cc80187ee8aa2c1990070f1d154583320143f42ee2b06640087d85dc560cc801c72a8202c19901eb6a0c405833200574c1080b066400af18110160cc8010ff0cba2cb190d21fa1e64596320061fba4c8b2c6400c3e87991658c8050fd0eb22cb190030fdd164596320043ec3ce8b2c6400c3f749d1658c80187f08ba2cb190021fa1c74596325d537c12e6b2c6400a77815cd658c8014e902b9acb190021fa1f43596320043ec3e86b2c643487e87d09658c8010fb0fa12cb1903b8b109425963207537414e2b2c647ca6d829c5658c8014bf06b8acb192529720d71596320051f420e2b2c6400a3d
  | 23 => 0x8004002009002001c00c0020000000000007000800400000000000280160000018018002004019000c0000020050038004000000801400a000000001000a000000000000000700c0010000001006000000a001000800c03600b00680000040010008008008008009003c0140000090018014000000000c00a0070000010004000001000c00000c007002400800000380080800010018004004005003800c0800000008000012006001800001200900e00000060000048024008001003000001e016001800400200a000000401a0020118038000001000000002600200b0014002000003801c00200e0098048002004000800401a002000000800a00d0018008016002001801801600100f000c000002000003c0260000000004022005000000000602900d803001a002007008001c0190038000038000004802000000900d8000004007000000c00c00b00580000020110018050014023000800800a00c0008004000004009001400a000003007400c0040008000030007004001c01000000000080100000008008018003000000400800800e000400400400c80000100050030004000002000000001000000f8000000003000008800400a006000000200000080d000e00100080040460090020014002009000003801800000080900000040008020000000001003402a00000b002000200201a009401e00100000040000070000000000000003803402200c00180040340080018018006001001000000000000100cc00e001008000c00c002006000003200700100080000000008004000000000000c00e03700800000120000008000000009000003c000001000001401e000000001001200e00380140060030008028000002001003003200b0010004000001004000c00400f0000008010001000000c000008001800402a011001001c010029007801800a001005002400400600200000520010008000000003001800000400b001803401200f001001c05c006002004002c00000100000040000018010020039000006001e0110070024004000001009c0020090030038000007000001802a0020010000000003000800c02c007004800c000000000002c008002000005802e000001001c00e001007000801200a000000001000400300200060000000004014004000002400a000000801c000000000800c002001002801800800300100000000050008004008002002000003200800900140000010018018052002006000402e003001800400002c001807c012011002800000a004002000800a00000200000000050040030000002003004800401f000002000c001000800400c000004801800000200100080060030000154002003000800c00000000400300000000020008006005000001c00200000100300000110020008000003000004800
  | 24 => 0x6953a58e46e1b40cb44ed5a08fac0004b4461073d4428195d0a4c41ee69859b9e604921ac304a8a470682a0061c4495ab802cb1af0a469395bf9598ce441e1a3a59800021c3b28f24a1c1d651a1800c503bd00f94480eca56394000090088203b9bc81307fe0d80000000000442800000000000000012c2b1902d990563884c50e19300007e80001b54000a260002bd8a8a1190000000a6c0003be80017c80001998000f460650001d197260003f4a09c808bb6149800060a0003ba9abc00018326a00015de0000000f14000000000000101c00013f989cbfe0002c5ac785121cb0fc1b9c20400059921ac00060c0000d6c1425c012b11a41fcb890001e34d9e636000000000000051b0ea0bc40f02a89e4000000000000006ce00000005c117823e064000000034c0000000000000000282000000012c99880000000000f4514c00000000000003823aa914c16a5b70000001796000581000142c46f37180000000002ea9c6406255a3f8aaa88d40005192708e127ab1d495d800031f28f9ea800014e0001becfec58a0b91f852dc0004c981b94d080955109815a296a42c1ee54c840938018149b8ae300011e49b000000011e95207a13e01170a5600031495b81d2b670001f9465e68049d241c3429365ada7c0a8e0c51cbac9938a00007c87345ca94a19a2fcc6b825d1ee00009e60000001f2927817d0ee8000ac01713d02c0c62ec3c0d113a8308bcf00029780004bd48287b56d6b752c4000054657428200000000000f495e841600000000007303f60000ba15e61750001bd866e4fb43aa5a066400000024fcd4e89411ea7350f83f40c909103162320aaa73960e1c10c11c60bf829b000000000001600000002ba0002671d70cf81f04bc2929800b9451b80004a288b011996c0003ab1b30bc47708f039f12a57da1b45a31eecd8c62e36421cd21659a481840c4cc3e745108ccda204216b00002b44320000fd446ab1a51380000de6132370244000000553000000074200020bc000000000000c0010008000000001000801c0240040098000004006000800c0040000000014002008001000000000300200080040130088004000000000003001200f00c800c00a034001800400c000000002800c0080028010000000000800403600300f0020004007002800003c0010008014004005000000000800000300c400e000000000400c006001804003001c007804401a0000020000004003000808c00001900300040020040020000002001002001000200400000000000010000010004009012800400a00a00100340020000048040000000000805001e028000804c03000d0028008006003000800c02401600f0000000008007004c03200f000003400400c0000008006004001001800400000380280140080000008000000003000400000000
  | 25 => 0x8200013d400000035e89f1328a7a5fe0ef0000b745c5a2e800000000000000000005ac000049a00000014a464a0b62148000c2c0f5282a48576600000000007ee64d1ca800000075b000000000000000000000008070002c4cf508ce15600000000000000000ade1ba0a5188cb52000019a494a660001e19b5d0c812350ca744abe80f1f1a4607da77000011340000004cc1bc425e23b5e81e9c628693158a0f00000005f08000a0e01d4998588eec36e08e94980005840000730000000000273d7f453523e89856d85985609fa90c400038b1efcedc0000001e9183c3c43bc8a445081862791fd06a87990c6804d1302cf2222434000bff1b500841162c335c0000b5419d452874578aa7939a16649c0a3d054aa39782a4920e165406e9760571b847e45f805fad88d7e496515abc800074507d170d6d29f854008c082c5370fe08f1134aeb47da62124c3bb41223a820a89c5eb1f3023c22d42e1038b047365168b8150aafb5af0510c5698002913ad1da6d31db05e8bc60350d29c708f84631041778ebe8df2fc82acd66c2503381545c6a312080f607deace27c0a7cd1c4334d22e3557a4174ada9841de29a129a5e924811b56d92e94e0542395260528c2cc34307409f240f06aa0c887e34b27babf869e3a23f000002a88362d380015b813d4f1aab0fae35109a1bb8e16b091aba2757204e60001c4916c52019c87383385a00001bb58845d233700a0d148f402e8ecd514a912c0116096e107399823d4e2b6500181180966202aa0350efe057609a6ed2ba00054580005f01c4000071522e8c80ed8ff918e5e803d800102e08229f1921744a501a42b900000004f70b5d32000000000000007c600004fc0fa00000020a400011a1579c1517c0000000000000bf95050144000000000000187a00051609dd39045721380013800003089c7d5f481d475a7417d01180001e4c00000000000000004fa02393a041ab24030933cf9220904faaf04e08bd0c80a5d64009a5a4a47cab884700a0b00ea266733a10f89de2fd1b12839836361000000068a2152dd99c4c4c00029880015360cc0000000d36b81066b02514e19b0001f2c000a4144b2614000a6a4a5907d0c000000023257c62ed2d888a000000045a800024069647a800186043735900000004c848d10f0fa25b05ce9ce553064f2c7985d54879d18eaf8095051815907d42186702430ad11ee81e2e402c0e58bf500020b0882b2b00585183006c9460800115c23a08e041961c7501eb173cd761f152c80004de0155e40ffc54800020cb0b40000005ee0000000723102006d30400047e00002dc65e480000136c1bb4f38000000000065800000038a0240000d3a5f3121afacd2a000000000000000043f800052a00000003f0c604e34a2192800044023580000002fb546000117ea021e61a
  | 26 => 0x1380701fb16d08745c203660d107455244236d896c000a122c6a5ec8b62ea0000e852986df25d8000000000114ac9570a586000000038e1ea29d11c418c3364c8a8114a80003cdae5d05614200030b81da90c5f82f4c3140001ea00108482d5135000144018e000198014a1e73c487acd9873d18da374ec07710f7258110635229a0000b8c3a55a115e56105655d300000000006190db400045a0002cf8f8e835296ac295d472f0909958be4b832fb821d5f844e00000017de9300000bf88d80000e49368b22049290ac54380b5452f80010d45eb0000f3983849938619ec00099a4d62c6c6e8b0d59aafd0cf26f30d7078c7bc98b2a02b085a20004360001124000286964c00000048a95100001e04cf13f1876afd27e8000cf44af0002d0165270100017d80000005e50ed50dec2a4eaab40c0600046221980d4a352182c008626f930080009b28e400000000005fa2809d24f1e06b00009d00001f41be80000000005f110d48c80001b9821922404136d24780004003638000e6a0005a716f800001236f1574f68b523e700000001ef00000000007c500000000000001b28b080002720002470000000381000170c0003e425b400032d000134c00013c00027bd370a9941f0fc10a08935468e2c3bebc625e2b182d07471ac23cc97016100f1004a0cbcc34ba0185e054e3f31704dc09533012d20158ad621a02cc6e28d40499e1ceba09441004cca44145454a168c302e417e1ba41880d62889fdc87015706b8fc41b4797348836d4fa43d10b036436c6732250720f7063e5a29750e3600025f956400000020413d80005cd000303c2be4490000cc119600000003c4000000503885cefc9e033f8ef92ee6aa0bf0000af6000000253d07a000000000025000000021e473463301f25e400085b5a6adb4194c210df000142a3564912dc40000005a880001920005b7a0ec000539512286d0167203128214da47bc32914a0a2897e3db154d4cc5b33308c303a600818c0c24c34ae14eca8ec2c84430de112000017400009a400000729e28b80000000000cb000087200000000c64a01eca824ac454600030e800002c2f487617cc7c3431800098881c43b125d0fa7fd53582750244b2212857059619e1d000001d40001250a653502f437d153c0004ab252aa20ed20002f30a0061eb2f1bc21000000000002f7981c8cf277152078c5e42ba98905fe59759a2f38dfc29d22a2bb47620920f12698d5c61057a1bf01b85242a92684a703d55cb130c7328d937817d47641ca459800050434d2f68e5800061e0002a59240a953d7030d6d4b78484898956c0260d3849018074e442102d7fab4f4ff21a41fa35d1229d3d37c9d200029a51180000000001818b0414302c40002d20610000cc60001818e990e234203f000000000055729c95aebbd37580000006
  | 27 => 0x646000000177c00063900000000000000001f3c1e60002ed244c0000d800000000000003ee034800000000016b00000000698000c086c14d180000000004062988faa06607f84d862440a30e800138e6382972b0c5440002e4800143ab0f00000011fe7f020d0d0cc149234669454d88341164122c0a64455bd06540000dd3c21fc800063d000149cb0a2b60000bdc5560005539aa098aa65428af440003a34c51b885300af00027a414e12b2ff081c8e83882ac1b611f05d35cd8298e0c00000000000226ab4c2000000074a00016e0ef8068000000152e7835df80a521e6f40000620d1207230c8a200004984be000088c1f661c95c95460884052908b5a00031882658020005c898fc46c9ad04f000045c00011bb104a160f61178001868b3957b8000ee883a000000167a0000000000dee9ab03d07e800099d3040000f8226307c02040008fa4cb0000000a9c00000009d89691261f7565aa330000000f2ca4b00020e131e3af2688c4d34027a5c52440f22b795498970ed676c451aed044ab1818694bc2dac025b09a9473a5e74d92a7d4b82dc2708b04cea33a046000092200e0000000e4878a5ee9dc82984c61e39d882ce2d455da0c40009b7203172c0000000000c44b9800021d0000e80b7b000000062c00023bab747d284a3aca34d7702540ef2c2d4f6b3f5ed064ce5a25052c1c551025b60000e9c00076100000000006e518d27d40004c9543226586e9f40e908000003224f40000000987556894873cbb527480e54061a63db91885429a701d2ebd77884e5af845905c88e10ca4bd6c69e539e099d53c187000226d1ce95900020c130c00000029188720eb578a9f0cde24631605350ca0000002a053c81f90c88e40e201b212c2554370acf0ab1c749ca849000211915e9da5578438a1020155080004ca92939f96995e034a27f800024e9bc31d80010340004eba8e1258c380000000d609d8477a43840600000022d0eaea0b174a278fda00000000016e630b1c89fe800062f00000000000000b180000004070d9afc8ecc130345ab0000000000019dc0009b11f99bf41761220b300005a05563dd00004186e80000000b6a0005a62385752956000000021e0003d30000000a742c180000304a22b1abe48a27770ee00004627e340088d004a9511b6000143e52c4e21f35030b4b3362a946ec21325628300002f315c00fcec6825054235878200009280013fa465162132835ab8c18308e17dc8024cc99f8c687eb2bb95f92bc6a41418edc1dc04f142ab7c63878100000018480002d59838ef44a700001c400245200000000008f6000303417a000195a8bc442b843f10000b2474b0002b940008b74488000fb40000bc8e5132e0001a027ad82c00020a80000000004f30a98ad41430000c900000000000
  | 28 => 0x1f7d22cb8800000000001810002c8463ca7702004c400011416da77c000b2c000310c00015224e8001784000000000177c02a49903955c000000000016e451e365ac5c000a3014f10986a00000000000000000000000000000000000004540004650e4cbde000000000051c000000163113e1f700015f40000563110f4000008e0000b8890800032e25d46d20965973110eda00026b857900a6a050a06d54ae4db000142423ebdb14089a0000be95ea9f4d40c7223b4223ce0e0e8000121d8460002c8145ceb400023c02f8000a250000f88b3800056c00000009d4000000000092800019e00009f74c729315c495f1942590e2e00002a00010965b200021c02ec00059800017ce8b100000000000004a0addd3a69920001dec0000002c080000000003c126953da5a512fa8780008ad00013c40001690d18bbd23248c11624a94303531f40c815dcacc15e0fe90ee5e1480904c33406d5d0090512e5dd31521840000006189b743563895b7001471cae804e29cd088be50ac254878468739727e45244600001b0025207442f24d40008873f99be16200e4260217c00000058e8001210000381ad40db80003349d90bb20005d80e6c7b60b8201a8fd6f80000002adc00000032a80000005570c2928c00049200000005380000c600c000048320117440003cd0a3818855c73745599450a68d500000000002c9193000005c10b000146d24e2ce4e5800000085200000d08241e852a927c80a0003c580000000a225713d0b781c622f853d5b244f00016d00000a31bd000168624e26f1ce80007b10c79270f88c2c5aaaacc8964cd2428d8c1d81d5389843440a93e0a9aaad2760005ec27c4dc8000000291c6c0bac3408440ffe000617abfd5941b70000000004a0f1b21a8903625a2308a9c0003d73df25fd05a2bd5c92a10d6c0ad000215400000044400000008b800024b45940000000001386815386925000071419fa46d3928e8424000000000000015ac07a4cb0000fb8c6e88a00016fc0000003ec99642724d503c8000000c2b09310800005682782778100c10258953444c0430101e540001980000000d6237b3419f6c0003e0088800000000010115c4000c281fe00001c089044aa394bac00059d1a3400093832191c136838407a19b4c0e55b000090875887e5a503ed66c2ad4d984040f80000e18d64000466163a8a0da8000000020c2d675e4852afca389aa619a1b40e074353687946f800030308fc00000000000010ae0000001d115a800000019148580002e280004ec4b65eba76d74660b566ac8cac827b4ab9b990a87fb35a26a550448d1d6a8048ea8c5096176c9ce1f2421994c01e1171b580b52c487b4a1a1d05ce2755fc000118008915d2774b3aa7820da500000ac908027848ec00056380001c48aa0139b0cfb010846180004da
  | 29 => 0xa9fa2f82d807024903d92eec00074841a2d6879453f2c3ada064ec08112130982250a00000008aa00045d80011fc28b000000129cade04db02d3727fc5491aa48a0965234000147c0a04e52a1c0000002d180000005fb000000178074c2d21ce15a400000027f04aea944dfa4f4a96a226038dc84c8a7e16e8000cca00000023b0982a833f39ae48ac2b90000000000826113800000000036c973961894900014c838400000015b40009ff0de88609be7524fb15c05203cb51180000001095ae92552de8e65be87652d68cc5c780007b40005ca8c4027413523f08e531a56742c800018200034fafdc9c813827f000101a0001970fe05a60000000000000000000000000017c00000008ba00023d986d8325780000000d840002f299ac6be0005588000b3ea4d4fd82c84d8a4e19501a574a00060f984800065805ba5f40561af0fea9113823d3111025d1dc8e36020cc51c455e55d17c5814a4f22f24dc7f23020bf97292e470a0a88090a004720bc093cc3e4113c02ad123a0000002b689ac5ee5c700000003df241126910c0582fe92840000000228add56a0002d10001072bc700021040009f234201913c4000521ac441ce2105ab80000000df0000000d7c73002c9cc4cc875424705bd76e42b495adf8d9463a0001ef4e4c1a91bf1a20ed449b307944182e676422b0517be31910912251e47ee38412e441430e42e8e151b49502810ee807837f47c8fb01bc04c1202088d20000474a8a809ab76176108c9980e623991304f0725115a0fd150a1132114a94fe0ba1d52380560c204501a1452c1ec000033cc1a0002ec2f0cf5800000004b80006ec0a000000009470a08bd8608ae63270000b7400017726bd6448112168181572a514631f088420000000a3c00c69460c1cc9050aa84d8000073e00039d8b7c92647f54d0c053d404a3d7978019c74d2eb8cd57f67ec15f038cb5e000000000000005c17586252c60000000001020b3b00000000000000002c5000000004500014c656100014740001e12fa29d8bb87f909f06640007d653721a03cc00a3b9852187c61c5240e490286ef1e4283525c8d03c900011b083712aa4443544aa0220658d241fe2a4a9156c80095e21c78000000259844920437721400009ba00000019a06de0000001a8573c6b502d00007a437052d2d590100002ca294c3c85410a5995c2ca3554c1800168e0005ff0000f3c13b1388000362000000143c0000004831e382085134a11bd40be032421235c6140e10002c48e520000002a8109e9045580fa84900003a0aa24000a002a60000c78000000284c0001150ca2814b507780000a50e4e00040204a983a1b92e10000000000068185542e68c0002c9c0f0b2861a927986c0002522e1d7d80d141085ec0feae71032fc4ad85a10000000d1e7b34b62520000000000
  | 30 => 0x4b3a2e555284d000000000000009b800000000013c8000f0c000468aeb80004e20002c152280000cba2b07720000ea0000ca034412585405f435e446805d4d824704ab019474b1f0001c3c000a603ca00000003070ed0b14f5aa522cf0eb804495c3959e9582a699574800135c000000000091e75800000bc59a1a025a94ed7a48a401d82a854a06c3c4219d4b666a0001e8800094d409800037e00003980000008a1000000000000000027700000005809ed52e67b015f98853740193d4800000000000018d467628a00000006b47e45c1000000000000000000009b51a4aeb4a065ea10f15fc422a5d00000000000000001c6818e20f5dd116400054a0000aa80006140000b9966679a4c4800103e9bd0a4856d7548b05ac82f158a7d45b300006105c73c2b098c8cc291d20001688acb2c4943159033c5d40e013e63874e6200d0f465434f00003e664932380013188b220c0a307f6ad511000000000002dc84b4000a39387086c9600000b00ad5478b063a98000dac0000ac8ec0428c0321b2cc57320005620c8422679f21d883800042f00000000007de3222fd8cbab9f00014f44464d2440145973400049a0de57925ae137000000051900030148445c417c8ce00007f5000000000000016c80004bc3e10cf9a8c00000000009ad88038610f9adc0000002cd800156400019eaca800033e00802d00000001c610500005732408000aa06a600d000182400000000017645d0150075d04640c09925d0348640000000173800021717b133ebb10001ab05bc530194abb01727560ff80000000001ee80017720004ce122814899b15405dc9a057c03aa3c4cbea1a046a05871a9705ea1034038a67508000138c0000b991b4aaaa404000000d7434631906a11b65bd15daf3458c3bf34e2ae06d0a6f1ce2be07c84be0002e9184e28d3e820cccfab98547a1e00006ad3b392991fa88900018b4dfe488000000000005e1da00007fa3e515981400006cd5d3800050e6ea00689cc000995000000010838f46f000060000038200000000001f30000000b5c13f2bd51a47d25d58f00a862d859c2dc0120c224eb25c40005255f51b396a6bd939088685ea00059e146800000013e80012a816a08500001e4ad34ad1fe12b04c70000000f383cf0000000c969ec1a729d40004674370c54fde56958b000000000022385b128a9a255f1dbc6ea8563c6000187e00000010a8ccc0000000bc8d8
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x401625919d154588310060b61d54101620c401a25546044058831007039d67458a320c40144f97551628c8310068a55182101600c401629921d154580310058c64474551600c401a315460742580310140fa6374593654840183b7420164d95210040fe6174193654840103f985d074d95210060bdd18210365484018377460440d95210058624164553634840121d9421572d8d2100487652859c3634840181d8755040d8d2100683551821036348401a155460440d8d210060b5c984194634840181e766106518d210050765e64550634840141f975915418d210058624164550634840160d941957218d210068555181d086348401a0d5460b4118d210048765085484634840181d875504018d2100683551821006348401a15546044018d210040f660655d2324840160d94194638c9210050d65065dc5324840103d94a1b754c521005856506518f2148401a295460840d81210068c55181103604840141d94196739812100507650655ce604840141d949d76398121005076527518e604840103d981d065581210040fa6065dd1604840141d94197735812100507650651cd604840182d825d470590210060d605751c16408401a0d546084098c2100685551811026308401a0d546084058c2100685551811016308401435941d776484210050d65085dd92108401515941d473484210058a648745516008401631911d154580210058c650854856008401a508520d21580210078855142485600840181c7361075587300140f2617455161cc001435941d561486300050b64a70dd7644c001435919c375d91305e686a0e801d7644c001a198360075d913000417259845d7324c00181c8619175cc93000417259845d4314c00181c86191750c53000507259855d0314c00181c86195740c53000703194645c8314c00144c96551720c5300040f65287d95214c00103e981d764485300040f65087595210c00503c985d154587200050765075dcd61c800141d941d4735872000e0d21d54505618800142d929c375d91200050d64670dd7644800103e981d764485204b60e201755c5640812da308055141584204b58c24174551610800103d981d56448420005076507598d210800141d941d563484200070c1d47458520080014709755161480200050b648705d564c4001435911c1755931000545650751cd21c400103f985d074596100048765285dc9638400382c875514258a100040f653865d7328400103d94e19758ca100040f662655d2328400143594997714ca100040fe5186dd5318400103f9461b75486100040f65087595218400141d94997734861000507652651cd218400141d941d66348610005076507558d21840010cd981cc62485100050d650751d92144001515941d473485100140f26174551620412d438905d15458810
  | 1 => 0x6a0000090007d00000b4153f8781c00000005e000000000042e800006c002200016001304c00068f0d44232800008618048305522900903b038a01406169c4944b34050005e00000000c38000007e2794900003900000342202c4e00438000083001407e0000214747c39950006e198a4ac5320868ec25082080000001a4000002800004e101d0c6671b10d022b37984103e109ac0019000a800093b86c5c84000b02e7901800640f2c80000002c08cbe753d8dcc44718934b61f0004c7a00000003a1100000004630198da7a2495c02020007000781c00000392e000c85111000141840040428000808100000200c00000008340000040004000014080000000c281800184c001810100000000182d7460840597320060d5d18110165cc801a295460840583320068c5518110160cc8018357460440596320060b609751c1648c801835756047059232006071cd841d5610c80503c985d154584320050e25d54901600c80503c985d15458a314b50e24174551628c40182f7460840d95310060ddd181103654c40141d9421676cc9310060b5d182101650c401835815d470590310060b5d5821c1640c40182d8755040988310068955181102620c
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xa846908520d2158021
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x5
  | 2 => 0x6
  | 3 => 0x2
  | 4 => 0x1
  | 5 => 0x4d
  | 6 => 0x4e
  | 7 => 0x4
  | 8 => 0x94d
  | 9 => 0x94e
  | 10 => 0x124d
  | 11 => 0x124e
  | 12 => 0x138d
  | 13 => 0x138e
  | 14 => 0x3
  | 15 => 0x8d
  | 16 => 0x8e
  | 17 => 0x150d
  | 18 => 0x98d
  | 19 => 0x98e
  | 20 => 0x128d
  | 21 => 0x128e
  | 22 => 0x150e
  | 23 => 0xcd
  | 24 => 0xce
  | 25 => 0x9cd
  | 26 => 0x9ce
  | 27 => 0x12cd
  | 28 => 0x12ce
  | 29 => 0x168d
  | 30 => 0x168e
  | 31 => 0x20d
  | 32 => 0x20e
  | 33 => 0x154d
  | 34 => 0xb0d
  | 35 => 0xb0e
  | 36 => 0x140d
  | 37 => 0x140e
  | 38 => 0x154e
  | 39 => 0x24d
  | 40 => 0x24e
  | 41 => 0xb4d
  | 42 => 0xb4e
  | 43 => 0x144d
  | 44 => 0x144e
  | 45 => 0x16cd
  | 46 => 0x16ce
  | 47 => 0x3cd
  | 48 => 0x3ce
  | 49 => 0x15cd
  | 50 => 0xccd
  | 51 => 0xcce
  | 52 => 0x15ce
  | 53 => 0x170d
  | 54 => 0x170e
  | 55 => 0x98955
  | 56 => 0x98956
  | 57 => 0x128955
  | 58 => 0x94995
  | 59 => 0x9ca
  | 60 => 0x9c955
  | 61 => 0x9c956
  | 62 => 0x12c955
  | 63 => 0x949d5
  | 64 => 0xb0955
  | 65 => 0x94b15
  | 66 => 0xb0956
  | 67 => 0x140955
  | 68 => 0x95415
  | 69 => 0x99255
  | 70 => 0x99256
  | 71 => 0x9d255
  | 72 => 0x9d256
  | 73 => 0x168a
  | 74 => 0xa4a
  | 75 => 0xb1395
  | 76 => 0x138b15
  | 77 => 0xb1396
  | 78 => 0xb89
  | 79 => 0xbc9
  | 80 => 0x98096
  | 81 => 0x98095
  | 82 => 0x150995
  | 83 => 0x150996
  | 84 => 0x1609
  | 85 => 0x1649
  | 86 => 0x151295
  | 87 => 0x249d5
  | 88 => 0x9c255
  | 89 => 0x249d6
  | 90 => 0x9c256
  | 91 => 0x1449d5
  | 92 => 0x9d455
  | 93 => 0x1449d6
  | 94 => 0x9d456
  | 95 => 0xcc9d5
  | 96 => 0x9ccd5
  | 97 => 0xcc9d6
  | 98 => 0x9ccd6
  | 99 => 0x1709d5
  | 100 => 0x9d715
  | 101 => 0x1709d6
  | 102 => 0x9d716
  | 103 => 0x1789
  | 104 => 0x130c
  | 105 => 0x17c9
  | 106 => 0x134c
  | 107 => 0x145695
  | 108 => 0x169455
  | 109 => 0x169456
  | 110 => 0xcd695
  | 111 => 0x168cd5
  | 112 => 0x168cd6
  | 113 => 0xb0215
  | 114 => 0xb0216
  | 115 => 0xcd555
  | 116 => 0x154b15
  | 117 => 0x154b16
  | 118 => 0xb15d5
  | 119 => 0xccb15
  | 120 => 0xccb16
  | 121 => 0x15ca
  | 122 => 0xb0cd5
  | 123 => 0x15cb15
  | 124 => 0x15cb16
  | 125 => 0x3ca
  | 126 => 0x164a
  | 127 => 0x155416
  | 128 => 0x155415
  | 129 => 0x15d555
  | 130 => 0x15c255
  | 131 => 0x15c256
  | 132 => 0xccb55
  | 133 => 0xccb56
  | 134 => 0xb4cd5
  | 135 => 0x170b55
  | 136 => 0x170b56
  | 137 => 0x17ca
  | 138 => 0x14cc
  | 139 => 0x3d455
  | 140 => 0x15d455
  | 141 => 0x15d456
  | 142 => 0xcd6d5
  | 143 => 0xcc3d5
  | 144 => 0x15ccd5
  | 145 => 0x1715d6
  | 146 => 0x1715d5
  | 147 => 0xd0c
  | 148 => 0xd4c
  | 149 => 0x104a
  | 150 => 0x1049
  | 151 => 0x104c
  | 152 => 0x1a8a
  | 153 => 0x1a89
  | 154 => 0x1a8c
  | 155 => 0x2cc
  | 156 => 0x125396
  | 157 => 0x124996
  | 158 => 0x1249d6
  | 159 => 0x125816
  | 160 => 0x10c
  | 161 => 0x14c
  | 162 => 0x139255
  | 163 => 0x139256
  | 164 => 0x138b16
  | 165 => 0x1396d6
  | 166 => 0x138b96
  | 167 => 0x9395
  | 168 => 0x89d5
  | 169 => 0x9995
  | 170 => 0x9816
  | 171 => 0x44a
  | 172 => 0x449
  | 173 => 0x99616
  | 174 => 0x5ca
  | 175 => 0x5c9
  | 176 => 0x589
  | 177 => 0x216d6
  | 178 => 0xb15d6
  | 179 => 0x255d5
  | 180 => 0x25a55
  | 181 => 0x24956
  | 182 => 0x25556
  | 183 => 0x255d6
  | 184 => 0x258d6
  | 185 => 0x15d715
  | 186 => 0x15d716
  | 187 => 0x1718d6
  | 188 => 0x1349d7dd
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 2120
  | 6 => 5522
  | 5 => 3141
  | 4 => 137
  | 3 => 1
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
  | 8 => packedAt gbK8 (1752+((h/20+packedAt gbK8 (1612+(h % 20)*7) 7) % 75)*7) 7
  | 7 => packedAt gbK7 (86912+((h/706+packedAt gbK7 (78440+(h % 706)*12) 12) % 3723)*13) 13
  | 6 => packedAt gbK6 (288976+((h/1840+packedAt gbK6 (265056+(h % 1840)*13) 13) % 6627)*14) 14
  | 5 => packedAt gbK5 (198930+((h/1047+packedAt gbK5 (185319+(h % 1047)*13) 13) % 4147)*13) 13
  | 4 => packedAt gbK4 (9950+((h/45+packedAt gbK4 (9590+(h % 45)*8) 8) % 199)*9) 9
  | 3 => packedAt gbK3 (82+((h/1+packedAt gbK3 (81+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffc3c1e0ff07ffff1fe01c07f0cf887c19f793
  | 1 => 0x7fc01ff07f87807e1fffff803340f9c66c9fc
  | 2 => 0xf83ffe0007ff8007fe001ffffc38f1e3870e1f
  | 3 => 0x3ffffff8000007ffffe0000fc0fe03f80fe0
  | 4 => 0x3ffffffffffff8000000000fff0003fff000
  | 5 => 0xffc0000000000000000000000ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x4a40406049008a331320c4126041882c085391
  | 1 => 0x48800a903485051204a49502114029422c0b4
  | 2 => 0x9015920004950084440112a584283141850c0a
  | 3 => 0x4226e552d000012699958020cac0dc02d80f40
  | 4 => 0x843b399ca6e665c0000600c10fbe000377a000
  | 5 => 0xe7003018c0c44600111803060fffeff8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeafce8feeaece0feeafce8feeaece0feeafce8feeaece0feeafce8feeaece0feeafce8feeaece0feeafce8feeaece0feeafce8feeaece0feeafce8feeaece0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_16779
namespace PEqualNP.Outside.L_meta_16779
open PEqualNP.Outside.L_meta_16779.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 4 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 13 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 17 := block_range (n:=17) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 17 := bs0_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 1 := bs0_5_0
theorem alls0 : ∀ k ≤ 5, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 4 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 12 := bs1_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 1 := bs1_5_0
theorem alls1 : ∀ k ≤ 5, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 1 := bs2_4_0
theorem alls2 : ∀ k ≤ 4, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 4 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 12 := bs3_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 1 := bs3_5_0
theorem alls3 : ∀ k ≤ 5, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
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
theorem bs5_2_0 : Interval s5Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 3 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 29 := block_range (n:=29) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 29 := bs5_3_0
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
theorem bs5_4_96 : Interval s5Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_128 : Interval s5Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_160 : Interval s5Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_192 : Interval s5Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_224 : Interval s5Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_256 : Interval s5Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_288 : Interval s5Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_320 : Interval s5Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_352 : Interval s5Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_384 : Interval s5Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_416 : Interval s5Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_448 : Interval s5Atlas 4 448 25 := block_range (n:=25) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 473 := (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat (concat bs5_4_96 bs5_4_128) (concat bs5_4_160 bs5_4_192))) (concat (concat (concat bs5_4_224 bs5_4_256) (concat bs5_4_288 bs5_4_320)) (concat (concat bs5_4_352 bs5_4_384) (concat bs5_4_416 bs5_4_448))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_64 : Interval s5Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_96 : Interval s5Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_128 : Interval s5Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_160 : Interval s5Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_192 : Interval s5Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_224 : Interval s5Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_256 : Interval s5Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_288 : Interval s5Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_320 : Interval s5Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_352 : Interval s5Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_384 : Interval s5Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_416 : Interval s5Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_448 : Interval s5Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_480 : Interval s5Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_512 : Interval s5Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_544 : Interval s5Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_576 : Interval s5Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_608 : Interval s5Atlas 5 608 24 := block_range (n:=24) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 632 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 bs5_5_192) (concat bs5_5_224 (concat bs5_5_256 bs5_5_288)))) (concat (concat (concat bs5_5_320 bs5_5_352) (concat bs5_5_384 (concat bs5_5_416 bs5_5_448))) (concat (concat bs5_5_480 bs5_5_512) (concat bs5_5_544 (concat bs5_5_576 bs5_5_608)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_32 : Interval s5Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 40 := (concat bs5_6_0 bs5_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_7_0 : Interval s5Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_7 : Interval s5Atlas 7 0 1 := bs5_7_0
theorem alls5 : ∀ k ≤ 7, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_2 i (by omega) hi
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
  · exact alls5_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 1 := bgb_3_0
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
theorem bgb_4_128 : Interval gbAtlas 4 128 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 137 := (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 (concat bgb_4_96 bgb_4_128)))
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
theorem bgb_5_3136 : Interval gbAtlas 5 3136 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3141 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat bgb_5_288 (concat bgb_5_320 bgb_5_352)))) (concat (concat (concat bgb_5_384 (concat bgb_5_416 bgb_5_448)) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))) (concat (concat bgb_5_576 (concat bgb_5_608 bgb_5_640)) (concat bgb_5_672 (concat bgb_5_704 bgb_5_736))))) (concat (concat (concat (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928))) (concat (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)))) (concat (concat (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)) (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312))) (concat (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)) (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536)))))) (concat (concat (concat (concat (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632)) (concat bgb_5_1664 (concat bgb_5_1696 bgb_5_1728))) (concat (concat bgb_5_1760 (concat bgb_5_1792 bgb_5_1824)) (concat bgb_5_1856 (concat bgb_5_1888 bgb_5_1920)))) (concat (concat (concat bgb_5_1952 (concat bgb_5_1984 bgb_5_2016)) (concat bgb_5_2048 (concat bgb_5_2080 bgb_5_2112))) (concat (concat bgb_5_2144 (concat bgb_5_2176 bgb_5_2208)) (concat (concat bgb_5_2240 bgb_5_2272) (concat bgb_5_2304 bgb_5_2336))))) (concat (concat (concat (concat bgb_5_2368 (concat bgb_5_2400 bgb_5_2432)) (concat bgb_5_2464 (concat bgb_5_2496 bgb_5_2528))) (concat (concat bgb_5_2560 (concat bgb_5_2592 bgb_5_2624)) (concat bgb_5_2656 (concat bgb_5_2688 bgb_5_2720)))) (concat (concat (concat bgb_5_2752 (concat bgb_5_2784 bgb_5_2816)) (concat bgb_5_2848 (concat bgb_5_2880 bgb_5_2912))) (concat (concat bgb_5_2944 (concat bgb_5_2976 bgb_5_3008)) (concat (concat bgb_5_3040 bgb_5_3072) (concat bgb_5_3104 bgb_5_3136)))))))
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
theorem bgb_6_5504 : Interval gbAtlas 6 5504 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5522 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 bgb_6_192) (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)))) (concat (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 (concat bgb_6_416 bgb_6_448))) (concat (concat bgb_6_480 (concat bgb_6_512 bgb_6_544)) (concat bgb_6_576 (concat bgb_6_608 bgb_6_640))))) (concat (concat (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 (concat bgb_6_768 bgb_6_800))) (concat (concat bgb_6_832 (concat bgb_6_864 bgb_6_896)) (concat bgb_6_928 (concat bgb_6_960 bgb_6_992)))) (concat (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 (concat bgb_6_1120 bgb_6_1152))) (concat (concat bgb_6_1184 (concat bgb_6_1216 bgb_6_1248)) (concat bgb_6_1280 (concat bgb_6_1312 bgb_6_1344)))))) (concat (concat (concat (concat (concat bgb_6_1376 bgb_6_1408) (concat bgb_6_1440 (concat bgb_6_1472 bgb_6_1504))) (concat (concat bgb_6_1536 bgb_6_1568) (concat bgb_6_1600 (concat bgb_6_1632 bgb_6_1664)))) (concat (concat (concat bgb_6_1696 bgb_6_1728) (concat bgb_6_1760 (concat bgb_6_1792 bgb_6_1824))) (concat (concat bgb_6_1856 (concat bgb_6_1888 bgb_6_1920)) (concat bgb_6_1952 (concat bgb_6_1984 bgb_6_2016))))) (concat (concat (concat (concat bgb_6_2048 bgb_6_2080) (concat bgb_6_2112 (concat bgb_6_2144 bgb_6_2176))) (concat (concat bgb_6_2208 (concat bgb_6_2240 bgb_6_2272)) (concat bgb_6_2304 (concat bgb_6_2336 bgb_6_2368)))) (concat (concat (concat bgb_6_2400 bgb_6_2432) (concat bgb_6_2464 (concat bgb_6_2496 bgb_6_2528))) (concat (concat bgb_6_2560 (concat bgb_6_2592 bgb_6_2624)) (concat bgb_6_2656 (concat bgb_6_2688 bgb_6_2720))))))) (concat (concat (concat (concat (concat (concat bgb_6_2752 bgb_6_2784) (concat bgb_6_2816 (concat bgb_6_2848 bgb_6_2880))) (concat (concat bgb_6_2912 bgb_6_2944) (concat bgb_6_2976 (concat bgb_6_3008 bgb_6_3040)))) (concat (concat (concat bgb_6_3072 bgb_6_3104) (concat bgb_6_3136 (concat bgb_6_3168 bgb_6_3200))) (concat (concat bgb_6_3232 (concat bgb_6_3264 bgb_6_3296)) (concat bgb_6_3328 (concat bgb_6_3360 bgb_6_3392))))) (concat (concat (concat (concat bgb_6_3424 bgb_6_3456) (concat bgb_6_3488 (concat bgb_6_3520 bgb_6_3552))) (concat (concat bgb_6_3584 (concat bgb_6_3616 bgb_6_3648)) (concat bgb_6_3680 (concat bgb_6_3712 bgb_6_3744)))) (concat (concat (concat bgb_6_3776 bgb_6_3808) (concat bgb_6_3840 (concat bgb_6_3872 bgb_6_3904))) (concat (concat bgb_6_3936 (concat bgb_6_3968 bgb_6_4000)) (concat bgb_6_4032 (concat bgb_6_4064 bgb_6_4096)))))) (concat (concat (concat (concat (concat bgb_6_4128 bgb_6_4160) (concat bgb_6_4192 (concat bgb_6_4224 bgb_6_4256))) (concat (concat bgb_6_4288 (concat bgb_6_4320 bgb_6_4352)) (concat bgb_6_4384 (concat bgb_6_4416 bgb_6_4448)))) (concat (concat (concat bgb_6_4480 bgb_6_4512) (concat bgb_6_4544 (concat bgb_6_4576 bgb_6_4608))) (concat (concat bgb_6_4640 (concat bgb_6_4672 bgb_6_4704)) (concat bgb_6_4736 (concat bgb_6_4768 bgb_6_4800))))) (concat (concat (concat (concat bgb_6_4832 bgb_6_4864) (concat bgb_6_4896 (concat bgb_6_4928 bgb_6_4960))) (concat (concat bgb_6_4992 (concat bgb_6_5024 bgb_6_5056)) (concat bgb_6_5088 (concat bgb_6_5120 bgb_6_5152)))) (concat (concat (concat bgb_6_5184 bgb_6_5216) (concat bgb_6_5248 (concat bgb_6_5280 bgb_6_5312))) (concat (concat bgb_6_5344 (concat bgb_6_5376 bgb_6_5408)) (concat bgb_6_5440 (concat bgb_6_5472 bgb_6_5504))))))))
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
theorem bgb_7_2112 : Interval gbAtlas 7 2112 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2120 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 bgb_7_480)))) (concat (concat (concat (concat bgb_7_512 bgb_7_544) (concat bgb_7_576 bgb_7_608)) (concat (concat bgb_7_640 bgb_7_672) (concat bgb_7_704 bgb_7_736))) (concat (concat (concat bgb_7_768 bgb_7_800) (concat bgb_7_832 bgb_7_864)) (concat (concat bgb_7_896 bgb_7_928) (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024)))))) (concat (concat (concat (concat (concat bgb_7_1056 bgb_7_1088) (concat bgb_7_1120 bgb_7_1152)) (concat (concat bgb_7_1184 bgb_7_1216) (concat bgb_7_1248 bgb_7_1280))) (concat (concat (concat bgb_7_1312 bgb_7_1344) (concat bgb_7_1376 bgb_7_1408)) (concat (concat bgb_7_1440 bgb_7_1472) (concat bgb_7_1504 (concat bgb_7_1536 bgb_7_1568))))) (concat (concat (concat (concat bgb_7_1600 bgb_7_1632) (concat bgb_7_1664 bgb_7_1696)) (concat (concat bgb_7_1728 bgb_7_1760) (concat bgb_7_1792 bgb_7_1824))) (concat (concat (concat bgb_7_1856 bgb_7_1888) (concat bgb_7_1920 bgb_7_1952)) (concat (concat bgb_7_1984 bgb_7_2016) (concat bgb_7_2048 (concat bgb_7_2080 bgb_7_2112)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 62 := (concat bgb_8_0 bgb_8_32)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 12, 44)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 12, 44)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeafce8feeaece0feeafce8feeaece0feeafce8feeaece0feeafce8feeaece0feeafce8feeaece0feeafce8feeaece0feeafce8feeaece0feeafce8feeaece0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276813032 * 2 ^ 32 + 4276808928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_16779.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,2]⟩,⟨.or,[2,3]⟩,⟨.and,[6,7]⟩,⟨.and,[2,3]⟩,⟨.or,[0,9]⟩,⟨.or,[0,1]⟩,⟨.and,[8,11]⟩,⟨.and,[5,6]⟩,⟨.or,[4,13]⟩,⟨.and,[10,14]⟩,⟨.or,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813032 * 2 ^ 32 + 4276808928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813032 * 2 ^ 32 + 4276808928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_16779

open PEqualNP.Outside.L_meta_16779 in
theorem PEqualNP.Outside.L_meta_16779 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813032 * 2 ^ 32 + 4276808928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813032 * 2 ^ 32 + 4276808928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
