import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_16945.Model
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


end PEqualNP.Outside.L_meta_16945.Model

namespace PEqualNP.Outside.L_meta_16945
open PEqualNP.Outside.L_meta_16945.Model
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

def SBf (j : Nat) : Nat := [6, 4, 7, 7, 5, 8].getD j 0

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

end PEqualNP.Outside.L_meta_16945

namespace PEqualNP.Outside.L_meta_16945
open PEqualNP.Outside.L_meta_16945.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x3000c05016208120290e0020020000be43bc43bf42bd42bf41bd41df31dd31be40bc40de30dc30
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x1101808e29a852d52d06b0a098cb54840
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
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
  | 4 => packedAt s0K4 (212+((h/4+packedAt s0K4 (192+(h % 4)*5) 5) % 20)*5) 5
  | 3 => packedAt s0K3 (111+((h/1+packedAt s0K3 (108+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x7ffc0ffffc0ff07ffffc0ff83ffe07e7f33f3
  | 2 => 0xffffff07fffffff81f03fffffc1fffff91fc7f
  | 3 => 0xf81ffff81fff07ffe003ff07ffe1ff81e1cf9c
  | 4 => 0x1fffffe00007fffffc0007fffe0001fe0fe0
  | 5 => 0xffe00000000007fffffffff800000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x90c44621448941016524c8498123212c2711b1
  | 2 => 0x21088812091082280a41119224144a50906446
  | 3 => 0x52551240d2284d52a0a26a44cb419505618a98
  | 4 => 0x659a249483b2969cd3c8308772980619da0f60
  | 5 => 0x861c38e71c3ce7e71cf3bce063111861fdf000
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcccf0c0fcc0f0c0fcccf0c0fcc0f0c0fcccf0c0fcc0f0c0fcccf0c0fcc0f0c0fcccf0c0fcc0f0c0fcccf0c0fcc0f0c0fcccf0c0fcc0f0c0fcccf0c0fcc0f0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_16945
namespace PEqualNP.Outside.L_meta_16945
open PEqualNP.Outside.L_meta_16945.Model
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
  | 0 => 0xfffff03ffffc183fffe0ffffc1ffff0073f3fc
  | 2 => 0xf83ffc1f07fffc3c1ff0f03fe1e07ffaccccf
  | 3 => 0xf003fffe007ffffc01fff003ffe007ffcf0f0f
  | 4 => 0x3ffffff801ffffe000003fffff801f00ff0
  | 5 => 0xfffc000000001ffffffffffc00000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x210011842000200442601118c022310c01515c
  | 2 => 0xa225228c84a90941d0a90a2952145254a4c4c5
  | 3 => 0x454a45106952129c2152a052a540a4a94b0b0a
  | 4 => 0x4a7388294c1b5ceab41888833999c031f00ea0
  | 5 => 0x8c630e318e639f33399ccce0311100c1fea000
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xfaaafaaafaaaf000faaafaaafaaaf000faaafaaafaaaf000faaafaaafaaaf000faaafaaafaaaf000faaafaaafaaaf000faaafaaafaaaf000faaafaaafaaaf000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_16945
namespace PEqualNP.Outside.L_meta_16945
open PEqualNP.Outside.L_meta_16945.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x900010040001488288969d500c00034000241c015ae0c48e193c0082558a8ba1029d7a3003c10d304451f0a2ca96184cd874c01e0001c004d04009b653129ff43fe43fd43fc43ff42fe42ee42fd42ed42fc42ff32ef32fe32fd32fc32ec32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21ee21fd21fc21ec21ff40fe40fd40fc40ff30fe30fd30fc30ff20ef20fe20fd20ed20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x328a4000000000ce763c868007d00000280000120cc4e368bc0a313d0648c731218ca85b1f0e45c0025924f8780784c943c2991c9a6003858de752e1904a6e391401c58180d0ae1d418605a043f8010222200f4c22336108004503008003f000444c1b3100088682f05ca243001ac20003a0d900002a800fc0b350b06e1e388c83e000e1649e5d42930ac3a20834000a3d9c00000018d466001588476152f8010882100a818771c048d208138000200290a0b4090000c4c0428b47000342004682044000c000800042c2c20041000bc04001420042c1804d80020005c7934580c2adca5a1db54b43bb28e877551d0edea4a1db14943b7290876d5210edaa9215b94e42b728c856d5090b5ea8a15b14d42d7a1a85ad4350ad8a2a15bd4142b7290856f54ccadaa9995b94732b6a86656e528ca7ca8194f55032b7aa065ae540cadaa8196b5503296aa0656e530cb9ca6195b94432b6a80655e53d06baa7a0db94b41b6a9683ad42d06dea4a0db14941d6a12836e52106daa420cf953319eaa6636e52cc6daa598cf952319eaa4636e528c6daa518dbd4931b629263d5310c6dea910db55221b729c436c53886dca310db542219f2a0433d54086dea810eb95021b6aa043ad540865aa810db94c21b6298436e51087cca210db54021b7296816d52d02dca5205b54a40d6a14815e53102baa6205b94840b6a9081ad42102eca2205d54440b7294616d528c27ea8984f15130b7a92616c524c2eea2985d145309f2a0613d540c2dca4185b54830bb2886175510c27ca9904f55320b7aa641ae54c82daa9906b5532096aa6416e53c82d8a7905b94720b6a94416f54482daa8905b94d20b629a416c51483d6a0905b94820b7a96216c52c42dca5085b54a109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x8b03007180326a6480a0e5082ae02c124402a9600080601e090000140aa95874350b0c5350d429998754cca2d64947328bd9150cca2d6595032c354d42d06a461509418b590524c64e63d52218b592538862f64542218b596540862d6414c219a580530870d5350840c9509511022d6494a308b59053c824c635512099185544822d6414d208b590514822d64948208b59052c422d6494a10
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
  | 5 => packedAt s2K5 (864+((h/16+packedAt s2K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s2K4 (3970+((h/44+packedAt s2K4 (3618+(h % 44)*8) 8) % 161)*9) 9
  | 3 => packedAt s2K3 (1028+((h/8+packedAt s2K3 (988+(h % 8)*5) 5) % 32)*6) 6
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffc1ffffff81fc1ffffff83ffffe47f1ff
  | 1 => 0xf07e0ffe0fc3fffe1fe1e0f07fc383ffba4e4f
  | 3 => 0xff800ffff003e1ffe001ff007ffc03c1c38f8c
  | 4 => 0xffffffc01fffffe00007ffffc01fc0ff0
  | 5 => 0xfffff000000001ffffffffff80000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x10040044008000002002211108048844009095
  | 1 => 0x25189488650550960d20c8a2324112b89a464a
  | 3 => 0x432dad14a3aa93aae3117a855ea82b0dc38b8c
  | 4 => 0xa514a214a20c54d56541008653270116c0d60
  | 5 => 0x8c618c398c3319f19b999cce06204221f76000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeeeaaaaeeaa8888eeeeaaaaeeaa8888eeeeaaaaeeaa8888eeeeaaaaeeaa8888eeeeaaaaeeaa8888eeeeaaaaeeaa8888eeeeaaaaeeaa8888eeeeaaaaeeaa8888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_16945
namespace PEqualNP.Outside.L_meta_16945
open PEqualNP.Outside.L_meta_16945.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x15a51a440001000ba8003021b0c800002498503122ce212600aa352507813400000007c3800058022309cc8000015003c74702480080500000040401007043100043ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21ee21fd21fc21ec21ff40fe40fd40fc40ff30fe30fd30fc30ff20ef20fe20fd20ed20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x16071ba22d2783a59d05aca3a88e0b2d888f1682a52990129e180019910186002a80000000000a24ab032b80090014809713a720800415001f8d05000d95800e8aa900021f26a3118c1219011304909e9c800980001d80260024142297a18f88079b2c0021189a8ca01c1a2a280b868c8602005810a0818220280042a2c08110001813404785ae28003cea18876e5210edaa421d794c42aea98853e540ca7aa8195794f41aea9e836e52d06daa5a0d794e41aea9c836f52506d8a4a0cf953319eaa6636e52cc6daa598cf952319eaa4636f524c6d8a498db94621b6a84433e540867aa810d794c21aea98437a50086f2a010eb95021d6aa043ce530879aa610db94421f328843ea50086daa010fa54021b4a80436e52902daa52057d4d40ae29a815e53102baa6205b94840b6a90817651102eaa2205b94a30b6a94613f544c278a8984f950309eaa0616e520c2daa4185d94430baa88613e54c827aa9905794f20aea9e41ae54c835aa9907394f20e6a9e416e51c82daa5105b14520f5a82416e52082dea5885b14b10b7294216d52843d241084fd51109e2a2215f53442b8a6885bd4910b629221e9204427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x2080004e0a6c004c350d5210f0d5454c21ca95150087295454021d294d50087495354021c355153c82686548110
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 8
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
  | 5 => packedAt s3K5 (788+((h/14+packedAt s3K5 (704+(h % 14)*6) 6) % 63)*7) 7
  | 4 => packedAt s3K4 (2694+((h/30+packedAt s3K4 (2484+(h % 30)*7) 7) % 111)*8) 8
  | 3 => packedAt s3K3 (312+((h/2+packedAt s3K3 (304+(h % 2)*4) 4) % 13)*4) 4
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xc1ffff83ffff0f07f0fe1fffc3fff81e89f3f3
  | 1 => 0xfe1f0ffc3e1ffff87f0fe1c1fc383fff764c9f
  | 2 => 0xffe00fffc01ff1ff800ffe01ffc03fe1878f1c
  | 4 => 0xfffffe001fffff00001ffffc001f80fe0
  | 5 => 0xfffff000000001fffffffffe00000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x44020088040010008012024440488844009131
  | 1 => 0x88841110902a00283104208884111298324486
  | 2 => 0x144aaa290d548353888b54156a82a545858b18
  | 4 => 0x3954cc42a906a59d5aa11021b3270189d80ec0
  | 5 => 0x219888733198c9e66ccd993822040611ef6000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeaeaeac8c8eeeeeaeaeaeac8c8eeeeeaeaeaeac8c8eeeeeaeaeaeac8c8eeeeeaeaeaeac8c8eeeeeaeaeaeac8c8eeeeeaeaeaeac8c8eeeeeaeaeaeac8c8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_16945
namespace PEqualNP.Outside.L_meta_16945
open PEqualNP.Outside.L_meta_16945.Model
def s4K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (i*5) 5
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (6+((h/1+packedAt s4K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x1ffffc0f0ff87c3c3ff87fff8703f83e39f673
  | 1 => 0xe1f87ff00fffffc03c3f8f03f803ffff26487f
  | 2 => 0xfe007ffff0ff87ffc03ff003fffc3fc1c78f9c
  | 3 => 0x7fffff0007ffffc00003ffffc001f80fe0
  | 5 => 0xffff8000000007fffffffffc00000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x443004601210800c044811198118488c089631
  | 1 => 0x8844c882a46444c21a148a2248229331224846
  | 2 => 0x40911124028009144029204892482484458298
  | 3 => 0x9566624a8835566aae84089364b30119b80d60
  | 5 => 0x1984438cccc667b333364ce040c20621f76000
  | _ => 0
def s4Atlas : Atlas := ⟨4,rawDecor 47 s4Pos s4Neg, 0xfaeafaeaf8c8f8c8faeafaeaf8c8f8c8faeafaeaf8c8f8c8faeafaeaf8c8f8c8faeafaeaf8c8f8c8faeafaeaf8c8f8c8faeafaeaf8c8f8c8faeafaeaf8c8f8c8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_16945
namespace PEqualNP.Outside.L_meta_16945
open PEqualNP.Outside.L_meta_16945.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d02fca5a05f54b40bf28e817d51d037e83a06f50740beaa4817e53902faa7206f90e40de21c817e52902faa5206fd0a40dea14817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c53502fea4a05f14940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea9881be431037886205f94840f7290816e52102faa4207b54840b6a9081bf421037a84205f94440fb288817651102faa2207d54440baa8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30ef19661dc32cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa7185f94a30f7294616e528c2faa5187b54a30b6a94617e518c2faa3185f94230ef98461fb308c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c3bc86987750d30bfa92617c524c3bc6498770c930bfa8a617c514c3be6298774c530fd98261de304c2fea8185f95030beaa0617c540c2fca6185f94830bea90617e510c2faa2185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c83de65907b0cb20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53883bca7105794e20bea9c41dd53882baa7105f14e20bea94417e51882faa3105f94220fda0441f840883f461107e4c220f790441fb20882fea8905f95120beaa2417c54482fea6905f94d20bea9a417c53483dc84907b50920f799241ec32482fea2905f14520f790a41ed21483f680907e10120fd18241f930483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20bf290417e51082faa2105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43f681887e10310bfaa4217e54842faa9085f15210bfa9c217e53842faa7085f14e10bfa94217e52842faa5085f14a10bea8c217e50843f441087e48210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea6885f94d10bea9a217c53442fea4885f94910bea92217c52443ec82887d50510fd10221f920443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf288217e50043f680087e10010fb88021fa10043ea20087e44010
  | 1 => 0xe5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7215f94a42dfa1485ef4290afca3215f54642bf28485fa5090af4a1215f54242fca8485795090afea6a177d4d42afa9a857c5350bb8a6a15714d42dfa1a85bd4350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310afaa6215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332bf28e657d51ccafca1995f54332bfaa4657e548cafaa9195f15232bea9c65df438cbb887195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf29865df430cbb886195f94832ef99065ee320cbba64197b4c832bf28865f6510caeca2195f54432faa886575510cafca0197e94032bd280657d500cbf2a0195e54032bf29e837d53d077c87a0ef10f41bf296837d52d077e85a0ef50b41bf286837d50d06faa920df94e41ef29c835e53906faa720f754e41aea9c837e52906faa520df94641dfa0c83f741906fca120df54241bfa9a837c535077c86a0ef10d41bfa92837c525077e84a0ef50941fba0a83be41506fea0a0fed4141bda82837c50507f0a0a0de14141bf2a0837e53106faa620df94841bea90837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331efa1e63dc43cc6fca598df54b31ef99663dd32cc6fca198df54331bfaa4637e548c77ca918cf95231beaa463bd548c67aa918df15231bea9c637e528c6faa518f78ca31ee194637e518c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c7be8698f710d31bfa9263ef524c6dea498df14931f6292636c524c7be6498f74c931fb98a63de314c6fea098df14131bfaa0637e540c6faa818df15031bf298637e520c6faa418f78c831ee190637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510fbcca21f6194437e51887ec6310fd4c621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a43df53486bea690df94d21bea9a437c53487b8a690d714d21fb18a43f531487ee4290fb88521bfa82437c50486fea810df95021df2a0433e54086faa810ef550219eaa0437c54086fea610df94c21ef298435e53086faa610f754c21aea98437c53086fca410fbcc821f6190437e51087de4210fd88421f690
  | 2 => 0x1368000000f8fa83d0000c00007e000000a60003ba75d3407b0248507e86014463842a3c1cc0008a8ca4aa93d0180d2605889e04a2200685597c28a8a03690e4be60c1914336074510925106490002630ca000801aa3b894cb92453e095c719702b290489929168000000002f0854d3825264000582001b0000f8a13310148b781b4485fd280bc0e840c508010f44ecde16d1766f43c1cd4e6178b719f4640011f92f3d20005515418c229358b7304000000544de434ad9360005100003b25a3fd0b1a00002a07119541a0000202627c00114a5b00030cd60002402213613d2d20d53b1650002e40004e00027d24a070009d4efa223ac11c071ea05c8813093904e78d189db4022e04581617e450001c94907c81402900c028000000902582200034c34ccc10222e8301b94622c000001a84b2944840003d65f4000872ba8d0e194025c97026840466580000111ba310260050fe378f721a398650468e00b85691d80c1364987600f4861f00c9b80fa8e8000a60007389c15f0cc910001660009750f2650b68b0da1711282cc2b8711c81bc248552845d0ea0dc1080000019b3ce85d1284521649d370230440546d941190238dc96a1e24a12d1971b45d8b0a541f00ccb19190007b00000045c864d28b2000001020003802d40024608215800000362000f78001da9490891c0ce3c03b8d6072710059990e62946697e2463e41c15243e3ec681553488ad0e1114844e887a603cc2b0040d51345ec74267472090c315302e7b52584b3b2384648ae05e024ed24d3267e4b21ff184578a58ce38a524e907229c561041f81b22bcfb9a329a59c3105123074cdf0e71f83dc8e9843181d8521ba0e08245f13138223c1d1a93c0119261062344fc0ea7248e61c219b20067281e05816c6591190c2f21689621b23c898fd1ae3e8674ae1ab10c678039471dc004000043a0004c13c00054190281e074060081c03400058000300000c0302007014100280b0001f0241c048000100701c0101c01010000181000002088010003b03c010104903c28024040040001404000090501d0000002c0300c0300c02000010440509c0004c00044060283603c02000010300c0380a05c04040010240f0000000412000020080007c5b004040080000c1000c0700c040482e00403000080180006403034010001c0000003402030010000009c0a00801004020340b0180607003000090dc1a01c020180b018140040500015000000180000820000550240b0000000c0201c0c00801008000040a0000600009008030000c02c02038300440a0280003401bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877
  | 3 => 0xbb9ad00046c838f41ea9dc2e8ef1f44a84b89e37e13c001bb414078c509146a624c823e3845cc6a0ad31e1e4ea8bd00000000137000000da8f31126880a20b00018c0000000010800000224760e59de2689a4000001621acc020f0c20841a0810a07f00002d0006bc01000000795090c73fa2752b133494330c69481ca348351911400b0401e21a2000a79b700017d2f00034286029a624e86d8539f6302404909752d60004900004032d350002f43140c0000000d800236470000000950000011515720a00000000000000000000003f80016c0004d4820000008400000000033c5d09047a96009a4e0d02306fa0215207c0e22d40a040f08000003c815a712a07cc60a2f4c86140003f0ea3acff19200028d07168000000000933381900000029447c2ca401d44240019a00062c3600039e00000000000000000823a07184c86e1ec720fda3743a0009592240c1a5381b3000544f2266062000851560000004c0e91388c0e382a1807a06ba27000
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x931cc26e62d52309b58b548c26e62152309b588548c27661152309d584548c23e6494a308f592528c32e6494a30cb592528c36a6094a30d394b308c23e64951308f994544c31d6315130c7152434c25c6550d30c7152324c29d640c930c7150324c2d5610c930b6980324c31c54cc530c7151314c2cc624c530d5145314c2ce628c1309798c540c26e62150309b588540c27661150309d584540c25f654c0309ed95300c32e62953208f99353c823d64d4f208f99053c823d6414f209d98453c82756114f20cb95142c82cc6350b20ab59032c82e5610cb20b318d21c825e63d52209758f548825e63152209758c548827661152209d584548835a6094e20b658c40882f16110220ae191308835a534c220d394f20882ba64c822097d8d544825c63551209dd85544827461551208fd91534823c6454d209dd8553482746154d20ba982424826c6550920b318d424826e65cc920ab59032482e5610c920ba980324823e64145208f590514825e63145209758c51482cc63485209e99740482d96310120ba98840483a94210120bc58440482ea628c1209e19530482b8644c120f20c930482ba64c8120b398e204827a60d50209798c540825d63150209b988540827661150209d584540826e62d4c208f990530823d6414c209d98453082756114c209e980530823e64948208f592520825e63940209758e500826f65480209ed95200825e63d53109758f54c423e64d4f108f59353c426f6254f109b18953c425f6354b109718d52c423e6414b108f59052c425e6314b109758c52c42f06050710ec50740c42f16110310ec90440c425e63152109758c548426e62152109b588548426e62d4e109b58b538423f6454e108f191538425e63d4a109758f528423e6494a108f592528423e64951109ed81544423e6515110cd584544423e6494d108f592534423f6454d108f191534426f6254d109b189534423e64949108f592524423f64549108f191524425f63549109718d524433454905109d195414433854881109e19520443385448110ce153104425e63d50109758f540426e62d50109b58b540423d6595010ce181540423e64150109798c540425d63150109b988540426d62150109d984540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c108f990530423d6414c109798c530426e6214c109b588530423e64d48108f593520425e63d48109758f520426d6594810cb952520432d5494810d394e520434d5394810cb951520432d5454810d394d520434d53548108f990520423d64148109798c520425d63148109b988520427a6014810ce553400436952d00109e59440043695210010cd55310042796584010da54a10042776544010cd551100427b6544010ae19110043695244010
  | 1 => 0xcb365494432cd552510cb365454432cd551510cb574354432d510d510cb573254432d54c9510cb3a5494032ce552500cb725194032dc546500cb3a5454032ce551500cb725154032dc545500ca7a6094b419e58252d069c6350b41c794f41906b66190d41a718d42506b46150941a798e415065e63141419758c505066e62141419b588505075a6314141d658c505073a4314141ce10c505076a6214141da588505073b4214141ce508505073a411414197d8d521065c63548418fd9541106b860504419dd95411067a60d53319e58354cc66e62943319b58a50cc71e548ca31c7950328c6d5610ca31c7953318c66e62951319b58a544c66f62551319b189544c67b60551319e181544c65e65d0d31b5987434c63e64149318f590524c67a60149319e580524c72e6414931cb590524c74f4314931d310c524c7656114931da980524c769601493197997324c74c52cc931d3149324c69e648c531d314a314c65e63d50319b988540c66d62150319e980540c679601503197596320c6d5610c8318f992510c63d649443197d95310c6cc624c4319dd95310c63f64540318f191500c67a60d53219e58354c865f63553219718d54c863e6414f218f59053c867a6014f219e58053c865e63943219758e50c865e63d52219758f548867b60552219e181548863e64d4e218f59353886e5610ca21f10ca31886e4624c621f1cc9318863f64542218f191508865e63951219758e544865f63551219718d544867b60551219e181544865e6394d219bd89534865e6514d21d55845348754538c5219d195314874c53885219798f540865d63d50219e983540867960d50218f596540863e64150219798c540865d63150219e980540867960150218f993530863d64d4c219e983530867960d4c2197596530871e5494c21c7552530871e5454c21c7551530874c6254c218f990530863d6414c219798c53086766114c219e98053086796014c21d354f320866d650c821d554e210866f6548421b318d21086776548421d554d210873a5494021ce552500875a5394021d654e500873a5454021ce551500875a5354021d654d500876b3254021da0c9500876b2154021da485500865f6354b409718d52d025e63947409758e51d02b86050740a718d429029e63906408f99741502b86050540c754e43102b96010c40d394e521034d5394840da982521034e5354840d354d521031d53d0840a718d421031d5350840cb94942103565394440d554e51103665294440d954a51103565354440d554d51103665254440d954951103364354440cd10d51103374254440cd509511037060544408f596411029e6390440cd54641103355110440cd547401023f6550040cd545401027b65500409d98754cc27561d5330a759032cc2d5610cb308f99251cc23d6494730b318
  | 2 => 0x1ccd31c8000003d8002e8b8c014800296a080058b06a11a8628e43c824e92ca2cb726a8627db26c7332ac1508034e07a087c90675abcd994c00006689e600b2e412f40ca76562cc48a86ac81c0008497000d19c2e024e000004080cd580044b7e12a0a1a3104b0f81511675080ea1ac5f80066800010a6810fe7d320039526d1f84411c0524c5d2505e9547816ab4820002302b86ca4000bc89a8600000176e508a0002a08a207f8440006e6700061000a98f4001a4001d0648000018c001389600000388cb000000ee00222c6294002e416aa4ea84252afa4a07829000869e891a14b98dc00180131a66c932bb23c96a3eeb2b6c0b90c8ac2bc3a2c300034800258a200000003a000000cc238001c4b58d8e112e5ca1687800001d8a8374dbaf63307279228e734078ace4ab8274aba51ac09880a9b130000b6c2970461609f0e2483509e8fcda0dead000c780027ade1d0aa9ca34571b8a716e003421c126ce260d4a32a681a90b5430060650009fb1aab8009b830002788d898de0008bb58428501e85eaabb0a7aac3506ae48d63b048d82fe118a84208c30aa273800000c6049ae4386623ac461a56ddb04bab3ce38002f3280fa1c3413450936770000d17c00164c58008ea485107ed7990cd82806224e5b5a3e8000025e00000d284076afc0b808042ee7293a1d924000000db48000f0208642801684000000002b0000007c569b0dab9e170cec90e6578daa28ca8b19e3125247baebe3646f9b659956002b853abe001fce6b8acd264718262190c46a54161a09a2120028c9d18800114c52707c2e832370000007b968ce9827a8006e89200312002d09aaa8c3adccf93ec220c80a44b8894e339863a263aa66b68e8b1838140210040100c0c0b00500c0000808070150040100c0a0000e0500301c000300000c01028010240800001010050000e098290001e02800008060240001c0703c22010050040107800020070380009c05000010100100011034340c0000001f01005008170040002801014000000000400014000840c05004024020000700007034000000c000010180a0480101002008010000e07c000800402c0201003010150580d02c040000003405004020040208c06018070000100000000120100802401000020667a6094b439e58252d0e6e62942439b58a5090e3f6550c4397d954310e5e63947429758e51d0a5e63942429758e5090b5a6394242d658e5090b3b4294242c714f4350aba60909428fd954210a6f65508428f99251cca3d64947328fd9150cca3c64543329e983548ca7960d52329d986544ca75619513297d8d544ca7661d50329d587540ca7a60d50329e583540ca3d6595032c718d540ca3e64150329d984540ca7561150329e980540ca796015032c7553430ca5d6510c32b3588430ca5f654c8329bd95320
  | 3 => 0x92b627e9de13998d10002232a5002c2f8908a8002d28e003a60005227288b203a658e083ae0de8560f2d86f0004f000a48000037cdb38600000b51c0818005e1ec0029800000d72402c16ca00004000000
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x1200a68001170b1005950003805c20051c830601005b2433d93536140201009208e683515c84354432a64e3218a0a0e4963588505068c39a84282834c1c54214141a34e7208a0a0e1654584328c6a338e86292638a5916014931cc2c2b00a498e0e6414a314c6633b66498c43521cd2154021a62e021aa2205147350951102b0b90c0a88818598d519044083aec2a0649861454584324c3062a0c498a6191188514c530b10e6a108090689635084048350a12c220241625d0324c120d10c819260905c1710c93048258bb482206218a1915244010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x2100a8083509611012088987190324c120c80645c4324c120
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
  | 4 => packedAt s5K4 (19544+((h/157+packedAt s5K4 (17974+(h % 157)*10) 10) % 568)*10) 10
  | 3 => packedAt s5K3 (1475+((h/9+packedAt s5K3 (1421+(h % 9)*6) 6) % 38)*6) 6
  | 2 => packedAt s5K2 (183+((h/1+packedAt s5K2 (180+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfe1ffff03c7fc70f1e3f1fffc703f07c19f673
  | 1 => 0x1fe1f8ffc07ffff01fc7e381f803fffce6487f
  | 2 => 0x1ffe00ffff87f8ffe007fc01fffc7f83078f9c
  | 3 => 0xe00000fffff800fffff80001ffff8003f80fe0
  | 4 => 0xffffff00000000fffffffffe00000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x42443011809088030209048cc1189118089631
  | 1 => 0x84884122092300300c42211108212660624846
  | 2 => 0x48409244901401452005482452484909058298
  | 3 => 0x819564892841929a56900049a4b20232b80d60
  | 4 => 0x1119800e326624ec9926927000c00c43d76000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeeaf8c8feeaf8c8feeaf8c8feeaf8c8feeaf8c8feeaf8c8feeaf8c8feeaf8c8feeaf8c8feeaf8c8feeaf8c8feeaf8c8feeaf8c8feeaf8c8feeaf8c8feeaf8c8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_16945
namespace PEqualNP.Outside.L_meta_16945
open PEqualNP.Outside.L_meta_16945.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c38182140400004085000238085000000101ffd5007fe5401ff55007fc5401ffd4c05fe5301ff54c05fc53007fd0c05fe43007f50c05fc4301ffd4803fe5201ff54803fc52007fd0803fe42007f50803fc42017fcc803fe32007f4c803fc3201ffd4407fe5101ff54407fc51007fd0401fe41007f50401fc41017fcc401fe31007f4c405fc3100ffc8401fe21007f48403fc2101ffd4007fe5001ff54007fc50007fd0001fe40007f50001fc40017fcc001fe30007f4c005fc3000ffc8001fe20007f48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x842004fdc4210007f6210802fff65440177fb2a2000dfd9510004feca8802ffe65440077f32a200bff5951005dfaca8802ffc65440077e32a200bdf1951001cf8ca88003ff64440017fb222000efd91100057ec888003fe64440017f3222000ff59110005fac888003fc64440017e3222000ef1911000578c88802fff5444017ff2a2200bff5511005ff8a888003ff63440017fb1a200aff98d10015fcc688003fd63440017eb1a200aff18d10015f8c68802fff5344015ff29a200bff54d10057f8a688003ff4344015ff21a2000ff50d10057f88688003ff62440017fb122009ff9891000dfcc488003fd62440017eb122009ff1891000df8c48802fff5244013ff292200bff5491004ff8a488003ff4244013ff2122000ff5091004ff8848802bff3244013ff1922000ff4c91004ff8648802fff5144017ff28a200bfd9451005ffaa28802ff55144017fe28a2000ffd0510007fc8288003f64144001fea0a2000fd50510007f8828802bff3144001ff18a2000ff4c510057f86288027ff2144001ff10a2000ff4851004ff8428802fff5044009ff282200bff54110027f8a088003ff4044009ff2022000ff50110027f8808802bff3044009ff1822000ff4c110027f86088027ff2044009ff1022000fe88110007fa4088003f92044009fe1022000ffc4110007f62088013fe1044009fb0822004ffd9410025feca08013fe65040077f3282004df9941001cfcca08013fd650400f7eb282004df59410004faca08013fc65040097e3282004ffd9010025fec808013fe64040017f3202004ef990100057cc808013fd64040017eb202004ef590100057ac808013fc64040097e3202007ffd501003ffca80801ffd540400ffe2a02004ffd8c10025fec608013fe63040057f3182004f798c10015bcc608013fd63040017eb182004f758c10005bac608013fc63040097e3182007ffd4c10037fca60801ffd530400dfe2982000ffd0c10037fc8608003fd430400dfe2182004ffd8810025fec408013fe62040037f3102004fb9881000ddcc408013fd62040017eb102004fb58810005dac408013fc62040097e3102007ffd481002ffca40801ffd520400bfe2902000ffd081002ffc8408003fd420400bfe2102006ffcc81002ffc6408003fd320400bfe1902008bf9841003ffea20801ffe510400ffea882007ff14410007fe8208003fe4104001fea082000ff10410037fe6208003fe3104001fe9882006ff0c41002ffe4208003fe2104001fe9082005ff08410025fcc008013ff5004009ff2802004ff54010027f8a008013ff4004009ff2002004ff50010027f88008013ff3004009ff1802004ff4c010027f86008013ff2004009ff1002004ff48010027f84008013ff1004009fb8802004ff84010027f42008013fd1004009fa8802000fe44010
  | 1 => 0xbfc5148001ffa0a4000ff90520007fa8290003fc4148023ff98a4000ff8c520007fa6290047fc3148003ff90a4001fbc852000ffc4290007fd2148001f690a4001ff0852000dfec09004bff5048009ff2824012ff54120027f8a090003ff4048009ff2024000ff50120027f88090047ff3048009ff1824000fe8c120007fa6090003f93048009fe1824001ffc812000ff64090013fe2048009f71024004ff08120027d84090007f82048011ffb2e2008bfd9710047fccb8800efe65c4011feb2e2008bf59710047f8cb8800efc65c4001ffb262000bfd9310007fcc988002fe64c4001feb262000bf59310007f8c988002fc64c4011ffaa62008ff95310047faa988023fc54c4001ffb1e2000bfd8f10087fcc78800afe63c4001feb1e2000bf58f10087f8c78800afc63c4011ffa9e2010ff94f10047faa788043fc53c4001ffa1e2010ff90f10007fa8788043fc43c4001ffb162000bfd8b1007ffcc588006fe62c4001feb162000bf58b1007ff8c588006fc62c4011ffa96200fff94b10047faa58803ffc52c4001ffa16200fff90b10007fa858803ffc42c4021ff996200fff8cb10007fa658803ffc32c4011ffa8e2008ff94710047eca388023fd51c4011faa8e2008ff14710007fe8388003fe41c4001fb20e2000ff50710007ea8388003fc41c4021ff98e2000ff8c710007fa6388043fc31c401fff90e2000ff88710007fa438803ffc21c4011ffa862004ff94310047faa188013fc50c4001ffa062004ff90310007fa8188013fc40c4021ff9862004ff8c310007fa6188013fc30c401fff9062004ff88310007fa4188013fc20c4009ffb2c2004bfd9610027fccb0800efe6584009feb2c200ebf59610027f8cb08012fc6584009ffb242004bfd9210027fcc908002fe6484009feb242000bf59210027f8c908012fc648401dffaa4200eff95210077faa90803bfc5484009ffb1c2004bfd8e10027fcc70800afe6384009feb1c2000bf58e10027f8c708012fc638401dffa9c200dff94e10077faa708037fc5384001ffa1c200dff90e10007fa8708037fc4384009ffb142004bfd8a10027fcc508006fe6284009feb142000bf58a10027f8c508012fc628401dffa94200cff94a10077faa508033fc5284001ffa14200cff90a10007fa8508033fc428401bff994200cff8ca10007fa6508033fc32840177eb0c200effd4610077fca30803bfd518401dfe28c2000ffd0610007fc8308003fd4184001fe20c200dffcc610007fc6308003fd318401bfe18c200cffc8610007fc4308003fd2184019fe10c2004bf98210027fea108013fe5084009fea842004ff14210027fe8108013fe4084009fea042004ff10210027fe6108013fe3084009fe9842004ff0c210027fe4108013fe2084009fd1042004ff48210007f24108013fc2084009ff8
  | 2 => 0x30005fec498057fe624c0037f3126000ff589300aff8c498006fc624c02dffa926015ff949300b7faa498057fc524c001ffa126015ff90930007fa8498057fc424c005ff9926002ff8c9300afbc649800bfd324c005fe1926002f70c930007fec298002ff614c001ff30a6000ff58530007f8c298002fc614c02dffa8a6016ff945300b7faa29805bfc514c001ffa0a6000ff90530007fa8298003fc414c005ff98a6002f7cc530017fc629800bfd314c001ee98a6002ff0c5300affe4298003fe214c001fe90a6015ff08530015fec09805bff504c009ff2826016ff54130027f8a098003ff404c009ff2026000ff50130027f8809800bff304c005fd9826004ff8c130027bc6098013fc304c009ee1826002fe0c1300affe4098013fc204c009ffb2c4004bfd9620027fccb1000efe6588009feb2c4014bf59620027f8cb10012fc6588009ffb244004bfd9220027fcc910002fe6488009feb244000bf59220027f8c910012fc6488029ffaa44014ff952200a7faa910053fc5488009ffb1c4004bfd8e20027fcc71000afe6388009ef31c4002b798e20027fac710002fd6388009eeb1c4000b758e20027f8c710012fc6388029ffa9c4013ff94e200a7faa71004ffc5388001ffa1c4013ff90e20007fa871004ffc43880037eb144001ffd4a2000ffca510007fd5288003fe2944001ffd0a2000ffc8510007fd4288003fe2144001ffcca2000ffc6510007fd3288003fe1944004ffd8620027fcc310002fe6188009feb0c4000bf58620027f8c310053ff5188029ff28c4014ff546200a7f8a310003ff4188001ff20c4000ff50620007f8831004fff3188001ff18c4000ff4c62009ff86310007ff2188003ff10c4001ff4862000ff84310012fe6088009ffa844004ff94220027faa110013fc5088009ffa044004ff90220027fa8110013fc4088009ff9844004ff8c220027f46110013fd3088001fc9844004ff0c220027fe4110013ef2088003fd9044004ff08220027f0411004bff65480257fb2a4012ff9952001dfcca9004bfd65480257eb2a4012ff1952001df8ca90003ff64480017fb224000ff99120005fcc890003fd64480017eb224000ff19120005f8c89004bff5448025ff2a24012ff55120097f8a890003ff63480017fb1a4011ff98d20015fcc690003fd63480017eb1a4011ff18d20015f8c69004bff5348023ff29a4012ff54d2008ff8a690003ff4348023ff21a4000ff50d2008ff88690012ff6248003ffa924001ff9492000fdca490007fd5248025f6a924001ff1492000ffe8490007fe4248003f72124001ff50920007da8490007fc4248003ff9924011fbcc92000ffc6490007fd3248003fe1924001fb0c920007fec290002ff6148001ff30a4000ff58520007f8c290002fc6148025ffa8a4012ff94520097faa29004
  | 3 => 0xeb288004df59440004faca20013fc65100097e328801dbf990400e7fea82006ffe5410039feaa0801bff15040027fec620013fe63100057f3188004f798c40015bcc620013fd63100017eb188004f758c40005bac620013fc63100097e318801cffd4c400d7fca620073fd5310035fe298801bffd0c400d7fc8620003fd4310037fe2188004ffd8840027fcc420006fe6210009f73108001bb98840027fac420002fd6210009f6b108000bb58840027f8c420012fc6210039ffa908019ff948400e7faa420067fc5210037ffa108000efd08400cffc8420003fd4210001dea10801bff108400d7fe6420067fe3210001fe9908019ff0c840027fec220013fe61100017f3088004fd98440005ecc220013fd61100017eb088004fd58440005eac220013fc6110039ffa88801cff944400e7faa220073fc5110037ffa088000ff904400077c8220003fd4110037fe2088000ef104400d7fe6220003fe3110001fe988801aff0c4400cffe4220003fe2110001fe9088019ff08440025fcc020013ff5010009ff2808004ff54040027f8a020013ff4010009dfa008004ff90040027f48020013fd4010009dea008000fe50040027fe6020013fc3010009ff9008004ff08040027fecb18012ff658c009ff32c6003bf99630027facb18062fd658c009fe32c6004bf19630027fec918012ff648c009ff3246000bf99230027fac918002fd648c009fe3246004bf192300c7fea918063fe548c031feaa46018ff15230015fac71800bff538c005ff29c6002ff54e30017f8a71800bff438c005ff21c6002ff50e30017f88718013ff628c009ff3146001bf98a30027dcc518006ee628c009feb146000bf58a30027dac518002ed628c009fe3146004bf18a300c7fea51805ffe528c031fea946017ff14a30007fe851805ffe428c001fea146017ff10a30017fe651800bfe328c005fe9946002ff0ca30027fec318013fe618c0017f30c6004ff58630005fac318013fc618c031ffa8c6018ff946300c7faa318063fc518c001ffa0c6000ff90630007fa8318003fc418c005ff98c6002ff8c630017fa631800bfc318c02fff90c6000ff88630007fa431805ffc218c0097f3046004ffd4230027fca118013fd508c009fe2846004ffd0230027fc8118013fd408c009fe2046004ffcc230027be611800bfb308c009fe1846004fe0c230027fe4118013fc208c02dffb2a6016bfd95300b7fcca9800efe654c02dfeb2a6016bf595300b7f8ca9800efc654c001ffb226000bfd9130007fcc898002fe644c001feb226000bf59130007f8c898002fc644c02dffaa26016ff951300b7faa89805bfc544c0097fb1a6002ffd4d30017fca69800bde534c005fea9a6016f754d30017f8a69800bff434c005ff21a6002f790d30017fa8698003dd434c005fe21a6000ffd89
  | 4 => 0x93fc52d0037ffa168024ff90b40007fa85a006ffc42d004bff9968024ff8cb40007fa65a0093fc32d0037ffb0e8000ff98740005fcc3a0003fd61d00017eb0e801bff187400effea3a0077fe51d003bfea8e801dff147400dffe83a0003bf41d0001ff20e8000ff507400077a83a006ffc41d004bff98e8000ff8c740007fa63a0097fc31d0049ff90e8000ff88740007fa43a0093fc21d003bffa868004ff943400effaa1a0013fc50d004bff9868004ff0c340127fe41a0013fc20d0009ffb2c8004bfd9640027fccb2000efe6590009feb2c8023bf59640027f8cb20012fc65900417eb248023ffd524011ffca92008ffd5490047fe2a48004ffd8e40027fcc72000afe6390009feb1c8000bf58e40027f8c720012fc6390047ffa9c8022ff94e4011ffaa72008bfc5390001ffa1c8022ff90e40007fa872008bfc4390009ffb148004ff98a4000dfcc520013fd62900017eb148004ff18a40025f8c52008fff5290043ff2948023ff54a4010ff8a520003ff4290001dfa148021ff90a40007fa8520003bd4290043fe2148022ffcca4010ffc6520003fd3290043fe1948004ffd8640027fcc320002fe6190009feb0c8000bf58640027f8c32008fff5190047ff28c8023ff5464011ff8a320003ff4190001ff20c8000ef90640007fa8320003fc4190001de20c8022ffcc640007fc6320003fd3190045fe18c8021ffc8640007fc4320003fd2190043fe10c8004bf98240027fea120013fe5090009fea848004ff14240027fe8120013bf4090001fda048004ffcc240027f86120013ff2090009fe1048020ffd9540105fecaa00037f65500013fb2a8020ff9954001dfccaa0083fd65500417eb2a8020ff1954001df8caa00837c65500073e32a8020ffd5140107fca8a0083be5450041feaa28020ef55140107f8a8a0003ff63500017fb1a801fff98d40015fcc6a0003fd635003ffe31a8002bf18d40107fea6a007ffe5350041fea9a801fff14d40007fe86a007ffe4350001fea1a801fff10d40007fec4a0002ff625003dff3128001bf98940007fac4a007bfc62500037e3128020ffd49400f7fca4a0083fd525003dfe2928000ffd09400f7fc84a0003fd425003dfe212801fffcc9400f7fc64a0003fd325003dfe1928000ffd8540005fec2a0003fe6150001feb0a8000ff18540005f8c2a0083ff5150041ff28a8020ff54540107f8a2a0003ff4150001dfa0a8000ff90540007fa82a0003bd4150001fe20a801fffcc540007fc62a0003fd315003ffe18a801effc8540007fc42a0003fd215003dfe10a8020ffd4140027fca0a0083fd5050009fe2828000ffd0140007f680a0013fe4050009df202801fffcc140027f860a007bff2050009fe1028004ffd9440025feca20013fe65100077f3288004df9944001cfcca20013fd65100397
  | 5 => 0x413115ffaa0988affc504c405ff9826202f7cc131017f860988abff204c455fe1026229ffd962114dfecb108a7fe65884077f32c4229ff5962114dfacb108a7fc65884077e32c4200ffd9221005fec910803fe64884017f3244200ff59221005fac910803fc64884017e3244229ffd522114ffca9108a7fd5488453fe2a44200ffd8e21005fec7108a3fe63884057f31c4200ff58e21005fac7108a3fc63884057e31c4229ffd4e21147fca7108a7fd5388451fe29c4200ffd0e21147fc8710803fd4388451fe21c4201bf58a2100ffea510807fe5288403fea944201ff14a2100ffe8510807fe4288403fea144201ff10a2100ffe65108a3ef3288403ff1944201ff4ca2100ff86510807ec32884037f30c4229ffd462114ffca3108a7fd5188453fe28c4200ffd0621007fc8310803fd4188401fe20c4228ffcc621007fc6310803f63188401fe98c4200fd4c621147f86310807ff2188403f790c4201fdc862100ff84310807f42188401ffb044200ff98221025fcc110803fd60884017eb044200ff1822114ffea1108a7fe5088453fea844229ff14221147fe61108a3fc3088403ff9044201ff0822113ffeca9089eff654844fff32a4203bf9952113ffaca9089efd654844ffe32a4203bf19521007fec890802ff6448401ff3224200bf99121007fac890802fd6448401fe3224200bf1912113ffea89089ffe544844ffeaa24227ff15121007fec690802ff6348401efb1a4200b7d8d21137fcc69080afe6348401feb1a4200bf58d21137f8c69080afc6348401ee31a4202b718d2113ffea69089bfe534844ffea9a4226ff14d21007fe869089bfe4348401fea1a4226ff10d2100dfec490807ff5248403ff2924201ff5492100ff8a490807ff4248403ff2124201ff5092100ff88490807ff3248403ff1924201ff4c92100ff86490806ff614844fffa8a4227ff9452113ffaa29089ffc5148401ffa0a4200ff90521007fa8290803fc414844dff98a4200ff8c521007ec6290803fd3148401fa98a4226ff0c52100ffe4290807f72148403ff10a4200fb8852100ff84290807ec2148403fa10a4200ffd8121005fec090803fe6048401feb024200ff18121025f8c09089fff504844fff2824227ff5412113ff8a09089bff304844dfe1824201ffc812100fde4090807fc2048437ffb2e801dbfd97400effccba000efe65d003bfeb2e801dbf597400dff8cba000efc65d003bffaa6801bff953400ef7ca9a0077fd54d003bdeaa6801bff153400dffec7a0097fe63d00057f31e8000ff58f40005fac7a006ffc63d00057e31e801dffd4f4012ffca7a0077fd53d004bfe29e801bffd0f4012ffc87a0003fd43d0037fe21e801bffd8b40127fcc5a0006fe62d0001feb168000bf58b400dff8c5a0006fc62d003bffa968024ff94b400effaa5a0
  | 6 => 0x57e3188230ffd4c4117ffca6208c3fd531045ffe298821bffd0c4117ffc8620803fd4310437fe218821bffd8841177fcc420806fe6210401feb108200bf588410dff8c420806fc6210461ffa90822eff94841187faa4208bbfc5210437ffa10822eff90841007fa842086ffc421045fff990822eff8c841007fa64208bbfc32104637f3088230ffd4441187fca2208c3fd5110461fe288821bffd04410077e8220803fe4110401fb2088200ff504410077a8220803f5411045fff988822fff0c441177fe42208bbfc2110437ffb008200ff98041025fcc020803fd60104017eb00821bff18041187fea0208c3fe5010461fea808230ff1404117ffe60208bffc301045dff900822eff0804116ffecb188b6ff658c45bff32c6203bf9963116ffacb188b6fd658c45bfe32c6203bf19631007fec918802ff648c401ff3246200bf99231007fac918802fd648c401fe3246200bf1923116ffea9188b7fe548c45bfeaa4622dff15231015fac71880bff538c405ff29c6202ff54e31017f8a71880bff438c405ff21c6202ff50e31017f88718803ff628c459ff3146201bf98a31007fac518802fd628c459fe3146201bf18a3116ffea5188b3fe528c45bfea94622cff14a31007fe85188b3fe428c401fea14622cff10a31017fe651880bfe328c459ef1946202ff4ca31017f8651880bdc328c4057f30c622dffd463116ffca3188b7fd518c45bfe28c6200ffd0631007fc8318803fd418c401fe20c6202ffcc631017be631880bf7318c405fe18c6202fd0c631167fe43188b3fc218c401ffb046200ff98231025fcc118803fd608c4017eb046200ff1823116ffea1188b7fe508c45bfea84622dff14231017fe611880bfc308c459ff904622cff0823115ffeca988aeff654c457ff32a6203bf9953115ffaca988aefd654c457fe32a6203bf19531007fec898802ff644c401ff3226200bf99131007fac898802fd644c401fe3226200bf1913115ffea8988affe544c457feaa2622bff15131015fec69880bff534c405ff29a6202f794d31017faa6988afdd534c405fe29a6202ffd0d31007be869880bfe434c405fea1a6202ff10d31017b88698803ff624c4017fb126200fbd8931005dec4988abfe624c4037f3126200ff58931157f8c498806fc624c401f63126201bb1893115ffea4988abfe524c457fea92622aff14931007fe84988abfe424c401fea12622aff10931017fe649880bdf324c405ff1926202ff4c931007ba649880bfc324c4057fb0a622bffd453115ffca2988affd514c457fe28a6200ffd0531007fc8298803fd414c401fe20a6202ffcc531017ee629880bfe314c401ef18a6202ff0c531017b8629880bf4314c455ff90a622aff08531007fec098802ff604c401ff3026200ff58131007f8c098812fc604c457ffa82622bff9
  | 7 => 0xa086fff62d0471ff3168201bf98b41007fac5a0802fd62d0437fe3168201bf18b41197fea5a08e3fe52d0465fea968238ff14b410dffe85a0803bf42d0471ff2168200ff50b410077a85a086ffc42d0473ff9968238ff8cb41007fa65a08e3fc32d0465ffa8e8232ff94741197faa3a08cbfc51d0473ff98e8239ff0c7411c7fe43a08e3fc21d0437ffb068200ff98341025fcc1a0803fd60d04017eb06821bff18341197fea1a08cbfe50d0465fea868232ff143411cffe61a08e7fc30d0471ff9068238ff0834118ffecb208c6ff6590463ff32c8203bf9964118efccb2080e7e6590463feb2c8231bf59641006facb208027d6590463fe32c8203bf196411adfac9208c7ff5490463ff2a48231ef9524118ffaa9208c7bd5490463fe2a48200ffd8e411bffcc72080afe6390401ef31c8202b798e41007fac720802fd6390401eeb1c8200b758e411bff8c72080afc6390463ffa9c8237ff94e4118ffaa7208dffc5390401ffa1c8237ff90e41007fa87208dffc4390401ffb148236ff98a4100dfcc520803fd62904017eb148236ff18a4100df8c5208c7ff529046dff2948231ff54a411b7f8a520803ff429046dff2148200ff50a411b7f885208dfff329046dff1948200ff4ca411b7f865208c2fe6190463ffa8c8231ff9464118ffaa3208c7fc5190401ffa0c8200efd0641007ee83208dfff319046ffe18c8236ffc86411b7f84320803ff6090401ff3048204bf98241007fac120802fd6090401fe3048231ffd424118ffca1208c7fd5090463fe2848237ffcc2411bff861208dbff209046dfe1048235ffd95411adfecaa08d7fe65504077f32a8235ff595411adfacaa08d7fc65504077e32a8235ffd51411affca8a08d7fd545046bfe2a28200ffd8d41005fec6a08d3fe63504057f31a8200ff58d411a7f8c6a080afc635046bffa9a8234ff94d411affaa6a08d3fc5350401ffa1a8234ff90d41007fa86a08d3fc4350401ffb128200bfd894119ffcc4a0806fe6250401feb128233ff1894100df8c4a08d7ff5250467ff2928235ff5494119ff8a4a0803ff4250401dfa128233ff90941007fa84a0803bd4250467fe2128234ffcc94119ffc64a0803fd3250467fe1928235ffd45411affca2a08d7fd515046bfe28a8200ffd0541007ee82a0803fe4150401df20a8234ffcc5411a7f862a08cfff2150467fe10a8200ffd8141005fec0a0803fe6050401feb028200ff18141025f8c0a08d7ff505046bff2828235ff541411aff8a0a08d3ff3050469fe1828233ffc814119ff840a086fff65104617fb288230ff9944101dfcca208c3fd65104617eb28821bff1944101df8ca208cafe6410461ffaa0821bff950411877ca8208c3fd5410461deaa0821bff150410dffec6208bffe63104057f3188200ff58c41005fac62086ffc631040
  | 8 => 0xf14b4200ffc85a1007be42d0803f72168401ff10b4200f7885a1007ff32d0803ff1968401ff0cb420dffec3a1003fe61d08017f30e8400ff58742005fac3a106ffc61d087dffa8e843eff947421f7faa3a10fbfc51d087bff98e843dff0c74200ffe43a1007fc21d0837ffb068400ff98342025fcc1a1003fd60d08017eb06841bff183421f7fea1a10fbfe50d087dfea86843eff143421effe61a10f7fc30d0803ff9068401ff083421e7fecaa10f2ff6550879ff32a8403bf995421e7facaa10f2fd6550879fe32a8403bf1954200dfec8a10f3ff5450879ff2a2843cef951421e7faa8a10f3bd5450879fe2a28400ffd8d42005fec6a1003df63508016fb1a843bff98d42015fcc6a1003fd6350877fe31a8402bf18d42007b8c6a100adc6350879ffa9a843bff94d421e7faa6a10effc5350801ffa1a8400efd0d421dffc86a1003fd4350801dea1a843bff10d4200dfec4a1007ff5250803ff2928401ff5494200ff8a4a1007ff4250801f7a128401ff9094200f7c84a1007fc4250803de2128401fb1094200ffe64a1007fe3250803fe1928400ffd8542005fec2a1003fe6150801feb0a8400ff18542005f8c2a10f3ff5150879ff28a843cff545421e7f8a2a10efff3150877fe18a8401ffc854200ff842a1003ff60508017fb028400ff98142007fac0a1003fc60508097e302843cffd41421e7fca0a10f3fd5050879fe282843bffcc1421dff860a1007ff2050803f79028401ff081421d7feca990eaff654c875ff32a6403bf995321d7faca990eafd654c875fe32a6403bf19532007fec899002ff644c801ff3226400bf99132007fac899002fd644c801fe3226400bf191321d7fea8990ebfe544c875feaa2643aff1513200dfec69900bff534c805ff29a6402ff54d32017f8a69900bff434c805ff21a6402ff50d32017f88699006ff624c803ffa926401ff9493200ffaa499007fc524c803ffa126401ff9093200ffa8499007fc424c803ff9926402fbcc93200ffc6499007de324c803fe1926401f70c93200fd86499003ff614c8017fb0a6400ff98532007fac299003fc614c8017e30a643affd45321d7fca2990ebfd514c875fe28a6402ffcc532017be629900bfc314c803ff90a6401ff08532007fec099002ff604c801ff3026400ff58132007f8c099012fc604c875ffa82643aff941321d7faa0990ebfc504c805ff9826402ff0c13200ffe4099007fc204c837ffb2e8232bfd9741197fccba080efe65d0465bf32e82039f99741197facba08cafd65d0401beb2e82009f597410dff8cba080efc65d0465ffaa6821bff95341197faa9a086ffc54d0437ffb1e8239ff98f41015fcc7a0803fd63d04017eb1e821bff18f41015f8c7a08cbff53d0473ff29e8232ff54f411cff8a7a086fff43d0473ff21e8200ff50f410dff887
  | 9 => 0x600000200000004c02a00a00600e00801600602000201400002409004602a00e00000000e00800400a00001a00002003603a00c00201c02c02a02801802600604a02202601800200400c00600004a00200001400200004200401400200800201000800a01a00a01200201200000400200002e02802000c00201603400a00600000002000605200000602600c00000a00800202000200400a03600000400000400200600400a02a01e01a00006400000806600800200001400800000400004004400000202200e02400a00403401a0181bffd9743215fecba190bfe65d0c077f32e8642ff59743215facba186ffc65d0c077e32e8602bf99343217fea9a186ffe54d0c85feaa6861bff15343015fac7a180bff53d0c05ff29e8602ff54f43017f8a7a180bfe43d0c05df21e8602f790f43017f887a180bbc43d0c37ffb168641ff98b4300dfcc5a1803fd62d0c017eb16861bff18b4300df8c5a190bff52d0c83ff2968642ff54b4320ff8a5a1907fe42d0c37fe2168602ffccb43017fc65a1907de32d0c05fe1968602f70cb430dffec3a1803fe61d0c017f30e8600ff58743005fac3a186ffc61d0c85ffa8e8642ff94743217faa3a190bfc51d0c05ff98e8602f7cc743017f863a1907ff21d0c83fe10e861bffd8343007fcc1a1812fe60d0c01feb068600bf583430dff8c1a190bff50d0c85ff2868642ff54343217f8a1a180bff30d0c05fe1868641ffc834320ff841a1903ff6550c817fb2a8640ff9954301dfccaa1903fd6550c817eb2a8640ff1954301df8caa180aff6450c81ffaa28640ff95143207faa8a1903fc5450c057fb1a8602ffd4d43017fca6a180bfd5350c05fe29a8602ffd0d43007be86a180bfe4350c05df21a8602ff10d430177886a180bdc4350c01ffb128600bfd89431fffcc4a1806fe6250c01feb12863fff1894300df8c4a1903ff5250c7fff2928640ff549431fff8a4a18fffe4250c7ffe2128602ffcc943017fc64a180bfc3250c01ffb0a8600bfd8543007fcc2a1803fd6150c01fe30a8600bf18543207fea2a1903fe5150c81fea8a8640ff14543017fe62a180bfc3150c7fff90a863fff08543007fec0a1802ff6050c01ff3028600ff58143007f8c0a1812fc6050c81ffa828640ff94143207faa0a1903fc5050c05ff9828602f7cc143017f860a18ffff2050c7ffe102861bffd97421f5fecba10fbfe65d08077f32e843eff597421f5facba106ffc65d08077e32e8401bf993421f7fea9a106ffe54d087ddf2a6843eff553421f77aa9a106ffc54d0837ffb1e843dff98f42015fcc7a1003fd63d08017eb1e841bff18f42015f8c7a10fbff53d087bff29e843eff54f421eff8a7a106fff43d0801dfa1e843dff90f42007fa87a1003bd43d0837fe21e8401bf58b4200ffea5a1007fe52d0803fea968401f
  | 10 => 0x7a441680c3e682d06f800006a84900001df14a8e8d00849f00002580001d50c318445f845c140a0d82e27e90050af800050a0b0191042e021355095400043214b92a80004c23850c90a3a8571b8a0b07a22a510a9bc4c8a10135594940000a442c8388fc85440000d8840e7b600000000007bf42512aca7209328fa08caca8430e30b50c682e93459a7903a13c3d590ac00e01800200000600000e00402801600000000000800403600200201200000c01a00400200003600400400001200801200605800000000000401401c01001c02200000600202000000202a01c00400000003c00a00200400001a00201203200400602000800a01200401605a00000000a00600000401201600c01c00406e02000a00202000600000200800a00a01206803000c00400000401a00200000000000e00000e00205400000600600200801801603400001a00201c01200000400203201400200200000a00000a00004005a00e0a200a00200c00200609400000000400000804000200200400003201800c04e02010c00c01c00001400200e00400e08a02000002a01000800401c02e02404600200400000000000a00000800600000001c00400000a00200000200a00002801207c00001e00400601e00000000800c00200202400004a00400000c02200000000c00201003a01801001800007600003603c00e00800402600600402200000a00600400200e03e00001803801400400000e00006e07202400200000200c04e00401006000201800a02e00802003802000400200400600008200a00c0080000120020040000a403604600002a00801800400001c00c00204800400202400003401e00e02601800200600000600001406400200602200800004600a00000c00a00001e00200006e00200001003400001800c03c00200200002400000000000201c00000000001200000000400201200000601002201400a02002400001a00602c00601001400e00000400000200000000020e00003c00200000400000000006a01600401403602c05c00c00a00c00000000600000000800000600000000403a00400400002e05800201200000201000a02801000203202a00200205000000000000c04200800600e01801a0040120ca0fe02000200600200400001a00401000000800000200200000212001e01800a01000600000200000003001400400400600000005401e00203000600601000200800200001201a01400600201a02a00401402400605202001600600201400400202400001600600000c00801000000402404200000002200401200000201008e01801605c01200a00800200c01200000200800000002800002000000600000603001802e00003801200a0420fc00001c00202400202000000401806000400401e03400400400209c00000a00e000
  | 11 => 0x85d4b623da1b99f500005d43fa8ec8140340398210015002a22aa12c4b26c72f00b940001cb32c80010004fd1260db800000000000000b82f50fd9610f220730300d3435062502d03781867ec242096c4963f643800007dc0003a61dcc46860d0db1c70ec476e17689dc89637d0071da47401c209d0f90bba69a0da000068241a00011b40000000701dfc81e17c01892003480000000000e8000024b0ac00007f017b16089280000791a380000000000000f9213b37d9320cce01c13e82c90026291c51fec66c4133c8219cda612c19e1e70f1003342a8be83ea55108f052ca6e42d3321420e524bc0001a0800013631a8ce8e8425d01f9f700000000000000ce8000229000090e31737921846f47c142a03642620ca3329cd50907ae09c9580bc42ba1918d380d824d1a506387965922ae1150d844363af901000000000001d50d257f0000fb43c08270789d550482320000f40d9805226a0000e547ef19401dc6982201c4865c2940fa13c8f38baa66923992c06106280d09fe84de5d10000728bd01db1160a6d0ca5850fe8000ad06940001a4cbfc0e30d7a170b340000000000d0606100000b82466e73bc000ca360003c5022056c17b0000df859605d10d928c27a1c91fd9b180003930001c3491a4d2106855035a5f00000000fe80000001d105421bc2279680616000000040059221f34014a40006fd357987017a4a23991d9800039a350a0a400023a3181c688ae6cb270094015249c0630454fb42080ae82b400056317f80000e00000c9800009e346130821ce683830ee8a3c65866f0001e543662ca2bc8ae40942780f103d000000000010989c67a80000000442000000000063085602212c82560000002114ce613536280003165e32f61248cac62122d1dc50c421c18c9e500f46e62451fcd03e59c2c98aec4840913208ff81f860626a8000f3261716996406ea0000000000efc0002770f1851000000016e03dc7d12301fe022e58e1cb1a542ae14d21480008f664019b8e30d640000039e78a705c611c85ac318352123880076a09a000120c6b83dc0b98b64c1440a0001a58b7863b00021b047600833d00009e844612880008320000001cbc39c0002249f609bc2022da1f4023600003397a85e400012f9eb000000042885dc00068629910a84a83b925294a80000000ac944cce42ac42d21dc00065800c95bd0dc7963a515081985fb106000002e1b518a0340e464214028698eb006643996b507a4892cd8eb48206da377800000010b1d503ec3cc527014090cc0271524a879c9e00943bd8b34a4830516a868c7783940450ab849277d0b38bc4866156058152000080d03706c02662f842918bc9cc73a36ca084eca12000c1f143c81c536a17d007250619294645443572129e8c5b8802260156800078d2ae9dc04ce2710001698208
  | 12 => 0x13438289000001082d51d0403c2fd000213800058f0461278abc5e50f880105e001034d8c1016a33837085a90d66813bd0d4cfee70c1430e9cd601f81439540cf81642b480185b650b05c10bce244e94081660a9e4c510f1fac8745cd35d098832c57b00010e03b272507c1e748460003160c804486bb2c68da43f27670758cb47206420000970c286f40a89798fcc2de01d1d700005b33880e106546030a2951cb800e84281b60d3e6f5000000000031a2fe960400028e09312b80008633820f0ccee5f20b791acfec2b84059d0ccba6181ff85082fe5a331386082a63e92c61f6d0ba57d10d15b42045f126720509a010d02299d87422703e90a40b843811208444a246900508d40de61282d780082bc66c1091fc907c2e600680b4c0071622c073508c4fe1e388cc03478b0991a24d720003b40610d704c741d17f05a23ac1ea11d4888169387903096c5f336d8b1102602c20882389ee4611291eb42e0871271070caa47a43e19cfcb487242d2875d09844d0411d2c9d80260cd88dc92244e308040cbb861d03f82407444341b919506200ce3621e24cc07a02e582fc6007811a2057cf2e2c11ae98549581cf2ba9aa03ec5d73ab9724f7c32625312f4cb81d628a87101ce01d02391dc88428b12b17e89ca6a90c49a88b0e2ef423826c68622e1c006e843222205e0f105c05583b0184c06e5ac1b306a818235516d2064bc84c91ea84286686a328b8c08b8a4080530504a060002a012682d82eb0001654eb60ba1d4918cc5a5ae24100002cc0000000fd45380f51b190dc0007d900004300001a543680007567b13dc8de08f086a2b50c1c8902530a70e346be09c326835c2d00641138ca502a79a3d90f246265e92b80f8825c428170a0d43204f811f1cb807c73b000122006a0d100001a800029e000194800079f0001bb40005610001528f4a0000000000ed61bb0179d240fc41838395c8000806396855503c671000155c0004090c0206000025724d99187f04e442f800057804e2351c7cb520003ad19ac44674f29a0b00a988390001af0bee4d720e1f1814601f17418e4e8c7d71f093108a04680ef00004b41e80000c3ccd03a6280058c02480914198a90de2581a4041c77e1f70e0022c68e5220890294e7a5ce35e8ba859c50238a003c96619d269867c0004e715a13040aa0db0000f583a624a21c99980007530000e7000082a1f580004fc47d2428000aec00038300000006df391000000023f1d803504da029000000035269c1590cac12400043c000000020a3758000eec52d30420e009605718f14340000342aa000084866a236207021c6a61f9197c0a836828800003d40000002020b7400031d13180003d93159a9c6d800008ca1344d84702408000f6603b3f0a1d08940000ca14f0aac7cf18d831c76e7863751988da430c261
  | 13 => 0xe543384db0939ee0df050f13419e49ec0e513b010c00200000006dc1b40813c396189b83bb072060c5863c52b205e44022733de1088cb605115688148243fd0001b247f800023e00000004970001f547c600002600006fe55309f0afc45a75d22f80004c800000007cc27e2af31117680008420001bb8f9862e29b06f414e39b00008bc61263104ba0ec8ac3f1380884c5e858a2a29ba4e1c82001e1df0c3268c0000d6c1dc0003668d605ae54b000000037c53124e80009e44b8384957c5d85c31c39938fca00000000002906f7243000000012939612ed02c3e628e000000085e0000f208285460001b010d05c711e8a580de0b6296091030a37417f06e4afc0c02059ba00820be03e0124a7e3013f69dc815450c26586c453051626b1a90e8e26037c8a290345892ec8e780f65b541282b831a5943121f1c57a1f20181a9451259914f99450b07000ec03e4f420ed3841bfc4dc69d0000000932024000032428e0002db14ec88a0e122e9ec0b6048f1c308a882e73900003dc2a43913da82146b2000256914400001641f87707e61502038e3cc784da1638ef83f427c0748eb800020e2ef81000000000000000a5600006e8a0873e0001819c6c00034900015b80000c200012c48805710a18044cda3f420000010a64413ef181000087221d94600002310001b3800057800010c40000001228a8c00065a3de8ef4ff87c013906e06641d22f08a500001211a79fe4c7037b2c18fa0c2432237f14106ac4cc3ba1b04bec3db0129f8880223526784949503f93f713640ca3cf0f59d649307283e582105e6000046934458c76c0478c7000063229801e0d6c6532d418245a44df39b9074e9a18716113b440613002401780c41c71681b54b76514039070410007409c041818a4eb0730468ae60561e907bc6c216207997d474a82e2d38e2c3f87311dc13d45260001850f350061403c205d80da78e3ef907cbde65725094a029800033d841451871d199974cd68406388802cb3e1613370e900185d029d159c33405007f8b7c87c6b530585e87321ab25b84885567a71b69af85348373939adc8c86b33281e0cd9046e3e40570a5e51a32f15040000d610821800000003f41920b7a63613a8d80d7e0001fd000000042c07b14f802a00041684700000001331c0c0000000000c588066cf15000000003ba0001db44c619200005e00007b43e5000071c7fd37601605c82a60a7937400007d34294cc13e11428f02cc00082230d8b305f600000002248ca526000000000000027e142400045b218000000063f10792307b071e1428000a406f029a82789261c825d11c434e33d14891fc0d02e32ad8c849f612a4220aa0040866065988031409939f1bd8ea03e516c0a0019e3af0560f0865e01426518683fe36f2fc148c9e670216790146ec7803a29e4843
  | 14 => 0x270001cd8a023f73af13bce9057a00010f00001d100000000002b50001038940365000000062a0001aa12fc53a0003a709fc0000000001a2865c61e3b082acba487634c8000cc256b000106c33c00000005b48046840d1000096a44323b0000f764742a1800056600004e9600e425d824707405c482b0001e3cc7a5552709c604e847e29e893825e4f92538cd4b7e3771f78000b103df05b998c3c285b0001d48c946dd23306c81d83ca0ea1a800460dc00000003220002be0e1400020400d911cf6e079000000063a5914070518452236021124000033f0001e140002dd18888440004a9000206c0006de0cc800000070b0001b440000000f68000f4c00011400003020000000000c7c0000000f0450800032610fd0602993eb1ffc8d2435000181c82c7e03e70118ae829210e818c67c86401e95348de45e37d0cc40007750899444c6e61f1938a340d21cc1f8173ccea754000119c6d60002751b5878035a2dc8360f3672015883c104c000000000023000000018980e268d32387d076c46212788e0dc60df019085058a2aa01100004f40d237e0134f5e1740418000762000405000000026a37286fc82a0002e620bc6bc41e3d515249b06331b520a0b2e00000000000004a408790f46e06492ac800000081200005f80004fa33f1c64a9c0000001d443ca7e31eb800000015b1b389948a60000669a5c7c00000ff000000000020680010665b200005b800002b1ef0000dae00030100000004b91a58cc073a427000078cd302ee3568000000116302800016227b39c00003b43b30ca9e4cb440003588d4417684f3bc9a48ec65b708815b0c1c0002ef116500e6c334388ace2652e0049b908987a92578f4c0a656217c97e48400760000adc7d80b939e141c76883c00016ac2e41a000000002127f11129b807500383930d080003063ab00000000002f3a03c0000982f6990d06400010b0a902fa6d00cc0a9c00059d0b2976c8f450e1890824000000371162cc9e39232580000000fd08f959825a4be3442044eee7fe1ee8e5c1de5ca02d8978c1e0c839988182b033b09b817c48c05925a062108276a0a48e207d40001f3800000000000017200007ba1c10000cfe000356000000000005786b89d068f1b200004d60361bc83a87983450099ab84d22f7002831049014419c99c0e2e5961181f9c3d857741a0000bdc2a90000c3506272b1870000caa18f0000000a424cd23c8000a0a0000001b281fc00000000000000004248000b420002ff971014459e1738000cfa7c43e98000fd478c0001e8800000036e10b87304ff0001dbc3e00003119a44bd61ac2eb0898f30000000000010c7642391f082b40951640c7cc2c60c08e9e08fba2d643a8000000678000205cb824f106988f0b7c00000001ac00048b00
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe1058810026ea1058810026ed1058810026ec10588100dcff76d0810024fe76d0810004fd76d0810024fc76d08101f67e65d08100067d65d08100debe64d0810006bd64d08101eede63d0810006dd63d081000eee62d0810006ed62d0810004ff7650810024fe7650810004fd7650810024fc76508101e67e65508100067d6550810006be6450810006bd6450810005df7350810035dc73508101dede6350810006dd635081000eee6250810006ed6250810005f77150810005f47150810004ff764c810024fe764c810004fd764c810024fc764c8101d67e654c8100067d654c810006be644c810006bd644c810016de634c810006dd634c81000eee624c810006ed624c810004fd76d041003d7e75d04100057d75d04101967e65d04100067d65d04100debe64d0410006bd64d04101cede63d0410006dd63d04101c6ee62d0410006ed62d0410004ff7690410004fd769041003d7e75904100057d759041018e7e65904100067d6590410006be6490410006bd6490410035de7390410005dd73904101bede6390410006dd63904101b6ee6290410006ed6290410236f66190410025fa7090410005f97090410004ff76504101ae7e65504100067d6550410006be6450410006bd64504101a6de6350410006dd635041019eee6250410006ed625041022ef661504100dcff7610410024fe7610410004fd7610410024fc76104101867e65104100067d65104100debe6410410006bd641041017ede6310410006dd6310410176ee6210410006ed6210410025fa7010410005f97010410084ff768c410024fe768c410014fd768c410024fc768c41016e7e658c4100067d658c410006be648c410006bd648c410016de638c410006dd638c410166ee628c410006ed628c410025fa708c410005f9708c410084ff764c41015e7e654c4100067d654c410006be644c410006bd644c410016de634c410006dd634c410005ef724c41002dec724c410156ee624c410006ed624c410037d4314c41007cff7688410024fe768841000cfd7688410024fc768841014e7e65884100067d6588410006be6488410006bd6488410146de6388410006dd638841000eee6288410006ed6288410025fa7088410005f9708841007cff764841013e7e65484100067d6548410006be6448410006bd6448410005df7348410035dc7348410136de6348410006dd634841000eee6248410006ed6248410025fb7644010006fb7644010004fb76440100077b75440102277875440100277a6544010027796544010007bb7444010007b87444010027ba6444010027b96444010027da6344010027d96344010026fb6244010027ea6244010006f96244010027e96244010006e96244010025fb7144010027f3714401021efa6144010027f26144010007f23144010007f13144010
  | 1 => 0x8c10036dc4358c10004ff7258c1000cfe7258c1000cfc7258c10036df3258c10006de3258c10036dc3258c10014ff7158c10014fd7158c10034fc7158c10036dc3158c10024ff7058c10024fe7058c10024fd7058c10024fc7058c10026de3058c10026dc3058c10006df7558c10006de7558c10006dd7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c10006de5258c10006dd5258c10006dc5258c10006de4258c10006dc4258c10036df7158c10006de7158c10006dc7158c10006df5158c10006de5158c10006dd5158c10006dc5158c10006df2158c10006dc2158c10026df7058c10026de7058c10026dd7058c10026dc7058c10026df5058c10026de5058c10026dd5058c10026dc5058c10026df4058c10026de4058c10026dd4058c10026dc4058c10026df2058c10026de2058c10026dd2058c10026dc2058c10026df1058c10026de1058c10026dd1058c10026dc1058c100dcff76d0c10024fe76d0c10004fd76d0c10024fc76d0c102167e65d0c100067d65d0c100debe64d0c10006bd64d0c10016de63d0c10006dd63d0c1020eee62d0c10004ff7650c10024fe7650c10004fd7650c10024fc7650c102067e6550c100067d6550c10006be6450c10006bd6450c10016de6350c10006dd6350c101feee6250c10004ff755881001cfe7558810004fd755881001cfc7558810004ff74588100dcfc7458810004ff7358810014fe7358810014fc7358810026ef7258810006ef525881002eee5258810006ed525881002eec525881002eee425881002eec4258810006ef325881002eee325881002eec325881000cff715881000cfd715881002cfc715881002eec2158810024ff7058810024fe7058810024fd7058810024fc7058810026ee2058810026ec2058810026fa1058810006ef7558810006ee7558810006ed7558810006ec7558810006ef7458810006ee7458810006ed7458810006ec7458810006ef5458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef5358810006ee5358810006ed5358810006ec5358810006ef4358810006ee4358810006ed4358810006ec435881002eef7158810006ee7158810006ec7158810006ef5158810006ee5158810006ed5158810006ec5158810006ef3158810006ec3158810026ef7058810026ee7058810026ed7058810026ec7058810026ef5058810026ee5058810026ed5058810026ec5058810026ef4058810026ee4058810026ed4058810026ec4058810026ef3058810026ee3058810026ed3058810026ec3058810026ef1058810026e
  | 2 => 0x1cfe7599010004fd75990100dcfc7599010026be7499010006bf54990100debe5499010006bd54990100debc5499010014fe7399010004fd7399010014fc7399010006be43990100debc439901000cfe7299010004fd729901000cfc7299010006be42990100debc4299010024fe7099010024fc7099010026be4099010026bc40990100debf7599010006be7599010006bd75990100debc75990100debf7399010006be7399010006bd73990100debc7399010006bf5399010006be5399010006bd5399010006bc53990100debf7299010006be7299010006bd72990100debc7299010006bf5299010006be5299010006bd5299010006bc5299010006bf3299010006be3299010006bc3299010006be71990100debc7199010006bf5199010006be5199010006bd5199010006bc5199010006bf3199010006bc3199010006bf2199010006bc2199010026bf7099010026be7099010026bd7099010026bc7099010026bf5099010026be5099010026bd5099010026bc5099010026bf3099010026be3099010026bd3099010026bc3099010026bf2099010026be2099010026bd2099010026bc2099010026bf1099010026be1099010026bd1099010026bc1099010004ff755901001cfe7559010004fd755901001cfc7559010026bf7459010006bf5459010006be5459010006bd5459010006bc5459010004ff7359010014fe7359010014fc7359010006be4359010006bc4359010004ff725901000cfe725901000cfc7259010006be4259010006bc42590100dcff715901019cfd7159010024ff7059010024fe7059010024fd7059010024fc7059010026be4059010026bc4059010026f71059010026f51059010006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf5359010006be5359010006bd5359010006bc5359010006bf7259010006be7259010006bd7259010006bc7259010006bf5259010006be5259010006bd5259010006bc5259010006bf3259010006be3259010006bc3259010006be7159010006bc7159010006bf5159010006be5159010006bd5159010006bc5159010006bf3159010006bc3159010006bf2159010006bc2159010026bf7059010026be7059010026bd7059010026bc7059010026bf5059010026be5059010026bd5059010026bc5059010026bf3059010026be3059010026bd3059010026bc3059010026bf2059010026be2059010026bd2059010026bc2059010026bf1059010026b71059010026be1059010026bd1059010026b51059010026bc1059010004ff7558c1001cfe7558c10004fd7558c1001cfc7558c10004ff7458c100dcfc7458c10026df7358c10006df5358c10036de5358c10006dd5358c10036dc5358c10036de435
  | 3 => 0xc6248510005fb7048510025f87048510004fe76d01100067f65d01100ee7c65d0110006bf64d01100debc64d0110005f671d0110005f571d0110007b541d01100dcff7650110004fd7650110004fc76501100057f755011005d7c75501100067f65501101067c6550110006bf6450110006bc6450110005f77150110005f47150110007b54150110014ff764c110054fd764c110014fc764c1100067f654c1100b67c654c110006bf644c110006bc644c110006df634c110016dc634c110005f7714c110005f4714c110027f0104c110005fa7688110026fa76881100077b6588110257786588110007bb6488110007b86488110027da7388110027d97388110006fb6388110006f9638811004df9728811000efa628811000ef86288110005fa7188110026fb6188110027f36188110257f25188110257f15188110007f24188110007f1418811000cff764811004cfd764811000cfc76481100067f65481100967c6548110006bf6448110006bc6448110006ef624811000eec6248110005f77148110005f47148110027e8204811004df8764811000ef8764811000cf876481100077b6548110247786548110007bb6448110007b86448110006fb6348110006f96348110025fb7248110027eb7248110007eb624811000efa624811000ef8624811004fe8624811004fea5248110247e9524811004fea4248110007e9424811024feb324811004fe83248110007f37148110005f87148110007f07148110026fb6148110027f36148110247f25148110247f15148110007f24148110007f1414811004feb2148110007e921481100067f65c41100467c65c4110006bf64c4110006bc64c4110025f671c4110026f761c4110025fa76c4110026fa76c4110024fa76c41100077b65c411023f7865c4110007bb64c4110007b864c4110005fb72c4110005f972c4110025fa71c4110026fb61c4110027f361c411023ff251c411023ff151c4110007f241c4110007f141c41100067f74594100067e74594100067d74594100067c74594100067f73594100067e73594100067d73594100067c73594100067e43594100067c43594100067f72594100067e72594100067d72594100067c72594100067e42594100067c42594100067f32594100067e32594100067c325941003e7f71594100067e715941003e7d715941003e7c71594100067f31594100067c31594100067f21594100067c21594100267f70594100267e70594100267d70594100267c70594100267f40594100267e40594100267d40594100267c40594100267f30594100267e30594100267d30594100267c30594100267f20594100267e20594100267d20594100267c20594100267f10594100267710594100267e10594100267d10594100267510594100267c10594100dcff7599010
  | 4 => 0x8910024fc70d891004eef20d89100057f755891005d7c75589100067f65589100067c6558910005bf7458910005bc7458910006bf6458910006bc6458910005df7358910055dc735891004eec6258910004ff75589100067f75589100047f755891001cfe7558910004fd755891001cfc75589100067c755891001c7c7558910004ff7458910006bf7458910004bf74589100dcfc7458910006bc7458910004bc7458910004ff7358910006df7358910004df7358910014fe7358910014fc7358910006dc7358910014dc735891004cff7258910006ef7258910064ff7158910006f7715891007cff7058910006fb70589100dcff76d0910004fe76d0910004fd76d09100dcfc76d09100067f65d09101f67c65d0910006bf64d09100debc64d0910005f671d0910005f571d0910004ff7650910004fe7650910004fd7650910004fc76509100067f65509101e67c6550910006bf6450910006bc6450910005df7350910055dc7350910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c9101d67c654c910006bf644c910006bc644c910024fe76d051005d7e75d05100057d75d05100067f65d05101967c65d0510006bf64d05100debc64d0510025fa70d0510005f970d0510004fe769051005d7e75905100057d75905100067f659051018e7c6590510006bf6490510006bc6490510055de7390510005dd7390510005f67690510006f6769051025df7759051027f76759051025df5759051000775759051000575759051000777659051027f74659051026df57490510007b764905100def664905100def46490510007b46490510006b4649051027fb6549051027fb55490510007d67390510007d57390510025f67090510025f47090510277b64090510277b44090510024fc76505100067f65505101ae7c6550510006bf6450510006bc6450510005fb7050510025f87050510025f47650510006f47650510024f4765051026df7755051026df57550510007776550510267746550510007b77450510007b764505100def664505100def46450510007b46450510007b74250510007b54250510007f37050510025f67050510025f47050510007f07050510004fe76105100067f65105101867c6510510006bf64105100debc641051025df67110510007b5411051006cfe768c5100067f658c51016e7c658c510006bf648c510006bc648c510024fc764c5100067f654c51015e7c654c510006bf644c510006bc644c510006df634c510016dc634c510005ef724c51004dec724c510005fb704c510025f8704c510064fe76885100067f658851014e7c6588510006bf6488510006bc6488510024fc76485100067f654851013e7c6548510006bf6448510006bc6448510005df7348510055dc7348510006ef624851000ee
  | 5 => 0x6be6519110006bd6519110006bc65191100073c65191100063c6519110006be6319110006bc6319110006be6219110006bc6219110007b57119110007b65119110007b55119110287b61019110287b410191100debf7519110006be7519110006bd75191100debc75191100debf7319110006be7319110006bd73191100debc7319110006bf5319110006be5319110006bd5319110006bc53191100debf7219110006be7219110006bd72191100debc7219110006bf5219110006be5219110006bd5219110006bc5219110006bf3219110006be3219110006bc32191100debf7119110006bd7119110006b57119110006bf5119110006be5119110006bd5119110006bc5119110006bf3119110006bc3119110006bf2119110006bc21191100debf7019110286be7019110006bd70191100debc7019110006bf5019110286be5019110006bd5019110286bc5019110006bf3019110286be3019110286bc3019110006bf2019110286be2019110286bc2019110286be1019110006bd1019110286bc1019110014fe76d8d100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d10056de63d8d10004ff75d8d1001cfe75d8d10004fd75d8d1001cfc75d8d100dcfe74d8d10004fd74d8d1000cfe72d8d10004fd72d8d1000cfc72d8d10006de32d8d10056dc32d8d10014fe71d8d10024fd71d8d10014fc71d8d10056df31d8d10024fe70d8d10054fd70d8d10024fc70d8d10056df30d8d100057f7558d1005d7c7558d100067f6558d100067c6558d10005bf7458d10005bc7458d10006bf6458d10006bc6458d10056dc6358d10005ef7258d1004dec7258d10004ff7558d100067f7558d100047f7558d1001cfe7558d10004fd7558d1001cfc7558d100067c7558d1001c7c7558d10004ff7458d10006bf7458d10004bf7458d100dcfc7458d10006bc7458d10004bc7458d10054ff7358d10006df7358d10056de5358d10006dd5358d10004ff7258d10006ef7258d10004ef7258d1000cfe7258d1000cfc7258d10006ec7258d1000cec7258d1006cff7158d10006f77158d10084ff7058d10006fb7058d100dcff76d0d10004fe76d0d10004fd76d0d100dcfc76d0d100067f65d0d102167c65d0d10006bf64d0d100debc64d0d10005f671d0d10005f571d0d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100067f6550d102067c6550d10006bf6450d10006bc6450d1000cfe76d89100067f65d89100067c65d8910006bf64d8910006bc64d891004eee62d8910004ff75d891001cfe75d8910004fd75d891001cfc75d89100dcfe74d8910004fd74d8910014fe73d8910004fd73d8910014fc73d8910006ef32d891004eec32d891000cfe71d8910024fd71d891000cfc71d891004eef21d8910024fe70d891004cfd70d
  | 6 => 0xe10d951005e7d10d951028e7c10d95100067f65d91100067c65d9110004ff75d911001cfe75d9110004fd75d911001cfc75d9110006bf54d9110006be54d9110006bd54d9110006bc54d9110014fe73d9110004fd73d9110014fc73d9110006be43d9110006bc43d911000cfe72d9110004fd72d911000cfc72d9110006be42d9110006bc42d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006be63d9110006bc63d9110006be62d9110006bc62d9110277b771d9110007b651d9110007b551d9110277b610d9110277b410d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006be53d9110006bd53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d9110006bf32d9110006be32d9110006bc32d9110276bf71d9110006bd71d9110006bf51d9110006be51d9110006bd51d9110006bc51d9110006bf31d9110006bc31d9110006bf21d9110006bc21d9110006bf70d9110276be70d9110006bd70d9110276bc70d9110006bf50d9110276be50d9110006bd50d9110276bc50d9110006bf30d9110276be30d9110276bc30d9110006bf20d9110276be20d9110276bc20d9110276be10d9110276bc10d911005d7e75991100057d75991100067f65991100067c6599110006bf64991100dcff759911001cfe75991100de7e759911001c7e7599110004fd75991100de7d75991100047d75991100dcfc75991100dcfe7499110004be7499110014fe7399110004fd7399110014fc739911000cfe7299110004fd729911000cfc7299110004fd71991100def57199110004fd70991100def970991100057f755911005d7c75591100067f65591100067c6559110004ff75591100067f75591100047f755911001cfe7559110004fd755911001cfc75591100067c755911001c7c7559110006bf7459110004ff7359110014fe7359110014fc7359110004ff725911000cfe725911000cfc7259110004ff7159110006f77159110004ff7059110006fb7059110004fe76191100067f65191100067c6519110006bd64191100dcff751911001cfe7519110004fd75191100dcfc75191100debe7419110006bf54191100debe5419110006bd54191100debc5419110014fe7319110004fd7319110014fc7319110006be43191100debc431911000cfe7219110004fd721911000cfc7219110006be42191100debc42191101b4fe71191100def571191100dcfc7119110024fe7019110024fc7019110005be7619110006be7619110004be7619110006bf65191100073f65191100063f6519110
  | 7 => 0x8e1000cfc7258e10006de3258e1006edc3258e1006edf3158e10024fc7058e10026de3058e10026dc3058e10026fa2058e100dcff76d0e10024fe76d0e10004fd76d0e10024fc76d0e10004ff7650e10024fe7650e10004fd7650e10024fc7650e10016de6350e10006dd6350e10004ff7558a1001cfe7558a10004fd7558a1001cfc7558a10004ff7458a100dcfc7458a10004ff7358a10014fe7358a10014fc7358a10026ef7258a10066ee5258a10006ed5258a10066ee4258a10006ef3258a10066ec3258a10066ef2158a10024fc7058a10026ee2058a10026ec2058a100dcff76d0a10024fe76d0a10004fd76d0a10024fc76d0a102aebf64d0a100debc64d0a10004ff7650a10024fe7650a10004fd7650a10024fc7650a102a6bf6450a102a6bc6450a10005df7350a1006ddc7350a1000eee6250a10006ed6250a10005f77150a10005f47150a10004ff764ca10024fe764ca10004fd764ca10024fc764ca100757e75d06100057d75d06100debe64d0610006bd64d0610025fa70d0610005f970d06100757e75906100057d7590610276bf6490610276bc649061006dde7390610005dd7390610006be6450610006bd6450610005fb7050610025f87050610286bf64106100debc6410610054fd768c610014ff764c610024fc764c610016de634c610006dd634c610005ef724c610065ec724c61006fd4314c610005fb704c610025f8704c61004cfd7688610025f8708861000cff7648610024fc7648610005df734861006ddc734861000eee6248610006ed6248610005fb7048610025f87048610025fb764821002efb7648210026fb6348210006f96348210027eb7248210027eb624821000efa6248210026f86248210027e86248210067ea524821029fe95248210067ea4248210007e94248210297eb3248210067e83248210005f87148210067eb2148210007e92148210025f976c4210006f976c4210005fb72c4210005f972c4210027f271c421005d7e76d951005e7e76d951001c7e76d95100067e63d95100067c63d95100067e62d95100067c62d951028f7771d951005f7471d951028f7610d951028f7410d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067e43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067e42d95100067c42d95100067f32d95100067e32d95100067c32d951028e7f71d951005e7e71d951005e7d71d951005e7c71d95100067f31d95100067c31d95100067f21d95100067c21d95100067f70d951028e7e70d951005e7d70d951028e7c70d951028e7e40d951028e7c40d95100067f30d951028e7e30d951028e7c30d95100067f20d951028e7e20d951028e7c20d951028e7
  | 8 => 0x4fe76d0b10004fd76d0b100dcfc76d0b100debe64d0b10006bd64d0b10005f671d0b10005f571d0b10004ff7650b10004fe7650b10004fd7650b10004fc7650b10006be6450b10006bd6450b10005df7350b10085dc7350b10004ff764cb10004fe764cb10004fd764cb10004fc764cb10016de634cb10006dd634cb100457e75d07100057d75d0710006bf64d07100debc64d0710024fd76907100457e75907100057d7590710006be6490710006bd6490710085de7390710005dd7390710025fa7090710005f97090710025f57690710006f57690710024f576907102bdf775907102377675907102bdf575907100077575907100057575907100def66490710007b66490710007b564907100def46490710237b65490710237b55490710007d67390710007d57390710025f67090710007f27090710007f17090710025f47090710277b64090710277b44090710006bf6450710006bc6450710005f77650710006f776507102b5f775507102b5f57550710007b77450710007b764507100def664507100def46450710007b46450710007b74250710007b54250710025f67050710025f47050710024fd76107100debe6410710006bd6410710007b54110710025fa7010710005f97010710024fd768c710016de638c710006dd638c710025fa708c710005f9708c710034ff764c710006df634c710016dc634c710005ef724c71007dec724c710024fd768871000eee6288710006ed6288710025fa7088710005f9708871002cff7648710005df7348710085dc7348710006ef624871000eec62487100debe64d0310006bd64d0310005f671d0310005f571d0310007b541d03100057f75503100457c7550310006be6450310006bd6450310005f77150310005f47150310007b54150310014ff764c310014fc764c310016de634c310006dd634c310005f7714c310005f4714c31000cff764831000cfc764831000eee6248310006ed6248310005f77148310005f471483100dcff759921001cfe7599210004fd75992100dcfc7599210026be74992100debe5499210006bd5499210014fe7399210004fd7399210014fc739921000cfe7299210004fd729921000cfc7299210024fe7099210026be4099210026bc4099210004ff75592100067f75592100047f755921001cfe7559210004fd755921001cfc75592100067c755921001c7c7559210026bf7459210006be5459210006bd5459210004ff7359210014fe7359210014fc7359210004ff725921000cfe725921000cfc7259210024fc7059210026be4059210026bc4059210026f71059210026f51059210004ff7558e1001cfe7558e10004fd7558e1001cfc7558e10004ff7458e100dcfc7458e10026df7358e1006ede5358e10006dd5358e1006ede4358e10004ff7258e1000cfe725
  | 9 => 0x9314c1200afeb214c120007e9214c1200457e75d93100057d75d9310085de73d9310005dd73d9310004ff75d931001cfe75d93100067e75d931001c7e75d9310004fd75d93100067d75d93100047d75d931001cfc75d9310006be54d9310006bd54d9310014fe73d9310006de73d9310014de73d9310004fd73d9310006dd73d9310004dd73d9310014fc73d931000cfe72d9310004fd72d931000cfc72d9310006f671d9310006f970d9310276be40d9310276bc40d9310004fd76993100457e75993100057d7599310006bf64993100dcff759931001cfe75993100de7e759931001c7e7599310004fd75993100de7d75993100047d75993100dcfc7599310014fe7399310004fd7399310014fc739931000cfe7299310004fd729931000cfc72993100def67199310004ff755931001cfe7559310004fd755931001cfc7559310006bf7459310004ff7359310014fe7359310014fc7359310004ff725931000cfe725931000cfc7259310006bd64193100dcff751931001cfe7519310004fd75193100dcfc75193100dcfe74193100debe74193100debe5419310006bd5419310014fe7319310004fd7319310014fc731931000cfe7219310004fd721931000cfc72193100def671193100def97019310286be40193100debc4019310086de63d8f10004ff75d8f1001cfe75d8f10004fd75d8f1001cfc75d8f100dcfe74d8f10004fd74d8f10084fd73d8f1000cfe72d8f10004fd72d8f1000cfc72d8f10006de32d8f10086dc32d8f10006f671d8f10086df31d8f10006f970d8f10014ff7658f10086dc6358f10005ef7258f1007dec7258f10004ff7558f1001cfe7558f10004fd7558f1001cfc7558f10004ff7458f100dcfc7458f10006df7358f10086de5358f10006dd5358f10086dc4358f10004ff7258f10006ef7258f10004ef7258f1000cfe7258f1000cfc7258f10006ec7258f1000cec7258f10086df3258f10024fc7158f10086dc3158f10086df3058f100dcff76d0f10004fe76d0f10004fd76d0f100dcfc76d0f10016de63d0f10006dd63d0f10005f671d0f10005f571d0f10004ff7650f10004fe7650f10004fd7650f10004fc7650f1007eee62d8b10004ff75d8b1001cfe75d8b10004fd75d8b1001cfc75d8b100dcfe74d8b10004fd74d8b10014fe73d8b10004fd73d8b10014fc73d8b1007cfd72d8b10006ef32d8b1007eec32d8b10006f671d8b1007eef21d8b10006f970d8b1000cff7658b10005df7358b10085dc7358b1007eec6258b10004ff7558b1001cfe7558b10004fd7558b1001cfc7558b10004ff7458b100dcfc7458b10004ff7358b10006df7358b10004df7358b10014fe7358b10014fc7358b10006dc7358b10014dc7358b10006ef7258b10024fc7158b1007eec2158b1007eef2058b100dcff76d0b10
  | 10 => 0x8520014fc7318520024fd7218520006ef321852002eec321852002eef211852002ef6211852002ef52118520024fe701852002ef97018520024fc7018520004fe76d0520004fd76d05200dcfc76d05200957e75d05200057d75d05200debe64d0520006bd64d052000dee72d0520005ed72d0520007ad42d0520006f761d0520006f461d0520004fe7690520004fd7690520004fc76905200957e75905200057d7590520006bf6490520006bc649052008dde7390520005dd739052000dee7290520005ed7290520025fa7090520005f97090520004ff7650520004fe7650520004fc7650520006be6450520006bd645052000dee7250520007ad4250520004fe7610520004fd76105200dcfc7610520006bf64105200debc641052000dee7210520005ed7210520006f76110520006f46110520025fa7010520005f97010520004fe768c520004fd768c520004fc768c520006df638c520016dc638c52000dee728c520005ed728c520167cc328c520025fa708c520005f9708c520004ff764c520004fe764c520004fc764c520016de634c520006dd634c520005ef724c52000dec724c52008fcf324c520024ec76485202ddef75485202dded7548520005ef7448520005ed7448520007cf734852008dee734852008dec7348520007cc734852008dcc734852000def714852000fe77148520007e76148520006ec6148520007e46148520007e63148520007e53148520007eb7048520025ee7048520025ec7048520007e8704852000eef604852000feb604852000cfe76d012000cfc76d0120006bf64d01200debc64d012000dee72d0120005ed72d01200dcff765012000cfe76501200f4fd765012000cfc76501200057f75501200957c7550120006bf6450120006bc6450120005ef725012000dec72501202d5fa768c120026fa768c1200adf9738c120016fa638c120016f8638c12000dfa728c120027ea728c12000dea728c120027e9728c120025f8728c120026fb628c120027eb628c1200bfea528c1202cfe9528c1200bfea428c120007e9428c12008feb328c1200bfe8328c120005f9718c1200bfeb218c120007e9218c120014ff764c12000cfe764c1200acfd764c12000cfc764c120006df634c120016dc634c120005ef724c12000dec724c1200afcc324c12000df8764c120016f8764c12000cf8764c120025fb734c120027db734c120007db634c120016fa634c120016f8634c12008fd8634c12008fda534c1202c7d9534c12008fda434c120007d9434c120007eb724c12000dfa724c12000df8724c1200afe8724c120026fb624c120027eb624c1200afea524c1202c7e9524c1200afea424c120007e9424c12008feb324c1200afda324c1200afd8324c1200afe8324c1200afc8324c120005fb714c12008fdb314c120007d
  | 11 => 0x2a6be40591202a6bc405912010cfe76191200957e75191200057d7519120006bd64191200dcff751912001cfe75191200de7e751912001c7e7519120004fd75191200de7d75191200047d75191200dcfc75191200debe7419120014fe7319120004fd7319120014fc7319120024ff721912000cfe7219120024fd72191200deed721912000cfc72191200debf42191200deee42191200cebd4219120004fe7119120004fd7119120014fe76d8d2008ede63d8d2000dee72d8d20025ed72d8d2008fcf32d8d20004ff75d8d2001cfe75d8d20004fd75d8d2001cfc75d8d200dcfe74d8d20004fd74d8d2008ede53d8d20006dd53d8d2008edc43d8d20024ff72d8d2000cfe72d8d20024fd72d8d2008eed72d8d20024ed72d8d2000cfc72d8d200bedf32d8d2008eef32d8d200bedd32d8d200beec32d8d20004fe71d8d20004fd71d8d2008edc31d8d2000cfd70d8d2008edf30d8d2008edc6358d200afcc3258d202f5fb7058d20004ff7558d2001cfe7558d20004fd7558d2001cfc7558d20004ff7458d200dcfc7458d200bcff7358d20006df7358d200acff7258d20006ef7258d2008eef3258d200aede3258d200aedc3258d200aeec3258d20004ff7158d20004fc7158d2008edf3158d202f4ff7058d20006fb7058d200dcff76d0d20004fe76d0d20004fd76d0d200dcfc76d0d20006df63d0d20016dc63d0d2000dee72d0d20005ed72d0d2020fcc32d0d20004ff7650d20004fe7650d20004fd7650d20004fc7650d20005ef7250d2000dec7250d20025ec7650920006ec7650920024ec76509202edef75509202eded755092000def745092000faf7450920007af64509200deee64509200deec6450920007ac64509202e7ae54509202e7ad5450920007cf735092008dee735092008dec7350920007cc735092008dcc7350920007af4350920007ad4350920005ef7150920007eb7050920025ee7050920025ec7050920007e8705092000eef605092000feb60509202a7ae40509202a7ac4050920004ff75d852001cfe75d8520004fd75d852001cfc75d85200dcfe74d8520004fd74d8520014fe73d8520004fd73d8520014fc73d8520024fd72d8520066f621d8520066f521d8520006f7619852004df970985200057f75585200957c7558520005bf7458520005bc7458520005df735852008ddc735852007dfb70585200957e75185200057d7518520005be7418520005bd741852008dde7318520005dd7318520006f56118520004ff751852001cfe75185200067e751852001c7e7518520004fd75185200067d75185200047d751852001cfc75185200dcfe7418520006be7418520004be7418520004fd7418520006bd7418520004bd7418520014fe7318520006de7318520014de7318520004fd7318520006dd7318520004dd731
  | 12 => 0x67198620006f65198620006f5519862007ef6219862007ef52198620024fe7098620026fa7098620024fa7098620026f61098620026fa1098620026f41098620004ff755862001cfe7558620004fd755862001cfc7558620004ff74586200dcfc7458620004ff7358620014fe7358620014fc7358620026f77158620006f65158620006f5515862004ef6215862004ef52158620024fc7058620026ef2058620026ed2058620026f61058620026f410586200dcff76d0620024fe76d0620004fd76d06200a57e75d06200057d75d06200debe64d0620006bd64d06201cede63d0620006dd63d0620004ff7690620024fe7690620004fd76906200a57e75906200057d759062009dde7390620005dd73906201bede6390620006dd6390620006f66190620006f56190620025fa7090620005f97090620004ff7650620004fd7650620024fc7650620006be6450620006bd64506201a6de6350620006dd6350620006f66150620006f561506200dcff7610620024fe7610620004fd761062017ede6310620006dd6310620025fa7010620005f97010620004ff768c620024fe768c620004fd768c620016de638c620006dd638c620025fa708c620005f9708c620004ff764c620004fd764c620024fc764c620016de634c620006dd634c620005ef724c62000dec724c620025fa704c620025fb764c220306fb764c220027db734c220016fa634c220027da634c220016da634c220027d9634c220026f8634c22009fda534c2202ffd9534c22009fda434c220007d9434c22000dfa724c22000df8724c2200afda324c2200afd8324c220005fb714c22009fdb314c220007d9314c220004ff75d912001cfe75d9120004fd75d912001cfc75d9120014fe73d9120004fd73d9120014fc73d9120024ff72d9120024fd72d912010ebf42d912010ebd42d9120004fe71d9120004fd71d9120006bf64991200f5f970991200dcff759912001cfe7599120004fd75991200dcfc75991200dcfe74991200debe5499120006bd5499120014fe7399120004fd7399120014fc7399120124fd72991200deed72991200deee4299120004fe7199120004fd71991200f4fd70991200def970991202aebe40991200debc40991200057f75591200957c7559120005df735912008ddc7359120005f77159120005f47159120125fb7059120004ff75591200067f75591200047f755912001cfe7559120004fd755912001cfc75591200067c755912001c7c7559120006bf7459120006be5459120006bd5459120004ff7359120006df7359120004df7359120014fe7359120014fc7359120006dc7359120014dc73591200f4ff7259120006ef7259120004ff7159120006f77159120004f77159120004fc7159120006f47159120004f47159120124ff7059120006fb7059120
  | 13 => 0xc530004fe7688530004fd7688530004fc7688530015de7388530005dd7388530006ef628853000eec62885300afcc3288530007d53188530004ff7648530004fe7648530004fc7648530005df7348530015dc7348530007d53148530014fe76d0130014fc76d0130006bf64d01300debc64d0130015de73d0130005dd73d01300dcff7650130014fe76501300fcfd7650130014fc76501300057f75501300b57c7550130006bf6450130006bc6450130005df7350130015dc7350130027b840501300dcff759922001cfe7599220004fd75992200dcfc7599220026be74992200debe5499220006bd5499220014fe7399220004fd7399220014fc73992200debf4299220126bd4299220004fe7199220004fd7199220024fe7099220024fc7099220026be4099220026bc4099220004ff755922001cfe7559220004fd755922001cfc7559220026bf7459220006be5459220006bd5459220004ff7359220014fe7359220014fc73592200f6bf42592200f6bd4259220004ff7159220004fc7159220024fe7059220024fc7059220026be4059220026bc4059220026ef2059220026ed2059220004ff7558e2001cfe7558e20004fd7558e2001cfc7558e20004ff7458e200dcfc7458e20026df7358e20006df5358e2009ede5358e20006dd5358e2009edc5358e2009ede4358e2009edc4358e200aedf3258e200aedd3258e20004ff7158e20004fc7158e2009edf3158e2009edc3158e20024fe7058e20024fc7058e20026de3058e20026dc3058e20006df7558e20006de7558e20006dd7558e20006dc7558e20006df7458e20006de7458e20006dd7458e20006dc7458e20006df5458e20006de5458e20006dd5458e20006dc5458e200aedf7258e200aede7258e200aedd7258e200aedc7258e200aedf5258e200aede5258e200aedd5258e200aedc5258e200aedf4258e200aede4258e200aedd4258e200aedc4258e20006df7158e20006de7158e20006dd7158e20006dc7158e20006df5158e20006de5158e20006dd5158e20006dc5158e200aedf2158e200aede2158e200aedd2158e200aedc2158e20026df7058e20026de7058e20026dd7058e20026dc7058e20026df5058e20026de5058e20026dd5058e20026dc5058e20026df4058e20026de4058e20026dd4058e20026dc4058e20026df2058e20026de2058e20026dd2058e20026dc2058e20026df1058e20026de1058e20026dd1058e20026dc1058e200dcff76d0e20024fe76d0e20004fd76d0e20024fc76d0e20016de63d0e20006dd63d0e20004ff7650e20024fe7650e20004fd7650e20024fc7650e20016de6350e20006dd6350e20004ff759862001cfe7598620004fd759862001cfc75986200dcfe7498620004fd7498620014fe7398620004fd7398620014fc7398620026f
  | 14 => 0xcfe7219130004fd721913000cfc7219130006de32191300d6dc3219130004fe7119130004fd71191300d6df3119130025dc7650d30006dc7650d30024dc7650d30325df7550d30325dd7550d30015df7450d300179f7450d300079f6450d300dede6450d300dedc6450d300079c6450d300adde7250d300addc7250d30005df7150d30007db7050d30025de7050d30025dc7050d30007d87050d30016df6050d30017db6050d3000cfe76d8930015de73d89300aeee62d89300afce32d8930004ff75d893001cfe75d8930004fd75d893001cfc75d89300dcfe74d8930004fd74d8930024fd73d8930024dd73d893000cfc73d89300aede32d89300aeee32d893009eed32d89300aedc32d8930004fe71d8930004fd71d893009edf31d89300aeec21d8930014fd70d89300aeef20d89300aeec62589300afcc325893031dfb7058930004fe76d0930004fd76d09300dcfc76d0930006bf64d09300debc64d0930015de73d0930005dd73d09300079d43d0930004ff7650930004fe7650930004fc7650930006bf6450930006bc6450930005df7350930015dc73509300079d4350930004ff75d853001cfe75d8530004fd75d853001cfc75d85300dcfe74d8530004fd74d8530024fd73d853006ede53d8530006dd53d853000cfe72d8530004fd72d853000cfc72d853006ef631d853006ef531d8530006f76198530055f970985300057f75585300b57c7558530005bf7458530005bc7458530005ef72585300adec7258530085fb70585300b57e75185300057d7518530006f56118530004ff751853001cfe75185300067e751853001c7e7518530004fd75185300067d75185300047d751853001cfc75185300dcfe7418530004fd7418530024fd731853000cfe7218530004fd721853000cfc7218530006de3218530036dc3218530036df3118530036f63118530036f53118530004fe76d0530004fd76d05300dcfc76d05300b57e75d05300057d75d0530015de73d0530005dd73d0530004fe7690530004fd7690530004fc76905300b57e75905300057d7590530006bf6490530006bc6490530015de7390530005dd7390530004ff7650530004fe7650530004fc7650530015de7350530004fe7610530004fd76105300dcfc7610530006bf64105300debc6410530015de7310530005dd7310530025fa7010530005f97010530024dc764c530315df754c530315dd754c53030edf654c53030edd654c530005df744c530005dd744c530006de644c530006dc644c530007cf724c5300adde724c5300addc724c530007cc724c5300adcc724c530006df624c530015df714c530017d7714c530007d7614c530006dc614c530007d4614c530006d4614c530007db704c530025de704c530025dc704c530007d8704c530016df604c530017db604
  | 15 => 0xc7650a302a6bf6450a302a6bc6450a30005df7350a30015dc7350a3000eee6250a30006ed6250a30004ff759863001cfe7598630004fd759863001cfc75986300dcfe7498630004fd749863000cfe7298630004fd729863000cfc7298630026f67198630006f65198630006f55198630086f63198630086f53198630024fe7098630026f61098630026f41098630004ff755863001cfe7558630004fd755863001cfc7558630004ff74586300dcfc7458630004ff725863000cfe725863000cfc7258630026f77158630006f65158630006f55158630056f63158630056f53158630024fc7058630026df3058630026dd3058630026fa2058630026f61058630026f410586300dcff76d0630024fe76d0630004fd76d06300c57e75d06300057d75d06300debe64d0630006bd64d06301c6ee62d0630006ed62d0630004ff7690630024fe7690630004fd76906300c57e75906300057d7590630015de7390630005dd73906301b6ee6290630006ed6290630006f66190630006f56190630004ff7650630004fd7650630024fc7650630006be6450630006bd645063019eee6250630006ed6250630006f66150630006f561506300dcff7610630024fe7610630004fd7610630176ee6210630006ed6210630025fa7010630005f97010630004ff7688630024fe7688630004fd768863000eee6288630006ed6288630004ff7648630004fd7648630024fc7648630005df7348630015dc734863000eee6248630006ed6248630004ff75d913001cfe75d9130004fd75d913001cfc75d9130006bf54d9130006bc54d9130024ff73d9130024fd73d9130116bf43d9130116bd43d913000cfe72d9130004fd72d913000cfc72d9130004fe71d9130004fd71d9130006bf64991300fdf970991300dcff759913001cfe7599130004fd75991300dcfc75991300dcfe749913012cfd73991300dedd73991300dede439913000cfe7299130004fd729913000cfc7299130006de329913012edc3299130004fe7199130004fd719913012edf31991300fcfd70991300def970991300057f75591300b57c755913012dfb7059130004ff75591300067f75591300047f755913001cfe7559130004fd755913001cfc75591300067c755913001c7c7559130006bf74591300fcff7359130006df7359130004ff725913000cfe725913000cfc7259130004ff7159130004fc715913012cff7059130006fb7059130114fe76191300b57e75191300057d7519130006bd64191300dcff751913001cfe75191300de7e751913001c7e7519130004fd75191300de7d75191300047d75191300dcfc75191300debe7419130006bf54191300debc5419130024ff7319130014fe7319130024fd73191300dedd7319130014fc73191300debf43191300dede43191300d6bd4319130
  | 16 => 0x8440024fe7688440004fd768844014e7e65884400067d6588440005bf74884400ddbc7488440146de6388440006dd638844000eee6288440006ed6288440006f66188440006f56188440004ff7648440004fd7648440024fc764844013e7e65484400067d6548440005bf74484400ddbc7448440005df73484400d5dc7348440136de6348440006dd634844000eee6248440006ed6248440006f66148440006f56148440025fb7650040006fb7650040004fb76500400077b755004032f7875500400277a6550040027796550040025fb7450040027bb74500400defa6450040027ba6450040027da6350040027d963500400dfbb4350040007b94350040027ea6250040027e96250040027f26150040027f161500400dcff759923001cfe7599230004fd75992300dcfc7599230026be74992300debe5499230006bd54992300debf439923012ebd439923000cfe7299230004fd729923000cfc7299230004fe7199230004fd7199230024fe7099230024fc7099230026be4099230026bc4099230004ff755923001cfe7559230004fd755923001cfc7559230026bf7459230006be5459230006bd54592300febf43592300febd4359230004ff725923000cfe725923000cfc7259230004ff7159230004fc7159230024fe7059230024fc7059230026be4059230026bc4059230026df3059230026dd3059230004ff7558a3001cfe7558a30004fd7558a3001cfc7558a30004ff7458a300dcfc7458a30026ef7258a30006ef5258a300beee5258a30006ed5258a300beec5258a300beee4258a300beec4258a300beee3258a3008eed3258a30004ff7158a30004fc7158a300beef2158a300beec2158a30024fe7058a30024fc7058a30026ee2058a30026ec2058a30006ef7558a30006ee7558a30006ed7558a30006ec7558a30006ef7458a30006ee7458a30006ed7458a30006ec7458a30006ef5458a30006ee5458a30006ed5458a30006ec5458a3008eee7358a3008eed7358a300beec7358a3008eef5358a3008eee5358a3008eed5358a3008eec5358a3008eef4358a3008eee4358a3008eed4358a3008eec4358a30006ef7158a30006ee7158a30006ed7158a30006ec7158a30006ef5158a30006ee5158a30006ed5158a30006ec5158a3008eef3158a3008eee3158a3008eed3158a3008eec3158a30026ef7058a30026ee7058a30026ec7058a30026ef5058a30026ee5058a30026ed5058a30026ec5058a30026ef4058a30026ee4058a30026ed4058a30026ec4058a30026ef3058a30026ee3058a30026ed3058a30026ec3058a30026ef1058a30026ee1058a30026ed1058a30026ec1058a300dcff76d0a30024fe76d0a30004fd76d0a302aebf64d0a300debc64d0a3000eee62d0a30006ed62d0a30004ff7650a30004fd7650a30024f
  | 17 => 0x6bf4258440006bd4258440026f77158440006f75158440006f65158440006f55158440006f451584400def741584400def44158440006f73158440006f43158440006f72158440006f42158440026bf4058440026bd4058440026f61058440026f41058440006f77558440006f67558440006f57558440006f475584400def67458440006f754584400def65458440006f554584400def45458440006f77358440006f67358440006f57358440006f47358440006f75358440006f65358440006f55358440006f453584400def74358440006f64358440006f543584400def44358440006f77258440006f67258440006f57258440006f47258440006f75258440006f65258440006f55258440006f452584400def74258440006b74258440006f64258440006f54258440006b542584400def44258440006f73258440006f63258440006f53258440006f43258440026f77058440026f67058440026f47058440026f75058440026f65058440026f55058440026f45058440026f74058440026b74058440026f64058440026f54058440026b54058440026f44058440026f73058440026f63058440026f53058440026f43058440026f72058440026f62058440026f52058440026f42058440004fd76904400e57e75904400057d759044018e7e65904400067d65904400d5de7390440005dd73904401bede6390440006dd63904401b6ee6290440006ed6290440006f56190440275bd7690440006bd7690440004bd76904403473e75904400073d7590440276bf65904402773e6590440346bd65904402773d65904400063d65904400079e73904400079d73904402779e63904402779d6390440005bd7290440277ae6290440277ad62904400ddbe7190440277b66190440006bd6190440277b56190440006b56190440275bd7090440276be6090440277ba6090440004ff76504401ae7e65504400067d655044033ebe64504401a6de6350440006dd635044019eee6250440006ed6250440006f661504400debf65104400df3e6510440336bd65104400df3d65104400063d65104400df9e63104400df9d6310440005bd72104400dfae62104400dfad6210440275be71104400dfb671104400dfb66110440006bd61104400dfb56110440006b561104400dfba7010440285bd70104400dfb97010440286be60104400dfba6010440004ff768c440024fe768c440004fd768c44016e7e658c4400067d658c440016de638c440006dd638c440166ee628c440006ed628c440006f6618c440006f5618c440004ff764c440004fd764c440024fc764c44015e7e654c4400067d654c440005bf744c4400ddbc744c440016de634c440006dd634c440005ef724c4400cdec724c440156ee624c440006ed624c440006f6614c440006f5614c440004ff768
  | 18 => 0xc5058840026ef4058840026ee4058840026ed4058840026ec4058840026ef3058840026ee3058840026ed3058840026ec3058840026ef1058840026ee1058840026ed1058840026ec10588400ddbd76d084000ebd76d084000cbd76d08400debf65d08400df3e65d0840356bd65d08400df3d65d08400063d65d08400df9e63d0840006bd63d08400df9d63d08400069d63d08402a5bd72d084000ebe62d08400dfae62d08400dfad62d084000ebc62d0840005be71d08400dfb661d08400dfb561d08400dfba70d08402adbd70d08400dfb970d08402aebe60d08400dfba60d0840124ff76508401e67e65508400067d6550840005df73508400d5dc73508401dede6350840006dd635084000eee62508402a5bf7650840126bf76508402a6bf65508402a73e655084034ebd65508402a73d65508400063d65508400079f73508400079c73508402a79e6350840006bd63508402a79d63508400069d63508400ddbf72508400dfaf725084000ebe62508402a7ae625084000eae62508402a7ad625084000ebc6250840005bc71508402a7b661508402a7b561508402a5bf70508402a6be60508402a7ba60508402a7af2050840004ff764c840004fd764c840024fc764c8401d67e654c8400067d654c840016de634c840006dd634c84000eee624c840006ed624c840004ff759844001cfe7598440004fd759844001cfc7598440014fe7398440004fd7398440014fc739844000cfe7298440004fd729844000cfc7298440026f67198440006f75198440006f65198440006f55198440006f451984400def741984400def44198440006f73198440006f43198440006f72198440006f42198440026f61098440026f41098440006f77598440006f67598440006f57598440006f475984400def47498440006f754984400def65498440006f554984400def45498440006f77398440006f67398440006f57398440006f47398440006f75398440006f65398440006f55398440006f453984400def74398440006f64398440006f543984400def44398440006f77298440006f67298440006f57298440006f47298440006f75298440006f65298440006f55298440006f452984400def74298440006f64298440006f542984400def44298440006f73298440006f63298440006f53298440006f43298440026f67098440026f57098440026f47098440026f75098440026f65098440026f55098440026f45098440026f74098440026f64098440026f54098440026f44098440026f73098440026f63098440026f53098440026f43098440026f72098440026f62098440026f52098440026f42098440004ff755844001cfe7558440004fd755844001cfc7558440004ff7358440014fe7358440014fc7358440004ff725844000cfe725844000cfc7258440
  | 19 => 0x94400067c21594400267f70594400267e70594400267d70594400267c70594400267f40594400263f40594400267e40594400267d40594400263d40594400267c40594400267f30594400267e30594400267d30594400267c30594400267f20594400267e20594400267d20594400267c20594400267f10594400267e10594400267d10594400267c1059440004ff7558c4001cfe7558c40004fd7558c4001cfc7558c40014fd7458c40026df7358c40006df5358c400d6de5358c40006dd5358c400d6dc5358c400dedf4358c400dedc4358c40004ff7258c4000cfe7258c4000cfc7258c400d6df3258c40006de3258c400d6dc3258c40004ff7158c40004fc7158c400d6df3158c400d6dc3158c40024fc7058c40026de3058c40026dc3058c40006df7558c40006de7558c40006dd7558c40006dc7558c400d6df7458c400dede7458c40006df5458c400dede5458c40006dd5458c400dedc5458c40006df7258c40006de7258c40006dd7258c40006dc7258c40006df5258c40006de5258c40006dd5258c40006dc5258c400dedf4258c40006de4258c400dedc4258c40006df7158c40006de7158c40006dd7158c40006dc7158c40006df5158c40006de5158c40006dd5158c40006dc5158c400dedf4158c400dedc4158c40006df2158c40006dc2158c40026df7058c40026de7058c40026dc7058c40026df5058c40026de5058c40026dd5058c40026dc5058c40026df4058c40026de4058c40026dd4058c40026dc4058c40026df2058c40026de2058c40026dd2058c40026dc2058c40026df1058c40026de1058c40026dd1058c40026dc1058c4012cff7650c402067e6550c400067d6550c40016de6350c401feee6250c40004ff755884001cfe7558840004fd755884001cfc755884000cfd7458840004ff7358840014fe7358840014fc7358840026ef7258840006ef52588400ceee5258840006ed52588400ceec52588400deef42588400deec4258840006ef32588400ceee32588400ceec3258840004ff7158840004fc71588400ceef21588400ceec2158840024fc7058840026ee2058840026ec2058840006ef7558840006ee7558840006ed7558840006ec75588400ceef74588400deee7458840006ef54588400deee5458840006ed54588400deec5458840006ef7358840006ee7358840006ed7358840006ec7358840006ef5358840006ee5358840006ed5358840006ec53588400deef4358840006ee4358840006ed43588400deec4358840006ef7158840006ee7158840006ed7158840006ec7158840006ef5158840006ee5158840006ed5158840006ec51588400deef41588400deec4158840006ef3158840006ec3158840026ef7058840026ee7058840026ec7058840026ef5058840026ee5058840026ed5058840026e
  | 20 => 0x14fc73d854000cfe72d8540004fd72d854000cfc72d8540006f721d8540006f421d85401057e75985400057d75985400067f65985400067c65985400fdde7398540005dd7398540006f761985400057f75585401057c75585400067f65585400067c65585400067f65185400067c6518540006f56118540004ff751854001cfe7518540004fd751854001cfc7518540006be5418540006bd5418540014fe7318540004fd7318540014fc731854000cfe7218540004fd721854000cfc7218540006f72118540006f42118540286be4018540286bc4018540004fe76d05401057e75d05400057d75d05400067f65d05401967c65d0540005be76d0540006be76d0540004be76d0540365bf75d054037f3e75d0540365bd75d05400073d75d05400053d75d05400073f65d054037f3c65d0540006bf62d0540006bc61d0540025be70d0540025bc70d05400debf60d0540024fe76905401057e75905400057d75905400067f659054018e7c6590540375bd74905400fdde7390540005dd7390540006f76190540006f46190540025fa7090540005f97090540024fc76505400067f65505401ae7c6550540006f76150540006f46150540005fb7050540025f87050540024bc7650540375bf7550540375bd75505400073f655054036f3c6550540006bf6250540007b77150540007b76150540006bc6150540007b46150540007bb7050540025be7050540025bc7050540007b87050540004fe76105400067f65105401867c6510540365be7410540007b54110540004fe768c540004fd768c540004fc768c5400067f658c54016e7c658c540005be748c540005bd748c540006f7618c540006f4618c540004ff764c540004fe764c540004fc764c5400067f654c54015e7c654c540006df634c540016dc634c540005ef724c5400f5ec724c540006f7614c540006f4614c540004fe7688540004fd7688540004fc76885400067f658854014e7c6588540005be7488540005bd7488540004ff7648540004fe7648540004fc76485400067f654854013e7c6548540005df73485400fddc73485400067f65d01400ee7c65d0140025be74d0140026bf64d01400077b65d014035f7865d0140025fa74d0140026fb64d0140027bb64d01400dfba54d014035fb954d01400dfbb41d0140007b941d01400e67f74594400de7e74594400e67d74594400de7c74594400067f73594400067e73594400067d73594400067c73594400de7f43594400067e43594400de7c43594400067f72594400067e72594400067d72594400067c72594400de7f42594400067e42594400de7c42594400067f32594400067e32594400067c32594400067f71594400067e71594400067d71594400067c71594400de7f41594400de7c41594400067f31594400067c31594400067f215
  | 21 => 0xf764c640004fd764c640024fc764c640005bf744c640005bc744c640016de634c640006dd634c640005ef724c64010dec724c640004ff7688640024fe7688640004fd7688640005bf7488640005bc7488640004ff7648640004fd7648640024fc7648640005bf7448640005bc7448640005df7348640115dc734864000eee6248640006ed6248640025f976d02400def976d0240027ba74d02400dfba54d024038fb954d02401057e76d95401067e76d954001c7e76d95403873f74d95401073c74d95400067e63d95400067c63d95400067e62d95400067c62d95403873e40d95403873c40d95403867f74d95401067e74d95401067d74d95401067c74d95400067f73d95400067e73d95400067d73d95400067c73d95400067e43d95400067c43d95400067f72d95400067e72d95400067d72d95400067c72d95400067e42d95400067c42d95400067f32d95400067e32d95400067c32d95400067f71d95400067e71d95400067d71d95400067c71d95400067f31d95400067c31d95400067f21d95400067c21d95400067f70d95403867e70d95401067d70d95403867c70d95403867e40d95401067d40d95403867c40d95400067f30d95403867e30d95403867c30d95400067f20d95403867e20d95403867c20d95403867e10d95403867c10d9540014fe76d8d400067f65d8d400067c65d8d400fede63d8d40004ff75d8d4001cfe75d8d40004fd75d8d4001cfc75d8d40024fd74d8d40014fc74d8d400fede43d8d4000cfe72d8d40004fd72d8d4000cfc72d8d40006de32d8d400fedc32d8d40004fe71d8d40004fd71d8d400fedf31d8d400fedf30d8d400057f7558d401057c7558d400067f6558d400067c6558d400fedc6358d40114fe76d0d400067f65d0d402167c65d0d40024fc7650d400067f6550d402067c6550d40006df6350d40016dc6350d40005fb7050d40025f87050d4000cfe76d89400067f65d89400067c65d89400f6ee62d8940004ff75d894001cfe75d8940004fd75d894001cfc75d8940024fd74d894000cfc74d8940006be54d8940006bd54d8940014fe73d8940004fd73d8940014fc73d89400f6ee42d8940004fe71d8940004fd71d89402aebe40d89402aebc40d89400f6ef20d89400057f75589401057c75589400067f65589400067c6558940005df73589400fddc73589400f6ec6258940005f77158940005f4715894010cfe76d09400067f65d09401f67c65d0940024fc76509400067f65509401e67c6550940005df73509400fddc7350940006ef625094000eec6250940005fb7050940025f87050940004ff764c940004fe764c940004fc764c9400067f654c9401d67c654c9400067f65d85400067c65d8540004ff75d854001cfe75d8540004fd75d854001cfc75d8540014fe73d8540004fd73d8540
  | 22 => 0xc740005ef724c740125ec724c740004ff76887400dcfe7688740004fd76887400ddbe7488740005bd7488740004ff7648740004fd76487400dcfc7648740005df734874012ddc7348740004ff7558e4001cfe7558e40004fd7558e4001cfc7558e40026df7358e40116de5358e40006dd5358e40116de4358e40004ff7258e4000cfe7258e4000cfc7258e40006de3258e40116dc3258e40004ff7158e40004fc7158e40116df3158e40024fc7058e40026de3058e40026dc3058e400fcfd76d0e40014ff7650e40016de6350e40006dd6350e40005fb7050e40025f87050e40004ff7558a4001cfe7558a40004fd7558a4001cfc7558a40004ff7358a40014fe7358a40014fc7358a40026ef7258a4010eee5258a40006ed5258a4010eee4258a40006ef3258a4010eec3258a40004ff7158a40004fc7158a4010eef2158a40024fc7058a40026ee2058a40026ec2058a400f4fd76d0a402adbd76d0a400f6bd76d0a402aebf65d0a403aebd65d0a40006bd63d0a4000ebe62d0a4000ebc62d0a40005be71d0a402adbd70d0a4000cff7650a40005df7350a40115dc7350a4000eee6250a40006ed6250a40005fb7050a40025f87050a402a5bf7650a4000ebf7650a4000cbf7650a402a6bf6550a403a6bd6550a400079f7350a400079c7350a40006bd6350a40007af7250a4000ebe6250a402a7ae6250a402a7ad6250a4000ebc6250a40005bc7150a402a5bf7050a40007bb7050a402a7b87050a402a7af2050a40004ff764ca40004fd764ca40024fc764ca40004ff759864001cfe7598640004fd759864001cfc7598640014fe7398640004fd7398640014fc739864000cfe7298640004fd729864000cfc7298640026f67198640006f65198640006f55198640026f61098640026f41098640004ff75586400067f75586400047f755864001cfe7558640004fd755864001cfc75586400067c755864001c7c7558640004ff7358640014fe7358640014fc7358640004ff725864000cfe725864000cfc7258640006bf4258640006bd4258640026f77158640006f65158640006f55158640026bf4058640026bd4058640026f61058640026f4105864011d7e75d06400057d75d064011d7e75906400057d7590640115de7390640005dd7390640006f66190640006f56190640025fa7090640005f9709064039f3e75906400073d7590640276bf659064039ebd65906400079e73906400079d7390640005bd7290640277b66190640006bd6190640277b56190640277ba7090640275bd7090640007b97090640006f66150640006f56150640005fb7050640025f87050640285bd7610640006bd7610640286bf6510640396bd6510640005bd7210640007b67110640006bd6110640285bd7010640004ff768c640024fe768c640004fd768c640004f
  | 23 => 0x146ec6388521007cc6388521146cc638852100dee718852100fe6718852100eef618852100fe76188521007e63188521007e53188521005ed7088521006df63d8121006dc63d8121004ff75d812101cfe75d8121004fd75d812101cfc75d81210dcfe74d8121004fd74d8121014fe73d8121004fd73d8121014fc73d812107efa20d8121135de7398121005dd7398121006df6398121006dc6398121006fb60981210057f755812113d7c7558121005bf7458121005bc7458121005df7358121135dc7358121006df6358121006dc6358121006df6318121006dc6318121026fa6018121006f96018121014ff7658f400dedc6358f40004ff7558f4001cfe7558f40004fd7558f4001cfc7558f40024fc7458f400dedf4358f400dedc4358f40004ff7258f4000cfe7258f4000cfc7258f40004ff7158f40004fc7158f4012edf3058f400d4ff7650f40016dc6350f4000cff7658b40005df7358b4012ddc7358b400deec6258b40004ff7558b4001cfe7558b40004fd7558b4001cfc7558b40024fc7458b40006be5458b40006bd5458b40004ff7358b40006df7358b40004df7358b40014fe7358b40014fc7358b40006dc7358b40014dc7358b400deef4258b400deec4258b40004ff7158b40004fc7158b402a6be4058b402a6bc4058b40126ef2058b400ccff7650b40005df7350b4012ddc7350b4000eec6250b40004ff764cb40004fd764cb400dcfc764cb400ed7e75987400057d759874012dde7398740005dd73987400def76198740004ff759874001cfe75987400067e759874001c7e7598740004fd75987400067d75987400047d759874001cfc7598740024fe7498740006be5498740006bd5498740014fe7398740006de7398740014de7398740004fd7398740006dd7398740004dd7398740014fc739874000cfe7298740004fd729874000cfc72987400def741987400def44198740276be4098740276bc40987400def46158740004ff755874001cfe7558740004fd755874001cfc7558740024fc7458740004ff7358740014fe7358740014fc7358740004ff725874000cfe725874000cfc72587400def741587400def44158740024bd76d07400ddbf75d07400df3e75d07403bdbd75d07400df3d75d07400053d75d0740006bd62d0740006be61d07400dfb661d07400dfb561d0740025be70d07400dfba70d07400dfb970d0740025bc70d07400ed7e75907400057d759074012dde7390740005dd73907400dfb44150740005bf7650740006bf76507403b5bf75507403b5bd7550740006bd62507400dfb771507400dfb76150740006be61507400dfb46150740025be7050740025bc7050740004ff768c7400dcfe768c740004fd768c7400ddbe748c740005bd748c740004ff764c740004fd764c7400dcfc764c740016dc634
  | 24 => 0xd74d8d21006dc74d8d21006df54d8d21006de54d8d21006dd54d8d21006dc54d8d21166df72d8d21166de72d8d21166dd72d8d21166dc72d8d21166df52d8d21166de52d8d21166dd52d8d21166dc52d8d21166df42d8d21166de42d8d21166dd42d8d21166dc42d8d21166df71d8d21136de71d8d21166dd71d8d21006df51d8d21006de51d8d21006dd51d8d21006dc51d8d21166df21d8d21166de21d8d21166dc21d8d21006df70d8d21006de70d8d21006dd70d8d21006dc70d8d21006df50d8d21006de50d8d21006dd50d8d21006dc50d8d21166df20d8d21166de20d8d21166dd20d8d21166dc20d8d21136dc6358d213ddf77158d21004ff7558d2101cfe7558d21004fd7558d2101cfc7558d21004ff7458d210dcfc7458d21164ff7358d21006df7358d21154ff7258d21006ef7258d21144ef7258d213dcff7158d21006f77158d21004ff7058d21024fc7058d21165de7618d21136de7618d21164de7618d211375e7518d211375d7518d21006df6518d21006de6518d21006dd6518d21006dc6518d21006df6418d21006de6418d21006dd6418d21006dc6418d213d6df6218d213d7d57118d213d6df6118d213d7d72118d213d7cc2118d213d7d42118d213d7cf2018d210dcff76d0d21004fe76d0d21004fd76d0d210dcfc76d0d21006df63d0d21016dc63d0d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21006df6350d21016dc6350d2100cfe76d052100cfc76d052113d7e75d05210057d75d0521006bf64d05210debc64d0521006df63d05211cedc63d052100dee72d0521005ed72d0521174fe769052113d7e75905210057d7590521135de7390521005dd7390521006df63905211bedc63905211b7e421905210dcff765052100cfe765052119cfd765052100cfc7650521006bf6450521006bc6450521006df63505211a6dc6350521005ef725052100dec725052119fe421505211b4fe7610521006df631052117edc63105213d4fe768c521166df638c521016dc638c5213d5f6768c5213cef6768c521155f5738c521167d7638c521016f6638c521016f4638c521137d4638c521016d4638c52100df6728c52100df4728c521166f7628c521167d6328c521167d4328c521167e7208c521014ff764c52100cfe764c521154fd764c52100cfc764c521006df634c521016dc634c521005ef724c52100dec724c521137d4314c52100df4764c521016f4764c52100cf4764c521165f7734c521007d7734c521007d7634c521016f6634c521016f4634c521137d4634c521137d6534c5213c7d5534c521007d7434c521137d4434c521007e7724c52100df6724c52100df4724c521157e4724c521156f7624c521157d7324c521157d5324c521137d7304c521157e7204c521007cf6388521146ee6388521
  | 25 => 0xc62100de4724c621157d7324c621147e7324c621147c7324c621157d5324c621157e4324c621147d7304c621006fb60982210057f755822114d7c7558221005bf7458221005bc7458221004ff75582210067f75582210047f755822101cfe7558221004fd755822101cfc75582210067c755822101c7c7558221004ff7458221006bf7458221004bf74582210dcfc7458221006bc7458221004bc7458221004ff7358221014fe7358221014fc7358221006ef325822104eec325822104eef215822104efa205822114d7e75182210057d7518221005be7418221005bd7418221145de7318221005dd7318221026fa6018221006f96018221004ff75d912101cfe75d9121004fd75d912101cfc75d9121006be54d9121006bd54d9121014fe73d9121004fd73d9121014fc73d91211b4ff72d91211b4fd72d91211b6bf42d91211b6bd42d9121024fe70d9121004fd70d91211b6ef20d912113d7e75991210057d7599121006bf6499121135de7399121005dd739912119df571991210dcff759912101cfe75991210de7e759912101c7e7599121004fd75991210de7d75991210047d75991210dcfc75991210dcfe7499121014fe73991210dede7399121014de7399121004fd73991210dedd7399121004dd7399121014fc73991211c4fd72991210deed729912119cfd71991210def57199121024fe7099121004fd7099121005df7359121135dc73591211c5f77159121004ff755912101cfe7559121004fd755912101cfc7559121006bf7459121004ff7359121006df7359121004df7359121014fe7359121014fc7359121006dc7359121014dc735912119cff7259121006ef72591211c4ff7159121006f77159121004ff7059121024fc705912119eef20591211b4fe7619121006bd64191210dcff751912101cfe7519121004fd75191210dcfc75191210debe74191210debe5419121006bd5419121014fe7319121004fd7319121014fc73191210dcff7219121174fd72191210debf4219121176bd4219121024fe7019121004fd7019121014fe76d8d21136de63d8d21004ff75d8d2101cfe75d8d21004fd75d8d2101cfc75d8d210dcfe74d8d21004fd74d8d21006df53d8d21136de53d8d21006dd53d8d21136dc53d8d21136de43d8d21136dc43d8d21164ff72d8d21164fd72d8d21166df32d8d21166dd32d8d2100cfd71d8d21136df31d8d21024fe70d8d21004fd70d8d21136df30d8d21136dc30d8d213d5de76d8d21014de76d8d21006df65d8d21006de65d8d21006dd65d8d21006dc65d8d21006df64d8d21006de64d8d21006dd64d8d21006dc64d8d21167d771d8d21167d721d8d21167cc21d8d21167d421d8d21167cf20d8d21006df75d8d21006de75d8d21006dd75d8d21006dc75d8d21006df74d8d21006de74d8d21006d
  | 26 => 0x1c7e7599221004fd75992210de7d75992210047d75992210dcfc7599221014fe7399221004fd7399221014fc73992210debf42992211c6bd4299221024fe7099221004fd7099221004ff755922101cfe7559221004fd755922101cfc7559221006bf7459221004ff7359221014fe7359221014fc735922119ebf425922119ebd4259221004ff7059221024fc7059221006bd64192211b5f671192210dcff751922101cfe7519221004fd75192210dcfc75192210dcfe74192210debe74192210debe5419221006bd5419221014fe7319221004fd7319221014fc73192210deed72192211b4fe71192210def67119221024fe7019221004fd7019221146de63d8e21167cc32d8e213d5f671d8e21004ff75d8e2101cfe75d8e21004fd75d8e2101cfc75d8e210dcfe74d8e21004fd74d8e21154fd73d8e21006ed72d8e21146ef32d8e21166de32d8e21166dc32d8e21166ec32d8e213d4fe71d8e21006f671d8e21146df31d8e21024fe70d8e21004fd70d8e21014ff7658e21146dc6358e2100dec7258e21147cf3258e21004ff7558e2101cfe7558e21004fd7558e2101cfc7558e21004ff7458e210dcfc7458e21006df7358e21146de5358e21006dd5358e21146dc4358e21146ef7258e21156df3258e21146ef3258e21156dd3258e21156ec3258e2100cfc7158e21146dc3158e21004ff7058e21024fc7058e21146df3058e210dcff76d0e21004fe76d0e21004fd76d0e210dcfc76d0e21016de63d0e21006dd63d0e2100dee72d0e21005ed72d0e2120fcc32d0e21004ff7650e21004fe7650e21004fd7650e21004fc7650e21005ef7250e2100dec7250e2119cfd76d062114d7e75d06210057d75d0621006bf64d06210debc64d062100cff769062100cfd769062114d7e75906210057d7590621006be6490621006bd6490621145de7390621005dd739062100dee7290621005ed72906211c4ff7650621006bf6450621006bc645062100cff761062100cfd76106210debe6410621006bd641062100dee7210621005ed721062100cff768c621014fe768c62100cfd768c621016de638c621006dd638c62100dee728c621005ed728c621167cc328c62100df5768c621016f5768c62100cf5768c621016f6638c621147d6638c621007d5638c621016f4638c62100df6728c621167e6728c621007e5728c62100df4728c621147e7328c621167d6328c621167d4328c621167e4328c621167c4328c6213dcff764c621006df634c621016dc634c621145ef724c62100dec724c621147cf324c621147d4314c6213ddf7764c6213eef7764c621007d7734c621007d7634c621016f6634c621016f4634c621147d4634c621147d6534c6213e7d5534c621007d7434c621147d4434c621147e7724c62100df6724c62100df4724c621157e4724
  | 27 => 0xe6418931006ed6418931006ec6418931157ce7318931157cd7318931166ef63189313efce5318931007cd5318931007cf43189313efcc4318931157e571189313deef61189313efe731189313efcc31189313efe43118931157ea7018931157e970189313efcf3018931004fe76d0931004fd76d09310dcfc76d09310debe64d0931006bd64d0931015dc73d09310079f43d0931006ef62d093100eec62d0931004ff7650931004fe7650931004fc7650931006be6450931006bd6450931005df7350931015dc73509310079f4350931006ef625093100eec6250931155dc764c93100edc764c93100cdc764c9313fddf754c9313fddd754c931005de744c931005dc744c931015df724c931017cf724c931007cf624c93100ede624c93100edc624c931157cc624c93100ecc624c931007d7714c931005dc714c931007d4714c931016df614c931017d7614c931005df704c931014fe76d0531014fc76d053115d7e75d05310057d75d0531006bf64d05310debc64d0531015de73d0531005dd73d0531006ef62d05311c6ec62d053117cfe769053115d7e75905310057d7590531015de7390531005dd7390531006ef62905311b6ec62905311bfd431905310dcff7650531014fe76505311a4fd7650531014fc7650531006bf6450531006bc6450531005df7350531015dc7350531006ef625053119eec62505311a7d431505311bcfe7610531015dc7310531006ef6210531176ec6210531007b541105313f5df758c5313f5dd758c531005de748c531005dc748c531005dd728c531007cf628c531166de628c531166dc628c531007cc628c531166cc628c531015de718c531017d6718c531016df618c531017d7618c531005dd708c531006ef62d8131006ec62d8131004ff75d813101cfe75d8131004fd75d813101cfc75d81310dcfe74d8131004fd74d8131086de53d8131006dd53d813100cfe72d8131004fd72d813100cfc72d8131086fa30d8131155ee7298131005ed7298131006ef6298131006ec6298131006fb60981310057f755813115d7c7558131005bf7458131005bc7458131005ef7258131155ec7258131006ef6258131006ec6258131006ef6218131006ec6218131026fa6018131006f9601813114d7e75d92210057d75d9221145de73d9221005dd73d9221175f671d9221004ff75d922101cfe75d92210067e75d922101c7e75d9221004fd75d92210067d75d92210047d75d922101cfc75d9221006be54d9221006bd54d9221014fe73d9221006de73d9221014de73d9221004fd73d9221006dd73d9221004dd73d9221014fc73d9221006ed72d9221174fe71d9221006f671d9221024fe70d9221004fd70d922119cfd769922114d7e75992210057d7599221006bf64992210dcff759922101cfe75992210de7e7599221
  | 28 => 0x91310deed7299131004ed729913100cfc72991311a4fd71991310def57199131024fe7099131004fd7099131005ef7259131155ec72591311cdf77159131004ff755913101cfe7559131004fd755913101cfc7559131006bf74591311a4ff7359131006df73591311a6dc4359131004ff7259131006ef7259131004ef725913100cfe725913100cfc7259131006ec725913100cec72591311ccff7159131006f77159131004ff7059131024fc70591311a6df30591311bcfe7619131006bd64191310dcff751913101cfe7519131004fd75191310dcfc75191310debe74191310debe5419131006bd54191310dcff731913117cfd73191310debf431913117ebd431913100cfe7219131004fd721913100cfc7219131024fe7019131004fd7019131006de76d0d31004de76d0d31405df75d0d31405dd75d0d31015de74d0d310179e74d0d31006df64d0d310079f64d0d31006dd64d0d310079c64d0d31005dd72d0d3120ede62d0d3120edc62d0d3120ecc62d0d31005de71d0d31007d671d0d31005d671d0d31007d571d0d31016df61d0d31017d761d0d31005dd70d0d3100cfe76d8931156ee62d8931004ff75d893101cfe75d8931004fd75d893101cfc75d89310dcfe74d8931004fd74d8931006ef52d8931156ee52d8931006ed52d8931156ec52d8931156ee42d8931156ec42d8931156ee32d8931146ed32d8931014fd71d8931156ef21d8931024fe70d8931004fd70d8931156ef20d8931156ec20d8931155ee76d893100cee76d8931006ef65d8931006ee65d8931006ed65d8931006ec65d8931006ef64d8931006ee64d8931006ed64d8931006ec64d8931007cf73d8931147cc73d8931147ce53d8931007cd53d8931007cf43d8931147cc43d8931147e771d8931147e731d8931147cc31d8931147e431d8931147cf30d8931006ef75d8931006ee75d8931006ed75d8931006ec75d8931006ef74d8931006ee74d8931006ed74d8931006ec74d8931006ef54d8931006ee54d8931006ed54d8931006ec54d8931146ef73d8931156ee73d8931146ec73d8931146ef53d8931146ee53d8931146ed53d8931146ec53d8931146ef43d8931146ee43d8931146ed43d8931146ec43d8931146ef71d8931156ee71d8931146ed71d8931006ef51d8931006ee51d8931006ed51d8931006ec51d8931146ef31d8931146ee31d8931146ec31d8931006ef70d8931006ee70d8931006ed70d8931006ec70d8931006ef50d8931006ee50d8931006ed50d8931006ec50d8931146ef30d8931146ee30d8931146ed30d8931146ec30d8931156ec62589313cdf77158931145ee7618931156ee76189311576e75189311576d7518931006ef6518931006ee6518931006ed6518931006ec6518931157ae7418931157ad7418931006ef6418931006e
  | 29 => 0xde7d75992310047d75992310dcfc7599231006bf54992310debc54992310debf43992311cebd439923100cfe7299231004fd729923100cfc7299231006de32992311cedc32992311cedf3199231024fe7099231004fd7099231004ff755923101cfe7559231004fd755923101cfc7559231006bf7459231006bf5459231006bc54592311a6bf43592311a6bd4359231004ff725923100cfe725923100cfc7259231004ff7059231024fc7059231006bd64192311bdf671192310dcff751923101cfe7519231004fd75192310dcfc75192310dcfe74192310debe74192310dedd731923100cfe7219231004fd721923100cfc7219231006de321923117edc32192311bcfe71192310def6711923117edf3119231024fe7019231004fd7019231166ee62d8a31167cc32d8a313edf671d8a3100cff7658a31015dc7358a31166ec6258a31167ce3258a31004ff7558a3101cfe7558a31004fd7558a3101cfc7558a31004ff7458a310dcfc7458a31166de3258a31166ee3258a31136ed3258a31166dc3258a31014fc7158a31136df3158a31166ec2158a31004ff7058a31024fc7058a31166ef2058a310dcff76d0a31004fe76d0a31004fd76d0a310debe64d0a31006bd64d0a31015de73d0a31005dd73d0a31004ff7650a31004fd7650a31004fc7650a31006be6450a31006bd6450a31005df7350a31015dc7350a311a4fd76d063116d7e75d06310057d75d0631014ff7690631014fd769063116d7e75906310057d7590631006be6490631006bd6490631015de7390631005dd73906311ccff7650631014ff7610631014fd76106310debe6410631006bd6410631015de7310631005dd7310631007b54110631006fb60982310057f755823116d7c7558231004ff75582310067f75582310047f755823101cfe7558231004fd755823101cfc75582310067c755823101c7c7558231004ff74582310dcfc7458231004ff725823100cfe725823100cfc7258231006de3258231056dc3258231056df3158231056fa305823116d7e75182310057d7518231005be7418231005bd7418231165ee7218231005ed7218231026fa6018231006f96018231004ff75d913101cfe75d9131004fd75d913101cfc75d9131006be54d9131006bd54d91311bcff73d91311bcfd73d9131006dd73d91311bebf43d91311bebd43d91311bedc43d913100cfe72d9131004fd72d913100cfc72d9131024fe70d9131004fd70d91311bedf30d913115d7e75991310057d7599131006bf6499131155ee7299131005ed72991311a5f571991310dcff759913101cfe75991310de7e759913101c7e7599131004fd75991310de7d75991310047d75991310dcfc75991310dcfe74991311ccfd73991310dedd739913100cfe72991310deee729913100cee7299131004fd729
  | 30 => 0xe75181410057d7518141276bf64181411a5de7318141005dd731814119dee7218141005ed7218141026fa6018141006f96018141014ff7658c410dedc6358c41004ff7558c4101cfe7558c41004fd7558c4101cfc7558c4117ede5358c41006dd5358c410dedf4358c410dedc4358c41004ff7258c4100cfe7258c4100cfc7258c4117edf3258c4117edc3158c41004ff7058c41024fc7058c4117edf3058c411ccff7650c4100cff7658841005df735884117ddc73588410deec6258841004ff755884101cfe7558841004fd755884101cfc7558841006be5458841006bd5458841004ff7358841006df7358841004df7358841014fe7358841014fc7358841006dc7358841014dc7358841176ee5258841006ed52588410deef42588410deec4258841176ee3258841176ec2158841004ff7058841024fc7058841176ef20588411c4ff76508411c6be6450841005df735084117ddc7350841004ff764c841004fd764c8410dcfc764c841016de634c841006dd634c84100eee624c841006ed624c8410ddbf75d04410df3e75d044143dbd75d04410df3d75d04410053d75d0441006bd62d0441285be70d04411857e75904410057d7590441425bd7490441436be649044117dde7390441005dd739044142f7675904410077575904410ddf574904410def664904410dfb664904410dfb6549044142fb55490441007d67390441007d57390441004ff7650441005bf7650441006bf7650441004bf7650441425bf7550441425bd7550441006bd62504410ddbf715044141ebe6150441417b65150441417b5515044140fb7215044140fb42150441285bc70504410ddf77650441006f77650441004f776504410ddf77450441007b774504410def664504410dfb664504410dfb65450441417b554504410dfb74350441007b5435044140fb642504410dfb442504410defb6098041026f860980410057f75580411857c75580410def86058041004ff75580410067f75580410047f755804101cfe7558041004fd755804101cfc75580410067c755804101c7c7558041006be5458041006bd5458041004ff7358041014fe7358041014fc7358041004ff725804100cfe725804100cfc7258041006bf4158041006f64158041006bd4158041006f54158041006fa5058041006f950580410defb40580410def8405804116d7e75d92310057d75d923117df671d9231004ff75d923101cfe75d92310067e75d923101c7e75d9231004fd75d92310067d75d92310047d75d923101cfc75d9231006dd73d923100cfe72d9231004fd72d923100cfc72d923117cfe71d9231006f671d9231024fe70d9231004fd70d92311a4fd769923116d7e75992310057d7599231006bf64992310dcff759923101cfe75992310de7e759923101c7e7599231004fd7599231
  | 31 => 0x6410dfb654d064145fb554d0641007d663d0641007d563d0641005f570d064118d7e75d82410057d75d82410067e65d82410067d65d82411bdde73d8241005dd73d8241006de63d8241006dd63d82410067e65982410067d6598241006de6398241006dd6398241006fb60982410067e65582410067d6558241006de6358241006dd6358241004ff755824101cfe7558241004fd755824101cfc7558241006be5458241006bd5458241004ff7358241014fe7358241014fc7358241004ff725824100cfe725824100cfc7258241006bf415824118d7e75182410057d75182410067e65182410067d65182411bdde7318241005dd7318241006de6318241006dd63182411b5ee7218241005ed7218241026fa6018241006f96018241014fe76d8d411a6de63d8d41004ff75d8d4101cfe75d8d41004fd75d8d4101cfc75d8d411a6de43d8d4100cfe72d8d41004fd72d8d4100cfc72d8d41006de32d8d411a6dc32d8d411a6df31d8d41024fe70d8d41004fd70d8d411a6dc6358d41005ef7258d4119dec7258d411bcfe76d0d41016de63d0d41014fc7650d41006df6350d41016dc6350d411a79c4350d41005f77150d41005f47150d4100cfe76d894119eee62d8941004ff75d894101cfe75d8941004fd75d894101cfc75d8941014fe73d8941004fd73d8941014fc73d894119eee42d8941006ef32d894119eec32d894119eef21d8941024fe70d8941004fd70d8941005df73589411a5dc735894119eec62589411b4fe76d0941005be76d09411b6be76d0941456bf65d0941456bd65d0941006bf63d094119dbd72d094100ebe62d094100ebc62d0941005be71d09410debf61d0941005bd70d09412aebc60d094100cfc7650941005df73509411a5dc7350941006ef625094100eec6250941005f77150941005f4715094119dbc765094100ebc765094100cbc765094144ebf655094144ebd65509410079f73509410079c7350941006bf635094119dbf7250941007af7250941007af625094100ebe625094100ebc625094119fac6250941007b77150941005bc7150941007b47150941005b47150941005bf70509412a6bc605094119faf2050941004ff764c941004fe764c941004fc764c9411ad7e75d05410057d75d05410df7675d05410df7575d05410dfb742d0541007b542d0541005f570d05411ad7e75905410057d75905411a5de7390541005dd73905414473e75905410073d7590541446bf6590541446bd65905410079e73905410079d7390541005bd7290541007b76190541005bd7090541004ff75d814101cfe75d8141004fd75d814101cfc75d8141014fe73d8141004fd73d8141014fc73d814100cfe72d8141004fd72d814100cfc72d8141006fb50d8141006f850d8141006fb60981410057f75581411ad7c75581411ad7
  | 32 => 0x6de6298e41006dc6298e41014ff7658e410067e6558e410067d6558e411bedc6358e41004ff7558e4101cfe7558e41004fd7558e4101cfc7558e41006df5358e411bede5358e41006dd5358e411bedc5358e411bede4358e41004ff7258e4100cfe7258e4100cfc7258e411bedf3258e41006de3258e411bedc3258e411bedc3158e41004ff7058e41024fc7058e411bedf3058e411bedc3058e411bddf7658e411bedf7658e41014df7658e41006df6558e41006de6558e410075e6558e410065e6558e41006dd6558e410075d6558e410065d6558e41006dc6558e410079e5458e410079d5458e41006de6258e41006dc6258e41006df7558e41006de7558e41006dd7558e41006dc7558e41006dd7458e411bedc7458e41006df5458e41006de5458e41006dd5458e41006dc5458e41006df7258e41006de7258e41006dd7258e41006dc7258e41006df5258e41006de5258e41006dd5258e41006dc5258e41006de4258e41006dc4258e411bedf7158e41006de7158e41006dc7158e41006df5158e41006de5158e41006dd5158e41006dc5158e41006de4158e41006df2158e41006dc2158e41006df7058e41006de7058e41006dd7058e41006dc7058e41006df5058e41006de5058e41006dd5058e41006dc5058e41006df2058e41006dc2058e411a4fd76d0e412167e65d0e410067d65d0e41016de63d0e41014ff7650e412067e6550e410067d6550e41016de6350e41006dd6350e41005f77150e41005f47150e4118d7e75d8a410057d75d8a410067e65d8a410067d65d8a411bdde73d8a41005dd73d8a41006de63d8a41006dd63d8a411b6ee62d8a4100cff7658a410067e6558a410067d6558a41006de6358a41006dd6358a411b6ec6258a41004ff7558a4101cfe7558a41004fd7558a4101cfc7558a41006be5458a41006bd5458a41004ff7358a41014fe7358a41014fc7358a411b6ee4258a411b6ec2158a41004ff7058a41024fc7058a411b6ef2058a4119cfd76d0a411f67e65d0a410067d65d0a411eede63d0a41006dd63d0a4100cff7650a411e67e6550a410067d6550a41005df7350a411bddc7350a411dede6350a41006dd6350a4100eee6250a41006ed6250a41005f77150a41005f47150a41004ff764ca41004fd764ca41004fc764ca411d67e654ca410067d654ca41016de634ca41006dd634ca4118d7e75d06410057d75d06411967e65d06410067d65d06411cede63d0641006dd63d0641005bd76d0641006bd76d0641435bf75d064145f3e75d0641435bd75d06410073d75d06410053d75d064145f3e65d06410073d65d06410079e63d06410079d63d0641006bd62d064145fb651d064145fb551d0641275be70d0641005f576d06410def576d06410df7675d06410df7575d064145f7665d06410077565d
  | 33 => 0xc40597410067f30597410067c30597410067f20597410067c2059741014ff7658f410067e6558f410067d6558f410dedc6358f41004ff7558f4101cfe7558f41004fd7558f4101cfc7558f410dedf4358f410dedc4358f41004ff7258f4100cfe7258f4100cfc7258f41006de3258f411cedc3258f411cedf3158f41004ff7058f41024fc7058f411cedf3058f4117cff7650f412067e6550f410067d6550f410df9c4350f4100cff7658b410067e6558b410067d6558b410deec6258b41004ff7558b4101cfe7558b41004fd7558b4101cfc7558b41004ff7358b41014fe7358b41014fc7358b410deef4258b410deec4258b41006ef3258b411c6ec3258b411c6ef2158b41004ff7058b41024fc7058b411c6ef2058b410ddbd76d0b4100ebd76d0b4100cbd76d0b410debf65d0b410df3e65d0b4146ebd65d0b410df3d65d0b410063d65d0b41006bd63d0b4100ebe62d0b410dfae62d0b410dfad62d0b4100ebc62d0b41005be71d0b410dfb671d0b410dfb571d0b41005bd70d0b412aebe60d0b41174ff7650b411e67e6550b410067d6550b41005df7350b411cddc7350b41005bf7650b41176bf7650b41466bf6550b414673e6550b41466bd6550b410073d6550b410063d6550b410079f7350b410079c7350b41006bd6350b410dfaf7250b4100ebe6250b4100ebc6250b41005bc7150b41005bf7050b412a6be6050b411c7af2050b41004ff764cb41004fd764cb410dcfc764cb411d67e654cb410067d654cb410067e65983410067d65983410defb6098341026f860983410067e65583410067d65583410def86058341004ff755834101cfe7558341004fd755834101cfc7558341004ff7358341014fe7358341014fc7358341004ff725834100cfe725834100cfc72583410defb40583410def8405834118d7f765964118e7f765964101c7f765964118f3e74596410073d74596410067e63596410067c63596410067e62596410067c625964118e7f745964118e7e74596410067d745964118e7c74596410067f73596410067e73596410067d73596410067c73596410067e43596410067c43596410067f72596410067e72596410067d72596410067c72596410067e42596410067c42596410067f32596410067e32596410067c325964118e7f71596410067e715964118e7d715964118e7c715964118e7e41596410067f31596410067c31596410067f21596410067c21596410067f70596410067e70596410067d70596410067c70596410067f30596410067c30596410067f20596410067c205964118d7e75d8e410057d75d8e410067e65d8e410067d65d8e411bede63d8e41006df6598e41006de6598e410075e6598e410065e6598e41006dd6598e410075d6598e410065d6598e41006dc6598e410079e5498e410079d5498e41
  | 34 => 0x91320dcfc75991320dcfe74991321fcfd73991320dedd739913220cfd72991320deed729913220ede329913220edc3299132004fe7199132004fd71991321eedf3199132024fe7099132004fd709913220ddf73591321edef7259132004ff755913201cfe7559132004fd755913201cfc7559132006bf745913220cff7359132006df735913220cdf73591321fcff7259132006ef7259132004ff7159132004fc7159132004ff7059132024fc7059132484fe76191321d57e75191320057d7519132006bd64191320dcff751913201cfe75191320de7e751913201c7e7519132004fd75191320de7d75191320047d75191320dcfc75191320dcfe74191320debe741913200cff731913200cfd73191320debf4319132476bd4319132014ff7219132014fd72191320debf421913247ebd421913247ede321913247edc3219132004fe7119132004fd7119132476df3119132024fe7019132004fd7019132004ff75d853201cfe75d8532004fd75d853201cfc75d85320dcfe74d8532004fd74d853200cfd73d8532014fd72d85323cef631d85323def621d8532024fe70d8532004fd70d8532006f761985321d57e75185320057d7518532006f56118532004ff751853201cfe75185320067e751853201c7e7518532004fd75185320067d75185320047d751853201cfc75185320dcfe7418532004fd741853200cfd73185323d6dd7318532014fd72185323eeef32185323d6de32185323d6dc32185323d6ec32185323eedf31185323eef531185323d6f52118532024fe7018532004fd7018532024fe76d81321d57e75d81320057d75d8132004ff75d813201cfe75d81320067e75d813201c7e75d8132004fd75d81320067d75d81320047d75d813201cfc75d81320dcfe74d8132004fd74d813200cfd73d8132014fd72d813231eef32d81322f6de32d81322f6dc32d81322f6ec32d8132004fe71d8132004fd71d813231edf31d813231efa30d81322f6fa20d8132006fb6098132026fa6018132006f960181320dd7f76597411967f765974101c7f76597410de7f63597410067e63597410de7c63597410de7f62597410067e62597410de7c62597410de7f60597410de7c60597411967f74597410de7e74597411967d74597410de7c74597410067f73597410067e73597410067d73597410067c73597410de7f43597410067e43597410de7c43597410067f72597410067e72597410067d72597410067c72597410de7f42597410067e42597410de7c42597410067f32597410067e32597410067c32597411967f71597411967e71597410067d71597411967c71597410de7f41597410de7c41597410067f31597410067c31597410067f21597410067c21597410067f70597410067e70597410067d70597410067c70597410de7f40597410de7
  | 35 => 0x1df5d7518d42006df6518d42006de6518d42006dd6518d42006dc6518d4247f9d7418d4247edf6418d420079e5418d420079d5418d4247edf6218d4247f9e4218d4247f9c4218d4247fcc4218d4247fcf2018d4247cfe76d0d4220edf63d0d42016dc63d0d4247dbe76d0d4248ebe76d0d424a5bf75d0d424a5bd75d0d421fdbd73d0d4220f9f63d0d42016be63d0d42016bc63d0d421df9c63d0d420169c63d0d4200dbe72d0d4200dbc72d0d420debf62d0d4220f9e32d0d4220f9c32d0d42005bd71d0d421df9f31d0d422a5be70d0d4220faf20d0d4200cfc7650d42006df6350d42016dc6350d42005ef7250d4200dec7250d4200dbc7650d42016bc7650d4200cbc7650d4249dbf7550d4249dbd7550d4220dbf7350d420079f7350d420079f6350d42016be6350d42016bc6350d421df9c6350d42007af7250d4200dbe7250d4200dbc7250d421ffac7250d421febf6250d42005bf7150d422a5bc7050d421df9f3050d421ffaf2050d4200dee74d094200fae74d094200eef64d094200faf64d09420dfae54d0942497ad54d0942007cf63d0942007cc63d09420dfaf43d0942007ad43d0942005ed70d0942006df63d8542006dc63d8542004ff75d854201cfe75d8542004fd75d854201cfc75d8542014fe73d8542004fd73d8542014fc73d8542006f651d8542006f551d85421c6f621d8542024fe70d8542004fd70d85421c6ef20d85421e57e75985420057d75985421ddde7398542005dd7398542006df6398542006dc6398542006f76198542005df73585421dddc7358542006df6358542006dc6358542006df6318542006dc6318542006f56118542004ff751854201cfe7518542004fd751854201cfc7518542176bd7418542006be5418542006bd5418542014fe7318542004fd7318542014fc7318542006f65118542006f55118542176f52118542024fe7018542004fd7018542006df63d8142006dc63d8142004ff75d814201cfe75d8142004fd75d814201cfc75d8142126bd74d8142006be54d8142006bd54d8142014fe73d8142004fd73d8142014fc73d8142004fe71d8142004fd71d8142126fa20d81421ddde7398142005dd7398142006df6398142006dc6398142006fb60981420057f75581421e57c7558142005df73581421dddc7358142006df6358142006dc6358142005f77158142005f47158142006df6318142006dc6318142026fa6018142006f96018142004ff75d913201cfe75d9132004fd75d913201cfc75d913200cff73d913200cfd73d913248ebf43d913248ebd43d9132014ff72d9132014fd72d9132486bf42d9132486bd42d9132004fe71d9132004fd71d9132024fe70d9132004fd70d91321fcfd7699132006bf64991321fddd73991321dded72991320dcff759913201cfe7599132004fd759
  | 36 => 0xe32d0f4220f9c32d0f42005bd71d0f421ef9f31d0f422adbe70d0f42484ff7650f42485bf7650f42476bf7650f424adbf7550f424adbd7550f420df9f7350f42016be6350f42016bc6350f4200dbe7250f4200dbc7250f42005bf7150f422adbc7050f421ef9f3050f421f57e75987420057d75987421edde7398742005dd73987420def76198742004ff759874201cfe75987420067e759874201c7e7598742004fd75987420067d75987420047d759874201cfc759874200cfe74987421b6be7498742006be5498742006bd5498742014fe7398742006de7398742014de7398742004fd7398742006dd7398742004dd7398742014fc73987420def741987420def441987421b6f52198742024fe7098742004fd70987420def46158742004ff755874201cfe7558742004fd755874201cfc755874200cfc7458742004ff7358742014fe7358742014fc73587420def741587420def4415874219ef62158742004ff7058742024fc70587420defb6098342026f860983420057f75583421f57c75583420def86058342004ff75583420067f75583420047f755834201cfe7558342004fd755834201cfc75583420067c755834201c7c755834200cfc74583420f6bc7458342006be5458342006bd5458342004ff7358342014fe7358342014fc73583420f6ee4258342004ff7158342004fc71583420defb40583420def840583420f6fa2058342014fe76d8d421dede63d8d42004ff75d8d4201cfe75d8d42004fd75d8d4201cfc75d8d4200cfd74d8d42006df53d8d421dede53d8d42006dd53d8d421dedc53d8d421dede43d8d4220edf32d8d42004fe71d8d42004fd71d8d421dedf31d8d421dedc31d8d42024fe70d8d42004fd70d8d421dedf30d8d421dedc30d8d4247dde76d8d42014de76d8d42006df65d8d42006de65d8d42006dd65d8d42006dc65d8d4220f9f74d8d420079e54d8d420079d54d8d4220f9e42d8d4220f9c42d8d4220fcc42d8d4220fcf20d8d42006df75d8d42006de75d8d42006dd75d8d42006dc75d8d4220edf74d8d421dede74d8d4220edd74d8d42006df54d8d42006de54d8d42006dd54d8d42006dc54d8d4220edf72d8d4220ede72d8d4220edd72d8d4220edc72d8d4220edf52d8d4220ede52d8d4220edd52d8d4220edc52d8d4220edf42d8d4220ede42d8d4220edc42d8d42006df71d8d42006de71d8d42006dd71d8d42006dc71d8d42006df51d8d42006de51d8d42006dd51d8d42006dc51d8d4220edf21d8d4220ede21d8d4220edd21d8d4220edc21d8d42006df70d8d42006de70d8d42006dd70d8d42006dc70d8d42006df50d8d42006de50d8d42006dd50d8d42006dc50d8d4220edf20d8d4220ede20d8d4220edd20d8d4220edc20d8d421dedc6358d4220dde7618d421dede7618d421df5e7518d42
  | 37 => 0x8b43004ff7158b43004fc7158b431dedf3158b4320eec2158b43004ff7058b43024fc7058b4320eef2058b432157e75987430057d75987430def76198743004ff759874301cfe75987430067e759874301c7e7598743004fd75987430067d75987430047d759874301cfc7598743014fe749874300cfe7298743004fd729874300cfc7298743006de32987431bedc32987430def741987430def441987431bedf31987431bef53198743024fe7098743004fd70987430def46158743004ff755874301cfe7558743004fd755874301cfc7558743014fc7458743004ff725874300cfe725874300cfc72587430def741587430def441587431a6f63158743004ff7058743024fc70587430defb6098343026f860983430057f75583432157c75583430def86058343004ff75583430067f75583430047f755834301cfe7558343004fd755834301cfc75583430067c755834301c7c7558343014fc74583430fede4358343004ff725834300cfe725834300cfc7258343006de32583430fedc3258343004ff7158343004fc71583430fedf31583430defb40583430def840583430fefa3058343015de74d0d430179e74d0d43016df64d0d430179f64d0d4320ede62d0d4320edc62d0d43005dd70d0d4300cfe76d89431feee62d8943004ff75d894301cfe75d8943004fd75d894301cfc75d8943014fd74d89431feee42d89431feee32d8943004fe71d8943004fd71d89431feec21d8943024fe70d8943004fd70d89431feef20d89431feec6258943004ff75d854301cfe75d8543004fd75d854301cfc75d8543006df43d85431cedc43d854300cfe72d8543004fd72d854300cfc72d85431cef631d8543024fe70d8543004fd70d85431cedf30d85432057e75985430057d7598543006f76198543005ef72585431fdec7258543006f56118543004ff751854301cfe7518543004fd751854301cfc751854300cfe7218543004fd721854300cfc721854317ef53118543024fe7018543004fd7018543004ff75d814301cfe75d8143004fd75d814301cfc75d814300cfe72d8143004fd72d814300cfc72d8143004fe71d8143004fd71d814312efa30d81431fdee7298143005ed7298143006fb60981430057f75581432057c7558143026fa6018143006f96018143014ff7658f420dedc6358f42004ff7558f4201cfe7558f42004fd7558f4201cfc7558f4200cfc7458f421eede5358f42006dd5358f420dedf4358f420dedc4358f421fedf3258f42004ff7158f42004fc7158f421eedc3158f42004ff7058f42024fc7058f421eedf3058f4200dbd76d0f42016bd76d0f4200cbd76d0f420ddbf75d0f424b5bd75d0f42016be63d0f420df9e63d0f420df9d63d0f42016bc63d0f4200dbe72d0f420dfae72d0f420dfad72d0f4200dbc72d0f4220f9
  | 38 => 0x10050040002006000000c00200d00a8028002017006000c0000050000018018006018800801800a00100f4008008000800000e015006001000600e006006002c002001800400002200780580120250018008000017000800c0000000000000006000000000c000001000000400c01c005800000a01d000800000400300000540000030008004002000004000803a01800000ec03e00c0000010006000001001002e001000004000c09500980000000020030030006002028000c010001000801000c001004001c000006003803c00e0070030014002017000001401200d001800000a003001801800a008001000400c003000802000601a000001c00803300100000100000000010002033017001c000000000004c014002002000c04400100200180080010068000014000001800c01000c001803000c000000800003400700000b401e012008000001000000000080180300038054010000002801801002300d0120004001001802002001c0000008016002001001400e005001000000c0010000040028009000000400007b008803000600202280000220070030074002009000000001e00202a0024002000035004800800801d801000001a00d806000000c022002802800a00880300020010168014002000018009000200001780f4006063011800c01c019001800000000400200000200120000000022000000800003a00200b80040140010058000010001007001400801800080240000020000004000021001003402601100a80000240030008070002004001801806400900d80140160010040004002000001002002000c002800002400500400000000150000088006001000001800e00400380000040010028014002001000000000a00d00400040280060050000000002002802c008002008001c068003015800000002600000400b4001008007002e005001004400c0100378024002009000003c002016000000801a00500a800400a00002280dc000008005800000600100100100120000000000004036013005c01c00d00280200480090018164050014001001800000e005806801a0030028008058009000800400400200000000000090000008000008000006c0020010040030000000003000003e004016002806201900480900000010080018012000001802000a000000001019001a001000001c000009800002c00e00780b407201a006000000002400500200000000030000008000002800000800302280c806800700180400060100070000008035003000000600b000000003801800cff7658b43015dc7358b430deec6258b4320fce3258b43004ff7558b4301cfe7558b43004fd7558b4301cfc7558b43014fc7458b4320eee5258b43006ed5258b430deef4258b430deec4258b4320ede3258b4320eee3258b4320edc325
  | 39 => 0x4800200b00080000020010088010000001003000401600000000800180000028020000000000801c00400000300840040020040020000001007002400a000000000c01c00704c800c00e00d0008060004000000001008c0030000024032000002000009001900b805000a000003000400a007001000000e002001800402200400280400ba00f00a001800600000d000000200100100180000060248020000000002801c00e00e0090088004001000000c002001002804c04001c0020004006000001003c000005002007400000d001802c028008005800c00400a00000640040000010000000005001802000c00d000801400000800000a8028003000000003000f00000000000000000020000007004009c010008000001001400b0000000000001001000000e00400300080080180030020030000006001c02000c0020004020000003808004a000000005000201a001000000a004001000000200a0000098076014000000003201b008800402c000003001c04600000a00b4002045002000400000100000000020270040008000006016805400c003001800000e00c018800004e004002001c00000200000180040060018008014008006004c000015006004400000c001000000c0000018000010000001000001200300980ac0020010090014006000000000803c003000001c038000000002400600501b00000020010000018002003008005c00c0010050030002000001000400400000200280000030060048006005005806400000c000810000c003000000000c00200000000200070098014004002002800004c01600000f80080060038004008015014009400a00000c000401200400000000d605500f005001c00201400040040060008014002003001000004a0ec001000800800400d0004004019007800403402200580bc00c00a0000000016006015005800600b000807400200000180040020010018000050010000800802a002008800000000500b000001000300780a0008008000000400000500c805400200a000001801800c007800401200601000000000070000030056001000006c00000300000000020040008034000004002000000400101080500140060018018020000001001c000000002000000a000001805c00600401080140120000000008000000000003400200a000002c00c00000001900e003f00a001000000000080040160040008008004000002000002201c000000007600e000801000200c000003c000003001000400a00600a0014044000002000c00400600000180000290060008000006015000801401a000801802800800b803801e001000008804e006003804c00e0240000030002037001801c010005008001800200e000000c004008001000802201701500b40000470038000010004000000800a01
  | 40 => 0x2000c00c00000000340040000008004000000002009c0000000048124010007000800002201800000440160140000154028001015000000202a007800000e01e0010008008003003800000800200181540120030000000000007005000400200200f00b400600a002001c00200d017000400202000680100000020008000000001001804000200000100100040000000010002021000000000002e00e8000012001005001800e001000800002c001000004c0000000120030004005001005000002e00600000120180020070000000002004001600000c800000000500d8048088000000003c0040030000008000012012800004c00b0010058012005009000803c00000100080100000008008004000002005400400f000800c03c00200300380140050080000014001030801800000400100ac00000200e004803a00f00c001400002e000002802600b00180440160000020038008005012000001001800d0014000000000800c01c00f003800800000f00b0030000008001802401a00500080380340060020114032011001805401000200480e400000400100080060120010004002000003804c000019001000800203b00a000000000300c80080000000010024062011001802000a00f018000002e002000000400200000d800000000400080180180030008000008003000000402600100b8008034012001002404800100900f409e00400080a800000000c80000000030030010004000000002800e0230200004006002000005c01a0000028000006028008800c00a007000000001000b002011c06800d0020044044034004001001e00200000ac00e006000805c01a0000008008004003000000802c00000c0008000003000000000000101e800402c000000000001e00e005001c004003008005c09c02a0008000008000005000c006000010002c02a002001802402400b002001c00a000000000000200b00500b801c00000280040f20020000250000000001002c01a0000040000002000000000c018001001800400000d00c8054000036001001c00600400280280000030000018018007000800000a000010000000c000001000807a003000000400200a003800800600100380040380070070000048007000002000800f0040150002006003000801600a000000c0100000000004004000000001804e000009003c050001009002400000100080300d800d004800000200000880000000010000000006000018000005e0000008000000017001003000c0070028004000001000800001400000000081a60060080004002019002000c00001d018002c00200000000000000010020004008016000004400801800080480000000000000010000006000c00600000a800000400000a803c00200d00a001800c01c000000c00000100580
  | 41 => 0xdc1b0980700014f300014af5da14f505acc3300007c205f192158884a33614000225c7c12be8c7015fc00029a40003908000378562e2f240001d4493b1450cb5052cf576068fb600001bc6394368359c00040a457651d00de0b659425dd448d000076e273987f63e4eb049c05512b9970031258583fc139d03b800010c4ba202bc2243b44c65646528c45bc000243000000013ca2488000000107920bc4901aa17a00af949e000000000000001ded5303bd027526d0c8344b0fb54e2d35014749493d340fa0861423111174f575157c0a20afe1bd54f149940003f84cef1714dad01950fb20504bd61a0eeb530c2ed38180000000e7900002a452000003c28bf92cc800047784dd2c813b8361c42042596c632b02fa11e88dd0d48da238455a700000001e013be3d2994c348cda410e91403a704095db545035815963ddd0e914b40ca433ce5d3c58e635be97b15d407fc0c0c0b713946fe2add2001acc78f2468bb20001368094580939ac67e4a68e2e1a0129c1d100005568ad53afc3984e2465d46ace19000122b1b7423b0e7567b5e643f420c04b300015af5a143655a547ea2f0c3923fb59032db015057180004ffd00e3c111752e791330d0548d232d18c579d2231a30432000000061ccb3e639124b131ce8315f400000000000d0124e006400e01000900040080000088000008018011003400000600b800000800100080280080020050068000000009801402200b002002c00604300780000020020010030004003000800800c001001800c0020090040000046003002800800000a001001400e03d0050000000008000000002c00700281b0008001004001c01000700000000120610048008022001005001801a053000806c016006001000000c00600b0000006000000000000a006001004c000002002800c000004000802800c028001001001400000b800c01e0000018004006018002000c0140000020040016015002000c0000010000008008000000004c01c0060048060038009001800008a0100000028040000007000000a0050028008000000021800400c00f000006800600500000dc00000200e803811a00d04f0000006000000800c00202c002803c018000000000402401d00180440680020020010008000002807802000900000740100120010008010000000000803604000b005808e007012004c00a01300280000060010038000006002002000000400f010806400e00400080240100000040004004006003000400801200000480000d30028000010002009000002e019008801803600b002802800000e0010000014004001801003400a000002c024002008802400002b00e804400600a005800000001c0010004008009000003c0c60030028004002007003800c00000c001807c000003000000800600300000f80020
  | 42 => 0x7f993413a049619c12445fcd4f82c3982b0dbcf202d9d3e018680760980bdb62e8dbc22698c4011d540619179304081c8096536a37e05dd21dc12300012250184a21000000004383ab50bc62e445c0f832658501b90c9a376d53c648c7b900005f3399c1633c0589e0784ee630bd0c7009965b090c5845b0c06436dc00059b87ca16b091418c133843f00000000d4e6350df10d0c4d200016322799302000000000197370b196de461c54223d058c00019142a3c86d00003235b9c0000000000240475017d8833000133904f81e460c4baa0000b65000000014f8000169837c52600002f4000047b08202af08162ab400050f80f10bf404b6184e414db0f5300016031e714eb2c3c00000000003a0119464356ee5b20e4f00000000000000553000046dc0000afc0000001930164556f0000f974adc4f25f74dc9096d6281d598dc0001468191c000478c000589c0003d54b28000000010857f114e073754f501c64f46043e28d77176d1bc00005564988016641474a328d1b100008150ef438c017cfc300005b45b811c1000019a129cb4a0e680000000000143c000000112d5ad51ea6358d985d380cd000183e33c580465458813d684f3645c9db138c09f051ca2c5bbd8202944000216c00015012f62b38840610106d55090fa09e523a4b840003850fae41e000000014255f6434e50884344a84e870dd916a0a400000d097702ee114f45c911408f0000656c0003bb40005adcb0c1a60000264d43b12149e4497000046e474101f400006e40000001217000000061758d850b0ad22b78a8741a4e3c16155ac3f5d0163dd81d7624039415bcc950700388008114611f86363ec56793e0897700d417e4cd93401d8c0b34c6084438c914c0bf023061f8000539800033500e24f445cb63d1488000129b329c000033027300017a61fc184a0000f581c0ccb10001315206c9a04eac0622570f3a099539800000005630af6374c00038893824c6d80b00006c41ff4000067575e367862b0d50f332a8c73b62b525606b04d7657c000000183b541971f0000ee5563c3ad49fd1a74f9821a01759610000566109800055d800012b00000a682233d8c00027046920000acc46d81df4aa80000c8876a0f684b90d8c14310ec81a0cc486a28b4bb52fd55d80000bbd476c00041f435d0710ab8617906c30c55341570c5901d40000fb508125e0a181100309144d6522b9543200000003f24ec900000005619533247cd82157c18445e00001134dcc00054ef0000000178d18d3bd94332a6000035a8000417815100017a100000006430f230168f6a2628ae261ad17a05480000000f3e4ab80005f1574d509c21161b0eba06c03dd00015f500000001434107000000063d4a4d2c5d77f44a54f663a05961be82586560000564005346ed74026ed90e0c500000000d
  | 43 => 0xfe0fbc0003fdd5484d741142a202675c8c8911128ca006a95c1000000000002702e910142f8cb731218d7c568415564e800000000002f882b80e4000000000000000b01452d0eb25740004cc92bd288d2852ed14be40e0da31d34ab02b0817b38a8b455d64fc1000000017180001f3003900017be000002e5d6d55c37a10442d212a33e691103a3d8361a5c87c400422219d57d116a04aa000178026e8bf01b6d208109ca773498000000000036cc0003d7c000000000000000000854a680cb40004cb00003368c1c1418c4d00000001ff8000435559e2ccd183000060336c80004d0c5f8271d0e20000f861ad55e81c2517d4edc1050000cca4260000000000029ec31f6261863000101205c51cf53447d400000000000f132d4441e5bc00274c3096f5814da60000de24c90c3924d0fa52905907000111d0000c6d00006a10f9800022d92ba08acb5312fc5820000375118567a000170100009b64b8170256a806e00000004c681e20000e7200002ce2f200004f3d68f2b3476b577c0003a4165917a40001e2d83700000000000a9928549c6366854d285d4a643683855690eab51816a25ee523347e4ec01db56c528f4e94499c8b727946f930949b0000026834100ea581c000279d33414900002288ed92b857c24be4caa5a3570707700f45d9425700003e833494c241180373b309ac39019435f7d11c00000000000d1534e117020100002ca8000069824b3dc88995edca9b2f9cc1a000174a14a40000358f78370c62c05f4f0b4f7194e3cc8000000145e000123800015382440f2d416430a4b30af91a08ceb1c00b4c34c8c0e1bb1937312d70312d5308000020100003701c0857150b58ab5facccb28682386510f252d7829358e98380ddcb3f2f0480c06bcf3162493065c296331365148417d15e054c81d3a841b3148803263a93ed55b142e4f78000005041c00001ff5fb453c3cd506a00018033fd0ee7000104d2a70b230000a490e9400046612ce0000eaa5bd17e63738c405f3c0004d84521396c000000000000000003e1105b1bfc00022c8000061c4fb4fc00000000cd01af888157b48fa22185481bb4c71166875b50045a32fa07a058c0ce95688ef75e609b90558000000146b13552923a4d41b000043809f800000000000d457cb211400022e800059890d70000de40000646000106700004e20000bf25458b9b4dc8000287580e3d6593e20903a6339c0002508000001133c5d9c0000b246851bbc0003b38000164944039c58de0228cbe000136411f46d14db93c55b556701e9192900003f562c10b60c794de0d7d462000000000002f73f114ba000164300000002f395d653b40003eb4158000000030fce9d152cab52c58d39000120e56d8f51498c46e000184c00016e500000003440000000063535693cd50f4d594728fda0
  | 44 => 0x41bc4c33618d142df86df340d2f24680bcf4788bf624d4c60087404352717884d7cde628f03e21e209b3450c3c562892fa54403d564882146364d6e32a127354b94840cd90d03f607a62acc776097c20501d14a148446aa388084f58445171d954b531307be508038901ad7834044cb307c458647dc05557c9557101c12a22e09f9043090910951395a78da800000000000000276000020608d64aec8a600000005e7525d4c14a58323466d51a44b200012f430f10a40000d000000e280d7870c6064ab910200000000000535191b379d0d143590b514bcd350b340004fa4000405400058ec13839b86932ef93b22a554732c2c8f70000a0224655f4228c7fa16ac44e43c89ed16780005aa8000000088213915220001680067800030a0d7a5f6d7841b5c4291dc8bf74afc0001ab4cd700010540000df20834c5300010ad1c5592d00014e2462089300017f000000005afc00000000000001638000000020f00001b0494f0000f3d64bc00004c0000360cbab1cc92d3039d743538478506d100705b0bc60a802bd00000f9575c8b151fd56a57840004da4000000117b10b000000004b800000000f8c0000000000000054123a4bbc00000001a682922968000295d5363ae04770428bf416e0d4616d80002bac00018580000da4000000000013d03b6375518a184814400000005c24abd61943a35ef17ac433177b3148e6c0f940710394ac7345ce215fe58913c0800004a0aa250e800021509c30a0863f4f394e45e50000390c7404a78a050910e30000000000014d90000d5033e0e181ee888a39d40000001485000188a0000411000000000012e6085d3db00000000000000292890407d800000017f200005e44d38479188c0003df42a515a917118c400024f15dd58258f200005af651962a05a4000000017964e0000323817400014901a5559d4338940420854f17b9566336c69b611d2fb52698c554040000000cba306c00031bc0003c400e025348df0000e07412d41e0a9c9de2c1030b08a0af246151c65ba4e233ba54f2000056c634c09c261966349141c53ca0a601f4024f399000042008eb51c40004cfc6a30000fa34e9c000000000000000003d249e00d2d4f930044c014c0000000044300ecda559714034c2cb4724197954c4188714dc1080001486097000000000000000f183228000000000000010ff00002740000bca0000000029805920d16cb62ed3fa363800000006a50b942b349d58ee45044000bc8bd75ef566c00016a8350586a1d64f3c020cbd80f601d5380c7a830a4b630b9d2992210f711e84cfe456544844f90e61d7c9cb4fb8a395038a262b2d14a18dc90d502155039a9936296d192132856d0384a8b300cc1235a48431fcd4444ee8c24032050024fcae731ed3b637a5314522595a228528a4384000245926d2721
  | 45 => 0x4936345013439c0001c2ccaf3f815fb05900006520000000169811bcadb3f518e0492412902ac00019e931320f41d235c8f1f414061d2ab863c37f98eb0000000576921d031c00045cc0a9529157d464068d51048ec52a50d442756c00000000000153254d4000592400029f40001d9c0003c6424a00002073a690634be013b39650df4909288292d179060532a3710000000053561248a011d020e41603c00001109459882e0000fbc000107e115d85511d4000119c07b21ad10828dcc134ff509302004010c1400000a03f609acadf303094e64287bf1695776493d0c029c88e440853e136e400021351b05ee11ce000145504ccc46000142925c460e1f8d2a7582c00000019243bf95b8000000038941de00009973ac462a00013971dd0000138541d2b0147600014d2453912211a800000011d21a5000000000001c3474e612c979567c0003bf043e17800000244b8d00002343e617dc0f9136f477402555540003bc466845f078204f172d251832100008d959fd5f162c48f839681ad5efc965382879754688052c1cb260e8452615915795bcc1e00858000000117663dc3cc386c8ae31e400059983f321d16b8419552000000004ded7563be4f730000000000052c4f24c7a2b8128f27318cb0000cfc172018b423058862111cb19442f505bcbb0204cc1e00006410c9589f1528d3f0000000000000008a84a41f140003c9c89434dd6ce2c4c8683b1d79e22ac422257cb43030cc8552942db0aa520f3a10079383107749347d9242059b0034f39000158423f87d62cac9ff4428a86456cbcd3d19697000000015b80003e64ee000000003c0c1965de5546448000045340000000f544cecfa904b01e52444d3c10a10a224e41ae517011237ed46e0b00aa447a13230a0c3d735b0a4c0cd0ba64760ed35ddc3661e1c4f75574c4a1a9d18e24616f7520533734050181bc52d50914f065eb43332c88fbb3750b3c13c0a813a6049a1b55841000183548d820a36580005e2c5a21560c54470c85642b867b1e486b41ca8ad4512c32f21cd2ea47cd91800011ef58bd1a5587c00000000005d70e88000139300010cb03984151fa0000145400016283cd212c7040000a5f1420d0e62502b14c740003cfc725024c2541e658f008000002e200c900014cd06aca2f000168a32c901b1de91652dc8d4a00000001700c510ef8c1800007ec495c28048a88652a693e740007225e8c8c32b244ea2ce8baf51ecd6348bc4d833395e5333c34c24a126849ec0580e3c23d1c484023f7811903f89031a3d0040f78883424120201dd39040187aa0534a9714689a92c6c09d4fe18694a086a0215ca10331874247c093d100cc7328a131e0b08fa74f608ac0000c8c533c0cb58753e25ea8ce833d51234bf45a412e87781fd5228111c1ed54250f612455920c382b4
  | 46 => 0xc1cd4df511f09c431a8c1650a88d20d24fe23f9489540f05c3430d2d11ae87842278f8b546450350486e31ac54072a986390000000554536028ed68b1eb983410c127a47c86545a6419b02393553510c91536826a35308103fa82e80c30e60239d1fc018c73000008510000412000037b4fecfc61440d561e0c0511cc584f179d1be000057a48c55592bbd1ee0f50eca15e5204045c5c25eb811a62750f327440c131992e56330000190022f09c54c93c1c2a10528c3b1f5c0fb13b4000647d7c8112560e4f68e9f14e98712045941000104a57f40004fc86d2354978f05d54360518bac6468cdd00005945a5972e50ad7c70000e68028d5ae254952945b435b008847f0344987000098839255602c151d5101400a09ec00000007e92dfc9dc04d15822b440003e580000eb01970f2938705e0e7c07f5344175d6ac30891bd0ab53d53000d8801004c244d912f511d7181248d2e51a8edd2664d735dbce6900006885c890e525e88173174000000172f04d92ec208454c5d9864a45f96540cf05f203b462113a596052a8c073c540f63ba06d86120b6400006d000006bf00000812f3000000000002f5800000000002e652605d840003d588122aa47bd1028c052ea04be32258cf3e3400000000005c980005620c2e000000055118392aa836123042d64b595bf2bcca5301f80001f6802c2fb1567000015e3764e7a06e184e43a02f0549535c4e0149904ac0003efc00054f88ad1cd01f45cac00522200bf39e061f2018be502b123f0000b5c2bfc0002d0400012111245ac84600c98000049c86c4c283040f5944c57345ff2a014c72d98f64503477528497ce5a2170d28a92cb545d562658cee21e687eb4cb87df1fd0c5a18d00003ff8ba71da0000513d2a8000000049bce3a64240000000c74226c21210608b3012573e5d14b1163b46000000000000109c1d5c03100bc00000005ae0000000000000006096d40000000000020232789504ad4c5851393a66048000000000054b5675571400000018e7000000041ec4bc49d88c821c45440000ddd0000000000000059c500f409c7e026f8000000000000018fe047c74b60f17874a0cf7b0f85048440cf8320882611789229593d19c3bf4a1b41d04694a8912a3b1552a1840000238c4d03a806d33cec0004254000000002a12a0ed800015d91b705a90000f5b4e395bd2d7cffc29c066457993861ca0b002fbd32f3f911570000000256551b2914ab655e858e000000023cd43900000003f5564714717163fbc49e0b1cf1c4e0cfcb2c5147e252938821e8e742a511255a90d7e05a0ee14fbc49b1984d7d39106a2252c968259d90f4a5c562303c060575503d4294faa113133a5430f8e19c8a6164a932206498e200017e300000005250dec4e7d6b6236c00020ed072000000024dc00046b43781a9
  | 47 => 0xb0917272515623240f530d410b000181852589d64b513fc0a1098d2fb54bf2e288fc173800022598cd27a08bf0918000002d0ea5b64000209d3625bb15ff03014140c48000244d8760b0cf3716e56ba02880000fc83b15d551c846e14f704dc00000010c65b8c97556cc5fd04e87e606d80f3120113447f800049a40001b152306224e312c945bc46a105a36a95f6343c0005634d9257c161454280d43abd3a44ab57fd4df4cab00000003dacd66057044b468800000000000000b302db4b091ba94fc192cd65155124800000002ffc00016856cc1edc5ef4ed0000322c00048b93aa2c2800027140003208000000080024005fe4c48000307c0001d68eee41594ee5d0915a4ec5543320581e03c046612d94431624f2164456c262d11e7267d5a5520c34f202993b56f8e3e023c000101095752880000000ea60dcc00000012222f0985933b800042484da572d6821d314bc19ac5e6000082b00000000000f5d52d99040ee83574574000000079538dc45c51c099b4db533500000005abd7d30ad464407a88f50b8800053ecfe3000028d000015d00000fc0000000000000010e460832912af27511456150e4b60e9853000111b44d49810ae928d02802b75a10fdd4f7d5d000006fc42f8b6b0e9d3ea2360e5e42e4e9247d958b2e309ab088428a217061553106bd42247b15238c0b131815a22bc8085009553605c91b4e14c960e34a2b419128e4f904af282149b223c0004c70c7d31a4ec12590000293c59c5ba15ee274c00059f8000501400001048502ee45610000c430000f6d00013b35720c0962715974ca4000591819900000000000000174800000000000000000609d964000079600006f7000171500013bb0000000074100a13143f84b7d73451180002338000104ccec5bd80004c38fb35148382269c0a848498c7000032b000179111a1105465d4d70a5c56b614966707683c3335867800e80002bd4b312fb80005728aca6264000000000038ad1530f4801e3e506f6532969000001f80000b5a3bc963d3bec48745b981f55511161e34a0c064d2c15f058dd42512a463f4252254c35a1208b8321fd61937140000000c1d1c84ce12da118b4ba04a1227d29010d551d4ed4d472a0cb842b90e455dccee4197ca7c0998d7b36fc09e55384b72184cbd4f58a075a2415f3fcd0a80c54009183472e5e6823526513920af194a08e400000001d648d4bf3000012227c817a34cd4c646014424280e2f357583f068cfee3c758151e38a3f29508da0dd0a03299c6d42af882911c97d41580b7530e9219504571429744c803dc0b00bfc2624ea0e8b43dce2c39283990c4403c5280bd4462499c59d05774ad86f8026cd9419ccea91dfd59948858e63de46e93c98bda504026c4f502aa28707c723bc1bd53604fe6294a742e2467c55c8f95073861
  | 48 => 0xfa3ab56863ca800042692eb0c585ea2c7d694367133149549f42e18f482c7473a60908d02e707de503c78600006c62d007e4597c36d20984484ddcf60414c00060294792e8436461445aa2bd03c11674def61f56f51c5c1cd1bf4ba019655f71fecfc802e847319dc5cd29112d02dbcc9701e92c05e18ed516c0a2206816b1357c65b00000003f400003dbc0002cb40005f312640a88dcf2384f42144800000000000ce4df421980002d840df4c9d25f334c2e602c569c053d0342c70d8406609d030dc9f50f6c0bc4cf44831cbd88008b42c42648e0f44840000c8097d0b7c00051607082e440005354fd63d408520a1ca33349115c29fcb4d1074a6d38681a233808b4329585b3cbd030070d66a1b68b3b3c48082318800012d00000000000311c00054ec7d20d587cf3d016d719251821338f2420e959b3c20c23541d6201e30ae8389071a0524dae3218724198d73029b0d4330ad1995248b7b4dc55db29d44ab22f516712c170859204db2bb50761dc18163d385591958ba3375d3eb51bca013eb116c3854f694dccbb328d8c3d2104aa504594132188a0910590e33a24b95323c7d301387131d70bd3202d15f4f00bba172810435fc4cf5c706f2194007f0e18a35262c86f44f055033085d0163d31709d8f7e01b0752000129400012ee156988539d83bb5cd4a4760a8d4013d487d39206bb370125800003c8089d5050000cad3ac80002dd8000458912657a8000073cc98114400041012d800006114a00ab43bd428e044d3bf5aecccd467c25a479094814ac0000000dd600007ab5b9000061d400000012cd190891c2a4d0472ba400f47243fa0000dab00000000001704391cb2449998220000ded287800007ecb9a2f7c0005b7114426b8c4e395c6f002f8c1400003f00000a2417dc000000041735794fd0001751000000003700003f00bc4642cfd200000003e7c7b85e4135865897af00014ea3ab8213382cfa41744c483f4c00034d10dd29996fd058414e50e17e744544e612242dd076400000016310cb8f7f2d740000e288d10000dba00002ab00000885d20d8b000096d55c0633449c0005b242dc0000e8a2838000000000022ec00000009b753a103f482d75f0000cb03f9c643443d5bc37e4d2f1d180b6115585f30d9430105029835c0d1932500005c3c0003fd87f20c6c7f924740001d0c46400000000bc40000000000318cd360000c450a552d2288009900010855944d81447c57e1ffc139038c000000082c4e350974e516763740f0f1db14b1221d45f398436c55fce5c63cc36b0be527d4de87db5c68fa012b47944fb18461460b905bad4370ed0446486d508005c0004d0577e58954a7000000062204d6302000046cd4c00000dfa341c11d2ed831a00014355da4000175593f00003604f485eb26784c43ed15a82318df648
  | 49 => 0x86cac14bb4745177000000004eb55b5291000000000002ea011097b289c0003a048ea00000005ca800039bd725342d62617d55275f10fa81c1cef8001c2ee1e253d7000174108198ef00006840000000000026e00014b3000000300003ce00001f54ccca3808a5196000068b0b2800029e45c70000000346800008f908462b04534df0d1b6208b446258ecd034cc6b4c7c7cb50985c957385fa23d809046fcd023998aac466d35a428c00037447c64de52ca05c0e994ef458107c902b0b8437227545be4eb81652dc120d5ccc000000001a37ad21e13f18773a14c41407400026740006535731000076f62d986e563977151854d626f00fd026864e552544d355caba0000e8d13e43595650e73310800028e889d00013f95b888c5098c912344ce04471c7b4562965e3d14000183d6165c84af04b642ef56c4f1a1864d62436528920a808d4a940003938000164d732000173b44c45980f4566f39c032a06c8d0942c07260000760000023604b41be3ce102500b446c114077701087b626015741b9c16d00aca6a230879004bc0001b88db84d086b80e78f4c3db89ad1e9cf005860bf118e18e34b912501430d9b10680c6349454625550ee1b2d68724e13c4155cb3d00013040000000189cc8700013f1573c29f51680004799206249c00000000000000f883654000394400000014c85f28ebe1c60362356000000000002cd48475fa98064d500003534676384844f0000b50127c88e00000002bb893023a192500009aa610cfaf03695ab41394ab4f751a6013083e45d12b8046cd746280bea266803f3b6c000537023a62e4e54581884c0218a9f3e990a64b2113d4124781603c5df116970b3a94e5317f03912178af83a30a435fdd1af03c81c626e17ff013c33222901bb000157b0bb0000618124040e954d548c0003c504dc5c197112b40ef3072cad3362455b32f134f64d497633656214581087522cd4b5c382d03ffd59a260cfa1147c17720d85b335bc8a5407862d004048b0f715a6637d92b61088ed481c8f10da8ca946189e93dd4edf0d543b547ed6b30b50d553ae4eff4dd800052096df47114db24f92b45af95411f01747429d64d3e044a0485818633101263de8607378d0c538994e0067c0005d8110e21806c900002ac22a9857000080d58d522044457206564e6d2330000069d72420e09325db101019e48b044102a64a800000e8060b5cb12b21eb00004ca07b35fe07615d180004e800001e6c000626c96c454984d59f12f000000004aad3204a100ad021000031548852f003d900016ed5d9000000000000000000348000033d0db61c0400000018bf00015ad290107052a033b0c701f74e3cbe13b3c26d23b988c000000044a05050bd156960500000ce839b21657b636413165fb96b420d4327349c01928c0a6b4f0995447f51
  | 50 => 0x60a06dd428028573c4a74f6111956dd40a97d543e0c840000160000120a00000000000aea000184534795e01254eb4000092b5bc8000251c05e2354fb844180006168dfd609400000006861c590c43570602405cee32698abb2de40002bdc00028d123d426d20c49512c9330000054e964c00010351c8d39646457f53870dee00009ec46d16ea2abc3810000fc75e2800034f95ba2640e5863a4d8f345800019d00b831c80000120ba90000000000000000000003df02992cdd2dc224811108781d3394188637213c14b7498c1178dc74c1c00023f40e90000c442b14e160049163059d82823893594d9491e2c209a43f98e9707e58783c1437949e4e3446053571c3cffa0614f66629089c45fd6395b350aa05b851e5980bdd1b2941a297175d0001833000050b0b2c95644e00892b60c2700018081d551934ac58bc29400d75d600001b98e102c658af0d34f652850000000186d2b0d56e212422644c103336015a014052a615a45d462a8b2e43f4000201c0000000d6d38cc00000013fe00010e411acf8000000005198000367d0ab30b400000019554f0d58756055fa3d1ce9b23286175d1062059ad10d0c4c2d523c00001c64e012d3979700014240ea00b9070538121a58b8282c7bc1f9449d17c06893f3c9da163446306345bb619c096424571d5b057fa60a4dca3a901ec08707ce000000018782fe54fc39f3430101628417219a8bfd43795ec3a9d6451a40df7207807c4d453264bbc25d222c00e444d68e1898cf24d18dfc43e478a07a04230de890b32ed1ac2ff820b31414e9319c0aa4eb588d5e08fca337000064209bd261541c64c98c135e1325632955e5e709a200001fa00000003edcd221f7400000000002a300002b194045fb028c2d5430f00007625a4d4873b585bf00015fe000156b275d80200016080000de04fa0858235c7270000951000182d2d603932e5800039495dc40d841f0000a0061ec0000bad33e4bfc2bb381595c02604c144ac7663590da94f656f8011973a0fe55180930bcb36b064f0ab80e852b8a5e50f092338780675560b7a5fbceb30a197d80cc0f305f68b0d0250e3d1cd800013786d933e439c36640001a059063af54c12d882b9000092a534d8fb117c0001a28e955395218000058338fc00005a877130850450000000000100b57e40000a04000441cec33ee800010f05072e48c7611b400000007d821200003484fdc60c014c344950d1fd83b025a83cf5b458a9440840c0f4c50e369c0ff26110d856d40d220c85281b791f442852035f242c1003177d4eb0a595b290683fe17bb16001e7581000027489a1586854e03406691e7870e14ed2ac27f473e2d580003838fb92c085324d15785000151324980002d6c00044b810300000b45d4885f00015eb4bd42772775719002195d4a1962464a00001
  | 51 => 0x2300e460e918ce086c4365974002620c2d31d2151c46e8853268c9a542dcddf58f01db54ad4ff65481a457881fc1a70acf3f14fec5800a6e094d1cd4ec064d006c77c33e92b334c0c1956700133b1108e6540e3623fd1e90a246d63ead4781994d544bcd578594ccc747313990fa95472f78cc30148b365a7ca8a3e6c7bb2939215000192e00000000000000000152822258d54a7cdda0bcc8021abc0233fe526a000164b00018c8604caec5b683fe22357fe4e54b8051f4d8a19c447b4f2d155000060104940000000df313f433f339400047409df32d17c6000085a000081c2dd0d9100000185478000000113b625d003523000042bc0004b1069e3d78d68000068e25b919558d8142326c24d2c685cc102c00006541a1052114904c80002f8175407282f6000125a5dd00000000c5b29e89204840000000077e1f2194b06a400058040003cb00000c3473d05500000c756770000798000000063c54b83adc7b03bbcc0d588c6664cc084a0231916487d13a2fe0000000000039348bc34ac00002f48be491d400000000000000000000ea23e4800054bc0002cbd87c5940000000000000000ec0000000025c9724c0106e42d011025506620db925100006455c5d2a91ebc72c63d85730ac88900eb900d31dd736331499111d80002a800005d2c57c1ba00000140000000141f000030152b4d0810f400044600000000000289534b278880101580005a314bd4f94ce43e418b52efc00026bd39c2e398a7287d0ed21180005624000586c2c5410d82327ad94751441e353b023114b84d459542d800010f52a390ec564d6b012040003f7c0002afca422988fb002c905237c079d623d39e40b550b5df05e10000a913834000000178100000002b697a9519589500016415bfc1b1000004d15e0000258d7ba63fc00000001d4251568159a47640484cff095400051e8db05ce062200000001de52c7080cf93365cd615b103953a195c250292261c14a0a2e955de64817b01cf15d20000db5000170c00001dd415537825780000e015c424b14ac40bc3bf305d4935928c6c58ad61e319000004b994505d97c3171080e3af0549502c2e9356c5390c904421ce09ca00006ac497902c6014e4c168018f1e4c3b946b8683407d54b26c5239363016212980704a2c0c4159d91c4c2459743d029143c4000148d92c40914fa24c48dc0ef143f1af12be2cd1665036c3b85e895395e34dd841c4a780d4c2af00f852706e8c783ab064c14c47a364555e362b852538a47f82eb8a645f58f2b4bf00733e2573f655cecb5b99349584c28f2d497a800000001334f09463c0004cb41411818a63000048a5fa40005af400000002940000000083c00034280680a6d71003096e1000145d650146c17955003ad47ee525c00030413cc00000000000000000000000018da4370
  | 52 => 0x8c5f0df42370480f2e58dc000000139a47fc0005ca400039dd2bc1cacd1d27ecb1000d000049c40000000000432990228c48d44f1800045ac0000e3995600015c348140000000dea59088e64fd40003a096402dc4ec61c7428b2df11da42c4e7d40886995e9050a00016a6000179b00000001038da10ea80003158b824fdc10950547b5432000024a4ed222a15145aa47691d4c96057a4eda00000000000f8c2530ca10000000273d66432b800000012de092490204d400009014bb4b6d4b7000097c28188760f2493a32fd298534108d082421031f960a0ca577209783005f818b74170383029d1a914250d31d3c21951d55910001477000000000000003354d454dac88c1c2934717a1449626934a32207dc27d842413247c4265485d0a14f9c59a0e1f45a0f8717582470fecf5c2f1d5bb2f716db123cc1557f18c0046097306711e025059531ea5552514cfdb523d031243d4cb200ca85606cdaf29f8cd1016d0990000d8d30d0f0d1968e5f0001287000062f00014dd5f940000000000415c02100011d148b400018613480091503000165709bd1646324b985a4442e49044945254cea000081f2b74c3e00005755190b292f14fd11e7c5345d691ed6238969389ccb95f00b69618969a0f190374a551d32eb40855a7566d46752cf395800022e4000137c2723248e8e09e12095fd0b4b46847f73e3c000484cd79451c000000000019813c7090891516f423f192000060340000000ac8000191229c4350519c000336000001a9583021c00000013a9000160c000000000017280000358000000060440000c0830646a85166524d3d3e7418325c04ec3aa10e0553d9102c9d1c52aac0002438ebb238013f30e12c51b1cd512e142de00013f4000038b0ad800000000004c8508b0fac0001ac0000000127e0434000000000024ccb490000a9640a011e5409564284c60c06942d206250425b4c000000175759603d0007c5451ec96a7250c66e432574c508579600c115049d155646d4c064479844596900927b96fe00001e927bd54513e000021e00004850dbd2ce5749382181d00016170001020256cf1762f800000016a525ac67d52e4beb08cc03800017b31ad8ed42ddcc0a1b3ca0d27dcf43263c000151c41b01505f121ec0720f80ef00c205b55db9800640014030985683044ab2219cdbb07449e140981cc434904c1664000208d67d5a84ff160c81ef3dc06e13520452104051b00010bc5454bb10000b781cb4989000146d6478e7b4f209745f40000657800018e919e000139b1890f11203c75856144f106441c70075901051521c516cb4f2c5562921e52b9000000000003af33048a713e97fb1cfd366000163f5ed40005e380004964000000075e000000000018db17d029e000183d4dfd0b333dc1eb4a4cc3214814721ce4d284064d71
  | 53 => 0xc31847332260720199cd4f263818e4f4cb3840f90b80e1d0862db8e7f0df8f0c5e252465484f1e2568c2a20dc11c63b09f00e5853f29d8ca63ec8b1828106f3549919a5f907c9313d4562154a6f15496b9103c5c100ccc933ad82e35314be425856d834b4a4622004d300455121dcd4a3607071b14d84064a0500c30b0dc64c645ad6171874634006f29cd62c1b00ab15f5cc205f3422e5ce49d9231c57b3dd167817b123b184c80938b4e9e3b5d4b01c783b734e8d6b1b2053d12c4dbe61c903b0c1d6ae5e958264708f67538d3a24ef14170fc53012e4c0e44b9cdb154dc07825fd1d72eed9133f38b9407982b007b8328185102e22d586f18ec90a53d03c2064087234349a842a51d62f4559832e05b24d49311265957e4610ff216dc5cf5b409fa0f7c15960b96fc603010f0f1c7cd347ceec515c0ef4e452e242215c927347ad116d6f10ff482520fc5d83e78feb10acb5733d86ae583d35e4868ede3ff45a703140953cd800042fc96223c8f4f4cad87a13b91f8159465258497531e453d03ba98bd000092d332557352d10f042b08630c6400000009361954000000000041440003748000123066c0b201f01f9c74717ec0000000aa134c40d9181406d59cd92605fccf35d884ef0000a484890b9d04005332ff130d2aa07294fd8f220a707492bc40005ec8a84182429d49f1237468c6cc1c4152c0f9d7635b1cb8b653ca0f00011003d2c6253170da05c14d9327f11510f2c5951b38cdf28c88cd5da800056e4000000045814652f70d18fcc3b709f111040002f9805c06500000248a9d0000000089400019bd005000173d408c248000000000000001778dff1a9831700000000114000494c7c31bec34553c05021ae4d2c4d355c70000a525aac000384c50400006e00d718a61e940000000000000145417640005744d4244c8f62506400043bc6ee0b3149106d4ca251f17fc372d4fe32d85ba2f48d496348c80015c4ff5f84b0362c8498622d44555dc84248f9137628c92e3e443a900004973e8800008b01150dc43ec38ec25615740005fd91eb04c4e623e140001a4579f103433842e95c038d4cfd0000e965e9ca920490b8756dd2d723e40eb3b08b2c49852e32bf0d1c2858b81385d61c12b8fd9000137e5bec000150c65c338cbb71aac3c40c60069000033740c8afb490cde500017b402940004e8c000458418000015f84d8cbfa00009ea00f446219780d85de80005c4869d49e00000c409210fdd0bd3674c9d1fc59274ac0c5700000003d04587000037f18f5524083059f03757d20e8908f3fa442d19613531fb5656584130f1f5523c1ac924c327156120a14cc11c492f4b68efa354d1190001563055d4630000ad6022d93300000000000000000000064e554a3cd049940095e4019800041890c2427d78c278cafd000135b5b5
  | 54 => 0x2c853a1241c296070884e0000ec8410434a477c25020c4000000000000001660001112000000032dc00000000000000f0e174d4ce06a0000000168300000002c1800000000ce413c0001c500005e487e100002a80b91801635d5ef2d8150f1f8800000000000000c7c0880c682a9d38c17e4b7d15785b1556c0004068397382543456015f340e444510dc7a234a47d105ccfe833302fb20b40361bd02d141cd7ab27f969200014df3444cf0476548a5b3c0001a58fc220640004ee537047d571e02ec4bb2b8c4a526fd6ad45dca5663846321df506b1fbd5b434616d22fa55a910648fb33892c62fed8f85a8097e286423231fd40c0418d7552744d126d52961150b97395551f21c001c1aa4b8f4f8c1bf0fb993c11c092404f46c31381893158c27f45604592c78dde0ecc67f1c710835939856332020812389b227096bc3fed1a458f88de4c0c00036d126c0b3d7e25be506042789580e1124a1adc0d533ed3a5430427d2700ced399442a00a51c0544507c14451e1341925b195d1f13398b1209a523250c52c2139c9f32494a3e2844b5921b826418f818a2e7d62d4ba5409568d8fa10cd0662a08adc2f54dc260413673b40fbd132c49c23114164e1123461c0f2931b80cf4431575501907f63f0e1d056d075442d356154c2043d488e52d50ea3580827c234d374000059011e03fc295434728a4d764b0cc9000000000d9d1e5000182156c00002da926e0cd400000008a910fd2521174a6554c4687176955f27e0a2e506166107250cd60b0b42446972749c8c30000001502d52f10ffd169000034800005555834000539c0000000000341556809e908a000000061e550449dc6eb15d10db000087e58d0dc10b5d672000071149aca8900000002a3421f076024e14a86cd3a440005c4c33e5654c9f0a8c1f30000a902b5d4b264c47060d1000034a80a43008fbe5c6c90500003e91d758c662a191d440458b44fc33d1b9400012897e842c92fe194d38a012944a455024126080002a788641d50f6c00017de2f64dcd42ec875233d34c40216440000ff55438c754dd53af38e4f1b00014591c7c4a90cb0e3815c80001a7d82f63091425dad1b20be04f634ec570574c839133186641858b338015cc2b116153f3569b2d192270b680ae55943b225995b225102e02b6418c48046295de13f333796a3115899810bcf44317905d39f8188527c62812211d43010e0217b58c33da157141e91d
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8df835d942040051b906bb28408003171cd65508100064e39cc8a1020048bc875914204001938e6b2284080023761b73508100062f32ee6a102000c5d65dcd420400193cc9b9a840800327593735081020e67316e6a1020008de8758d42040011b90eb1a84080123b21d625081000667b9ac4a102000ccc7358942040018eacbb8a84080032d593715081000672b16e2a1020008f5861c542040018eaca38a84080032d59071508100246e41eec99020048ec82dd932040091b90eb1a64080123b21d624c81001c3f42aeda08203287f865d7410403787cc8bae82080031798d75d041000637312eba08200787f8759741040010fb0eb2e82080030f9d564d04100061ebaac9a082000c5e7558f41040018baeab1e82080031b9d562d041000636baac5a08200387e85dda41040010fb0bbb4820800a37a0f76904100046ec1eed208200387e855da41040051bd06bb482080021fe1975904100062f31aeb2082000c6e625d6410408d8ecc2bac82080021fe1d65904100043ec3acb2082000c5e73596410400187ceb32482080030f5d664904100064f39cc92082000c3e75592410400187aeab248208003279cd64904100046fc32e72082000c5e655ce41040018bacab9c82080032799173904100064eb22e72082000cce625ce41040011bf0eb1c82080023761d63904100062f3aac72082000c5d7558e41040018dceab1482080031b5d562904100066739ac52082000ccd7358a41040099d4e0b1482080032e591709041000674b12e120820048bc84dd9410400917b08bb082080131e9c165104100266d382c62082004cea7058841040018f2cab80820806f2e99170104100066cb1ae02082000ce9625c041040099d4e0b1462080033658d708c41000674b12e11882000c6c725953104001ca862b2a62080032b1ca644c41000656392c89882000e94315913104001998e4b1a620801ab5205634c41015476c36e49882000c6e65dc931040018dacbb9262080032b993724c41000656b26e49882028cce63dc9310400199ac7b9262080023ba1d624c41002c7643ac49882000ec43158931040091df0eb1442080133a9c162884100047dc32e11082000ce9625c221040018b8e6b2a4208003271ce64484100064e39ac890820268dd86dcd21040018bccbb9a42080031759773484100064f326e69082000c9d64dcd210405999cc5b9a420800237a1d63484100346e43ac69082000ccf735892104001998e6b1242080031e1d776440100063dc2eec8802000c7885dd9100400197709bb220080032e21376440100063dbb6ea8802000cbb76dd11004001976ec3a220080034e1d4744401000735baac48802000e68755891004001d56e8b122008003aa1d1624401002675b8ac48802004ee3715891004001dc2c518a2008003b85893144010
  | 1 => 0xd0a212c8080028f61442590100061fbaceab202000abb805d5640400957100baac808002ada0673590100055ac0ce6b202000a3e851cd640400147b0a39ac80800387d4e53590100054fc1ae4b202000a9c835c9640400156902b92c8080028fa1472590100051ec28e4b202000a9e83d49640400153b07a92c8080022fa1c52590100045ec38a4b2020008be870c9640400117b0e192c8080028fa1432590100051ec2864b202000ab6810c9640400156b02192c808012aea0032590100055cc0064b202000a3e859c5640400147b0b38ac808002a7a0e71590100054ec1ce2b2020008be87d45640400117b0fa8ac808002a7a0c51590100054ec18a2b202004aba8014564040015730028ac8080028fa1431590100051ec2862b202004aba800c564040015730018ac8080022fa1c21590100045ec3842b202000a3e85085640400147b0a10ac808002a7a0c21590100054ec1842b202004aba8008564040015730010ac80801237a1f5358c100062fbaea6b1820048dc8754d63040091bd0f192c60800317dd67558c100052f428e8b182000a5d851d16304001c3ea92a2c60800297a147258c100052ec28e4b182000a9e841c9630400153b08392c608002b5a047258c100356ac08e4b182004ada801c9630400d5b300392c60800237a1f5258c100046ec3ea4b182000a9e84149630400153b08292c60800297a144258c100052ec2884b182000a5e851c563040014bb0a38ac608002a7a135158c100054ec26a2b1820008de8714563040011bb0e28ac60800237a1c2158c100046ec3842b182000a5e8508563040014bb0a10ac608002a7a102158c100054ec2042b182004ada8008563040015b30010ac60801237e1d63d0c100245e43ac8a1820048dc8758d43040091dd0fa92c408002b3a0f525881000566c1ea4b1020048ec8754962040091dd0f992c408002b3a0e755881000566c1ceab102000aae841d5620400155b083aac408002b3e0d74588100056641ae8b102000ae4815d162040014dd0a3a2c4080029b614745881000717aa4a8b102000aeb8055162040095d100aa2c4080029ba14735881000536c28e6b102000aae841cd620400155b0839ac408002b9a04735881002d72c08e6b102004aea801cd620400b5d30039ac40800393d4e53588100057340c86b102000ae58190d62040014dd0a21ac4080029b614435881000537428e2b102000a6d851c5620400155d0838ac408002ab610715881000567418e2b102000acd831c5620400b5d30038ac408002aba13515881000556c26a2b102004aea8094562040015d30128ac408002b3a0c515881000566c18a2b102004aea8014562040015d30028ac4080029ba14315881000536c2862b102004aea800c562040015d30018ac4080123be1d62d08100146e41eeca102000
  | 2 => 0xf64485100064e398c890a2000c5f65dcd21440018b8cbb9a428800327d9373485100064e326e690a2000ccc73d8921440012eb0b38e808806f2d19271d0110274dbc3a83a022004ab48650740440010ff0abb2808800e1f215765011001c3e428eca02200087e86dd540440010fd0fb2a80880021f21f65501100061fbaec8a022000c3c75d91404400187eea32280880030f1d464501100065bb20e2a0220049b48750540440095690ca0a8088012ec2014150110004bac28e29822000e386519220440035d104b1c40880123ea1a7188110005b8c2c831022000cb464dc520440012eb0a38a40880026d61071481100065a320e29022000c7876d952044001970edb2240880032e1d864481100071c328c89022001aea82d8d2044133d9065b1a40880063e21d634811024de441a849022000b71851c520440017630838a4088002dc6164148110007d0a128290220049e88748520440039d0ec90a4088126f220d2148110006f038a429022051c7a76d97104409d974edb26208806f2e9d864c41100071c328c988220018fa86dcb10440016e30b20e20880030fdd274594104c53dc02e8b282004a78805d165040018bee739aca080029da0643594100053ac0c86b28200087e8710d65040010fb0e21aca0800297a0f72594100052ec1ee4b282000a3e841c9650400147b08392ca080021fa1c42594100043ec3884b28200087e870c965040010fb0e192ca080028fa1032594100051ec2064b282000a76810c965040014eb02192ca080129ea0032594100053cc0064b282097a79809c565040010fd0e18aca080021f61c31594100043f43842b28200087d87085650400147d0810aca080028f61021594100052f41842b282000a5d8308565040094f50010aca080029e60021594100245e422eb320201bc3f75d52640400917908b9cc8080122f21172990100046fc1ae532020028dc835ca640403787eeb3acc80800387d4e53990100054fc1ae53202000a9c835ca640400153d07a94c808002a760f52990100dc5f438a532020008bd8714a640403717d0e194c8080022f61c32990100051f428653202000a3d850ca640400156d02194c808002ad60432990100255d400653202000ab9800ca640400147d0b38cc8080028f61671990100054f41ce33202000a9d839c6640403717d0fa8cc8080022f61f51990100054f418a33202000a9d83146640400147d0a18cc8080028f61431990100dc5f4384332020008bd87086640400147d0a10cc8080028f61421990100054f418433202000a9d8308664040095750010cc808002ae60021990100247c402eab2020048be87d51640400187eebaa2c80800f0f9d654590100245e43aa8b2020048be8790d640400156d0321ac8080028fa1443590100051ec2886b2020048be87909640400147
  | 3 => 0xca1a20028be87d9143440070fd0dbaac4880021fa1f65589100062e39ecab12200087e8719562440018b8e632ac4880030fd9774589100061e32ee8b122000c3f651d16244001878ca3a2c4880022fa1f64589100061fbaec8b122000c3c75d916244001938e7b22c4880022fa1c64589100061fba8c8b122000c3c751916244001938e6322c48800317d9773589100062e32ee6b122000c9f64dcd6244001938c9b9ac48800e1fa1f75589100045fc22eab12201b8bc845d562440011bf06baac48800a3720d75589100043f438eab12201b8be87dd1624400187eebba2c4880030f1d774589100061fba8e8b122000c3c751d162440051bd0fb9ac48800317dd773589100062e3aee6b122000c9f74dcd6244001938e9b9ac48800317dd473589100062e3a8e6b122000c9f741cd6244001938e839ac488003331cf72589100065a3a6e2b12200087f855db42440070f90abb684880062f21176d0910004bac2ce3a12201bcb4649c742440091e90cb8e848806f2d19171d091001c3f42eeca12200087d85dd942440051bd073b284880023760e76509100043fc2aeca12200387c855d9424400117f08bb2848800237e0d76509100146e41aeca1220008f7815d942440018b8e7b2a84880062fa1f64509100064e39ec8a122000c9c7319142440018becbb9a84880031719773509100064fb26e6a122000c9c64dcd42440070fd0bbb264880021f617764c9100dc5f426ec99220008bd84dd932440010ff0abb2648800e1f215764c9100045fc22ec992201b8bc845d932440011bf06bb264880023be09764c9104d43e432eba0a201bc3c645d741440a30ff0fb2e82880021f61f65d05100061f3aec9a0a2000c3d75d9341440070f90b3b482880c61f21975905100043fc3ecb20a200b87d87d9641440018bce7b2c82880030f9d764905100061ebaec920a2000c9e73d92414400187cea32482880030f5d464905100064f398c920a2000c5f655ce41440018b8cab9c828800327d9173905100064e322e720a204b974865d641440012ef0fb2c828806eada1b64905100065b3b6c920a2000d3575d924144001a6aea32482880038dd9464905100071a328c920a2000e36751924144001c6aea3248288003555d673905100074a324e720a2000cd6765ce4144001aaaeab9c8288003a519173905102765c386c8a0a2000c7865dc141440a38e8edb2a828813b2d1db74505102765a3b6c8a0a201bcb4761914144001c6eca322828806f2d1db42505100055a43284a0a2054cb476509414409db66e83828288002f860870505100dd5a4328220a2000e376550441440018d8e5b2a62880032b1cb644c51000656390c898a2000ccc72d8d31440018decbb9262880031b197724c51000657b26e498a2000cac64dc931440018b8e7b2a4288003271c
  | 4 => 0x44400117f08baac8880023ee0175591100061fbaee8b222000c3c75dd164440018f0ebb82c88826b1d5c465191100045fc3ac83222000a3f8559064440014790ab20c88806e2f21175191100de1fbaea832220008df835c864440051b906b90c8880030f9db65191100045ec3cca32220008bf87594644400153d06328c888002a760c65191100061f3b0ca3222000e1e831946444001c3b06328c8880038d60465191100051f42cc63222000a3d8598c644400147d0b310c8880028f61662191100071bb2ae23222000e34655c46444001c68cb288c888142ad21951191100de1fbacea3222000e1f5394c644400156d02298c888002ad60453191100054fc1ae43222000a9c835c8644400153d07a90c888002a760f52191100055b40ea43222000ab581d4864440a157501290c888002ae60252191100dc5f438a432220008bd87148644403717d0e190c8880022f61c32191100051f428643222000a3d850c8644400156d02190c888002ad60432191102855d400643222000ab9800c8644403796ee4b88c8880032d5c971191100de5bb82e2322201b8be87d44644400117b0fa88c888002aee0151191102855c402a23222000a9e83144644400153b06288c8880028fa1431191100051ec2862322201b8be87084644400117b0e108c8880028fa1421191100051ec28423222000a9e83084644400153b06108c888142aea0021191100051fc2ae03222000a3c855c064440a196ae2b80c8880028fa1730191100051ec2e603222000ab681cc0644400156b03980c88806e2fa1f20191100045ec3e403222000a3e85c80644400147b0b900c8880028fe1510191100051e42a20322200087e87d9563440018d8e5b2ac6880021fa1c6558d1000636390cab1a2000c3f65dd16344001878cbba2c6880030fd947458d100061e328e8b1a20008be87d91634400187eebb22c6880030f1d76458d1000656396c8b1a20008be87191634400187eea322c6880030f1d46458d1000656390c8b1a2000c6f65dc963440018d8cbb92c6880032bd937258d1000656326e4b1a200387e87dd5634400117f08baac68806e2f2117558d1000477c12eab1a20018ec825d563440010fd0e3aac68806e2fa1f7458d100061fbaee8b1a2000c3c75dd1634400187eea3a2c6880030f1d47458d1001c6e43aa6b1a209bccc7254d63440031dd0fb92c6880031bdd77258d10006363aee4b1a2000caf74dc96344001958e9b92c6880031bdd47258d10006363a8e4b1a2000caf741c96344001958e8392c68800333dcc7258d100043fc2aeda1a200387c855db434400517908bb686880025d61671d0d100de5a324e3a1a20048f4865c743440070fd0bbb286880021f6177650d100043fc2aeca1a200387c855d9434400117f08bb286880023be097650d1000c76412e
  | 5 => 0x80062f21176d0a1000c5ec26eca14200087f855d942840070f90abb2850800237e0d7650a100146e41aeca1420048ec875894284001998e6b1285080032dd907150a1001c3f42eec994200087d85dd9328403787cc8bae83081422fe1d64d06100061ebaac9a0c204fc75615d6418409d17d0f3228308003331c9634c6100066639ac490c209cec83258d20840a579106a124108002f8e054248210295e441a429042000a3e8498f654400147b0931eca880028fa1262d95100051ec24c5b2a2000c3d741d365440974ed023a6ca881469d60474d95100062eb98e7b2a200087e8710f65440010fb0e21eca880028fa1272d95100051ec24e5b2a2000a5f835cb65440014b906b96ca881469ea0072d95100053cc00e5b2a200087e8710b65440010fb0e216ca880021fa1c32d95100043ec3865b2a2000a3e840cb654400147b08196ca880029da0432d95100053ac0865b2a2051a7a800cb65440014f300196ca880021fa1c31d951005c3ec3863b2a200087e8708765440170fb0e10eca880028fa1021d95100051ec2043b2a2000a5e8308765440014bb0610eca881469ea0021d95102253b40ee1b2a200087e87cc365440010fb0f986ca880021fa1f20d95100043ec3e41b2a2000a3e84c83654400147b09906ca880030f5d754d91100055ac0ea9b222003c3c75953644400717f0eaa6c8880028fa1443d91100051ec2887b222000a3e8510b644400147b0a216c888002a7a0c65d91100054ec18cbb222000e1e831976444001c3b0632ec8880038d60465d91100051f42cc7b222000a3d8598f644400147d0b316c8880028f61662d91100071a32ca3b22204eab486547644400187aea3aec888002a7a0c75d91100054ec18ebb222000ab6811d7644409d56b023aec8880028fa1673d91100051ec2ce7b222000e1f5394f644400153d07b96c888002a760f72d91100051f42ce5b222000a3d859cb644409d57500396c888002ae60072d91100054f41ea5b222000a9d83d4b644400117d0e296c8880022f61c52d91100045f43865b2220008bd870cb644400147d0a196c8880028f61432d91100055b40865b222000ab5810cb644409d57500196c888002ae60032d91100051fc2ae3b222000a3c855c7644409d17d0fa8ec8880022f61f51d91100054f418a3b222000a9d83147644400147d0a18ec8880028f61431d91100045f43843b2220008bd87087644400147d0a10ec8880028f61421d91100054f41843b222000a9d83087644409d5750010ec8880028fa1770d91100051ec2ee1b222000a9e83dc3644400153b07b86c8880028fa1730d91100051ec2e61b2220008be87c83644400117b0f906c8880028fa1720d91100051ec2e41b22201bc3c645d6644400187cebb24c8880030f5d764991100043f43ecab22200087e871956
  | 6 => 0x666398c290a4000bc5831852148023b88e718a42900067921d3148520005724326290a4000dc873dc121480a917b0fb2680900467320d72d01202ac5f438c8a024000a3d8519140480013d70ea146090046f220d428c12000cf5412e318240009eb8748630480237910690c6090056f2209434c1200ade541ee49824011bc8835093048001f1286a126090056f2209314c12008de441a429824000fc13148530480051bd07baec9880023760f75d931001e1f3aca9b2620038bf8755364c40018bceb39ec988003175d673d93100062f3aae7b262000c5d755cf64c40019aae738ec98806f0f19175993100061ebaec9326201bc3f425d664c403787882bacc98806f0fd0175993100045fc3ac832620008df835c864c40051b906b90c98806e2fa1375d8f100045ec26ebb1e20008ef825d563c40031d904baac78800e3721d5358f104de66392a6b1e20018ee87dc963c400199ee6392c78800e1fa1676d0f100043ec2ceda1e2041acc8258f43c40091eb0d38e87880025d61671d0f100066ab1ce3a1e200387e859d943c40010fb0b3b287880023be097650f1000c76412eca1e20008df835d562c40051b906baac58800a37a1f7358b100066639ee4b16200387e859db42c40010fb0b3b685880062fa1276d0b100146f41ceda1620008dd839db42c40091eb0d38e85880025d61671d0b1001c3f42ceca16200087d859d942c40051bd073b285880023760e7650b100046fc1aeca1620028dc835d942c400147b0b32285880062f21d6450b100046fc1aec99620008ef825d932c40070fd0a3b265880021f614764cb1000c6e43ac69962001acc8258d32c4037878c8bae83880030f5d764d07100051ec2cc920e2000c76755da41c40018eaecbac8388002cd61664907100066abb4e720e2000d55759ce41c40019aaecb9c8388003555d57390710006b8baae120e20008be8719141c40012eb0bbb28388002ec6036450710004db438c8a0e2000ab48650941c400117f0eb2083880036c505701071016566412c718e20048de87d8d31c4001998e5b1a63880a2b320d62887100247743ec490e2000ccc73d8921c409d17f0eb2681880025d61671d0310274dbc3a83a0620508be8799140c400147b0b32281880126d21d41503100ad66412c69862000975851c530c40019aac638a6188046b320d6248310004bac28e290620009b5841c520c40011bf06b94c90800a3720d729921001c3f43eeab242070c7710dd564840e18ea21baac9081c21fa1c755921001e1e3aca8b2420048bc87551648400117f08baac70806e2f2117558e100246e43aa6b1c20048de878c963840010ff0abb6870800e1f21576d0e100043fc2aeca1c200387c855d943840091b90eb1a87080123b21d5258a100247743e64b14200087f855db42840070f90abb6850
  | 7 => 0x7e859c664480010fb0b38cc89000a37a0e71991200046ec1ce3322400387e87dd564480011bf06baac89000a3720d75591200047bc0aeab2240008f4815d564480010fd0e3aac89000f0f1d6545912001c5e43aa8b2240028de87dcd64480018beebb9ac890003171d773591200062fba8e6b224000c5c751cd64480018eeebb8ac8900031d1d771591200066bb9ee2b224000cd473dc564480018eeea38ac8900031d1d471591200065bba0e2b224000cd7731c564480019a8e638ac8900032d95071591200065aaa0e2b224000cb6401c564480019688038ac89006f0f99175191200045fc3ac83224000c3d75590644800156902b20c89006f0fd0975191200061ea12ea322401bc3c415d4644803787e80ba8c8900123b60b75d8d2001c6fc3aa7b1a40008bf845d5634803717908baac6900023de057558d200047a40aeab1a400387e851c563480010fb0a38ac6900021fe1576d0d2001c3e42aeda1a40048ec865cb43480010ff0abb2869000e1f2157650d200046fc1aeca1a40008f7815d943480011e902bb286900123ba1b7250d2000596c28c8a12408f9ce87dcd4248001998edb9a8490003331d8735092008ec639e86a1240019ac8750d4248001b90e7b8284900021fe1574d852001c3e42ae9b0a40008df835d361480051b906ba6c2900023de1d61185200055a422c230a401b8be84dd4614800117b09ba8c29000a37a0f75185200046ec1eea30a40018f980dd461480018f2e13a8c29000e1fe1d75185200063cb82ea30a4000c3e759d0614800187aeb3a0c2900032e5c274185200061f3aae830a4000c3d755d06148001972e0ba0c2900032d20574185200062f3ace630a4000c5d759cc614800193ce9398c290003275d273185200066cb84e630a40028df875cc61480018bceab98c290003175d573185200064f3a2e630a4000c9d745cc61480019b2e0b98c29000333e09731852000666412e630a4000cd6215cc61480019aa42b98c290003335cf321852000e74b866430a401bc3e645d7414800187aeab268290002ad20564d052000696baa85a0a4000ab58418741480070fd0a3b482900021f61476905200146f418ed20a40008dd831da414800147b0a32482900063e219709052001c3f428eca0a400087d851d9414800117d0f3228290002ad20564505200043fc2aec20a400387c855d841480011bf06bb0829000a3720d76105200045ec3ec820a40119cc835c841480019cae430882900063e21970105200043fc2aed18a400387c855da31480070fd0a3b462900021f614768c5200dc5f420ed18a40008bd841da31480031f10cb846290267720c9708c52000c76410ec98a4000ccf321d9314802b998e4b1a6290002b5205634c52002476432e890a40119cc835d121480f539d0fb9a429003e3ba1c61485200
  | 8 => 0x64b90c898003175d632191300054ec2464322601bcb4415c4644c0031bd0738ec4980021fe1576d093001c3e42aeda1260018bc845db424c037938c8b9e849806ea721943d09300146e418eca1260018be87d91424c00147b0a3228498003271937350930014ce43a86a126054a9c8650d424c001938eca1a84980021fe1574d853001c3e42ae9b0a60008f787584614c0070ff0eba8c298003170c975185300062f98aea30a60008dd878c8614c0018baeb190c29800e1fa1476905300043ec28ed20a60028de831da414c00187cebb2482980028f61464905300061f3a8c920a6000c9c645ce414c0070fd0a3b282980021f61476505300043fc2aec20a600387c855d8414c037938c8b98829800a3e21970105300246e432e898a60159cc825d1314c001998e53226298002b5a06644c5300052ec28c898a6000c9f74191314c001998e4322629805673a1f724c5300046f43ec498a6015ccc72d89314c0211bd0e30a629800297614614c53000666390c298a6010ad687185314c0019ad0e30a629800395a14614c5300072ac28c298a6000ad582185314c001d8ee430a6298003b11c8614c530006e4396e098a600087f855da214c0070f90abb442980022fe1176885300dc5e422ed10a600387e851da214c0010fb0a3b44298003351d931885300ade24126310a6000ec7624c6214c0051b9063b2429800a7521d31485300066a3b26290a6000c3c75d91404c00147b0a32280980030f1d4645013001c3f42ce3324400087d859c664880051bd0738cc9100023760e71992200247c402eab2440048bc8755164880091bd0fa9ac71000317dd75358e200246e43aa6b1c400387e851c563880010fb0a38ac71000317dd67558e200052f428e8b1c4000a5d851d16388001c3ea92a2c710012b6a027158e2000567c12e2b1c4000a5e851c563880014bb0a38ac710003355c47158e200054f426a2b1c4000a9d84d4563880011bd0e28ac7100023761c5158e200246fc3ac7a1c40048dc8758d43880091f501bacc3100123d61e51986200146f41ee8b0c40008dd83dd161880091e90ea8ac31006f0f99175d06200062f31aeba0c4000c3d7559341880018bceab1e8310003175d563d062001c3f42eed20c400087d85dda41880051bd07bb483100023760f76906200247d406ed20c40028de835da41880018bcc6bac831000237e1973906200046fc3ac720c40008dd8758e41880018bceab1c8310003175d563906200063abacc320c4000c757558641880099b4e0b1883100033658d70106200247d406ed18c4000cd9635c231880091b907bb263100123ea03764c6200ae66392c698c4000ad48158d318805199cc7b926310002b6e19434c2200056dc32629844015bc8824c530880031f301baec8900021fe1571d912001c3e42ae3b2240038
  | 9 => 0x61104400065ab92c220880048f58798631100091b907bb262200063b20b764c44000477c12ec98880018ec825d93110037878e8b2a62200031b1c9654c4400061eb2ee89888000c9f7458d3110001998e4b1a62200023b61b724c4400063732ee49888000c6d65dc9311005199cc7b9262200033358f724c4400047743ac498880008ec8758931100019cee530a6220003391ca614c4400247a43ac29888000cb7745853110037968e8b0a622000339dc9614c44000672392c298880048f5815da2110037878e8b2c42200022f61b74884400061eb2ee910880048f587986211000196ee8b0c422006f2d1d161884400146e41eec90880048ec82dd921100091e903bb2422000237e0d76484400146e41aec908801bc3c7459521100018b8e6b2a42200030f59774484400046ec36e69088000c5e65dcd21100018bacbb9a42200b33398b73484400046f43ac690880008dc8758d211000195ee8b12422000333dcd62484400066639ac49088000cd77398521100019a8e730a42200123d21d61484400065bba2c2908801bcb47458521100019aee6b0a4220003351cd61484400063c3aeeca008000c7b85dd940100018f10bbb280200031eddb755004001c3f42ce3324600087d859c6648c0091790eaa2c918002b360f5258a300247643aa4b14600387e851c5628c0010fb0a38ac51806e2fa107158a300045ec20e2b146011ace839d5628c00159b073aac518002aba107558a3000556c20eab146000acf835d1628c0014dd0a3a2c5180029b6147458a3000717aa4a8b146000acf835c5628c0014dd0a38ac5180029b6147158a3000557420e2b146000aad841c5628c02f59d0638ac518002b360c7158a3002575400e2b146017ae9801c5628c00155d09a8ac518002ab6135158a3008d67418a2b146000acd83145628c00317908bb685180062f6137650a3020e67316e6a146011ccc73589428c0091eb0f28cc3180123d21d51586300de1f322eba0c6000c6e625d7418c00187aeab2683180031b9d562d063000636baac5a0c600387e85dda418c0010fb0bbb483180031b989759063000667312e720c6000c6e7558a418c0018daeab148318047339cd629063000666b9ac520c6000c7575986418c0018eaeab0c8318003355cd619063002675382c420c6000ce9625c0418c0091d905bb243180b33398b734863008e6639ac490c6000c3d75d53644c00153b07aa6c8980021fe1571d913001c3e42ae3b2260008dd878ca644c0070fd0b38cc8980021f616719913001c3f43eeab2260008bf845d5644c0010fd0e3aac8980030f1d774591300045fc3ac83226000a3c85590644c03717908ba8c89806f0f21175191300de1fa12ea3226000c5c325d4644c03787882ba8c89800317cc575191300de1fa02ea3226000c3d75d50644c001998
  | 10 => 0xb0880048f487545611003756908a8ac220002b5a0c51584400056ac18a2b08801bab684cc561100014ed0a18ac2200029d61431584400dd5b42642b088000a768508561100014eb0a10ac22006eada1021584400056b41842b088000ad58308561100095e50010ac22006eada1275584400055ac24eab088000ab7845d5611003756908baac220002bce01755844002578402eab088000ad6831d561100015ab063aac22006f8d95354584400dd5b424e6b088000ab5849cd611003756908b9ac220002b9e09735844000572412e6b088000a76851cd61100014eb0a39ac22000395d4e53584400055bc22a6b08801bab48454d611003756d09392c220002ad61272584400dd5a422e4b088000ad7835c961100015a906b92c2200029da1472584400053ac28e4b08801bab6841c9611000156b08392c220002b5a0c72584400056ac18e4b088004af2801c961100015e300392c220002b5a0f52584400056ac1ea4b08801bab684949611000156b09292c220012bca02525844000578c04a4b08801bab684149611000156b08292c220002ada1f42584400dd5bc0684b088055ab580d0961100015af06a12c220002b520d42584400055a43a84b088000e97835096110001d2906a12c22006fa9e0942584402a55bc0284b088054ab58050961100a9d4e40a12c220153a948142584400dd5b42464b088000ab5848c961100011ed0e192c2200023d61c32584400053b42864b088000a75850c9611003756d08192c220002ad61032584400257940064b088000af1800c961100070fd0abb4822000a37a0d769044018c3fc32eb2088000c5e635d641100018dcc4bac82200721fe1d65904400043ec3acb2088000c5e73596411006f1bf0cb9c82200031799573904400062eb2ae72088000cce625ce41100351bf0eb1c82200023761d63904400062f3aac72088000c5d7558e41100018dceab1482200031b5d562904400066739ac52088000ccd7358a41100018eceab0c82200031d5d561904400066b39ac32088000cd573586411000187ceabb4822006f2d9c576904400061f42aed2088000c3d855da411000193d06bb482200032760d76904400de5b40aed208804ecb5815da411000187aecbac82201a28fe1d65904400051ec3acb208801bc3e71596411009d87ee0b2c822013b0f5c165904402771b882cb208804ee3510596411000193aed39c8220003479d673904400070eb2ce72088000c9d765ce4110001c3acab9c82200030f59572904400071b3aac32088000e35755864110001d2ce6b0c8220003a55cd61904400065ab92c3208804ecb770586411009d96ae0b0c822013b0f9c565104400df1b38aca208801bc3f705944110037c74e0b2882201430f5c165104400df1cb82ca2088000c3d655c8411003756f0eb08822013b2de1d
  | 11 => 0x1003753d09a8ac620002a76135158c400046f438a2b1880008dd87145631003753d0990ac620002a76132158c400046f43842b1880008dd8708563100014bd0a10ac620002976142158c400dd4f42042b188000a9d8408563100095b50010ac620002b66002158c400247743ea4b108000ace83d49621000159b07a92c4200123b21d525884001c3f428e2b10800087d851c5621000317b0838ac42000a37a0c71588400046ec18e2b108000ace839d5621000159b073aac42006eaba1075588400cd56c20eab10801be2e54d5162100014dd0a39ac4200029b61473588400dd57420e6b108019aad841cd62100015cd0239ac420002b9604735884002575400e6b108019ae9801cd6210001c9ea729ac42006eab211715884000567c1ae2b108000acc835c562100014dd0a38ac4200029b61471588400dd57420e2b108019aad841c5621000159d0638ac420002b360c715884002575400e2b108019ae9801c5621003755d09a8ac420002ab613515884000567418a2b108000acd83145621003755d0998ac420002ab61331588400053742862b108000a6d850c562100a987ae4b2e842006f0fdc165d08402ae1eb82cba1080008bd869c7421000187acb38e8420003171cd65508401dc6ec36e6a108000c5e65dcd42100018bacbb9a84201073398b73508400046f43ac6a10801a8dc8758d421003787ee4b2a842006f8bdc965508402a61fb82caa108054c3d7059542100a9c5e40b2a84201538b48165508400070eb2ee6a108041e8e62dcd4210001c3aca39a842023fa398873508400054f43ac6a108000a9c8758d4210037d1ee4b1a8420153a3c8163508402a746902c6a108000c3d651c542100091b90eb1a64200123b21d624c84000477c12e730880018ec825ce61100011bf06b94c22000a3720d72984400dd5b426a330880048f58794661100091eb0e28cc220002b5a0c51984400056ac18a33088000a76850c661100014eb0a18cc2200029da1421984400053ac28433088000ad68308661100015ab0610cc22006eada1275984400055ac24eb3088000ad6831d661100015ab063acc22006f8d953549844000573c12e73088000ae4825ce61100014ed0a39cc2200029d61473984400072ba9ca73088000ad7835ca61100015a906b94c2200029da1472984400053ac28e5308801bab6841ca611000156b08394c220002b5a0c72984400056ac18e53088004af2801ca61100015e300394c220002b5a0f52984400056ac1ea5308801bab68414a611000156b08294c220002b5e0d42984400056a41a8530880008f6870ca61100011eb0e194c2200029da1432984400053ac2865308801bab6840ca611000156b08194c220012bca00329844000578c00653088000ab681d09611000156902a12c2200123da1f51584400dd5b426a2
  | 12 => 0x28b0f5d065185400047bc3ac230a8003c3e7595061500011bf06b90c2a000a3720d72185400056ac184230a800387c859db41500650f90cbae82a00021fe1f65d05401043ec3ecba0a8000c3c659db415000187ceb3b682a00030fe1676d05400061e42ceda0a8000c3e765d741500d92790cbae82a006f0fd8175d05400de9db02eba0a800093f87d97415000187cedb2e82a00030f5d762d05400061eba8c3a0a80a287c865d641500010fb0fb2c82a0003179cf65905400062fb2ae720a8000c5c655ce41500019aae7b0c82a0003355cc61905400063c32ee0a0a8070c3c76d954150001c6eca30a82a00038dd9541105400043fc2aed18a800387c855da315000127b0b3a462a00030f196748c5400061e32ae918a80028f58718631500070fd0bbb262a00021f617764c54000c77414ec98a80008ed829d931500018d8e5b2a62a0003331cb634c54000637b2ee498a8000c6c65dc931500051ed0fb0a62a0003391cb614c54000672390c298a800087f855da21500070f90abb442a00022fa1a74885400049ec2ce910a800387e85dd921500010fb0bbb242a000a37a0e76485400046ec1cec90a8000c5c73d9521500018becbb9a42a00031719773485403863d3b6cba028070e3b64d9740500018bee739aca202868fe1173594400dd1e422e6b288000a5e83dc965100014bb07b92ca2006e8fa1272594405051ec24e4b288004a7a809c9651013f4f301392ca2006e8fa1072594400e51ec20e4b28801ba3e848c9651000147b09192ca200021fa1c32594400043ec3864b28801ba3e840c9651000147b08192ca200029da0432594400053ac0864b288004a7a800c965100014f300192ca2006e8fa1371594400e51ec26e2b28809ea3f845c5651003747908b8aca202769ee0171594400253c402e2b288000a5e831c565100014bb0638aca2006e8fa1331594400051ec2662b28800087e870c565100010fb0e18aca2006e8fa1321594400051ec2642b28800087e8708565100010fb0e10aca2006e8fa1021594400051ec2042b288000a5e8308565100014bb0610aca200129ea0021594400053cc0042b2880048de87d4d63100018beeba9ac6200123721d5358c400dd4f42464b18800387e851c563100010fb0a38ac62000317dd67558c400054fc22eab18801ba9c845d56310037c3ca9aa2c62006ea7a127258c400054ec24e4b188000a5e851c963100014bb0a392c62006ea7a107258c400d54ec20e4b188000ad6811c963100015ab02392c620012b6a007258c400d56cc00e4b1880008de87d4963100011bb0fa92c62006ea7a125258c400054ec24a4b188004ada8094963100015b301292c62006ea7a105258c400054ec20a4b18801ba9c845c5631000159f04b8ac620002b32097158c400052f428e2b188000a5d851c563
  | 13 => 0x61ebacc3a0e800093d85dd941d000156902b1283a000e1fa17768c7400043ec2eed18e80008ef825d931d00031d904bb263a000e1fa1776887400043ec2eed10e80028de83dda21d00011bb07bb443a000237e0d76487400146e41aec90e80048dc8754d63900070fd0a38ac7200021f6147158e400247643aa4b14800387e851c562900010fb0a38ac52000a37a0c7158a400046ec18e2b148000ccc73589429008393eedb9a852023f27dd87350a400045ec30e2a14800387e85dd932900010fb0bbb265200023be09739864000c76412e730c80008df835ca61900051b906b94c3200123d61e519864001c3f43eeab0c8051c3f40dd561900a387a81baac3200030fdd742586400061fbaa84b0c8003c747594561900091e90ea8ac3201bf0f59175d06400063abacc320c8000c75755864190001a3ceb39c83200028fe1561906400069cbaae120c8000a3f855d8419000147f0ab0883200021fe15768c64001c3e42aed18c800087f855d931900070f90abb263200023be09764c64000c76412ec98c8000ccc7258d31900015a902b1a63200021fe15768864001c3e42aed10c800087f855d921900070f90abb2432000237e0d76486400146e41aec90c8000ccc7358921900014ed0331ecaa00029d60663d95400062eb98e7b2a800087e8710f65500410fb0e21ecaa00828fa1272d95400051ec24e5b2a8000a5f835cb65500014b906b96caa00021fa1c42d95401043ec3885b2a800087e870cb65500010fb0e196caa00028fa1032d95400051ec2065b2a8000a76810cb65500014eb02196caa01c29ea0032d95400053cc0065b2a8000a5e839c765500014bb0738ecaa00028fe1171d95401051e422e3b2a806ca3e841c765500e147b0838ecaa00021fa1c31d95400043ec3863b2a800087e8708765500010fb0e10ecaa00028fa1021d95400051ec2043b2a8000a5e8308765500014bb0610ecaa01c29ea0021d95400053cc0043b2a8065a3e84dc365500010fd0f986caa00021f61f30d95400043f43e41b2a800087d87c83655000147d09906caa00028f61320d954001c3f42ce3b1a800087d859c763500010fd0fb2ac6a00021fa1c6558d4001c3f42ce3b12800087d859c7625000317d0938ec4a000a37a0e71d89400046ec1ce3b12800087e87d9562500018b8e7b2ac4a00021fa1c65589400062e398cab128000c5f65dcd62500018b8cbb9ac4a00031dd9771589400063a32ee2b128000c77651c562500018e8ca38ac4a0003171cf65509400062fb2ee6a128000c5c65dcd42500070fd0bbb264a00021f617764c9400055ac2043b0a8000ad58308761500015e30010ec2a0003179cf65985400062f398cb30a8000c5f655ce61500018b8cab9cc2a0003355cf619854001c3f436eab0a800087e87d9561500010fd0e32ac2a0
  | 14 => 0xd859db43884371df0cb96871080e1fa167650e210043ec2ceca1c42008dd839d94388437878c8bae83108030f5d764d06210051ec2cc920c4281ab681d91418840117d0e32283108022fe1d6410621144e641ae420c422cbc4835ca31884031bd0fb1a63108b3331cb634c621166e2396e698c42019d687d8d318840178b05b1a63108b3711cb634c6210056b4368698c4200bc582d0d3188483b88e5a1a631080e1fa1f75582210045fc22eab04421b8bc845d5608840187eebba2c1108030f1d774582210061fba8e8b044200c3c751d1608843795d043a2c11086f2b60874582210de5b408e8b04421bcb5811d160884011f70eb00c11080e2fe1d54d91210de1e322eb3224200c3d75d9264484011bf06baac89080a3720d75591210047dc02eab2242048f8805d564484051bd0fb9ac890803331cf72591210045fc3ac8322420087f855c064484070f90ab80c890803175d753d8d2101c6fc3aa7b1a420087f855c363484070f90ab86c690802a7a1265d8d210054ec24cbb1a4200a5e8599363484014bb0b326c690803175d475d8d210052f42ce9b1a4200a5d859d36348401c3ea92a6c690802a7a1351d8d210054ec26a3b1a42008de87147634844d1bb0e28ec69080297e1570d8d210052e42ae1b1a4200acd821c363484011bd0e286c6908023761c50d8d210054f420a1b1a4200a9d84143634845959d04286c690802b360850d8d210056b408a1b1a4200ad58114363484011bf06baac6908023be097558d210046ec3cca31a4200a9e84994634840153b09328c690802b360a6518d210046fc3aca31a4200acf8259463484011bb0f320c69080297a166418d210052ec2cc831a42008df8759063484011bf06bb286908023be097650d210dc6f43ec6a1a421bc3c645d741484018b8c6bae82908030f5d764d05210062f3aec7a0a4200c5d75d8f4148401998c6b9682908031718d7590521006b210aeb20a42378dc865ce41484011bf0fb1c829089a3761f63905210062f3aec720a4200c5d75d8e4148401998c7b9282908b3331cb634c5211466631ee498a4202cd476dcd3148459b88e5b9a62908b3351db634c5210056b4368698a4202cd476d0d31484559c8edb9262909eab3a1b63885211476231c6310a4201ae4864c62148451d88c698c42908033318d70885211646e436e6b0242008de87d8d60484018beebb1ac090803171d763581210064fba6c6b024200c9c74d8d60484011bd0e31ac09080317dd463581210062e3a8c6b024200c9f7418d6048401938e831ac0909eb339c863181210047dc3ac030242008df835d562d00051b906baac5a000a37a1f7358b400146f41eeb30e80008dd83dd661d000787ceb2a4c3a0003179d673987400062ebace730e8000c5e755ce61d00018baeab9cc3a00030f5d562d074000
  | 15 => 0xb326c498a6f339d953d893120e673b687b126200bc681d0f624c40155d093aec498802ab61275d893114567418ebb126200acd831d7624c40159b07ba6c4988029ba1674d893100536c2ce9b126200e2f54953624c40155d09a8ec498802ab61351d893114567418a3b126200acd83147624c4014df0ab86c4988029b21570d893100557c22e1b126200aac845c3624c40159b06386c4988023ba1c50d893100476c38a1b126200aae84143624c40155b08286c4988a2b3a0c50d893100566c18a1b126200ae681143624c4015cb02286c4988023b61e651893100557424ca3126200aad84994624c40159b07328c4988023be1d651893100567c1aca31262a3ace83194624c4011db0f320c4988029ba16641893100536c2cc831262008ef87590624c51f59906320c498802b3a19531893100566432a63126200e4f6554c624c401d18c9a18c498802f1a07431893100c5f424eda126201aac82593424c483d18c5a1e84988028f616645093100d57414c8a1262018bc87591424c483998c5b9a849880275a0773509310064e3b686a126241e8c62d0d424c451998e7b12849880237a1a744c93120e66314e899262009d6819d1324c4012bb0a3a26498a3f33188744c93100d67436c4992622accc76d89324c4511bd0c38a649880257614714c9313d666310e2992627ddc7721c5324c4012bb0bb82649897b3318b704c9310de1e322eba0a6200c6c625d7414c40187aebb2682988033318973d0531006373aec5a0a6200c6d75d8b414c4018d8c4bac8298803550c5759053100666312e720a6200c6e75d8a414c4018daebb1482988a3339cf629053100666b9ec520a6200ccc62dcd414c503d48c4a08829880257616748c53100666314e918a62378de861d2314c401998c43a462988de75a04748c5310146e432e518a622cccc625ca314c45959d0db14629880257e15708c53100666312e118a6203c5e7554f604c4551d90db92c0988023ba1f625813100637baec4b026200c6c75d89604c40195ee9b12c0988032b1d3625813100477438c4b026200c6f75189604c4018d8ea312c0988032bdd06258131006563a0c4b02625ecce73188604c4011f70eb00c09880a37a0f75d92210046ec1eebb24420087d879d764884070ff0ebaec91080f0f9d654d922101c5fc3aa9b244200c5e759cf64884018baeb39ec91080a37e1d73d92210062f3aae7b244200c5d755cf64884018eaeb38ec91086f0f19175992210061ebaec9324421bc3f425d6648840187a84bacc91086f0f10575992210de1fa02eb32442008fb805d564884091f100baac910a06ada0774592210045fc3ac8324420087f855c064884070f90ab80c91086e2fa1375d8e210045ec26ebb1c420087f855c363884070f90ab86c71080e3721d5358e2101c3f42ceda1c420087
  | 16 => 0x1509410045f436e0a12820387e851d932504010fb0a3b264a086f4d10575d054140cdbc3a85a0a821bdb3405c34150401a3ceb39c82a093a2f21970905412765c302e120a82008ef825cf60504031d904b9ec0a080237e0d72d81410146e41ae5b028200ab98414360504015e302286c0a093b0fd9175181410047dc3ac03028200a788558060504371b90ea9ac62080237e0d75588410146e41aeab1082028de87dcd62104371d90ea92c4208038b551525884100c5ec26e0b1082018dc8758d32104051d90eb126420a2f0f98575d04410de9b30aeba088200c3d7558b41104638eaecbac8220803555d5739044101c3f42eeca08820087d85dd9411040127b0bbb282208030fa1776504410061ec2eeca088200cb651dd9411040196aa3bb28220a93a908562504410063b42eeca088200c7585dd9411043796ca9bb282208032d55376504410059ac2ee8a088200b9583dd14110407878eb2a2c0209422f21d54580412845f43e82b008200a3d85d0560104a157501a0ac02086fac10241580412845e43a82b008250ab8805056010437d6680a0ac02080f1e1d650580410071d2a4a0b00821b8f8875416010401c72a8a82c0208021f61e75d923101c3fc3aebb246200c5e755cf648c4018baeab9ec9188028fa1764992310dc5e422eb324621bc3c845d6648c43787e84bacc918803170c975992310de1e20aeb3246200c5f315d6648c43787e80bacc9188030f5d7549923100666192e53246200c5d758ca648c40147d0bba2c9188022fa1f54592310061fbaea8b246200ab681d51648c40117f0eb20c9188021fe15701923101c3e42ae0324620387e859db428c4010fb0b3b685188062fa1276d0a310de4f322e7a146200a3d85991428c4031790eb228518803279937350a310051ec2cc920c6200c3e75992418c40187ceab2483188032799173906310de4f322e620c620387e87dd5608c4018b865baac11880317cc775582310062fbac64b046204cea605c8608c4011f70eb00c1188033a5c960182310046ec1eebb2262038bf87553644c437878c8bacc8988030f5d764991310de1fa12eb32262008ef825d5644c4031d904baac8988023ee0175591310247c402eab2262018ee87dc9644c40199ee6392c8988022fe1d64191310046fc1ae4322620087f855c0644c4070f90ab80c8988d23761f64d0d3120d66412c9a1a62008dc865cb434c483998c4b9686988be37a1a71d0d31004aec2ce3a1a6200ccc629c7434c45f3ad0d38e869880335a1a71d0d31006ab42ce3a1a6200d55859c7434c4013ab0538e869880257e1570d0d3100666312e1a1a6200acd83d4b624c4071df0ea96c4988021fe1570d893101c3e42ae1b1262008bf845c3624c43717908b86c498802aba1265d893100556c24cbb126200a6e85993624c4014db0
  | 17 => 0x1c8200a9d84d456390401caea328ac72080237a1c5158e410046ec38a2b1c8200a5e8590563904014bb0b20ac72080237a1c2158e410052f42842b1c8200a5d85085639040153d0810ac720802a76102158e410056d40042b1c8200ad98008563904014bd0bb82c720802976177058e4100567414e0b1c8200acd829c163904015ad03382c720802a7e117058e410046f438a0b1c82008dd87141639040153d08282c720802a76105058e4100567410a0b1c8200acd8214163904015ad02282c720802b56045058e410052f42e40b1c8200a5d85c81639040153d09902c720802a76132058e410056b40840b1c8200ad58108163904019aac7b8a87208021f61e65d8a410062f39ccbb14820087f8759762904018bce6b2ec5208031799573d8a410062eb2ae7b1482008dd8798f62904018bceb31ec520803175d663d8a410046fc3ac7b148200c5e7558f62904018baeab1ec52080e1fa177058a410043ec2ee0b148200c5c7359542904011bb0db9a8520803179977350a410062eb2ee6a1482418de8758d429051f1b90eb1a85208031d5977150a410063ab28e2a14820387e851d932904010fb0a3b265208063721d634ca4100d66412c6994823287f865d741904018bcc6bae83208c61fe1d65d06410062f3aac7a0c8200c5d7558f419040187ccabb683208030f9d576d06410061ebb2eba0c828693f865d7419043787cc2bae83208024f61d65d06410061ebb2cba0c8200c9d7698f4190401a3aeb31e83208038799663d06410064ebb2c7a0c8200d1d7558f419040187aeab1683208031d99576d06410063abb2cba0c8200cd57698f41904019aaecb1e83208039559563d06410062f39ccbb048200c5e7359760904018bccab9ec1208031759573d82410062f3acc7b048200c5d7598f60904018bceab1ec120803175d563d82412745f43ca8b048203c3c7595160904051bd07b92c1208023760f72582412745f43e82b048200a3d85d05609049d57501a0ac12080e1fe1975182410043ec3cca3048200c5e7399460904018dce5328c1208021fe1d65182410062f39aca3048200c6e7259460904018bccab98c1208031759573182410046ec3cc63048200c5e7598c60904018baeb318c120803339ca63182410046fc3ac63048200c5e7558c60904018baeab18c120803339c963182410063732ae43048200c6d655c8609040199cc6b90c1208033358d721824102675302e430482008fb8758060904019d2e4b00c1208021fe1570d8d4101c3e42ae1b1a820087f855c362504070f90ab86c4a08062f21170d89412ac5e432e1a128200ccc73d894250483938edb9a84a0a3f271d87350941006cbb98e2a128200d94731c5425040136d0c38a84a08032da1871509410065bb28e2a128200cb5651c5425040136b0038a84a08032d1807
  | 18 => 0x4018b8e6b2a85a0803179977350b410062eb2ee6a168200c3f7659542d043787ee4b2a85a086f8bdc96550b4100717902caa168200e1d65dcd42d0401c3aca39a85a08030f5947150b412a45ec36e0a168200c3d65dc142d043787ce932cc1a086f8ed0165983410df1da02cab0682018ee82dcd60d04011db05b9ac1a080a37a0f72583410046ec1ee4b068231a3f865d1659040167100ba2cb2080297a0c62596410052ec18c4b2c8200a7a8018965904014f300312cb20a1a9de0574596410053dc02e8b2c8200a78805d165904018bee739acb208029da0643596410053ac0c86b2c823187e8710d65904010fb0e21acb2080297a0f72596410052ec1ee4b2c8231a3e841c9659040147b08392cb208c61fa1c42596410043ec3884b2c820087e870c965904010fb0e192cb208028fa1032596410051ec2064b2c8200a76810c965904014eb02192cb208029ea0032596410053cc0064b2c8286a3e849c565904010fd0e18acb208021f61c31596410043f43842b2c820087d87085659040147d0810acb208028f61021596410052f41842b2c8200a5d8308565904014f50010acb208029e60021596410053b40ce0b2c824fa75819c1659040147f08b82cb209a28f211705964118d1f420e0b2c8200a3d841c165904014bd06382cb208029760c705964100537410e0b2c8200a6d821c165904014ed02382cb208c69d60470596410043f43e60b2c820087d87cc165904014ed02182cb208029d60430596410043f43e40b2c820087d87c81659040147d09902cb208028f61320596410053b40840b2c8200a758108165904018bcc6baec7208021f61e65d8e410043fc3acbb1c8200a9d84d966390401c3b0932cc720802a761a5498e410070f32ca931c8200a9f865526390401c3ccaaa4c72080297a146298e410052ec28c531c8200a9d8418a63904015b500314c720802b66006298e410062fbaea6b1c8200a9d84d4d63904071b90ea9ac72080e1fa177058e410043ec2ee0b1c82008de87d9563904018beed32ac720803876126558e410062fbb2cab1c82008de871956390401c3ccb2a2c72080297a146258e410052ec28c4b1c8200ada8018963904015b300312c72080317dd67558e410054f424eab1c8200a9d849d5639040159d053aac720802b360a7558e4100567c12e8b1c8200acc825d163904015ad03aa2c720802b56075458e410070faa4a8b1c8200a5e851c963904014bb0a392c7208dea7a107258e410054ec20e4b1c8200ccd721c963904015ad02392c7208deb56047258e410056d400e4b1c8200ad9801c963904011bd0fa92c7208023761f5258e410054f420a4b1c8200a9d8414963904015ad03212c720802b56064258e410052f42884b1c8200a5d8510963904014bd0a38ac720802976147158e410054f426a2b
  | 19 => 0xe3de1d51d85420062f3aec730a8400c5d75d8e61508018bcea31cc2a1003175d463985420063abaec330a84008de87d8d61508011bd0e31ac2a10023de1d611854200c5ec26ea30a84008bd87950615080787ceb2a0c2a1002ad606541854201c7ac3ca230a8400ab5849446150801c6aa9288c2a10038d95151185420043fc2ae030a840387c855c0615080317b09baec0a11522f61e54d814201e1f3aca9b02840387e859c760508010fb0b38ec0a100a37a0e71d81420046ec1ce3b0284418dc86dcd60508011bd0fb1ac0a100317dd763581420062e3aec6b0284008de8718d60508018beea31ac0a1003171d463581420066bb1ee2b028400cd463dc560508019aec638ac0a10033518c715814247e67390c630284008fb8758060508070fd0b38cc8990021f61671991320043fc2ae1322640387c855c2644c8011bf06baac8990022fe1d641913255d4fc1ac8322641bc3f425d4644c80187a84ba8c899003178c975191320062e192ea3226400c5f315d4644c8011ef0eb08c2992aab5e0d611853254d73c12c230a64018dd83dd4614c8010fb0f3a8c299003175ce751853201c3fc3aea30a6400c5d735d4614c8018bc64ba8c299003170c975185320062f98aea30a640087d879d7604c8070ff0ebaec099003178c975d81320062e192ebb026400c5f315d7604c9519b2e7b04c09929f3a5cb60981320047dc3ac0302641be2f4298965d04018bee739acba0a9a8fe1173597410dd1e422e6b2e8200a5e83dc965d04014bb07b92cba086e8fa12725974152d1ec24e4b2e8200a7a809c965d04014f301392cba086e8fa1072597411951ec20e4b2e821ba3e848c965d040147b09192cba08021fa1c32597410043ec3864b2e821ba3e840c965d040147b08192cba08029da0432597410053ac0864b2e8200a7a800c965d04014f300192cba0a2e8fe1171597410053dc02e2b2e8200a78805c565d043747d0998acba08028f61331597411943f43862b2e820087d870c565d043747d0990acba08028f61321597411943f43842b2e820087d8708565d043747d0810acba08028f61021597410052f41842b2e8200a5d8308565d04014f50010acba08029e60021597410dd1f424e0b2e826fa3d849c165d043747d08382cba08ca8f61070597410052f418e0b2e8200a5d831c165d04014dd04382cba08029b60870597411953b408e0b2e8200a75811c165d04010fd0f982cba08021f61f30597410dd1f42060b2e8200a3d840c165d04010fd0f902cba08021f61f20597410dd1f42640b2e8200a3d84c8165d043747d08102cba08028f610205974101c3f42ee0b1e820087d85dc163d0437c3886b2a87a086f8bd096558b4101c3f42ee0b16820087d85dc162d054b87ae4b2e85a08030f59671d0b410045fc32e1a168200c3d655c342d
  | 20 => 0x2008001000000200000000000080010068004018000000802c0000020070000004001007800000000200000040040040020020024000001000400a003000001801c001000000c002001001000c00c002000000000c005001800800000000180100040020008000004000001000400000200000240060020008004002009000800000000000480000000000018008002000000800001801300000000020040000000000002001800400200000680000060080020008000000000000801000100000140000060000018000000000001c004009009801c00400100280200000000030000004007004802800c000000800800200e0010000006006000000000000000000080080010000008006002001001c0060040010008000000001001c0000000000008014000002002000a0070028004006005001800000400500606e3b21d5258b4301c3fc3aeb30e8600c5c325d661d0c018be62bacc3a18023761e32987430062ebac6530e860387e87dd560d0c018b865baac1a180317cc775583430062fbac64b06860387e859c76250c010fb0b38ec4a18021fe1570d894301c3e42ae1b1286008f7875846150c010ff0ab80c2a180e1f215701854301c3f42ce3b02860087d859c76050c011f70eb00c0a186e3721d5358f4200c5f426eb30e84028de83dd661d08011bb07bacc3a10030f9d2759874201c3fc3aeb30e8400c3e745d661d080787ceb2a4c3a10022fe1d54987420062f3ace730e8400c5d759ce61d080193ce939cc3a100a37e1d73987420062f3aae730e8400c5d755ce61d080193ce8b9cc3a100333e09739874200666412e730e8400cd6215ce61d08019aa42b9cc3a100e1fa1f75583420061e3a6eab0684018bc845d560d0801878e83aac1a100f0f1d654583422ac5e43aa8b068400c5d75d4f635080153b09a9ec6a1002b360b53d8d4201c6fc3aa7b1a840387e859c763508010fb0b38ec6a10021fe1570d8d4201c3e42ae1b1a8400ad68199763508015ab0332ec6a1106a721954d8d420062eba8ebb1a8400a9e841d7635088353b083aec6a1106b3a0875d8d4200566c10ebb1a8400e1f54953635080159b05b8ec6a100297a1671d8d420052ec2ce3b1a8400cd7719c7635088353b0838ec6a1002a7a1351d8d420054ec26a3b1a84008de8714763508011bb0e28ec6a1106a761370d8d420052fc2ae1b1a8400a5c855c3635080159b04386c6a100237a1c50d8d420046ec38a1b1a8400a9e84143635080153b08286c6a1106b3a0850d8d4200566c10a1b1a8400ad68114363508015ab02286c6a10023761e6518d420056b40cca31a8400ad58199463508011bf0eb28c6a123ea72195418d420070e32aa831a8441ccc72d8d4350805938edb9a86a1107631cb7350d4220e4e3b6c6a1a84019ac845c34250837b5080b8684a10
  | 21 => 0x200140140020028020000000002803c0000010008004010000001000001e00000000000040000018000006000000000000000d001002000c000000801c002003008800000800000700140000110020000000003000002800000700000040020000000004008000000000000400000080140040000000040000000000800400800400080000020010008014000001000803800400000000040000060010018000005000806c002008000001401400100000000000030000000004002000000402400000080080000000048004000000001000001600c001001400000200000000040010008008000000001803801a00b00380000020010030000006003001800800000400380040040000028000002000003000c012004000000000000f0050004008000000004c0000000028004024001000000000a00100080080000050000000008000000000c00000100000000000050008004006000000000400000100200080020030000040000006000001400400300000180000060038008004002001000c0000040000018000002000802c0000030008004006000001000800c004002001800000000380000060020000004002006001800001e001000000c00400900000400040040000000004003004000001200300980000000000000000022006000000401200a002000000200000080100160030000008006000000800000200200b000000400000280000060000010000002004005801800c0010008010004007000800000400000000180000020008008000001000001000400d0008004000006001800000a0000040020000000001800c00400100e80000040000068004010005004800000a000000001000400000300400040020000000002000015800000c00000000140020040018000002005001800c02a00000000140000020000008014002006000002c0070008000004000005000400200000000080000030050030002001005001800a007000800400200300000040180000008000000001000000000600100a8000000002001801800c00100000340000050008004000000000801c0000000030000006005000800c00c0020008018004002000800c00e0000008004002000008000c00001500000000000040010048000003000800c000000001000000a000008800000400000080000000040088000004004000002c00000100180040020060020018000001000802c002000000000401400100100000140010030004002002000002000a0060008014000000000000400a0000040000000000000000000400400080040000010000008004010008000400000100080040020030000004004002000800000000100080000000070000008000003001800400800400380040040000008018000000000800c0020030040000016006000000000
  | 22 => 0x20c8a85600000000003e901980000007f035eac4c8f47ae000000000043e0001378d142f200017cc000218000000076e0000770000e7218335c0f6879665800004bc0000000ed13f8000315011072400028a560924c0009fb00013540000000000000ad84a40001900a8a0a00cd80000000c21b790f0000000000105c00000000000ad1f200000000011160004bb20cd0de67f1dea4b123200000000003420003fa029c91800027480014b41c10000000cae00005d93900008dd49a000153c000111000000049900000004b443440a00003f600000029fc51000003e000000032b0001de00007ba04f85cd510000000135000000000020b8a246e84229ee0000445146000004200054d8b70000000000053000020f00000000008c24940000d2c00017d8000fa40f200016e449289500f800000000014b0428e065f7217000000042000010140680001f9000162c39f00000005322290ca15680002d64be2344702000000000142471300018148ca67349316140009092a38b7853e0002ee1c0814a57300000002a40004d2a60d0ea00000023f14d41d500000000000004590a380009e648e19e8dd400039f0000000a7d08989ec6ba00000007e0000b2c00028bcaa026e172000100685c0002a4081e8dc00022000000000000000e4a82606ba9f0a2a0001dd00000000001eb21cc00021400000013dc6db00000000005380000060f1800000000000008fd3b600000000000002194abc32400001b40003b80000000c885c638020dd4020ca0001d7832ea2200026985a8a0a43fa10c02e150000000034a2982e79ff400000012b800075c3c0482a9243da64b0000000cc66e71ac915d57044d0648fd46e225453380340ce742000228035a5a200017354cc00042bac7546200052190009109441180cb435e0f70530a80ae43fa51b8b44ee80160000000ff85fe0000744000000000000008a9a90000f7164c2c306aa2d4000000000000099e00000003c4000a733ee2bd80000004fb0000eba00021800011c60001eb84252dc0001652950cc48794fd00640007dd4b6ab60f7e4ba4c40000a40690000000074411c1ba9adce1614047108f929a9dc0000a985fa7df05591ed3b600000000000000000000004005002000400000000000000080040030008006004000000400c002000000000000000000000020000000004000003001800400c00100180740000010000030000003000800800000d0048000006003000002c000000005000401a0080008008006007001800802e005000800c00600b0000004000000000002800400100100240000070010000004001000800000c00400300000000000008010004000000000000800100080180060000010034002001001000c00c00a0000010000002000800c00400d0030034006004000000c00400200
  | 23 => 0x20000000ea44c85709a74f6c0000000f0c00091300000000007d10002480000000000000000000000000000003ef0001555354a131ee86201420003518a0400039d1c3251400054b02a09040000000d300012e804e00026ad2fe285000000000000012e150145601a26d8000ccc5db4df0fb400044f0bf04d80009390001f084789ad2cda65ccba00000015c13689d20001894d2a9bc1e41de816e6190000d6c0a29ea01f2c88c9825f2be00010622df38c023cbb283422b00005622ab00008a80c29a70db00000000000000000b24115000250c00000000017c80000003f50000c825d600013b00004771c983780004eb1df80005f800000200001fe43d16485880004a201eaaecb5a00026489943d26d73ada44800000000000000000000000afd41e000000000100262d000000000089746300008c8b19000205c0d40e22e82bcc67c45b1ea0a4d3722ff40d02e08fe2790001e3400000000019dcd0658600000000007e300000005980004b01f40b286df56813fc0009d60631c98d7471c1c2948c13836800000000008b9000058d38c0000001e713d600000000240000002bf9d500000000001e489240004e29d840000000001c7d60ea7a38a86646240001e6157c0000ae2d722e0aba5523db80000000000001bd0b886942b5a01840a34e1d581a472e156303a8642080004d01fcc000a2e57ca55c0001b81f59a8800000000100011de9ca158196ce0e2d2542a34c8520000000000a02a0c3438000a7e1ac087a5414826f20b59010c6213545300000000000000840cf80001198000000aa32e89a78ee492339482504a47a5000000000031f000090cd5843630b8000b6200000000000b60001718000dba000554800000063e0000000300000000036400049156b80001fcadc18c80000d000000027391a03af191800000000000006f506a00056317ec714ac20000000b9cb3755000004d22a9046800154c6840002ce00e6b110000000114aab40e25682f2000433000000000025e000119e00057200010a29710000000b982cf0fb00000000002c40c5cf788551620000c163ac0e209800000000001ce8760768000000000000024380006e40000000104000000329000000012a0000000e1e7c3409000029e00000000011bc8085562751074238578197d3f298c0f2000000017807c1e8d4c21bf0d428b000000000000000006ad000000081c0000caa9b40000000000000c5c7b43c2a11c00000000014c07282af00000001e60004b992a540c0000000000c2a4260f712bc0005e80002c7000089948426f51665660b41a6878a96f0000000b3441d00000000006d91cc00000004380000dd95880004e39300e087bb000091843a02d1bea954a4274f4f800014484850000e0061a3f10000b1514a9031e8800000023658c00000000000a714
  | 24 => 0x5a40f450d44d000000000024d0000000ae30000000eee339000000000000015200000004e30000c2d0c476b000000023e0001168d4949aa281b587e41f671b4a42840a5624700003ac00052a000171ce42ad4000000008696642f8120e5059130d0e1d17e000000000110298000000005425614aa87f0000000000000071c64e3148a48000a89223897530aa7b4ff00010a064200000000000a331d95e90305bf5638de400099855a00000001a333800002ca0004c5a0652201eb297162860600007c80000000000000000886049000000000000039a80008506e42a210050c20972729cb0a8238918786f06887484db94b066018c0da1b8c7f6000000000000087b000018914441933a96a87508680e7015423419e00012014780002530000c10025330000100e5d7000000000091100000000000002f31f9c00000022980000002ae1e9800000000000000000000002938000f940522ab0000e2e00027a00005500002200f242ec0d200010ccc506202d42434ca2242362a4e15fa00000022dc498000363ac68000846350800000056d000138542a234000000097c00000000000004740a6800000000001f800036037b323800000000052b00000000004ef800038e3c24fe27354deac800000000000000f600000003a93108000d5e2090000f8c000000117a8940009a10001b20d800000c200004080000001b981b805e000000000000000000000008ab000264400017400000000001432791e5c196b3119f800000063400022455fe0002caa58844a4bd0f2908d41c3b2000269096c7104e824285725e400000013e22c716eab6cc7284a275000000000000000000008a91b2000000000000000000001f000000010221cc1c58000ecc00000022300000000000000000b06000107c3624892a19bbd4346b208a15a000080925980007cc3950000000000000000007820400043000000000000001444000000427a058f302e70f10a18cac10b101870c000a6e42905b0b0675f01200011e28da5000a3443646b281274d2166123a3214d4c001340e87f4c3857e52880004aa0000000b2c0182ba000288400034800011700f200036d24908b200000017b000079b29680004c62ad45f1a08e180004550258000a64000000000083f0001bf400000048fa8442b84ee000000000068f1d8846c0008873b81138c20000474929400004d0001dcc000a913be989052a69b163000037c5101970000e9600000023cc00048623724d8fea6ed1bfa8e151e49f50689352f00004ae91249582b52c4a1200981581c1924126466f29e2b3481808b3e98000ac4413493a32c00007819325a0eea21a00014f50d455836900003e86023550000c1e000416a2e8b82611577221926088350f96e89b00002dc00010f46ce05e1e10ba862b0000584000ae954300000962
  | 25 => 0x2afc0000000002c345d234c000000000000000004049421c60000000cce52600000005aa7f61f980000003b955ca1b0e247c115f218cbe02c000024dc0006d117c0000000000000044491e00026ea084776b1235f80015be0e41e91bd48540002c680000000000c309114ea00000000002880754f01c7905e00000000005c4000000000000054227b044844c2353f213485eca040c781705584ce0958000000000000000166c00030b160915a51b37d00008ce00000025795c425000000c800000000000000006bc549000000092d59224bc0003ea00000011b200056798390e063641e800000000000000002ba0003f12b94ffe6e01de03e862803020800000003020002320000aa400003d01501412f181d0928a162cb2274ab264d0000000000000301833913c8301421178000000000000086a0000000000e467650000000f260002ea800143a00014800006f833d303194c2920002d9000005e347000233123a00004815ed124ad240a8d4c0004984e483b43040001b980007c43f4098a91000089019a8000e8a00000000000000000908000d3e0004af92fc000918003889030a0000000c14000000221147400000000000000003222cc135827e0002c011d55bc0002cf18bd5d60000000fc0f2c0002fa00012ee0000000e902f487d44c1fb80000000000000dfe8a1071839944cacc00027d4f527b94f28440cf20004dd8e1165c8f75928a0961061b02c094d4a02cd2848e94000b1454080015ea000000154c4240004ae28d0a9a00000000000000000000000000000000000000000b346800000000000880000004c50001d9d3b032f01d1308000000000000047e0000000ccc5d64df018969400000036691d88228580000000f928ac00025eca26000000000000000010b2a5000065a00000008f800000000000002e0007800000063500024cc0008363e000000000004ef187800025600000014b200000017a53641550001468f540002a500000000000000000000000000045800000000000000000f641400005c20004b183680000b100000000000000000000000134287868099600016c8a5c05c4b5000000089448b000000000046d00021a40fc33709e000001c00008b8ffc000000467162c4fa72a4d80da40000002940734b6c4060000bc04f83f90000000000374000000143c0004820000000000000000021000007e80012944d9000000000000000025010464610000660000afc42621f00ae1051bc1281518000000216800003b37c0998bc29704ab246c4644bb43206c8000153204120c4ce00029108f4e6e00000000011a44f300000013e400042104e00007f1000000000000334b8000000524000187563ca6807614303b07a1519000026400036a956d34429d3538d2853495b2bc27cc0de9531fb0800fbc0000002
  | 26 => 0xd154b027f3c890e40000ac000137111c00000000009cc0001ef0000e62aef000000000000000000000000000000000e9450e00028d4000ae61f70b9800000000010ece8842c0daa3c046294f24a9dfc830709074239c00000051187bc00000017780000000000000098000a470000c395380402f3800164200050480005228c50eea2200003b442214006689173541f8051e67117997f000000029b00015e49583e211a47042765039a8041000000024f07d000006e96ec000000000266c6186640000000e32ae000000001c23a73b780b04e828b36f27755e214a32c85dc42e27e4751c50000af406001fc0000003ed09ac5d80002e01be40000000551c38000000000000093a00000026180002fe00000003760004e40488a2856a3d42078bd60000000000000000000000111220e218909400047136213c04ee0004aa0000000505361882cc782ee125043809e5df038a51913865e55b224cf349ac52e18dc00034056e9794000b2a000096000020700000006ca1c0355839cd940001ad00004420003868000aea0000001de40000000002b140000004ea80000004240000000cd05653e28bd09f800043c216d3341751f3800000062600000000007e60000da8ab8000000146400000005a800063699425a00000007414388a9c00000000000013964323ec800000041a51390bc0000002c81e9d2e468859a00000000003a19b50f9a9bf2f10d44956b233e7911075a00059598fc06ca9a1e308280006980000000000000231a68c1320004a0967c0005f60002c0c0000001e68e44d6062a47f86b8bd43c13ec19b09fa13d3ae15300003ec47421750440004e21a440000005362479324b17144898865800000000003e6ad90e5000031647800011cd62081f35f05192566222cc8e30678a2a2fc0ecd64e9e747f1b180000004832709616000000049546622e3400c583126fc41d800109a206083092c9a28f44ba935c0f62680000218000ad642594cd60480b228a3b0f1400013d25300002c805f8000a140004ff85f4000a303658000000407000292cc6400000019ec2309e400000001d44f809406900005310001dd8276000263000105814515a1cfd4720002fe869c9b40003aa84c0cd60ad000245400000006b1e98000a6b4390000faa0000001e2c00079e51d16cc000981062a26c00000039da87006e3d946691c8322a9755a95b935c7b004d97201826ae2da07e8a7297d077a6343ce6000b71c1867009a4fc114929c31c0001ac447479d0000000000af7183000000000011b80010b2a7e1752cbc0009fd412800043276d000059820697937880000000004e7930c4e09314c49da400049c41c90fca5e3490dd2be896e5ee0f0a8fc00021304e89d40004684cb02310400000001e542ce41e0970f3c53c0a9000285d4e4a8d2608000000
  | 27 => 0x80000000014eb0b0c531298c584aed000239556e88215d855c1740df45213d476a84e00000001e01f200000000000000001f6c640000192a5f8d4835c00000000008ee0002a0cfae0005949cb400008e54a889ca0c37e4ed1fe425a8541938b380009250000074b46503184145d3981a2000087000000000000f00000000000000000466000238400064a00028503d409800000006ce45f00000011be45400018613b200000e00000147b23fd000026ea45000252c89063a230184d2c200000024eced406b086a3e00002483ea00000000000b4800000000000017e40001cb0001f84fd04ae0a117c55301c50b50054000000000000154a9af12280000007803c11b600000003da8cd8db801b2d0941020044c12d80000000000001f3878836d4e0a63c8048f53922a7c00035800022d80460005169c812043fc00000014ba72e000899000026a049000000041b0001dec0000b3000231c000a4f000204128470a46503d52b257151d97e80004f939999a4afa5ac00021dc00000000010b557caae3648880c1448a4ce2cc000000056480000000001e7000110a40900000000000003798d080006bb0001388aae000000000060200055e8000354a200000001404147472064068649606618b03d092a000000062600029a00000005af4201d303a80002680000e5699e000000000067e30a168133a74e21d00000005d32311478d523e453821b4cdc58133e80000008eb000230c000029000000154e08832789c8c903fe3c40ad8ee200059992b507000000000000000c7476856911a7e504a8d780000000000de80000000701fec2f60002ba00a0fee00000000000008d70000000000087000000000000044793a08d8a531089b940ac73200020f09ee12646aa0ac0006b900000010ec4fb24b9ad8b4c6cf000290800000024f018c5ca1271889b3084e00022800006c44cd029a82c04e1642fa82140003df000000000000000900003b80004b5000117a26100000006aaa4a3cc99a80005765348dc0ac60913a8a48936a7c655e0900b3a5323c8076c0007c80002030964b0f0000d3cfe42512b482c8054a4c00000012ca0c30960c413d000049f0140000000473116033485e23505c112c63d5508ed8ec4000000000065200000002c00002ed0000d5c00027100000011c000009d187c00070806418250481d608c82e4972000000243c000525000000000000000000000000af160ac240fa19c58080000008022aa000091aa994f480000e034b00016a4d385bc05224b951600015e8000000000000000000000000000000000002ce00000009e1000052c00000000017085a61c20000000d68000527235800069300000000008270001fa40000000328748e68000000164c000aec02ca7b0c08a780000000724000000048c0000000000000000414000
  | 28 => 0x11c80000000001d089b1650000152a61d180b3504496c0084ac355d027954456056990ac00059756700000009210bf800143000055980000722b332a25442901e300000014eeaad54200000000003b180013042800002360b4ea794538c013622a2068800000018d568a70016c99500028f800000001c2400458000000049156000000004f91b6120402893d50466d2110e6c00000000000000005d20000000c020000000000000aaa29f07d400000000022500001710dc9bd8ca093d0000f6c000044361142c806000311800000000004103a4bb411d0e40000e600000001bb0dee3fd00003940000004bd02108fa000000000000000031c0000f127493bf1b88f620000000000000aaf4fb860522c000269a5b11a845d3448204f7c0bd1b180015964a838b000063c41651e9a2d3ae8b143f1c1564056f4e8800000040a0002210d320000000000000000000000121800000000000000003ab8000000399457800000080e0f0000000091a23ca0f85a005f0001d9039e08052f1ebc0000000001ecc0001540000000000a8a0001380f5a38f000177488c000000000068264631397b406a2fa00000015ce0000000f60b92ae85588d8527e52925c0764664a5f46084e40ec849099a59c10619d5968b60710a9300005b4e5e7470000b6d1f400000000013201b713c2ba93088ae54e887c9882da136ac1400020100019944b20464c5054517663014dacc89e20002bb800032c9e215c07dc00015f25392c074c00007e0f845640d0151931c00000000000000003040000000f440a2547000000000000002f8b7a8a80000d5000079427d00006cc9a80001458000215000000000000006980000007ac000000000000000000000004701cb0000fac000000280cb1e4213772c38f3e0002c61acc00000014a1fb50e83c73a8251d4ec000032139cffc0000000978f96000405077d0523be0000000000a3644fa67c00019f00029003563a010f0000000000000000000077c000064d50028700000014b600000013b56364811bb800082a66119423ec00015e00016acd8260d3c728200000000001fb0af27c74b5a010c860000000a70000000000035000046f115a4d400075a44511680003a30001d5940a48e00011040000001af80000000000002bec0007eb50d80013de000000000071a34600000000000000c38f40ea600020900000002d70eb8ce8000000000000000049b00000000000004098000de00d800009396000003c1800000000045e12100000001f015910540cd28c23252c83aa38d153cf567bd04980000000002a70000dfc000000000000000000017bc00076e3f7800000012949d06a55946720ff80000003502a40db881676033c0199374686306000000053a4db172ce7868e0000000f40b1f1c82638e80a521f28000ce
  | 29 => 0x39c0f8a41cb6e172000264d08200000027d02c05460c52c28a766d343588349628000300f540005490000c840000000861ba40008f2155206cbfe33b32e270ca6a1d00000000e6c04a00022d00000000ef1a04a6e22300a000000c000000000099891400000008aa9010000000662000000036d1ec7a40000000000b04000041c0000001141b58c663ca0000fdce9a6a6538800101a00015e06cc0006852d22b5400000000009cc3a600000000002f800034900000003183938d806140004948080a0e0474d9a8a501e23b00000000005c335a8c740dc4822778fe152c2b74cc82d04185c500000005e283202d1b84ff07cc5590ca8b080102f02be000000000000000000001cf0000e7a00000001b0b7c5d80002b002de0000ad84790dc0000000ba0000afe17b8000000000000000000051c2ef00000001fe0040000df61e63c31a312a494952b81c800000000000000000000001638caaa870c900000000002552919490a6517c912c00078702e800069a0002518d582b20004620bd400040d53a159c4de9b80001bace7058723f1c44188759554147c0006763680000000ada45180000000000001728f028670000e680006a54f196d4c927010000000f1e55100022c00000000001070e444374f681dc634000000000162a0000001c740003070000c246d8000000033c50618e000243899400000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x19b2c0182a0e7800d023cc80527c700000000046ad42d3800980004400030292055c012a7340830b12bc6173a558a6001102100b0a222440400001a001020c1810100447800a38b8a00515644325d661d0c01455910cb755834300515644325d4644c801455910c9751853200515644325d7604c80141d9799663d06410050d656861c542504014b09059471509410050d654601c54250401455910c9759923100531644325ca648c40103d989d664906310051564432dd5608c40184d8518a71d0d3100613e14625c3434c40128e94a19531893100613189851d1324c40184c62614714c9310061318985dc1324c40184d8518a748c53100613e14625c2314c4591c49760b634c6210047125d82d0d31884015619008575905210040f660659d2315000141f975967390440007059d6735864110001455910c9751913000531644325c8644c001455910c975185300040f66275192414c00184d851c8644c5300061361472185314c00185687614614c530004b1a63624c6214c00103d981d464501300050d654401c564480018357520564191200060d5d48159341480f58c9801cc61485200ace226143509304802b3c0984c5214c1200068560d811976444001a158360465191100050d65c651924144001c157519173905100042d660641c52044001691900c5644c410005b0640315893104001c28751d16244010
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x4
  | 3 => 0x6
  | 4 => 0x1
  | 5 => 0x4b
  | 6 => 0x4c
  | 7 => 0x4e
  | 8 => 0x138e
  | 9 => 0x94b
  | 10 => 0x94c
  | 11 => 0x94e
  | 12 => 0x124b
  | 13 => 0x124c
  | 14 => 0x124e
  | 15 => 0x138b
  | 16 => 0x138c
  | 17 => 0x98c
  | 18 => 0x98e
  | 19 => 0x128c
  | 20 => 0x128e
  | 21 => 0x9cb
  | 22 => 0x9ce
  | 23 => 0x12cb
  | 24 => 0x12ce
  | 25 => 0x10b
  | 26 => 0x10c
  | 27 => 0x5
  | 28 => 0x10e
  | 29 => 0x180e
  | 30 => 0xa0b
  | 31 => 0xa0c
  | 32 => 0xa0e
  | 33 => 0x130b
  | 34 => 0x130c
  | 35 => 0x130e
  | 36 => 0x180b
  | 37 => 0x180c
  | 38 => 0xb0c
  | 39 => 0xb0e
  | 40 => 0x140c
  | 41 => 0x140e
  | 42 => 0xb4b
  | 43 => 0xb4e
  | 44 => 0x144b
  | 45 => 0x144e
  | 46 => 0x28b
  | 47 => 0x28c
  | 48 => 0x28e
  | 49 => 0x148e
  | 50 => 0x184e
  | 51 => 0xb8b
  | 52 => 0xb8c
  | 53 => 0xb8e
  | 54 => 0x148b
  | 55 => 0x148c
  | 56 => 0x184b
  | 57 => 0x184c
  | 58 => 0xcce
  | 59 => 0xd0c
  | 60 => 0xd0e
  | 61 => 0x188c
  | 62 => 0x188e
  | 63 => 0xe8b
  | 64 => 0xe8e
  | 65 => 0x18cb
  | 66 => 0x18ce
  | 67 => 0x95396
  | 68 => 0x94056
  | 69 => 0xb9396
  | 70 => 0x149396
  | 71 => 0x138956
  | 72 => 0x98956
  | 73 => 0x98954
  | 74 => 0x128956
  | 75 => 0x95496
  | 76 => 0xb8956
  | 77 => 0x94b96
  | 78 => 0x1489
  | 79 => 0x148956
  | 80 => 0x289
  | 81 => 0x14c9
  | 82 => 0x99254
  | 83 => 0x99256
  | 84 => 0xd09
  | 85 => 0x1889
  | 86 => 0x138b96
  | 87 => 0x139496
  | 88 => 0x9c996
  | 89 => 0x12c996
  | 90 => 0xcb
  | 91 => 0x98b16
  | 92 => 0xd0996
  | 93 => 0x98d16
  | 94 => 0x168b
  | 95 => 0x9d296
  | 96 => 0x8c
  | 97 => 0xb49d6
  | 98 => 0x9cb56
  | 99 => 0x150c
  | 100 => 0x9ce96
  | 101 => 0xa0116
  | 102 => 0x28116
  | 103 => 0xb9816
  | 104 => 0x148116
  | 105 => 0xd0116
  | 106 => 0x188116
  | 107 => 0x180a16
  | 108 => 0xa1856
  | 109 => 0xb8a16
  | 110 => 0xa0b96
  | 111 => 0x184a16
  | 112 => 0x1949
  | 113 => 0x181316
  | 114 => 0x29316
  | 115 => 0x149316
  | 116 => 0xd1316
  | 117 => 0x189316
  | 118 => 0x180b96
  | 119 => 0x181856
  | 120 => 0xb4b16
  | 121 => 0x154c
  | 122 => 0x24b
  | 123 => 0x16cb
  | 124 => 0xb5416
  | 125 => 0x20c
  | 126 => 0xb5456
  | 127 => 0xb4cd6
  | 128 => 0xb58d6
  | 129 => 0xb8293
  | 130 => 0xb8296
  | 131 => 0xb9496
  | 132 => 0x28b96
  | 133 => 0x148296
  | 134 => 0x149856
  | 135 => 0x29856
  | 136 => 0x148b96
  | 137 => 0xd0b96
  | 138 => 0x188b96
  | 139 => 0x185496
  | 140 => 0xd1856
  | 141 => 0x189856
  | 142 => 0x40c
  | 143 => 0x58b
  | 144 => 0x178b
  | 145 => 0x160c
  | 146 => 0x188d16
  | 147 => 0xd0e96
  | 148 => 0xd18d6
  | 149 => 0x188e96
  | 150 => 0x1898d6
  | 151 => 0x4956
  | 152 => 0x5816
  | 153 => 0x94994
  | 154 => 0x2c9
  | 155 => 0xecb
  | 156 => 0x124994
  | 157 => 0x11396
  | 158 => 0x11496
  | 159 => 0x10996
  | 160 => 0x10d16
  | 161 => 0x11796
  | 162 => 0x749
  | 163 => 0x17cb
  | 164 => 0x28b93
  | 165 => 0x184d16
  | 166 => 0x185796
  | 167 => 0x150994
  | 168 => 0x1689d3
  | 169 => 0x21414
  | 170 => 0x25453
  | 171 => 0x598d3
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 2169
  | 6 => 6501
  | 5 => 2873
  | 4 => 50
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
  | 7 => packedAt gbK7 (88929+((h/723+packedAt gbK7 (80253+(h % 723)*12) 12) % 2603)*13) 13
  | 6 => packedAt gbK6 (340219+((h/2167+packedAt gbK6 (312048+(h % 2167)*13) 13) % 7802)*14) 14
  | 5 => packedAt gbK5 (181948+((h/957+packedAt gbK5 (169507+(h % 957)*13) 13) % 4588)*13) 13
  | 4 => packedAt gbK4 (3612+((h/16+packedAt gbK4 (3500+(h % 16)*7) 7) % 67)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x3fff8783c1fc3fffe1c03f80fc288e7c19f673
  | 1 => 0xc3c07803fe1fc380fe003ffffcd74990e6487f
  | 2 => 0xfc007ffc001ffc00ffffc3ff031871e3078f9c
  | 3 => 0x7fffffe00000fffffc0003e07e03f80fe0
  | 4 => 0x7fffffffffff0000000003ff8003fff000
  | 5 => 0xffff8000000000000000000003fffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x4430180402404866041848218000224089631
  | 1 => 0x42841801920841089202292ce0434890624846
  | 2 => 0xa80922a40016a8122494825209181161058298
  | 3 => 0x2124d4af5400024d92b300432e06e02b80d60
  | 4 => 0x20207673299b3278000c001843bd8003d76000
  | 5 => 0x333c0060310220401030206083fefdd8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefaeafeeaf8c8feeefaeafeeaf8c8feeefaeafeeaf8c8feeefaeafeeaf8c8feeefaeafeeaf8c8feeefaeafeeaf8c8feeefaeafeeaf8c8feeefaeafeeaf8c8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_16945
namespace PEqualNP.Outside.L_meta_16945
open PEqualNP.Outside.L_meta_16945.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 4 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 12 := bs0_4_0
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
theorem bs3_3_0 : Interval s3Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 8 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_32 : Interval s3Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_64 : Interval s3Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 92 := (concat bs3_4_0 (concat bs3_4_32 bs3_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 44 := (concat bs3_5_0 bs3_5_32)
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
theorem bs4_4_0 : Interval s4Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 1 := bs4_4_0
theorem alls4 : ∀ k ≤ 4, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_4 i (by omega) hi
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
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 50 := (concat bgb_4_0 bgb_4_32)
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
theorem bgb_5_2848 : Interval gbAtlas 5 2848 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2873 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 (concat bgb_5_192 bgb_5_224)) (concat bgb_5_256 (concat bgb_5_288 bgb_5_320)))) (concat (concat (concat bgb_5_352 bgb_5_384) (concat bgb_5_416 (concat bgb_5_448 bgb_5_480))) (concat (concat bgb_5_512 (concat bgb_5_544 bgb_5_576)) (concat bgb_5_608 (concat bgb_5_640 bgb_5_672))))) (concat (concat (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 (concat bgb_5_800 bgb_5_832))) (concat (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)) (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)))) (concat (concat (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)) (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216))) (concat (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312)) (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)))))) (concat (concat (concat (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 (concat bgb_5_1536 bgb_5_1568))) (concat (concat bgb_5_1600 (concat bgb_5_1632 bgb_5_1664)) (concat bgb_5_1696 (concat bgb_5_1728 bgb_5_1760)))) (concat (concat (concat bgb_5_1792 bgb_5_1824) (concat bgb_5_1856 (concat bgb_5_1888 bgb_5_1920))) (concat (concat bgb_5_1952 (concat bgb_5_1984 bgb_5_2016)) (concat bgb_5_2048 (concat bgb_5_2080 bgb_5_2112))))) (concat (concat (concat (concat bgb_5_2144 bgb_5_2176) (concat bgb_5_2208 (concat bgb_5_2240 bgb_5_2272))) (concat (concat bgb_5_2304 (concat bgb_5_2336 bgb_5_2368)) (concat bgb_5_2400 (concat bgb_5_2432 bgb_5_2464)))) (concat (concat (concat bgb_5_2496 (concat bgb_5_2528 bgb_5_2560)) (concat bgb_5_2592 (concat bgb_5_2624 bgb_5_2656))) (concat (concat bgb_5_2688 (concat bgb_5_2720 bgb_5_2752)) (concat bgb_5_2784 (concat bgb_5_2816 bgb_5_2848)))))))
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
theorem bgb_6_6496 : Interval gbAtlas 6 6496 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 6501 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat bgb_6_288 (concat bgb_6_320 bgb_6_352)))) (concat (concat (concat bgb_6_384 (concat bgb_6_416 bgb_6_448)) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))) (concat (concat bgb_6_576 (concat bgb_6_608 bgb_6_640)) (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 bgb_6_768))))) (concat (concat (concat (concat bgb_6_800 (concat bgb_6_832 bgb_6_864)) (concat bgb_6_896 (concat bgb_6_928 bgb_6_960))) (concat (concat bgb_6_992 (concat bgb_6_1024 bgb_6_1056)) (concat (concat bgb_6_1088 bgb_6_1120) (concat bgb_6_1152 bgb_6_1184)))) (concat (concat (concat bgb_6_1216 (concat bgb_6_1248 bgb_6_1280)) (concat bgb_6_1312 (concat bgb_6_1344 bgb_6_1376))) (concat (concat bgb_6_1408 (concat bgb_6_1440 bgb_6_1472)) (concat (concat bgb_6_1504 bgb_6_1536) (concat bgb_6_1568 bgb_6_1600)))))) (concat (concat (concat (concat (concat bgb_6_1632 (concat bgb_6_1664 bgb_6_1696)) (concat bgb_6_1728 (concat bgb_6_1760 bgb_6_1792))) (concat (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888)) (concat bgb_6_1920 (concat bgb_6_1952 bgb_6_1984)))) (concat (concat (concat bgb_6_2016 (concat bgb_6_2048 bgb_6_2080)) (concat bgb_6_2112 (concat bgb_6_2144 bgb_6_2176))) (concat (concat bgb_6_2208 (concat bgb_6_2240 bgb_6_2272)) (concat (concat bgb_6_2304 bgb_6_2336) (concat bgb_6_2368 bgb_6_2400))))) (concat (concat (concat (concat bgb_6_2432 (concat bgb_6_2464 bgb_6_2496)) (concat bgb_6_2528 (concat bgb_6_2560 bgb_6_2592))) (concat (concat bgb_6_2624 (concat bgb_6_2656 bgb_6_2688)) (concat (concat bgb_6_2720 bgb_6_2752) (concat bgb_6_2784 bgb_6_2816)))) (concat (concat (concat bgb_6_2848 (concat bgb_6_2880 bgb_6_2912)) (concat bgb_6_2944 (concat bgb_6_2976 bgb_6_3008))) (concat (concat bgb_6_3040 (concat bgb_6_3072 bgb_6_3104)) (concat (concat bgb_6_3136 bgb_6_3168) (concat bgb_6_3200 bgb_6_3232))))))) (concat (concat (concat (concat (concat (concat bgb_6_3264 (concat bgb_6_3296 bgb_6_3328)) (concat bgb_6_3360 (concat bgb_6_3392 bgb_6_3424))) (concat (concat bgb_6_3456 (concat bgb_6_3488 bgb_6_3520)) (concat bgb_6_3552 (concat bgb_6_3584 bgb_6_3616)))) (concat (concat (concat bgb_6_3648 (concat bgb_6_3680 bgb_6_3712)) (concat bgb_6_3744 (concat bgb_6_3776 bgb_6_3808))) (concat (concat bgb_6_3840 (concat bgb_6_3872 bgb_6_3904)) (concat (concat bgb_6_3936 bgb_6_3968) (concat bgb_6_4000 bgb_6_4032))))) (concat (concat (concat (concat bgb_6_4064 (concat bgb_6_4096 bgb_6_4128)) (concat bgb_6_4160 (concat bgb_6_4192 bgb_6_4224))) (concat (concat bgb_6_4256 (concat bgb_6_4288 bgb_6_4320)) (concat (concat bgb_6_4352 bgb_6_4384) (concat bgb_6_4416 bgb_6_4448)))) (concat (concat (concat bgb_6_4480 (concat bgb_6_4512 bgb_6_4544)) (concat bgb_6_4576 (concat bgb_6_4608 bgb_6_4640))) (concat (concat bgb_6_4672 (concat bgb_6_4704 bgb_6_4736)) (concat (concat bgb_6_4768 bgb_6_4800) (concat bgb_6_4832 bgb_6_4864)))))) (concat (concat (concat (concat (concat bgb_6_4896 (concat bgb_6_4928 bgb_6_4960)) (concat bgb_6_4992 (concat bgb_6_5024 bgb_6_5056))) (concat (concat bgb_6_5088 (concat bgb_6_5120 bgb_6_5152)) (concat bgb_6_5184 (concat bgb_6_5216 bgb_6_5248)))) (concat (concat (concat bgb_6_5280 (concat bgb_6_5312 bgb_6_5344)) (concat bgb_6_5376 (concat bgb_6_5408 bgb_6_5440))) (concat (concat bgb_6_5472 (concat bgb_6_5504 bgb_6_5536)) (concat (concat bgb_6_5568 bgb_6_5600) (concat bgb_6_5632 bgb_6_5664))))) (concat (concat (concat (concat bgb_6_5696 (concat bgb_6_5728 bgb_6_5760)) (concat bgb_6_5792 (concat bgb_6_5824 bgb_6_5856))) (concat (concat bgb_6_5888 (concat bgb_6_5920 bgb_6_5952)) (concat (concat bgb_6_5984 bgb_6_6016) (concat bgb_6_6048 bgb_6_6080)))) (concat (concat (concat bgb_6_6112 (concat bgb_6_6144 bgb_6_6176)) (concat bgb_6_6208 (concat bgb_6_6240 bgb_6_6272))) (concat (concat bgb_6_6304 (concat bgb_6_6336 bgb_6_6368)) (concat (concat bgb_6_6400 bgb_6_6432) (concat bgb_6_6464 bgb_6_6496))))))))
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
theorem bgb_7_2144 : Interval gbAtlas 7 2144 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2169 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 (concat bgb_7_480 bgb_7_512))))) (concat (concat (concat (concat bgb_7_544 bgb_7_576) (concat bgb_7_608 bgb_7_640)) (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 bgb_7_768))) (concat (concat (concat bgb_7_800 bgb_7_832) (concat bgb_7_864 bgb_7_896)) (concat (concat bgb_7_928 bgb_7_960) (concat bgb_7_992 (concat bgb_7_1024 bgb_7_1056)))))) (concat (concat (concat (concat (concat bgb_7_1088 bgb_7_1120) (concat bgb_7_1152 bgb_7_1184)) (concat (concat bgb_7_1216 bgb_7_1248) (concat bgb_7_1280 bgb_7_1312))) (concat (concat (concat bgb_7_1344 bgb_7_1376) (concat bgb_7_1408 bgb_7_1440)) (concat (concat bgb_7_1472 bgb_7_1504) (concat bgb_7_1536 (concat bgb_7_1568 bgb_7_1600))))) (concat (concat (concat (concat bgb_7_1632 bgb_7_1664) (concat bgb_7_1696 bgb_7_1728)) (concat (concat bgb_7_1760 bgb_7_1792) (concat bgb_7_1824 bgb_7_1856))) (concat (concat (concat bgb_7_1888 bgb_7_1920) (concat bgb_7_1952 bgb_7_1984)) (concat (concat bgb_7_2016 bgb_7_2048) (concat bgb_7_2080 (concat bgb_7_2112 bgb_7_2144)))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 6 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 18, 50)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 5 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefaeafeeaf8c8feeefaeafeeaf8c8feeefaeafeeaf8c8feeefaeafeeaf8c8feeefaeafeeaf8c8feeefaeafeeaf8c8feeefaeafeeaf8c8feeefaeafeeaf8c8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277074666 * 2 ^ 32 + 4276811976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_16945.Model.Repr at out
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

def mono : List Gate := [⟨.and,[3,4]⟩,⟨.or,[0,6]⟩,⟨.and,[4,5]⟩,⟨.or,[2,7]⟩,⟨.or,[4,5]⟩,⟨.or,[8,9]⟩,⟨.and,[0,10]⟩,⟨.or,[1,12]⟩,⟨.and,[11,13]⟩,⟨.and,[2,3]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4276811976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4276811976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_16945

open PEqualNP.Outside.L_meta_16945 in
theorem PEqualNP.Outside.L_meta_16945 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4276811976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4276811976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
