import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_15243.Model
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


end PEqualNP.Outside.L_meta_15243.Model

namespace PEqualNP.Outside.L_meta_15243
open PEqualNP.Outside.L_meta_15243.Model
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

def SBf (j : Nat) : Nat := [2, 4, 4, 6, 3, 5].getD j 0

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

end PEqualNP.Outside.L_meta_15243

namespace PEqualNP.Outside.L_meta_15243
open PEqualNP.Outside.L_meta_15243.Model
def s0K1 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 1 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 1 => packedAt s0K1 (i*3) 3
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 1 => packedAt s0K1 (4+((h/1+packedAt s0K1 (3+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffffffffffffff
  | 3 => 0xffffffffffffffffffffffffffffffffffffff
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffff8b
  | 2 => 0xffffffffffffffffffffffffffffffffffff95
  | 3 => 0x26
  | _ => 0
def s0Atlas : Atlas := ⟨1,rawDecor 14 s0Pos s0Neg, 0xc000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_15243
namespace PEqualNP.Outside.L_meta_15243
open PEqualNP.Outside.L_meta_15243.Model
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
  | 2 => 0xffffffffffffffffdf83fff801ffffe00fff0f
  | 3 => 0x6ffc1ffffe007ffff007f0
  | 4 => 0xffffffffffffffffffffffffffffffffffffff
  | 5 => 0xffffffffffffffffffffffffffffffffffffff
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xffffffffffffffff808842592a4a96e5b2db77
  | 2 => 0xffffffffffffffffa17884af68932b748b6f0b
  | 3 => 0x1213c9324dda4db6da47b0
  | 4 => 0xffffffffffffffff842111c4711c71d8ec75dd
  | 5 => 0x8421e0781e07e1f0f86ee
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xaaa0000000000000aaa0000000000000aaa0000000000000aaa0000000000000aaa0000000000000aaa0000000000000aaa0000000000000aaa0000000000000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_15243
namespace PEqualNP.Outside.L_meta_15243
open PEqualNP.Outside.L_meta_15243.Model
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
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0xffffdfe0ffffff803fffffffff00ffffffe1ff
  | 3 => 0x6bff07c1ffffc00ffc01ffff00ff007e38
  | 4 => 0xffffffffffffffffffffffffffffffffffffff
  | 5 => 0x73fff801fffffff00001ffffff00007fc0
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xffff8022108825914952c4a45b2b2b4b6aaedb
  | 1 => 0xffffa05e21104af512654ac8ada0b5d5b3616d
  | 3 => 0x1484f23a9325bb49929d37b5a0e61a7638
  | 4 => 0x10844211c46238e2311c6c6c6b8dc5bb6
  | 5 => 0xe1087bde0783c0fc3e1f8f8f8c0e07dc0
  | _ => 0
def s2Atlas : Atlas := ⟨3,rawDecor 59 s2Pos s2Neg, 0xaa88000088880000aa88000088880000aa88000088880000aa88000088880000aa88000088880000aa88000088880000aa88000088880000aa88000088880000, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_15243
namespace PEqualNP.Outside.L_meta_15243
open PEqualNP.Outside.L_meta_15243.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x19c2d49040018a80000b628009020be43bc43be42bc42bf41bd41be40bc40de30dc30ee20ec20f610f410
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x14c100903200e0002cb94a438f29c851c5350658a4a0ce14141e418041b040043a060087808010
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 9
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
  | 4 => packedAt s3K4 (244+((h/4+packedAt s3K4 (224+(h % 4)*5) 5) % 19)*5) 5
  | 3 => packedAt s3K3 (255+((h/3+packedAt s3K3 (243+(h % 3)*4) 4) % 11)*5) 5
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0xfffffff807ffffffffffff80fffffffffc3fff
  | 2 => 0xff83fffff803ffff807fffff01fff807ffc7c7
  | 4 => 0xffc1ffffffc01ffff807ffffe03fff807f8f8
  | 5 => 0xf0001ffffffffe0000007ffffffc000007ff00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x21108259092492588909168b162c5b4b49db5b
  | 1 => 0x422104af424924a952522b40ab56ad95942dad
  | 2 => 0x847609325762393247644dd5819b30c6e6c6c6
  | 4 => 0xe843b1c46473b1c4644771e6cd03c6e0c770f0
  | 5 => 0xf7bde078783c1f878787e78f1e2070707bf00
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xa8a8808088888080a8a8808088888080a8a8808088888080a8a8808088888080a8a8808088888080a8a8808088888080a8a8808088888080a8a8808088888080, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_15243
namespace PEqualNP.Outside.L_meta_15243
open PEqualNP.Outside.L_meta_15243.Model
def s4K2 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s4K2 (i*4) 4
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s4K2 (5+((h/1+packedAt s4K2 (4+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffdf0ffc1fc7
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffffffffffffff
  | 3 => 0x6ff0ffe0f8
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffa1e22f19c3
  | 1 => 0xffffffffffffffffffffffffffff8224552a5d
  | 2 => 0x4489a54ae
  | 3 => 0x188ee398f0
  | _ => 0
def s4Atlas : Atlas := ⟨2,rawDecor 15 s4Pos s4Neg, 0xc080c080c080c080c080c080c080c080c080c080c080c080c080c080c080c080c080c080c080c080c080c080c080c080c080c080c080c080c080c080c080c080, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_15243
namespace PEqualNP.Outside.L_meta_15243
open PEqualNP.Outside.L_meta_15243.Model
def s5K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s5K4 (i*5) 5
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s5K4 (6+((h/1+packedAt s5K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x7fff00ffffffffc03fff80fffffff807f8ffc7
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffff00ff807fffffffff01fc03ffffff18ff
  | 3 => 0x83ffffff00007fffc03ffffe0003fff80fe0f8
  | 4 => 0x3ffffffffff8000003ffffffffc00000fff00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x904bd8292cc51463a48bc0972d5658c3986bc3
  | 1 => 0x20950942450a288489148b2a5698ab4ca3b55d
  | 2 => 0x412652e88a534d293227558198c335974d18ae
  | 3 => 0x76389c8cec6c723223b9e6cd0313c6e18ee0f0
  | 4 => 0x7bc0e0f0f0707c3c3c3e78f1e3e207060fde00
  | _ => 0
def s5Atlas : Atlas := ⟨4,rawDecor 31 s5Pos s5Neg, 0xc888c080c888c080c888c080c888c080c888c080c888c080c888c080c888c080c888c080c888c080c888c080c888c080c888c080c888c080c888c080c888c080, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_15243
namespace PEqualNP.Outside.L_meta_15243
open PEqualNP.Outside.L_meta_15243.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x4031f9b9b0c9488800000000580138a00170000200f9502918a9e1780000000820705159a801013168e8f0d109c018b09000481210e1416000b9e881c9a069f219987928c098398861d0d98121d9911208400101860b2400188000408402305b90028284007fd5001fe54005f95001fd54007f150017c54007fd4c03fe53007f54c03fc53007fd0c03fe43007f50c03fc43007fd4801fe52007f54801fc52007fd0801fe42007f50801fc4200ffcc801fe32007f4c803fc32007fd44017f51007f94401fd51005f54401fc51007fd0401fe41007f50401fc4100ffcc401fe31007f4c403fc31007fc8401fe21007f48401fc21007fd4001fe50005f94001fd50007f140017c50007fd0001fe40006f90001fd40007f10001bc4000ffcc001fe30007f4c003fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x1a4000bf58d2000df8c690003dc63480036e31a4000bfd8520007eec290002f761480017e30a4000fd18520005e8c2900037f5148001bea8a4000df94120006f8a090003be4048001de2024000fec8120007dc4090002ff65080077f3284000bf5942001df8ca10002ff64080017f3204000bf59020005f8c8100037e5408001be2a04000bfd8c2000dfcc610003de63080036f3184000bf58c20007bac610002dd63080037e3184000bf9882002fde6410017ec32080017f3084000bf58420006fea2100037d5108001f71084000fb08420005fcc0100037e5008001be2804000fed00200077c8010003bc4008001fc2004000ee10020007de4010003fa2008001f69004000fe48020005fecb8800efe65c4001bf32e20009f99710005facb880037d65c40013eb2e2003bf19710005fec988002fe64c4001df3262000af99310005fac988003bd64c40015eb262000bf19310006fca9880037c54c40017fb1e2001bf98f10005fac788006fc63c40017fb162000bf98b10005fac588002fc62c4001bfa8e2000df54710007f6a1880037e50c4001be2862000fe14310006f0a188003fb40c4001df2062000ef10310007f08188003b840c40017fb2c2000dfd9610004fecb0800efe65840017eb2c2003bf19610006f8cb080027c65840017fb242000bf99210005fac908002fc6484001bf2a42000df15210005fec708006fe63840017eb1c2001bf18e10005fec508002fe62840017eb142000bf18a10005fac3080037f5184001bea8c2004fdcc610027e86308003f72184001fa10c2000bf98210006fca1080037c5084001df2042000ef10210007ee2108003fb10840017fb2a2000dfd9510004feca8800efe65440017eb2a2003bf19510006f8ca880027c65440017fb222000efd91100057ec888002fe64440017eb222000bf1911000778c888002bc6444001bf2a22000df15110005fec688003df63440016fb1a2001bf98d10005fac688006fc6344001ee31a2001b718d10005fec488003ef624400177b122000bf98910005fac488002fc6244001f63122000bb18910006fea2880037d5144001bf2822000df141100077c8088003bc4044001fd8822000fd84110005feca0800efe6504001bf32820009f99410005faca080037d65040013eb282003bf19410005fec808002fe64040017eb202000bf19010006fca8080037c54040017fb182001bf98c10007bcc608006de63040017eb182000f758c10005bac608006fc63040017fb102000bf98810005fac408002fc62040017f3082000dfd4410006faa20800bf73104005fa1882000fdc8410007e84208002fe6004001fda802000df94010006f8a008003f85004001bc2802000fed00100077c8008003bc4004001fc2002000ee10010007ee2008003fa1004001fa8802000fe44010
  | 1 => 0x3bd6510001de3288000cf194400077ec62001fbe6310001deb188007ef18c400077ea62001fbe5310001dea988007ef14c400077ec420003be6210001deb108000ef188400077ea420003be5210001dea908000ef1484003f7e6420003be3210001de9908007ef0c8400077ec220003be6110001deb088000ef184400077ea2200033f5110001df2888000ef544400067aa220003bc511000fdf9888000ef8c4400077a622001fbc3110001df9088000ef884400077a4220003bc2110001df3008000af9804000774c020003bf5010001df2808000cf940400077aa020003bc50100019e2808007efcc04003f786020002ff658c0077f32c6000bf5963001df8cb18002ff648c0017f3246000bf59230005f8c9180037e548c001be2a46001bf58e30005fcc518002fd628c001ef1946001f70ca30005fcc318002fd618c001bfa8c6000df54630007bc6318007dc318c0037f3046000df94230006f8a118003fb408c001df2046000ef10230007f08118003b8408c003ef9846001fecc23000ff06118002ff654c001bfb2a60009fd953001dfcca98002fd654c0077e32a6000df19530004f8ca98002ff644c001dfb226000afd9130005fcc898002fd644c0017e3226000ef1913000578c8980037e544c001be2a26001bfd8d30007bea698007dc534c001efa1a6001f710d30005fec498003ef624c00177b126000bf18930007d8c498002ec624c003ef9926000f74c930005fec298003f7614c0017bb0a6000bf18530007e8c298002f4614c001bfa8a6000df5453000fbe6298003dd314c0037fb026000df94130006f8a098003fb404c001df2026000ef10130007f08098003b8404c003fd9826000f78c13000fb86098007f8304c0017fb2e4003bf99720006fccb900027e65c80017eb2e4000df59720004facb9000efc65c80017fb264000bf993200077cc990002be64c80017eb264000ef593200057ac990002fc64c8001bf2a64000df15320005fec790006fe63c80017eb1e4001bf18f20005fcc390002fd61c8001bfa8e4000df54720006fca1900037c50c8001fda064000ef90320007788190003f840c8001dc2064000bfd962001dfccb10002fd65880077e32c4000bfd9220005fcc910002fd64880017e3244000df95220006f8a910002ff63880037f31c4000bf58e2000df8c710002fd628800df79944006fb0ca20005fcc310002fd6188001bfa8c4000df54620007dc4310003ec21880017f3044000df94220006f8a110003be4088001de2044000fbc8220007f64110002ff6548001bfb2a40009fd952001dfcca90002fd65480077e32a4000df19520004f8ca90002ff6448001dfb224000afd9120005fcc890002fd64480017e3224000ef1912000578c8900037e5448001be2a24000bfd8d20007bec690002df63480037f3
  | 2 => 0x50006f884280277f3214001bf190a000df4c85004ef8642800f7f6114001bf308a000df58450004fac22800f7c6114001bfa08a000df90450006fa82280037c4114013bf988a000df8c450006fa62280277c3114001bf908a000df88450006fa42280037c2114001bf300a0009f98050006f4c0280277f3014013be180a000bfd974001dfccba00037e65d00013f32e8000bf59740006facba00027d65d00077e32e8000df95340006f8a9a0006fe63d00017eb1e8001bf18f40005fcc5a0002fd62d00017f30e8000bf58740006fea3a00037d51d0001bf2868000df14340005fecb2000efe6590001bf32c80009f99640005facb200037d65900013eb2c8003bf19640005fac920003bf5490001bf2a48000ef952400067ca920003bd5490001be2a48000ef1524000678a920006fe6390001ef31c8001b798e40005fac720003dd63900016eb1c8001bf18e400077e8720023be4390001dea1c8008ef10e40005fcc520002fd6290001dfa148000ef90a400077a8520003bc42900017f30c8000bf58640006fea3200037d5190001dfa0c8000ef906400077a8320003bc41900017f3048000df94240006f8a120003bf4090001fda048000efd96400077ccb200033e6590001deb2c8000cf5964000778cb20003bf6390011df31c8000e798e400077ac7200039d6390011de31c8000efd4e400477ca720003bd5390011de29c8000efd8a400077cc520003bd6290001de3148000efd4a400077ca520003bd5290001de2948008efcca400077c6520003bd3290011de1948000efd86400077cc320003bd6190001de30c8000efd46400067ea320003be5190001dea8c8000cf5464000778a320023bf3190001df18c8000ef4c640047786320003bf2190001df10c8000ef48640007784320002be6090001dfa848000ef942400067ca120003bd5090001de2848000cf142400477e6120023bc30900017fb2a8000dfd9540004fecaa000efe65500017eb2a8003bf19540006f8caa00027c6550001bf2a28000df15140005fec6a0006fe63500037e31a8000bfd8940005f8c4a0002ff61500017e30a8000dfd4540006faa2a00037e5050001be2828000fed01400077c80a0002ff6510001bfb2880009fd944001dfcca20002fd65100077e3288000df19440004f8ca20002fe6410001dfaa08000df950400077ca8200033e5410001deaa08000df1504000778a8200033c54100037f3188000bf58c4000df8c620003bf431000fdf2188000ef50c4003f788620002fe62100017eb108000efd08400077c8420003bd4210001de2108000bf98440005fac2200037f5110001bea888000efd04400077c8220003bd4110001de2088000bf98040006fca0200037c5010001dfa008000fe900400077a8020003f94010001dfb288000cfd94400077cca2000
  | 3 => 0xf3224200bf59121005f8c8908037e5448401be2a24200bfd8d2100dfcc690802fd63484037e31a4200dfd4521006faa290803f72148401f710a4200bfd8121005f8c090802ff65084077f3284200df99421004fcca10802fd6508401beb2842009f5942101df8ca10802ff64084017f3204200ef990210057cc810802fd6408401deb204200af59021005f8c8108037e5408401be2a04200bfd8c2100dfcc610802fd63084037e3184200bf98821007dea410803ec5208401f7a104200fb10821007dc6410803ed32084017f3084200dfd4421006faa210803f74108401fa2084200fbc8421007ec4210803ed2108401fa9084200bf98021005fac010802fe64d4007df326a000af99350005fac9a800fbd64d40015eb26a000df9535001ef8a9a8006fe63d40017eb1ea001bf18f50005fcc5a8002fd62d40017f30ea000bf5875001efea3a80037d51d40017eb2ca000bf99250005fac9280037f5494001bf2a4a000df55250006f8a928006fe6394001ef31ca001b798e50005fac728003dd63940016eb1ca001bf18e50006fea72802b7e5394001bea9ca00adf14e50005fcc528002fd6294001bfa94a000df94a50006faa5280037c52940017f30ca000bf58650006fea3280037e5194001bea8ca000df1465001dfcc1280037f5094007fda84a000dfd9250006fcc9280027e6494001beb24a000df19250006fec72802b7e6394001af31ca000df58e50006bac72802b7c6394001bfa1ca00adf90e50006fa872802b7c4394001bfb14a000df98a50006fac5280037c6294001bfa14a000df90a50006fa85280037c4294015bf994a000df8ca50006fa652802b7c3294001bfb0ca000df98650006fac3280027d6194001be30ca000dfd0650006fc83280037d4194001be20ca00adfcc650006fc63280037d3194015be18ca000dfc8650006fc43280037d2194001be10ca0009f98250056fe612802b7c30940017fb22a000efd91500057ec8a8002fc6454001de322a000af19150006fca8a80037c54540017fb1aa001bf98d5000df8c6a8002ff62540017e312a000bfd8550005f8c2a80037f5154001bea8aa003fed4150006fca0a800efe65140017f320a000bf5905001efea8280037e5414001beaa0a003df1505000dfcc628002fd63140037e318a003dfd4c5004efca6280037d5314007be298a000bf98850005fac42800f7f5214001bf290a000df5485001ef8a428002fe61140017eb08a003dfd4450006fca2280037d5114007be288a000bf9805001efea02800ffa5014001bea80a003fe5405001efec8280037e64140013f320a000df5905001ef8c82800f7f6314013bf318a000df58c5001ef8c6280037f4314013bf218a000df50c5004ef8862800f7f6214001bf310a000df5885001ef8c4280037f4214001bf210a000df508
  | 4 => 0x802fd63d04037e31e8200bf98b41005fac5a0803bf42d0401dea168200dfd4741006faa3a0802fe60d04017eb068200bfd964101dfccb208037e65904013f32c8200bf59641006facb208027d65904077e32c8200bf592410077ea9208037e5490401be2a48200ef1524100678a920806fe63904017eb1c8201bf18e41005fcc520802fd62904017f30c8200dfd4641006faa320803bf4190401fba0c8200bf98241005fac120802ff6550401bfb2a82009fd954101dfccaa0802fd65504077e32a8200df19541004f8caa08037e5450401be2a28200bfd8d41007bec6a0802df63504037f31a8201bf18d41007b8c6a0806dc63504017fb128200fbd8941005dec4a0802fc6250401f63128200bb189410077e84a0803bd4250401bfa8a8200df54541007ee82a0803be41504017fb028200fed8141005f6c0a0802fc6050401fc3028200be18141005feca2080efe6510401bf32882009f99441005faca208037d65104013eb288203bf19441005fcc820803bf5410401bf2a08200df1504100778a8208033c54104037f3188200bf58c4100df8c620802fe62104017eb108200bf98441006fea2208037d5110401dfa088200fd904410077a8220803f541104017f3008200bf58041005fecb1880efe658c401bf32c62009f99631005facb188037d658c4013eb2c6203bf19631005fec918802fe648c4017eb246200bf19231006fca9188037c548c4037eb1c6200f7d4e3100fb8a718803df438c403ee21c6200bf98a31005fac518807df328c401ee9946201bf98631006fea3188037d518c403ef98c6201fdcc63100fe86318802fe608c4017eb046201f70c231005feca9880efe654c4017eb2a6203bf19531005fec898802fe644c4017eb226200bf19131006fca8988037c544c4037fb1a6200bfd8931005f8c498803de324c403ee1926201bfd8531006fea2988037d514c403fb98a6200f78c53100fb86298807f4314c4017fb026200bf1813100fbe6098802ff65c84077f32e4200bf5972101df8cb90802ff64c84017f3264200bf59321005f8c9908037e54c8401be2a64200bfd8f2100dfcc790803de63c84036f31e4200bf58f21007bac790802dd63c84037e31e4200dfd4721006faa390803f741c8401fa20e4200bf98321005fac190802ff65884077f32c4200df99621004fccb10802fd6588401beb2c42009f5962101df8cb10802ff64884017f3244200bf59221005f8c9108037e5488401be2a44200bfd8e2100dfcc710803de63884036f31c4200bf58e21007bac710802dd63884037e31c4200bf58a21007dea510803ec5288401f7a144200fb10a21007dc6510803ed32884017f30c4200dfd4621006faa310803ef2188401fb90c4200bf98221005fac110802ff65484077f32a4200bf5952101df8ca90802ff64484017
  | 5 => 0xe3200dfcc519007df328c803f79946401fb0ca32005fcc319002fd618c803ef98c6400bf98232005fac119007dc308c8017fb2a6400dfd9532004feca9900efe654c8017eb2a6403bf19532006f8ca990027c654c8017fb226400bf99132005fac899002fc644c801bf2a26400df1513200dfec699006ff624c803f79926400f78c93200fb86499007ec324c8017fb0a6400bf1853200fb86299002ff604c8017e3026401f7cc132005fcc9a8802fd64d4407bfaa6a200df95351006faa9a880f7c54d44037f31ea200bf58f5100df8c7a880f7f53d4419bf29ea200df54f5101ef8a7a8802fe62d44017eb16a203dfd4b51006fca5a88037d52d4407be296a200bf98351005fac1a880f7f64d4401bf326a2009f99351006fac9a880f7c64d4407bfb1ea20cdf98f51006fac7a880f7c63d4401bfa1ea20cdf90f51006fa87a88337c43d4407bfb16a200df98b51006fac5a880f7c62d4401bfa16a200df90b51006fa85a88037c42d4419bf996a200df8cb51006fa65a88337c32d4419bf98ea20cdf0c75101efec1a88037e60d44013f306a200df5835101ef8c1a88337f30d4419be186a200bf59651004facb28802fe64944017eb24a200df95251006f8a928806fe63944017eb1ca201bf18e51005fcc528802fd62944077f30ca200dfd465101feea328802fe60944017eb04a200bfd91510077ec8a8802bf64544017e322a200ef1915100578c8a88037f5454401bf2a2a200df55151006f8a8a8802ff6354401efb1aa200b7d8d5100dfcc6a8806fc6354401ee31aa201b718d51006fea6a882f7e5354401bea9aa20bdf14d51005fec4a8803ef625440177b12a200bf18951007d8c4a8802ec6254401bfa92a200df94951006faa4a88037c5254407fba8aa200df94551005fec0a8803fb60544017db02a200bf18151007f0c0a8802f86054401bfb22a200cfd9151006fcc8a88037d6454401be322a2009f1915100678c8a88023c6454401bfb1aa200d7d8d5105efcc6a88037d6354417be31aa200d718d51006fe86a882f7e4354401bea1aa20bdf10d51006fec4a88036f6254401bf312a200df58951006f8c4a88036c6254401bfa12a200df90951006fa84a88037c4254417bf992a200df8c951006fa64a882f7c3254401bfb0aa200ddd855105efe62a882f7c3154401bfb02a200ded8151006fcc0a88037d6054401be302a2009f18151006f0c0a8802786054417bf982a20bdf0c15101dfcca288027e65144017f320a200bf59051006fca82880f7c54144037f318a200bf58c5100df8c628802fe62144017eb10a200bf9845101efea22880ff65114401bea88a203fd54451005fcc028802fd60144017fb2e8200dfd9741004fecba080efe65d04017eb2e8203bf19741006f8cba08027c65d0401bf2a68200df1534100dfcc7a0
  | 6 => 0x3ee29aa600bfd8953005f8c4a9802ff6154c017e30aa600bfd8153005f8c0a9802ff65d0c077f32e8600bf5974301df8cba1806fe64d0c01bf2a68600df1534300dfac7a1807be43d0c03ef21e8601ef10f43005fcc5a1802fd62d0c03ee1968600bf98743005fac3a1807dc31d0c017f3068600bf5834300fbe61a1802ff6550c01bfb2a86009fd954301dfccaa1802fd6550c077e32a8600df19543004f8caa1806ff6450c01bf2a28600df1514300dfec6a1803df4350c03df21a8601ef10d4300fb886a1802ff6250c017e3128600bfd8543005f8c2a1802ff6050c017e3028600bf99352005fac9a90037e54d4807be2a6a401bf98f52005fac7a9006fc63d48017f30ea400bf58752005fcc1a9002fd60d48017eb2ca400bf992520077cc929002be64948017eb24a400ef592520057ac9290037e5494801be2a4a401bf98e52005fac729006fc639481dbf29ca40edf14e5201dfcc5290037f5294807f7a94a400bf98652005fac329002fe60948017eb04a400bfd9152005f8c8a90037e5454801be2a2a400bfd8d52007bec6a9002df63548037f31aa401bf18d52007b8c6a9006dc6354807f7a92a400df94952005fec2a9002fc61548017fb02a400bf1815201dfcca29002fe64148017eb20a400df9505201ef8a829006fe63148017eb18a401bf18c5206efca62900f7c53148017f310a403dfd485201fdca4290037d5214807f6a90a400bf98452005fac229002fe60148017eb00a400bfd974201dfccba1002fd65d08077e32e8400efd5342006fca9a10037c54d0801de2a68400cf1534200dfcc7a1002fd63d08037e31e8400bf98742005fac3a1002fe60d08017eb068400bfd964201dfccb210037e65908013f32c8400bf59642006facb210027d65908077e32c8400bf59242006fca9210037c54908037f31c8400bf58e4200df8c721002fe6290801dfa148400fbd0a42005fcc321002fd61908017f3048400bf58242005fecaa10037f65508013fb2a8403bf99542005facaa100efc6550801be32a84009f195420077ea8a10037e5450801be2a28400ef1514200678a8a1002ff6350801efb1a8400b7d8d4200dfcc6a1006fc6350801ee31a8401b718d42007de84a1003be42508017fb0a8400fdd8542005eec2a1002fc6150801fa30a8400bd18542005fec0a1003fb60508017db028400bf18142007f0c0a1002f860508017fb288403bf99442005faca2100efc65108017f3208400df95042006f8a821006fe63108017eb188401bf18c42005fcc421003bf4210801f72108400ef50842007da8421002fe61108017eb088400bf98042005fac021002ff658c8077f32c6400bf5963201df8cb19002ff648c8017f3246400bf59232005f8c9190037e548c801be2a46401bf58e32007bea719007dc538c801efa1c6401f71
  | 7 => 0x401600000000800000802600400600e00000000400200001400400000600000000400000200000601400200200c00a00400400001800000200001600601200000000200000200400200600a00000e00201e00000000400000200400008200201e00000800000a02200800000000c00000a00001a00002000000000000200200000000001c01c00000001001a00201e01e00a00000c00002e00200c00e00a00a00000000e00400600600601600000800000000400a00e01c00400000c00a00000000000000000000600000000000400600400000601800000000800401800400600000001000600400000000000000200400200000200600000200800400200000c00000200000402000000001400200200200000200001600a00600002e00400600401600800200800400800002400003c00600000400002400600201600000000200600c00200600600000200200000000000200400200803800000800400000600000000000a01600001400001a00200200000000200800200000400400400600200000600800000200800001bf98f54005fac7aa006fc63d50017f316a800bf58b54005fcc3aa002fd61d50017f306a800bf58354005facb2a00efe6495001bfaa4a803efd525400dfcc72a002fd63950037e31ca810df94e54086f8a72a002fe62950017eb14a800bf98654005fac32a002fe60950017eb04a8009f99254006fec72a0437e6395001beb1ca810df18e54086fc872a0437c4395001bfb14a800df98a54006fac52a0037c6295021bf994a810df0ca54006fec32a0037e6195001beb0ca8009f58654006f8c32a0437f3195021be18ca800dfd8254006fcc12a0027e6095001beb04a800df18254086fe612a0437c3095007dfaa2a800df95154005fec6aa006fe63550037e31aa800bfd8954005f8c4aa002ff61550017e30aa800bfd8154005f8c0aa00efe65150017f320a803dfd505401f7ca82a0037d5415007deaa0a801bf98c54005fac62a006fc631501fbf298a803df14c54005fcc42a002fd62150017f308a800bf58454005fcc02a002fd6015001bf320a8009f990540067cc82a00f7f631501fbf318a800df58c5401ef8c62a03f7e431501fbe218a803dfd8854006fcc42a0037d6215007be310a80fdfcc85407ef8642a00f7f6115001bf308a800df58454004fac22a00f7c611501fbf988a80fdf0c45401efec02a0037e60150013f300a800df5805401ef8c02a03f7f301501fbe180a801bf99753005fcc9a9802fd64d4c01bf2a6a603df1535300dfac7a98077e53d4c03ef29ea601df14f53005fcc5a9802fd62d4c03ee196a600bf98753005fac3a9807dc31d4c017f306a600bf5835300fbe61a9806ff6554c017fb22a600bf19153006fca8a98037c5454c037fb1aa603f7d4d5300efca6a98077c5354c0
  | 8 => 0x93174c0011c80006b1744f5cec0000000000000f280017e8000b34000e800000000000000017400008a99dc555658000000000000000380000001408124e4c3f58380080011b0000b0c000004620000000000000000000a785a98d8609028c24cd43ace318b43a84d0ce8bfca819e84740001a0000b680000000012fc000d412a034c0005d8d853b8fe913c00148555c0000000010fd651760bb43714cd2f146109d1e84c4d64ba4a28241540ce4d381b8000000000000d0d1d903d16c00000000000000000000000077166400000047000000000046505196c6a4000bd00000016449cca552e8b50000d715ac7e10f03ec00000031c00042d9908f16bc3241008ec000848fad031624198f681391657940012843b92940012d40000291303895cc0012f4a64be00000005983905458b95a05340000003553540010dc5f400118839c148000654000cdd8cd07c0f83751ac9b90859393f00e13091f8ee82c000000000000000000000026c2a19745fcc6c000001491388a58e448b40000000002248680011a4bd4000000000ec90b0000000585498000938e059f0eb169c0018e5834b48b24ed17780000000012200cc000000000284000000000f145414b4000000000000114e7973800000000000000000000000075d7a4accc48000ef960c000c4c368ad000000000086d2c80000018440000000002bc00000002ca303a0e1d00403015ca68a0c72c53d800e10b898d1a44be5951064c8d9e0c180b4b60dd82e8bad3156559cc000000604001a3c2fc0000000e97b140c00177c09c0014d8e5c30400002600a00000400801201600800201800000000001200201000a00a00a00600400200000c01c00200600000400000001000400200600400400c00600000603200000000400a00000200400001000c01200600000a00600200c00600a00800000201400c00400000601a00400002800402a01800c00c00000000000801801e00000200400000400000200000600000600600000200000000600c00200e01400e00000400400000000000601000000600200c01600000400401400c00000401801000001800200200a00800000400e00000c00c00400600000000000400600600000000000400001600400000a00a00400400200000000000401c00800400800c00201a01800200a00600600400800a02400001a00000e00000800000200600a00400a00000000000600200c00400e00200600600c01600001000800800c00200800401e03400000200400a00002400000000802800000200400000e00a00600000600000800e00200000200400400000600200000804800400400600000400800400c00400400200200000600000400000003200600000000400a00000001400400000200000400001400800a00200800000e00201400200601c
  | 9 => 0x6d40c8b8d47cb20c14eecd8d994c844780000000000001c17e1350f78558000408adcc58b80a002f53851513680000011d400129d5c0e0c0000002740000003f89580000b00000018a40013240015d00000000000000000000017640008bc000000000000001a3000000000000000000000152d32000078c0016d000105d7809e08ad7d4248d7d900cf4b540014659a0c048410494b8a88000001a4000000000125d5040008c0ca8e8cb1c001840050f7542c7f8588f05058068780db8f9d394cac0000017fc434cf0db16082b90d02f82b57dc6f455c0009d00003200000007e4000000000000c9da4c00067016cb104b07c40bc1583346306240016f40014780004b90a10d52540013f4cd9a1538c000000001109784000000000000d49a04668bf99b8a7d0407d4000000000af80005f80017f800000000145c0000011e00018acf4c8a46e0c7501d6dd9bcce0f3186000085cb58000710001618000000000ecc000000e48000000e14001024000da446c0010340001bd270f0d43cee551c000c280000000012d000182d9100c438d6a00004e40000000014f0000000b74000000750d9c0015989d42dd5880004dc0780000016b8c1d358a40d1d72406cf552acb6437c0000000009904e99497355517ad5b4dcd3e03307155840015940018c0f580014580000000016cce6573c12cbbd8040004a92dcfec000001470ea1a240010b4b3c879094400001668000e6114902c3fc0006992cc0000000005c8000a383f000144c0000000000000011909e8644308000a24ba00000000011bc00190970436409800000000018c8e800073c0004f968d5659153e87ac0001817bccc8c98000778000000f49534090ccd2e46f8288730000000000fe020ce215592b800000104c00153d9d80007b00000018dcea4000000000000000000dd40000f40000000000000005b400000000000000000000166c00046184cbe869c0005ad600824a84c0035da500005b96285e00d4b40e900d13393049e4000000fc08342e49fd748d891281957d98300019040000007cc00107112c0000003c0ff4300a908015b8641114548884cec000674bc000000000067c0011c0000af1689935571008001924019319675180f198e8000db430d2a40016b00000007400000017c468189cb6d20800000000000000000068996800064d69471c4d8f3c0002200000000015d8ffc00000177508972c00000152179197093c0018c8df84f400000000000183c0fc000000978000000001158fb09447395dd9fd5240017e59a8000000000c20c0c000df54f4aa16342ac085718f700493107fcd2910433cc44ac81f52440a45380002583402a452000161c9600000000000009800000000010c1930000aed9ecd215c82b07f16058ecac4e9cc416fce541d928000089c5e800000190c0
  | 10 => 0xff9888ddc00000050c1c40015600002d55a42c411da0191c3b40011547640000000005519b15f00018680000000000014c19c8001989a390a4594b457697d1771554b28344c60ae586c82c1ec95d1740007d90c4498b150ac694ca0001614d24000c918998d4b946b8a194307e82f013424d1859d55300010bc000001178000844ba8000cd170c000000001538a2c00000c9bc0000000000011d16780009c0704000000000000000c2c6fc001488fc80008b05800003d80000019d0000f3400000188150d37400132d874000d7879d8a997956874400172000000156cb18000ca46d8260000001920e40d9800000000102179cd112340000000005b00001500000008641419580f00000000012585a4000638000000a4cfb4bc80000000000013bc0004c80011a0000fd94143e40000000000006506a0000410000fd48280014a4ef1044b5d4ac8e1a280000004514b13480009896f10b8000000000001640000870fc56e5201884ff04493b09b000000000050892c0018080dc4550380010ec17490800048d43800000000023400000000090400128c1316f8c79574fa4164a1d1f06ecafd2111946b572988c8095c4b9802524116800000000059181c00000198159c00075800000089000058c0000019a40007840016913a57cceb40000000000008a0ed50980456c40009180011b4204000000000f7c0000000008940000002a975c0000000012040000001fc22c000000ad53c476ca4400167061949515da4924c57ce74e3c2092a8378000000228000000510e2d01859caa40000018513cc000000188000000814000e5074c2984b4c50e88e288218147992900019c0df00000017003e94a91f4c70af40017141dc34800054c0000000a00000000006c4bec00000004c0001e4000000000f000014e4000f4597d0cd13921518c21c40c000000d4cdad4755017519607dcec58fd0c84f1638f644ec000418818000000250000000fa0000000000000000094001410000f250a98180000012e00000012b4b70000000b4d0e920cdd0fe40009113d4000d557c19991349408d1264000001518c34000000ed8d50955a100012b17a8c08444fcca500010d8f88f1d3ac000cf800032888c3596a46e8bcc760850564a4800019c969711870000f9000000108089812936c70883d17189047d27c9c5510fdc41c70c5ccd1939c3d0185a1c560914000b08b3005c6640008fc1ad4449a44cc9a0d3d8f07b40016a87b96d4000d5c000000000000000de4000c557f1380000000000000001680000d311c4001730000000064dec7919e400090c0000013980000000001f800000000154c9700000000005c0f380000005bd2bc001a0d39108c98d6e00001cc0000012751dc000360c38394294dbcabc4800000000004283980014287557ec8748dc7a9919454a1
  | 11 => 0x61d5a985400000000157c000074000000000e3400000146ca940006ac000000000000000794000000000000000000000001360610700cb400000073414c0000009202003b096c0e48e45d000060d3001914049dc0000000014ed120a14350efc000cb8b9000000000000000000000000098526c0001b58f8290000001610000d44000000dfc12036ce840006bc7a00008d8000000dc000000187975400088168534d98c948634144629298000000000e95481a2c0001180000016c04c0000f08000000000f611100018280009293441559b4000a6c000eac0016200000000000005192480011440c128910000032c8581604380000000000006e48600000000009d8000000f6c00000000000062c000f2d3fc56825400123c00000001c00000092400180c000000000504cb12f930d0780000019549011180142d80008302c95295d53d05780002440005280000001696e98b119c0215e4bf0000000f800000000006f0001548314000b840013a12ed4bc000d906a94c97f4a0838457499866c91c000000000230aa87740013c8cc4000000001820d14b9d7b4658060000a20001230cfd1a9578000000000000d2d0904d4000000de1335328e68000000000000f10718000eb96d91e40341b137d940c7c94d2c4b003dd01463c3e00a9440000000040000000d680003a400000000135d06185987c7280014a00013dcc10000000da800000133000000077c000001698f840000019280000009ac7c00000004a4da17a1450000000310000000d7443c21095000146800080c28c530000ee000158c0000006900015bc4680010008b921851413cf400590e00010100000000005240016c80000013640000005d400045845c000000000e08c30000000ad80016ec000000000000000000000cbc8cc488ab94d5a189ec00000000017800017c0000011ed3d98103c911ce011b95f8bb0a344a00009644040000008898a00000009f4000e24c68d585a0ea93e403cd3592cb785e4a8d0686c81d163001057198596465cc647d0001758000ae87f4d08bf4000000000ab0edc000000bd81a995d9f52518bc000000a5cf8c28171c51d2282145f0218d040000000000000000013f99452680002788c963d79922512400000121c2702680000018944218e13b4000839160001239a34600fb8000000000001424000de80000000d81084bc000000c88805a21199260ef4000000c802cc0ac000000a04d800000013c0e194d09f1140d0000133d51514c000000000001590d615b0748000678fbd418f946c14c55800000001e000000000000194c00199c8f564800182527970808800000178c0000007ec0000013a8d6ce58a9c0007890f497c000000dc4494484b2c5ecab40000000000000000004e0000001400000e994fd22ca98000000000000000000000000
  | 12 => 0x6dcb38000000fd000000000000165c29ce70000a3d5f4a600019f8bdd4dc9757c85dcf2049c8d4000648768000e6d48c0000000014f80000000000007c80000002e00015e00001f15fc00000000099c6603c40000018f40008540001d44ac810338bb81c881c0009940012c00006d13ec001864000000a7506d49c0398480008c541c0006cc2ed00c4fc84c3d40000013700009b40017b985c000fa86843bc0000015440000005c59c4000b04ebc0000000014e80010540005001e80016ac000000110f500000015ec000000000cc110c0004409f9660000b7c0000019ac0004301a562c61425d5e993c00000000005400000131c00000000000000134031942000000023d0e400041400093517c0000000014480000014e0bc4000000aac44d50808c000000c957896b51fc9c9a0800164cd94ac0c3c42468c10c7a53782d167cdc856c8f90f807c87c000490264f98ae01707252d80011cc0ed07407023852ca70720e7c27c3cd8c54349a8c5c0000b8e3976c0000000001047bc0800000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc6214110004be76901100063f65901100063c65901100069f63901100469c6390110006af6290110006ac6290110004be76101100063f65101100063c65101100069f631011003e9c6310110006af6210110006ac62101100067865c4110006b864c4110026d46384110006e4628411000cde73d9410004dd73d94100047d76994100047e7499410004bf7459410004bc745941001c7f76594100053c74594100063f74594100047c74594100063c74594100043c745941001c7f715941005c7d715941000678705941001c7e75d90100047d75d901000cde73d9010004dd73d90100047f755901001c7c755901001c7e75190100047d751901000cde7319010004dd7319010004ee7219010004ed72190100047f76950100047d76950100865e63950100057a709501001c7f76150100047d76150100063f64150100063c641501007e5e631501001c7e75d8c100047d75d8c10004dd7698c100065e6598c100065d6598c10014f47158c1000cdf7658c100065e6558c100065d6558c100065e5458c100065c5458c10016d77158c10006d47158c1001c7e75d88100047d75d881000cde73d8810004dd73d881001c7e75188100047d7518810004be7418810004bd741881000cde7318810004dd731881001c7e75984100047d7598410004be7498410004bd74984100047d76d44100665e63d44100065d63d44100047f76544100053c745441005e5e63544100065d6354410015d673c8410004f576084100067965d4010005ba74d40100047f76940100047d76940100565e63940100065d63940100057571940100057a709401001c7f76140100047d761401004e5e63140100065d6314010005757114010004f976140100067a76140100057976140100067976140100047976140100057a74140100075a63140100075963140100077271140100057971140100077171140100067a61140100977331140100977031140100077321140100077021140100057a75d0010006d963d00100063e65900100063d65900100469e63900100069d6390010005ba70900100073850900100063e65100100063d651001003e9e63100100069d63100100073a5010010007385010010004f976100100057875100100073a5410010007385410010006d96310010006ba7610010006b976100100073b75100100073875100100073a6510010007396510010006bb63100100079a6310010006b96310010007996310010006996310010006ba6210010006b86210010007b27110010007b17110010006ba61100100073b511001000739511001008fb3311001008fb03110010007b32110010007b021100100077050c4010007b040c401000cf97684010005787584010004f77644010015d47344010005e47244010004fb7644010005787544010005b87444010
  | 1 => 0x961001e7a701961001c7e75d92100047d75d921000cde73d9210004dd73d9210004ee72d9210004ed72d921001c7e75992100047d75992100047f755921001c7c75592100047e76952100047c76952100047e761521001c7c76152100063e64152100063d64152100047f7558e1001c7c7558e1001c7e7598a100047d7598a10004be7498a10004bd7498a100047f7558a1001c7c7558a10004df7358a1000cdc7358a1000cde7318a10004dd7318a100057a70d46100053c7454610005787054610025d673c86100057571942100057571142100063f65902100063c65902100063f65102100063c65102100067865c421001c7e76d95100047e74d9510004bf7459510004bc7459510004df735951000cdc7359510004ef7259510004ec7259510004fb70595100047e76195100047e74195100547e701951001c7c701951001c7e75d91100047d75d91100063f65d91100063c65d91100063e75d91100063d75d911001c7e75991100047d7599110004be749911000cde7399110004dd7399110004ee7299110004ed72991100047f755911001c7c7559110004df735911000cdc7359110004ef7259110004ec7259110004fb7059110004be76191100063f65191100063c65191100063f75191100063c7519110044be701911003cbc70191100047e76951100047c76951100063f64951100063c64951100865c63951100047e761511001c7c76151100063f64151100063c641511007e5c631511000cde76d8d100065f65d8d100065c65d8d100069f64d8d100069c64d8d100065e54d8d100065c54d8d100047f7558d1001c7c7558d10004bf7458d10004bc7458d10004ef7258d10004ec7258d10024f77158d10004de7618d100065f6518d100065c6518d100069f6418d100069c6418d100066f65d89100066c65d8910006af64d8910006ac64d8910006cf63d8910006cc63d89100066e54d89100066c54d891001c7e75989100047d7598910004be7498910004bd749891000cde7398910004dd7398910004ee72989100047f755891001c7c7558910004bf7458910004bc7458910004df735891000cdc7358910004f77158910004ee76189100066f65189100066c6518910006af6418910006ac6418910006cf6318910006cc63189100066e54189100066c54189100047e76d45100063f64d45100063c64d45100065f63d45100665c63d45100066f62d45100066c62d45100057a70d45100047c76545100053c74545100063f64545100063c64545100065f635451005e5c63545100066f62545100066c62545100057870545100047e76941100063f64941100063c64941100065f63941100565c63941100066f62941100066c62941100047e76141100063f64141100063c64141100065f631411004e5c63141100066f62141100066
  | 2 => 0x47d7598820004be7498820004bd749882001c7e75984200047d75984200665e63d44200065d63d44200053c745442005e5e63544200065d635442000578705442002dce7388420006cd6388420006cd63084200565e63940200065d639402004e5e63140200065d6314020006d963d00200469e63900200069d6390020005ba709002003e9e63100200069d63100200073a5010020007385010020004f976100200073a5410020007385410020006d96310020006ba7610020006b976100200073b7510020007387510020006bb63100200079a6310020006b96310020007996310020006996310020007aa7210020007a97210020006ba621002009fab321002009fa83210020006ba61100200073b5110020007395110020007aa2110020007a82110020007a840c8020004ef764802002dcc7348020005e47148020004fb7648020005b87448020004be74d9710004bd74d97100047e7499710004df735971000cdc73597100047c74597100065f73597100065c73597100067b705971001c7e75d93100047d75d93100063e65993100063d65993100063f75993100063c75993100047f755931001c7c7559310004df735931000cdc73593100063e65593100063d65593100063f75593100063c75593100069f73593100069c7359310006bb705931001c7e75193100047d75193100047f76953100047d76953100063e64953100063d64953100057a709531001c7f76153100047d76153100063e64153100063d641531001c7e75d8f100047d75d8f10004be74d8f10004bd74d8f10004ee72d8f10004ed72d8f1001c7e75d8b100047d75d8b10004be74d8b10004bd74d8b1000cde73d8b10004dd73d8b1000cde7398b10004dd7398b1001c7e7518b100047d7518b10004be7418b10004bd7418b100063e64d47100063d64d47100053c74547100063e64547100063d6454710005787054710005ba74d43100063e64943100063d64943100063e64143100063d64143100067965143100057976143100067976143100057a74143100073a64143100073964143100057971143100057a75d03100063e65903100063d65903100073850903100063e65103100063d65103100073a5010310007385010310005787510310006b964103100073a5410310007385410310005b97610310006b976103100073b75103100073875103100073a6510310007396510310006bb6310310006b96310310006ba6210310006b862103100073b5110310007395110310004be74d9610004bd74d961000cde73d9610004dd73d9610004ee72d9610004ed72d96100053e74d96100047e74d96100063e74d96100043e74d96100063d74d96100065e73d96100065d73d96100066e72d96100066d72d96100067571d96100067a70d96100047e741961001e75711
  | 3 => 0xd7498620004df735862000cdc73586200053c7454620005787054620035ce738862001c7e76d95200047e74d95200047d71d9520004bf7459520004bc7459520004df735952000cdc7359520004f77159520004f471595200047e76195200047e74195200047d711952001c7e75d91200047d75d91200063f65d91200063c65d91200063e75d91200063d75d912001c7e75991200047d7599120004be749912000cde7399120004dd7399120004f67199120004f571991200047f755912001c7c7559120004df735912000cdc7359120004f77159120004f47159120004fb7059120004be76191200063f65191200063c65191200063f75191200063c75191200047e76951200047c76951200063f64951200063c64951200865c63951200047e761512001c7c76151200063f64151200063c641512007e5c631512000cde76d8d200065f65d8d200065c65d8d200069f64d8d200069c64d8d200065e54d8d200065c54d8d200047f7558d2001c7c7558d20004bf7458d20004bc7458d20034ef7258d20004f77158d20004f47158d20004de7618d200065f6518d200065c6518d200069f6418d200069c6418d200067765d85200067465d8520006b764d8520006b464d8520006d763d8520006d463d85200067775d85200067475d85200067654d85200067454d852001c7e75185200047d7518520006776518520006746518520006b76418520006b46418520006d76318520006d463185200067675185200067575185200067654185200067454185200047e76d452001c7c76d45200063f64d45200063c64d45200065f63d45200665c63d45200067761d45200067461d45200047e76545200047c76545200053c74545200063f64545200063c64545200065f635452005e5c63545200067761545200067461545200057870545200047e76941200063f64941200063c64941200065f63941200565c63941200067761941200067461941200047e76141200063f64141200063c64141200065f631412004e5c6314120006776114120006746114120004be76901200063f65901200063c65901200069f63901200469c6390120006b76190120006b46190120004be76101200063f65101200063c65101200069f631012003e9c6310120006b76110120006b46110120006b864c8120036cc6388120006e46188120004be74d9420004bd74d942000cde73d9420004dd73d942001c7e75d90200047d75d902000cde73d9020004dd73d90200047f755902001c7c755902000cde7319020004dd73190200865e63950200063e64150200063d641502007e5e6315020004dd7698c200047f7558c2001c7c7558c2002cec7258c2000cdf7658c200065f7558c200065c7558c200065e5458c200065c5458c2002ecf7258c20006cc7258c2001c7e7598820
  | 4 => 0x41300063f64941300063c64941300066f62941300066c62941300067761941300067461941300575830941300547e76141300063f64141300063c64141300066f62141300066c621413000677611413000674611413000cfa76d0130006e862d0130006f061d013003cbe76901300063f65901300063c6590130006af6290130006ac6290130006b76190130006b4619013003dba7090130044be76101300063f65101300063c6510130006af6210130006ac6210130006b76110130006b461101300073a501013000738501013003f983010130006bb64101300073a54101300073854101300079b431013003f984310130006e86210130006f06110130045ba7610130006ba76101300073b75101300073875101300073b65101300073865101300079b731013003f98731013003ebb63101300079b531013003f985310130007ab6210130006b86210130007a86210130006a8621013003f9b3210130007993210130007b36110130006b86110130007b06110130006b061101300073b511013000739511013003f9b3110130007993110130006cc628c130006d4618c13000798408c130004be74d9720004bd74d97200047e74997200047d7199720004df735972000cdc73597200047c74597200065f73597200065c73597200047f715972001c7e75d93200047d75d93200063e65993200063d65993200063f75993200063c75993200047f755932001c7c7559320004df735932000cdc73593200063e65593200063d65593200063f75593200063c75593200069f73593200069c7359320006bb705932001c7e75193200047d75193200047f76953200047d76953200063e64953200063d649532001c7f76153200047d76153200063e64153200063d641532001c7e75d8f200047d75d8f20004be74d8f20004bd74d8f20004f671d8f20004f571d8f2001c7e75987200047d759872000cde7398720004dd739872001c7f76d47200047d76d47200063e64d47200063d64d47200047f76547200047d76547200053c74547200063e64547200063d64547200057870547200063e64943200063d64943200063e64143200063d64143200063e65903200063d65903200063e65103200063d65103200073a5010320007385010320006b964103200073a5410320007385410320005b97610320006b976103200073b75103200073875103200073a6510320007396510320006bb6310320006b96310320006ba61103200073b511032000739511032000cde73d9620004dd73d9620004bf7459620004bc745962001c7e75d92200047d75d922000cde73d9220004dd73d9220004f671d9220004f571d92200047f755922001c7c75592200063f64152200063c641522001c7e75d8e200047d75d8e2001c7e75986200047d7598620004be7498620004b
  | 5 => 0x4bd76d404003d9e73940400059d73940400071e73940400071d73940400053d71940400053e70940400063e60940400073a6094040004bf76540400053e76140400053c76140400053d71140400053e70140400073a70140400063e60140400073a601404001c7e75d92300047d75d92300047f755923001c7c755923001c7e75986300047d7598630004ef7258630004ec72586300053c74546300057870546300073a501023000738501023000cf976102300073a5410230007385410230006ba761023003eb976102300073b751023000738751023003f9a7310230007997310230006ba62102300079a321023003f983210230006ba61102300073b51102300073951102300079a311023003f98311023001c7e76d95300047e74d95300565e73d95300065d73d95300047d71d9530004bf7459530004bc7459530004ef7259530004ec7259530004f77159530004f471595300547e76195300047e74195300047d711953001c7e75d91300047d75d91300063f65d91300063c65d91300063e75d91300063d75d91300469e73d91300069d73d9130046b970d913001c7e75991300047d759913003cbe7499130004ee7299130004ed7299130004f67199130004f571991300047f755913001c7c7559130004ef7259130004ec7259130004f77159130004f47159130044be76191300063f65191300063c65191300063f75191300063c75191300047e76951300047c76951300063f64951300063c64951300047e761513001c7c76151300063f64151300063c6415130004de76d4d30005da70d4d30004de76d0d300066f65d89300066c65d8930006af64d8930006ac64d89300066e54d89300066c54d89300066f65189300066c6518930006af6418930006ac64189300066e54189300066c541893002ece7318930006cf531893002ecc5318930006cf431893002ecc431893002ecf311893002ecc30189300055c754c930006cc624c9300067765d85300067465d8530006b764d8530006b464d8530006e762d8530006e462d85300067775d85300067475d85300067654d85300067454d853001c7e75185300047d7518530006776518530006746518530006b76418530006b46418530006e76218530006e46218530006767518530006757518530006765418530006745418530016d67318530006d75318530016d45318530006d74318530016d44318530016d73218530006d53218530016d430185300047e76d453001c7c76d45300063f64d45300063c64d45300066f62d45300066c62d45300067761d45300067461d45300047e76545300047c76545300053c74545300063f64545300063c64545300066f62545300066c6254530006776154530006746154530005787054530006cc624c530006d4614c530005d8704c53004c7e769
  | 6 => 0xc75504400059f735044003d9c7350440005af7250440005ac7250440005bb70504400053e75104400053d75104400063c651044001c7e75980400047d75980400063e54980400063c549804000cde73980400053e74940400047e761404001c7c76140400053e74140400053e75d00400053d75d00400073a5490040007385490040005d97390040004bf76500400053f75500400053c7550040004fb765004003d9e73d94400059d73d9440005ae72d9440005ad72d9440005ba70d94400071e73d94400071d73d94400072e72d94400072d72d94400053d71d94400053e70d94400073a70d94400053a70d9440005ba70194400063e76194400053d71194400053e70194400073a70194400053a7019440005ba70d8c400053f7558c400053c7558c400063c65d8840005ba70d88400053e75988400053d75988400053f75588400053c75588400063c65588400059f735884003d9c7358840005b77158840005b4715884003d9e73188400059d7318840006ad6218840005ba7018840005ba70d4840005b970d4840004be7694840004bd76948400059f735484003d9c7354840005bb7054840005b870548400053f754c8400053c754c840005bb704c840005b8704c840005ba70d84400053e75984400053d75984400063c65984400053f75584400053c75584400059f735844003d9c7358440005af7258440005ac72584400053e75184400053d75184400063c651844003d9e73184400059d7318440005ae7218440005ad7218440005ba7018440005ba70d4440005b970d44400053e76d44400053c76d44400053e70d44400073a70d44400053a70d44400073970d44400053d7594440004bf7654440004bc76544400059f735444003d9c7354440005af7254440005ac7254440005bb7054440005b870544400063f76544400053e76544400053c76544400063c76544400043c76544400071f73544400071c73544400072f72544400072c72544400073771544400073b70544400053c70544400073870544400053870544400053e75144400053e758c4400053d758c440005bb704c440005b8704c44003d9e73c84400059d73c8440005ba70c8440005b970c84400053e75884400053d758844003d9e73884400059d7388440005ba7088440005b97088440005bb7048440005b87048440004be7608440004bd76084400053e75084400053d75084400053e75980400053d75980400063f65980400063c659804003d9e73980400059d73980400063e75980400063d75980400469e73980400069d73980400063f51980400063d5198040006ba70980400073a75980400073975980400073b65980400073865980400079a7398040005b97398040007997398040005997398040005ba7298040005ba71980400073b5198040007395198040
  | 7 => 0x86400053e75986400053d75986400063e65986400053e75186400053d75186400063e65186400459e73186400059d7318640005ba70186400053f76d46400053d76d46400071e63d46400071d63d46400053e70d4640004bf7654640004bc76546400059f73546400459c7354640005af7254640005ac7254640005bb7054640005b870546400053f76546400063f76546400043f76546400053d76546400063c76546400071f73546400071c73546400071e63546400071d63546400072f72546400072c72546400073771546400073b70546400053c70546400073870546400053870546400053e758c6400053d758c6400459e73c86400059d73c86400053e75886400053d75886400459e73886400059d7388640004be7608640004bd76086400053e75086400053d75086400459e73942400059d73942400073b50942400053d76942400071e73942400071d73942400071e63942400071d63942400053d71942400053d76142400071e63142400071d63142400053d71142400073a701424001c7e76d95400047d71d9540004bf74595400047e76195400847e741954001c7c74195400047d71195400047e76951400047e761514001c7e75185400047d75185400047e76d454001c7c76d45400047e76545400047c76545400053c74545400057870545400047e76941400047e76141400063f65901400063c659014000cde73d9440004dd73d9440004ee72d9440004ed72d94400047e74d94400063e74d94400065e73d94400065d73d94400066e72d94400066d72d94400047d71d94400047e70d94400067a70d94400047e741944001e3e74194400047d71194400047e701944001e7a701944001c7e75990400047d75990400053e74950400057a709504001cbd769504001e3e76950400063d76950400053d71950400073a70950400073970950400053e74150400057a7015040004bd76150400063e76150400063d76150400053d71150400073a70150400073970150400047f7558c4001c7c7558c4000cbd76d0c400053f7550c400053c7550c4001c7e75988400047d75988400047f755884001c7c75588400063c5458840004df735884000cdc7358840004f77158840004f471588400063c65d0840005b970d08400053e75908400053d75908400053f75508400053c75508400063c65508400059f735084003d9c7350840005b77150840005b47150840005bb7050840006ad621084001c7e75984400047d75984400063c54984400047f755844001c7c7558440004df735844000cdc7358440004ef7258440004ec72584400047e76d44400053e74d44400057a70d44400047c76544400053c74544400057870544400053f75d04400053c75d0440005b970d04400053e75904400053d75904400063c65904400053f75504400053
  | 8 => 0x1c7e76104500047d761045001c7e768c4500047d768c4500057b704c45000578704c45004d5e73c84500055d73c84500057a70c84500057970c845001c7e76884500047d768845004d5e73884500055d73884500057b704845000578704845001c7e76084500047d76084500053e74084500053d740845004d5e73980500055d73980500565e73980500065d739805001e7a70980500075a73980500075973980500057a71980500047d71997400047f71597400057a70953400057a701534001c7e75987400047d759874001c7f76d47400047d76d47400057a70d47400047f76547400047d76547400053c745474000578705474000cde73d9640004dd73d964001e3d74996400047d71996400063f74596400047f7159640005b970d52400865e639524001e3e65952400053d76952400063d76952400053d719524001cbf765524007e5e63152400063d65152400053d76152400063d76152400053d71152400065e6598e400065d6598e400071e5498e400071c5498e400065e6558e400065d6558e400071e5458e400071c5458e400469c7458e400065e5458e400065c5458e4000e9e63d0e4000cbf7650e400053f7550e400053c7550e400063c5458a400063e65d0a400053e7590a400053d7590a400053f7550a400053c7550a400063e6550a400059f7350a400459c7350a40006ae6250a40005b77150a40005b47150a4001c7e75986400047d75986400063c549864001c7f76d46400047d76d46400053e74d46400665e63d46400065d63d46400047f76546400047d76546400053c745464005e5e63546400065d63546400057870546400053f75d06400053c75d06400053e75906400053d75906400063e65906400053f75506400053c75506400059f73506400459c7350640005af7250640005ac7250640005bb70506400053e75106400053d75106400063e65106400053e74942400565e63942400065d63942400053e741424004e5e63142400065d63142400053e75d02400053d75d02400073a50d02400073a54d0240006d963d02400459e73d96400059d73d9640005ba70d96400053d71996400063f76596400053f71596400459e73196400059d7319640005ba70196400053e75d8e400053d75d8e40005ba70d8e400071e6598e400071d6598e400469f7658e400071e6558e400071d6558e400053e75d8a400053d75d8a400063e65d8a400459e73d8a400059d73d8a40005b671d8a40005b571d8a40005ba70d8a40006af6298a400063e6558a400053e7518a400053d7518a400459e7318a400059d7318a40005ba7018a40004be7694a40004bd7694a400059f7354a400459c7354a400053f754ca400053c754ca400053e75d86400053d75d86400459e73d86400059d73d8640005ae72d8640005ad72d8640005ba70d
  | 9 => 0xd72192500057a70192500565e63d8e500057a70d8e500065e6498e500065c6498e500565c6358e500565f7658e500065e6458e500065c6458e500047f7650e500047c7650e500555e73d8a500055d73d8a500057a70d8a500065e6398a500053e7418a500053d7418a500555e7318a500055d7318a500065e6318a500057a7018a500063e64d0a500047e7690a500047d7690a500047f7650a500047c7650a500063e6450a500055f7350a500555c7350a50005777150a50005747150a500057b7050a50005787050a500047f764ca500047c764ca500053e74d86500053d74d86500555e73d86500055d73d86500065e63d86500065d63d86500056e72d86500056d72d86500057a70d86500065e63586500065d63586500047c74586500555e73186500055d73186500057a70186500047f76d06500047e76906500047d76906500063e64906500047f76506500047c76506500055f73506500555c73506500056f72506500056c72506500057b70506500057870506500047e76106500047d76106500063e64106500047e768c6500047d768c6500555e73c86500055d73c86500047e76886500047d76886500555e73886500055d73886500047e76086500047d76086500053e74086500053d74086500063f75191500063f64951500063c64951500047e76151500063f64151500047e76d45500063f64d45500063c64d45500053c74545500063f64545500063c64545500067761545500057870545500063f64941500063c649415001e3c54990500047f765505001e5c5358c50004be7498850004bd7498850004df735885000cdc73588500053e74948500053d74948500055f735485004d5c7354850004bf7458450004bc7458450004df735845000cdc7358450004ef7258450004ec725845001e7751584500047d76944500053f74544500053c74544500055f735445004d5c73544500056f72544500056c72544500057b705445000cde73980500047f76540500053f74540500053c74540500047d719905001e5c6358c500047f7650c5001c7c7650c500053e74988500053d74988500055f735885004d5c735885001c7e76908500047d76908500047f765085001c7c76508500055f735085004d5c73508500057771508500057471508500057b70508500057870508500047f764c85001c7c764c8500053f74584500053c74584500055f735845004d5c73584500056f72584500056c72584500063f74584500047c74584500063c74584500043c74584500065f73584500065c73584500066f72584500066c72584500067870584500047f76d04500057a70d04500057970d045001c7e76904500047d76904500047f765045001c7c76504500055f735045004d5c73504500056f72504500056c72504500057b7050450005787050450
  | 10 => 0x9521004f8705952101c7e75d91210047d75d91210047f755912101c7c7559121004df735912100cdc7359121004ef7259121004f77159121004fb7059121004f870591210063f64151210063c64151210047f7558d2101c7c7558d21004bf7458d21004bc7458d21004fb7058d21004f87058d210053c745452100578705452101c7e75d81210047d75d8121004be74d8121004bd74d812100cde7318121004dd7318121004be74d9421004bd74d94210047d76994210047e74994210047e7099421004df735942100cdc735942101c7f76594210047c74594210065f73594210065c73594210066c72594210047c705942101c7e75d90210047d75d9021004bd76990210063e65990210063d65990210063f75990210063c7599021004be70990210047f755902101c7c7559021004df735902100cdc7359021004fb7059021004f870590210063e65590210063d6559021005b870590210063f75590210063c75590210069f73590210069c7359021006ac7259021006b47159021006bb7059021004bc7059021006b87059021004b8705902101c7e75190210047d7519021004be74190210047f76950210047d76950210063e64950210063d649502101c7f76150210047d76150210063e64150210063d641502101c7e75d8c210047d75d8c21004be74d8c21004bd74d8c2100cde7398821004dd73988210066d65d4821004ed7614821005e57114821006ad64d08210072c54d0821004ed761082100ced768c8210056c754c82101c7e75984210047d759842100cde7398421004dd73984210047d76d44210063e64d44210063d64d44210047f76544210053c74544210063e64544210063d6454421005787054421006b564d0421007a742d0421004f57610421007345410421005cd73c8421004ef7648421007655148421004f776484210047f755802101c7c7558021004bf7458021004bc7458021004df735802100cdc735802101e3c549935001e3c759935001e3f519935001e3c509935001e3c545935001e3f515935001e3c50593500063d649535001e7751587500053c74547500063e64547500063d64547500057870547500063e64952500865e639525000579709525007e5e63152500565e5358e500565c7558e500065e5458e500065c5458e5000e5e63d4e5000c7f7654e5000e5e6354e500053e7494a500053d7494a500765e6394a500055f7354a500555c7354a500057b7054a5006e5e6314a500665e63d46500065d63d46500053f74546500053c74546500055f73546500555c735465005e5e63546500065d63546500056f72546500056c72546500067561546500057b70546500053e74d42500053d74d42500555e73d92500055d73d92500057a70d92500047d71992500555e73192500055d73192500056e72192500056
  | 11 => 0x63c54984410047d76d44410047f76544410053c74544410057870544410053c75d0441007345490441004bf76504410053c7550441005b87050441004f77650441005e472504410063c54980410047f755804101c7c755804105c7d76996310047e74996310047e709963101c7f76596310047c74596310065f735963105e5c73596310047c705963101c7e75d92310047d75d92310047f755923101c7c7559231004fb7059231004f8705923101c7e75192310047d7519231004ee7219231004ed72192310047f76952310047d769523101c7f76152310047d76152310055c754ca3105c7d76d46310647f76546310053c74546310057870546310047f755823101c7c7558231004bf7458231004bc7458231004bf7459531004bc7459531004df7359531004ef7259531004ec7259531004fb7059531004f8705953101c7e75d91310047d75d91310047f755913101c7c7559131004df7359131004ef7259131004ec7259131004fb7059131004f870591310063f64151310063c6415131006cf628c9310053c745453100578705453101c7e75d81310047d75d8131004be74d8131004bd74d8131004be74d9721004bd74d972100cde73d9721004dd73d9721004fa70d9721004f970d972101c7e75d93210047d75d932100cde73d9321004dd73d9321004fa70d9321004f970d93210047f755932101c7c755932100cde7319321004dd73193210865e63953210063e64153210063d641532107e5e63153210047f7558f2101c7c7558f210065f7558f210065c7558f210065e5458f210065c5458f210665e63d47210065d63d47210053c745472105e5e63547210065d63547210057870547210073454107210047f755832101c7c7558321004bf7458321004bc745832100cde73d9621004dd73d96210047e74996210047e7099621004bf7459621004bc74596210053c74596210063f74596210047c74596210063c74596210043c74596210066f72596210047c705962101c7e75d92210047d75d922100cde73d9221004dd73d9221004fa70d9221004f970d92210047f755922101c7c755922101c7e75192210047d751922100cde7319221004dd73192210047f76952210047d76952210865e639522101c7f76152210047d76152210063f64152210063c641522107e5e631522101c7e75d8e210047d75d8e210065e6598e210065d6598e210065e6558e210065d6558e210065e5458e210065c5458e210066d6514a210072c54d0a2100ece638ca2100cef764ca210056c754ca210665e63d46210065d63d46210053c745462105e5e63546210065d6354621005787054621005cd73c86210047f755822101c7c7558221004bf7458221004bc7458221004bf7459521004bc7459521004df735952100cdc7359521004ef7259521004fb705
  | 12 => 0xe73d9741004dd73d9741004ee72d9741004ed72d9741004fa70d9741004f970d97410057a70d97410063e74d97410065e73d97410065d73d97410066e72d97410066d72d97410067571d97410047e70d97410067a70d97410047a70d97410067970d974101e3e741974101e7571197410047e70197410057571953410057571153410047f7558f4101c7c7558f4101c7e7598b410047d7598b410047f7558b4101c7c7558b41004df7358b4100cdc7358b410063c65d0b41006ae62d0b410063c6550b41005b47150b41005b87050b410053e74d47410053c745474100578705474101c7e75983410047d759834100cde7398341004dd73983410047f755834101c7c75583410047e70996410063f74596410047c7059641005b571d52410063d65152410053d76152410063d76152410053d71152410053e70152410063c5458a410053c74546410057870546410053c75d06410073551d06410073654d06410063c54982410047f755824101c7c755824101c7e76d95410047e70d9541004bf7459541004df735954100cdc7359541004ef7259541004ec7259541004fb7059541004f870595410047e76195410047e70195410047e76951410865c63951410047e761514107e5c631514100cde76d8d410065f65d8d410065c65d8d410065e54d8d410065c54d8d410065f6518d410065c6518d410066f65d89410066c65d8941006cf63d8941006cc63d89410066e54d89410066c54d89410066f65189410066c6518941006cf6318941006cc63189410066e54189410066c54189410063c65d0941006ac62d09410063c6550941006ac6250941005b47150941005b870509410047e76d45410053e74d45410065f63d45410665c63d45410066f62d45410066c62d45410047c76545410053c74545410065f635454105e5c63545410066f62545410066c6254541005787054541006e462d05410063c659054101c7e75d81410047d75d81410067b65d81410067865d8141006db63d8141006d863d8141006eb62d8141006e862d81410067a75d81410067975d81410067a54d81410067854d81410067b51d81410067951d81410067b6518141006786518141006db6318141006d86318141006eb6218141006e862181410067b7518141006787518141006bb74181410067a5418141006785418141006bb4218141006b942181410067b5118141006795118141006ba41181410047d76994410047e709944101c7f76594410063c74594410047c70594410063d65d50410047f76950410047d76950410053e749504100575719504101c7f76150410047d7615041005757115041004bd76150410063e76150410063d76150410043d76150410073671150410053d71150410073571150410053e70150410063c545884101c7e75984410047d7598441
  | 13 => 0x89510053f74589510053c74589510063c64589510055f735895105d5c73589510057771589510057b70589510057870589510063c64189510065c63189510066d62189510056e76189510066e76189510072f64189510066e64189510066c64189510072c64189510062c64189510074f63189510066e63189510066c63189510074c63189510064c63189510063c64d09510047e76909510047d76909510063c64909510047f76509510047c76509510063c64509510055f735095105d5c73509510057771509510057471509510057b70509510057870509510063c64109510063c648c9510047f764c9510047c764c9510063c644c9510063f64d85510063c64d85510065f63d85510665c63d85510066f62d85510066c62d85510073764d85510073464d85510075763d85510075463d85510076762d85510076462d85510053e74d81510053d74d81510063c64d81510073a74d81510073974d81510073b64d81510067a64d81510067864d81510073864d81510063864d81510075b63d81510075863d81510076b62d81510076862d81510067b61d81510077361d81510053e74981510053d74981510063f64981510063c649815105d5e73981510055d73981510065f63981510065c63981510056e72981510056d72981510066f62981510066c62981510057a70981510067b60981510053f74581510053c74581510063c64581510055f735815105d5c73581510056f72581510056c72581510063f64181510063c64181510065f63181510065c63181510066f62181510066c62181510067960181510063f74181510047e74181510063c74181510067b30181510067830181510057a76181510067a76181510073b74181510073874181510067b64181510073b64181510063b64181510067a64181510067964181510067864181510073864181510063864181510067b63181510075b63181510065b63181510067a63181510067963181510067863181510075863181510065863181510067b62181510076b62181510066b62181510067a62181510067962181510067862181510076862181510066862181510067b61181510077361181510067b74181510063b74181510067a74181510067974181510067874181510063874181510067b73181510067a73181510067973181510067873181510067b43181510067a43181510067943181510067843181510067b72181510067a72181510067972181510067872181510067b42181510067a42181510067942181510067842181510067b32181510067a32181510067932181510067832181510067b71181510067b311815100678311815101e75719945101e3c54990510047d76950510047f76544510053c745445100578705445101e785098051004bf7458051004bc745805100cd
  | 14 => 0x5e5e53d8d5100cde76d8d510069f64d8d510069c64d8d5105e5e75d8d510065e54d8d510065c54d8d510069f6418d510069c6418d510063c64d4d5100e5c63d4d5100c7c7654d510063c6454d5100e5c6354d51006af64d8951006ac64d8951006cf63d8951006cc63d89510066e54d89510066c54d8951006af6418951006ac6418951006cf6318951006cc63189510066e54189510066c54189510066e53189510066c53189510063c64d49510066c62d49510053e74949510053d74949510063c64949510765c63949510066f62949510063c64549510055f735495105d5c73549510066c62549510063c641495106e5c63149510066f62149510063c6494551004be74d8151004bd74d8151006bb64d8151006b864d8151006db63d8151006d863d8151006eb62d8151006e862d8151006ba74d8151006b974d81510067a54d81510067854d8151006bb6418151006b86418151006db6318151006d86318151006eb6218151006e862181510067b7518151006bb7418151006b874181510067b54181510067a54181510067954181510067854181510067b53181510067a53181510067953181510067853181510067b52181510067a52181510067952181510067852181510067a51181510053e70d91510053e74991510063f649915105d5e73991510055d73991510056e72991510056d72991510057571991510057a70991510057970991510055f735915105d5c73591510056f72591510056c72591510057771591510057b70591510057870591510063d64191510063e43191510063c43191510047e70191510053e76191510063e76191510063e63191510063c63191510053e70191510063f73191510063e73191510063d73191510063c73191510063f72191510063e72191510063d72191510063c72191510063f32191510063c32191510063f71191510063d71191510063f31191510063c31191510063f70191510063e70191510043e70191510063d70191510063c70191510063f30191510063c30191510063c64d8d5105e5e63d8d5105d5e76d8d510071f64d8d510065e64d8d510065c64d8d510071c64d8d510061c64d8d510053f7458d510053c7458d510063c6458d5105e5c6358d510056f7258d510056c7258d51005777158d510057b7058d51005787058d510055e7618d5105e5e7618d510071f6418d510065e6418d510065c6418d510071c6418d510061c6418d510063c64d0d510047f7650d510047c7650d510063c6450d510063c64d89510072f64d89510066e64d89510066c64d89510072c64d89510062c64d89510074f63d89510074c63d89510053e74989510053d74989510063c649895105d5e73989510055d73989510065c63989510056e72989510066f62989510057571989510057a709895100579709
  | 15 => 0x75418542006765418542006745418542006b45418542006345418542006e7421854201c7e75d81420047d75d81420067b65d81420067865d81420073854d8142006db63d8142006d863d8142006f361d8142006f061d81420067a75d81420067975d81420067a54d81420067854d81420063c54181420067b6518142006786518142007385418142006db6318142006d86318142006f36118142006f061181420067b7518142006787518142006bb7418142006bb54181420067a5418142006785418142006b85418142006385418142006ba4218142004be74d94420063e64150420047f7558c4201c7c7558c4201c7e75988420047d7598842004bf7650842005b87050842004ef7650842005e4715084201c7e75984420047d75984420047f755804201c7c7558042004be74d9632004bd74d963201c7e75d92320047d75d92320047f755923201c7c7559232004fb7059232004f870592320063e64152320063d641523201c7e75986320047d75986320047f755823201c7c7558232004bf7458232004bc745823201c7e76d95320047e74d95320047d71d95320047e70d9532004df73595320747e76195320047e741953206e5c32195320047d711953206e5c31195320047e701953206e5f301953201c7e75d91320047d75d913201c7e75991320047d75991320047f755913201c7c7559132004df7359132004f77159132004f47159132004fb7059132004f870591320047e76951320047c76951320047e761513201c7c76151320065c658c93201c7e75185320047d751853201c7e75d81320047d75d8132004be74d8132004bd74d813201e3f549935101e3c549935101e3c545935101e5c5358f51004be7498b51004bd7498b5101e6f5298b51004df7358b5100cdc7358b5101e6c5258b510053e7494b510053d7494b510055f7354b510655c7354b5100cde7398351004dd739835101e7b509835101e785098351004bf7458351004bc745835101e78505835101e3f64993510047e709935101e3c645935101e5c6358f510047f7650f5101c7c7650f510053e7498b510053d7498b5101e6f6298b510055f7358b510655c7358b5101e6c6258b5101c7e7690b510047d7690b510047f7650b5101c7c7650b510055f7350b510655c7350b51005777150b51005747150b510057b7050b51005787050b510047f764cb5101c7c764cb510655e73983510055d739835101e7b60983510047e74983510065e73983510065d73983510053f74583510053c745835101e7860583510063e6495251005757195251004bf7458251004bc7458251004be70d91510063f75191510063e53191510063c5319151004be70191510047e76d51510063c64d51510063f64951510063c64951510865c63951510063c64551510063f641515107e5c6315151
  | 16 => 0x84540067b70584540047c70584540067870584540047870584540063e649805407d5e73980540055d739805401e7b60980540063c74980540065e73980540065d73980540047d719805401e3c549935300c7c755935300c7e7598753004ef7258753004ec725875301e77515875301e78509835300c7c7558353004bf7458353004bc745835300c7e76951530063c6495153004be74d8153004bd74d8153004ee72d9743004ed72d97430871e439534301c7e75987430047d7598743004ef7258743004ec72587430047f755834301c7c755834301c7e76d95430047d71d95430047e70d95430847e76195430047d71195430047e701954307c7e76951430847e761514301c7e75185430047d751854301c7e75d81430047d75d814301e3c549935201e775198752004df735875200cdc735875201e77515875200cde7398352004dd739835201e785098352004bf7458352004bc74583520063f75992520063e53992520063c5399252004be7099252004bc70592520063e64952520063d64952520056d72952520063d64152520063e64d4a52004bf7458252004bc74582520063c64951520865c639515207e5c631515200cde76d8d520065e54d8d520065c54d8d520053e74949520765c6394952004be74d8152004bd74d815201e3c549905201e3c54590520047f765485206d5c735485201e77515845201e785098052004bf7458052004bc745805200cde73d9742004dd73d9742005ae72153420063e76153420063d76153420072e72153420072d72153420053d71153420053e701534201c7e75987420047d75987420063c5498742004df735874200cdc73587420063c549834200cde7398342004dd73983420047f755834201c7c75583420047d71996420047e70996420047f71596420047c70596420063e65d0a420072e54d0a4201c7e75986420047d75986420047f755824201c7c755824201c7e76d95420063d74d95420047d71d95420047e70d9542004df735954200cdc7359542004f77159542004f47159542004fb7059542004f870595420047e76195420047d71195420047e7019542004be76d51420047e76951420053e74951420865c63951420047e761514207e5c63151420063f65151420053e76151420063e76151420053d71151420053e701514200cde76d8d420065f65d8d420065c65d8d420071c54d8d420065e54d8d420065c54d8d420065f6518d420065c6518d420071c5418d420072c54d09420053e75909420067765d85420067465d85420073454d8542006d763d8542006d463d85420067775d85420067475d85420067654d85420067454d854201c7e75185420047d75185420063c5418542006776518542006746518542007345418542006d76318542006d46318542006767518542006757518542006b
  | 17 => 0x800100601000000700000400300000000200700101700000f00a00000500000600000000700201b00100400600100000300000600000300900000200900001600100000d00800d00300f00700700100100a01101b00101200a00000300300100000600100300200a01a00500200000000d00900400200200d00200201200400000a00000b00000700e00000900900400100200802000400f00600200003501f00100001100700600400000600000000100000600300100400000100000100300300600000300000b00200300500000100401e00b00600000000000100300400200200200300000000100302300400000500100700d00000000200400100f00900000700300100101000000000f00700000000200800f00702400a00000800001200100000600400600400500a00c00f00a01500400800000300100100d00b00900300500800600a00c00000500000500000000a00000700200100500400000000000101600100a00000100800300200300100600000100200000800200300400400000002d00000000500c00000000400400102101100000100500000800e00000101e00000300300500500301000000200000000000200000000000100200000300000600c00800500200000d00100000100200000200100b00603200e00000000300700500000d00d00400100400200000100000c00f00100900700600300300f00a00101601000c00700700000000e00602800100202302500300300700200200000d00000000000000900202300000200200a00001000000800200600c00600000600400100400200100200000301700300000501500a00201b01a00100000600900600000000600000300300000400001000100200200b00000000101200a00100800100200001300500200d01300100000700100000100a00f00300d00400000401e77515875401e7850983540865e5358e540056e72d8e540056d72d8e540865c6358e540855e73d8a540055d73d8a540066d6218a540855e73d86540055d73d86540056e72d86540056d72d86540057a70d86540057970d86540047c70586540067561186540063c74982540047d71982540855e73182540055d73182540056e72182540056d72182540067960182540047f765505401e6f5298854004df735885400cdc735885401e775198454004df735845400cdc7358454004ef7258454004ec725845401e775158454004fb7058454004f8705845400cde7398054004dd739805401e7b509805401e78509805401e3e74990540053d72990540053e71990540053e709905401e6f62988540055f735885407d5c735885401e7761984540055f735845407d5c73584540056f72584540056c72584540057b70584540057870584540065f73584540065c73584540066f72584540066c725
  | 18 => 0x3ca6c24401d352420002cb9e140007f600012104a86d3188128169e27b0e01be118c00057ba27c00002c3e680002ca00026323c894454b1c48ae8e262ed38e130555e0004fa80005d600000000013026b60000000ffc23522b212848e25000000012ee00044c072469613f18400003cc20a00002c8b124ba00000010c00000000a882c69cd3a5800144e42a0002cec1ce1771a202d40006664332a7075083506a8001628000000063c2149a15099460b2200000000000002e73a0a97c5e847a0978b08dd01753502ac52c051439415813868410002dd898844558caae800000000200d00500201000600500200000400100200100300900400500401200100100000b00a00300100000000300400100001101600500c02700500a00400001000c00000900000400200100901400000100701800b00300701e00500400100302200000300a00b00000f00200b04c00d00300900000000000d00400a00300b00401301f00200000d00700b00000200100100300600100300500600000000000500900100f00500001900000a03f01400001200400000100700000301100100400002000001400000c00100001200b00000000200000001900000300300500100b00100100200700100000400200500000300400d00000400400100000e01000d00000100900000202000100000000500000800100b01100b00101900900002500100200100100900200700200000100000100c00000001000c00000201b00001a00400000000100001f00000800000200002800c00000401e01800300000300300602600000400000400000300000000100600100800400200000e01000001700000500601b00400500700300400900300000302b00000600800700803300c00200000600000000400000c00100000400400a00100000100400300301000000701000000f00000000400200201100000000000200000000000c00000501101700000000e00302c00b00302400700004a03100200300600100300200401400000100a00400a01000100700000300200000300800300200000000a02200400000000a00300000600800f00400600900200400000100000c00300600100200000a02f00000400500d00500800301d00000300600000a00201100201500500300200200100d00a00000000500000002700000100b00100100002c00700400000100000900000000000800000200000200500400000000200000000b00300000f00400300000100200100200700000000300003300500000000000201600000000000100501200300000400001f00100600400100000800700200101400400000200600100502000002b00402700000000d00000100b00001b00300300600400000001b00400100000100400500000f00500000d00200300b001007000004001013001
  | 19 => 0x520f00011108290ad866d1aa688000292455c44d09e0fdd1bc73d00011a4c627a00d303d47a648300006e4b0e98f49a0000c7600027321ac00094a5298928d0e04a3e380011d684900000000000002ee247c000000194000026c000455a6c041284b13a22a40000000001e74000a8453a031400000000000000007dc000214ca7821508f80000001da00017f400000057480015fa87200000000002a51c78000ec47d60fc231c00085653300000003ea5042b8474aaa03bf8f604b6a321af9dbc374529000079036000000001fc07200015a017cbca1ac1829a8481a0d84cf121c0269e85ad9ef41d45d13ba00dcb3c5944a69cecacc95547f05506cea0f58d0e453040954a380007e68a42e129486b62360e9123556033b2f69c44a728262db866068c11527a2a401e40003342649172b80204ab0ceba53500023695446f10001d780000001be80000004fc0000000000598000000085c0732e515c4a924eb0000e28924000000000115a9f4212800000000000010102d6b5e1210000592b2c05f11f4c8c8942e58000ef88f5000092cce0a5035311602a40002bc86a55324b31d5954cf728a10bc800000089d00015397122b60a8a7f8c068851d61f3800062f00000014d40000000d6965661e1e59c2d21800020326740220000c8287404a79659788580000000000e400000000f8800000015000000600000001d38990000ab502e2b9040800001a000117e00017c80013dc3600001fd13000004b41d3cde43c50001be80000002f79db000087f00000006600000002598d161bf00000000000003f507e5122000438293970618516a20c16fab8e43e9da4a2c512519a77c95e51b0db8e7808c31526a20ccf847730001d90bc8a5b394a74ca407d216c1c40000b060800e88b4a4b016b02c40004d2000000000000000004389de501000216d11c8f8068158400000024f29e4ea0b4137017245b41712bc14bc00000047b0000d96a675a111240003df04d1ab81888a749013ec97c9d80000dfd3b20005acacdccea59f2da2ae13740963c080f4b7048f3ec800000004b0000f34f5e0004b7800052a0005b7a5a54b40003ea00000000000002bcd35c6be3a9925808e2f731a00000000000001428aa002b24c8c9400036928180014de5080000000d8606a193000000000000008d02fe6070002b7400005e0000ebd6d870f20092981fa19a15aab6407e00000000000005801dc800000000000027880000000002c78e42000000077039005600024e0198999404a2d4000b671ed8dcd27e00000009e40003243008000000b3550080011fe5d600000011663b00000000d228e811920540c62832cd206d582aa60798a9950c50d0af17e0a263a444917a54164e41e702b477e56746b9b5424e0cf26cabb1338351263a7c952492300021bccc6000088ab8
  | 20 => 0xa4eeeab41101a092508ca00000000006a33870d21458129000252c0004d700000000d609d4f98000958b6020e1c98000b0543c8ffc8a85d82af9b10850000000000140c2260672a0c00001d18d9990d3c00000014380002131389b78cb60005b7215cab660b0000f0920886234b0f50ada97835a08b054082d4fb16ed6a085929f246ce068fb2799bb0b722c81579a74e749b3584148815ea724d897fccac0000000959668a565092a200646d12d480005ecb8214f000039867e0000000b443475c61c1098a0002ba0e545284b937e1b009e28cf33f8cfd16210533da1e82fa794086abf8c743cf24c000061266d4be99cc0001c10000000b401d600015780002e008a20892c67e32bb201800ab0251b000047238322085154b2af058b949044ea943feab300000005b890fccca0b40c7000147e00026d09000000000000e0800016138c000009a42b1fd26a0a820f90000000596b250001c30f8a0000001d29436338190aae47180001441ce40000000521a8877a090202aa840005b64e01d305a6000551a7508587c0484800160e000136000162669f3ada4140120005b214b0de60004660d4c000000000000000058354b000000000000026900000a900000004c400058b2a38000000000079d1060002e9800000037725e0000000000000113849e0002252954dec4db1470000046a1018b0e38ac40000322a2cc8e29d00f000050ea3c02a12c475a51c20ca7754f8b7236b16b4c2400055900010a4a313291db80440e52859ecc20c3f4000161918461124ea45950a3e03aa0710ed000000004a0c202c5244800092e8c94f580d440c21950e03b40000580002dad086a4c0a4a10108c5440000000fd893d49e150894200f0000000a5a15d40400013ac36e1cda38c000b3900003e0e2457b575800109c29b0001b7ca348391b593f86800000c4a9d4486000111197c52268a3d224b02de4623ef10cc0000000002d0000000000000002be000083a40000000043680002161ae03794b800000000000005c40001c2072c0001df000000000000032e80017020003f900000001a50000cb0afe80e00009dc0000000f81f0c00000023e00000dc0000001b6149e0002da9028cc2b030000c1000004e43522b061a6570001a5c00000000015540009fd23983f80004bd1e380586689f1449a2c12ae3e50001d38fc06092cd9ffc2264260d7a72835aaf80df1c8126c98e0eea9842ac2c00002230000637000105550200050d0000d502b300022100006ed1bc11101665855b5148d0e831a3b895340002fc254837c00045b07580016ba9be2118af800006800024440000002ff020000000000008440005730ff095c52ea3743610d0aba00021b25689b064d2f41734cc0563000000000094126f800045265400012b403682b00019ac7888d21cf94d04fa15
  | 21 => 0x3e14c9a5495c6c12a89fb8f163a60f589a15ce2a701e127cf8c78437b94c84361640000000bb40005089d94c2a1884ae8000e6a5273ad00012e45cf4c8ad884628b43e08e00f045ac597258509a8df2a28b44ba42921b41eb12928505bd25acd546672279ac8b9c6fd1ec84b50003192981ccc6307882071e0c5c21322d18ab483a5bf0001b38724a5c4a80294998b8a1b202246ba00030529f40000002a380a84a607500023580009a300000000008445868000c52000000000000000000000000003132d41ae8000221000000148800000000009ba7b6000000020452100002180000000000000000000000000000030a5b6875038a9e6063a73c44a0003920dd078025922aa34d3d434131820e07823d655624692bead344da0641c00720de22040000001889c5540a6dd0000c5c80e8254af03a4c4a3424c3a40563e9c54a28e8c95090e19700b4f4a0001c3922007476300000000006cf14e00001f83632ccac240000001c400001244ab000193d1d24f616f80012561370600ac000046c1f5962800000020598080008bd0471080e5a3450f4a43c0000d635380011868ed00028949fa7f3201097d56e1b30bb0104434aae08c1eec8be3221779cc55c6ace288a3bc000a430000494a1e677524272ca9e2231728fb896c23f0000c0800072f01f064d5bc9a23748000000a2f261aa55014a0d58900c06f6b4633c914c00064037284583384bb3c38000f7e2dd4060000c7e1954fc8c784506e61be27b14301e24700000fb63ba1508ab157c000033a240000437395a3613f8b3604e2c851e22055c22ce0c388bc4f81c2410e0002829d212fc00050a01200004a31cc00000000005bb8000000000311a590e4496c2b8197911e05a0c0a38948eaca0580ea85203c836a164c4d67fb13325cd69844c59d0fe4baab88434ab68ba000000680a0b2c00010f2d280000bf25a80013649971662b502d45840000d6112a5fb00000012146b15ab000127200027d20f08743e83c522d800081c3630b043d85ee39e2975636144402a8b54a2afb3721198c900004cd0d352a881d10f8000c1e9100000f700004cd24514e941280d43c0f78000a423d58000f0cb705a996914042aa34499bd6fc22a2d52680ad03c355200008da0263109a7114677e3420000000a2e468800136ab540a300000000000000000000b7800000000004ff00000800005a600024c0e9214236bac909c299000006d511a55735480000000000001a008d6a691e8069d2b801f2f98aa07fc17a05180000c2985000222c66e00045780009e41d7137826cb1c0000000684db23e748a2a945e20002328d3119cb7c13495c8000a03000000000037e0000000c500005bf9621288b654f00000df6afc19026dd05e41a1f82c9c36262e214800000073f2379e654c402e53621d50308dc21f1e
  | 22 => 0x90847c11902d8b34fb420d1ea8820c660005658dc515443d2b484e00006933f396484e60140721174ff052a2f12c30c0021d20883ec00063247211d06c47190ea970d2542f0000000000013a000132c0000004a6289929eb5537f9f4416e73211d8000000b11267000087827c41da40800030f2be91c839a1aa3f791a8a70a4606919f490468c30b9b295548482592c8c0000d100000017167254cb2cc492885c04a2c892f21ed4d30c0c94aa6b04124955361683eb9f2892a9e90fb938849219f0ab864549a1330001c0828e4de3fba2c8000117118204884e50021ca1ec88e3f104f8a052669cc5690b4000000000000000d20000c319880ee3f54620d640000004c4035c0028cd0ac9e4127c01900019646a80760002d60aac2c63da00000000004ad80014caaf100000007f000029b2c405ae0003df0718c0cac8276a6d814058b3060948c265db0c20000d309a7230801c15000023b800000000000000ec00000051580006a08a25bd95012800b900011480000003be8808bee65a0001f3d2e0000027a4bd2ce3231f619553c8a1639c000076828636d825c00077b0001e8ce2e19e11d29eceac6ac2d9800000007c0002518bba00029f8bfd3680003f82bb558a0c83070000c0a00013b00013de0000001240fc275702989a94c059c2382e1c00084c39711f8e0a0b6000215406288600000014820004329640f4e7ed0001fac0003b708e91700008f72b700000000000000000a563123cc1e98b8a9db1a7810c4787b841f91a00006bd000000014c51558c105953e73429e80010bc5bc50717c4d8e0000d411e42b082056383696a425e26108700fa000000000000000025b800000000000000010049da430a3d004836c4e9029c99256f14b098c2e87a255d95710229710951d186021665c6834c8e28131061b252d49751750bed6d01b824d00283f89fb2bbad1cf6e43152297f0c7c9c80f42b112feaa739b9cd89f04ec0429a48d7229f4750b546b81672430b64af46d24b285809c66454d783dc8423853a181882986905540000294a9d4bd94990f821416528840f086e2861d100005bd1a1819553419600d000076a5df167800069c42f162068807081655e9e3485aa6351c099d592b2900000012b200000000010c823d064a0d141411c15f8278fc400014624ecc987b2000000089092205d067508a20e3ee8000d1e0000000000000aea00000010068144a10b9800000000000007c65753cd8000000a2847300005040003a02ad83180000000ff4eeaa0705e99d800011a0002c98bec91c00020c80e837933498616e61c21d91cc157e6390000ed88ecb0a0000a4c67261900016c542eae8000000150e33a50f9201190a243e5a6309d29561e9023d70c3cc0001c8d26a000126a2650fc77810ba830d0208a000000004e5524021e38000b
  | 23 => 0x16f0e805fc1fb2ca923000028f00002f000030c3e980003647973100000eaa40c000278c00062a1b30cc4f5a36f0000000d8a0005990b485124d5515000000000028ba7089e00003ce0f452da27f0a5aacc00000000000000000000002c8078c00000000004aa50700001c48804e8055211ccf881e12e83fc0000000000000000837546ab54e3a80100015915f400000007d05e600000009706bc0000000001326af200001555ae00035580000008210e8800000016e0002d7c64e81a4500e74000a350c185ec7c800035e00d965069904203507380000001d1c08a76739f2c3d2109d52e6000008056a3c8900d6880000000000a6e00003f27240000000178aa4d9870d0be01ece848fc1dd9ad4c1a9510d595f0c8264b4d482448ea2a321819104f416d28c9f204e022d000046d5cc32b209850c0000000002744c282755a1a8f428000000000016c20000a0800000072700000008fe9de158a86537869b028a8f923000045f2bb800000038d25d14a82483af89e04c255a0c518f4488a224e3949431a93225c150c1442b9571189c93823850aa8d08108b838fabd967a82a0881ac09ee792472a9b54bc64a42e912ca0c70004c0018c365594f295b0bd681f1a4a32cef43a953f1e7cba89d73771a909c000008783d000000000000010c63dd5a7139caca64300026343ec0003b3000000055800003700000004c32b6002012e000000000085a0001f100000000000000ec22070bf00000003140e8000135a0004338000db8000496a25cc6a76d438800000022e00000000003752fd000019a62d1741e30000000375000054881055682ec1566780000000000ac600000000928421d099247784324ca9ed4c9ca4b0f19ab4926873298a8a4bf21fd000103d13c97a040853c4dc30e3dd2d452a64a41eba3b015c0002a500015263fc000217c210000000147d3307e90001c6c00043b4341ae07d20d90ca205c99037006e874d5be87732817053f00004ff929c3c08274a7000000006600005cc84882420b9630a980de5950000b80a7300019b8000000000188880014d06d918c0001ca18e1e540001200001cb168a00b000000116e0005ab80000000002d7800000006d20f922c0a436d0002c54f78b48275000086a45700018e00003290002b355b61f32d3aa6025610309805c02901350b606902086e258e05715783812c68f24c6c56b532000032e6fe00001406aaa3b58223e9522aff53891e0dc61f53d71180ee438d2a31970d1c3e20a993e40004911ed0adc7cc38b1a5202c00000038385684202ce0002de46545a137a177860c3ca00020b8406b661f0830427a58100014cc5867b000000000002f500004d00000000000000de00000000fc8ed630b2e3a9c042458f00000001e20003b80cbca3c9584d5a45d69600000028105e40a12d81
  | 24 => 0xa60e2c5e60ff883c000000000068cea20930001a954940004531f554b07603c48000d1a77954b9ec40d800000000000008230a7194c0000600b4800011a00000018f04c00041df262d55212157287e8bea502000167457a000000048d23c0000c90000762adc0c389305dc28b3f3187cdf200046016f80009ac0e7a9fc8f64594798000fd06bb4cd838c24801c09119e8728a1e21100000005ae17d15509a61e135ba0d8980b635ba8d5c194548233a8c00662bc16e00016e87f954117b167e9d04c480000007f50002d340847e41a903d951e41b16d87b81cc7454e7178ced441406100012a4376268862cf267aa17194ec00000037581740245f236d04482c400019b06ec1969c64e22a005fa10c19993955de07a0002cc16d22f83c0126c884701357ac7450810915583b8a084180c11b3507c6e71121bbd28689626e03b02624b4180179c91c83d58583c000028d5969178000aab546015d1380ac0000939400651000000076666c12c236c0001b4000066400000000016ac0000b80001dd82769f7342800000008c0e180000002b800000002582453d0a8e8bd40003efa13d25c0004f080012dc00000000000009190001358c4c3350f929a123a3b847ea4e8bc20001f6a3740007d80000d84afc0000001a180000004dc00000005284cf87a840245a1f7a6f4bb293100020e8e1498448580004da00e08f25d918a8545871b4118239318e9960e3ca57077a39d21a807022142570aaf51c308dc3b29122dd00004ca4ca1fb000027c8873ae23e48208580931c5117661d5600d941c2451444933ceb01bd35f80011744ee568800114a33e4be2588d289071cd28e40008824f3a3c000025a4570000b8846e4d286d897e00014d00003b60005ae24dc8243fb16380009020000041b84456000000000101e1802f80000000000255000000000004c91191a892654f0000f920000011ea00b22464c19f314dc61a00000000007e51428cb4000ac24d50404000332000030ccd4ad60381accff872a599800160099458080016b40001bd0e581c40001178da8c4882c1391c2056433d1199e780000000000001372752338975d4f03972680318d060001721a68b049bf3042b4041600051197803b0af907402206ac876128a3b89ea1de0e3800124861653d000c43051037a8cf05d200009c8eb8c560002e326ed44000c000000002a2ec3c7981115000000008000009fa3e817d0b64b3c4ee00008a088a15d820cce807913f073922a9031b91fc4116672544800122600053b2268c580004f6a1445144640bc17201f40005201b2159ea8a0148c1c02eb490d00130f3490646c87bc0004854141fe8eb28e14e080847329294a420c4a3a7064c505c8870927000000048200046829dd5e831f000110c500
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xc3b641c15148001870c8382a29000316d8c70545200062c318e0a8a4000c73611c151480018e0c2382a290003131d47258c200041e422eb3084000c1e631d151080010b90eb1aa210003071d163544200062d318e0a884000c59631c1510800b19f0eb1c421000217e1d63940200070cb1ca02004000e19631404008001872ec2a080100038695163100200070c2a2c62004000a99839d84008001872ec3a88010002a661a631002009d54412c62004000e1b8558c4008001c310ab18801000386dd563100200070c3aac62004015e8b8258c4008001d1104b188010003a258e721002009dc441ae42004000e89635c8400800174102b9080100038658f51100200049c43aa22004000e19635444008027715071088010003a258e211002000744b18422004000c3a649c254c40010790eb22a3880030e99070547100061cb20e0a8e2000938845c450c400153706b2081880028e61a54103100051cc30a82062000a9b835d840c40014730dba881880028e618751031000555416c62062000a998398840c40012710ea888188003079d273d96100060f3a2e7b2c2000c2e749cb658400189ce7396cb080030b9d172d96100061d3a4e1b2c2000c39749c365840018b4e7386cb08003165ce70d961000635394e1b2c2000c69729c3658400107d09baac5080030e19270d45100041f430e8a8a2000c1c631d1514400107d0fb22a2880020f21c64545100060e3a6c6a8a2000c2c74d895144001858e8312a2880030ed9070545100061c320e0a8a2000c5b631c151440018b0c6382a2880031ad88705451000634310e0a8a200083e801d16504001876e8382ca080030e1d070594100043cc34e12a0200083d87190540400145b04320a808002872116598c100050e422cab18200083c845d7620400107908bb6a2080030798c74544100060e3a2c6a88200083e84dda500400187708bb0a0080030e21176140100062cbb4c62802000c597658c50040010f70cb88a0080024e2117114010095a841ae22802000b60825c450040256a507908a0080020fe1d65900100051cc30a12002000b318114240040010790eb2880080028e61a50100100070cb1ca02002000a39861404004001c32c628080080021e6187510010004b8c08ea2002000e1a5458c4004001c30a8b188008002a660e76100100051cc36ea2002000b3181dd440040014730c3a88008002cc60475100100054cc34c62002011ab08158c4004001c34cab1880080038659563100100070dbaac62002000e187558c4004029d2702b188008003a420563100100045cc38c42002000a99831884004001a60eb3888008046e420d7110010005d0412e22002000a3986d444004001c32c7a8880080024e21d51100100051dc32a22002000e196354440040237250790880080021e6187584010
  | 1 => 0xedb82a2200030edd870544400068db98e0a888000d18731c15110001a56e4382a2200034a1c870544400049d404eb1888000938805d631100010790cbac42200026660c70484400049d404ea1088000938805d4211000107f0ea8cc020003469d573980400068cbaae73008000d1b655ce6010001a30cab9cc0200024e61f51980400068cb9ea3300800093b8754660100014710ca8cc020003465cd51980400058cc1cc1280800093a801d8501000163307380a0200024e61e60140400058cc1cc0280800093887544408c00107908b88ca98003131d4624c9300051b426ebb0a600083c845d4614c00146908ba8c2980029521532185300041f424eca8a600083e861d1514c00107d0fb22a2980020f21c6454530006163a6c4a8a6000c2c74189514c001868e9b0aa2980030d1d061545300061db20e0a8a6000c38641c1514c0018d6c4382a2980031a188705453000639b08e0a8a6000c70611c1514c001990c43826298057a20c062101300a748180c22026000e2862940404c001c60c328080980038a188501013000718308a02026000a3a86950404c0014750c2a080980038a9506210130007142a0c42026000e8b43188404c02bd108631080980038c9506110130007182a0c22026000e9343184404c029d208630880980028ea1b75101300051d430ea2026000a9a86dcc404c001c56ca31080980038a194621013000715ba8c42026000e2875188404c02bd15063108098003a2dcc62101300af44398c42026000e8b53188404c02bd10a63108098057a2cc462101300058c42a642026000e88624c8404c001d40c5b0880980038cd94611013000718328c22026000ea362184404c001d40c430880980038ca14611013000718c28c22026000e3375184404c001c60ea3088098053a4a0c611013000749b98c22026014e9073184404c001d26a63088098053a414c61101300a749990c22026000e9132184404c0014750da8880980038a18b51101300071830ea2202600093887544404c0014710ca8880980038a18951101300071830aa22026000e88624c4404c001d20c29888098003a2188408c1300074830881182600083c845c665c800107908bacc3900020f21176547200041ec30e8a8e400083c8799151c80010790eb22a3900030e99070547200061cb20e0a8e4000a9b8359040c80014730d2a081900028e61854103200054dc1aec2064000a3986dd440c80014730c3a88190002aca0763103200054cc1cc22064000a3986d4440c80012710ea8881900028ee1951103200051b40ec82a4400083c845c4654800146d09baec2900020f21175185200051a422ea30a400083e849d9514800107d0c3a2a2900030718c74545200041f43ec8a8a400083c871915148001838e9b1aa2900030d1d361545200061a3a0c2a8a4000
  | 2 => 0xc70590210064c398e0b204200ca8721c16408401960e2382c8108030ee1470590210061c428e0b204200a3880592540840147100b20a8108022e20174d8c2100516c30a9a104200965811d5320840107908bacc2108028e20164d44210041e43cc8a88420083c87591510840147100b22a2108030e99070544210061cb20e0a884200c3576150410840164908a8a4210802d820151484210061d320e0a8ea000c39641c151d400183cc73a4a5280030798c74546500060e3a2c6a8ca000c4e631c9519400149d04324c728003079d26318a500061b320e2a14a000c3a641c1429400183ce931ec328003079d163d86500062731ce5b0ca000c5a639c361940018b2c7386c32800217e1973c86500041f424ed10ca000938805d0219400107d0c3a2a2a80020fa1f64545500061db20e0a8aa000c38641c1515400107908bb4a2280024e20174988500060e3a6e6b08a000c1c741cd6114001858e9b92c2280030b1d0725845000626398e4b08a000c3b741c16114001870e8382c22800316dcc70584500062c398e0b08a000c6b721c161140018d0e4382c2280020f21176884500049c402e8108a000c36651c5429000146b022a4c3200030798c74546400060e3a2c6a8c8000c5a631c151900018b2c6382a3200020f61e65106400049c402e332c8000c36659c76290001874cb386c520002aaa036298a400049c402eb30c8000a3581996619000183f07bb2a3200030720f76546400061c406eca8c8000c1f76dcd519000183eec39aa32000307dda63546400060fbb2c6a8c8000c2f76dc9519000185eec392a320003431cc72546400061dbb6e0a8c8000c3b761c15190001a36e6382a320003461cc705464000695b90e0a8c8000d28721c151900012730c382a3200034698c70546400068cb18e0a8c800083f865d6219000107f0cb88a1200020f21076545400041f430e8a8a8000c4e739cb651000185ce8b96ca200028b60a76150400058cc1ce02a08000c34541c56210001868ca38a84200028d60465104400068d2a2e72008000d18545ce4010001a1ce7396ca20003469ce70d94400068cb9ce1b288000d2a729c36510001a52e5386ca200026660e701944000516c14ec3288000b19839c06510001a3507380ca200034660e70194400049d406eab18800093a801d5631000133307386c4200024ea0275988400049c402eb3108000c34651c5621000133307386a4200026660e70d84400049d404eb3088000938805d6611000146b02328c2200030b1957218440004ccc1ce1a88800093a809db5110001275003b6a220002c660e70d44400068d41ce1a888000d19839c35110001275013b2a2200024ea0076544400061d400eca888000c1c76dcd5110001838ec39aa2200030b1db7254440006163b0e4a888000d0c731c9511000187
  | 3 => 0x8302a200e1b64d8c6054401c30c9b18c0a880386dd363181510070c3a6c6302a200a3a8498c605440147309318c0a880296a0e631815100535414c6302a200a698298c605440147708b18c0a88028e211631815100535c12c6302a200a688258c60544014e702b18c0a880296a1863181510070db20c6302a200e186418c6054401c36e8318c0a8803861d0631815100715b26c4302a200e2864d886054401c96c7b10c0a88039218f621815100715ba6c4302a200e2874d88605440147509310c0a88028e61262181510052d41cc4302a200a598398860544014d505310c0a88028ee1162181510051c422c4302a200a5b8358860544014b106b10c0a88029ce05621815100535430c4302a200e2b641886054401c50c8310c0a880392d8c621815100724318c4302a200e2b741886054401c50e8310c0a88039418f611815100730316c2302a200a5a83dd060544014b307ba0c0a880386a0f74181510070cc1ee8302a200c3a871d06054401870e9b98c0a88028ea1273181510051cc24e6302a200a3b845cc605440147108b98c0a88030e1d1731815100535c12e6302a200a68825cc60544014e702b98c0a88021ea1e43181510043cc3c86302a200a3a849c8605440147309390c0a88030e1d272181510051dc22e4302a200a38845c860544014b706b90c0a88029620d721815100539c0ae4302a200c38741c860544014b506390c0a88029660c72181510043dc3a84302a2008788750860544014b706a10c0a88029620d421815100539c0a84302a200a708150860544014e503990c0a88029c60732181510053541662302a200a6982cc4605440183ce939ecba0803079d173d9741006173a4e5b2e8200c4e739cb65d040185ce8b96cba08030e9d270d97410062d39ce1b2e8200c59739c365d04018d4e5386cba08031a5ca70d97410061c424e1b2e8200c3a745c365d0401868ca38a85a08030e1947050b410049c402e22a48200a3a801526090401868ca38a84a08030e194705094100654310e0a128200c1c631d15150401838e9b1aa2a08030b1d36254541006163a0c4a8a820087a861c151504018b6c6382a2a08031618c705454100635b10e0a8a8200c68621c151504010f70ea8ec0a08028e21151d81410055840a843028200a3a84d44605040147108a88c0a08020fe1971150410049c402e22a08200b24825c4541040183cc63a2a3908021721d63547210060e3a2c6a8e4200c5a631c151c84018b2c6382a3908020fa007459621006163a6e4b2c4200a3a80d90548840143908b2cc710802872116558e2100516c30a9a144200c1e631d15188401838e8b1aa3108031698c70546210062cb18e0a8c4200c4c731c96508401874ca382c8108030e59470590210061a3a8e2b204200c3b751c16408401870ea382c81080326dc
  | 4 => 0x45440145f04b20c8a88028b20964191510051dc02c8322a200a3880590645440147501218c8a88028e602431915100517414c6322a200a2d8298c645440147501318c8a88028e60263191510051d404e6322a200a39809cc645440143f06b90c8a88028720d72191510051bc0ae4322a200a3b805c8645440147100b90c8a88028da0732191510051ac0e64322a200a1f835c4645440143906b88c8a88028be09711915100516412e2322a200a3b805c4645440147100b88c8a88028ba0b311915100516c1662322a200a1e839c0645440143b07380c8a880307a0e70191510060ec1ce0322a20083e87cc0645440107b0f980c8a880296a0264d8d510050f400c9b1aa200c1c631d16354401858c9b92c6a88030b1907258d5100626318e4b1aa200c3864dc16354401870c8382c6a88031618c7058d510050f424c831aa200a4e8299063544014b501320c6a8803079d86418d510050f400c831aa20087a80dd943544014d501326c4a88028ba0064d895100706326c7b12a200e0c6418f625440183ce6324c4a88030719173989510060f3a0c7312a200c2e74d8a6254401870c9384c4a88031618e709895100635b14e1312a200c38645c26254401838e6322c4a88030719373589510061a326e2b12a200c3864dc16254401870c8382c4a88021be1d621895100516422c4312a200a4c8358862544014d100b10c4a88028ba1264189510052741cc8312a200a6a80990625440185cec320c4a88028ba00641895100706326c6312a200a2e8498c625440149d07318c4a88029aa02631895100707b20c6312a200e0c6418c62544010f100bb484a88021ea0376509510060e398c8a12a200c1c64dcd4254401868c9b8a84a88030d19071509510043d436e0a12a200c3864dc14254401870c838284a88020fa13764c9510043d406ec992a200e246418b615440147500326c0a88038619363d81510070c320c7b02a200e2864d8b6054401c50c8316c0a88039218c62d81510060f398c9302a200c1c645ce605440183ce9b1cc0a8803079d0639815100616324e5302a200c4c639ca6054401858c8b94c0a88030b9d36298151006173a0c5302a200c4e7318a6054401874e9b04c0a88020fa1c64581510060e398c8b02a200c1c64dcd6054401858c9b92c0a88030b19072581510043dc3ac0302a200a3b84580605440147108b00c0a880296e0d60181510052c41ac0302a200a6b8258060544014d104b00c0a88028ea0374181510051d400e8302a200a3a84cc0605440147309980c0a88028ea1276181510051cc24ec302a200a3a8499060544014b507320c0a88029660e641815100535414c8302a200a698299060544010f70eb20c0a880296e0d64181510052c41ac8302a200a6b8259060544014d104b20c0a88028ea1864181510061d3b0c
  | 5 => 0x8442f6115360340ee000001fc3a8534462d600045c001a32e40006f2710a2b71690000007b4018951361cc2e80620c89c5786b48a2040007a06424c00225056b64be00059a000000000000011400003eb895f0000000013700028c000000000000013a00000036c771c922c65814af0000000000b13880014a80039a000002ea3f0000000000000000000017e000b4800000934120b814853070000356a4cffa18234b505b80054abb8000990005380000000091c0027d286088000f30000000024b06a068cc1e523c331651ca42097461a654322f11b2981cca646e80000000000177000000000002eaa84001900010080000100c00203400002002000010050020000000000601401000002000000060000000280301e00801803000004020010000040800f0080000000400000c000010080100280200001000004000018018040000100180700000c0180902200c010010000000180700200806000000014028020140180000500206009008002010008060160040080d0000000081c0200000000001a0000300500c00c000020000180800200a00000000000000000000080340180000000c008070000000000200000003001002008038000020000080500c01c0100a00002c050010100080100300402c01001000004000000120040e8050100040000700a0000480000001808803002000000000060000000a00600c0180000800002005000000008020020240000000200c00006004010000000060300180a00c0040000200001001803000008018040000100180001e000010080000340080700001401898e6392c22a00316dcc70584540062c398e0b08a800c6b721c161150018d0e4382c22a0030ee1070584540061c420e0b08a800a2d821d26015001475003a4c02a0021e20171195430050f41eeb324a400c2e645ca5494801838c73a4a4a90024e20171153420043c402e332c8400878805c4655080127100b88a8a10028ba1854d094200539406ebb0a8400878805d4615080146b022a0c2a10038515363185420070a2a0c630a8400a70805d4615080146b0e2a0c2a10028da005418542007122a68430a8400e30541876050801475002a0c0a10028ea1854181420070c2a6c63028400e185418c6050801c60a9b08c0a10038c15061181420051d42ee83028400a3a871506050801473022a0c0a10028ea1642181420051c402c82a4640083c845d6618c80107908b88ca990021e20171195320045c402e9316a200938805d262d4401838c73a4a4a88020f2197494951006173a6c5292a200c1c731915254401838c9b9aa4a8803131cc62549510052d41eea302a200a5983dd4605440147509290c0a88028e61252181510052dc1aa4302a200a58835486054401876c9384c8a88020fe1d64191510050fc1ac8322a200a1c835906
  | 6 => 0x25000000000002ec000000000000003d4000000260008186c0001f089810428001479fd008bc53d26646008cc18000000000002c348aa94b8b00001791da1d21a0001880053894800248000a440002f350a280c8e7000000b800005a4a40018c000000590000005e8f928d5504f8000493de075521d90000003c8253be000a287e000194a58000000000012c17217c4309d378a896787654000000112424324000005d25515e93919a0000015747cac028000074084000704b64bc002130405b0b226f116000001665465d12c8001823488a80033815c5d000190000680bd1d00014719a0004f400000000688a9800000580df80159013c250b5166000000003120dd76a6233e1008c25e2c63e0b713a5aaa101c000000000e88cf0007d00000000000055800000738af9950000002d00052c8fcf88fb00027cfb8005d64a0002b9000001271ac302000fa800060af000000106344001f05d00000028535c2b8000003a4308df00025a0f0000001340b8001af000000002d014a1a474a49576b0c001590000000000a0000009900006c0003f8000001ec0023a0000009e0000000000017e0003911b800244000000875560000900012c1380000040a0012d2c451834c0000055a9300000057e001708002d6650000fa14c0010f23d5ca4752e0001d80f80000041c364712331ae69c47150240ac8ed1e631c0002c20f000000820004f60004f00024c49d1626824a520e80781be54400000000504000000000004c00000081c000000003c4000004680009ba701f80016488d00000000000000000cf0bb000955148000000002a0000008b84a29228e001598000000000000056278ce01342b082d77a17000228350270ac8246e0004ee31c1c8520000015d29e4c68980020c0008291680030e000002d80044050215609a000c28c53a64acf52d3000b5c0581e27e46d2315e08c0009180037272c00136000001441c1000ad86b10e000778002af038000000fd3dc7acfd13343412d19053000610000004b0000c9800332000000000001b4000110002d8e40000003e4378412e619c370330007314d00023e59c8895c59c3280006800056d1c8000004080020355c000000000000000617f506000f48002aa0340b04c34c000ed80032487cd99303d80a80000000000075800516001430f72000000000000066c000001ca000b40ce05095d538cb4869fcf390c3ba8d4db23c1ec1540000001e6d45a00057065d738000006f51094a3c8001348000005b54f8a334a270851b0228001410000e42b10098a4a8674b506331eb7c0a80000000000000000490b1085112add73202090000ee00000000000000000000000aa0009d5338000e8000000ed000000001aa000000001f312e880000001085000000031a000000000000000400000058400261100758f0
  | 7 => 0xa50e1a641a8594000422ec6443100011e001608f41de00098a112383fc001a030406cd08be1224656313510429c1320d0005e14396f3707a0442423f26200018042c000001090007ec481b700000000000000484000001b45100010b29e3100000048297c000ad0002492880040ca41041865c800144a2b5002a55484318c7f8301e05bc6a5221d7536000a900000000000000502b14be800276000001c200005c5005c0001f450ad14808bc1e8001c66ecda2ac030000542db2700fcad0004da000001d801c0000021c0000000027e0b6b31002232ba9596eab51e0b1c879ba5c6015700000000014e9492e294075075254354000000c2718000001fc73c708000000501d8074540013c0004447d8048000004413c864000b08002b40e28c4f10000b2854000004f8001658c0362a989726b0000000000035a00129a73000000000001440000000028489000276000001602720007147900038e0000006608e5e4838004c042000000000000c580036493c001d50000013500020a0006c000470000000005b486d
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x1402c0b088012e932a06296612300000800d1c99e00868ea9000c1401814c10c012309060454185420048c24187150615080141993a1c74181510060a1d0825cc60544018187460c721815100449251811d5320840116090604754c8210040e261641c1510840123090606659864000606e0c80dd951900014259119572184400050664e801d95110001818865cd519804000682214624c8404c001610954c861101300060a21c62544404c00183087185511013000486a637558c4008001a0885209631002009ca2261635c84008001a81632057210020004862616354440080018188758d511002009ca2e61638844008001133976045090010005846447558c40040018188758d5110010
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x4
  | 2 => 0x4c
  | 3 => 0x6
  | 4 => 0x124c
  | 5 => 0x8c
  | 6 => 0x128c
  | 7 => 0x10c
  | 8 => 0x130c
  | 9 => 0x14c
  | 10 => 0x134c
  | 11 => 0xbcc
  | 12 => 0x19cc
  | 13 => 0x44c
  | 14 => 0x164c
  | 15 => 0x74c
  | 16 => 0x194c
  | 17 => 0x10054
  | 18 => 0x14054
  | 19 => 0x10094
  | 20 => 0x4114
  | 21 => 0x8114
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 68
  | 6 => 1685
  | 5 => 2959
  | 4 => 754
  | 3 => 27
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (i*15) 6
  | 7 => packedAt gbK7 (i*26) 17
  | 6 => packedAt gbK6 (i*37) 28
  | 5 => packedAt gbK5 (i*48) 39
  | 4 => packedAt gbK4 (i*59) 50
  | 3 => packedAt gbK3 (i*70) 61
  | _ => 0
def gbH (k i : Nat) : Nat :=
  match k with
  | 8 => gbHint (packedAt gbK8 (i*15+6) 9)
  | 7 => gbHint (packedAt gbK7 (i*26+17) 9)
  | 6 => gbHint (packedAt gbK6 (i*37+28) 9)
  | 5 => gbHint (packedAt gbK5 (i*48+39) 9)
  | 4 => gbHint (packedAt gbK4 (i*59+50) 9)
  | 3 => gbHint (packedAt gbK3 (i*70+61) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (16+((h/1+packedAt gbK8 (15+(h % 1)*1) 1) % 2)*1) 1
  | 7 => packedAt gbK7 (1922+((h/22+packedAt gbK7 (1768+(h % 22)*7) 7) % 82)*8) 8
  | 6 => packedAt gbK6 (69077+((h/561+packedAt gbK6 (62345+(h % 561)*12) 12) % 2691)*12) 12
  | 5 => packedAt gbK5 (153864+((h/986+packedAt gbK5 (142032+(h % 986)*12) 12) % 3906)*13) 13
  | 4 => packedAt gbK4 (47247+((h/251+packedAt gbK4 (44486+(h % 251)*11) 11) % 1203)*11) 11
  | 3 => packedAt gbK3 (1944+((h/9+packedAt gbK3 (1890+(h % 9)*6) 6) % 33)*6) 6
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xff800ffff003ffffffffe003ff1ffffc78ffc7
  | 1 => 0xffffffffffffffffffffffffffe3087fffffff
  | 2 => 0x7ffffffffffc01fe003ffffffffc0f8fff18ff
  | 3 => 0x7ffff007fffffe00003ffffc00fff00f8fe0f8
  | 4 => 0x80000007ffffffffffc0000000fffff00fff00
  | 5 => 0xfffffff8000000000000000000fffffff00000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x978c065971019696d5796061b90d73bc386bc3
  | 1 => 0xaab4baaa962f2b2b6992ada6ca630855d3b55d
  | 2 => 0x4d595d34eb5481cc0c2cd6cb74bc0d8aed18ae
  | 3 => 0x71ee66073d9bcc80313f1b7018dfb00f0ee0f0
  | 4 => 0x700807cfe2f1f1be08038060f6dee00fde00
  | 5 => 0x7e7f8fc00e030101c0301c0380fbef7ff00000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xeaa8c080c888c080eaa8c080c888c080eaa8c080c888c080eaa8c080c888c080eaa8c080c888c080eaa8c080c888c080eaa8c080c888c080eaa8c080c888c080, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_15243
namespace PEqualNP.Outside.L_meta_15243
open PEqualNP.Outside.L_meta_15243.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_1_0 : Interval s0Atlas 1 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_1 : Interval s0Atlas 1 0 1 := bs0_1_0
theorem alls0 : ∀ k ≤ 1, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_1 i (by omega) hi
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
theorem bs3_3_0 : Interval s3Atlas 3 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 9 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 14 := bs3_4_0
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
theorem bs4_2_0 : Interval s4Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 1 := bs4_2_0
theorem alls4 : ∀ k ≤ 2, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 1 := bs5_4_0
theorem alls5 : ∀ k ≤ 4, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 27 := bgb_3_0
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
theorem bgb_4_736 : Interval gbAtlas 4 736 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 754 := (concat (concat (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat bgb_4_96 (concat bgb_4_128 bgb_4_160))) (concat (concat bgb_4_192 (concat bgb_4_224 bgb_4_256)) (concat bgb_4_288 (concat bgb_4_320 bgb_4_352)))) (concat (concat (concat bgb_4_384 (concat bgb_4_416 bgb_4_448)) (concat bgb_4_480 (concat bgb_4_512 bgb_4_544))) (concat (concat bgb_4_576 (concat bgb_4_608 bgb_4_640)) (concat bgb_4_672 (concat bgb_4_704 bgb_4_736)))))
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
theorem bgb_5_2944 : Interval gbAtlas 5 2944 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2959 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 (concat bgb_5_192 bgb_5_224)) (concat bgb_5_256 (concat bgb_5_288 bgb_5_320)))) (concat (concat (concat bgb_5_352 (concat bgb_5_384 bgb_5_416)) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))) (concat (concat bgb_5_544 (concat bgb_5_576 bgb_5_608)) (concat bgb_5_640 (concat bgb_5_672 bgb_5_704))))) (concat (concat (concat (concat bgb_5_736 bgb_5_768) (concat bgb_5_800 (concat bgb_5_832 bgb_5_864))) (concat (concat bgb_5_896 (concat bgb_5_928 bgb_5_960)) (concat bgb_5_992 (concat bgb_5_1024 bgb_5_1056)))) (concat (concat (concat bgb_5_1088 (concat bgb_5_1120 bgb_5_1152)) (concat bgb_5_1184 (concat bgb_5_1216 bgb_5_1248))) (concat (concat bgb_5_1280 (concat bgb_5_1312 bgb_5_1344)) (concat bgb_5_1376 (concat bgb_5_1408 bgb_5_1440)))))) (concat (concat (concat (concat (concat bgb_5_1472 bgb_5_1504) (concat bgb_5_1536 (concat bgb_5_1568 bgb_5_1600))) (concat (concat bgb_5_1632 (concat bgb_5_1664 bgb_5_1696)) (concat bgb_5_1728 (concat bgb_5_1760 bgb_5_1792)))) (concat (concat (concat bgb_5_1824 (concat bgb_5_1856 bgb_5_1888)) (concat bgb_5_1920 (concat bgb_5_1952 bgb_5_1984))) (concat (concat bgb_5_2016 (concat bgb_5_2048 bgb_5_2080)) (concat bgb_5_2112 (concat bgb_5_2144 bgb_5_2176))))) (concat (concat (concat (concat bgb_5_2208 (concat bgb_5_2240 bgb_5_2272)) (concat bgb_5_2304 (concat bgb_5_2336 bgb_5_2368))) (concat (concat bgb_5_2400 (concat bgb_5_2432 bgb_5_2464)) (concat bgb_5_2496 (concat bgb_5_2528 bgb_5_2560)))) (concat (concat (concat bgb_5_2592 (concat bgb_5_2624 bgb_5_2656)) (concat bgb_5_2688 (concat bgb_5_2720 bgb_5_2752))) (concat (concat bgb_5_2784 (concat bgb_5_2816 bgb_5_2848)) (concat bgb_5_2880 (concat bgb_5_2912 bgb_5_2944)))))))
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
theorem bgb_6_1664 : Interval gbAtlas 6 1664 21 := block_range (n:=21) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1685 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)))) (concat (concat (concat bgb_6_416 (concat bgb_6_448 bgb_6_480)) (concat bgb_6_512 (concat bgb_6_544 bgb_6_576))) (concat (concat bgb_6_608 (concat bgb_6_640 bgb_6_672)) (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 bgb_6_800))))) (concat (concat (concat (concat bgb_6_832 (concat bgb_6_864 bgb_6_896)) (concat bgb_6_928 (concat bgb_6_960 bgb_6_992))) (concat (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088)) (concat (concat bgb_6_1120 bgb_6_1152) (concat bgb_6_1184 bgb_6_1216)))) (concat (concat (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312)) (concat (concat bgb_6_1344 bgb_6_1376) (concat bgb_6_1408 bgb_6_1440))) (concat (concat bgb_6_1472 (concat bgb_6_1504 bgb_6_1536)) (concat (concat bgb_6_1568 bgb_6_1600) (concat bgb_6_1632 bgb_6_1664))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_32 : Interval gbAtlas 7 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_64 : Interval gbAtlas 7 64 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 68 := (concat bgb_7_0 (concat bgb_7_32 bgb_7_64))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 2 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 52, 53),(inputs.getD 2 zero, 49, 53),(inputs.getD 3 zero, 49, 57),(inputs.getD 4 zero, 37, 53),(inputs.getD 5 zero, 21, 53)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 4 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19),(inputs.getD 1 zero, 17, 19),(inputs.getD 3 zero, 49, 57),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 25, 57)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 21, 53)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 3 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 6, 14)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 5 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 21, 53)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeaa8c080c888c080eaa8c080c888c080eaa8c080c888c080eaa8c080c888c080eaa8c080c888c080eaa8c080c888c080eaa8c080c888c080eaa8c080c888c080
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 9 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 49 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) (SBf 2) :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have s3 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 3 zero)) (SBf 3) :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
  have s4 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 4 zero)) (SBf 4) :=
    slice_correct (ms:=fixRows 48 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (3936927872 * 2 ^ 32 + 3364405376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_15243.Model.Repr at out
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

def mono : List Gate := [⟨.and,[1,2]⟩,⟨.and,[0,4]⟩,⟨.and,[0,2]⟩,⟨.and,[1,7]⟩,⟨.or,[3,8]⟩,⟨.and,[5,7]⟩,⟨.or,[6,11]⟩,⟨.or,[11,12]⟩,⟨.and,[10,13]⟩,⟨.or,[9,14]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,15⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 9) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3936927872 * 2 ^ 32 + 3364405376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3936927872 * 2 ^ 32 + 3364405376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_15243

open PEqualNP.Outside.L_meta_15243 in
theorem PEqualNP.Outside.L_meta_15243 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3936927872 * 2 ^ 32 + 3364405376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3936927872 * 2 ^ 32 + 3364405376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
