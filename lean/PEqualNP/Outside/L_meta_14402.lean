import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_14402.Model
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


end PEqualNP.Outside.L_meta_14402.Model

namespace PEqualNP.Outside.L_meta_14402
open PEqualNP.Outside.L_meta_14402.Model
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

def SB : Nat := 4

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

end PEqualNP.Outside.L_meta_14402

namespace PEqualNP.Outside.L_meta_14402
open PEqualNP.Outside.L_meta_14402.Model
def s0K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (i*5) 5
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (6+((h/1+packedAt s0K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffff83c1e0e03fffffffffe067fff
  | 2 => 0xf83ff07ff83ffc01ff003c3fc3fe07f984e73
  | 3 => 0xffc1ff83ffc1fffe00003fc3fc3ff81e0739c
  | 4 => 0xf0001fffc0001ffffffffc003ffc0001ff83e0
  | 5 => 0xffffe00000001fffffffffffc0000001fffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x10908142090000140a02488448442a280614a5
  | 2 => 0xa549523492569ac295509162962b4155984a52
  | 3 => 0xc62a5491a452bd6aa141226a26a39505e06318
  | 4 => 0x843188210718c98cc66438003b310618aa83e0
  | 5 => 0x84210c6386316331989c3b300021861557c00
  | _ => 0
def s0Atlas : Atlas := ⟨3,rawDecor 62 s0Pos s0Neg, 0xffffccc0ccc0ccc0ffffccc0ccc0ccc0ffffccc0ccc0ccc0ffffccc0ccc0ccc0ffffccc0ccc0ccc0ffffccc0ccc0ccc0ffffccc0ccc0ccc0ffffccc0ccc0ccc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_14402
namespace PEqualNP.Outside.L_meta_14402
open PEqualNP.Outside.L_meta_14402.Model
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
  | 0 => 0xf83ffffffffffff83060e0ffffffffff807fff
  | 2 => 0x3e1e1f0f0f83ffc07f00e1e3878f87e65293
  | 3 => 0x3fe01ff00ffc1fff8000fe03f80ff878631c
  | 4 => 0xffc0001ffff0001fffffff0003fff0007f83e0
  | 5 => 0xffffffe00000001ffffffffffc0000007ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x420001000000000000200220088080000425
  | 2 => 0x56954d326a55569aca750a7149c52d17665292
  | 3 => 0xa718d554a66a52bd7a9414b512d44e71786318
  | 4 => 0x32108888444318c993264600036664222a83c0
  | 5 => 0xc4211110888c63162c5898d998000844557800
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xffffaaaaaaaaaaa0ffffaaaaaaaaaaa0ffffaaaaaaaaaaa0ffffaaaaaaaaaaa0ffffaaaaaaaaaaa0ffffaaaaaaaaaaa0ffffaaaaaaaaaaa0ffffaaaaaaaaaaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_14402
namespace PEqualNP.Outside.L_meta_14402
open PEqualNP.Outside.L_meta_14402.Model
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
  | 0 => 0x1e3e3c7ffc7ffe3f0c63831ffc7ff83f00f3cf
  | 1 => 0x1fc03f8e3f8e3fc7f07c03e38f8e3fc7334d33
  | 3 => 0xe0003ff03ff03ff8ff8003fc0ff03ff8c38e3c
  | 4 => 0xffffc0003fffc000fffffc000fffc000fc0fc0
  | 5 => 0xffffffffc0000000fffffffff0000000fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x2004400040000400000800480120800001045
  | 1 => 0xc4148944492854085064292124849286314512
  | 3 => 0x1a912289244a801ac80524849212530c28a28
  | 4 => 0x488c032520240c92352918000e498192540f80
  | 5 => 0x9130204803493124ca52639260000624abe000
  | _ => 0
def s2Atlas : Atlas := ⟨3,rawDecor 59 s2Pos s2Neg, 0xffffeeaaeeaaee88ffffeeaaeeaaee88ffffeeaaeeaaee88ffffeeaaeeaaee88ffffeeaaeeaaee88ffffeeaaeeaaee88ffffeeaaeeaaee88ffffeeaaeeaaee88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_14402
namespace PEqualNP.Outside.L_meta_14402
open PEqualNP.Outside.L_meta_14402.Model
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
  | 0 => 0x1e3e3c7ffc7ffe3f0c63831ffc7ff83f00f3cf
  | 1 => 0x1fc03f8e3f8e3fc7f07c03e38f8e3fc7334d33
  | 2 => 0xe0003ff03ff03ff8ff8003fc0ff03ff8c38e3c
  | 4 => 0xffffc0003fffc000fffffc000fffc000fc0fc0
  | 5 => 0xffffffffc0000000fffffffff0000000fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x2004400040000400000800480120800001045
  | 1 => 0xc4148944492854085064292124849286314512
  | 2 => 0x1a912289244a801ac80524849212530c28a28
  | 4 => 0x488c032520240c92352918000e498192540f80
  | 5 => 0x9130204803493124ca52639260000624abe000
  | _ => 0
def s3Atlas : Atlas := ⟨3,rawDecor 55 s3Pos s3Neg, 0xffffeaeaeaeae8e8ffffeaeaeaeae8e8ffffeaeaeaeae8e8ffffeaeaeaeae8e8ffffeaeaeaeae8e8ffffeaeaeaeae8e8ffffeaeaeaeae8e8ffffeaeaeaeae8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_14402
namespace PEqualNP.Outside.L_meta_14402
open PEqualNP.Outside.L_meta_14402.Model
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
  | 0 => 0x7fc7fff87f0ff0ff0f87e1ffe1fc3f0fa4f4cf
  | 1 => 0x87f870ff8ff0ff0ff1f87e1c3e1fc7f1db4b33
  | 2 => 0x7ff80fff000fff1fe007fe03fe007fe638c3c
  | 3 => 0xf80000ffffff0001ffff80003ffff8007c0fc0
  | 5 => 0xffffff0000000001ffffffffc00000007ff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x400008001001000000802400240100001045
  | 1 => 0x20820111040140102088220882090241094112
  | 2 => 0x55112aa222aaa88356445541354094ac628c28
  | 3 => 0x14354cc44a882aa59b5511023992b024740e80
  | 5 => 0x662668876cccccc9ede67993910320c97fe000
  | _ => 0
def s4Atlas : Atlas := ⟨3,rawDecor 47 s4Pos s4Neg, 0xeeeaeeeaeee8eee8eeeaeeeaeee8eee8eeeaeeeaeee8eee8eeeaeeeaeee8eee8eeeaeeeaeee8eee8eeeaeeeaeee8eee8eeeaeeeaeee8eee8eeeaeeeaeee8eee8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_14402
namespace PEqualNP.Outside.L_meta_14402
open PEqualNP.Outside.L_meta_14402.Model
def s5K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s5K3 (i*5) 5
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s5K3 (6+((h/1+packedAt s5K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x7fc7fff87f0ff0ff0f87e1ffe1fc3f0fa4f4cf
  | 1 => 0x87f870ff8ff0ff0ff1f87e1c3e1fc7f1db4b33
  | 2 => 0x7ff80fff000fff1fe007fe03fe007fe638c3c
  | 3 => 0xf80000ffffff0001ffff80003ffff8007c0fc0
  | 4 => 0xffffff0000000001ffffffffc00000007ff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x400008001001000000802400240100001045
  | 1 => 0x20820111040140102088220882090241094112
  | 2 => 0x55112aa222aaa88356445541354094ac628c28
  | 3 => 0x14354cc44a882aa59b5511023992b024740e80
  | 4 => 0x662668876cccccc9ede67993910320c97fe000
  | _ => 0
def s5Atlas : Atlas := ⟨3,rawDecor 31 s5Pos s5Neg, 0xeeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_14402
namespace PEqualNP.Outside.L_meta_14402
open PEqualNP.Outside.L_meta_14402.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0xf0ac0064402cdc00ecf800a86cc8945400247404fc90b080f4e000d4c4e88848cc0044703000980034080068009c842000006014003800002800007c780000d01c4ca08c5c00e4a4b8010018bc0cb450c058d800103cbc0000008200000011200081800e00181240001ff54007f95001fd54007f15001ff53007f94c01fd53007f14c01ff43007f90c01fd43007f10c01ff52007f94801fd52007f14801ff42007f90801fd42007f10801ff320077cc801fe32007b8c801fd3200774c801ed3200734c801fc32007fd4401fe51007f54401fc51007fd0401fe41007f50401fc41007fcc401fe31007f4c401fc31007fc8401fe21007f48401fc21007fd4001fe50007f54001fc50007fd0001fe40007f50001fc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x944000bf98620005fac310003ee2188001f610c4000bf98220007de4110003fb20880017fb2a4000bf99520005faca90002fc65480017fb224000bf99120005fac890002fc64480017fb1a4000bf98d20005fac690002fc6348001f72924000fb54920007dc8490003ed4248001ef9924000fb8c920007ba6490003ed3248001e69924000bfd8520005f8c290003ef2148001f690a4000fec8120007dc4090002ff65080017f3284000df99420004fcca10002fd6508001beb2840009f59420005f8ca10002ff64080017f3204000ef990200057cc810002fd6408001deb204000af59020005f8c810002ff63080017f3184000f798c20005bcc610002fd6308001eeb184000b758c20005f8c610002fe6208001ef9904000fb8c820007ba6410003ed3208001e69904000bf98420007ecc210002f661080017eb084000fd58420005eac210003ee2108001f61084000bf98020007de4010003fa2008001f69004000fe48020005fecb88002fe65c40017eb2e2000bf19710005fec988002fe64c40017eb262000bf19310005fec788002fe63c40017eb1e2000bf18f10005fec588002fe62c40017eb162000bf18b10007be6588003ee32c4001ee9962000fb4cb100079a6588003f651c4001faa8e2000fd90710007ea8388003f631c4001fa98e2000fd88710007ea4388002ff65840017f32c2000bf59610005f8cb08002ff64840017f3242000bf59210005f8c908002ff63840017f31c2000bf58e10005f8c708002ff62840017f3142000bf58a10005f8c508003df3284001f71942000f74ca10007da6508003cd32840017eb0c2000bf98210007f46108003f93084001fd1042000fe48210007ee2108003fb10840017fb2a2000bf99510005faca88002fc65440017fb222000bf99110005fac888002fc64440017fb1a2000f7d8d10005bec688002fe63440017eb1a2000bf18d10007b8c688002dc63440017fb122000fbd8910005dec488002fe62440017eb122000bf18910007d8c488002ec6244001ef9922000fb8c910007ba6488003ed3244001e69922000fd94510007eaa288003f64144001faa0a2000fd8c510007ea6288003f62144001fa90a2000fe8c110007f26088003fa2044001fc9022000fec4110007ec2088002ff65040017f3282000df99410004fcca08002fd6504001beb2820009f59410005f8ca08002ff64040017f3202000ef990100057cc808002fd6404001deb202000af59010005f8c808002ff63040017f3182000f798c10005bcc608002fd6304001eeb182000b758c10005f8c608002ff62040017f3102000fb98810005dcc408002fd6204001f6b102000bb58810005f8c408003df3204001f71902000f74c810007da6408003cd32040017f3082000bf98010007ee2008003fa1004001fa8802000fe44010
  | 1 => 0x2fc6350001dfa1a8000ef50d40005fec4a0002fc6250001dfa128000ef50940007be64a0003ee3250001ee9928000fb4c9400079a64a0002ff61500017e30a8000efd05400077a82a0003fa5050001fca828000fed01400077c80a0002ff65100017f3288000df99440004fcca20002fd6510001beb2880009f59440005f8ca20002fe6410001dfaa08000ef15040005fcc620003de63100016f3188000bf58c40007bac620002dd63100017f3108000fb98840005dcc420002fd6210001f6b108000bb58840007be6420003ee3210001ee9908000fb4c8400079a6420002fe6110001fb3088000bd98440005fac220003f561100017ab088000bf980400077e8020003fa4010001dea008000fe50040005fecb98002fe65cc0017eb2e6000bf19730005fec998002fe64cc0017eb266000bf19330007bca798003dd53cc001ef21e6000f750f30005fcc598003ee62cc001773166000bf58b30007dac598002ed62cc001ef9966000fb8cb30007ba6598003ed32cc001e69966000bf98730005fac398003df31cc001ee98e6000bfd9630005fccb18002fd658c0017e32c6000bfd9230005fcc918002fd648c0017e3246000bf58e30005fcc518002fd628c001ef9946000fb8ca30007ba6518003ed328c001e69946000bf98630005fac318003de318c001ee18c6000bf98230007be6118003fb308c0017fb2a6000bf99530005faca98002fc654c0017fb226000bf99130005fac898002fc644c001ef29a6000f754d30007bc8698003dd434c0017fb126000bf18930007be6498003ee324c001ee9926000fb4c9300079a6498002ff614c0017e30a6000f7cc530007ba6298003fb304c001ef1826000bfd9430005fcca180037e650c0013f3286000bf59430006faca180027d650c0017e3286000bfd9030005fcc818003be640c0015f3206000bf590300077ac818002bd640c0017e3206000bf98c30005fcc418003ee620c001773106000bf58830007dac418002ed620c001ef9906000fb8c830007ba6418003ed320c001e69906000bf98430007ecc218002f6610c0017eb086000fd58430005eac218003de310c001ee1886000bf98030007be6018003fa300c001ee9806000fe4c030005fecb90002fe65c80017eb2e4000bf19720005fec990002fe64c80017eb264000bf19320005fec790002fe63c8001ef31e4000b798f20005fac790003dd63c80016eb1e4000bf18f20007dca590003ed52c8001f72164000fb50b20007be6590003ee32c8001ee9964000fb4cb200079a6590002fe61c80017eb0e4000fbc8720007da4390002ff65880017f32c4000bf59620005f8cb10002ff64880017f3244000bf59220005f8c910002ff63880017f31c4000bf58e20005f8c710002fd6288001ef9944000fb8ca20007ba6510003ed3288001e69
  | 2 => 0x21005fac890802fc64484017fb1a4200bf98d21005fac690802fc6348401ef9924200fb8c921007ba6490803ed3248401e69924200fdc8521007dc4290802ff60484017e3024200bfd9421005fcca108037e65084013f3284200bf59421006faca108027d65084017e3284200bfd9021005fcc810803be64084015f3204200bf590210077ac810802bd64084017e3204200bfd8c21005fcc610803de63084016f3184200bf58c21007bac610802dd63084017e3184200bf98821007dca410803ed5208401f72104200fb50821007be6410803ee3208401ee9904200fb4c8210079a6410802fe6108401f79084200fd88421007da4210803f521084017f3004200fe98021005f4c010802fd6008401fcb004200be58021005fcc9a8002fd64d4001bfaa6a000df55350005fcc7a8002fd63d4001bfa9ea000df54f50005fcc5a8002fd62d4001bfa96a000df54b50007be65a8003ee32d4001ee996a000fb4cb500079a65a8002fe61d40017eb0ea000dfd4750006faa3a8002fd65940017f324a000bf59250006fca9280037c54940017f31ca000bf58e50005fcc528002fd6294001ef994a000fb8ca50007ba6528003ed3294001e6994a000bf98650005fac328002fe6094001bfa84a000fed4250005fec8a8003bf64540015fb22a000bf1915000778c8a8002bc6454001bfaa2a000df55150005fec6a8002fc6354001bfa9aa000df54d50005fec4a8002fc6254001bfa92a000df54950007be64a8003ee3254001ee992a000fb4c9500079a64a8002ff61540017e30aa000dfd4550006faa2a8003fb5054001bf282a000bf99450005fcc828003be64140015f320a000bf590500077ac828002bd6414001bf2a0a000df15050005fcc628003de63140016f318a000bf58c50007bac628002dd63140017f310a000fb98850005dcc428002fd6214001f6b10a000bb58850007be6428003ee3214001ee990a000fb4c8500079a6428002fe6114001fb308a000bd98450005fac228003f561140017ab08a000bf98050006fea028003fa5014001bea80a000fe54050005fecba0002fe65d00017eb2e8000bf197400077ca9a0003bd54d00017f31e8000bf58f400077e87a0003bd43d00017f3168000bf58b400077e85a0003bd42d0001ef9968000fb8cb40007ba65a0003ed32d0001e69968000bf98740005fac3a0003bf41d0001dea0e8000bfd9640005fccb20002fd65900017e32c8000bf592400077ea920003bc54900017f31c8000bf58e40005fcc520002fd6290001ef9948000fb8ca40007ba6520003ed3290001e69948000bf98640005fac320002fe6090001fd2848000fe542400077e8120003fb40900017fb2a8000dfd9540004fecaa0002fe65500017eb2a8000bf19540006f8caa00027c6550001df2a28000ef55140005fec6a000
  | 3 => 0xf9948200fb8ca41007ba6520803ed3290401e69948200bf98641007eca320803f55190401dfa0c8200fdd0641005fcc120802fd60904017fb2a8200bf99541005facaa0802fc6550401dfaa28200ef15141005fec6a0802fc6350401dfa1a8200ef50d41005fec4a0802fc6250401dfa128200ef50941007be64a0803ee3250401ee9928200fb4c9410079a64a0803f65150401faa8a8200fdd05410077c82a0802ff60504017e3028200bfd9441005fcca20802fd65104017e3288200bf99041005fcc620802fd63104017f3108200bf58841007be6420803ee3210401ee9908200fb4c8410079a6420802fe6110401dfa088200fd904410077a8220803f541104017f3008200bf58041005fecb98802fe65cc4017eb2e6200bf19731005fec998802fe64cc4017eb266200bf19331005fcc598803ee62cc401773166200bf58b31007dac598802ed62cc401ef9966200fb8cb31007ba6598803ed32cc401e69966200bf98331005fac198802ff658c4017f32c6200bf59631005f8cb18802ff648c4017f3246200bf59231005f8c918802fd638c401ef29c6200f754e31007bc8718803dd438c4017f3146200bf58a31007be6518803ee328c401ee9946200fb4ca310079a6518802fe618c401ef98c6200fdcc631005fcc118802fd608c4017fb2a6200bf99531005faca98802fc654c4017fb226200bf99131005fac898802fc644c4017fb126200bf18931007be6498803ee324c401ee9926200fb4c9310079a6498803f7314c401ef18a6200bfd8131005f8c098802ff650c4017f3286200df99431004fcca18802fd650c401beb2862009f59431005f8ca18802ff640c4017f3206200ef990310057cc818802fd640c401deb206200af59031005f8c818802fe630c401ef2986200f754c31007bc8618803dd430c4017f3106200fb98831005dcc418802fd620c401f6b106200bb58831007be6418803ee320c401ee9906200fb4c8310079a6418802fe610c401ef9886200fd8c431007ba6218803f5310c4017f3006200fe98031005f4c018802fd600c401fcb006200be58031005fecb90802fe65c84017eb2e4200bf19721005fec990802fe64c84017eb264200bf19321005fec790802fe63c8401ef31e4200b798f21005fac790803dd63c84016eb1e4200bf18f21007be6590803ee32c8401ee9964200fb4cb210079a6590802fe60c84017eb064200bfd9621005fccb10802fd65884017e32c4200bfd9221005fcc910802fd64884017e3244200bfd8e21005fcc710802fd63884017e31c4200bf58a21007dca510803ed5288401f72144200fb50a21007be6510803ee3288401ee9944200fb4ca210079a6510802fe6188401f790c4200fdc8621005fcc110802fd60884017fb2a4200bf99521005faca90802fc65484017fb224200bf991
  | 4 => 0x3dd424c801e6a126400f710932007988499003df614c801ef30a6400f758532007b8c299003df604c801ef3026400f758132007b8c099003ef654c801f732a6400fb59532007d8ca99003ef644c801f73226400fb59132007d8c899003ef544c801f72a26400fb55132007d8a899003ef634c801e7b1a6400fbd4d320079ea699003ee534c801e729a6400fb54d320079aa699003ec534c801e629a6400fbd0d320079e8699003ee434c801e721a6400fb50d320079a8699003ec434c801e621a6400fbd8532007dcc299003ed614c801f630a6400fbd8132007dcc099003ed604c801f63026400f3d95320079cca99003cd654c801e632a6400f3d91320079cc899003cd644c801e63226400f3d51320079ca899003cd544c801e62a26400f3d85320079cc299003cd614c801e630a6400f3d81320079cc099003cd604c801e63026400bfd9432005fcca19002fd650c8017e3286400bfd9032005fcc819002fd640c8017e3206400bf98c32005bcc619002fe620c801773106400f7cc832007dc6419003dd320c801f69906400f34c832005fcc219002fd610c8017f3006400bf58032005fcc9a8802fd64d4401bf2a6a200df15351005fcc7a8803de63d44016f31ea200bf58f51007bac7a8802dd63d4401bfa9ea200df54f51005fcc5a8803ee62d440177316a200bf58b51007dac5a8802ed62d4401bfa96a200df54b51007be65a8803ee32d4401ee996a200fb4cb510079a65a8802fe60d44017eb06a200bf59651005fcc928803be64944015f324a200bf592510077ac928802bd64944017f31ca200bf58e51005fcc528802fd6294401ef994a200fb8ca51007ba6528803ed3294401e6994a200bf98651006fea328803f751944017f304a200bf58251005fec8a8802fc6454401bf2a2a200df15151005fec6a8802fc6354401bfa9aa200df54d51005fec4a8802fc6254401bfa92a200df54951007be64a8803ee3254401ee992a200fb4c9510079a64a8803f75154401bf28aa200bfd8151005f8c0a8802fe65144017f320a200bf59051005fcc628802fd63144017f310a200bf58851007be6428803ee3214401ee990a200fb4c8510079a6428802fe6114401bfa88a200fd94451006faa228803f551144017f300a200bf58051005fecba0802fe65d04017eb2e8200bf197410077ea9a0803bc54d04017f31e8200f798f41005bcc7a0802fd63d0401eeb1e8200b758f410077e87a0803bd43d04017f3168200fb98b41005dcc5a0802fd62d0401f6b168200bb58b410077e85a0803bd42d0401ef9968200fb8cb41007ba65a0803ed32d0401e69968200bf98341005fac1a0802ff65904017f32c8200df99641004fccb20802fd6590401beb2c82009f59641005f8cb20802fd64904017f31c8200bf58e41005fcc520802fd6290401e
  | 5 => 0x8742005fcc1a1002fd60d08017fb2c8400bf99642006fccb210027e65908017eb2c8400df59642004facb21002fc65908017eb248400bf98e42007bcc721002de63908017eb1c8400f758e42005bac721002fe6290801f72948400fb54a420077e8521003ef42908017f30c8400bf58642005fcc121002fd60908017fb2a8400bf99542005facaa1002fc6550801dfaa28400ef15142005fec6a1002fc6350801f72928400fb54942007de84a1003be42508017fb0a8400bf18542005fec0a1002fc60508017fb288400bf99442005faca21002fc65108017f3208400bf98c42007bcc621002de63108017eb188400f758c42005bac621002fe6210801dfa108400fb908420077a8421003ed42108017f3088400bf58442005fcc021002fd60108017fb2e6400bf99732005facb99002fc65cc8017fb266400bf99332005fac999002fc64cc801efa9e6400f794f32007baa799003dc53cc801efa1e6400f790f32007ba8799003dc43cc8017f30e6400bf58732005fcc199002fd60cc801efb2e6400f799732007bacb99003dc65cc801efb266400f799332007bac999003dc64cc801efaa66400f795332007baa999003dc54cc801efa966400f794b32007baa599003dc52cc801efa166400f790b32007ba8599003dc42cc801efb0e6400f798732007bac399003dc61cc801efb066400f798332007bac199003dc60cc8017fb2c6400bf99632005facb19002fc658c8017fb246400bf99232005fac919002fc648c8017eb1c6400b758e32005fcc519003ef528c801f72946400fb54a32007d8a519003ef428c801f72146400fb50a32007d88519003df328c801f79946400bf98632005fac319002fe608c8017eb046400fbd9632007dccb19003ed658c801f632c6400fbd9232007dcc919003ed648c801f63246400fbd5232007dca919003ed548c801f62a46400bb58e320059ac719003ef538c801f729c6400fb54e32007d8a719003ef438c801f721c6400fb50e32007d88719003ef618c801f730c6400fb58632007d8c319003ef608c801f73046400fb58232007d8c119002ff654c8017f32a6400bf59532005f8ca99002ff644c8017f3226400bf59132005f8c899003df534c801ef29a6400f754d32007b8a699003df434c801ef21a6400f750d32007b88699003ef524c801f72926400fb54932007d8a499003ef424c801f72126400fb50932007d88499003ef324c801ef1926400bfd8532005f8c299002ff604c8017e3026400f7d9532007bcca99003dd654c801ee32a6400f7d9132007bcc899003dd644c801ee3226400f7d5132007bca899003dd544c801ee2a26400f7d89320079ec499003df524c801e7a926400f7949320079ca499003dd524c801e6a926400f71493200798a499003df424c801e7a126400f7909320079c8499
  | 6 => 0x1eeb18a800b758c54005fcc42a003ee621500177310a800bf58854007dac42a002ed62150017f308a800fd98454005ecc22a002fd6115001fab08a800bd58454005fcc02a003fa60150017d300a800bf58054007f2c02a002f960150017f326a600bf59353006fca9a98037c54d4c017f316a600bf58b53005fcc3a9802fd61d4c017f306a600bf58353005facb29802fe6494c01df324a600af99253005fac929803bd6494c015eb24a600bf98e53006fea729803df5394c017f314a600fb98a53005dcc529802fd6294c01f6b14a600bb58a53005fcc329802fd6194c017f304a600bf58253005fec8a9802fc6454c01bf2a2a600df15153007bea6a98037e5354c017fb12a600bf18953005fec2a9802fc6154c017fb02a600bf18153005fcca29802fe6414c017eb20a600bf98c53006fea629803de5314c01bea98a600f754c53005fcc429803ee6214c0177310a600bf58853007dac429802ed6214c017f308a600bf58453005fcc029802fd6014c017fb2e8600bf99743005facba1802fc65d0c01dfaa68600ef15343005fcc5a1802fd62d0c017f30e8600bf58743005fcc1a1802fd60d0c017fb2c8600bf99643006fccb218027e6590c017eb2c8600df59643004facb21802fc6590c017eb248600bf98e43007bca721803dd5390c01dfa1c8600f7d0e43005fcc521803ee6290c01773148600bf58a43007dac521802ed6290c017f30c8600bf58643005fcc121802fd6090c017fb2a8600bf99543005facaa1802fc6550c01dfaa28600ef15143007bca6a1803dd5350c01efa1a8600ef90d43005fec4a1802fc6250c017fb0a8600bf18543005fec0a1802fc6050c017fb288600bf99443005faca21802fc6510c017f3208600bf98c430077e8621803de4310c01dea188600f750c43005fcc421803ee6210c01773108600bf58843007dac421802ed6210c017f3088600bf58443005fcc021802fd6010c017f326a400bf59352006fca9a90037c54d48017f31ea400bf58f52005fcc3a9002fd61d48017f306a400bf58352005facb29002fe6494801df324a400af99252005fac929003bd64948015eb24a400bf98e52007bcc729002de63948017eb1ca400f758e52005bac729002fe6294801bfa94a400fbd4a52005fcc329002fd61948017f304a400bf58252005fec8a9002fc6454801bf2a2a400df15152005fec6a9002fc6354801f7a92a400df94952005fec2a9002fc61548017fb02a400bf18152005fcca29002fe64148017eb20a400bf98c52007bcc629002de63148017eb18a400f758c52005bac629002fe6214801bfa90a400fb94852006faa429003ed52148017f308a400bf58452005fcc029002fd60148017fb2e8400bf99742005facba1002fc65d0801dfaa68400ef15342005fcc7a1002fd63d08017f30e8400bf5
  | 7 => 0xc1811000069cc5e94410033e4c256a0008c400032800087800000000000100100000100800400000000100000000700800000000800a00200400100300500000000800500700400201f00000100100200000200200400000300000100a00300000100100500900100000000400000000900000000000000400000600700000200000700000000300000100100800200b00200500100200200300001000100100000600000300a00800000000200300101800300200000300200400401300f00100100400d00200100700101300300200600100200900000000300800601b00000100100100600e00400000000300100300100100200b00001200400200700500000200900000000000000100300000000200e00000500200200000200400000600300300401800200800400000000100100500000700200100000000400100800000000000100200100000000000700600400300200000500000b00801700000500400600200100200201100000000100100200000000100000300000100001300d00100000000100500000400000500100000000100100300100000000300500000500000000000700000300100300000100000100000800000100600100200600100300500100f00000100300100100000000100100000100200300200900300000a00100500000200100200000d00300300100100600c00400000400000800100000000200d00100900000100500300100400100000100100200100000000100200000300700a00000100000000000200000100000000100001800100000000500f00000000300100100100600b00600200a00800200500000700000000100100200200b00400000b00200c00400000200000000000000200002301200100300000600000400300200500900000000200100200900000d00100900200000400200a00000200400000000a01100400300000000a00300200400900200700300500100500100500400500400000400100000000500000500400000000000200200000701100100000000100000500100000700400100300000a00c00000000400300201101700200101200000000200200000100000300000000200100000100400100000000000c001001003003000000000005009000005fcc7aa002fd63d50017f316a800bf58b54005fcc3aa002fd61d50017f306a800bf58354005facb2a002fe6495001bfaa4a800efd52540067ea92a002fe63950017eb1ca800bf98a54005fac52a002fe61950017eb0ca800bf98254005fac12a003bf5455001bf2a2a800bfd8d54005f8c6aa002ff62550017e312a800bfd8554005f8c2aa002ff60550017e302a800bf99454005fcc82a0037f5415001df2a0a800df550540077aa82a0033d54150017f318a800f798c54005bcc62a002fd631500
  | 8 => 0x44e8582000748ab80005741f80ce0000000004040000e800000000000034e00038c00029e14e004a7837266800000000073e0003f607e5184de2743c264e42c000000a6a0000000000b00000000c80000000000000002665b49864c0a1826230200000006000000000000032400042e000bd808a6f2ad200000062a16ca9a47c00048662894a2381e4168000bac00053e248af60000000002d61c66e80000000002d40001623bc04a00000061e00000075a000000bb297a48421a1ac05cb260000003f00005cc000200000b508a268e01c0007ce1b4424b44476516308824474b0a8f6000854bb04cc39e58e8fc86039c000000a5a7acbde0000f692a00000054a9005480007e4b88000868000000ae800028600000000039400083c244c4818e1fe7f831a0000003180000004f80000005f400015600000032c00000071400096c856000b6e014a5c230000228830000000afab7c5567a40269d4780c167c80002bc0002a600000018ac2a998bf67ea0000000000004d482c00000000064a00000000000002e72ebf4aea0001ca584000000000000000334000b4a7e894600000000000031000000000056000089a7640007c20803fab2c7eeb3672402059c00084e2dc7c0a305f0810b7e7360005c40006420000000000002560004480000006180000000000006c80001f0af200000090a00020200000020e0006068ce0000008825f262c00000000000037400041ea360d40000000005960000002544f20005ee00000014c48c9d60000de5f63c00001222d838234ab92c6c48044200044000000000072c0003460000000009589da0009760000000cc4f6478b1a0000009484a600056ca600000000007da7066faaf000003ca7a4a49267ae3a0be800092c0001422fca0ab5e0006860562c092454c0000000caa8c930000aba2085684360005864f0ace6dcbfc36805e5045080009ec00000019000004c15ca3831c000000250048380154b3a00033cbfa00015223e37c2880e20002941b6c643c6000700a163c4a1cb120000005649d00005f86823a80004085c80003a600046200c99e5be2f4b824521aa0003ee24e000000000b060004ea9a830c00028c0003708a618238a1140000000000000000000000000003869a4c0e000000ad4042a505c672a25a796aee000b585ae3767c42c8a4a378a62c0c0a05b000009600045c0002f8000000806000b689e08a40004ba00020406c0008e85268be0002e2b3e00084c00000089800000000ac206b60000002a80000000a40000003f20000fa78c0f8000aae000c5a6de97eb62c1e0009100007fa5fe64000096eadc0007768d4000c428880007fc444000a1a000000000000678a9c01e4fa000b1ea46224000c2cb52000330c1aa687b28f86d0000000000858c3061aafe000c289228c821e00087c0
  | 9 => 0x57c434b5ca740003f815a00025201a000b540006607204ac742b1600000082200062e6ec00017800005a000000000000b8e7661a8000b4e4380c60000000002da9d81989e86fc9842326f84c812a0000000005520525ce19c2f02e40005885fa69895e6e204e00081a0004b8c6a00000000091870e00000069000070c47a9c42ca5380920003529645a20009f63a200054e9ca1d41d6000a5e000b106aaaa259a0002820000387021a09ce29290cb7475c2b03de0008d0a4c6fe00000067a23c000aca85ab5a31e0006da7f24dc884c66a0cb564887544a0c082980000dc0005a026a2c45e60001c046ea1eb3c158920b466f0738a2424c9c2a28982398a6cc06a9252067460c9ac6460003d20008ba8043e80000000000000000000008e27083500000000000008743ba3e20008dc00000000047eadab9c000a660000ae4ce000000894848a7e2ee78e4e481273a63a10aa882b8036c547c627861006a43027a000b6c000bf800000049a12cad0784498a2000000000075e46403e96a0547bc000000000000000000000000ab00009c0000c340003b20000000000000a2000abc00006e0000002466d68b00008ee00000000048e0000006b80002c61040000000006ac974320170000000000c586143b60864109ae8cc45e000000626c565924469083443b0000b2810e7e03408805542581963622145d0360bb48442d2a8003458a0008903be1089b20f0c50272000b789068ca000008612c260aca3271000039287e0be0000c0c244228180000188524720004aaa9e6c00000007d40001d86ca0006160aa00039a00043a85e000000000314000000000000546420000000000866000000b843040000009f846c32a402000000baa00045a0004565ea0003ca4004163161fa0005e200000000000000045800000000000014a9de172c14000000726bfe000ad85ec16e2b6124aa48de622896950ade0000004b6000c124ca18c00000084a0d23aa0829e40700000a60006be2cc0005c2b0e5e83e05dc0000002a000000074466c2f269a23497c23600000027c0000007f668400000000000008876249c0006e60006e49960000008da00007c0002d05d6000bae58c7be82684288e5944543ce0009fa000000be26f60009b80005c00d0ba215070409c0000fe5a8000966000ab40008360000000000000160000006a0000b08000ae694285cbd62400308fa800c4c9be00067e00000000000000041a024b902961480000000003909ee364b6400029aae400077c0ec9c69aab40b8600072800043ebbe0005a6a96bf216a00076025eba01fc8f46808bc000000ab27582c279055c0009a60c24c6672000000000a6e1b29ba000000000000000544000062b38acc0004d04d2542000000b7a0004b400000063e6a800000000097853000077a50c000000bda2a
  | 10 => 0x7d67f40002a2000000000000abe00000029c0007120000eea98000b2e0000005987e2bc26a4ae21e2aaabc689e6965906303b47a640e0003560009800000004bc000000000000000b6a43c000b988aac2e0f2012000aa8b32ac85e0c0490200000000000086ca0ead671e71c6440006248f01885ba9622aa0008b4a3e000beaa8e7685b8a869fe00087a8c6af469400000000000074e0000000002120000001385720e0bc0218990000000c5c3cc5da00090eac68c28865a45deb807868d287600095a95c51a2807163fc0000007786321ba1e00000000288284d8970a0893850e41400034c10283e20c6f4c6e78a0005d800050a3ea676b306b053c6b227e3e637e0d609000000060400091c00049e130000000000000bd4788662502000000000000000084c327b8bce3d480c000000c4e000000000772a58a008b698e26e99c770bb660e000000a540000000006a691abee3320443dc4be00038800000000000000060a00066e00000000016465065ca2e570532c520f4000a047a871a000000000bec140260a48000000a70b9eb8a000bd225c36609400000017e0004b2a263da904a940007ca870ae000067c64c000000c0a5d440a000000000000a227404b00006546561cc5140c4ba80000003e400077e00094e89200084646600000000038470a1de0000001ae1da16014405863412e9321b80005500006640babd01e81ea8fe0007820769680000744948642e80000005bc1204069e673c44a00083820a93e00036e11e6ee5ac6700da28a00000059e00011c00036a0000006cc1d2460b2ac620509b691452e802b42b003f493a74c4e026c8d800065e88c1f679eb2247000079c35c00057a36c29053a578afc000000000c44ba4b240000000e687200000003a23a00000019e0000007d00004680000000006b456232ea7c2de42a82066a0000006ea76a0000000006c4ac2b6652a648000952a3c1060002767e6b8c4fe7b60000007744968a0bca30a8e609e000b9641215e3ac5060008ae000000000000000000a02000000166000000b700000000000000008ac2ac216312ac00008ec7d89c80002421367222209880000000000000002ae000174000000000a42000338354000002000af86c2000000000a8a0002267984da9340004ec0005287eca0648a752bc475043235e10c9a28345aa0006584f45e495655804000051c4d681c7dc1288e01be51ec029128d656e3009728321bc45011689c44e85002c7ba0bcaa02fa00000041800000088a0000005fc210270000000000a141ec00000007892ec00000c60746000348000a640003ec00000066600000058022e0000000003580001949dcb3432655a000a728b8a840660006d21dc3fe0002220001a20000000000005348f20003360001340004fc000792b600007a0ba600052c000
  | 11 => 0x9e26ba0009d274a7320325d2bba0000001a6a1200080a00013a4a23a47d2000b7691e1f265a000000aec0000006367de000482000b0c19a4e60000000e44e22e0000b1491600000000050039655e2ea2b43c8000000000000000000a820000b60980000005241ee00000000000022c07a9cc118b20000000000ac40a817c00062086a0000009bc7180000008b20000d811ab040060006c6c3e0005b6000000b4800014600000000069e00082e3d0000000000000b4c28e0b20000000000003b8816a2a0680007a200000057e2fe00000000000000000069282a0006a200000026896083a0000000009f038e41cbe63d6000b9a2be0000000000009366e00009ea000000a5200068a0000fc688730000000000a4e1ce000000510a34a90bf06ce94c21c6ae3d830604608c0000007b40009940007fe000126bcc00076c00073400046aa4006451200099a0ea35ac40608492a2ca101d09fc00000000092800076e00044c0001124a81320000000b894040c00002a0105b24ae00000e17a4c42b200000000000000000017600093c1c4000284c36a760000009f4000186ab6b948ea4ee5401848a8000000a44756000000000b189920001f40006386d8c4624a61c000aa686ebe0000000522000c108140009f20005ca0001c200080e00000000009a8c01c86528082ecb0281e3228e4bbc2e62cebb8c38000192000a3a0000000000000000000000003aeb72000000000000a56000c6800000000063c342c22862bdc0721e62066bc4900006020000000000000000009b400060033a00098c1a430e0000000009a000026400000008e6d4000426c4a000000be4022000794000000000aac2f6000000000000b1c180954bc80000000000008400000007f000042879ac1c00000000037a5760000000007aa0007b000000000000000000000000000068c0b40000000001b07cc9b056600022a00098a0002ba00013ec3ac3c13c5360
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe72d9010004ed72d9010004bd76990100063e65990100063d65990100063e65590100063d65590100047e75190100047d7519010004be7419010004de7319010004dd7319010004ee7219010004ed7219010004f671190100047e75d8c100047d75d8c10004be74d8c10004bd74d8c10004ee72d8c10004ed72d8c10004ee7298c10004ed7298c10004dd7698c100065e6598c100065d6598c100069e6498c100069d6498c10005cd7298c10006ce7298c10004dd7298c10006cd7298c10004cd7298c100065e6558c100065d6558c100069e6458c100069d6458c10004df7258c10006ce7258c10006cd7258c100047e7518c100047d7518c10004be7418c10004bd7418c10004de7318c10004ee7218c10004ed7218c10004f67118c10004fa7018c100047e75d88100047d75d8810004be74d8810004bd74d8810004de73d8810004dd73d8810004de7398810004dd7398810004ed76988100066e65988100066d6598810006ae6498810006ad6498810005cd7398810006ce6398810006cd6398810006ce7398810004ed7398810006cd7398810004cd73988100066e65588100066d6558810006ae6458810006ad6458810006ce6358810006cd6358810004ef7358810006ce7358810006cd73588100047e75188100047d7518810004be7418810004bd7418810004de7318810004dd7318810004ee7218810004f67118810004fa7018810004df76cc810004dd76cc8100065e65cc8100065d65cc8100069e64cc8100069d64cc810006ce62cc810006cd62cc810004ef768c810004ed768c8100066e658c8100066d658c810006ae648c810006ad648c810005cd738c810006ce638c810006cd638c810004df764c810004dd764c8100065e654c8100065d654c8100069e644c8100069d644c810006cf624c810006ce624c810006cd624c810006cc624c810004ef764c810004ed764c8100066e654c8100066d654c810006ae644c810006ad644c810006cf634c810006ce634c810006cd634c810006cc634c810005cf764c810006cf764c810004cf764c810006ce764c810005cd764c810006cd764c810004cd764c810006cc764c810006cf654c810006ce654c8100074e654c8100064e654c810006cd654c8100074d654c8100064d654c810006cc654c810006cf644c810006ce644c8100078e644c8100068e644c810006cd644c8100078d644c8100068d644c810006cc644c810007c7714c810007c4714c810006cd3298410006cd32980100067565c4010006b564c4010006d563c4010006e562c4010007c532c4010004f97684010006d96384010006e96284010007c93284010004f77644010006756544010006b56444010006d56344010006e56244010007c53244010004fb7644010006d96344010006e96244010007c93244010
  | 1 => 0xc210007c93288210007c93248210007c532c4210007c932c4210004de7399510004dd7399510004ee7299510004ed7299510004bf7459510004bc7459510004df7359510004dc7359510004ef7259510004ec7259510004de7399110004dd7399110004ee7299110004ed72991100047f75591100047c7559110004df7359110004dc7359110004ef7259110004ec7259110006cf72d8d10004dd72d8d10006cc72d8d10004de7398d10004ee7298d10004ed7298d10004ef7258d10004ec7258d100047e7518d100047d7518d10004be7418d10004bd7418d10004ee7218d10004ed7218d10004de7618d10005cd7218d100065e7518d100065d7518d100069e7418d100069d7418d10006ce7218d10004dd7218d10006cd7218d10004cd7218d10006d57118d10006d97018d10006cf63d8910006cc63d8910006cf73d8910004ed73d8910006cc73d8910004de7398910004dd7398910004ee7298910004df7358910004dc73589100047e75189100047d7518910004be7418910004bd7418910004de7318910004dd7318910004ee7618910005cd7318910006cf6318910006cc63189100066e75189100066d7518910006ae7418910006ad7418910006ce7318910004ed7318910006cd7318910004cd7318910006e57118910006e97018910004de76cc910004dc76cc910006cf62cc910006cc62cc910004ee768c910004ec768c910005cd738c910006cf638c910006cc638c910004de764c910004dc764c910006cf624c910006ce624c910006cd624c910006cc624c910004ee764c910004ec764c910006cf634c910006ce634c910006cd634c910006cc634c910006cf764c910005ce764c910006ce764c910004ce764c910006cd764c910005cc764c910006cc764c910004cc764c910006cf654c910006ce654c910006cd654c910006cc654c910006cf644c910006ce644c910006cd644c910006cc644c910007c6714c910007c5714c910007ca704c910007c9704c910005b57494510007c53294510004f47654510007c53254510005757590510007c53290510004f47650510007c53250510006d4638c510007c5328c510004f4764c510007c5324c510006e46288510007c53288510004f47648510007c53248510006d8638c110007c9328c110007d2318c110004f8764c110007c9324c110007d1314c110006e86288110007c93288110007e22188110004f87648110007c93248110007e12148110007c932c4110007c53284110004be74d9410004bd74d9410004de73d9410004dd73d9410004ee72d9410004ed72d94100047d76994100047e7519410004be7419410004bd7419410004de7319410004dd7319410004ee7219410004ed7219410004f671194100047e75d90100047d75d9010004de73d9010004dd73d9010004e
  | 2 => 0x6cc644c820006cd3298420006766598420006756598420006b66498420006b56498420006d66398420006d56398420007c53298420006d73298420006e63298420006d53298420006e53298420006c53298420006cd3258420006766558420006756558420006b66458420006b56458420006d66358420006d56358420007c53258420006d73258420006e63258420006d53258420006e53258420006c53258420004ed76884200066d6588420006ad6488420006cd6388420006e561884200066d6508420006ad6408420005cd7308420006cd6308420006e56108420005e97008420006cd32980200066d65c8020006ad64c8020005cd73c8020006cd63c8020006e561c8020007c93288020006f16188020004ef76480200066d6548020006ad6448020006cd6348020006e56148020004fb7648020006f16148020004be74d9710004bd74d9710004de7399710004dd7399710004ee7299710004ed72997100047e75d93100047d75d9310004de7399310004dd7399310004ee7299310004ed7299310004ee7298f10004ed7298f100047e7518f100047d7518f10004be7418f10004bd7418f10004ee7218f10004ed7218f10004de7398b10004dd7398b100047e7518b100047d7518b10004be7418b10004bd7418b10004de7318b10004dd7318b10006cf624cb10006ce624cb10006cd624cb10006cc624cb10006cf634cb10006ce634cb10006cd634cb10006cc634cb10006cf764cb10006ce764cb10006cd764cb10006cc764cb10006cf654cb10006ce654cb10006cd654cb10006cc654cb10006cf644cb10006ce644cb10006cd644cb10006cc644cb10007c6714cb10007c5714cb10005b57494710007c53294710007c53254710005757590710007c53290710007c53250710007c5328c710007c5324c710007c53288710007c53248710004bf7459610004bc7459610004be7419610004bd7419610004de7319610004dd7319610004ee7219610004ed72196100047f75592100047c75592100047e75192100047d7519210004de7319210004dd7319210004ee7219210004ed7219210004ee7298e10004ed7298e100047e7518e100047d7518e10004be7418e10004bd7418e10004ee7218e10004ed7218e10004de7398a10004dd7398a100047e7518a100047d7518a10004be7418a10004bd7418a10004de7318a10004dd7318a10006cf624ca10006ce624ca10006cd624ca10006cc624ca10006cf634ca10006ce634ca10006cd634ca10006cc634ca10006cf764ca10006ce764ca10006cd764ca10006cc764ca10006cf654ca10006ce654ca10006cd654ca10006cc654ca10006cf644ca10006ce644ca10006cd644ca10006cc644ca10007c7714ca10007c4714ca10007ca704ca10007c9704ca10007c9328c210007c9324
  | 3 => 0xe654ca20006cd654ca20006cc654ca20006cf644ca20006ce644ca20006cd644ca20006cc644ca20007cb704ca20007c8704ca20006cd3298620004df7358620004dc7358620006cd3258620005cd7308620005e97008620005cd73c8220004bf7459520004bc7459520004de7319520004dd73195200047f75591200047c7559120004de7319120004dd7319120004ed7298d20004f77158d20004f47158d20004ee7218d20005ad7494920005cd7394920004ec76549200056d7590920005cd7390920004ec7650920005cd738c920004ec764c920006cf634c920006cc634c920006cf764c920006ce764c920006cd764c920006cc764c920006cf654c920006ce654c920006cd654c920006cc654c920006cf644c920006ce644c920006cd644c920006cc644c920007cb704c920007c8704c920006cd32d85200047e75185200047d7518520004be7418520004bd7418520004de7318520004dd7318520006cd3218520004ee76c8520005cd73c8520007c932c8120004be74d9420004bd74d9420004de73d9420004dd73d9420004f671d9420004f571d94200047d76994200047e7519420004be7419420004bd7419420004de7319420004dd7319420004ee7219420004f67119420004f571194200047e75d90200047d75d9020004de73d9020004dd73d9020004f671d9020004f571d9020004bd76990200063e65990200063d65990200063e65590200063d65590200047e75190200047d7519020004be7419020004de7319020004dd7319020004ee7219020004f67119020004f571190200047e75d8c200047d75d8c20004be74d8c20004bd74d8c20004f671d8c20004f571d8c20004dd7698c200065e6598c200065d6598c200069e6498c200069d6498c20006ce7298c20004ed7258c200065e6558c200065d6558c200069e6458c200069d6458c20004df7258c20006ce7258c20004dd7258c20004cd7258c200047e7518c200047d7518c20004be7418c20004bd7418c20004de7318c20004ee7218c20004f67118c20004f57118c20004de7398820004dd7398820004dd76cc8200065e65cc8200065d65cc8200069e64cc8200069d64cc820004ed768c8200066e658c8200066d658c820006ae648c820006ad648c820005cd738c820006cd638c820004df764c8200065e654c8200065d654c8200069e644c8200069d644c820006ce624c8200066e654c8200066d654c820006ae644c820006ad644c820006cf634c820006ce634c820006cd634c820006cc634c820005cf764c820006cf764c820006cf654c820006ce654c8200074e654c8200064e654c820006cd654c8200074d654c8200064d654c820006cc654c820006cf644c820006ce644c8200078e644c8200068e644c820006cd644c8200078d644c8200068d644c820
  | 4 => 0x90300066e65988300066d6598830006ae6498830006ad64988300066e65588300066d6558830006ae6458830006ad6458830006ce73588300065e65cc8300065d65cc8300069e64cc8300069d64cc830006cd62cc830004ed768c8300066e658c8300066d658c830006ae648c830006ad648c830005cd738c8300065e654c8300065d654c8300069e644c8300069d644c830006ce624c830004ef764c8300066e654c8300066d654c830006ae644c830006ad644c830006ce634c830005cf764c830006cf764c830006cf654c830006ce654c8300074e654c8300064e654c830006cd654c8300074d654c8300064d654c830006cc654c830006cf644c830006ce644c8300078e644c8300068e644c830006cd644c8300078d644c8300068d644c830006cc644c830006cd3298430006766598430006756598430006b66498430006b56498430006e66298430006e56298430007c53298430006d73298430006e63298430006d53298430006e53298430006c53298430006cd3258430006766558430006756558430006b66458430006b56458430006e66258430006e56258430007c53258430006d73258430006e63258430006d53258430006e53258430006c53258430004dd768c4300065d658c4300069d648c430006cd628c430006d5618c4300065d650c4300069d640c430005cd720c430006cd620c430006d5610c430005d9700c430006cd32980300065d65cc0300069d64cc030005cd72cc030006cd62cc030006d561cc030007c9328c030006f1618c030004df764c0300065d654c0300069d644c030006cd624c030006d5614c030004fb764c030006f1614c030004be74d9720004bd74d9720004de73d9720004dd73d9720004de7319720004dd73197200047e75d93200047d75d9320004de73d9320004dd73d9320004de7319320004dd7319320006ce7298f20006ce7258f20005ad7494b20005cd7394b20006cd6394b20006cd6354b200056d7590b20005cd7390b20006cd6390b20006cd6350b20006cd638cb20006cf634cb20006ce634cb20006cd634cb20006cc634cb20005cf764cb20006cf764cb20006cf654cb20006ce654cb20006cd654cb20006cc654cb20006cf644cb20006ce644cb20006cd644cb20006cc644cb20006cd3298720006cd3258720005cd73c8720006cd63c8720006cd6348720004bf7459620004bc7459620004be7419620004bd7419620004de7319620004dd7319620004f67119620004f571196200047f75592200047c75592200047e75192200047d7519220004de7319220004dd7319220004f67119220004f571192200047e7518e200047d7518e20004be7418e20004bd7418e20004f67118e20004f57118e20006ce634ca20006cd634ca20006cf764ca20006cc764ca20006cf654ca20006c
  | 5 => 0x7c53258440006b75458440006b45458440006d73258440006e63258440006d53258440006e53258440006c53258440006cd32980400063d65d00400069d63d0040006ad62d00400078d32d0040006b561d0040006796590040007c93290040004bf76500400053c75500400063d65500400069d6350040006ad62500400078d3250040006b56150040004fb7650040006796550040007c93250040004be74d9730004bd74d9730004ee72d9730004ed72d9730004ee7219730004ed72197300047e75d93300047d75d9330004ee72d9330004ed72d9330004ee7219330004ed72193300059d7494f30005cd7294f300055d7590f30005cd7290f30006ce7358b30006ce5358b30006cd5358b30006ce4358b30006cd4358b30006cd62ccb30006ce624cb30005cf764cb30006cf764cb30006cf654cb30006ce654cb30006cd654cb30006cc654cb30006cf644cb30006ce644cb30006cd644cb30006cc644cb30006cd3298730006cd3258730005cd72cc730006cd62cc730006cd624c730004bf7459630004bc7459630004be7419630004bd7419630004ee7219630004ed7219630004f67119630004f571196300047f75592300047c75592300047e75192300047d7519230004ee7219230004ed7219230004f67119230004f57119230006ce624ca30006cd624ca30006cf654ca30006ce654ca30006cd654ca30006cc654ca30006cf644ca30006ce644ca30006cd644ca30006cc644ca30007cb704ca30007c8704ca30006cd3298630004ef7258630004ec7258630006cd3258630005cd720c630005d9700c630005cd72cc230004bf7459530004bc7459530004ee7219530004ed72195300047f75591300047c7559130004ee7219130004ed72191300059d7494d30005cd7294d30004dc7654d300055d7590d30005cd7290d30004dc7650d30005cd738c930006cf624c930006cc624c930006cf654c930006ce654c930006cd654c930006cc654c930006cf644c930006ce644c930006cd644c930006cc644c930007cb704c930007c8704c930006cd32d85300047e75185300047d7518530004be7418530004bd7418530004ee7218530004ed7218530006cd3218530004de76cc530005cd72cc530007c932cc130004be74d9430004bd74d9430004ee72d9430004ed72d9430004f671d9430004f571d94300047d76994300047e7519430004be7419430004bd7419430004de7319430004ee7219430004ed7219430004f67119430004f571194300047e75d90300047d75d9030004ee72d9030004ed72d9030004f671d9030004f571d9030004bd76990300063e65990300063d65990300063e65590300063d65590300047e75190300047d7519030004be7419030004de7319030004ee7219030004ed7219030004f67119030004f5711
  | 6 => 0xc65cc9400066f658c9400066c658c940005cd738c9400065f654c9400065c654c940006cf624c940006cc624c9400078f424c9400078d424c9400066f654c9400066c654c940006cf634c940006cc634c9400078f434c9400078d434c940006cf764c940006ce764c940006cd764c940006cc764c940006cf654c9400074f654c9400064f654c940006ce654c940006cd654c940006cc654c9400074c654c9400064c654c9400078e744c9400078d744c9400078e544c9400078d544c940006cd32d8540006cd32185400063c65d05400059d73d0540005ad72d05400078d32d05400063c65505400078d32505400067865941400073a5494140007c93294140004f87654140007395454140007c93254140007c932d01400063c65901400078d3290140004de73d9440004dd73d9440004ee72d9440004ed72d9440004f671d9440004f571d94400047d76994400063c74594400047e7519440004be7419440004de7319440004dd7319440004ee7219440004ed7219440004f67119440004f57119440004fa7019440004bd76d50400063d65d5040004bd76150400063d6515040005b97015040004ee7298c40004ed7298c400065e6598c400065d6598c40005cd7298c40006ce7298c40004dd7298c40006cd7298c40004cd7298c400065e6558c400065d6558c400069f5458c400069c5458c40004df7258c40006ce7258c40006cd7258c40004de7398840004dd73988400066e65988400066d6598840005cd7398840006ce6398840006cd6398840006ce7398840004ed7398840006cd7398840004cd73988400066e65588400066d6558840006ce6358840006cd6358840006af5458840006ac5458840004ef7358840006ce7358840006cd7358840004df76cc840004dd76cc8400065e65cc8400065d65cc840006ce62cc840006cd62cc840004ef768c840004ed768c8400066e658c8400066d658c840005cd738c840006ce638c840006cd638c840004df764c840004dd764c8400065e654c8400065d654c840006ce624c840006cd624c840004ef764c840004ed764c8400066e654c8400066d654c840006ce634c840006cd634c840005cf764c840006cf764c840004cf764c840006ce764c840005cd764c840006cd764c840004cd764c840006cc764c840006cf654c840006ce654c8400074e654c8400064e654c840006cd654c8400074d654c8400064d654c840006cc654c840006ce644c8400078f544c8400078c544c840006cd3298440006766598440006756598440006d66398440006d56398440006e66298440006e56298440007c53298440006d73298440006e63298440006d53298440006e53298440006c53298440006cd3258440006766558440006756558440006d66358440006d56358440006e66258440006e56258440
  | 7 => 0xc850006ce654c850006ce644c8500078e644c8500068e644c850006cd644c8500078d644c8500068d644c8500074e544c8500074c544c850006cd3298450006b66498450006b56498450006d66398450006d56398450006e66298450006e56298450007c53298450006d73298450006e63298450006d53298450006e53298450006c53298450006cd3258450006b66458450006b56458450006d66358450006d56358450006e66258450006e56258450007c53258450006765458450006745458450006d73258450006e63258450006d53258450006e53258450006c53258450006cd32980500063d64d40500065d63d40500066d62d40500074d32d40500067561d4050006b96494050007c932940500047f76540500053c74540500063d64540500065d63540500066d62540500074d3254050006756154050004fb7654050006b96454050007c93254050004de7319740004dd7319740004ee7219740004ed7219740004f67119740004f571197400063e65953400063c65553400047e7598f400047d7598f40004ee7298f40004ed7298f400047e7598b400047d7598b40004de7398b40004dd7398b40006ce624cb40006cd624cb400078f424cb400078d424cb40006ce634cb40006cd634cb400078f434cb400078d434cb40006cf764cb40006ce764cb40006cd764cb40006cc764cb40006cf654cb40006ce654cb40006cd654cb40006cc654cb400078e744cb400078d744cb400078e544cb400078d544cb400047e75987400047d7598740006cd3298740006cd32587400059d73d0740005ad72d07400078d32d07400078d3250740004de7319640004dd7319640004ee7219640004ed7219640004f67119640004f571196400063d65d5240005b970d52400063f6515240005b97015240004ee7298e40004ed7298e40004de7398a40004dd7398a40006ce624ca40006cd624ca40006ce634ca40006cd634ca40006cf764ca40006ce764ca40006cd764ca40006cc764ca40006cf654ca40006ce654ca40006cd654ca40006cc654ca400078f544ca400078c544ca40006cd3298640004df7358640004dc7358640004ef7258640004ec7258640006cd3258640007385494240007c93294240005b874542400073b5454240007c932542400078d32d0240007c932d02400047e7599540004bf7459540004de7319540004dd7319540004ee7219540004ed7219540004f67119540004f571195400047e76195400063d74195400065e73195400065d73195400066e72195400066d7219540006767119540006757119540006797019540004be76951400063c6595140004bc76551400063c6555140004ee7218d40004ed7218d400063c65d0d400063c6550d40004de7318940004dd73189400063c65d09400063c65509400065f65cc9400065
  | 8 => 0x6cd32587500055d73d47500056d72d47500074d32d47500074d32547500063d6495250005797095250005797015250004ee7298e50004ed7298e50004de7398a50004dd7398a50006ce624ca50006cd624ca50006ce634ca50006cd634ca50006cf764ca50006ce764ca50006cd764ca50006cc764ca50006ce644ca50006cd644ca500074e544ca500074c544ca50006cd3298650004df7358650004dc7358650004ef7258650004ec7258650006cd32586500074d32d4250007c932d4250004de7319150004dd7319150004ee7219150004ed7219150004f67119150004f571191500069e73191500069d7319150006ae7219150006ad7219150006b67119150006b57119150006b970191500047e76d51500063c64d51500063c6455150004ee7218d50004ed7218d500063c64d4d500063c6454d50004de7318950004dd73189500063c64d49500063c64549500069f64cc9500069c64cc950006af648c950006ac648c950005cd738c9500069f644c9500069c644c950006cf624c950006cc624c9500074f524c9500074d524c950006af644c950006ac644c950006cf634c950006cc634c9500074f534c9500074d534c950006cf764c950006ce764c950006cd764c950006cc764c9500074e754c9500074d754c950006cf644c9500078f644c9500068f644c950006cc644c9500078c644c9500068c644c9500074f544c9500074d544c950006cd32d8550006cd32185500063c64d45500055d73d45500056d72d45500074d32d45500063c64545500074d3254550007c932d41500063c64941500074d32941500047d76950500063d64950500063d6415050005797015050004ee7298c50004ed7298c500069e6498c500069d6498c50005cd7298c50006ce7298c50004dd7298c50006cd7298c50004cd7298c500069e6458c500069d6458c500065e5458c500065c5458c50004df7258c50006ce7258c50006cd7258c50004de7398850004dd7398850006ae6498850006ad6498850005cd7398850006ce6398850006cd6398850006ce7398850004ed7398850006cd7398850004cd7398850006ae6458850006ad6458850006ce6358850006cd63588500066e54588500066c5458850004ef7358850006ce7358850006cd7358850004df76cc850004dd76cc8500069e64cc8500069d64cc850006ce62cc850006cd62cc850004ef768c850004ed768c850006ae648c850006ad648c850005cd738c850006ce638c850006cd638c850004df764c850004dd764c8500069e644c8500069d644c850006ce624c850006cd624c850004ef764c850004ed764c850006ae644c850006ad644c850006ce634c850006cd634c850005cf764c850006cf764c850004cf764c850006ce764c850005cd764c850006cd764c850004cd764c850006cc764
  | 9 => 0xd6599021006ae72990210063e65590210063d65590210047e75190210047d7519021004be7419021004de7319021004dd7319021004fa7019021004f970190210047e75d8c210047d75d8c21004be74d8c21004bd74d8c21004fa70d8c21004f970d8c21004dd7698c210065e6598c210065d6598c210069e6498c210069d6498c21006ce7298c210065e6558c210065d6558c210069e6458c210069d6458c21006ce7258c210047e7518c210047d7518c21004be7418c21004bd7418c21004de7318c21004ee7218c21004fa7018c21004f97018c21004de7398821004dd7398821004ed7694821005ad7494821006ad6494821005cd7394821006cd63948210066e6554821006ad6454821006cd6354821004ed76908210056d75908210066d6590821005cd7390821006cd63908210066d6550821006ae6450821006cd6350821004dd76cc8210065e65cc8210065d65cc8210069e64cc8210069d64cc821004ed768c8210066e658c8210066d658c821006ae648c821006ad648c821005cd738c821006cd638c821005e5718c821004df764c8210065e654c8210065d654c8210069e644c8210069d644c821006ce624c8210066e654c8210066d654c821006ae644c821006ad644c821006cf634c821006ce634c821006cd634c821006cc634c821005cf764c821006cf764c821006cf654c821006ce654c8210074e654c8210064e654c821006cd654c8210074d654c8210064d654c821006cc654c821006cf644c821006ce644c8210078e644c8210068e644c821006cd644c8210078d644c8210068d644c821006cc644c821006cd3298421005cd73c8421006cd63c8421007c53288421004ef7648421006cd6348421004f77648421007c73248421006cd32980210067a6598021006796598021006ba6498021006b96498021006da6398021006d96398021007c93298021006db3298021006ea3298021006d93298021006e93298021006c93298021006cd32580210067a6558021006796558021006ba6458021006b96458021006da6358021006d96358021007c93258021006ea5258021006e95258021006ea4258021006e94258021006db3258021006ea3258021006d93258021006e93258021006c93258021006eb2158021006f22158021006e92158021006f121580210063e64d5350004be7498f50004bd7498f50004ee7298f50004ed7298f50004be7498b50004bd7498b50004de7398b50004dd7398b50006ce624cb50006cd624cb500074f524cb500074d524cb50006ce634cb50006cd634cb500074f534cb500074d534cb50006cf764cb50006ce764cb50006cd764cb50006cc764cb500074e754cb500074d754cb50006ce644cb50006cd644cb500074f544cb500074d544cb50004be7498750004bd7498750006cd3298750
  | 10 => 0xc431006cd62cc431007c5328c431004df764c431006cd624c431004f7764c431007c6324c431006cd32980310067a6598031006796598031006ba6498031006b96498031006ea6298031006e96298031007c93298031006db3298031006ea3298031006d93298031006e93298031006c93298031006cd32580310067a6558031006796558031006ba6458031006b96458031006ea6258031006e96258031007c93258031006da5358031006d95358031006da4358031006d94358031006db3258031006ea3258031006d93258031006e93258031006c93258031006db3158031006f23158031006d93158031006f13158031004be74d9721004bd74d9721004de73d9721004dd73d9721004de7319721004dd73197210047e75d93210047d75d9321004de73d9321004dd73d9321004de7319321004dd7319321006ce7298f21006ce7258f21006cd638cb21006cf634cb21006ce634cb21006cd634cb21006cc634cb21005cf764cb21006cf764cb21006cf654cb21006ce654cb21006cd654cb21006cc654cb21006cf644cb21006ce644cb21006cd644cb21006cc644cb21006cd3298321006cd3258321004be74d9621004bd74d9621004de7399621004dd73996210047e75d92210047d75d9221004de7399221004dd73992210047e7518e210047d7518e21004be7418e21004bd7418e21004fa7018e21004f97018e21005ad7494a21005cd7394a210056d7590a21005cd7390a21006ce634ca21006cd634ca21006cf764ca21006cc764ca21006cf654ca21006ce654ca21006cd654ca21006cc654ca21006cf644ca21006ce644ca21006cd644ca21006cc644ca21007c7714ca21007c4714ca21005cd73c8621006cd3298221004df7358221004dc7358221006cd3258221004be74d9521004bd74d9521004de7399521004dd7399521004ed72995210047e75d91210047d75d9121004de7399121004dd7399121004ed7299121004ed7298d21005cd738c921004ec764c921006cf634c921006cc634c921005e4714c921006cf764c921006ce764c921006cd764c921006cc764c921006cf654c921006ce654c921006cd654c921006cc654c921006cf644c921006ce644c921006cd644c921006cc644c921007c7714c921007c4714c921007c532c8521006cd32d81210047e75181210047d7518121004be7418121004bd7418121004de7318121004dd7318121006cd3218121004be74d9421004bd74d9421004de73d9421004dd73d9421004fa70d9421004f970d94210047d76994210066e72994210047e7519421004be7419421004bd7419421004de7319421004dd7319421004fa7019421004f970194210047e75d90210047d75d9021004de73d9021004dd73d9021004fa70d9021004f970d9021004bd76990210063e65990210063
  | 11 => 0x6cc654cb31006cf644cb31006ce644cb31006cd644cb31006cc644cb31006cd3298331006cd3258331004be74d9631004bd74d9631004ee7299631004ed72996310047e75d92310047d75d9231004ee7299231004ed72992310059d7494e31005cd7294e310055d7590e31005cd7290e31006ce624ca31006cd624ca31006cf654ca31006ce654ca31006cd654ca31006cc654ca31006cf644ca31006ce644ca31006cd644ca31006cc644ca31007c7714ca31007c4714ca31005cd72cc631006cd3298231004ef7258231004ec7258231006cd3258231004be74d9531004bd74d9531004dd7399531004ee7299531004ed72995310047e75d91310047d75d9131004dd7399131004ee7299131004ed7299131005cd738c931006cf624c931006cc624c931005d4714c931006cf654c931006ce654c931006cd654c931006cc654c931006cf644c931006ce644c931006cd644c931006cc644c931007c7714c931007c4714c931007c532cc531006cd32d81310047e75181310047d7518131004be7418131004bd7418131004ee7218131004ed7218131006cd3218131004be74d9431004bd74d9431004ee72d9431004ed72d9431004fa70d9431004f970d94310047d76994310065e73994310047e7519431004be7419431004bd7419431004ee7219431004ed7219431004fa7019431004f970194310047e75d90310047d75d9031004ee72d9031004ed72d9031004fa70d9031004f970d9031004bd76990310063e65990310063d65990310069e73990310063e65590310063d65590310047e75190310047d7519031004be7419031004ee7219031004ed7219031004fa7019031004f97019031004dd7694c310059d7494c310069d6494c31005cd7294c310065e6554c310069d6454c31004dd7690c310055d7590c310065d6590c31005cd7290c310065d6550c310069e6450c310066e65988310066d6598831006ae6498831006ad64988310066e65588310066d6558831006ae6458831006ad6458831006ce7358831006ce5358831006cd5358831006ce4358831006cd43588310065e65cc8310065d65cc8310069e64cc8310069d64cc831006cd62cc831005d571cc831004ed768c8310066e658c8310066d658c831006ae648c831006ad648c831005cd738c8310065e654c8310065d654c8310069e644c8310069d644c831006ce624c831004ef764c8310066e654c8310066d654c831006ae644c831006ad644c831006ce634c831005cf764c831006cf764c831006cf654c831006ce654c8310074e654c8310064e654c831006cd654c8310074d654c8310064d654c831006cc654c831006cf644c831006ce644c8310078e644c8310068e644c831006cd644c8310078d644c8310068d644c831006cc644c831006cd3298431005cd72c
  | 12 => 0xf654cb41006ce654cb41006cd654cb41006cc654cb410078e744cb410078d744cb410078f544cb410078c544cb41006cd3298341006cd3258341004de7399641004dd7399641004ee7299641004ed72996410065e73996410065d73996410066e72996410066d7299641006767199641004ee7298e41004ed7298e41004de7398a41004dd7398a410065e65cca410065d65cca410066e658ca410066d658ca410065e654ca410065d654ca41006ce624ca41006cd624ca410066e654ca410066d654ca41006ce634ca41006cd634ca41006cf764ca41006ce764ca41006cd764ca41006cc764ca41006cf654ca41006ce654ca410074e654ca410064e654ca41006cd654ca410074d654ca410064d654ca41006cc654ca41007c7714ca41007c4714ca41007c53294641006766554641007c532546410063e65d06410078d32d0641007c532d0641006cd3298241006cd3258241004de7399541004dd7399541004ee7299541004ed7299541004be76d51410063f65d5141005b671d51410063d65151410059d7315141005ad7215141005b67115141005b97015141004ee7218d41004ed7218d410069c6350d41004de7318941004dd7318941006ac6250941005cd738c941006cf624c941006cc624c9410078f424c9410078d424c941006cf634c941006cc634c9410078f434c9410078d434c941006cf764c941006ce764c941006cd764c941006cc764c941006cf654c941006ce654c941006cd654c941006cc654c9410078e744c9410078d744c9410078f544c9410078c544c941007c7714c941007c4714c941005b67494541007c53294541004f47654541007345454541007c53254541007c532d05410053e75905410078d3290541006cd32d81410047e75181410047d7518141004de7318141004dd7318141004ee7218141004ed7218141006cd3218141004be74d9441004de7319441004dd7319441004ee7219441004ed7219441004f67119441004fa7019441004f97019441004ee7298c41004ed7298c41004de7398841004dd7398841005cd738c841006ce624c841006cd624c841006ce634c841006cd634c841006cf764c841006ce764c841006cd764c841006cc764c841006cf654c841006ce654c841006cd654c841006cc654c841006ce644c8410047e75984410047d7598441006cd32984410078d32d0441007c53290441004bf76504410078d3250441004f77650441007c53250441006cd3298041006cd3258041004be74d9731004bd74d9731004ee72d9731004ed72d9731004ee7219731004ed72197310047e75d93310047d75d9331004ee72d9331004ed72d9331004ee7219331004ed7219331006ce7358b31006cd62ccb31006ce624cb31005cf764cb31006cf764cb31006cf654cb31006ce654cb31006cd654cb31
  | 13 => 0xca51006ad644ca51006ce634ca51006cd634ca51006cf764ca51006ce764ca51006cd764ca51006cc764ca51006ce644ca510078e644ca510068e644ca51006cd644ca510078d644ca510068d644ca51007c7714ca51007c4714ca510063e64d46510074d32d4651007c532d4651006cd3298251006cd32582510063f64951510057671951510055d73151510056d7215151005767115151005797015151004ee7218d51004ed7218d510065c6354d51004de7318951004dd73189510066c6254951005cd738c951006cf624c951006cc624c9510074f524c9510074d524c951006cf634c951006cc634c9510074f534c9510074d534c951006cf764c951006ce764c951006cd764c951006cc764c9510074e754c9510074d754c951006cf644c951006cc644c9510074e544c9510074c544c951007c7714c951007c4714c951007c532d45510053e74945510074d3294551006cd32d8151004be7418151004bd7418151004de7318151004dd7318151004ee7218151004ed7218151006cd3218151004ee7298c51004ed7298c51004de7398851004dd7398851005cd738c851006ce624c851006cd624c851006ce634c851006cd634c851006cf764c851006ce764c851006cd764c851006cc764c851006ce654c851006ce644c851006cd644c851006cd32984510074d32d4451007c532944510047f76544510074d3254451004f77654451007c53254451006cd3298051006cd3258051004de73d9741004dd73d9741004ee72d9741004ed72d9741004de7319741004dd7319741004ee7219741004ed7219741004fa7019741004f970197410063d65153410059d7315341005ad7215341005b67115341005b970153410047e7598f410047d7598f41004ee7298f41004ed7298f41005cd7298f410065e7598f410065d7598f41006ce7298f41004dd7298f41006cd7298f41004cd7298f410069f5458f410069c5458f41004df7258f41006ce7258f41006cd7258f410069e6350f410047e7598b410047d7598b41004de7398b41004dd7398b41005cd7398b41006ce6398b41006cd6398b410066e7598b410066d7598b41006ce7398b41004ed7398b41006cd7398b41004cd7398b41006ce6358b41006cd6358b41006af5458b41006ac5458b41004ef7358b41006ce7358b41006cd7358b41006ae6250b41004df76ccb41004dd76ccb41006ce62ccb41006cd62ccb41004ef768cb41004ed768cb41006ce638cb41006cd638cb41004df764cb41004dd764cb41006ce624cb41006cd624cb410078f424cb410078d424cb41004ef764cb41004ed764cb41006ce634cb41006cd634cb410078f434cb410078d434cb41005cf764cb41006cf764cb41004cf764cb41006ce764cb41005cd764cb41006cd764cb41004cd764cb41006cc764cb41006c
  | 14 => 0x5cf7458132005cc7458132006cf6458132006cd6458132005cf7158132007c77158132005c77158132005cc7158132007c47158132005c47158132006cf6158132006cd6158132007cb6058132006ce6058132005ce7618132005ce75181320074e75181320054e7518132005cd75181320074d75181320054d7518132005ce74181320078e74181320058e7418132005cd74181320078d74181320058d7418132005ce7118132007c67118132005c67118132005cd7118132007c57118132005c57118132006ce6118132006cc6118132006cf6018132007ca6018132006cd6018132007c96018132004be74d9432004bd74d9432004de73d9432004ee72d9432004de7319432004ee72194320047e75d90320047d75d9032004de73d9032004ee72d9032004de7319032004ee7219032005cd738c832004df764c832006ce624c832004ef764c832006ce634c832005cf764c832006cf764c832006cf654c832006ce654c832006cd654c832006cc654c832006cf644c832006ce644c832006cd644c832006cc644c832006cd3298432006cd3258432006cd3298032006cd32580320063d64153510055d73153510056d7215351005767115351005797015351004be7498f51004bd7498f51004ee7298f51004ed7298f51005cd7298f510069e7498f510069d7498f51006ce7298f51004dd7298f51006cd7298f51004cd7298f510065e5458f510065c5458f51004df7258f51006ce7258f51006cd7258f510065e6354f51004be7498b51004bd7498b51004de7398b51004dd7398b51005cd7398b51006ce6398b51006cd6398b51006ae7498b51006ad7498b51006ce7398b51004ed7398b51006cd7398b51004cd7398b51006ce6358b51006cd6358b510066e5458b510066c5458b51004ef7358b51006ce7358b51006cd7358b510066e6254b51004df76ccb51004dd76ccb51006ce62ccb51006cd62ccb51004ef768cb51004ed768cb51006ce638cb51006cd638cb51004df764cb51004dd764cb51006ce624cb51006cd624cb510074f524cb510074d524cb51004ef764cb51004ed764cb51006ce634cb51006cd634cb510074f534cb510074d534cb51005cf764cb51006cf764cb51004cf764cb51006ce764cb51005cd764cb51006cd764cb51004cd764cb51006cc764cb510074e754cb510074d754cb51006ce644cb51006cd644cb510074e544cb510074c544cb51006cd3298351006cd3258351004de7399251004dd7399251004ee7299251004ed72992510069e73992510069d7399251006ae7299251006ad7299251006b67199251004ee7298e51004ed7298e51004de7398a51004dd7398a510069e64cca510069d64cca51006ae648ca51006ad648ca510069e644ca510069d644ca51006ce624ca51006cd624ca51006ae644
  | 15 => 0xd7099132005cf7559132005cc7559132006cf6559132006cd65591320078f6459132006ce6459132005cf7159132005cc7159132005cf7059132005cc7059132005ce7619132005ce7519132005cd7519132005ce7419132006cf64191320078e6419132006cd64191320078d6419132005ce7119132005cd7119132005ce7019132005cd7019132005cf76d5132005ce76d5132005cd76d5132005cc76d51320078e64d51320078d64d5132005ce71d5132005cd71d5132005ce70d5132005cd70d5132005cf7695132005ce7695132005cd7695132005cc7695132005cd75951320074e65951320074d6595132005ce74951320074f54951320078f54951320070f5495132005ce7195132005cd7195132005ce7095132005cd7095132005cf7655132005ce7655132005cd7655132005cc76551320078f54551320074e5455132005cf7155132005cc7155132005cf7055132005cc7055132005cf7615132005ce7615132006ce7615132004ce7615132005cd7615132006cd7615132004cd7615132005cc7615132005ce75151320074e65151320074d6515132005ce74151320078e64151320078d64151320074f54151320078e54151320074d54151320078d54151320070d5415132005ce7115132007c67115132005c67115132005cd7115132007c57115132005c57115132005ce7015132007ca7015132005ca7015132005cd7015132007c97015132005c97015132005ce75d8532005cd75d8532005ce74d8532005cd74d8532005ce70d8532005cd70d8532005ce7598532005cd7598532006cf6598532006cd6598532005ce7498532005cd7498532006cf6498532006cd6498532005ce7198532006cf6198532007c76198532005ce7098532005cd7098532005cf7558532005cc7558532005cf7458532005cc7458532007c76158532006ce6158532005cf7058532005cc7058532005ce7618532005ce75185320074e75185320054e7518532005cd75185320074d75185320054d7518532006cf6518532006cd6518532005ce74185320078e74185320058e7418532005cd74185320078d74185320058d7418532006cf6418532006cd6418532006cf6118532007c66118532006cd6118532007c56118532006c56118532005ce7018532007ca7018532005ca7018532005cd7018532007c97018532005c97018532005ce75d8132005cd75d8132006cf65d8132006cd65d8132005ce74d8132005cd74d8132006cf64d8132006cd64d8132005ce71d8132005cd71d8132006cf61d8132006cd61d8132005ce7598132005cd7598132005ce7498132005cd7498132005ce7198132005cd7198132006ce6198132006cc6198132005ce7098132006cf6098132007cb6098132005cf7558132005cc7558132006cf6558132006cd6558132
  | 16 => 0x4d320074c6554d32005cf7454d32005cc7454d320074e5454d320074c5454d32005cf7154d32005cc7154d32005cf7054d32005cc7054d32004ee7614d32005ce7314d320074d5314d32005ce7614d32006ce7614d32005ce7514d320074e7514d32005ce7414d32005cd7414d32005ce7114d32005cd7114d32005ce7014d32005cd7014d32005ce76d0d32005cc76d0d32005cf75d0d32005ce75d0d32005cd75d0d32005cc75d0d320078f64d0d320078c64d0d320078f54d0d320078c54d0d32005ce71d0d32005cd71d0d32005ce70d0d32005cd70d0d32004ee7690d320056e7590d320056d7590d32005ce7390d320078f4390d32005ce7690d32006ce7690d32005cf7590d32005ce7590d320074e7590d320054e7590d32005cd7590d320074d7590d320054d7590d32005cc7590d32005cd7490d32005ce7190d32005cd7190d32005ce7090d32005cd7090d32005ce7650d32005cc7650d32005cf7550d32005ce7550d32005cd7550d32005cc7550d320078f7450d320078f6450d320078c6450d320078f5450d320078c5450d32005cf7150d32005cc7150d32005cf7050d32005cc7050d32004ee7610d32005ce7310d320078d4310d32005ce7610d32006ce7610d32005cf7510d32005ce7510d32005cd7510d32005cc7510d32005ce7410d320078e7410d32005ce7110d32005cd7110d32005ce7010d32005cd7010d320056e75185320056d7518532005ae7418532005ad7418532006e56118532005ea7018532005e97018532005e77158132005e471581320056e75181320056d7518132005ae7418132005ad7418132005e67118132005e57118132005ce74d95320078e74d95320058e74d9532005cd74d95320078d74d95320058d74d9532005ce71d9532005cd71d9532005ce70d9532005cd70d9532005cd7699532005ce7599532006cf65995320074f6599532005ce7499532005cd7499532005ce7199532007c67199532005c67199532005cd7199532007c57199532005c57199532005ce7099532005cd70995320074f6559532006ce6559532005cf7459532005cc7459532005cf7159532005cc7159532005cf7059532005cc7059532005ce7619532005ce7519532006cf65195320074e6519532006cd65195320074d6519532005ce7419532005cd7419532005ce7119532005cd7119532005ce7019532005cd7019532005ce75d91320074e75d91320054e75d9132005cd75d91320074d75d91320054d75d9132006cf65d9132006cd65d9132005ce71d9132005cd71d9132005ce70d9132005cd70d9132005cd7699132005ce7599132005cd7599132005ce7499132006cf64991320078f6499132005ce7199132007c67199132005c67199132005cd7199132007c57199132005c57199132005ce7099132005c
  | 17 => 0x74c6554932005cf7454932005cc74549320074e54549320074c5454932005cf7154932005cc7154932005cf7054932005cc7054932004de7614932005ce72149320074d5214932005ce7614932006ce7614932005ce75149320074e7514932005ce7414932005cd7414932005ce7114932005cd7114932005ce7014932005cd7014932005ce76d0932005cc76d0932005cf75d0932005ce75d0932005cd75d0932005cc75d09320078f64d09320078c64d09320078f54d09320078c54d0932005ce71d0932005cd71d0932005ce70d0932005cd70d0932004de76909320055e75909320055d7590932005ce72909320078f4290932005ce7690932006ce7690932005cf7590932005ce75909320074e75909320054e7590932005cd75909320074d75909320054d7590932005cc7590932005cd7490932005ce7190932005cd7190932005ce7090932005cd7090932005ce7650932005cc7650932005cf7550932005ce7550932005cd7550932005cc75509320078f74509320078f64509320078c64509320078f54509320078c5450932005cf7150932005cc7150932005cf7050932005cc7050932004de7610932005ce72109320078d4210932005ce7610932006ce7610932005cf7510932005ce7510932005cd7510932005cc7510932005ce74109320078e7410932005ce7110932005cd7110932005ce7010932005cd70109320055e75185320055d75185320059e74185320059d7418532006d56118532005da7018532005d97018532005d77158132005d471581320055e75181320055d75181320059e74181320059d7418132005d67118132005d57118132005ae74d9532005ad74d9532005cd7399532005e67199532005e57199532005cf73595320056e75d91320056d75d9132005cd7399132005e67199132005e57199132005cf7359132005ce73d5132005cd73d51320072f5495132005ce7395132005cd7395132005cf7355132005cc7355132004ee7615132004ed76151320072d5415132005ce7315132005cd7315132005e67115132005e57115132005ea7015132005e97015132005ce75d8d32005cd75d8d32005ce74d8d32005cd74d8d32005ce71d8d32005cd71d8d32005ce70d8d32005cd70d8d32005ce76d4d32005cc76d4d320074f65d4d320074c65d4d32005ce74d4d32005cd74d4d320074e54d4d320074c54d4d32005ce71d4d32005cd71d4d32005ce70d4d32005cd70d4d32004ee7694d32005ae7494d32005ad7494d32005ce7394d320074f5394d32005ce7694d32006ce7694d32005cd7594d32005ce7494d320078e7494d320058e7494d32005cd7494d320078d7494d320058d7494d32005ce7194d32005cd7194d32005ce7094d32005cd7094d32005ce7654d32005cc7654d320074f7554d320074f655
  | 18 => 0xe75183320055d75183320059e74183320059d7418332005d67118332005d57118332004be74d9632004bd74d96320047e75d92320047d75d9232005ae7494a32005ad7494a320056e7590a320056d7590a32005ae74d9632005ad74d9632005cd73d9632005cd73196320056e75d92320056d75d9232005cd73d9232005cd73192320072f5495232004ee7615232004ed76152320072d5415232005ce7315232005cd7315232005e67115232005e57115232005ea7015232005e97015232005ae7494e32005ad7494e320056e7590e320056d7590e320056e75186320056d7518632005ae7418632005ad7418632006e56118632005ea7018632005e970186320056e75182320056d7518232005ae7418232005ad7418232005e67118232005e57118232004be74d9532004bd74d9532004f67199532004f571995320047e75d91320047d75d9132004f67199132004f57199132004de76d4d32005ce72d4d320059e7494d320059d7494d32005ce7294d32004dc7654d32005cc7254d32005ce7214d32004de76d0d32005ce72d0d320055e7590d320055d7590d32005ce7290d32004dc7650d32005cc7250d32005ce7210d32004ee76d4932005ce73d4932005ae7494932005ad7494932005ce7394932004ec7654932005cc7354932005ce7314932004ee76d0932005ce73d09320056e75909320056d7590932005ce7390932004ec7650932005cc7350932005ce73109320047e75185320047d7518532004be7418532004bd7418532004fa7018532004f970185320047e75181320047d7518132004be7418132004bd7418132004f67118132004f571181320059e74d95320059d74d9532005cd7299532005d67199532005d57199532005cf72595320055e75d91320055d75d9132005cd7299132005d67199132005d57199132005cf7259132005ce72d5132005cd72d51320071f5495132005ce7295132005cd7295132005cf7255132005cc7255132004de7615132004dd76151320071d5415132005ce7215132005cd7215132005d67115132005d57115132005da7015132005d97015132005ce75d8932005cd75d8932005ce74d8932005cd74d8932005ce71d8932005cd71d8932005ce70d8932005cd70d8932005ce76d4932005cc76d49320074f65d49320074c65d4932005ce74d4932005cd74d49320074e54d49320074c54d4932005ce71d4932005cd71d4932005ce70d4932005cd70d4932004de76949320059e74949320059d7494932005ce72949320074f5294932005ce7694932006ce7694932005cd7594932005ce74949320078e74949320058e7494932005cd74949320078d74949320058d7494932005ce7194932005cd7194932005ce7094932005cd7094932005ce7654932005cc76549320074f75549320074f6554932
  | 19 => 0x8543004ed72d85430047e75181430047d7518143004ee7218143004ed7218143004f67118143004f57118143004be74d9443004ee72d9443004ed72d9443004de7319443004ee7219443004ed7219443004f67119443004f57119443004fa7019443004f970194430047e7598c430047d7598c43005cd7290c43004bf7650c43004df7650c43006ce7358843006ce4358843006cd43588430063d64153520056e7215352005757115352005797015352004be7498752004bd7498752006ae72992520069e6498e520069d6498e52006ce7298e520069e6458e520069d6458e52006ce7258e520063e64d4a52006cd63d4a52004de7319152004dd73191520063f64951520056e72951520056e72151520057571151520057970151520053e7494952004de73d8552004dd73d8552004be7418152004bd7418152004de7318152004dd7318152004f67118152004f57118152006ce7298c52006ce7258c52005cd7394852006cd63948520047f7654852004ef7654852006cd6354852004de7319742004dd7319742004f67119742004f57119742004fa7019742004f970197420063d6515342005ae7215342005b57115342005b970153420047e75987420047d7598742004de73d9642004dd73d96420066e7299642004de7319642004dd73196420065e6598e420065d6598e42006ce7298e420065e6558e420065d6558e42006ce7258e42005cd7394a42006cd6394a420066e6554a42006cd6354a420063e65d0a42006cd63d0a42004de7319542004dd7319542004be76d51420063f65d5142005ae72d51420063d6515142005ae7215142005b57115142005b97015142005ae7494942005cd7394942004ec76549420072c54549420053e7590942004de73d8542004dd73d85420047e75181420047d7518142004de7318142004dd7318142004f67118142004f57118142004be74d9442004de73d9442004dd73d9442004de7319442004dd7319442004ee7219442004f67119442004f57119442004fa7019442004f97019442006ce7298c42006ce7258c420047e75988420047d7598842005cd7390842006cd6390842004bf7650842004ef7650842006cd6350842004be74d9732004bd74d97320047e75d93320047d75d93320059e7494f320059d7494f320055e7590f320055d7590f320059e74d97320059d74d9732005cd72d9732005cd72197320055e75d93320055d75d9332005cd72d9332005cd72193320071f5495332004de7615332004dd76153320071d5415332005ce7215332005cd7215332005d67115332005d57115332005da7015332005d970153320059e7494b320059d7494b320055e7590b320055d7590b320055e75187320055d75187320059e74187320059d7418732006d56118732005da7018732005d970187320055
  | 20 => 0x4ed7298f54004de7398b54004dd7398b540053d76d52540063d76d5254004ee7298e54004ed7298e54004de7398a54004dd7398a54004ee7218d54004ed7218d54004de7318954004dd7318954004de73d8554004dd73d8554004ee72d8554004ed72d8554004de7318154004dd7318154004ee7218154004ed7218154004f67118154004f571181540053d75950540063e65950540047f7655054004bf76550540053f76550540063f76550540043f76550540053f73550540053f72550540053f71550540053c7055054004ee7298c54004ed7298c540071d5498c54005cd7298c54006ce7298c54004dd7298c54006cd7298c54004cd7298c540071d5458c54004df7258c54006ce7258c54006cd7258c54004de7398854004dd73988540072d5498854005cd7398854006ce6398854006cd6398854006ce7398854004ed7398854006cd7398854004cd73988540072d5458854006ce6358854006cd6358854004ef7358854006ce7358854006cd7358854007355498454006d66398454006d56398454006e66298454006e56298454007355458454006d66358454006d56358454006e66258454006e56258454007395498054006da6398054006d96398054006ea6298054006e96298054006f26198054006f161980540063d5458054007395458054006da6358054006d96358054006ea6258054006e96258054006f26158054006f161580540067b5458054006ba5458054006795458054006b954580540063954580540063d64153530055e7315353005757115353005797015353004be7498753004bd74987530069e73992530063e64d4e53006ae6498a53006ad6498a53006ae6458a53006ad6458a53006ce7358a53006cf5358a53004ee7219153004ed72191530063f64951530055e73951530055e73151530057571151530057970151530053e7494d53004ee72d8553004ed72d8553004be7418153004bd7418153004ee7218153004ed7218153004f67118153004f57118153005cd7294c530047f7654c53004df7654c53006ce7358853006ce5358853006cd5358853004ee7219743004ed7219743004f67119743004f57119743004fa7019743004f970197430063d65153430059e7315343005b57115343005b970153430047e75987430047d7598743004ee72d9643004ed72d96430065e7399643004ee7219643004ed7219643005cd7294e430065e6554e430063e65d0e430066e6598a430066d6598a430066e6558a430066d6558a43006ce7358a43006ce5358a43006cd5358a43006cf4358a43004ee7219543004ed7219543004be76d51430063f65d51430059e73d51430063d65151430059e7315143005b57115143005b970151430059e7494d43005cd7294d43004dc7654d430071c5454d430053e7590d43004ee72d
  | 21 => 0x8c00400200000a000200200700a8004001000000000e0060008014000002000000400a00000200000020010058000020000000000000800000300d0004007000000002000300a0004018020003000402800e0050034004015001007400402000c000400000300b000000400a000003801e001006000400201e02d8008024006005004c02e000001800001600e001801400000b00a000000e00e000000403c001005000400c000007002000000f000801800000500a002400e004001000414800100300dc000008003803800800300d005c00e003000004002e00200000000060030240000002001002800003800000200000020050000000018001009806000000000000080060170018044028000000001802c05f00000100000080050000002002003800400c000012001c00001e0058014002001001000002200000100000100170040020002012000000c010003000000000400b00100000000030018028004001001003005e008000000c00c00c00200040040020158058000006001000001200300480180060000000018018001009802000a009007004000e001019801400200000400180000130000000000007004800c040003000000003c0000010000006004005005801a00300180040020000010118000000000801400000602f007801800d0000008004003006800800001a007800000000f0088134000003001803003201e00000580160220078004000005000011800601701580040000010020000016008004807400c00100080540040020048098004001005000800001500580000540550008000000010009002400400a003001c004000000000007c002000810c030015000804000400000080ac0300010008018004003003000000c00100000e4000005001801800000500000000060090048024010004000800c000009004002400000200200e800000000a802800a013000000c002022000801801000000a000000200d000804c008012007801004a007000000400000000000240340120030004010016002801c00000a001806c0c60010050014026001001001c00200500000380060050008078000048000000400000e00e000c00200600800540c40030018078000001001000c006003006000400200100d8010004002001000805e00b00c802400e02500c80180060060130004024000002800c02400200d80d40060050010014000000001000404c0030000080006000001807801800300380080000040048000016007013000807400b0008068000001004000407c00a0010010004002000002003400d004002c00600500200ac00e00100000480020000020004000000009805c008002000801000800100000080000010018178010004000800003a000004002c07c001001803400800200680f4004007004ee7298f54
  | 22 => 0x7880003e10bb00017ec1f6503834d0c46c46d50001610d2b035a4284120000003794a068d362fab94ed4b07683884c0003c320380014700001e628300005640a311912346f728f0ff13d296f00002a02805904f10aa185062d0000000000c9100280100080000000006000000005c00e001000001800c011000000000000000000500000000000008006003001004000000200a800000c0160000000028002000000801c001003800000000f001808000201e00682040060000060010000002000000000c00b0008008006004007800c00000400180280000630010000000000001004c0040070000000002004000001001e013001800c014001001800c000006002800400200a00b008c00e042003800000401000c800c02000601e001800200400800040300100000070006002000003c01c00000000000c0010000800c0000000008040000003000801c030002001000401000300480d0006001000800406e004005800c00003200300ec00202a002803c00000800b801c00602b001800800000e004002c00000c001800c0560000048010000005015002801e00501080000180090018004002006010006400000e00f801c10e014003800001e0120068038000003000000c00800a00d808c00a000006002400201b000801400e006000800401202d006001c00402c017801800c006001003c00003d0110028004035004015000600100200480120130000000002004005000801c005000801001406f00200040280000050088000000011800000a0260000008014000000800400800000480300160190058018000007001800c000001002001c03200100000000000230040030000000007801002e000000008c03200200a801000602f000001c0020010010020014000000000000c0190130004030004000005000c0040028038008028005000400000700280100020020000018002002003005000000c000002401603f001800c004000000800003e0030018000002001004000800400000000000140030008004008002010800000a00e00000040040000098024002000000803000203e00e002803c00b00080cc0100200008008006004004801000800200f800000000a00000000280020068000002004000803400000c006800000000400b004001200c00200240140010000000002079000000001000a000000000600c000800400e00c008000800e001001001400c0070020008014003003801800400e000800c0320010018048000018004801c05e0030000000012037000800403e001000807c0020140060000006001000800400000000a803001c0000008000004010000007c01c00d003000c006001000002c0140020040024004000000000400000103f800000800a005800000800000d8004000000000006000201800400
  | 23 => 0xeb98556d460e1d01c5009c6044fa2814000afa00036f4000276000251190c958411b4ed8ae8ff56f0001b2c6ab6330e49112000342879d5361aa5462130a2208b0dc87f439c58f5441088a543600e7b788b4a0f952890992f623b00a8da53261b53d0ab140f2c9b0f932a40320312758e7d2ac3206e7224d158dd721eb648ae84bb1f3a068a96cf520fb34870630c556856170235e2438810a2814f49e3178f94a4d672a89990841d1292208fa4b4f5a6a2ccd6edf71fc0b4063e42b53903d50904810620de0034b270242044a1095b5571bb53a26d32cf97ec000a5600023d494400000131c000000010a144d93242c6a60ab8000000000000000053717012a000858846e000000000053e8524000d340001380dcc5243442dfdbfe4da1b980000000003e732ac262d1c03c2e550965470002e18ae61221da244800040400000009400004ed8ad456ca4b0002f912f29080cdb2b942e064270a425ba4000000000000081f2b1b37c0000005d28b5801a2890000e797b48700001a917d03d9000145d5fc8220001f41b824b536e11d9ab07780001e4800000000034b000094b3cb173c642763079800004028a2c908b00004ee34e0b88108721284b0b12c09c93dd1fa946caf71d394bd07e06625e92f07ac2e75b09729a10597609ad7877437e1b20a9491e0112f90c4133eccb1e78bf19940001a480006ac4313da2aa41f60006ee0e00f0e440400063caa651b56eaff400009521933d00001fb2d333a0ffcb0f35903ace24cff469340889c45a00035ad3fe210485b305b52864346a90d334b8d38d11303421c162724c1ac66824082404cfc3d83099cec690697292a3d1854c4d3cc27796741ab4ab9de924edd154e87249e094c3d582bc6f678c27c1c5cd868b055313a1b9e6192cf30c49084a60642e0914c6d45c70a34a920e50741ff0f7e8a51313261050ad727f01cd6c46a24753338a34df35192d7d98aa460a112dc0beba93d3b1c969c0003078000168000533800000013f19500005061b72ce9b9c00000021d84c000000000012e5ae62fd00003f91ca0006648000fe40000a62fec00009752a272d4e290700001a87603d00000dc4bc073f000090d65032755f8b005d0ba216928948ac68f00022f18b46a517d8001452000140a60cfa87536090000a6837c56e000080600000000a175e3671e0830d43e34a4ed17e51e60002052ae14560006ec1e6d5c017932100000000005f50f8c4ac0000000000000d2f0000001304d3763e19043d897a16a8cbc2640005df119db1c00024804accfece62bd2f28bb20004c88465a807ec0f0b19000033500036799801ac5f800b000000000000017901c20001eb87e49106168371ac03310ef8000000000000000165653b419168d250000000000032485a579b6cd0100005278c70000da70000ae40
  | 24 => 0x415282a2450e24376c5361d03a00000002d92ec8296e3b1fc2fc2cc62c143c07ec4a03104ecdbc7d3436083d47cab92230fb10b879e1aca165502b70229a564600182573b3a515e1384e7a050d08b4c3ba34a511008002d000094a91623300014b8a13000014c6dcbbc29b14e5a1c072058b14c0000000000d700000004c80060000499000000189899e01b8001a424f3246b768dbe4b86199239884b6d02a11eccf49470d298f000adc962eaca55f83f400002c1324786468368cada5c968029f0f3a0003b0a214000b4864d181cde012914288e992ecf71250aed19c00053084e44fe880000106c0000e408f9ded84e01411c2de822cbc403d2d29246c8927b9dcd17c0386359e8800043a3eb0000bc886a04732a883c0396c886fcd84b2107d28f128c0006aa1030ce25b93a40000ff665c00015c88287a323b86793606fb4a988a80007de0b228bcc5484f1811398000c6a50e28dc4daada2e81309194000263a5c93669646778bb16d63ab39d0001a6672b3ff8000e9893a4c0b2291187541959aa04ea44f000318db1a4085520114aa277e00022e575c6861a1970c000000314b7e15e20bd421253d8eabf44e68e306aaccd00032494de36c0a293397c644b2cb0d08e7c35262403697e227a14baca921ead200000017267183b10105af00003f192bccee10e0002258000ba700024cc0009436f0a5887669f10c32cd08a8df12a819380000004f1a18496c27432b88c5a0635141c8000142da12a1ae209de0000000000000bd70003291b700ad39ab64db088fb21c848c00000007bb77d8042944d70000374a850210d5c26812d00000005fe0000002d74000b604668fb998c1f900013d400000039830b9b5000000036800000000d98754000dec34581bc650ae80001d459108605c284a0fe00000000000c500000518000a9050b00000000001816d580000005da41f0c052042652df13899c075e106000081218e24299ec64abcd63695e54545331c78000fda00030d91140002a13881ab12845e508f075cbb81e64f98fac688b9c4018c1c000b2e50816a4000000518045cb663532a91c112a861e000000014a00022935754720000002808de23e261f13c492622624e9e4c00002600004a87427af49daadc56013a3fcb43c000a9c2e580012641e356a2ed18964e93dc9d9c0000000001fbc000000000000041c000000267100e0005d5a110c9e0003ecac9990ace40d134f80006a16ea02c9a920c12d000000600d713e22d08f830b08e1cb9232000135800000000023085d00005f10000445bdc0000fa94494760006de28f5bce000298027d34800044bb35c00065b4b99b8d0a60002c09ca9af8d4a196800002c13500030c057a3b853c96fc8b66b91fd9edd2360001012cc80000000651c7cc4edaf2280c210d600916e0000000bdb4
  | 25 => 0x3a397185da8c11fe80000003122ff27b42c084e1c2b6d924400019b9aa93869a237a037c000d9432a000019c0002698000c2e15c54fb6000001b801215980ae8c316f8950000c7957e84340004cd261a900a0cb5269128642d86370000000f7c00039e9e693fc8e820b9f209b877d4cb9a500006ca05e1d2daae7cc0000d8d3c229c5651b417da7e51c400005bc87255516c98721774bbb5159f263141396f452656e47c210d678c04062a83965e000147917c00000005386000002d4432a2680005ad00000010acc8f5db9d18ebac8300015b0cea66c11780015fe52d298aee4000b926080000bf08c02e000007ba6836379819bf8ad9637280150684a4158000fe80001f31f0862841659624140002e319f28619f44d119cb544ab691e47e13b0b8e00000016b0000d3223105ec6d0777054ad55130071000180400066a045000000000041ba1dc4c806d36ca3b867aba86bd8000294d1224e13959861a06bf2ddcc9a0001d600000007f868d2fa447e270000131426c3e8552ae289f465016d80006462350002124000000559131032a89b31080008d20004c437d0000d0d66a9f9c0006895138000a9c3ff326344ca705cc2a1235158ec21000000124a00045bab0c09e5d43700000e680000f980013f0bfe2d80bccbac3465c794988f0db534d0000c5e00000000007eab033b30001ace44709600018ce09a686030979848621725d400002f3b00fe52f04730a200001965573c587601921ae15683509966024dab065aa034e59018ece447f75fb935da14b1600e1bf554e00000011753ce0002d78000a6499d00014b8d3614d4e6087c9f858200008a067eb562c3927920827804100009fa86941010f9b16000623000117ea28057000000034d0000000f86d8100e8000e625a72f0800000049b0a194fcce04c11050cd166200000028780000005b1845036cca52768f25960000110853968abc600020d161896c2f58000e7811b2daa35dbea8122bb0000d747682b59f6c5b42680a88a5456408855600018f01af1b6873059ac955e124b8c7c00000008f04ae82e01aa58ca9e9550fa2b591f4b0b45e9bac74a00058723d892ea5900700007509171c680016ae82449227c10800001de9871bd2068127927c000000000000127a1155dc129c2e41e4071b42c0000001fd17884c025318789c86de2ee58b9920c96b0a5cbb4c400000000000000148a856d9ee00004d6000000000026765f8d3c0003c703daaf09046ea0e89b614a66ce22aaa5c0008dd27b0dfcb6e4a450aa28536c2000230b20000b7b0003368a1848b2912ad54d65fc3c899cd50068c0c38000000c963b68dc96e6752126800052065a000148117058c4010410a880005998000de6b9856780000000005968000bb61d007a1959512ce10488e9995a000402800183eb041598a8c
  | 26 => 0x87027f54a2b47c490b3b256a1193b248321191d4ab0970440a21885a46853308d9a72a9036a81789300d61e921f5b80b904d4948c8243655db008c3fe26f0c9a1d43da34c33215953d69c63cb9afc2786bd000000110e8f707e1ea584a0003a280008febc02d59b14f3808d1c53504fc0ba60000000c703be0001bfd86cdad1cbb590424545085a1cd30c98e00013000009dd5542e2d49cd700000000000ac2163a86d16a6d73b900009665e3577afb97d86473948904b8a00000000018a20003daa160b0615a115b058c6630302634e0f78460153b695a7ad9c494800065c8251148000eb62153c78b7424a12e14f8c249a40003c52dc88e456a5e0932552c8da2c72b2ce6685d00011bc522000000012c000b1b0bf95057583ce6e693797487d86afb014132d362f31b908da20d4d39e547ec67c2d71d08a1428740735680003c800024bd13c155659011d1ac0e65759d24d5296865b8b2db4c3db0000c88e14c3b07705656fcc382868624d4e90c6cda85078c88b3ddaf4075a01e5f98b60762c9c1782fe000027b5582fe9acc3cb000290800060514f0b907cad9a6341a8d4682c302e8a086d688d3131f7106600013183748787160000218000000390000000000055880015b000006d80cd5823046888af1660a20031888c0009e52c02df48385543a0b0d0866aa01f8b5e470441a10d36fc49689f30b2cf83107250001b25ab2857505881c17c66b1c307202e02c93e326dd41a9d22f48018d805ff1088000000b1d571308d1905a40ae9be16349064cb000176200009e806c20e42a67380009242451bc897c7a889c61030d4f62b3860024fd3a810c584a0319d4a3f130a70821e0562ce0f44202000000000000058600006ecd00612653a599524a12000139028e4423081a1c0000c000027d5be4384680a61d5660000002f2ccfab425cb345d4107d52bb840131e9c558c37782b6ac4235803d0be64a66e935451640e2e40e459b82084af823cf283bb113b7acfbeb5b475862c7fc8303018e68faea6d0002a8800000059100010145d5377a4b5b98a4118dadd807a7261a5b4f0ac0000648309184cc940002eecc9200b46a800000000041880019f88010001165c00dc3473000150e3322838000000c495be19b9af45353d29455afe25a6b40aa81ceaec4a837f98aa2f25b4b4e8a8c569250adbc1c46f631729882341db0b79c784d483a1e1206d11e9ee128938c8d8ce214b06c84603ed162ac5544838e2181bb80000005d8237d6b04df27508140d225e5faaf74f0aace0000000cb00000001d713e4ca86b907a8cf000000024adae88925b42f0cafc31368220194d266827a14718e605146330397f23660b592b937282d6970ce0caa2664c60ee5b96c410cba738a3a96e54529fd7e48ed5ec2c0149087f12234c109a6bb3d030446f4025
  | 27 => 0x660bb2d83386d668f1965aea651651136cd5c1523a01d7d38837610bae1c9ce58d42aa804c227c76772c70956ddb3f4b53884e3a46312de506c2795f5b3c5a8ec0a11207c4c603a30598bc531601007f97b47de0d832f354cc10be557689cc4dc39348f8000f063bf29ea754e9c6904ee0be95a0ced24b307456215448a2e74e1c6ec0481eb410a78034530fcdb446347137142ccd9923c9ab44bad9800605cd8c0b6700ba811434a3534b2eb4b22167075136080aaf56b4ab210383f73531a4c58209c01f26fd21cbcf0899ea14588a35748ddc62c97d000000193a91338c8d1c0008846239034886dfa1c49de4f328c425932305eac403c7310db48259000217902e2460cfb2000000000002e30c4a0704f7b1d030a28e49f33b03066b648a8f80fec3ae33a0a88f7ad100522e100fa24047f33e0bbc16a0002699b20ded078800000066139c90d9a50b5c48e30701744cf144231c6be883406b414edc21c4c6b720154067105a88d864bd6564a385774c810ed000118400040aa9dcbbacb90c617dcb367364238260000dc214eb0181c235d0000000aba66344c8000e360002db00000008a25f0ab90752a554cc983167ad8f00401fcbd02e500000005fcbce2fa16685943de396346c0000003159c91bd097c68c9b84ab400012c0a99bf26c800000005084f20000dd5a4a57100037557540005d03458000488000033400070b2cab004000a5a1ce2dd4f9604d614906137c9360af18254ca7c50002ce4c4400000030780007f14a035ddb1887853db4a9a8419a0000000320aea000000000057b17b000147418a6411d3d0da7060001d640000003d51f102241750b7277d414dbb32fb7c06a868e11126f586ed4640cac1938243557312259762b81731ac0574d7604a21d03ee6b828102751c05841a28adc00000060d97d9042013081a5d0c8a7c91db2d04ccca860ecad956d81695718c682d0aee2afb6b97c071325f21157c44d9538024c1a28c951106b43c023d13486c52dad442ab22d863c9670901b3c87edfb5e29cb4ef8cf2450216d9b0b8312aad64882def526266d34087b3791a651fa74a35f1b49488a036ae29280dc2ac4678b5ca3263d53ab2d4ab8ab643e06a13f614b3488340000d652f52240a4e5ee200b4fd32a22e55e94a52caa064c5260129caa100023786582033842c7800010500010d0092518306a4011b23304779db084200038183b47b8abb0000a6c4fc6c10ab9af0b880de00033590f4941146194ca560004f52b188b8d886661868552317194847524c4253d611b8ce46e20461bd4eb40756adabec2f4dea17515f4c86a5d2a035f53ecd4f31b26a85de1eb6dd0939adc3262bc25f80fc65d6b684280ca3c50de0af8cc44ff536091d81a076055b3d91e40276e22be47a6de43993619a5a82c1128ebc5307764fe0b3
  | 28 => 0x7c0549353658001312be712610817fe2d91363054ac20015341b1d97497f14932999887da00014594b05d8000000000000007036c003e67629600000f80fd5188ed5732bd941e175c7aa15f06c8728ede9a150b1090c481d61b836c4674826468a8b4b0a5684de14a115ac2b54200b800053c5890f340009af603902cfc8000000294800e4cc00029d8000000000085906a4b15ef033000000019daff03481330b08000000494161000168eadf535000062acfd566800085e00054aaf70d683245daad1000000065f3150f3e00040c34d4be61dc68aac50000000547800000069e49a0c60000a33462a0a8a1ccfb000214438c80461ea6c52725aa45727f59a65b843b33508b08ec5601200f4cd6a64700002c60005cda95d5ec055433000121a0000001484000000200283c0003746eeaa4c0007010002578fc4dd6386159daded2440498c9504b0d4fc87791ce6db27d91d01aa599498b60ce1aa8e0c8a6156f00f6454870060c15035ab45157443868c32f01125bb62da22806c3d72efa700402b5a6cf9801844af455a311033229a3e09a7c000c0c00035556222ab46c0751a12d2000031ec85000000000007e67b000025ad4bea782f392c1834c9330526c967ecc80251684000a114cc2445356b404ae162c3d2000428086ca00dd338797f55f07e11a0348d6e2000545a96c55e083374a71d692ce3090a5845f247e6518408d2a3da3829fa0f049ec0000000cdedb244ea0e17a889459286f8c6833618c91e881e72f4d6000072a76b3f58b44c7225c000115d4c012f00000001f09030ca02dc000df663600001727813e784419a04950000001a3a4c85398000cf2b541d91fe800064445885f1076ba141ea5a861c0921d50fc1b44124693a02cd3a0d24e412d06d40f000016e90a40003a1a2a80b8000074a98c682b014b892fd4c8c770fc1dd400000065c00016a288e39424dd0ceca00e59e410c69ad00001d0f800583848b4db8c94a0201564ed200037c85059fc25b69316f0fe6b64209aa615a20776da2d2ca028f154d2610716b9f65a16a0c3ec0b3c222c98ca2e1668a790da23502e09ec8e3868139c26e88a25702351e2045a75063d08d0ade6980a9b2cc3f4ba349083bcabc7dd3102bc97127276c4b65ccdaa7418e869c9348bb657974c052cc25ca0e5043c9e839b9c1c76e0001210288548bd3119336d3506354e9800c5d22bf5880b3c2ac1841ad87342c4771128021cfcc12738a83c83de0000000e60f1221901a123021251f000000000054d607ab855561c35e49d613cc8a42518818af8000000248000000062e33ac00060b00000b4000a505248000b844443a219480002770000bdc0000001f502fd5460000001f44000a1d4a89ed955e1984eb06d0720000000174989e7fd0e900001409f76781ecc5e816d067b33cc7e1a
  | 29 => 0xec00000011b8000780000000000000000002900000000005c88000000bbd4d1922800000036e9c7585e6af634912557c5756ce83194f49526560f910d01186f317d57aad064fd10449a86600003148e4647d6f01195b721e8226b608568396643800153c1d300000008e281e53f2568000d851999a4889000014ca104000000000000000080f1e50000b28148000000114ede3000000031a6cd5dfae684921c55f781403881a3658a04c26e44a2d8b025766dac4780000df809e11caa3534a91d3e68000be000000021bd73c12663b000038e76426ea5751d264641789f4210a5e11f0b180006b32552460d400000218001a9000018698600000b859b07c0b300004ca0a0012c0226db9625ad808160a0000ee0b236b8a4b11c63116af00c9aa46692f79c0178ec712381e90d8c02129f07945d6a913aaaa519424ba51702b0dd00c72489c083f892a0cb33640001dd6a58000000c3c5a18a80b9c0000000000fdc75700025200000000000000aaa00026327414dc16528223e433a0600360e656a000046da8243524025e92dd00006652561dfd29a000582b728e9a00009f0fa593c2182a630e97648cc0000001b2a00037f06c02f0be60000000000b53000016d60486e2c502ec00009b000000014c0003338c28eca03c42a000188a3626a697b08320004b49ac5ac239d00006f4c2853a00000018ac562388811193e8161828000ba2c7d1ad17340008953ab07f80000000002e00afe8e4000000000059363f0000000dbe2032729aac61d6798a1991a6fa4a496d10fc8ba2a5000058802b05a80007780002149178000361589a6ec000b351cdadb80006231ac00018b200019e0f11bfac50366322d98e00000017e936817d6ec8418000a211ef8880c58bd117c24e10f20000b890400c2b3728800000000002d10e1c000b240000000000c184ec2bc0024b466b13184f1aad51388164c743a25b31b956324a9000300d5a6a9900013280008cb119b74163e4d027c80e83dca471bea78197a9b832003b1156a4566f0875a86c085662f
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x8cf8759132440011990eb22648800293e15644c9100052642ac89922000ac6869c53244001988ed38a6488002b1219714c910006623b2e29922000cc8769c13244001b84e33826488002b2219704c910006e0b8ae09922000ac4864ca5144001b0ae8994a288002b12193254510006623b264a8a2000ac4864ca4144001a8aea9948288002b12193250510006623b264a0a2000ac4864ca31440015890c9926288003311d9324c510005624326510a2000ac4864c92144001988ec9924288002b2219328c110006643b2649822000ac8864ca2044001990ec9924088002b1219328411000466c14e7b2820008cd839cb650400119b05398ca080023360e721941000466c14e7b2020008cd839cb640400119b05398c8080023360e72190100062732ae53182000c4d655ca630400191cc8b94c608003235917298c100062732ae73102000c4d655ce620400191cc8b9cc4080032359173988100046743ec49902000a4e85d89320400149b0bb126408002a3a13624c81000546c26c499020008ce87189320400149d0a312640800293614624c81000547420c49902000a8d84189320400158d023126408002b2a00624c8100046743ec69902000a4e85d8d320400149b0bb1a6408002a3a13634c81000546c26c699020008ce8718d320400149d0a31a640800293614634c81000547420c69902000a8d8418d320400158d0231a6408002b2a00634c81000466c3cec9902000a4e859d9320400149b0b3b26408002a3a12764c81000546c24ec9902000cc4815d9320400119d0e3b2640800293a14764c81000526c28ec9902000a8e841d9320400151b083b26408002b1a04764c81000565400ec99020008ce87d95320400119b0fb2a6408002a3a13654c81000546c26ca9902000a4d86995320400189eed32a6408003135da654c81000627bb2ca9902000c4d76595320400119d0e32a64080023361c654c81000527428ca9902000a8e84195320400151b0832a6408002b1a04654c8100046743ec899020008cd87d91320400149d0bb22640800293617644c81000546c34c89902000c8f76991320400191aed322640800383996644c81000706b2cc89902000c8f76591320400191aecb22640800383995644c81000706b2ac899020008ce87191320400119b0e322640800293a14644c81000526c28c89902000a8e84191320400158d023226408002b161b714c81000662bb6e29902000e4565dc53204001d0ac9b8a6408002b1618714c81000662bb0e29902000e45651c53204001d0ac838a6408002f0600714c81000562c32658802000e45654cb1004001d0ac89962008002b2619328401000664bb26508020009c4874c9100400158b0c992200800331dd9324401000722b2a648802000e85644c910040015930c992200800332dd93244010
  | 1 => 0xaca994c210003a1991329842000742b22653084000ac7864c96108001c8cca992c2100039159532584200074332264b084000e85644c9610800189acab98421000323591730842000662b9ac21084000c69655c02108001952c8b8042100033258d700842000626b2ae79004000c8d645cf200800198ae6b0e4010003b04c9618802000466c14e732e20008cd839ca65c400119b0539cc9880023360e729931000527428c49962000a4d8518932c400151d083126588002a3610624cb1000527428c69962000a4d8518d32c400151d0831a6588002a3610634cb1000527428ec9962000a4d851d932c400151d083b26588002a3610764cb1000547426ca9962000a8d84d9532c400119d0f32a65880023361e654cb100052742ec89962000a4d85d9132c400119d0f32265880023361e644cb10006623b2e29962000d85744ca51c4001a8aea99483880023360a731961000466c1ce432c20008cd829cc648400119b07390c90800293a14624ca1000526c28c49942000a8e84189328400151b08312650800293a14634ca1000526c28c69942000a8e8418d328400151b0831a650800293a14764ca1000526c28ec9942000a8e841d9328400151b083b26508002a3e11654ca1000546422ca99420008ce87195328400119b0e32a6508002a3a10654ca1000546c20ca9942000a4f8559132840014990ab22650800233a1c644ca1000466c38c89942000a4e85191328400149b0a3226508003319d8714ca10005e0c00e29942000dc0719c1328400178102b82650800370dc5704ca1000466c14e732a20008cd839ca654400119b0439aca880023360c725951000466c14e732220008cd839ca644400119b0439ac8880023360c72591100060ebaae831a2000c4e755c8634400189aeab90c688003239d17218d1000646ba2e431a2000cc5725c463440018b2eab80c688003265d17018d1000664b92e031a2000cd1715c0634400185aeaba0c488003139d5731891000626baae63122000c8e745cc624400191ae8b98c488003315cd711891000634baae03122000ca9745c06244001992e6b80c488003385c570189100046743cc499220008cc87589324400149d0a312648800293614624c91000547420c49922000a8d84189324400119d0f31a64880023321d634c91000527428c69922000a4d8518d324400151d0831a6488002a3610634c91000467434ec9922000ac7815d9324400119d0c3b2648800293a14764c91000526c28ec9922000a8e841d9324400151b083b2648800313a14764c91000626c28ec9922000c8e841d9324400191b083b2648800331604764c91000664c00ec99220008ce87995324400119b0f32a648800233e1d654c9100046643aca9922000a8f84595324400151908b2a648800233a1e644c91000466c3cc89922000
  | 2 => 0x1654c93000527c2ac89926000a4c85591324c001783023826498003139d5321853000626baa6430a6000c8e744c8614c00191ae8990c298002a3a13654c83000546c26ca9906000ac681d95320c00158b03b2a64180029361a654c83000627bb2ca99060008ce87195320c00149d0a32a6418002a3a10654c83000546c20ca9906000ac681195320c00158b0232a641800293a17644c83000526c2ec89906000ac681d91320c00158b03b226418002a361a644c8300070732cc89906000e0d65991320c00191eecb22641800383995644c83000706b2ac899060008ce87191320c00149d0a322641800293614644c83000547420c89906000ac681191320c00158b02322641800391995329843000722b2a653086000e86644ca610c001d0ac8994c218002b1e1932584300072332a64b086000e45654c9610c001d0cc8992c218003a1591325843000626b2ae41886000c8d645c8310c00198ae4b08621800316595700c4300064cb22e01886000cc9625c0310c00189acab9660180032359172cc03000662b92c39806000ec132586300c00149b0b392c790002a36127258f2000562c0ce4b1e4000c8d7458e52c800189aeab1c8590002a3a13654cb2000546c26ca9964000a4e85d9132c800149b0bb22659000293a14764ca2000526c28ec9944000a8e841d9328800151b083b26510002b1a04764ca2000562c08ec9944000a8f84595328800151908b2a6510002a3a10654ca2000546c20ca9944000ac681195328800158b0232a651000293e15644ca200052642ac89944000a4e85191328800149b0a3226510002b1a04644ca2000562c08c89944000bc1811c1328800119b05398ca900023360a731912000547c22ca9924000a8c84595324800119b0e32a649000293e15644c9200052642ac899240008cd871913248001783023826490003139d5321852000626baa6430a4000c8e744c8614800191ae8990c2900023360e721942000466c1ce43204000a4e85d8d320800149b0bb1a6410002a3a13634c82000546c26c69904000ac681d8d320800158b03b1a641000293a14634c82000526c28c69904000a8e8418d320800151b0831a6410002b1a04634c82000562c08c69904000a8e84d95320800151b09b2a6410002b1a07654c82000562c0eca9904000a4d86995320800189eecb2a641000233a1c654c82000527428ca9904000a8e84195320800151b0832a6410002b1a04654c82000562c08ca9904000a4e85d91320800149b0bb226410002b1a07644c82000562c0ec89904000a8d869913208001c1ccb322641000383596644c82000647bb2c89904000e0e655913208001c1acab22641000233a1c644c82000527428c89904000a4d85191320800151d083226410002b1a04644c82000562c08c89904000e46654ca6108001c8
  | 3 => 0x69928000e0c6550d325000149d0bbb264a000293617764c94000527c2aec9928000a4c855d9325000158f02bb264a0002b1205764c9400052742cca9928000a8f84595325000119d0e32a64a00023361c654c94000563408ca9928000ac581195325000149d0c32a64a000313a1c654c94000626c38ca9928000e0d841953250001c8d0232a64a000391604654c94000724c00ca9928000e0c659d1325000170b033a264a0002a3219744c9400070632ae89928000a8e869513250001c18cb2a264a0002a3219544c9400070632aa89928000c1c655cf4150001858cab9682a00026361d32d05400070632a65a0a8000e0c654c941500014750d2a4a0a0003921953294140007852a2652828000c38765515050001990ec992a0a0003c255132541400070632a6520280008cd829cf651000119b07396ca200023360a731944000466c1ce43288000c39655c0541000189ccab94c620003135957298c400054cc00a8b188000c4e655ce621000189acab9cc420002aa60054588400052742cec9908000a4d859d9321000158d033b26420002b1606764c84000467438ec9908000a4e851d9321000149b0a3b26420002a3a10764c84000563408ec9908000ac5811d9321000119d0fb2a64200023361f654c8400056340eca9908000ac581d95321000149b0d32a642000313dda654c84000626bb4ca9908000c4f76595321000189aecb2a642000383211654c84000467438ca99080008cd87195321000149d0a32a6420002a3a10654c84000563408ca9908000ac58119532100015950032a6420002a361b544c84000646bb6a89908000e0d65d51321000151b0c2a26420003235d8544c84000706b28a89908000b8980151321000158b0531cc220002b160e629844000563c32653088000ac5864ca6110001c8cca994c22000391595329844000562c14c6b088000ac583989611000158f0c992c220002b161932584400072332a64b088000e45654c96110001563002a2c220003a1d513258440007422a264b088000a8d864cb4010001c1aca9968020003a14c961d004000724b2a65200800083c875954010001838eab1a80200030b1d5625004000546c3264a008000c8f764c94010001a18ea99280200038359532500400061a3aac2a008000e85325854010001996ec992802000392595325004000526c2ce6b166000a8d849cd62cc00158b0339ac598002a36125358b3000526c2c86b166000a8e84d9532cc00151b09b2a659800293a17644cb3000526c2ec89966000a8f84595328c00151908b2a6518002a3a10654ca3000546c20ca9946000ac681195328c00158b0232a651800293e15644ca300052642ac89946000a4e85191328c00149b0a3226518002b1a04644ca3000562c08c89946000bc1811c1328c00151f08b2a6498002a321
  | 4 => 0x25400158f02bb264a8002b1205764c950005a2c0cea992a000a4c865d5325400119d0e32264a80023361c644c95000563408c8992a000ac581191325400191d0e32264a80032361c644c950007073a8c8992a000e0d751913254001d0d0232264a8003a1604644c95000744c00c8992a000a4e86d513254001c18c9aa264a800383191544c9500060e322e7a8aa000c2c645cb515400129b0e996a2a80038319132d45500070632264a8aa000e0c644ca505400191cc8b94c628003235917298c500052cc00a8b18a000c8e645ce621400191ac8b9cc4280029a600545885000547424ec990a000a8d849d9321400158d033b26428002b1606764c85000467438ec990a000a4e851d9321400151d083b26428002a3610764c85000563408ec990a000ac5811d9321400191eed3226428003235da644c85000647bb2c8990a000c8d76591321400149b0d2a26428003135da544c85000706b24a8990a000c4d761513214001c1ac82a26428002d2600544c85000562c14c7308a000ac58398a611400158f0c994c228002b161932984500074332265308a000e85644ca611400158b0531ac228002b160e625845000563c3264b08a000ac5864c96114001d0cc8992c228003a1591325845000538c00a8b08a000e46544c96114001c88a8992c2280029361932d405000706b2265a80a000e45325875014001d12c8994a028003071d16354050006163a2c4a80a000a4d864c9501400189eec992a028003431d1325405000706b2264a80a000c34745855014001c8a64b0aa02800332dd9325405000744b2264a80a0008cd829cc65d000119b07390cba00020fa1c65553400052742cc49968000a4d8598932d000149d0b31a65a000293616634cb400052742eec9968000a4d85dd932d000158d033b265a0002b1606764cb4000467438ca99680008cd8719532d000158d0232a65a0002b1604654cb40005c2c0ce89968000e0e6595132d0001c18caaa265a0003139d5329874000626baa6530e800098d874cb41d000119b05398cb200023360e72196400041ec3eca2a48000c3b655c0549000158f02bb26520002b1205764ca4000527428ec9948000a4d851d9329000158d023b26520002b1604764ca4000467438ca99480008cd87195329000158d0232a6520002b1604654ca4000706b2ea89948000b8980d513290001c1eca2a26520002e2600544ca4000466c10e6b0c80008cd831c9619000119d0e992c3200023321d3258640007842a265284800093a87d515090001b10e8992a120003c2d51325424000466c14e632a80008cd839c8655000149b05398caa00029360e72195400062ab9ae232a8000c65725c46550001872e8b80caa0003165cd701954000634b92e032a8000c71715c06550001c18cba1264a000383195424c9400070632e8
  | 5 => 0x8802b26027258f2100547426ca9964200a8d84d9532c840119d0e32a659080293a17644cb2100526c2ec899642008ce8719132c840149d0a3b2651080293614764ca2100547420ec9944200a8d841d93288401595003b26510802b2600764ca2100547426ca9944200a8d84d95328840149d0bb22651080293617644ca21005e0c00e299442009e1801c5324840151d09b2a6490802a3613654c9210046743cca99242008cd87995324840149d0bb22649080293617644c9210046743cc899242008cd87991324840198aec38a6490802f0600714c921006273aa643024200c4d754c8604840191ce8990c090803235d1321812100526c1ce53284200a8d839ca640840191ac8b9ca4108023361d639482100646ba2c72904200c4d655ce420840119b0eb1c8410803135d5639082100662b1ae31904200a4e85d8d320840149b0bb1a6410802a3a13634c82100546c26c69904200aca80d8d320840159301b1a641080293a14634c82100526c28c69904200a8e8418d320840151b0831a6410802b2a00634c82100564c00c69904200a8e84d95320840151b09b2a6410802b2a03654c82100564c06ca9904200a4d86995320840149d0a32a6410802a3a10654c82100546c20ca9904200aca8019532084015930032a641080293a17644c82100526c2ec89904200aca80d91320840159301b226410802a361a644c8210070732cc89904200e0d659913208401c1ccab22641080383595644c82100527428c89904200a4d85191320840151d083226410802b2a00644c82100564c00c89904200ac586cc92108401c94ca994c01080392595329802100745322653004200e89644ca60084015970c992c01080392995325802100724b2a64b004200e8a644c96008401d12c8992c010802aa612525802100564c1ca4b004200a6985909600840159307212c010802b8606325802100564c1e42b004200ec1328856008401d866490ac010802a3a12624cb5000546c24c4996a000a8e8498d32d400151b0931a65a8002a3a13764cb5000546c26ec996a000ac6819d932d400158b033b265a8002d1606754cb5000707326a8996a000c8e744ca61d400191ae8994c3a80025361d32d475000563c0aec994a000ac4815d9329400151d083b26528002a3610764ca5000563408ec994a000ac5811d93294001c1ac92a26528002d2602544ca50005a4c00a8994a0008cd821cd619400119b06392c32800233a1d32586500046643a64b0ca0008cd829cc645400119b07390c8a8002a360a731915000546c1ce4322a000c95735c4645400194ae4b88c8a8003265cd701915000654b92e0322a000cb1715c06454001c18c9a9264a800383191524c95000706326a6992a000e0c6454d325400151d09bb264a8002a3613764c95000547c22ec992a000a8c845d93
  | 6 => 0x626c3cca9948200e46819953290401c8acbb8a6520803315d8714ca41005a2c28e29948200e45651c532904017830038a65208039199532546410070732a65a0c82009c7874cb419040119b0539ccaa08023360e72995410041fc3aca2a28200c39655c0545040149d0bbb264a080293617764c9410046743cca99282008cd87995325040170d033a264a0802a3219744c941006463b2e89928200b84815d1325040151d0daa264a080383d97544c941005c340ea8992820098d871513250401c1aca2a264a0802e1a04544c941005c4c00a89928200ac686dc5325040198aec38a64a0802d1614714c941005c3420e29928200d85741c532504017830038a64a0803619d132945410058ac18a8a8a8200b25821515150401663002a2a2a0803311d93254541007822a264a8a82009c7874cb4150401a1cea99482a08023360a731814100466c1ce430282008cf874c8605040119b0e990c0a0803139d5321814100626baa6430282008cd829cc651040119b07390ca20802b1a06764c84100527428ec9908200a4d851d9321040151d083b26420802b2a00764c84100564c00ec9908200a8e84d95321040119d0e32a64208023361c654c84100563408ca9908200aca8019532104015930032a642080233a1e644c841006273aa653088200c4d754ca611040191eec992822080331dd9325044100564c04e6b166200a8e84d9532cc40151b09b2a659880233a1c654cb310052742ec89966200a4d85d9132cc40119d0e3226598802a3a13654ca3100546c26ca9946200a4e85d91328c40149b0bb226518802f0600714ca31004e8c00e29926200a8e84d95324c40151b09b2a649880293a17644c93100526c2ec89926200bc1801c5324c40189cea990c098803135d53218131006473a2643026200c8d744c8604c40149b0539cca18802a360a739903100646b22e52986200c4d655ca430c40151b0929ac41880293616435883100662b12e39906200a8e84d95320c40151b09b2a6418802b2a03654c83100564c06ca9906200a4d86995320c40149d0a32a6418802a3a10654c83100546c20ca9906200aca80195320c4015930032a641880293a17644c83100526c2ec89906200aca80d91320c40159301b226418802a361a644c8310070732cc89906200e0d65991320c401c1ccab22641880383595644c83100527428c89906200a4d85191320c40151d083226418802b2a00644c83100564c00c89906200ac5868c9310c401c94ca994c01880392595329803100745322653006200e89644ca600c4015970c992c01880392995325803100724b2a64b006200e8a644c9600c401d12c8992c018802a6612535803100564c14a6b006200a598590d600c4015930521ac018802b4607325803100564c1662b006200ec1328c5600c401d846498ac01
  | 7 => 0x4d75580604c80191ae8b00c099002b1205601813200662b8ac030264009cb87580604c801b82e2b00c099002a3a13654c83200546c26ca9906400a4e85d91320c80149b0bb2264190030e5917015351006473a2e531ea200c8d745ca63d44014b3002a2c7a8803239d17398b5100646ba2e7316a200a698015162d440151d0931265a8802a3612624cb5100627bb2a4996a200a8e8498d32d440151b0931a65a880313dd9534cb5100547426ec996a200a8d84dd932d440189d0bbb265a880323a13764cb5100646c26ec996a200c4f765d532d440189aed2a265a88025361c544cb5100626bb0a8996a200e0d6415132d440168d022a265a8802d2600544cb5100466c14e7324a2008cd839ca649440151b0539cc928802a360e729925100547424ec994a200a8d849d9329440151d083b26528802a3610764ca5100565400ec994a200ac9801d9329440119d0f32265288023361e644ca510064743cc8994a200c8d879913294401d0d033226528803a1593714ca5100662bb0e2994a200b85841c53294401d0ac838a6528802f0600714ca510070732265a8ca2009c7874cb519440151d09bb264a8802a3613764c951005a340cea992a200a4c865d53254401898ecbaa64a8802d1205754c95100707b24a8992a200b4681951325440129b0e2a264a8802d1a04544c951005a4c00a8992a200ac686dc5325440198aec38a64a8802d1a14714c951006a2ba8e2992a200b85841c532544017830038a64a880271e1d32d4551006873a26528aa2008cd829cc605440119b07390c0a880233e1d321815100466c3a64302a200c8e744c8605440191ae8990c0a8802b1a06764c85100527428ec990a200a8e841d9321440151b083b26428802b2a00764c85100564c00ec990a2008ce87995321440189eec992a22880331dd9325445100466c14e7b2e82008cd839cb65d040119b05398cba08023360e72197410061cb2ae02a68200c4e755ca63d040189aeab94c7a0802a66005458f41006273aae73168200c4d755ce62d0401553002a2c5a080293a16624cb4100526c2cc49968200c8f7650932d040149d0b31a65a080293616634cb4100647bb2869968200a4e85dd932d040149b0bbb265a080313a17764cb4100626c2eec9968200c8e84dd932d040119d0fb2a65a08023361f654cb4100467438ca99682008cd8719532d04015950032a65a0802b2600654cb4100647bb2e89968200c8d76d5132d040131b0e2a265a0803235d8544cb4100706b28a89968200b868115132d0401713002a265a08023360a739964100466c1ce532c8200a4d829ce659040149b07394cb2080293a16764ca4100526c2cec9948200a4e851d9329040149b0a3b26520802b2a00764ca4100564c00ec99482008ce87995329040119b0f32a652080313a1e654ca410
  | 8 => 0xecb88a899003315d9711513200782aa2e22a26400d46655c4544c801a8acab88a899003619917115132006c2b22e22a26400cca769c0544c801992ed380a899003c25527015132006e138ce02a26400dc1719c0544c801a1aa8b80a899003329d9701513200664bb2e02a26400f09545c0544c801b84e2b80a899003705c57015132006a532ae02a26400d49655c0544c801b14c8b80a899003625917015132006a5aa2e02a26400d8a545c0544c801a92a8b80a89900362551701513200684aa2e02a26400a8d84d96614c80149b0bb24c29900263a137558532004c6c26eab0a640094e85dd1614c80129b0bba2c29900253a147058532004a6c28e0b0a640098e841c1614c80131b08382c29900351a06751853200546c26ca30a6400ac581d94614c80189ceab28c299003439d6741853200686bace830a6400d86819d0614c801a1ceaba0c299003435d5741853200647b2ae830a6400c8d655d0614c80149b0bb20c299003135d7641853200562c0ec830a6400c4d75590614c80191ce8b20c29900233e1d6118532004e3c3ac230a6400ac787584614c80198f0eb08c299002b1e156118532007233aac230a6400e4575584614c80158f08b08c299003a19d1611853200742ba2c230a6400ac480584614c801a94eb380c299003525d67018532006c53a4e030a6400d89749c0614c801d82c3380c299003315857018532006a53aae030a6400d49755c0614c801b14e8b80c299003625d1701853200760b0ae030a6400ccb655c0614c801992cab80c29900332d91701853200664b22e030a6400ccb615c0614c801b84c2b80c299003325857018532006e0b0ae030a6400cc1615c0614c80138d033aec0990027160675d813200546c26cbb0264009c6819d3604c80138b033a6c0990029361764d8132004c7c22eb302640098c845d6604c80129f0aba4c09900253215749813200564c00c33026400a8d84d95604c80149b0bb22c09900253a147158132004a6c28e2b02640098e841c5604c80131b0838ac09900351a147158132006a2c28e2b026400cc7651c5604c80198aca38ac09900361a107158132006c2c20e2b026400cc7641c5604c80198ac838ac0990037060071581320046743ec2b026400cc471d85604c801988e2b0ac099003311c66058132006873ace83026400d0d759d0604c801a1ceaba0c099003435d57418132006a33ace23026400d45759c4604c801b0ce9388c099003615d27118132006a33aae23026400d45755c4604c801b0ce8b88c099003615d1711813200466c3cc23026400c4d75984604c80191ae9308c099003315c6611813200626ba8c23026400c8d74184604c80198ae2308c099002b2600611813200626baec03026400c8d74d80604c80198ae3b00c099003705c6601813200467c3ac03026400c
  | 9 => 0x7054d32004e2c08e0a9a640094f8754c534c80119d0c3ae869900271a0475d0d32004e2c08eba1a64009ca801d7434c801393003ae8699002c3a1764d0d3200547430a9a1a6400d0d75153434c80170b022a68699002e260054d0d32004a742ce3a1a640094d859c7434c801a1ceba1c869900253a167650d32004a6c2ceca1a6400b0e85dd1434c80161d0bb22869900263a1f5450d3200687baea8a1a6400a8e86151434c801a1aea2a28699002e16045450d32005c4c00a8a1a640094e851c1434c80129b0a382869900271a047050d32004e2c08e0a1a640094e859cc434c80129b0b398869900263e1d4310d32004c7426ea21a64008ce861d4434c80138d023a88699002716047510d32004e5400ea21a64009c9801d4434c8019c2c2b80c29900271a0674d9532004e2c0ce9b2a6400d86819d3654c801b0b033a6ca99002c3a136599532004c7424e332a640098d849c6654c80198ecb38cca9900361a127199532006c2c24e332a6400b0e84d95654c80158d0332aca9900263a107059532004c6c20e0b2a64009c6811c1654c80138b02382ca9900233e1d6519532004a7c3aca32a64009c6819d7644c80138b033aec89900351a0675d9132006a2c0cebb226400c4e75597644c80161d0bb24c89900253a167199132004a6c2ce33226400d46859c6644c801a8b0b38cc89900331d92719913200547426cab226400b0e85d91644c80158d03322c89900253a147059132004a6c28e0b2264009c6811c1644c80138b02382c89900233e1d6419132004c7c3ac832264009c681ddb544c80138b03bb6a899002e160664d5132006473b2c9aa26400b0f85593544c80138d03bb4a899002716077695132005a2c0ccb2a26400c4e76596544c80161f08b2ca899002c361f549513200686c3ea92a264009c681dd9544c80138b03bb2a899002536167655132004c6c24ecaa264008ce86dc5544c80119b0db8aa89900233a18705513200466c30e0aa264009c6811c1544c80138b02382a89900271a077615132004e2c0eec2a264009ca80dd8544c80139301bb0a8990023361e76151320062742cec2a26400c8e849d8544c80119d0c3b0a89900271a047615132004e2c08ec2a264009ca801d8544c801393003b0a8990025361e6515132006273b4ca2a26400b0d84994544c80168b03328a899003139d96515132004c6c3cc82a26400c8e76990544c80161b0b320a899002e16066415132006473b2c82a26400e0d65590544c80161b0b2a0a899003439d65415132004a7c3aa82a2640098f87550544c80161f0eaa0a89900343e1d541513200487c3aa82a26400b0f86550544c80161b0caa0a899003839d9541513200706bb2a82a26400b0f81550544c80161900aa0a899003319da711513200662bb4e22a26400f05549c4544c80198c
  | 10 => 0xaa0a80091d831c1541500125b04382a82a0024d60470550540050fc32a9318a800d0d545ca631500143f0caa2c62a0028be19549885400686aa2e7310a800a2f86551621500146f0caa4c22a002b160a639845400562c1cc5308a800a3786551611500158b0531ac22a00385551635845400562c1cc4b08a800e255458961150014770caa4c02a002b260a639805400564c1cc5300a800a388055160150014770caa2c02a00386552635805400564c14c6b00a800e195458d6015001c52a9312c02a002b260e625805400714aa2c4b00a800e31549856015001c62a8b0ac02a0028e21d54580540051dc1aa8b00a800a3b82551601500147702aa2c02a0030e591701535300546c14e7324a600c39655c054d0c0149b0539ccb218020fe1d65151430061cb2ae02a28600b15811515350c01633002a2a6a18030e591701535200546c1ce5324a400c39655c054d080149b07394cb210020fe1d65151420061cb2ae02a28400b25811515250801653002a2a4a100247e1d54153320068caa2e02a66400cd1615c061cc80125f0eaa0a9190034a551701523200670b0ae030c640091f87550544c80161f04aa0a89900346551701513200587426cba926400a4e86153524c801a1ae82a6a499002d160454d4932005a4c00a9a92640098e849c7524c80131b0938ea499003439d35294932004c7424eca92640098d849d9524c80161d09baaa499002c3a13655493200687ba4a8a926400a4e86151524c80168b022a2a499002d26005454932004c7420e0a92640098d841c1524c80138d02382a499002716047054932004a7c3aa429264008ce861d7424c80138d023ae84990027160475d0932004e5400eba1264009c9801d7424c80161d0bb268499002a3a1854d093200686ba8a9a126400b8581153424c801713002a6849900253a1671d0932004a6c2ce3a126400d0e75d0a424c80129d0b3b284990025361676509320058742ee8a126400b0e85d91424c80131d0faa2849900343dd7545093200547430a8a126400d0d75151424c80170b022a28499002e26005450932004a7428e0a12640094d851c1424c80138d023828499002716047050932004a742ce4212640094d859c8424c80131f0ea10849900263a13751093200467430ea21264009c6811d4424c80138b023a8849900272a007510932004e4c00ea2126400cd1615c0614c80125f0eaa0a899002c3e0d541513200694aa2e02a26400b0e84d97534c80149d0c2a6a699003435d054d4d32005a2c08a9a9a6400b4980153534c80131d0938ea6990026361271d4d32006873a6a729a640098e849d9534c80131b093b2a699002c3a137554d3200587426caa9a6400d0f74951534c80149d0c2a2a699002d16045454d32005a4c00a8a9a640098e841c1534c80131b08382a69900271a04
  | 11 => 0xb0004aa46d0000000004b422a00000048d0004cd42523c1b32b517d2c558035739c0b625f27c0001600000d90001ad5d25293d60c448000000052142e39100037e0001290004a12db00000000011154c5e14b22014361000005a30e820c5b155600058144f4180000003452a331d4523e338b39f0662ef18e0002ee4ab06150a52252c2b631c23119d5ac54642823a21312a04856700058f0e23ea3c641014c47f40451a4291d54cf1ce3aa43512b2ae2045e301e2880ee2765b43e23da16443958b0000003264d700b44000000000040a30f2cd5e716c24b27d2eb34c3c83095e01e72a74f300000005a00048b5d013b5b70281063f757731a5202790000bc30157910b0001e820a03138108006927e02a002004290090020340080b00002c010000040140080100402c0100002a00007007002004048000000380780600e0000400101c000008000000100280101c0000000100602c0600c0000000004801203007001008000000000020080580100200800004030008010030100380000003c0a00080100200408804016048048200000042180903002c0000202e0440080303a0780780100c008128030000380000007400409001004000098000000040006200000402002020024060300000181b80700602001002016038000030140140c8080220081c80500006c000000180100980103a024050080080040180000c0000080300000004005000008058000320040600d0000000681404a040000000040a0030010000080180c00c0180183e00e0000000600001000014000000020000020040380f0020000380a008000088250280000000c0040000380300608000015004098060020260000000400801801824000000020060020000480c00000c0580001a000010050000c8038240080040180500601000800012000040200020000280400a00c0d8080000001500e0000041380c00c020088000040002500b0020100080001000c1080a00c050000020020100000201e020008030020a80100c03c014030000080100001000402400012024000000070fe00c0100400c0000200e0000000000300000c0080e000070000000080500200100c03c068010000140d01804600401005008180070040000181a00e00001c030040000280102300c000000010000440202300a0000000800c05c0000000e004020040060000081d00a02c140000120341300000e0140000101001c0100200204c000010060200280705a0140000000e00c0401500800005000002018010230000040701400a018028010100500000000e0040300000001001015002000030080000380000803c08000027000034010060000000180f0020800119b0539ec2aa0023360e72d855400466c14e6302a8008cd839c8605500107b0f32ca82a0024760f715505400496c16e2
  | 12 => 0x38a0001f91a642444c2f71791425f31654f100009c4450002f92985cb0000000c542600027f4151ec4970002583d005c5491692a84eb45800042741c5540222e90000c35175aa57140335210f0000845a75dc3ba0000003a32332fb00c4934d10005bf0cc0000003a72b809832039022c38d0004e50b40d630d0103fa5312c056a00037a45607c17154326a11a4db2ea5b30de24f15f4e80005f80001240944b815848605f1f52535195f45663314c82d211905317448f4490914812923ad47e5db1403dc3c35933fe42c47d1c10b212022431e04f10437800022e0003ec02900000059c5ca0002990000890001090462aa0c953a54f0002ac00052b54515a45a5b900000e50c3153100000000540001f000043f3b42501965d63634444b311521d0fc25c38c5d50002a53212860bd46c1500000004a037d1e202400005e5920000b351430228f17f1b52755335a10ad59b00043749807241b0000001ff0515550003035ec19412302032f5782120005755be5ce1c62871682ed1bd14d53c3d741e0be3e600017a40006e33d0002ad4b900004700032d00000017b01631b47900029c0000002165f93f950654816b0fe3b22fe5d30000004dd1630005ef1a70001c51d13064304711972d30e71fe18c3f50e54ef2d81e15993252d93e409d1a00001cf4e21e000000003b00002c2ec00059d00009b57450b4f638825700042d5a50e943b0004941aa2b300004d2df17551e01d0000003803b700001f4550005c30004590000000000973ce4a44f72e509228134d0af3a20001b01d94a55df0004663ed5963180000003920003991760005440000001a40065ae5d14bb2ce0000001e504a0273c20ff0704ad56d00056f0003fb27a0fa3a14572ff12c36b4fd5573834fb1372640010c14d20ab3bd4721fa52f3b31282075fd3c103020319e2af36d1e600026501120e0001050001db0003610000a13f024253d0005b55de2a215d0000435020000415ba23825d0005360cd5f60001911c208354709a07936c3bc48304222f23f5c617c59024e5955855d919c2f80003e937b1dd0000001da41146e49600017838e1011c016a00000000008e42b50f21e3a427314100043111300023d45320b3b815c0000000001fb03c2bf0003342004da09651c2185fc02e0000d23f62510504a657d0005af0005b24ff1f100006b1072fa1363a82c800826b15e0000000730000000005870000000685ed0e353f5041304ae4642c752d03500008d08f0001ba0005245a93750000000000002453b55dd29558a1ae1725d44e100004956e00000000000013d0000000ed4220005c25343040f405726f5650b81081770005f201216756118b5c139a2c40000f644d1b40000000000001d600050e0004ec1bb00000011c26848a58c2930dd07725b0000885f500000000036a28
  | 13 => 0x8435550747319f12e0650003a514334f0001450360140000a61352e63970454430000d75e208255152856c3354bf3954d521a20d57039e09f17e35c1624cc49e1cc34e4855e813f00048c25a00022815b4d800058600038700010c52349216f2470002be44203208c4172945010a046a2524022414df1cd19527b37c1391ea5841ca03e2911d44b53c93d159122602d33c3373af51f32c00f40e2f60d30001e316e00033e5b60ef09920218031f0bf53037229d3692320581930750000564333fc22b14f5503774605cc1c80d11384be4f25cd07e4f95c707432b00000000048e3271b62da3823140000004e70da1b25cf4a20952440f327700000037032219834b1120002671481614fe00001900023e5630001ab3530004230000000003b900000000032900052a2fc57c5c45fa3cb48700000045f2dd0003c00f142f43e00000010e2464b10784cb4bd00925451244b3643324ce1fc59a2e03840000003ab00041a3e700050d0004215112c60b73422bc2275b05892f52804761873e12ab1af3cf0f25403de2b70003b607a5a80df00012d34752725e0005da1810341a85693392900000d51222602fd05902124d00011d38f56222913c0b03664dc0fb3a03082bd0004b706033300000027113e5f135044121f1185bb4ed4fc35a2b254213a0005c03d30004681702085e53675104ca0004480000003c400047c1f65ab00008521930753b23958d0cb1515761565820002853585ea0003bf0000000002a926147a3f108b57f54b2a60000a94052e30024a320f3eb0aa0a45033934ea4e43db0175ad5c547040f3a63d42d10042bb2f05975833f220938555b00a3ac5881920c747b1260b12a04de4bc57e24c0004633600000000c041f1df1590000630000a72c10004061a318f20540d1171bf2d02f345e2970761345640640001b90001b85f00003c75b83132f42481210a256b54e03f21733600049b31644a0860bb3e00000003df47450949c1bc29f4c30003055f75583190ac36f1be46b44734300000005b40b00009e1cb0523301d24c02550ca3000a800008a0001521160001465601d006d3e815421422d52e2151f75984d428257b44e2d75521021d31e90ba28d54d1b111f0f526c2dc3405185a22703982b914907b4092ca0a31f338927810a30c06224302532a2960b50fd59403928a3b119b30a55d0030133241663d51325a42e40ae4d63943cd0e10004ac00026d5eb33f0000000a504e3ae00000000029e3792cf0000000000003124c632e3dd1ee2c34b62a400000000045d3565a645c1de0005380180000000004460004c400043843a11b0f046945b12f2371442de48818800019028306c5d74d94ba5a000003700053e4af18a55c3fd2351fd0000005352e100d58e1c70000004893cc0003bb42a4e000019900022231149f00055f
  | 14 => 0x1a90004671534c735d4f03ff1733863f400007f2564144622d650028c4a84b008709001a4c540c03359f0550002620000000e44510cf4e34781eb0dc5e65253ee3743d918303d24a0383380930ea47743d5133d25bd30e10d53249919a4650e60674f52b01572403620c61b75d85683960000001f857a40835b4345150004e641202635e4fa3651e400014e3173512d52f142012541635f0000052cc3541dc18d35950539b1333762250d033b3681f43be49d1a52ba3f814b4d04f84c24071d822102f0e03ef45428e48439d3410ce46f55948200004b43c01c1c35395c806f25934a0ec26333a51b4132b14f43461a143214a1d74a94d35160233f308104015521c2f25731ed1270f70b90d83a906a2e25412e837f03a4c13e51850003483d800053755a11407134941d4950c240127216d4a75fb37329b04c2362743c52115721824e92843ca11e2d45bc1c94ee0f91034901c42e752602b55e2665e434418911049a2a120623451d0d45c94610f855359e1a237105d07d13126914732301b4750db26e2305082c245054a29a23b0eb0155ee2b42cb1ef2892232c91861f222021b3b000736e4c94191ac0c830b5e904432821002a4912491
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x80110f985d45450d32006425d580151434c80110d989d65415132004c164786550544c80110f97619541513200603e1e76550544c80180f875d954151320048365b81550544c80120d962015415132004c164480550544c80150797552711513200541e5d545c4544c801c0576551711513200701595645c4544c80150b97552701513200542241545c0544c80150b975517015132007029d9545c0544c801c0976551701513200740552715c0544c801d01545c5701513200542652655c0544c80154191995701513200542656645c0544c80158191991701513200702595645c0544c80150898551701513200542e59545c0544c80150996551701513200542e45545c0544c80128594e1561185320049165784584614c801c05755d161185320049165480584614c80128594201611853200530241615c0614c801c42755857018532007105d5615c0614c801c82745857018532007205d1615c0614c80148994d95701853200530647655c0614c80144995d91701853200530647645c0614c8014c098585701853200530e55615c0614c8014c394585701853200521653651c5604c80190585610715813200511657641c5604c80194185600715813200660611801c5604c801849756006118132006225d180184604c801845752056018132006215d081580604c80184976600544cb51006825918015132d44018c176600714ca51006a0591801c5329440190575610714c951006305d9801c5325440194175600714c951006225d98015132d0401a0965600544cb41006305d9801c53290401a4165600714ca4100483e61651513250401a0965600544c94100641615741c532504018c176600714c941006605d1801c53250401305981513254541005c0640544c95150401605919d4644c9500062161d81191325400188987600644c950006a060580191325400180d8719132d4550006125d980151321400164190151325845000603618744c95014001c04744c9615405000483a606555132d000120d98d94544ca4000682d9580151329000150a97d5132542400061161d81195325000184987600654c94000682611801953250001a4181600654c94000681195819d1325000180d8719532d054000582a5a544ca5050001c08765513254140006225d9801513210001a0965600544c840005a0640544c9611000180d861d532500400050325d654c94010001c04754c96150040006309d9801c532840011c298dc5704ca1000603615841d9324400184985600764c91000622611801d932440018c181600764c91000530a5a719c132440018c0865c5704c91000621219744ca5144001844865d53290510006305d9801c53204001a4165600714c810006a0591801c532040010c49761932440100061121d654c91004001884875913244010
  | 1 => 0x5f0e000c8382900016410f0000067410000000140006800299c8c4693c9bc0000239d4903b081fcca43000003a4417000080044204e05c1b1f01416001a00e002d0fc00173f000cc0007800f0601480000000020000113b15caa3100000c600211cc00774180000001b8010a352500000211f000640000000ac01001440000368000008000000000000549200270004c00001d0000000030401b000c000000000032000480078003d000584d00000a82700000801300114d44b00000000042000283a030a85600000000002029c444860d08cb65e438cc8c25001b09859001841c0d1c87c482f2e8600650370b4d67b091607a7d278040c0878081c10480400000000180c24000020001824044408580c2c24000c30200024500008040000000000080140f965517298c5400503e59545ce62150012199320154580540048a648805516015001231912015458054006825518298d6015001a095460e62580540048664c8755160150012299221d54580540048c64487551601500121993e0554580540048a64b81551601500150b925517015132006425d180153524c8019097560054d093200443e6175151424c80190975600545093200542e4d545c0544c8019097460054d4d32006425d580153434c
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x50880398082802902c65c200048134c482a8b80a899002501a1241545c0544c801204d3130aa2e02a26400940684985517015132004a0343cb2a8b80a899002409a6e45545c0544c801220d2920b0ae030a64009206909058570185320048834a4c2c2b80c299002481a4261615c0614c801240d272ab0ae030a6400910697945857018532
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 65
  | 6 => 1592
  | 5 => 3585
  | 4 => 1534
  | 3 => 137
  | 2 => 12
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
  | 7 => packedAt gbK7 (1837+((h/21+packedAt gbK7 (1690+(h % 21)*7) 7) % 86)*8) 8
  | 6 => packedAt gbK6 (65264+((h/530+packedAt gbK6 (58904+(h % 530)*12) 12) % 2543)*12) 12
  | 5 => packedAt gbK5 (187615+((h/1195+packedAt gbK5 (172080+(h % 1195)*13) 13) % 4303)*13) 13
  | 4 => packedAt gbK4 (96127+((h/511+packedAt gbK4 (90506+(h % 511)*11) 11) % 1841)*12) 12
  | 3 => packedAt gbK3 (9950+((h/45+packedAt gbK3 (9590+(h % 45)*8) 8) % 218)*9) 9
  | 2 => packedAt gbK2 (988+((h/4+packedAt gbK2 (972+(h % 4)*4) 4) % 15)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x1f0fc3ffc3e1f87ff83fc0fe07f00127a4f4cf
  | 1 => 0xe3f0fc387c7e1f870fc1ff0ff87032da5b4b33
  | 2 => 0xfc00ffc07f801ff80ffe000fff8cc31c638c3c
  | 3 => 0xffff00007fffe0000ffffff0000f03e07c0fc0
  | 4 => 0x7ffffffff0000000000ffc007ff000
  | 5 => 0xffffffff8000000000000000000fffff800000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x10048000020090002400200000000801045
  | 1 => 0x411044110822088220409404a060304a094112
  | 2 => 0xac88aa82559115504eb40229570cc314628c28
  | 3 => 0x36aa220466d544408f392ae0110f03a0740e80
  | 4 => 0x7b799e64e2100c40622554007fe000
  | 5 => 0xdbccf3270000000004203081844aabff000000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xffffeeeaeeeaeee8ffffeeeaeeeaeee8ffffeeeaeeeaeee8ffffeeeaeeeaeee8ffffeeeaeeeaeee8ffffeeeaeeeaeee8ffffeeeaeeeaeee8ffffeeeaeeeaeee8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_14402
namespace PEqualNP.Outside.L_meta_14402
open PEqualNP.Outside.L_meta_14402.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 1 := bs0_3_0
theorem alls0 : ∀ k ≤ 3, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_3 i (by omega) hi
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
theorem bs5_3_0 : Interval s5Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 1 := bs5_3_0
theorem alls5 : ∀ k ≤ 3, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 12 := bgb_2_0
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
theorem bgb_3_128 : Interval gbAtlas 3 128 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 137 := (concat (concat bgb_3_0 bgb_3_32) (concat bgb_3_64 (concat bgb_3_96 bgb_3_128)))
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
theorem bgb_4_1504 : Interval gbAtlas 4 1504 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 1534 := (concat (concat (concat (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat bgb_4_96 (concat bgb_4_128 bgb_4_160))) (concat (concat bgb_4_192 (concat bgb_4_224 bgb_4_256)) (concat bgb_4_288 (concat bgb_4_320 bgb_4_352)))) (concat (concat (concat bgb_4_384 (concat bgb_4_416 bgb_4_448)) (concat bgb_4_480 (concat bgb_4_512 bgb_4_544))) (concat (concat bgb_4_576 (concat bgb_4_608 bgb_4_640)) (concat bgb_4_672 (concat bgb_4_704 bgb_4_736))))) (concat (concat (concat (concat bgb_4_768 (concat bgb_4_800 bgb_4_832)) (concat bgb_4_864 (concat bgb_4_896 bgb_4_928))) (concat (concat bgb_4_960 (concat bgb_4_992 bgb_4_1024)) (concat bgb_4_1056 (concat bgb_4_1088 bgb_4_1120)))) (concat (concat (concat bgb_4_1152 (concat bgb_4_1184 bgb_4_1216)) (concat bgb_4_1248 (concat bgb_4_1280 bgb_4_1312))) (concat (concat bgb_4_1344 (concat bgb_4_1376 bgb_4_1408)) (concat bgb_4_1440 (concat bgb_4_1472 bgb_4_1504))))))
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
theorem bgb_5_3584 : Interval gbAtlas 5 3584 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3585 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)) (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 bgb_5_416)))) (concat (concat (concat bgb_5_448 (concat bgb_5_480 bgb_5_512)) (concat (concat bgb_5_544 bgb_5_576) (concat bgb_5_608 bgb_5_640))) (concat (concat bgb_5_672 (concat bgb_5_704 bgb_5_736)) (concat (concat bgb_5_768 bgb_5_800) (concat bgb_5_832 bgb_5_864))))) (concat (concat (concat (concat bgb_5_896 (concat bgb_5_928 bgb_5_960)) (concat (concat bgb_5_992 bgb_5_1024) (concat bgb_5_1056 bgb_5_1088))) (concat (concat bgb_5_1120 (concat bgb_5_1152 bgb_5_1184)) (concat (concat bgb_5_1216 bgb_5_1248) (concat bgb_5_1280 bgb_5_1312)))) (concat (concat (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)) (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536))) (concat (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632)) (concat (concat bgb_5_1664 bgb_5_1696) (concat bgb_5_1728 bgb_5_1760)))))) (concat (concat (concat (concat (concat bgb_5_1792 (concat bgb_5_1824 bgb_5_1856)) (concat (concat bgb_5_1888 bgb_5_1920) (concat bgb_5_1952 bgb_5_1984))) (concat (concat bgb_5_2016 (concat bgb_5_2048 bgb_5_2080)) (concat (concat bgb_5_2112 bgb_5_2144) (concat bgb_5_2176 bgb_5_2208)))) (concat (concat (concat bgb_5_2240 (concat bgb_5_2272 bgb_5_2304)) (concat (concat bgb_5_2336 bgb_5_2368) (concat bgb_5_2400 bgb_5_2432))) (concat (concat bgb_5_2464 (concat bgb_5_2496 bgb_5_2528)) (concat (concat bgb_5_2560 bgb_5_2592) (concat bgb_5_2624 bgb_5_2656))))) (concat (concat (concat (concat bgb_5_2688 (concat bgb_5_2720 bgb_5_2752)) (concat (concat bgb_5_2784 bgb_5_2816) (concat bgb_5_2848 bgb_5_2880))) (concat (concat bgb_5_2912 (concat bgb_5_2944 bgb_5_2976)) (concat (concat bgb_5_3008 bgb_5_3040) (concat bgb_5_3072 bgb_5_3104)))) (concat (concat (concat bgb_5_3136 (concat bgb_5_3168 bgb_5_3200)) (concat (concat bgb_5_3232 bgb_5_3264) (concat bgb_5_3296 bgb_5_3328))) (concat (concat (concat bgb_5_3360 bgb_5_3392) (concat bgb_5_3424 bgb_5_3456)) (concat (concat bgb_5_3488 bgb_5_3520) (concat bgb_5_3552 bgb_5_3584)))))))
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
theorem bgb_6_1568 : Interval gbAtlas 6 1568 24 := block_range (n:=24) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1592 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat bgb_6_288 (concat bgb_6_320 bgb_6_352)))) (concat (concat (concat bgb_6_384 (concat bgb_6_416 bgb_6_448)) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))) (concat (concat bgb_6_576 (concat bgb_6_608 bgb_6_640)) (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 bgb_6_768))))) (concat (concat (concat (concat bgb_6_800 (concat bgb_6_832 bgb_6_864)) (concat bgb_6_896 (concat bgb_6_928 bgb_6_960))) (concat (concat bgb_6_992 (concat bgb_6_1024 bgb_6_1056)) (concat bgb_6_1088 (concat bgb_6_1120 bgb_6_1152)))) (concat (concat (concat bgb_6_1184 (concat bgb_6_1216 bgb_6_1248)) (concat bgb_6_1280 (concat bgb_6_1312 bgb_6_1344))) (concat (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440)) (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 bgb_6_1568))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_32 : Interval gbAtlas 7 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_64 : Interval gbAtlas 7 64 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 65 := (concat bgb_7_0 (concat bgb_7_32 bgb_7_64))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 4 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 32, 48),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 4 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 4 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 4 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 4 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) SB) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 6 zero,inputs.getD 4 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 7 zero,inputs.getD 5 zero,inputs.getD 1 zero,inputs.getD 0 zero]
def fullWord : Sig := 0xffffffffffffffffffffeeeaeeeaeee8ffffeeeeeeeeeeeeffffeeeaeeeaeee8ffffffffffffffffffffeeeaeeeaeee8ffffeeeeeeeeeeeeffffeeeaeeeaeee8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 11 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) SB :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) SB :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) SB :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have s3 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 3 zero)) SB :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
  have s4 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 4 zero)) SB :=
    slice_correct (ms:=fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
  have s5 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 5 zero)) SB :=
    slice_correct (ms:=fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds5 certs5)
  have allCuts : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) SB := by
    intro v
    fin_cases v
    · exact s0
    · exact s1
    · exact s2
    · exact s3
    · exact s4
    · exact s5
  have low := boundgb certgb allCuts
  have lift := lift_ok (u:=true) (ms:=fixRows 192 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,64,192)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,64,192)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 2 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 4, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def sample7 (r : Row) (i : Fin 8) := bit r (fullRoots.getD i.val zero)
theorem table7 : ∀ r, posted (sample7 r) = bit r fullWord := by decide +kernel
theorem raw7 : List.ofFn (fun i : Fin 8 => fullRoots.getD i.val zero) = fullRoots := by decide +kernel
theorem eval7 (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = posted x) : (execute gs fullRoots).getD o zero=fullWord := by
  apply bit_ext
  intro r
  have e : List.ofFn (sample7 r) = fullRoots.map (bit r) := by rw [←raw7,List.map_ofFn]; rfl
  rw [←bRead,exeBits gs r fullRoots (fun g hg => (legal g hg).1),←e]
  exact (h (sample7 r)).trans (table7 r)
theorem binaryLower (low : Lower true fullRoots fullWord 11)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x)=posted x) : 11 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper fullWord := proper_of _ (by decide +kernel)
  have out := getRep (u:=true) (execute gs fullRoots) o
  rw [eval7 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_14402.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,5]⟩,⟨.or,[8,6]⟩,⟨.and,[9,7]⟩,⟨.or,[0,2]⟩,⟨.or,[11,3]⟩,⟨.or,[6,7]⟩,⟨.and,[12,13]⟩,⟨.and,[1,5]⟩,⟨.and,[0,4]⟩,⟨.or,[10,14]⟩,⟨.or,[17,15]⟩,⟨.or,[18,16]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,19⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 11) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o legal _ correct
  by_cases clean : ∀ g ∈ gs, g.op ≠ GateOp.not
  · refine ⟨gs,o,?_,Nat.le_refl _,correct⟩
    intro g hg
    obtain ⟨op,len⟩ := legal g hg
    exact ⟨op.elim Or.inl (fun h => Or.inr (h.resolve_right (clean g hg))),len⟩
  · push Not at clean
    obtain ⟨a,ha,hop⟩ := clean
    have lo := binaryLower low gs o (by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using legal) correct
    have less : gs.countP (fun g => !isNot g) < gs.length := by
      by_contra! bad
      have e := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length bad) a ha
      simp [isNot,hop] at e
    exact ⟨mono,19,monoShape,by change 12 ≤ gs.length; omega,monoEval⟩
end PEqualNP.Outside.L_meta_14402

open PEqualNP.Outside.L_meta_14402 in
theorem PEqualNP.Outside.L_meta_14402 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
