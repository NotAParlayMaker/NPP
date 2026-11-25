import PEqualNP.Defs

-- This proof reuses the signed circuit certificate from L_meta_7306.
-- That certificate is adapted from L_meta_7794, whose root certificate
-- is adapted from benoitrazet, PR 12184.
-- The live-wire checker and the smaller graph certificates are adapted from the project proofs
-- L_meta_1667 and L_meta_1677, distributed under Apache-2.0.
-- Each root search considers all nine inputs. Restriction bounds and conflicting truth-table
-- rows eliminate children, and checked graph permutations identify equivalent states.
-- The signed search counts binary gates with complementation available for free.
namespace PEqualNP.Outside.L_meta_10830
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
private lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
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
        exact Or.inl (get_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (get_rep w i) (get_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (get_rep w i)

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

private lemma extract {u target} (gs : List Gate) (w : List Sig)
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

private lemma b_read (i) (w : List Sig) (j : Nat) :
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
  simp only [b_read]
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

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
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
def graph : Sig := 0xfffffffffffffffefffffffffffffffafffffffffffefffefffffffffffafff0fffffffefffffffeffffffeeffffffaafefefefefefefefeeeeeccccaaaa0000
def seed : Sig := inputs.getD 0 zero ||| inputs.getD 6 zero
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool := (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed_table : ∀ r : Row, bit r seed = (sample r 0 || sample r 6) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem seed_nonzero : seed ≠ zero := by decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl

theorem exec_extends (gs : List Gate) (ws : List Sig) : ∃ l, execute gs ws = ws ++ l := by
  induction gs generalizing ws with
  | nil => exact ⟨[],by simp [execute]⟩
  | cons g gs ih =>
    obtain ⟨l,hl⟩ := ih (ws++[gv ws g])
    exact ⟨gv ws g::l,by simpa [execute,List.append_assoc] using hl⟩

theorem raw_signed (C : Circuit)
    (legal : PEqualNP.MetaComplexity.FanInTwo C) (small : C.gates.countP (fun g => !isNot g) ≤ 14)
    (computes : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = edge x) :
    ∃ k S, k ≤ 14 ∧ Live true graph k S ∧ ∀ a ∈ S, a ∈ inputs := by
  let result := (execute C.gates inputs).getD C.output zero
  have goalEq : result = graph := by
    apply bit_ext
    intro r
    rw [table_eval C legal, edge_table]
    exact computes (sample r)
  have rep := get_rep (u := true) (execute C.gates inputs) C.output
  change nrm true result ∈ _ ∨ ¬proper (nrm true result) at rep
  have pg : bit 0 graph = false := by decide +kernel
  rw [goalEq, nrm_id pg] at rep
  have targetIn := rep.resolve_right (fun hn => hn graph_proper)
  obtain ⟨k, S, hk, run, hs⟩ := extract C.gates inputs legal (by simp) graph_proper targetIn
  have ns : inputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at hs
  exact ⟨k, S, hk.trans small, run, hs⟩

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
def typeWord (t : Nat) : Sig := bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)
def varsX (m : Nat) : List Sig := if m<512 then vars m else vars m ++ [typeWord (m/512-1)]
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 4) ||| (x 1 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 0 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 2 &&& x 8) ||| (x 3 &&& x 8) ||| (x 5 &&& x 8)
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
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

def supportPairs (t : Nat) (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) =>
    let hi := ((mask/512-1) >>> (4*i)) &&& 15
    let r := if mask >= 512 then (if hi = 0 then 0 else 1 <<< (hi-1)) else if t/81==2 && i==t/9 % 9 then 1 <<< (t % 9) else if t/81==2 && i==t % 9 then 1 <<< (t/9 % 9) else 0
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
def assertSize (m hints L : Nat) :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card-1)
theorem size_of {u m hints L} (h : assertSize m hints L = true) :
    Lower u (vars m) (graphGoal m) L := by
  simp only [assertSize,Bool.and_eq_true,decide_eq_true_eq] at h
  intro p bank hr ha
  exact h.2.trans (lower_count (proper_of _ h.1.1) _ h.1.2 p bank hr ha)

abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig := graphGoal m
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m % 512+512*(c.1/512)
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (varsX free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (varsX free) (varsX q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {u} {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice u (varsX (rawMask m c)) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  revert ok
  obtain ⟨z,o,q,s,L⟩ := c
  intro ok
  let ms := fixRows z o
  let raw := rawMask m (z,o,q,s,L)
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
  change (((properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)

def carryOK (old rep : Nat) (swaps : List Nat) :=
  (properB (graphGoal old) && plainWord (graphGoal old) && (varsX old).all plainWord) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (varsX old) (graphGoal old) (varsX rep) (graphGoal rep)
theorem carry_of {u old rep L swaps} (ok : carryOK old rep swaps = true)
    (h : Lower u (varsX rep) (graphGoal rep) L) : Lower u (varsX old) (graphGoal old) L := by
  simp only [carryOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound {u} (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower u (varsX q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he

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

abbrev Bits := BitVec 416
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 416 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 416 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 416 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 416 → Row) (x : Decor) := x.2 = pairSig r s x.1
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

def asRow (cols : Nat → Bits) (i : Fin 416) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 416) (j : Fin 9) :
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

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 4) ||| (x 1 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 0 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 2 &&& x 8) ||| (x 3 &&& x 8) ||| (x 5 &&& x 8)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 416) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 416) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
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
  let n := v.toNat % 18446744073709551557
  (n*(n+971)) % 18446744073709551557
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
    if (rs ||| column d z.2) != BitVec.allOnes 416 then true else
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 416) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 416 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
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

abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)

def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none

abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List ColumnInfo × List (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (g : Forest) : Nat := g.1
def Forest.mode (g : Forest) : Bool := !(g.1.testBit 10)
def Forest.cap (g : Forest) : Nat := g.2.1
def Forest.samples (g : Forest) : Nat → Bits × Bits := g.2.2.1
def Forest.cols (g : Forest) : List ColumnInfo := g.2.2.2.1
def Forest.autos (g : Forest) : List (List Nat) := g.2.2.2.2.1
def Forest.levels (g : Forest) : Nat → Packing := g.2.2.2.2.2.1
def Forest.index (g : Forest) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  exact raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 416) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 416) (hq : chartSamples m q = 0) :
    properPairs (chartGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
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

def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := packedAt data (i*width) width
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)

def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more

def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols[idx]?).bind fun ci =>
    materialize g.mode (varsX (rawMask g.mask ci)) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool g.mode (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols[i]? with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (List.mem_of_getElem? e)

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible g.mode (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov g.mode ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible g.mode (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact hT (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h

def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n
theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 416) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.all (fun c => colCheck g.mask c prior) &&
  g.autos.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible g.mode (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower g.mode (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) (essential_plain ess).1 (essential_plain ess).2 _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

theorem lower_discard {g prior ci hints} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (ok : colCheck g.mask ci prior = true)
    (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask)
    (nd : (vars g.mask).Nodup)
    (cut : poolCut g.mode (subcube ci.1 ci.2.1) ci.2.2.2.2 g.cap 0 (varsX (rawMask g.mask ci)) (vars g.mask)=true) :
    Lower g.mode (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) (essential_plain ess).1 (essential_plain ess).2 _ (poolCut_sound (col_sound ci prior low ok) [] rfl nd cut)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (u : Bool) (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (carries : List (Nat × List Nat)) :=
  carries.map (fun v => (v.1,L)) ++ old
theorem extendKnown_ok {u old L m carries} (previous : Known u old)
    (main : Lower u (varsX m) (graphGoal m) L)
    (ok : carries.all (fun v => carryOK v.1 m v.2) = true) :
    Known u (extendKnown old L carries) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact carry_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known true [] := by simp [Known]
theorem known_down {u es} (h : Known true es) : Known u es := fun e he => lower_down (h e he)
def lanePlace (v : Nat) (upper : Nat) := 2^417*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^417 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<417 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<417 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<417 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
theorem broadcast {α} (a : Bits) (xs : List α) :
    units xs.length * a.toNat = combineLanes (fun _ => a) xs := by
  induction xs with
  | nil => simp [units,combineLanes]
  | cons v xs ih => simp only [List.length_cons,units,combineLanes,lanePlace,Nat.add_mul,Nat.mul_assoc,ih,Nat.one_mul]

def fullMarks (r packed : Nat) := ((packed+r) >>> 416) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (417*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^417)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 417*(i+1)-417=417*i := by omega
      have ge : ¬417*(i+1)<417 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 416 = (a==BitVec.allOnes 416) := by
  by_cases h : a=BitVec.allOnes 416
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^416-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^416 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (417*i) =
      (f xs[i]==BitVec.allOnes 416) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^417*u+x+(2^417*v+1)=2^417*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^417 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬417*(i+1)+416<417 := by omega
      have di : 417*(i+1)+416-417=417*i+416 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)

abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat

def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2

theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]

def packedOp (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=0 then (a.1 &&& b.1,a.2 &&& b.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else if op=2 then (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
  else (b.1 ^^^ (b.1 &&& a.1),b.2 ^^^ (b.2 &&& a.2))
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp op (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (dbin op (a x) (b x)).2) xs := by
  by_cases h0 : op=0
  · simp only [packedOp,h0,ite_true,packedSig,lanes_and,dbin,bv]
  by_cases h1 : op=1
  · simp [packedOp,h1,packedSig,lanes_or,dbin,bv]
  by_cases h2 : op=2
  · simp [packedOp,h2,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv]
  · have e (x y : Bits) : ~~~x &&& y = y &&& ~~~x := BitVec.and_comm _ _
    simp only [packedOp,h0,h1,h2,ite_false,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv,e]

def takePacked (c : PackedCov) (a b : Nat) (ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) ka kb) xs := by
  cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (dbin op a b) ka kb
def combField (c : NodeContext) (d ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov c.2.2.2.1.1 (column d a.2) (column d b.2) ka kb |||
    column d (dbin op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 417) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (417*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 417) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

def availableMasked (u : Bool) (p : BoundPool) (m : Sig) :=
  m==zero || m==p.domain || (p.wires.map (masked p.domain)).any (fun v => v==m) ||
    (u && (p.wires.map (masked p.domain)).any (fun v => v==(p.domain ^^^ m)))
theorem masked_comp (d x : Sig) : masked d (neg x) = d ^^^ masked d x := by
  apply bit_ext
  intro r
  simp only [masked,neg,bit,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,r.isLt,decide_true,Bool.true_and]
  cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl
theorem available_mask (u) (p : BoundPool) (x : Sig) :
    availableB u p.domain p.wires x = availableMasked u p (masked p.domain x) := by
  simp only [availableB,availableMasked,masked_comp]

def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]

theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b kb ≤
    (delTwo ws a b ka kb).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  simp only [delTwo]
  omega

abbrev QuickPool := BoundPool × Nat × Bool
noncomputable def force {β : Type} (n : Nat) (f : Nat → β) : β := Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n
theorem force_eq {β : Type} (n : Nat) (f : Nat → β) : force n f = f n := by cases n <;> rfl
noncomputable def forceMap {α β : Type} (f : α → Nat) (l : List α) : (List Nat → β) → β :=
  List.rec (fun k => k []) (fun a _ ih k => force (f a) fun x => ih fun xs => k (x::xs)) l
theorem forceMap_eq {α β : Type} (f : α → Nat) (l : List α) (k : List Nat → β) : forceMap f l k = k (l.map f) := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    change force (f a) (fun x => forceMap f l fun xs => k (x::xs)) = _
    rw [force_eq,ih]
    rfl
def nmask (d : Nat) (a : Sig) : Nat := Nat.land a.toNat d
noncomputable def anyEq (m : Nat) (l : List Nat) : Bool := List.rec false (fun v _ ih => or (Nat.beq m v) ih) l
def nconst (d m : Nat) : Bool := or (Nat.beq m 0) (Nat.beq m d)
noncomputable def navail (u : Bool) (d : Nat) (pm : List Nat) (m : Nat) : Bool :=
  or (or (nconst d m) (anyEq m pm)) (and u (anyEq (Nat.xor d m) pm))
theorem nmask_eq (d a : Sig) : nmask d.toNat a = (masked d a).toNat := (BitVec.toNat_and _ _).symm
theorem beq_toNat (a b : Sig) : Nat.beq a.toNat b.toNat = (a==b) := by
  rw [Bool.eq_iff_iff,Nat.beq_eq,beq_iff_eq]
  exact BitVec.toNat_inj
theorem nconst_eq (d a : Sig) : nconst d.toNat (nmask d.toNat a) = isMaskedConstant d a := by
  rw [nmask_eq]
  have e : Nat.beq (masked d a).toNat 0 = (masked d a == zero) := by
    have z0 : zero.toNat=0 := by simp [zero]
    rw [←beq_toNat,z0]
  rw [nconst,e,beq_toNat]
  rfl
theorem anyEq_eq (x d : Sig) (pool : List Sig) : anyEq x.toNat (pool.map (nmask d.toNat)) = (pool.map (masked d)).any (fun v => v==x) := by
  induction pool with
  | nil => rfl
  | cons a l ih =>
    change or (Nat.beq x.toNat (nmask d.toNat a)) (anyEq x.toNat (l.map (nmask d.toNat))) = _
    rw [ih,nmask_eq,beq_toNat,List.map_cons,List.any_cons,Bool.beq_comm]
theorem navail_eq (u : Bool) (d a : Sig) (pool : List Sig) :
    navail u d.toNat (pool.map (nmask d.toNat)) (nmask d.toNat a) = availableB u d pool a := by
  have x : Nat.xor d.toNat (masked d a).toNat = (masked d (neg a)).toNat := by
    rw [masked_comp]
    exact (BitVec.toNat_xor _ _).symm
  rw [navail,nconst_eq,nmask_eq,x,anyEq_eq,anyEq_eq]
  simp only [availableB,isMaskedConstant]
def unav (u : Bool) (p : BoundPool) (w : Decor) : Nat := cond (availableB u p.domain p.wires w.1) 0 1
def slowCost (u : Bool) (p : BoundPool) (ws : List Decor) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) : Bool :=
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let cm := ws.countP const - constantLoss const a ka - constantLoss const b kb + (isMaskedConstant p.domain z).toNat
  (((ws.map (unav u p)).sum == cond ka 0 (unav u p a) + cond kb 0 (unav u p b)) &&
    decide (k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+cm)) &&
    (availableB u p.domain p.wires z || (availableB u p.domain p.wires a.1 && availableB u p.domain p.wires b.1))
def zN (op x y : Nat) : Nat := cond (Nat.beq op 0) (Nat.land x y) (cond (Nat.beq op 1) (Nat.lor x y)
  (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y)) (Nat.xor y (Nat.land x y))))
theorem zN_eq (op : Nat) (d a b : Sig) : zN op (nmask d.toNat a) (nmask d.toNat b) = nmask d.toNat (bin op a b) := by
  have tn (x y : Sig) : Nat.land x.toNat y.toNat = (x &&& y).toNat := (BitVec.toNat_and x y).symm
  have tx (x y : Sig) : Nat.xor x.toNat y.toNat = (x ^^^ y).toNat := (BitVec.toNat_xor x y).symm
  have tor (x y : Sig) : Nat.lor x.toNat y.toNat = (x ||| y).toNat := (BitVec.toNat_or x y).symm
  simp only [nmask_eq]
  unfold zN
  by_cases h0 : op=0
  · subst h0
    change Nat.land _ _ = _
    rw [tn]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,ite_true,BitVec.getLsbD_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  by_cases h1 : op=1
  · subst h1
    change Nat.lor _ _ = _
    rw [tor]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,Nat.one_ne_zero,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e0 : Nat.beq op 0=false := Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
  have e1 : Nat.beq op 1=false := Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
  by_cases h2 : op=2
  · subst h2
    change Nat.xor _ (Nat.land _ _) = _
    rw [tn,tx]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,OfNat.ofNat_ne_zero,OfNat.ofNat_ne_one,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e2 : Nat.beq op 2=false := Bool.eq_false_iff.mpr (fun h => h2 (Nat.eq_of_beq_eq_true h))
  rw [e0,e1,e2]
  change Nat.xor _ (Nat.land _ _) = _
  rw [tn,tx]
  congr 1
  apply bit_ext
  intro r
  simp only [masked,bin,bit,h0,h1,h2,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
  cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
def nloss (d x : Nat) (keep : Bool) : Nat := cond keep 0 (cond (nconst d x) 1 0)
theorem nloss_eq (d : Sig) (a : Decor) (keep : Bool) :
    nloss d.toNat (nmask d.toNat a.1) keep = constantLoss (fun w : Decor => isMaskedConstant d w.1) a keep := by
  rw [nloss,nconst_eq,constantLoss]
  cases keep
  · cases isMaskedConstant d a.1 <;> rfl
  · rfl
abbrev QS := Nat × Nat × Nat × Nat × Nat × List Nat × List Nat × Bool
noncomputable def quickSpec (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) : QS :=
  let d := p.domain.toNat
  let ms := ws.map (fun w : Decor => nmask d w.1)
  (d,ms.countP (nconst d),p.bound,Nat.add k p.paid,(ms.map fun m => cond (navail u d (p.wires.map (nmask d)) m) 0 1).sum,ms,p.wires.map (nmask d),u)
noncomputable def forceBool {β : Type} (b : Bool) (f : Bool → β) : β := Bool.rec (f false) (f true) b
noncomputable def forcePool {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) (f : QS → β) : β :=
  force p.domain.toNat fun d => forceMap (nmask d) p.wires fun pm => forceMap (fun w : Decor => nmask d w.1) ws fun ms =>
  force (ms.countP (nconst d)) fun c => force p.bound fun l => force (Nat.add k p.paid) fun t =>
  force (ms.map fun m => cond (navail u d pm m) 0 1).sum fun v => forceBool u fun u => f (d,c,l,t,v,ms,pm,u)
theorem forcePool_eq {β : Type} (u k ws p) (f : QS → β) : forcePool u k ws p f = f (quickSpec u k ws p) := by
  have e (b : Bool) (f : Bool → β) : forceBool b f = f b := by cases b <;> rfl
  simp only [forcePool,force_eq,forceMap_eq,e]
  rfl
noncomputable def forcePools {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (ps : List BoundPool) : (List QS → β) → β :=
  List.rec (fun f => f []) (fun p _ ih f => forcePool u k ws p fun q => ih fun qs => f (q::qs)) ps
theorem forcePools_eq {β : Type} (u k ws ps) (f : List QS → β) : forcePools u k ws ps f = f (ps.map (quickSpec u k ws)) := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih =>
    change forcePool u k ws p (fun q => forcePools u k ws ps fun qs => f (q::qs)) = _
    rw [forcePool_eq,ih]
    rfl
def kwN (v : Nat) : Nat :=
  let n := v % 18446744073709551557
  (n*(n+971)) % 18446744073709551557
abbrev Lane := NodeContext × Nat × Nat × List QS × List Nat × Nat
noncomputable def laneOf (c : NodeContext) : Lane :=
  let ws := c.2.2.1.map (fun w : Decor => w.1.toNat)
  (c,c.2.2.1.length,cond c.2.2.2.1.2 4 2,c.2.2.2.2.1.map (quickSpec c.2.2.2.1.2 (c.1-1) c.2.2.1),ws,(ws.map kwN).sum)
noncomputable def forceLanes {β : Type} (cs : List NodeContext) : (List Lane → β) → β :=
  List.rec (fun f => f []) (fun c _ ih f => force c.2.2.1.length fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
    forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
    forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => ih fun ys => f ((c,n,l,qs,ws,t)::ys)) cs
theorem forceLanes_eq {β : Type} (cs) (f : List Lane → β) : forceLanes cs f = f (cs.map laneOf) := by
  induction cs generalizing f with
  | nil => rfl
  | cons c cs ih =>
    change force c.2.2.1.length (fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
      forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
      forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => forceLanes cs fun ys => f ((c,n,l,qs,ws,t)::ys)) = _
    rw [force_eq,force_eq,forceMap_eq,force_eq,forcePools_eq,ih]
    rfl
noncomputable def fastCost (s : QS) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (s.2.2.2.2.2.1.getD i 0) fun x => force (s.2.2.2.2.2.1.getD j 0) fun y =>
  let av := navail s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1
  let hi := Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (nloss s.1 x ka)) (nloss s.1 y kb))
  let lo := s.2.2.2.1
  and (Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond (av x) 0 1)) (cond kb 0 (cond (av y) 0 1))))
  (cond (Nat.ble (Nat.succ lo) hi)
    (force (zN op x y) fun z => or (av z) (and (Nat.ble (Nat.add lo 2) hi) (and (av x) (av y))))
    (cond (Nat.ble lo hi) (nconst s.1 (zN op x y)) false))
theorem spec_get {d : Nat} (ws : List Decor) (i : Nat) (hd : nmask d zero=0) :
    (ws.map (fun w : Decor => nmask d w.1)).getD i 0 = nmask d (ws.getD i defaultDecor).1 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none => exact hd.symm
  | some v => rfl
theorem fast_slow {u k p ws i j op ka kb} (h : fastCost (quickSpec u k ws p) i j op ka kb=true) :
    slowCost u p ws k (ws.getD i defaultDecor) (ws.getD j defaultDecor) op ka kb=true := by
  have z0 : nmask p.domain.toNat zero=0 := by
    have : zero.toNat=0 := by simp [zero]
    simp [nmask,this]
  have su : (((ws.map (fun w : Decor => nmask p.domain.toNat w.1)).map fun m => cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) m) 0 1).sum) =
      (ws.map (unav u p)).sum := by
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left ?_)
    intro w _
    change cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) (nmask p.domain.toNat w.1)) 0 1 = _
    rw [navail_eq]
    rfl
  simp only [fastCost,quickSpec,force_eq,spec_get _ _ z0,su,List.countP_map,Function.comp_def,nconst_eq] at h
  generalize ws.getD i defaultDecor=a at h ⊢
  generalize ws.getD j defaultDecor=b at h ⊢
  replace h : and (Nat.beq (ws.map (unav u p)).sum (Nat.add (cond ka 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) 0 1)) (cond kb 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)) 0 1))))
   (cond (Nat.ble (Nat.succ (Nat.add k p.paid)) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb))))
    (or ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) (and (Nat.ble (Nat.add (Nat.add k p.paid) 2) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (and ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)))))
    (cond (Nat.ble (Nat.add k p.paid) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (nconst p.domain.toNat (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) false)) = true := h
  rw [zN_eq,nconst_eq,navail_eq,navail_eq,navail_eq,nloss_eq,nloss_eq] at h
  have ca : isMaskedConstant p.domain (bin op a.1 b.1)=true → availableB u p.domain p.wires (bin op a.1 b.1)=true := by
    intro zc
    simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
    exact Or.inl (Or.inl zc)
  simp only [Nat.add_eq,Nat.sub_eq,Nat.succ_eq_add_one,Bool.and_eq_true,Nat.beq_eq] at h
  obtain ⟨hu,h⟩ := h
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
  refine ⟨⟨hu,?_⟩,?_⟩
  all_goals
    generalize ws.countP (fun w => isMaskedConstant p.domain w.1) - constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) a ka -
      constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) b kb = c at h ⊢
    generalize isMaskedConstant p.domain (bin op a.1 b.1)=r at h ca ⊢
    generalize availableB u p.domain p.wires (bin op a.1 b.1)=q at h ca ⊢
    cases h1 : Nat.ble (k+p.paid+1) (p.bound+c)
    · rw [h1] at h
      cases h2 : Nat.ble (k+p.paid) (p.bound+c)
      · simp [h2] at h
      · have := Nat.ble_eq.mp h2
        simp only [h2,cond_true,cond_false] at h
        subst h
        rw [ca rfl]
        simp <;> omega
    · rw [h1] at h
      have l1 := Nat.ble_eq.mp h1
      simp only [cond_true,Bool.or_eq_true,Bool.and_eq_true,Nat.ble_eq] at h
      rcases h with rfl | ⟨l2,ha,hb⟩
      · simp <;> omega
      · first
        | (have : (!q).toNat ≤ 1 := Bool.toNat_le _
           omega)
        | simp [ha,hb]

theorem anyEq_iff (m : Nat) (l : List Nat) : anyEq m l=true ↔ m ∈ l := by
  induction l with
  | nil => simp [anyEq]
  | cons a l ih =>
    change or (Nat.beq m a) (anyEq m l)=true ↔ _
    rw [Bool.or_eq_true,ih,Nat.beq_eq,List.mem_cons]
noncomputable def linkAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (l.2.2.2.2.1.getD i 0) fun x => force (l.2.2.2.2.1.getD j 0) fun y => force (zN op x y) fun z =>
  Option.rec false (fun ys => forceMap (fun v => v) ys fun ys =>
    and (anyEq z ys) (and (l.2.2.2.2.1.all fun v => or (and (not ka) (Nat.beq v x)) (or (and (not kb) (Nat.beq v y)) (anyEq v ys)))
      (ys.all fun v => or (Nat.beq v z) (and (and (or ka (not (Nat.beq v x))) (or kb (not (Nat.beq v y)))) (anyEq v l.2.2.2.2.1)))))
    (fl (Nat.add (kwN z) (Nat.sub (Nat.sub l.2.2.2.2.2 (cond ka 0 (kwN x))) (cond kb 0 (kwN y)))))
theorem keySet_sum (xs : List Sig) : keySet xs = (xs.map keyWord).sum := by
  have go (a : Nat) : xs.foldl (fun v x => v+keyWord x) a = a+(xs.map keyWord).sum := by
    induction xs generalizing a with
    | nil => rfl
    | cons x xs ih => rw [List.foldl_cons,ih,List.map_cons,List.sum_cons,Nat.add_assoc]
  exact (go 0).trans (Nat.zero_add _)
theorem delTwo_sum (f : Decor → Nat) {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) (ka kb : Bool) :
    ((delTwo ws a b ka kb).map f).sum = (ws.map f).sum - (cond ka 0 (f a)) - (cond kb 0 (f b)) := by
  have er {l : List Decor} {x : Decor} (hx : x ∈ l) : (l.map f).sum = f x + ((l.erase x).map f).sum := by
    have := ((List.perm_cons_erase hx).map f).sum_eq
    rwa [List.map_cons,List.sum_cons] at this
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  have e1 := er ha
  have e2 := er hb
  have e3 := er hm
  cases ka <;> cases kb <;> simp only [delTwo,delOne,Bool.false_eq_true,ite_true,ite_false,cond_true,cond_false] <;> omega
theorem fastCost_good {u p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws) (ne : a≠b) (al : allowedB u op=true)
    (h : slowCost u p ws k a b op ka kb=true) :
    scalarPoolCut u p k ((delTwo ws a b ka kb).map Prod.fst) (movedChoice op a b)=true := by
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let rest := delTwo ws a b ka kb
  have ck := keptCount const ws a b ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b kb ≤ rest.countP const at ck
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  obtain ⟨⟨hu,hc⟩,hz⟩ := h
  have sum := delTwo_sum (unav u p) ha hb ne ka kb
  rw [hu] at sum
  have zs : ((delTwo ws a b ka kb).map (unav u p)).sum=0 := by omega
  have hs : (rest.map Prod.fst).all (availableB u p.domain p.wires)=true := by
    apply List.all_eq_true.mpr
    intro _ hm
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
    have v := List.sum_eq_zero_iff.mp zs _ (List.mem_map_of_mem hw)
    cases e : availableB u p.domain p.wires w.1
    · simp [unav,e] at v
    · rfl
  have opOK : (!(!availableB u p.domain p.wires z) || choiceOK u p.domain p.wires (movedChoice op a b))=true := by
    simp only [Bool.or_eq_true,Bool.and_eq_true] at hz
    rcases hz with hz | ⟨x,y⟩
    · simp [z,hz]
    · simp [choiceOK,movedChoice,x,y,al]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b kb+(isMaskedConstant p.domain z).toNat) at hc
  dsimp only [rest] at hs
  have ez : choiceVal (movedChoice op a b)=z := rfl
  simp only [scalarPoolCut,ez,hs,opOK,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
  cases hc' : isMaskedConstant p.domain z <;> simp [hc'] at hc ⊢ <;> omega

theorem zN_full (op : Nat) (a b : Sig) : zN op a.toNat b.toNat = (bin op a b).toNat := by
  have e (v : Sig) : nmask one.toNat v = v.toNat := by
    rw [nmask_eq]
    congr 1
    exact BitVec.and_allOnes
  have := zN_eq op one a b
  rwa [e,e,e] at this
theorem getW (ws : List Decor) (i : Nat) :
    (ws.map (fun w : Decor => w.1.toNat)).getD i 0 = (ws.getD i defaultDecor).1.toNat := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none =>
    have z0 : zero.toNat=0 := by simp [zero]
    exact z0.symm
  | some v => rfl
theorem wire_ne {c : NodeContext} {i j} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) : (contextWire c i).1 ≠ (contextWire c j).1 := by
  have gi : contextWire c i = c.2.2.1[i] := by simp [contextWire,List.getD_eq_getElem?_getD,hi]
  have gj : contextWire c j = c.2.2.1[j] := by simp [contextWire,List.getD_eq_getElem?_getD,hj]
  rw [gi,gj]
  intro e
  apply hij
  apply (List.Nodup.getElem_inj_iff nd (hi:=by simpa using hi) (hj:=by simpa using hj)).mp
  simpa using e
theorem link_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) (h : linkAt fl (laneOf c) i j op ka kb=true) :
    (c.2.2.2.2.2 (keySet (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))).any (sameWords
      (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  have hne := wire_ne nd hi hj hij
  have ha := mem i hi
  have hb := mem j hj
  have hab : contextWire c i ≠ contextWire c j := fun e => hne (congrArg Prod.fst e)
  have kv (v : Sig) := kept_value nd ha hb ka kb v
  have sum := delTwo_sum (fun w : Decor => keyWord w.1) ha hb hab ka kb
  have wi : contextWire c i = c.2.2.1.getD i defaultDecor := rfl
  have wj : contextWire c j = c.2.2.1.getD j defaultDecor := rfl
  simp only [linkAt,laneOf,force_eq,getW,←wi,←wj,zN_full] at h
  generalize contextWire c i=a at *
  generalize contextWire c j=b at *
  change Option.rec false _ (fl (keyWord (bin op a.1 b.1)+(((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum -
    (cond ka 0 (keyWord a.1)) - (cond kb 0 (keyWord b.1)))))=true at h
  have tot : ((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum = (c.2.2.1.map (fun w : Decor => keyWord w.1)).sum := by
    rw [List.map_map]
    rfl
  rw [tot,←sum] at h
  have tag : keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst) =
      keyWord (bin op a.1 b.1)+((delTwo c.2.2.1 a b ka kb).map (fun w : Decor => keyWord w.1)).sum := by
    rw [keySet_sum,List.map_cons,List.sum_cons,List.map_map]
    rfl
  rw [←tag] at h
  generalize keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst)=t at h ⊢
  cases hf : fl t with
  | none => simp [hf] at h
  | some ys =>
    obtain ⟨xs,hx,rfl⟩ := hfl t ys hf
    rw [hf] at h
    simp only [forceMap_eq,List.map_id',Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,anyEq_iff,Nat.beq_eq,Bool.not_eq_true'] at h
    obtain ⟨h1,h2,h3⟩ := h
    have back {v : Sig} (hv : v.toNat ∈ xs.map BitVec.toNat) : v ∈ xs := by
      obtain ⟨w,hw,e⟩ := List.mem_map.mp hv
      exact BitVec.toNat_inj.mp e ▸ hw
    apply List.any_eq_true.mpr
    refine ⟨xs,hx,?_⟩
    simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
    constructor
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact back h1
      · obtain ⟨hw,va,vb⟩ := (kv v).mp hv
        obtain ⟨w,hm,rfl⟩ := List.mem_map.mp hw
        rcases h2 _ (List.mem_map_of_mem hm) with ⟨x,y⟩ | ⟨x,y⟩ | x
        · rcases va with va | va
          · exact absurd (BitVec.toNat_inj.mp y) va
          · simp [va] at x
        · rcases vb with vb | vb
          · exact absurd (BitVec.toNat_inj.mp y) vb
          · simp [vb] at x
        · exact back x
    · intro v hv
      rcases h3 _ (List.mem_map_of_mem hv) with x | ⟨⟨x,y⟩,m⟩
      · exact List.mem_cons.mpr (Or.inl (BitVec.toNat_inj.mp x))
      · refine List.mem_cons_of_mem _ ((kv v).mpr ⟨?_,?_,?_⟩)
        · obtain ⟨w,hw,e⟩ := List.mem_map.mp m
          exact BitVec.toNat_inj.mp e ▸ List.mem_map_of_mem hw
        · rcases x with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
        · rcases y with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
noncomputable def fallbackAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  or (and (and (Nat.ble (Nat.succ i) l.2.1) (and (Nat.ble (Nat.succ j) l.2.1) (and (Nat.ble (Nat.succ op) l.2.2.1) (not (Nat.beq i j)))))
    (or (l.2.2.2.1.any fun s => fastCost s i j op ka kb) (linkAt fl l i j op ka kb))) (checkAt l.1 i j op ka kb)
theorem fallback_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (h : fallbackAt fl (laneOf c) i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true,Bool.and_eq_true] at h
  rcases h with ⟨⟨hi,hj,ho,hn⟩,h | h⟩ | h
  · have hi := Nat.ble_eq.mp hi
    have hj := Nat.ble_eq.mp hj
    have ho := Nat.ble_eq.mp ho
    change Nat.succ i ≤ c.2.2.1.length at hi
    change Nat.succ j ≤ c.2.2.1.length at hj
    change Nat.succ op ≤ cond c.2.2.2.1.2 4 2 at ho
    have al : allowedB c.2.2.2.1.2 op=true := by
      cases hu : c.2.2.2.1.2 <;> simp [hu] at ho <;> simp [allowedB] <;> omega
    have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
      simp [contextWire,List.getD_eq_getElem?_getD,ht]
    obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    have hne := wire_ne nd hi hj (fun e => by simp [e] at hn)
    have closed := fastCost_good (mem i hi) (mem j hj) (fun e => hne (congrArg Prod.fst e)) al (fast_slow ok)
    have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut c.2.2.2.1.2 p (c.1-1)
        ((delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst)
        (movedChoice op (contextWire c i) (contextWire c j)))=true :=
      List.any_eq_true.mpr ⟨p,hp,closed⟩
    simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
    repeat' split
    all_goals rfl
  · have cut := link_sound nd hfl (Nat.ble_eq.mp hi) (Nat.ble_eq.mp hj) (fun e => by simp [e] at hn) h
    simp only [checkAt,evalMove,closeChild,cut,Bool.true_or]
    repeat' split
    all_goals rfl
  · exact h
def swapIdx (v t : Nat) : Nat := cond (Nat.beq t (v &&& 15)) (v >>> 4) (cond (Nat.beq t (v >>> 4)) (v &&& 15) t)
def validSwap (v : Nat) : Bool := and (Nat.ble ((v &&& 15)+1) (v >>> 4)) (Nat.ble ((v >>> 4)+1) 9)
set_option maxRecDepth 8192 in
theorem swap_table : ∀ v : Fin 144, validSwap v.val=true → ∀ t : Fin 9, swapIdx v.val t.val<9 ∧
    wordMove (swapRows v.val) (inputs.getD t.val zero) = inputs.getD (swapIdx v.val t.val) zero := by decide +kernel
theorem swap_input {v t : Nat} (hv : validSwap v=true) (ht : t<9) : swapIdx v t<9 ∧
    wordMove (swapRows v) (inputs.getD t zero) = inputs.getD (swapIdx v t) zero := by
  have lt : v<144 := by
    simp only [validSwap,Bool.and_eq_true,Nat.ble_eq,Nat.shiftRight_eq_div_pow] at hv
    omega
  exact swap_table ⟨v,lt⟩ hv ⟨t,ht⟩
def idxOf (perm : List Nat) (t : Nat) : Nat := perm.foldl (fun t v => swapIdx v t) t
theorem idx_move {perm : List Nat} (ok : perm.all validSwap=true) {t : Nat} (ht : t<9) :
    movedWord (perm.map swapRows).reverse (inputs.getD t zero) = inputs.getD (idxOf perm t) zero := by
  rw [movedWord,List.foldr_reverse,List.foldl_map]
  induction perm generalizing t with
  | nil => rfl
  | cons v perm ih =>
    simp only [List.all_cons,Bool.and_eq_true] at ok
    obtain ⟨lt,e⟩ := swap_input ok.1 ht
    rw [List.foldl_cons,e,ih ok.2 lt]
    rfl
noncomputable def decodeN : Nat → Nat → List Nat → List Nat
  | 0,_,ws => ws
  | n+1,bits,ws => force (zN ((bits >>> 8) &&& 3) (ws.getD (bits &&& 15) 0) (ws.getD ((bits >>> 4) &&& 15) 0))
      fun z => decodeN n (bits >>> 10) (ws++[z])
theorem decodeN_eq (F : Sig → Nat) (F0 : F zero=0) (Fb : ∀ op a b, F (bin op a b)=zN op (F a) (F b))
    (n bits : Nat) (ds : List Decor) :
    (decodeBank n bits ds).map (fun w => F w.1) = decodeN n bits (ds.map fun w => F w.1) := by
  have gd (ds : List Decor) (i : Nat) : (ds.map fun w => F w.1).getD i 0 = F (ds.getD i defaultDecor).1 := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases ds[i]? with
    | none => exact F0.symm
    | some v => rfl
  induction n generalizing bits ds with
  | zero => rfl
  | succ n ih =>
    rw [decodeN,force_eq,decodeBank,ih,gd,gd,←Fb,List.map_append]
    rfl
theorem selectLive_map {α β : Type} (f : α → β) (bits : Nat) (ws : List α) :
    (selectLive bits ws).map f = selectLive bits (ws.map f) := by
  induction ws generalizing bits with
  | nil => rfl
  | cons w ws ih =>
    rw [List.map_cons,selectLive,selectLive]
    split
    · rw [List.map_cons,ih]
    · exact ih _
noncomputable def fastState (g : Forest) (k i : Nat) (perm : List Nat) : List Nat :=
  let raw := (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*depth
  force (packedAt data (i*(len+(selected g.mask).length+depth)) (len+(selected g.mask).length+depth)) fun rec =>
  selectLive (rec >>> len) (decodeN depth (rec &&& ((1 <<< len)-1)) raw)
theorem fastState_eq (g : Forest) (k i : Nat) {perm : List Nat} (ok : perm.all validSwap=true) :
    fastState g k i perm = ((stateSet g k i).map (movedWord (perm.map swapRows).reverse)).map BitVec.toNat := by
  let ms := (perm.map swapRows).reverse
  let F (a : Sig) : Nat := (movedWord ms a).toNat
  have F0 : F zero=0 := by
    change (movedWord ms zero).toNat=0
    rw [moved_eq_rename,(rename_constants _).1]
    simp [zero]
  have Fb (op a b) : F (bin op a b)=zN op (F a) (F b) := by
    change (movedWord ms (bin op a b)).toNat = zN op (movedWord ms a).toNat (movedWord ms b).toNat
    rw [zN_full,moved_eq_rename,rename_bin,moved_eq_rename,moved_eq_rename]
  have raw : (wiresOf g).map (fun w => F w.1) = (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat := by
    simp only [wiresOf,rawDecor,List.map_map]
    apply List.map_congr_left
    rintro ⟨j,a⟩ hm
    obtain ⟨hj,rfl⟩ := selected_entry hm
    exact congrArg BitVec.toNat (idx_move ok hj)
  have len : (wiresOf g).length = (selected g.mask).length := by simp [wiresOf,rawDecor]
  unfold fastState stateSet readNode
  rcases g.levels k with ⟨a,depth,b,c,d,e,f,data⟩
  simp only [force_eq,storedDepth,len]
  rw [List.map_map,List.map_map,selectLive_map,←raw,←decodeN_eq F F0 Fb]
  rfl
noncomputable def linkedFast (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Nat) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).bind fun perm => cond (perm.all validSwap) (some (fastState g k pair.1 perm)) none
noncomputable def flOf (g : Forest) (k : Nat) : Nat → Option (List Nat) := fun tag => (g.index k tag).bind (linkedFast g (k-1))
noncomputable def batchMove (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,cov) := b
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  if len>k then true else
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp op a b'
    let mask := fullMarks r (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b') ka kb ||| packedColumn (!u) z)
    onMarks (fun c => fallbackAt fl c i j op ka kb) mask xs

theorem batchMove_at {fl u} (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (pass : batchMove fl u (makeBatch k n xs) (xs.map laneOf) i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 416 then true
      else if !properB (dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild u xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((delTwo xs[q].2.2.1 (contextWire xs[q] i) (contextWire xs[q] j) ka kb).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,mode,len,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b) ka kb |||
        packedColumn (!u) (packedOp op a b))) (xs.map laneOf)) = true at pass
    rw [if_neg small] at pass
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r,cov] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 416
    · apply fallback_sound nd hfl
      have m := marked_ok _ _ _ q (by simpa using hq) (by
        rw [mark_at _ _ _ hq]
        exact beq_iff_eq.mpr hit) pass
      simpa only [List.getElem_map] using m
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]

noncomputable def batchPair (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) :=
  let f := batchMove fl u b xs i j op
  f false false && f true false && f false true && f true true
noncomputable def batchRow (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i : Nat) (js : List Nat) :=
    js.all (fun j => (opsOf u).all (batchPair fl u b xs i j))
noncomputable def batchRows (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) : List Nat → Bool
  | [] => true
  | i::js => batchRow fl u b xs i js && batchRows fl u b xs js

theorem batchRows_at {fl u} (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows fl u (makeBatch k n xs) (xs.map laneOf) js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    refine ⟨?_,ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩ op hop
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    rw [mode] at hop
    have pass := allRows.1 j hj op hop
    have check := @batchMove_at fl u k n xs i j op
    simp only [batchPair,Bool.and_eq_true] at pass
    simp only [testPair,Bool.and_eq_true]
    exact ⟨⟨⟨check hi hj' hq budget arity mode nd hfl pass.1.1.1,check hi hj' hq budget arity mode nd hfl pass.1.1.2⟩,
      check hi hj' hq budget arity mode nd hfl pass.1.2⟩,check hi hj' hq budget arity mode nd hfl pass.2⟩

noncomputable def runBatch (fl : Nat → Option (List Nat)) (u : Bool) (k n : Nat) (xs : List NodeContext) :=
    batchRows fl u (makeBatch k n xs) (xs.map laneOf) (List.range n)
theorem runBatch_at {fl u k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hm : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (hn : xs[q].2.2.1.length=n)
    (pass : runBatch fl u k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha hm nd hfl (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov g.mode ws,rules,ls)

theorem flOf_ok (g : Forest) (k i tag : Nat) (ys) (h : flOf g k tag=some ys) :
    ∃ xs ∈ (contextOf g k i).2.2.2.2.2 tag, ys=xs.map BitVec.toNat := by
  change ∃ xs ∈ ((g.index k tag).bind (linkedSet g (k-1))).toList, _
  unfold flOf at h
  cases hp : g.index k tag with
  | none => simp [hp] at h
  | some pair =>
    simp only [hp,Option.bind_some,linkedFast] at h
    simp only [Option.bind_some,linkedSet]
    split at h
    · contradiction
    next v =>
      cases ha : g.autos[pair.2]? with
      | none => simp [ha] at h
      | some perm =>
        simp only [ha,Option.bind_some] at h
        cases hv : perm.all validSwap with
        | false => simp [hv] at h
        | true =>
          simp only [hv,cond_true,Option.some.injEq] at h
          refine ⟨(stateSet g (k-1) pair.1).map (movedWord (perm.map swapRows).reverse),?_,?_⟩
          · simp [v]
          · exact h.symm.trans (fastState_eq g _ _ hv)

def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)) := rfl

theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩

def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
-- Evaluate each packed column before sharing it across the row checks.
noncomputable def forceSignals {β : Type} (sigs : List PackedSig)
    (cont : List PackedSig → β) : β :=
  match sigs with
  | [] => cont []
  | (pos, neg)::tail =>
    force pos fun pos => force neg fun neg =>
    forceSignals tail fun rest => cont ((pos, neg)::rest)

theorem forceSignals_eq {β : Type} (sigs : List PackedSig)
    (cont : List PackedSig → β) : forceSignals sigs cont = cont sigs := by
  induction sigs generalizing cont with
  | nil => rfl
  | cons sig sigs ih =>
    obtain ⟨pos, neg⟩ := sig
    simp only [forceSignals, force_eq, ih]

noncomputable def forceBatch {β : Type} (b : Batch) (cont : Batch → β) : β :=
  let (k,n,count,sigs,any,once,twice) := b
  force count fun count => forceSignals sigs fun sigs =>
    force any fun any => force once fun once => force twice fun twice =>
    cont (k,n,count,sigs,any,once,twice)

theorem forceBatch_eq {β : Type} (b : Batch)
    (cont : Batch → β) : forceBatch b cont = cont b := by
  obtain ⟨k,n,count,sigs,any,once,twice⟩ := b
  simp only [forceBatch, force_eq, forceSignals_eq]

noncomputable def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  forceBatch (makeBatch k ar xs) fun b =>
    forceLanes xs fun ys => (List.range len).all (fun d =>
      let i := lo+d
      batchRow (flOf g k) g.mode b ys i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (flOf g k) g.mode (makeBatch k ar (contexts g k start n)) ((contexts g k start n).map laneOf)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  simp only [rowCut,forceBatch_eq,forceLanes_eq] at h
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  simp only [rowCut,forceBatch_eq,forceLanes_eq]
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)

theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch (flOf g k) g.mode k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (flOf g k) g.mode (makeBatch k ar xs) (xs.map laneOf) (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have nd : (xs[q].2.2.1.map Prod.fst).Nodup := by
    have p := one.2
    simp only [prelim,Bool.and_eq_true,decide_eq_true_eq] at p
    rw [e]
    exact p.1
  have hfl : ∀ tag ys, flOf g k tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat := by
    rw [e]
    exact fun tag ys h => flOf_ok g k i tag ys h
  have hm : xs[q].2.2.2.1.2=g.mode := by rw [e]; rfl
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hm nd hfl hn (cutsRun h)

def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v

def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

def listPieces {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d ∧ listPieces f (xs.drop (xs.length/2)) d
theorem listPieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
theorem slice_self {u} {raw : List Sig} {T : Sig} {L : Nat} (pT : proper T) (h : Lower u raw T L) :
    Slice u raw T one L := by
  refine ⟨id,raw,fun r => bit_one r,fun a ha => ?_,observe_proper pT,h⟩
  exact Or.inl (List.mem_map_of_mem ha)

theorem plainA {u} {m q cap : Nat} {prior : Nat → Nat} (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (e : (graphGoal q == graphGoal m && (varsX q == vars m) && (prior q == cap+1) && properB (graphGoal m) &&
      decide (vars m).Nodup && poolCut u one (cap+1) cap 0 (vars m) (vars m)) = true) :
    Impossible u (graphGoal m) cap (vars m).toFinset := by
  simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at e
  obtain ⟨⟨⟨⟨⟨e1,e2⟩,e3⟩,e4⟩,e5⟩,e6⟩ := e
  have h := low q
  rw [e1,e2,e3] at h
  exact poolCut_sound (slice_self (proper_of _ e4) h) [] rfl e5 e6

theorem cut_root {u} {m cap : Nat} {prior : Nat → Nat} {ws : List Sig}
    (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q)) (ci : ColumnInfo)
    (ok : colCheck m ci prior = true)
    (cut : (decide ws.Nodup && poolCut u (subcube ci.1 ci.2.1) ci.2.2.2.2 cap 0 (varsX (rawMask m ci)) ws)=true) :
    Impossible u (graphGoal m) cap ws.toFinset := by
  simp only [Bool.and_eq_true,decide_eq_true_eq] at cut
  exact poolCut_sound (col_sound ci prior low ok) [] rfl cut.1 cut.2

theorem index_root {u} {g : Forest} {m cap i : Nat} {prior : Nat → Nat} {ws : List Sig}
    (hm : g.mask=m) (hu : g.mode=u) (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g cap)
    (idx : indexedRoot g cap i ws = true) : Impossible u (graphGoal m) cap ws.toFinset := by
  subst hm
  subst hu
  exact root_index low geom blocks (Nat.le_refl _) idx

def essOK (m hints : Nat) : Bool :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs && (xs.map Prod.fst == vars m)
theorem plain_low {u} {m hints cap : Nat} (ok : essOK m hints = true)
    (a : Impossible u (graphGoal m) cap (vars m).toFinset) : Lower u (vars m) (graphGoal m) (cap+1) := by
  simp only [essOK,Bool.and_eq_true,beq_iff_eq] at ok
  apply lower_impossible (proper_of _ ok.1.1) (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 _ a
  intro v hv
  apply essential_ok ok.1.2 v
  rw [ok.2]
  exact List.mem_toFinset.mpr hv

def neighbor10830 (i : Fin 9) : Nat := [4,5,6,7,0,1,0,0,2].getD i.val 0
def absentRow10830 (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighbor10830 i)
def presentRow10830 (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor10830 i))

set_option maxHeartbeats 1000000 in
theorem requiredInputs :
    (∀ i : Fin 9, bit (absentRow10830 i) graph ≠ bit (presentRow10830 i) graph) ∧
    (∀ i j : Fin 9, i ≠ j →
      bit (absentRow10830 i) (inputs.getD j.val zero) =
      bit (presentRow10830 i) (inputs.getD j.val zero)) := by decide +kernel


theorem twoRoots (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 14) :
    ∃ (u : Bool) (k : Nat), k ≤ (if u then 13 else 14) ∧ Live u graph k inputs.toFinset := by
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have len : C.gates.length ≤ 14 := small
  have mode : ∃ u : Bool, (u=false → ∀ g ∈ C.gates, isNot g=false) ∧ C.gates.countP (fun g => !isNot g) ≤ (if u then 13 else 14) := by
    by_cases hn : ∀ g ∈ C.gates, isNot g=false
    · refine ⟨false,fun _ => hn,?_⟩
      have := List.countP_le_length (p:=fun g => !isNot g) (l:=C.gates)
      simp only [Bool.false_eq_true,ite_false]
      omega
    · refine ⟨true,by simp,?_⟩
      push Not at hn
      obtain ⟨g,hg,hx⟩ := hn
      have lt : C.gates.countP (fun g => !isNot g) < C.gates.length := by
        rcases Nat.lt_or_ge (C.gates.countP (fun g => !isNot g)) C.gates.length with h | h
        · exact h
        · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
          simp only [Bool.not_eq_true'] at eq
          exact absurd eq hx
      simp only [ite_true]
      omega
  obtain ⟨u,mono,count⟩ := mode

  have out := get_rep (u:=u) (execute C.gates inputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract C.gates inputs legal mono graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : inputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ inputs) : ∃ i : Fin 9, inputs.getD i.val zero = a := by
    rw [←input_list] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = inputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run inputs (inputs.getD i.val zero) sub (absentRow10830 i) (presentRow10830 i)
        (requiredInputs.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply requiredInputs.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨u,k,hk.trans count,eq ▸ run⟩

theorem directSplit
    (m : ∀ k, k ≤ 14 → ¬Live false graph k inputs.toFinset)
    (s : ∀ k, k ≤ 13 → ¬Live true graph k inputs.toFinset) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 edge 14 := by
  rintro ⟨C,legal,small,computes⟩
  obtain ⟨mode,k,hk,run⟩ := twoRoots C legal (funext computes) small
  cases mode
  · exact m k hk run
  · exact s k hk run


def padSamples (n a : Nat) : Bits :=
  BitVec.ofNat _ (if a.testBit 0 then a ||| (((1 <<< 416)-1) ^^^ ((1 <<< n)-1)) else a)
def sampleAt (n : Nat) (data : Array (Nat × Nat)) (i : Nat) : Bits × Bits :=
  let p := data[i]?.getD (0,0)
  (padSamples n p.1,padSamples n p.2)
def mixTag (h : Nat) : Nat := (h*513158153883743911432465183)%618970019642690137449562111
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls17 : Lower true (vars 17) (graphGoal 17) 1 := size_of (hints:=4) (by decide +kernel)
def es17 := extendKnown [] 1 [(17,[]),(34,[84,16]),(65,[101,100]),(66,[101,100,16]),(68,[101,33,100,32]),(129,[118,117,116]),(136,[118,117,50,49,116,48]),(144,[118,117,115,114,113,116,64]),(260,[135,134,133,33,132,32]),(264,[135,134,133,50,49,132,48]),(288,[135,134,83,82,81,132,80])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs17 : Known true es17 := extendKnown_ok (m:=17) baseKnown ls17 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls67 : Lower true (vars 67) (graphGoal 67) 2 := size_of (hints:=102) (by decide +kernel)
def es67 := extendKnown es17 2 [(67,[]),(69,[33]),(70,[33,16]),(81,[67,66,100,97,64]),(98,[84,83,82,97,80]),(137,[50,118,49]),(152,[67,50,118,65,48]),(193,[117,116,115,114,113,96]),(268,[135,134,49,32]),(290,[135,133,132,131,130,101,129,16]),(292,[135,84,83,134,81,32]),(296,[135,84,83,50,134,81,48]),(324,[135,133,132,131,98,129,96]),(392,[117,116,131,114,99,129,112])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs67 : Known true es67 := extendKnown_ok (m:=67) vs17 ls67 (by decide +kernel)
def s145S := sampleAt 9 #[(0x3f,0x49),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x1c7,0x92),(0x0,0x0),(0x0,0x0),(0x1f8,0x124),(0x0,0x0)]
def s145C : List ColumnInfo := []
def s145D3 (_ : Nat) : Nat := 0x7
def s145L : Nat → Packing
  | 3 => (1,0,1,0,0,1,0,s145D3)
  | _ => emptyPacking
def s145I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s145 : Forest := ⟨145,3,s145S,s145C,[[]],s145L,s145I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs145_3_0 : block s145 3 0 1 = true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs145_3 : block s145 3 0 1 = true := bs145_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts145 : checkedTables s145 3 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · exact bs145_3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs145 : graphValid s145 (boundsBefore es67) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls145 : Lower true (vars 145) (graphGoal 145) 4 := lower_forest (g:=s145) (i:=0) (hints:=4) (before_sound es67 vs67) gs145 ts145 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es145 := extendKnown es67 4 [(145,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs145 : Known true es145 := extendKnown_ok (m:=145) vs67 ls145 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls51 : Lower true (vars 51) (graphGoal 51) 3 := size_of (hints:=1048660) (by decide +kernel)
def es51 := extendKnown es145 3 [(51,[]),(163,[118,116]),(170,[118,50,116,117,49,16]),(178,[118,115,114,116,117,65,16]),(202,[50,100,117,49,16]),(204,[100,117,49,32]),(210,[99,98,100,117,65,16]),(212,[99,100,117,65,32]),(277,[135,134,133,33]),(281,[135,134,50,133,49]),(305,[135,134,131,130,133,81]),(329,[135,50,100,133,49]),(330,[135,50,100,133,49,16]),(353,[135,134,131,130,100,133,81]),(389,[135,118,116,133,33]),(404,[134,131,132,117,65,32]),(417,[134,131,130,116,133,81]),(432,[135,118,131,114,116,133,81,64])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs51 : Known true es51 := extendKnown_ok (m:=51) vs145 ls51 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls71 : Lower true (vars 71) (graphGoal 71) 3 := size_of (hints:=1638) (by decide +kernel)
def es71 := extendKnown es51 3 [(71,[]),(300,[135,84,83,134,82,49,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs71 : Known true es71 := extendKnown_ok (m:=71) vs51 ls71 (by decide +kernel)
def s83S := sampleAt 21 #[(0x60fff,0x221a3),(0x1bf060,0xa736a),(0x0,0x0),(0x0,0x0),(0x1c007f,0x1d4a5c),(0x0,0x0),(0x1fff80,0x158c10),(0x0,0x0),(0x0,0x0)]
def s83C : List ColumnInfo := []
def s83D3 (_ : Nat) : Nat := 0xf
def s83L : Nat → Packing
  | 3 => (1,0,1,0,0,1,0,s83D3)
  | _ => emptyPacking
def s83I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s83 : Forest := ⟨83,3,s83S,s83C,[[]],s83L,s83I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs83_3_0 : block s83 3 0 1 = true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs83_3 : block s83 3 0 1 = true := bs83_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts83 : checkedTables s83 3 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · exact bs83_3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs83 : graphValid s83 (boundsBefore es71) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls83 : Lower true (vars 83) (graphGoal 83) 4 := lower_forest (g:=s83) (i:=0) (hints:=100) (before_sound es71 vs71) gs83 ts83 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es83 := extendKnown es71 4 [(83,[]),(85,[33]),(99,[84,16]),(102,[32,84,33]),(195,[117,116]),(197,[117,116,33]),(201,[117,50,118,100,49]),(294,[135,133,130,101,128,66]),(298,[135,133,131,130,101,128,67]),(325,[135,133,32,132,16]),(326,[135,133,32,132]),(332,[135,133,134,32,100,49]),(354,[135,83,82,80,132,97]),(356,[135,83,134,32,100,81]),(393,[135,133,50,118,48,132,16]),(396,[117,50,134,48,116,33]),(408,[135,133,131,50,118,48,132,65]),(424,[83,50,134,48,116,81])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs83 : Known true es83 := extendKnown_ok (m:=83) vs71 ls83 (by decide +kernel)
def s153S := sampleAt 21 #[(0x87ff,0x191a3),(0x0,0x0),(0x0,0x0),(0x10f860,0x15bb6a),(0x1f007f,0x16224c),(0x0,0x0),(0x0,0x0),(0x1fff80,0x84410),(0x0,0x0)]
def s153C : List ColumnInfo := [(8,0,145,512,4)]
def s153D4 (_ : Nat) : Nat := 0x2f
def s153L : Nat → Packing
  | 4 => (1,0,1,0,0,1,0,s153D4)
  | _ => emptyPacking
def s153I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s153 : Forest := ⟨153,4,s153S,s153C,[[]],s153L,s153I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs153_4_0 : block s153 4 0 1 = true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs153_4 : block s153 4 0 1 = true := bs153_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts153 : checkedTables s153 4 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs153_4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs153 : graphValid s153 (boundsBefore es83) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls153 : Lower true (vars 153) (graphGoal 153) 5 := lower_forest (g:=s153) (i:=0) (hints:=28676) (before_sound es83 vs83) gs153 ts153 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es153 := extendKnown es83 5 [(153,[]),(209,[101,116,64,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs153 : Known true es153 := extendKnown_ok (m:=153) vs83 ls153 (by decide +kernel)
def s87S := sampleAt 36 #[(0x6820ffff,0x28a21aa3),(0x9b03f0660,0x8b1a7366a),(0xe3fc00780,0xa39c6378a),(0x0,0x0),(0xfc00007ff,0xfc514a55c),(0x0,0x0),(0xffffff800,0x54618c010),(0x0,0x0),(0x0,0x0)]
def s87C : List ColumnInfo := [(4,0,83,512,4)]
def s87D4 (_ : Nat) : Nat := 0x5f
def s87L : Nat → Packing
  | 4 => (1,0,1,0,0,1,0,s87D4)
  | _ => emptyPacking
def s87I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s87 : Forest := ⟨87,4,s87S,s87C,[[]],s87L,s87I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs87_4_0 : block s87 4 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs87_4 : block s87 4 0 1 = true := bs87_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts87 : checkedTables s87 4 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs87_4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs87 : graphValid s87 (boundsBefore es153) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls87 : Lower true (vars 87) (graphGoal 87) 5 := lower_forest (g:=s87) (i:=0) (hints:=1636) (before_sound es153 vs153) gs87 ts87 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es87 := extendKnown es153 5 [(87,[]),(103,[16,84]),(199,[117,116]),(302,[135,83,134,80,50,33,65]),(327,[135,133,32,16,132]),(364,[135,83,134,80,82,49,100]),(428,[134,48,82,33,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs87 : Known true es87 := extendKnown_ok (m:=87) vs153 ls87 (by decide +kernel)
def s115S := sampleAt 41 #[(0xb303f3c0ff,0x1128b1d253),(0x14dfc0cffc0,0x51c6447ca),(0x0,0x0),(0x0,0x0),(0x18e000f00ff,0x18e924e24ac),(0x1f0000fff00,0x1f0a28bb830),(0x1fffff00000,0x1eac3002020),(0x0,0x0),(0x0,0x0)]
def s115C : List ColumnInfo := []
def s115D4 (_ : Nat) : Nat := 0x1f
def s115L : Nat → Packing
  | 4 => (1,0,1,0,0,1,0,s115D4)
  | _ => emptyPacking
def s115I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s115 : Forest := ⟨115,4,s115S,s115C,[[]],s115L,s115I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs115_4_0 : block s115 4 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs115_4 : block s115 4 0 1 = true := bs115_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts115 : checkedTables s115 4 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs115_4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs115 : graphValid s115 (boundsBefore es87) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls115 : Lower true (vars 115) (graphGoal 115) 5 := lower_forest (g:=s115) (i:=0) (hints:=1048660) (before_sound es87 vs87) gs115 ts115 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es115 := extendKnown es87 5 [(115,[]),(203,[115,96,113,83,65]),(205,[115,114,96,113,83,66]),(227,[16,117,84]),(333,[135,131,130,98,96,129,83,64]),(334,[135,131,98,96,129,83,65]),(341,[135,33,133]),(355,[135,134,96,129,133,64]),(357,[135,130,98,96,129,64]),(362,[135,131,130,128,101,67]),(397,[135,115,130,99,112,129,82,64]),(412,[135,115,130,99,128,113,82,66]),(425,[131,130,99,112,129,64]),(426,[115,114,134,112,49,117,65]),(440,[131,114,99,112,129]),(453,[33,133,116]),(457,[50,118,49,133,100]),(460,[135,134,32,49,117,100])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs115 : Known true es115 := extendKnown_ok (m:=115) vs87 ls115 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls171 : Lower true (vars 171) (graphGoal 171) 4 := size_of (hints:=1077335) (by decide +kernel)
def es171 := extendKnown es115 4 [(171,[]),(186,[66,67,48]),(206,[118,50,48,117,49]),(214,[66,118,50,64,117,65]),(218,[66,67,48,101]),(220,[66,67,48,101,33]),(234,[100,98,118,99,112,117,49]),(242,[66,116,99,112,117,65]),(285,[135,32,84,16]),(307,[132,116,131,84,16]),(309,[135,67,32,84,16]),(313,[66,135,67,48,84,16]),(331,[134,118,133,49]),(345,[134,100,98,116,99,64,133,49]),(361,[100,98,135,99,48,101,16]),(369,[132,130,116,99,64,133,81]),(419,[134,132,131,117,16]),(421,[134,132,135,115,32,117,16]),(434,[134,66,131,64,117,65]),(436,[134,135,115,32,117,65]),(458,[134,132,130,135,131,112,101]),(468,[134,98,114,131,96,117,65]),(481,[132,130,118,115,96,133,81])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs171 : Known true es171 := extendKnown_ok (m:=171) vs115 ls171 (by decide +kernel)
def s179S := sampleAt 50 #[(0x3003ff3c03ff,0x10250b1c4913),(0xcc0300cfff00,0x4d1746451f4a),(0x0,0x0),(0x0,0x0),(0x30ffc00f003ff,0x1045814e0922c),(0x3f00000fffc00,0x3b26098bae0b0),(0x0,0x0),(0x3ffffff000000,0x2eb82e00300c0),(0x0,0x0)]
def s179C : List ColumnInfo := [(0,32,145,514,5)]
def s179D5 (_ : Nat) : Nat := 0x5f
def s179L : Nat → Packing
  | 5 => (1,0,1,0,0,1,0,s179D5)
  | _ => emptyPacking
def s179I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s179 : Forest := ⟨179,5,s179S,s179C,[[]],s179L,s179I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs179_5_0 : block s179 5 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs179_5 : block s179 5 0 1 = true := bs179_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts179 : checkedTables s179 5 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs179_5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs179 : graphValid s179 (boundsBefore es171) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls179 : Lower true (vars 179) (graphGoal 179) 6 := lower_forest (g:=s179) (i:=0) (hints:=1048660) (before_sound es171 vs171) gs179 ts179 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es179 := extendKnown es171 6 [(179,[]),(405,[134,133,33]),(433,[134,131,130,133,81])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs179 : Known true es179 := extendKnown_ok (m:=179) vs171 ls179 (by decide +kernel)
def s211S := sampleAt 50 #[(0x200ff980ffff,0x1418820683),(0xd80c06ff0180,0x5a5d32a74daa),(0x0,0x0),(0x0,0x0),(0x31ff0070001ff,0x108e06714291c),(0x0,0x0),(0x3e00007fffe00,0x3a4824558b050),(0x3fffff8000000,0x2f70b8060c060),(0x0,0x0)]
def s211C : List ColumnInfo := [(0,2,145,576,5),(2,0,209,512,5),(16,0,195,512,4),(66,0,145,512,4),(128,0,83,512,4)]
def s211D6 (_ : Nat) : Nat := 0x46811f
def s211H5 (_ : Nat) : Nat := 0x4a79809841
def s211D5 (_ : Nat) : Nat := 0x14c0d26060020644ce240fe20fe40fd40fd20fd42
def s211H4 (_ : Nat) : Nat := 0xe45f000d2
def s211D4 (_ : Nat) : Nat := 0xfa509f22a416e25502788a905b09540
def s211L : Nat → Packing
  | 6 => (1,0,3,0,0,1,0,s211D6)
  | 5 => (5,1,3,0,0,6,0,s211D5)
  | 4 => (4,2,3,0,0,4,0,s211D4)
  | _ => emptyPacking
def s211I : Nat → Nat → Option (Nat × Nat)
  | 6,h => lookupWord 2 6 1 7 3 0 s211H5 (mixTag h)
  | 5,h => lookupWord 2 7 1 6 2 0 s211H4 (mixTag h)
  | _,_ => none
def s211 : Forest := ⟨211,6,s211S,s211C,[[]],s211L,s211I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs211_6_0 : block s211 6 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs211_6 : block s211 6 0 1 = true := bs211_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs211_5_0 : block s211 5 0 5 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs211_5 : block s211 5 0 5 = true := bs211_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs211_4_0 : block s211 4 0 4 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs211_4 : block s211 4 0 4 = true := bs211_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts211 : checkedTables s211 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs211_4
  · exact bs211_5
  · exact bs211_6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs211 : graphValid s211 (boundsBefore es179) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls211 : Lower true (vars 211) (graphGoal 211) 7 := lower_forest (g:=s211) (i:=0) (hints:=100) (before_sound es179 vs179) gs211 ts211 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es211 := extendKnown es179 7 [(211,[]),(213,[33]),(409,[131,130,112,64,99,129])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs211 : Known true es211 := extendKnown_ok (m:=211) vs179 ls211 (by decide +kernel)
def s217S := sampleAt 39 #[(0x2041fffff,0xc4311a3),(0x0,0x0),(0x0,0x0),(0x4d07e0b060,0x452ce6b56a),(0x71f800c07f,0x513084c44c),(0x0,0x0),(0x7e0000ff80,0x7ea294ee18),(0x7fffff0000,0x2ac3180810),(0x0,0x0)]
def s217C : List ColumnInfo := [(64,0,153,512,5)]
def s217D5 (_ : Nat) : Nat := 0x5f
def s217L : Nat → Packing
  | 5 => (1,0,1,0,0,1,0,s217D5)
  | _ => emptyPacking
def s217I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s217 : Forest := ⟨217,5,s217S,s217C,[[]],s217L,s217I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs217_5_0 : block s217 5 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs217_5 : block s217 5 0 1 = true := bs217_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts217 : checkedTables s217 5 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs217_5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs217 : graphValid s217 (boundsBefore es211) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls217 : Lower true (vars 217) (graphGoal 217) 6 := lower_forest (g:=s217) (i:=0) (hints:=28676) (before_sound es211 vs211) gs217 ts217 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es217 := extendKnown es211 6 [(217,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs217 : Known true es217 := extendKnown_ok (m:=217) vs211 ls217 (by decide +kernel)
def s358S := sampleAt 50 #[(0x0,0x0),(0x680c0180ffff,0x2a1d10a246a3),(0x900ffeff0180,0x10543a870d8a),(0x0,0x0),(0x0,0x0),(0x31ff0070001ff,0x110e06714291c),(0x3e00007fffe00,0x3c4824558b050),(0x0,0x0),(0x3fffff8000000,0x2ef0b8060c060)]
def s358C : List ColumnInfo := [(2,0,356,512,4),(4,0,354,512,4),(32,0,326,512,4),(64,0,294,512,4),(256,0,102,512,4)]
def s358D6 (_ : Nat) : Nat := 0x234095f
def s358H5 (_ : Nat) : Nat := 0x5726b2c8415300d000e534190a2
def s358D5 (_ : Nat) : Nat := 0xb688de6543ca140fd43fd21fd42fd40fd10fd30fd20fd41fd31fd32
def s358H4 (_ : Nat) : Nat := 0x87c300f570008900a82174e600c2001
def s358D4 (_ : Nat) : Nat := 0x2da2379950f28502788a90d78d510b612a81741550ef00a995e81532bb0aa873e45486b86a885b89540
def s358L : Nat → Packing
  | 6 => (1,0,3,0,0,1,0,s358D6)
  | 5 => (10,1,3,0,0,6,0,s358D5)
  | 4 => (10,2,3,0,0,6,0,s358D4)
  | _ => emptyPacking
def s358I : Nat → Nat → Option (Nat × Nat)
  | 6,h => lookupWord 4 14 3 8 4 0 s358H5 (mixTag h)
  | 5,h => lookupWord 4 16 1 8 4 0 s358H4 (mixTag h)
  | _,_ => none
def s358 : Forest := ⟨358,6,s358S,s358C,[[]],s358L,s358I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs358_6_0 : block s358 6 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs358_6 : block s358 6 0 1 = true := bs358_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs358_5_0 : block s358 5 0 10 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs358_5 : block s358 5 0 10 = true := bs358_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs358_4_0 : block s358 4 0 10 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs358_4 : block s358 4 0 10 = true := bs358_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts358 : checkedTables s358 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs358_4
  · exact bs358_5
  · exact bs358_6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs358 : graphValid s358 (boundsBefore es217) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls358 : Lower true (vars 358) (graphGoal 358) 7 := lower_forest (g:=s358) (i:=0) (hints:=8607762000) (before_sound es217 vs217) gs358 ts358 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es358 := extendKnown es217 7 [(358,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs358 : Known true es358 := extendKnown_ok (m:=358) vs217 ls358 (by decide +kernel)
def s119S := sampleAt 75 #[(0xc60d0101fccf301fff,0x420515142c47324a93),(0x1093601fe0333fff980,0x1160d0e191150f98a),(0x671c7fe0003c3c01e00,0x251473e3c7bc3c6de3a),(0x0,0x0),(0x781f8000003fc001fff,0x781f8a8a953b80c956c),(0x7fe00000003ffffe000,0x7fe00b0b162eeaf0070),(0x7fffffffffc00000000,0x5aca8c0c18000080040),(0x0,0x0),(0x0,0x0)]
def s119C : List ColumnInfo := [(0,16,102,513,5),(0,32,85,514,5),(4,0,115,512,5),(17,0,102,512,4),(34,0,85,512,4)]
def s119D6 (_ : Nat) : Nat := 0x40992bf
def s119D5 (_ : Nat) : Nat := 0x1ef52
def s119L : Nat → Packing
  | 6 => (1,0,3,0,0,1,0,s119D6)
  | 5 => (1,1,3,0,0,1,0,s119D5)
  | _ => emptyPacking
def s119I : Nat → Nat → Option (Nat × Nat)
  | 6,_ => some (0,0)
  | _,_ => none
def s119 : Forest := ⟨119,6,s119S,s119C,[[]],s119L,s119I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs119_6_0 : block s119 6 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs119_6 : block s119 6 0 1 = true := bs119_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs119_5_0 : block s119 5 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs119_5 : block s119 5 0 1 = true := bs119_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts119 : checkedTables s119 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs119_5
  · exact bs119_6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs119 : graphValid s119 (boundsBefore es358) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls119 : Lower true (vars 119) (graphGoal 119) 7 := lower_forest (g:=s119) (i:=0) (hints:=1050196) (before_sound es358 vs358) gs119 ts119 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es119 := extendKnown es358 7 [(119,[]),(231,[16,117,84]),(343,[135,33,133]),(430,[115,134,112,49,117,65]),(455,[33,133,116]),(492,[115,134,112,49,114,117,100])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs119 : Known true es119 := extendKnown_ok (m:=119) vs358 ls119 (by decide +kernel)
def s187S := sampleAt 80 #[(0x10c002403ff33cc03fff,0x1040264290b11cc49513),(0x32c0380300ccffff300,0x12d1791b4644551f34a),(0x0,0x0),(0x9c3003ffc00f0f003c00,0x943076c7c1ef0f0dbc3a),(0xe03ffc00000ff0003fff,0xa0345805014ee0092a2c),(0xffc00000000fffffc000,0xfec26026098bbaae00b0),(0x0,0x0),(0xfffffffffff000000000,0x4b8b81382e00003000c0),(0x0,0x0)]
def s187C : List ColumnInfo := [(8,0,179,512,6)]
def s187D6 (_ : Nat) : Nat := 0xbf
def s187L : Nat → Packing
  | 6 => (1,0,1,0,0,1,0,s187D6)
  | _ => emptyPacking
def s187I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s187 : Forest := ⟨187,6,s187S,s187C,[[]],s187L,s187I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs187_6_0 : block s187 6 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs187_6 : block s187 6 0 1 = true := bs187_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts187 : checkedTables s187 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs187_6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs187 : graphValid s187 (boundsBefore es119) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls187 : Lower true (vars 187) (graphGoal 187) 7 := lower_forest (g:=s187) (i:=0) (hints:=1077332) (before_sound es119 vs119) gs187 ts187 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es187 := extendKnown es119 7 [(187,[]),(497,[134,130,116,64,99,133,81])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs187 : Known true es187 := extendKnown_ok (m:=187) vs119 ls187 (by decide +kernel)
def s207S := sampleAt 68 #[(0x19240fffa4e8103f,0x9242543a4685083),(0x26e380cc0c7301fc0,0x22e392cd2c53254d2),(0x38fc00f00f83fe000,0x28fc12f12e83a6492),(0xc0ffff000ffc00000,0x40b6c7006ffc1428a),(0x0,0x0),(0x0,0x0),(0xff0000000ffffffff,0xd5002402412858b2c),(0xfffffffff00000000,0xbf4938ab800060c30),(0x0,0x0)]
def s207C : List ColumnInfo := [(8,0,199,512,5)]
def s207D5 (_ : Nat) : Nat := 0xbf
def s207L : Nat → Packing
  | 5 => (1,0,1,0,0,1,0,s207D5)
  | _ => emptyPacking
def s207I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s207 : Forest := ⟨207,5,s207S,s207C,[[]],s207L,s207I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs207_5_0 : block s207 5 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs207_5 : block s207 5 0 1 = true := bs207_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts207 : checkedTables s207 5 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs207_5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs207 : graphValid s207 (boundsBefore es187) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls207 : Lower true (vars 207) (graphGoal 207) 6 := lower_forest (g:=s207) (i:=0) (hints:=30310) (before_sound es187 vs187) gs207 ts207 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es207 := extendKnown es187 6 [(207,[]),(335,[135,32,16]),(365,[84,134,80,118,82,16,48]),(429,[84,134,82,33,48]),(444,[134,64,82,33,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs207 : Known true es207 := extendKnown_ok (m:=207) vs187 ls207 (by decide +kernel)
def s215S := sampleAt 78 #[(0x4001fff068080fffff,0x2a8302828206a83),(0x9b3019809b00ff01980,0x8b34b9a68b26a74d9aa),(0xe3c01e00e3ff0001e00,0xa3c4be26a3a7264de2a),(0x0,0x0),(0x303ffe000fc000001fff,0x10151c00cfc14142951c),(0x0,0x0),(0x3fc000000fffffffe000,0x354090048545858b0050),(0x3ffffffff00000000000,0x2feae1570006060c0060),(0x0,0x0)]
def s215C : List ColumnInfo := [(4,0,211,512,7)]
def s215D7 (_ : Nat) : Nat := 0xbf
def s215L : Nat → Packing
  | 7 => (1,0,1,0,0,1,0,s215D7)
  | _ => emptyPacking
def s215I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s215 : Forest := ⟨215,7,s215S,s215C,[[]],s215L,s215I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs215_7_0 : block s215 7 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs215_7 : block s215 7 0 1 = true := bs215_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts215 : checkedTables s215 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs215_7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs215 : graphValid s215 (boundsBefore es207) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls215 : Lower true (vars 215) (graphGoal 215) 8 := lower_forest (g:=s215) (i:=0) (hints:=1636) (before_sound es207 vs207) gs215 ts215 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es215 := extendKnown es207 8 [(215,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs215 : Known true es215 := extendKnown_ok (m:=215) vs207 ls215 (by decide +kernel)
def s219S := sampleAt 78 #[(0x400480ff93380fffff,0xc82418118206a83),(0x1ac0700c06dcff01980,0xad2f26d3254a74d9aa),(0x0,0x0),(0x263007ff0071f0001e00,0x22306d8f0771f162de1a),(0x383ff800007e00001fff,0x2834700c067e0142951c),(0x0,0x0),(0x3fc00000007fffffe000,0x3f424048245aa58b0050),(0x3fffffffff8000000000,0x15cb8270b800060c0060),(0x0,0x0)]
def s219C : List ColumnInfo := [(8,0,211,512,7)]
def s219D7 (_ : Nat) : Nat := 0xbf
def s219L : Nat → Packing
  | 7 => (1,0,1,0,0,1,0,s219D7)
  | _ => emptyPacking
def s219I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s219 : Forest := ⟨219,7,s219S,s219C,[[]],s219L,s219I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs219_7_0 : block s219 7 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs219_7 : block s219 7 0 1 = true := bs219_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts219 : checkedTables s219 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs219_7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs219 : graphValid s219 (boundsBefore es215) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls219 : Lower true (vars 219) (graphGoal 219) 8 := lower_forest (g:=s219) (i:=0) (hints:=28772) (before_sound es215 vs215) gs219 ts219 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es219 := extendKnown es215 8 [(219,[]),(221,[33]),(473,[133,130,112,99,129])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs219 : Known true es219 := extendKnown_ok (m:=219) vs215 ls219 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls222 : Lower true (vars 222) (graphGoal 222) 5 := size_of (hints:=822572640) (by decide +kernel)
def es222 := extendKnown es219 5 [(222,[]),(250,[101,117,100,83,66,49]),(377,[128,134,112,100,67,82,49])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs222 : Known true es222 := extendKnown_ok (m:=222) vs219 ls222 (by decide +kernel)
def s235S := sampleAt 75 #[(0x861c80ffb7380ff980,0x20c8643931860f98a),(0x1186700c049cff01fff,0x82722d1014a344aa3),(0x0,0x0),(0x66387ff0071f0001e00,0x222858f0771f162de1a),(0x0,0x0),(0x783f800007e00001fff,0x783d84c267e054a955c),(0x7fc0000007fffffe000,0x7f40048246ca58b0050),(0x7ffffffff8000000000,0x5dd7270b800060c0060),(0x0,0x0)]
def s235C : List ColumnInfo := [(0,8,99,640,5),(0,32,201,514,5),(8,0,227,512,5),(32,0,203,512,5)]
def s235D6 (_ : Nat) : Nat := 0xe123f
def s235L : Nat → Packing
  | 6 => (1,0,2,0,0,1,0,s235D6)
  | _ => emptyPacking
def s235I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s235 : Forest := ⟨235,6,s235S,s235C,[[]],s235L,s235I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs235_6_0 : block s235 6 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs235_6 : block s235 6 0 1 = true := bs235_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts235 : checkedTables s235 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs235_6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs235 : graphValid s235 (boundsBefore es222) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls235 : Lower true (vars 235) (graphGoal 235) 7 := lower_forest (g:=s235) (i:=0) (hints:=1077334) (before_sound es222 vs222) gs235 ts235 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es235 := extendKnown es222 7 [(235,[]),(349,[32,135,16,84]),(363,[134,128,118,129,80,48]),(371,[134,96,112,129,133,67]),(373,[130,98,96,112,129,67]),(427,[134,81,48]),(442,[132,130,100,128,116,113,84,49]),(459,[118,133,49]),(462,[134,32,118,117,49]),(476,[66,134,64,33,101,67]),(483,[132,134,96,112,129,133,115]),(485,[132,32,135,16,117,83]),(489,[132,130,134,96,135,16,101,83]),(490,[132,130,134,96,118,97,117,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs235 : Known true es235 := extendKnown_ok (m:=235) vs222 ls235 (by decide +kernel)
def s238S := sampleAt 76 #[(0x0,0x0),(0x930fcc0099c03fffff,0x1105cc8808c888d523),(0x31cccf0036e7fc03300,0x114ccf1992a59d9b36a),(0xc60f0ffff8f80003c00,0x42050543f8f8585bc1a),(0x0,0x0),(0xf80ff0003f000003fff,0xf80fa0333f035352adc),(0xfff000003ffffffc000,0xeea000222d526260090),(0xffffffffc0000000000,0xbdfafabc000383800e0),(0x0,0x0)]
def s238C : List ColumnInfo := [(0,128,102,520,5)]
def s238D5 (_ : Nat) : Nat := 0xbf
def s238L : Nat → Packing
  | 5 => (1,0,1,0,0,1,0,s238D5)
  | _ => emptyPacking
def s238I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s238 : Forest := ⟨238,5,s238S,s238C,[[]],s238L,s238I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs238_5_0 : block s238 5 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs238_5 : block s238 5 0 1 = true := bs238_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts238 : checkedTables s238 5 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs238_5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs238 : graphValid s238 (boundsBefore es235) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls238 : Lower true (vars 238) (graphGoal 238) 6 := lower_forest (g:=s238) (i:=0) (hints:=823162448) (before_sound es235 vs235) gs238 ts238 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es238 := extendKnown es235 6 [(238,[]),(246,[67]),(311,[132,134,129,81,33,116,48]),(315,[132,128,96,129,80,33,116,48]),(347,[16,84,33,135]),(423,[134,129,81,33,48]),(438,[134,129,81,33,67]),(470,[133,33,67]),(474,[133,66,118,49]),(498,[132,134,129,133,98,67]),(500,[132,134,97,101,82,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs238 : Known true es238 := extendKnown_ok (m:=238) vs235 ls238 (by decide +kernel)
def s243S := sampleAt 84 #[(0x1086007feb300ff3c03ff,0x204a16110a0b1c4913),(0x2319806014dff00cfff00,0x109a2e8c054746451f4a),(0x0,0x0),(0x0,0x0),(0xcc61ff8018e0000f003ff,0x44208b0298e2424e0922c),(0xf07e00001f00000fffc00,0xf0764c131f0a8a8bae0b0),(0xff8000001ffffff000000,0xfe8048121eab0b00280a0),(0xffffffffe000000000000,0xbbdd705c000c0c00300c0),(0x0,0x0)]
def s243C : List ColumnInfo := [(32,0,211,512,7)]
def s243D7 (_ : Nat) : Nat := 0xbf
def s243L : Nat → Packing
  | 7 => (1,0,1,0,0,1,0,s243D7)
  | _ => emptyPacking
def s243I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s243 : Forest := ⟨243,7,s243S,s243C,[[]],s243L,s243I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs243_7_0 : block s243 7 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs243_7 : block s243 7 0 1 = true := bs243_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts243 : checkedTables s243 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs243_7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs243 : graphValid s243 (boundsBefore es238) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls243 : Lower true (vars 243) (graphGoal 243) 8 := lower_forest (g:=s243) (i:=0) (hints:=1048660) (before_sound es238 vs238) gs243 ts243 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es243 := extendKnown es238 8 [(243,[]),(413,[131,130,112,64,99,129,82]),(441,[131,130,112,64,99,129]),(469,[33,133])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs243 : Known true es243 := extendKnown_ok (m:=243) vs238 ls243 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls317 : Lower true (vars 317) (graphGoal 317) 5 := size_of (hints:=8598358020) (by decide +kernel)
def es317 := extendKnown es243 5 [(317,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs317 : Known true es317 := extendKnown_ok (m:=317) vs243 ls317 (by decide +kernel)
def s359S := sampleAt 78 #[(0x4eb019808e8080ff980,0x46b4b9a686a6a64f9aa),(0x70c01e001300ff01fff,0x50c43e220322a344aa3),(0x83001fffe3ff0001e00,0x300aa87a387060de0a),(0x0,0x0),(0x0,0x0),(0x303ffe000fc000001fff,0x10311c00cfc14142951c),(0x3fc000000fffffffe000,0x3a8090048585858b0050),(0x0,0x0),(0x3ffffffff00000000000,0x2fcee1570006060c0060)]
def s359C : List ColumnInfo := [(1,0,358,512,7)]
def s359D7 (_ : Nat) : Nat := 0xbf
def s359L : Nat → Packing
  | 7 => (1,0,1,0,0,1,0,s359D7)
  | _ => emptyPacking
def s359I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s359 : Forest := ⟨359,7,s359S,s359C,[[]],s359L,s359I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs359_7_0 : block s359 7 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs359_7 : block s359 7 0 1 = true := bs359_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts359 : checkedTables s359 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs359_7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs359 : graphValid s359 (boundsBefore es317) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls359 : Lower true (vars 359) (graphGoal 359) 8 := lower_forest (g:=s359) (i:=0) (hints:=8590984790) (before_sound es317 vs317) gs359 ts359 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es359 := extendKnown es317 8 [(359,[]),(366,[134,81,48])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs359 : Known true es359 := extendKnown_ok (m:=359) vs317 ls359 (by decide +kernel)
def s435S := sampleAt 80 #[(0x1e2c03c3003ff3c03ff,0xa2c8941089231c9125),(0x99930030cc0300cfff00,0x999338304f83e04787e0),(0x0,0x0),(0x0,0x0),(0x1e1c003f0ffc00f003ff,0xa1c1129051444e1224a),(0xe01fffc3f00000fffc00,0x200443c3b05816b8781c),(0x0,0x0),(0xffe00003ffffff000000,0xf5402202ea6298024090),(0xfffffffc000000000000,0xdffbbc3c0380e00380e0)]
def s435C : List ColumnInfo := [(256,0,179,512,6)]
def s435D6 (_ : Nat) : Nat := 0xbf
def s435L : Nat → Packing
  | 6 => (1,0,1,0,0,1,0,s435D6)
  | _ => emptyPacking
def s435I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s435 : Forest := ⟨435,6,s435S,s435C,[[]],s435L,s435I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs435_6_0 : block s435 6 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs435_6 : block s435 6 0 1 = true := bs435_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts435 : checkedTables s435 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs435_6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs435 : graphValid s435 (boundsBefore es359) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls435 : Lower true (vars 435) (graphGoal 435) 7 := lower_forest (g:=s435) (i:=0) (hints:=21475885140) (before_sound es359 vs359) gs435 ts435 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es435 := extendKnown es359 7 [(435,[]),(437,[133,33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs435 : Known true es435 := extendKnown_ok (m:=435) vs359 ls435 (by decide +kernel)
def s461S := sampleAt 78 #[(0x8c7603001901ff9c07f,0x4368b440944a38d123),(0x0,0x0),(0x1309803fe6e0180e7f80,0x101829162e2592a4992),(0x2431ffc018ffe00f8000,0x11a1c0c8b0e06f850a),(0x0,0x0),(0x0,0x0),(0x383e00001f00000fffff,0x383c11089d088445264c),(0x3fc000001ffffff00000,0x3f801209174b15802850),(0x3fffffffe00000000000,0x3eee5c2e000c06003060)]
def s461C : List ColumnInfo := [(64,0,397,512,5),(65,0,396,512,4),(68,0,393,512,4),(128,0,333,512,5),(129,0,332,512,4),(136,0,325,512,4),(256,0,205,512,5),(260,0,201,512,4),(264,0,197,512,4)]
def s461D7 (_ : Nat) : Nat := 0x41857233f
def s461H6 (_ : Nat) : Nat := 0x33c8002479337a8a0000118000208
def s461D6 (_ : Nat) : Nat := 0x138481304a11844140501a119e325078a0a01fd32fea9ff50ffaa1fd20fea0ff443fa43fd54
def s461H5 (_ : Nat) : Nat := 0x840000001a80010c834d402
def s461D5 (_ : Nat) : Nat := 0x3347a8a09f95921be81943b78d910af91920bd85953bb89954
def s461L : Nat → Packing
  | 7 => (1,0,4,0,0,1,0,s461D7)
  | 6 => (9,1,4,0,0,7,0,s461D6)
  | 5 => (6,2,4,0,0,5,0,s461D5)
  | _ => emptyPacking
def s461I : Nat → Nat → Option (Nat × Nat)
  | 7,h => lookupWord 3 14 1 8 4 0 s461H6 (mixTag h)
  | 6,h => lookupWord 2 13 1 7 3 0 s461H5 (mixTag h)
  | _,_ => none
def s461 : Forest := ⟨461,7,s461S,s461C,[[]],s461L,s461I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs461_7_0 : block s461 7 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs461_7 : block s461 7 0 1 = true := bs461_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs461_6_0 : block s461 6 0 9 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs461_6 : block s461 6 0 9 = true := bs461_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs461_5_0 : block s461 5 0 6 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs461_5 : block s461 5 0 6 = true := bs461_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts461 : checkedTables s461 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs461_5
  · exact bs461_6
  · exact bs461_7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs461 : graphValid s461 (boundsBefore es435) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls461 : Lower true (vars 461) (graphGoal 461) 8 := lower_forest (g:=s461) (i:=0) (hints:=8589964806) (before_sound es435 vs435) gs461 ts461 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es461 := extendKnown es435 8 [(461,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs461 : Known true es461 := extendKnown_ok (m:=461) vs435 ls461 (by decide +kernel)
def s223S := sampleAt 126 #[(0x800024901fff041a4e8080fffffff,0x64904a83000a46828206aaa83),(0x13566038e019809a6c7300ff0199980,0x11566978e4d9a68a2c5326a74d999aa),(0x1c67803f001e00e38f83ff0001e1e00,0x1467897f04de26a28e83a7264de1e2a),(0x26078003fffe000fc0ffc000001fe000,0x22078036db1e00efc0ffc16162dfe01a),(0x3807fffc0000000fff000000001fffff,0x2807aa38001800cfff0001414295551c),(0x0,0x0),(0x3ff800000000000fffffffffffe00000,0x3ea8012000900485551285858b000050),(0x3ffffffffffffff00000000000000000,0x15f855c124e15700000006060c000060),(0x0,0x0)]
def s223C : List ColumnInfo := [(8,0,215,512,8)]
def s223D8 (_ : Nat) : Nat := 0x17f
def s223L : Nat → Packing
  | 8 => (1,0,1,0,0,1,0,s223D8)
  | _ => emptyPacking
def s223I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s223 : Forest := ⟨223,8,s223S,s223C,[[]],s223L,s223I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs223_8_0 : block s223 8 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs223_8 : block s223 8 0 1 = true := bs223_8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts223 : checkedTables s223 8 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs223_8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs223 : graphValid s223 (boundsBefore es461) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls223 : Lower true (vars 223) (graphGoal 223) 9 := lower_forest (g:=s223) (i:=0) (hints:=30308) (before_sound es461 vs461) gs223 ts223 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es223 := extendKnown es461 9 [(223,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs223 : Known true es223 := extendKnown_ok (m:=223) vs461 ls223 (by decide +kernel)
def s239S := sampleAt 132 #[(0x40643392403fff8e3a4e80403ff33300,0x241192419507861a46834181f3330a),(0x8980cce3803300104c73007fc03fffff,0x88044e388b322000c531148c8955523),(0x30e38f0fc003c00e38f83ff80003c3c00,0x10a38f0fc19bc66a28e83b39999bc3c6a),(0xc303f00ffffc000fc0ffc0000003fc000,0x4102d00b6c3c00efc0ffc0b0585bfc01a),(0x0,0x0),(0xfc03fff00000000fff0000000003fffff,0xfc03fbb003300ccfff0006a35352aaadc),(0xfffc00000000000ffffffffffffc00000,0xef54000002200885961284c2626000090),(0xfffffffffffffff000000000000000000,0xbefd2ee493c2af00000007038380000e0),(0x0,0x0)]
def s239C : List ColumnInfo := [(8,0,231,512,7)]
def s239D7 (_ : Nat) : Nat := 0x17f
def s239L : Nat → Packing
  | 7 => (1,0,1,0,0,1,0,s239D7)
  | _ => emptyPacking
def s239I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s239 : Forest := ⟨239,7,s239S,s239C,[[]],s239L,s239I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs239_7_0 : block s239 7 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs239_7 : block s239 7 0 1 = true := bs239_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts239 : checkedTables s239 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs239_7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs239 : graphValid s239 (boundsBefore es223) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls239 : Lower true (vars 239) (graphGoal 239) 8 := lower_forest (g:=s239) (i:=0) (hints:=1078870) (before_sound es223 vs223) gs239 ts239 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es239 := extendKnown es223 8 [(239,[]),(351,[16,135,33,84]),(431,[134,81,48]),(446,[134,64,81,67]),(508,[134,64,97,98,101,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs239 : Known true es239 := extendKnown_ok (m:=239) vs223 ls239 (by decide +kernel)
def s247S := sampleAt 148 #[(0x4040cc0003fffc6306801003ff33cc00ffff,0x440025502c21028150280b11cc125413),(0x89833330033000849b001ffc00ccffffcc00,0x8811332173218008b10d21c86445487cc8a),(0x30e33c3c003c00338e3ffe00000f0f000f000,0x10a33c3c677c67928a3b3e6799ef0f1b6f1ba),(0x0,0x0),(0xc303c03fffc0003c0fc00000000ff0000ffff,0x410140150d800d3c0fc0a815054ee0064a86c),(0xfc03ffc00000003ff0000000000ffffff0000,0xfc03eec0ce00ce3ff006b0d6358bbab780370),(0xfffc00000000003ffffffffffff0000000000,0xef5400008800882d6544c0982600002400240),(0xffffffffffffffc0000000000000000000000,0xbefebbaaf02af000000700e03800003800380),(0x0,0x0)]
def s247C : List ColumnInfo := [(0,4,179,576,7),(0,16,102,641,6),(0,32,213,514,8),(0,128,102,529,6),(1,0,246,512,6),(1,16,102,640,5),(1,128,102,528,5),(4,0,243,512,8),(16,0,231,512,7),(34,0,213,512,7),(64,4,179,512,6),(68,0,179,512,6),(128,0,119,512,7),(128,16,102,513,5),(144,0,103,512,5),(145,0,102,512,4)]
def s247D9 (_ : Nat) : Nat := 0x116e59267f
def s247H8 (_ : Nat) : Nat := 0x974091e55a9309004600740058a2470
def s247D8 (_ : Nat) : Nat := 0x3372237269d7951b0d362f9231bb9216ac971c31c77cc9ec32f2a2b4a1be64f4196ac94c5665d7918d8cf164c1f26514d599b425c2be501f4be3c11803fe30ff597fe60ff543fd60ff54ffd30ff943fd63fbd4bed20
def s247H7 (_ : Nat) : Nat := 0xcd31b6e3000455577b5872591a0c00c00000c
def s247D7 (_ : Nat) : Nat := 0xa1015880ac0d01702d6e26b717396e31176f9c885f22e72dc626f972e5029976f9c8996fcb160c695c6a1f047cba1aeba4ea30de4614803f7a9461fbd4a60fdea4b07ef524c3f6b1ea57f55e30bfaaf304fe674c2f693c617b41f52bbc6eb04fc674c2f693cc1770dd60
def s247H6 (_ : Nat) : Nat := 0x1a004901ec2d40169
def s247D6 (_ : Nat) : Nat := 0x3347a8a0cef5299d309ed78d4a60dcf528dd60cef5219d309ed78d4a30dcf520dd60
def s247L : Nat → Packing
  | 9 => (1,0,4,0,0,1,0,s247D9)
  | 8 => (11,1,4,0,0,9,0,s247D8)
  | 7 => (14,2,4,0,0,9,0,s247D7)
  | 6 => (6,3,4,0,0,5,0,s247D6)
  | _ => emptyPacking
def s247I : Nat → Nat → Option (Nat × Nat)
  | 9,h => lookupWord 4 14 3 8 4 0 s247H8 (mixTag h)
  | 8,h => lookupWord 5 16 4 8 4 0 s247H7 (mixTag h)
  | 7,h => lookupWord 2 10 1 7 3 0 s247H6 (mixTag h)
  | _,_ => none
def s247 : Forest := ⟨247,9,s247S,s247C,[[]],s247L,s247I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs247_9_0 : block s247 9 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs247_9 : block s247 9 0 1 = true := bs247_9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs247_8_0 : block s247 8 0 2 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs247_8_2 : block s247 8 2 9 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs247_8 : block s247 8 0 11 = true := (@block_merge s247 8 0 2 9 bs247_8_0 bs247_8_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs247_7_0 : block s247 7 0 7 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs247_7_7 : block s247 7 7 7 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs247_7 : block s247 7 0 14 = true := (@block_merge s247 7 0 7 7 bs247_7_0 bs247_7_7)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs247_6_0 : block s247 6 0 6 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs247_6 : block s247 6 0 6 = true := bs247_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts247 : checkedTables s247 9 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs247_6
  · exact bs247_7
  · exact bs247_8
  · exact bs247_9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs247 : graphValid s247 (boundsBefore es239) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls247 : Lower true (vars 247) (graphGoal 247) 10 := lower_forest (g:=s247) (i:=0) (hints:=1050196) (before_sound es239 vs239) gs247 ts247 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es247 := extendKnown es239 10 [(247,[]),(471,[33,133])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs247 : Known true es247 := extendKnown_ok (m:=247) vs239 ls247 (by decide +kernel)
def s251S := sampleAt 133 #[(0x40443000900ffd5b26700ff33cc03fff,0x4100990a42c090230a0b11cc49513),(0x8180cb00e00c02a4db9ff00ccffff300,0x804b45e46d18004a9474644551f34a),(0x0,0x0),(0x1326270c00fff00338e3e0000f0f003c00,0x1122250c1db1f07b38e3e2e2ef0f0dbc3a),(0x1c38380fff000003c0fc00000ff0003fff,0x1428280d16014053c0fc02424ee0092a2c),(0x1fc03ff000000003ff0000000fffffc000,0x1fc03fb098098263ff000a8a8bbaae00b0),(0x1fffc00000000003fffffffff000000000,0x1fff400090090243f6b54b0b00002800a0),(0x1ffffffffffffffc000000000000000000,0xad5d2e2e04e0b8000000c0c00003000c0),(0x0,0x0)]
def s251C : List ColumnInfo := [(32,0,219,512,8)]
def s251D8 (_ : Nat) : Nat := 0x17f
def s251L : Nat → Packing
  | 8 => (1,0,1,0,0,1,0,s251D8)
  | _ => emptyPacking
def s251I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s251 : Forest := ⟨251,8,s251S,s251C,[[]],s251L,s251I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs251_8_0 : block s251 8 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs251_8 : block s251 8 0 1 = true := bs251_8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts251 : checkedTables s251 8 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs251_8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs251 : graphValid s251 (boundsBefore es247) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls251 : Lower true (vars 251) (graphGoal 251) 9 := lower_forest (g:=s251) (i:=0) (hints:=1077332) (before_sound es247 vs247) gs251 ts251 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es251 := extendKnown es247 9 [(251,[]),(505,[130,112,129,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs251 : Known true es251 := extendKnown_ok (m:=251) vs247 ls251 (by decide +kernel)
def s254S := sampleAt 130 #[(0x0,0x0),(0x413003eb300cc00926739c03fffffff,0x110016b322cc88002318c888d55523),(0x181cb3333c00f0036db9ce7fc0333300,0x814b3333c66f19924a94a59d9b3336a),(0x26260c3c3c000ffff8e3e0f80003c3c00,0x22220c143c00e543f8e3e0f8585bc3c1a),(0x38380fc03ffff0003f03ff000003fc000,0x28280d403d50f003bf03ff00585bfc01a),(0x3fc00fffc00000003ffc00000003fffff,0x3fc00ffe800cc0333ffc00035352aaadc),(0x3ffff000000000003ffffffffffc00000,0x3f7ea000000880222db54a52626000090),(0x3fffffffffffffffc0000000000000000,0x15d5f2abc2af0abc000000038380000e0),(0x0,0x0)]
def s254C : List ColumnInfo := [(16,0,238,512,6)]
def s254D6 (_ : Nat) : Nat := 0x17f
def s254L : Nat → Packing
  | 6 => (1,0,1,0,0,1,0,s254D6)
  | _ => emptyPacking
def s254I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s254 : Forest := ⟨254,6,s254S,s254C,[[]],s254L,s254I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs254_6_0 : block s254 6 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs254_6 : block s254 6 0 1 = true := bs254_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts254 : checkedTables s254 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs254_6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs254 : graphValid s254 (boundsBefore es251) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls254 : Lower true (vars 254) (graphGoal 254) 7 := lower_forest (g:=s254) (i:=0) (hints:=823621200) (before_sound es251 vs251) gs254 ts254 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es254 := extendKnown es251 7 [(254,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs254 : Known true es254 := extendKnown_ok (m:=254) vs251 ls254 (by decide +kernel)
def s319S := sampleAt 130 #[(0xaac0000facc033003333cccc03fffff,0xaad24005acd2b34a1111cccd4955553),(0x403002ccccf003c00ccccffffff33300,0x40330eccccf31bcc6444455571f333ca),(0x28cc0030f0f0003ffff0f0f0f003c3c00,0x28cc06f050f007951ff0f0f0f0dbc3c3a),(0x30f0003f00ffffc000ff00ff0003fc000,0x30f006f500f547c01eff00ff00dbfc03a),(0x3f00003fff00000000ffff000003fffff,0x3f0024bffa00250094eeee000292aaaac),(0x3fffffc00000000000fffffffffc00000,0x39fc47000000060018bbbbaaa8e000030),(0x0,0x0),(0x0,0x0),(0x3fffffffffffffffff000000000000000,0x603b80aaf0ab82ae00000000300000c0)]
def s319C : List ColumnInfo := [(8,0,311,512,6)]
def s319D6 (_ : Nat) : Nat := 0x17f
def s319L : Nat → Packing
  | 6 => (1,0,1,0,0,1,0,s319D6)
  | _ => emptyPacking
def s319I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s319 : Forest := ⟨319,6,s319S,s319C,[[]],s319L,s319I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs319_6_0 : block s319 6 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs319_6 : block s319 6 0 1 = true := bs319_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts319 : checkedTables s319 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs319_6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs319 : graphValid s319 (boundsBefore es254) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls319 : Lower true (vars 319) (graphGoal 319) 7 := lower_forest (g:=s319) (i:=0) (hints:=8591018068) (before_sound es254 vs254) gs319 ts319 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es319 := extendKnown es254 7 [(319,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs319 : Known true es319 := extendKnown_ok (m:=319) vs254 ls319 (by decide +kernel)
def s367S := sampleAt 126 #[(0x9d5602b3019808e3a4e8080ff99980,0x8d5696b34d9a6861a46a6a64f999aa),(0xe018033c01e00104c7300ff01fffff,0xa018873c45e22000c5322a344aaaa3),(0x1066003c001fffe38f83ff0001e1e00,0x66017c00ca87a28e8387060de1e0a),(0x26078003fffe000fc0ffc000001fe000,0x22078037d51e00efc0ffc16162dfe01a),(0x0,0x0),(0x3807fffc0000000fff000000001fffff,0x2807e238001800cfff0001414295551c),(0x3ff800000000000fffffffffffe00000,0x3f50012000900485961285858b000050),(0x0,0x0),(0x3ffffffffffffff00000000000000000,0x15f81dc02ae15700000006060c000060)]
def s367C : List ColumnInfo := [(8,0,359,512,8)]
def s367D8 (_ : Nat) : Nat := 0x17f
def s367L : Nat → Packing
  | 8 => (1,0,1,0,0,1,0,s367D8)
  | _ => emptyPacking
def s367I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s367 : Forest := ⟨367,8,s367S,s367C,[[]],s367L,s367I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs367_8_0 : block s367 8 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs367_8 : block s367 8 0 1 = true := bs367_8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts367 : checkedTables s367 8 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs367_8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs367 : graphValid s367 (boundsBefore es319) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls367 : Lower true (vars 367) (graphGoal 367) 9 := lower_forest (g:=s367) (i:=0) (hints:=8591017558) (before_sound es319 vs319) gs367 ts367 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es367 := extendKnown es319 9 [(367,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs367 : Known true es367 := extendKnown_ok (m:=367) vs319 ls367 (by decide +kernel)
def s375S := sampleAt 148 #[(0x14c2b0003f30006306801003ff33cc00ffff,0x442b22417322821029152288b11cc925493),(0x6710c00333c000849b001ffc00ccffffcc00,0x2510c60f33c618008b30d61d86445587cd8a),(0x88230003c3ffff38e3ffe00000f0f000f000,0x23006d41507d28a383e0781ef0f036f03a),(0x0,0x0),(0xcf03c0003fc0003c0fc00000000ff0000ffff,0xcf03c0ccbe80cd3c0fc6a8d5354ee0364ab6c),(0xf003ffffc000003ff0000000000ffffff0000,0x5002710f00000e3ff000b016058bba8780070),(0xfffc00000000003ffffffffffff0000000000,0xfda800880000882d6544c0982600002400240),(0x0,0x0),(0xffffffffffffffc0000000000000000000000,0xaffd8ef02beaf000000700e03800003800380)]
def s375C : List ColumnInfo := [(0,16,358,513,8),(0,32,85,770,6),(0,256,83,548,6),(2,0,373,512,7),(2,32,85,768,5),(4,0,371,512,7),(4,256,83,544,5),(16,0,359,512,8),(17,0,358,512,7),(32,0,343,512,7),(34,0,341,512,5),(36,256,83,512,4),(64,0,311,512,6),(256,0,119,512,7),(256,32,85,514,5),(258,32,85,512,4),(260,0,115,512,5),(288,0,87,512,5),(290,0,85,512,4),(292,0,83,512,4)]
def s375D9 (_ : Nat) : Nat := 0x656a5067f
def s375H8 (_ : Nat) : Nat := 0x4dcd38f47e8060012b8000067ac349800204801046
def s375D8 (_ : Nat) : Nat := 0xa23346a4e80e4889d1016894c0e982d11141a1230026a23305a601ad41b40c9405a290c5b4480645064a1db489022824a80e2d068484071a832316d1a981141328874061282653a035119a3527407916227b5c463d6c4dd0237cb6204580bc00ff597fd42ffd47fd64ffd4bfd61ff487fd51ff507fd62ff54bfd54ffd53fe65
def s375H7 (_ : Nat) : Nat := 0x3d046184c0599f71c5d2800a8000f375e50d1fa1e155591a252d2a319301800a3c0073a42b2400b225be2e8055c5df859119041106e231120
def s375D7 (_ : Nat) : Nat := 0x19f0089870049045931000000011420000792168878229000861cf80580268931569b460530c34d367c0314934604b341173e0168c1251812e7c02cf8062d267c02c19c58338a348be1c842047e1e5781db759d1731c76edb66c5ac665785cd6e5894f480f1340a82546d1683909813002fea3ea57f91d52bfeae90fef5250aff2ba43fd58751bfa8ea95fe67546feaba437f89d54bfa2fa95fe27546ff0bacbfd54521bfc2ea95fd67d46fe93ea97f59d51bf8ae90dfd17996fe93ea3fb549219facfaa4fc6750ade23ac36fd1e65bd84eb2dbd47996fa0baa97d85d549fecfaa5ee275967f33a856f91d61
def s375H6 (_ : Nat) : Nat := 0x1b801242879d1ee5903ab90e1006364746b5c8b9849890
def s375D6 (_ : Nat) : Nat := 0xe0080000000000000058a73a4bc6ec96a84678c941e28280cef5219d42bb448587519f61851f529ee2859d519f90815d219ee2859f519f41851d528ff6815d219bd4815d219ec2859f518fd6815d219f61851d529f41851f52d751515d219bf4815d219ec2859d51d6d2515d21
def s375L : Nat → Packing
  | 9 => (1,0,5,0,0,1,0,s375D9)
  | 8 => (14,1,5,0,0,10,0,s375D8)
  | 7 => (34,2,5,0,0,10,0,s375D7)
  | 6 => (17,3,5,0,0,7,0,s375D6)
  | _ => emptyPacking
def s375I : Nat → Nat → Option (Nat × Nat)
  | 9,h => lookupWord 5 19 3 8 4 0 s375H8 (mixTag h)
  | 8,h => lookupWord 12 39 5 10 6 0 s375H7 (mixTag h)
  | 7,h => lookupWord 6 20 2 9 5 0 s375H6 (mixTag h)
  | _,_ => none
def s375 : Forest := ⟨375,9,s375S,s375C,[[]],s375L,s375I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs375_9_0 : block s375 9 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs375_9 : block s375 9 0 1 = true := bs375_9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs375_8_0 : block s375 8 0 14 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs375_8 : block s375 8 0 14 = true := bs375_8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs375_7_0 : block s375 7 0 12 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs375_7_12 : block s375 7 12 22 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs375_7 : block s375 7 0 34 = true := (@block_merge s375 7 0 12 22 bs375_7_0 bs375_7_12)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs375_6_0 : block s375 6 0 17 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs375_6 : block s375 6 0 17 = true := bs375_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts375 : checkedTables s375 9 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs375_6
  · exact bs375_7
  · exact bs375_8
  · exact bs375_9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs375 : graphValid s375 (boundsBefore es367) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls375 : Lower true (vars 375) (graphGoal 375) 10 := lower_forest (g:=s375) (i:=0) (hints:=8590984788) (before_sound es367 vs367) gs375 ts375 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es375 := extendKnown es367 10 [(375,[]),(487,[116]),(494,[134,81,48,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs375 : Known true es375 := extendKnown_ok (m:=375) vs367 ls375 (by decide +kernel)
def s379S := sampleAt 138 #[(0x930ac001f98015b267007fccf3007fff,0x110ac920b9928090232512c473292a53),(0x31c4300199e002a4db9ff80333fffe600,0x1144318799e318004a963b1911563e6ca),(0x0,0x0),(0x24c608c001e1ffff38e3e00003c3c007800,0x244208c036a0a87f38e3e170bbc3c1b783a),(0x38f80f0001fe0003c0fc000003fc0007fff,0x38f80f0325f40653c0fc0d2693b80d255ac),(0x3f000ffffe000003ff00000003fffff8000,0x2d0009c438000063ff000140a2eea1c0030),(0x3ffff00000000003fffffffffc000000000,0x3feea00220000443f6b54984c0000900120),(0x0,0x0),(0x3ffffffffffffffc0000000000000000000,0x12bdf63bc15f578000000e0700000e001c0)]
def s379C : List ColumnInfo := [(16,0,363,512,7)]
def s379D7 (_ : Nat) : Nat := 0x17f
def s379L : Nat → Packing
  | 7 => (1,0,1,0,0,1,0,s379D7)
  | _ => emptyPacking
def s379I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s379 : Forest := ⟨379,7,s379S,s379C,[[]],s379L,s379I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs379_7_0 : block s379 7 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs379_7 : block s379 7 0 1 = true := bs379_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts379 : checkedTables s379 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs379_7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs379 : graphValid s379 (boundsBefore es375) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls379 : Lower true (vars 379) (graphGoal 379) 8 := lower_forest (g:=s379) (i:=0) (hints:=12885983316) (before_sound es375 vs375) gs379 ts379 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es379 := extendKnown es375 8 [(379,[]),(478,[114,97,82,134,112,49]),(506,[114,113,101,135,16,100,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs379 : Known true es379 := extendKnown_ok (m:=379) vs375 ls379 (by decide +kernel)
def s381S := sampleAt 125 #[(0x8c156001d80c0133993380fffffff,0x4156880da2d10118811a246aaaa5),(0x0,0x0),(0x112998026600ffedce6dcff0199980,0x29981a260643a54a254870d9998c),(0x126631e00387ff0071f071f0001e1e00,0x122231e03a868f0771f071f162de1e1c),(0x1c783e0003f800007e007e00001fffff,0x1c783e0133f04c267e007e054a95555a),(0x1f803ffffc0000007fff8000001fe000,0x16803bfa3c000e077fff800162dfe01c),(0x1fffc000000000007fffffffffe00000,0x1fff8001200048245aa55aa58b000050),(0x0,0x0),(0x1fffffffffffffff8000000000000000,0x95dc405c15970b8000000060c000060)]
def s381C : List ColumnInfo := [(32,0,349,512,7)]
def s381D7 (_ : Nat) : Nat := 0x17f
def s381L : Nat → Packing
  | 7 => (1,0,1,0,0,1,0,s381D7)
  | _ => emptyPacking
def s381I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s381 : Forest := ⟨381,7,s381S,s381C,[[]],s381L,s381I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs381_7_0 : block s381 7 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs381_7 : block s381 7 0 1 = true := bs381_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts381 : checkedTables s381 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs381_7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs381 : graphValid s381 (boundsBefore es379) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls381 : Lower true (vars 381) (graphGoal 381) 8 := lower_forest (g:=s381) (i:=0) (hints:=8598357508) (before_sound es379 vs379) gs381 ts381 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es381 := extendKnown es379 8 [(381,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs381 : Known true es381 := extendKnown_ok (m:=381) vs379 ls381 (by decide +kernel)
def s439S := sampleAt 150 #[(0x3c2b0001f980003300007fffccf3001ffff,0x142b2120b990a0110084aa42c473224a913),(0x133310c00199e0000cccc006600333ffff9800,0x133310ce4799e726044cfa2e7d19115e8f9f4a),(0x203c230001e1ffffcf0f00078003c3c001e000,0x20142300f6a0a87fcf0f06ef837bc3c1ede0fa),(0x0,0x0),(0x3c03c0001fe0000f00ffff80003fc0001ffff,0x1403c0425f40214500550b00853b80449522c),(0x3c003ffffe000000fff000000003fffffe0000,0x24002710b8000058fbb004c00262eea17000b0),(0x0,0x0),(0x3fffc00000000000fffffffffffc0000000000,0x3ebe8008c0000460aeeaa705538000098004c0),(0x3fffffffffffffff0000000000000000000000,0x1bebd8ef015f5780000038001c00000e000700)]
def s439C : List ColumnInfo := [(0,16,294,641,6),(0,128,294,529,6),(16,0,423,512,6),(34,0,405,512,6),(128,0,311,512,6),(260,0,179,512,6)]
def s439D8 (_ : Nat) : Nat := 0x8d5267f
def s439L : Nat → Packing
  | 8 => (1,0,3,0,0,1,0,s439D8)
  | _ => emptyPacking
def s439I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s439 : Forest := ⟨439,8,s439S,s439C,[[]],s439L,s439I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs439_8_0 : block s439 8 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs439_8 : block s439 8 0 1 = true := bs439_8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts439 : checkedTables s439 8 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs439_8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs439 : graphValid s439 (boundsBefore es381) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls439 : Lower true (vars 439) (graphGoal 439) 9 := lower_forest (g:=s439) (i:=0) (hints:=8590985300) (before_sound es381 vs381) gs439 ts439 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es439 := extendKnown es381 9 [(439,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs439 : Known true es439 := extendKnown_ok (m:=439) vs381 ls439 (by decide +kernel)
def s443S := sampleAt 147 #[(0x3c2b0003f3000430002400fff33cc00ffff,0x142b22417322841022648a48b11cc925493),(0x4cb10c00333c0000cb003800c00ccffffcc00,0x4cb10ce0f33ce1804be17b86f86445787cf8a),(0x0,0x0),(0xc230003c3fffe70c003fff000f0f000f000,0x23006d41507e50c076c1f01ef0f036f03a),(0xf03c0003fc000380fffc000000ff0000ffff,0x503c044be8045280d458114114ee0124a92c),(0x7003ffffc000003ff0000000000ffffff0000,0x1002710f00000e3fb0160058058bba8780070),(0x0,0x0),(0x7ffc00000000003ffffffffffff0000000000,0x7ae8008800008812e2981260a600002400240),(0x7fffffffffffffc0000000000000000000000,0x6ffd8ef02beaf00000e003803800003800380)]
def s443C : List ColumnInfo := [(0,1,298,656,6),(0,2,409,544,8),(0,16,298,641,6),(1,0,442,512,7),(2,0,441,512,8),(2,256,145,552,6),(8,0,435,512,7),(16,0,427,512,7),(16,1,298,640,5),(17,0,426,512,5),(34,0,409,512,7),(128,1,298,528,5),(128,16,298,513,5),(145,0,298,512,4),(256,0,187,512,7),(264,0,179,512,6)]
def s443D9 (_ : Nat) : Nat := 0x1f4ea6267f
def s443H8 (_ : Nat) : Nat := 0xd79e4e61855ac00850c
def s443D8 (_ : Nat) : Nat := 0xd21eb2500d88cb43b1312a34f9b0ab3eadeac4f411db128edaf32b13ad8fd126b7eaec3411ccc855208c83c11803fd20ff543fd30ff4cbff53ff54fff50ffd4bfd52
def s443H7 (_ : Nat) : Nat := 0x170825420001b01a86
def s443D7 (_ : Nat) : Nat := 0xc74163a0b4c674c22e91e2b805dba2bc64602fe93ea77f49f50bf40ea9dde37542fc03aa7770dd50
def s443L : Nat → Packing
  | 9 => (1,0,4,0,0,1,0,s443D9)
  | 8 => (9,1,4,0,0,9,0,s443D8)
  | 7 => (6,2,4,0,0,7,0,s443D7)
  | _ => emptyPacking
def s443I : Nat → Nat → Option (Nat × Nat)
  | 9,h => lookupWord 3 12 2 8 4 0 s443H8 (mixTag h)
  | 8,h => lookupWord 2 9 3 7 3 0 s443H7 (mixTag h)
  | _,_ => none
def s443 : Forest := ⟨443,9,s443S,s443C,[[]],s443L,s443I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs443_9_0 : block s443 9 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs443_9 : block s443 9 0 1 = true := bs443_9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs443_8_0 : block s443 8 0 9 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs443_8 : block s443 8 0 9 = true := bs443_8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs443_7_0 : block s443 7 0 4 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs443_7_4 : block s443 7 4 2 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs443_7 : block s443 7 0 6 = true := (@block_merge s443 7 0 4 2 bs443_7_0 bs443_7_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts443 : checkedTables s443 9 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs443_7
  · exact bs443_8
  · exact bs443_9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs443 : graphValid s443 (boundsBefore es439) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls443 : Lower true (vars 443) (graphGoal 443) 10 := lower_forest (g:=s443) (i:=0) (hints:=12885979220) (before_sound es439 vs439) gs443 ts443 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es443 := extendKnown es439 10 [(443,[]),(499,[116,64,99,129]),(501,[116,64,99,130,133,81])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs443 : Known true es443 := extendKnown_ok (m:=443) vs439 ls443 (by decide +kernel)
def s445S := sampleAt 132 #[(0xc156000ec0300024f000900ffffffff,0x41564406c8b22024502292248d55525),(0x0,0x0),(0x8329980133003ffb38cb00e00c0333300,0x8129981d130390fb38cb16e16c5b3331c),(0x431e001c3ffc00c3f0c00fff003c3c00,0x31e00d4341c06c2d0c06b0701bc3c0c),(0x183e0001fc00000fc00fff000003fffff,0x83e0089f811044d400d45044112aaa4a),(0xe03ffffe0000000ffff000000003fc000,0xa03bfa1e000380effff01601605bfc01c),(0x0,0x0),(0xffc000000000000ffffffffffffc00000,0xf78001100022088292a298498a6000090),(0xfffffffffffffff000000000000000000,0x5ec405e0acbc2f000000e00e0380000e0)]
def s445C : List ColumnInfo := [(32,0,413,512,8)]
def s445D8 (_ : Nat) : Nat := 0x17f
def s445L : Nat → Packing
  | 8 => (1,0,1,0,0,1,0,s445D8)
  | _ => emptyPacking
def s445I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s445 : Forest := ⟨445,8,s445S,s445C,[[]],s445L,s445I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs445_8_0 : block s445 8 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs445_8 : block s445 8 0 1 = true := bs445_8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts445 : checkedTables s445 8 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs445_8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs445 : graphValid s445 (boundsBefore es443) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls445 : Lower true (vars 445) (graphGoal 445) 9 := lower_forest (g:=s445) (i:=0) (hints:=8598353924) (before_sound es443 vs443) gs445 ts445 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es445 := extendKnown es443 9 [(445,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs445 : Known true es445 := extendKnown_ok (m:=445) vs443 ls445 (by decide +kernel)
def s463S := sampleAt 133 #[(0x103c4eb300cc00064900fffe93a0100ff,0x1446b322cc88024922548e91a452223),(0x6b30733c00f0009b8e00cc031cc01ff00,0x2b30533c6af1a88b8e72cdcb14ce57372),(0x83c083c000fffce3f000f003e0ffe0000,0x14003c00a542ca3f012f04ba0e261212),(0x10c0303ffff000303ffff0003ff0000000,0x103d507001902db07001bff0140a0a),(0x0,0x0),(0x0,0x0),(0x1f003fc00000003fc00000003fffffffff,0x1d003a80084021354008402104a1188c8c),(0x1fffc0000000003fffffffffc000000000,0x1ffe80000c80322fd24d8ab60001a0d0d0),(0x1fffffffffffffc0000000000000000000,0x1febefc2af0abc00000e00380001c0e0e0)]
def s463C : List ColumnInfo := [(2,0,461,512,8)]
def s463D8 (_ : Nat) : Nat := 0x17f
def s463L : Nat → Packing
  | 8 => (1,0,1,0,0,1,0,s463D8)
  | _ => emptyPacking
def s463I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s463 : Forest := ⟨463,8,s463S,s463C,[[]],s463L,s463I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs463_8_0 : block s463 8 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs463_8 : block s463 8 0 1 = true := bs463_8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts463 : checkedTables s463 8 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs463_8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs463 : graphValid s463 (boundsBefore es445) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls463 : Lower true (vars 463) (graphGoal 463) 9 := lower_forest (g:=s463) (i:=0) (hints:=8589964902) (before_sound es445 vs445) gs463 ts463 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es463 := extendKnown es445 9 [(463,[]),(493,[84,32,134,118,48,81])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs463 : Known true es463 := extendKnown_ok (m:=463) vs445 ls463 (by decide +kernel)
def s475S := sampleAt 148 #[(0x40f0930fcc00010002400fff267003ffffff,0x501105cc22000086422423023088235423),(0x1b2c31cccf00006b003800c00db9ffc00cc00,0xb2c114ccf16602b597966d664a959d66cd6a),(0x0,0x0),(0x2030c60f0ffff98c003fff000e3e00000f000,0x42050540f88c036c0f00ee3e05816f01a),(0xc3c0f80ff0000e0fffc000000fc000000ffff,0x4140f80fa00cca0d3380cc0ccfc0350d4a8dc),(0x0,0x0),(0xfc00fff000000ff0000000000ffffffff0000,0xf400eea000288fd0a20288288b54a62980290),(0xffff000000000ffffffffffff000000000000,0xbeba000000300572c41310b10000c03000300),(0xfffffffffffff000000000000000000000000,0xffffbdfafabf0000f803e03e0000f83e003e0)]
def s475C : List ColumnInfo := [(0,2,409,576,8),(0,256,211,520,8),(1,0,474,512,6),(2,0,473,512,8),(16,0,459,512,7),(66,0,409,512,7),(128,0,347,512,6),(256,0,219,512,8),(264,0,211,512,7)]
def s475D9 (_ : Nat) : Nat := 0xa902057f
def s475H8 (_ : Nat) : Nat := 0x68005805900011eff9ab68000024
def s475D8 (_ : Nat) : Nat := 0xc4044ac4d8808d5a44f881ab4144e2a60d1ac0f5c089181ab8312303570624606ad30688a0784b8572913712c5000ff8c3fe50ff143fd50ff4c3ff53ff54fff50
def s475H7 (_ : Nat) : Nat := 0x89d560617c0060c007498a711203235b7065a138c2686cc35c00a5bd0d47de6019c74d0d617c7d66ddd3d4b00398f500020409300e003ac0
def s475D7 (_ : Nat) : Nat := 0x14184a042905be210e40a810031082408060e01cf016780c30000006bc61262506bc61262506f88860e386e3059982c70cf72e39e1b906cf0c772f19e0a625c31cc21b73639e1b922b8820f7e1ed789dd761cd721bd6e1ad689915e9755c16b599614f93945911400f5330a9230691181d003bf1aaa1df4d550ff2a1185ff578c3fd28261df4d750fbea7187de37542ff2ba617f4de50ff2a0985fe37542feabca17f81d53bfe0ea9dff07d4feea9a617f4df50bfaae985fd578c2fe83ea77f01d53fb86ea85fc574c2fe9b8a17fd5d30ef2a02877b50942dea38a1778dd50bda4e285dc37542ee9b8a177cdc50
def s475H6 (_ : Nat) : Nat := 0x3b113eb0015021cf50435e6ea00187cf055900145c398c1a5000477900000711c030
def s475D6 (_ : Nat) : Nat := 0x12040000000e210700812040088100000878276716c67625d584c473b362a2520140f0a0500f5a3854050f5a3554230f593554130f583854050d7a7854050b78084d550d790515d30d79504dc509de3855d309ed2815d30d5e3555e309bd4801d53bd908d4e30d5d3515d309ed2801d539bd4815d30bd80854d309dc3855e509dd3815d3097a7854050d59504dc50
def s475H5 (_ : Nat) : Nat := 0x380000880800052b2b9a06
def s475D5 (_ : Nat) : Nat := 0xf668f514195889541371432b512a826e286560e67854050cad1ccf0a80a195a389e1501432b20a9c0ae986560e27854050
def s475L : Nat → Packing
  | 9 => (1,0,4,0,0,1,0,s475D9)
  | 8 => (8,1,4,0,0,9,0,s475D8)
  | 7 => (34,2,4,0,0,10,0,s475D7)
  | 6 => (21,3,4,0,0,8,0,s475D6)
  | 5 => (7,4,4,0,0,5,0,s475D5)
  | _ => emptyPacking
def s475I : Nat → Nat → Option (Nat × Nat)
  | 9,h => lookupWord 3 16 2 7 3 0 s475H8 (mixTag h)
  | 8,h => lookupWord 12 39 5 10 6 0 s475H7 (mixTag h)
  | 7,h => lookupWord 7 27 4 9 5 0 s475H6 (mixTag h)
  | 6,h => lookupWord 3 11 3 7 3 0 s475H5 (mixTag h)
  | _,_ => none
def s475 : Forest := ⟨475,9,s475S,s475C,[[]],s475L,s475I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs475_9_0 : block s475 9 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs475_9 : block s475 9 0 1 = true := bs475_9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs475_8_0 : block s475 8 0 8 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs475_8 : block s475 8 0 8 = true := bs475_8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs475_7_0 : block s475 7 0 8 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs475_7_8 : block s475 7 8 26 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs475_7 : block s475 7 0 34 = true := (@block_merge s475 7 0 8 26 bs475_7_0 bs475_7_8)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs475_6_0 : block s475 6 0 2 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs475_6_2 : block s475 6 2 19 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs475_6 : block s475 6 0 21 = true := (@block_merge s475 6 0 2 19 bs475_6_0 bs475_6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs475_5_0 : block s475 5 0 7 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs475_5 : block s475 5 0 7 = true := bs475_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts475 : checkedTables s475 9 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs475_5
  · exact bs475_6
  · exact bs475_7
  · exact bs475_8
  · exact bs475_9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs475 : graphValid s475 (boundsBefore es463) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls475 : Lower true (vars 475) (graphGoal 475) 10 := lower_forest (g:=s475) (i:=0) (hints:=12884930660) (before_sound es463 vs463) gs475 ts475 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es475 := extendKnown es463 10 [(475,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs475 : Known true es475 := extendKnown_ok (m:=475) vs463 ls475 (by decide +kernel)
def s477S := sampleAt 142 #[(0x20c460ec0180004001200ffe4ce00ffffff,0x40206c85908000832424860464221aa43),(0x0,0x0),(0x4308933001ffc1ac01c00c01b73ff006600,0x10011302c85c0ac4bc26c4c9522713662a),(0x84331c3ffe00263001fff001c7c00007800,0x1114341e03a2301b60f01dc7c160b781a),(0x3183c1fc00000383ffe000001f8000007fff,0x1083c1f81182328351c08c119f80944a549c),(0x0,0x0),(0x3e03fe00000003fc000000001fffffff8000,0x3e03fc00310623f43101883116a998cc0190),(0x3ffc0000000003ffffffffffe00000000000,0x2f7800002204415ca60930a6000120900120),(0x3ffffffffffffc0000000000000000000000,0x3feeeeacbc1780003801c0380001c0e001c0)]
def s477C : List ColumnInfo := [(0,4,153,832,7),(0,8,85,896,6),(0,16,332,641,6),(0,64,408,517,6),(0,256,209,524,7),(1,0,476,512,7),(1,16,332,640,5),(1,64,408,516,5),(4,0,473,512,8),(5,64,408,512,4),(8,0,469,512,8),(8,4,145,832,6),(8,256,209,516,6),(12,256,209,512,5),(16,0,461,512,8),(17,0,460,512,5),(20,0,457,512,5),(24,0,453,512,5),(64,0,413,512,8),(64,4,153,768,6),(64,256,145,524,6),(65,0,412,512,5),(68,0,409,512,7),(69,0,408,512,4),(72,0,405,512,6),(72,4,145,768,5),(72,256,145,516,5),(80,0,397,512,5),(81,0,396,512,4),(128,0,349,512,7),(128,8,85,768,5),(128,16,332,513,5),(129,16,332,512,4),(136,0,341,512,5),(144,0,333,512,5),(145,0,332,512,4),(152,0,325,512,4),(256,0,221,512,8),(256,4,153,576,6),(260,0,217,512,6),(264,0,213,512,7),(268,0,209,512,5),(272,0,205,512,5),(320,4,153,512,5),(324,0,153,512,5),(384,8,85,512,4),(392,0,85,512,4)]
def s477D10 (_ : Nat) : Nat := 0x1d42c37f
def s477H9 (_ : Nat) : Nat := 0x35ce0037dba1457c8810c90044801d17200000bccc08edbfb0bca8f200eb2ac01263f2560b01007ce612c0009c006020010359793
def s477D9 (_ : Nat) : Nat := 0x2c627283c1cd5828ed01cf98b0459383a83682c1ce949c69c2cb1d4c7cd5a7053ba038638b2c990134569c7429f3c1d121305505271b41606167143879c2cb050c98d5a70b0aa0f182ced15901d3682c6c71440604174561c8ce1eb1116a100e3683a187563c6d05a705288c31e42650510174169c74a1f3c70476b24d08c71c59d9c98b1744e0a76b1f3c7ad3859d3ea119c5969c15316b013b385a45079c00b295078c127284e58b2131d505271ab4e16154070c7909a7283a50f9e4269ca03140a7bd36eac5d5ca5b3de6b4998d50d202bd674ede1a13135c8ab9432504347c8de1862bc4a07c8d11441b01b000ff50bfe30ff593fd54ffd47fe50ff4c7fc50ff583fd40ff843fd20ff543fd43ff4c3fd32ffd4ffe40ff58fff54ff54ffd51ffd43ff52ff443fd52ff487fd61ff597fe20ff997fe60
def s477H8 (_ : Nat) : Nat := 0x168cb3d81cb4afb1125c0301c79815233544352f2f8d1b137f16a66444f5ab68fb6f19702a9099e47e08592fdc03a0875f2347168052f2f9a888b5414a4a11e9a26887939ac0719aaae77131240672a605081b5838ada84683a6e040b000000011a5e61c6c69708ace9d578104000080301ef372ce20b9c1a1212625a50d8671665156c585963938a3cc2d828000c6fb07212b12d40c0b7f4342aadd1f00659f3fd41b435d4c697bc630ea658ca3e9aca7fa2c38bc9dded437618b7812e3f17bc42118fc4578508838c0cd360ca04705ca22f42dbdb0cbc4c15ec8b2209ad9b238800000a81c60c19d536915750437a0a600077e4c3c0012e6000000299d4c8352800216d44167cf31b9c286be55811bd9309f2541b9f4f86ef86ed95151109648a1098856cfae0389a94b7ccad44c015917e6ea06210b53910e61811390462d7c0f99db85200e24931a514ec9393620c9586b16d108a8f5e4cac52aa87647df09127b2f10e9677e0780001768eba2040799e800001c0002cea0000000003d98280000690c000000731f38c036303426800211da0b15780019e72288050003932a9ae09ba0f02407837de2ea888816076b12ad2a000000289d49126f90d218ac72a0400002471a000003432a40006d5c1ddbf400000071500024f22c4c2ec892405070e6d9c3542ff060006a4000000091d63d61fdecb3410000000ce550c00b6904120014d050c100040ea448006681830600080009818004ac3021a40501347c40206403b6260c30e0e0010012619010249582005800208016800f04005020000b00e00130a3c893226018358b8483
def s477D8 (i : Nat) : Nat := #[0x60a70232072015e041007a0007fe37553fea12a1ff59150ffaa8907fd424c3fea2aa1ff8dd20ffac8987fd60543feaa261ff50120ffaa0a07fd64d4ffea9a85ff55132ffac0987fd6454ffea8c61ff51553ffaa0907ff53583feb26a1ff4c940ffa2b287ff53503fea9461ff50d20ffaa6b07fd30483fea2aa5ff58350ffc4eaa7fd53503fe92ca1ffd4140ffea4a07fd52503fea9a41ff45d50ffa2aa87fd218c3fe93aa1ff48650ffaa0887fd514c3fe92aa1ff58630ffa86a97fd30443fea9261ff58650ffa6aa8fff53443ff23a41ff59630ffac2287fd52903fe90aa1ff59650ffaa6887ff50443fe90a61ff51d50ffac2a87fd67543fea9a43ff59550ffac2987ff53587feb2a61ff54d61ffac3a87fd6554fbea2aa1ef55142f7ac8aa77d45d43deaa281df8d550fda849077e45543deb2287df4d550f7aa8a1ff9508c3fd28241ef59240bfa6fa95fd27d4efeabc417f55d32bfc4ea87bd34502fe83ea57f4de60bfeaf185ff574cafeabc217fd5d20bfc8ea9ffa504c2fe8bc617f59f53bfc0e98dfe074cafe2ba657f51d32bface985fe47542fe2ba637f8dd54bfa8fa85fc074c7be9aea17f41f54ff2a0905fd5750eff1ba417f15d10bfacf187dd238c2ff33a61f7d4e30bfc8ea95fc57582ff83aa9f78dd50bfe0f32dfe5758eff2ba617f95d40bfe0e995fe07552fe9bea97f4de50ff2a0985fd37482ff83ea97f59c50bfc2ea9dfd27942ff13a817fc1d52bfc6ea85fc0750efe03aa97fd5d43bfa8e287ed32482fea3a417f01d63bf8aeb1dfe6754efeabca17f95d10bfc0ea9dfe574caff03aa37fc1d53bfa2e985fd27143eea1a617f95d43bf80ea97ed52482feabc817f45f53bfeaf305fe0758feea1a65f7d4d43bfe0fa9dfe274c2fe9bccb7fd5d40bfa2ea85fd67d42fe03acb7f45e50bfc6eb2dfc57503eea9a617f55d42bf8ae905fd37d42fe03aa37f51f53bfc0ea95fd57483f6a92657f8dd40bfa2e285fd37843eea9a657f95d60fda24905fe174c2ff13aa97f49f54bfacea9dff57842fe83ea37f41e65bfeaf105fe57482ff83a877f51f52bfc6ea8dfd27d42ff1baa5fb4c921bfeaea15fe47482ff13a877f59e50bfa2ea9ff950882feaba617f55e30bfc0ea1dfd278c2fe83ea77f15d43bfa6fa8dff0750afe93c817fd5e40fdea490dfc0754efeaba81f70dd50bfc8e985fe07596ff13aa77f85d50bf8ae985fd17d42ff83ea57f8dd10bfaaf305fe574c6fea3c617f01d32bfc8e995fd474c2feb3aa17f4de40bfa6e285ff574c2fea3ca17f8dd60bfa6f105ff07d46fea3c417f99d50ef2a02877b509427fb3ea33f59c509fcce90dbd47142dfa38a16f91d10b7a8fa8dde375427fb38a17b49c50bda4f305f6175927eb3ea37dc5e60bea2e285f517982f7938a17dc5c50bdc4eb2ddc37542ee9b8a177cdc50,0x39478f1790480351a4621c81ecea88bd22041200c7140f9658832b965138d9c96ccac3e50f0614503120f129b22a0508338c528050ac3c54b5666232038f4b346714788440c54cd90a8d060b0506ce269630ee705934b0f9b20769853387ea0e0b1790ba0d9d51a40e98bc81ecea8d2203cb470fa2e572ca01a08d5aa07c8404d2c1641e211106454276945993a007a58a0a4c0f50492c45607cea81e28e0fb44b132199501b39a0c0c3eccac965a8230718f918b207e3b4b2b941ce0e363e3074bc8d2681f053e56403690f47729e388e5b965090c3e442961ea81c24b0311b4101659773b2b9650190512d0052ba58ec824e51c2838aca654b72906723208f974b28aad95caa8460e6a6c814ce202e36411e934258f19992d588c99049ca391c51f4bce66562a2c5e40e8fe75469202e58988080b4d9029519c0c7001f101c7038a8e3a2f2072a090c0cad504841f1c1173364342a10671e58183c63e440a306c8d224e52838a8a9b22a08050a0c4620b1d1fce26963038a8b21988d51a0bd1ac3e3c0e463a7e8d6ce1d07051f1e467340ecb0f9474156b587f3934f9c4d2d143c5e807c8151d051fce1e4f402ab0ee70f9b384c9a142ca279c4c3a3e166d6e8231eb67340f8e829b587b3884741c17947d3919d4c180c280a726cea89207293670ecb0f859b3816a15818a3a0b9cd7d0b23e7cea82606140536b0e82b4670f9ba3381475587cd914c199d3a2864ee824d61c2f46b110f8e83828f23a35814741d3878f6a35a4367e59cf665595b64c58f762f5883612580f5f1578b5d457075af567358e55ff56d556b54c54e752b547350e53ff4f1538b4d053174b752a349a522f48151cb460514743f50b341a502f3fd4fbb3dc4f373bb4eb339e4e2f3794dbb35c4d173374c933164c0f2f54b8b2d04b072af4a8329249ff26d496b24848e7227485320247af1d9471b1b0467718f45d3166453f139449b11044070f343430c642af099420b078417703b40830063fbefe13f4afc43ed6fa73e12f723d5ef3d3caaf143bc6edf3b42eae3a6ee7d399ae5438f6e2f3862e0e37fede9373adb83666d8b35f2d5a350ed25346ad103406ce332f2ca2323ec6d317ac4830b6c0b2fc2bda2edeba12e2ab742d76b472c92b0e2bfeaf12b6aac42ab6aa32a42a82299ea5528faa2c28369ff27b29de270e9ad268a98c25c6957250292a244e8fd23ca8dc23068b7229288621ae84920ca81820067f71f927ca1ece7a11e2a7801d9674b1cc27121bae6cd1aaa6981a1667b198264618ce61d182a5f017665cb17025a2164e575155a53c14c651f14324ea134e4bd126a48411a644f10d2422102e3f50f4a3c00e863930e1236a0d5e34d0cba3200c462fb0bc22da0b3e2b50aaa29409d625308f221e081e1e1071a1b0065618705b2146049e11103da0e0030,0x34e1290f03ac11581db11080e3c252075818e91a90c05384ac0ed832305651838f918c1c5548724380e3566c448e20f4c490e387c9060d1c88ca456448e6c2240fc72010887e386460b143064ea584203ab36221138187070a803a904064e1c1c70f920d48187060c9c463060f4e1908f450e75101594806942064e231a5108f0e48541c69524ba3924a10f03120d58808c5c8463a9036869408e20f10119091a1a500789002f2c31f8e231a50f120d9e39951083e9c4839606804e212118f8d9d9510701103e9c4064e8096200a909a07e39108ce8088acd05924a851b420348f11a0b91060c9c472c48017961b4204734901c808c548ca88ce32023682e2548f540cb9a1106ca88cf1c4a7a54e8420fb411c7113a129e948ceca88344681f8e210038eab12a01c6058858882cd00e51d1f07562100a038b103c18753878aac30503c423561e1c716220b34039938188c60f1c283e2c51f8e2205072d402830f1110b21459a0b503e4431e218e182c5e40367546903a0189043d90d097a446620164e142644591d469143c1840ba59049ca0e6c8068e5dd28ba80140285934b67031a2f208ea34804c47caa848ac5051f0f1a02b0b8d10b9a0600200c3a806241c711e445e9540f8f201aa07d5885590a83ed0cc607ca56e5542331185934b108396532a58aac0e3d94a9ca3f9c80b96262322711030f2a58765397387c791503c0a4048e07961f94e5ca3c5e469541014982e588c9903ecca8d051f85681b3643411aa1576144ad50483c8a614a8232cb11e572ca019b2b974b208cb914c3b50299c3e7041f2a1e5078f8c0e5a50572b9738811179150383e59607ca94e520ce38f91883c7c4463f1c3d2c88b06a84e1e3cb228e8f6572ca670fa72199507f39a0c4696ccac4c81ece4b6807d20644b0e340e2f22a3488cb903e9da595ca6968e23cae594070644b6572ca0391981f96509258aac3d94a9ca0e3f9c84e0b1e062828c540f672b16a29b208c50a474d90295056623c8546828ee511e40f72e903a0802f38985ca0c45a4311061e185934b1067172b207c7394a20ac96cc3e5211e1290f838e12586c8071790488b51a460b20281e24b11e572ca1419992d5894d900b50299c0c704062a183540fab1258197463b95903dca3864bc81c682328f910a5b96508f28a2e96419cccac666c868541fce354640a531197392d995818a419029514c596cae5942328111881e5aa06338b179151a43c466221f11305cb1190741b29595][i]?.getD 0
def s477H7 (_ : Nat) : Nat := 0x4260a6e5f520065fbb55cdc27340bbb7f95bb2e005a30f00d90b75f21c8a15f28a7a0001cec8f9d1d8c628a2691d5b782888e000140b47b5fd53000020d4001e9a52570fe54382862a212f98a80cb98e9389dad1bc09a03d60981cd2a928a4eba7757270aac28e718612c849d7408e4ff220e580007912174000000993800105664d25c523e0de47908a04aa0dac8ed9b486448908dd534af7de546b19cbba013cb00f5a59fc00130958183bf0ce000b4a6ae4cb200004c79d0078040b382490001e10000716ed83cee000247745f6a5a0093980012af5189b240004395249c5f60e000c6400025fb64310d20b6c52ca9e998000000000f5271aae536d3d247b30001e8b207318e25e645c32da1a8714ff000136be1941d82e00005a8466589bc3e57600000000dedc3ae364b5188915669b130a3118c81ff991b58a0400032f42eba57480a705b78000a16801ec5b2686d2e8a8003a74e7d618393dd94cddd591897512e9d93dabe312410185e13c25ed10dd10a8f7db8b06a363bc65a3ab0e0682a1dcfaf5063ea5f25b65a619cbcda4a8464038b35c36e8213d202443df35484624f8a1eb311a52b000023a89c7c6800071ff625338001ae2b51f395c400000003adfd39832b0a935de0a642e3f00035d5a61f02c48f0c9f12f604264883468e08c89c90b8a0b0231495d82fc3439a0f2418e9000529c19fc0298e0a54d084d081212d7a1cb10a93008d5f687c309417dcf0ad9c5719801576aa18cb86246c000129fa420b02568165c45844000d6df36185ce57d1f5b2c66fab107b84080468d0e28387000030212a008b2c304031e1c185a6280020a20280004828a160158d1244a80140408204786a0140408b0a30780040440124087023e20f112a001810028f0b0128b8204082010c65680384008134a800f1a40112
def s477D7 (i : Nat) : Nat := #[0xd188dd50bf618593539fe0851f52ded72485309fd1855e509fd2815d409fe0851f539fd288dd409fd28c1d539fd1801d53bee2859630dbd6151c50ddd488dd50bf618591539fd28d5d40ddd420dd509fd5891d20bf61859350bee28596509fe5859d50bfa0850d209fd188dd509fd28c1d439fe484dd20df95049e309fd48c1f52ddd218dd50ddd640dd509fe4855d209fd5889d409fd7854940ddd450dd509fd1855e309fd1815d309fe3851d20fd838541209fd488dd509ff5889d409fd2801d439ff78d4940ddd600dd50bee484c9209fd78d4d40ddd478dd50ddd618dd509fd5849e40bee28595509fe7854a409fe2855d43ddd678dd509fd68d5d309ff0891d529fd4815d209fd2895d409fd6801d539fd4815d32ded6149c509fd3889d54ddd658dd509fd18c1d53bee28595309ff78d4d10bdc38541209fd4889d509ff78d4d60d7d6515d309fd2801d549fd0889d549fe2881d549fd6855e509fc78549409fe0845f53ded5249e309fe784c940ded5249e40bf80854d10bee2859553ddd2351e30ddf5351e309fe78546309fd5849e309fd4889d53ddc3745d50ddd150dd50ded1249e30ddc3749d50bdc3854110ddd210dd50ddd470dd50ddd610dd50ddd614dc50ddd670dd50ddd61cdc50ddd650dd50f5a3854050f5a3554230b78085155097f5801d43d6d2515d328fd6815d30d5d3515d32bda0848e3097c584dd208fd6815d43bb8084d140bb808551409bf4815d208ff6801d438ff6801d538ff6801d54f5935541308fd6815d409be4845d30d790515d2097e584dd209bf4815d309bd4815d60d5e3595d439ee2859d53f5838540509ed2899d308ff6815d408ff6815d309f71801d528fd6815d329f71801d53d7a78540509be4845d509f80855d439bd4815d409bd4885d5397d5801d439de3855d40d6d2515d20b78084d5509be4845e50d790515d30bd80850d309de3855d209bf4815d32d79504dc508ff6815d439df3801d549de3855d309ef2801d439ed2815d308fd6815d209df3815d209fb0815d329de3845d50d5e3555e309ed2815d208fd6801d549dc3841f529fa0855d439f51801d529ef2815d309de3841f528fd6801d539ee2859d509bd4801d539dc3855e40bd908d4e309dc3855d409ef2801d549dc3855d209f71815d309bd4815d63d5d3515d309f51801d539dc3859d509f51815d209f51801d329f51801d438fd6801d439be4845e309de3859d509ed2801d539ef2801d539f51801d549bd4815d309bd4815d209bd4815d329f51815d309f71801d329ed2801d439bf4801d539f71815d209ee2859f509dd3801d549f90815d329ee2859f539ed2801d319f51815d32bd80854d309f71815d329ed2801d549ed2801d519de3855e409dd3815d209dc3855e509dc3845d509dd3815d3097a7854050d59504dc50,0xbdc1e8ef4279ebcbde54f1c7873c25e08eff77d3bb1dceed976a3b3dd94ebc7573a81d12e7b736b959c90e3a71ab8c1c44e147033805be6dee6f03749b9adc86dd36d5b4ed996c5b5f5accd586a9b539a80d3268db4599fecf1671b3559a0cc265eb2bd954ca5650326d91ac88641b1f98e0c6b625b0f5870c21609b0157eebe05e92f35790bba5daae9d744b945c32e056d4b4159e2cdd664b2d5942c69618afe57cabd15deaea56e2b39592abb556aaa1546a955482a094e8a6f53529954aea3751928b543ea11501a7f93f29f44f7a7853a69ce4dba6a534899f4c8a60d2ea9704b5a5992c29534a7250126492d494246922a91048123f51f08f346523151808b2452225911087a43aa1c10d685d42c212908a82e414a06d01a8084019fd4fce7d93e59ef4f4c7863c09d84eb87333899ba8db86bc3529a80d2468d33f997cca264c316189cc3260b2f11774b9e5ca2e296dcb645a42cb1548a9a52428b14449be4da261928c93c47e22a914088442b213108483840e1f70f807b63d61e88f0c76a3b01d10e7471e38a1b50d4c69c32e1900c486082ff1788bb05bc2be15c8aac54c29814509f04ee272132095849023a10d080c3d81e70e8072c37a1b80cc05982c21530a2849422e0f7074832415209b04681d8076000d7d4515d32f794554120f5d458dd50f794554130d7d4595d32f791854050dbd648dd54dbd7459153afe6848630bdd28d4e30f793554120afe6848650dbd5489d40ddd288dd50ddd428dd50dbd6495d43afe6848550dbd6455e40f796154050b7d488d550f9d64d4d43b7e5859d509fd48d5d32ddd648dd509fe7859630f7968540509fd48d5d309fd68c1f53bbe4845d509fe5859e30ddd458dd509fe7850d529fd4801d52bdd28d4d439fd48d5d209fd0891d329fd288dd509fd48c1d52fda3854120bee4854920afe68485309fd4881d52bfa0845650bfa0851d50f5d450dd50dbd6451f53dbd5091d10d7d0595d20bf80850d20ddd608dd50ddd688dd509fd3891d209fd6815d309fc7855120bde38541409fd18c1f539fd18d5e30f7961d42509fe3855d42cfd5399d21dbd3091d109fe78549409fd0891d52bbd48d4d409ff7854940dbf5391d109fd688dd50bde3854120b7e5858350bfa0845d50d7d6595d30dbd5391d10dbd5489d43bed38d4921dbf5091d109fd6855e309fe5849e409fd1841f539fd68d5e30bed08d4921bbd48d49409fd288dd54bee2859d509fd68c1d53bee084c9219fd2891d309fd28d5e409fe0845d50bf61859150dde3745d509fd488dd209fe4895d209fd2891d50ddd158dd509fd5889d439fd6841f53dbd644de409fd488dd529fd78d4940ded128dd20bfa0854d10dde3749d50fcd1248e30bf618591309fe5849e309fd18d5d30bde38541109fe2855d40ddd258dd509fd28c1d54dd,0x4c87c41e088c21f1189a416b08046092258256b28b1c100784820f040ca0812c102582e508182965608889d101ac1008c5ae810100004840d20d48200000ca080461000148081c2230959ca242843c1034684e50ba02000783920b582072840ce0b38200018206705d01c506ca1202144e80801280a142e80f880d60309d01940446100b420940400002ac10000c80805ae8030d2c1008046254072c11204d06916382006582065040d60e3820345204d61008c1240000006382e50b48200000070c7420c505ac10003e103a02d608000118412d60f8c001205a41a504000000c10e04020118a3a1001d017406a410000072840e80b582000902003a020000462d7408080007c34a088c3960e38200003e10558203432040cb05d01001ca17405ca17404461078885521181c6000e383e30628441e0313ca1f088f154e0307885d080e9c06180d0a203942072844682470cba10090461e181a41118791920307c80118400728408d0b203cae408fcbd203878e0c907f1c07221420c76480c1f03940012e883e06a70c18e0f8187520f81c1e4034821fa70800032821fc732868d080000f84ba103382022841e5c547478e0308006c73486ce08882ce0819c1017428e011746067040450aac29a0800220b282ab083c21e11e2878a0f0b1c1f1032407101901064846071e3b141f03078a02285321012161c364040e23c90c461e464a0a30f62846367059c12ea145e8eb07c0e1e119bd1d60f08c0e1f3434a1890b684fc2460d105a821c0d6061019805c019ff0ff37f2bf81fa4fc47db3e7df10f837ba][i]?.getD 0
def s477H6 (_ : Nat) : Nat := 0x1c4c005c1100701594a021a818000000000e80000000105801423d4e660e3eb123e475c3da967ba3adcd2206d90e44dbbd37519dc59132471061195c02ca0d72ad83c91715e97232efd909a500122b8d000000270c2c2f4582d1df608e0642e88000000ec1420000000021358c3488a84a23351f4df5e2350a90bce4f0000220246010ce019822
def s477D6 (_ : Nat) : Nat := 0x1e0b2c108032b0420080003041f081680cd01000000000008c2d7a020201d60802302480000e80800003ac1004604919608000658200000079421185af40404000194040eb040118124000007942f40401185a40000000440f88220b9c0f89ce0ea403846373a1d16a403c04079024078231c0547081ee290208880fb9c2f8fd4f17b6e9fa2e778edff7adaf5cd5f52d3748d0f3ece734c1f02b56d0b2ec6adeb2ab6a8a8e7699e6297658926448fe3a8d630885f47bdea795d6745a467d9a655906055453d4a515404ed2244cfa3acc82bc8217c4606400abc3ca8aa8241d1d648d65750eaf4f2b42a02856e0257459153abd3ca30a80a11be4946107d4e9bcd290c6ea84de5640850d20cbca2a102ba6599e379211754379225042471855b16572485308f714ad1abc6159e39542474423bf121ba4ea84778e50889d548ee9c8f0aa2411de395624748237c928c60ea9c77a25678dd50cbcb4cf0a80a11df890dd175432f2313c2a0284770e55891d208ee1ca1113aa95ce295a2375432daca940ae985738a5678dd50aeb0cac91baa11ee295a1578c23be723c2a890756465504dc50cceb2470abc811ee295a2375425f2d2042a68846f92518c1f539dca4810a9a214de6948437542b3c928c46ea86670de4845d508ee1caf0a92811de8951c375432f2c33c2a02865e5a27854050cbab2a302ba615da09514375423bf131ba2ea84f38e508d49218f714ad1aba61979199e150142b3872a848e885570e50595d208df24a311baa15ce2959637543ab2c2a826e287565a5504dc508ef1caf0a92811de8959c37542b9c52b386ea8575865640dd50ae714aca1baa195889541371432b512a826e286560e67854050cad1ccf0a80a135939021455432b4713c2a0284d65640850d30cac82a702ba41959054e0574c32b26a840ae996560e27854050
def s477D5 (_ : Nat) : Nat := 0x25593a1e54554120
def s477D4 (_ : Nat) : Nat := 0x105622d3a1e54554120
def s477L : Nat → Packing
  | 10 => (1,0,6,0,0,1,0,s477D10)
  | 9 => (32,1,6,0,0,11,0,s477D9)
  | 8 => (279,2,6,0,0,14,0,s477D8)
  | 7 => (315,3,6,0,0,13,0,s477D7)
  | 6 => (72,4,6,0,0,10,0,s477D6)
  | 5 => (1,5,6,0,0,1,0,s477D5)
  | 4 => (1,6,6,0,0,1,0,s477D4)
  | _ => emptyPacking
def s477I : Nat → Nat → Option (Nat × Nat)
  | 10,h => lookupWord 11 42 4 9 5 0 s477H9 (mixTag h)
  | 9,h => lookupWord 93 314 7 13 9 0 s477H8 (mixTag h)
  | 8,h => lookupWord 105 353 7 13 9 0 s477H7 (mixTag h)
  | 7,h => lookupWord 24 87 5 11 7 0 s477H6 (mixTag h)
  | 6,_ => some (0,0)
  | 5,_ => some (0,0)
  | _,_ => none
def s477 : Forest := ⟨477,10,s477S,s477C,[[]],s477L,s477I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs477_10_0 : block s477 10 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs477_10 : block s477 10 0 1 = true := bs477_10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs477_9_0 : block s477 9 0 32 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs477_9 : block s477 9 0 32 = true := bs477_9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs477_8_0 : block s477 8 0 24 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs477_8_24 : block s477 8 24 182 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=5)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs477_8_206 : block s477 8 206 73 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs477_8 : block s477 8 0 279 = true := (@block_merge s477 8 0 24 255 bs477_8_0 (@block_merge s477 8 24 182 73 bs477_8_24 bs477_8_206))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs477_7_0 : block s477 7 0 2 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs477_7_2 : block s477 7 2 109 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs477_7_111 : block s477 7 111 204 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=5)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs477_7 : block s477 7 0 315 = true := (@block_merge s477 7 0 2 313 bs477_7_0 (@block_merge s477 7 2 109 204 bs477_7_2 bs477_7_111))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs477_6_0 : block s477 6 0 11 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs477_6_11 : block s477 6 11 61 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs477_6 : block s477 6 0 72 = true := (@block_merge s477 6 0 11 61 bs477_6_0 bs477_6_11)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs477_5_0 : block s477 5 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs477_5 : block s477 5 0 1 = true := bs477_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs477_4_0 : block s477 4 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs477_4 : block s477 4 0 1 = true := bs477_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts477 : checkedTables s477 10 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs477_4
  · exact bs477_5
  · exact bs477_6
  · exact bs477_7
  · exact bs477_8
  · exact bs477_9
  · exact bs477_10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs477 : graphValid s477 (boundsBefore es475) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls477 : Lower true (vars 477) (graphGoal 477) 11 := lower_forest (g:=s477) (i:=0) (hints:=8589964804) (before_sound es475 vs475) gs477 ts477 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es477 := extendKnown es475 11 [(477,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs477 : Known true es477 := extendKnown_ok (m:=477) vs475 ls477 (by decide +kernel)
def s491S := sampleAt 140 #[(0x41e09d600cc002187200ffedce00ffe600,0xa08d645cc8c008324648e4c64623e64a),(0x1a580e1800f0004619c00c01273ff007fff,0xa580a18c1f1840209cc2d84052c3612ac3),(0x0,0x0),(0x2061306000ffff98e1fff001c7c00007800,0x110600d541e88a160f01dc7c160b781a),(0x0,0x0),(0xc381c07fff0001e0fe000001f8000007fff,0x408140621e0039e0f602c059f80341a543c),(0xfc01ff80000001ff00000001fffffff8000,0xf401f501180231fd00128251b29389c0130),(0xfffe0000000001fffffffffe00000000000,0xfff40001900321775c9b0b60001a0d001a0),(0xfffffffffffffe000000000000000000000,0xbf7eaf9de0abc000001c0380001c0e001c0)]
def s491C : List ColumnInfo := [(0,1,298,704,6),(0,2,393,608,6),(0,8,99,896,6),(0,32,201,770,6),(0,64,424,515,6),(0,128,354,521,6),(0,256,195,552,6),(1,0,490,512,7),(2,0,489,512,7),(8,0,483,512,7),(32,0,459,512,7),(32,2,393,576,5),(34,0,457,512,5),(64,0,427,512,7),(64,1,298,640,5),(64,2,393,544,5),(65,0,426,512,5),(66,0,425,512,5),(67,0,424,512,4),(98,0,393,512,4),(128,0,363,512,7),(128,1,298,576,5),(128,8,99,768,5),(129,0,362,512,5),(136,0,355,512,5),(137,0,354,512,4),(193,0,298,512,4),(256,0,235,512,7),(256,8,99,640,5),(256,32,201,514,5),(264,0,227,512,5),(288,0,203,512,5),(290,0,201,512,4),(296,0,195,512,4),(392,0,99,512,4)]
def s491D9 (_ : Nat) : Nat := 0x1a512da839077f
def s491H8 (_ : Nat) : Nat := 0xee0011a85520880054e9007c0e840006b00187005a0002f000031a0521c0767041580140d
def s491D8 (_ : Nat) : Nat := 0xd1c3e41c2d1e52031b1d1c7c8a87651c92b2814d042142b1ed961f245a049c171cb0f31b912651c2a38ea0695203367830220a16764951d20e2819642412087192142e14010d9f0c0c86c7a00c4291ca8b907669692910545922143860634884024143c60cda20c14834e84264cbadcaee7e93e127e1d76858057d3e474fc2e0971f45c10821003fd42ff593fd54ff547fd21ff583fd40ff58bfd30ff4cbfd20ff543fd63ff587fd53ff443fd52ff507fd31ff597fd43
def s491H7 (_ : Nat) : Nat := 0x105a4981e200a5000ce8e7090da5043a723d62fd300000005640a26b0001b40076080
def s491D7 (_ : Nat) : Nat := 0x898a02035b280c44d8325161c08015224a00011c12501634a90071a091450438026c400940920b29360c5002f977b95b6d163af4c608d769335909b371a4783705014017f81d21bfc8ea9dfe3750aff2bac97f85d60bfc4e985fe675467e33a65770dd61af8ae904fe674cafd03aa95f95d20bf00eaa5f41750efb0ba876f11d10b7c8e885ec27596ef1bac37b89d65
def s491L : Nat → Packing
  | 9 => (1,0,6,0,0,1,0,s491D9)
  | 8 => (21,1,6,0,0,10,0,s491D8)
  | 7 => (21,2,6,0,0,9,0,s491D7)
  | _ => emptyPacking
def s491I : Nat → Nat → Option (Nat × Nat)
  | 9,h => lookupWord 7 35 2 9 5 0 s491H8 (mixTag h)
  | 8,h => lookupWord 7 28 3 9 5 0 s491H7 (mixTag h)
  | _,_ => none
def s491 : Forest := ⟨491,9,s491S,s491C,[[]],s491L,s491I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs491_9_0 : block s491 9 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs491_9 : block s491 9 0 1 = true := bs491_9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs491_8_0 : block s491 8 0 21 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs491_8 : block s491 8 0 21 = true := bs491_8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs491_7_0 : block s491 7 0 14 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs491_7_14 : block s491 7 14 7 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs491_7 : block s491 7 0 21 = true := (@block_merge s491 7 0 14 7 bs491_7_0 bs491_7_14)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts491 : checkedTables s491 9 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs491_7
  · exact bs491_8
  · exact bs491_9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs491 : graphValid s491 (boundsBefore es477) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls491 : Lower true (vars 491) (graphGoal 491) 10 := lower_forest (g:=s491) (i:=0) (hints:=12885979222) (before_sound es477 vs477) gs491 ts491 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es491 := extendKnown es477 10 [(491,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs491 : Known true es491 := extendKnown_ok (m:=491) vs477 ls491 (by decide +kernel)
def s502S := sampleAt 157 #[(0x0,0x0),(0xd3301b4400330000930fcc00099c003fffffff,0x53300945447351201105cd48808d48948d5523),(0x1203c2488003ffff31cccf00036e7ffc0033000,0x201400880d55037114ccf01992a419c19b306a),(0x0,0x0),(0x603c338f0003c000c60f0fffff8f8000003c000,0x2014338f0c37c30e4205054c3f8f8c58c5bc31a),(0x183c03c0ffffc0000f80ff00003f00000003ffff,0x8240140981b8006cf80fa00333f00350352a0dc),(0x1fc003ff000000000fff0000003ffffffffc0000,0x1f8003f6029200a48eea0002a22d52a62a600a90),(0x1ffffc00000000000fffffffffc0000000000000,0x1dfebc00031c00c70bdfafab3c00033833800ce0),(0x1ffffffffffffffff00000000000000000000000,0x17dbeabf67e02af800000003c00003c03c000f00)]
def s502C : List ColumnInfo := [(0,128,358,528,8)]
def s502D8 (_ : Nat) : Nat := 0x17f
def s502L : Nat → Packing
  | 8 => (1,0,1,0,0,1,0,s502D8)
  | _ => emptyPacking
def s502I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s502 : Forest := ⟨502,8,s502S,s502C,[[]],s502L,s502I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs502_8_0 : block s502 8 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs502_8 : block s502 8 0 1 = true := bs502_8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts502 : checkedTables s502 8 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs502_8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs502 : graphValid s502 (boundsBefore es491) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls502 : Lower true (vars 502) (graphGoal 502) 9 := lower_forest (g:=s502) (i:=0) (hints:=9681962576) (before_sound es491 vs491) gs502 ts502 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es502 := extendKnown es491 9 [(502,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs502 : Known true es502 := extendKnown_ok (m:=502) vs491 ls502 (by decide +kernel)
def s255S := sampleAt 236 #[(0x801024330000092400ffff118e3041a4e801003ff3333cccc00ffffff,0x2411000099240a540b00861000a468150280b1111cccc12555413),(0x1026000ccacc00e3800cc00221049a6c73001ffc00ccccffffffcccc00,0x2200044acc85e3886cc86000008a2c5310d21c864444555487cccc8a),(0x6038b38f0cf000fc000f000cce38e38f83ffe00000f0f0f0f000f0f000,0x2028b38f0cf19dfc19ef19e44a28a28e83b3e6799ef0f0f0f1b6f0f1ba),(0x984c0c3f00f0000fffff0000f0fc0fc0ffc00000000ff00ff0000ff0000,0x88440c2d00f003db6c3f003ef0fc0fc0ffc0bc1785eff00ff0076ff007a),(0xe0700fc000fffff000000000ff000fff00000000000ffff000000ffffff,0xa0500d4000f5436000340034ff000fff0000a815054eeee000064aaa86c),(0xff800fffff00000000000000fffff00000000000000ffffffffff000000,0xff800fffbb00338003380338fffff0000006b0d6358bbbbaaab78000370),(0xfffff0000000000000000000fffffffffffffffffff0000000000000000,0xfdfd50000000220002200220bb5965551284c0982600000000240000240),(0xffffffffffffffffffffffff00000000000000000000000000000000000,0x57abf292ee0abc0493c0abc000000000000700e03800000000380000380),(0x0,0x0)]
def s255C : List ColumnInfo := [(8,0,247,512,10)]
def s255D10 (_ : Nat) : Nat := 0x2ff
def s255L : Nat → Packing
  | 10 => (1,0,1,0,0,1,0,s255D10)
  | _ => emptyPacking
def s255I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s255 : Forest := ⟨255,10,s255S,s255C,[[]],s255L,s255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs255_10_0 : block s255 10 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs255_10 : block s255 10 0 1 = true := bs255_10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts255 : checkedTables s255 10 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs255_10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs255 : graphValid s255 (boundsBefore es502) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls255 : Lower true (vars 255) (graphGoal 255) 11 := lower_forest (g:=s255) (i:=0) (hints:=1078868) (before_sound es502 vs502) gs255 ts255 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es255 := extendKnown es502 11 [(255,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs255 : Known true es255 := extendKnown_ok (m:=255) vs502 ls255 (by decide +kernel)
def s383S := sampleAt 236 #[(0x11302ab00000facc00cc00118e3041a4e801003ff3333cccc00ffffff,0x1102ab224005acc8acc8a00861000a469152288b1111cccc92555493),(0x61c100c002ccccf000f000221049a6c73001ffc00ccccffffffcccc00,0x214100c60eccccf186f186000008a2c5330d61d864444555587cccd8a),(0x820a3300030f0f0000ffffcce38e38f83ffe00000f0f0f0f000f0f000,0xa33006f050f001e541f44a28a28e8383e0781ef0f0f0f036f0f03a),(0x930c0c3c0003f00fffff0000f0fc0fc0ffc00000000ff00ff0000ff0000,0x91040c3c00ef500f543f003ef0fc0fc0ffc0bc1785eff00ff0076ff007a),(0xe3f00fc00003fff000000000ff000fff00000000000ffff000000ffffff,0xe3f00fc00ccbffa003340334ff000fff0006a8d5354eeee000364aaab6c),(0xfc000ffffffc000000000000fffff00000000000000ffffffffff000000,0xb4000e7f10f0000000380038fffff0000000b016058bbbbaaa878000070),(0xfffff0000000000000000000fffffffffffffffffff0000000000000000,0xffdea0000880000002200220bb5965551284c0982600000000240000240),(0x0,0x0),(0xffffffffffffffffffffffff00000000000000000000000000000000000,0x4afbf180ef00aaf0abc0abc000000000000700e03800000000380000380)]
def s383C : List ColumnInfo := [(8,0,375,512,10)]
def s383D10 (_ : Nat) : Nat := 0x2ff
def s383L : Nat → Packing
  | 10 => (1,0,1,0,0,1,0,s383D10)
  | _ => emptyPacking
def s383I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s383 : Forest := ⟨383,10,s383S,s383C,[[]],s383L,s383I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs383_10_0 : block s383 10 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs383_10 : block s383 10 0 1 = true := bs383_10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts383 : checkedTables s383 10 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs383_10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs383 : graphValid s383 (boundsBefore es255) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls383 : Lower true (vars 383) (graphGoal 383) 11 := lower_forest (g:=s383) (i:=0) (hints:=8591017556) (before_sound es255 vs255) gs383 ts383 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es383 := extendKnown es255 11 [(383,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs383 : Known true es383 := extendKnown_ok (m:=383) vs255 ls383 (by decide +kernel)
def s447S := sampleAt 242 #[(0xf02ab000007d6600330000486600000924007fffccccf333001ffffff,0x502ab212002d6642b32140482200109924852a42c4447333224aaa913),(0x132cc100c001666678003c0000019959800e3800660033333ffffff999800,0x132cc100ce47666679c9bce4c0008959f45e3ba367d191111555e8f999f4a),(0x200f0a330001878780003ffff671e19e000fc00078003c3c3c3c001e1e000,0x20050a3300f78287801f950ff671e19e0ddfc06f7837bc3c3c3c1ede1e0fa),(0x300c3c0001f807ffffc000187e01e0000fffff80003fc03fc0001fe0000,0xc3c0037a807aa07c003d85a01e001db6c0f8007bfc03fc006dfe003a),(0x3c00fc00001fff8000000001f8001fffff0000000003fffc000001ffffff,0x1400fc00425ffd0008500429a8001eaa160010a00853bbb800044955522c),(0x3c000ffffffe0000000000001ffffe000000000000003fffffffffe000000,0x24000e7f10b800000016000b1fff76000980004c00262eeeeaaa1700000b0),(0x0,0x0),(0x3ffff00000000000000000001fffffffffffffffffffc0000000000000000,0x3ebfa00008c000000118008c0525dc154e0492705538000000009800004c0),(0x3fffffffffffffffffffffffe000000000000000000000000000000000000,0x1bfaf180ef00557855e02af0000000007000038001c000000000e00000700)]
def s447C : List ColumnInfo := [(4,0,443,512,10)]
def s447D10 (_ : Nat) : Nat := 0x2ff
def s447L : Nat → Packing
  | 10 => (1,0,1,0,0,1,0,s447D10)
  | _ => emptyPacking
def s447I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s447 : Forest := ⟨447,10,s447S,s447C,[[]],s447L,s447I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs447_10_0 : block s447 10 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs447_10 : block s447 10 0 1 = true := bs447_10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts447 : checkedTables s447 10 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs447_10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs447 : graphValid s447 (boundsBefore es383) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls447 : Lower true (vars 447) (graphGoal 447) 11 := lower_forest (g:=s447) (i:=0) (hints:=8591013972) (before_sound es383 vs383) gs447 ts447 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es447 := extendKnown es383 11 [(447,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs447 : Known true es447 := extendKnown_ok (m:=447) vs383 ls447 (by decide +kernel)
def s479S := sampleAt 241 #[(0x400f044c00facc00660000080000249001ffff041a4e800800fffffffff,0x50044005acc21661080000010649084a843000a46842842086aaa843),(0x1b2cc1872ccccf00078000135660038e00198009a6c73000fff001999800,0xb2cc0852ccccf16b78b5811566b978e5cd9ae68a2c532e6ae75cd999aea),(0x200f020830f0f00007fffc1c678003f0001e000e38f83fff000001e1e000,0x500003050f000b2a05c14678097f004de026a28e8382702604de1e02a),(0x40300c303f00fffff8000260780003ffffe0000fc0ffc000000001fe0000,0x4103500f54078003a20780036db01e000efc0ffc01601602dfe001a),(0x183c00fc03fff0000000003807ffffc000000000fff000000000001ffffff,0x81400fc03ffa000c600632807aa63800318018cfff00019419432955519c),(0x0,0x0),(0x1fc000fffc0000000000003ff800000000000000ffffffffffffffe000000,0x1f4000f7a80000028401423ea80142000a100508555128518518a30000510),(0x1fffff00000000000000003fffffffffffffffff000000000000000000000,0x17ebfa000000000308018415f8558c124c615630000000620620c40000620),(0x1fffffffffffffffffffffc00000000000000000000000000000000000000,0x1fffafbefcaaf0abf055f8000001f0000f8007c00000007c07c0f800007c0)]
def s479C : List ColumnInfo := [(2,0,477,512,11)]
def s479D11 (_ : Nat) : Nat := 0x2ff
def s479L : Nat → Packing
  | 11 => (1,0,1,0,0,1,0,s479D11)
  | _ => emptyPacking
def s479I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s479 : Forest := ⟨479,11,s479S,s479C,[[]],s479L,s479I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs479_11_0 : block s479 11 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs479_11 : block s479 11 0 1 = true := bs479_11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts479 : checkedTables s479 11 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs479_11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs479 : graphValid s479 (boundsBefore es447) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls479 : Lower true (vars 479) (graphGoal 479) 12 := lower_forest (g:=s479) (i:=0) (hints:=8589964900) (before_sound es447 vs447) gs479 ts479 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es479 := extendKnown es447 12 [(479,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs479 : Known true es479 := extendKnown_ok (m:=479) vs447 ls479 (by decide +kernel)
def s495S := sampleAt 241 #[(0x400f02755800acc006600010190ce49001ffff8e3a4e800800fff999800,0x502355905acc836641800090464920ca907861a4690690620f99990a),(0x192cc03806000cf0007800022603338e0019800104c73000fff001ffffff,0x92cc02806311cf18978c4802201138e6459b22000c53322b23644aaab23),(0x220f004198000f00007fffcc38e3c3f0001e000e38f83fff000001e1e000,0x205000198035f001b2a0dc428e3c3f00cde066a28e838670660cde1e06a),(0x40300981e0000fffff800030c0fc03ffffe0000fc0ffc000000001fe0000,0x881e000df540780039040b402db01e000efc0ffc01601602dfe001a),(0x0,0x0),(0x183c00e01fffff0000000003f00fffc000000000fff000000000001ffffff,0x82400a01f886e00036001b3f00feec0019800ccfff0000d40d41a95550dc),(0x1fc000ffe000000000000003fff0000000000000ffffffffffffffe000000,0x1f4000fd4004480022401123bd50000009100488596128498498930000490),(0x1fffff000000000000000003ffffffffffffffff000000000000000000000,0x1ffffa0000067000338019c2fbf4bb924de156f00000006e06e0dc00006e0),(0x1ffffffffffffffffffffffc0000000000000000000000000000000000000,0x17dbaf57e077800abc055e00000000000e000700000000700700e00000700)]
def s495C : List ColumnInfo := [(0,2,397,608,7),(0,32,205,770,7),(0,64,424,519,7),(0,128,358,521,9),(0,256,195,556,7),(1,0,494,512,10),(2,0,493,512,9),(2,64,424,517,6),(4,0,491,512,10),(4,256,195,552,6),(6,64,424,513,5),(8,0,487,512,10),(32,0,463,512,9),(32,256,195,524,6),(34,0,461,512,8),(36,256,195,520,5),(64,0,431,512,8),(64,2,397,544,6),(66,0,429,512,6),(128,0,367,512,9),(256,0,239,512,8),(256,32,205,514,6),(288,0,207,512,6)]
def s495D11 (_ : Nat) : Nat := 0x72d1328ccff
def s495H10 (_ : Nat) : Nat := 0x9a24003b0029000258b05100e5561743340
def s495D10 (_ : Nat) : Nat := 0x950a0753336b8ee55744aa671a015c9968510af38ee45741d2a11e673aba25516123cd35d074aa088e71a6ba0e9424a3cd04d741d2a91e673aba25523cce75744a12b1e6824eae89508f33cb420a562671dc994e1878db45e53e40cd42946a0ec00ffaebffdd7fe3afff51ffae9ff5c7fea8fff71ffee9ff553ffaa7fe75
def s495H9 (_ : Nat) : Nat := 0x46417b800b3116f17ad3782bc342a4c1154cc004beb4003a1d915728a8f5214ea100bc69892c72674d65253a3375c2e710052800d1c00001c3c40c6002db000996ca5fa626cda0690800009c00003d201100f5ff2c6000281084013055
def s495D9 (_ : Nat) : Nat := 0xd011814d73b29ca4eca4741729109af1e8e739008a65c7cf5aed0821979e3d73b41ea65d13b9e309ad01f4149daf298168cad31f39dad010a66d0472e3e65766b5a8cbcc3e31bacec3294d13b1f3d681c02834cbaf41ea650841773c7af424168cb8f9ced741043465298f9aed689d94a82d18f9eb450699744ee78c16b4e59c506e8c7cf5a270268432e8d67d13886b1b94c0b46529af1f3a0b92132f3c60b5e85c820532e3e7af42e404cac31f3d7a2722a68cac35e3e612724ae5053b1f3d7a100b2b4d13b1f3d68cbcf1aed7a020245409971f3d73b423465a1af1f30539043465d61f1f39c82195a689dcf1eb426d1979ebc656623465044a76bc7cd04346569af1f39c8d1948eb8cb31f3468cac0a6bc7ce720268cac35e3e739194210e78d76bd08ca535e8e78e71c0e5a1a0734d67205676bd05ddaf411c7cca94ca9cba11eb284371ca6bd194833dc7cba0a10d7cf1ee473d7a08635d94e40ae5cd8f5f3d0453335e3e7a0887ca8ca5286bd00b1f32bb15a35e529cf1ae3d0cb5050fe78f76b4c61a575e8e78f2a30b3012f1ee2ad52c5eba2aae96688e79a6c25b24be3ca2d61c60d1ff9f3de2dd39c45b51a4194d85976567157d4893952a11ad0b8fc4ed0ddcce8c10b38a989888b07d86e460c4fc4082dc2040f40037f55d71dfe575c6ff96171bfd48dd6ff5e354bfc585d37f55f71bff78546ff5e275fee285d6ffd6374ff571d46ff52275bfe78546ff46075bfd78552ff1e154bfd58dd3df5d554f7d75d52ff46375bfe485d6ff52075bff585d2ff16171bfe78552ffde154bfe185d6ff96174bfc78546ff5e351bff78d53fd86154bfd78546ffde351fbe485c6ffd6371bff585c6ff46275bfd58dc7efdd154f7e755535f5d475afd681d6bfda075d7f759d6efd2275bbd489d6fd86154bf518dd6fdc6375bee285d6ef92171
def s495H8 (_ : Nat) : Nat := 0xe7668bc004e4ce5c8a3344fcbe126a1300d8d4eaa870903b400000000c003560a18802ac28080d09120
def s495D8 (_ : Nat) : Nat := 0x250245d004683110f402180c0004e6e5e8ebec11e3f315500000000000009c0068304728008c542015cc10ae3081ddd7d02a23cbc7e68cee02e756a8d31eef276ba1c6de6cb519eca62aa146863c9d0be4a22803adc52ba8eb97d571e154bbb2cae3a8e5f5d4585c65fad23c2a93ee295e151cbf44aea3acfb8a578d467dc52bc2a93bd499e15497fb48b0b8cfd8657855277a93ac2e32fd69161719fa8cef0a8cbfda4785527dc52ac6e99f517de3519f714af13adcfd677455337c8f3c2a93f519de1549fa8cef1aa4ef52758dc677c92bc2a317e895d475
def s495D7 (_ : Nat) : Nat := 0xc5b8a6895d475
def s495L : Nat → Packing
  | 11 => (1,0,5,0,0,1,0,s495D11)
  | 10 => (12,1,5,0,0,10,0,s495D10)
  | 9 => (53,2,5,0,0,12,0,s495D9)
  | 8 => (26,3,5,0,0,9,0,s495D8)
  | 7 => (1,4,5,0,0,1,0,s495D7)
  | _ => emptyPacking
def s495I : Nat → Nat → Option (Nat × Nat)
  | 11,h => lookupWord 4 16 3 8 4 0 s495H10 (mixTag h)
  | 10,h => lookupWord 18 64 6 10 6 0 s495H9 (mixTag h)
  | 9,h => lookupWord 9 32 5 9 5 0 s495H8 (mixTag h)
  | 8,_ => some (0,0)
  | _,_ => none
def s495 : Forest := ⟨495,11,s495S,s495C,[[]],s495L,s495I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs495_11_0 : block s495 11 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs495_11 : block s495 11 0 1 = true := bs495_11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs495_10_0 : block s495 10 0 12 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs495_10 : block s495 10 0 12 = true := bs495_10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs495_9_0 : block s495 9 0 11 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs495_9_11 : block s495 9 11 42 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs495_9 : block s495 9 0 53 = true := (@block_merge s495 9 0 11 42 bs495_9_0 bs495_9_11)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs495_8_0 : block s495 8 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs495_8_1 : block s495 8 1 25 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs495_8 : block s495 8 0 26 = true := (@block_merge s495 8 0 1 25 bs495_8_0 bs495_8_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs495_7_0 : block s495 7 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs495_7 : block s495 7 0 1 = true := bs495_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts495 : checkedTables s495 11 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs495_7
  · exact bs495_8
  · exact bs495_9
  · exact bs495_10
  · exact bs495_11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs495 : graphValid s495 (boundsBefore es479) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls495 : Lower true (vars 495) (graphGoal 495) 12 := lower_forest (g:=s495) (i:=0) (hints:=8591013462) (before_sound es479 vs479) gs495 ts495 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es495 := extendKnown es479 12 [(495,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs495 : Known true es495 := extendKnown_ok (m:=495) vs479 ls495 (by decide +kernel)
def s503S := sampleAt 275 #[(0x800780a61580000fcc000020206600000fffff8c60d00010001fffccf30001fffff,0x2802215840905cc205000002200409542058420508150814102c4730824a8413),(0x326660338860000ccf0000044c19998000cc000109360001fffe000333fffff98000,0x126660128862c43ccf162300440899ac85cd64300116590d590eb219115590f9ac8a),(0x440780441180000f0fffff98719e1e0000f0000671c7fffe00000003c3c0001e0000,0x402800011800db505406f88519e1e019df00cf25147033e033c067bc3c036de01ba),(0x0,0x0),(0x1807806781e00000ff000006181e01fffff00000781f8000000000003fc00001fffff,0x802806781e01832fa00c1a2080a00a983600c1a781f830a830a86153b8030c95186c),(0x6078007801ffffff00000007e01ffe00000000007fe00000000000003ffffffe00000,0x20480028013881bc00000dc7e01f76003380019c7fe0006b006b00d62eea06f000370),(0x7f80007ffe00000000000007ffe00000000000007fffffffffffffffc000000000000,0x7e80007ed4005120000289077aa00005220029105aca8a4c0a4c14980000a48005240),(0x7fffff800000000000000007ffffffffffffffff80000000000000000000000000000,0x77fd7d00000061c000030e05f7f5dd563c0ab1e000000c700c7018e00000c70006380),(0x7ffffffffffffffffffffff8000000000000000000000000000000000000000000000,0x5fb7d7d7fec77e00afabf00000000007c0003e0000000f800f801f000000f80007c00)]
def s503C : List ColumnInfo := [(0,1,294,720,7),(0,2,405,608,8),(0,4,179,832,8),(0,6,145,864,7),(0,16,358,641,9),(0,32,213,770,9),(0,36,145,834,7),(0,128,358,529,9),(0,256,211,548,9),(0,258,145,612,7),(1,0,502,512,9),(1,16,358,640,8),(1,128,358,528,8),(2,0,501,512,10),(2,32,213,768,8),(2,256,209,548,7),(4,0,499,512,10),(4,32,209,770,7),(4,256,211,544,8),(6,0,497,512,7),(16,0,487,512,10),(16,1,294,704,6),(16,128,358,513,8),(17,128,358,512,7),(18,0,485,512,7),(20,0,483,512,7),(32,0,471,512,10),(32,256,211,516,8),(34,0,469,512,8),(34,4,145,832,6),(36,256,211,512,7),(48,0,455,512,7),(64,0,439,512,9),(64,2,405,544,7),(64,4,179,768,7),(64,6,145,800,6),(65,0,438,512,6),(66,0,437,512,7),(66,256,145,548,6),(68,0,435,512,7),(68,32,145,770,6),(70,0,433,512,6),(96,2,405,512,6),(98,0,405,512,6),(128,0,375,512,10),(128,1,294,592,6),(128,16,358,513,8),(129,16,358,512,7),(130,0,373,512,7),(132,0,371,512,7),(144,0,359,512,8),(145,0,358,512,7),(160,0,343,512,7),(178,0,325,512,4),(256,0,247,512,10),(256,32,213,514,8),(258,32,213,512,7),(260,0,243,512,8),(260,2,145,608,6),(272,0,231,512,7),(288,0,215,512,8),(290,0,213,512,7),(292,0,211,512,7),(320,4,179,512,6),(324,0,179,512,6),(358,0,145,512,4),(384,0,119,512,7),(404,0,99,512,4)]
def s503D12 (_ : Nat) : Nat := 0x5868a106c34cff
def s503H11 (_ : Nat) : Nat := 0x54c6090012bb5b4e94000002f1d40011fa8a9203e85103aac76320000149c42ae7b0003b76460800000a3000e645171696aa5c80032ee688ac1c24eef20f1cce007ac0013e0001611000000d4603010
def s503D11 (_ : Nat) : Nat := 0x9a908d2e0a14b63c6ca09101b1bcd5604a6402c3a6850b826d80d31a19292040596d345c9902e940c0e9a2c09b60354a4846cd1705165b22342e68501ad8b8480d31a6d2825341619586e4c12b1a940e3eac2234a4846cd0590565b06243a52402eb0dc3068a0194171b356c18060c202490790338d2cb69a3cd4a4856071006915b04a8d8f252b0a04838f35291b6d58402042240ca0b8d20149a90b62e4024d4819c68a5b1c2e403a68343026d80d31b213416416c1873694123dac2130d05c807171b831cda342c48de68b8250591a6535216c1878d2e940c2cb69a0612035160648071b974a032240340c2e503a6ab2d8243085827281a1d34215844256ca8d909a0b210c2822b620546880185ca034d565b09061130964080366a52b03826d80d72017291b5934416c184c504442d1a901cac94372106406484690174a145b4d111610b24038682c3018dce6d1a113528726f584412a278d20109a94b6ac1206035904846cd145b1710910a05acda344830ba50de682521c4129206e35580c8900eac94201a372240946cd4a101b561b90a44a342cde6830d82519558bb8217876dd6535b94ff4953fb3512b723d19311906efe4f6aed0e56decd72ce8c6ebc4b3aa709c691c8527986be63456a4f044638c2d22381ae12408a001ff8c3febaffd31ffacbff587ff307fd32ffae1ff50bfea87fd40ffc41ff583ffa8ffd74ffea5ff54ffe987fe10ffca1ff5c7fea1ffd73ffac7ff58bfeb27fd10ffa43ff143fe907fd51ffea1ff507ff32ffe40ffae5ff54bffa9ffd76ffaa9ffd53ff3affe70
def s503H10 (_ : Nat) : Nat := 0x110e53b12341441cddac53541b39965b024c10659ae5facbd1a7389be5a018792bc68dca54c231f8071a51562205b5e26f27c83b40ee89aa221338284eafea051ce02407f4c05a81849a4f538613e4319d8d1d603f93a63e22af439bd519d204f1239a2db66d483844faa97b0189ce43f8fbc1c6a69484cd4d08f4980ad1dfef6d2882d1c468e3897b2470da442d2e0183a514fff4c4a8a257f18e22438259eec4e128a4b5a1af3e4b10bbd52000000016a08b8f030f0000000e7e000312a10706135cda68932034b3cd0df4bb08816cc21952a2b3e9768b642901b32dd2a8000f547a89a6fc2bcf86031377113e8f301d2e8e89846d66c8c3a24000f8049c80004540290002db8b5a310b2b5dbcd3df2be438000ab14563a78000aaf0002228000a16000502222875882c58028a713c87e2be4000000f710003032000a408003e0fd1900042f0805130b0bd84f8f7af20007bb80004f77a511654666c2764d190000000000145c5184e6e8df21391731e79d0345863ce1e258002c14000d27bd0f557e7f0007ba7a66000000129a62b8a577db8749fdced0647906d640df984a043822000e98800211d83e7a90001890000c6329c6d2ee62a5b8000000b4f0000003205a562628000001620d898003c5f34000019b21d0147623a369216049d53828f55023d89da0b25380806a2b9bb6b22f453d69a617183c875bca9e41506460f17a074655f9fa1d2de2e66f52730cd6b51ce653cdbe0830a0073b9c00028500068e3c1e0d3e8820379f4450d869af90ebf038963ca7d21f55f3b8000000f46982fb540012e4666406951ae9fe93000057e0eaea0cd22e2ca78663887e52843279228d40169539a172089618cb037dc8b96ccae7996817a23134da488a5576a5f011d0b402e0f04053901040001091265032208061d0000000204091c0a011f0d00392705010203001b1f0706497b000702000101070104003971002600310f05010804020d00102e00060a0535010d0009000005000d0103051b20071e06010a830000003f0d3e0519b10b002c0e062b04000e01
def s503D10 (i : Nat) : Nat := #[0x3ff58d71ffd655cbff59552ffd72983ff54a60ffd21943ff50560ffd35547ff54530ffd548c3ffd5230ffe758c3ff59554ffd63487ff5c950ffd25543ff55260ffd53507ff45650ffd414c3ffd5260ffe75983ff58d51ffd41943ff51550ffd72583ff86150ffd52583ff58d41ffd535cbff4d552ffd724c3ff54930ffd54583ffd5160ffe75583ff5ca50ffd25943ff51553ffd544c3ffd5130ffe754c3ff58d72ffd6354bff51650ffd5458fffd5163ffe7558eff46270bfd3854aff16170ff950882ff46260bfd58442ff46265bfe2854effd6220bfe185daff5a152bfc08486ff96162bff58482ff96173bfd589c2ff4a230bfd488c2ff52352bfe585daff92150bfe28542ff5e210bff08546ff56240bff08486ff56220bfe4854aff82175bfe184caff5e350bff58486ffc2352fef5250aff9a151bfd788c2ff96121ff950842ff9e153bfd78542ff8a161bfd48882ff5a351bff58442ff9e150bfe18482ff5e353bfd58942ff4a250bfd089d7fd5c751bfd4854aff96164bfc58586ff96140ff950442ff96131bfd389d6ff92165bfd08d4aff9e151bfd08d47fe54120bff58982ff46220bfd48542ff46250bfe58482ff56121bfe28596ffc2275fed42482ff4e351bfd48982ff16132bff588c2ff4a265bfd38486ff46050bfd58482ff8a131bfe28502ff52350bfe28552ff5a354bfd18d4bfd5c510bff58902ff5a151bfc58442ff86153bfd68486ff8a110bfe28592ff02152bfe08486ff4a350bfd28842ff4e352bfd58843fe94110bfd28982ff86162bfe0854aff92153bfe784c6ff5e250bfe185cffe94120bfd28d4effc2351bfc584c6ff4e354bfe58442ff9a175bfe185c2ff16120bfe38486ff52050bfd18d4eff02154bfe585c2ff92162bfe28546ff42354ff551442ff16176bfd48482ff86175bfe18596ff16143ff551486ff52250bfe08546ff46350bfd48996ff96132bfd78996ff4a110bfe1854aff5e110bfd78982ff8e175bfd78d46ff4a354bfe6854aff4a240bfe5850eff02175bff08d52ffd6270bfd38546ff8a143bfe68486ff5e151bfe68552ff96161bfc58592ff5a275bfd188c2ff52353bfd78142ff56230bff58842ff8e152bfe38552ff16121bfc08546ff5a352bfc58502ff46275bfe38546ff16162bff0854aff56260bfe08552ff92120bfc585ceff4a050bfe18542ff4a351bfe484caff9e165bfe78586ff9e110fed52487fb549209fd78d527f1e142afd68d4ebf9a130aff68d4ebf5a050bbc485c6f74e2659ff78142bfda050f7950142efd2275bec285d6ef52275bf418552fd46050bf618552f7ce265bde38582bf1a1309ff78d52fd46240bee285d7ded42509fe7850a7f5e050bef289c2ef52050bbf48142f7ce050bf718902fb4a270bf718142fbca050bbe485c6f74e050bdc38582fb4a050,0x8b805888c20db26b20224d830168106b3340ac6a5050224b0855901b82c180646982537cd0301609c69d1b9a1002d1c0c11641090db6344092058304281beb3282109434c20c682c199a110a0428cd6d8198d4a4b320711634419a058a0182146b21d585a98f4fde9aed29fa42f451e85fd0259ecf3b7e707cd75999330be5d3cb3194c325fe472c8398f3f1bce308c59b89df110e1ddc3218533088e0d6c11380f2feedf87be997b92f54de5cbc0d769ee9b5cfbb94b7186df85bb5b6bf6c4ad50da66b3fd6612c9bd8eab15f6166c01d7c8af1b5cbab70d667ac2356eeac05521a99751d6a0b53a5a69f4c52956523ba395454287d50bfa0af40067d5cf559ded3a827254de29ad1342665e4c5498332eea5a94afc955f296650ac9b692c1247245ec85590231eee3bbc7338dcd1a4231445db8b2f154e28344b988c7107e1edc39786950c1a161425a841b067209ec0e781350111ffbbfaa7eccfc41f5d3e767c64f74dec7bd5d7a20f30de323c2977caeea9daebb1075bcea21d2239dc730ce4c1c7f389f70a4e015bdc377d6e4edb8db58b65b6c0ad6bdaa8350c697ed1c9a09b3e1674ccd89981b2b664aec8298deb1826222c359832b0065f2abd457822eb75c9eb8096d62d5f5a48b33963c2c225786adb55902ad354e8a8e54faa99652b6a45d460a88650969ff93c6a7404dd49a99331260c4b5a951528e24c648f290f91e6a38046308b99155a270445887c50d2214e41f082d10261ff63f527ce0f7a1eb03cc678a0eed9da03aca743ce611c7538506f90dc71b5335fa6b2cd3199fb335c6584c8a18ac30e26090be297782e685be4b4d165f2c48575cac9954f2a165340a41944827f64e949b09314256a49c491211d7230244ac873909120763f947c30f421dd83a347248dea1b3a35406860cbf18c030285ec0b9416a02c3055b0a69146e27cc4d3096b123c234444688400fe61e503a387150d6c1a1031b85ea0b4c156428f04da095011b421003d307300d7418c82de052208c80fb81b302cc046406f0091009a0003ff5d630ffd18543ff5d565ffd75983ff92150ffe28543ff50a30ffd75543ff59542ffd42983ff5e150ffd70543ffd4630ffd42543ff9e150ffd75583ff5d230ffd50503ffd4a30fff51983ff59574ffd7554fff5d530ffd74983ffd4a60ffd42583ff52150ffd75943ff5c630ffd74543ff59571ffd5350bff50930ffd71983ff5d563ffd28543ffd4560ffd42943ff48630ffd74583ff5c550fff52583ff59521ffd21983ff58d42fff514c3ff5d153ffd518c3ff5d130fff524c3ff54110ffd65547ff5c560ffd21543ff54660ffd50483ff50630ffd74943ff58f51ffd65507ff54d71ffd714c3ff50660ffd7458fff45550ffd63d4bff48560ffd71943ff50550ffd53487ff48530ffd728c3ff54a30ffd5158,0x85b8b8a8805e6874b717184c0c496696e0b302c2537cd03c762e3ed8180b88448466c682c4427db2485c214089170e04e6b6c8c106412a0c866807b6870b8120b4a501c221be415c8b3887219401e6b590bdb026190e5a30138d096695937ca2b93940942f3537860981288800f1b0bca6b00d9a116da250c60a61d9a45eda24ae3a6b208e5b888180b3e401622cd094422e47232006460dd162b3650250bd666a18269ba11c28972df280c3650750ecd097586106432822076b116374627290b07668130c1080d18d060272812cd4de5c81f6511c228587b590c40841f94096b26f9a38304626ca6d91d9a9723520bc80380c3717180310ca03b35b6d60a6249472dc500c05940790ca09735ac45ed8128c872f299012888430b44eda199a472d340c4708b20b79765100b0c88b35b6890b80c8060871a92cd2de5d94404f2890cd42c430ed66d9250c5e503a27896db5861ee5125ac858e2182144b31a92052da5d945be6912a458271a125766929374220810dcd65358b738884f94070df586566372803db6695d120323140e0584418061b9b200e058186e2e30231a09cd231173720201c22c822c6e8c101c138d0902c199a9b9d162101c3b3409571c160e0f8446e2e365334ae14c3919b6892002411ee5071ac36401c8cca0186eac57206021066525db604e6a1c9c80381994030de5c710e351812cd4dd5d94402b208dcd20d4289476d85ca4d02d1c225be405c71083334925b82d6d8d40571b901202b35b61720079005eda1c09cd2801894a63734038901b6cae45a5160ec80186eae4a1f359486eb21d105044b6c901e4117b687027348c12a4438ddb2bb29120366918903642340eca283590c1bc2d42112e5025ac9be68e94c86680609db4395c8b4a831b9401c4b6d9a9701818a01a2f6c068923044716e3659901202a5d94db6695940364117ac1ba305684d23a1794146b16f0c46341609cd0485d3738884f8d05a4b6c0c10a0470bca09b6dac46c33348e50884f9486c3b3492db6b12284702d6e2e28304d94496696f2e3a201994cd4b874b73e50750b5be6a1826380a1b94876685212db6b13948581b6c1286088068d6650401e0717280e886b234b6111f1a2ecd08050211102d114c6e6b21b6061b34205663450211102d020c6888180b14668428d643728124d4d8427c68bb342014084440c408320b6cd03044b705a0158d102b32828116695c21508817b61409b340c10a35820ca0f4245d666b298d902426c089b825594d608024382eb3299046c686f200320402212e68160c108a1194c803b583790018e20cd2531a2810888188176373590db030d14c6e4017b656668e20d66501c3e283818370581b206ca6366f9a096b240094083342214030420bc6a06facca440440e3278438d06080166cd0331b3705825207106401,0xb1100c0d12db2b8e099b6354194866b0259a9bc2d62705e6b6d068903046896640159441cbb348d44a876c8e6094439401e6a17ac860261cac8030459412887348e97241623cd24b6c2e14241003c682f6d1203669400c4830252eca1081f37cd20628c01ed95d12ca01908b8766853b689230e3111033292edb44b34064e50070b506b00db68943138d05824242ecd4dce09c6848160ccd4dce0ac6a433483512490db61728149ac82385cb7431c57105beb3285c683012129be6b292e423b2828d62dd350c85a0479485eb36c284943334905223340b060e96e601a2e1d9a04a304270701b200b1b830c8b8766a2422466da1a801e34179a896d81806407729ac5b89ca09c6a2f5994cd2308137482f348e1744b6c2338871a92102da1794d643334b75e6b2910d643a1aa0896d92214581a259adb230418d4c3b59941f280aacc8650079adb2b8130e4628158d5b24b34b717225022cd65027ac8744b6c81282f35b6874241823402c4d9a490b96e613248810bca6b2199a5ba7299a970c21c3a061d1c0b060a16e5116436caeca0261d9a46272803cd42d41ac87026189132db2892866b334b785a617944766b59b689430468d502c438d490b96f9a38884d9adb02c182810a0460bdb0a0199a49241020ca048438dcd22f588c9ba87b20ca6b1245011047c1ed6650d90070300c3797650ea0ca00c199a976d8130ec82a340e85e535837860a119484e6817b6066b21d0d11a8161810e6a1db6048b9094458871a12574df3480623851945bcb8d9410e36219a458835806db44918c1d6516f9ad6094d94116421b9a45883590edb02518c89653340bdb03359068808d52cc86365d94546db34a15028814c05a3b3512066d8467140ad1d0bca6b16f0c408f6c0b47033342646a0458dca00f35ac85eda250c032c459aca0a7590e896d900c11e5125b61466a5c904880421245cdd199ac6a3283e85c30448e32504590db438139a5722d32c0526b208e976516e864a831b9a01c4b6c061702d390c6829419adb0b950a250ab1a0c116504e92db4b842986a2e1d9a1144b6cae408b202505a38199a10a04e22ca00f590b866da24065668170e1d0605c6ca03a16061bc305074708045904d42f29ac5bc3142208e501c37d619180e116406eaeca1c4225ca4411d9a896db589ca0f6170c10a48c0e0364016370618608c01abb28098766910d01e421794d643b3421db02618c0588f3426db0b91c8d42321aaeca43b3512db0893941d43b350b8608ce0c070465d941a0dce03c6a2f6c06896691827480917948766853acdb44918aca6344e22cd42f6d0c4921842b0602c74232250438ddb01a259a5722d203c802f3409db0321c8cd030170d8708cd2cc682b28839766920925121b6cc066d91d9a8908e5d94400f1b9413e6b588bdb4491806582d1c2,0xd34be99a3a586140ad1d0c5ba6b599485a510b610e34810ccd2de1695b2f6151450a4a5c75b2f219acca42c508e4434433d466515d123c40453e57439166822697d3347450cb65ec2a58a1ca24a5c88a4c96d9a492df1b0c408e1794db24a19ac1424334a83cce58a046a3b6d90cd2534be8642c448e34291a934866b6d1451239252e5ad91cbc9641e6665b2f759948642d2421441e672c502436d9a4963530d110a76d0eca2ba259a462a149346a43292c496d91ca2cd4b9910562ca7d0e461a09338a2811bb6476433495b2f2292e4923a167852814a8ddb6422889cd239072e62da088e8a4cd786824ce28a0486d9259ac6a61a2611ed8199a8702d02010e41199a8765045b612c255cc83ad97b33494b0c90110a7588e866536d0b4966970a52a811b90966d91d9a44e51072e6c405023896d8199a05a1349c8a64142865bcb90b65e4321628471958b2906421bb68766918986c7158aeca41b213746261a219eaba248b34116cbd99a4a2864d27215909628728865bcb95145b2220ebc42cca08846e404a22ca6b219b6cd2251d0b10b558b2906362112cd6d918983cce588d486d91d9a49256cbd8642d2421326939905beb21994858850ca8688853b65743a259a45a609338a23521b64724b3495b2e5118d8a66944b744cb950a5029d2092c6eda299a4320e5cc83cce58a046a3b35b6c8261aac594f6248c34421139562bb299a9bc271a8c5880458d4666a0c21ca6d84f1257316cb944636590a5166b28b744cb990a53a81218d9624b6d9a43651072e6a404429476da190b4966929a83a7259335b984021c822d5d9adb096130e112e09338a2811a8edb66b20985282289a472df2086972614a08a26b208e5ba8a5c98563628a05b24b34b750cb951a562315d949b88b210e4ab21ab2cd4436d0e892312b65ce356fac8666b290b11225690c689f2822866db58924366a16216c2a58a04d2396f94c821a5ca86c7128ae836426e8b4234439012a39139adb43216225a6a089c8a4cd6e6854b1409ac82396f94514b958d9642940925b66b28b750cb96ac86acb2120db66a1c8c4a693990862de16214321342bd62de199485e404495b2220f2c5cade667ca08f588e132376d0ccd42d50799cb14090db669258d4c355887594de38843c4211394a4df34ae84e3516a1008b1a8b5766b6c278941842b5b41111145cade667824ce28a0486d9259ac6a60f334d6416e8e961e0f2c99a696f90471e0f2c99adb34b7496350b65ce356f0ccd42c44894a40458d13c310db6cd24a16215c51350b972dc4590472209334d6416e8e8a1e091499a696f90471e091499adb34b7496351105621e11399bac908856441658d9044b6d9a4625342b862de1790111e29324d6416e8e861e2932862696f90471e2932862db34b74963501205cdf340f06024e8,0x42941145b6356f9a492265ca11c2f290c132376dac4766952c5b63619945be6a5c9210aa152c502d96f8dcd6512489972f590c472dd350bca0a119411eb12092db430519a85a934be85451448e971d10b610e3481ac866696f9485ae20229f6515d0e461d34be854b14594474b9026202d924b7d6433359485a84cb6cd03016925b9e15908a2811a894766945b6972d34be866b3290b11239026cd42d6dac862df28924c1e66b65be69258d96216cbc8a2a1248e971e340c8702c5137342b1b14502410d9a496d9432e5e42590a97651408d44a8b6c8ecd32353c5644b28ae872311145b6356f0bcd4b924214c1266b6cd2dd258d8a216d0a5e4b151944923a5c9c6cb2152eca28120864966b6ca1641][i]?.getD 0
def s503H9 (_ : Nat) : Nat := 0xa9e529d617a074827eb155f910d12d3b144d73bfadce0ae8e888bad5c2bc6a000fdd3e4d5fd4051e1d2418812ab6c55d04b94b20252eca000000090cb9910d8e1afd000025d600000030b80004d9073c3eac84b1a591f2f0a453278e1051bcf20bf054d7244e99cb96d4bdc5db643988d85053a0ad82a1c53a9d00b3146ed3cef5604975805a0052500000000000002bb338ac4e21ca70fcd9196000dcf000130e0008ba5a351e0000e0455a0000faba832114001f030598003301d37c897d85f70000fd9e0c3cb10f500010780011c6ec97df693e8f229fcc770199902282b4ff80a550005800001f6b29a800337b184a011e968e17498999f4fa587ae0000003d26e51a5b80021b7943d40be99663676cbf10c8b43b09e15e132c71c21cac9075f31179580c56023d6a391b000000124721a12849e800000043a37794830000000000000a314b1c0b68b00000000000000697ca46668b5478fd4e0000000c5c000000057f7608938b1956e9ab21c4001f4f1e94ca9302d2d0007849a9bb6513288f4ef09058098002992c20f1f4cc902d3d15703ef8a43d5ca36a1052a62a213dfdc812d75d16b6dc538942ca022231b3bac5074c63bac64b5faf854bdfa28bb1dba165340490003e6d9c837392ed357e0e2f614a3264af9b3a50516d6d4dae65959ed8e304155651309a7d6c3b6b89cec757b9d757c644c0383c37796b8bf62977c8270b7fd0e244e818b82faa558ebc4e9916964b8a9000003c00000032de7a804313444e475e5caba1d501098271933c990e57e9c903fd37d420000edc0004e50006dd50f879c5d8800209be6606a087cec90f3a931a282e000074933f3a89c1741688e651c2d2c923f3b055d97f6634a4b770ac00005edc450ae83ee4f4610ca8ed3e61bf98d45eb3ebeff640000c596c3638263c353f234de0006506bfe604aef91b80036a2762c2956451b0fd0d77045de80a6b7860e35a1b644e1880034bda53c11e99c56c05c2e3af35ecc4464878d5e989eaaacd0b0040765985a13e022ac3f13f7c5adbc04adb6a658a26abb525a82431e594e30aafb6ab29e85eaf148f0cb9108e1a110456c5245a13830185606b23cb3ecdfea41dab7536dc668593f3121999d1b06e92bc109d10375d64c7fa2b66236941a485d01d50f53cfb19ab3ae60e0e1668d436f582f2a599a435a7afdbbe893637ec602090126010017022413010001130814011442081100000f10030009050c03000402022c043f0d121559170906000c00020302460a1a02010504100103040400091404011e0e0a020100000b2520020a04040407093c132607021409040282000f0a010d0400000657221f09000001440101010015000202021813210003120004030300360305091000042e11000108580508032725000708061302
def s503D9 (i : Nat) : Nat := #[0xec4ea9184ff96518982fe832aa2c73fd494a2609ff2ca91185fd8655458f7bae31c2c13fe594a2609febceb1305fb0a5785427fcb28c4613ff59462609ff24ab1305fb8a5755827fb13a94613fe8954660affbcea89857f9e5425827f8b2bc4613fe195e230d7eb88d0984ffa25548c27fb13a8cc1b7d65161219ff44a43185fb8a57554e7fa528c4c17ee295d530dee90c70b04ff5a7584867faf28c4c13fd29d6260bfb0ca90a867f54e7850a7fab28c4615fe7950930df6a9251184ff8a518982f7c92b8c617ee295d650affbcea8b1ebf484684c377acb242e3bdd518e160aff3ca85286df41458502f7c92b8cc17ee295d5639fea4a51184ff965489827f8b2944619fd639e1429fe2ca31186f7506385835faa2342613fd2946230bdf24ae2a84ff165789837baea1c2c13fe194a2609ff3cab1184ff626759827fa33ac4613fe595e2609ff24a51186bf504684c27fc92ac4613fc59462609febceb1186df4d4584867fc32944613fd39d61219ff0caf1305ef925715837ba841c2c13fd5946260deeb9470b06f754a385827fcb29446177c59486509feaca51304ffa25518c37eae28c4613ff0916121ddea9c90b8def925714c27fb133ac61afd721a130d7ea90d0984ffa25219827f8b2944c1bdd548e160defaa470b04ff427584877bceb1c2c1bdf510e1609ff3cab1305ef925719427fb13a8c61bdd740e160defa9070b04ff965788c35faa834261bbd6392171d7faa0d0986bf9d4684c27fa33ac4c13fc59522309ffaca51184ff4e4584867fc52a44c13fd89d5260df6a9251304ff8a5488c27fa92ac4c1bf551462309ff3ca31184ff925289827fcf28c4c1bdd710e160dee90870b06f7544385837ba821c2c1bdd720e160deea9070b06f7550385837bea81c2c1bde750e16097eb48b08867bd487850a5fed22c2417b4495c75197eb48b090cdf96528442bd8f2a12413f419523509fa8c8b0904fd86548d4a3fef22c2217b4495c51097fb48b090cfb8a5785476f20a2c2212fd69161208febc8b0884df165284427f2122c2433f419521509dea48b0904fb8a57854277e922c2213ee295e351dbc828b0904fd0654854a7be722c2213f519161108ffbc8b090cfb0a578d423fef22c2413bf49161209ef9c8b0904fd466484827ba722c2412ff6916110dba8a8b0884f7ce4584867ba722c2213bd49161219fb8c810bacfbca6784436f512a80a13ec295e3518febc8b0904fd464085d67ee33242413ec295e1508febc8b090dfa0255248277a922c2213f619521529f714af1a84fb4a4085527de522c2213f619521509f694cf0884fec24584867de52042a93f419523529fb8c8b0904fd86548d42fe012a8a21b751516121db6928b0904efd24584867da522c2213ec295e1519f6948b0904f74e4584876da4a2c24337a8954050,0x1a31a95ff86575583feaa290ac17fd7954660dfebaab1185ff165218c2ffa333ac617fe2954530bfe2ca43306ff5d558982ffc32a92c17fe195d530ffaa8a42985ff46675982ffa53a8c617fd79d4560bfe94ea8b06ff509588c3fdaa490c617fd29d4660bff0caa4986ff58e285477fa84ac4c1fed5248660bfebcea2985ff4a7544c2ffaf2a8ac17fe195d563ffab1aa290dff16521582ffaf2a8a61bfd6386152dfeba2b1185ff466755837fac6bc6a37fd29d5163bfe2ca42985ff4a7515837fae8ac4c17fd199d530ff6a9242b06ff5c5588c37fac6bc2a37fd29d4530ff6a9242986ff5c5589837fac62c2437fd199d563dfe90ab1186ff58d28d477fa42ac4c1fed6354921dfe8aab1186ff455589837fa82ac461bfd4156260dfeb92b1186ff495588c37fae4ac4c1bfd2556260dfea2ab1186ff51558982bfaf3aa4615fd79d5260afe3ca851867f5947850b5faeb342615fc7950a60afe3ca84a86bf50a684c2bfaf3aa2c15fc7950960afebcea8986bfd46684c2ef8b2b82a19fd531e142d7eba4d09857f1e5424c35fea5342617bc495c630dbeb2cb090eef594485c6bf8f2a14a17bc495c660afebcea8b1ebf5c6684c33fac63c2857bc495c550df6a1251186bf486684c2f7e933ac617f41952150dbe82cb0a05fb8a578542f7892b8ac17ec295d630bdea4ceb186fd5c518982f7e933acc17f41955230bf614aeab2dfd865548c35faa334261bf56506154bf614aeb305ef526759837eacb0c2a9b7d3596121ddea9890b8edf41658482fe832aa4c17bc495c530bfb0caa9306f75d6385827faf2ac4c13fd7956230d7ea0cd0984ff16548982fd852baaa13fd4956230bbf2ca43284ff627529827fc32ac4c17bc495c650bfa0ca8aa84ff4a7588c35faea342617f619515509ff44aa5185fb4275250b6fa0a2c221bdd428e160ddeb1890b8d7fde7548c37eaa28c4c17bf499d5609ff44aeb304ff42458486fd852baac17bd499d560affbcea9304ffa25758c27feb2944c13fe1956230bfa0caa8b04ff8a5188c2fdc52bac61afd421a1309fea4eb1304ff527588c35fae5342617f61955160d7ea94d0985efd26754c2fdc52baacb5fe7950a309ff44aa9305fb0a57554efdc52bacc17ec295d530bdea4cea986df416584433facb3c285bdf518e1609ff14ab1305fd0654554f7eae2846a33fe8954a60dbe828b0905fd065544c2fec32a2aa75fe7950a60bfb0caa8986f75d2385835faa9342613ff09d6121defa9470b05df965785427faf28c461aff549a130bf614aeb286bf9d6684c2fdc52baaa1aff511a130bfa0ca8b285efd267558f7da84944c17f619516509ff14ab1184ff427584827feb28c4615fe79509509fe84eb0886bf5d0684c27fad22c243aff521a130bf614aeab1def5267558ebfef3aa2c13fd594a2309f,0x39a7b333e644cc5798232e3e5a4cb03957b29de522ca1393c3266e4aac90f91bb225e432c83390031e4e37ec6538b7b149e234c3bf86f30d1e162c29383d305ee07cc0b38062fe1df6ebe6f7bb2f55de4cbc3f77f2ed8dd5cba737392e56dc58b82f6ee2dbbdb0eb5af6ad2d34da14b36b65aac8ad8cab09b600abd6d776ae6b5baab40d640abc3565aaa0d500a9cf5222a0fd3e8a7774cfa96ad294a47f489a8e8d172a23b43ea857d08ca083402a7dacf6a9e173a6272bce0c9b8335da68bccc29903317a604cbd296e72ca2582cae2951b295a4fbc9b692af23e2447c84e902f1f323c0c72c8d8719e2320c5d88b1b1532280c4ac8913119a212c3c686e30cc217cc2b884b3083a0d2c14681f702ea04bc04c7feefe89fabbf027d5af9b1f01bda47ab2f4b1e70bc967896ef89dcbbb56762aeba1d62ba5c73fae679ca4b8ea713ee1f1c09b7aa6ee6dd69b82b6e26d56d981af1b57a6a5ed369a38b44e67f2ce919b1b34a65eacad1934b250640ac7898d0b14c6216c2b1830b00c5faabe797a4af1c5dcaba41713adfa5b22b5e168cacc458deb0195d8ab525622aaa1547aa3053f2a7094c5a92251aea1b9411a7d84f6a9e713b2a7064dc69a3931ca5da4af69499281a4a448c691291faa3b446aa8bd9146a24c441686610a6a0ee41328188ffc9fb83eb27c38f619e963c9677d8eee9d923a8e73a0e629c6638226fb8dd19b58367e6bd0d6d9aa4348a6798cd7996e321e6310c3c98242f8a5e38ba1970c2d6e5960b0695b82a7653e8a48944627ba4e7098f92c024ae47e08cc913a21a241a07ff8fb41e6e3c0075a8e601c16368869c8cd0190a31105f28b9a16762b485398a2813ce26704a388f2114e21c041787c60ef61ce837786b80cb218b02e185640a3212c023c8438079e0de819c82da04f608980d4815e021202d002a8000bfea4ea5185ff52752982ffc92a94617ff5948630ff7a9285185ff92552982ffeb290cc17fe5948630ff7a9285305ff96521983feae3a8c617fd4954a30bfea4ea4b07fd5c751982ffa92a94c17fe7954630bff24aa4b05ff565218c2ffa93a92617ff5948560bff3caa3307fbd4942582ffab290cc17fe5948560bff24aa4985ffd65214c2ffc52aa461fef5250930bfe8cea5187fd5c7515837fac6a46a57fe5948530bfea4aa4b05ff8a554982ffa33a94c1bfd6392152bff3caa2b07fd5c7514c37fac7ac2437fd4954930ff6b1ea4a15ff565215837fac72c2437fe7954530bff14aa3185ff565214c3feac6b8ea3bfd6352152bff0caeb185ff8a554583feaa290c617fd19d4960bff14aa3305ff86575983feaa290cc1bfd639e151bff0caa5185ff8a5544c2ffa33a9261bfd6356121bfebcea3185ff4a7548c2ffc32a94c17fd79d4660bfe94ea9305ff5e5518c2ffc52aa2c77fe2954560dfeb,0x63734a40edb9a0ca51a06438dcb3b664b9a4d28cd6590636fc831c78329466b2c6df90638f06528db659cd36ec971a8e5390c350cc3b9a2830b2892d07290756dd6178d283104cfb6c48a13e41d6124cd7285c3710283b6c4b9ac399747294861610e1dcd76d496189eb08e841b6c3022c2cfca720c6c451016f866168e50a528710e6b0bed82263712c3206672847441887585b9b94e40a0c379a6db0c289b7c2d5d612506b3586043859ca0c3710edb9ae51acc39aec49449735ca75810d6e6e50a2e430de690bc3bac827b6430216729c6e208676c506258594296493d2830dc3394eb30ec2ca2572948043cd6174976d8661c9e6b94c43acc3b0d283b6c493d6729c831b9010c5be1985a58e4f8a0c430ce53acc4b0b285590125ca71b5bf35d661985912aeb0a0c37b6e419a2899bc330b57284956fcd44186f587e50a1e3710e690b81bacc4bb6430226759ca31a5b8445e6b0de40a04cf0e288e00f2085a1dcd218511408e50a0c37ace6b106d9b747295b7351032110f1b8656f85ab94e34a0c439a6db0c285b7c2d5d61418876dc6b3450b3786616ac43b6e34a04cca1c48fca11c5be16146186eb38dc410b28312edb0c2853c814186f3499e1c511f9428390c2d0ee6809c30a24e21db759cd14186b28cb61d892bace430d42f0ec339a280a24f6d8821dca624507587e698d8488ccdc8b3729cd32185d6e1361870880bed80c09828e68214759cd7291061ac856d5ba3942838dc311ec2ca13a7a4666e458805e518dc2c282df0c3759cd728c864044f1b8656f85ab9a44b0de53ac2830e3f6c864241380c859b94e430c28138c2ca2391dca7585b8445e538d882b7e68928870cc2d31b918458564eb394edb9a2819064b0bc330e511d90729c87585be198590c9e539a24ab7c2c26c30fca31788734506258776cc661aa8dd902308b838bd672988440c696e6e5310e68a0ed98dc4b0bc318e5729c8440474445be1985a39a0250c0960e42cdcd729887588700250625db27942838dc2fb644b0c018a14e1b8876dca141d6334cda39429ca26430de6b0b08609edb0cc399d6735ca3215b0435b9c02e34a042d12ed90c285186e2050735db624d7e1c8e530d00b0ee68a044bb6eb12117340584ddb050060428ed13d99bb1cf616ebe7d71bad1f576eaa7d49ba81f4cce953d21ba27f422e7ffcf739dcf396e6d3cd43996f30ae5cfcb13950f288e4cbc933914f206e39fc6b38c4f166e287c4ab883f0d0e16fc253838f04ee057c0237f7efb8df2bbdcb7a2ef22ddffbb73757ee8cdcd3b91b711ee00dbbbb6eb6cbed74daa3b46b67becd4d963b23b63aec3ed84baf935e0eb9ed6bbad13590eafed5cbab0b54fea7cd4b3a8db504e9e6d387a6834bee950d25ba42b469e8b0d12fa183414e806cfc79f033cee77ace879c8337ee6dacd8,0x79082883eda2e2268ee69196414d072841913cd51d97260acb18e6df94cb8a83e5999e0e3c50a1e3486a4b9a4b8a0eda905215c865841f6dcd113477299728a0c50be23b2e2e678389a0e360a8b889e6ab72490479135b0eacc520b6f5922e29c811c5bd349710c7cb0a2e40a0a372e22794eda8ee690a662186b58d73185076d87625cd290ae6a8e4bbb6a48a93e284965d85d6fcd443c6a19082b2c64b2eedb94e68a1a39582629998d8d6422eeda0c63992e690d6319ca625db61dcd35c8648a12e0bdcbb94314e510b9421bace40b7c330b0a90ca46f8835d073166828838b8892868ee68f8266626820a21a2eed89220ce41975468cb7a371428492cb8c4971b1061910d6fcd6168cb0a06db07ccb0434175631ac87358a76cc732496b237e530d6ba12630ed045cc6f6dcd31dc841882dc22c330b238b8d000502188594b7a370a2872ce5092cb919660f9960842f98e27a2e288b056584316f97729c811c8a438d20e2eeda0ce6a92218a25358c3b64c21083e422e8339a287b62268ea354ce36e282eac6818de4314edb9a6392c8414c951dcd45ddb1428a34b7c83acc3394c2c924341c6e590573444e5d5bf28492a946db2c8339a6dd92e35197659ca147db7354931d05260a29a2ee69b7648d5b65850f1a497355be5dca214a294a1171b9641444f355be5dca12498298e6de2e2a0b56628ce408db960a639b78b8a82907c87350b76c44d1d0594346aa0ae34a18b9b7e69923e2186940d7316ca76d87625cd298ee6a2eeda9228e0a3b28c5f358976cd761c72248fad8799e0e2cb20c6fa94638a50c159651c41913cd65dca25b9621b71b4117321db325cd71b06238d828838ba92edb9a2191cd24146d214752586617db260acb083218a2a4bb6cbb944e29c8107db112977354720bd285921e2186b1650735db624c661c965237c35ae8498b3609998b14ad8a12492ee36b7e690c4628dcd590236e682eac68190e3714ed992e69285659ca51dcd65ddb52454a69020f8dedb9a85a9221a0b2894cd45d0636fc831c68322e669b7e418e362186b17ca14187735db319d6624b8322e6db9a6dd92e34f06528d0658c6f6cc7721cd260acb0a6e539a6df2e64905b8438661649171428b90a3bb62279a4b8a0a3554a3119637903b0a6832946832c64192edb9ae3530571a44c5d5bf34491eac66b1482db7e418e3b58c3b64c2120bab19ac51b7e418e3c175636d8a734dbb25c6a0a52844d04145bf204745c431da082bb620e928b8863b28c5e2186e25cd76cd761c924486a6874d65847145c816f977288525a082b2ecb3b62488620d14d122430e0acb0a8639b7cbb943b410573517112471067620ba16590531cdb951ca65c7620ba152996418deb2458329463590e6b2ced98e649306528d031bc8659db734c72694cb19c81db72b119,0x5010dc816f971e2e6818dedb9a63b908310c651bc846fca35c911f0aa832c642b6e6888adf94e3489cb998514196125ca171971dac6320ee4237e51ae48918861aca35cc59421c369a6ba1262cc1140dc6e2086217019f2ca698dc2aa02df94e4086cb958592546e675b334623b2ca830a21b902df94cb92db45d06734dbb25c69e0acb0a6e69b7cbb946490534151736fcd3246671b7134196415c811c5be5dca10c9adb0b6430ceb2b7e6b94e362151510531cdbc5c5a3422c330b265850f1a5052197525ca10dcd76c85320a6372c28fb629b9a63b94cb9410d1a49335866166c2f0c2dd8deb394e4222414e510aac6db1482f9a6dd92e35185c404716fd6619ca721112714e3483eda924bb9a21918766e500e09e4000c350c42c213c18df31c36b336c369a6ca12630e506284717d9715a082b2ecb089e688e20d05065983f284917b971d0ae372ce6889adf2ee50924e1bca62050734c5b19db625d661cbc1c88ccf2c642b636585060fca1245c65c7c2b2c2808ee50becb8f8a71a44a5d5bf34491f2c829a0e5083a4bb621b2e4c14c6947db14d17734c72085cb29ac1f33634c41975468ea024b14e3489e6ab7cb918a416df558c7159a82b2c639b7e532e28b904b350531d1736e5172076e5886dc799e59838e2e68190ed992e6b8d8310506284917b97172c24b2ec32b7e6b948878d496f486285111d971aa0cb390238b7a6b2ee50864e295b6175bf1bcd65d10b209a8092cb30a2278de6ab7e532e5608446678a3215b1b14280922e32e284304f2186a1885c0676b237e53106ba0e630f0645cd031bdb31dc8734882990cb0a3ed992e68a8e532e562985e5dc816f1131a7e6a206d9b7648a8571b96107db7354910dca65ca81b8d003104310b088e42e098a53599b1a6c508ecbb0b2de22e40e5bd2185145967284765c8c1314ccc6de310c28e2e66a0c6df90638d8861ac5941cd76d8931987260c8b9a064192e6bb6e35185a418656c49112664a2e284b82f4b17418cd36fc831c6adb8d88190adf0ce6b0b885317418db734dbb25c69f0b88092c33acadf9ae538d885505d58d0628c6f6cc7721cd27908818d2df0cc2e223e585033583e658218be2898e191dc84405bc458661678299028fb664a2ee68a8462050e25db2168600dc6a1a082b9a20c898ba8e3d205be41d6619ca61647230d28b9a42c094330ee411563118a3790230a663310c35ace5312edb0ee69ae5417563418a320c976dcd71a9c5190adb32c1c88c10f9660f9960842832cc1f942f88ecb8e51415db1074945c431f14a688e288b7e412e3e59c841441d1ddb113cd65dca2b142169a63732c1f043b1c4f17c5165dca1a0a8b8b721b90238d9660f996084831bd64879671b05107db525cd10d97728a82b8dcb0a16df9ae532e6493ca113c6f595be19cd616202,0x2af14614655e58c28d85a409dc5098a614d00cbe683141b0b4813b96132cc29a01926516298510be6832c1926516598512a02f714193c5f182416285c1f2cccc75017b960c9e2f8c120b2c2b11469758a1333cb30719538a1043c1314ccc799e59838d88a34bacb099617c22a72c20879660f998f33c53041e678a608328b1424478a17c22971428479617a261dac6c878a609998f07278beccf2c29459612232972c2846d9358c38f33cb3071e285e89b26b1871e084f17d99e2858f9ac165983e6636b1876c8799e29820ca5c50ba1e298266638f5ac130f1f358d943c52871423c79660f998ca920690c5099660f998ca5cb0ba19439611e32a481a432c2364d630e329f1427478a609998f14c13331b58c3b64330314620653e28510ca7cb09d198196310329f2c28865c17a609038a172cc1f321e5983e6636b1876c879660f998f2ca4045c17a609039615886d84d051b4865d8662862971428478a609998da0a3690c5b0bcb0cc436c2cb307ccc78a609998f14a40452e58508ca7c50a21e0f966663cb307ccc6cd144df0ca920a8dc50853e58510f14c13331b58c3b643668a26f865490546e584c1314ccc78a609998f072e0bdccf2c2e5983e643c41ac162d46d2197e585c10b82f733c50ad630ed90db6621bc1e5983e66361dac6c879660f990f2ea3690c5f142e5983e6636d9886f078a609998f2ca344db142de8d878f5ac6ca382e29826663c528d136c50b7a36b1846cb0dc418c365983e643640a22a46d630ed90d90288a91e1ad608a1634450b1a2669856706cd30ace0db6621b91944c809b6621b91944c809856684c2b342283142788ecb8b851419613dca11d971e9a23b0aa41b628b2ec510116215b35dca41cc61e2e6da0ce69b764b8d3d34476154836c517299665c923822a43acc3394c2db64418df31c3ccf0716194d11d99d20db1b04ccc517418d031bdb31dc87348ada0b0020c480a116215b35d0731666f188614785d344752199b6c68ba0c6819064b9aedb8d41258551acd56c50e5d8a2310c35ac6b98c284386d34d772909318708a90239b6c330b361546e58cd1255b143ca65c9cb307ccb042418deb2436b31ac42b66ca0e630e10d1a49335d6619ca61682f8a263871731ac876d0631cc97348283142f492cb8bca7204316f86759858568c68a08390c42e06372844f1b5bf59867358587e9c328d24b33ad99a3629503215b7344456fc69139728a0c50922e32e297a50b243c2b2c280bde5092cb8f8a534c6d405bf204365c8adb0ccbb8de6ab7e5221641247629][i]?.getD 0
def s503H8 (_ : Nat) : Nat := 0x22036e8e044a2c000e55b28000000000000039b8000657d1468eb12185b04bab73e223005530c5d0f60007050c79d6e42c00000014d8535651000064d644f544bec9b348a00003dbddb6b6b8b70988a9cc400021f000120d45abae0a52af0c5c8003a1ca88f668000000e2eb847c4f583ca7b6574f38ee63bd49f2512504bf74380009032daa6d8bb285e87a74b00021bda80163000000000090dd40c190ac900002685d590f231c94792a071a919aa702bc27f7f629400150cf2d41e065f6f953ee89000106a4959065a69e9120000024a76a3000285f42c00068c942c40cd07439812e98a0003086813615b3d4610160000034f73bc1a58763c0005bcd886712c18a2be94361ad5d00019ba8d674c5a3463800006a24920ea0008493a7c9dde1f83272744e9d226382aa80bd24f79c54b0000a18000000007df1df662c0b1a0527c70e8b5a55640a88713b08ecce674abd50a511b4425a660f2a8f18248536612fa514e1a78cdf15b02aa1515de4df329ccb5f972db10211bdcac09a77e0ad631ccb99d5ac2612305999d92a1a3ca40117aac0ec33789ca125c6b6e030118499382e6d4dcb9186731af63a985581a59f9da17446c12120ea172c73ad7f5662795e3adf39774350fee67c0754538fc460f21207359f40f15dc3c9162a4cb41ab4e5c746f06c10aadf1cfdf4742f1c3d482936d8fd90d037d5ecbac0012e2f22d9a2d5b0b4d59417f403c25b5f2158a40d31569302e8e5448a8ffbdc00032566a9a24000e30a313a301fe83d401d3d00d640c820b8e3422e327098cd9d416b3000108c842a07110b021b2c0403162c03030000020000090b02010000005006053500090416021b2000034601012704000003080006012a28050c0300000c0300025c3600490100d801040017050517170006120c0935020e092c0b501202000004131c0002000f097f14080f5e070e00
def s503D8 (i : Nat) : Nat := #[0x89d4630af746a758e160cfd58c1952352af79e9510e160ddb4945948630abf169211a1309efd285948530af74ab518e1609fb0a97954530af7569210e160abf46a751a130ddb4945948660ef3549218e1608ff62b5948630edd58d1516121abf4ab511a130afb8a97556230ebb549211a130cef58f4916121a7f9e94256230af78a9540e160af746b520e160cfb58c295e151afb8a97556260a7f9e94256260ddb4945948560ddb4945948530af78a9510e160af7869750e160ef5545210e160edb58d2516121af7869520e160aef9297156230af75eb510e160af74ab540e160aef9297156260af75e9510e160af7169210e160af746a750e160af74ab510e160ef3549210e160a3f5eb549a130a3f1e9429a130aaf129719a130a7b1e9424a230aed1297146260aafd2a759a130a775eb548e160abb0a9759a130aaf52a759a130abd069549a130abd869549a130a7b42b521e142a771e9428e160cdea690516120cde5950916121a3f5eb541a130c9f4d56916121a3f1e9421a130a3fdeb549a13087f5e85946260aed129714235187f5e8594a260abb8a9759a130a7b1e9424a260a3f9e9429a1308df9692946260cde4d509161218fd8694956260ae7129718e16087f5e859462309de4285948650aaf129711a1308fbca8594626087fde8594a2308fd468594a2608fdc68594a2608fbcaa794623087f5e8594a2308fb0a979562608fd06949562608fd86949d6260ae7d2a758e1608df9692946230af30a9758e1608fdc6a494a230ae752a758e1608fd468594a230aaf929719a1308fbcaa7946260af5069548e160af5869548e160aafd2a751a1308df16929462608fb8a97956230cdea690516110a775eb540e160abb0a9751a130aaf52a751a130abd069541a130abd869541a13087fde8594a260a771e9420e16087fde859462308fd86949d6230a77deb548e160aed1297146230af38a9758e1608fdc6a494a260a3fdeb541a130a779e9428e1608fd86949562308fd46a494a260abb8a9751a1308fd46a494a230a3f9e9421a1308fbca859462308ef52859462308fdc68594a230cdd4545946230cd75953916121ae7129710e1608fb0a979d62308efd28594a2608fb8a979d62308fd06949d62308fd06949d626087fde859462608fb4a85946260cdd45459462608efd28594a2308efd2859462608fb0a979562308ef528594a260ae7929718e160ae7d2a750e160af30a9750e160ae752a750e1608df16929462308efd285946230aaf929711a130af5069540e1608fb8a979d6260af5869540e1608fd06949562308ef528594a2308fb4a85946230cdb494594a2308fb4aa79462608ef52859462608fb4aa79462308fb8a979562608fb0a979d6260a77deb540e160af38a9750e160a779e9420e160cdb494594a260ae7929710e160,0xabf929529a130abfd69219a130ebbd49429a130bed12971d4630abf969219a130bed12971d4660d7bd487950960ebd5c7519a130abf529529a1309fd86949d4a30d7bd487950930abf9e9519a1309fd86949d4a60abf569219a130bed12971d45609fb8a97954630e7b58f521e1429fe4285948630abf8a9549a130abf46b529a1309fb8a97954660bed12971d45309fe42859486609fd86949d4960afb62b5250a609fb8a979d46309fd0694954a30ded58c495c7519fb8a979d46609fd0694954a609fd86949d4930cfe5a909161219fb8a97954560abf8a9519a130af752b528e16097fde859486309fe4285948560abf869759a130ebd545219a130af7929528e16097fde859486609fb8a97954530cfd58e1952352abf52b521a130af7d69218e1608ff62b5948660abf869529a1309fe4285948530ef3d49428e1609fb8a979d4560abf929521a1309fd0694954960af7969218e160abf5eb519a130abf4ab549a130abfd69211a130ebbd49421a130cfb58e295e1519ef52859486309fb8a979d4530ef55c7518e160abf969211a1309fd0694954930af7529528e160abf5e9519a130cfe58d0916121a7f1e942562309ef5285948660afb62b5250a309fb0a979d463097fde85948560ebd5c7511a130af79e9518e160abf169219a130abf529521a130a7f1e942562609fb0a979d4660abf46a759a130af7569218e160cfb58e295e35197fde85948530cfd58c195215297f5e85948630abf9e9511a130abf4ab519a1309fd8694954a30abf569211a13097f5e85948660ebb549219a1309fd8694954a60af78a9548e160cfd5c589d4660af746b528e1609ef5285948560cfe9a90916121c7f58f79161219fb0a979d4560abf8a9541a130abf46b521a1309ef52859485309fd06949d4a309fd06949d4a609fb0a979d4530aef129715623097f5e859485609fd8694954960ddd4545948630af78a9518e160cef58d4916121aef1297156260cfe4e90916121ddd454594866097f5e85948530af7869758e160ef5545218e160cfe8e909161219efd2859486309fd86949549309fb0a97954630cfb58c295e351abf8a9511a130af752b520e1608ff62859486309efd2859486609fb0a97954660abf869751a130ebd545211a130af7869528e1609fd06949d4960af7929520e160af75eb518e160af74ab548e160af7d69210e160c7f58d7916121cfd58e1952152ef3d49420e160abf869521a130afb0a975562308ff6285948660af7969210e1609fd06949d4930afd0694556230abf5eb511a130abf4ab541a130ddd4545948560afd8694556230af75e9518e160afb0a97556260afd0694556260ef55c7510e160afd8694556260af7169218e160af7529520e1609efd2859485609fb0a97954560abf5e9511a130ddd4545948530cfd5c5,0x75658dc176438a178a041c5020072c0d8d081d60400b1a175810000eb020072c0f1408016402eb020000003706f45a52c6e0cb21cb0a0058d082cd18eb21831db14c958dc18e6adb145118e76d2408284c939a91a4340e6840310e42db0c1668c2b8d183076b63403b3463ac860c76c5045c4b880dd7387759edb87712f347341c2b560dc2394118eb2182f5659a76dc50e681db081881cd1921a9e0805118e76d2408003ae729edb87712f346058dc18e6adb1922834968ef344818630bf6c7b1b82f561927356db8a1c0014521b4838d20346b90129e0b900b8d080d039a100c4390b6c3d20e344014521b4838d20346b90159a30ae3460341ab1cd70a268d143edb471000878770d19a0e15a5078138a6ac720622db18d070ad58330bc535659ac08e34dc53026ac180c7590c19a52cd3b6e58776c101a076c2142649cd48d2034838d11a0d58edb8510000714c09ab060e29813560c0ae02014a2044e1dd60b0672cd2864ac6b9ab6c7b6c621c80dcd041668c2b8d1d9a30ae346ed83a35c8489142414a2044e68207201000d0694735c28981f96694720622db18d070ad283d1a287db68e2038a604d58330bcb34a59ac0ee34c0c0fcb34a0dc6841a35c8489142414e208405701002db1887203341a51db70a272cc0fa507cb303e9418a71042e5981f4a0f1578a6c45e21b103871c2b614706d831c10e01afed7f1bf65f72faf7d2be15ecaf2f792bc6ddf6ef175dba6dd22e71728b8c5c22df16e8b5bda9ed4569db46d9cacdb65db2c5922c71628b11d87ac33614afcd7a6bb35d4ae256feb755b5acd562aaf556aaad552aa7552aa87d3d29b34bea5752a6933489a3cd1d287141da014fca7db3e89ec4f227713a89d1ce7a71d3899bccda66b33549a7cd2a67531f987cbfe5f52f5972cb5658b2b594d4a2a4f526a932c9564752098fcc7a63c91d48dcc6a63331898bcc5d22df1548a244d225f11f88d442a20b10087dc3821a10c085842ae14d08b83dc1ae0cd06182e413208f02c813c08a02500d7e8bed9f4cf967bdbdadeccf617a8bd31e78f007783baddb6ed6768bb05d62eac74e3a5dd24e8273939b5cd0e63729b939c92e39714b891c3ee0f6ffb7e9beadf06f5b799b96d8f6c53615aead7069a33e198ec9663db1d98a0c4b612b0817f4bbe5cc2d19640b05559aa61526a6d52ea96144ea2250ea7593a29954c824f91d88e747122c5158891440a1c50c285c420a0f102c7fb3fb1f14f807a53bf9de8e927183899bb4d8e68032d184cbda5e82cb1618b0256629a94c0a2a4e426f93689aa4af25512108fe46f235113c8683e21de0eb074e3811ad8d2c6342ff1778ba85b42d51680a7c4b023210087f03ac18f0c505902a814f08f040c1fc0ee074839017c08d033810404c000d7bd487950a30abf52b529a130d7bd487950a6,0xe28e8040e58e804001be0f14d402072cd40201bd099e37c2e281003960400e2817581615c5040072c0818572c172c0838a078a05d607960796078a05d61b3940e1c9cb02007140f076662059008396078a05d604000038233311be0f2c0839604000714c08237c17581e281e28137a1c081e28133c6f846e0de89d638710a2b202e58107140f2c09bd0830b60cc5d636c814cf1be10a2b202e581001d6078a05d6078a0400e281072c0d8d0f2c08000e581758e1c4eb03cb02007140f140f2c0f1408a1b1a2e581e581e28103ac08a1b1a27286ce50384272c0f14082c805ca38417140f140f140bac0801c50d00b96079604164020e5810001cb30389d605d604df0400e58680581c3c5020003960406e0de880037a1060cc5d85ac6d90299e37c2e581e5813706f45c502003ac0838a][i]?.getD 0
def s503H7 (_ : Nat) : Nat := 0x81410692372ad0e63ca0012a48f90de3dee1570a457b03d09e82e7d2728e823097e4015d8ec5ea6ce78000222b55df410001200073794a098e70b3987a5923ec27432ff0c61996bcf04a7c94116c922fc4d554dba379772be1900540f62a3000000660a9c000220002e80021ae1400c4080000162726a0735022dc252c000d408702100030000046200820c1c0410204006880014091
def s503D7 (_ : Nat) : Nat := 0xe102000000000e1065c400000000000000000001c08100000000e1c2001c38d788000000000000e040800000381c20e0708000000000000000000988e040431edb01acc97059366810e63b82c930bc0806a3d9a04398ee0c24c2f0381a8f6d80d664b8309311c0e0863d4f4ecf738ccf2eca724c7f1abf6f8bceeeba6e4b7edab56d0b2ec6b06bcadeb2ab69ca5e92a3688a0e7e9b66898e469063c8de328b62888e1e8661480dfe7e5f47bdea765d470dbe6e5b46bdaa695a066d966458c61d825f57853d1a394bc21c5e0a400d1dea43d285342616ad12d71d46684c297c35a74848b090caf61b52b529a130a3db17a90f2a14c12bb8ad7a546684c257c858b490cd0984aee2b5eb519a13095e836a52a534261a73d487a50a385829bc55a6a848b090c8ff7b169219a130d1dea43d2843426147b62f521e5428c2dca25ae3a8c70b053da3b5a90916121b56896b8ea2342612af52c5a486684c257615af5a8cd0984bd61b52b528e16095ec36a56a4342614ed12d716275198247ebd8b490cd0984af61b529529a130979c56bd2a31c2c12f642c5a4863858257715af4a88d0984af90b169211a13095e836a56a5342612f38ad7ad46385825ea0da94a9470b04aee2b5eb511a130a5f4d69d2122c2432bd06d4a548684c29ec1dad4848b090c9df7b169218e160d39ea43d2841c2c14de2ad654245848655fa58b490cd0984aec2b5e9519a13091fef62d242342616e512d71d44385825cea58b490c70b053b44b5c589d4630979856bd6a31c2c12af52c5a484684c257615af5a88d0984bd61b52b520e16085fb362d242342612775ec5a486385825eb0da94a9470b048fd7b169211a13095ec36a52a4342612f38ad7a544385825ec858b490870b04bd41b52b528e16087bb362d2421c2c12f38ad7ad443858257a0da95a90d0984bd41b529520e160973e962d2431c2c12f30ad7a546385824efbd8b490870b04abf4b169211a13095d856bd2a2342612e752c5a484385825e615af5a8870b049dd7b169210e16097ac36a52a41c2c12f506d4ad48385825cfa58b490870b04bcc2b5e9510e16085db36152ea342610af66c4a5c4684c207ecd8f4a10d09842f59b069541a13083bb363d2841c2c10f566c1a550385821cecd894b8870b043cd9b0a9750e160
def s503H6 (_ : Nat) : Nat := 0xd807498021000066df03c06
def s503D6 (_ : Nat) : Nat := 0x8de6543ca14092b59c12d71d44684c20bb6702b5eb511a13082f59c06d4ad48684c303bd499b1e9421a13093959c12d71d4438583073d499b1e9420e16083d59c06d4ad48385820f36702b5eb510e160
def s503L : Nat → Packing
  | 12 => (1,0,7,0,0,1,0,s503D12)
  | 11 => (43,1,7,0,0,12,0,s503D11)
  | 10 => (347,2,7,0,0,15,0,s503D10)
  | 9 => (468,3,7,0,0,15,0,s503D9)
  | 8 => (318,4,7,0,0,13,0,s503D8)
  | 7 => (80,5,7,0,0,10,0,s503D7)
  | 6 => (8,6,7,0,0,6,0,s503D6)
  | _ => emptyPacking
def s503I : Nat → Nat → Option (Nat × Nat)
  | 12,h => lookupWord 15 56 5 10 6 0 s503H11 (mixTag h)
  | 11,h => lookupWord 116 395 8 13 9 0 s503H10 (mixTag h)
  | 10,h => lookupWord 156 528 8 13 9 0 s503H9 (mixTag h)
  | 9,h => lookupWord 106 358 8 13 9 0 s503H8 (mixTag h)
  | 8,h => lookupWord 27 92 7 11 7 0 s503H7 (mixTag h)
  | 7,h => lookupWord 3 14 1 7 3 0 s503H6 (mixTag h)
  | _,_ => none
def s503 : Forest := ⟨503,12,s503S,s503C,[[]],s503L,s503I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs503_12_0 : block s503 12 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs503_12 : block s503 12 0 1 = true := bs503_12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs503_11_0 : block s503 11 0 43 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs503_11 : block s503 11 0 43 = true := bs503_11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs503_10_0 : block s503 10 0 38 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs503_10_38 : block s503 10 38 187 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=5)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs503_10_225 : block s503 10 225 122 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs503_10 : block s503 10 0 347 = true := (@block_merge s503 10 0 38 309 bs503_10_0 (@block_merge s503 10 38 187 122 bs503_10_38 bs503_10_225))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs503_9_0 : block s503 9 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs503_9_1 : block s503 9 1 71 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs503_9_72 : block s503 9 72 266 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=6)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs503_9_338 : block s503 9 338 130 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=5)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs503_9 : block s503 9 0 468 = true := (@block_merge s503 9 0 1 467 bs503_9_0 (@block_merge s503 9 1 71 396 bs503_9_1 (@block_merge s503 9 72 266 130 bs503_9_72 bs503_9_338)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs503_8_0 : block s503 8 0 117 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs503_8_117 : block s503 8 117 201 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=5)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs503_8 : block s503 8 0 318 = true := (@block_merge s503 8 0 117 201 bs503_8_0 bs503_8_117)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs503_7_0 : block s503 7 0 8 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs503_7_8 : block s503 7 8 72 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs503_7 : block s503 7 0 80 = true := (@block_merge s503 7 0 8 72 bs503_7_0 bs503_7_8)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs503_6_0 : block s503 6 0 8 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs503_6 : block s503 6 0 8 = true := bs503_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts503 : checkedTables s503 12 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs503_6
  · exact bs503_7
  · exact bs503_8
  · exact bs503_9
  · exact bs503_10
  · exact bs503_11
  · exact bs503_12
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs503 : graphValid s503 (boundsBefore es495) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls503 : Lower true (vars 503) (graphGoal 503) 13 := lower_forest (g:=s503) (i:=0) (hints:=8590984788) (before_sound es495 vs495) gs503 ts503 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es503 := extendKnown es495 13 [(503,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs503 : Known true es503 := extendKnown_ok (m:=503) vs495 ls503 (by decide +kernel)
def s507S := sampleAt 248 #[(0x1007801261580007e600004044300009000fffd5b267000fff33cc003ffff,0x2800221584482e61140000410089908a422c0902308a08b11cc2495093),(0x69960063886000667800008180cb000e000c002a4db9fff000ccfffff3000,0x299600228862c1e678b0c000804b585e586d618004a9587586445561f358a),(0x0,0x0),(0x8018498c118000787ffff326270c000ffff000338e3e000000f0f0003c000,0x488411800da82a03f122250c01db01f007b38e3e02e02ef0f00dbc03a),(0x301e071f01e00007f80001c38380ffff00000003c0fc0000000ff00003ffff,0x100a071f01e01897d00629428280d31603140c53c0fc0324324ee00c92a32c),(0xc0e007e001fffff8000001fc03ff000000000003ff000000000ffffffc0000,0x402005a0013881e0000071fc03fb005800580163ff000068068bba81e00070),(0xff0007fffe000000000001fffc00000000000003fffffffffff00000000000,0xfd0007fdd4005180001461fff4000a500a502943f6b54a70a7000029800a60),(0xfffff80000000000000001fffffffffffffffffc0000000000000000000000,0xeff5d00000006100001840ad5d2e2c604c60b18000000c40c4000031000c40),(0xfffffffffffffffffffffe0000000000000000000000000000000000000000,0xbfdffa57bec77e057d5f800000000f800f803e0000000f80f800003e000f80)]
def s507C : List ColumnInfo := [(0,2,409,608,9),(0,128,354,537,7),(0,256,211,552,9),(1,0,506,512,8),(2,0,505,512,9),(8,0,499,512,10),(16,0,491,512,10),(32,0,475,512,10),(64,0,443,512,10),(128,0,379,512,8),(128,1,298,592,6),(128,16,362,513,6),(144,0,363,512,7),(256,0,251,512,9)]
def s507D11 (_ : Nat) : Nat := 0x1d97601090ff
def s507H10 (_ : Nat) : Nat := 0x6fc03234
def s507D10 (_ : Nat) : Nat := 0xac297b0d3d96155852f6977034aab0a5ec34cbb855ab0c5e891f64aa56e3700ffcc1ff183feb07ff60
def s507H9 (_ : Nat) : Nat := 0x2afd8229004cbd7c71e608cb23b80447
def s507D9 (_ : Nat) : Nat := 0x474e1a2d97bc6faab4275c38076cbddd5b6b871be84e5ea70d38df6d43251b6ba71ba44e08c34276d72f770d3c6fb13eeaa648c348f7d695b2f78571beda13abb8230d37db8cbd0c94e1a13b6b97bc069df6d7de10c89461a13bebc65e869aca718da01731915711b398ab1c03b003f78e160bfd68983be58060efb609827f5e060b7d58182fdc6060bde385827fde060bed28182ef52060bf518182f74e060
def s507H8 (_ : Nat) : Nat := 0x906bb8445
def s507D8 (_ : Nat) : Nat := 0x1162e1d0576f1d797dee9077edd7ef8e1d3923af0e9e3b8ce5f5186fef47a01eda3958060d7d44ac0304f78e5689825f512b00c1ad9604e060
def s507H7 (_ : Nat) : Nat := 0xa07804c
def s507D7 (_ : Nat) : Nat := 0x3582ec1760e9a0cb6a69604e060cb68ea8958060cb68e68958060
def s507L : Nat → Packing
  | 11 => (1,0,4,0,0,1,0,s507D11)
  | 10 => (4,1,4,0,0,8,0,s507D10)
  | 9 => (13,2,4,0,0,10,0,s507D9)
  | 8 => (5,3,4,0,0,8,0,s507D8)
  | 7 => (3,4,4,0,0,5,0,s507D7)
  | _ => emptyPacking
def s507I : Nat → Nat → Option (Nat × Nat)
  | 11,h => lookupWord 2 5 1 6 2 0 s507H10 (mixTag h)
  | 10,h => lookupWord 5 15 3 8 4 0 s507H9 (mixTag h)
  | 9,h => lookupWord 2 6 3 7 3 0 s507H8 (mixTag h)
  | 8,h => lookupWord 1 5 1 6 2 0 s507H7 (mixTag h)
  | _,_ => none
def s507 : Forest := ⟨507,11,s507S,s507C,[[]],s507L,s507I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs507_11_0 : block s507 11 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs507_11 : block s507 11 0 1 = true := bs507_11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs507_10_0 : block s507 10 0 4 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs507_10 : block s507 10 0 4 = true := bs507_10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs507_9_0 : block s507 9 0 11 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs507_9_11 : block s507 9 11 2 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs507_9 : block s507 9 0 13 = true := (@block_merge s507 9 0 11 2 bs507_9_0 bs507_9_11)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs507_8_0 : block s507 8 0 2 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs507_8_2 : block s507 8 2 3 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs507_8 : block s507 8 0 5 = true := (@block_merge s507 8 0 2 3 bs507_8_0 bs507_8_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs507_7_0 : block s507 7 0 3 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs507_7 : block s507 7 0 3 = true := bs507_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts507 : checkedTables s507 11 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs507_7
  · exact bs507_8
  · exact bs507_9
  · exact bs507_10
  · exact bs507_11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs507 : graphValid s507 (boundsBefore es503) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls507 : Lower true (vars 507) (graphGoal 507) 12 := lower_forest (g:=s507) (i:=0) (hints:=12885979220) (before_sound es503 vs503) gs507 ts507 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es507 := extendKnown es503 12 [(507,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs507 : Known true es507 := extendKnown_ok (m:=507) vs503 ls507 (by decide +kernel)
def s509S := sampleAt 232 #[(0x20180230558000ec00c000101024f0002400fff2673267003ffffffff,0x800105590406c82c8200000245020a482483023102320883555485),(0x0,0x0),(0x5060044a6600133000fff0606b38cb003800c00db9cdb9ffc00cccc00,0x1020000a6602d130164170202b38cb09b826c264a944a909c26cccc2c),(0x8084998c78001c3fff0009898c3f0c003fff000e3e0e3e00000f0f000,0x4888c7801d4340f00e8888c2d0c03ac0f00ee3e0e3e05816f0f01c),(0x303071e0f80001fc000000e0e0fc00fffc000000fc00fc000000ffffff,0x101071e0f80219f810c10ca0a0d400d43410c10cfc00fc045114aaa91a),(0xc1c07e00fffffe00000000ff00ffff0000000000ffff00000000ff0000,0x41405a00efe87e0003e03eff00ffff01b806e06effff0001d876ff007c),(0xfe007fff00000000000000ffff00000000000000ffffffffffff000000,0xfe007ffe00065000328328fdfd00000d20348348b54ab54d6358000350),(0xffff800000000000000000ffffffffffffffffff000000000000000000,0xefef0000000460002302305757292a29c1270a70000000098260000260),(0xffffffffffffffffffffff000000000000000000000000000000000000,0xbebda577101780acbc0bc0000000000e003803800000000e0380000380)]
def s509C : List ColumnInfo := [(32,0,477,512,11)]
def s509D11 (_ : Nat) : Nat := 0x2ff
def s509L : Nat → Packing
  | 11 => (1,0,1,0,0,1,0,s509D11)
  | _ => emptyPacking
def s509I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s509 : Forest := ⟨509,11,s509S,s509C,[[]],s509L,s509I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs509_11_0 : block s509 11 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs509_11 : block s509 11 0 1 = true := bs509_11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts509 : checkedTables s509 11 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs509_11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs509 : graphValid s509 (boundsBefore es507) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls509 : Lower true (vars 509) (graphGoal 509) 12 := lower_forest (g:=s509) (i:=0) (hints:=8598353412) (before_sound es507 vs507) gs509 ts509 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es509 := extendKnown es507 12 [(509,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs509 : Known true es509 := extendKnown_ok (m:=509) vs507 ls509 (by decide +kernel)
def s510S := sampleAt 250 #[(0x0,0x0),(0xd32c0063104002ccb000c0000413003eb3000cc000926739c003fffffffff,0x532c0021105446ccb512d44800110016b3522cd488002318d48948d555523),(0x1200f0084a280030fc000fffc181cb3333c000f00036db9ce7ffc003333000,0x20050000a280d705c03640dc0814b3333c066f019924a94a419c19b33306a),(0x200309318c30003f0ffff00026260c3c3c0000fffff8e3e0f8000003c3c000,0x9108c3003750d00f003a2220c143c000e5403f8e3e0f805805bc3c01a),(0xc03c0e3e0fc0003ff000000038380fc03fffff00003f03ff00000003fc0000,0x40140e3e0fc0c37ff030e0c3a8280d403d530f00c3bf03ff00c58c5bfc031a),(0x303c00fc00fffffc0000000003fc00fffc0000000003ffc0000000003ffffff,0x102400b400e781b800006c01b3fc00ffe8000cc00333ffc0000350352aaa0dc),(0x3fc000ffff0000000000000003ffff00000000000003ffffffffffffc000000,0x3f8000ffde002920000a482923f7ea000000a8802a22db54a52a62a60000a90),(0x3fffff00000000000000000003fffffffffffffffffc0000000000000000000,0x3bfebf00000031c0000c7031c15d5f2abc2acf0ab3c00000003383380000ce0),(0x3ffffffffffffffffffffffffc0000000000000000000000000000000000000,0x2fdbfa4af7187e00aa2f80be000000000000f0003c000000003c03c00000f00)]
def s510C : List ColumnInfo := [(16,0,494,512,10)]
def s510D10 (_ : Nat) : Nat := 0x2ff
def s510L : Nat → Packing
  | 10 => (1,0,1,0,0,1,0,s510D10)
  | _ => emptyPacking
def s510I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s510 : Forest := ⟨510,10,s510S,s510C,[[]],s510L,s510I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs510_10_0 : block s510 10 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs510_10 : block s510 10 0 1 = true := bs510_10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts510 : checkedTables s510 10 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs510_10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs510 : graphValid s510 (boundsBefore es509) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls510 : Lower true (vars 510) (graphGoal 510) 11 := lower_forest (g:=s510) (i:=0) (hints:=9413555792) (before_sound es509 vs509) gs510 ts510 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es510 := extendKnown es509 11 [(510,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs510 : Known true es510 := extendKnown_ok (m:=510) vs509 ls510 (by decide +kernel)
def s511S := sampleAt 414 #[(0x200078008981558000003eb300019800000801024330000004920003ffffe231c608349d00010001fffccccf3330001fffffff,0x280008815584090016b308159840a0000002411000204c92102950816010c200148d08150814102c44473330824aaa8413),(0xc99660030e08060000b3333c0001e000001026000ccacc00071c0003300004420934d8e60001fffe00033333fffffff9998000,0x499660010a08062c43b3333c588de2c460002200044acd642f1cb21b3590c000011458a6590d590eb2191111555590f999ac8a),(0x1100780041051980000c3c3c00001fffff06038b38f0cf00007e00003c000199c71c71f07fffe00000003c3c3c3c0001e1e0000,0x1002800000519800dbc143c001bca80df02028b38f0cf00cefe0067bc033c89451451d07033e033c067bc3c3c3c036de1e01ba),(0x2001804986061e00000fc03fffffe00000984c0c3f00f000007fffffc00001e1f81f81ff8000000000003fc03fc00001fe00000,0x4882061e0003bd403d5007e0003e88440c2d00f0001edb600fc0007de1f81f81ff800bc00bc017bfc03fc000edfe0007a),(0xc01e0071f807e000000fffc00000000000e0700fc000ffffff800000000001fe001ffe000000000000003fffc0000001fffffff,0x400a0071f807e001832ffe800306801834a0500d4000f54c1b00060d003069fe001ffe00030a830a86153bbb800030c9555186c),(0x301e0007e0007fffffff000000000000000ff800fffff000000000000000001ffffe000000000000000003ffffffffffe0000000,0x10120005a00073f881bc0000000370001b8ff800fffbb00019c0000ce000671ffffe00000006b006b00d62eeeeaaa06f00000370),(0x3fe00007ffff80000000000000000000000fffff00000000000000000000001ffffffffffffffffffffffc000000000000000000,0x3fa00007fef500005120000000a24005120fdfd50000000291000148800a44176b2caaa250a4c0a4c149800000000a4800005240),(0x3ffffff8000000000000000000000000000fffffffffffffffffffffffffffe00000000000000000000000000000000000000000,0x3bff5fd00000000061c0000000c380061c057abf292ee0ab1e02498f02ac78000000000000c700c7018e000000000c7000006380),(0x3ffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000,0x2fedfd7a57df8c077e002abc2afc0157e000000000000003e00001f0000f80000000000000f800f801f0000000000f8000007c00)]
def s511C : List ColumnInfo := [(8,0,503,512,13)]
def s511D13 (_ : Nat) : Nat := 0x5ff
def s511L : Nat → Packing
  | 13 => (1,0,1,0,0,1,0,s511D13)
  | _ => emptyPacking
def s511I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s511 : Forest := ⟨511,13,s511S,s511C,[[]],s511L,s511I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs511_13_0 : block s511 13 0 1 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs511_13 : block s511 13 0 1 = true := bs511_13_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts511 : checkedTables s511 13 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs511_13
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs511 : graphValid s511 (boundsBefore es510) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls511 : Lower true (vars 511) (graphGoal 511) 14 := lower_forest (g:=s511) (i:=0) (hints:=8591013460) (before_sound es510 vs510) gs511 ts511 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es511 := extendKnown es510 14 [(511,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs511 : Known true es511 := extendKnown_ok (m:=511) vs510 ls511 (by decide +kernel)
def m511S := sampleAt 143 #[(0x3ffe0000007ffc001fff,0x41420a105082841420a105082841420a105),(0xfff8003ffe000,0x2c8d646b23591ac8d646b23591ac8d646b23),(0x1fff0000000001fff0000000000000,0x1bc0de06f03781bc0de06f03781bc0de06f),(0x3ffe0000007ffc0000000000000000000,0x7c03e01f00f807c03e01f00f807c03e01f),(0xfff80000000000000000001fff,0x1868c3461a30d1868c3461a30d1868c3461a),(0x7ffc00000000000000000000000003ffe000,0x3701b80dc06e03701b80dc06e03701b80dc),(0x1fffffffffc000000,0x5242921490a485242921490a485242921490),(0xfffffffffe0000000000000000,0x63831c18e0c7063831c18e0c7063831c18e0),(0x7fffffffff00000000000000000000000000,0x7c03e01f00f807c03e01f00f807c03e01f00)]
def m511C : List ColumnInfo := [(0,1,302,720,8),(0,2,413,608,10),(0,4,187,832,9),(0,6,153,864,8),(0,16,366,641,10),(0,32,221,770,10),(0,36,153,834,8),(0,64,440,519,8),(0,128,358,537,10),(0,256,211,556,10),(0,258,145,620,8),(1,0,510,512,11),(1,16,366,640,9),(1,24,102,896,6),(1,64,440,518,7),(1,128,358,536,9),(2,0,509,512,12),(2,32,221,768,9),(2,64,440,517,7),(3,0,508,512,8),(3,64,440,516,6),(4,0,507,512,12),(4,1,298,720,7),(4,2,409,608,9),(4,64,440,515,7),(4,256,211,552,9),(4,258,145,616,7),(5,0,506,512,8),(6,0,505,512,9),(6,64,440,513,6),(6,256,209,552,7),(7,64,440,512,5),(8,0,503,512,13),(9,0,502,512,9),(9,128,358,528,8),(16,0,495,512,12),(16,1,302,704,7),(16,64,424,519,7),(16,128,358,521,9),(17,0,494,512,10),(17,64,424,518,6),(17,128,358,520,8),(18,0,493,512,9),(19,0,492,512,7),(19,64,424,516,5),(20,0,491,512,10),(20,64,424,515,6),(21,0,490,512,7),(23,64,424,512,4),(32,0,479,512,12),(32,2,413,576,9),(32,64,408,519,7),(32,256,211,524,9),(33,0,478,512,8),(33,64,408,518,6),(34,0,477,512,11),(36,0,475,512,10),(36,64,408,515,6),(36,256,211,520,8),(48,0,463,512,9),(49,0,462,512,7),(64,0,447,512,11),(64,1,302,656,7),(64,2,413,544,9),(64,4,187,768,8),(64,36,153,770,7),(64,258,145,556,7),(65,0,446,512,8),(65,2,412,544,6),(66,0,445,512,9),(66,36,153,768,6),(66,256,145,556,7),(67,0,444,512,6),(68,0,443,512,10),(68,1,298,656,6),(68,2,409,544,8),(68,32,153,770,7),(68,258,145,552,6),(69,0,442,512,7),(69,2,408,544,5),(69,16,298,640,5),(70,0,441,512,8),(71,0,440,512,5),(72,0,439,512,9),(74,256,145,548,6),(81,0,430,512,7),(81,2,396,544,5),(83,0,428,512,5),(84,0,427,512,7),(96,2,413,512,8),(96,258,145,524,6),(98,0,413,512,8),(98,256,145,524,6),(99,0,412,512,5),(100,2,409,512,7),(102,0,409,512,7),(115,0,396,512,4),(128,0,383,512,11),(128,1,302,592,7),(128,8,119,768,8),(128,16,366,513,9),(129,16,366,512,8),(130,0,381,512,8),(132,0,379,512,8),(132,1,298,592,6),(136,0,375,512,10),(144,0,367,512,9),(144,1,302,576,6),(145,0,366,512,8),(148,0,363,512,7),(148,1,298,576,5),(160,0,351,512,8),(162,0,349,512,7),(192,1,302,528,6),(196,1,298,528,5),(196,16,298,513,5),(208,1,302,512,5),(209,0,302,512,5),(212,1,298,512,4),(213,0,298,512,4),(256,0,255,512,11),(256,4,187,576,8),(256,6,153,608,7),(256,32,221,514,9),(256,36,153,578,7),(257,128,102,536,6),(258,32,221,512,8),(260,0,251,512,9),(260,2,153,608,7),(264,0,247,512,10),(276,0,235,512,7),(288,0,223,512,9),(290,0,221,512,8),(290,4,153,576,6),(292,0,219,512,8),(320,4,187,512,7),(320,6,153,544,6),(320,36,153,514,6),(324,0,187,512,7),(324,2,153,544,6),(324,32,153,514,6),(326,32,153,512,5),(358,0,153,512,5),(392,0,119,512,7)]
def m511D14 (_ : Nat) : Nat := 0x10118a9b91ff
def m511H13 (_ : Nat) : Nat := 0x2340b8384f15f596301bf200077101f1c009748612650c528a77c1300195958c2000840012000192c000061400a62d196943278001ab9760008f
def m511D13 (_ : Nat) : Nat := 0x247203c124753734544f201b8a896653c8e406124cdc5269bc8246493c1ec7e78ac8e403725984527901245b3732962b20139866e58ac80f03a9b89cd23900dc92381d1ecf20139266e49bc822a27361ecf00f4456407b1b89cb23904541137329a2a3791c810609309e402324cdcca68ac804e6414cdcd1591c806e4b42024f151b8ee40273d994f208a89c74789b994f208a820d4279b88cf2390124c33714854f151bc8e407b308a4f208a8dc96272c824601248dc38153cde40272483cd83f3c8092270acdcb23900046e45249a6f208a984f064361ed13790124c264360fcf23901fc12499b854f3791c80924b2c822a7891984753714a06e5b91c80927b37ccf11d3784ec5d27987135e2b735b29d4ff9892262740a78ce099f2fa56ca11201fc39463ca10fe1742201d800ffd86ffd41ffd76ffc86ffd71ffd42ffc70ffd80ffd52ffd60ffc80ffd50ffd70ffd85ffd64ffd40ffd81ffd54ffd84ffd74ffd72ffd75ffd10ffd21ffc60ffd20ffd61ffc87ffc76ffd82ffd62ffd87ffd65
def m511H12 (_ : Nat) : Nat := 0x2aa9a53c1100a8d1fe8d338906f4e9ea67434ec640bb9d3127d78d520bc339844c32ce56e0e45341809ab646512a71acd1716ecc9ab139a7adb98bd405980003e2613073ea9e5329d4511ad7e40a6b5125b85e945a33912e18c82bc31cf1bdca2000001756723eec31c3f61944d867e82179000452e162b05c60800356cda3e818000e287a91697930d04b95596943168a71f359c2e94e145e510c83e12777300003e0506000885ada6cb2d7abad213bc7bf1c79ea88d2c000093d990411194ec283249cff9912cf56cad238107c1943886c87af2beab30b849c000622fa3d64956ba5c7f4c6466309846266a277661d33c5c29e62edbb81d200073f4ab698e70782222969fc2f492c5e7d577a76f0f2aa2a0c4b9d0b38c52c97aff7ef9825c166478513ac000a38d766e48700000e8bed96262000c669e6c8a400026a8003c14000b0a00011330012d2fa84de29b39337c9e97ead80002db767e44b74e83fd8b42cb6c24454f0e000000000264000055a0000aa36f7bcccb89c5f52a000000320206ee9780028eb697aa78003c7e000d8429b0000000e3e1c75df200089ba81b56e00031a80121ec1105b6380e0911ace21ac3eca324d19a0436ea746d9475dbd32f24f51d43b6f1688a4726a5502723207463c9e096da6a3e00bf5bf8f8401854681265b5c640000117f451ec63b03d360408d579a9a5f0c45030a72ac900070e6d0e17b6b5c038921034373da680004ef14b6955aa0000e6f582cde60006ae2bc2c8a5425614c8486000021bbb751d5559ab40153e56000cc819a635cb8a40c000000000054294ef69057d819fcb11a6000ec645fb70b3aa3ba0e8a9c7772f580447c3a9780007e1800161a8618e83ebb102298787d64cf4a715daf8c2e000cbe79a0001557c678314000793e1e4449db97758a211f400052916fea117052c8d631aa86c6e7991005db671f2307d80f8000ba10007d7db4f66735ad8b3292b28a9ad0a01cc2ae00028242dd007192148954fba49357aaf881e6b44dcddeece278284904ace4825037d3ea1888db1a93d1b9cb42609d298e5a10d99527a502c59702047036287e9f47a99091ac16a01da1de59c9660005494000eb2030003010928132e0000000011110d1b170910020004000a060f0e01020025150117000e001000020103050700021007000049020308321f05100200040c0602100300080c0f020b2d111a05010c0000000110010e0200001303020506010a010400008f39010006013d0f010369000b2213203014003a10170e25030302032a00000a00020d210b2813001a051802100005
def m511D12 (i : Nat) : Nat := #[0x80ffeb2a85ffd82543ffa92b07ff58950ffe44a21ffc76617ffaea907ff48110ffeb28e1ffd84587ffacac07ff61d60ffe34aa1ffd74587ffae4b0fff62520ffeab2c1ffd87543ffb04b87ff58970ffec2ac5ffd59483ffac2907ff59182ffe43a21ffd82503ffac4a07ff59570ffe43a43ffc87483ffa32907ff61d64ffeaa305ffd5458bffaacb27ff59540ffec22c5ffc87587ffae8c17ff5d162ffec3aa9ffc695d7ffaeac17ff60910ffebaac5ffc69613ffacac27ff59574ffeb2ae5ffd87443ffb0e90fff60961ffec3a41ffd65483ff8d2c3fff21d62ffec3ac3ffd8758bffacac17ff61d65efeb3ae3bfd68603bfaceb87fd5c541efeb3ae5efd765837fad0c0eff52180efea3ae1fec2961bdfaecb27fe60150bfeb4a857fc69602ff912b8dff5a510f7ea32c17fc895daffaf2b15ff02521bfe34b0b7fc89486ff912b95ff52486bfe44aeb7fd89503efb0aa97fd50510ffab8a217fc89593f7ac8a0dff1e586bfebcac97fc79482ffb123b5ff42476fdeb22857fd7921affb12aa5ff62560bfe44ae1bfd6860aff8f2c05ff62550bfe04aeb7fc89542ff912907fe5c140bfec48e17fc79507fdae4a15ff56487bfeb4aa5f7d45542ffb12a0dff1a570bfebcacb7fc695c6ff812bb5ff52510bfe04b0bff960443f7b08a15ff5a470ffcc02417fc79612ffa32437fb50920ffcb02417fd79183efaeaa85ff5a550bfeb490f7fc79586ff812c15ff5a521dfebc3017fd69202ffb1290dff1e550bfebc901fed52482ffad2aa5ff52520bfe44aa9efd8658affa9290dff46460bfec4acb7fc89506ffad2907ef59140bfe44acb7fd491daffa12435ff5e552bfec4aa5ff581442ffaf2b0dff1a510bfebca43efd86597feb0290dff1e581bfe04ae37fd79552ffaf2885ff1e510bfe44ae97fc79616ffaf2905ff52487bfeac9017fc0961effb12a15ff46476efec3ae57fc79583f7ae8a05ff56470fbebaaa97fc095caffa324077f61d75bfe948e17fc69506ffab2435ff22510bfec4a417fd2921eff8f290fef61154bfe8490f7fd59182ff812b2dff1a581bfec4ae97fc096077faf0c27fd58510ff6c12a57fc6961eff912b05ff56520bfebcaa17fc69553feac290dff1e565bfe3caa9fed72482ffa3243dff4a480bfec4ae5f7d6554aff912b0dff56476bfec4ac97fd29443efacaa85ff62510bfe3cb057fd7950affaf2a05ff02586bfe3cac97fc695d2ffa32385ff5a541bfec4ac37fd8958affaf2b07ef12570bfe34aeb7fd89182ffb12bb5ff56540bfec4ae37fd69502ff812b0dff62570bfec4aeb7fc69542ff8d2c25ff56542bfebca83fed62487fdac49057f5e4609fec48e16fd691c2fd852c35fd46460bee9c8c17dd391c2fea32405df564709fec48c177d59182fda52385fd46470bdea48c17bc495c2fda52305ef52470,0x2cff99deb3726662cb99948b250641ec7398c1b12461dac289826b00c5f82bd89795aecc5d2ab9796ffadc85afab4a1678ac9c58b6b0695f1abac56c2ac8156aaa945492a8214d9a9685262a39944da86450329f613cba7604e3e9b79349a6524c0e97192bda53049b69269222a40447368d9118ca2ce44f288690e7a198429a83e105ba08040928020fde9f683e627bc0f4d9e643c5a77b0ecb9d4c3a167300e359c2037966e50da49af4356669a0d0e99f0335e65b8c9198d8311a6108bfb97ac2ec25cd0b74969e2ca65820ae8959a2a9e5438a66948c28964fb09da937e267a4bf09629284247247b88d19158222e4330840902c1fc23e807aa8f0a1d9239d07148dd41b12354868d8cd018f630c05f78ba4169e2c3856b8a8c14aa28784e98992128e2418462888e109a1fe03d187620e421ba8354865e0c4e17982cd85500a0a12e8232841a07c60eb01b0830c05820a5011f8208037a05c80a2810e0186020801b8000ffe44ae3ffc895dbff8d2c07ff61941ffe8cac1ffd865dbffb0cb8fff5d941ffe3cb0dffd8650bffaeca17ff50971ffec30e1ffc861c3ffa82c07ff5d980ffeb8b01ffd86583ffaeca97ff50560ffebb2c1ffd71583ffa84c07ff61950ffebb2a1ffd42583ff8f2c07ff54870ffea12a1ffd89583ffb00b07ff54960ffec32e1ffd80543ff90cb87ff58150ffebb30bffd86593ffb0ca07ff22564ffebb2c9ffd645c7ffb00b87ff61542ffe43281ffd525c3ffb0a387ff5c160ffeacac1ffc895cbffae0a87ff61954ffeb2301ffd85583ffaecc0fff5d954ffeb22a5ffd52503ff8f2a87ff51960ffebb309ffd845c7ffb0cba7ff50981ffe94ac1ffd865cbff90cba7ff59150ffeb9283ffd811c3ffb0cbafff61910ffeaa301ffd76443ffb0c90fff61570ffec0ac1ffd54583ffaec90fff61920ffebaa85ffd42443ffae8c07ff50520ffec22c1ffd72603ffaec907ff5c520ffeba2a5ffd74583ffaeac07ff61150ffec0221ffd72583ff8f2907ff61564ffe908e1ffd85503ff8f2b07ff5d150ffe90b01ffd86587ffaeab07ff5c950ffeb0221ffd76587ffb00907ff60570ffe90ac1ffd21203ff912907ff50961ffeb0241ffd611c3ffaa0907ff58580ffeb2303ffd81503ff912b07ff5c110ffec2ae9ffd16583ffb0ab97ff58480ffe90ae1ffd645cbffae0907ff02586ffebaac9ffc87583ffac8887ff61460ffec2a41ffd64487ff8ecc07ff48540ffea4a41ffd64483ffac2b87ff5d181ffec1283ffd72607ffaecc17ff60971ffeaa2e5ffd69483ffb08b97ff1d950ffebab09ffc79443ffb08887ff51961ffec10e1ffd61503ffac4387ff61d41ffec0a41ffd74443ffaa8907ff61121ffeb1301ffd86597ffae4887ff5e560ffec2241ffd76597ffae890fff60960ffec3a85ffd79483ffae8907ff588,0x3e401b9000507f1382e70d3208dc7b12723366e04918a48539027e7cdf201557b5e08722ce82e409b90d24c2a1d44e8c8f158df201947b03cf11e40a4c6e2e0ca6c83230043702887124f900beb0e462e0f6b21c6cc563788c7bc80d886479010e030ca0181e852f2019323210611e8f9be40138fea48f6079008c8f10c800f9243a00cf9006f918f6249720147235e2372a6236093900b6320b87cdf201093a170649240c446f9022a400141fc4e752437c807b89c0632139046ebc07f1382e7c4323c80865864959080410f9bc9390210061b20c546c0133728139be4087a4e4611671b223c8249cdcb9be40a48d89f9715c80271846652d373e403246e1f82e061b23c81098dd780fc173e2191e4024874259b23c800f92737194c040d98ae419b9661c81498dc5c0a4d9ba12248d81381f9007e8cdc0fc82494e85c09842462a326409baf613982605e37c803f03cd900c8a4e6e13972049c5143d6c8dcd9062abc2759b84c079f238df200e80f2c6f902923d8b9139b3752720024652313f381924e409b90c320747c5720422375843f030f9064624c6e1f8843c9f37c80491e44e01a2712d19be40248d80784e1f9f20c5427187372e418a84e30e6e5cde78c8c49c800912cf900921388b988d81f81e8cdc4909c531b03f03cf8a8d39b84e4c57201e0271b08403c7b46418ae20138c25cdf201240f1b0270fcf900922d81e3604e1f9c61c8027cdc98ae419884e309737c804909c6c03c3f3e4130e2a13e6e041b37c80491b00f09c3f3e2a138c39066e5ffd3fe7bfa9ff12fd8ff9a3f0efddcfb4bf593e87fccef907f0bbdecfb70f60feaa3d29fa08f353e553c84f8c8f0fbe0a3bf3f79cee8fdb7bb35f60ceb6fd563a7cf49ae877cf739c3f346e5f7cac392df21ae38bc59b88df0c6e0e3c09b7e8ef90de77bbc374dee5adbf7b69b6aded10d963b1735feebb2d6cfac4b559ea72d477a7c34d7e96ed247a36344be842cfef9eb33a6e702cd5b99b3310e5eacb0394b3261e482c8478f631bce32ec5db8a13121e1e4c31f84eb081e0b8c0db808afe6df6ebe337aeaf28ddf2bb277572e88dcc6b8cf704ade3db7cb64f6b4ad43da32b3a765aac8fd8e8b11360d2bead794ae935bfab63d67cac635722acdd53caa0b52c2a2dd3f2a7634d72979d2a8a4bb48728e8d1a4a2b3443a86bd06ea0473f127c1cf2e9ddb3a62726ce029b6f35b2695cccc98db30625d7cb5095f72ac2528ca06936325c2497c8da91332162401c7cc8f031cb2375c6828c9717b22d0c5608a03128a221c3ee87470d3a186c29a84db08620e6c1788283042a064c060802aff01fb0bf0c7d82fa29f10bdcc7b02f501e7abcb478bef051de4bb6a762aeb29d3aba2a7382e5d9c95b8cc70eee0b1bf0b7966ebedc51b6eb69c6ca2d841aecb58e6aaed459a6ab494689,0x2150a4803e6e1fa4e24a47902ca3c0f69c80868de610a4b9062a322f09d66e139e150dd09c8f2001578925091e401b82e3287e6c8f201941703c3f0dcf88640bc44632af62a90e45a7208dc6412c0c28139be47902c2462c843916909b2092737030b900d90ac939b97374246c1843fc80491908c4e6f900921f8d85cdf201044912c64030f9b87e3c6463da5390092889e37c80640e8b9be40bc2742e493138848cdf155ef201b178362191e4024868259a78c806c0eb372c6e26641138745c5637c807b9840849cf1be40431183dc4e6c432021a1513a27200f11e418a84c3266e618715c808f4eb3709cf900d91bc46320966c422309b2021c0600c6540f69be40320c23610c78df20c8c7b17ca91e2a1be403280c3d9d09c82278dc640fc173e6ea4a7f900d8592637c8f201ed29018f902933088f1b852698408c8249cdd27362a1fc6f900ca521b208dd0f5b12736479046e25916211b10857200e8641e80c389d8a8c39066e139b10c8f20856490e87a38d911e413c0759b983fc8049114784df233e219005a3290e030067cdf23c804b1048713849466e07892366401f9b230df20c54061ec6503d0a4e403dc6f1380c6c573722c6c1e061c80641ec87564028c6e23ad85c432049c8643e49200f9064600c6e288143c9f23c43201940a03c3406518ae6f901161381e360f03da637c8f20425780fe153e2b1be403d8d85cdc0fc83151b07b1e0f9026e1c092bd8041d44e88dc64c807b5240c342b9bc93900ca588f2021a37194b88641918921d096649f208dc0a5943f854f900921388a9b81e3607e88f637c8f200e8a25e411b8cabc0f46cdf201384b1247901a27404f902939b8c858c7202185bc8cb9b8c82487f900d86c8f37c8049154780fc7b46411bc93918f694c2a701637c8f2021a4932139006ebc07f1382e7c8f208dd610283f4a4174640a487e4588f1bc4e7c83238dd610283f4a615446f900f7918745c8f20424375e03f854e25e479046eb0812b210a8c81279840812e37346e846418aac23d8187c8f15c82370fc6503cf900d825c6e4cdf15c806c5e17b36404346eb0ac8b61a15c8f37927201940f3e6e326418a8f63c0d874dc7bc802703c6c218e044c33c07493e6f901f1089f20924640e803387f900922288e3626e7c43208547a0983a03cf900d924e6e4c550809f2001161cdcf8aa6f900c237af6139f150dc0688f201ec653c2b9024f24cc20466e709c8452f2003cb1be4013074079427c81155244e187373c46a4e403288f1b987b20d37c8c49c80c25e411baf1138f46c43209243a89c03366f91e40320fea48f630900914637c801e5b0b1be4032074061737c57201b0781ecc360939004e2d81e6c805f43c7b49cb90293918133c46e6c5720cdd784ea2303cf9024e87cf0048971b9f10c80190d00a88c65,0x40e9371ec5c23320194e0be40360140987f1b9f20c546510a372a4f902462488a45c6e23aca1fa909c822798549cdd153e2a80e413226ea285113c529cdf2089d499854b304cbc6418a88f1bc9632a215217204dc4b89cc07c961584f8a8d99046e8c421519486c803a104e0ca4f0ae40b28851b9f23c40421db205243a3868460931be402d8507c8c0fc807a12e3736478a89d9001e1ce6e3283a91e71085465c802f9243a06931b89391e413d8b62e2528805085aa1c49e1548e498df20566e84afe2489c20c4f900969c4026c803a8b6491e86546479001e3ce6e32880703c271b215c802f9246bcdd3880f2a4e411390ca59e2d4dc0621b200ea6512503d90c20c4f9046e6c4320154650e45636460346e3b10d902921d2017c800a0ac3f8dccb0c6f902d8264126c8e154dc0fc80860e84146411b896360f45c5537c82275ec0e984f8aa4e05640b288f1b8f481ed3717227c803a36479be402e01e32c92bc274212a37527200f07b2c02842d522a4f24a471be40905c51c8e371e929c80f91e40018d61d0806c8c55c80495ed3701c5b171391874460cb1b8b83de4007a723426085257fc8337995154e479be4132a96a4c10252019924864df23c80063af7918d7900744326e202017147201e93789cd9bc12938b0918973faca24883902c6cc808b8dc884c4f90453322939ba2a8cde27c82648a54b524f91c109bab6bda9332e4085e32021e375b0b900f43610c4397231e5371af2012cd9bc4724af02e27413640210caa1ec8649d65107204dce93c92036404326e1d2ca889e234dc49c817b16c5c99538aa6f904c8bd85114c4e8c432049c42596490e8ebc64045ad91b9615422095aa7f49e49cdd23c8159ba4f25a1124e40918ec8c407b0e88c17320194f1b81ea4e403d84c61ec864df2310529c80e05101900971bc4e64dc8601b20927230e929462005292066403206871ee274de65173200e8f042b711cd513af69ba9390248617d3701b230ea29c8119181f8a8cb900851b9c19c83238556110a374a502882e051011be47901c79c8f108572006a490e86503d44300c2fa6e1d44f901f1003c2602834c81493e2125c9391e40432c2b20f29c540ac832311e374a47a462191e40214921d25271ed3717c860d323c80e3de471b8b894e401d1f208dc2612c0f2a7b886401a44e0c8147c8149cdc2603cb9007e3282e1bc466cdf2012c411242603cf91e2a07e4032e6e6c8f208dc190fcb8824605640328680c9f1502320cdc272e2191e402486825982688f20c5737194d1be47901183d874689f37193201240612cf9b813902924644e9f9c4bc82375e0291e8d9046e4007e0544e0b9d23c5455c8065cdcd9be40bc2f61490e459f37c804bc8c79124064a5093c6eb621e28e406c81498dc099e32330a391c6f902f10a9a61c4086c8,0x4cabda929c4109d253742720c5583986273e2a276400784e360019ba315c8c8cc80074dc6b1051880079004c4390c079e7b03f15c823709c6c12901a44f1b91932e406cde78c805c524658e842449284b069bc4f90082782678c804bc8d618dd2942924646e13640329a3849e379ef2048e3a594494a719026f13c52a4af69d223701b15c806c0d47b3a479b8922ae403287e7cdc5c5267809b208e842195213640bc62b2588f1b8ca8822239aa275e1494eb37c8120ca5b900071baca259c6bcdc4ec80501044b3c2b8864043e461d45225a337c814988e085e2275ed3f4a92460cb9046e1e1b3112c65c807a2e418aa1313cc29ba9670d3238dc8c8a720301425e4045c6f139b101947b1708cc803a3e462591632e4007c6e706451c80878dc30364684ccb043078ae409ba227c8178159094dc4b3e2a32a6e2a9199008270fc5121f231272010a374a538842b9010e1d44e259c26219378b43a92720195032e411b8f496896603c6c8eb151db37c80f988cb900f4259715cdd7819720154501713a109591e20078cb902923d0748c8f37c80411386521c4b03c4956469b81f900f425990849e388de7b9272048e3a481e364922a8d79be407c8f101ec5c1948c03f200e921d46e460b8328f7901f20c56371b0421e8d91e6e43883900d03289c07896acdc6cc80030184e349284c4713b069bccb9008294072089e615253707d15421313e2a9bb0790453322337c804e1b0442cf6078ed900d98ac6e70641ec81151093789ce056402491622c6e141f23925371948cc800f105191c6e32e40432920301e1d272012c271b23722c0f109024e47901171b88a23a521fa47ac432009e159240f1b01a0e9591a12a5e2b04309904ca9ba43f1472021c4e074424de274e4113cd89b90e5c43200bc0321a1521ce24a5a0be403d2cb1b9c6c8573709c4ec804112c0f4e2a80e4113a6ea281d30a215c81372186c0e8413e2a056409b88f138f478267849f2012d235963742138aa6f9044f14cc8a5a33713b205e0555ec8b381f8ae4013c6e3602725a2234260860e279ab15c81374e462ae402487e229160388e9ba81921b2310629c81373c4f904d845a6e5c8d0182149c82654713745539ba47900822590e130ca813b2003c279246c85400cdd3880144506893e406926234dc8c09b20194f9be40362f045af6439c4bc806522e372c929ba1307e413644e706486857204dc4189ce1f8a243a4e24e4091884b2c6ea1b3205245c264113a6e184c880a9314a2a9c807919737100b9b90e27640208ca258928c8d0182145526654df204412842d54224f9062b25a471ba80a89c4b99637c80c0c80791e40b08971ba528cde09587209fc4bc8c491052954c390646050971bc527218264dc3a92720194f9009c258f23580c6c43200e8261ea49194e3646f90118,0x1703f2009a370fccbc66f9001ebd84c459f1089d4902b201f43438151389732c6f901b23c813712c8b1086b3e6f30a121f8939191914e40902a6112f238de29c80ea49179004d1b8ca65b00ac808a0d0b16e4132874438966cdc26c80418b48712c6540971b8cb9025a3d1949c826189d3acdc1f3e2130e40a4af113af69fa13fc540a194474df201e9191e6f3c0b832e4007c74a4884a4ff23c544703c0ac80654dc7a56479b8aa2487f9000e8491898e2379ef23c823a125294640211169b8ca2a8967c8f371943fc804910c0703d391e4032a6e07884458968c412dc81491947a0e8e1a0f71b91913e406c8d498df202306503cf9b85c96e4043882328968c400a1b32006434326e9c64130a9313a74701b2019637219494b43a462b91e6f90084bc05c358d09d2b3713978c805c09c001b13a03c425a7024e409b89cbd8729d44e9c8d78821494eb3799720446e2e64007918138d83d8749c8f37c8149996085e17b4fd2270831be40138003611807a549c8e83586094a7208dc414e6e1fa1224ccb13e411191895272089e644eb378a430466f900b0060c8bc1b370983fc804988c653a9245e4091c6e130ca703f151286c4eb2009f37403316e409bcca209b37527208a57b4fd7889d191a6f90][i]?.getD 0
def m511H11 (i : Nat) : Nat := #[0x201bf929b3ec106c051993e318d8f5a5cd9390b6cf8823646e199b94c2b54269e26c383383aad9cfba749a28ec949a232e0000c6f2cd2cb0b000033782202168906cb360182a3f7f9c926bb836541a507043340ce43c75a2bf0b792bdb36566bccec87d60fb67aaa75ad38c8e28194947b9dc4be25a4f6303a5cc9ea90a6f316a129833b3118bd4e91dc669133430511510b507dd8ac5198b1cc92ce835ea254b34b4438dd41939cfe457d08c0e31f2ce63a78fe85260bdb77cf67d5886e12af7d344761f68060a5a654ecd67abd02a1ecb5c1075ab4b57e0000000091138390edb28b23e58a6a0003584e992765420440000000000089264b5c8a6a8ff648d5d4e2720000000000059ff88e5a4e8c540c36e842a0ba47813007929aba24317a8580af0e99c6293f1661af2a763ba89ed2caed6c000000000004d2c00000000000000000000000001ebd0000707661b344df1529a33193390c8c45353a154909bd932e176e4a4e311157325bc51b2d180005526712ef15bc725a9ba26a0003418b2c78908d448000249126f56f3c0000b2d65ddcb640000d0616380091544b1d1000085b3a28436ca1e8692a52c00003a0a0f06a955130397e4c9510ba91561a692001e7785990a267f0c43fad6b62f0f18a418000584c21a1e040000444e13719c2238a0000605758b219fc69eca49e847c0e0a18e16d52b0c44a7a40001da0dc8a5224707f4a5faa796e61263c4d0ca3343a887808fb936e1d8d3a6801080711f153841609a168a7f531d014aba3a0453088d058232142943ba6660886010800000f120056000c053206000402212158010005006f0100010504140002290003000208010009284c007900050d2f0107301e001e000c04040a0e0100010f0322011a05782f0e0b0201021908351820020d0200050000051b080100330422010e00000c00500305000402000211001a021a0400001b0000001c01050007001f1100000202090c26030f08941408191601081612040010000000080004690c040a03112c0c13052001051a2900023b010406061730002f29020107080d160462171100310204090000040a000f0020160f000000000b000246090600008600100014051a0500020100010c020a02092405030300051402000000450100030207210403551f2e00101d0b0d0086050d070007000517000001050303140401220100040618060314041f0501390807000c0007180d001001550900280b020801000800171004094600003d00210203060001020502001a2d0000420b06050c09080d2900000a0508074d0a0202060b16940c0205070200000900060322000e0001200235270c4b050f25002600040024040202090e0006190509044f0003001409080000161d2f2a030e1c0000031a8401004e2115173b1a082f03010400001003,0x50000ee57a91528fb49dd460c7bf4f5539d10f9cf5f067e6f28861c3d7a2c108f62d321fa8c913a1cba9d5b02cce153a1cc9e5fc0fa1c009d68d5c46c2579cfca0fba0bc11ab0c071d5f404e8b48e2dd89626155cc25b60444151155313ed04274c668f88a18a3ea49e54b5532b1e9899647188abc9f32536373b25365ddc240ea81e035e79026696de234a0ee1531b618affd481d1cda6a629ff0dc0896c316743a655ec2b9227008f43e3b7dc12264e79a47b6603c800031e8cc86c11332ca8588356d69244b75c8c44fa7044d481585c61673d663401e59b1943f46d62888000e40800000dff054e667ca8597b6cd53068e2bd41ee0a190d4647aa5a0017d76e4a7e9f802e961ed72e000008c2b3cd25cc98c982b352306a01795ce5768e2b628734517837766dec932c93000190f6c39096a6397f36be5611d2d6e246aa98efaf094000000000036d058c50168d0fd0a143751b400013b927f1a16bd1ec2a200000002dc9000055948d94289a514d6c08d15175badc6031ec0e652000040c8000117d0000e7b191739b70399256b06b40d9283075deb1175f7e24492e0350d1465a24f4868249c61e22b388ec651024095be5fbd1cdc7e64f7725c536c19451988484d3fc692347859d600011415ad0e0c641ee18f204271360ce9d0194896916f38e08a215a83d2d38ad31d52ee99ba4f755308b8d15800038bc000045c3523e4480ccf12cc4aa3a546b2ba0bd6118cd4dc2749796b7f0b4d0dd91380bf2c73a29c5482a1142734016c54605800005955d7ea000119259a6631fd177ca0200cfa51ae368500997f5fc446a51763dcb97493b6e6cb3c88a85cc3f5a891330571a0705cd7975a06acd02d3d69e8540ef18857de01fe69430f388b21df07740002db4799ef5800d0dda6c3ad05c4a8a48997cef8a3909a212cb80e48961156cb7000000014f8000011a4000089e40000c39d03cf4f5c3be84000000000000000024a1d194000525f0000a0cbc8ba2260001006c000000042c40000000000025880000000000099436ef5556000000000000a8ddc176645327e1b52c4800000000a4e0000a9dc31672800000e44a0002a3d0000b70aa6098c2810800000001d4000000001276e8e24287f22000004ec80008418000114f6bbf0001c66e8a7090f13da05ea99c528e0535e275190d10714a28068dc3e3df7830277409e3bddc56f32590cd49ef89e103614bfd861323380fb0a1800059804081a3a100087b5a540dc1f8ff7445c9f9de54b9800014f65221947ea2ae9321e14b06b167930302374cf4d8a6210c17b986dc82cc02840a000008d3046d18aa21c74d690efa21790cc47f93e2972139c2a03b4dee886bfc00012e25200e34e033beefa93c651a983c2dec264b0704472ef15c7f387812e5735fa2c003f59052126ca3d3ecc424484,0xa765821540476a95421b80006032000114e800036aa6508dbf019147fc5139c4601b9a8410d73e9f00000001a3c5079c2bd00012cc8c6874490000000161211c600008e03134a3a80000d2dd9fb784c2610c17f45524710312c7e2d069056f66e20b4d96733d515c0a11c9c0b04a8d464021e6b1dec20a00000002c57000122501f9cc87046272885d8041397408b20000116f00000003441a39673e934aea9e7a939277a2c9e0eca99452f2510d8d38219131e42c0001825000134be27402da8013850591d0ae7000000000006354048e2f5fe9c50f5d490f4e68a57c6f352d2dae5552882d9ec4f90000517ec8ea6ae40007803a24a0dfd067095f000000031e05a05f28baa82459ccdd06a1c33ea4d04aab5e66783181040322c951e444fe49bd9d912d74525050317b8c8d675284e9403304bdb854340025070544ae2cb940508da1af54099987241b4c671afb983660306b406fc390c7028fcd8c77a688880cf8624f639ed0568fde97c027f0cc18a61d0db1726eba4c831fa0520b0d4d33e0ef167f725e475800b42a7502802c252d6653f2c7471ab1b09beaaacdc41c85a7f3656653ea3e143080d33511b2e0b04ce68d05f69d5e9c14b0f4331ca530e961c49f431bdb290f205cb09875e59a09dc8943b5993ae0000000000085da91069ac62ec00016bc58e3eb18c4712e5e94a4406f7c780bf699a9a0a70cc41000000000000a8b400000000001b24a530187f28a2b1a3608c977f6af49f128391c9d5a20001868d028308953f025f082a916e4b8c1b96509d567448b1451d0b94342eb18515525b85f6ff52004470f4b873f5e0a1c230862d241c2094766239ee8448c1152104fca625d113de92e951ae4bda44d73278e071649c8cc17410badba18cb0426c22c82e648864a8b351c34c8de22b990a321d7cbd00018d8d172f9e101fa00018f60000451734c01bb00001293f4a4000615668c8a7f715de08558c0ae9458f8000446bcb0bcc50000d2f200000002306814e000313b325d448a00034db5cad73fdac99c55a87d576b83940000000f5bb2df000013cc00016f240004b3e39f4cfef8c77c33630fce500005b1037a863528a378edc38ae708653cbaa3a3f401255d6a70da3200000003d036072e04e0f934d64302429400074460000ec4567c800000004a5520393c384798d91a2f520f74d4c6fb66724b3682002fe1b0e2f8e96d50e11312109b45e0c4dd3de92f8249916e22601a7871c0752e9633937010348290a99208855cef06610000f00dea0dc1d798376b429b489588ccd629ea2369948e1675e46cdc400274c020eed1c0e8000b9e2e03e504f12cf5b75476a0179b0309fa01566838f2e6ba297be06d1d8d24e0487e3dc0e8568928f9205dcf306f13255532649d80aa20b1c00824660fd8136159790ee39400015b4c99,0xd4100007beb495ceb4a86d5b8fb60e65614dd030ed78883220f180df050348182501a28b127a8dcdf50a0ac43348d246e49eed4966d7d44699f1f8a5a197856b2c56422d19d081614f7a83c4058e180005763e14966591e5a11e0000000000079a4212917c91b429896429c7c80003858c7cd1b1787997e84618d29c45f09ce412dced05219176e79e4aef08175bc62c3997d30ae73fc9cd137283b674865f400019e2676602d9926e50281b6023962a6b2016ee0000000705da977123b65792ad25a926b3da1006e62bc84c4618316315ff068a9e1000002e3a3][i]?.getD 0
def m511D11 (i : Nat) : Nat := #[0x27fd8a02576def548495c27fd9a219749ff6297958a7fd1a1e584bfb4a8874827fd7a225209ff629191c27fc9a619709ff628794867fc8a4a4709ff568895827fc8a5a5109ff628695067fc9a61954def549491c27fd1a025829ff5286961e7fd4a565209ff269726027fc8a5e5419ff269766067fc7a625109ff528895967fd2a025879ff229694827fd4a1e5869ff428895c67fd0a1a5819ff1e98958a7fc0a625619ff269845867fc7a4a5109ff628695c67fd0a22575dfb585291c27fd8a1e5109ff5e80960a7fd0a225419ff5e8696067fc9a59120df7609391c27fd6a225549ff669655037dd624e4709ff6688758a7fc7a5a5209ff269615c27fc0a5e5659ff5687961a7fd0a225769ff269766127fc9a591809ff4a8795827fc0a62565dfd485191c27fc6a625709ff269764427fd9a5d1529ff229191c27fd5a1e5849ff4a87961a7fc8a5a5429ff428796167fc9a611209ff428695c7f6d6554920def615491827fc9a609109ff668766027fc9a609709ff269645ca7fc9a5d560dfd589192027fc9a615609ff5e8094867fc7a5a5109ff269865067fd9a219709ff5e80961a7fd8a1a5759ff669745867fd9a619769ff528796067fd9a605709ff6697654a7fc9a605709ff5e8095967fd9a61570dfb229291c27fd5a1a5709ff269844437bd8512570df7595391c27fd4a1a5819ff629591837ed854a4609ff4686961e7fc9a55120dfd585191c27fc6a5e5549ff1a9191c27fc9a5d9209ff629291c37bd85524709ff1a9895427fc7a625509ff4a88958377d82564709ff5a80960a7fc0a5e5619ff4287961a7fd6a1e550ddf589591c27fd8a025619ff269726067fc8a5e5649ff468796027fc7a625219ff5a87960a7fd5a225749ff528795973fd5a62460def604495c37ed824a470dfd629191c37ed624a470def605491c377d8a56460ddf595591c37ed8a4a470dfb595291c37f48a46470def484495c37f58246470dfb58929202fed4a54920dfd589191c37bd2152470bef1297948377d6556520dfd1a9191c37bd6112570def585491c37f56546470def608495c37bd6212570def609491c37bd6252470def594495c37bd655247097f5e8694425fd7a1a5708ff62879603db9475c1409f74e8694423fd8a1a5109bf1a9294427f80a5e5649bf5a8795827dd3a025659fb4a8095d67f51a1a5108ff628095da7f51a025769ef528694427f51a225109fd4680961e7bc4a5e5609fd4688948277d5a1e5509fb0a9895967ec2a625768ff628696027f51a025869ef129895c277d5a1a5509fb4a8794827ec2a625609df568694427ed2a025769fd4688954277d5a025769fb4a8095967f51a1e5109f74e8095d67bc4a5e5109ef528095da7ec2a625649f74e8095da7dd3a025729ef129795427ed2a1a5109fb0a9895867bc4a5e520,0xddf1a9591c27fc9a5d1829ff1e9695433fd65624709ff5e8695527fd1a1e5609ff468794827fc8a4a510ffa5c960482fed6a54920dfd4a9191c27fd9a58570df7605391c27fd2a025719ff269716027fd5a1e5649ff669865d27fc9a619719ff229494827fd7a225659ff669215c27fc9a5d9859ff528895827fd1a225609ff528894867fc9a605209ff428895527fd0a225219ff428895827fc9a5c960ddf469591c377d85564709ff669825c27fc9a505809ff4287960a7fc9a5d9509ff5a8796067fd7a625609ff269725437f56a464809ff269745867fd9a595749ff4a8795067fd6a46480cff561891827fc9a5d5649ff5e8895427fc8a5e542dfd549191c27fd2a1e5549ff428695067fc9a591829ff5e8895867fd7a1a541df7629391827fd9a615749ff1e94921a7fd6a225509ff468895927fc9a61564dfb5a9291c377d85564609ff568795827fd2a225419ff528895db7ed854a4709ff6696460af7d5a1d9509ff528895d77dd214e4709ff629691c27fc9a611719ff269746067fd7a565209ff4a80961beed86589219ff269714827fc9a591719ff269216027fd0a225729ff5e8096167fd9a1d9509ff029794867fd1a1a5849ff468696027fd7a225109ff468095db77d81564709ff569291c27fc8a5e562fbb619624827fd7a225649ff0297954b6fd825a4709ff269415827fd7a1a5849ff0297958a7fd1a02587dbf499691c27fd9a611619ff5e8894867fd5a22570dfd485192027fd9a609409ff1e9895967fd4a1a5759ff269845427fd9a615409ff669855937ec6a4a4709ff269865d67fd6a025759ff528696027fc9a60960bfb5e9524827fd9a485409ff269844867fd7a1a5859ff269874437dd614e4709ff468095ca7fd4a5e562dfb605291c27fc6a565409ff5698958377d2a56470bbf5a88758a7fd0a1a584dfb0a40961b7f55a464709ff269645427fd2a22571dfd615191c27fd6a225729ff269644427fd1a225209ff628094867fd2a02576dbf499692027fc9a619749ff669744867fc9a595809ff628795527fc9a5d980def618495c27fd0a225619ff269655d36fd565a4709ff2297948777d21564709ff269656127fd6a025729ff1e9895877f561464809ff628795067fd4a225619ff229794837bc86125709ff269855d27fc9a5d9419ff5a8895d6ff51a225209ff269724427fd8a1e5619ff229591c37bd8652470bfd468874427fd5a025869ff269855c27fd6a1e5849ff1a9895d77ed5a4a4709ff628695d37bc86524709ff1a9895027fd6a1e5549ff4680961aff90a21d20bfd468874867fd2a1e5649ff668875867fd5a025769ff428794867fc8a5a5419ff2697660b7ed124a4709ff269756127fd0a1e5619ff269864437f581464709ff5a8095c7fe96260120ddf585591c2fed2a1e520ddf229591c,0xc27fd2a1e580bfb0a9865427fc9a55160df7219391c27fc9a5c5609ff5a8894827fd2a025819ff468895c3ef946581109ff629694827fd6a225709ff5a8096067fd0a1a5859ff5a8796027fd6a02585ffa54960482fbd4a219409ff229795827fd9a21d20cff585891c27fc9a61d64fbe519604827fd4a1a571ddf5a9591c27fc9a61d549ff62879542fec2a619709ff628095d67fd2a1e5849ff669766167fc9a61d219ff269616027fd8a02572df7549391c27fc9a609419ff4a9191c27fc9a5d9549ff528795876fd815a4709ff5a879616fed4a589209ff229595027fd5a1a5879ff269875867fc9a609719ff5e9694827fd8a1e5649ff269815827fc9a485709ff269845ca7fd9a61d619ff568895da7fd1a1e582ddf619591c27fd9a595709ff428796067fd0a1a5549ff66876616fed7a589209ff669805827fd5a1a5749ff668861c27fd1a1a5749ff2698654377c8656470cff469891c37f585464609ff628795976fd8a5a4709ff628095c6efc6a465209ff468895da7fd6a225749ff66974606fec2a619409ff4a8895dafec8a5c9209ff468895d27fd9a619409ff5a9292027fd2a1e5819ff1e9895827fc7a525219ff629591c27fd7a025619ff269875967fc9a505209ff4a8895c27fd6a22541bfd4680961a7fd6a225719ff528894827fd8a1e5609ff5e8895537ed864a4709ff269545ca7fd5a025879ff4a8095d67fc8a525219ff5e8895827fd0a22565dbf485691c27fd7a1a550df761539182fbc4a5e5609ff528695437ec864a470fdb615524827fc6a625749ff568796037f56a464709ff5a8795827fd5a1e520bfb0a9865527fd5a02572ddf495591c2ff98a581209ff269655c27fd4a1e5829ff628695437f52a46480dfb469291c27fc0a5e4869ff428895927fd9a605409ff269875427fc9a619209ff0298958a7fd2a46480ddf629591c27fd4a1e5219ff468795937dd5a4e4609ff229695037dd854e4709ff528895ca7fd1a1a570cff4a1891c33fd62624709ff528796167fc0a625219ff1a9591c27fc8a5e561bfb0a9865d27fc9a5d5809ff4a8795437ec2a625609ff5e8096067fd4a1a5859ff5a80961e7fd6a225769ff668865027fd5a225649ff5a8795076fd165a4709ff229494427fd9a595429ff5a8794827fd4a225719ff668874437ed524a4709ff4286961e7fd6a4a4709ff528694427fd6a225609ff4a879442fec2a619759ff568696027fd9a5d1829ff5a8894427fd4a5a520cff4a9891c27fc9a55180dfd619191c27fd2a22510bfb0a9895827fd2a225649ff269874827fc9a5d5209ff1a9795427fc8a5a470ffa5c9804827fd9a21d609ff5a8794437f486464709ff1a9895527fc7a424869ff229794427fd4a225509ff269725067fd1a225729ff628694427fc9a61d609ff4a8895d27fc7a5652,0x70bff229745877fd651e580ffd5d161443fed7460952dff5d0895837fd2958570dff5d159482ffd4a21d61bff42887487ff94a58110bff629615c3ff97a58120dff614795937fd851a574bff02987586ffc7a61162bff629625c3ff57458521ffe595705037fd6562470dff5e559582ffd6a1e550bff62974486ffd4a54960ffb589211c37fd161e560fef58574502ffc0a5c961ffe52960483f7d7459552dff61579583fbd8512570ffb589804837fd821e550bff029765977fd7422561dff585291c37fd5952560dff58879542ffd2a5d181dff589792037fd565a470dff60579502ffd8a58540dff5c0695437fd744a510bff62962503f7d7459550bff42887587ff98758120dff615695037fd7462510dff5e5295837fd651e584dff56587582ffd7a61964bff62974586ffc7a59181fef609645037fd494a560dff5e90921affd7a61564dff60579583fbd8112570ffb589215c37fd2959540bff5e8894837fd875a520dff485795037fd8202571bff5697460bfed625c120dff465825c37fd821e510dff5d189586ffd5a5d162bff2297458b7fd815a540dff5d18958bfbd5659140bff1e919482ffc7a59121bff5288758affc0a61d62dff60879583fbd825d140dff609591c3fed6248540fef589745037fd6256470bff4a9745877fd215e560fef484495c37fd615e540dff5d0695437fd2959570dff48569502ffc7a51961bff4288758b7fd2162570bff029875977fd8a4a470bff6297458b7fd561e560fef595745037fc895e560dff459795837fd6502572fef584495c3fed8458920dff565825c3fed7458921dff565625c37fd654a470ffb5d162482ffc7a55182bff1e95458b7fd165a540dff585895c37fd6562574dff609795037fd625e540bff1e96460b7fd8246470dff4a5655d37fd825e560fef608495c3fbd6212570dff595795037fd8256540dff589595037fd825a540dff558795937fd6262570dff55979583fbd6512570bff4697460b7fd565a540dff595895c3fed8758920cff1a9891c33fd6862470cff1a1891c2bfd8a1d980b7f5e8865c33fd5262470cff569891c36fd1a5a470dbf569691c35fd855e460dbf619691c3ef97658110cff561891c36fc865a470fbe5d9604836fd525a470bbf5a8795833fd1862470dfb1e42961b3fd6a62470bbf5a8875836fd861a5109ff66961502fec2a618709ff5e8895067fc9a611609ff269875067fc9a591819ff628794827fd1a625609ff5a9191c3fe942601209ff269865ca7fd7a1a510cff485891c27fd8a1a5709ff5a9594827fd7a1a5809ff1a9891c36fd2a5a4709ff428695d67fd8a1a554ffa509604827fd0a1e5659ff269744867fd4a22510dbf615691c27fd1a1e5869ff568696127fc7a62520df7619391c27fd9a21d219ff628095967fd6a56470dbf229691,0x593efd7659182ffe5d160443dfd6251d70bff528766177fd8a5a470bff62965503ff9215c140fbf619655c2ffc6a60470ffe5d1804837fd2162470bff5e946587ff58148570ffe611604837fc7956520dff580894437fd6062520bff4a8875837fd611e520ffe1e9604437fd645e552bff229655037fd5961160bff468865d3fed8254870ffe5d160482ffc9a5d980dff2697660affd8a56560dff5918954affc0a5d921bff629525037fd745a550dff584895c37fd215a470dff58479603ff56148470dff4a581502ffd4a61976dff5d169487efd8655964fdf5d9655437fc9a61970dff5e519583fed8254960dff465766037fd7462521dff4a5855c3efd8659540dff4a5865d37fc7956560dff58159483dfd6551d70bff1e984487ff58148540bff46889593efd7655964bff26985593fed7454920ffe585705037fd865e540fdf595521c3fbd8159140dff585891c3efd8251960bff5287961b7fc7946520bff229611c37fd845a520dff219795037fc9a5d981fbf5d18658b7fd851e560dff52519583fbd855d140bff46887582ffd5a21970dff5c089442ffd8a59574dff5c189482ffd7a60960dff614095cb7fd745a520dff61879592ffc0a5d961dff619191c37fd215e480dff459691c37fd4961d62dff615291c2ffc8a59574bff1a9815c2ffd0a21974bff529865837fd7462552bff26987482ffc7a61161fdf559605437fd865e560fef618495c2ffd1a60160ffd58570443fed8254970ffd5d1814437fd6262540dff5c0895837fd6422510dff5d0694437fd2960570dff5c159483efd5651960bff1e982582ffd5a21940dff59189482ffc7a56520bff56889583fbc8612570bff5e80961b7fd525e540fbf619655d2ffc8a46560fef48564503ff56148570dff61959503ff57460521dff619695037fd811e560fef60574502ffd7a59182bff1a9815037fd615e480bff26964602ffc7a59152bff02972607f7d6554970bff629611c3fed6460952bff52959582ffc8a58570bff629621c37fd814a470dff4a5615037fd6456520dff1e959483fed8254940dff62579582ffd0a1e586dff595895037fd704a510bff229744877fd6222570fdf59570543ff56148540dff54979583fbd5212570dff588796037fd7062510fef45964502ffc0a5d582bff0297558b7fd8952560dff5e56460affd4a21d21dff465865d2ffc9a5d560bff26985582ffc0a61d21ffe60970502ffc7a46560bff568865d37fd495d952fdf59552503ff9625c140dff5d0894437fd6262470dff608795077fd7462520dff549695037fd565e564bff5e986582ffc8a58540dff48479583fbd215d140dff569291c37fd651e520dff4a5855d3f7d4659550dff5d069607ff97a58110dff46564602ffc0a5d982dff61579502ffd7a61560dff465825037fd825a4,0x964dff58189543efd464a560fdf615525c3fec2a61974dff58089542ffd6a54870bff52989583ff9525c140bff62960542ffc6a61540dff590895caffc8a48540ffe60079482ffc7a62560dff5d969542ffd6a22576ffe5d180542ffd8a1e560dff61879542ffd5a21d60bff5e889582ffc0a5d952f7f559675c2ffc8a5d564bff5e9565837fd525a470fbf60546583dfd2151d70ffb5d952483efd7659121dff4a586503f7d6461552bff468861c3f7d8554940dff52576597ff98a58120bff5e8695437fd7622554dff615795937fd7062560ffe601604837fd741a580eff5a1825c37fd845e562dff625595837fd851e520dff5d9895977fd745a510fef619645037fd7062550ffb54879482ffd6a48470dff565805837fd7622541dff5c089542ffd0a1d985bff629211c37fc9a5d985dff5c0894837fc7946560bff22959582ffc6a61574ffb0a989582ffd6a21d60dff5d0894877fd7662552fbf619621c3dfd6151d70bff5a9525c37fd4662560fbf5d946586ffd8a59470bff52929583bfd6860940dff59189543ff9855c140ffb54960483efd2151960dff625295837fd8602571dff565865d3efd865d965dff590895437fd1961970dff61879442ffd8a1e520dff60169482ffd9a21d60ffe5c160442ffd4a55960bff229651c2ffc8a55160dff59089482ffc9a61d60ffe601704837fd2961970bff5e964607f7d7461552bff62956583efd825d960bff1e9595837fd851a570dff26980583fbd5259140bff229415837fd811e520bff46879582ffd8a54870bff02976616ffd1a21970bff1e9894837fd855a470ffe5c160482ffd1a22560bff5a9525037fd495d982dff61879583fbd865d140dff619591c2ffd7a55964bff5e952583efd8659470dff551895837fd705a550dff618095cbff58148470fef21974502ffd6a48570bff5e989582ffd8a54960dff48589503efd4645960ffe591804837fd864a470bff629215c37fd855e460bff26976543fed525c120ffe60570503efd8655960dff5d189583bfd745a182dff5c989582ffc7a60560bff468865037fd7622510fbf5d9565837fd0a5a487fbf619625c37fd7462550dff5d989482ffc7a61560bff56879582ffd7a59121dff5d0895437fd1a4a470bff629655c37fd465a550dff62479582ffd5a22564dff5c1694837fd7562560dff5d089482ffc0a5d981bff5a9215037fc9a61974dff605691c2ffd4a60960dff4a5855037fd891e520dff54879583fbd525d140bff229655c2ffd8a48540dff58589502ffd0a21970ffb591524837fd2122570dff5d16954b7fd5961970bff568861c37fd211e580ffb5d98254affd8a54970dff5d8895837fd7656520bff62960483fbd8559140bff52869603ff5815c110f7f609475c3efd8658940dff618795537fd701a510bff62956,0x2fcc17420b65058982b3014f40a3304fb826c012d20917046802250109a080603da01db40e2006be033b818c00bd2058c02a281424096e0465020980f30070a033e018100aec04fe022d00f30067c02dc0132007000238008e0000fff61970583ffd865c150fff61576583ffd525c160fff5d186583ffd865d150fff61576593ffd5462560fff61570583ffd7454960fff5d589583ffd8551960fff61970443ffd8648570fff60570583ffd865c120fff61159583ffd2160170fff619615c3ffd855d160fff48570583ffd851e560fff61974443ffd6160170fff61974487ffd165c160fff5d181583ffd865d120fff5d121603ffd7461961fff61570483ffd7448560fff5d161603ffd815c120fff619655c3ffd7445960fff60970583ffd8558870fff60970543ffd855e560fff61574483ffd6560170fff61549583ffd8756560fff55970583ffd815e560fff615625c3ffd874a560fff58570483ffd7460520fff619655d3ffd7460960fff5d182543ffd8558940fff59574603ffd7455960fff609611c3ffd825c110fff6157458bffd7458520fff609615c3ffd655c120fff60961503ffd7460910fff60979583ffd8252560fff595821c3ffd7460961fff59574483ffd6560970fff59582503ffd655d182f7f619675c3bfd765a180f7f549675c3bfd6860160fbf5d919583bfd6860170fbf61976583dfd8559d70eff51968603efd7662560fbf54976583bfd6860470f7f605675c3dfd8651d70fbf51919583efd865d964eff5d168603dfc8651d70ffe5d980543efd7656560f7f485675c3fec2a61870eff5a1815c3efd855d960f7f549475c3efd8651960fbf5d96454befd764a560ffe60160543dfd1659d70eff5a181502ffd4a58980dff1e469603efd4662560bff5e962603efd815d960bff1a9851c2ffd7a1a580bff22971583efd5251960fdf5d98554affc8a48470bff46989582ffd5a4a560ffb0a9865c37fd7622564bff229765837fd865e564dff61879482ffc8a5c960ffe60170542ffd6a1e580f7f615475c3efd855d964fdf615521c37fd1a5a470bff26971582ffd5a22576bff629295837fd495d985eff5d1686077fd7662560ffb0a9865037fd8602575bff22975582ffc8a5e560bff1a9805c37fd7662550fbf48576582ffd1a22576fdf61552582ffd2a22576dff5d8895437fd5a5a470dff5c169443ff9865c140ffe591805437fd4262560dff5d8894837fd861e541ffe21970503efd4656560bff5e96454affc6a61570bff1e986582ffc8a48570eff5a1821c37fd8602576bff5e9295837fd1961940fbf61546583dfd8151d70dff619691c3efd7659181bff269815837fc9a59181dff590895c7dfd8259d70fbf5d889582ffd4a61560bff5e959582ffd9a60160dff1e989583efd7645960ffe5d980482ffc8a5d,0x7844b9925bad2d74967e4b21257952b6895624a8825351291a943b49fa24e5d268a92fe4966a49ed243c91cc48c2a44f9220490c6484aa4139200e8fc047b723c9d1daa8e834723a37d51b468d514674a325d188a8c0945d622d6916108ab6453d228cd13d889a544b4a248911a0887e441ba1f3d0f108741438da1b510d30864642ffa16b50ab6850942562113d081083c141b220ca105ee82bb413a208b503b6819440a1203ed017e806d40189ff7cfed87f1a3f5e9f9acfc327dbc3eaa1f408f9767c7f3e1c1ef98f7547b633d8e1eb80f51c7a263cdf1e5b0f26078d33c461e114f01277b73bbd9dcfcedda76b13b2f9d860eb8c75743a861d290e8ba741639dc9cd9ce64072e4394e9c92ce3f271bd38bb1c4bce1e6708b38221bff4df986f9037a49bbb0dd4a6e74371c1b798db126d4d36831b2fcd8f06c1b35e49ae34d6766aff35619aa1cd4806a1a34e99a688d2cc692a34771a2c8d0aa67f833de19d50ce0466c63345198b4cbe26594329619368c9526462320d98f50c7306351318518ae0c50e622a30f198670c2aa6119306918258c08860132fe617e98bea85f0d2f6897a28bc9c5dfc2eda975b8ba7a5ceb2e4717148b82c5bc42db396c80b5865a7c2d2016760b33859552c7c1626cb07c57ec2bd295da4ae0256af2b2e95858ab8855722a9595364a8f8541429e694e18a67e5303295e149a8a45c51f228d5945bca26650e128581414ca0184fba27bf13cdc9df64ea9272b938409b924d822692933a4995a4c5b25ff12e8496b44b1e256b92a40949249f724d8125fc925a48d02439920dc8fe047bf23c191c988d92468d2333918548b864566229a9136088e0442921f690e9886a8430d216e10a5484c8421d20e010610827a40eb204c9011c802c3fb91fb90fcac7dc83e9d1f2b0f83c7b4e3d761e8c8f31c79003c2e1df90eeac76c83b1d1d708ea9474bc3a0c1cd78e5cc724238da1c498e0ac6f9c37661b8f8db346d3836341af10d6986ad435231a738d254689c341d19e58cd8c663832e0193c0c89863ea31ae18b38c3fc615a306618048bedc5eb42f0817660ba145c7c2e0216dd8b5fc5a5a2ce6164a0b134580c2bd515c70ad4856002ab915440a8d8540a299d14a00a410517a289714280a0244f6e2770139489bb44d4c265f13170979c4b40255912890932c48f2243d11f008e384662230b116788a20449821ef10d408584423420c81040881143ffc1fcd0fc887d543e1c1edd0f50879103bfa1da00eac87448396a1c630e0e06f54371c1b310d6f86a34348c1a150cdc0656c321218ac0c328604c2f82177a0b9f05bb02d3416320af0056902ae615370a6d051c8284013c309b884c7c25b0127b091a047e023201149087b842ec2114102d07ed83e7c1ec60f06075a03a0c1c4c0dd406c1034ec19bc0c8c061d0,0x85e4ba1259492a1493c24953246d921348f7e471b233b9174c8a0644a1221f90ec485ee427f2103905e481d640471fc68fb4c7c5e3d8b1e738f16477ee3b951d788e934735239311c678e15c6f3a370f1b358d7cc6a9e34c11a0e8cde465aa323118d18c3fc608a2f8b17898ba6c5c1a2d7f16628b02c56fa2b05151a8a6445206287513dd89c044ce6261112cc8942c48fa23ef11b088a9c44322175107e8810c3f6a1f110f20876cc3a761cad0e1a86dec36061a8b0cfe865bc3196183d0bc185bd42cce15d90aa58529c27ae131d0952848b4233e10e5083683f241e4a0ec3070f836441a060c5f05d282c04146209a304a0821c40f6e07290363819940b820507023180ea405de024b00d38040c00e9ffd0ff807f9cbfb9dfd40fe597f03bf6d5fac6fd277e653f1e1f84cfbdf7dc6bed19f614fac37d43be8d5f3dcf9917ca53e439f178f86a7c11bdf19eebcf7227b683d9cdec58f5da7ac43d4d9e9c8f4a87a2b3d011e77af36b798cbcaf1e4eaf22e78f93c6ade286f107785abc18de064efeb77ccbbd49ddeaeea37733bb855dbb2ed9276a5bb3b9d938ec6b76123afa1d76eeb657589bab31d4f4ea3374fbba719d2e8e92274733a27dd09ae7f073c439d05cdf4e69d732b39811cb7ae581729239349c92ce42371f3b8e55c69ce2e6715ab89e5c464e1e070ccb8549c216e0b970443815dbff4df926f9ab7be5bd4ede6b6f0cb76f1baeadd186e63371d1b85adbe66dca36d09b5e0dab46d313686db366d9776c8d36379b102d82f6be935eb1aecad71e6b66359e9ac7cd5ec6ad2b554daa02d4ba6a44b5085a788d37d699034b91a50ed24068f73469da2aad1036853341519feecfbb67b4b3c5d9d8ace736716337959b26cd5766883335198d8cc1a65e9b2e059648cad2654b329119426c9d764bd324759196c8846429b20058f74c75d638b31b698d26c64162fd316758aacc50f6264311d98848c3dd61c5b0ce585b8c27f6121b07f18354c14d607db027980c4c0265fefafe8d7ea2bef45f56af9f17c28bdcd5ebdaf44d7998bc9b5e2faf061778cbb695d8baeb1574d0ba2c5cf2ae6217240b8ce5c43ae0d56fdcb7a75baaadbe16d78b66a5b0c2d7456afeb5225a732d225682cb3c459beacd0565c8b29259202c7e56364b160588cac3756142b0705814abf895f36af545786abb195cbcae1756e82b5cd5a58ace556442b10557f4abc955cc2ad715614aac3553e2a90153f2a9b254b02a46551a4a880541ca9fc94f6ca764537e29a7d4cdca61c52e5295e14a36a4c952362909547a6a38c519d28ba14542a24f50f92870542f4a13e50812823d407a9feb4fd7a7dcd3e6e9eda4f49a795d3c209dc94ec6a74ed39fe9cb84e3e270d537f29bbd4db5a6c6535d09ab74d38268d133f099b14cafa646131a2988a4c272601d2f6a9,0xa6c00283d1bf203e61811c8324f3724e68119879025e24e5e405242a8474cb8dcc89f9003f46e5e00b9a046610b449c26c3ae40744f58790108c93cdcdc830aa172f06102717bc4e8e2a8df9007b2c289c031ebc723e4042524e3737202129279b82601e6e205241a227e404fcdc833c6492d896487c3a24e844f5e39013a011cdcc8dca487b44fc80bc41138872c3c80030033f37e409248488cc4e92cfc80a485b4fc0fc23e273c08cc213b9073724e6109c803da59c4e218d98788408e419249398b672021e17c939513f2007e8dcb08173715c6f1ec111272f15ac24239003fc6e89cf98493f20c93cde041b901090c89279b80c3022c93cdc93930a822c93cdc939790561e2b8dc3d90844e7293c803d03f08f8df139f91f202135e124e37356110fcdc8472044e6c1bb60d17062982d8c15960a0704a1822ac1026074f0387819dc0b6604ef01ff80cec054601b300618015bff25ff52ff477f72bfa65fc6efdd57eaebf3edf906fc217ddfbedcdf5f6fa837d1bbe6fdf2baf9117c78be18defd6f7b57bb4bdc1ded76f6597b06bd705ea66f4bb7a2cbcfdde72af3337973bc9bde41af1ab7899bc345e0def00d77d5bbdd5de7eeeb17727bb705da92ecd1762cbaed5d622ea8374e4ba495d102e7c77391b9aadcc0ee5637275b9175c79ee357714eb883dc35ae0f37027b7eadbe0ede8f6eeab7575b946dc156de4b6c95b52eda1f6cc8b6465b0ead7d16b96b5a7dac22d5576a64b50eda75ad31f6948b47b5a2bed0a567eab3d1d9ceecde966a2b3335987ecbc765bdb2b5d9466c9a56480b21cd8fcac7416364b18ed8b86c51f6227b0ead863ac28f60eab051d819ec0415fceafc3d7cd6bdb15e9caf3057866bb8f5d6aae91d731ab9155c0cadd256d76b6015ac4ad2e567feb39d5992acab56412b191588cac17d5f1eaf17572eab68d5a56ac875612aadad5562aa2354d5aa475511ea81753c4a9bed4caea5c95287a91ad4736a30d5134a881d42c6a0674ff7a7d853dfe9e454ed0a744d390a9bf74da9a6b15344299a94c8da62352ffe975b4b71a58a52ade94b54a08a4e0d25be925148eca44d5217a900347afa3b9d1cb28dcb469ea326518428b934598a2a3513fe89b3447ca21550f6286f7433fa181d0b1e8517424fa109d070682df4133a070d026a809140019fd7cfda27e2d3ecf9f4f4f95e7c373dd49ebbcf412797b3c769e124efce77593b709d94ceb8a75213a289ceb4e58e720d38ca9c314e06e6fa9378d9b9dcdb7a6cd736199aeecd5aa6a4734f29a55cd192680f33aa99ac4cc4665693278991e4c7aa6347315c98904c33a60e3303597f74be9e5ec12f2f97694ba5a5c732ddc96cacb50e59e32c9f96214afee57532b5795884aafa54ef2a3094ef4a6e252f9291f9466ca21a506927ed93cdc9d264e1b26bb9334c9,0xc47480aa10832a3ae405e6e1b02772048292cc23993f201c61e4109d8a93f26e6e6e03da4826213c80dc8c25e37117c80214653f204f79271bd2321e66f1c8213c612974dcc9ec2e7200741b0bc404396c4960eb901a2480c897c8032286363710c5b39013880820f5c801d065372029211c45e37052626fc80248402f789cd1259bc278d9c82079b9000a2ff8dc25e273710c4fc80a49614684fcfc413672030c600bc4291887e4112c328410da8e4603e9b88c083197901f9047884ed249fc7b81f211189c477201f20c6e5b0878512f2002e9b01f80ac6e60149971bf200965e6fc80a4a082f05ef1393f473721fc80461271166cc28d214f202938dcdc8291e3747e43d0b9932109e6fc8f9044941e7812593906378965b0c8989fd37e40464bc8e24a7be418dc8798c226c297c80843f9047b24e17cbc829ba2623283cbcddbc46184e13b90183615be40524802b906370ca92cb02330c27612e0f8af2066e8e2acde34b7b01d09cd9e193c09646d971bf202928e411269b9058d8c24ccdf9046c84f03e249b3c6618124fd9bc29e4052504ef24d37e4001a1d0653c61e4109c9f93722e62100339007b6938dccd2630f20a6e4fe139b9180fe6f12c277200831951c4230f2084f5248193a3b378c2c278ac27707c80f5e084e370e9c81a49b1ba6ce400e89c8f9ba4be405ec2808709c8613184bdf20e20d24a34274710e4092c9396c10c43ce0fd93d610158df90017210887422cb6087119c80d1ef8ae370d9c80208363f20e2118613b492f8d2ce1448796ce418dc93994272000612c94979bb78e400308437b51670d9c5790047014cdda59f0ab61213c8f9057807f8ddb224b096c115c812596410c72f6cdf901860d852c817f9016c2720892426363372c08cc309f8ab09696cdf90239bf2084ec25bc1498c241881a78ab098c3c809f93284e7e21c82139492f31848314b4309e2acdf9046184ed2cec2624905e21c823643f39378c3c80bdb4984e6e6fc8213b0909d18483103404e8c2cdf9018984e6e4109c38378296581198613f20692cdd8083062a98c3c80af37f61309cdcdf904270ff1ee0794b3f20a6e89cbd8402f208c309caf1230f20692cde13b0103ec551c82b09080f3cdc202273a49e405ec3a1372b498c3c80acc272f15811985a2828e40cde13a38ac6184fc800734566e78c3c80af4272408cc309d84b49e6fc818aa39be6169302213f2069678c2c279034984fcdd8a9f9bc61e4109da4b4b37158119859bc276f60a390238ab378c2039bdc27e40741fc80a488b08f8df139f9b80829289f9013f37102c202913834e40064fc5484027e41cdca5244595307e11f1be27380ae4052445e37c4e6e40524008800158df139d13d61e41924847373161e4013b9ba27292121f1ec2e1270be6cc30239063711249cc52513,0x96c43243cfcdf30f2049649c272418108e6fc823642781f1eca5879413a4d86339018b2e37e4148d1fe1521e62b789f9003a2234c6e2339006c2f2301e1ca3285c475c802121a4c08cc309d9d737e400c11c802880ac6ec9ca9b0aff201f1566f185bd80e84fc80ede005615e400ff1b9293b10e41184bf4276921c0c4a0ada65e400e899879bf2049649c27408082807ed8484d7802f8ddb2720e469e411e23613f26e45cc1b00544bc6fc80a029938516cb8df901b8800fe4000e3288750c7810d2613b78e6fc80c9b29b986e4040ca12c2122ae418dcc23214f20c6e4e405ec17a1730821cdc8e32f20c6e12c0188001e80145b028e37e405a6f184c317b84fc80cd2630f2084eceb9b81f3e272f1c80b0a3f46e85cecdc9396c21f9253df203a6ce4061a9b93886780d817039c3ae401091c800790969209b1b9b9042766f1842718737370d8c279014927e68c309da4b78e6fc80d09da49090c9cdf901b1b86ce4023020f153715cf10279016c66e43c93a3f4f37e401b0439391f20c2a8dcbc16147e5911cdd24a4b0d9c8036a41396c2f1c831ba3f42e6c9302330b37e4049d461f9063703c5b0289406017c6e1901ff20356189312d43129e406e4109e3094966e61cd4dc32f20074230a5b028f2008f8dca0fc45f200158df139b8ab098c3c809f93784e7cc30239004b08449c45e3747200f20e83a24b2f158c25f83872031b09ce89f90161e6e1e42018bf720e2b1861397c37378119852e127c92ceb902424e6167102213f2066ed259d239ba0829389cbc7202f68109fa584f20893cdc9310f37150d802823b37697c80fcdf9006c10e4e47cdf9020f2f0994bde491009e2ac2630f20a6f09c9f9c9d18ce4062d36150cf202d81471b9630f2084e618275153183c4e2319bf20280a07fc800bb78c6f89cf88c057202931971b9b1ba65119c8091879033767109d9d3493f208139e093b372d992487a174f378139e3901494ca6c93c80bda65a6e5e47c403d03a0e55279000f8ca96f00300be3707e423901d42129e4012c805d36109e400ff1b982db2364ed97900863279e20069a4f2024f9860403a4f23e2112f902860a0138fc40b208ce4022cb61b91c4be400293280fc6e1e91c8f3c409e40524aae373f106c31279044b074d9391a08483f64f5e31bf2002e74a202b90165c6e5e409b28a83fc6e028d98405637853c80a49846637053c80431630f2031109c27337300a0d9c8225e372f1021fc832488624e200f12c05720c6e1943d1b3c409e478dd94f202927e6fc82258580ca104cc2613c69693cdd8a9b1b88c8cbc809c813217ba6f525139b9bc276931a5a5979b96c4961e7902492f67e6f12f9044900c9b0c9b29bf202a24c93c800307b64f8dc841cb6337119c809c8c07f37116994438712f7c81388c32f200855254105,0x3e4012f13971b88607819790179000a0a38dd93979ba3f4929b113a0fe405ed1c8c84737e4112e3284e08280e109f9034b2f65e2a4de30b0920bc80834276f09e21c82a4934214899079c057200ca52e9b978816c10021b90179180fe4023038e3708319505b0b088ee40590ac2391f102329949a7202148e47c831bc65a920193dc3a01e9e411e23d93f8d9cc48b9d2896cc6fc8094dcbdf20c47525079836720c6e00c4004b37208f04fe9bc6c22e6892cdc84c6ce405a6e19711841119c80dc8f1ba0fe40231329b8842d01800f9028610e7e4109caf461206c62b8dda4f208f68e80320a4f2008f8dc2a8653523e4112cb2c4950c62f014791e37653c80c89b9008bc6e194bcc4298471191b2249a9bf2023388d07978843f8925b3905238f67c6e23313f202623e41194bc3374966e40239328f9bf2084f184271062067e411249b9056131b0d9259b86ce40a30b88c05720c6f194259b9b97b117c813295c1f2066f1858494184e7e208d0b2720892430c5851b9494f789f901b1b88ce40994909d9bc69602d240fb153f37e40ce8ae46184f524a1239000a0cb8dd25979016c41292f1b9791f20a6f924bda6541e7e209279024b24e5b01d10f403f033c8024e370586e471979053709600c4000f47200961971b8421166015c80a8d37c4e5e6f854407200d1924bc17b0529c6e5b087f2010c5c6fc80a49614f789cd85790637ac20288403f64e8c479e20493f2931959bf20413fcf102790145292cdf13a391a0fe405e225e374ca7cc30239033749649cd184bf72084ed2cac179042766f186a49862754553c4225c49e40a18948793f1082bc803c83ac4e12cfcdd137201165ec329ab0c38c6e4203db27e4078c2c2427720e6f09d8a9c9504b085c8032d37373781289b3c720292194fcdc0344bac3c8193c492108015c5423f2066ed2c93e618109e6f1879042709c52cd8df90164a4e8fc8c98bc720e461471bb29317b30ccdf9006c2f208f0c563613f26e6e2152790264268429139c473616c9c8f90171bc7be4052532971bf200740f03287b3720a6e9908ca2729194c9c829ba0c2f37e4109ca086767acfce23114f20c6e411902330e3706c10493f204227e6e52604a65e406e47c4225f200a0618271f9053741e5ec20169bf20a2a9909fa27300ae418dcb2a512e78813c8d94f202938dcfc8c07f2001492f1bc653f1584e039a2c6966e6496cdc93f200f5984dcdd91879e411248799c272084f18584b3767e40d109e9b864e40d24b89f90047232cdcb18790427692c54bd9113f102c25b12588ae405ec3ca3882270aa4fc32f202922311c4124834a4e92f901b904270e04fc8b978ae37083c80328553661e4002825e3785266121c23095e84fc80d8579ba4be405ee148873f2009610b1b8550ca6e4061125e27272024f9271b,0x42727e4c88b9b9ba3f2c292421a27e40766fc8324a8600c8e8361f90149c6f99713c7b3661e40cdc93a86c928ea04006493826fc8230c272f66c2bc811d06b10f12cdc80afa6c1f102c9c80400862d864698dc46627e405e411e398c6c62a4fe3d9e13b37e4118427187373787f1263df2064f1e0fc402a88b10e194bdf203d37e409909f909e2a89cfc8f1b83a0f623232f2001e8e47c439044b0a00e84384e47108971279003a64e6e411e29bc6c62a4fcd18584f2020dc55bc42722282c9c831b8512d85e40cdd2586c240f66f1b21388c2f37e401902ab7830e666ec278ab838d309cdcdf90178101924bda65393fe40514a4b370d86e211879013469309c851e30b49e404679bc273164c6fc804316c2e15e418debc10907ec9cf4dda4c6184fc80ade00503f02f8dc94f203f37af1c8311949c1052c84e270ecae474dc1d08c8cbc80079d8ae37e411ed1d0066921b11c8f881340d692d24f203e7881243f9063789649cf9e193c09646d9790149c6e88119873c0420b849f9014e874981fcdd1f88ae405ed321f9bf20292990bc2273623118cde32f20286c09610845e37e40609d1879000e84e5159b9f900170ca0ff1b970af202f69929ba0c37370d813b900414966e418de259784ca5c4fc80b0a3fc6e5e10b9d9bc61e404e213b7b2924089d2791c08e6f0249f88c29299790279bf2029709e3084e20c7e405242ae374ca5e6e8fd24a6c44e83cbdf2047200078dc4004b0d86e41c8ca4c7bc538dcc9ecade27e40524bc4291f20c928d10510f380ae4022f1be272f37e401e624a652f10e4109e30b49268428f4dc9d83a0cbc80a42a30f202b2d259d427380a2ffc8025e37c4e6e6292c461090d613b901f11f3710e92e3297be407e464238807a49d927904650749e474dc07f20c93194bd8068749c6f1943db4901fc80dcdf9004e8c309dbc1b91f1001e1e79003a0ca80d1cdc367202f621cbc08b3f200961b02108bc6e68c3c81a4c272b25212033900646938dcdc421fc788931ef9016c3b78e4005c1fe378ca03cf8dc1e265e40218bc8115065c6e00c259b30f202f092d9bc29300a1178df13f202f23af003c2172049c1723293a4f372fe1b39017b3006871c829be498749b0cd243872084e4e21c80b62865005e2b8dc0326c0f7c80cc1630b5b66ed249a427e40844d8de3df20292194dc819ba4b0d84c92cdc3607ae405014de28af2007f8df139f9bf2001fc8c43a060ca12d017f900022f789cb09f9046162a4fc991b9053722e4fd1320f3309e2b09e34b4b66e6e4049c40003c6e12f30c08472301e02b9014ba6f194f9243628ce40cdcbc42a4f20c464289a20f380a0978dd14f202803e40a1832887285be46ca7900862d37e414549fa2641e611c4a7900f9bf202f09942a887372030989d259390637104d942894c200,0x1879017b69309cdcdf9004e8c2de213993cf100341b3903490747e46527906370ed1ecdc569b8410ca157901a34b496f1cde139791f2009610a3288ba6e7e46924bc737e4092cbd85009c9e410273c1272d98dc2590f406c308d2f901191f200aa1971b8420967e47c4035c4b475c82249f8af373165ecbc7200d87cf10279004b24f8dcb610f47238138dcaae78e40524fc40366780841c82e43ae408c6e5b09390fe40218c8e390337e46138438393f372f05279026444e6e6ede39000f6f7195459f9b879e419250197b0d878c3c808534966f09cd88c32842e401712c13a3a2de6fc801208708219425a045e37e409949187903492f709c889832a3b075c831b951a637e40230361791f37af05270414bcca4242572052348118df3088c24fc80e9e78806c034d241d7203a19e418dc9310f280ae409471b929280aa6f89f901512f10cc302324a3ae4049c3d219bc27670d2634b3a300ae418dd3284b2c27e414de30b1527e60ca8ec46041e418dcc59390051c6e5b0bc5630b09e40cde1384f396c11c584b27202f37e4089d32879092684f4dc3272030c5cc29ee14f20292cdcc02928e37253c80bc80056370968a4bc8f9bf200f312532a0f3f370d89719d649e40908e61025e27e404e414dca8a6c27101041e832f20074624c4671bf2021e5cc2cdc46429e4052d90273c720496cdcdc563097be2063613f203f20a6e5eea4a2641e6e2a5b042c09c6fc80d1ef1b9490b9c80329b1b96c413c80a4979bf2041e9943c8493737e411b084a492f68fce1b0adf2029244c3cdf9017b29289c9f9c9f94928acdf9006c323cc6e23390123097e84fc81a49630f2084ecdc8c95c1c3f8d9c8207c4988b09d05b02df20474409d1879033ae6f09c0f9f30c080158df9044b24e7e414dc3584e0f25cc3c80bc33785292cdc579b86c3165e39017b3e37e408fe939084326e6f5e390149c52424a5e274249e6e21f9024b2f70a4fc4007c65e40218439836720308d2c9c42a4a64e404d0852273c78e6f09f9014b8f703e3620b64090079e39004bc6e74d81082e649275c80c5b39000a07f8df0a9a30c27275c829b9487f202d98dc28952d929e400e894df9004b25400c329b9b97f0d9c80bd980362301412e32e37e406e405b087c3424e02a0c9f3080ac6f0a79004b3737c925e3902652f6200fcdc3625c675c8324a423a261198df900652f378c3c80c4c2709c620f9249dd370cbc800343a385ce409ec93e618100e8e8e39063724f1eda4a3a810019348c05615e405941fe373f23e6fc810797b4ca22cfc8c2d860e40218ac063084ee4007e13b1566e8e4683f1b9498f6997901d8484c81f1b19bc5384e7e215842af202100e42b1e3de37e4052532979bb78e4109c27461341520bc809b887c4e6e6e03f11f20212d24c9ec3603a0b9c80b18790,0x11a4f31e41c411c8e9b93430cd24bdf203f202934dc1614227e684ed26847202723a6e4e883186693c80e85d40251c6fc8087991fa5181f19543f2366fc8110223634962acdf901a0246c66fc838a9513a0f8f7c82a4e37357b2be4eb90226a6e83ce4fca8c6430ecdf9018b6523e4112623c3f88b8dd05b03ce49c965ef901b91c0f62a5099bf20347b64fc801d05ac6e684e4eb907108c3524811f8823ac9348f9024221e766e96d2e7204931b0d58613d08809c838ab373b78e2103f9004ee62154e9159bf205168fe07f238ca800d985433374928ea93f2044088d8cdf8af202a6c0741e7887208926e2061aa4f232f7c809a1e1fc498851e71bb23e40c9d15279033730c4e91320f3986e474579015f2744199ba107c4944fc803a161a041e414dcb617248062d90eb90537313f28a156323372f2368b03d9bf15215c80f020bde2767bc838ab3726888d901398b49e41c40cd26367208084c13c40b6523e6312620f2089696ff09e3094ba6fc80d5ef9013a2bf88e9ba0f3b7f81fcc524f238cbc8125f104c088d8d2798f10e406810d2636720246c809c838ab372f108c86189a349e4066924ea139868c9c829b9dbf949e411939894b84fc4111b311b374b896f902493b4981e4ea13142e21c80ecddbdf234b601f9024981e88111b19bf15e405cffc8125d2366e43cd09d9b8252b7191bdf2029288105ef05b37e46cf49a715e409c160eb907100f3127919e30f206924279bc273710233c80851348c309cf18790349213cde139b139492c28d39013f37372f0524bda26e404fcf187903376704d213919692866f187904272325e2bc821380e0911859b9f8ab37e41185bd80e84e781ecde13c6c893c80c13a30f20675cde1381f3f23e4022f1b86509610807a19bc6184fc808c979bf2029318613b7827eded1c8f9be15e4003c2084e0c419425a99bc61671c8213b3a6f67e6e58790227088138d1879042766e464bc4224f20896d841a7236c88e204679010a269186139f9b86c2f622cbc72010e7293c801f80ac6f89cd4df9026427e45d139b9bf202939871390929672f089b90637896194c15421065275c80a1952580ac6fc80bc8025a842ca4e21c811d6490f41b0dc8d9b86b47fc808c9a30f2084e4fe9b917322de409243283a4066e21c822583a45221cdc8d0788be409971b9980c61232c7390427692c559ba79bb09e404fca486c3723e405ed2486ba6e6e47cdf3c40941e9979014944616924279bc27e406e6fc821384e8c213cdc8e04637e40170a4c7b4ca8c468d31bc65e40524dcdf902060ca21c2598b605f0b9c809c8128e372d84e405e132c4bc6e56131878ab3770709f901f3c16c813c819ba4b36234f6cde32f202926e2000d3603ae405692ceb9bc6984e07cdc80b6178c6e8ff0a991a637e405b09390fc927a6f,0x93a84fc80a11c0546c0978df901536649875c8107f10314967109e3237be40cdcf5859bc0c4b6dec03a49e40889310f88308e404d391a6587e9c4ede390151c534dcc8fd28f204851b19b9ab0c27a10cdda4c0462bc81109d9bf208c25e4a01a3600666ea1924a3ae407e20d248cf2030c83cdc561ba65e411ecac2204e7864f8dd91f20a928e47c8007e379161961f9d0cd3d66fc82329624e09ac310798f1064fc8225908546c809c838ab372e3da6fc8d84265e40464fc80a5a64afecdd13998484e28318798f2084fc40a5a4b628bc6fc808cdc2e7208d80e8a89e1fa6c41fc821b9993b238931ef90637868741f5e388731e40140c54790180a6e8988b9b8820f90c9b03a7203164c6fc80bc71510e5b0e5b043e37e404c6e1942ac3f230927f9b1bc537e4645f90200000fc2bc8f9071090e0e432a711b09c7b1b390715482cdd0c2636720a92cdca02823b272118df9047a396cc920eb900422e6ce205249d723297c80f12593c0181521d91c37e40884f09a32715e40cdcd09cbdc61269c819ef1566e841fc569bf23e415ec039c36035e4101b8ac7bc6e7a4e43f0af204858dcc954bda65e401029b98a4d37e404fc0a142c4e747ecdd24a4748b1b3901eb0c27a110119bf20e2a78a21eb1bb27e40500185790487e201941c9e24f206471ee1bb27338381f8f790033e471978ab374c088d9c559bf202c27e4103c1d2498d9c401f211a041c6f1b390162c80e8b8c9e24f20c6e4210c2193e37af0c8f904513f23a2acdcc0151e4040c8ba00386066e38d8d240323ae418dcd49da4f204338dc879b91b49e63c4207f200f27e46cdc071492b6def901e36404e2acdf901584e27e419909fd3722e7c6fc82a4c7b41e89cc9b28aa2741f8df9043f3e27e41c433213a29252ce83e9ef20e2b1ee1b98b608bc6fc808c2224887475c42277230cbc812e0c1b53d84fc823271566e8a129b21ff2082f8dcd45791f2009d21f98807e208e400e82e3378d852698f791f20e2b03cbdb374449e2188c9a7204ca6a4f91487f15c6fc81051f0496ca47c831bc4b314984fc80a5f31e21190e99788720e6321c270073c78e210ff90449e621563da29be23c7a427907154ca7e46de19bc65e4103f8aa3f44088d9c559bf202d37e40524a1179e464fcf5ecaff202749929ba273a0f037cc791f20e2021cf4f51d20fe461e7907103c6c808d258ab37e4060159879004ba4f8dcdc4293e4950dc811a27b3c27e411b12483e2d7fe408999b94b41e68d802b9004bc6e5647426bc36a87f8df9041764e9c92cdd4323aa47c80879cb6649c96a1b90279360b8c8cddbc720e2a4fcec8e1d36ae211279044b64e884ecdca480e2b7c82321d36720a6e1e425961fd232d910a28e37e407c925b0b2079210864e0eb9004d2c6c613c4124f31483c8125a2b0c27a110,0x730f202a25fb139798d3d4ca1e790710350884f011bc710e63c81a4a087e3724dc80259624c3a647c8225f1064e7c7b1b184b37e41c55209d918574cb0fc958613d08809c838ab3739842c858791f2049662f660f9194966fc80dc8107f15af089e1fe373e23cd409713d3de404ea9ba107a6c44f9261d710e40789313b907106104d391a65896943398420d27e40cdcc14035a6c41e4e211b311a4947ec2798a8ce40987f11623e3764fc822490844278c242a9bf20296666f1b390087213f28a10c0712bc249e41cc4937102ca7e47c428a91930d527901064531c1188cadf2030d89cf82390349af04269be65e46841e9b398f102f7c80a493f471089289f902652690fcec8e43637c93c8202b273a03e200ea32f23e4021ce5b02380ae418de3d191bc274f703e367202927515c8f88007e63c8124c0f47e98111b398f15e21c80ccdf9046c88703e139193c2747f03e36237e406a6e4d0a497be47c80c89ebc509e4105e1fc373c27274d2632720285c40f5e38820fe41cc4272273d784cb8df9004b2a0f44e9b31ba0ce415261fa08cf206934dd1360b22e741fc43902278712181f1e13b3700e1242df2034494d81a225f1030dc80e5ef13983e405259b999ea65875c8388169b97b4d9c821d040317b66fc802a9862f1084f021bc349e63c80e43cb6710869c820c999c508808d2613b7be40cdd14dcbdf20c464eb1398217200974dc2b94a4c27e405459b93f8c872025279190a30e4df901f8860b67b1939013a3327c2b5e284b2387f0df90209ff10292de23272004bcc613a79046c612cdd2596b0c27a110138ab37e40724dcc73fc49e4112f8810c4627e40d2484e29a6e68d903d9bc78e41c54439e91f104141951a7204327c7148cb663a893c831b9e0c803ac312f1bb27e40726e5279197be4056139879013fa6f89c8b9e4332364e127906378687e2bc80bda65a6e418c54704378e47c829be653e61e205279013ac4e52ce46633d15e41184a5b3784e8e4045cc0151a6e990dc40204864cbc821d1b905370809b0bd94a4d37c4e4d0bdf20300781fc8388378e63c8f8a800496c1150d2057202e0b2f6cf632720e2acdce83e8aa6ce4089f1bc3f3f202d98dd43923634930dc81a5979342746f03d9ef154f7c80e404a4e272144df901a07b38492def91c65e40cdd102213b38692ded9bf203c6c6920eb900422f1541e89e1fa6cc6fc80f09c9f94566f190a1eeb084164fc829b9b24806874c9f905373465e41c5798d236f1c40002224d23413c4398f202ca7c6e5b3900872208c4e4299bf20296601f1979024ea6e5a6e95790186201921158421327c6fc80f09e13349e63c82327103a6ce4012c2108ba6e6c465ecc1f20292cdf139f884494f649b901653137c4e5279017b2c27693423901113a0faf1c561fe37e407693c4230,0x78938df9010c420f4d91ed0672090d8dcfcc61394b2f3187901a9b80ecd94f79193ae407e2ac8e3de374cbc80c13831710e41cc6362423e3d66e5ee32720e2b030f12513a6c09c000a4d390723c16d84463373a0fe2185428486419c80e422b0e09c6ec9f9044b3f202a34dc85101c4e63149b09a72021456131859b84484fc80a59e24934e2095532f208967e20d248c986e40990dc802023a8d800cb1b19c249675c819b9a13b3866f013905083531c10618ade65e47c80ec2713d37e419909fd153e0b68b1919bf20e2a428f984bc13fe205279897be4089d34dd32887e4048d9c819b98723238bf1ef9063764e6e208229ef232f7c809d60b417bc4fc80a49592b158d81099bf202c86093c8f90637868630c416a4f23a6fc80dc411f88c41fc8d32f203f1090c99420720e4683e1d23887208d909e07c4947400100da13d3de2bc819bc643b23e209b106434e40524f09d84b7846e85d1ff203f1084f021a4f31e406a2bc809d02c208ce418de36139054944e83f1ba6587e7a6f88e24b78cc9c80071c93523e41cc425f102ca701f0fc36637e40584ed26047202164e405271b96c2f2309c03b887208c3cc4222313d37cc803b9013a342766fc81a4c268c8c54f4dcbdf23275c80b44330f206925fb1393f386c01f8543a43ae40684f1858a94266fc808c9e91c45e410fe45e3721876124de8ab78e464ff901f98c4910fc402a865e407e414de430404d90e8dc8025d7844e9b107e373a49497c413672041e89e1d20360872fe5ef98f20e2092d09443d72066f1b0bc8225c42c6e1b0bc4124c7be40c8cb29a98e27c5256f90186317b66f1b09a63de41c5606231193f28a5e19bf2029389d04d0a4d372f789f901a2486b0d803f90169e80f415c4391c65469c810ca624f1021e499437208967275c8f90062a6e01cd21a02b27647c831b9a24c3f64f14621637e404210c2482e27a6f992a4f20a2a84d883e3df20e2b8dcd1b0c5b37e40409c07c9fb37e4058d802823b37e409e8c404a490ac4e4df90188cf206929929ba273226e204d224f204ca66478de054518f30079032741340934df11f2001c6e2a83e1bf234cbc823d9cc51344d9c8085169bf23e4083f8ac8b4cb0fd04d0c3537093c8f90190cd3d81fc8f9046566e7647426bc6156d50ff9063764e9e20619a4a26e40464d4169be27e404e8b89ca493ae41c4107993605da6fc8027169ba4990c9b107a27e410e90cde13c08e2bc80a5b30a842c6fc80ac249be27a2a4ff90199ba3fe41c563240c3623a6e1242df2000e994f88d065374c9c80c31907a6c87089e24f20a6f0e9109e133378c9c838a9a36404e63c838af10351526e5ef906272bc684e4ff9071566f190cd1613c6166e42b907153d23031157887318cbc818a84b4964c7ac8f88327869c820ca39026c0f213a9b9,0x803172300e6432cdc20c6ce40511c03a02f23e409271b9f98c1741e9b390161393fe2052407731e411911c4202a27e400f9367153879e40102363372f202a389c85101a6e62f71b19be3de404e8c89abc637e4012c329b1bf2041e89d3647b90c7099824b6720c6e5e4189c8ce6127f4dcc23887926e404e4083f8861544e13a431e25f208841229ba6c308c0c1c80782311d372135e390349c4e8e6213b91862e41c40039cb0f312c85ef91f2011676115e193e15e411471bb23448680bc8f906372d15c4e4eb900142f1584f0219bf20295fa6e5ef91f202b234ca173902492926a465902283f2905a6f98407627e404e8fc838873110e41932c4b3949c4e4d39014b2f10af09959ef2080bc54f09e13464e2bc819b991c72081f09c43c6c66e7a460fc28c6566fc80d4549d7230c5c8388007380acc212f1bd27e406e208229ee27e404e8bd9f1ba7b093c8f9000e3265119c831b9391a0fe40cdc8514b346c09602b1bf202a3a037c8f9071010e6893c439020f4d889d1d44b47102f022cb0f232f7cc4b272010ea87e03c13f200d98dcd4dd13f208925ed329a98e61c4e5ef901862b2711818032f2027104ca9264372049662111979024e08450d9c830a82707c8e8c5278813a44dc830599b0c3fc6f9e39071521878715e284c05c92c8f9043764e920a23b91d37e4001e249c0c04e81fc8e32f31e41c418a84b526c00fc569b97b0c5c8020a236309e415259b951ff10e409263640fe6309cbda613949671c819bc6430426f012c32d37e40643292f9046c66e00cc58424720484cdcb224b3905cc3c829b934a9389e8aa2b0d3dc124201b72064f1078ae37513f28bc8cbc337293c80e9b01d720006100a0d9c1b0988718790427283c559ba81380fe401b000449372030815525929bf202f7990a4e273234893c40937202ca6e211b184a4947fcc546720456184f42202731e41c57882213d378c25ed9ef202747e2b4df1197be40994cc20bdc4ee4699790040a6e8a6e5ef13f2027452689b39008c66e541e9b113c7be2bc831b9f0ad27475c8043a4b351526e4671393fe406a1109e02349e4052a24079010a2f34df919f91f206104d388265232429061882f23e414dcb82e32315284cdf901991d370921153283f361587421c32f20e20609c4eb90187266c612de39013fe474569ba207c6ce411259b969ef23c6fc8232a06e2a9ed109f90238492dee07b37474884ecdf8ac268c9c80c1269b97b26801f91f203a0f4d9cc790715e201acf12593b23869c8225f103a4941fcc791f20233c4043a136720096426bc537313fc4f990bc337e40524e83ebc720c6fc8d3284b3a0fa6e1240385be406117187907318f7c8e321ca4f10275c8ca5f2037100e89b39020fe2a667a83f91a65875c83881c4726ce4036621b02ef2009c5a471461fc8,0xe6cd9c8388149269c8ca59f11f1047e23390065371001e01e1f88ce4719790214556100e92798f20e208fe06270aa3ae411b043a4b35150d112cc3710e47197900874e3104e1b11a00f4f660d81c788434e41066051e13c08e2acdf901613720c47c559bc65313823389f90137293f090038642021243a6fc823284b3f103065ef90426e2b03ce4eb91f200c5c40039904e37a7a49b907152ca787ec9e0ce37647c80c83c2e265e47c81249b13f20e219909a149296746949f90089c6e511803e9bf238cbc80c1ddbc37be40a2cb03ebc710693cc613f203f10af10178af2367a9979020f483f0a303e3284e66fc80ecdd1ff1581f09b901a8a905e47c80439373249e2103e137312f7c8125a31b88ce469979020f3337e401382e80e2f3182e83d36227e40684f09b8af31e41193881f1bc7b86819790715326565a46798f20e2021ce83f9071049321b91a6549680151b31bf20096584f09a327206925418c8e9b86000e104c49a24e7bc71c831b90c3e08a6f5e084e65e46d2790213600787fc404672036086f1c8f906652a34de8aa390149c4e4d0a59730b09e2102398a495188fc07527e40b41fcc791f20e2021c832658969c17c813210a66e52cd48c19c55e411978a84166e8e2b09e0472066e56f1c8ca493fe21c8230f3101c924d48cb2720c6fc569383f4184e4012d2a90867200965931b96bc637e4012d3294a4c0f297cc788426e407611c802726511654ab4dd32f202325e2b4df9017b611c8d329064720493c423640f2f7cc613a3f48474d84d3901192a0f0874dc248454cbc801fa30ac3a01e21f91865e41c411c423288ce410fca90f1ba0f4d889f9043a3a6509613803928ab096f0416a4f2326fc81188f35710c4e5249a7202968c6fc813608c41e89cd4df9017bc4e578bc809a265e20464851a13b3866f09a327203234119c831bc6c2e272134df14f20692690c92790710496994d89f90378a2b4df149513e1510fc811d06c80664d95e003f10085cc7900684715e411ef1bf234ca83cfc4207f202f7c8d1ff314c892538c63d86c869c80079836710e63c802204e48471198de36720217b2c3c8cb272030ccdce83cbc043e205ef98f234cbc804388b5e3a64fc822f1082b372b6038a4c26e4068ca233905372308a6f10cbdf234cbc8224a19c04e8c2cea13f2066e7a471559bc65e4012cdc8213c08692c559b9a9ba0f10fc8d32f20303f24c14691e37e40590f82ca4f10275c81321a1c40586ec8f9032710e727e524bf627e405a2a41584e2726fc80dc571ba7be40498b2982723a0c409390710371541e0d7907238f78dce89846720c6e194b099c1e3d067c838ab37818841e9b398f1044fc838a8004449e201b39000f47409e25a113a0fcf1cc790549e207e405249a723297c40cde224f3124dc8388165388ca6fc,0x40f4931b213913d84a8d909c90f419c0f11c402c92607b3884e541e9b2248d3da340ed1b090f41988ec4640aa180460e13c0f8d834d883c37538208c08338ab48c703d25c6c84e427e61ca8830233747f09e3640f284e84e86636129b9340c0381f1b213b152325a20514a498b050581f1b0494613a3f81e4886184e92e07c6c240f8d909c1f1128a1950e347f03d22c27220fa6f0fd36102840f4331b213960ca0fa2a9b090fe22c0a917124b8550cc2750c441f0fe28a6c207441e9b0685d9be158d909ca630a495b0514dca83d3643f184e02d03e36427295e20d9848c911a42750c30661c2b03e3621950d09cccde361342f709ca0ce2a8b90134a6e381ecde3642723370ac8fc66188c906a924e40466270d28c2742e341e9b30aa2782f4dcc630a495b04b4dca1410786e4d844d90d23dc86262723241aa4919ba7b4691b0883d365371e6122e428a89462a1781f09e361324a1940ca18883e28a2782e9b0a6008b90a2a2466e0f92fc27262722e428a8920ba0f44e9b081dc0c080c45511862f6cdc9a1062bc68a302a0bc80225f66e1d207c6c84e62be5ed9b9862685c4e5ed9b986268550c9ed9ba5f468527fc40a4f3101d09b901d07f10293c8d32f2086876705259bc26e4103cc92613c0f269c823671047e841e10e9bf234cbc80259e07b3d84fc808c934e20707fc4390007e6303f918494036a7b03f8ab3784dc80fc4132c34e40524a83f98f20e47c57880623b3806703c27465e40cdce4fe9bf2023389ca4ff8af2066f03e131b88427811cc78af2033230ae9969b84b2e23e2119798807e401241fa107d3de210d390419340884ed2790131bc7be41c561a7230ca03d083c03f23e41c5420d37394927fc80a8b3781f098f987887202685271394b393fe404669bf232c0f067c8e32f20e2a1059ba213b38811c819b96b242707fc4024807e63c810c231c523c6fc80b298270070963c6e9ec1386c01fc811d1c9ff2066e51607c2635372324ff13f202d3de209b39043a0f264d9c801a549014564699788720e2bcc4121e9ea0fe21c8e1d7200f27e46113903378cb03c259f30909c4fc81a4959320fe21c8e1a720292601e109bc04ba6fc8e32f2045236700ce32f2066e68710179072386e21cd987906272a25fa8a988cb37e47c80310073720e46618313370][i]?.getD 0
def m511H10 (i : Nat) : Nat := #[0xe0d2f0eb000125cae664be4a31c000064769d527a6c9e98af8000000042c800000000001476400043fe036000026675c1201a7684844af894f43c000185a0c0dd1e5e21c0000000e7ebb0ad1099b940000eaa291c00007299f0cb9e7606a795acd8dc2b800027d94e14000036971efe09c0000000828d0d7b5c6a29c21b603b92312072331b2326025a4939770000105438a0899089a00007922563800025a4c0bd96ec6fdf096000024cda7f000031acd626a80c6105097c32d71eb4470000f7240000df831ce96f9d2529bda8b7a7ba47a041c116925160002da26afec3f6e0f00000374956e01442366c6b9715014b1772a1a225aaeb4c5691b8978200035e960f535940e695ee3917e6fe000000000bc650370b88ff62a7b017cce889a2456f47ca8fea28097400000000d70311b000000028a28afa067c00004299b3374ab287784b5b21838d733400072fce18daf0d84e1470b3072410c1ff45b95136fdb8ee73907919ca4c0001cc4000000000004247b073e2ec85d6afb8009ee24838984338a211c94c36af904ff6eb18a6f106e8b5ca8de50e9ba4504b0925e6c86114300001c7a549116ca9063d0b000000000001ced61d3000002784480000d91ed1e253b325821b283a1010a115000065e80000000a93ead740000000517d01985d0fb2d37790830561ccaf00018c4bc2d1bd635b76f126413b37a2a86bac0901c040300000401000080200f00817004010942000c010540000c3a00000008240100000c02070090540101043000190380003c070040004800068060600005c010001c11001208060000317802000040280000c1d0000e028000000901c0c0d0010000f0580202c580281601002050220080b00c0c01c080040e0540000c120301a034010142b0080200400014c000c080480f0240a04c03000140043d00401094150bc1005c0021819044000400404406008000140008c0300017004062d80a03807034000040301018000100a800000140980b1104c0100200c000040100802024250100000003048000380d00423138060a800000000100500c1e04c170c802004110a0010140b08c00048280ac03008070081000005010010400b000040400101004024050ec0008c59008050200002c0102004058170680501c040bc6406c0000007144160080c0002408004018030443528437020000081e020050200002c0002018014040000a008040401c054020180100000010010040002000004010482880c0100c0305804004001500905c0102886008010300d0700100417028040043803019014041f00c0440f00000038160000000c20000000e01402c00004100180200c0003c0000c0400c0109407018180000101007004030040206c0303c0201c030280b00c000000600c0003000014000500600400024090140801401,0xf25cf05e39febc6480512688d4f1c3e6458c52993ba914261ac06c83c4cbcc8f691575dfa092f912b05dd5481a172d520635c8b3e6c4bbaab8d4660cfc300243f183c42dd7bf4543cd98a3cd445ac6119aa0640421052d8b67377a10665c793a59d7f1ff05cc0aeba56c5f082bd9c0b8d0b804cd9b199683b30e0066c12260e113bf276d48628075103909dcfcc34b6408211acc7ac36b4aec3750124b0a0239e2e092980003540a48606614c100010bf791c8000a3532c8e9c184c7078bc82613ed84fb8b26d83c434803e387aa340000000a0cf5308cbe9a5a02068d65da0ba110001496c80020e60001629ca26b49700010c95927eb24a8be0002941800047dbf16000020ede02dc50f0c8db6198ecc80b262b105877427d0e423bf4b326239c00002d2000000004f9800094646b3b5210000d0218c6763f0000e6fa0784c9cea2a0001a275c5880005233c6b50012af7000000031ce0bda43d2eb4e0098000446392df1320280315691015d2920a26aaa407e00eb9dd1d2aba20e78990e49a8a97dd51bbd38a46c89885da4cf063f03d6086c41791b463265222a1034d65d81372c7c401dab5ac79dc3c440aa7341eaabe20001a90f9b4000063a200000000000525f4f6c0004c22d2c2000000000000000000199df188670800011f98805f4c12a9142a5ba2f986f0879bc8a94e71fd19ea2a39ff826c0001116eadf690d304ddd054aa00018760d06ec0c661c00038db44a073df607e5caabbbd36490a20fae8fcb83e0d1e604f2a60001cabe851d35607d2f0580b2da3a28602a6d0c92012e159667e0b2282ba590f07b852000008d4aad01f9384db83bcb57c50800191c600004ef008900008d9020380005607aac59235a2e0001d0544a080000000853c000526115decb9018ebc4620d3abdb2054b389544a7ac09d00000946a31fcbac0fba9716899cd5688427324ab5c0e3a351064801b8105b6b396169028ad000084db50e586b38299114706b63183d8b07d32fe9ac0b2b0189aba915fa80fd4e400001a8a0c8017245ec8e26adca853a51252e3386c893e97a6152a91c8dbcc00539f2ed07f1f10b20c800043fb87b9a656b4e365fb22f11a49560001a6c68d7d0e231524b8a538c07af5700000c402ba9559e0dcc8267453e5b1f1fd955b9ae627f4e5e4f68b5a80ac07965865af2521261f3c78ac6804d32ed8c903b17384de9051cb4a202566d1864f32245b019c93942ff86be7a9a85210079ab0000c75b2370033e07400000001a5f370ef04400059eac7672616938680a6658532f493931f286bc2d703780500001f26c95508d214760002e5b1135002eeb69072233910eb229543cbae1057ac46b94af21ca5ebed41583388807bc479e197739e60ca2a3898892cbb9072fffc5b687e604400030b043b7000084cb04cc0cef27bd1c,0x800000000000110225c403260001cdbc000012943a1a0940000000a0b150dc000381ea2b68ae693ab237445f70fd45fd1f2c53b298b9f5c07691192f014041a59a0b332700852a7cb924ee2c8956885719aaed4000585505fe0000000220844a8241cc0e90c0c1d589e016a019966d95121903443dd06969b258a30dc6277047ada2cc5cd686e792c6c1b361090eb1ca4b48742662c78f1f1abb4b290eec1caf03d9c10587268ac43b1b417e896198387b17dec06ad5621c028d361ffe5e8ba8d2d005bc1e850d1a9762b5e9824465e0c0cc05a0e20ecd85f410164cf236b166677443134235432e09acdf517e6959a4c595d03fc80db205149c4ac4592bd0efe3b9b2723486eba86a2cb2742a0d21811f8b0b7f7b0e34fba0f6606f30b0ce29284126ee87f23ac0fdc1f4eecb59049025636f1c78b6ca6fe1879139df3800000018a5852880008874892d9e494876911caf3252c35c92efc9415351b0b40834548a0daae67230a85dda7f162041ecd9fdb73b535145ac40e40d0778117c32a92544a27685c8f7ca48b5755936e8e14c0b40524820b91f089bd23826260c8ef07d71f0ee7e025032a528431989aa5abba4f30a21e05f93311fc7183d4bbcc9e2014316529684e0000c5fd0fd59897524e1700003153f339826ad87d40413176435113b1bcf4486de3a4069ca8611e35c95f0b722756c247a1a233d118345c14e6399780c740354e143ea3442ed7da48719d82508b448d442015612cf21d763113b56580b44935443815d0b030613a0ec308459d41b01cbe08eec5b23c9c25e3ecc51fa4e9cbeb02b4db4d6efadea2102722d24884540e6d2b9491e85b4055adc41d23110f58a2669a2bca2353688daacb5a3f1c2dca17b895e19e994c8395503e49807a22b081e39a652515c29b135a9820000ae0943742b566f4aa67e6369b901abe652cb35c4fd4364f2fa0a406825c6f3010d07b4af093aee58976c45850a443bc658000f7378b3063ee38e507a2cd20897a7ed315e47f1144c8567f5c8ce974d380c012b0399c9fbee27944789cda831ae4c6efe6dadd9797136e04687850ef000172ad160b32982c671bf5812bc600004b1b23a74b45460ec57148000063c0000125aa1870000ecf0225dbe5000000035a60000e088000208b62f1f6e1911ee5d0000679fc23f64d000034f7254596800007952224ecfc493c52f8312b87c88de526000030c08000451ee8a68f630309154a6dc0ea289ff5ca0003446f267f1c0ea694f85362937ea71de19d22b463d6663645037e634f674895b00009898410a182daf0759b6f3162edbaf767f0a1c8aacb4d39674fa26003ca723e35279e029bc220d92a7e4a72bd7c0bbc5670ddd2868650d111417d37501b4abd2dc67819806b84f94a031571347d2c59df419555608e98892fc03922252a35cc08d,0x774fd17acae7c31568d4bcc0166b52f5b2c9200000000000000000002c0679722f][i]?.getD 0
def m511D10 (i : Nat) : Nat := #[0x569291c33beb2ab4948e1daf6196552470afd856c4a92b077b581485491c337eab2d43cb093fb4ac0a5d982afdab635252384fdd3b029765867ee9d814b92c3ddb5892156470cf7aca25312b84f7d5b0297660abfac5ac48c8e15ef56c8612570cefa36ad012bb4fdd3b0297560abdead90ca48e13f74ec0a5d562af78d6c0892b857f58b1a9191c27f695814bb2cb5ef12d1960970eedacaad2523877ad82548495c2bde35b02a48e13ef52c0a5d9829efab6052ecb2d7bc4b4a5615c3bdab0a4224ae1deb6095252470afe956c1232384fed2b0298758bbdab0a42a48e1dcf5955212570af7916b0892b8773d65549491c2bde45ac2a48e13ef52c0a5d9659fba76052ecc157bc4b565825c2bde25ab2b12e13f74ec0a5d965af7b16b0892b867dd654e8095cabdec5ac424ae15ef62d6152470af7b16b12923857bc4b4a5655c3bd6b124224ae1deb5892152470cdbb0c9d0d28855ed7b229291c29f615ad0c48e10ff62c7a42486add856c32d23857741b5a9591c2bbc85914ac8e11df56c8a4a4708fd856cd30cba47ec2b669865023ee9d814bcacb57b5ec6a4a470ccfb0cad0d28846fd6b1e90921a3bead8d48c8e14fb0ad6a624708f7896cd30ab847bd4b229291c23de25b34b0ae15db56c8a4a470af9856c327238477d5b0297921a3f695814bcacb1fd46c9a619208fba76052f2a955bd7b218495c23de25af4c4ac11fb4ac8a564708fd856cd308b0c7ec9b5e9524823f655b0c948e11bf5ac8a4a470af5a96452523853ed8b1a9291c23dea58d48c8e11f74ec8a56470aed856c32b238576d2b229591c23f615b34c2ac91fb66c2a61870afe2163523238557d7b229591c23de25b3490ae19f90a51a02586add856c52d23847dd3b229291c23f615ab4c4ac15dd56c6a46470aeba76452b23847f80b669745863f615b34c3ac39bb6192a1a510addad6452523847ec2b5e9895823f615b34bb30b1ef12d9a609708fda56352323855f57b1a9191c237e35b3490ae15f90ad86464708fe956b2a323857cd3b229291c23ee9d8d48c8e11fd46c8a4a47087fb16352323857b54b1a9191c23fa8d914ac8e11fe02d9a595748f7a96052f24347dd3b0297958a3f64daf4b12415dd46c8a56470aee8b6c52323847f51b0297921a3be55b02ac8e11fb4ac0a5e4868df8d6cd242a057e51b229291c23f615b14b48e11ef52c8a564708dfad6452b23847bc4b5e959482bf2958d48c8e15cf52c8a56470acfad6452b23857ac2b618495c2bf4858d4948e15f54ec6a46470a7eb16352323857e90b229291c2bd615b0ca48e11fb0ad1a62560afca36352523847dd3b269644823ee9d814bc90d1ef12d9a595708ff016cd30cba57cd3b1a9291c23fc05a94bcac51ef12d9a60570af5a96352523847bc4b668865c23de25af4b4a415db56c6a4a470,0xe11ff5ec9a595848ffb363d2c8a947fc8b4a9191c23fe4daf4a92c1ddd58521564708ff956bb3129073bd68609491c2bf6858f214b0d5fb1ad814a4708ffa964d304b047fd9b1a9851c23fec5934b0ae13fb4ac0a5d921cfd856c52d23847fcab5d18958a3feadb14b48e11ff42c7a625658ffaf64d30caa57bd6b548495c23fe4da34c02c13f74ec0a5d985cf7ac225312b857dd8b585391c27dea5814bb3031ff56c9a619708ff9568cb04b867ed704a8694433eec2a7404ae51ff56c8a5a5409fd856c52c2b847fcab6117958b37e93314b48e15f762d624e4708ff956c0af2b047fd8b269645427dea5914b2a813df56c0a5d9218ffad64d30ea857ed1b229291c3bf2b0a24948e15ef5ad52524708ff916cd2c2b8677d8b568095da3febd814c4ac33ef12d7a4a56097fb16052ecc147fcab591594823febd8d4c4aa11ff22d5a1e5648ff916cd242a047fd7b2696460a3febd934c32413fb4ac7a59121eedacaa92523847fcab59589502bde8d90c24ae11ff4ac9a5d9809fea36052ecc147fc9b629615c23fe85934b23055fb22d614a4709fda56052ecb0c7fc9b5e9646063feb5914ac8e11ff5ec9a595809fd856c52c2a047fd0b26964606bde8d90ca48e15fb22d1a4a4708ffb16ad0d2b857bd6b484495c23fecd914b0a819bf5598a5a4708ffb36452e8b14f7d5b029765867ee9d814bb3031ff52c7a625628ffa36452f2b057bd8b484495c27dea5814bb2431ff66c8a584708ffb16352323847fd6b269845cb3f689114948e13f74ec0a5c981afead6452323877e582549191c2bdeb5a42a48e11ff62d6a1e5208ffa564d2e8c0e7bd82129795823fea5ad444aa15ef12d29615708ffa964d302b047fcab465825025fec5814bb2cb5ef62d21524708ff956b0b123847fd6b4a879602bbec5ac2ac8e11ff2ad7662550ed7b0cb1092b847fd9b229655c23fec58d4aca813ef52c6a60540aefb16b12b23847fd2b1e989582bdec5aca24ae15df5ac8a564708ffa364d2e8c147fd6b269815c23fe55a32c32811ff5ed4a1a5818ffad63d2d2a857ed8b569291c23fe55b048c8e1daf61962524708ff956acb0cba47fc9b629215c23fe55ae4c4ac11ff66c8a59540ef9ac490a723857f4ab619191c277eb58f4c22c55ef62d6552470af7916b2892b847fd6b269875523fe55a42c4ae19fb4492a1e5608ffa964d30cb947fcab465865d2bfa45ac28c8e11ff5ac9a61d208ff9568cb0cb847fd0b269766167dea5814bb2c39fb6095a4a4708ffaf6b5112a857bd8b548495c33f6ba25434a219fb5d02a62561af7916b2a923857ed1b1a9291c2bf6c5ac2948e13f74ec0a5d921afe916952323857ed8b589291c33deab094bcac15fb0ad895e560cf7ac425312b857bd8b549491c3b5ec32ca24ae15ef12d2960570ef6b0290892b867ed8a,0xc9d012b957ed8b595291c2b7ec5a4cb48e18ff56d8a025768ffb164d2ec9047fd4b269865427fc05af4b23051ff66c6a61574af7896acb0cb847fd8b269655c23fe55a42c4a819bf6096a1e560eeeb0290ab23867ec6a569291c2bfa959148c8e11ff1ed0a225218ffb36452e8b0d7dc6b605391c2bf6c5ad4948e11ff2ad814a4708ffaf64d30ab247fcab61d694827f695814bb30b5fb22d654a470cfd8544d30cb847fc9b529825823fe55a32b23015ef1ad85125708ffab64d308b04efd6b1e9595823fecd914b2ae91ff4ac9a61974eedb0aad2523847fd0b1e98958a3fe55ac8c4aa15ef22d21125708ffa963d312b0c7fd5b1a9895c33faba23444a415fb0ad865e540afdb16a92523857ec9b591524823fecd814bb30b1ff26d7a559608ffad64d308a877cd82549391c23fe8db143cac15fb52c790a5868ffad6ad2523847fcab5d1895863fe55acac4ae91ff02d7a225218ffab64d30eb047fd4b269875963fead8d4c4ae93df56c0a5d985c7fa50c52d23857bc6b615491c33fab223444aa13bf5ac7a60960afd916ad252384fec2b629655d2bde45a42a48e11ff52c7a62565efaac290a723867bd21129795823fe4db14b2ae9dbb619654a47097fb16052ecb0cefd6b0298758a3fecd914908e11ff5ac9a5d584efcb02892523847fcab4a5865c23fecd8d4c08e11ff5ad8a1e5648ffa564d30eb247fc9b62974586bbe55b04ac8e11ff22d9a585409fba76052eca947fcab565875823feb5814bcaa53fb0ad1a62560ee7b0aa9092b847fc9b5e8696033fcab014bcac91ff56c8a5a4708ff936bd2c8c147fd6b229191c3baeb2aa49c8e19bf5596a1e5608ff9368d2e8c176f586589191c23fe85934c3acb1ff42c9a619758ff956acb08b04fec2b629611c2bde25a52c32e11ff5ec0a62521afdb16352523857dc8b585391c23fea5934bb3035fd62d6546470cfdae815312b0577dab589591c27de25af4acac11ff2ad2162470ee7b0aa92923847fd8b26976542fd615b0c24ae11ff46c8a4a4708ffa564d308b04fed2b029766063fe55aeac4ac11ff26d7a609608ff936a530cbb47fd8b269644823fec5ab434ae99df5d15a1a5108ffaf605312b2c7fc8b568795823feb58f4c4aa11ff1ed4a225658ffa164d2ecc0e7ec295e80961a7dea5814bb30b1ff2ad495d9658ffa964d2ecc2e77c8b568095da3fe3dab4c4ac15fb0ad8656540cf7a2c252f2b047fd2b468895c23fe3da9434b0b1ff2ad8646470edda24932d23857ec9b5d9524823fe55a52c0ae15fb2ad814a4709dfad60530eb2cf7d5b029766073de90894c4ae11ff42c9a61954afeb16a92323847fc6b669855023feadad43cb099fb46d2a02576afdab6432523873bd68608495c33faba23444aa11ff26d8a5d121afdad6ad2523847fcab5257660bb7ac32ca8c8,0x91c337ebb2d444aa91ff2ad7959182cefb0cad012bb66fd165a879582bf6c5a34948e11ff4ac9a61d609fea36052ecc2dfac2b61974502bf615b0cac8e1cef5a18152470edea428b2d23847fd8b26975582fdc25af4b02411ff46c9a619708ffb36452e4b047fd2b229795927dea58d4c2a819bf4996a22570a7f956b0b123847fd5b22979593bbac2aa48c8e19bf4996a1e5808ffb164d242b847fd1b1a9895d2bee45aca9c8e19fb1e82a62560af7896bcab2b047fc9b5e9855923fe95934c0ae19f752d3a1a5108ffb36452f2b067dd864e8095d79f6b4314948e1d9f495565a470efcac28d2523857dd8b549391c2bf6b5aa4948e11ff42c8a5e5628ffab64d2ecc267f57046889482b7e45a2cb48e15df1ad8a564708ff916cd2e890e7bd8512979582bde25a32c32e1f6e595475c1409fda56052eca947fd2b269865c23feb5934aa301db7619654e470aefad690ab23847fd8b1e9694827f615b14b2ae11ff1ed1a625608ffaf6b5112aa47fd7b2296948337ea32d444ae51ff4ac9a591808ffad6ad0f2b247fd8b5a9291c3beac0a429c8e11ff2ad815a54097fb16052ecc0c7fcab615795833f6c5a5404aed1ff52c7a62521cf7b0ca5012bb577d8b485591c33fab023444aa11ff46c8a5a4708ffb36452eab047fd7b269815833bec2ab4948e11ff5ac9a611209dfad6452a8b04f7d5b0297654b3f615134c32e95ef12d794a5608ffb56ba112b0f3f568609191c337eab2d43cb01deb0ad8612570afda3643252384efd6b229755923feb58f4aca411ff2ad6162540e7dac490b123876ec2b629691c33fab223444a415bf62d5a5a4708ff916ad012bb66fd865a879543b3ec32c4ac8e11ff2ad54625608ffb3645242b867ed590a9865c23fead914bcac11ff42c7a62521cfdae015312b047fd0b269865cb1feb5b1404aed1ff62d6a025728ff956b0b12b867ed5b4a8095db3f645234948e11ff02d7a1a585ef5856c32923847fd0b1e9895863fe55acac48e15fb5ad124a4708ffa3635312a04efd6b2297458abf615b0c3caa93fb0ad8a59540cefae0ad0d28847fd8b269645cb3f6892d4948e11ff56c9a61974afdb16892523847fd1b269865d23febdad444a411ff42c9a595848ff8f685112b2e77d2b568095db3dec0894bcac11ff56c6a625408ffaf605312b147fd7b269865423fecd914ba2431ff2ad76565208ff8d6cd30ab847fd8b269755923fe3db14b4a411ff22d1a1e5648ffb16b50f2b047fc8b669215c23feb5934ba3055f756c864e4708ffaf64d30ab047fd1b1a9895c23fe85ad444aa11ff5ec9a59181eddb0cb12523847fc0b5e8696063fead8f4c4ac11ff52c8a5e56297fb16052ec90e7dd864e8095da7dea5814bb2a55bf62d165a4708ffb36452ca3847fd8b5a8795533fab823444aa11ff26d8a58970cfbb,0xf52c8a5a5208ffab64d30eb256fd1b229691c23feb5914aca819bf5d06a4a5108ffa364d304b847fd6b269855d23fe35b34c2ae95bf62d525a470e7bad0c12723847fc0b5e8895863fec5934bb2a9cdf59552624708ffb16352b23863fd1b628095db3dec3094bcac13fe02d7a59181cdfb02b50f2b04f7d5b1e96454a9fe45ac2c48e11ff56c6a62470cdfb0cb5012b976f581485691c3776a3054c4ac11ff22d1a1e56097fb16052eca957ec2b618795423feb5934b93013fb0ad8a565608ffa964d2cac077e42b619191c23feb5934bab01dbb4492a5a470afd8d6c2a523863fd2b628095da3fe3da9444ac35fb22d124a4708ffb36c50f2b047fd1b628095da3fe55ab2c32e11ff5ad2a22570afbad6a92723867f576468894823fead934b23011ff2ad825a5408ff956b22f2a947fd8b269655d23fec5ab43cac9df96051a4a4708ffb363d302b063fd18629691c337ec5ad43cac11ff62d6a1e5508ffb363530ab866fd865a8795523feb5914bcac95fb56c8a4a4709bfaf635302b847fcab615691c2bbec58d4ac8e11ff2ad29605408ff956c12f2b04ff51b229744863fec5934b92c11ff52c6a625508ff936a530ab067bd89129795823fecd814bb3051ff2ad845a5208ffb363d304b047fd9b1a9815c23fec5ab43cac19df4955a1e5609fd856bd312b047fd8b5a8095d63fe55b0ab4a81ddb615524a47097fb163d2c8c167bd52129795823fecd8f4b23055fd22d6a464708ffa564d2ecc24efd6b229725823fe55ab2c02c15f746c864e4709ff016bd2c890e7f48b468095da3fecd8f4c2ac19bf4856a1e5608ffa964d30c9047fcab46576602bf655b0a948e1cdf5a182564708ff936bd30ab056fd5b219691c23fea5934bb3051ff66c8a585708ffab64d2ecc056fd5b4a9691c23fe4da54ba3031ff66c0a5d9528ff9168d012bb66fd8a4a9691c27f615b14b28e11ff2ad65625708ff95694b0ca047fd9b1e98458b97e94314b48e15fb5ad1a4a470cdfa8cb5112a857dd6b485391c277eb5914baac19df5ad5a02576a7fb16b0b123847fd8b269745873f6ac854c32e91ff4ac8a464708ffa964d30cbad7dd8b485391c23feb5934c12e15bf1ad815a4708ffb3645242a057f48b485191c23fecd814c3ac59fb6192a02576bf7096bd2c08847fd1b629691c2bbe95914ac8e1f6e609475c1408ff95694b0cba47fd8b0297958a3fecd914aa2c12ff62c0a5d9858ffb3635302a047fd4b5a889483edcb128eb82815df56d62564708ffab6950f2b047fcab525766171fe943143cac11ff4ac8a5e560adfab6452d23873bd68604495c23fe35b14ac8e11ff2ad4961d62eddb04a92d23873ed68609291c3b6ec32c49c8e11ff56d6a1e5808ff956c2af2b247fc9b5e9865833fabb23444aa11ff62d2a1e5609ff016bd28cb0d7dd8b5953,0x92b877bd65609491c397e8c30cb48e1d9f4955a5a470a7f8d6ac3123853fc8b485891c29fe35a34c48e14ff46c6a62470adf8d68cb0ca07db98651d7050337ead30cb48e1f6e219475c140cdfaecb51129053fd5b1a9891c3b7615b0cb48e19f742d3a1a510fdd2a4bb2c0907db95251d70502b7e45a34b48e15bf2ad815a470adfad63ca32b053fd6b549891c2b7e35a32c32e19bf46d6a1e560edea428d2d2384efd6b1e989582b7e35b0ab48e177b0ad8651d70adf91690ad23873dd68605391c337eadad43cac14ff46c6862470a7fb56b0b123865fd855e8695c29fe35ab4c48e13bf5ac7a61560a7fad690b1238767d85549691c33fcc3014bcac99bf6196a1e560cefb4aa92d2387db98551d705033eebda7434a2137f5ec8a59570adfa568d2d2384bfd8b1e964607be615b0c9c8e19bf6196a1e520cdfa8cb511290737d68605591c337ec32d4948e14ff22d6562470cdfb12b50f2b072fd28619691c27f615a94c4ac1cbf4618a5a4709ff016bd2c8a97ee95251960482b7e55b0ab48e19bf5496a1e560dddaec15312b067dd704e869443edcc0a8eb82818ff4618a1e560a7f956b2b123863fd70628694439f6b4302948e15bf22d5a5a470adfab6932d23866fd701a9294433f655b0c948e17be5ac7a581109dfad6452ecb066fd8a569691c2bee35b0a9c8e15f722d214e470eed856c32b23847fd6b468895c23fe55b0cac8e11ff22d6a464708ffa56452d2a056fd1b219691c26febd8d4c2ae11ff2ad815a470adfb168d2d23857ed9b0a9861c3b76c32d4948e11ff26d4a589808ff956a4aeca94efd6b1e9195823fe3dad4aca411ff1ed0a1a5818ff816bd112b2c7fd6b269746063feadad404b0f3ef12d7a62560afd856c3012bad6fd6b1e5595823fe8d914b4a819bf5d96a225508ffa164d30ab247fd4b5a8895d7edc90a8eb82811ff1ed4a1a5818ffb164d2a8b053fd5b1a1891c2b7e95a2cb48e11ff22d9a5d1618ffad64d30ab847fcab61959502ff415b0cb82815bf62d215a470cff30a052f2b247fc9b52952583baec2aa49c8e15ef12d79465608ffad63d3129066fd855a8795823fe85934bb3051ff56d6a1e5608ff956b23129053fc6b461891c2bbe55b0cac8e11ff62c9a5d1218ffa96b5112b963fd68628095da3fea5934c2ac11ff66c6a615408ff8f6850d2c2e7ed6a469291c277eb58f4c0ac11ff26d8a595708ffb56ba11290c7fd6b229795833fa90a3444ae15bf62d565a4708ffa1635312a847fd6b1e9895833eeba27434a219fd6191a025768ff936bd2c4c047fd7b269825823fe8d8d4c48e11ff1ed0a22561cdfb0cb5012bac7fd1b22979593edcb0a8eb82815bf62d2a5a470a7f95690b123856fc8b559691c23fe8db143cac9cfd5852162470aef8d6c2ab23863fd74628694423fe55ae8c4a431f,0x3feba25444a217ef5ad215d1409ff956bab12b07ff16148570502fdec5a42ba2817ef1ad8512570cffae8c50d2885fbc8b484495c33fead934bb3017fb02d7660952bef8f6b230aa967fd74229294437f6ba2d4a9241dbf615265a470efdb04a92d2387f796554970503f5ec32c4ba281f7b5892151d70cffae88d112b057fd9b615705833feba134c0a415ff62d561e560bf7b16b2ae8a05ff88b585705033feba21444a439ff5c11a22520eefb0aa92f2b04ffcab595805c3f9ec2aa424ae1cff5a1825e540bf7916b2ae8a04ffd0b229615c33fec5934baac99ff56c9a61d60affb16a90f2b05fbd8b54974503bbec2aa4b4a819ff5d16a22550edfb0cab0f2b07ebd86595745033febda1434b03fed605215d140aff936c0af2b057fd6b549795027fe55b02bcac15ff26d865c110fddae8c32c490e7fd7426921603ddeb430424ae19ff5d11a1a580aff936bab12b07eed7461962483fd6c12a4b22817fe62d615c140bff316b12e0a067fd7056889582bfe8d90cbca819ff5c08a5a510cffad64d30ea85fbd6b548495c27fe858d4c0ae19ff62c9a5d9509ffa36452f2b057fd6b48579502fdead90cba2815ff66d855d160df7b04252f2b057fd8b485795033feba23444a415ff66d851e560aff936b2ae8c067fd7442889586fde35b02ba281dbf619625e540bf7a3643092b857fd8b595795033febda1444acbdf7615624e470fedacaa92e09077ed82548795833febc914acac1feb609525d140aff936c12e08857fc9b61570582bfe45acabca817ef5ad2112570ff6ac290ae8a076fd82459691c2bfec5aac3cac99ff56c9a5d984bf7b1690892b857fd8b549795033fec5934baac19ff62d6a1e554aff936c32e88867fd6b428895d7ff4b1242b8281fcf595525d140fd7b0cb1092b876fd8659579502fde45ac2ba281dfd605215e540bf7b16b2892b857fc7b5918954b3feba2b444ac15ff46c895e560cffae8452d2885fbc8b594495c3b7ec32ac3cac99ff5d10a1a581affb16a92f2b05fbd8b548495c3f5ec32ca24ae19ff5ac9a5d584ff6b0290892b857fd8b54969502bfead90cbca81fdb5d16554920cffae84d3048857fc9b615745833feadad43cb097ef62d615d140aff8d6c0af2a05fbd8b58974503bf6c12a4bca817ef56c8612570efeac290af2a05fec7b5918254bbeec12c29c8e1ddf595525e540bf78d6c0892b857fc8b58579503bf6c12a4bcac1feb6095212570edfb04ab2d2387fb561484495c3bf6c12a4b4a81feb589215d140fe7acaa9092b85fbc8b584495c2bfead912bcac19ff5e48a46560affb16b0af2a057fd8b58979502fdec5ac224ae17ef62d6212570aff936c2af2b077dd65609391c3bdec2ac424ae1dfb589215e540ef7b0ab1292387fad62484495c3bdec12c224ae1def6096152470ef7acac1,0x102920138c08fc043101f800e2c067c02f101520095c03e401a500ac003cc014c005900007d7d85549675c3cfeb4302a3ae1f7b0ad8651d70fcfb0aa92ecb05efc9b60576582efe35b0aa3ae177f22d2151d70bbfb16a92ceb87bf96860570503ebec2aa4a3ae1f9f5d96461552ddfaec452b2b079fd68609475c3f3ec2aa4a32c1ffa0ad865c140bbfad6a928eb87ded82549675c377ebb23444ac17bf62d525d960bbfa364328eb867fd5b26987592fbebdac8c2aa577f5ad2151d70bff0d6c2ae0a06efd855a879582ffc45a42b828177f62d2151d70cffaf6850d2c2f6fd7061869443e7ec32c4a3ae177f62d6551d70fef30aa92e0a07bbd6860574502efe45acaa3ae19ff56d6a02587bbfb16a928eb876fd765918954afbe05aecc2aa5ddf615525a470f9fb0cb2a8eb87df581485475c3f76c12a4bb2c1dbf6152a5a4709ffa163530ab867fd5b5a879603dfcb4304b8281ffa54970581209ffb363d302b04ffd8b56879583fd615b0cba2817bf62d52519609ff956b0b00b84ffd8b1e959582ffcb5aa4b82813ff66c7a615609ff936bd30ab076fd7461869442bfe4db02b82c19ff5ac9a5d580bbfab64328eb86efd765688958377ebb1148cac15ff26d865c150fe7b0aa92c8a05dfc6b605475c2ffc8d90cb8281f7b6095251d70edfb048d2d2387eed765918254b9feb4302bca817fe5ad215c140affb163cab2b04ffd0b229655c27fec5934baac17ef1ad855d140bff31690ae0a07df561485475c2fde45a42ba281fdb615525c120affaf6b2312a94ffd0b1a9855d3b7ec12b4b48e1ffa5d15258120cffae0c50d2a87ef98658970503ebeb2aa4a3ae17bf26d855d960bff316b2ae0a06fbd8512979582efe45ac2a3ae19ff6156a1e560eefb0aa90f2b07f3d85549745027fe55b0abcac1eef5a18112570bff116b2ae0a067fd74269616027fecd914baac13ff5ec9a60560fddb04a928cb05ff98b549705033feba134c0ac19ff6255a1e5609ffab635300b867fd705a8894427fead914bcac1dfb0ad865e540cffae095112887ef98659570503ff8c0a42b82815ff26d865d150cffae0c50d28857fc0b5d98954abfe4db0eacac15ff62d525a470f77ad0c12e8a067fd7022929442ff6b5aa4b82419ff5c11a22560aff936c0ae0904ffd7b269855827fead8f4c4ac13ff42c8a48570bbfb16b0a8eb84ffd0b229655d2efec5ac4a3ae1feb0ad8612570fedae8c2aa4905fbd6b54974502ff6bdac8c12a59ff5d18a1a550bff2b6432e0a067fd705a889542bfe35b0abca813ff56c9a61d60aff91690af2a04ffd7b22959582ffc35b02b82817ef46c865d140fddb0cb1242b84ffcab485805c27fe55b0eacac17ef62d52591409ffa3635300b87fe98254970503f76c32c4b82419ff5d15a1a580cffae8b511288777d8554979503,0xd16048a9d4534228cd13cc899944a6223cd114c884d43f421e6d0e848701436621a2d0c7c85fd42e4215bd0a1484bd42322108d07c48389419e20c1d055c8261410a2077d033c815140882033d011c80413ffa1fe6cfe9c7ee93f481f93cfbec7db53eae1f4ccfa147cbd3e3e1f08cf7dc7ba13db61ec4cf5747a793d161e7acf33c79693c941e33cf13478353bf41defceecc77313b721da2cec6475fd3ad81d58cea4474c93a3e1d11ce82473b939b01cc7ce5a4729139281c7ace324714538761c30ce104704138001befcdecc6f1937601ba2cdc946e2136fc1b73cdb1c6d4d368c1b35cd92c6c4935fe1aeecd6dc6b45357c1aadcd4d46a1134f41a69cd28468f5344e1a13cd01c67d933c619d2cce1466bd3338198eccbdc65a132a4193ecc98c646d321618f7cc73c6339317618aacc4a461f930d6185acc23c60d130361807cbfa45f852fa217bacbd6c5e812f201779cbb345d352e7a1726cb8b45c192dec16e8cb67c5af12d5e169bcb48c5a112cf41672cb35c596d2c9c1646cb19c58812c1a1605cafc457a12baa15c4cad8c569d2b221580cab6c55692a941533ca94c544d2a0014e9ca6b45325298414aeca4f4522d28f61467ca2bc5105285c141aca0544fd127b613cac9dbc4e9d2740138cc9be44db126b8134bc99ac4cb92642130dc98344bf125d812d8c962c4abd2526127fc9364496524981238c91144825240411f4c8f244745237611aac8cbc461122e21166c8acc4525226c1125c88c4442121f010e1c86bc4311217410a3c84cc420d20da1056c823440c120461012c80143fe11fc40fcec7e0c3ee91f420f8dc7ba43d911ea20f3ac79543c5d1e0e0ef6c77343b4d1d800eb8c75143a491d160e7ac733c39511c820e2ac70bc381d1be20ddac6e5436f51b6c0da8c6cac35fd1ad80d61c6a8c35051a5c0d1dc688433f519ec0ce2c6694330919580c9bc645c31ed18e20c5ac623c30d1183c0c0dc5fec2fb517c00bccc5dcc2e99171a0b79c5b342d65168c0b35c595c2c7916280b00c579c2bb115b20ad1c56242ae915660a9fc547c29f114d20a55c522c28d5144a0a14c502427e913d409dfc4e7c26fd134c0992c4c2c25d512d00957c4a3c24e9125a091cc487c23fd11d808d8c462c22c91144088ec43dc21a110aa0841c415c2085102e0806c3f541f5d0f8807b0c3cec1e110ed00757c3a241cd10e3c070ac37a41b790d9606bac350c1a390cea0664c328c18f90c56061ac303c17c50bbc05cdc2dbc16910b160571c2adc152d0a700521c287413f909d604d4c25f412ad09360487c238c118508a2043dc21541069080e03f0c1eec0f35076e03a3c1c840e0106ce0359c1a340cc1062e0306c17b40b8d05a002bcc154c0a590506026cc129c090d045a021cc103407cd03c601d2c0dfc06bd03380188c0b94057,0x81264088e03f501dd80e04068e02f5015d80a04048e020d00f580784034e016d009980384014e006d002580043ff7dff9cffbd7fd03fe3dfeb4ff3d7f903fbddfdb4febd7f563f9ddfcccfe497f163f83dfbe4fdd57edc3f63dfae4fd497e963f46df9ccfcc97e5c3f26df914fc6d7e283f06df7ccfbb17dbe3ecedf5dcfaad7d363e8ddf3d4f9cd7ccc3e55df22cf8c97c383e0edeff4f7b97bbc3dd6dee34f6e57b5e3da1decbcf61d7afa3d69deae4f5317a783d28de8c4f42179f03cf0de704f31d795c3ca0de484f1f578e63c6bde324f15178943c3fde17cf095782a3bfeddfa4ef8577a83bc0ddd9cee8d77203b7fddb94ed8976b63b4add9ececb5763a3b09dd79ceba575b83ac5dd5f4eac575423a96dd3ece9b574b43a43dd19ce8a574383a08dcface7ad73b639cadcdece6b5733a398fdcbe4e5a572a0393fdc9ace489722a3904dc7a4e385719c38b7dc53ce281711a387fdc394e19570a43838dc144e06170223800dbf54df456f8837b3dbd1cde416efa3769dbab4dd016e60371fdb8acdc156df636e7db68cdb116d62369adb424d9e96cce3650db1d4d8916c283609dafb4d7996ba635bfdad7cd6716b1e357bdab8cd5796a903531da90cd44569f634e1da6a4d305697434afda4fcd23168f8346bda2c4d0fd68583412da02ccfd567be33d4d9e3cced1674e338dd9beccd9d66ba3349d99cccc9966383308d97accb9565a432bbd9544ca6d650a3277d9324c939647c3230d90d4c81163ee31e0d8e9cc701635a3199d8c7cc5cd62c63158d8a44c4c9624a3111d8824c3ad61aa30c7d858cc279611c3077d8324c12d607c3024d808cc0055fe22fe6d7e9cbef55f542f99d7c1cbdb55ec02f4cd79ccbc995e2c2f02d777cbba15db62ec7d75bcba855d162e71d72f4b9455c7c2e2ad711cb84d5c062df2d6f14b7615b902dc0d6dccb6a55b2c2d82d6bacb5955aaa2d41d69a4b4915a282d03d679cb37559942cb9d6534b24158fa2c6cd62b4b125586c2c25d6094b01557ea2be1d5ea4af29575c2b9ad5c6cade956d42b5cd5a7cad2156642b24d585cabd555b82acbd55dcaab9553c2a8ad5404a9c154b42a49d51e4a89954322a0bd4faca77d538c29a6d4c54a60d52f8296bd4aaca515526a291ed4844a3ed51d628e0d469ca30d516c2899d4464a20950ea286ad42d4a12950562814d40249fd14fc227cdd3da49e914f28278cd3bcc9db14ec4275ad3a0c9cb94e3c270dd37bc9ba94db426c9d35b49aa54d382688d33dc99a14caa2638d314498494bfe25ebd2eac97214b7025aad2cec96354b0c256fd2b2c95794a962543d29cc94994a2c2505d2794939549a424c1d25bc92b54940248cd23e4918d48942433d211c904147f423e6d1eb48f31477823a8d1c7c8dfd46f02361d1abc8d114668231dd183c8bf545ce22d6,0x49209126e372f8868ab1390409a7900851fc83184d274df09c4fcc693e40a6e81e27f84e6549f20d3722620f2dbc7989a4c9fe13984e30f9023c8318709c57c9e6e7020ce6f784e2f46c61349463353c27d3713f3f90630e139bc28bea4f989bda3187c80d274df09ca84fe406928c82b25f20c27c6118417b1863313e9b8bd9046a4f901b1e0c9e423cdfc83124de6e24589264f00d8966f37f20308079849627378ae30e138bf7900be1ade1cc4c271844ff09fc80f211ac38f18938f7e6264fe408f20c27184c6134b2a24f9be1fe3c63d993f901d527c809934de89ca7086f1e400ce2066f784e7f20c61309549f37c273605e9ba327900c3171874df09fc80618bc93e402f6611a6ec4e6f20c61349159c272a13f8aa320be7900bf1b1845fb09fc805f3c54d6f1e40693810613e6f84e7f3733ff200670431414273e309a4e139a9a318ac9b184d2456709fc80be6e037e418c26f06f684e2f48f20349c27309c61f373324884835d9bf9014cf4cfcd17c8019c507cc709d1e6f0830ca01b10f8966481f37c3f327c7bc493313f901040bdea4e9b9b5244d0823c8189c428de6e67f84e6a60ce67a8c62828f37c49327108079f20379031388490409fe9b9909fcdfc81190cf450419ccfd1e412f0411293e6ec4e6f37c49079308f20627319e8339ad99f883613f901e3c351dfd8ef64773e3b7d1da18ec2475ce3aad1d398e8e473fe39c51cb98e544722e38dd1c518e26470ee386d1c258e0a46fae379d1bb18dca46e0e36b51b3d8d9046c0e35cd1abd8d5646a6e35151a618d224689e33fd19ed8ce8466ce334519858cae4655e327519298c8c463be31a518b58c58462ae310518658c304613e307d182d8c0845fce2f9517b98bce45dfe2ec517518ba045c5e2df516e98b6645abe2d2516758b2c458ee2c3d15e98ae04565e2af515518aa04548e2a0d14f58a6c452ee293d14818a38450ee283d14198a0444fae27b513bd89d044dde269d1331898a44bae259d12a589444497e243d120d88f84474e233d118d88b24451e2255110d88784434e216d10a58844441ae209d1031880a4400e1fb50fbd87d643e0e1ecd0f31879043bde1d9d0ebd875643a0e1ccd0e3d87104380e1be50dd586e2436ce1b2d0d7986ae434fe1a2d0d05866e432ce19150c6d86284306e17e50bd585dc42e6e16cd0b3d858442bae15b50ab18544429de14b50a49851c4283e13e509ed84f44272e137509a984c64258e128d09358486423ee11a508c1844c421ee10bd084d84184207e0fed07d983de41eae0f050765839e41cde0e1d06f1837041b0e0d4d069583364193e0c4d060982f04170e0b4d057d82b64153e0a4d0515827c4133e094d048982364113e084d03fd81f040f0e074d037d81bc40d3e0665032d818e40b9e05c502c5814e40a2e04f50269,0xc544fc4cb09cd84fe40233e218c3e62673765b007f20649a2735bc607f8838af98f91e32f902289e0204ebc8050bc40de218c384e60b693e406d23b3133437b2730b13da4c8ce9bf901b48ccdec57c80cfcae13662280333754937bc0b25989bd99a0ede3c43195c57cc7c80c67e66f62be40473767b1193a206b0f98f9078818d6c4185c6f87f88b2104c17c51e3719a48be0b98689fc83c555edcdcc64e883ac3e41e205c27f20c6114b319f313730e13f906041a4b9b9a49f9878f7c83c54decde47e21c938682445c27c61f203497372891724e1d193e9b9709f022cdfc81d24b8c22b3e4184e6925c5b489e371b139040a5d9bf9014cdc138dec7a476626926686f65c27c61b37f207492c84193e24e25eb0f98f9078823124c9fc835859ed8dcce4722f2a3a6e4d23349301f203372d989a499a1bd93187c8052ce1b09cac9721064e075e405337349301f20258a99b9bde139302309ecdfc80d44b62a6f666f8164c27c61b37f203512c8471b80762df906249848b124c9fcc712fc40de21cc2c4fa93269e406627d4993a208f20b37309171b80762de249709f987c82cdfc54c04dc2b044d0cc7524ee6e6c27e61f31f20319f103630980f8ae13d9bf901b184c67c4309fcc7c80d62ac4f30c411275e41a6e734902c33f180a1a499f8c5240fc1538df89cbe6ec106f06f7e40a2b84ea922f49f20c61109349f37c2731b0b04e24f9ba93f901bcdf18413b09cc27c80ce218c22f769384fe406537c61035f1517b427f2017c4788630e8a9bc7901bde13ea48c0244d1527c8388c83cbe40a93e6e2124c944e6122e4987b327e372f9bf9019e833e138a099f9c527c809f80fd02b89cde6f8f08938f7e40a4e87e7537f20349c2757ec6113f3f906309a4884e13f9b9989fc808204674dcbe21a93e408c98166f06f63008f2062713f208d3711731bc1bd9c1f90788033e138bd231a4c24d27cdf09cbac32108f7e4064f8926d6187b006327f20e373791a2582841d7900271b8578de1ec488c9ca6f0811e6fe4069384e6b61e49627134308f2010a3e30f9069b8bd8c36139bc819244245938dcb6c3e41a6e2f6004610c4e730904ec61f37c27f20379be30f901bd8c06139bc68aa109fcdfc81190de019cdec5e91e6e67be4067e0ce28384e7c0bf20349464d372e30e9be138bd9c08c31bc80d265ef187c40c2709cf8c22fc6fe20d84fe406f20109649264d372f9bc84b13b30f9002718d27187c804fc10d4dd09cea6fe2a81f84e2f7e402f87d15f20d3713f2086273324cb651fa1a79017c83184c2413b09fcdcde6f8c3a2a7026f784e3007e27649f20109b372e308ace13f901a497184e07c5709c5f05f8ca4fe4047fc6e21042e6649f20109e3712628a4f9001fa0571bf139bcdcde05e8def09c19fc80fe46269e414cac9241e6f205,0x3c52c89acdfc80bc20c4fe40c1ecd907e6f23f10619e4982229c19bd88c26de15274dfc8fc80de20475e418962ca5142c0b33af207152e1398cf88634f9897196cdfc8fc8092cbe21c164f72c9e40c69e2a76276641308e28e1ff90120ebc82423c8f1978dcc70820629153371871e30d9be139bdf90144fc83f4dc89bc8045cd24fcc3c7be41e2a6226909d7883fe37327f208173db0f90184391843f98883788625a7124c9f587c818d3c40d6464cb874af7e41a6e6349e3760fd78f23f20343614679059b9345689c9904ff4dfc80d893cf1a4fe63e41e20a4c7d78c49f23f31665f20f1060f47082438a455cf4cdcdec984e8c9e4027566e5e61c27c08737349f203407f9191d632f902a5f881e423584c9d17bc80a61227fa6ecd9e4022e6c49165c4b286f20f103081bbc630d9be13f901b8df1170fc7e41c6e8962184c61c27f20186d372f8841a307f91f9078a98c2789f4dd527c80a2cb097e41c6e4c27c61f207373492f906308c3d9be1396527984c1782fc8fc82cdcfa466026a23d37d3df15378664f2033989bd99a0cde192fc40defcc7c805b0f87f88ac223f23908c3f321d61e37f153e24ebc393f98f907881b21dcdd8ff82f587c8fc83c54f84fcc267f66fe40530b908c49f20c51e37c3f3b13e9bf900a8931874df09cd27c80be41074c97e210ca5187737f201f91e0be0ceb0ea4990f1b9fcc7184defc8309c52cc6686936626f6430135114b0f8870ab0cf05f98f91f90239e282492fc838dc5b0d21144fac2c93e63e40c97e208e37978665f20f152f88730b13c8cda4f901989f4df5e19b3c81833c54f44e4c829766fe405e37c5b634327f20c493630d9bf9061399f97186cdf09fc80d44b0d9e41074697e205c27f15c6117e301f20371bf91d32f9021d1079ac540b05a6ec11a7a6f1e47e2be407c27864f20d373492b13b320b09fc4318441bc80a4d8c92275e40c97e206c27e61f20f15305b373630f8ae13f900bf0be1bcc75879e392749fc8185cf213af1a6e4d9e402966f20264b3714ba272f1bca4d93f3c7901931821d52782e1efc8cd93c838dcfe2184fe418c22805f2014bd37c27258a80a0bc804eacdc83c8613a2a27fa6ecd9e40620ff2313aa65f20a4bf103e9be9e9bc33279078a98050d24cfc78c22962b384fe405f1016c83a042f202e30d9be13f9078a9829b02309fc80e1acdcb075c6fe410ca450940f351b37426f2033881438b1275e3cc7c83c41994d66fc47e4029641e5c61937c27f201172c1d484788791e32f903259ecdc89bc8052c83cb21011cacbe47e40530be37c3fc4590828c31bd99a0f8dd83e5e3c8d997c83c54fe2184fcc260b693e406e1062760ff2066c83f3484ebc391d24f1bf903939f09f187c80e1acdcbe400ce68ae6e67e5c27f20c61103b372891628e1ff1b93c83186,0xc27b15c61351b37f20371bf1eebc393f9078a9b21ccdcd24c071a49647e40ca2e6ec7e518ef2066c1d989bd99a0f0ff1178dc7e4121107464e0845f31f2315110af202c1d69bf9043290cde455de0cffc80a275e4044d297e205243909d37627f203493713cb0f8819a7903249992c4ebc83c42194ba46613c6fe40ca221e617e37f106189fd1393269bf9008b9848b8e3124c9f8dcaa118cbe46275e4166e6908d61e1587b327f20e373d882270038dc24c16c54cdf09cbe4041e8686c9e4727f293e208a2765b737007f206493788613e309bde9ef9078a9cc23127c81a1b12c430d8c3a6f84fe402965b1537b337c0b2505b9b92480392df901acdc92f48fc8043cb816675e4027f62a5908565f2383af20e37343db32f91f9071bc1d19197c804eacdc8a92613a6fc4fe402026e61627b1593af20f103484ebc70ac1ff1b993f901c19ccfc61c50709fc80d8d366f84e6a24e37564e78d3df20f157273e138af630982f9016927c835e3cc583fc40d84fe40af78c2a225b61723f2030817bf15106d374630f906139a8d9bd8a98cddc24c16c5702cbe204f7c17e41e47e2ac687349d23b78c08f31f10f203e13b9bf90630ea4a8b9a1944ebc8192fc40be4787e29dac3c6fe40617bf20f23a6513ab37368a98409a532f91f90625f8823c804d30ff127c409b0d84f8932c8c75e41e206949e27e61f20b373053307b3679070841f97c8f8df8f75e3c83c54c3ce5190d9e4166e426cf2083ae3721b642dd91f90443168279e3c8d59612f8dfc80fe46c92869e4121fe206908036d3d327d61f20f15e37479013df1be248b6178dd5939e34f7c83c55c9ce51901e6fd0cbe405b3166c047f201192f885bc1a4e3279016c8d8fd915cdc8603c17cc32f0e93e4766fe408b23c09f20949e3736c3613e9bf900a59302c4fc524509cdfc80d09210fa6e314bd37226f2021c208199f8f8df1ec4cfd87e2e61a27142737f202932f1bf9041d10e18c14421344e4c9e40e93a6e6961e27f20f1573767b3798f91f3094382779018e0cdec5a46669e4162a488466c87b60ff202e91984b28f1bf900879b09fc83184deecdcb892469e41897e202ca637b334b311f8813273c713f9078ab131f4f59efc838dc5b0b62ba6f8c227f84fe40693817bf23a65f20d37358a9808889a8f9017c8c83e997c810ea92fc40e669e4162a3c49c4bf10834f23364f203881b9ee30d9be13f901989d4b59b3cc7c81833c40faf1212c4fe41a6e692626cd37f201512228a438b09f187c40cd1c57c80d892875e406d98965c27f15737c61f2037b31b08477919b279017c421ef89fc83c55898d84fcc26f7e4166e5d78f20c0fc6cc27b376493e9e89101b193f8af1b9b98689dcdfc8042bc54d84e603e2b8d366e5908c3f327d61e37f20f153f88705abdf30e9ef91f9078aa08,0x405187b37f201e04b93f904a4c2c9709fc43187c80cd1c54d213af102f07fc6fe466c9e408c61c27f2013ab3729808a88a4275e309dcde193c80d24e6f1e204f23349309e23f20e37c6c3184f13f902a4e9b97c5589d83e8de9fa0ffc80f893cc3e63a4fe41e20c3271497101791f882bdf30e9ef9078af139f09fc83184cfecdcbe63af0a7fcc3e41e2bc4e7978f10e1560ff31f23665f204132c1d79069b9216cdb3c82218924fc7bcc3e406f66226a27d61737f20f1563f378af88705abdc327901bc8f1275e3cc7c80c3fc40fe210f7e41e47e2ac1e6d61378d27f20e49601e373d24e1d2bdd32f91f9061c69ba042483c89bc81d274dcde21c7bac3c4fe41e2aa68766cc4923af20c4b2c3659bf901259289e926584973c80ba2a41fa6e27e44de406f2028664bf1016c2e34e139a4b9b934dd83fc8f5e38f7c83c54fe63e2bcc267fc17af1e47e408e3760f66c627886f203798c1ff3c79078ae93a931f02e457c804e852cb07f0fce4fe41292573757be0bf23e3df20f153b91e24f98f907882b29b1470ff8dfc809e47045e6201cc93e20c7e7327908e38c49f20e373613f90180f8ae30d9b9856ca3d89c6189e20c69c4fe401185a3760f62766c87bf2034a489d3367904a597c8f8560898ebc40b84f66f8c220de405c27f20319f10c61f313788493f30f1ef9018c9b12758782fc8d8ebc83c40fe210f6cd9e41e2ac186308b61527f31c49f20c4bf1041a4e9bf13ebc7903043021fc4398589fc824e8be202f6a69a7be47e41e2a7c27464351b37f202cb0827788798d13f901259ccfc5fbc80630f66f8163c61f20c27f3137b14b3005428f1b9b679017584de349fc838dfc55804f8d366f84ee924c27f20102f10c61f3137900a5d9be13934df8f75e389fc83c55898e4746114cbe47e41897e207327441d61f20e3728833bc630e13f9059b995244d29b3c8152cba2a4ca269e21e418966465f20b372192604613f903a4d9b97c4309f8f7c82593c555ecfe2ba6e00e0824d37e27608d3df15378f2060442a4aa589d79078813618c14cdc61c7897e21893075e466c9e407f2026543ae37258ae046139a8d9bf901b8df8f75e3c57c81c9cd90fe2be21010af7c17e47e40798460fe49f2021a4dbc602798f907881bc4309fc83184c16524d44e10e0b1a6fe405327e37d61d3df20f156053e24f905b08bdb13e9b9bc821960eb8dc96626926686f64737e0bf15f23961f2063f3f3c624b93f98f907881b21f09fc83184deecdcaa1287fc6fe4082e6d86e2313af20b3740f2805428f1bb93f9017c4382f5878f7c8fc815efc551c6ee4faf1c7be41e2aac87f15f10808e27f2057b3193eb0e9ef90302f8ab1b9ccd3c81c54784f8c3e40e9366e588466587bf20f152e8a9b2225f901b097187c82cdc61f09ca6136f1c46a93e41a6fc4e7,0xe2ca4715334f201c07b24f919bdf98e32f90325f882709dcdf187c83c54decd84e633e4166e4309c61c27f20749d37321d7887905258b296cc4e18cd0dec8669e4120522a4b15014133df05cb0f91f9078ab9b9d420a3bc8103086116c387e269e40c4fe21892888460f87bf23665f20f153f1ecb098cf05f98f91f90788230ff1178dd49fc80b84f66f8d3e2a60a5f10f20626465211a0b2f90625f8817020a3249fc819258fcc47e48ae6e3c27f20c6133fb372f9189d484788632f903259f586420c9fc81178b84e693e41a104b78349309c61c27f20d373e05f9018cd9b90cdfc80138c049e202f7ac3e47e40a69e2a7000723e15f20b610393083f98ebc705a9ff30f91f8af9023454de3c42423c8cdefcc719712fc815211ac2c93e62c966f7e41e210189627664138a8bc8b184d46cdf09fc80be21ac3c7bc4fe41e2a6f67305132386b15c0b2f8843679021d021174df98546782f527c8fc80fe63e2bcc3c4faf1e4067e7c69c27386b37233609a790524d25974dc18001c6233e41a6e4ca411914bd3726cf202ca482a332f1b9090bc43c83cc5590defc8fc54a1d3e47e21044c744334f2004e1b8a99be059bd9061ccdc1387e2184f8d260b6925c27f20c6137bb372c841bc625f88624f98ab2f919bdf902bc435859ef4f7c83c5789cf309e40c1fc92c4e5c61b37c27f201512e30984e13f903a48889b48f8548ff8dfc8043cd21144fac2067c7be41e2ae6e8627208b37f2014b2b9bf8ac13c84790158e121c4a924d8275e40a97e206f2086583ad37259899a1bd8cd44c045a7a6c2c33c17e63e47e41e208309b78d37549f23f20333611ff9059b88c978dd89bc57c81194a6f1892c1fe63e47e41e207e15723f10665243291d7902a5f8817c5789cdefc82cdcb84fe40a33e218c3e62633f337b15c69223259bf900a590c9f8dfc57587c830fcc81e51d8cbe404927e61240f31f20f10371bf906bc724b939b21b98649fc43023cc403bc819258fd384fe418c22fc67e5a3788666c60f87b627f203b9be13e30a9ff9078a9b4de423c8f197c80618de6307faf1e47e40c1fe2a7337186305c0b241d432f90325f8816197c8061b4dc8616c70cf6c6e4549134f20a6c54b2c270038b8dec9cc238f55e3c83c54e669e4162a373767b1613f30f9078819a38a98d14cfc5e218cbc463e1526c97bc3af20d373613a3259bf901a89702c466cdfc80d24b84f8c3e20668e2be406984665f20e152613f8ad9be30f901829a03ca32197c82cdcb2c3e40c743319b1517c1932f9009d59b934dfc8fc80de3525820de21293e46af7e405f1037be0bd61e3df23f20f154484ebc70ac1ff91f1b9b2790229275e183fcc7c4189fc80fe21075896453e405927649f10e61334f203493f88730f98f0af9030c9d42503ecdd09bc80d44d24fe21cc250fe,0xbc80666f62a089e404723b1566508cf1024b343659bf90125938e18658d2423124c9fc838dd06930f78d9e41c6e580ff2383ac65f2054bf103a27003e9b8fc420d19b3c81833c54d84f8c2296669e40587bc65f20f2383ad37302702200a0c419cf718709fc82cdcdc7b24fcc2669e41e206b2336ce37f208512c8ae30d9b8a8e13f9018c2658413bc43cc7c8fc80f24fe2bcc3e40e6ec7e622613af20b3724364bc7904bdf989a5f881f09ecdf1a4dec8c1f309e46ccbe41c2a6f10c2767bd3d964f20f153e13a321c37904a5951ec597c838dc9e21cc2a69a7be41e2bc4e7e27305e3d961f20f15b37399fbbc19bf90135e2427c8f4dcd9212fc80f816e6fe406324f2304e961f31f20012378831a705f91f9004618d274df5e3c8d823c80d2c3e40c743d61f20e23f3137b63f649f1080c4e05b9b9c18339bd94cf7c8189878c366f84fe4070c517bc6133fc27f20f1034939320a5e9bf901292503f194e1bc8292cdc2be40c7ec6e4c49519e0bf31f23d61f20f10478af1bb91ebc3063367901c997c804674dc9ac3647e21e63e41e2a0007d3d327d61634f20f10313291d790625f8814d87c43c8c618d9312fc80fa6e693af1e46c11e406305e0be3d961f23f20f15b37438a99b9bdc3610c21c57c829944d3c8fc4192d1e47e20c69cc3e401186c27464f20386b37299bb84982c8aca497127c818d0721144ee71e40c92e6e6d3d361d27f20f31f10609389fe30899613f9008b9952c8ebc83c42194a89210f8cbe406f7e208967f20e3dc6cc0fc27186b373e34e13b9b9a49149f127c831478df0fccef18104b324fe404966361186f23364d37f20379012891f82739b971275e3cc7c81997c40de4766fe418ca43281e610646717900bd984d8a90c22997c83c8c4674dcd8c2e6f84fe402925e78c49727f31f20f105643e9bf8ab0469e9bc791f901fc4358782d9ef4f7c8fc83c550e6f8c3e4070c67584e6e3724bf2010f2193e9eeb0f9033df1b99de3022cde49fc8092cd62a0282134105e27f2015e28bda1379009d59b97c404ebc8099252cac97e21075e402d85334f207151f98e13f900bce3095c8d99446026a22c65908f20186d372f8ac939bdf30f901889b09fc57c83186cdcc04dc6fe404a22d84f10949e27f2057b2f90630e138a5e9b97c421edc9fc83c55990d84f8d267f66e426c186f2054bf102e30d9be13f902a4974dcde3c81993524be418c227f26f84e5908d6132783af2064bf103827604144c93f9031f9909f8dfc82d870fcb84fe41e2b8c2e6ea7e6f10c27c61f207491067153f88413f98f904843a4984ebc8252fc4083cbc7a64fac3e63e40c33e207d37865f20186271b993e9eeb0f9030c9b4dcd275e1993c80b2f1e21c2accbe63e406827908f207492613f90630abda9b969261b0ce8e1bc81cdcc433e41c6,0x5f9010c231278e3c8149f8dccc710cb64610e4c61b37c27f203862cb082739c513f9039b98138231997c8092cac4ecd907e07c4737f20f158279082b9bb1f8b186cdf09fc804e8ac1ecd8c4fe404b37f2090330933f2e30e13f901c359b95cdf187c80e18ceb09cd293e40c1ec4ecd9c6f002718a334f201a13a1f9b0f1b91590de1127c43c80ded0fce6f66682c69c27749b372634d8a9a8d9be1394630c27c806603c17cc32f166fe47e41e2a817bf20c2713ad37289fe30e9be13f9008b98dff09d526190defc8152cf8c229384fe40e6e533df2062618a5d9be13f901309fc80c07c57186cdcde4609ccc3269e41e20617904e9031932a1d7884a5f9017127c809ef8dc594a6c9a6fe40096466ca4917bf20d372e04f1b9b67904a495c9fc8221a1649413cf1e41c6e4962d86927e61f20f1567b73731845b0b91f9078809a08c88520d261ef49fc838dca0ba00fa6e3f31e0b53f864f20f153790307cbc33293c8099589c61b4dcbc6f2f1e41e2acca5f208277379087497153591e04f1bf904a49b61bc438f709e593c814d3c54f8c2e6f84fe406925301151169191ff1bf9010b887989b3c8061b4dc88c8275e41a6e4e23f20d083492791f90630c2718cd9b9b58642289f8f40cfc83c55cdd1a2a2f64cbe41a6e5337709305b15c0b2e1f82b889b20ebc8192fc40b2c2067087e4144fe2ae6e7c49f10908f23565286c4bf204513b9b94679013c409950ebc8292cb8c366f84fe40e925c61c27f2017c17ef15371beb0f24f90693b0c9a5e3857c83cc7c41994d24fcc3e20669e40c926627d37d7866cf2060cf1539a4e9bebc33279017024db3c825278dcb62067e2f23364361d37f2004b28c73367900f8dcc22c9d5e3927c80de41e626f68d8c93e20c7e7f2071533733f2613f8ad9be30f901829b5e19b189d83fc80d278dcfc166c80b9e47e40c926c2766c60c83f1f30b24e0412cc93f901bc83c8d0ea99652fc4083cf892c1fe63e47af1e41e207909d78c61f20c273497373cbc71b9b67904289642fc818e86e6fe2bac3e41c4ec7e6f15827f209087372e13f9018cf88630f989b187c80d46cdec5709cd8c384fe4070d66e5737e27f20961f1563f319b9a4980f901041718709fc81d264dccc1ecd9e403509e1543fe37f2036c3391e24b36798f907883061fc4389f8f7587c83c555ecf8c209d84fe40e6e5c27864f20d371862ca4b13f90307b3671bc009fcc545f82f5e3987527c8fc81030da6fe404d84109e23f2020f749d3731829c308cd31a6c546015c6ee4fe410a25f1027be27f20f15634318289a19b99c6059718709fc80d274dcb24fe2bcc3e40e6ec7e6d61a27f31007f2064963ff1045b0f1ba93f9078ae1f9bc8e587c5610c049cdc8ffc811892cf6c6e2d84c61b37c27f203512c84ebc630e13f9039b9a49e42d8e,0xc64c26b10e232613840b04fe454784f81e6383d310e138709ccfcd147c476622c27219a151d3db360983d9b0562a160f97f1613845ec3c4762a2c27b37160439e8983d9b05810ef162a32340e3dc2f61a0f857016c8c7002c1f6f03627905118cca488e18deccd2cc49c4666f62a3c27b151691d880a8fe610566e6138d984e481760f9841d9b803d24eb09309ecdc5c46132730f36c1d0bcc23138ec54384e2f62b150d8a8709f012cc46c4e6f02000c17584584e1b150b07b3608deccd2cc4784f66221550e1399bd8a8d154366e60b8d8323f0f0811fe138e0ff0544c1f2382b150c9fca289138303382ac4e3c27b311711d9b8b88c2c4f2f73063c043451313b07dbc0c166f8118d8362733d113d858fce1058098d82c270d9b984e360c062154566f8098d83a179841019a2759b8f03f1b0461e6d82c27c04b101d8a87020d14566e60b8d83060098cda48b09c924cdc66f66696623060d311613d988b09f840584f81e7063c04778b311e046360b09ec54462e2a22a49b37e23182cdf0231b0660a70c200460703f1b309c8fc80e23b10161399bd8a8ec5436621c27099bd8a8acdf0231b0780aec3646397b983102ab880983ede05810ef16623e23b3111879b608c14e18581070c2b31080cdec54460a70c2c043831424c9bb138d83e5fc581e70627370e13d9b8b011cf6c40784e1b310e041c18ac5438f7869647c624317351119bd8a8b021cf6c407808ef02386b31159886cdccd0dece18962a1386b311613d8808cdec545810ef02055731102be880acdf0131b078098d82b37c08c6c1e04636091542e6e6686f670c4319b49158804c66d2456201317351118b9a889cdccd0dece188e6e6686f670c4c0b737f20319238a99be059bd9318709fc81d26cdcb62be418c26a366f84e6c61b37c27f207492e309a4e13f9039b97c82cdd52689c9e2104fe41e2b211e62633437b1413c847903a49385583fc825e1994b8c2e6f84fe406925c27f10c61334715f2034a4b07b3631382a71b81f1e03d8e013821c904ee6ee71211e405b37c61c27f200522e30a2759be13f90150fc120584f66f8c2275e405f20b3754920f211f82439b8ccdfc80138c04800fe200c43c61c27f20549b372f906139a48c14b186c56cdf09fc80d8166338d366e473704e05d007f202e309a4e13f9039b9709fc83c57186cdcc04d010e6f44fe412925c61c27f20749b372f901b20c369b9b094c04d44466ee1260b62b8165d61a2763ff10f31007f20649451392491ff90798cb0803f8822c54cdf02cdec904fe2ae6f211e405f31f1560f054f2366531bc7903130cc041485c6f87e2c27f10c693347152cb0f9031d0f855c8d9947817e406322f7620551917904e1e30e13f900c359b97c8c13801fc42587cc7c80e669e40e2a3f10f2013426571564b318cb9be0,0x12921d23b1016918421ec5448861d23c081691d8a8a5243c476202d23b15170ad918b4c41745a4762a2d23087b151f118748ecdc4293662223f04310348c20e150e918788f19309860670862e23b151691d9b88554307f292c4e3d23b151691d9b8b88ec54584f6202d23c08b311b9b8748c3646185e887c191982d8a8b48ecc45a4666f62a3b31098c9c30989ccf44e6e1e23b151224c07c138c060b0862c270e918709f03cd146a680ea2e23b37100107f292c4e3c2723f10348c208610480e13f188ac5709c5a478116203e230e91d9888c5c1485c636462b100f11874dd5ec1746c4e6f0217b0e13e020b88ecdc5a4762a2c27b151613d0a8b0172184c1ecd82b3733437b386250aa362078d89e8d19b07c4762a2d23337b151a218788ecdc40670aa2d230c2181988c16c54584f62a203338315880719309acc788c8c1f28a2041f8748ecc45c46160f98410275988b09d5ef1b06c4ec1ecd8337b3831184e360989d83e5fc7c476622e23337b151e07e360989d83d9b0780b081868e170bc5d3709829c30b09ec544c4ec1f6f10024c270b13d1fcc20f09c85c4c1e486257b07513139bc0b48ecdc4c1ecd82d230984e360b05589c584f66e2e31c86151a3360b88c2c4ec1ecd83c0473d139887011de2c546c1e0ba2][i]?.getD 0
def m511H9 (_ : Nat) : Nat := 0x2381afa4383249181be36651dbc001089db1cb557400000000361b525223991cec9d40a4001a0748edecc3e885100e4bc20972c050cf98a94242a1194ace5863d645d0d231c0259882f5ba52ad86db413be1c95d8358dfd131cd0c6853d23654870d978fc94fc4400000000205e57b1c6cc8c7f04197c002864001ca9014001d08602c0ac61c9c1e406f81d4240010135aa4d7d9dd158d14c15f8e28003cf8000002c5400222fc941041540011c00eb8699f40038758f704d14794ad82cbae4f8f358f11f8b0002d5b4e4c7bce04bc000d3f9dc001213e0813653160e56c49a9e80499a7c3ad2e05ad6a5a05c9dfe6158da00fca35661f39e11d3c81d53a251d8160b04141f0010425443c00c10091040c202300a14e0c6923054045100188840d4d7374cc4c0505
def m511D9 (i : Nat) : Nat := #[0xbdb86c605475c140fda982549475c140fdb161485475c14097f80c5ed6462552a6fd8c5496a1e560e73d855484a5e560fd3965549475c140bdb88c585475c140afadac0ad8612570e67d746195a1a51097ec2c66d855c160bdb98c585475c140bdb98c589475c140e6ed706192a1a5109fe82c62d655c1409fe80c5ed6460952e6ed825496a1e5609dec2c62d6151d709f3d4c02d766155297ec2c66d855d160fda962485475c140a7bd8c5484a5e560e6ed746192a1a5109f5d3c02d76615529fac2c62d655d140e7ad825484a5e5609fe82c62d615c14097bd4c02d766255297dd3c02d766255297ec2c62d655e5409fac2c62d65125709fad4c02d76609529fac2c62d615d1409fcd3c02d766095297ec2c62d615e5409fac2c62d611257083fd8c66c6a60470bda82c619475c14083fd8c02d7a1a585a76d5c2291a4a47083fd8c1ed0a2256586fd6c22d5a1e564a6ed6c2291a4a470a7cd3c2291a4a47096ec2c62d5a5a47086fd6c1ed0a1a58186fd6c02d7a22565a7741c5ad5a0257687bc4c66c6a6057097e90c22d5a4a47093ec2c6ad616247083fd8c1ed4a1a58196ed6c22d5a4a47086fd6c66c8a59470a7790c22d5a02576976d5c22d5a4a470c76d1256c8a4a47095ed7c22d5a4a47083fd8c1ed0a1a58187bd4c02d7a1a581877d5c02d7a1a58587f51c22d5a0257696ec2c62d565a47087bc4c66c8a4857087dd3c02d7a22565a3ed8c1a95a4a470a7adac0ad861257087dd3c02d7a1a581a6ec2c6196a1e55487ed9c0ad8a5847083fd8c02d7a1a58193ec2c62d6162470877cac62d215647087f4ac62d654647096ec2c62d1a5a47086fd6c1ed0a2256587ec2c56d8a5a470c6ed125ac8a4a470a7751c22d5a0257687dd3c22d5a0257697cd3c22d5a4a47095bd7c22d651257097cc2c62d654e4708fadac0ad8612570a7cc2c6193a02575877cac62d615647087f51c66c8a48470c7cd124ec8a4a47096ec2c62d165a470877c9c56c0a5d98187ed2c22d5a0257687dd3c02d7a1a585a6ec2c6196a1e55097e51c22d5a4a47087ed2c02d7a1a585a7ac2c6244a5e56086fd6c1ed4a2256587ed9c0ad8a59470a774ac6052156470a75d3c22d5a0257697e51c22d1a4a470a7ac4c5642a6197087ecac62d654a47087ec2c46d8a5a47086fd6c22d5a1e56087edac0ad860257587bc4c66c8a5957087ed2c02d7a22565a7e90c1a95a4a47097ad4c22d5a4a47097741c6ad6256470a76d2c22d5a02576a7e51c1a95a4a47087bd4c02d7a2256587ed2c02d7a1a58197cc2c62d614e47095bd7c1ad811257087bc4c66c6a61570a67d6c22d5a0257687ecac62d614a470976c2c62d615647087bd4c02d7a1a58587bc4c66c8a5857097ac2c62d651257097ac2c62d655247097ac2c62d611257097ac2c62d615247087adac0ad8612570,0x2e201040fdc4e2c8406e2a1b8a8607e1b8a86e6e1078543715082e6e1b8a86e6e1c845cc440b9884e6f715140fdc4e2e91841908b880ae621b8a8400b8a84e6f715102612c6c140fc3c270dcdc2081fc525c4e3f1187c621b9887a461f0a84171008207f1497138fc2a1e1386e621f118400003c621e1387c6210001a233a4fc8060d88061c400061fe6220c3fcc44f15080037b78809e4611bdf1844f1508030e100dec286759bf02c61877880b8161000037bd9889e2a1791840187d988bc1652df30fc82669f10301e2a1880840f15085f8230519a09e2a103c543f310c3886f638416cc46f62d9b861f8c23e9185e2a1d9e94b76f1f31e047c43e40778a8460217e10030ff3113c542c3f3420b66237b101e2a11bdecc440d91bc54408828430833ff900fe2037b10362af2310c142f1508029c1791840187d988b817c6113c403f101bd8b6621871000f150f48c2f23080602178a840f230f48de2a278a87a46f1513c543b781a494b7811309f9bfc8184e8b90b8bb6cb5ab48b36b24b12b00afbae9ad7ad2ac0aaea9ca7da78a66a47a28a16a119f29e09ce9c99c49b299398e96f95d94b9399349088f68e48d28c08ae8a989789286685484283081e81981480f80a7f87e67d47cf7ca7c579979477577076b74c72d71b7167116f26e06c16af6aa69869368165563662461f61a6155f65e45d25cd5ae55b55654453252d51b5094ea4d84d34c14a24834644384264143b43a238337e35f34d32e30f30a2f82d92d42b52b029e27225324e22f21d20b2061f41e21dd1be19f18d16e14f14a14513312110f10a0f80e60e10cf0b009e07f06d000f9b968605475c140fda82c619475c140e6dd706193a1a510bdb86c615475c140bdb88c485475c140fd3985549475c140e6dd746193a1a510f9b968609475c140bdb96c549475c140bdb91c219475c1409f780c5ed6461552e67d855496a1e560bdb96c485475c140bdb98c485475c140fcb986589475c140bdb98c595475c140bdb88c595475c140bdb98c549475c140fcb986595475c140fdb181485475c140e67d706195a1a5109dec2c62d6551d70bdb95c219475c140][i]?.getD 0
def m511H8 (_ : Nat) : Nat := 0x8003e
def m511D8 (_ : Nat) : Nat := 0xa27b505ac62caa3ae0a04f6a0b58c585475c140
def m511L : Nat → Packing
  | 14 => (1,0,8,0,0,1,0,m511D14)
  | 13 => (33,1,8,0,0,11,0,m511D13)
  | 12 => (436,2,8,0,0,15,0,m511D12)
  | 11 => (1348,3,8,0,0,17,0,m511D11)
  | 10 => (1231,4,8,0,0,17,0,m511D10)
  | 9 => (151,5,8,0,0,12,0,m511D9)
  | 8 => (2,6,8,0,0,3,0,m511D8)
  | _ => emptyPacking
def m511I : Nat → Nat → Option (Nat × Nat)
  | 14,h => lookupWord 11 42 4 10 6 0 m511H13 (mixTag h)
  | 13,h => lookupWord 146 490 8 13 9 0 m511H12 (mixTag h)
  | 12,h => lookupWord 450 1515 8 15 11 0 m511H11 (mixTag h)
  | 11,h => lookupWord 411 1383 10 15 11 0 m511H10 (mixTag h)
  | 10,h => lookupWord 51 172 6 12 8 0 m511H9 (mixTag h)
  | 9,h => lookupWord 1 4 1 5 1 0 m511H8 (mixTag h)
  | _,_ => none
def m511 : Forest := ⟨1535,14,m511S,m511C,[[]],m511L,m511I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_14_0 : block m511 14 0 1 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_14 : block m511 14 0 1 = true := bm511_14_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_13_0 : block m511 13 0 33 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_13 : block m511 13 0 33 = true := bm511_13_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_12_0 : block m511 12 0 17 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_12_17 : block m511 12 17 187 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=5)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_12_204 : block m511 12 204 232 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=5)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_12 : block m511 12 0 436 = true := (@block_merge m511 12 0 17 419 bm511_12_0 (@block_merge m511 12 17 187 232 bm511_12_17 bm511_12_204))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_11_0 : block m511 11 0 44 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_11_44 : block m511 11 44 596 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=7)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_11_640 : block m511 11 640 636 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=7)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_11_1276 : block m511 11 1276 72 = true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_11 : block m511 11 0 1348 = true := (@block_merge m511 11 0 44 1304 bm511_11_0 (@block_merge m511 11 44 596 708 bm511_11_44 (@block_merge m511 11 640 636 72 bm511_11_640 bm511_11_1276)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_10_0 : block m511 10 0 104 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_10_104 : block m511 10 104 822 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=7)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_10_926 : block m511 10 926 305 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=6)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_10 : block m511 10 0 1231 = true := (@block_merge m511 10 0 104 1127 bm511_10_0 (@block_merge m511 10 104 822 305 bm511_10_104 bm511_10_926))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_9_0 : block m511 9 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_9_1 : block m511 9 1 91 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_9_92 : block m511 9 92 59 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_9 : block m511 9 0 151 = true := (@block_merge m511 9 0 1 150 bm511_9_0 (@block_merge m511 9 1 91 59 bm511_9_1 bm511_9_92))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_8_0 : block m511 8 0 2 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_8 : block m511 8 0 2 = true := bm511_8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tm511 : checkedTables m511 14 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bm511_8
  · exact bm511_9
  · exact bm511_10
  · exact bm511_11
  · exact bm511_12
  · exact bm511_13
  · exact bm511_14
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gm511 : graphValid m511 (boundsBefore es511) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lm511 : Lower false (vars 511) (graphGoal 511) 15 := lower_forest (g:=m511) (i:=0) (hints:=8591013460) (before_sound es511 (known_down vs511)) gm511 tm511 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem fromLower {u : Bool} {k : Nat} (lb : Lower u (vars 511) (graphGoal 511) (k+1)) :
    Impossible u graph k inputs.toFinset := by
  have vr : vars 511 = inputs := by decide +kernel
  have tg : graphGoal 511 = graph := by decide +kernel
  rw [vr,tg] at lb
  intro s hs run
  have rr := list_run run inputs (by decide +kernel) rfl
  have sup : supply u (inputs.map observe) (inputs.map observe) := fun _ hm => Or.inl hm
  obtain ⟨q,bs,hq,hit,le⟩ := contraction (observe_proper graph_proper) rr _ Reach.start sup
  have hlow := lb q bs hq hit
  omega
end PEqualNP.Outside.L_meta_10830
open PEqualNP.Outside.L_meta_10830 in
theorem PEqualNP.Outside.L_meta_10830 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8)) t → 15 ≤ t := by
  intro t ⟨C,legal,small,computes⟩
  by_contra! low
  exact directSplit (fromLower lm511) (fromLower ls511) ⟨C,legal,by omega,computes⟩
