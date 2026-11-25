import PEqualNP.Defs

-- The AND/OR circuit is checked on all 128 assignments.
-- The signed search uses the forest and restriction lemmas of L-meta-10802,
-- adapted there from L-meta-1674, L-meta-670 and L-meta-1667.
-- Each forest certifies a restriction of the graph in this file.
namespace PEqualNP.Outside.L_meta_10892
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
def graph : Sig := 0xfffffffefffffffafffeffeefefeaa00fffffffefffffffafffeffeefefeaa00fffffffefffffffafffeffeefefeaa00fffffffefffffffafffeffeefefeaa00
theorem graph_proper : proper graph := by unfold proper; decide +kernel
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
def typeWord (t : Nat) : Sig := bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)
def varsX (m : Nat) : List Sig := if m<512 then vars m else vars m ++ [typeWord (m/512-1)]
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6)
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
    let r := if t/81==2 && i==t/9 % 9 then 1 <<< (t % 9) else if t/81==2 && i==t % 9 then 1 <<< (t/9 % 9) else 0
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
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


abbrev Bits := BitVec 195
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 195 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 195 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 195 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 195 → Row) (x : Decor) := x.2 = pairSig r s x.1
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

def asRow (cols : Nat → Bits) (i : Fin 195) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 195) (j : Fin 9) :
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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 195) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 195) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide)]
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
  let n := v.toNat % 2305843009213693921
  (n*(n+971)) % 2305843009213693921
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
    if (rs ||| column d z.2) != BitVec.allOnes 195 then true else
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 195) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 195 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
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


def lookupShort (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 4 then
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
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 195) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 195) (hq : chartSamples m q = 0) :
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

def prefixWidth (d : Nat) := 10*(d-1)
def denseRowWidth (d flags : Nat) := flags % 16 + (if d=0 then 0 else 10) + flags/16
def denseRowStart (d raw dict : Nat) :=
  (dict % 65536)*prefixWidth d + (dict/65536)*(raw+d)

def forestRecord (tab : Packing) (raw i : Nat) : Nat :=
  let (_,d,_,dict,flags,_,marker,word) := tab
  let width := 10*d+raw+d
  if marker<1024 then packedAt word (i*width) width else
    let off := denseRowStart d raw dict+i*denseRowWidth d flags
    let pre := packedAt word off (flags % 16)
    let lastBits := if d=0 then 0 else 10
    let last := packedAt word (off+flags % 16) lastBits
    let mask := packedAt word (off+flags % 16+lastBits) (flags/16)
    let base := (dict % 65536)*prefixWidth d
    packedAt word (pre*prefixWidth d) (prefixWidth d) |||
      (last <<< prefixWidth d) ||| (packedAt word (base+mask*(raw+d)) (raw+d) <<< (10*d))


def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := forestRecord (g.levels k) raw.length i
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

def forceDatum {α : Type} : Nat → (Nat → α) → α
  | 0, next => next 0
  | n+1, next => next (n+1)

def readSortedHints (data : Nat → Nat) (dict cw d gapBits : Nat) :
    Nat → Nat → Nat → List (Nat × Nat)
  | 0,_,_ => []
  | left+1,st,first =>
    forceDatum st fun pos => forceDatum first fun base =>
    forceDatum (packedAt data pos 32) fun head =>
    forceDatum (Nat.log2 (head ^^^ (head+1))) fun ones =>
    forceDatum (base+(ones <<< gapBits)+packedAt data (pos+ones+1) gapBits) fun key =>
    forceDatum (packedAt data (dict+key*(cw+d)) (cw+d)) fun pair =>
      (pair &&& ((1 <<< cw)-1),pair >>> cw) ::
        readSortedHints data dict cw d gapBits left (pos+ones+1+gapBits) (key+1)

def promoteHints {α : Type} (a b : Nat) (xs : List α) : List α :=
  let rec collect : List α → Nat → List α → List α → List α → List α
    | [],_,first,second,other => first ++ second ++ other.reverse
    | x::tail,i,first,second,other =>
      if i=a then collect tail (i+1) [x] second other
      else if i=b then collect tail (i+1) first [x] other
      else collect tail (i+1) first second (x::other)
  collect xs 0 [] [] []

def forestHints (tab : Packing) (raw i : Nat) : List (Nat × Nat) :=
  let (num,d,cw,dict,flags,ow,marker,data) := tab
  if marker<1024 then
    let start := num*(10*d+raw+d)
    let pos := start+num*ow+packedAt data (start+i*ow) ow
    getPairs data cw d (packedAt data pos 6) (pos+6+marker)
  else
    let off := denseRowStart d raw dict + num*denseRowWidth d flags
    let pairs := off+num*ow
    let priority := decide (4096≤marker)
    let pos := pairs+(marker-(if priority then 4096 else 1024))*(cw+d)+packedAt data (off+i*ow) ow
    let n := packedAt data pos 5
    let gap := packedAt data (pos+5) 3
    if !priority || decide (n≤1) then readSortedHints data pairs cw d gap n (pos+8) 0 else
      let width := (n-1).log2+1
      let a := packedAt data (pos+8) width
      let b := if n=2 then 1-a else packedAt data (pos+8+width) width
      let extra := if n=2 then width else 2*width
      let xs := readSortedHints data pairs cw d gap n (pos+8+extra) 0
      promoteHints a b xs

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
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
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
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 195) &&
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

def Known (u : Bool) (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (carries : List (Nat × List Nat)) :=
  carries.map (fun v => (v.1,L)) ++ old
theorem extend_ok {u old L m carries} (previous : Known u old)
    (main : Lower u (varsX m) (graphGoal m) L)
    (ok : carries.all (fun v => carryOK v.1 m v.2) = true) :
    Known u (extendKnown old L carries) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact carry_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known true [] := by simp [Known]
def target (x : Fin 7 → Bool) : Bool := decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[
    ⟨.or, [4, 6]⟩,
    ⟨.or, [0, 6]⟩,
    ⟨.or, [1, 3]⟩,
    ⟨.or, [0, 2]⟩,
    ⟨.or, [0, 9]⟩,
    ⟨.or, [1, 6]⟩,
    ⟨.and, [8, 3]⟩,
    ⟨.and, [5, 11]⟩,
    ⟨.and, [7, 10]⟩,
    ⟨.and, [12, 4]⟩,
    ⟨.or, [15, 16]⟩,
    ⟨.or, [14, 17]⟩,
    ⟨.or, [13, 18]⟩], 19⟩

theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 7 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel

theorem witnessSize : smallCircuit.gates.length = 13 := rfl

theorem noNotReuse {gates : List Gate} (fit : ∀ g ∈ gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (h : ∀ g ∈ gates, g.op ≠ GateOp.not) :
    ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨ops,arity⟩ := fit g hg
  refine ⟨?_,arity⟩
  rcases ops with a | b | c
  · exact Or.inl a
  · exact Or.inr b
  · exact (h g hg c).elim


def sevenInputs : List Sig := vars 127
def sampleSeven (r : Row) (i : Fin 7) : Bool := bit r (sevenInputs.getD i.val zero)
theorem sevenList : List.ofFn (fun i : Fin 7 => sevenInputs.getD i.val zero) = sevenInputs := rfl
theorem sevenSampled (r : Row) : List.ofFn (sampleSeven r) = sevenInputs.map (bit r) := by
  rw [←sevenList,List.map_ofFn]
  rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem sevenTable : ∀ r : Row, bit r graph = target (sampleSeven r) := by decide +kernel

theorem sevenEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates sevenInputs).getD i zero) =
      (C.wires (List.ofFn (sampleSeven r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sevenSampled]
  rfl

def lowRow (i : Fin 7) : Row := Fin.ofNat 512 (1 <<< ([3, 4, 4, 0, 0, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 7) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([3, 4, 4, 0, 0, 0, 0] : List Nat).getD i.val 0))

set_option maxHeartbeats 1000000 in
theorem allSevenRequired :
    (∀ i : Fin 7, bit (lowRow i) graph ≠ bit (highRow i) graph) ∧
    (∀ i j : Fin 7, i ≠ j →
      bit (lowRow i) (sevenInputs.getD j.val zero) =
      bit (highRow i) (sevenInputs.getD j.val zero)) := by decide +kernel

theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k sevenInputs.toFinset := by
  have goalEq : (execute C.gates sevenInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (sevenEval C legal C.output r).trans ((computes (sampleSeven r)).trans (sevenTable r).symm)
  have out := get_rep (u:=true) (execute C.gates sevenInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates sevenInputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : sevenInputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ sevenInputs) : ∃ i : Fin 7, sevenInputs.getD i.val zero = a := by
    rw [←sevenList] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = sevenInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run sevenInputs (sevenInputs.getD i.val zero) sub (lowRow i) (highRow i)
        (allSevenRequired.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply allSevenRequired.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨k,hk,eq ▸ run⟩

theorem replaceShort
    (lower : Impossible true graph 11 sevenInputs.toFinset) (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 7 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 7 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 13 ≤ gates.length
  · exact ⟨smallCircuit.gates,smallCircuit.output,witnessMonotone,(by simpa only [witnessSize] using big),witnessCorrect⟩
  by_cases mono : ∀ g ∈ gates, g.op ≠ GateOp.not
  · exact ⟨gates,o,noNotReuse fit mono,Nat.le_refl _,correct⟩
  push Not at mono
  obtain ⟨g,hg,hop⟩ := mono
  have lt : gates.countP (fun q => !isNot q) < gates.length := by
    rcases Nat.lt_or_ge (gates.countP (fun q => !isNot q)) gates.length with h | h
    · exact h
    · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
      simp [isNot,hop] at eq
  have legal : PEqualNP.MetaComplexity.FanInTwo (Circuit.mk gates o) := by
    intro g hg
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using fit g hg
  obtain ⟨k,hk,run⟩ := physicalSigned (Circuit.mk gates o) legal correct
  change k ≤ gates.countP (fun q => !isNot q) at hk
  exact (lower k (by omega) run).elim


def repeatRows (k value : Nat) : Bits := BitVec.ofNat 195 (value * ((2 ^ (k * ((195 + k - 1) / k)) - 1) / (2 ^ k - 1)))

def g41Y : Array (Bits × Bits) := #[((repeatRows 7 0x2f), (repeatRows 7 0x6)),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 7 0x5b), (repeatRows 7 0x18)),
    (0x0, 0x0),
    ((repeatRows 7 0x74), (repeatRows 7 0x60)),
    (0x0, 0x0)]
def g41C : List ColumnInfo := []
def g41D3 (j : Nat) : Nat := if j = 0 then 0x7 else 0
def g41L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g41D3)
  | _ => emptyPacking
def g41I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g41 : Forest := ⟨41, 3, fun i => (g41Y[i]?).getD (0,0), g41C, [[], [83], [48], [48, 83], [80, 83], [80]], g41L, g41I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g41P3n0 : block g41 3 0 1 = true := by decide +kernel
theorem g41B3 : block g41 3 0 1 = true := g41P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g41T : checkedTables g41 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g41 0 0 0 = true)
  · exact (rfl : block g41 1 0 0 = true)
  · exact (rfl : block g41 2 0 0 = true)
  · exact g41B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g41G : graphValid g41 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low41 : Lower true (varsX 41) (graphGoal 41) 4 := lower_forest (g:=g41) (i:=0) (hints:=3) (before_sound [] baseKnown) g41G g41T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K41 := extendKnown [] 4 [(41,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V41 : Known true K41 := extend_ok (m:=41) baseKnown low41 (by decide +kernel)

def g73Y : Array (Bits × Bits) := #[((repeatRows 7 0x2f), (repeatRows 7 0x6)),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 7 0x5b), (repeatRows 7 0x18)),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 7 0x74), (repeatRows 7 0x60))]
def g73C : List ColumnInfo := []
def g73D3 (j : Nat) : Nat := if j = 0 then 0x7 else 0
def g73L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g73D3)
  | _ => emptyPacking
def g73I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g73 : Forest := ⟨73, 3, fun i => (g73Y[i]?).getD (0,0), g73C, [[], [99], [48], [48, 99], [96, 99], [96]], g73L, g73I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g73P3n0 : block g73 3 0 1 = true := by decide +kernel
theorem g73B3 : block g73 3 0 1 = true := g73P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g73T : checkedTables g73 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g73 0 0 0 = true)
  · exact (rfl : block g73 1 0 0 = true)
  · exact (rfl : block g73 2 0 0 = true)
  · exact g73B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g73G : graphValid g73 (boundsBefore K41) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low73 : Lower true (varsX 73) (graphGoal 73) 4 := lower_forest (g:=g73) (i:=0) (hints:=3) (before_sound K41 V41) g73G g73T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K73 := extendKnown K41 4 [(73,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V73 : Known true K73 := extend_ok (m:=73) V41 low73 (by decide +kernel)

def g81Y : Array (Bits × Bits) := #[((repeatRows 7 0x2f), (repeatRows 7 0x6)),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 7 0x5b), (repeatRows 7 0x18)),
    (0x0, 0x0),
    ((repeatRows 7 0x74), (repeatRows 7 0x60))]
def g81C : List ColumnInfo := []
def g81D3 (j : Nat) : Nat := if j = 0 then 0x7 else 0
def g81L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g81D3)
  | _ => emptyPacking
def g81I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g81 : Forest := ⟨81, 3, fun i => (g81Y[i]?).getD (0,0), g81C, [[], [100], [64], [64, 100], [96, 100], [96]], g81L, g81I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g81P3n0 : block g81 3 0 1 = true := by decide +kernel
theorem g81B3 : block g81 3 0 1 = true := g81P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g81T : checkedTables g81 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g81 0 0 0 = true)
  · exact (rfl : block g81 1 0 0 = true)
  · exact (rfl : block g81 2 0 0 = true)
  · exact g81B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g81G : graphValid g81 (boundsBefore K73) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low81 : Lower true (varsX 81) (graphGoal 81) 4 := lower_forest (g:=g81) (i:=0) (hints:=4) (before_sound K73 V73) g81G g81T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K81 := extendKnown K73 4 [(81,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V81 : Known true K81 := extend_ok (m:=81) V73 low81 (by decide +kernel)

def g84Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 7 0x2f), (repeatRows 7 0x6)),
    (0x0, 0x0),
    ((repeatRows 7 0x5b), (repeatRows 7 0x18)),
    (0x0, 0x0),
    ((repeatRows 7 0x74), (repeatRows 7 0x60))]
def g84C : List ColumnInfo := []
def g84D3 (j : Nat) : Nat := if j = 0 then 0x7 else 0
def g84L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g84D3)
  | _ => emptyPacking
def g84I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g84 : Forest := ⟨84, 3, fun i => (g84Y[i]?).getD (0,0), g84C, [[], [100], [66], [66, 100], [98, 100], [98]], g84L, g84I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g84P3n0 : block g84 3 0 1 = true := by decide +kernel
theorem g84B3 : block g84 3 0 1 = true := g84P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g84T : checkedTables g84 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g84 0 0 0 = true)
  · exact (rfl : block g84 1 0 0 = true)
  · exact (rfl : block g84 2 0 0 = true)
  · exact g84B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g84G : graphValid g84 (boundsBefore K81) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low84 : Lower true (varsX 84) (graphGoal 84) 4 := lower_forest (g:=g84) (i:=0) (hints:=33686528) (before_sound K81 V81) g84G g84T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K84 := extendKnown K81 4 [(84,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V84 : Known true K84 := extend_ok (m:=84) V81 low84 (by decide +kernel)

def g27Y : Array (Bits × Bits) := #[((repeatRows 11 0x5ef), (repeatRows 11 0x2e)),
    ((repeatRows 11 0x294), (repeatRows 11 0x330)),
    (0x0, 0x0),
    ((repeatRows 11 0x1e7), (repeatRows 11 0x3c0)),
    ((repeatRows 11 0x618), (repeatRows 11 0x400)),
    (0x0, 0x0),
    (0x0, 0x0)]
def g27C : List ColumnInfo := []
def g27D3 (j : Nat) : Nat := if j = 0 then 0xf else 0
def g27L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g27D3)
  | _ => emptyPacking
def g27I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g27 : Forest := ⟨27, 3, fun i => (g27Y[i]?).getD (0,0), g27C, [[], [64, 49]], g27L, g27I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g27P3n0 : block g27 3 0 1 = true := by decide +kernel
theorem g27B3 : block g27 3 0 1 = true := g27P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g27T : checkedTables g27 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g27 0 0 0 = true)
  · exact (rfl : block g27 1 0 0 = true)
  · exact (rfl : block g27 2 0 0 = true)
  · exact g27B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g27G : graphValid g27 (boundsBefore K84) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low27 : Lower true (varsX 27) (graphGoal 27) 4 := lower_forest (g:=g27) (i:=0) (hints:=67) (before_sound K84 V84) g27G g27T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K27 := extendKnown K84 4 [(27,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V27 : Known true K27 := extend_ok (m:=27) V84 low27 (by decide +kernel)

def g29Y : Array (Bits × Bits) := #[((repeatRows 11 0x5ef), (repeatRows 11 0x2e)),
    (0x0, 0x0),
    ((repeatRows 11 0x294), (repeatRows 11 0x330)),
    ((repeatRows 11 0x1e7), (repeatRows 11 0x3c0)),
    ((repeatRows 11 0x618), (repeatRows 11 0x400)),
    (0x0, 0x0),
    (0x0, 0x0)]
def g29C : List ColumnInfo := []
def g29D3 (j : Nat) : Nat := if j = 0 then 0xf else 0
def g29L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g29D3)
  | _ => emptyPacking
def g29I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g29 : Forest := ⟨29, 3, fun i => (g29Y[i]?).getD (0,0), g29C, [[], [64, 50]], g29L, g29I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g29P3n0 : block g29 3 0 1 = true := by decide +kernel
theorem g29B3 : block g29 3 0 1 = true := g29P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g29T : checkedTables g29 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g29 0 0 0 = true)
  · exact (rfl : block g29 1 0 0 = true)
  · exact (rfl : block g29 2 0 0 = true)
  · exact g29B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g29G : graphValid g29 (boundsBefore K27) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low29 : Lower true (varsX 29) (graphGoal 29) 4 := lower_forest (g:=g29) (i:=0) (hints:=1027) (before_sound K27 V27) g29G g29T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K29 := extendKnown K27 4 [(29,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V29 : Known true K29 := extend_ok (m:=29) V27 low29 (by decide +kernel)

def g43Y : Array (Bits × Bits) := #[((repeatRows 13 0x777), (repeatRows 13 0x36)),
    ((repeatRows 13 0xa28), (repeatRows 13 0x338)),
    (0x0, 0x0),
    ((repeatRows 13 0x13f3), (repeatRows 13 0x3c0)),
    (0x0, 0x0),
    ((repeatRows 13 0x1c8c), (repeatRows 13 0x1c00)),
    (0x0, 0x0)]
def g43C : List ColumnInfo := [(2,0,41,0,4)]
def g43D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g43L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g43D4)
  | _ => emptyPacking
def g43I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g43 : Forest := ⟨43, 4, fun i => (g43Y[i]?).getD (0,0), g43C, [[], [48]], g43L, g43I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43P4n0 : block g43 4 0 1 = true := by decide +kernel
theorem g43B4 : block g43 4 0 1 = true := g43P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43T : checkedTables g43 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g43 0 0 0 = true)
  · exact (rfl : block g43 1 0 0 = true)
  · exact (rfl : block g43 2 0 0 = true)
  · exact (rfl : block g43 3 0 0 = true)
  · exact g43B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43G : graphValid g43 (boundsBefore K29) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low43 : Lower true (varsX 43) (graphGoal 43) 5 := lower_forest (g:=g43) (i:=0) (hints:=83) (before_sound K29 V29) g43G g43T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K43 := extendKnown K29 5 [(43,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V43 : Known true K43 := extend_ok (m:=43) V29 low43 (by decide +kernel)

def g53Y : Array (Bits × Bits) := #[((repeatRows 10 0x26f), (repeatRows 10 0x2c)),
    (0x0, 0x0),
    ((repeatRows 10 0x190), (repeatRows 10 0x330)),
    (0x0, 0x0),
    ((repeatRows 10 0x1d5), (repeatRows 10 0xc0)),
    ((repeatRows 10 0x22a), (repeatRows 10 0x300)),
    (0x0, 0x0)]
def g53C : List ColumnInfo := []
def g53D3 (j : Nat) : Nat := if j = 0 then 0xf else 0
def g53L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g53D3)
  | _ => emptyPacking
def g53I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g53 : Forest := ⟨53, 3, fun i => (g53Y[i]?).getD (0,0), g53C, [[], [64, 82]], g53L, g53I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g53P3n0 : block g53 3 0 1 = true := by decide +kernel
theorem g53B3 : block g53 3 0 1 = true := g53P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g53T : checkedTables g53 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g53 0 0 0 = true)
  · exact (rfl : block g53 1 0 0 = true)
  · exact (rfl : block g53 2 0 0 = true)
  · exact g53B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g53G : graphValid g53 (boundsBefore K43) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low53 : Lower true (varsX 53) (graphGoal 53) 4 := lower_forest (g:=g53) (i:=0) (hints:=1028) (before_sound K43 V43) g53G g53T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K53 := extendKnown K43 4 [(53,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V53 : Known true K53 := extend_ok (m:=53) V43 low53 (by decide +kernel)

def g54Y : Array (Bits × Bits) := #[(0x0, 0x0),
    ((repeatRows 10 0x26f), (repeatRows 10 0x2c)),
    ((repeatRows 10 0x190), (repeatRows 10 0x330)),
    (0x0, 0x0),
    ((repeatRows 10 0x1d5), (repeatRows 10 0xc0)),
    ((repeatRows 10 0x22a), (repeatRows 10 0x300)),
    (0x0, 0x0)]
def g54C : List ColumnInfo := []
def g54D3 (j : Nat) : Nat := if j = 0 then 0xf else 0
def g54L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g54D3)
  | _ => emptyPacking
def g54I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g54 : Forest := ⟨54, 3, fun i => (g54Y[i]?).getD (0,0), g54C, [[], [65, 82]], g54L, g54I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g54P3n0 : block g54 3 0 1 = true := by decide +kernel
theorem g54B3 : block g54 3 0 1 = true := g54P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g54T : checkedTables g54 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g54 0 0 0 = true)
  · exact (rfl : block g54 1 0 0 = true)
  · exact (rfl : block g54 2 0 0 = true)
  · exact g54B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g54G : graphValid g54 (boundsBefore K53) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low54 : Lower true (varsX 54) (graphGoal 54) 4 := lower_forest (g:=g54) (i:=0) (hints:=1115200) (before_sound K53 V53) g54G g54T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K54 := extendKnown K53 4 [(54,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V54 : Known true K54 := extend_ok (m:=54) V53 low54 (by decide +kernel)

def g57Y : Array (Bits × Bits) := #[((repeatRows 13 0x25f), (repeatRows 13 0xe)),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 13 0x1db3), (repeatRows 13 0x1b0)),
    ((repeatRows 13 0x1144), (repeatRows 13 0x19c0)),
    ((repeatRows 13 0x1fa8), (repeatRows 13 0x1e00)),
    (0x0, 0x0)]
def g57C : List ColumnInfo := [(16,0,41,0,4)]
def g57D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g57L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g57D4)
  | _ => emptyPacking
def g57I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g57 : Forest := ⟨57, 4, fun i => (g57Y[i]?).getD (0,0), g57C, [[], [83]], g57L, g57I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g57P4n0 : block g57 4 0 1 = true := by decide +kernel
theorem g57B4 : block g57 4 0 1 = true := g57P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g57T : checkedTables g57 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g57 0 0 0 = true)
  · exact (rfl : block g57 1 0 0 = true)
  · exact (rfl : block g57 2 0 0 = true)
  · exact (rfl : block g57 3 0 0 = true)
  · exact g57B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g57G : graphValid g57 (boundsBefore K54) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low57 : Lower true (varsX 57) (graphGoal 57) 5 := lower_forest (g:=g57) (i:=0) (hints:=3) (before_sound K54 V54) g57G g57T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K57 := extendKnown K54 5 [(57,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V57 : Known true K57 := extend_ok (m:=57) V54 low57 (by decide +kernel)

def g58Y : Array (Bits × Bits) := #[(0x0, 0x0),
    ((repeatRows 11 0x5ef), (repeatRows 11 0x2e)),
    (0x0, 0x0),
    ((repeatRows 11 0x294), (repeatRows 11 0x330)),
    ((repeatRows 11 0x1e7), (repeatRows 11 0x3c0)),
    ((repeatRows 11 0x618), (repeatRows 11 0x400)),
    (0x0, 0x0)]
def g58C : List ColumnInfo := []
def g58D3 (j : Nat) : Nat := if j = 0 then 0xf else 0
def g58L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g58D3)
  | _ => emptyPacking
def g58I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g58 : Forest := ⟨58, 3, fun i => (g58Y[i]?).getD (0,0), g58C, [[], [81, 67]], g58L, g58I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g58P3n0 : block g58 3 0 1 = true := by decide +kernel
theorem g58B3 : block g58 3 0 1 = true := g58P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g58T : checkedTables g58 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g58 0 0 0 = true)
  · exact (rfl : block g58 1 0 0 = true)
  · exact (rfl : block g58 2 0 0 = true)
  · exact g58B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g58G : graphValid g58 (boundsBefore K57) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low58 : Lower true (varsX 58) (graphGoal 58) 4 := lower_forest (g:=g58) (i:=0) (hints:=1134656) (before_sound K57 V57) g58G g58T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K58 := extendKnown K57 4 [(58,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V58 : Known true K58 := extend_ok (m:=58) V57 low58 (by decide +kernel)

def g77Y : Array (Bits × Bits) := #[((repeatRows 13 0x777), (repeatRows 13 0x36)),
    (0x0, 0x0),
    ((repeatRows 13 0xa28), (repeatRows 13 0x338)),
    ((repeatRows 13 0x13f3), (repeatRows 13 0x3c0)),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 13 0x1c8c), (repeatRows 13 0x1c00))]
def g77C : List ColumnInfo := [(4,0,73,0,4)]
def g77D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g77L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g77D4)
  | _ => emptyPacking
def g77I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g77 : Forest := ⟨77, 4, fun i => (g77Y[i]?).getD (0,0), g77C, [[], [48]], g77L, g77I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g77P4n0 : block g77 4 0 1 = true := by decide +kernel
theorem g77B4 : block g77 4 0 1 = true := g77P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g77T : checkedTables g77 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g77 0 0 0 = true)
  · exact (rfl : block g77 1 0 0 = true)
  · exact (rfl : block g77 2 0 0 = true)
  · exact (rfl : block g77 3 0 0 = true)
  · exact g77B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g77G : graphValid g77 (boundsBefore K58) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low77 : Lower true (varsX 77) (graphGoal 77) 5 := lower_forest (g:=g77) (i:=0) (hints:=1539) (before_sound K58 V58) g77G g77T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K77 := extendKnown K58 5 [(77,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V77 : Known true K77 := extend_ok (m:=77) V58 low77 (by decide +kernel)

def g83Y : Array (Bits × Bits) := #[((repeatRows 12 0xc77), (repeatRows 12 0x36)),
    ((repeatRows 12 0x8a8), (repeatRows 12 0xc38)),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 12 0x3cb), (repeatRows 12 0x1c0)),
    (0x0, 0x0),
    ((repeatRows 12 0xf34), (repeatRows 12 0xe00))]
def g83C : List ColumnInfo := [(2,0,81,0,4)]
def g83D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g83L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g83D4)
  | _ => emptyPacking
def g83I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g83 : Forest := ⟨83, 4, fun i => (g83Y[i]?).getD (0,0), g83C, [[], [96]], g83L, g83I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g83P4n0 : block g83 4 0 1 = true := by decide +kernel
theorem g83B4 : block g83 4 0 1 = true := g83P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g83T : checkedTables g83 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g83 0 0 0 = true)
  · exact (rfl : block g83 1 0 0 = true)
  · exact (rfl : block g83 2 0 0 = true)
  · exact (rfl : block g83 3 0 0 = true)
  · exact g83B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g83G : graphValid g83 (boundsBefore K77) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low83 : Lower true (varsX 83) (graphGoal 83) 5 := lower_forest (g:=g83) (i:=0) (hints:=68) (before_sound K77 V77) g83G g83T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K83 := extendKnown K77 5 [(83,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V83 : Known true K83 := extend_ok (m:=83) V77 low83 (by decide +kernel)

def g85Y : Array (Bits × Bits) := #[((repeatRows 11 0x127), (repeatRows 11 0x6)),
    (0x0, 0x0),
    ((repeatRows 11 0x258), (repeatRows 11 0x18)),
    (0x0, 0x0),
    ((repeatRows 11 0x4eb), (repeatRows 11 0xe0)),
    (0x0, 0x0),
    ((repeatRows 11 0x794), (repeatRows 11 0x700))]
def g85C : List ColumnInfo := [(1,0,84,0,4)]
def g85D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g85L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g85D4)
  | _ => emptyPacking
def g85I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g85 : Forest := ⟨85, 4, fun i => (g85Y[i]?).getD (0,0), g85C, [[], [100], [32], [32, 100]], g85L, g85I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g85P4n0 : block g85 4 0 1 = true := by decide +kernel
theorem g85B4 : block g85 4 0 1 = true := g85P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g85T : checkedTables g85 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g85 0 0 0 = true)
  · exact (rfl : block g85 1 0 0 = true)
  · exact (rfl : block g85 2 0 0 = true)
  · exact (rfl : block g85 3 0 0 = true)
  · exact g85B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g85G : graphValid g85 (boundsBefore K83) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low85 : Lower true (varsX 85) (graphGoal 85) 5 := lower_forest (g:=g85) (i:=0) (hints:=1028) (before_sound K83 V83) g85G g85T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K85 := extendKnown K83 5 [(85,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V85 : Known true K85 := extend_ok (m:=85) V83 low85 (by decide +kernel)

def g86Y : Array (Bits × Bits) := #[(0x0, 0x0),
    ((repeatRows 12 0x863), (repeatRows 12 0xc32)),
    ((repeatRows 12 0xcbc), (repeatRows 12 0x3c)),
    (0x0, 0x0),
    ((repeatRows 12 0x3c7), (repeatRows 12 0x1c0)),
    (0x0, 0x0),
    ((repeatRows 12 0xf38), (repeatRows 12 0xe00))]
def g86C : List ColumnInfo := [(2,0,84,0,4)]
def g86D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g86L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g86D4)
  | _ => emptyPacking
def g86I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g86 : Forest := ⟨86, 4, fun i => (g86Y[i]?).getD (0,0), g86C, [[], [98]], g86L, g86I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g86P4n0 : block g86 4 0 1 = true := by decide +kernel
theorem g86B4 : block g86 4 0 1 = true := g86P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g86T : checkedTables g86 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g86 0 0 0 = true)
  · exact (rfl : block g86 1 0 0 = true)
  · exact (rfl : block g86 2 0 0 = true)
  · exact (rfl : block g86 3 0 0 = true)
  · exact g86B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g86G : graphValid g86 (boundsBefore K85) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low86 : Lower true (varsX 86) (graphGoal 86) 5 := lower_forest (g:=g86) (i:=0) (hints:=33621056) (before_sound K85 V85) g86G g86T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K86 := extendKnown K85 5 [(86,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V86 : Known true K86 := extend_ok (m:=86) V85 low86 (by decide +kernel)

def g89Y : Array (Bits × Bits) := #[((repeatRows 11 0x15f), (repeatRows 11 0xe)),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 11 0x233), (repeatRows 11 0x30)),
    ((repeatRows 11 0x4c4), (repeatRows 11 0xc0)),
    (0x0, 0x0),
    ((repeatRows 11 0x7a8), (repeatRows 11 0x700))]
def g89C : List ColumnInfo := [(8,0,81,0,4)]
def g89D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g89L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g89D4)
  | _ => emptyPacking
def g89I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g89 : Forest := ⟨89, 4, fun i => (g89Y[i]?).getD (0,0), g89C, [[], [67], [96], [96, 67]], g89L, g89I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g89P4n0 : block g89 4 0 1 = true := by decide +kernel
theorem g89B4 : block g89 4 0 1 = true := g89P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g89T : checkedTables g89 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g89 0 0 0 = true)
  · exact (rfl : block g89 1 0 0 = true)
  · exact (rfl : block g89 2 0 0 = true)
  · exact (rfl : block g89 3 0 0 = true)
  · exact g89B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g89G : graphValid g89 (boundsBefore K86) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low89 : Lower true (varsX 89) (graphGoal 89) 5 := lower_forest (g:=g89) (i:=0) (hints:=3) (before_sound K86 V86) g89G g89T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K89 := extendKnown K86 5 [(89,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V89 : Known true K89 := extend_ok (m:=89) V86 low89 (by decide +kernel)

def g90Y : Array (Bits × Bits) := #[(0x0, 0x0),
    ((repeatRows 10 0x16b), (repeatRows 10 0x1a)),
    (0x0, 0x0),
    ((repeatRows 10 0x56), (repeatRows 10 0x11c)),
    ((repeatRows 10 0x3eb), (repeatRows 10 0x1e0)),
    (0x0, 0x0),
    ((repeatRows 10 0x294), (repeatRows 10 0x200))]
def g90C : List ColumnInfo := []
def g90D3 (j : Nat) : Nat := if j = 0 then 0xf else 0
def g90L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g90D3)
  | _ => emptyPacking
def g90I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g90 : Forest := ⟨90, 3, fun i => (g90Y[i]?).getD (0,0), g90C, [[], [49, 100]], g90L, g90I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g90P3n0 : block g90 3 0 1 = true := by decide +kernel
theorem g90B3 : block g90 3 0 1 = true := g90P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g90T : checkedTables g90 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g90 0 0 0 = true)
  · exact (rfl : block g90 1 0 0 = true)
  · exact (rfl : block g90 2 0 0 = true)
  · exact g90B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g90G : graphValid g90 (boundsBefore K89) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low90 : Lower true (varsX 90) (graphGoal 90) 4 := lower_forest (g:=g90) (i:=0) (hints:=50421824) (before_sound K89 V89) g90G g90T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K90 := extendKnown K89 4 [(90,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V90 : Known true K90 := extend_ok (m:=90) V89 low90 (by decide +kernel)

def g92Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 13 0x777), (repeatRows 13 0x36)),
    ((repeatRows 13 0xa28), (repeatRows 13 0x338)),
    ((repeatRows 13 0x13f3), (repeatRows 13 0x3c0)),
    (0x0, 0x0),
    ((repeatRows 13 0x1c8c), (repeatRows 13 0x1c00))]
def g92C : List ColumnInfo := [(8,0,84,0,4)]
def g92D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g92L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g92D4)
  | _ => emptyPacking
def g92I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g92 : Forest := ⟨92, 4, fun i => (g92Y[i]?).getD (0,0), g92C, [[], [66]], g92L, g92I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g92P4n0 : block g92 4 0 1 = true := by decide +kernel
theorem g92B4 : block g92 4 0 1 = true := g92P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g92T : checkedTables g92 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g92 0 0 0 = true)
  · exact (rfl : block g92 1 0 0 = true)
  · exact (rfl : block g92 2 0 0 = true)
  · exact (rfl : block g92 3 0 0 = true)
  · exact g92B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g92G : graphValid g92 (boundsBefore K90) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low92 : Lower true (varsX 92) (graphGoal 92) 5 := lower_forest (g:=g92) (i:=0) (hints:=33711104) (before_sound K90 V90) g92G g92T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K92 := extendKnown K90 5 [(92,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V92 : Known true K92 := extend_ok (m:=92) V90 low92 (by decide +kernel)

def g99Y : Array (Bits × Bits) := #[((repeatRows 10 0x26f), (repeatRows 10 0x2c)),
    ((repeatRows 10 0x190), (repeatRows 10 0x330)),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 10 0x1d5), (repeatRows 10 0xc0)),
    ((repeatRows 10 0x22a), (repeatRows 10 0x300))]
def g99C : List ColumnInfo := []
def g99D3 (j : Nat) : Nat := if j = 0 then 0xf else 0
def g99L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g99D3)
  | _ => emptyPacking
def g99I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g99 : Forest := ⟨99, 3, fun i => (g99Y[i]?).getD (0,0), g99C, [[], [80, 97]], g99L, g99I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g99P3n0 : block g99 3 0 1 = true := by decide +kernel
theorem g99B3 : block g99 3 0 1 = true := g99P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g99T : checkedTables g99 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g99 0 0 0 = true)
  · exact (rfl : block g99 1 0 0 = true)
  · exact (rfl : block g99 2 0 0 = true)
  · exact g99B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g99G : graphValid g99 (boundsBefore K92) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low99 : Lower true (varsX 99) (graphGoal 99) 4 := lower_forest (g:=g99) (i:=0) (hints:=85) (before_sound K92 V92) g99G g99T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K99 := extendKnown K92 4 [(99,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V99 : Known true K99 := extend_ok (m:=99) V92 low99 (by decide +kernel)

def g101Y : Array (Bits × Bits) := #[((repeatRows 11 0x5ef), (repeatRows 11 0x2e)),
    (0x0, 0x0),
    ((repeatRows 11 0x294), (repeatRows 11 0x330)),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 11 0x1e7), (repeatRows 11 0x3c0)),
    ((repeatRows 11 0x618), (repeatRows 11 0x400))]
def g101C : List ColumnInfo := []
def g101D3 (j : Nat) : Nat := if j = 0 then 0xf else 0
def g101L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g101D3)
  | _ => emptyPacking
def g101I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g101 : Forest := ⟨101, 3, fun i => (g101Y[i]?).getD (0,0), g101C, [[], [96, 82]], g101L, g101I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g101P3n0 : block g101 3 0 1 = true := by decide +kernel
theorem g101B3 : block g101 3 0 1 = true := g101P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g101T : checkedTables g101 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g101 0 0 0 = true)
  · exact (rfl : block g101 1 0 0 = true)
  · exact (rfl : block g101 2 0 0 = true)
  · exact g101B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g101G : graphValid g101 (boundsBefore K99) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low101 : Lower true (varsX 101) (graphGoal 101) 4 := lower_forest (g:=g101) (i:=0) (hints:=1541) (before_sound K99 V99) g101G g101T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K101 := extendKnown K99 4 [(101,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V101 : Known true K101 := extend_ok (m:=101) V99 low101 (by decide +kernel)

def g105Y : Array (Bits × Bits) := #[((repeatRows 11 0x29f), (repeatRows 11 0xe)),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 11 0x573), (repeatRows 11 0x70)),
    (0x0, 0x0),
    ((repeatRows 11 0x1a4), (repeatRows 11 0x180)),
    ((repeatRows 11 0x648), (repeatRows 11 0x600))]
def g105C : List ColumnInfo := [(32,0,73,0,4)]
def g105D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g105L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g105D4)
  | _ => emptyPacking
def g105I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g105 : Forest := ⟨105, 4, fun i => (g105Y[i]?).getD (0,0), g105C, [[], [101], [48], [48, 101]], g105L, g105I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g105P4n0 : block g105 4 0 1 = true := by decide +kernel
theorem g105B4 : block g105 4 0 1 = true := g105P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g105T : checkedTables g105 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g105 0 0 0 = true)
  · exact (rfl : block g105 1 0 0 = true)
  · exact (rfl : block g105 2 0 0 = true)
  · exact (rfl : block g105 3 0 0 = true)
  · exact g105B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g105G : graphValid g105 (boundsBefore K101) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low105 : Lower true (varsX 105) (graphGoal 105) 5 := lower_forest (g:=g105) (i:=0) (hints:=3) (before_sound K101 V101) g105G g105T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K105 := extendKnown K101 5 [(105,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V105 : Known true K105 := extend_ok (m:=105) V101 low105 (by decide +kernel)

def g106Y : Array (Bits × Bits) := #[(0x0, 0x0),
    ((repeatRows 10 0x145), (repeatRows 10 0x324)),
    (0x0, 0x0),
    ((repeatRows 10 0x2ba), (repeatRows 10 0x38)),
    (0x0, 0x0),
    ((repeatRows 10 0x1cd), (repeatRows 10 0xc0)),
    ((repeatRows 10 0x232), (repeatRows 10 0x300))]
def g106C : List ColumnInfo := []
def g106D3 (j : Nat) : Nat := if j = 0 then 0xf else 0
def g106L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g106D3)
  | _ => emptyPacking
def g106I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g106 : Forest := ⟨106, 3, fun i => (g106Y[i]?).getD (0,0), g106C, [[], [97, 83]], g106L, g106I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g106P3n0 : block g106 3 0 1 = true := by decide +kernel
theorem g106B3 : block g106 3 0 1 = true := g106P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g106T : checkedTables g106 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g106 0 0 0 = true)
  · exact (rfl : block g106 1 0 0 = true)
  · exact (rfl : block g106 2 0 0 = true)
  · exact g106B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g106G : graphValid g106 (boundsBefore K105) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low106 : Lower true (varsX 106) (graphGoal 106) 4 := lower_forest (g:=g106) (i:=0) (hints:=51400784) (before_sound K105 V105) g106G g106T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K106 := extendKnown K105 4 [(106,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V106 : Known true K106 := extend_ok (m:=106) V105 low106 (by decide +kernel)

def g108Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 11 0x28a), (repeatRows 11 0x322)),
    ((repeatRows 11 0x5fd), (repeatRows 11 0x3c)),
    (0x0, 0x0),
    ((repeatRows 11 0x1ed), (repeatRows 11 0x3c0)),
    ((repeatRows 11 0x612), (repeatRows 11 0x400))]
def g108C : List ColumnInfo := []
def g108D3 (j : Nat) : Nat := if j = 0 then 0xf else 0
def g108L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g108D3)
  | _ => emptyPacking
def g108I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g108 : Forest := ⟨108, 3, fun i => (g108Y[i]?).getD (0,0), g108C, [[], [82, 99]], g108L, g108I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g108P3n0 : block g108 3 0 1 = true := by decide +kernel
theorem g108B3 : block g108 3 0 1 = true := g108P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g108T : checkedTables g108 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g108 0 0 0 = true)
  · exact (rfl : block g108 1 0 0 = true)
  · exact (rfl : block g108 2 0 0 = true)
  · exact g108B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g108G : graphValid g108 (boundsBefore K106) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low108 : Lower true (varsX 108) (graphGoal 108) 4 := lower_forest (g:=g108) (i:=0) (hints:=36722176) (before_sound K106 V106) g108G g108T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K108 := extendKnown K106 4 [(108,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V108 : Known true K108 := extend_ok (m:=108) V106 low108 (by decide +kernel)

def g113Y : Array (Bits × Bits) := #[((repeatRows 13 0x25f), (repeatRows 13 0xe)),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 13 0x1db3), (repeatRows 13 0x1b0)),
    ((repeatRows 13 0x1144), (repeatRows 13 0x19c0)),
    ((repeatRows 13 0x1fa8), (repeatRows 13 0x1e00))]
def g113C : List ColumnInfo := [(32,0,81,0,4)]
def g113D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g113L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g113D4)
  | _ => emptyPacking
def g113I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g113 : Forest := ⟨113, 4, fun i => (g113Y[i]?).getD (0,0), g113C, [[], [100]], g113L, g113I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g113P4n0 : block g113 4 0 1 = true := by decide +kernel
theorem g113B4 : block g113 4 0 1 = true := g113P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g113T : checkedTables g113 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g113 0 0 0 = true)
  · exact (rfl : block g113 1 0 0 = true)
  · exact (rfl : block g113 2 0 0 = true)
  · exact (rfl : block g113 3 0 0 = true)
  · exact g113B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g113G : graphValid g113 (boundsBefore K108) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low113 : Lower true (varsX 113) (graphGoal 113) 5 := lower_forest (g:=g113) (i:=0) (hints:=4) (before_sound K108 V108) g113G g113T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K113 := extendKnown K108 5 [(113,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V113 : Known true K113 := extend_ok (m:=113) V108 low113 (by decide +kernel)

def g114Y : Array (Bits × Bits) := #[(0x0, 0x0),
    ((repeatRows 10 0x15d), (repeatRows 10 0xc)),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 10 0x2b7), (repeatRows 10 0xb0)),
    ((repeatRows 10 0x148), (repeatRows 10 0x3c0)),
    ((repeatRows 10 0x2a2), (repeatRows 10 0x300))]
def g114C : List ColumnInfo := []
def g114D3 (j : Nat) : Nat := if j = 0 then 0xf else 0
def g114L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g114D3)
  | _ => emptyPacking
def g114I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g114 : Forest := ⟨114, 3, fun i => (g114Y[i]?).getD (0,0), g114C, [[], [65, 101]], g114L, g114I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g114P3n0 : block g114 3 0 1 = true := by decide +kernel
theorem g114B3 : block g114 3 0 1 = true := g114P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g114T : checkedTables g114 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g114 0 0 0 = true)
  · exact (rfl : block g114 1 0 0 = true)
  · exact (rfl : block g114 2 0 0 = true)
  · exact g114B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g114G : graphValid g114 (boundsBefore K113) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low114 : Lower true (varsX 114) (graphGoal 114) 4 := lower_forest (g:=g114) (i:=0) (hints:=68223040) (before_sound K113 V113) g114G g114T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K114 := extendKnown K113 4 [(114,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V114 : Known true K114 := extend_ok (m:=114) V113 low114 (by decide +kernel)

def g120Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 11 0x5ef), (repeatRows 11 0x2e)),
    ((repeatRows 11 0x294), (repeatRows 11 0x330)),
    ((repeatRows 11 0x1e7), (repeatRows 11 0x3c0)),
    ((repeatRows 11 0x618), (repeatRows 11 0x400))]
def g120C : List ColumnInfo := []
def g120D3 (j : Nat) : Nat := if j = 0 then 0xf else 0
def g120L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g120D3)
  | _ => emptyPacking
def g120I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g120 : Forest := ⟨120, 3, fun i => (g120Y[i]?).getD (0,0), g120C, [[], [99, 84]], g120L, g120I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g120P3n0 : block g120 3 0 1 = true := by decide +kernel
theorem g120B3 : block g120 3 0 1 = true := g120P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g120T : checkedTables g120 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g120 0 0 0 = true)
  · exact (rfl : block g120 1 0 0 = true)
  · exact (rfl : block g120 2 0 0 = true)
  · exact g120B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g120G : graphValid g120 (boundsBefore K114) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low120 : Lower true (varsX 120) (graphGoal 120) 4 := lower_forest (g:=g120) (i:=0) (hints:=53891072) (before_sound K114 V114) g120G g120T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K120 := extendKnown K114 4 [(120,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V120 : Known true K120 := extend_ok (m:=120) V114 low120 (by decide +kernel)

def g31Y : Array (Bits × Bits) := #[((repeatRows 16 0x37f9), (repeatRows 16 0x78)),
    ((repeatRows 16 0x4902), (repeatRows 16 0xc20)),
    ((repeatRows 16 0x8204), (repeatRows 16 0x1040)),
    ((repeatRows 16 0x17e9), (repeatRows 16 0x1f80)),
    ((repeatRows 16 0xe816), (repeatRows 16 0xe000)),
    (0x0, 0x0),
    (0x0, 0x0)]
def g31C : List ColumnInfo := [(2,0,29,0,4)]
def g31D4 (j : Nat) : Nat := if j = 0 then 0x5f else 0
def g31L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g31D4)
  | _ => emptyPacking
def g31I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g31 : Forest := ⟨31, 4, fun i => (g31Y[i]?).getD (0,0), g31C, [[], [33]], g31L, g31I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P4n0 : block g31 4 0 1 = true := by decide +kernel
theorem g31B4 : block g31 4 0 1 = true := g31P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31T : checkedTables g31 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact g31B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31G : graphValid g31 (boundsBefore K120) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low31 : Lower true (varsX 31) (graphGoal 31) 5 := lower_forest (g:=g31) (i:=0) (hints:=1091) (before_sound K120 V120) g31G g31T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K31 := extendKnown K120 5 [(31,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V31 : Known true K31 := extend_ok (m:=31) V120 low31 (by decide +kernel)

def g55Y : Array (Bits × Bits) := #[((repeatRows 14 0x119d), (repeatRows 14 0x98)),
    ((repeatRows 14 0x2260), (repeatRows 14 0x60)),
    ((repeatRows 14 0xc02), (repeatRows 14 0x3880)),
    (0x0, 0x0),
    ((repeatRows 14 0xf2b), (repeatRows 14 0x700)),
    ((repeatRows 14 0x30d4), (repeatRows 14 0x3800)),
    (0x0, 0x0)]
def g55C : List ColumnInfo := [(1,0,54,0,4)]
def g55D4 (j : Nat) : Nat := if j = 0 then 0x5f else 0
def g55L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g55D4)
  | _ => emptyPacking
def g55I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g55 : Forest := ⟨55, 4, fun i => (g55Y[i]?).getD (0,0), g55C, [[], [16]], g55L, g55I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55P4n0 : block g55 4 0 1 = true := by decide +kernel
theorem g55B4 : block g55 4 0 1 = true := g55P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55T : checkedTables g55 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g55 0 0 0 = true)
  · exact (rfl : block g55 1 0 0 = true)
  · exact (rfl : block g55 2 0 0 = true)
  · exact (rfl : block g55 3 0 0 = true)
  · exact g55B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55G : graphValid g55 (boundsBefore K31) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (varsX 55) (graphGoal 55) 5 := lower_forest (g:=g55) (i:=0) (hints:=1092) (before_sound K31 V31) g55G g55T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K55 := extendKnown K31 5 [(55,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V55 : Known true K55 := extend_ok (m:=55) V31 low55 (by decide +kernel)

def g59Y : Array (Bits × Bits) := #[((repeatRows 23 0x84dcf), (repeatRows 23 0xce)),
    ((repeatRows 23 0x11b8b0), (repeatRows 23 0x3cf0)),
    (0x0, 0x0),
    ((repeatRows 23 0x672fc3), (repeatRows 23 0x73f00)),
    ((repeatRows 23 0x45f014), (repeatRows 23 0x47c000)),
    ((repeatRows 23 0x7e0228), (repeatRows 23 0x780000)),
    (0x0, 0x0)]
def g59C : List ColumnInfo := [(2,0,57,0,5)]
def g59D5 (j : Nat) : Nat := if j = 0 then 0x5f else 0
def g59L : Nat → Packing
  | 5 => (1, 0, 1, 0, 0, 1, 0, g59D5)
  | _ => emptyPacking
def g59I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g59 : Forest := ⟨59, 5, fun i => (g59Y[i]?).getD (0,0), g59C, [[], [80, 65]], g59L, g59I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P5n0 : block g59 5 0 1 = true := by decide +kernel
theorem g59B5 : block g59 5 0 1 = true := g59P5n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59T : checkedTables g59 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g59 0 0 0 = true)
  · exact (rfl : block g59 1 0 0 = true)
  · exact (rfl : block g59 2 0 0 = true)
  · exact (rfl : block g59 3 0 0 = true)
  · exact (rfl : block g59 4 0 0 = true)
  · exact g59B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59G : graphValid g59 (boundsBefore K55) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low59 : Lower true (varsX 59) (graphGoal 59) 6 := lower_forest (g:=g59) (i:=0) (hints:=67) (before_sound K55 V55) g59G g59T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K59 := extendKnown K55 6 [(59,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V59 : Known true K59 := extend_ok (m:=59) V55 low59 (by decide +kernel)

def g61Y : Array (Bits × Bits) := #[((repeatRows 26 0x229bef), (repeatRows 26 0x1ee)),
    (0x0, 0x0),
    ((repeatRows 26 0x1857150), (repeatRows 26 0x8079f0)),
    ((repeatRows 26 0x25c5e63), (repeatRows 26 0x1e7e00)),
    ((repeatRows 26 0x397e014), (repeatRows 26 0x31f8000)),
    ((repeatRows 26 0x3f80588), (repeatRows 26 0x3e00000)),
    (0x0, 0x0)]
def g61C : List ColumnInfo := [(0,4,41,16,5), (4,0,57,0,5), (8,0,53,0,4), (16,0,41,0,4), (16,4,41,0,4), (32,0,29,0,4)]
def g61D4 (j : Nat) : Nat := if j = 0 then 0x4fd5102 else 0
def g61D5 (j : Nat) : Nat := if j = 0 then 0x408804a0e140fd24ff02fd02 else 0
def g61D6 (j : Nat) : Nat := if j = 0 then 0x2c68819f else 0
def g61L : Nat → Packing
  | 4 => (1, 2, 3, 0, 0, 1, 0, g61D4)
  | 5 => (3, 1, 3, 0, 0, 5, 0, g61D5)
  | 6 => (1, 0, 3, 0, 0, 1, 0, g61D6)
  | _ => emptyPacking
def g61I : Nat → Nat → Option (Nat × Nat)
  | 5, tag => lookupShort 1 2 1 3 1 0 (fun j => if j=0 then 0x0 else 0) tag
  | 6, tag => lookupShort 3 8 1 5 2 1 (fun j => if j=0 then 0x713d0020094 else 0) tag
  | _, _ => none
def g61 : Forest := ⟨61, 6, fun i => (g61Y[i]?).getD (0,0), g61C, [[], [83]], g61L, g61I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P4n0 : block g61 4 0 1 = true := by decide +kernel
theorem g61B4 : block g61 4 0 1 = true := g61P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P5n0 : block g61 5 0 3 = true := by decide +kernel
theorem g61B5 : block g61 5 0 3 = true := g61P5n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P6n0 : block g61 6 0 1 = true := by decide +kernel
theorem g61B6 : block g61 6 0 1 = true := g61P6n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61T : checkedTables g61 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g61 0 0 0 = true)
  · exact (rfl : block g61 1 0 0 = true)
  · exact (rfl : block g61 2 0 0 = true)
  · exact (rfl : block g61 3 0 0 = true)
  · exact g61B4
  · exact g61B5
  · exact g61B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61G : graphValid g61 (boundsBefore K59) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low61 : Lower true (varsX 61) (graphGoal 61) 7 := lower_forest (g:=g61) (i:=0) (hints:=1027) (before_sound K59 V59) g61G g61T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K61 := extendKnown K59 7 [(61,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V61 : Known true K61 := extend_ok (m:=61) V59 low61 (by decide +kernel)

def g62Y : Array (Bits × Bits) := #[(0x0, 0x0),
    ((repeatRows 17 0x12b5f), (repeatRows 17 0x15c)),
    ((repeatRows 17 0x5420), (repeatRows 17 0x10060)),
    ((repeatRows 17 0x9888), (repeatRows 17 0xe180)),
    ((repeatRows 17 0x7f2d), (repeatRows 17 0xfe00)),
    ((repeatRows 17 0x180d2), (repeatRows 17 0x10000)),
    (0x0, 0x0)]
def g62C : List ColumnInfo := []
def g62D4 (j : Nat) : Nat := if j = 0 then 0x1f else 0
def g62L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g62D4)
  | _ => emptyPacking
def g62I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g62 : Forest := ⟨62, 4, fun i => (g62Y[i]?).getD (0,0), g62C, [[], [50, 84]], g62L, g62I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62P4n0 : block g62 4 0 1 = true := by decide +kernel
theorem g62B4 : block g62 4 0 1 = true := g62P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62T : checkedTables g62 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g62 0 0 0 = true)
  · exact (rfl : block g62 1 0 0 = true)
  · exact (rfl : block g62 2 0 0 = true)
  · exact (rfl : block g62 3 0 0 = true)
  · exact g62B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62G : graphValid g62 (boundsBefore K61) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low62 : Lower true (varsX 62) (graphGoal 62) 5 := lower_forest (g:=g62) (i:=0) (hints:=1135680) (before_sound K61 V61) g62G g62T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K62 := extendKnown K61 5 [(62,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V62 : Known true K62 := extend_ok (m:=62) V61 low62 (by decide +kernel)

def g87Y : Array (Bits × Bits) := #[((repeatRows 17 0x6137), (repeatRows 17 0x36)),
    ((repeatRows 17 0x14228), (repeatRows 17 0x1e038)),
    ((repeatRows 17 0x184c0), (repeatRows 17 0xc0)),
    (0x0, 0x0),
    ((repeatRows 17 0x1f4b), (repeatRows 17 0xf00)),
    (0x0, 0x0),
    ((repeatRows 17 0x1f8b4), (repeatRows 17 0x1f000))]
def g87C : List ColumnInfo := [(1,0,86,0,5)]
def g87D5 (j : Nat) : Nat := if j = 0 then 0x5f else 0
def g87L : Nat → Packing
  | 5 => (1, 0, 1, 0, 0, 1, 0, g87D5)
  | _ => emptyPacking
def g87I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g87 : Forest := ⟨87, 5, fun i => (g87Y[i]?).getD (0,0), g87C, [[], [32]], g87L, g87I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g87P5n0 : block g87 5 0 1 = true := by decide +kernel
theorem g87B5 : block g87 5 0 1 = true := g87P5n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g87T : checkedTables g87 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g87 0 0 0 = true)
  · exact (rfl : block g87 1 0 0 = true)
  · exact (rfl : block g87 2 0 0 = true)
  · exact (rfl : block g87 3 0 0 = true)
  · exact (rfl : block g87 4 0 0 = true)
  · exact g87B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g87G : graphValid g87 (boundsBefore K62) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low87 : Lower true (varsX 87) (graphGoal 87) 6 := lower_forest (g:=g87) (i:=0) (hints:=1092) (before_sound K62 V62) g87G g87T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K87 := extendKnown K62 6 [(87,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V87 : Known true K87 := extend_ok (m:=87) V62 low87 (by decide +kernel)

def g91Y : Array (Bits × Bits) := #[((repeatRows 23 0x489bef), (repeatRows 23 0x1ee)),
    ((repeatRows 23 0x57150), (repeatRows 23 0x4079f0)),
    (0x0, 0x0),
    ((repeatRows 23 0x145e63), (repeatRows 23 0x47e00)),
    ((repeatRows 23 0x27e014), (repeatRows 23 0x78000)),
    (0x0, 0x0),
    ((repeatRows 23 0x7a0588), (repeatRows 23 0x780000))]
def g91C : List ColumnInfo := [(0,2,73,16,5), (1,0,90,0,4), (2,0,89,0,5), (8,0,83,0,5), (16,0,73,0,4), (16,2,73,0,4), (64,0,27,0,4)]
def g91D4 (j : Nat) : Nat := if j = 0 then 0x5b89504 else 0
def g91D5 (j : Nat) : Nat := if j = 0 then 0x190808fd04 else 0
def g91D6 (j : Nat) : Nat := if j = 0 then 0x1ac6881df else 0
def g91L : Nat → Packing
  | 4 => (1, 2, 3, 0, 0, 1, 0, g91D4)
  | 5 => (1, 1, 3, 0, 0, 1, 0, g91D5)
  | 6 => (1, 0, 3, 0, 0, 1, 0, g91D6)
  | _ => emptyPacking
def g91I : Nat → Nat → Option (Nat × Nat)
  | 5, tag => lookupShort 1 2 1 3 1 0 (fun j => if j=0 then 0x4 else 0) tag
  | 6, tag => lookupShort 1 2 1 3 1 0 (fun j => if j=0 then 0xc else 0) tag
  | _, _ => none
def g91 : Forest := ⟨91, 6, fun i => (g91Y[i]?).getD (0,0), g91C, [[], [96]], g91L, g91I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91P4n0 : block g91 4 0 1 = true := by decide +kernel
theorem g91B4 : block g91 4 0 1 = true := g91P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91P5n0 : block g91 5 0 1 = true := by decide +kernel
theorem g91B5 : block g91 5 0 1 = true := g91P5n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91P6n0 : block g91 6 0 1 = true := by decide +kernel
theorem g91B6 : block g91 6 0 1 = true := g91P6n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91T : checkedTables g91 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g91 0 0 0 = true)
  · exact (rfl : block g91 1 0 0 = true)
  · exact (rfl : block g91 2 0 0 = true)
  · exact (rfl : block g91 3 0 0 = true)
  · exact g91B4
  · exact g91B5
  · exact g91B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91G : graphValid g91 (boundsBefore K87) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low91 : Lower true (varsX 91) (graphGoal 91) 7 := lower_forest (g:=g91) (i:=0) (hints:=67) (before_sound K87 V87) g91G g91T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K91 := extendKnown K87 7 [(91,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V91 : Known true K91 := extend_ok (m:=91) V87 low91 (by decide +kernel)

def g93Y : Array (Bits × Bits) := #[((repeatRows 22 0x44dcf), (repeatRows 22 0xce)),
    (0x0, 0x0),
    ((repeatRows 22 0xab8b0), (repeatRows 22 0x3cf0)),
    ((repeatRows 22 0x122fc3), (repeatRows 22 0x23f00)),
    ((repeatRows 22 0x23f014), (repeatRows 22 0x3c000)),
    (0x0, 0x0),
    ((repeatRows 22 0x3d0228), (repeatRows 22 0x3c0000))]
def g93C : List ColumnInfo := [(1,0,92,0,5), (4,0,89,0,5), (8,0,85,0,5), (16,0,77,0,5)]
def g93D6 (j : Nat) : Nat := if j = 0 then 0xe411f else 0
def g93L : Nat → Packing
  | 6 => (1, 0, 2, 0, 0, 1, 0, g93D6)
  | _ => emptyPacking
def g93I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g93 : Forest := ⟨93, 6, fun i => (g93Y[i]?).getD (0,0), g93C, [[], [64, 50]], g93L, g93I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93P6n0 : block g93 6 0 1 = true := by decide +kernel
theorem g93B6 : block g93 6 0 1 = true := g93P6n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93T : checkedTables g93 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g93 0 0 0 = true)
  · exact (rfl : block g93 1 0 0 = true)
  · exact (rfl : block g93 2 0 0 = true)
  · exact (rfl : block g93 3 0 0 = true)
  · exact (rfl : block g93 4 0 0 = true)
  · exact (rfl : block g93 5 0 0 = true)
  · exact g93B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93G : graphValid g93 (boundsBefore K91) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low93 : Lower true (varsX 93) (graphGoal 93) 7 := lower_forest (g:=g93) (i:=0) (hints:=1027) (before_sound K91 V91) g93G g93T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K93 := extendKnown K91 7 [(93,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V93 : Known true K93 := extend_ok (m:=93) V91 low93 (by decide +kernel)

def g94Y : Array (Bits × Bits) := #[(0x0, 0x0),
    ((repeatRows 21 0x1853a3), (repeatRows 21 0x1c01b2)),
    ((repeatRows 21 0xca43c), (repeatRows 21 0x3c)),
    ((repeatRows 21 0x11c140), (repeatRows 21 0xf1c0)),
    ((repeatRows 21 0x2ff87), (repeatRows 21 0xfe00)),
    (0x0, 0x0),
    ((repeatRows 21 0x1f0878), (repeatRows 21 0x1f0000))]
def g94C : List ColumnInfo := [(2,0,92,0,5)]
def g94D5 (j : Nat) : Nat := if j = 0 then 0x5f else 0
def g94L : Nat → Packing
  | 5 => (1, 0, 1, 0, 0, 1, 0, g94D5)
  | _ => emptyPacking
def g94I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g94 : Forest := ⟨94, 5, fun i => (g94Y[i]?).getD (0,0), g94C, [[], [49, 100]], g94L, g94I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94P5n0 : block g94 5 0 1 = true := by decide +kernel
theorem g94B5 : block g94 5 0 1 = true := g94P5n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94T : checkedTables g94 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g94 0 0 0 = true)
  · exact (rfl : block g94 1 0 0 = true)
  · exact (rfl : block g94 2 0 0 = true)
  · exact (rfl : block g94 3 0 0 = true)
  · exact (rfl : block g94 4 0 0 = true)
  · exact g94B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94G : graphValid g94 (boundsBefore K93) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low94 : Lower true (varsX 94) (graphGoal 94) 6 := lower_forest (g:=g94) (i:=0) (hints:=33645632) (before_sound K93 V93) g94G g94T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K94 := extendKnown K93 6 [(94,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V94 : Known true K94 := extend_ok (m:=94) V93 low94 (by decide +kernel)

def g103Y : Array (Bits × Bits) := #[((repeatRows 17 0x12b5f), (repeatRows 17 0x15c)),
    ((repeatRows 17 0x5420), (repeatRows 17 0x10060)),
    ((repeatRows 17 0x9888), (repeatRows 17 0xe180)),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 17 0x7f2d), (repeatRows 17 0xfe00)),
    ((repeatRows 17 0x180d2), (repeatRows 17 0x10000))]
def g103C : List ColumnInfo := []
def g103D4 (j : Nat) : Nat := if j = 0 then 0x1f else 0
def g103L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g103D4)
  | _ => emptyPacking
def g103I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g103 : Forest := ⟨103, 4, fun i => (g103Y[i]?).getD (0,0), g103C, [[], [33, 101]], g103L, g103I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103P4n0 : block g103 4 0 1 = true := by decide +kernel
theorem g103B4 : block g103 4 0 1 = true := g103P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103T : checkedTables g103 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g103 0 0 0 = true)
  · exact (rfl : block g103 1 0 0 = true)
  · exact (rfl : block g103 2 0 0 = true)
  · exact (rfl : block g103 3 0 0 = true)
  · exact g103B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103G : graphValid g103 (boundsBefore K94) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low103 : Lower true (varsX 103) (graphGoal 103) 5 := lower_forest (g:=g103) (i:=0) (hints:=1621) (before_sound K94 V94) g103G g103T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K103 := extendKnown K94 5 [(103,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V103 : Known true K103 := extend_ok (m:=103) V94 low103 (by decide +kernel)

def g107Y : Array (Bits × Bits) := #[((repeatRows 22 0x273ef), (repeatRows 22 0x1ee)),
    ((repeatRows 22 0x38a150), (repeatRows 22 0x1831f0)),
    (0x0, 0x0),
    ((repeatRows 22 0x53e63), (repeatRows 22 0x3e00)),
    (0x0, 0x0),
    ((repeatRows 22 0x39c414), (repeatRows 22 0x21c000)),
    ((repeatRows 22 0x360988), (repeatRows 22 0x3e0000))]
def g107C : List ColumnInfo := [(0,2,73,32,5), (1,0,106,0,4), (2,0,105,0,5), (8,0,99,0,4), (32,0,73,0,4), (32,2,73,0,4), (64,0,43,0,5)]
def g107D4 (j : Nat) : Nat := if j = 0 then 0x4fd5102 else 0
def g107D5 (j : Nat) : Nat := if j = 0 then 0x310808fd02 else 0
def g107D6 (j : Nat) : Nat := if j = 0 then 0x1ac6881df else 0
def g107L : Nat → Packing
  | 4 => (1, 2, 3, 0, 0, 1, 0, g107D4)
  | 5 => (1, 1, 3, 0, 0, 1, 0, g107D5)
  | 6 => (1, 0, 3, 0, 0, 1, 0, g107D6)
  | _ => emptyPacking
def g107I : Nat → Nat → Option (Nat × Nat)
  | 5, tag => lookupShort 1 2 1 3 1 0 (fun j => if j=0 then 0xc else 0) tag
  | 6, tag => lookupShort 1 2 1 3 1 0 (fun j => if j=0 then 0x40 else 0) tag
  | _, _ => none
def g107 : Forest := ⟨107, 6, fun i => (g107Y[i]?).getD (0,0), g107C, [[], [48]], g107L, g107I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107P4n0 : block g107 4 0 1 = true := by decide +kernel
theorem g107B4 : block g107 4 0 1 = true := g107P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107P5n0 : block g107 5 0 1 = true := by decide +kernel
theorem g107B5 : block g107 5 0 1 = true := g107P5n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107P6n0 : block g107 6 0 1 = true := by decide +kernel
theorem g107B6 : block g107 6 0 1 = true := g107P6n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107T : checkedTables g107 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g107 0 0 0 = true)
  · exact (rfl : block g107 1 0 0 = true)
  · exact (rfl : block g107 2 0 0 = true)
  · exact (rfl : block g107 3 0 0 = true)
  · exact g107B4
  · exact g107B5
  · exact g107B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107G : graphValid g107 (boundsBefore K103) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low107 : Lower true (varsX 107) (graphGoal 107) 7 := lower_forest (g:=g107) (i:=0) (hints:=83) (before_sound K103 V103) g107G g107T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K107 := extendKnown K103 7 [(107,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V107 : Known true K107 := extend_ok (m:=107) V103 low107 (by decide +kernel)

def g109Y : Array (Bits × Bits) := #[((repeatRows 22 0x473ef), (repeatRows 22 0x1ee)),
    (0x0, 0x0),
    ((repeatRows 22 0x2b2150), (repeatRows 22 0x331f0)),
    ((repeatRows 22 0x10be63), (repeatRows 22 0x3e00)),
    (0x0, 0x0),
    ((repeatRows 22 0x22c584), (repeatRows 22 0x23c000)),
    ((repeatRows 22 0x3f0818), (repeatRows 22 0x3c0000))]
def g109C : List ColumnInfo := [(0,4,41,64,5), (1,0,108,0,4), (4,0,105,0,5), (8,0,101,0,4), (32,0,77,0,5), (64,0,41,0,4), (64,4,41,0,4)]
def g109D4 (j : Nat) : Nat := if j = 0 then 0x57d4d02 else 0
def g109D5 (j : Nat) : Nat := if j = 0 then 0x210808fd02 else 0
def g109D6 (j : Nat) : Nat := if j = 0 then 0x1ac6881df else 0
def g109L : Nat → Packing
  | 4 => (1, 2, 3, 0, 0, 1, 0, g109D4)
  | 5 => (1, 1, 3, 0, 0, 1, 0, g109D5)
  | 6 => (1, 0, 3, 0, 0, 1, 0, g109D6)
  | _ => emptyPacking
def g109I : Nat → Nat → Option (Nat × Nat)
  | 5, tag => lookupShort 1 2 1 3 1 0 (fun j => if j=0 then 0x40 else 0) tag
  | 6, tag => lookupShort 1 2 1 3 1 0 (fun j => if j=0 then 0x0 else 0) tag
  | _, _ => none
def g109 : Forest := ⟨109, 6, fun i => (g109Y[i]?).getD (0,0), g109C, [[], [48]], g109L, g109I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P4n0 : block g109 4 0 1 = true := by decide +kernel
theorem g109B4 : block g109 4 0 1 = true := g109P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P5n0 : block g109 5 0 1 = true := by decide +kernel
theorem g109B5 : block g109 5 0 1 = true := g109P5n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P6n0 : block g109 6 0 1 = true := by decide +kernel
theorem g109B6 : block g109 6 0 1 = true := g109P6n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109T : checkedTables g109 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g109 0 0 0 = true)
  · exact (rfl : block g109 1 0 0 = true)
  · exact (rfl : block g109 2 0 0 = true)
  · exact (rfl : block g109 3 0 0 = true)
  · exact g109B4
  · exact g109B5
  · exact g109B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109G : graphValid g109 (boundsBefore K107) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low109 : Lower true (varsX 109) (graphGoal 109) 7 := lower_forest (g:=g109) (i:=0) (hints:=1539) (before_sound K107 V107) g109G g109T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K109 := extendKnown K107 7 [(109,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V109 : Known true K109 := extend_ok (m:=109) V107 low109 (by decide +kernel)

def g110Y : Array (Bits × Bits) := #[(0x0, 0x0),
    ((repeatRows 16 0x1317), (repeatRows 16 0x8036)),
    ((repeatRows 16 0x4a2c), (repeatRows 16 0x7038)),
    ((repeatRows 16 0xacc0), (repeatRows 16 0xc0)),
    (0x0, 0x0),
    ((repeatRows 16 0x3f57), (repeatRows 16 0x7f00)),
    ((repeatRows 16 0xc0a8), (repeatRows 16 0x8000))]
def g110C : List ColumnInfo := []
def g110D4 (j : Nat) : Nat := if j = 0 then 0x1f else 0
def g110L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g110D4)
  | _ => emptyPacking
def g110I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g110 : Forest := ⟨110, 4, fun i => (g110Y[i]?).getD (0,0), g110C, [[], [33, 101]], g110L, g110I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g110P4n0 : block g110 4 0 1 = true := by decide +kernel
theorem g110B4 : block g110 4 0 1 = true := g110P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g110T : checkedTables g110 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g110 0 0 0 = true)
  · exact (rfl : block g110 1 0 0 = true)
  · exact (rfl : block g110 2 0 0 = true)
  · exact (rfl : block g110 3 0 0 = true)
  · exact g110B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g110G : graphValid g110 (boundsBefore K109) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low110 : Lower true (varsX 110) (graphGoal 110) 5 := lower_forest (g:=g110) (i:=0) (hints:=34625104) (before_sound K109 V109) g110G g110T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K110 := extendKnown K109 5 [(110,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V110 : Known true K110 := extend_ok (m:=110) V109 low110 (by decide +kernel)

def g115Y : Array (Bits × Bits) := #[((repeatRows 21 0x189cf), (repeatRows 21 0xce)),
    ((repeatRows 21 0xb12b0), (repeatRows 21 0x380f0)),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 21 0x146713), (repeatRows 21 0x6700)),
    ((repeatRows 21 0x1a5824), (repeatRows 21 0x1c7800)),
    ((repeatRows 21 0x1fe4c8), (repeatRows 21 0x1f8000))]
def g115C : List ColumnInfo := [(2,0,113,0,5)]
def g115D5 (j : Nat) : Nat := if j = 0 then 0x5f else 0
def g115L : Nat → Packing
  | 5 => (1, 0, 1, 0, 0, 1, 0, g115D5)
  | _ => emptyPacking
def g115I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g115 : Forest := ⟨115, 5, fun i => (g115Y[i]?).getD (0,0), g115C, [[], [64, 81]], g115L, g115I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115P5n0 : block g115 5 0 1 = true := by decide +kernel
theorem g115B5 : block g115 5 0 1 = true := g115P5n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115T : checkedTables g115 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g115 0 0 0 = true)
  · exact (rfl : block g115 1 0 0 = true)
  · exact (rfl : block g115 2 0 0 = true)
  · exact (rfl : block g115 3 0 0 = true)
  · exact (rfl : block g115 4 0 0 = true)
  · exact g115B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115G : graphValid g115 (boundsBefore K110) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low115 : Lower true (varsX 115) (graphGoal 115) 6 := lower_forest (g:=g115) (i:=0) (hints:=68) (before_sound K110 V110) g115G g115T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K115 := extendKnown K110 6 [(115,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V115 : Known true K115 := extend_ok (m:=115) V110 low115 (by decide +kernel)

def g117Y : Array (Bits × Bits) := #[((repeatRows 23 0x831cf), (repeatRows 23 0xce)),
    (0x0, 0x0),
    ((repeatRows 23 0x13eab0), (repeatRows 23 0x1f8f0)),
    (0x0, 0x0),
    ((repeatRows 23 0x664f13), (repeatRows 23 0x60700)),
    ((repeatRows 23 0x370c4), (repeatRows 23 0x47f800)),
    ((repeatRows 23 0x7d8428), (repeatRows 23 0x780000))]
def g117C : List ColumnInfo := [(0,32,84,1,5), (1,0,84,0,4), (1,32,84,0,4), (4,0,113,0,5), (16,0,101,0,4), (32,0,85,0,5), (64,0,53,0,4)]
def g117D4 (j : Nat) : Nat := if j = 0 then 0x5d85524 else 0
def g117D5 (j : Nat) : Nat := if j = 0 then 0x2a1808fd24 else 0
def g117D6 (j : Nat) : Nat := if j = 0 then 0x1ac6881df else 0
def g117L : Nat → Packing
  | 4 => (1, 2, 3, 0, 0, 1, 0, g117D4)
  | 5 => (1, 1, 3, 0, 0, 1, 0, g117D5)
  | 6 => (1, 0, 3, 0, 0, 1, 0, g117D6)
  | _ => emptyPacking
def g117I : Nat → Nat → Option (Nat × Nat)
  | 5, tag => lookupShort 1 2 1 3 1 0 (fun j => if j=0 then 0x4 else 0) tag
  | 6, tag => lookupShort 1 2 1 3 1 0 (fun j => if j=0 then 0x60 else 0) tag
  | _, _ => none
def g117 : Forest := ⟨117, 6, fun i => (g117Y[i]?).getD (0,0), g117C, [[], [100]], g117L, g117I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g117P4n0 : block g117 4 0 1 = true := by decide +kernel
theorem g117B4 : block g117 4 0 1 = true := g117P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g117P5n0 : block g117 5 0 1 = true := by decide +kernel
theorem g117B5 : block g117 5 0 1 = true := g117P5n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g117P6n0 : block g117 6 0 1 = true := by decide +kernel
theorem g117B6 : block g117 6 0 1 = true := g117P6n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g117T : checkedTables g117 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g117 0 0 0 = true)
  · exact (rfl : block g117 1 0 0 = true)
  · exact (rfl : block g117 2 0 0 = true)
  · exact (rfl : block g117 3 0 0 = true)
  · exact g117B4
  · exact g117B5
  · exact g117B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g117G : graphValid g117 (boundsBefore K115) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low117 : Lower true (varsX 117) (graphGoal 117) 7 := lower_forest (g:=g117) (i:=0) (hints:=1028) (before_sound K115 V115) g117G g117T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K117 := extendKnown K115 7 [(117,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V117 : Known true K117 := extend_ok (m:=117) V115 low117 (by decide +kernel)

def g118Y : Array (Bits × Bits) := #[(0x0, 0x0),
    ((repeatRows 25 0x1c18dcd), (repeatRows 25 0xc007cc)),
    ((repeatRows 25 0x5f5732), (repeatRows 25 0xfc7f0)),
    (0x0, 0x0),
    ((repeatRows 25 0x327857), (repeatRows 25 0x103800)),
    ((repeatRows 25 0x19b8188), (repeatRows 25 0x11fc000)),
    ((repeatRows 25 0x1ec2620), (repeatRows 25 0x1e00000))]
def g118C : List ColumnInfo := [(0,32,84,2,5), (2,0,84,0,4), (2,32,84,0,4), (4,0,114,0,4), (32,0,86,0,5), (64,0,54,0,4)]
def g118D4 (j : Nat) : Nat := if j = 0 then 0x4fd5112 else 0
def g118D5 (j : Nat) : Nat := if j = 0 then 0x60a004a0e140fd14fe12fd12 else 0
def g118D6 (j : Nat) : Nat := if j = 0 then 0x2c68819f else 0
def g118L : Nat → Packing
  | 4 => (1, 2, 3, 0, 0, 1, 0, g118D4)
  | 5 => (3, 1, 3, 0, 0, 5, 0, g118D5)
  | 6 => (1, 0, 3, 0, 0, 1, 0, g118D6)
  | _ => emptyPacking
def g118I : Nat → Nat → Option (Nat × Nat)
  | 5, tag => lookupShort 1 2 1 3 1 0 (fun j => if j=0 then 0x8 else 0) tag
  | 6, tag => lookupShort 3 8 1 5 2 1 (fun j => if j=0 then 0x4540e21a000 else 0) tag
  | _, _ => none
def g118 : Forest := ⟨118, 6, fun i => (g118Y[i]?).getD (0,0), g118C, [[], [98]], g118L, g118I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118P4n0 : block g118 4 0 1 = true := by decide +kernel
theorem g118B4 : block g118 4 0 1 = true := g118P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118P5n0 : block g118 5 0 3 = true := by decide +kernel
theorem g118B5 : block g118 5 0 3 = true := g118P5n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118P6n0 : block g118 6 0 1 = true := by decide +kernel
theorem g118B6 : block g118 6 0 1 = true := g118P6n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118T : checkedTables g118 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g118 0 0 0 = true)
  · exact (rfl : block g118 1 0 0 = true)
  · exact (rfl : block g118 2 0 0 = true)
  · exact (rfl : block g118 3 0 0 = true)
  · exact g118B4
  · exact g118B5
  · exact g118B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118G : graphValid g118 (boundsBefore K117) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low118 : Lower true (varsX 118) (graphGoal 118) 7 := lower_forest (g:=g118) (i:=0) (hints:=34669632) (before_sound K117 V117) g118G g118T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K118 := extendKnown K117 7 [(118,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V118 : Known true K118 := extend_ok (m:=118) V117 low118 (by decide +kernel)

def g121Y : Array (Bits × Bits) := #[((repeatRows 22 0x4113f), (repeatRows 22 0x1e)),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 22 0x8ece3), (repeatRows 22 0xce0)),
    ((repeatRows 22 0x338b04), (repeatRows 22 0x3cf00)),
    ((repeatRows 22 0x22fc48), (repeatRows 22 0x23f000)),
    ((repeatRows 22 0x3f0290), (repeatRows 22 0x3c0000))]
def g121C : List ColumnInfo := [(8,0,113,0,5), (16,0,105,0,5), (32,0,89,0,5), (64,0,57,0,5)]
def g121D6 (j : Nat) : Nat := if j = 0 then 0xe411f else 0
def g121L : Nat → Packing
  | 6 => (1, 0, 2, 0, 0, 1, 0, g121D6)
  | _ => emptyPacking
def g121I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g121 : Forest := ⟨121, 6, fun i => (g121Y[i]?).getD (0,0), g121C, [[], [99, 84]], g121L, g121I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g121P6n0 : block g121 6 0 1 = true := by decide +kernel
theorem g121B6 : block g121 6 0 1 = true := g121P6n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g121T : checkedTables g121 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g121 0 0 0 = true)
  · exact (rfl : block g121 1 0 0 = true)
  · exact (rfl : block g121 2 0 0 = true)
  · exact (rfl : block g121 3 0 0 = true)
  · exact (rfl : block g121 4 0 0 = true)
  · exact (rfl : block g121 5 0 0 = true)
  · exact g121B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g121G : graphValid g121 (boundsBefore K118) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low121 : Lower true (varsX 121) (graphGoal 121) 7 := lower_forest (g:=g121) (i:=0) (hints:=3) (before_sound K118 V118) g121G g121T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K121 := extendKnown K118 7 [(121,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V121 : Known true K121 := extend_ok (m:=121) V118 low121 (by decide +kernel)

def g122Y : Array (Bits × Bits) := #[(0x0, 0x0),
    ((repeatRows 26 0x1c29b67), (repeatRows 26 0xc001e6)),
    (0x0, 0x0),
    ((repeatRows 26 0x4571d8), (repeatRows 26 0x79f8)),
    ((repeatRows 26 0x23c5e63), (repeatRows 26 0x1e7e00)),
    ((repeatRows 26 0x397e00c), (repeatRows 26 0x31f8000)),
    ((repeatRows 26 0x3f80590), (repeatRows 26 0x3e00000))]
def g122C : List ColumnInfo := [(2,0,120,0,4), (8,0,114,0,4), (16,0,106,0,4), (32,0,90,0,4), (64,0,58,0,4)]
def g122D4 (j : Nat) : Nat := if j = 0 then 0x57d4d01 else 0
def g122D5 (j : Nat) : Nat := if j = 0 then 0xc1a0fd02fd01 else 0
def g122D6 (j : Nat) : Nat := if j = 0 then 0x468815f else 0
def g122L : Nat → Packing
  | 4 => (1, 2, 3, 0, 0, 1, 0, g122D4)
  | 5 => (2, 1, 3, 0, 0, 4, 0, g122D5)
  | 6 => (1, 0, 3, 0, 0, 1, 0, g122D6)
  | _ => emptyPacking
def g122I : Nat → Nat → Option (Nat × Nat)
  | 5, tag => lookupShort 1 2 1 3 1 0 (fun j => if j=0 then 0x8 else 0) tag
  | 6, tag => lookupShort 5 15 2 6 1 3 (fun j => if j=0 then 0x7fa4b317c800001038000b704 else 0) tag
  | _, _ => none
def g122 : Forest := ⟨122, 6, fun i => (g122Y[i]?).getD (0,0), g122C, [[], [99, 84], [49, 100], [49, 67, 84, 101], [65, 101], [65, 83, 100, 101], [81, 67], [81, 99, 84, 101], [97, 99, 100, 101], [97, 83]], g122L, g122I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g122P4n0 : block g122 4 0 1 = true := by decide +kernel
theorem g122B4 : block g122 4 0 1 = true := g122P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g122P5n0 : block g122 5 0 2 = true := by decide +kernel
theorem g122B5 : block g122 5 0 2 = true := g122P5n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g122P6n0 : block g122 6 0 1 = true := by decide +kernel
theorem g122B6 : block g122 6 0 1 = true := g122P6n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g122T : checkedTables g122 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g122 0 0 0 = true)
  · exact (rfl : block g122 1 0 0 = true)
  · exact (rfl : block g122 2 0 0 = true)
  · exact (rfl : block g122 3 0 0 = true)
  · exact g122B4
  · exact g122B5
  · exact g122B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g122G : graphValid g122 (boundsBefore K121) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low122 : Lower true (varsX 122) (graphGoal 122) 7 := lower_forest (g:=g122) (i:=0) (hints:=51466304) (before_sound K121 V121) g122G g122T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K122 := extendKnown K121 7 [(122,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V122 : Known true K122 := extend_ok (m:=122) V121 low122 (by decide +kernel)

def g124Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 27 0x17c6acf), (repeatRows 27 0x3c07cc)),
    ((repeatRows 27 0x287c7b0), (repeatRows 27 0x1e7f0)),
    ((repeatRows 27 0x4c978c5), (repeatRows 27 0xc1f800)),
    ((repeatRows 27 0xef8310), (repeatRows 27 0xfe0000)),
    ((repeatRows 27 0x730142a), (repeatRows 27 0x7000000))]
def g124C : List ColumnInfo := [(0,32,84,8,5), (4,0,120,0,4), (8,0,84,0,4), (8,32,84,0,4), (16,0,108,0,4), (32,0,92,0,5)]
def g124D4 (j : Nat) : Nat := if j = 0 then 0x5b89504 else 0
def g124D5 (j : Nat) : Nat := if j = 0 then 0xa0120220d140fe04fd04fd02 else 0
def g124D6 (j : Nat) : Nat := if j = 0 then 0x2c68819f else 0
def g124L : Nat → Packing
  | 4 => (1, 2, 3, 0, 0, 1, 0, g124D4)
  | 5 => (3, 1, 3, 0, 0, 5, 0, g124D5)
  | 6 => (1, 0, 3, 0, 0, 1, 0, g124D6)
  | _ => emptyPacking
def g124I : Nat → Nat → Option (Nat × Nat)
  | 5, tag => lookupShort 1 2 1 3 1 0 (fun j => if j=0 then 0x40 else 0) tag
  | 6, tag => lookupShort 3 8 1 5 2 1 (fun j => if j=0 then 0x2ac08941000 else 0) tag
  | _, _ => none
def g124 : Forest := ⟨124, 6, fun i => (g124Y[i]?).getD (0,0), g124C, [[], [66]], g124L, g124I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g124P4n0 : block g124 4 0 1 = true := by decide +kernel
theorem g124B4 : block g124 4 0 1 = true := g124P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g124P5n0 : block g124 5 0 3 = true := by decide +kernel
theorem g124B5 : block g124 5 0 3 = true := g124P5n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g124P6n0 : block g124 6 0 1 = true := by decide +kernel
theorem g124B6 : block g124 6 0 1 = true := g124P6n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g124T : checkedTables g124 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g124 0 0 0 = true)
  · exact (rfl : block g124 1 0 0 = true)
  · exact (rfl : block g124 2 0 0 = true)
  · exact (rfl : block g124 3 0 0 = true)
  · exact g124B4
  · exact g124B5
  · exact g124B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g124G : graphValid g124 (boundsBefore K122) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low124 : Lower true (varsX 124) (graphGoal 124) 7 := lower_forest (g:=g124) (i:=0) (hints:=36852736) (before_sound K122 V122) g124G g124T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K124 := extendKnown K122 7 [(124,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V124 : Known true K124 := extend_ok (m:=124) V122 low124 (by decide +kernel)

def g63Y : Array (Bits × Bits) := #[((repeatRows 35 0x1039becf), (repeatRows 35 0x1ece)),
    ((repeatRows 35 0xc14700b0), (repeatRows 35 0x780f0)),
    ((repeatRows 35 0x382901500), (repeatRows 35 0x1c0181f00)),
    ((repeatRows 35 0x42f1de6c3), (repeatRows 35 0xf1fe000)),
    ((repeatRows 35 0x70be60114), (repeatRows 35 0x60fe00000)),
    ((repeatRows 35 0x7fc005828), (repeatRows 35 0x7f0000000)),
    (0x0, 0x0)]
def g63C : List ColumnInfo := [(2,0,61,0,7)]
def g63D7 (j : Nat) : Nat := if j = 0 then 0xbf else 0
def g63L : Nat → Packing
  | 7 => (1, 0, 1, 0, 0, 1, 0, g63D7)
  | _ => emptyPacking
def g63I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g63 : Forest := ⟨63, 7, fun i => (g63Y[i]?).getD (0,0), g63C, [[]], g63L, g63I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7n0 : block g63 7 0 1 = true := by decide +kernel
theorem g63B7 : block g63 7 0 1 = true := g63P7n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63T : checkedTables g63 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g63 0 0 0 = true)
  · exact (rfl : block g63 1 0 0 = true)
  · exact (rfl : block g63 2 0 0 = true)
  · exact (rfl : block g63 3 0 0 = true)
  · exact (rfl : block g63 4 0 0 = true)
  · exact (rfl : block g63 5 0 0 = true)
  · exact (rfl : block g63 6 0 0 = true)
  · exact g63B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63G : graphValid g63 (boundsBefore K124) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (varsX 63) (graphGoal 63) 8 := lower_forest (g:=g63) (i:=0) (hints:=1091) (before_sound K124 V124) g63G g63T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K63 := extendKnown K124 8 [(63,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V63 : Known true K63 := extend_ok (m:=63) V124 low63 (by decide +kernel)

def g95Y : Array (Bits × Bits) := #[((repeatRows 68 0xc108b830c8b8ece3), (repeatRows 68 0x4f8fce0)),
    ((repeatRows 68 0xeb011100b9102bb00), (repeatRows 68 0xfe000780fc700ff00)),
    ((repeatRows 68 0x3022265e016f70204), (repeatRows 68 0x7ff007ff0000)),
    ((repeatRows 68 0x404f83ebee8180c29), (repeatRows 68 0xf87ffff8000000)),
    ((repeatRows 68 0x838bf80c311233150), (repeatRows 68 0xff800000000000)),
    (0x0, 0x0),
    ((repeatRows 68 0xfdfc4470c26c4c29e), (repeatRows 68 0xfff00000000000000))]
def g95C : List ColumnInfo := [(0,2,77,16,6), (1,0,94,0,6), (2,0,93,0,7), (3,0,92,0,5), (4,0,91,0,7), (4,2,73,16,5), (5,0,90,0,4), (6,0,89,0,5), (8,0,87,0,6), (9,0,86,0,5), (10,0,85,0,5), (16,0,77,0,5), (16,2,77,0,5), (20,0,73,0,4), (64,0,31,0,5), (66,0,29,0,4), (68,0,27,0,4)]
def g95D4 (j : Nat) : Nat := if j = 0 then 0x280400000000050081cb666c16aa4e90e59ad4e84d950c03855153481915b0d28195454d2c642065515348e7825da3585239e0967816148d5868dd058523960227596148e6285d560852721e1054d102f09454153440a399a17585102d61055d61440a78e1570851029e1855c21440b62dd53441102d89754d10440b58dd50545902 else 0
def g95D5 (j : Nat) : Nat := if j = 0 then 0x2810000000000000230101801600680100008068010000008b0400000000000280100201600580128040280400504a012806240c200181a804b0100a01680400504ad24200a01022c04b0a38a0440722088816807064412e6b82dab52ceb22c2af2aeaa2a2a7296a428aa127e9e26a992569223a8d22e8821283206801fa7b1e6781da751ce721c26f1ae6a19a6317e5c16a571565213a4b116441023d0e6380d2310be2c09a2507e1c04a0d0260026fb9ac122ced70899459dc4eb246b9d516064576a9a40c8acee27592059bae91b20bb55c6364176b1b22c82ed636455059dc4eb2a693e81d654d2ceba4ca9a59e4759534b9c4eb2a697681d654d2e6938ca9a5d90719534f1c4ea2a696781d454d38fb2a8a9a71c6551534e3a8b02a69675d2054d26f33a0a9a4dc6741534e3a8a82a693d5da358527ab3c0b0a5d63741614dcc4eb2c293989d658527b03acb0a6760559614cea0ab2c293ddd5608527abaac10a6f105582149bc6eb2a093b89d654139ca2a0a8269f654d104d3aca9a209e641534413cd03a68825e970915029dccea2a057a5c26540ae71baca815e66745502bd48e82a05f28dd0540bf08ba0a8176a4541502ed28a82a05f84550540bc6a2a68817c9054d102f940e9a205f84161440af2bac28815e57685102bc2e10a2057add50440af4baa08817a94541102f12688220579dd51640b7332a2c817e10545902 else 0
def g95D6 (j : Nat) : Nat := if j = 0 then 0x201000c09813107325e20c202001880808008201000c78b53901218000802002101000c40200188c4164c50431f2418212002060043e4220420b04003080808010608085a24018b04588448044480248890a01058848890a01860b119310a2d1200c5a24018844850082512140200040000a80010bc8080082d4e4048400c08004202020020c0210b4010c16232628232c4405008b0322028054480220a11201162b93a22228280812a0304c404658ad444c50461ab1120115c9d111141403ac56254060988090b15c9d01c3444505015a1334e63c918b7095f0bab65ec8d84ad353a9d51f9fb3c26e4ba93f1f634c4e88307e05be9772e41bab5a670c5984b035ecb89602904f896923232404780db9a330250c898e318222826000bf58e45bf58245bf8d945fb89945bb89945bf81945bf59235bf91935bd81915fd4d515df51605bf59205bf91905f78d905b78d905fd45905df91505df51505fd45505bfd9534bf59534ef51534f78d534f74d534f7d9534f799534f759534f719534e751534f781534f741534f781934f741934fd8d614fd4d614fd81614fd41614bd59614bd58214bfd9504bf59504ef51504fe41504e74d104fb91502fb51502fb99502fb59502f945502fa41502f34d102fb59102f985102fa41102f945902 else 0
def g95D7 (j : Nat) : Nat := if j = 0 then 0xe30b22412208100a38c2c890488204028e2c92241220a10402ce2c922412208124f38c2e9a240a100a38b24890488204028e2c922412208100a30b24892284738c2c92241220a104030c2c89228462e9a240a100738c2c922412208100bb09a06122047309a240c20402312b42889320a7218655908378ae19836003fc8bfd45ff1aff4d7ea2bfe05fe82f7cd3fa69dd34fb0a7f413da05f501 else 0
def g95D8 (j : Nat) : Nat := if j = 0 then 0x3128208233f else 0
def g95L : Nat → Packing
  | 4 => (17, 4, 5, 0, 0, 7, 0, g95D4)
  | 5 => (70, 3, 5, 0, 0, 10, 0, g95D5)
  | 6 => (55, 2, 5, 0, 0, 11, 0, g95D6)
  | 7 => (14, 1, 5, 0, 0, 10, 0, g95D7)
  | 8 => (1, 0, 5, 0, 0, 1, 0, g95D8)
  | _ => emptyPacking
def g95I : Nat → Nat → Option (Nat × Nat)
  | 5, tag => lookupShort 9 28 2 7 5 0 (fun j => if j=0 then 0xca00b64439800120600004e5600029001028000037a74c030040 else 0) tag
  | 6, tag => lookupShort 35 107 4 9 7 0 (fun j => if j=0 then 0x6e01c87a249e4288004d67d9f84ca2172bd76083b90002ed2a800050f442f0000000000000000000040401300000e322089b040198000b36d111e000018c0028c2e000051401140050001b2d20000000004eb1586cd29401855f8b6660dd4ce400000041062340027384920026c013d150004c0047ede2c1e20800202525012205170000403000003103 else 0) tag
  | 7, tag => lookupShort 28 83 5 8 6 0 (fun j => if j=0 then 0xd3aa6187909520e40feb59838829ed051c000400000000007300000082238db500b2cef0ca9218ee1bf11f00000000940000a20049d72c0041000036000000efa76600e80056dd00ded100c0004cda4b06e534009c028220588c008801000020000008c60 else 0) tag
  | 8, tag => lookupShort 7 22 4 6 4 0 (fun j => if j=0 then 0x2d6096a189bcc755c0005a400000d2040 else 0) tag
  | _, _ => none
def g95 : Forest := ⟨95, 8, fun i => (g95Y[i]?).getD (0,0), g95C, [[]], g95L, g95I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P4n0 : block g95 4 0 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P4n6 : block g95 4 6 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P4n12 : block g95 4 12 5 = true := by decide +kernel
theorem g95B4 : block g95 4 0 17 = true := (@block_merge g95 4 0 6 11 g95P4n0 (@block_merge g95 4 6 6 5 g95P4n6 g95P4n12))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P5n0 : block g95 5 0 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P5n6 : block g95 5 6 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P5n12 : block g95 5 12 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P5n18 : block g95 5 18 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P5n24 : block g95 5 24 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P5n30 : block g95 5 30 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P5n36 : block g95 5 36 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P5n42 : block g95 5 42 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P5n48 : block g95 5 48 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P5n54 : block g95 5 54 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P5n60 : block g95 5 60 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P5n66 : block g95 5 66 4 = true := by decide +kernel
theorem g95B5 : block g95 5 0 70 = true := (@block_merge g95 5 0 36 34 (@block_merge g95 5 0 18 18 (@block_merge g95 5 0 6 12 g95P5n0 (@block_merge g95 5 6 6 6 g95P5n6 g95P5n12)) (@block_merge g95 5 18 6 12 g95P5n18 (@block_merge g95 5 24 6 6 g95P5n24 g95P5n30))) (@block_merge g95 5 36 18 16 (@block_merge g95 5 36 6 12 g95P5n36 (@block_merge g95 5 42 6 6 g95P5n42 g95P5n48)) (@block_merge g95 5 54 6 10 g95P5n54 (@block_merge g95 5 60 6 4 g95P5n60 g95P5n66))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6n0 : block g95 6 0 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6n6 : block g95 6 6 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6n12 : block g95 6 12 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6n18 : block g95 6 18 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6n24 : block g95 6 24 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6n30 : block g95 6 30 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6n36 : block g95 6 36 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6n42 : block g95 6 42 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6n48 : block g95 6 48 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6n54 : block g95 6 54 1 = true := by decide +kernel
theorem g95B6 : block g95 6 0 55 = true := (@block_merge g95 6 0 30 25 (@block_merge g95 6 0 12 18 (@block_merge g95 6 0 6 6 g95P6n0 g95P6n6) (@block_merge g95 6 12 6 12 g95P6n12 (@block_merge g95 6 18 6 6 g95P6n18 g95P6n24))) (@block_merge g95 6 30 12 13 (@block_merge g95 6 30 6 6 g95P6n30 g95P6n36) (@block_merge g95 6 42 6 7 g95P6n42 (@block_merge g95 6 48 6 1 g95P6n48 g95P6n54))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P7n0 : block g95 7 0 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P7n6 : block g95 7 6 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P7n12 : block g95 7 12 2 = true := by decide +kernel
theorem g95B7 : block g95 7 0 14 = true := (@block_merge g95 7 0 6 8 g95P7n0 (@block_merge g95 7 6 6 2 g95P7n6 g95P7n12))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P8n0 : block g95 8 0 1 = true := by decide +kernel
theorem g95B8 : block g95 8 0 1 = true := g95P8n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95T : checkedTables g95 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g95 0 0 0 = true)
  · exact (rfl : block g95 1 0 0 = true)
  · exact (rfl : block g95 2 0 0 = true)
  · exact (rfl : block g95 3 0 0 = true)
  · exact g95B4
  · exact g95B5
  · exact g95B6
  · exact g95B7
  · exact g95B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95G : graphValid g95 (boundsBefore K63) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low95 : Lower true (varsX 95) (graphGoal 95) 9 := lower_forest (g:=g95) (i:=0) (hints:=1091) (before_sound K63 V63) g95G g95T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K95 := extendKnown K63 9 [(95,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V95 : Known true K95 := extend_ok (m:=95) V63 low95 (by decide +kernel)

def g111Y : Array (Bits × Bits) := #[((repeatRows 35 0x103e7def), (repeatRows 35 0x3dee)),
    ((repeatRows 35 0x383440150), (repeatRows 35 0x1800601f0)),
    ((repeatRows 35 0x4ae102a00), (repeatRows 35 0xf183e00)),
    ((repeatRows 35 0x409fcc63), (repeatRows 35 0x1fc000)),
    (0x0, 0x0),
    ((repeatRows 35 0x70be0b014), (repeatRows 35 0x60fe00000)),
    ((repeatRows 35 0x7fc010388), (repeatRows 35 0x7f0000000))]
def g111C : List ColumnInfo := [(2,0,109,0,7)]
def g111D7 (j : Nat) : Nat := if j = 0 then 0xbf else 0
def g111L : Nat → Packing
  | 7 => (1, 0, 1, 0, 0, 1, 0, g111D7)
  | _ => emptyPacking
def g111I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g111 : Forest := ⟨111, 7, fun i => (g111Y[i]?).getD (0,0), g111C, [[], [33, 101], [48], [48, 33, 101]], g111L, g111I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n0 : block g111 7 0 1 = true := by decide +kernel
theorem g111B7 : block g111 7 0 1 = true := g111P7n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111T : checkedTables g111 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0 = true)
  · exact (rfl : block g111 1 0 0 = true)
  · exact (rfl : block g111 2 0 0 = true)
  · exact (rfl : block g111 3 0 0 = true)
  · exact (rfl : block g111 4 0 0 = true)
  · exact (rfl : block g111 5 0 0 = true)
  · exact (rfl : block g111 6 0 0 = true)
  · exact g111B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111G : graphValid g111 (boundsBefore K95) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low111 : Lower true (varsX 111) (graphGoal 111) 8 := lower_forest (g:=g111) (i:=0) (hints:=1619) (before_sound K95 V95) g111G g111T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K111 := extendKnown K95 8 [(111,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V111 : Known true K111 := extend_ok (m:=111) V95 low111 (by decide +kernel)

def g119Y : Array (Bits × Bits) := #[((repeatRows 55 0xc00a213f19f1), (repeatRows 55 0x3f19f0)),
    ((repeatRows 55 0x17a01442c05600), (repeatRows 55 0x7e00000c01e00)),
    ((repeatRows 55 0x2115f914eae046), (repeatRows 55 0xff00ffe000)),
    (0x0, 0x0),
    ((repeatRows 55 0x4a3b219f43221b), (repeatRows 55 0x3001f000000)),
    ((repeatRows 55 0x7403be600c4560), (repeatRows 55 0x7803ffe0000000)),
    ((repeatRows 55 0x7fdec098b0998c), (repeatRows 55 0x7ffc0000000000))]
def g119C : List ColumnInfo := [(0,32,84,3,6), (1,0,118,0,7), (2,0,117,0,7), (2,32,84,1,5), (4,0,115,0,6), (16,0,103,0,5), (20,0,99,0,4), (32,0,87,0,6), (36,0,83,0,5), (64,0,55,0,5), (65,0,54,0,4)]
def g119D5 (j : Nat) : Nat := if j = 0 then 0x48f309183017a41c264d6d713a6b1a5ae274d534b3c6e92a69d34d62588e7713aca91f4d3549523 else 0
def g119D6 (j : Nat) : Nat := if j = 0 then 0x4040004071040245c4317108a24617214404000010101407204015408014100404000010114193482350e813f1c8d257289389648210fc72331809c481e0d854240f0601800bf58e35bf58a35bf89935fb89935bb89935fb09935bb49835bd45835be41835df4d625bf58e25bf8d925df8d525df4d525ef8d634ef4d634efd9534ef8d534ef4d534ef89534ef49534ef89934f74d623fb89623bf59623bf59523f74d523fb49523 else 0
def g119D7 (j : Nat) : Nat := if j = 0 then 0x9398a490a210149394921442025272924288404a4e62924288405250729242884052507292428840520e5a4a201ce62d072880849ca490a21012941cc524851080beae8adf377fb1d3c701e803fe6bfe35fe9aff0d7fc4bfd25df1a6f4d3fc47fd23 else 0
def g119D8 (j : Nat) : Nat := if j = 0 then 0xe84202bf else 0
def g119L : Nat → Packing
  | 5 => (7, 3, 4, 0, 0, 6, 0, g119D5)
  | 6 => (28, 2, 4, 0, 0, 9, 0, g119D6)
  | 7 => (10, 1, 4, 0, 0, 9, 0, g119D7)
  | 8 => (1, 0, 4, 0, 0, 1, 0, g119D8)
  | _ => emptyPacking
def g119I : Nat → Nat → Option (Nat × Nat)
  | 6, tag => lookupShort 4 13 1 5 3 0 (fun j => if j=0 then 0x188800c0000bb4ba04 else 0) tag
  | 7, tag => lookupShort 14 43 3 7 5 0 (fun j => if j=0 then 0x74b7e80000dcf9431ea4000000015991b6bae001c220300000018020b10003b002b9580b00a84040901028 else 0) tag
  | 8, tag => lookupShort 5 17 3 6 4 0 (fun j => if j=0 then 0x86a404a12bac00000398000005081 else 0) tag
  | _, _ => none
def g119 : Forest := ⟨119, 8, fun i => (g119Y[i]?).getD (0,0), g119C, [[]], g119L, g119I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P5n0 : block g119 5 0 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P5n6 : block g119 5 6 1 = true := by decide +kernel
theorem g119B5 : block g119 5 0 7 = true := (@block_merge g119 5 0 6 1 g119P5n0 g119P5n6)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P6n0 : block g119 6 0 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P6n6 : block g119 6 6 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P6n12 : block g119 6 12 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P6n18 : block g119 6 18 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P6n24 : block g119 6 24 4 = true := by decide +kernel
theorem g119B6 : block g119 6 0 28 = true := (@block_merge g119 6 0 12 16 (@block_merge g119 6 0 6 6 g119P6n0 g119P6n6) (@block_merge g119 6 12 6 10 g119P6n12 (@block_merge g119 6 18 6 4 g119P6n18 g119P6n24)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P7n0 : block g119 7 0 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P7n6 : block g119 7 6 4 = true := by decide +kernel
theorem g119B7 : block g119 7 0 10 = true := (@block_merge g119 7 0 6 4 g119P7n0 g119P7n6)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P8n0 : block g119 8 0 1 = true := by decide +kernel
theorem g119B8 : block g119 8 0 1 = true := g119P8n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119T : checkedTables g119 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g119 0 0 0 = true)
  · exact (rfl : block g119 1 0 0 = true)
  · exact (rfl : block g119 2 0 0 = true)
  · exact (rfl : block g119 3 0 0 = true)
  · exact (rfl : block g119 4 0 0 = true)
  · exact g119B5
  · exact g119B6
  · exact g119B7
  · exact g119B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119G : graphValid g119 (boundsBefore K111) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low119 : Lower true (varsX 119) (graphGoal 119) 9 := lower_forest (g:=g119) (i:=0) (hints:=1092) (before_sound K111 V111) g119G g119T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K119 := extendKnown K111 9 [(119,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V119 : Known true K119 := extend_ok (m:=119) V111 low119 (by decide +kernel)

def g123Y : Array (Bits × Bits) := #[((repeatRows 79 0x918c22058834f5cffe5), (repeatRows 79 0x7fc7fe0)),
    ((repeatRows 79 0x10f40540a37e05eb0840), (repeatRows 79 0xfc0000007f07ff8000)),
    (0x0, 0x0),
    ((repeatRows 79 0x22214897ca6bf80c916b), (repeatRows 79 0x1ff87ff8000000)),
    ((repeatRows 79 0x44463e1af78c80712190), (repeatRows 79 0x3f1fff8000000000)),
    ((repeatRows 79 0x7b802fe3003011824202), (repeatRows 79 0x7f003fe0000000000000)),
    ((repeatRows 79 0x7cfbb01c0440e6007c1c), (repeatRows 79 0x7fffc000000000000000))]
def g123C : List ColumnInfo := [(0,2,73,48,6), (1,0,122,0,7), (2,0,121,0,7), (3,0,120,0,4), (8,0,115,0,6), (9,0,114,0,4), (10,0,113,0,5), (16,0,107,0,7), (16,2,73,32,5), (17,0,106,0,4), (18,0,105,0,5), (24,0,99,0,4), (32,0,91,0,7), (32,2,73,16,5), (33,0,90,0,4), (40,0,83,0,5), (42,0,81,0,4), (48,0,73,0,4), (48,2,73,0,4), (50,0,73,0,4), (64,0,59,0,6), (65,0,58,0,4), (66,0,57,0,5), (80,0,43,0,5), (82,0,41,0,4), (96,0,27,0,4)]
def g123D5 (j : Nat) : Nat := if j = 0 then 0x580b83e884000000000000000000000000008200041260200000000000000000001040024d207b3c1d4e46f361a4cc6330174b4572a1449c4b21d027231974ae51259147e39198b44e210d8300c00a9d688d534c923e8217559123f0d454953448e1fe1576c9103e4f65c952340eda6024549502b69828950540ada8e1254150287f855cf6440b5a41575c9102f29454950440aea6152441102dab754910440b9a49505d8d0287e871d56340b964d50558d02e69254156340a1fe157458d02d69055d72340b5a5d50548d02f49354152340b6a5d10448d02f89344112340a7c82172895019f18381d254067c82175c9101be208497234067c82175c8d019f2085d523406f88212548d01bd183c95034067c9e12540d01bd183c9d03406dce152740d01bd38548d03406f46152340d01fc32548d03407f04952340d01 else 0
def g123D6 : Nat → Nat
  | 0 => 0x84403e83903181e01a81901781201080900580027f03ac512cfd748d9259fae11b24b3f5ce06497788ba0c12cfe6749534bbc6e92a69bd496164d27ab842c9a4fd678d7249fc6eb2e493f81d65c93cf1aa69926bd654d324d7a68b06493f5da35492deba46a925ee07497239fc0eb2e47bb49560c8f3ea2eca91cfd74d95239fae1b2a473f91d6548f6f1baca91cfe0759523bdae192a47778dd2548fe71ba4a91dee0749523eda8a92a473f5d76448e7eb86c891cff75591239faeab22473f81d6448eeebaa6891f9d454d123f9a4a9a247b74d60648f7692c0c91cfd7581923dba69032473f5d20648ebfbaa0c91e7d45d95039fae9b2a073f5cb6540f3fb2e4a81cfd76c9503bbae792a073f99d2540e7ebaec881cfd72d91039fc4eb2207775d53440fcea2a6881f9d34c91039faed92207775cf2440eeeb9e4c81df970c9903dba6b132073f5d62640f6e9a44c81cfd74899039fae5132075fdd52640eefbaa4681ddd7548d03dbeca91a07f3c952340fe692a4681ddf7448d03bbae891a07b7d912340f6eb224681cfe0759612bdae51ac053f5da3580af71ba4b014fe3759602bdaea91c05f34d52380b76b2a47014fd7558e02dba6ab1c05bb4956380a7ebb48a815ed7291502beae322a057e5c24540a7ebb46a815ed728d502bf2e11aa053f5d36540a7eb9eca815ed72995029fc6eb2a05be81d6540af6b9e4a814fd7689502bdae512a057e5c22540afd03a4a815ee4749502bdc6e92a05fa81d2540bb722a4a8176d4549502cfecb0aa056f5d21540a7ebb42a815ed7285502bf2e10aa059fd951540bbd12a0a817e92541502ed24a82a057d85d3440a7ebaec8816bd34d91029fae7b22053fdd56440b5ea2ac8814fe3759102fd20b922057b5d72440bd69a648815ed73c9102bdaea92205eb5152440bf482a48815fb7541102f728a82205fa4950440bdc9a208817a92441102dda4bb1a05be4176340a7ebaec6814fd74d8d02afeeab1a055f1d56340b3fbaac6814ff7558d028feeab1a053f5d56340b3e3aac6816dd3558d02dde4ab1a05bb4956340b7c82ac6814ff7458d029fae8b1a05b74d16340b76b2e46817e905c8d02bdaeb91a057bdd52340af6baa46817cd3548d02ddeca91a05bb5952340bf482a46815ef7448d02bdae891a05f34d12340bf482246815bf7445902bf40e92a03bd457624067ebaec480cfd73d8901beae912a037d5ca25406fb1ba4a80ff20749501be40e92a03755cc254067bb384a80df10709501beaeb92203f949723406fabae4680cf676c8d01beeea91a037d5d523407ea9aa4680fe72548d01fca4a91a03fc5d503407e89aa0680ff32540d01fe24a81a03fcc9d03407f893a0680fd12340d01deacbb12037d5d7624077ab26c480ff104d8901beae9b1203fc40f62406fab9ec480df57518901
  | 1 => 0x7040025e523e118850200083010184002000000070400010100000301020009841000410000104000b02e1c30704000080400302000810882540b44a210b01e88300000002000800c040800200000041001c1000120109504821207085011201080410401200c0003010050103041010400001207084804212040848110830000000000000010100001040040400104101019c10104001040410004101040410000404000000081010400102041011404010c501204044000076208501005010000000104041000000003010f2c0c048101c01c000007040005010304100014045011404501005008003940c080000c10108041029c107042c101040414c6209302c200081000020400104041010408137342f24c2c118dcbf0b04437342f24c20218041000412f88a724c11400104901009c1371508dc4824209c0c070082704249c2424008dc2414312ec090827038201c0259c10002c030802703420d9c116010ac5ac22c0abf2b3aae2aaaa92a3aa22a0a9f29da9a298a97293a92290a8f28ba86282a8127da7c27aa77275a7426ca69267a6625ea59253a4a242a4123fa3e23ca37235a3222ca2b229a28224a2321fa1e21ca17211a0c208a031ff9f81f69f51f19f01ec9eb1e79e41e29e11df9da1d49cf1c79c61c49c31c19c01be9bd1bb9ba1b69b51b39b01ae9ab1a99a61a29a119d99a19899519199018c98918598418297f17d97c17a97917597216e96b16796015695515394e14a94914594414294113f93c13893713593413293112d91e11c91b11991611491310f90e10a9091079041008fd0f98f80f08eb0e98e80e68e10dd8dc0d88d50d18ce0ca8c50bf8be0ba8b90b78b40b28af0ab8a80a489708d88007c87b07786c06a86706386205e859047
  | _ => 0
def g123D7 : Nat → Nat
  | 0 => 0xb04c88e10141006d4244560c12203c10300b24243841090f121c4122022210a0c131c38282040125c5890a105d82c4880e12141024961a304070908101005561bb0427090b08024a0d182038509081210200c281022e1c20654a0f090408c3c607080a0810040f982c4a70e131410300b283c60b4e1c262050408030a05088808a64a0c0a1008c50284022170e14208333870a1014102009281422a50286546070a0a0801ca0f0a1208118a05820442814241022940a1208114a2c0a1008018b14040042a5028402291181c284443141eb06070b881410200b1e3960c0a2941e396070a0a0802560c0a120818038f583028482060103c72c181420180414189c3850504080245894e1c28a5060b129c282820091f313870a120818048b4e1c28482047982d3870a131410300a1400258181a2040063059a10589c324840a08130c3421b16270c921028204c0708101002942033387480e102820600035bb4589d203850408029a2c4e901c28204012dda2f589d20385040802da121ab13a4070a0818000c684978d589d20385040c0006b45fb1627480e1410300018d096c58213a4070a0818000d6e4a6ec12213c20406016d16674e901c282060002da0d58213a4070a081005e80f361964ca4e3f71b78c0c4be1d706f815be85e12e2b6d0b5759decc7625af3d61aa7551fa85d31a8f54359edce7669532f978cab24b32308f2460e2990eb841c0fa01cfd77c5bda5e64f1077aba6dcbadfc6d4b61dacad4367f3355920c445ffae95722b765a32c2156aa5b51928093c09be4bca595294913471a30513086f41fa074fe87c43b89d20e066cc3471940c165e22ce9560a424d5260924486e3dd1da0d4c60e2c2137885436815a07c82980a6000bf59225bf58a25bf58225ff8d925bf8d925ff4d925ff85925ff45925ff81925bf81925ff41925b758c25bd45825bf41825be41825ff49534bd85934ff8d724bf59724ef4d324bf58f24bf58324ff8d524ff4d524fb49723bf59723bd58723bf58323ff51523bfd9523ff59523bf59523f74d523fbc9523ff49523fb49523bfd9123ff59123bf59123f74d123bf81923ff41923ff51503bfd9503ff59503f74d503ffc9503ff49503bfd9103ff59103bf59103f74d103ffc9103ff49103ffc9903bf89903ff49903f748d03bf59612b758e12bf58212ff8d602ff4d602fb49602bf59602fb48e02bf58e02ff91502ff51502ff8d502ff4d502bfd9502ff99502ff59502bf59502fbc9502ff89502ff49502fb49502ff85502ff45502fe41502ff4d102bfd9102ff59102bf59102fbc9102fb49102fe41102bfd8d02ff58d02bf58d02fbc8d02ff48d02fb48d02ff44d02ff45902fd49601fd48e01ff49501bfd8901fd89501fd49501fd09501fdc9101fd49101fdc8d01fd48d01fc40d01fdd8901fd18901
  | 1 => 0x192e58a0f5830384c40808034b941e303860809081005972a506070809081005144e1c3305ca0c4e1c2020200a2e2d38711102001960c8810014a04420442830384048408020a85420442e507ec4e18262c24941bb04670c1116100517283f60cce1c30509881210200f2e507ecce1826242491181e1095e7cc8e8b0801ca040a60c0e182020200824446270f1a24020a1298305a70e18262040401a5260c0e1420242040145078c0cb8f08b941eb23870c110125c78c8e1c30404040155c6ec8e18222c2009283c6470e18284048408030c9458305c70e108305c60b8e1c202c2040165ca0b0cc17182e38202008305ca6c162038444497283d60b8e1c304c480b282e387082982e5160b8e1c2624051424407ac182e4470e080803488f583058844394244480f582e447880808036a1222407ac182c407881114038a0c171c38242040125c5890a8408c64a1218263871cb8c131c384050408028b95282442e504880f0408e50487082090e1032849609911c3840504080309111cb060910888284c9111c
  | _ => 0
def g123D8 (j : Nat) : Nat := if j = 0 then 0x5d650fb0c9c718488284100f61759440fb0c9c71848828410115d43ec3271c61220a10403975134913cd3081c488284101050c9c718488284100b5103cd3271c61220a104039750fb0c1c61220a104035750fb0c2c81c61220a10403d859436c30a1c610284100e5d4b0c2481c488204031650db0c2271c40a104035650db0c2271c610284100e50fb0c9c718488204031440fb0c9c718512208100e6164d0b2718204959436c3089c71840c204039236c227081008a99382434207b0df9952ca4e0888e717424c33048036001fe25fe92ff097fa69ff24fe927fc8ffa47fd13fe81ff84bfa25fe02fe817d807fa03f501 else 0
def g123D9 (j : Nat) : Nat := if j = 0 then 0xc388223f else 0
def g123L : Nat → Packing
  | 5 => (38, 4, 5, 0, 0, 9, 0, g123D5)
  | 6 => (206, 3, 5, 0, 0, 12, 0, g123D6)
  | 7 => (111, 2, 5, 0, 0, 13, 0, g123D7)
  | 8 => (17, 1, 5, 0, 0, 11, 0, g123D8)
  | 9 => (1, 0, 5, 0, 0, 1, 0, g123D9)
  | _ => emptyPacking
def g123I : Nat → Nat → Option (Nat × Nat)
  | 6, tag => lookupShort 29 86 4 9 6 1 (fun j => if j=0 then 0x2c00007739b0a000024000c02750d5a098032112ce06c915800000011a003832887000000085ccc2ca652e78000000af0001f5b0415400008f1440223ac8000400230000003000021dcb4251ead1112d412a1f0488800008b800488dcc085180001308021092421020201003210002 else 0) tag
  | 7, tag => lookupShort 138 414 4 11 8 1 (fun j => if j=0 then 0x512c3c9080013a5112cb37486c24000000000200000068d88c0ec0067585299000173d261a45095d0ab14061aab000003610005820803600013e0000061d40400000000000000000bc000034000008948644a68a000000007c7001120e57bd0008a000000001ae12e0000000003e274d020f310916c29d9700d9cd1e845238000000001b0000ae9e499e008e400153fa9000000000000000de98000001d6115cc4c2e0c556e6a8690fb5f23245fa90003b30c40ea0364c000ec0002b611c00000407000ac400125ee40000017fcad06d406bf1415bc63b4216a2c366e242b616135f514e75d000000000002b0b106c42ce2ee0e8b62a31eeaeae292400159a0852285a2728ec76177499368e00055e00031443c906540000000000116b640008a918229e95001910002458a410c00000d300024882a000000000008a344400041cd000000000001a135a64b0ceda5ab0000000000002d3798234e1a70000000000040800213146406000000000012a8cbebd000001650000000003df819995818d00057325e52e700c6d9c0000044a0000d47e13ad2e1afb957685765a9242c07326d751359fe2787d40ba8fdf65e0ed5715b9310002bd4f000c7e65b1146f4c3669056596c98c3cd80085923000000a8a0000056ba88a8b5628200000238a33000000000008f5264004ba153a0c4484e00000209800000000000000000000f8000000000074a91600064800d4d43c00000831c374b60b26b9b400639a9e88e60395d0a0253c50c8ccdc22f800c8083f634654ef830948001202001014810102238020203642012010210270101a00001147023451010400050000082300200110832002006081004001302003a2010020432010300661410110002017 else 0) tag
  | 8, tag => lookupShort 78 234 4 10 7 1 (fun j => if j=0 then 0x12f00139ebf3d00061003328fc6c1882d00000558000000000034b024c000148fb9fce99c83b6920f15a811794220cf24a0c7e94432a4ef1d1aec1001890026d59c0000181c611951c0000000002307390d0031c003ab0001e93e3703141c7e86efd4e82a36b3d290036a000000012502e6300133b10854b3289154481196322cc00000d535a9244bec152d6e4000000f58800012600246da109d72130880097e6600000000026c62e00358aa2480015e49c0088c00508001900086fa10028a55eaa230000000003d5da11cd594a9aec004ac000013800000f62357ae00f6d0571c00e7a0848400d0f24955990031240c1a00000000110000018000003061440060aa30000005b071345980400f8cea14c00000005b800b2c00000000000000000000000d5100082213004030044906000008221030310020000231045000001030520517011400003031 else 0) tag
  | 9, tag => lookupShort 14 45 3 8 5 1 (fun j => if j=0 then 0x23c000002c30a232e920400010ca4421ba002293800003117982400000297000034000003a802109c1cac02b28e9001000600 else 0) tag
  | _, _ => none
def g123 : Forest := ⟨123, 9, fun i => (g123Y[i]?).getD (0,0), g123C, [[], [99, 84]], g123L, g123I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5n0 : block g123 5 0 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5n6 : block g123 5 6 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5n12 : block g123 5 12 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5n18 : block g123 5 18 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5n24 : block g123 5 24 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5n30 : block g123 5 30 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5n36 : block g123 5 36 2 = true := by decide +kernel
theorem g123B5 : block g123 5 0 38 = true := (@block_merge g123 5 0 18 20 (@block_merge g123 5 0 6 12 g123P5n0 (@block_merge g123 5 6 6 6 g123P5n6 g123P5n12)) (@block_merge g123 5 18 12 8 (@block_merge g123 5 18 6 6 g123P5n18 g123P5n24) (@block_merge g123 5 30 6 2 g123P5n30 g123P5n36)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n0 : block g123 6 0 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n6 : block g123 6 6 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n12 : block g123 6 12 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n18 : block g123 6 18 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n24 : block g123 6 24 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n30 : block g123 6 30 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n36 : block g123 6 36 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n42 : block g123 6 42 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n48 : block g123 6 48 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n54 : block g123 6 54 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n60 : block g123 6 60 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n66 : block g123 6 66 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n72 : block g123 6 72 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n78 : block g123 6 78 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n84 : block g123 6 84 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n90 : block g123 6 90 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n96 : block g123 6 96 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n102 : block g123 6 102 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n108 : block g123 6 108 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n114 : block g123 6 114 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n120 : block g123 6 120 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n126 : block g123 6 126 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n132 : block g123 6 132 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n138 : block g123 6 138 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n144 : block g123 6 144 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n150 : block g123 6 150 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n156 : block g123 6 156 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n162 : block g123 6 162 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n168 : block g123 6 168 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n174 : block g123 6 174 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n180 : block g123 6 180 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n186 : block g123 6 186 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n192 : block g123 6 192 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n198 : block g123 6 198 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n204 : block g123 6 204 2 = true := by decide +kernel
theorem g123B6 : block g123 6 0 206 = true := (@block_merge g123 6 0 102 104 (@block_merge g123 6 0 48 54 (@block_merge g123 6 0 24 24 (@block_merge g123 6 0 12 12 (@block_merge g123 6 0 6 6 g123P6n0 g123P6n6) (@block_merge g123 6 12 6 6 g123P6n12 g123P6n18)) (@block_merge g123 6 24 12 12 (@block_merge g123 6 24 6 6 g123P6n24 g123P6n30) (@block_merge g123 6 36 6 6 g123P6n36 g123P6n42))) (@block_merge g123 6 48 24 30 (@block_merge g123 6 48 12 12 (@block_merge g123 6 48 6 6 g123P6n48 g123P6n54) (@block_merge g123 6 60 6 6 g123P6n60 g123P6n66)) (@block_merge g123 6 72 12 18 (@block_merge g123 6 72 6 6 g123P6n72 g123P6n78) (@block_merge g123 6 84 6 12 g123P6n84 (@block_merge g123 6 90 6 6 g123P6n90 g123P6n96))))) (@block_merge g123 6 102 54 50 (@block_merge g123 6 102 24 30 (@block_merge g123 6 102 12 12 (@block_merge g123 6 102 6 6 g123P6n102 g123P6n108) (@block_merge g123 6 114 6 6 g123P6n114 g123P6n120)) (@block_merge g123 6 126 12 18 (@block_merge g123 6 126 6 6 g123P6n126 g123P6n132) (@block_merge g123 6 138 6 12 g123P6n138 (@block_merge g123 6 144 6 6 g123P6n144 g123P6n150)))) (@block_merge g123 6 156 24 26 (@block_merge g123 6 156 12 12 (@block_merge g123 6 156 6 6 g123P6n156 g123P6n162) (@block_merge g123 6 168 6 6 g123P6n168 g123P6n174)) (@block_merge g123 6 180 12 14 (@block_merge g123 6 180 6 6 g123P6n180 g123P6n186) (@block_merge g123 6 192 6 8 g123P6n192 (@block_merge g123 6 198 6 2 g123P6n198 g123P6n204))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7n0 : block g123 7 0 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7n6 : block g123 7 6 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7n12 : block g123 7 12 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7n18 : block g123 7 18 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7n24 : block g123 7 24 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7n30 : block g123 7 30 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7n36 : block g123 7 36 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7n42 : block g123 7 42 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7n48 : block g123 7 48 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7n54 : block g123 7 54 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7n60 : block g123 7 60 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7n66 : block g123 7 66 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7n72 : block g123 7 72 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7n78 : block g123 7 78 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7n84 : block g123 7 84 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7n90 : block g123 7 90 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7n96 : block g123 7 96 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7n102 : block g123 7 102 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7n108 : block g123 7 108 3 = true := by decide +kernel
theorem g123B7 : block g123 7 0 111 = true := (@block_merge g123 7 0 54 57 (@block_merge g123 7 0 24 30 (@block_merge g123 7 0 12 12 (@block_merge g123 7 0 6 6 g123P7n0 g123P7n6) (@block_merge g123 7 12 6 6 g123P7n12 g123P7n18)) (@block_merge g123 7 24 12 18 (@block_merge g123 7 24 6 6 g123P7n24 g123P7n30) (@block_merge g123 7 36 6 12 g123P7n36 (@block_merge g123 7 42 6 6 g123P7n42 g123P7n48)))) (@block_merge g123 7 54 30 27 (@block_merge g123 7 54 12 18 (@block_merge g123 7 54 6 6 g123P7n54 g123P7n60) (@block_merge g123 7 66 6 12 g123P7n66 (@block_merge g123 7 72 6 6 g123P7n72 g123P7n78))) (@block_merge g123 7 84 12 15 (@block_merge g123 7 84 6 6 g123P7n84 g123P7n90) (@block_merge g123 7 96 6 9 g123P7n96 (@block_merge g123 7 102 6 3 g123P7n102 g123P7n108)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P8n0 : block g123 8 0 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P8n6 : block g123 8 6 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P8n12 : block g123 8 12 5 = true := by decide +kernel
theorem g123B8 : block g123 8 0 17 = true := (@block_merge g123 8 0 6 11 g123P8n0 (@block_merge g123 8 6 6 5 g123P8n6 g123P8n12))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P9n0 : block g123 9 0 1 = true := by decide +kernel
theorem g123B9 : block g123 9 0 1 = true := g123P9n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123T : checkedTables g123 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g123 0 0 0 = true)
  · exact (rfl : block g123 1 0 0 = true)
  · exact (rfl : block g123 2 0 0 = true)
  · exact (rfl : block g123 3 0 0 = true)
  · exact (rfl : block g123 4 0 0 = true)
  · exact g123B5
  · exact g123B6
  · exact g123B7
  · exact g123B8
  · exact g123B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123G : graphValid g123 (boundsBefore K119) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low123 : Lower true (varsX 123) (graphGoal 123) 10 := lower_forest (g:=g123) (i:=0) (hints:=67) (before_sound K119 V119) g123G g123T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K123 := extendKnown K119 10 [(123,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V123 : Known true K123 := extend_ok (m:=123) V119 low123 (by decide +kernel)

def g125Y : Array (Bits × Bits) := #[((repeatRows 65 0x3118691c419bdcf9), (repeatRows 65 0xffc78)),
    (0x0, 0x0),
    ((repeatRows 65 0x4227c021bf0d6b00), (repeatRows 65 0x7e0003f8fff80)),
    ((repeatRows 65 0x844096f52df00c8b), (repeatRows 65 0x7fc3ff00000)),
    ((repeatRows 65 0x108f904bbc6007114), (repeatRows 65 0xf807ffc0000000)),
    ((repeatRows 65 0x1f075f8c008218020), (repeatRows 65 0x1f0fff80000000000)),
    ((repeatRows 65 0x1ef860702304e0246), (repeatRows 65 0x1ff00000000000000))]
def g125C : List ColumnInfo := [(0,4,41,80,6), (0,32,84,9,6), (1,0,124,0,7), (1,32,84,8,5), (4,0,121,0,7), (5,0,120,0,4), (8,0,117,0,7), (8,32,84,1,5), (9,0,84,0,4), (9,32,84,0,4), (12,0,113,0,5), (16,0,109,0,7), (16,4,41,64,5), (17,0,108,0,4), (20,0,105,0,5), (24,0,101,0,4), (32,0,93,0,7), (33,0,92,0,5), (36,0,89,0,5), (41,0,84,0,4), (44,0,81,0,4), (52,0,73,0,4), (64,0,61,0,7), (64,4,41,16,5), (68,0,57,0,5), (72,0,53,0,4), (80,0,41,0,4), (80,4,41,0,4), (84,0,41,0,4)]
def g125D5 (j : Nat) : Nat := if j = 0 then 0x81000b6785b30603d24950548d03b6a384950540aad86135d9102e69254156340b5a5d50548d02f49354152340bd889d2541501 else 0
def g125D6 (j : Nat) : Nat := if j = 0 then 0x400080040008400421b020808100241006c11b046c242090401309020c0090208016090846068202a161c02990101db08043100108401004004160908582420204081d06409402c2430f090800024082001010982020dc02421980c51b3670cceb0967e6c4038261c0346c5cd99814098700870086603106c4fc03430ac25981610098700d6b04d82414300ac151036b260a3e4768c112a1a42684104a063fe7e0f69e63c6750e89c6386660c898e2fe5d0b09562965109e9322464608a91220e4107e8ee1ae2803e86a0660b00e81a0160013f5ce264167f33a0a91cfd75819239fae5b2a07778dd6540fed1ba0a81f792541503df20b132073f5d62640eefbaa4681edf6548d03f9a4a91a07f64152340e7f1baca816ee2759502bdc6e92a05fa89d0540bbc9aa0a817692541502d7a6bb2205af4576440a5ebaec8814ff7558d029faeab1a05bb4956340b7c82ac6815ef7548d02bdaea91a05f34d52340b76b2a46817e90548d02d7ec889a05bd457624077c82ec480cfd75d89019fae7b1203fc89d05407f893a0a80f314541501ee24a82a03fc49d03407e891a0680ef565d8901fe20bb12037d5d762407f881ec480df573d8901 else 0
def g125D7 (j : Nat) : Nat := if j = 0 then 0x2c2530684086adc080b129830487081010069960244260c0c722040066cb0f16243021cb13203e5898c1822344080803980f1a203a20439b6c406cc962c304840808034d9a6c5868c4839b32345890c3362c3658b060a02024b1320365894c1824384080803980f1a2130606393e03c68c162530689081414271aa02c406483196c4c80b1222304870808034cb62c244070d0e1024300c314020011b16122230606090c02bb6b8d9210118b13203c6ab12223048708080389d01eac589101c3648708121807d01c0036c4d86bcd1210e71b305625344090e1024261c6c4f8305625344090e10242716264358b12982c4090e1020300f36d89b099af3448500a36d984cd6253e6880e1218069b2ed982b12982c487081218000f365db7099af344080c14030db627c180c5625305890e10243000226ebf6e03462bcd102030500d6c4d86b5625305890e1024300ea3c9db9a49899528ea8b385281b7eb7a673e70769f66f60e5b45925465164ae43f4243ed39332b2bc27020f1a01460c9068000ff89905bf89905ff49905ff45504ff41523bf81923ff41923bfd9503ff59503ff49503fe41503bf89903ff49903f748d03ff4d502bf59502fb49502ff45502fe41502afd9102bf58d02fb48d02ff44d02edd1601fd49601fd48e01bfd8901edd1501ed51501fd49501fc41501fd48d01fc40d01fdd8901 else 0
def g125D8 (j : Nat) : Nat := if j = 0 then 0xbad82159730d20818408076cb248195963cc3081c4102021b2caa285658f30d20810201fb2d82079858e34824410201ebecb2aa6081c5cc30910408086cb6081a61730d2081840807afb2d82065659438c244102021b2c9e085659240e348206102022e6d85730818442fb2d8206565cc30a206102020dafb60657308184017d16796e4f90b36ca81c857090007f417fa29fd04fe91ff44ffa07fd12fe817d807fa03f501 else 0
def g125D9 (j : Nat) : Nat := if j = 0 then 0x5a0b310433f else 0
def g125L : Nat → Packing
  | 5 => (7, 4, 5, 0, 0, 6, 0, g125D5)
  | 6 => (47, 3, 5, 0, 0, 11, 0, g125D6)
  | 7 => (34, 2, 5, 0, 0, 12, 0, g125D7)
  | 8 => (11, 1, 5, 0, 0, 10, 0, g125D8)
  | 9 => (1, 0, 5, 0, 0, 1, 0, g125D9)
  | _ => emptyPacking
def g125I : Nat → Nat → Option (Nat × Nat)
  | 6, tag => lookupShort 6 18 1 6 3 1 (fun j => if j=0 then 0x212a400b0000205408fdd98000484 else 0) tag
  | 7, tag => lookupShort 30 91 4 9 6 1 (fun j => if j=0 then 0x300000000000000042438504a77d431300205540068c0e4c90cd018011f4f00000000000216ae00000012c000600017f2e3f2c24c409423820ab5a3a20a3a491a2b0288a52ad0021eaa00000004fa32a0a0000031002320000003b8698614e15db872103600002235e20011000080003104700104 else 0) tag
  | 8, tag => lookupShort 27 83 4 9 6 1 (fun j => if j=0 then 0x6db7c021d0ce5507100335e9e4800000018ea340922000000342500046c0000c0000000000002a2000e02e18922a62401440021400606673400000042a28c2cf000001361b48100006c7f319aae258018f00001928770c13419712a611020731622000152100530 else 0) tag
  | 9, tag => lookupShort 10 29 2 7 4 1 (fun j => if j=0 then 0x9b207900002a000f800a201b00caa4c534449a55c280000c0380 else 0) tag
  | _, _ => none
def g125 : Forest := ⟨125, 9, fun i => (g125Y[i]?).getD (0,0), g125C, [[], [96, 82, 67]], g125L, g125I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P5n0 : block g125 5 0 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P5n6 : block g125 5 6 1 = true := by decide +kernel
theorem g125B5 : block g125 5 0 7 = true := (@block_merge g125 5 0 6 1 g125P5n0 g125P5n6)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P6n0 : block g125 6 0 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P6n6 : block g125 6 6 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P6n12 : block g125 6 12 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P6n18 : block g125 6 18 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P6n24 : block g125 6 24 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P6n30 : block g125 6 30 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P6n36 : block g125 6 36 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P6n42 : block g125 6 42 5 = true := by decide +kernel
theorem g125B6 : block g125 6 0 47 = true := (@block_merge g125 6 0 24 23 (@block_merge g125 6 0 12 12 (@block_merge g125 6 0 6 6 g125P6n0 g125P6n6) (@block_merge g125 6 12 6 6 g125P6n12 g125P6n18)) (@block_merge g125 6 24 12 11 (@block_merge g125 6 24 6 6 g125P6n24 g125P6n30) (@block_merge g125 6 36 6 5 g125P6n36 g125P6n42)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P7n0 : block g125 7 0 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P7n6 : block g125 7 6 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P7n12 : block g125 7 12 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P7n18 : block g125 7 18 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P7n24 : block g125 7 24 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P7n30 : block g125 7 30 4 = true := by decide +kernel
theorem g125B7 : block g125 7 0 34 = true := (@block_merge g125 7 0 18 16 (@block_merge g125 7 0 6 12 g125P7n0 (@block_merge g125 7 6 6 6 g125P7n6 g125P7n12)) (@block_merge g125 7 18 6 10 g125P7n18 (@block_merge g125 7 24 6 4 g125P7n24 g125P7n30)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P8n0 : block g125 8 0 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P8n6 : block g125 8 6 5 = true := by decide +kernel
theorem g125B8 : block g125 8 0 11 = true := (@block_merge g125 8 0 6 5 g125P8n0 g125P8n6)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P9n0 : block g125 9 0 1 = true := by decide +kernel
theorem g125B9 : block g125 9 0 1 = true := g125P9n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125T : checkedTables g125 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g125 0 0 0 = true)
  · exact (rfl : block g125 1 0 0 = true)
  · exact (rfl : block g125 2 0 0 = true)
  · exact (rfl : block g125 3 0 0 = true)
  · exact (rfl : block g125 4 0 0 = true)
  · exact g125B5
  · exact g125B6
  · exact g125B7
  · exact g125B8
  · exact g125B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125G : graphValid g125 (boundsBefore K123) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low125 : Lower true (varsX 125) (graphGoal 125) 10 := lower_forest (g:=g125) (i:=0) (hints:=1027) (before_sound K123 V123) g125G g125T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K125 := extendKnown K123 10 [(125,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V125 : Known true K125 := extend_ok (m:=125) V123 low125 (by decide +kernel)

def g126Y : Array (Bits × Bits) := #[(0x0, 0x0),
    ((repeatRows 43 0x3e01814e2cd), (repeatRows 43 0x1e0000063cc)),
    ((repeatRows 43 0x23f02907b0), (repeatRows 43 0x1f80003f0)),
    ((repeatRows 43 0x4427f05c00), (repeatRows 43 0x3fc7c00)),
    ((repeatRows 43 0x49e42bfe417), (repeatRows 43 0xe03ff8000)),
    ((repeatRows 43 0x70f7cc008c8), (repeatRows 43 0x60ffc000000)),
    ((repeatRows 43 0x7f983021322), (repeatRows 43 0x7f000000000))]
def g126C : List ColumnInfo := [(0,32,84,10,6), (2,0,124,0,7), (4,0,122,0,7), (8,0,118,0,7), (16,0,110,0,5), (32,0,94,0,6), (64,0,62,0,5)]
def g126D5 (j : Nat) : Nat := if j = 0 then 0x4f61758e35 else 0
def g126D6 (j : Nat) : Nat := if j = 0 then 0x20440806204406c85b2c0bf58e35fd85935bd85935bd45835be41835 else 0
def g126D7 (j : Nat) : Nat := if j = 0 then 0x1952ce8a440a654b3a291029952ce8a440ab8b807f8d7fa6bfc35 else 0
def g126D8 (j : Nat) : Nat := if j = 0 then 0xad102bf else 0
def g126L : Nat → Packing
  | 5 => (1, 3, 3, 0, 0, 1, 0, g126D5)
  | 6 => (5, 2, 3, 0, 0, 6, 0, g126D6)
  | 7 => (3, 1, 3, 0, 0, 7, 0, g126D7)
  | 8 => (1, 0, 3, 0, 0, 1, 0, g126D8)
  | _ => emptyPacking
def g126I : Nat → Nat → Option (Nat × Nat)
  | 6, tag => lookupShort 1 2 1 3 1 0 (fun j => if j=0 then 0x0 else 0) tag
  | 7, tag => lookupShort 3 10 2 6 3 1 (fun j => if j=0 then 0x8800218c8c00922 else 0) tag
  | 8, tag => lookupShort 2 10 1 5 2 1 (fun j => if j=0 then 0xf000200000c24 else 0) tag
  | _, _ => none
def g126 : Forest := ⟨126, 8, fun i => (g126Y[i]?).getD (0,0), g126C, [[], [49, 100]], g126L, g126I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n0 : block g126 5 0 1 = true := by decide +kernel
theorem g126B5 : block g126 5 0 1 = true := g126P5n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n0 : block g126 6 0 5 = true := by decide +kernel
theorem g126B6 : block g126 6 0 5 = true := g126P6n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n0 : block g126 7 0 3 = true := by decide +kernel
theorem g126B7 : block g126 7 0 3 = true := g126P7n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P8n0 : block g126 8 0 1 = true := by decide +kernel
theorem g126B8 : block g126 8 0 1 = true := g126P8n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126T : checkedTables g126 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g126 0 0 0 = true)
  · exact (rfl : block g126 1 0 0 = true)
  · exact (rfl : block g126 2 0 0 = true)
  · exact (rfl : block g126 3 0 0 = true)
  · exact (rfl : block g126 4 0 0 = true)
  · exact g126B5
  · exact g126B6
  · exact g126B7
  · exact g126B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126G : graphValid g126 (boundsBefore K125) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low126 : Lower true (varsX 126) (graphGoal 126) 9 := lower_forest (g:=g126) (i:=0) (hints:=34690112) (before_sound K125 V125) g126G g126T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K126 := extendKnown K125 9 [(126,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V126 : Known true K126 := extend_ok (m:=126) V125 low126 (by decide +kernel)

def g127Y : Array (Bits × Bits) := #[(0x491615382a0a1013249970180593017b295f4d869d7d9133, 0x83ff0007ff800fff8000),
    (0x82ed8000401420240022a086bb00d6104206ff7d60100084, 0xff8000000000000000f007ff80fc000007fffff0000000),
    (0x10008004085f90048014ccbf41000ebdef6e4880800122208, 0x1ff00000000fff80000fffffff8000000000000),
    (0x21431298910204bf14a707ddfddef0003808811905184c451, 0xfff0000ffffffff00000000000000000000),
    (0x42041ce17e6418d7ef3ff00e01e4a0c1c04f01e206627789e, 0x7fe000fffffff0000000000000000000000000000),
    (0x7c7807005f97ef18083800100e00c10600700e041883800e0, 0x7ff000007fffff00000000000000000000000000000000000),
    (0x7f8fe7fe601808e00fc008e070070e380f807007e0fc07f00, 0x7fffffff80000000000000000000000000000000000000000)]
def g127C : List ColumnInfo := [(0,2,77,48,7), (0,4,43,80,7), (0,32,84,11,7), (1,0,126,0,9), (1,32,84,10,6), (2,0,125,0,10), (2,32,84,9,6), (3,0,124,0,7), (3,32,84,8,5), (4,0,123,0,10), (5,0,122,0,7), (8,0,119,0,9), (8,32,84,3,6), (9,0,118,0,7), (9,32,84,2,5), (10,0,117,0,7), (10,32,84,1,5), (11,0,84,0,4), (11,32,84,0,4), (12,0,115,0,6), (13,0,114,0,4), (16,0,111,0,8), (16,2,77,32,6), (16,4,43,64,6), (17,0,110,0,5), (18,0,109,0,7), (19,0,108,0,4), (20,0,107,0,7), (21,0,106,0,4), (24,0,103,0,5), (32,0,95,0,9), (32,2,77,16,6), (33,0,94,0,6), (34,0,93,0,7), (35,0,92,0,5), (36,0,91,0,7), (37,0,90,0,4), (40,0,87,0,6), (41,0,86,0,5), (44,0,83,0,5), (48,0,77,0,5), (48,2,77,0,5), (64,0,63,0,8), (64,4,43,16,6), (65,0,62,0,5), (66,0,61,0,7), (68,0,59,0,6), (69,0,58,0,4), (72,0,55,0,5), (73,0,54,0,4), (74,0,53,0,4), (80,0,43,0,5), (80,4,43,0,5), (84,0,43,0,5), (96,0,31,0,5)]
def g127D5 (j : Nat) : Nat := if j = 0 then 0x930c083d760d4ef11428c9af0b17652519420764d3348a5234848ec9b2696a84ac865198541101 else 0
def g127D6 : Nat → Nat
  | 0 => 0x2bb28e9589190640a6ea9a5624641902bb8686585190640aeaa4a5614641902bb28e9585190640aeca3a5213641902bb2692384d90640a3ea0a64f8651502a7a9e9468213540abc93a11a084d502a7a5e8468213540abe11a11a084d502c3b9a4796193440aae9a6e25064d102aba9a9894193440aeaa6a525064d102de2525394193440b8e87a619064d102fa24e5464193440be89494d9064d102e2b519768e17440baa94641a385d102af886995e190440abaa4a5658641102af28e9596190440abe21a5658641102eaa9a6496190440a7a9a4a253641102baa9a9494d90440b2eb9661985411029eaaa7466150440b6ab965198541102cf8e1a196150440b3e1868658541102de851a196150440a7a9a3e594541102cbae59864e10440b6ab965193841102eaae19464e10440b6aa6a6593441102d6a1e9964d10440af8a3a6193441102eaa9a9864d10440bb8a3a6193441102fa2e59364d10440bb89868e13441102be269a384d10440a3f20a64e4855901af8829388a146406be20a64e2851901abc69b48821364063f1a9d22084d901af88a94882136406af1a6a52084d901af468e9482136406be22a652084d901cf88a994821364063f19a823464d901cf482193d19364073e229821464d901cec413948e1764073d2098e1365d9019dce8e4955905406771a39255641501dd85662951905407761a58a54641501bcc92956519054077622955946415019f88a9948d905406f622a5193541501cf88a609619344073e3a2825864d1018bda6986219344072f186424864d1018fc82998919344067d20a64e464d101ba94a88651934406eb10a219464d101bb4428864d93440779209d19364d101be4683464d93440779209519364d101af88a986415344063f20a659839d101af48293660e744077a2498a58641101de452939219044077a1598a54641101de84e62951904407ea229e194641101ba84a886519044067b1a4a2536411018fc692894d904406eb1a6d253641101bac9a9494d904406f91a3d193641101af88a986e1504406be22a6198541101af44e88661504406be12a2198541101dace594661504407ab08651985411019eca6986d15044077918664f4541101be88a98651504406f913a2194541101be84a886515044076b3965193841101eace19464e104407731866563441101be88a9464d1044076b39651934411019ec6a6964d104406f91a3a593441101be88a9964d1044076b26a6593441101de88a9964d1044076b19625934411019ecaa4964d104406bb38a2593441101be84a8964d1044067b1a9a193441101be468e864d104406f923a6193441101be88a9864d1044067b2a92193441101be44e8864d104406fa12a2193441101fa4e59364d104407e90964d93441101ee461a384d104406f91a68e13441101
  | 1 => 0xd636c798a19195d4741b1ce398a15751d06877a69574e04741a9ce3a55d2811d06a758e9574604741b2d90364e4855906d2751d3911d5641b49d574e44751906d2b55d2911d4641a17d9a963784d9459796822951a175169e62a5198085d45e3641903921764d79590540e485d935e3a41902921764d797105406485d935c7a40b90921764d71f101e42485d93587b6a7788a1464d69ea0a5e22851935a7a829978a1464d7359954e50811935c7aa5d29420464d73590364e485590587b6a7788a1464169ce3a5e22851905a738e9978a1464171ce398a17651905cd6655094e0464165ce2a652368dd05cd640d93e19454169e61a562285d934a7a829588a1764d29e9a0e4a085d934e2e5d949420764d38d9764e5081d934e3c5d919420764d33b149465081d934da64e9091d9464d36b11a4247651934da6529091d9364d36d11a424764d934da6825464d9064d2e99a0d213641934b2b4a876519754d2cb90a1d9465d534a798a976861754d29e52a1da185d534a7c42876861754d39590540f865d534e6a41102e19754d397105407865d534e6c41101e19754d31e902e43865d534ec641503e19454d34b9764247651534ba6428764d9454d2cad2a1d94641d34b2d46876519074d2cb9a49d90641d34a738e9588a1764129e61a562285d904ba64e848559064136994a4e47641904bac86959519064136a9598a54641904daa4e62951906412eb1a19614641904ba68e95851906412eb11a1e14641904ba668f494d906412cad2a1d9465d504a798a976861754129d53a1da185d504a794a87686175413ab14641a185d504eac5190686145412e993a1d90651504b2e6924641a37413caa2a519068dd04f26519068dd344132b986424864d104ba6428864d934412ab9a8a19064d104ba668e8641934413aaa2a619064d104ba64e876419344136c9398a54641903bb28a9464d90640ead9a8d253641903bb28a9494d90640e6d9a9d213641903b3669f484d90640eeca2a5213641903bd28a9464d50540ed597a1193541503bd24a8464d50540ef511a119354150383fa69862197440ecad2a219465d103b2d468865197440ecb9a4919065d103b3668e464197440fcaa2a519065d103d2e225464197440fc9b464d9065d103f26519364197440ecd88a4d9065d103d36225364197440fc994641a385d103cb6619092193440ee8d2a219464d103ba5468865193440ee990a219464d103ba669b494193440ee9a6a525064d103ba6692864193440faca2a619064d103ab66a2464193440ee99a4919064d103fa28a9464193440e3ea0a64e4855902af28e9956024640abca0a6553811902af28e9956027640abca3a5624841902af28e9959210640a6e9a39a54841902af8686585210640abca3a56148419029bae8e495590640a6e9a392556419
  | 2 => 0x1a020000000034040000e8a0f45040000000000000000000000000000000000000000000000000000000000000606080000000000000000000000000000000000000000001a0c1006080000000000001a241d1208000000000001810400000000000002960805541296080000078907c482000000000038904002c482000000000000001804000000000000000000000000100218d8384c1c1000000000000000000000000000000606080c0c1000c0577921800000000685074283a14100aa82005779210000000015de48400000c10000381820000000000000603070182000e040020c20aa09207a06204a03201a001fe9fd1fb9fa1f89f71f59f41f29f11ef9ee1ec9eb1e99e81e69e51e39e21e09df1dd9dc1da9d91d79d61d49d31d19d01ce9cd1cb9ca1c89c71c2dc15bfdbe5bcdbb5b71b59b41b29ae5aa1a89a71a59a41a29a119f99e19c99b19999819699519399219098f18d98c18a98918798618498318198017e97d17b97a17897717597417297116f96e16c968566d65563d62560d5f55dd5c55ad59557d56554d53551d5054ed4d54bd4a548d47545d44542d4153fd3e53cd38934532d3152fd2e52cd2b529d28526d2291e51cd1b519d18516d15513d1250e10c90b1099081069051039021008fc4facf68f24f0cef4edcec4e80e3ce24e0cdf4ddcdc4dacd94d50d38d20cdccc4cacc94c7cc64c4cc34c1cc04bc0ba8b90b78b60b48b30b18b00ae8ad0ab8aa0a88a70a58a409fc98c9489309189008e88d08b88a08888708588408288107f87e07c87b079878076872470c6c86b06145fc5e45cc5b459c5845404fc4b84a045c4443d43bc3a438c37435c2ec2d42bc2782602482301ec1d41bc1a418c17415c14412c1140d008c0740300180025e5a08655789d46a79869576022751a9ea0a55d8089d46a7a829376022751b2af96e518089d46979682196162751a9e61a6158389d46a79869856022751a9ce3a6558089d46a79869956022751a9ea0a6558089d46a7a829936022751b97105406485
  | _ => 0
def g127D7 : Nat → Nat
  | 0 => 0xf464d901bf8c868c9b2037e629519364077e410a326c80efc412385d9019fbca470bb2033f5948e176406fe4129b2ec80ef58e1365d901bf314a8c9aa03f724955905406ee492ab20a80dfc64e4641501fb8aca8c82a037f23951905407fc452a320a80df88a54641501fb8ab28c82a037f1948d905406fe4929b20a80edc55a4841501fb92326a82a03f71464d5054077628cc046880efc659808d101d7bc350c9a2037b594a1934406fcc52c326880dfc825864d101d7b34b0c9a203be629619344067cc52c326880efc825864d1019f904b0c9a203af586219344067ed304326880df94a4864d101bf88490c9a2037b190d19344075ef0d2326880cfd662464d101bdaca48c9a2037d59391934406fcc52a326880ebde19464d101fd314a8c9a203eb78651934407d690ca326880ff4825364d101be904a6c9a203ed7864d934407da90c9b26880fe5d19364d101fcaa326c9a203bf386415344077e30c82a6880fec519054d101fe89b20a9a2037f2094da744067cc52c34e880cfde59839d1019facb3073a203bd53660e744077e26cc04e880efc659809d101df8c9b013a203bf105e19744067eb27c32e880dfc825365d101cfabb470ba2033f5968e174406fe3312b20880dec6525641101bf944aac822037f193e1904406f63294320880dfc64e8641101bf924b0c82203fb24961904406f6492c320880dfc8e58641101ff114b0c822037e22961904406ee32a4320880dfc4e48641101be89c90c822037e12921904407f630da320880deca634641101bd8c9e8c822037f19891904406f63292320880dfc64e4641101bf114a8c82203fb15951904406f6472a320880fec4e54641101fd114a8c82203fb15651904407f670ca320880face194641101f584328c822037f1988d904406f63291b20880dfca2536411019f944a6c822033f0894d904407f66929b20880dfc9253641101fd8a4a6c82203fb3464d904407f628c9b20880efca1b8541101df8c370a82203fb146e1504406fe32dc2a0880dfce598541101df9c330a82203bf286615044077e30cc2a0880efc2198541101fd8a330a82203bf39661504407f630da2a0880dec65b4541101bc8c9e8a82203fb38651504407f650ca2a0880fec6194541101fd84328a82203fb1464d5044077e30d1c20880fec51a3841101bf8cb470822037f3964e104406fe32c9c20880efce193841101df8c327082203fb3464e104407f628c9c20880ff44d93841101fd8c3468822037b1968d104406e632b1a20880dfce593441101bf8cb26882203fb2464d104407f628c9a20880ff44d93441101fd9cb268822037b3964d104407f652c9a20880fec6593441101bd8cb26882203fb0964d104407f670c9a20880feca193441101fd8c326882203fb0864d104407f226c9a20880fe48e13441101
  | 1 => 0xc815f28e55841902df4ac49083205be9959210640bdd4d2a420c815ba9a54841902bf51ca9083205bea585210640b7d2b0a420c816fa5223841902bf4ca47083205be9484e10640bdd492ab20c815ba9255641902f75242ac83205ee9485590640bdd2b12320c815baa624641902b74c9c8c83205eea585190640bdd2b0a320c817aa9214641902f751c28c83205ee9385190640add4929b20c817ba5253641902f74a426c83205eca384d90640b75a69c328a814fb64f8651502df5c4a0ca2a05be1068614540afd321a326a815fa642464d502af73ca8c9aa057cd391193540abdaf22326a815f9464464d502bf48488c9aa057e9909d93540afd412bb26a815fa925064d502f752320c9aa05ee9464193540b7d68d0426a816fa91a084d502df4a34109aa05be8468213540b7d4ed0426a816fa5da084d502d7734b0c9a2059ec796193440af5321a3268817abe19464d102f67c326c9a205beb894193440b7d31283268817ea525064d102fe49ca0c9a205ee9864193440b5d30c83268817aa519064d102f649b20c9a2057ea094d67440b7d26ac04e8816fa655809d102df4c9b013a2057ea094d57440b75a8d1c2e88167b5da385d102df483470ba2053ed968e17440afd512ab208815fa64f8641102df4caf0c82205be993e190440bf5492c3208815ea9258641102bf51cb0c82205aea696190440b7d4b2c3208816fa5658641102dd524b0c82205bea396190440b7d272c3208815eaa634641102bd4c9e8c82205eab865190440afd5129b208817ea5253641102df4c370a82205fa946e150440afd32dc2a08815fae598541102df5c330a82205be9866150440bf568cc2a08817ea5198541102bf10cb0a8220578993d150440afc432a2a08815eae594541102fd5c328a82205fa9865150440b7d70c9aa08816fa6193541102fd5a326a82205fa9464d50440b7d30d1c208817ea51a3841102bf4cb470822057eb964e10440afd32c9c208816fae193841102df4c327082205fab464e10440bf528c9c208817f24d93841102b94cac6882205fab964d10440af572c9a208817ea6593441102bd4cb26882205fab864d10440b7570c9a208817ea6193441102dd4c326882205f89364d10440bf14709a208816f24da085cd029f4cb410b9a05bc9348217340a7d329042e6814fde4e48559019fac9c90ab203bf196603464077e326c068c80cf98a584919019f904b07232037f2094e1464077cab11428c80ef94e22851901df2cac50a3203be5938a146406f6c92ab28c80ef98a15651901df094a10232033e62961236406deb2da426c80dfc643484d901b7b34a909b2037e62952136406fe412a426c80efcd22084d901df8a44109b2037f194821364077e5290426c80efc652084d9019f8ca4109b203bf197821364077e411a326c80df564
  | 2 => 0xbb2da426c81df6643484d903b6f34a909b2077ce295213640efb412a426c81ef6522084d903aeecbe8c9b2077ce295193640edf32da420c81df664f4841903b7d34a90832077da395210640efd452a420c81df66523841903afccbe8c832077d993d190640edf3292320c81db664e4641903bf514a8c83207ed9395190640fdd452a320c81fb68e14641903f6da326c83207ed9464d90640fdb6929b20c81db69253641903f6ca4a6c83207edb484d90640fdb2909b20c81d7b8a5465d503aee9c88cbaa075ed291197540ebea32232ea81d7e424465d503becc848c9aa077ce295193540ebbaf22326a81df34a4464d503bea8c88c9aa077d9091193540fdb48c8326a81fb6519064d503becc9e8c82a077d9939190540efd452a320a81d7e5e44641503bec9c88c82a077e9291190540efe2322320a81df69253641503fada326a82a07f5a464d50540feb28c9aa0a81fd61193541503c7fc350cba2075bd94a197440ebbb27432e881d7e642865d103aef1cb0cba2075ee296197440ebf412c32e881e3f9a5865d103cef1cb0cba2079ee296197440f3f412c32e881e3f618865d1038ff4c10cba2075ed292197440ebea32432e881e3fe1a465d1038fecc48cba2075bd949197440ebbb27232e881d7e642465d103af714a8cba2078ff865197440fb5c52a32e881f2fe19465d103e5e4328cba2075dc894d97440f9bf0c9b2e881f37219365d103ecfa326cba207d9d464d97440ebf112832e881f3ee19065d103e7c4320cba207dbb464197440f9f48c832e881f3e519065d103edca320cba207cb9464197440fbb26c832e881f364d9065d103ecea3470ba207dd9068e17440ebbb2d1c2e881f6e51a085d103eec9b410ba2075f9968217440fbb471042e881de7652864d103becc850c9a2077ce296193440efb412c326881eb79a5864d103de714b0c9a207bda096193440f5bb0c4326881cf7a60864d103be69490c9a2077d5192193440efb2124326881eb7e1a464d1039eecc48c9a20779d949193440ebbb2f2326881df6642464d103be714a8c9a207adf865193440ff1c52a326881fa7e19464d103f4e4328c9a207dda095d93440fb3e8cbb26881f67519764d1039ec44a0c9a207f9b494193440ff32928326881ef6e19064d103f6d4320c9a207ed9864193440f7b30c8326881eb6619064d103fcda320c9a207eda464193440fdb28c8326881fe6519064d103f4ca320c9a207bdb864153440f7b30c82a6881fe6d19054d103fcca320a9a207bd9868213440ff328d0426881df665a084d1039f7c9c90ab2053ed939215640b7d32ac068c816fa64d80d1902df4cab0123205bcd954e04640b7d32a8408c816f84650811902b7734a909b205be9956027640b7d2091c2ec814fb652385d902bf4ca4b0832057e1919610640afd492ac20
  | 3 => 0xd9754123fd303b2ea825774e4765d504af6948ecbaa093be98d197541357f0ca32ea8272f1d9465d504d7dc320cbaa09eb946419754133eeed0c2ea8267d9da185d504cfabb430baa099f4768617541376a8d0c2ea826fc41a185d504cfb0c70cbaa099be34e197541337a69c32ea8247fe4f865d5048fec9f0cbaa098ff8691975412bdc52a32ea8263fe19465d5049df44aeda2a09ab90661b4541373aecc1e8a826e641983d1504bd714a8ca2a09eba4641945413d728c8328a8267ddda1851504cfabb430a2a09bb546861454137e20d0c28a8266f8df8651504cde9bf0ca2a093bd93e1945412f73213b28a825eb8a57651504e5ebb0eca2a0979d391d945412f5a523b28a826eee190651504f5dbb20ca2a09eb87641945412bdc52bb26a827ae519064d504adeca4ed1ba091fd989da37412bdc52bb46e827ae519068dd04adeca48d1ba095f99091a374123fb312346e8257b8a5468dd04ed714a8d1ba09dbb4641a374139f48c8346e8273e519068dd04edca320d1ba09cb94641a37412b7b294346e8257e426868dd048fec4d0d1ba098ff869d937412b7b293b26e8257b8a5764dd04c7fc32ec9ba091fe981d937412bda523b26e8257d464764dd04d5fc328c9ba09cbf76519374135f70c8326e8273edd9064dd04e7c3b20c9ba09eb94641937413db26c8326e826ae419868d104d9ebb30b1a209b3906616344127f412c3268825778e5764d104bd714a8c9a209abf865193441397eeca3268826be619064d104f5d2320c9a209eb94641934413db26c83268826ee51a084d104dec9b4109a2093f99682134413b3a8d1ba688277641a374d104aeecb46e9a2093bd98a1934412b7b2f43268825e764e864d104bdcc850c9a2097ae2961934412f7412c3268826af9a5864d104dd714b0c9a209bba096193441357b0c43268824efa60864d104adfbc90c9a2097ad2921934412f6a3243268825ee424864d1049decc4ec9a2095bd979d934412f3b273b268825ee642764d104bcf1caec9a2097ae295d93441397cd2bb268827678e5764d104ed714aec9a2093be981d934412b7d2e3b268825e74e4764d104bd6948ec9a2097b5191d934413d3f0c9b268827a7219364d104ecfbb26c9a209d9d764d934413f327283268826eee19064d104f5d4320c9a209eb986419344137730c83268826ae619064d104f5dbb20c9a209eb87641934413f326c83268827a64d9064d104ddcc34109a209f993682134412f732d04268827675da374d104fcc8346e9a20979d968dd34413f34111ba68824fb8a58491903cf6bc450a3207bcd388a14640f3db2f1428c81ef364e2851903a7ecb690bb2075dd93d217640ebf321a42ec81d3f9a5485d903aef1ca90bb2075ee295217640ebf412a42ec81d77652385d903aeec9e8cbb2075ee295197640ed
  | 4 => 0x699f776861754d33eced0c2ea9a67d5da185d534cfa3b430baa69bb546861754d37aa6d0c2ea9a67d863865d534cbe82f0cbaa699be04e19754d337a09c32ea9a67740f865d534cf68170cbaa699f501e19754d23ff21c32ea9a47f643865d534c7fc348cbaa695ee29519754d31ff0ca32ea9a4efa2576d15349cf44a6da2a697ae29519454d33eeed0c28a9a67d5da1851534ddaa3430a2a69bd536861454d367a0bc328a9a66f81f8651534dce81f0ca2a693bd90e19454d2f3b273b28a9a5eb8a57651534e5ebb0eca2a697ad291d9454d2f72123b28a9a6e7e193651534f4fbb26ca2a69e9c764d9454d2bdc52bb20a9a6e7d1a3841534dcea347082a695bd949da074d23fb313b40e9a57b8a57681d34adeca48d03a695dd9391a074d23fb312340e9a57b8a54681d34ed714a8d03a69d9f464da074d3b3a8c9b40e9a56f6528681d34aeec9d0d03a691fd89a1a074d2bdc52c340e9a67b8a58681d34c7fc34ec83a695bd949d9074d2bdc52bb20e9a63fe197641d348ff4c0ec83a695ed291d9074d2bea323b20e9a6afe194641d34e5fbb28c83a69cbc76519074d35bf0c9b20e9a737dd93641d34e6e3b26c83a69cfa76419074d39f2ec8320e9a7ae5190641d34f6c9b20c83a691fd939e156812bdc52bb26b0247f64e78559049fcc8490ab2095f6196177641375c91142ec8256f925585d904aef1cab0bb2095f61956176412bf412ac2ec8272f9a2485d904afd04a70bb209cee688a1764133dcb1142ec8267b562285d904ed724450bb2099ee388a1764133da71142ec8263fa25761d90487f44aec3b2091fd93a1c7641373a929c0ec8247f8e58791904bdb0cab0a32097ba0956146412f74129c28c826eb5622851904dd69c450a3209eae28dd946412d5a523b28c825ad4647651904a7ecb6f09b2093bd949e1364123fb293c26c8253f9a5784d904b5ecb6909b2093f99092136412d7cd2a426c8257764f764d904aef1caec9b20979d93d1936412fe3232c20c825ee9255841904bed1cab0832097f1191e106412e732a2420c825eea5c4841904bcc9c890832096b99495906412df492ab20c827ae9215641904f5c242ac83209eba48dd906412df327bb20c825bea607641904b3cca8ec832096f9391d906412db2723b20c827ae55b4641904bdcc9e8c832096b99491906412df3272320c827ae9214641904f5cab28c83209ebb7651906413d72b2a320c825ae8e54641904f5c9ca8c83209eaa2951906413d74b0a320c827ae5614641904f5c3c28c83209eba3851906413d7270a320c825ae6523641904f5da326c83209eb9464d906413d76929b20c825be9253641904f5ca4a6c83209eda384d9064123fb133b6ea8257b8a576dd504f5ca320dbaa091fd8991b75412bdc52a36ea8263fe1a765d504af714aecbaa098ff865
  | 5 => 0x14b092320b5de395e1464173def11428c82e7b5e22851905db6ac450a320b9ee978a1464173db2f1428c82edb6562851905cf7146eca320b5bd94dd946416b7c92bb28c82d778e57651905cf7142eca320b73e49559464176dc50ab28c82e77a5d3811905ceecba702320bb5d954e0464177b2129c08c82cfe8e50811905df494a102320b3ee2961236416afb2b2348e82d7b8a54691d058ff24b0d23a0b8fe4661a474171fa8cc348e82d7764f468dd05aef1ca8d1ba0b5ee2951a37416bba722346e82d7b4a4468dd05afa8c88d1ba0b5f90911a37416bbb291b46e82ede40f86515059bec9f0ca2a0bd7618dd945416edc52a328a82ddb8a5464d505bae9c88c9aa0b76d2911935416eea322326a82dde424464d505c7e834f0ab46993d459e1568d32fa0b3c2ad1a47f4267855a34e5ca320cb84698fd069e1564d32fa0b3c2ac9a47f64278559349eec9c90ab2695de3955b764d2bec32c2eec9a53f643769d934dd724450bb2693ed908a1764d29fb21342ec9a56f925585d934aef1cab0bb2695f619561764d2bf412ac2ec9a72f9a2485d934e7734450bb2699ee588a1764d33dab1142ec9a76b922285d934af6c8450bb2691ed908a1764d33dc51042ec9a67be4a085d934aef1ca10bb2699ee28421764d2bbc72ab2ec9a63fa25761d93487f44aec3b2691fd90a1c764d31faec840ec9a4f74e5081d934c7cbb2103b269bb949420764d37b272840ec9a6fc465081d934bcf1caada32694fd90dda464d23fc12c3c8c9a4f782583919349f6c8450a32694fd90dd9464d2f3c72ac28c9a5ed8655851934dd6ac450a32697ad908a1464d2f3c728428c9a6eb8a10851934bcf1caaca3269eae28dd9464d2d7b21bb28c9a5ab4a47651934b5a8c8eca32696bd091d9464d2d72123b28c9a5e7925584d934bcf4b8909b269e9e48559364d3d3890ab26c9a7a7923764d934b6ec86ec9b2696de981d9364d2cbb2a3b26c9a5b7424764d934b6c848ec9b269b9e08d19364d3d3aada326c9a5e7643464d934dcf0428c9b269e9d56519364d3d3eeca326c9a63fa257681934a7ecb6f0832693bd949e1064d23fb293c20c9a53f9a57841934b5ecb690832693dd93921064d2d7cd2a420c9a6e7d213841934dcea4270832695f990dd9064d2d7b293b20c9a57e8257641934e7714aec83269cfa095d9064d2f7321a320c9a53f65e4641934b5eca48c832696dd93919064d3d5c52a320c9a7a74e14641934bed04a6c83269e9f464d9064d3d3a8c9b20c9a7b68253641934f4fa426c83269e9d484d9064d23fb133b6ea9a57b8a576dd5349ef44a6dbaa691fd8991b754d2bdc52a36ea9a63fe1a765d534af714aecbaa698ff865d9754d23fd303b2ea9a57b4a4765d534afc848ecbaa693be98d19754d357f0ca32ea9a72f1d9465d534d6fc326cbaa
  | 6 => 0x55a06a7f3ca909b40d1fd939217581a3fb132be8e8356f92557d1d06aef1caafa3a0d5de3955e4741abbc72c2c8e834bf64e6851d06d7734450a3a0d9ee2895d4741abeb232ba8e835778e55751d06cf7142aea3a0d1fe8955c4741abbc72ab88e8366fa254711d068df44a8e23a0d9dd574e04741b33a8e9c08e8367b55d2811d06cfaaba3023a0d1fd98d1e3741abdc52a3c6e8357b8a5848dd06cf714b091ba0d5ee2951d3741a5fd12a3cac836be40e485590697ec9c90ab20d6ee2951d5641a5fd3023aac8372f51c4755906b6e9c88eab20d6ed2911d5641adea3223aac8347f62657d19068fec4c6fa320daf9566034641a7f726c068c835b78e5579190697f44aaf2320d9ee2895d4641b3dc511ba8c836bb8a15651906b5f24ab0a320d6f6195614641adf412ac28c835be8253851906d76ac450a320daed388a14641adeb232ba8c835af9255751906b6f1caaea320d6fa0955d4641bd5c5123a8c8372f55c4751906b4e9c88ea320d6ad2911d4641a5fd12a3c6c834fe652084d906aeeca46e9b20d6ee295193641b5f410a326c8353f65f484d906b6ec9e909b20d6f990d213641addc52a426c835be825484d906d7ca44109b20d6f9948213641a5fb31a3a6c835b764f474d906b7cc868e9b20d6de3951d3641addc52a3a6c835b7652374d9068ff04b07bb28b9dd0360f765163ff26c06eca2c7f64d80dd945c7e83490bb28b97d05921765163fb27242eca2c7f642485d945ed724450bb28b9e6188a1765173ca03142eca2c7b642285d9459f6c8450a328b97e58de1365172fcb1bb26ca2d7764f764d945afcc86ec8328b5f59391a17516beb212342ea2d798a54685d45afb24a6d0ba8b5f64941a175179ec8c8342ea2f3d5190685d45cfb233010ba8b9f546602175173ef2cc042ea2e5f962485d935cef1c490bb26b8fe06921764d71fa0d242ec9ae5f416485d935cee81c90bb26b9ed02921764d73ea03242ec9ac7fe42485d9358fec8490bb26b5bd94ddb464d63fb13bb68c9ad6f92576d19359f714b092326b5fa095e1464d73def11428c9ae7b5e22851935cf74bc50a326b9ed978a1464d67db211428c9ae7b8a37651935adeca6eca326b5be495d9464d73dc50bb28c9aedb8a156519359ef04a702326b9fa97420464d73f32e8408c9aede6550811935dec9ca102326bbe929420464d67dc52c240c9af578e55691d35abecac8d23a6b5ee2951a474d63fc92c348e9ae3f9198691d35c7ea330d23a6b5ee2951a074d6bf412a340e9ad774e44681d35af69488d03a6b5f51911a074d6bf2122340e9ae778e2485d905cee1c490bb20b1ff93921764163fb27242ec82e77e52385d905dbc81c90ab20b37d93921564172fb0bbb68c82d6f65376d19058fec4eeda320b5be495db46416bbc72bb68c82dcf92556d19059f7
  | 7 => 0x558c94190e31c062c8c4c188830f061a0c27183e30706050bfd17ea2fc85f50bc417642e6c5c70b8116ca2d3859e0b2a16122bf05750ace15962b205600abd156a2ab45500a8e14f8298052e8a5a14ae29285120a21141e281c4ff89fc13e827b04f489e113a827084df89b7135e26884ca897e12d825544a40922123e243448288f811d6238c46b08d31196232046288bd112e223c4410848107620cc41087fb0fdc1f983e787a40f1a1db03a3072f0de01b14359867e0cd8191830d85fa0bb216e02d305940ae615482a005150a2413ec26a84c3096c127c246847608e611ac22c84420860108c20883fa07a80ee01d0839406d20c94187030105de0b1015e02b405440a54144027104c80970127823d045608640f701a5033006040bc815d02a0050c0938124021a038805e00a50130021802d802b00008decc68f23aad5de3941e4755aaff2ac1c8eab65fe558391d568ff04b0723aad9dd0360e4755a3ff26c048eab47f64d8091d56cfc81b0123aad3bd9392156d1a77b21242ada35778e5565cf468f6c8450ba48d5de396157091b76c910c2aea34fd6421855d46d5f344909ba8d5f61955d3751bb5c92abc4ea357b8e55789d46ef30caaf13a8d5e61955e2751abdc12abc4ea373b9a53789d46af72ca6f13a8ddae494de2751abdc129bc4ea367ba253789d46cf6abb0113a8d9ed376022751b5df2cc044ea36ebe518089d46af71cb0b13a8dde6196162751abcc32c2c4ea357b8258589d46af7cab0713a8d9ed8560e2751abdc12c1c4ea357be558089d46cf6c2b0113a8d5ef936022751b3db06c044ea367be598089d46cf7cab0113a8d9ed956022751b3df28c044ea367be4d8089d46cf6c9b0113a8dabe689210751abec32aba0ea373b9a22741d46cf72c44e83a8ddae4889d0751b3dc7113a0ea34ef64e48559469dec8490ab28d9ee3889d5651b3dc1113aaca357b6422755946aef04b0a9b88d9dd858213711abbb2b0426e23677615084dc46cf6c2a508388d9e5284610711abf472c2a0e2367e6163841c46afccac708388d9f9854e10711bbd30a9420e237784a11841c46c7e83490bac6d97d05921758db3ea03242eb1b47f642485d6368f6c8450ba46d1fd8995f474dab7c92abe8e9b5778e58591d3697ec84d0a3a6daee688a1474da7db211428e9b67b8a25751d36cf7142aea3a6d1fe8955c474db37d12a388e9b46fa254711d36a7ecb68f03a6d1fd98d1e074dabdc52a3c0e9b53f65a8481d36aeec9d0903a6d5ee29612074db3dc52c240e9b53f65b4741d36af714a8e83a6d2fe8951e564db2fcaf242ac9b6778e24755936b7714a8eab26dcbd4711d564da3fb132be8c9b47f62607d1936cef03b07a326dadd5660f464da7bc12c1e8c9b4fb6422851936cf7144aea326d9ee2881d464db5dc50ab28c9b4bf64e48
  | 8 => 0x55caa5d54a2a875508a9c95302a53548ca8e551629f2537aa6d54d6a9a05330a6414c4298552faa5d54b6a96552baa5554a4292c5248a42147128da519aa301459a8a6513ca20943aa85e50aca14d411a82050129fc93eda7ab4f289da53a427314e2a9bbd36c26c64d369a61340a6794cec999132ba6544ca298fd31e26344c6298a5310a60f4c0e97fd2fba5ef4bc497692df25bb4b7096c12c2a5784ae095b52b525674ac895852af254c4a8894f128b24ff49b2931d25fa4a34936922523ba46f48d891a5230a45e48a29139220a4344858907d209240f480e9011200a3fe47e28fb91f5a3e847ca8f891efa3dc47a88f311d5a3a8474a8e891cfa39747288e1d1bfa37c46f28dc51b7236646bc8d4519aa32345fa8b9916022b345568a79148a289450289f9133a25f44ae89511262249448c890d11b222944428879108a209440287d10f3a1df43ae873d0e121b0433c86450c2217c42f285d90b4a16642c685590a72146427284b108d2112420a83f507820e341c08375065a0c34130822d03f207b40c8817102a2047408880f101a202c4052808500a201140128004ffc9ff13fd27f84fef1fd63fa67f2cfe41fc53f847ee8fd91faa3f447e68fc91f8f3f187e10fbe1f743ed87d90fae1f593e5c7c98f879f0c3dfe7bc8f6b1ebf3d3c79f4f381e593cac7938f259e483c8078e0f181e283c407860f059e033bf677a4ef09dd93ba27710ede1db43b58767cec69d7b3ab4755cea79d473a7e74dce9a1d2c3a3e745ce879d0739fe73f0e7c9cf639e67398e6f1cd6399c732ce5f1cb6395c72ace541ca039307240e441c8538f071ace319c5b38a67118e129c1d37f86fe4df89bee37cc6f78ded9bd837aa6f34de29bbd376a6eb4dd01b9d372a6e34dc29b7d36f46dc8db79b6736be6d5cdaa1b5136926d18da19b3b36666bf8d7b1aee35cc6b78d661ac4353c6a58d471a8134f2694cd231a393458687cd091a0a33fa67e8cf699e033b06740ce419c0332a6634cc2997832d6653cc94991731ec63b8c7318ca31486248c42987330cc6114c19982130005fa4be697c52f205d94ba997412e185bd4b7196bd2d4c5a28b3496662cbc5958b1816282c405860b0596032bf657ccaf595e32bb65738ae315b92b4e5654aba15622aaa5534aa2951a2a2e5450a88950429e45380a6714a828dc5120a1d9433284c5078a08940e28164fe49fb13ee27b84f509e613b0270a4dcc9ab934f26664c4898012e4255449e89251247247448c8912920923ee47bc8ee91d0237c46748ac912e221043c486a90cd218042cc855909e211841d48319051209240f0817901d20163f087da8f8f1efa3d707a00f1a1df23b2474f0e731ca438ec70d0dfe1bf637b86ee0dd41b7a36986cc8d871af435b46b28d5d1ab434bc6898d0b19fc33d86770ce1199e32f46
  | 9 => 0x310cb80c20b0cb724377855038cb7250780d032070778181540e130cbf258025de06055038cbf2585c0c8f321e62bcc27974f2dde57bcac7948f271e4cbc96791cf1f1e3cbc7178d2f199e2cbc51789cf105e1a3c1d782af049e053bfd77e0ef79de8bbbf775aeea9dd13b957706ee01dbc3b7076d0ed6dda9bb4b7686ed01d99bb2b7650ec95d8ebb107606ec01d79baf075daeba9d73bae475c2eb79d6dbad875a0eb21d513a9f752eea51d463a8474b2e945d273a4b7490e8b1d123a1c7432e859d073a0b7410e815d0139f573bce76dce4b9c67386e701cdeb9b5735ae6a9cd3b9a47342e665ccb39937302e5f9cbb397372e0e5b5cb5396272bee571caa3951729ce52dca439457284e4d5c96b925723ae455c8438e271aae2f9c5b38907110e201c37386b70d0e181c2eb85570a4e13dc21383a706ee0a9c0eb810701adfedbfc37f56fe4dfbdbf137df6fa4df15bdc37ab6f3cde45bc2377c6ee8ddb1bb237576e9edc7db72b6dd6daadb35b6036b86d56da8db5036936d0cd9f9b36365f6caed951b26363f6c64d8bdb13b6246c42d865b08b6096c0cd7f9af8b5da6b90d701adeb5ba6b64d6a9ad3b59f6b24d63dac3b57f6ae4d5bdab3b5646ac2d579aadb5586aaad549aa535426a7ed4f1a9cb5366a66d4c1a9435256a1cd42da7cb4f669e6d3ada71b4e069b0d355a6934cf6984d2e9a5934af6958d2a5a5334a36940d261a4ab48d6914d21da42347c68f2d1b1a34b46168bcd16da29b450689ad129a23b4446878d0d1a1634296824d015a0133f067d0cf959eeb3d5679acf159e133ba676eced19d3b39f672ece299c1337a66e4cdbd9b6336466b8cd519a8b349668ccd0d9a0333d6674ccc9997b3226634cc3598032f365cccb65954b29c6514c955929324f6498c8fd91e3239646cc8b9915b2286440c8619083208640ac7f58fd31e863c0c7398de31af634ec67d8cbb18f6304c5c18b6b1516292c48d88b31096202c3f987db0ee61d6c3a1872b0e261b4c349862b0c2616ac2c9857b0a760d0c0917ff2fce5f8cbef97d8afa95f42be657c8af6b5ea8bcb9795af1e5e2cbc4d780aef45dd8bb9176e2ecf5d8ebafd75baeb45d58ba7d74bae8f5d04b9d5731ae605ca6b92d721ae3b5c66b8c17142e165c12b8056fa2df15bd2b75d6ea2dcc5b92b7056dcada75b3eb65d6c7ad8c5afeb5f16bcad765adcb50d69dad335a60b4b56952d275a3eb45d68a2d115a1cb42d67f2cf659dcb30d65b2cb3594cb27964b2c8e5916b2216402c7858d6b1a162dac4e588cb0f961b2c335860b0a1612ac135820b0356052bf857eaafc95f7abec57d2af995ecabd6579caf2d5e1abc05766aead5d42ba55744ae695cbab945718ae115be2b6f56c4ad415a42b455684ace959bab2a5644ac695892b055604abd55742ae555a6ab19561aabb5
  | 10 => 0x589c0c20610300c30b018b2ccb1055036cb0c31224810ccb04cb62420c6cb08ea036cb0cea0600d0c341a5de060171560db2f0ae27c501303308e154cb083406217b2f0a028c21c3405d0a0c3485ecb028033086062cb32e0300c50d3de06217956cbf1470b017b2ccb6260318340cc2cf7a17956cbe27c52434778181540e32fc56048778181540e32fc57170321344ac130394b02864d013d2c03113445c130394b02864d11704f4b00c5005e00c20b057724372c18a655e1783126ab2c0510841c3c90863459870c5360c245987098304050409aa2906255f2dc9e1683226a15f4be17831405048300c20141e0c120c0308707780e0c70061c90c7020c030c707780e20c41c1c90870f240710847781103805107092c201410341c0c11c2c9085504012c49104392c05080504090810a4201799601e4210870805e10830a45ef2507105e1082d78c90a29d7b07c170314ea5785eb244178c910830805e10830995ea5a075084218651082195c910831cc16157c921050000141007004050449e0c215f85e0c31c3c900c31c3c9015831085000006a0342f781805855d2fc93087004900c410c4b04050400141d2c1001604709a821c00e92c3000e0455045512c2178420820179491084b794b3083280de5544c107092c287fde95707e17838007004900c410c550470060215dc909cb045e10820019040000404eab79161540e01c031c04045503421d0733a818157c901c85c0c03308b72ccb08030418f24850c310b01801c8500cc21c2c32c2324115f07e170310ea03bcbc1f85c0cc2108806055035cb10ea061cbc1f85c0c63a81815fcbc1f85c0c70b0577240310310b01906055f2407e1585c0c03308cf78180585572fc901cc22057325030c741ccea06016157c901c03308a4340d32c38a65572707e1705c0c71d02977816f25c941cc220741540d72c0730861d07072fc972503187385a5572707c0c67785530833aa0300c33a818157c96170318741ccea06055f2460b05732431ccea156cbf240700cc22001c2cb014421070062cb01f0300c421c700600e0f0300c21d070155031070062cb0c741c055b2c401c9041840c030c2c378041084080de1543a144208dea14420cde7268510843795572dc9a150310873a82005a8540c537b859084210577242082de060161540ef24072074882de060161540e331cbf2707e170334de80c033084378c208de724c20c293785572dc941d03308830811c010610300c30b0cb085503420c47015cc9107032c232c10c6cb08ea036cb0cea0600d0c3115dc90c1805855036cbf240730881d0297781805855836cbf2707e1404c0cc23acb32c21c0573240310cb04743aacb32dc914181542154cb0818b2fc901cc21401d0707250310741c2cbf2407c0c033088778161540e32dc941c7060cb80c
  | 11 => 0x9a0c03508806003080e20c200300b01d060407410741074170800601060160c10014041360c2018304050405040504050405040014100030400000741e0c10741060100c1c0c100006010601e2c1060102c10341002a0610d62fc9c0c033088c2c10cc31f25031000b003080d22c20cc31a2dc980c57780ec0d0310310600da2fc930860cc31075c9c0d03188b80c20cc1822dc9100054100005411081c0c10781c0c1c0c140c4209420542042042c420c42070b041e050b1082c2c1c2c11081094420825080420c25724420c250800d725c5108600050405040504050400141f240508050409040505c9040000000900420a8100c102c102c901428a810741000074103810a810a81001803420380d082a042a042a042ae2c20a81d0378bf2484182a042a074180380df246001804007410741000000307830403041d0783041d00c2000307830783058304000c10003040d0703040001d04000150415042c0760d0370bf27c5a0c03108a074142c100c107410c41d20c300c10cc31077c9a0c035087074107410770b082c04330b01d8340df24841c201082080420a0b308282cc2082c0742074107403080178030856714272c172c160c11a419a86906255f2f8971683204505cb042f154212c01082cb78de06004142cb780ec2b8941f031c20b78d50e20b780ec2b89c0c672c172c10cc2ce25c531450b01802bc5314033087061cb32c3a25c508de72e890c2c62420b018b2ccb02881183132d890c6a37a040ede0619702a04308637a0300cc2102b3798980cc215cb04310b86a0600af15c5c0c03308a0d02c1a818a5dcb028c221c580c030c20355cb0c330c42c9a86a35789f15c5c0ca0b0d580c0310313540d0c340c41865ecb028c21c340c42b42840ac1832d8980c50b06a038cb7170318000c101014d35e0498a6264660c719411941c0c117b030b0307030465046504650465046a50825081194040865578040c65228040c655794b229c501061955e010319442084504010434f781805c55d2fc560c8000010940420b34b52c30b15503430d0311a830d031c5f4b0280350870d0330b06af79175574bf1484c04b0d0310b06a0394bc0471940408650456714272c106c42080006a0710a0c001011540d72c3714172c10cc18e25c531450c42c0600af14c500cc2202c72ccb0c3306389f15c51789051772f89625c514330c42ce27c571460b1cbe2430c51772f8962450c42c06c181540af15c5c0c03308b0d3de06017155cb02bc530890ccea0625515789f15c5c0c900341542624140c03082cb78de060041420b78550ec504de626c50c56b1423a820b143b785604b0ae27031834882de060171540e331cbc2b89f17033634b7a5504b0ac25c5c0c81a6de0621702a04308737a0300cc210de05d8980cc2146504654242154c208c20
  | 12 => 0xd04350cc2af781d05f15e2dc9f14c1204c0d0331b42a0a7de07416c578bf25c5300d0d01d05c16e2fc9f1470d0330abde07715e2fc9f149b781c2c182cc208c2041d041d070b04300a80ec2fc9f14c21c34077c9f1440d0300a81dc2fc9f147010b30820d01021542cc20e1582c2f241014101410240108050434040504005412548b08050434040520420d34308340cc300c00d00308340434043304950400d010d09522c30c02a0834043422c2035e045e0300b0c0d78103450405041e014000f450745078b0400a74508000072415799562dc9315c340800218b0595040000000304030400000216c142014102c1d785e074150380bf27c5238bc2c20117624262c145410a410000a411781e2f0b080e2f0b0b8bc2c297815081508100022c1000900c010c00000240300430000000000240108002410003040b240508030400000741000074103810a811a843086a07421a81d034307810000141003371420141f241f24125c0508025c0508337142002372dc50c33714200130434f2420d3c9f17831000d1830808d016e0c30a017058307417083360c20cd83083385420cc2a06c1805f15727c5e0cc1204b0d0330a82906418c57c9e0cc0280504050409004201410d010141000504050434072a0420072a042c71420601503b033085c0c10c42c06015c0c50a820b780ef27c500c7308100cc2090330820600308180342c0c10b02a03b0330850600d082c0a818c0c4308100340cc95057c9f170300cc22402570380c03103677a1530848570380c0310360d02877bc9725c540cc22434035cb30840d030075cbf25c9c0d0320338aa15727c5c0c68a9c580c0310368a820255cb14340a815725c580c031e2a0aa0300c40c09503430cc2a036cbf270300cc22000d030b2d03100e0400d03040c30b02a080009520c030c08a4103450405041e014000f450745042904280429254208011a82808095d14500072415799572dc93158340800201660c265410000000008a616c14301410d010835e0540ef27c500c70d03305dc9135e0601503bc9f15831e2905f030d420428d7815d15421534053445d890d34059830d15040002904005f030800d303081bc0c2508100d4208835082014204000020c0308000000000080c10a810c02cd2fc921283180000000b040b2405080b040001d0400341060103883086a0740dd2c83146a0600d0c150374bf27c500e421c340cc17724406015d2fc9f158390870144108050417c0c20d01d083404030400d01dd2e831283041d0401041000003400c20d003083404005f830817041d0434e0c20d01d0834043404340417e0c20d016e0c305c1660c30d003083402c20d0100005f030800033d2c20d010d010d303081bc0c20d019c0c307410d00e0834043402c24540d0800034074830c0304340c01dd2fc
  | 13 => 0xf27c5210300007810003040078102c10003781f15c3004300c507c90408d34908c504098cc50a33258208c96314c310c5040314104cc30833314208dc530c304cc3083385d490c3305d490c0314125a010896314c30c032c130c130c1714c308c304c3060104072dc50a0104000340634d2420cd450800cd4508000000000000030c14a41caa2946e19c57cbd0c7021604032c14a41caa2906315f2dc9b17432034040000cab8bf15c300450781808100071410000000d3c908340c7c9f144000900c010c000000090403040000030b040000900c010c022c1000000a2c100007810000000000cdc50ac50749074906cb041e02c2caa5e52f49d170380870d3c90834f27c5e0c432c10d0330b018f27c5e0c772c172c102c09004300002410034040002bc0c20d010034c0c20af030834c0c2000b024010c00000216a142002ba0c20d8340a34e0c20d857083015c20cd83083360c2c0c10d81c0c10d810ce2a0a2a04340cc310b32a057c9f178324330c42c0af2a055c9f1783304812c3404410481042bc0c20c010d00308340400af8308330ac20c010cc300ac30d00308340400cc10af0308330ac2000304000340429041e0407141421060b9e85dc570c4f15c30043e1410000141014100b40497858200b404b404b430c201c904000000000000c100c1000000000f24100274598560c40116615830c000050405040a2c1000002962c267810601000000000014100820400000541029e4082001e04000200400000000a418a41f24100244598b614408d830804598b614360c1000504050749068b040a0c10000a583099e04400629e782c2c10a418a4100001410541208100150400000000a410229c0c2c0c10a7030829c0c207f03081f40c20d10e0828055104390ce2e0bf27c5256a0a420790e02c30cc300a9150578bf27c51124328000017805080000714100001410141f241f24101c504008dc570c371413240970c3f15c300437240908090405040a04150434f2420d3c9f14300340778bf27c516c304340cc300778bf27c51c3462c2075950a2a04000090042000000e2c162c10cf8b0800ce8b080001
  | _ => 0
def g127D8 : Nat → Nat
  | 0 => 0xd465d103dbd465d103ddd365d103df9065d103dde385d103dfa085d103fdf864d103bdf864d103fde864d103fdd864d103bdd864d103fdc864d103f9f464d103fde464d103fdd464d103f9d464d103ddd764d103fd9064d103fd9054d103fda084d103be58195902be98095902fee4855902bee4855902bed83d1902be980d1902bed8391902be980919029ee7851902b6d8511902bed3811902bcd38119029ed7811902be51811902be90811902be9808d902bee484d902fed484d902bed839d902be9809d902bee385d902fea085d902bea085d902fea5841902fe95841902fea4841902bea4841902fe94841902fea3841902fe93841902eea5641902fe95641902ee95641902eea4641902ee94641902eea3641902fe93641902ee93641902bcd83d1502be980d1502bef8651502fe90651502be61851502fef464d502fee464d502fed464d502fec464d502fee764d502fed764d502fe9064d502bea084d502b6d858d102be9808d102fef864d102bef864d102fed864d102bed864d102faf464d102fad464d102fcd364d102fe9064d102fed359d102bed839d102be9809d102fed355d102bee385d102fe95641102feb8641102beb8641102fe98641102be98641102fab4641102fa94641102fe93641102feb8541102fe98541102fab4541102fe94541102fa94541102fe93541102fea3841102fe93841102faa3441102fe93441102fa93441102fea085cd02bea085cd02bf584959019f58795901ff64855901bf64855901bf583d1901bf180d1901bf58491901bf58391901ff55851901bf63851901ff53851901fe62851901be62851901ff55651901b758511901bf53811901bd53811901be528119019f57811901bf10811901bf5848d901ff7484d901bf6484d901ff5484d901ff5784d901ff2084d901bf2084d901ff7464d901ff5464d901b75859d901bf5839d901bf1809d901ff6385d901bf6385d901ff5365d901bf586d1501bd583d1501bf180d15019f67851501ff6464d501ff5464d501f715641501ff24641501ff14641501ff23641501ff13641501bf24841501f714541501f713541501fb5468d101bf5868d101b75858d101bf1808d101ff7864d101bf7864d101ff6864d101ff5864d101bf5864d101ff4864d101fb7464d101ff6464d101ff5464d101fb5464d101fd5364d101ff1054d101ff5369d101bf5869d101bf5839d101bf1809d101bf7865d101ff6365d101ff5365d101bf6385d101ff25641101ff15641101ff38641101ff28641101ff18641101ff08641101fb34641101ff24641101ff14641101fb14641101ff23641101ff13641101ff38541101bf38541101ff18541101bf18541101fb34541101fb14541101ff13541101ff23841101ff13841101fb23441101ff13441101fb13441101b77855cd01
  | 1 => 0x851904fbd5651904fbf7651904ebf7651904ebc76519049fe878d904bfd878d9049fd878d904bbd848d904bf9808d904dff784d904bfe784d9049fe784d904dfd784d9049fc784d904fbf484d904bfe484d904fbd484d904dff764d904dfd764d904fbf464d904fbd464d904ffa5841904ff95841904ff87841904ffa4841904fba4841904fb84841904ffa3841904ff93841904efa5641904ff95641904ef95641904ffb7641904efb7641904ff97641904ef87641904fbb4641904efa4641904ef94641904fb94641904eb94641904efa3641904ff93641904ef93641904dfe76dd504dfd76dd504fbd46dd504ff906dd504bfd86dd504dfe46dd504dfd46dd5049fd86dd504bff865d504dff765d504dfe765d504dfd765d504dfc765d504fbf465d504fbd465d504ff9065d504bf6185d504dff865d5049ff865d504dfe465d504dfd465d5049f6185d504fbd76d1504fb906d1504bbd86d1504b9d83d1504dff7651504dfd7651504fbe4651504fbd4651504ff90651504bf61851504bbf8651504fbf7651504fbe7651504fbd7651504fbc7651504fb90651504dff764d504dfd764d504fbf464d504fbd464d504ff9064d504dfe768dd04dfd768dd04fbd468dd04ff9068dd04bfd868dd04dbf468dd04dfe468dd04dfd468dd04dbd468dd04df9068dd049ff868dd04dfe868dd04dfd868dd049fd868dd04bff864dd04bfd864dd04dff764dd04dfe764dd04dfd764dd04dfc764dd04fbf464dd04fbd464dd04fdd364dd04ff9064dd04ffa084dd04dbf768d104fbd768d104dbd768d104fb9068d104bbd868d104b3d858d104bff864d104bfd864d104dff764d104dfd764d104fbe464d104fbd464d104fdd364d104ff9064d104bfa084d104dde374d104fbf864d104bbf864d104fbe864d104fbd864d104bbd864d104fbc864d104fbf764d104dbf764d104fbe764d104fbd764d104dbd764d104fbc764d104f9d364d104fb9064d104fba084d104f9e374d1049fd87d1903bdd83d1903bfd84919039fd8791903bdd8391903bf98091903dfd7851903fdd3851903fee2851903bee28519039fd7811903bdd3811903bed2811903bf51811903bf90811903dff485d9039fe485d903dfd485d903dde385d903dfa085d903dff465d903dfd465d903fdf484d903bde484d903fdd484d903fda084d903fdf464d903fdd464d903ffb4841903ff94841903fda3841903ffb4641903efa4641903ff94641903ef94641903fd93641903ed93641903dff465d503dfe465d503dfd465d503dfc465d503fdf464d503fde464d503fdd464d503fdc464d503fd9064d503ffb4641503ffa4641503ff94641503ff84641503fd93641503f593541503dff865d1039ff865d103dfe865d103dfd865d1039fd865d103dfc865d103dbf465d103dfe465d103df
  | 2 => 0x1934bfd8091934bee2851934cff7651934fbd5851934fae2851934bbe0851934fbd0851934fbd5651934fbf7651934ebf7651934ebc7651934fde584d934fdd584d934fdc784d934fde484d934f9e484d934f9c484d934fde084d934bde084d934fdd084d934ede564d934fdd564d934edd564d934fdf764d934edf764d934fdd764d934edc764d934f9f464d934f9d464d934efd7681934cfd7681934ebd4681934edd36819349fe8781934bfd87819349fd8781934bbd8481934bdd8381934dff7841934bfe78419349fe7841934dfd78419349fc7841934fbf4841934bfe4841934fbd4841934fdd3841934dff7641934efe7641934efd7641934dfd7641934cfd7641934fbf4641934efe4641934efd4641934fbd4641934ebd4641934fdd3641934edd3641934dfe76dd534dfd76dd534fbd46dd534fdd36dd534bfd86dd534dfe46dd534dfd46dd5349fd86dd534bff865d534dff765d534dfe765d534dfd765d534dfc765d534fbf465d534fbd465d534fdd365d534bf6185d534dff865d5349ff865d534dfe465d534dfd465d5349f6185d534fbd76d1534f9d36d1534bbd86d1534dff7651534dfd7651534fbe4651534fbd4651534fdd3651534bf61851534bbf8651534fbf7651534fbe7651534fbd7651534fbc7651534f9d3651534dff7641534dfd7641534fbf4641534fbd4641534fdd3641534bde3841534dfe7681d34dfd7681d34fbd4681d34fdd3681d34bfd8681d34dbf4681d34dfe4681d34dfd4681d34dbd4681d34ddd3681d349ff8681d34dfe8681d34dfd8681d349fd8681d34bff8641d34bfd8641d34dff7641d34dfe7641d34dfd7641d34dfc7641d34fbf4641d34fbd4641d34fdd3641d34ff90641d34fde3841d349fe7855a04fbd484da049fe784da04dfd784da049ee285da04fbd464d604dfd764d6049f6185d604bbf864d204fbd864d204bbd864d204f9d364d204dbd764d204dbd465ce049ff865ce04dfd865ce049fd865ce04ddd365ce049fe8795904bfd87959049fd8795904bbd8495904bf58195904bf98095904bfe78559049fe78559049fc7855904bfe4855904bfd83dd904dfd56dd904dfd85dd904dfd83dd9049fd83dd904cff769d904bbd849d904bfd839d904bfe485d904fbe485d904bbe485d904bfe385d904fee285d904bee285d904dfe685d904cfe685d904dfe585d904dfd585d904dfe485d9049fe485d904dbe485d904dfe385d9049fe385d904dfd385d904dee285d9049ee285d904dfd565d904cfd761d904b7d851d9049fe871d904bfd381d904bdd381d904bed281d904bf5181d904fbd56d1904fbd76d1904bbe87d1904bbd83d1904cff7691904bfd87919049fd8791904bbd8491904bfd8391904bf98091904bee2851904cff7651904fbd5851904bbe3851904fbd3851904fae2
  | 3 => 0x6ebc4751906efe3751906efd3751906efd478d906afd848d906bfa084d906dde374d906eff464d906efd464d906eff484d906afe484d906efd484d906efa084d906eff474d906efd474d906ede374d9069fe784db45dfd784db459fe7841b45dfd7841b45cfd065db459fd865cf45ddd365cf45ddd865cf45ddd065cf459fd865c345df9065c345dfd03dd9459fd83dd9459fd80dd945dfe485d9459fe485d945dbe485d945dee285d9459ee285d9459f6185d945f7e4855945f3e4855945bfd8391945bfd8091945bee2851945dff784d945bfe484d945dff764d945dff7841945bfe4841945dff7641945efe4641945efd4641945df64685d45df54685d45df63685d45df53685d45df60685d45df50685d459f58085d459fd84dd935dfe485d9359fe485d935f7e4855935dff76d1935dfd76d1935f7d56d1935bfd80d1935bfd8491935bfd8091935dff7851935dfd7851935fee2851935bee2851935bfe0851935dff7651935dfd7651935f7d5651935bdd3811935bed2811935bf51811935bfd0811935bf90811935efd4681935bfd8481935bfe4841935efe4641935efd4641935d7d5691d35dfe4691d35dfd4691d359fd8691d35dff4681d35dfe4681d35dfd4681d35dfc4681d359fd84dd905dfe485d9059fe485d9059de385d905f7e4855905b7e4855905dff76d1905dfd76d1905f7d56d1905bfd83d1905bfd8491905bfd8391905dff7851905dfd7851905f7d5851905bfe3851905fee2851905bee2851905dff7651905dfd7651905f7d5651905bfd3811905bdd3811905bed2811905bf51811905bf90811905bfd848d905bfe484d905d7d5691d05dfe4691d05dfd4691d059fd8691d05dff468dd05dfe468dd05dfd468dd05dfc468dd05dde368dd05b7f8651505d7f7651505f7e4651505f7d4651505f7f464d505f7e464d505f7d464d505f7c464d5059fe7855a34fbd4841a349fe7841a34dfd7841a34ebd4641a34cfd065da34fbd4641634dfd7641634d7d065d634dbd465c2349ff865c234dfd865c2349fd865c234df9065c2349fe8795934bfd87959349fd8795934bbd8495934bdd8395934bf58195934bfe78559349fe78559349fc7855934bfe4855934bde3855934bfd80dd934dfd56dd934dfd85dd934dfd80dd9349fd80dd934cff769d934bbd849d934bfd809d934bfe485d934fbe485d934bbe485d934fee285d934bee285d934bfe085d934dfe685d934cfe685d934dfe585d934dfd585d934dfe485d9349fe485d934dbe485d934dee285d9349ee285d934dfe085d9349fe085d934dfd085d934dfd565d934cfd761d934b7d851d9349fe871d934bed281d934bf5181d934bfd081d934bf9081d934fbd56d1934fbd76d1934bbe87d1934bbd80d1934cff7691934bfd87919349fd8791934bbd8491934bdd839
  | 4 => 0xdfd8391d569fd8391d56dfd8091d569fd8091d56bbe4855b46bfe3855b46bfe0855b469f6185d746dfd565cf46dfd865cf46dfd855cf469fe085cf46dfd085cf46dfd565c346dfd865c346dfd855c3469ff835c346dfd835c3469ee285d246dfd855ce46dfd845ce469fe085ce46dfd855c246dfd845c2469ff835c246fbe4855d46bfe3855d46ff61855d46bf61855d46bfe0855d469fd808dd46efe684dd46bfe584dd46fbe484dd46bfe084dd46dfd574dd46ded5789d46ded3789d46bed8089d46ded8589d46ded8389d46ded8089d469ed8089d469fd8381d46efe6841d46bfe5841d46fbe4841d46bfe3841d46dfd5741d46dfd3741d46dee2741d46bbe4855946bfe3855946bfe0855946dee2755946dfd854dc469fe084dc46ddf854dc46ddd854dc46dde084dc46ddd084dc46dfd8541c469fe3841c46ded2841c46df51841c46dfb8541c46df98541c46dfa3841c46df93841c46de92841c46df11841c469fe485d6369ee285d2369ff845c236dfd845c236bfd8495d369fd8495d36bfe4855d36dfe57d1d36dfd57d1d36afd86d1d36b7d85d1d36bfd80d1d36dfd5791d36dbf4791d36dfd8591d369fd8091d36bfe6851d36efe6851d36afe6851d36fee2851d36bee2851d36bfe0851d36dfe5751d36dfd5751d36dfd5711d36dbd4711d36dff4781d36dfd4781d36bfd8481d36dfe8481d36dfd8481d369fd8481d36dff4741d36dfd4741d36efd4795936bfe4855936bde3855936dfe4755936efe4855936eff4755936efe4755936efd4755936efc4755936dfe57d1936dbe47d1936dfe07d1936bfd87d1936efd56d1936bdd83d1936bfd80d1936bee2851936dfe5751936dbe4751936dfe0751936efd5651936afe4855a06afe484da06efd484da069fe485d6069ee285d2069ff845ce06dfd845ce06bfd8495d06bf58195d069fd8495d069f58195d06bfe4855d06bde3855d06dfe57d1d06dfd57d1d06afd86d1d06bfd83d1d06dfd5791d06dbf4791d06dfd8591d069fd8391d06bfe6851d06efe6851d06afe6851d06bfe3851d06fee2851d06bee2851d06dfe5751d06dfd5751d06dfd5711d06dbd4711d06b7d8511d06bdd3811d06bed2811d06bf51811d06dff478dd06dfd478dd06bfd848dd06dfe848dd06dfd848dd069fd848dd06dff474dd06dfd474dd06efd4795906afd8495906bfe4855906bfa0855906dfe4755906efe4855906afe4855906eff4755906efe4755906efd4755906efc4755906dfe57d1906dbe47d1906dfe37d1906bfd87d1906efd56d1906bfd83d1906bf980d1906efd5791906efd4791906afe8791906afd8491906afd8391906bee2851906dfe5751906dbe4751906dfe3751906efd5651906efd5851906afe3851906efd3851906eee2851906efe5751906efd5751906efe4751906ebe47519
  | 5 => 0x497aa2d15084a7b553a629cd14d84a62c52f8296654adea5455292292a548eca3f251e428e3146a0a2e7515a28a294454a20050dda86454286a1195046280f940289f994faea7c193d4c9e6a4f0e276853a4c9ce14e40a701936f29b3d4d7326a19344c99d84cc9a6419313a986a4c00a5e3d2e4c96c64b33258852bb895974aa4a53c92924941749eda4d5d25ca9285493fa49e5242091ef48b5a4505224090f6486aa426520de903c480023f111ec88f3a4771a3a0d1c8e8e1446d5a359919e88cc1463e230b917ae8b77459022a95145489b844a7a244d115488a44446221ad107087ea43e021ded0e1286bb4348a19550c0e85b042c32154d0a2e84c04246a1049079a837f419420bd50518822c40e1a05d5026080f44045a0118ff967f623f931fbf0fd927e693ef29f734fb587d8b3eb99f524fa867d223e809f338f9247c443e119ef78f7207b423d6c9eabcf52e7a253ceb9e6b4f2f479503c8a1e33cf14a787b3c289e078efd677943bac1dbbcecfa761d3ad59d550ea1e74af3a351d100e7d273ad39b41cbd8e4f6723638ef9c6f8e3167134386e9c260e070701737ed9bdecde486eb237201b7a4db246d0e36529b1c8d7ee6b8e35971abecd57e6a8c351a9a6c4d23668a9341b99e60cedc66f33369199c8cc5a660332e819698ca9e651c326719290c8be6447320e98f3cc75c634e318018a5cc426618f30b718510c24660d5305a18204c0ae60092fd017dd8be865f102f6117964bbbc5d992e9397460b9ee5c972e2016f80b76c5b832d9a96b9cb5445a542d0796728b2e6595b2c9416368b10658112bf395e64ae4e56c72b2f15768ab1855112a4b151b0a7be5352296b94928a38c516f2883141c0a0204fb927a813b549cb44dcd26cd1345899244c0525c992c6095284a1924b8923b4908a47b8239591ac08c2245842280111cc87de433e215d1094483ac4140204c100987fe63fb71fc20fcb47df43ed01f218f7b07af43cff1e660f0fc78183b911d8b0ea6c7452398a1cb00e37070c2382e1bcc0dc086cc635e81aa00d33868a633cf199c8cad4646231b618828c1985fa02f4c17640b9105b262d18164e8b06457182b2c15810a9d453d0296414628a1044fd42766139089ae04c9e261312d50942c4956243911e808d0c456c227a10fb086e842d820fa10488815440201f9e0f8d07a583cc61dcd0ec887458396c1c440df686f0c37441b150d3f867a4329418ab0c1385e442e0816920b07056942a4214f70a42851d8288613d109bd04c2025ce12a2091c84764225010fe083403f901ec00edc0754839fc1bae0d41064c8307817340b280552028a4132608d0042a81efc0e52068a03078157809b4045f01e480ca8054c022200ca8039000d20000dbf4791d56dfd3791d56dfd0791d56bfd8391d56bfd8091d56dfd0391d56
  | 6 => 0x5b37e89bbb4dcea6e4536ef9b3a4d80a6bb135c99ac24d56a69ad34919a2accfd667a9337499934cbf2656f32a89928cc89e63e9319d98b54c52661af30929826cc08e5fcf2f6c97984bbd25da72ea09736cb8ea5c0f2db096becb5065a2f2c9c9634cb02657892b49957dcaada54bf2a0894ef4a56a5207287f942649ffa4f3d272c9361c99d64c4f260f92e9c95624a4b24fb925fc9256482323c391c3c8c9e45c522b8912c488de43d3219b90a24832640af1fdc8fb547d4a3e511ec88f5847a3e3c171dd88ec9c75823a011ca98e1bc6fca376d1b568d9646bc2357b1a668d19c6772335319648c98c63d6311918748c0ec5f1a2ebb16fd8b45c58f62b9715868a97c536228df142189ee44eca2711133a896d449c6246b120b88f0c45e2220d108b8830c404e1fc10f8087a243bb61d990e99871cc36fa1b290d198677c321a18170b7e858642a46142d09b684c6424221109084883e241d920de50689830bc17920ae5053f8281c11fe08ab042b8200c0fa6076d038381a840c0a0521021580cd404a2015b003b7fedbfd81fe90fecd7f563fa51fce6fe527f18bf841fbdefdc57ec03f5a1fa34fcf07e633f271f8d2fbe57db53eb99f4d6f9f97cf53e725f350f9907cbc3e43df1dcf8c47c24be0a1effcf7d47bc33dc2dedc2f6667b0c3d795eb1cf56d7a9d3d41de996f4987a3bbd135e810f3cc79d13ce05e666f3097966bca21e474f1c878ab3c36de09cf01b77fd3be69dee0ef3d77613ba61dcb8ee3276f23b67dda7eece8765abb19dd87aec1375f4bae49d5f8eac0751e3a849d352e94074943a3f9d0e2e81173cb39db1cde2e688730b397d5cb06e51a725d390b5c82ae3a37186b8b8dc4f4e22370fcb873dc35ce133707bb81a9c080e00d6fe8b7d7dbe7cdede6f4837999bc42ddf76ed4b75fdb9e4dca46e2b36fd9b750db2d6d78b6ad5b4ced9f56cbd363fdb0e4d7dc6bbe35d25adf6d6926b1935791ab50d51b6a54b50b9a7e4d380698734adda4d2d1f768ddb45d9a262d0da683d340f9a004cfbd67c9b3ccd9d94ce8e6712b37c99b12cd32665bb3211986ccbf165cd32ca1956cca836511b26c59290c8cd644d320598f48c73b639ab1cbd8d7ac69c62feb174d8b64c57f62aab14d18a26c4d76249310c987fec3d561bf30c9d8558c25e60f6307758378c18960a6b03d98198c090600f2ff417f4cbf6a5f8e2fb157d36be5f5f0d2f6e97b0ebd0c5e682f2517868bc015dc7aecbd75d4baae5d3dae84973acb9525c74ae29170f4b83e5bef2dd8d6e84b7185b72adaed6cfeb6165aff2d72d6b1eb5535a7e2d2b968f6b41b59e22cd9165f6b2da595cac91d63f2b1cf58ce2c5c9626cb0f15863ac27560d4b0405806abe255eacaedb57542b9455c84ae2156e9ab5f15a92ace05632aafcd5702aafd55652a91953a8a9595
  | 7 => 0xc1606424020ea14882bc5e4b35597c964c1c0f05819090083a84c20af179aa4c65f25930703c16074221201175098415e2f35498cbe4b260e0782c0e844240222913082bc966af2f930703e160603211c291007cbc966a93397c90441c0f858180c8480a44c651007cbc4c65f260e07c2c0c06423ce873350a42c55a592f93854260cc149782c55a592f924903e17060321000e14b782c55a5f270f850260c8459d3bc180b1541d4be4a1f0a054180c8471a8ab4b25885e2ad2c97c92481f0b83019080061a813a0c4d4c9418a741897a97c92481f0b83019080061a9bc162a83896c943a0c9189a853de0b156964be4e15098330d54b25867435156964b64e0c73a1abbc162ad2c97c9c2a130658c4d4de2a83897c9c2e0d0055a8522610378bd16aa93297c9a4a1c0e8541b0885004c625525a0c43a1ccd41fef178aa4be49260f85c180c840040d41fef178aacb25f249385c180c840038e81fef060abcbe481f0a054180c840038d45e0d15497c92481f0b830190a000038d41a8c81c00286a328300086a2f06aaa550932c97c924c220e07c2e0c06428024ea14b7831160b1541ccbe4b260e0782c0d0083a852de0c458aa0e65f25930703c140903611090093a9bc182ab2f92c98381f0a048180cd3a3a9bc18e5b2f92c983e150a0481a00e7537830cbe4b260f8542812068031d4de0c15796cbe4b260e07c2812060339d429ef0602c55e5f260e07c2812066ba852de0c058aacbe4b260e0782812060340207439ba853de6f0602c55e5b2f92c98381f0b050240c068054e8eaef058abcbe4c1c0f850240c0669d1d4de0c1541c4c65f25930703c1409034020707537830550713197c964c1c0f050240d0083a9bc18aa9541dcb65f25930703e14090301909114b7a2d552672f930703e160603211aea14881bc16aa83b96cbe4b241107c2a14090321201314881bd16aa93397c90441f0a0581908e3a081bc180b1541dcbe4c1c0f85819a296f058aa0e6672f92088381f0a048180d8483a852266f0622c5565f25930703c1409036120117537830550732f92c98381f0a048180ce75378300e06b2f92c983e150a0481a00e3a77830162a8381a4c65f260e07c2812067babbcde0c058aa0e2632f92c98381f0b050240c06804fbc162a83898cbe4c1c0f850240c0668a5bd16a5f260f850260c85002ea7ff53f0a9e354de2a6555300a966d494aa45151ada8ab54446a1ab506ca81853fd29f5f4f34a78553b3a9d134e44a6e9536a29ab54d30a67a531e6988d4c01a5c352cbe95e74ab7a5275279692c34925a47052292909b47eda3c6d1cfe8dad4676a306d16268a7744b7a23dd10da87f543aca1a650bfa853d422ca0ef5061e823d40eba02f4ff6a7ed13eed9f394f8927b1d3d259e59cf07677573b1e9d51ce8ea7391393b9c724e1a67
  | 8 => 0x809a34189a9bc550712f13c5c1c050260d0586aef57a2f550752d140a44f168a0441c05132955064210566aef178aacb25e278a45c180c84013857de0c157960ac48278a454180c02699636832100453517839552ab2c970a056278a45c180c85014068ea6f060aa0e65c281509e2b1409036120501a3abbcde0c554abcb65c281589e2b14090301a234757783117aaf2e140ac4f16060334683375779bc180bd5796cb8562513c56281206814868337577a2f55e5c2b1209e2c0cc1a3abbc180b957970a056278a04819a3419babbc172af2e140ac4f140903019c347537831172a839970a054278ac50240d0283a9bc182a839970a056278ac50240c0673a840de0732e1589448238ac50240d0270d040de0c05caa0ee5c281589e2c0cd1a3a8d2de2a83b96cb8502b1309047158a048180d0298d0d2de0b9541ccce5c28158904714090301b09175098cade0c155970a054278ac50240d848141d4de0c1541ccb8502b13c562812060339d4de0c0381acb8562513c56281206813869de0c05caa0e06b2e140ac4f1409033868eaef37830172a839970a0562613c562812060340a634ef05caa0e65c281589e281206033657de8b84c1d4b0562513c562916026cd257de8b84c1d4b0562413c522a0e0271a8535e2f258aa0e25f249207c2e0c06003c5a6aaf05b97c904617060028d45e2ac10414d78bc962a92f924903e160983019080078a7bc5e0b155964be49240f85c180c84003ed429ef0602c55e5f250f8502a0c064238e873350a4bc162a92f924903e150b83019080089c0d45e2ab2c97c92481f0b83019080071d052de2f05b92c94390893a1a8bc556592f924903e17060321000e3a0c5964be4b250639ced5de8b55796c924e1f0b832ed529ef45aabcb64e1f0b8320966a6f178ab49210c6a6f058aa4ce5f270f85c1908b350a7bc5e0b155964be49270e07c2e0c064200226a14f782c5565f270f85c1946a14f78b6162af2d9387c2e0c8261a83fde0d064abcbe4e1706002c626a14f7830162af2f9287c28150603211e74399a8bc55a592f924903e17060321000f18b78aa0ec1a0c6189c0bc55a592f924903e17060321000e3a0c4aac9c1a0c619378220e4381f060020e16aef038994be4a1f0a854180cc385abbc0ea5f250f8502a0c8458c4ab4b25c0d0631d06255a592d93031cd4de0b13397c983e14098321000c3507cbc162ab2c97c924e17060321000e188b0d41fef05b97c903e140a8321000e969a9964b800a6aef178aa126592f92498401f0b830190a0080b5964b03a0c003578bc162a83897c92481f0b8301800daf058aa0e2632f9387c2e0caaf058aa0ee5f250f8502811060332bc16aa84b97c9c2e0c0049a8ca5e210865649083750a4401f2f13397c98381f0b058180c847ba85220af1792cd565f25930703
  | 9 => 0xc70c0381bc9e2b140b83203a0e06e2f8ac5028e1d8a856160bc1a0c70e836160be4f17060321138341843318b27068314663185f278b830190886f1541c0d05b258b83419231cf074aa158683617c9e2a1306603417034188332a8541b0b05b260640cf3c550ac341b0b05f278a84c19831162782a0e06c2f93c5c1942c0e8381a0c8582f92044180cb13081bc9e0e834190b05f15060361108e0e8381a0c85b15060320686d159aabc560772f158962e0c8068d0566aaf03b968ac48278a044180cd35178ab0410695e2f25caa4b056278a458260c0642009e34ef1782e556592c1589e2917060321004f1a5abbc180b957968ac48278a83019a343517a2e556592c1589e2917060321004f1a0c4586aef45eabcb4562413c54180ce15dabbc17aaf2f8b8300926a6f05caa4ce5e2b13c5c1908b35778bc172ab2c978a056278a45c180c840140626aef05caacbc56278b8328d5de0e06cabcbe2e0c0249abbc590b957978ac4b1706402c626aef0602e55e5a2b1209e2a0c0668d0582b357781d4b4562413c54180cd1a0c4bc972ad2c960ac4f148b83019080278d0622b2aa285351782e556592e1589e2917060321004e188b0d5de0bf2c158904f148a8301804e179abbc5e2ab2c960ac4f148b830190a0278bed5de8bf2c158944f158a45809835175abbd17e582b1209e2915070134586a6f3541ccb8502b13c56281206033840de6a839970ac4a278ac50240d0268d0622cb51abbcde6af2d970a056278ac50240c0690d0622cb57792ed5e5c281589e2c0c0670d0662c15dabbcde6af2d970ac4a278ac50240d0290b0d5de6f3541ccb8502b13c56281206033c622c6f3541c0d65c2b1289e2b140903409e34160acd4206f03b970a056278b0334686a6f3541dcb65c28158984f158a048180d0288d0566a6f03999cb8502b13c50240c06c23c6831161abbc976af2e140ac4f140903386833159abbc976af2e140ac4f140903019e34160acd5de07035970a056278a04819c34160acd5de6f3541ccb8502b1309e2b14090301a0531a0c4566aef039970a056278a048180ce1a5782e5507131978ac4f170658d2bc172a83b968ac48278a044180cd1a1a6bc5e8b954960ac4f148b04c180c840140682c3557aaa0ee5d2d140a448238b450220e85014a695e8bd5425cbc56248cc5c1900c329560683210a6a3297a0683210c654540d064214ca5e2a92d14c581a0c8449a8ca5e81908532c0c840110d42632d7aab4b4502913c5a28110742809e65af52d158904f1408832468696f05cab4bc56278a04c1908c1a77830172a83a968ac48278a83019a3435156964b14685e8b956964bc502b13c522e0c0642009e34189a82e8a1468312f45e960ac4f148b83019080268d0626aef05cab4b25e278a84c1c04d1a0ccd5de0b956964bc4f150983
  | 10 => 0xa0c042c0f062960be48278a05c180c0460a83a1506d2c960b0190311805c9220c0304bc1a0c51552c960b10d42aa592c16c919bc950712d92c5418e310e8629621a81b4b41886a0c0341621a83a9506d2c50c03696c5228a340c456960be4f170682246833188602ec9186833188622b4b05f278b83411634160622a150703697c9e28110660d0301506d2f93c5c180c8450d052de0c0561b4be4f1409832118340e8622b4b8592c16032468300bc549383018e340e8622b4b05e0e06830194341605e2b4b05a2471a12e068310686aa5c2c96c9c1c0d0648d031150a82f0631a83b150ad2d06031c3a188a83a97c9e2e148a054180cc4f07431150712c17c9e2d150a05c19a1d0ac2c960bc1a0c70e8622b4be4f170603211234c1a0c31a0c19383418a341845697c9e2e0c06422468de0a83896c962e0d0648602b4b25c0d06031fbc1d0c456960be4f17068228684b8186341652c96c9818c341677a2b4b05f278b834114346f0541c4b64b1606832460de0c4542a0e0612c17c9e2e0cc167783b150a83a97c9e2811060333bc1d8a83a97c9e2b15064b7831150712f93c562e0c9150783a182a8551b8be48278a05c1808ecf0742a8d4582f93c5c180c8458cc2a0d059245180b0d41e0aa3717c904f140b83011a30350a91a8b05f278b8301908b161a8548dc582f928301908a1885c1bc9448a3318a3417c9418c338ae37164916559e8ae3717c5c2e0c0249a8541e0e860aa15c5f2413c502e0c0471a8559e0e9542a8d4582f9389e2e17060321206a1567836550ae3717c5c2e0c0261a8559e0c9542b8dc5f271383001831350ab3c182a8551b8b05f2713c5c2a0c06424462de0a8384188782a0dc582f9209e28170603011a310ab243188b3bc0e06f278ac502e0ca188381b8be2b140a38c42a0d4588310ac341ac915bc0ec1a0c418836160be4f17060321123318b27068314600e06832160b62a0c818834170310663106c2c16c9818f8b458433c5a2d9220b01c0d45b14090301900d85a2c3188b0d42a8683717c90240ca199a8540dc5c2d16c9206631350aa1a0dc5f240903019631350abbc0e06831160be4f140903019c31350abbc0e06831160be4f140903019c260a808315098bc02104cc90106262f05516c962a0c04409606420c4a5e81a0c84289593032108252f03592c581a0c8440984b5e06c2c16044180e84422cbd0b4590841017a168b210a5e85a2d924214405e06c2d16c962908813082bc0d0622c170301d088458984a202f0781a8b05f278b0301908d15074305506a2d0638782a0dc582f9209e2817060301182a04622a6486310f62f9209e2817060200942a6f1541c0d45b258a8324622a0e860ab8be4f15098328540d45a0c4151561a0d648a2a2a83717c9e2a130640a8300e06a2f93c5c1902a0e8381b8be4a0
  | 11 => 0xb8301908aef074301565f278b8301908a1a1a831150af278b83206833350602e49418e34199a83c188a82f9209e2817068301004f1a0ccd42a0c05793c5c180c8458d11a0d4592c5350a83115e4f170a4502a0c0658ce559e0bc57168a64f170b83209834199aa2a15e4f168a8502e0cb1b0d052dee4b258b8341908a1a4542a0d65f278b8301908a1a0c197c964e0d0638ce54178ab278b831c6c34153782b03210e34350a82b8381a0c0640d0d4188a85793c562e0c91a0ccd42a0c4542bc9e2e0ca1a1a83c15a582f9209e28170603011a34198b05417248c34198b0d41ea582f9209e28170602009c34199a854950ad2f93c5c180c8460b0d42a0a83a97c9e2a0c0650000c0541ea582f9209e281706022c5618448630150783015a582f9209e28170603011c34180601c20d306030c68300aa0c41a52c1618d05618a582d1230d06018a58834180569683165495628120603186d2a10255960418682c150612a1564b160603292a158180c4188b12bc9e2b140903019231160612a15e4f14090301942c950a92b03018c31184a92a0d14682c350a840de0c03b93c5819636350a9bd154a81071b1a854de0c03b93c50240c06c230d42a8ac0c0629a831c96281206031c682c150612a1564c0c8161a85418e4f14090301922c350a92a15e4f14090301946a0c2542bc9e28120603246833350abbc950af2f93c50240c0668d0666a157792a15e5f278a048180cd1a1a855de4a85797c9e2812060330682c350a8300e06b2f9204819630350aa2a95658c31181a854180732f92048180cb006cc908308301866a4a811060314582aaf1783c1802008814c0d06031066294ab260683018e2caf078180be48278a05c180c0460a85020af1783c150190362f5140420aabc5e0f5140431a8555e2f07993450110292f25596c9a2b1506022452280b5144350a44145418a6a140812b45020d5e0b65425cbe4b17064024545ee2c08042882bc1e0a82f9209e2817060381008d150a4405e0b4140438a852200b255930501115e0b65421cbe4b1706002468330c05d9228d05820af0622a15077278a832c6820af0602a0ee4f170603286920af0602a0e2632f93c5c196341407a8b034180c0440d2bc1e0ba268a021c68292f40d06421868aa350a6bc5e64d16068321166a1457a2a15a28107d557a3c168a84b17c9c4a1d8b83201a29145783115e4f16098301908b2f05606830190861a17a064210685e64c0c8428d0525e0ab2d92c581a0c8450b0515e8a8541dcbe48238a044180e84709404109512020c521521068321046a8aa54082003064e0c30c20c0619a830954180c5160a8314b2582c6150612b4be4f1509832206830186304ab2707034180c7180a92b4be4f15098320582a0c03a97c94180c80f0602b4be48278a05c180c0458a8304b41882
  | 12 => 0xf62e168b210a34550a6bc5ec5c2d16c9a2908b1417a2a15065146d557a3c168a848208fc5f2712c5c1900e148a2bc1d8ac33160be4f148459782b8b85a2c16421cbd8b8590841a17b170b649086149782b8b85a2d92c561908a180a2bc5e8a854200e0622c17c9e29a200f008310079120210535e0ac2c842d7a168b21086a3017a2a95060daa305782a0c4582f93c5a1c08b150742161a83ac9a18a6a0e855160ba18c6a0ea542a0ba18c33180a83a1724d0c860324541d4ae2f93c52250c815076168b058a2c150752b0b4582d934381942c150752b8be4f14894324602c150741c8b05f278b43283c1d0ae2c17c904f140b4301162a0e90c3150759218c03c1dc5f2413c502d0c060200982a0c0541a0ba190c0640c4581724882c0ee2d16431455432180c4350a993432180c66f2541c8b64b148638c43a18a1886a06a2e8621a8309506d0c5350741a03103a0d629168628d8695e0f2542a0be48278a058260c0670cc601d4a8545180792a15a582f9209e28170603011a33158742a8914576aef45796c9e2e0c024908112a24041d7a2a10e5f258b830010340ec5697c9e2e0c06422466310e85d9228d066310ec5697c9e2e0c06422c68306f0762a1507034184be4f170668d067de0e8541b4b05f278b83411834198b055de0e85697c9e2a130660d03c1d8a856960be48278a05c180c0470cc541d0bb2451a0cc3c1d8ad2f9209e2817060301004e1a0a9bc1d8a8541c4b05f278b8330686aaf0782a0e05f2413c502e0c0668d0662a020834199aabc1e0702f9209e28140983346833350aabc950a83b93c5c180cc1a0b4d42aaf4782d950762f9389c19000079a8555e0b0541dc9e281106032c0802086c2aaf07817c904f140b040260cc1b0aabc1e0c0541c0be48278a050260c0642406829c180c840218541d0c0541acb2582c0648d1bc1e0108de0f314042061960b0c3c180a835960be48278a05c180c0469a831c9e2e0c51a0ccd42a0c2542bc9e29140b8301908e1a32c960b1068184ab17060318682c0c7258a4518622c0c25793c522817060321162c1532c960b146833b512441a5abbc17caf2d93c5c1904a1a0cc59c9106818e4f158a05c18ede0f7240420d1bc1e65f2592c5011034198639220d0622c0f2542a0be48278ac502e0c06023c6831167278ac502e0c81632c17c91059de0f061960be48278a05c180c0468d062cb05f259230d067de4bf2d9209e2e0c915dabbc17caf2d93c5c1804a1a0adbc1e8480861a0cc586a0c7278b8320686a1537b2a0ee5f278a04c19080468d0d41e0c02f9209e2817068301808d1a0602a0d6592c1638d0d42aef0632acbe4f170651a855de0d8602f95e5b278b8320804d1a1a85429ef0643016caf2f92c5c19000078d868296f0608430d0662c350a82ec9c180c9188b03015e4f158
  | 13 => 0x66303507717c9e2906a1537b2a0e0662f93c5e19080460d0d41e0ee2d160be48278a0501808d1a9a855de0e85f2b8b64f178641009a34369a85429ef0742d95c5f258bc320000f1a0a83a170b0541b8b05f2493c522b0c860340686a157783b95c5f278ac3286cde0ea2c8428cc606a1505f160b649031187783a15c582f93c562908bef0743015c582f93c561908a1a1a83b150ae2f93c520666a0e85d1649186833350783b15c5a2f9209e28140602009e34199a855de0e857160be4f148460d0d42a2f0762a8b05f278b8522814d1a2341a0b4190c619cabbd9e0bc5716c9e2e170641306833350762a15c5f278b4542814c1b0d0538b45f2592c5211233957782f15c5b278a40d067de8a8541b8b05f278ac32118341662d17c9648c36153782b0b459087350a82b8b85a2c1638d0d5de0ec5717c9e2b1491a0ccd42aef0762b8be4f14a951792a0c8582c61b4a84ade2f2546180a83a950ac2c163a542b0b058831187792a0c8582f93c5629434188c03a950a832160be4f14b184a8549505b0c6181783a180a83a160be4f158658c4592a4a8345181a854256f1783a0e85f278a58d8d42a6f17a2a950602c91b1a854de2f0741c0c8582f93c5611a6a15456160b14d41d0642c17c9e2b1481a0c0541d4a8559238d0606a15074190be4f1491a0c0d42aaf2542a0c8582f93c5306833350aabc950a832160be4f14c198c0d42a0e8a34198c0d58be4f168603411434199a855de0ea5717c9e29128660c0d42a0e8381a0c45f278b432cd41e0e857160be48278a05a180c0468cc602a0b92451a0cc606a0f62f9209e2816860301004e199a855de4a857160be4f16864230606a151782a0e4582f93c5a1960002c157783d8be48278a05a180c0460ac3a890c582aef0783a15c582f9209e28168603010040088d0581dc58834c582c31a0b02b8b458a2c4a8341620d286030c681da18634188a83b43218c34159a83a89a180c71a0c4d41dc5f278b4301a08a1a0b03b0ba18a340ee2e0620d0541d4a85717438190c91a0b0d42a0ae2e168ba19234161a855de0ea542b8be4f14894334682c350aa2a9505d0c8188b0d42a0e838188b05f278b4332bc08dabcc90ebc1d85a2c1629aa2a950622c1630c0555e2f0783a0c058089af42d160b10675e85a2c16c918615e0f62c17c904f140a0401808c150a04b5e2f0782a0b206c5ea2808415578bc1ea28086350aabc5e0f3268a0220525e4aa2d934562b0c0448a02d8ba2886a14897168ba28c6a14094bc95065147af05b2a120862f92c5e1900a1517b8b02010a25af0782b8b05f2413c50280e04023454252f05a0a021854250b3260a021abc16cae2f920803317860028661d0bc2d9228d06025af1783b150a83917c9e2983412d783a150762c17c9e294280f42d160ba28087af0782e89a280862
  | 14 => 0x7c924f148a83011a6a150a73c182a85717c9c4f170a62081129240418943c020c548208868208542612a7b168be4f160a8201162a12a783150959202104c25cf0782b8b05f2413c50280c0468942a040c54254f010412b240843104a9e0aa2d92c50210c8130833c1e0a82f9209e28170603011a9e0ac080420833c1e0a82f9209e2817060381008db54833c0c65f278b83206d2a1560e0428823c1ee4f170603810089104782a18823c15458085148803c83010a29106783c8b010c2910078920214401e010617e4a240420802e1645f2512851c66290f725060218401e45808419e78921cab3d15c5f170b830090200ad240421a8401545d240431a8409e0f52506021c5220cf0791783018088350a8539e0e9542bc9c4f170b8330d42a14e7836550ae2f8b85c1804c350a83f9e0c9542b8be4e270640001a6a150a43f9e0f060aa15c5f2713c5c2a0cf1007a1649010a200f008315098409ee4f160b8341008a150a4409e10542910324042898419e0f05417c904f140b8301808d10054184b11d42a10278184b18400c25b244102782a0c25b258a8321d59e0612f93c5c18e29104783dc9e2e0c07020114268f05517c9e2e0e04022452200f40c0428a4411e0f155930301102912c0c042094410301082564c0c0420a44a2025b258b034180891b0d2d429af0792a158662c17c904f140a03406833160612a1518682c0f2542b8b05f2413c502d0c06023868330c05441a0cc586a4a85717c9e29128658d0666a8a85717c9e2b0c07022c52420852200f00841a3a851150ae2d17c964f158a0461c080478d066301505717c9e29128650d03c188a85717c904f140b4301808d1a0cc54181068330f0622b8b05f2413c502d0c0468d054188a8541d8be4f1486032cd55e0f0541d8b05f2413c50280cc198a81818ccd55e0f038198be48278a05019833350aabc950a83b160be4f14b350aabc1507031160be4f14a368b4d42aaf4782d950762f9389c19000078300410d8555e0f430198be48278a05019836155783c1d0a838198b05f2413c50280c84862c164201095e2f0541c0c4582f93c5c1c08b1507430150682d86430192de0f22c0423783cc501081d6180c30f0742a0dc582f9209e28158603011a343507717c9e28c34199a855de0ea542b8b05f278a4502908f1a30c8603103a95c582d8a28d0601de4b148a30c461de0ea57160be4f148a05211834b512431a5abbc17cae2d93c5e1904a198c0541724b0c86032068331872441a07717c9e2b140a3b783dc90108346f07b92c962b0c0440d0661de48834188c03c950ae2c17c904f158a0501808f1a0c4618be4f158a052069de4be2d9209e2f0c815dabbc17cae2d93c5e1804a1a0cc601de4b2586032061de0f07717c904f140ac3018080268d063c964b0c0630adbc1e45c240430d0
  | 15 => 0x5e65b258b034190890b2160683018a34188b254550af278b8324581581a0c0628d0662c1595492831c685e81a0c8428d11a0d4592c0630b254550af278b852281506032c6ccb08683315860aa1564e0c0648c45418e4f158b830190891a0cc54550af278ac5c180c8458c0582a0c32f93c5c180c8450cc572acf457168a64f170b8320992a1405a928581a0c0640d06631161542bc9e2d150a05c1982c0e85693034180c71a378bd152ad2606832112341437b92c962e0d0642246833950a81acbe4f1706032116341887597c964e0d0640ce54578ab278b831c58c58180c410155970310682a2a85707034180c81a0c4592a1515793c562e0ca1a0cc622c950a8aa15e4f170658b0545581a0c0630c4aa0d818834198ad9220d0662c1503697c9e2e0c06422c602c9503a97c9e2e148a054180cc180b2555e0712c17c9e2d150a05c19a3425c0d0620d06255a592d93034190346f03b06831462309506297c9e2e0c06422868310eb270683186230950a81d4be4b150648d097030c681825b260628c4592a1503897c9e2b170655ab3c1e4a8541d4b05f2413c50280cd19da82a0c10699e0f2542a0e05f2413c502d0c0668d06615020834199ab3d150a83b93c56180cb19bab3c1e8a838194be48278a05019aea156793d150a838184b05f2593c562b0cf756793d150703297c964f158ac33068eacf27a2a150703392c9e2b158668d0679e0f4541c0be48278a050250cd1567a2a15077278a042180ca142541a0b10522812e783c156582f9209e28140602385228106783c1505f2413c502b0c0602386833148a393c5186c3414e783c950a82f9209e2b140a0338539e867260dc5628160902286929cf43396c904c1b8b04e1c08c15dab3c17cac3b96c9e2f0c025dab3c16ca84397c9040198bc300191e0f2542b8514531e0f25619cbe4c1b8ac582408c128789785010a341007b0a43010c33954a650a3cf05e2bcbc5f170b83209d9e4a8300426783d8501091ea582c0420100410d33c1ec280851a50c0682010a341467b0a8214682a146782b8521a0885a3ab3c9e0b25597c96481987003168b336bab3c9e0b25597c964b0e006ad1d59e4f254241065f25920661800d756793c950904197c96481986003168eacf2792a1265f2593060330c006bab3c9e4a84997c964c180cc30018a0cf65421cbe481a8ac300142612e783c15c582f9209e28140602342b02084b9e0f057160be48278a0501c08046ca8558b0c4a15084a150106254580831489404189492020c4a1e010617e4a240420942e16e4a250a831c66490a559e8ae2f8b85c18048129250602104a15a4808412856920210d42545d240429a85429cf0783a550aa2f9389e2e170671a85429cf16c36550ae2f8b85c1804d350a83f9e2c864aa15c5f27138320000e148943f9e0f62c1
  | 16 => 0x9a319577838180bc5796c9e2d0cb18ca853de0d0602d15e5f258b43306c34950aabc1ec582f9209e28140702011f2aef05eab8b64f17860124682c950a83d8be48278a05a180c0468d0662c158559230c2bc5e0f0742a0c1ebc1e0ee2c17c904f140a0401808c1b578bc1e0a82c62f00826f1783c15010a34198c154550ae2c17c9e29140a423754286f1542a0ec5f278bc321008c1a30c8603105008d062302ae2f93c51dbc1e458084188c03c1506e2c17c904f140ac301808e182a83a55c582d8a38d0601de4b148a30c1541dc582f93c5228148450d2aa490c682bd577aab8b64f17864128662b0e85492c32180c81417a920211bc5e0f1542b49010f2a046833188c03a55c5f278a48c1bc150708300c1559343146630158742a49a190c0648c1bc150710c5180559218c03c1dc5f2413c502d0c06020098316f0541d432180c7189542ac9a190c0638cc602b6488368f1783c1d058c36955781c0c4582f93c5c29140b8334501e85a2c1602186c2a2f433168b18bd0b21062a2f42d164214685e85b248428a8bd0b4590852f42d160b010a34188c254550ae2f93c524601585a2c1628cc602b2aa2c92317a168b210834184ab3c550aa2c17c9e2e148a0534688d0682c8628cc572acf45717c5c2e0c8250a0bd0b4582e92021c6833188c254550ae2f93c5a2a140a68c0301585a2c17494190342f456168ba490871b4aabdc9e2c130603211234184aa97c9e2e0c064224663015b2441b4a8555e0f02f9209e2817060381008e957782f55e5b278b83009234184a8541ea582f9209e28170603011c33180ac2ac914595e2f0783015020088166aabc160772f928762e0caaf078300c05f2413c502e0c060233555e0b03397c9438198b8300163610578bc1e2a8540646aa415e0732f93c5c190166284de2f0782acb010c34198b154550af278a4502e0c06423468cb2582c0628a0bccb0108311615793c5c18cde0f32c0420c4581e0a835960be48278a05c180c0470d058aa0c1558b830190341606392c5228c2c5506393c52281706032114330c055964b0580c71a0ceaa4910682bd577aabcb64f1706412851496286de2f078aa1565d240444a8bd4b65d268b03011034198c458182af278b832469aa6f1542a0ee5f278a04c19080468d0622cd57783a550ab2f93c5c19831160af55de2a85796c9e2e0c8201346831166abbc550af2f92c5c1800c16054216074aac910662c158602b4b2582c920328581508581564862cef078314b05f2413c502e0c0602009c310ad2c960b1462550ad2c960b648e34198b056c914682c15082bc0ee4f170603286c349557a3c5e0f0600648da555e077278b852281408830198341407a06830180871b0a8bd04c1a0c61b4aabc18e4f16098301908a1a17a064210545e81a0c064218685e64c0c8428d054
  | 17 => 0xd8699e2aa3393c5421002063ccb4100841b0782a8c6592c1602206c1e0aa1186430180881b0341603106c9e4632c1628d84b9e0f055960be48278a0501808d1b2118603106c20cf0782a0be48278a056180c0468d8692a14d792a15e4f1491b478bc1e0a8311638da3c5e0f0540836aabd150872f92080331786002c4ade0f42c96021866300bd2c16c91850de0f05a96c5010e1e0ec542b4b05f2413c502b0c0602343a186180c41a0a4401e8180861a0cc581764d0c0638a450de0f0598a021c3c188a85597c904f140b4301808c0e861960b1255de8af2d93c5e180481b3783c0210662b0ed2c16c918612a1507a960be48278a056180c0468d9bc1e6580851a0cc561864d0c0638b2542aef07997c904f140b4301808d1a0cc535ee4f158a458112360f32c960be48d3414d7b9245810d3499eaabc16caf2f92c5e1900b1b0a03c170b72492456190c0658d0662c0f062960be48278a056180c0470d0674be4b148a33783d4b2582f92021c6833a5f258a4518601d0b82f92496190c0648d0bc1ea592c174964b140450cd526311b7a2ecbe2b158650cdbd1709b2f8ac5619033d57782f95e5d249209e2b0cb15b782ecba49278ac561804a15b782f9565d2493c562b0c0258af55de6f05f2bcb65d2493c562b0c0276abbd95e5d278ac3009034198c03c1d65f2413c502d0c0602009c3419f258a45a18cde0f72686430180871a0cf92c522d0c61632c960be4d0c860320685e0f52592c5a190c060228684b05d2593432180c819d792f4b2502993c5a2d0ca1b0d0672aaf2542bc9e2e148a05306d1e2f0782a0c45e2481b4aa3c5e0f057120421923315ca8c75e8ad2f8b45a1a04b143783d4b010b2a150783b150ad2c17c904f140ac301808f18ca854296f0762a1525f2593c562b0ce950a852de0ec542bc964f158ac332542a6f0762a15a592f92c9e2b158668c6542a6f0762a15a5f2593c562b0cd148a1bc1ee4f16860222542a0f0622a1565f2413c502d0c060200801018cabbc1b0c45796c904f168658c65429ef0643115e5f258a05a19831950a852de0c05c2d150ab2f92c9e2b148684a854296f0622a1565f2593c562992a1537830170b4542acbe4b278ac5a190cf18ca854de0c4542acbe4b278ac5a1
  | _ => 0
def g127D9 : Nat → Nat
  | 0 => 0xe9c0e450e160dc70d780d210cce0c930c600c2d0bf60bc30b900b590b260ae30a940a4d0a0609b70974092d08e208a70864083907f6079f075c071106ca06830648060105d605970558050904c2047b043003e903a60363032402e102a2024b020001b50182013b00f800b90072004700005fd7495afeb9cad7d5c656bfae12b7fe4755aff23aadff11d56bfc6eab5fe0755bfeab68d7f5d746bfae7a35fd70d1afebac8d7f5d246bfae7235fd7091aff2ba8dff55d46bfc6ea37fd3751bf713a8d7b89d46bfc0ea37fd0751bfeab28d7f5d446afaea235fd3711aee9b88d7b49c46bea2e235fd0711afc8388dbf55a36bfaeb1b5fd748dafeb846dff95d36bfcae9b7fd574dbffa3a6dff91d36bfc8e9b7fd474dbfe23a6dff81d36bfc0e9b7fd074db7f2b26dff55936dfaac9b7ff464dbfea326dbf55a06dfa8d036fd3681afebac0d7f5d206bfae7037fe5741aff2ba0dff55d06ffe8e837fe4741aff23a0dff51d06ff88e837fe3741aff1ba0dff4dd06dfcac837fd5641b7eab20dffd1906dfc8c837fd4641b7ea320dbf8d906ffa6c836fd3641bfe9b68bff41b45bfaeda2dfd73d16eeb9e8b7f5c345bfeeca2dfd76517beab28bff91945ffa8ca2ffe36517fe9b28bff81945ffa0ca2dfe37517fb0ba8b7d85d45bfc0ea2dff764d6febb26bdf55935ffe8c9affe464d7fea326bff11935ffc0c9affd064d6ff23a6b7f81d35bfeec82dfd76417beab20bffd1905ffc8c82ffd46417fe2320bff8d905ffa6c82dfe47416ff1ba0bdf51505efa6a82ffd568d3dea3469ff41a34bfaed1a7bd458d3fe82c697f5d634afaeb1a5fd708d3ff2b269ff55934ffeec9a5ff764d3ff3b269ff5d934bfaec9a7fc764d3dfa3269ff91934ffa8c9a7bd464d3ee9b269ff81934ffa0c9a7ff754d2ffbaa69ff5d534bfaea9a7bf454d3fea2a69ef51534ffa0a9a7fe074d2ff03a69ff41d34ffaad027bd46813fe9b4097f5da04f7a8b027fd35812febac09ef4d204bfae7027fe56413feab209ffdd904bfeec827fe76413febb2097f5d904ff8ec827bf46413ff23209ff51904f7a8c827fe36413fe9b209fe41904ffeea825ff75413febaa097f5d504f7e8a827fd45413dea2a09ff4d504ffc6e825fe37413fe9ba09ef8d104ffa68827bd34413ffa3207ff91903ffa8c81ffc4640efebb207f74d903ff20c81dfd7540fee9aa07fe41503bfae881fdd3440ff72b205fb55902fde8c817ee4640bf6a3205fb11902fdc6c817ed3640bf73b205fb5d902fd20c817ef4540bf6a2a05fb4d502fdaea817ee3440bf69a205fb9d102fdae8817e90440bf6b9a05fd95901feaac80ff746407fb23203fd51901fe88c80ff636407fa9b203fd9d901feaec80ff745407faa2a03fd4d501feaea80ff105407fb1a203fd4d101fece880ff574407f882203fd5cd01
  | 1 => 0xf0baae5a5c50544e2a282418180a6d5bcbc2eab96971415138a8a0906060281a15b56f2f2a8725c50544e2a282418180a2686256d5bcbcaa1c971415138a8a090606029356f2f0baae5a58544e2a28241809c5e56d5bcbc2eab969615138a8a09060281a15b56f65854484e2819468d4bc2eaa1d96971415138a8b06060281a3534af0baa872665a5c505448462a2824181a100aad44ccabcaa971415138a8a0906068402815b511af0baa872665a58544e2a28241a100a468d5bcbc2eaa1c971415138a8a0906060289a356f2f0baa8725c50544e2a282418180a256d5bcbcab969615138a8a090602715b56f2f0e0d8baae5a58544e2a2824180a269bc2eab961512138a06515b56f2f0baa87258544e2a28241809ed43ebcaa1d969792930e0f0b0606007b5148faf2a872665a5e4a4c383c2824181a10026d453bcbc2cab969792930e0f0a090606008b514ef2f0b2ae5a5e4a4c383c28241818022e8d453bcbc2cab969792930e0f0a0906060093514ef2f0b2ae5a5e4a4c383c28241818022e8d5bcbcaa1c9792930e0f0a09060600818b56f2f2a8725e4a4c383c28241818020d43fbcbc2cab969792920f0a090600796b50fef2f0b2ae5a5e4a483c282418020d4bc2caa1d969792930e0f0b0606007b5148faf0b2a872665a5e4a4844383c2824181a1002ad4524cca3ebcaa9792930e0f0a09060684009351110af0b2a872665a5e4a483c28241a1002452403ebc9997920f0a0a068463514ef2f0b2a8725e4a4c383c28241818022d5bcbc2caa1c9792930e0f0a0906060083a350fef2f2ae5a5e4a483c28241801ed43fbcbc34322cab969792920f0a090600894ef0b2ae5e483c2828194d43fbcbc2caa24221e9792920f0a0906008c14e411340e840ad406640233fd43f953f563f073ec43e893e4e3e0b3dc83d853d423cfb3cb83c713c363c0b3be83ba13b663b173ad83aa93a6a3a4b3a2439fd39be399f3964392538e2389f385c382137e237a3375c371536d6368b3648360935c635933544351134c63477343c340933ce338f334c330932c6328b324c320d31c6317f314030f530b2307330302ffd2fae2f7b2f302efd2ea62e772e3c2de12dae2d5f2d102cd12c922c6b2c302bed2baa2b632b102ab92a5a29fb2994292d28ea28ab2884283d27fe27c3278c273d26f226a3265425fd25a62567253024f124b6247f243023e52396234722f02299225a222321e421ad2152211f20c8208920461feb1fa81f7d1f3a1eeb1e901e4d1e0a1dcb1d8c1d551d0e1cdf1c901c391c0a1bdb1b801b251ae21aa71a601a2119ee1997195c190118be187f184017e517b2175b171c16d91682163b160015bd156e151314d0148d144e140f13d813911362131712c01291123a11e311b81175113a10f310b41081102a0fef0f940f550f160ed7
  | 2 => 0x6553514af0f0a8807064585e4c4a4e2c2a2e1c1a1812a52bc3c2a201c191617938a8986847553513102f0f0eca8a864585e4c4a4e2c2a2a181a1012cd5bcbc3b2a2a1c19161792938a8a86068156f0f0eca874585e484e282a181811ed5bcbc3b2a1c1a191792938a8a860679b1a35152f0f4a8a8745a5e4c4a4e2c2a2824181a1012c6866d455bc2b97938a09060661a1835154f2f4a8a87062585e4c4a4e2c2a2824181aa6866d5bc3c2b961792138a0b06060479494102f0f0a872665e48462824181a12154d44c4abc3d2a2a96179312938b0a8a0906068404a9514942f0f0a866585e484836282c181812269bc3a2a1c1a189617938a09060671a156f0f0e8a872585e484e282c181812068d454bc3c312a2a1d16979312938b0a8b060699b35152f0f0c4a8a8745a5e4c4a4e2c2a2824181a1012cd455bcbc312a2b969792938a8a09060681a356f0f0c4a8ae585e484e282c181812068d455bcbc312b969792938a8a090679a35156f2f0c4ae5a5e4a4e2a282419e68d5bc3d2b961792138a0b060469a35156f2f0c4a8ae5a5e4a4e2a2824181a2d455bc302b97938a09060659a35154f2f0c0ac5a5e4c4a4e2c2a2824181a46866d455bd3cbc302b9716979312938b0a8a090606a9a35156f0ae5e4e28241819668d4553cbc312a2a1c1896179312938b0a8a090606a9835154f2f0c4a8a87062585e4c4a4e2c2a2824181aa68d455bd2a2b97938a065352f0f0c4a8765a5e4a4e2a2824181812054bc3d2a19961792138a0b06060473514902f0f4a8765a5e4a48462a2824181225440bd2a19961792120d8a0a09060479a102f0f0c0a8765e4e2c1819954d452bc3c2a1d971697931292118b0a8a09060604a94af0f0a872665e48462824181a11d54d44c4abc3c312a2a96179312938b0a8a0906068404b356f2f0c4a872585e4a4e2a28241819e55bc3c312a1c961792138a0b0606047b56f2f0c4a8706a585e4a4e2a282419e69bc302a1c1a189617938a090606755356f4f2f0e8c0a87062585e4c4a4e2c2a2824181abbc2a1c189617938a0906065b5154f2f2a8ac686c585e4c4a4e2c2a2824181a6d4553cbcaa2b1a1b16179312938b0a8a09060699a19b5154f2f2a8ac686c585e4c4a4e2c2a2824181aad4553cbcaa2a1d1a1b16179312938b0a8a090606a18b56f0f0a8706c5e484e282c1811c62d455bc1c1a17938a090606618b5156f0706864585e4e28198544cbc2a191792138a0a09060469312af0f0685e4e2824181a1184c40bc3c1a191617938a06846156f0f2a8706c5e484e282c1811bbd3caa2a1c1a17938a09060661a15b52f2a8765a5c50544e2a2c18180a06856d4bcaa1c9996971415138a8a090606840299a356f2f0baae5a5c50544e2a282418180a268d5bcbc2eab96971415138a8a0906060289a1995b56f2
  | 3 => 0x452513c3d2a2a1d971697931292118b0a8a0886070404c96351514944f0f4a8a8765c5a5e4c4a48462c2a2822181c101325452513c3d2a1c18961792138a0b86068144f0b4a884665e484032282c261c11f3d2a2597920c8b860049514944f0f4a876585e484846282822181a2d44c4b3c3c2b161792138a0b8606047b512cf0a8645e484e282826181811cd4544a3c191617938b0a0986046b5151492cf0f2a8ac585e4c4a4e2c2a2c1a18126d4544b3c3caa2b16179312938b0a8b068604919b51512cf0f2a8ac585e4c4a4e2c2a2c1a18126d454524b3c3caa2b16179312938b0a8b0686049b5151312cf0f4aaac585e4c4a4e2c2a2822181c1012ad4544c4b3c3d2aab16179312938b0a8a0886070404a951312cf0f2ac585e484e282e181811e544b3c2b161792138a0a0886066b513104f0f0ae585e484e282c181811ed4413c2a19961792138a0a09060473515100f0665e4e2c2824181811ad45452413c3caa2b16979312938b0a8b0606049b515104f0f2a8ac5a5e4c4a4e2c2a2c181812466d454413c3caa2b16979312938b0a8b0606049b51514904f0f2a8ac5a5e4c4a4e2c2a2c1818126d4544c413c3d2aaa1896179312938b0a8b06070404ab51513104f0f4aaa862585e4c4a4e2c2a2c181c1012a544c413c3cab961792138a0b060604795104f0a862585e484e282c1819a52403caa2a199717920d8a0906060479312900f062585e4e2824181811a6c68d454bc3d2a2a1c1916179312938b0a8b06868404b1a19b5156f0a864585e4e2e1986858d4553cbd2a2a1c1916179312938b0a8a088606a9a19b56f0f0ac585e484e282e181811e52504abc3c2a201c191617938a898684855351493102f0f4a8a864585e4c4a4e2c2a2a181a1012c545250bc3c2b161792138a0a0986060481a14af0ac5e4e2826181146855bc3c302a1d161792138a0a86060481a35152f0f0eca8a874585e4c4a4e2c2a2c1a1a66cd454bc3c3b2a2a1c1916179312938b0a8b06868404b35156f2f0eca8a864585e4a4e2a2e1a1a068d5bc3c3b2a2b161792138a0b86060481a35156f2f0eca8645e4a4e2a2e1a19e68d455bcbc3b2a191792938a8b868679a356f0f4ac5e484e282e181811a68d455bcbc3b2a2a19161792938a8b86868b5156f0e8a864585e4e2e19668d455bd3cbc3a2a1916179312938b0a8b068699a19b5156f4f2f0e8a864585e4c4a4e2c2a2e1c1a1aa68d455bc2a191617938b8659a35156f2f4a8a85e4e2e19668d455bd3cbc3b2a2a1c1916179312938b0a8a088606b1635156f4f2f0eca8a87064585e4c4a4e2c2a2822181acd4bc3c3b2a1c19161792938a8b8686048152f0f4ac585e484e282826181811cd4524abc3d2a201c191792938a8b86860489512af4a8645e484836282826181811e684abc3c3a2a1d1617938b86
  | 4 => 0x3c302b961792138a0a8606047956f0ae5e4e2a18e6c544abc3c1c191617938a89868471b152f0f0ac585e484e282826181811e686655bc3caa2b161792138a0b86060481a16156f0f0a874585e484e282a18181206154bc3caa1c19161792938a8b8686048552f0f0ac585e484e282826181811d544abc3caa1c191792938a8b86860479a18556f2f2a8a8645e4a4e2a2e1a19e62615455bcbcaa2a19161792938a8b868689a1898556f0f2a8ac585e484e282e1818122686155bcbcaa2a191792938a8b868679a189855156f2f2a8a864585e4a4e2a2e1a1a4615455bcbcaa1c19161792938a8a8606818556f0f0a874585e484e282a181811e626155bcbcaa1c1a191792938a8a860681a181512af0f074585e4e2e19854bc3d2aaa1c1916179312938b0a8b870686049952f0f07064585e4e2a261a1186860553cbcaa2a1916179312938b0a8b068691a1998154f2f2a8a864585e4c4a4e2c2a2c1a1a66c5440bc3c1c9997938a0906068471a19956f2a8ae5e4e282418198686055bc1c1a189617938a09060671b152f0f0a866585e484e282c181811e686655bc3caa2b961792138a0b06060481a18156f0f0a872585e484e282c18181205954bc3caa1d969792938a8a090606048552f0f0a866585e484e282c181811d5440bc3caa1d969792938a8a09060479a16556f2f2a8ae5a5e4a4e2a282419e62595455bcbcaa2b969792938a8a09060689a1896556f0f2a8ae585e484e282c1818122685955bcbcaa2b969792938a8a090679a189655156f2f2a8ae5a5e4a4e2a2824181a4595455bcbcaa1c961792938a8a090606816556f0f0a872585e484e282c181811e625955bcbcaa1c1a961792938a8a090681a1615102f0f0765e4e2c1819854bc3d2aaa1d9716979312938b0a8a090606049952f0f072665e4e2824181a1186858553cbcaa2b16979312938b0a8a09060691896156f2a8ae5e4e28241819868665855bd3cbcaa2b9716979312938b0a8a090606a9a156f2a8ae5e4e282418196685855bc1c1a189617938a0906067189816156f4f2f4aaa87062585e4c4a4e2c2a2824181ac6255bc1c189617938a09060661a1835154f0f4a8a872585e4c4a4e2c2a2c1a1a66858d4553c3d2a2a1d16979312938b0a8a860699a19b54f0f0a876585e484e282e1819e68553c3c2a1c18961792138a0b860679a4f0a870625e4e2e192553c3c2a1d961792138a0a08860673514944f0f4a8ae585e484e282e1818120d4533d2a19961792120d8a0a0986060481a3515148f4a8a8665a5e48362c28261812268d45452513c3c2b9716979312938b0a8b068604a1a19b51514944f0f0ae5c5a5e4c4a4e2c2a2c1a1812a68d45452513c3d2a2a201c1896179312938b0a8b068604b98351514944f0f4a8a8807062585e4c4a4e2c2a2c1a1812e68d45
  | 5 => 0x6866553c3caa2a1d961792138a0b86068154f0f0a87062585e484e282e1819c5a553c2c1d97928b86005154f0f0a876585e484e2828221819c6d54553c3caa2b969792938a8b8687040489b1a554f0f2a8ae585e484e282e18181206c6954553c3caa2a19969792938a8a0986860499b554f0f0a87062585e484e282e1819e6d553c3c2a1d961792138a0a08860679b1a1514af0f4a8ac5a5e4c4a4e2c2a2c1a1812754bc3c2a19961792120d8a0a098606048556f0f0e8aa585e484e282e181811d55bc3c302b961792138a0a8606047152f0f4a8a866585e484e2828261818120686655bc3c2b961792138a8a0b86060481898156f0f4a8aa585e484e282e1818120625855bc3d2a2b961792138a0a860604855152f0f4a8a866585e484e282826181812268675452bc3d2b969792938a8b86860481a19d5156f0f4a8aa585e484e282e1818122686755bcbd2a961792938a8b8686719d56f0bcae5a484e2e19555bd2b96938b860241a19d5156f0f4a8ae585e484e282a1818122686755bcbd2b969792938a8a860671b1a19952f0f4a8ac5a5e4c4a4e2c2a2c1a1812654bc3c2a19961792138a0a098606047952f0a870665e4e2826181166255bc3c3a2a961792138a0b8606047956f0aa5e4e2e18e55bc362b96938b86024956f0c8ae5e4a2e180126255bc
  | _ => 0
def g127D10 (j : Nat) : Nat := if j = 0 then 0x345478a8e962e4898a161833551e2a3864b17244c50a12183047aabc78acb17244c50b0c198aaf1e2b2c5c913142c3066345578f15962e4898a161833555e3c5658b9226285860cc68aaf1e2a2e4898a161833155e3c545c913142c3065b45578f15962e4898a14198aaf1e2b2c5c913142832da2a3c5474b17244c50b0c19aa949e2a3864b17244c50a121830482a4a78a8b9226285090c182355203c5464b17244c50a0c11ad155e3c545c913142c30662abc78a8b9226285860cb68aaf1e2b2c5c913142833155e3c5658b9226285065aabc78a8e1a2e4898a141997a58a131418d7a5c90e1418db973b61cb8558683cad8b5001d6b4c5ac9d50a1ba2ce4345d060060003fe56ff55bff46ff91bfd46ff11bfe36ff4dbfe06ff41bff45ff517fd35ff417fe34ff4d3fe04ff413fd03fb40bf501 else 0
def g127D11 (j : Nat) : Nat := if j = 0 then 0x78b2450c57f else 0
def g127L : Nat → Packing
  | 5 => (4, 6, 6, 0, 0, 5, 0, g127D5)
  | 6 => (277, 5, 6, 0, 0, 12, 0, g127D6)
  | 7 => (1236, 4, 6, 0, 0, 15, 0, g127D7)
  | 8 => (1030, 3, 6, 0, 0, 17, 0, g127D8)
  | 9 => (251, 2, 6, 0, 0, 16, 0, g127D9)
  | 10 => (21, 1, 6, 0, 0, 11, 0, g127D10)
  | 11 => (1, 0, 6, 0, 0, 1, 0, g127D11)
  | _ => emptyPacking
def g127I : Nat → Nat → Option (Nat × Nat)
  | 6, tag => lookupShort 2 6 1 4 2 0 (fun j => if j=0 then 0xa501c else 0) tag
  | 7, tag => lookupShort 139 418 4 11 9 0 (fun j => if j=0 then 0x13e0000000000030d47a8100043a9e8b041a000534000004e702c0a00c89bcbcbd80026100000255e4e17223807000000000604820000001c8000000027800000000000687000000058008be003638000c4bd64e25d99f29e0e2525260000000008a00053000df60000023c207934648000018800000083a000004ff8d400e754d800191265a970e123084000497bf987c804e62fb11ce045810c68226000c2c00e2b218a243b09d80a00204e0810b83c830000019bd564108639551da1a000000000000004393064ca011464c00010600000000001a123a0001e4000000000013580066e826000000000000016f0000000020f80000189668ccc000000000009a53b800000d6b2367d27f4e40b613aae4900840024fcd00031be401ee318000d3ddeb5c004c5001bac766d4465b8c004cd96483083ab1d531dc5d28bcf2a856d80056c000000005871e8000000002280000000098d522e157f23f7c6ed1fbb7e542184660032cc1ec70a5b672b48a8bf1366074f7c4671512cae000006ca0000020de3007c000000000019040000000000000000d900030ba1252195982ae5000a04000aa0000022d000055be40046d0001192e2650003761b25b000000002e900189089c6b0000000009e8fba536170920581a280004442230a2c40000007880000036a5b886ce341272495014993584bc8ce12400692c53a80006154011d4000dc932c4308c4709527c74469de628d1a800a030b800000dcd9e36ae0215e2ec3f0b30cdc2906cb887e2b752c911b2c512c62f17aa8b21253904830049030600083030666700300020040200f401820041a31010081320020611000217403432bc210100a1020c40103000050931010000108032111270002023011b0242 else 0) tag
  | 8, tag => lookupShort 618 1855 5 13 11 0 (fun j => if j=0 then 0x60000c59039ee2795310d00000000012d5898327d8cc0005fec87800189ccc730a66320000000000000000249800040e00000051e4001a685bb1220000b6e56c00000000000000000000000489000139b9b382204c431f9ae54fb07000000000027182d9bb2082f2e83003b0cbc0b412ec3a900000000009482536c8f67c1a00006ad96ab32c133810c0000000006b087000001b582e3246000d70a7f30d72eb4502b837df0dc4b827cd1029745a051d08d2867a22d27a72f391c2b80034b2000000612a2fa00061231e00000001608a9355fc39dc981b32180000e548b8001c3cc6f0000000ac600000000000008db531b1ff8e2e44916f6512c30000003296296e25e8491d78c500000028634bcd402fa37c74c46018c78001a444e580000009d9e05e39f5cd1d3a52000207c2f6d22ee0c49886e61c20ce1ee3d5084021c000000000000000023400000006170610004a8918280107723d800192f000000000000017a80000000cd0000e180000001fb83427f2000c8e000000000000007ac001b704522a4c599b49831abc311898c1a580023db2474cc80001663e24af0cbf7688ced9700012922bb0006f4c000000c3e32b5342000000065099bc2d09b8002028a8c5a56513749301d25524400000000000000fc000cad00007740000006b6d2f732996f23a40000000003238001b070000e58000000000723c000000000000045516e876ee3a7c3aa3000471742ac1919d80012448760002f20000000000414369842598da41f1684680004d961e80001d0001900a0000006f294f40008b3020902e263dbb91126ce000000000345a000000000000143a90082bd30ccaf0002a1c0000008fea7a400000000000013ac000def305a9a00009e8847805100a0101a0008610500050020000e00189201020000c300001116c0008040044001ea4984000000101400001c2010c008400404201802008800108c208402030a20ad000004510460080621084728400180403b000198c20080108c4a000436382300403000030048808c0018000008040000233400110002800200004004043b80020021000220084100c0100002000250840d000611840020401005e000c6500320280800884000522210000002030ce10186208000180010080718c200000130009004000002100412000200802001843580000030200061004220046021c2000c0301c20220600888000c0210c070800228801200c00044000c611040050003184e1204a100020290c2300a8280e8004400000010000504a401020000000008b084061006148080180000800a00061004000912101401004610010000160084403002518020088605180000d22004032000300c80000230002000000008000004000c6000021004440800038000200200000030042008c1200401040200001 else if j=1 then 0xe2aca4a74a0000000e480000ae0000003112000e5c80013f20000002ee0001461000202c001911c7c80019a2000000000000117f1be80022c00940000000000000c9d00fc000ab39592aa8001b681b3000000030800068a278a00000007bf5ee0001ec437c407a50d6ec24315038a00022c37feb87a5700016f400018e00032ac0004f280000240000004786098000000000105a000c81000000000048580000014624c4e6a11d03f40be00034e000049007b00000009a0c17e7ea00052f925b12a0000000001185a7b0000faf2a019a0000eec0002d1cc08ae898e13989b417640a49a00067c663a0fa5908000001c8616b80004d400093e892c00145641a00000000005c780032da4100000588001b73000000096aacf0a0329f39c0884fa4c2b27eb4447def833b70ccdf9905077e0000000003942000d4cab652d7b5a0068d38186000c26d0a89a412ee2c51a80ee30689083f4000388a05085a2f41a548d827459d3180000000000000000244175e000000209c001c42e672d468bc23950c800188ea95e260d2000119100012e32b10f309f27450569b0227274914200000020bb476000000000128736a000059118c8cf000478f344327c5c800306b220c1e856c001862939c8a435a0004c951ec57e0005e4c00a36e153496821157cc351b0e27d2ca000c95521095695c0c6b24000000050d800117a00000000000000004d7800000000000044a49039ff993255014db1085bcd5a06f09794a45aa868a7c148800022f14acc20000000334000446808c0000006d81486000068836d3c0000c6b10d80ac000dc80a7920842f00070880000000004f002d000000000030a78d985f800103e0000000002007cb6a6101ec000bea4a7f12750641a06bc9f86e94bfe3b000000000000000000000000000000348bc200000000000000000000001a88000000000000024500000000000a287dc0000001eb00000009619cd000186e000000112000091900000000001d01652768062afe1d303526861c1e132f7f50200015c0000464492e60ed88377a369006fb75391de592208000036c0000000842000000000000000000000025ac00441968e00000000000000001af300000000000000000f90001cb05aa0000000bbc571314d8a00e400005653a94a200048ea269bd9d4c4add542c284d8a89879f972000000311d33d8f22bba04c000000603c00000000000028dc00000061e0000000000464015200007900016b00ecc5acd365930abcfa86554a5cbe9078000000c54d39032f04206640443279810fe52dce6000000000000022bbc5d0004bc795087140e80000008a7000125140db22d698e840000000000002284a46c07000000086f000000224dca58e1ea5e967b3858befeb83b85c0c2ebcb392223000234b2ab836517e0e629c000d86c9 else if j=2 then 0x1839068e5000665f0580001478954000000a4aade0000a6c0000000001acb0000000000a270004fdb54c2e993b8092965b8d00000000000008b180000018f091e800089a0000000678000000000000237a000c24213c000000c8348b130f9f60b7e04400133c615a7775699df64ba02b3542d400070830840000000000001433000282b0eb4431bdc59d3b0bb10ff679a49ca028c5511b80f8558f50f6812d9b4000101580ca51000021524b2ec988c77062c37e00032607ba41fcc100000340a324da2ef99647e0004bfc24f196915f0110f400017389e043e0000000000000000192e2346e500c8c1a3800bd43f664ed6e589c725cdca412d3c41c5d238c8cfb3917213143e543d080309d4131b8963c2291ccc805aceccc00000063a80000010e18344b8e55dc8200064ec0019248140eb000000021f0000000000d18ea0860594c8e6326701338554ee16e85890a638a9a74a600025dedb4000a6600042d80011a600001c00e8b030f4097800000000030c00012c80000002578b820000000000000022800143a00000062b35f6000000000000000099acab575140f9828000336000211c1cb72a0000006d180000000004d5d71902307c4de40000005ba800317d029a460bf38b400000000017ae047d9b00012a290900000000010c4000470847ea841ff624a05e8a255eed1d709114878c6f325148b87e51f24102ed4588000001a61524a850137aa758fd21676b1880006057207c01572f18f13c00000000000fe8490002a6d4c18ef0a6c98a37e28b987d28000140e2294f383f0000055275449fb7f93230545b9818e366cc73643a722bcda67d28dadfc2a1802d3be9505128628000636800000002a00000018800000002264000000000624c000000000000290e000c20a96800084b06c00010a8000ca300c0001c7759b85cc78e00092108dc4dc00000028c38f4a6b0006374070000c12a884270c4f0000000000a3519947012ea00000000029a60001a78003230000a35800023f27100026b23743d2a1d8aaf7cd147e060000001309a4680010a33db1aeadf07463bd0000000001adf00000016a48c800048fb65400000000006740000f744c8445840c9ad0cb1348d50006ba0580000d5a882e3300005f625dc85ca40e0687ec7e012c5f8ac4c68bb3f20c21a458a000651a4cd4db95fa08a67c513b509c0e30133837142900000000000000000000bb300000000014cf1778e7c000a85000000000000000000030db3ab63e89fe3e13cd9d6e723634000000000255091600072d28bebc3109806d1160914dc8000000000000000000149d00000024e8000c4065065fb157a5572df4af3424418891257b9c00006a64a94bd03280000000000006be561c11d53acf5100fa41d6960400009a315851930fba2598250482a400081e61e54f20 else if j=3 then 0xb9e1e6000000140294d71826a6465dcea75e4ca9e74bca3d400000000000013f40000000000000000000000251b41b637afb87173a2ce200000002ac000000278200000000000008a557d00017f7822dae606737c000a4e40781a7c1ece7a6ac0014b1000443975c0009f3ad7c00000000061680c82040006f9676e2a90f14ee521f3aa05e040754b99d209e4f0001cca000000060000000011ff8b88c763991c342120e000114436a97112b086800191300043aa02688f0e3cc82438000df94ba80012cd0006f1b4182da42c41666bd248200000000000065649d919583bd7c6d8c34e97e97a086000132dc0e33219984c3986045727a18b5e5a26276dc1710680000000000004ff0001b30158800042e28a0006c490d43151b7e8f2811394056ea3a074000427000349a3dccc9c974000000de26e654b832be04e9be467364508c21b5723d08590 else 0) tag
  | 9, tag => lookupShort 515 1545 6 13 11 0 (fun j => if j=0 then 0xa443181657d89fa0d212b03c82bf0db8404cf22b42cfb6542f62f553db7145241d96c89351b4c2365cb8c6df745ac03304a526a4ef280aa781680000001ab00026f32220000006d2d6ce0009738000001c00da40c8177314cc3329b00000000000003422aa48924e7800096d000000000000018000000011f500000033e400000064367443364bfc61565603a9514b235fe00000000000000000000000000000000000310e000dac80000000a8000613000000000000016160004ff626742a000000444800189c0a9ccfe3c93f50b8642a709be9484453d604078941ee027408bb1ca0a7c000ba74dc4eb541a38e1c580025700000004bb00000001e763577633c8125087f6ae1ad00000000000000006aff5fa82fd6a20357940000ad80000000009f503b063f0b69fbcfd000092e442a908000000cd0211a1be94ad872f8762ea54000000243a000000660c00000000000037debaf513cad80019860006f680011dc000000043c00012b88d165a00000000033c038700048f73ee131c1ea45401e00000069c4000b8d0004c48001226000421a0a08c7481c8fc29c000c6bcac0001bfb08d000334b38601b09e947597453306dd1cd8dbce8497b0100f100000036b9a68000000306a00000046476b60fcd66c88751c8078ef80024b400000000035ab0d8000244f232b2e9ef80000013cfc75000000000098300000008331684fff5dd1e100023d42520000002d3f6e519b4fe4af1672b569e9a6aa5d2ad31f4000000036c00000026ef373c4980a76ed9ed53fe7080001de980cb1c78e00091680035c91210000000000000ddb00000019185edec74000000da7086e6fb05dd97ebc82b0beb5e1680b3cea88000000000000000000000009ebdb8634e30000001893000010400c21000840061c30010000030000420004430801811030070000830c008220218000008d0020131090000820030c00431800000001401c33500000c128000004204c04d0810070800050c10400400ca0440070020400030850002010004801010020060060031470000800c01c21400000000c000118008000a04220200610300210a4800c01030000c00070000410401040020800400420000803c100100008400000004d1000000430002040030060001010022000040094000c100000008200804000a0022020420410010021810c00410010c400100208000800128000034100404000208a0010800455013420000420430000010803004040020000c004200000208000000100004b0400000000000000c00000c00001401001800000c50c01820850020400410000040030091000810000402c00400050000000040c008020008100004400004000308214008100004200014000200000204204000008800508204000100108b0c0042000000000284040000040000 else if j=1 then 0x694b7000200086e000000356800042ac1a27e000003a800328c0008db48182c60b7000045918ba35cad0000000000ce4ac2216b81c937ef0c6bfb9f0004344001385c5380010c438c44f4f831fe9320000003108000000483f030a801e649840003bcd356d02592b810946c682e2000d6c800061b03400040426fe0004fc4f9d7a0000d7300015f22cb00062810b3bf918a295800000000000000000004070b753820004460000000194caa80022c82725af2b0408eac44f8edab7acbaa9338000000032d70885b7380004a3800000036613c00013f4000c1547ba51a000c5fed48000b0740a80024789d600000024ec0000002fcc001012000000000000000000033ae820000000000000099200006a63b21548000000000c2d00005bc0004a8c2404ca0001220000000000000000000026e837c7a80a4000106000123a0001ea800045e192dbf606b6393464738af80000000000000000000c51036b1e0000000000113f36d0e00000000000919000322889a87c82c45e91bad3be26c6150f783b888f665aafd12e104000000c448c6f40809243869542e728504b4a180000000000003212110c56000000000000023780008e0cd3800312a0005f10a3c0000000000002088000cc980000000008c662536c006c0790ecd56a0009172ef8000a03dfb01700000000006a4978a0000122ed40001e8577cbc60d58cc000000000000007080032361c6cfb23ec000000193000000194396fad2400015e000000000000000040a000000000000026771b9ccc2dbc0009b50000000000aad80a0efe3e99f948b8045103250000c5fb58719500000026633fe4642b3a1dda9589869f62cca90010809b54ab118d964eb19da7554ea81400000000062d04908fe000485d4f381d17bcc3221d9ca151800132c00000000000000008216b6c0000000002fc4000000d35c0ec0012140000000000000000073400000097b000317200002400036e9039915a5b041190c5094507630a819cd8de25c5152c9e25087470548c4c5771ca0000006f340000004df000303d12d4bd278f40202b8d3000238f87e0bac6047f1be6175647a46090f0006f040001b415be0c12fb8839c12c976aa1d1475aff32ca000000675474d1254d8a7300cb8f3ce7081d4a7b6192324d0000a5d50c8000000000d4380015a4000cd17014001977c24af500008c3000425e796000000298800080b97d6a6d76e0005a8000338800000000020448049b44c9f3113054f9c7980008ca000000154c000c83a84337e00000000000000005a568034e800090500022d123800002a827b3ed0de828c000000000418204a00000023340268c1c97e220001a4b87121f30c229a8d180000013330f868ec0000009e30b806463ac5ce8ed27212d604880305b437a402cf1269a3191a628a626c2a10c56c else if j=2 then 0x32ad3ded550748512000c74a52468a101c13aee30371d913981373331ecca84c0c19f33c99b8000001ae894c293c001bc05cd0b280000000006ae4000137000276c000058882c2f00d72abd630ff40011620000000000000000000033b8711f2c8cc000ab29610000000000548e3b5047902c6a000019682ccd0cd04165be3899a9062ed84f08583e33a60a10f7800357a000cc380000019225ac400800000045700000002315c78000000000d6600000019c55bcee847afaba82b496c6ebaeb60168261c90e39916294359393df601ec5169448d4840023e27b0bc80022bf190d84ef4511e00000004e53518d641ba79552e2c08048d1e72e000c96000129b0e800046b831a0b8db700023d2000000210e09cacf000207c00000048e0000001b6300000031b200012e0000000a6d0006e931a407211b416d6260abd3200021920000000ec000138a459cca266b9d407d031052600041880001ec0009c8882d4b103c91bc5a8000a70ce1e4fc00010600320e000080adcc00030a29970004ebb31c000000414c02eb435116aec00188008200017ba3154ace5208032fc99eaa535182a0c39ab4639e00019644e228b2d791621911fa000cb0872c000803923a4a80000005414ea6361063d79cbd400000043f800000114b990a6bc41cbdc1c4a78b7e5af0dbe048c1143519aea98d39000000008a800000056c055f24d0a647a2ef57b2c030000000000000dcc8001304aed82580005581fb00046934b2334da10ea07f588b96e06ec2d2bc949f0000000000000066b6700000000000001330cbc000077418f1142c5b49821a128827416125217c0cfb3660005aa0000000000971a208480000000000117c00000000030f400094e00000000000002e2000195c89380026f600000000025fcab153e4ca9241984c17455163c05f00000031850985300000152000000000000000000000003fe18b0000000000000a020f60001243000000000000054b000311c000000000000000000000007240009628000000b62c3ea30074b857cc021d20ce8ba4be67743fa28a06e68832f6b839e90e5a33eaaed1f00013b00009d5c34261ea4951249162e434494c8acf5513100004768000a4e9ddcf900000004b02cea338000000000172a0000002a112de8ef58263754730459ad0dad07da5f41f884f4382 else 0) tag
  | 10, tag => lookupShort 126 377 5 10 8 0 (fun j => if j=0 then 0xad11aea2a1dc201e8b327534c3a80000154545591910b5cdba0dd25a0400003d77322f20fac4f4000027b8350598db8de6614004a5bdedf6876b6ef100269dc8000020c000000000000000898c47cf86001100038a00000000c75a800ad5c5000000006600000001f814c00003cd135bc000b6100f4e3855003a469c97b424221e113c12adc728a6c0086400000df93c0054a65001b07dae9000982240000000c6000000000ce5b8f00007a060000022de0ede57ea800bbe0400000c4ef54f99a17dd9000009a117327c8c0e7e507d30e2f9e4d15518964d2ad0000000000d0c6202bcb9ebd22a6dc11c00e780097350b8400000005ae90f28004b0003ea44b44bb00000ca400003afc835e300a5fb3993740000321d2dd5000000af2df05e50003aaac1c41e6c000000000000000c74000017c001f733d7f575e2c5227d5958b8de8c8c80db8b1f9cce6b800003f2001bdf5b74000003ad36000084914523c00000000000086f0956b9c4b888f981fd839defa1260b0e6133f5dd39c0a6d4eec600048003a30000000000e4400000c2afc00e150fa7c00000009e0000000029800001d800316234005f59500000000ee000de52400633b2f0d313926724800138002cc008c0004d7a02e722000000000000000e50009d460014618082f0840008401000000080000024030e050447000220802900ce0604400280000840080043000012880000208002000001000200a00b000000180400001000a910c000104100400000a0 else 0) tag
  | 11, tag => lookupShort 11 33 3 7 5 0 (fun j => if j=0 then 0x121233832f8b05b8f4800002700011c7a2e41802a011400001500009806a10041 else 0) tag
  | _, _ => none
def g127 : Forest := ⟨127, 11, fun i => (g127Y[i]?).getD (0,0), g127C, [[]], g127L, g127I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P5n0 : block g127 5 0 4 = true := by decide +kernel
theorem g127B5 : block g127 5 0 4 = true := g127P5n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n0 : block g127 6 0 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n6 : block g127 6 6 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n12 : block g127 6 12 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n18 : block g127 6 18 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n24 : block g127 6 24 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n30 : block g127 6 30 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n36 : block g127 6 36 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n42 : block g127 6 42 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n48 : block g127 6 48 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n54 : block g127 6 54 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n60 : block g127 6 60 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n66 : block g127 6 66 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n72 : block g127 6 72 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n78 : block g127 6 78 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n84 : block g127 6 84 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n90 : block g127 6 90 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n96 : block g127 6 96 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n102 : block g127 6 102 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n108 : block g127 6 108 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n114 : block g127 6 114 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n120 : block g127 6 120 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n126 : block g127 6 126 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n132 : block g127 6 132 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n138 : block g127 6 138 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n144 : block g127 6 144 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n150 : block g127 6 150 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n156 : block g127 6 156 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n162 : block g127 6 162 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n168 : block g127 6 168 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n174 : block g127 6 174 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n180 : block g127 6 180 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n186 : block g127 6 186 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n192 : block g127 6 192 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n198 : block g127 6 198 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n204 : block g127 6 204 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n210 : block g127 6 210 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n216 : block g127 6 216 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n222 : block g127 6 222 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n228 : block g127 6 228 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n234 : block g127 6 234 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n240 : block g127 6 240 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n246 : block g127 6 246 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n252 : block g127 6 252 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n258 : block g127 6 258 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n264 : block g127 6 264 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n270 : block g127 6 270 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6n276 : block g127 6 276 1 = true := by decide +kernel
theorem g127B6 : block g127 6 0 277 = true := (@block_merge g127 6 0 138 139 (@block_merge g127 6 0 66 72 (@block_merge g127 6 0 30 36 (@block_merge g127 6 0 12 18 (@block_merge g127 6 0 6 6 g127P6n0 g127P6n6) (@block_merge g127 6 12 6 12 g127P6n12 (@block_merge g127 6 18 6 6 g127P6n18 g127P6n24))) (@block_merge g127 6 30 18 18 (@block_merge g127 6 30 6 12 g127P6n30 (@block_merge g127 6 36 6 6 g127P6n36 g127P6n42)) (@block_merge g127 6 48 6 12 g127P6n48 (@block_merge g127 6 54 6 6 g127P6n54 g127P6n60)))) (@block_merge g127 6 66 36 36 (@block_merge g127 6 66 18 18 (@block_merge g127 6 66 6 12 g127P6n66 (@block_merge g127 6 72 6 6 g127P6n72 g127P6n78)) (@block_merge g127 6 84 6 12 g127P6n84 (@block_merge g127 6 90 6 6 g127P6n90 g127P6n96))) (@block_merge g127 6 102 18 18 (@block_merge g127 6 102 6 12 g127P6n102 (@block_merge g127 6 108 6 6 g127P6n108 g127P6n114)) (@block_merge g127 6 120 6 12 g127P6n120 (@block_merge g127 6 126 6 6 g127P6n126 g127P6n132))))) (@block_merge g127 6 138 72 67 (@block_merge g127 6 138 36 36 (@block_merge g127 6 138 18 18 (@block_merge g127 6 138 6 12 g127P6n138 (@block_merge g127 6 144 6 6 g127P6n144 g127P6n150)) (@block_merge g127 6 156 6 12 g127P6n156 (@block_merge g127 6 162 6 6 g127P6n162 g127P6n168))) (@block_merge g127 6 174 18 18 (@block_merge g127 6 174 6 12 g127P6n174 (@block_merge g127 6 180 6 6 g127P6n180 g127P6n186)) (@block_merge g127 6 192 6 12 g127P6n192 (@block_merge g127 6 198 6 6 g127P6n198 g127P6n204)))) (@block_merge g127 6 210 36 31 (@block_merge g127 6 210 18 18 (@block_merge g127 6 210 6 12 g127P6n210 (@block_merge g127 6 216 6 6 g127P6n216 g127P6n222)) (@block_merge g127 6 228 6 12 g127P6n228 (@block_merge g127 6 234 6 6 g127P6n234 g127P6n240))) (@block_merge g127 6 246 18 13 (@block_merge g127 6 246 6 12 g127P6n246 (@block_merge g127 6 252 6 6 g127P6n252 g127P6n258)) (@block_merge g127 6 264 6 7 g127P6n264 (@block_merge g127 6 270 6 1 g127P6n270 g127P6n276))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n0 : block g127 7 0 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n6 : block g127 7 6 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n12 : block g127 7 12 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n18 : block g127 7 18 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n24 : block g127 7 24 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n30 : block g127 7 30 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n36 : block g127 7 36 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n42 : block g127 7 42 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n48 : block g127 7 48 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n54 : block g127 7 54 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n60 : block g127 7 60 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n66 : block g127 7 66 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n72 : block g127 7 72 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n78 : block g127 7 78 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n84 : block g127 7 84 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n90 : block g127 7 90 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n96 : block g127 7 96 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n102 : block g127 7 102 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n108 : block g127 7 108 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n114 : block g127 7 114 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n120 : block g127 7 120 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n126 : block g127 7 126 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n132 : block g127 7 132 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n138 : block g127 7 138 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n144 : block g127 7 144 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n150 : block g127 7 150 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n156 : block g127 7 156 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n162 : block g127 7 162 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n168 : block g127 7 168 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n174 : block g127 7 174 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n180 : block g127 7 180 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n186 : block g127 7 186 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n192 : block g127 7 192 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n198 : block g127 7 198 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n204 : block g127 7 204 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n210 : block g127 7 210 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n216 : block g127 7 216 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n222 : block g127 7 222 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n228 : block g127 7 228 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n234 : block g127 7 234 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n240 : block g127 7 240 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n246 : block g127 7 246 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n252 : block g127 7 252 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n258 : block g127 7 258 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n264 : block g127 7 264 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n270 : block g127 7 270 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n276 : block g127 7 276 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n282 : block g127 7 282 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n288 : block g127 7 288 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n294 : block g127 7 294 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n300 : block g127 7 300 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n306 : block g127 7 306 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n312 : block g127 7 312 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n318 : block g127 7 318 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n324 : block g127 7 324 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n330 : block g127 7 330 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n336 : block g127 7 336 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n342 : block g127 7 342 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n348 : block g127 7 348 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n354 : block g127 7 354 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n360 : block g127 7 360 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n366 : block g127 7 366 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n372 : block g127 7 372 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n378 : block g127 7 378 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n384 : block g127 7 384 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n390 : block g127 7 390 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n396 : block g127 7 396 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n402 : block g127 7 402 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n408 : block g127 7 408 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n414 : block g127 7 414 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n420 : block g127 7 420 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n426 : block g127 7 426 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n432 : block g127 7 432 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n438 : block g127 7 438 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n444 : block g127 7 444 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n450 : block g127 7 450 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n456 : block g127 7 456 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n462 : block g127 7 462 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n468 : block g127 7 468 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n474 : block g127 7 474 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n480 : block g127 7 480 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n486 : block g127 7 486 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n492 : block g127 7 492 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n498 : block g127 7 498 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n504 : block g127 7 504 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n510 : block g127 7 510 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n516 : block g127 7 516 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n522 : block g127 7 522 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n528 : block g127 7 528 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n534 : block g127 7 534 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n540 : block g127 7 540 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n546 : block g127 7 546 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n552 : block g127 7 552 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n558 : block g127 7 558 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n564 : block g127 7 564 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n570 : block g127 7 570 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n576 : block g127 7 576 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n582 : block g127 7 582 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n588 : block g127 7 588 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n594 : block g127 7 594 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n600 : block g127 7 600 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n606 : block g127 7 606 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n612 : block g127 7 612 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n618 : block g127 7 618 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n624 : block g127 7 624 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n630 : block g127 7 630 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n636 : block g127 7 636 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n642 : block g127 7 642 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n648 : block g127 7 648 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n654 : block g127 7 654 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n660 : block g127 7 660 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n666 : block g127 7 666 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n672 : block g127 7 672 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n678 : block g127 7 678 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n684 : block g127 7 684 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n690 : block g127 7 690 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n696 : block g127 7 696 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n702 : block g127 7 702 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n708 : block g127 7 708 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n714 : block g127 7 714 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n720 : block g127 7 720 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n726 : block g127 7 726 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n732 : block g127 7 732 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n738 : block g127 7 738 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n744 : block g127 7 744 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n750 : block g127 7 750 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n756 : block g127 7 756 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n762 : block g127 7 762 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n768 : block g127 7 768 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n774 : block g127 7 774 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n780 : block g127 7 780 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n786 : block g127 7 786 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n792 : block g127 7 792 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n798 : block g127 7 798 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n804 : block g127 7 804 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n810 : block g127 7 810 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n816 : block g127 7 816 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n822 : block g127 7 822 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n828 : block g127 7 828 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n834 : block g127 7 834 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n840 : block g127 7 840 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n846 : block g127 7 846 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n852 : block g127 7 852 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n858 : block g127 7 858 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n864 : block g127 7 864 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n870 : block g127 7 870 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n876 : block g127 7 876 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n882 : block g127 7 882 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n888 : block g127 7 888 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n894 : block g127 7 894 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n900 : block g127 7 900 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n906 : block g127 7 906 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n912 : block g127 7 912 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n918 : block g127 7 918 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n924 : block g127 7 924 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n930 : block g127 7 930 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n936 : block g127 7 936 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n942 : block g127 7 942 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n948 : block g127 7 948 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n954 : block g127 7 954 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n960 : block g127 7 960 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n966 : block g127 7 966 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n972 : block g127 7 972 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n978 : block g127 7 978 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n984 : block g127 7 984 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n990 : block g127 7 990 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n996 : block g127 7 996 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n1002 : block g127 7 1002 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n1008 : block g127 7 1008 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n1014 : block g127 7 1014 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n1020 : block g127 7 1020 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n1026 : block g127 7 1026 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n1032 : block g127 7 1032 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n1038 : block g127 7 1038 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n1044 : block g127 7 1044 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n1050 : block g127 7 1050 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n1056 : block g127 7 1056 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n1062 : block g127 7 1062 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n1068 : block g127 7 1068 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n1074 : block g127 7 1074 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n1080 : block g127 7 1080 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n1086 : block g127 7 1086 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n1092 : block g127 7 1092 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n1098 : block g127 7 1098 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n1104 : block g127 7 1104 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n1110 : block g127 7 1110 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n1116 : block g127 7 1116 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n1122 : block g127 7 1122 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n1128 : block g127 7 1128 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n1134 : block g127 7 1134 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n1140 : block g127 7 1140 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n1146 : block g127 7 1146 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n1152 : block g127 7 1152 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n1158 : block g127 7 1158 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n1164 : block g127 7 1164 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n1170 : block g127 7 1170 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n1176 : block g127 7 1176 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n1182 : block g127 7 1182 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n1188 : block g127 7 1188 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n1194 : block g127 7 1194 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n1200 : block g127 7 1200 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n1206 : block g127 7 1206 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n1212 : block g127 7 1212 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n1218 : block g127 7 1218 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n1224 : block g127 7 1224 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7n1230 : block g127 7 1230 6 = true := by decide +kernel
theorem g127B7 : block g127 7 0 1236 = true := (@block_merge g127 7 0 618 618 (@block_merge g127 7 0 306 312 (@block_merge g127 7 0 150 156 (@block_merge g127 7 0 72 78 (@block_merge g127 7 0 36 36 (@block_merge g127 7 0 18 18 (@block_merge g127 7 0 6 12 g127P7n0 (@block_merge g127 7 6 6 6 g127P7n6 g127P7n12)) (@block_merge g127 7 18 6 12 g127P7n18 (@block_merge g127 7 24 6 6 g127P7n24 g127P7n30))) (@block_merge g127 7 36 18 18 (@block_merge g127 7 36 6 12 g127P7n36 (@block_merge g127 7 42 6 6 g127P7n42 g127P7n48)) (@block_merge g127 7 54 6 12 g127P7n54 (@block_merge g127 7 60 6 6 g127P7n60 g127P7n66)))) (@block_merge g127 7 72 36 42 (@block_merge g127 7 72 18 18 (@block_merge g127 7 72 6 12 g127P7n72 (@block_merge g127 7 78 6 6 g127P7n78 g127P7n84)) (@block_merge g127 7 90 6 12 g127P7n90 (@block_merge g127 7 96 6 6 g127P7n96 g127P7n102))) (@block_merge g127 7 108 18 24 (@block_merge g127 7 108 6 12 g127P7n108 (@block_merge g127 7 114 6 6 g127P7n114 g127P7n120)) (@block_merge g127 7 126 12 12 (@block_merge g127 7 126 6 6 g127P7n126 g127P7n132) (@block_merge g127 7 138 6 6 g127P7n138 g127P7n144))))) (@block_merge g127 7 150 78 78 (@block_merge g127 7 150 36 42 (@block_merge g127 7 150 18 18 (@block_merge g127 7 150 6 12 g127P7n150 (@block_merge g127 7 156 6 6 g127P7n156 g127P7n162)) (@block_merge g127 7 168 6 12 g127P7n168 (@block_merge g127 7 174 6 6 g127P7n174 g127P7n180))) (@block_merge g127 7 186 18 24 (@block_merge g127 7 186 6 12 g127P7n186 (@block_merge g127 7 192 6 6 g127P7n192 g127P7n198)) (@block_merge g127 7 204 12 12 (@block_merge g127 7 204 6 6 g127P7n204 g127P7n210) (@block_merge g127 7 216 6 6 g127P7n216 g127P7n222)))) (@block_merge g127 7 228 36 42 (@block_merge g127 7 228 18 18 (@block_merge g127 7 228 6 12 g127P7n228 (@block_merge g127 7 234 6 6 g127P7n234 g127P7n240)) (@block_merge g127 7 246 6 12 g127P7n246 (@block_merge g127 7 252 6 6 g127P7n252 g127P7n258))) (@block_merge g127 7 264 18 24 (@block_merge g127 7 264 6 12 g127P7n264 (@block_merge g127 7 270 6 6 g127P7n270 g127P7n276)) (@block_merge g127 7 282 12 12 (@block_merge g127 7 282 6 6 g127P7n282 g127P7n288) (@block_merge g127 7 294 6 6 g127P7n294 g127P7n300)))))) (@block_merge g127 7 306 156 156 (@block_merge g127 7 306 78 78 (@block_merge g127 7 306 36 42 (@block_merge g127 7 306 18 18 (@block_merge g127 7 306 6 12 g127P7n306 (@block_merge g127 7 312 6 6 g127P7n312 g127P7n318)) (@block_merge g127 7 324 6 12 g127P7n324 (@block_merge g127 7 330 6 6 g127P7n330 g127P7n336))) (@block_merge g127 7 342 18 24 (@block_merge g127 7 342 6 12 g127P7n342 (@block_merge g127 7 348 6 6 g127P7n348 g127P7n354)) (@block_merge g127 7 360 12 12 (@block_merge g127 7 360 6 6 g127P7n360 g127P7n366) (@block_merge g127 7 372 6 6 g127P7n372 g127P7n378)))) (@block_merge g127 7 384 36 42 (@block_merge g127 7 384 18 18 (@block_merge g127 7 384 6 12 g127P7n384 (@block_merge g127 7 390 6 6 g127P7n390 g127P7n396)) (@block_merge g127 7 402 6 12 g127P7n402 (@block_merge g127 7 408 6 6 g127P7n408 g127P7n414))) (@block_merge g127 7 420 18 24 (@block_merge g127 7 420 6 12 g127P7n420 (@block_merge g127 7 426 6 6 g127P7n426 g127P7n432)) (@block_merge g127 7 438 12 12 (@block_merge g127 7 438 6 6 g127P7n438 g127P7n444) (@block_merge g127 7 450 6 6 g127P7n450 g127P7n456))))) (@block_merge g127 7 462 78 78 (@block_merge g127 7 462 36 42 (@block_merge g127 7 462 18 18 (@block_merge g127 7 462 6 12 g127P7n462 (@block_merge g127 7 468 6 6 g127P7n468 g127P7n474)) (@block_merge g127 7 480 6 12 g127P7n480 (@block_merge g127 7 486 6 6 g127P7n486 g127P7n492))) (@block_merge g127 7 498 18 24 (@block_merge g127 7 498 6 12 g127P7n498 (@block_merge g127 7 504 6 6 g127P7n504 g127P7n510)) (@block_merge g127 7 516 12 12 (@block_merge g127 7 516 6 6 g127P7n516 g127P7n522) (@block_merge g127 7 528 6 6 g127P7n528 g127P7n534)))) (@block_merge g127 7 540 36 42 (@block_merge g127 7 540 18 18 (@block_merge g127 7 540 6 12 g127P7n540 (@block_merge g127 7 546 6 6 g127P7n546 g127P7n552)) (@block_merge g127 7 558 6 12 g127P7n558 (@block_merge g127 7 564 6 6 g127P7n564 g127P7n570))) (@block_merge g127 7 576 18 24 (@block_merge g127 7 576 6 12 g127P7n576 (@block_merge g127 7 582 6 6 g127P7n582 g127P7n588)) (@block_merge g127 7 594 12 12 (@block_merge g127 7 594 6 6 g127P7n594 g127P7n600) (@block_merge g127 7 606 6 6 g127P7n606 g127P7n612))))))) (@block_merge g127 7 618 306 312 (@block_merge g127 7 618 150 156 (@block_merge g127 7 618 72 78 (@block_merge g127 7 618 36 36 (@block_merge g127 7 618 18 18 (@block_merge g127 7 618 6 12 g127P7n618 (@block_merge g127 7 624 6 6 g127P7n624 g127P7n630)) (@block_merge g127 7 636 6 12 g127P7n636 (@block_merge g127 7 642 6 6 g127P7n642 g127P7n648))) (@block_merge g127 7 654 18 18 (@block_merge g127 7 654 6 12 g127P7n654 (@block_merge g127 7 660 6 6 g127P7n660 g127P7n666)) (@block_merge g127 7 672 6 12 g127P7n672 (@block_merge g127 7 678 6 6 g127P7n678 g127P7n684)))) (@block_merge g127 7 690 36 42 (@block_merge g127 7 690 18 18 (@block_merge g127 7 690 6 12 g127P7n690 (@block_merge g127 7 696 6 6 g127P7n696 g127P7n702)) (@block_merge g127 7 708 6 12 g127P7n708 (@block_merge g127 7 714 6 6 g127P7n714 g127P7n720))) (@block_merge g127 7 726 18 24 (@block_merge g127 7 726 6 12 g127P7n726 (@block_merge g127 7 732 6 6 g127P7n732 g127P7n738)) (@block_merge g127 7 744 12 12 (@block_merge g127 7 744 6 6 g127P7n744 g127P7n750) (@block_merge g127 7 756 6 6 g127P7n756 g127P7n762))))) (@block_merge g127 7 768 78 78 (@block_merge g127 7 768 36 42 (@block_merge g127 7 768 18 18 (@block_merge g127 7 768 6 12 g127P7n768 (@block_merge g127 7 774 6 6 g127P7n774 g127P7n780)) (@block_merge g127 7 786 6 12 g127P7n786 (@block_merge g127 7 792 6 6 g127P7n792 g127P7n798))) (@block_merge g127 7 804 18 24 (@block_merge g127 7 804 6 12 g127P7n804 (@block_merge g127 7 810 6 6 g127P7n810 g127P7n816)) (@block_merge g127 7 822 12 12 (@block_merge g127 7 822 6 6 g127P7n822 g127P7n828) (@block_merge g127 7 834 6 6 g127P7n834 g127P7n840)))) (@block_merge g127 7 846 36 42 (@block_merge g127 7 846 18 18 (@block_merge g127 7 846 6 12 g127P7n846 (@block_merge g127 7 852 6 6 g127P7n852 g127P7n858)) (@block_merge g127 7 864 6 12 g127P7n864 (@block_merge g127 7 870 6 6 g127P7n870 g127P7n876))) (@block_merge g127 7 882 18 24 (@block_merge g127 7 882 6 12 g127P7n882 (@block_merge g127 7 888 6 6 g127P7n888 g127P7n894)) (@block_merge g127 7 900 12 12 (@block_merge g127 7 900 6 6 g127P7n900 g127P7n906) (@block_merge g127 7 912 6 6 g127P7n912 g127P7n918)))))) (@block_merge g127 7 924 156 156 (@block_merge g127 7 924 78 78 (@block_merge g127 7 924 36 42 (@block_merge g127 7 924 18 18 (@block_merge g127 7 924 6 12 g127P7n924 (@block_merge g127 7 930 6 6 g127P7n930 g127P7n936)) (@block_merge g127 7 942 6 12 g127P7n942 (@block_merge g127 7 948 6 6 g127P7n948 g127P7n954))) (@block_merge g127 7 960 18 24 (@block_merge g127 7 960 6 12 g127P7n960 (@block_merge g127 7 966 6 6 g127P7n966 g127P7n972)) (@block_merge g127 7 978 12 12 (@block_merge g127 7 978 6 6 g127P7n978 g127P7n984) (@block_merge g127 7 990 6 6 g127P7n990 g127P7n996)))) (@block_merge g127 7 1002 36 42 (@block_merge g127 7 1002 18 18 (@block_merge g127 7 1002 6 12 g127P7n1002 (@block_merge g127 7 1008 6 6 g127P7n1008 g127P7n1014)) (@block_merge g127 7 1020 6 12 g127P7n1020 (@block_merge g127 7 1026 6 6 g127P7n1026 g127P7n1032))) (@block_merge g127 7 1038 18 24 (@block_merge g127 7 1038 6 12 g127P7n1038 (@block_merge g127 7 1044 6 6 g127P7n1044 g127P7n1050)) (@block_merge g127 7 1056 12 12 (@block_merge g127 7 1056 6 6 g127P7n1056 g127P7n1062) (@block_merge g127 7 1068 6 6 g127P7n1068 g127P7n1074))))) (@block_merge g127 7 1080 78 78 (@block_merge g127 7 1080 36 42 (@block_merge g127 7 1080 18 18 (@block_merge g127 7 1080 6 12 g127P7n1080 (@block_merge g127 7 1086 6 6 g127P7n1086 g127P7n1092)) (@block_merge g127 7 1098 6 12 g127P7n1098 (@block_merge g127 7 1104 6 6 g127P7n1104 g127P7n1110))) (@block_merge g127 7 1116 18 24 (@block_merge g127 7 1116 6 12 g127P7n1116 (@block_merge g127 7 1122 6 6 g127P7n1122 g127P7n1128)) (@block_merge g127 7 1134 12 12 (@block_merge g127 7 1134 6 6 g127P7n1134 g127P7n1140) (@block_merge g127 7 1146 6 6 g127P7n1146 g127P7n1152)))) (@block_merge g127 7 1158 36 42 (@block_merge g127 7 1158 18 18 (@block_merge g127 7 1158 6 12 g127P7n1158 (@block_merge g127 7 1164 6 6 g127P7n1164 g127P7n1170)) (@block_merge g127 7 1176 6 12 g127P7n1176 (@block_merge g127 7 1182 6 6 g127P7n1182 g127P7n1188))) (@block_merge g127 7 1194 18 24 (@block_merge g127 7 1194 6 12 g127P7n1194 (@block_merge g127 7 1200 6 6 g127P7n1200 g127P7n1206)) (@block_merge g127 7 1212 12 12 (@block_merge g127 7 1212 6 6 g127P7n1212 g127P7n1218) (@block_merge g127 7 1224 6 6 g127P7n1224 g127P7n1230))))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n0 : block g127 8 0 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n6 : block g127 8 6 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n12 : block g127 8 12 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n18 : block g127 8 18 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n24 : block g127 8 24 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n30 : block g127 8 30 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n36 : block g127 8 36 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n42 : block g127 8 42 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n48 : block g127 8 48 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n54 : block g127 8 54 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n60 : block g127 8 60 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n66 : block g127 8 66 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n72 : block g127 8 72 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n78 : block g127 8 78 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n84 : block g127 8 84 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n90 : block g127 8 90 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n96 : block g127 8 96 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n102 : block g127 8 102 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n108 : block g127 8 108 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n114 : block g127 8 114 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n120 : block g127 8 120 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n126 : block g127 8 126 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n132 : block g127 8 132 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n138 : block g127 8 138 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n144 : block g127 8 144 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n150 : block g127 8 150 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n156 : block g127 8 156 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n162 : block g127 8 162 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n168 : block g127 8 168 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n174 : block g127 8 174 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n180 : block g127 8 180 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n186 : block g127 8 186 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n192 : block g127 8 192 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n198 : block g127 8 198 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n204 : block g127 8 204 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n210 : block g127 8 210 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n216 : block g127 8 216 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n222 : block g127 8 222 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n228 : block g127 8 228 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n234 : block g127 8 234 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n240 : block g127 8 240 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n246 : block g127 8 246 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n252 : block g127 8 252 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n258 : block g127 8 258 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n264 : block g127 8 264 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n270 : block g127 8 270 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n276 : block g127 8 276 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n282 : block g127 8 282 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n288 : block g127 8 288 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n294 : block g127 8 294 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n300 : block g127 8 300 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n306 : block g127 8 306 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n312 : block g127 8 312 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n318 : block g127 8 318 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n324 : block g127 8 324 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n330 : block g127 8 330 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n336 : block g127 8 336 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n342 : block g127 8 342 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n348 : block g127 8 348 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n354 : block g127 8 354 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n360 : block g127 8 360 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n366 : block g127 8 366 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n372 : block g127 8 372 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n378 : block g127 8 378 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n384 : block g127 8 384 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n390 : block g127 8 390 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n396 : block g127 8 396 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n402 : block g127 8 402 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n408 : block g127 8 408 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n414 : block g127 8 414 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n420 : block g127 8 420 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n426 : block g127 8 426 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n432 : block g127 8 432 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n438 : block g127 8 438 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n444 : block g127 8 444 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n450 : block g127 8 450 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n456 : block g127 8 456 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n462 : block g127 8 462 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n468 : block g127 8 468 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n474 : block g127 8 474 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n480 : block g127 8 480 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n486 : block g127 8 486 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n492 : block g127 8 492 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n498 : block g127 8 498 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n504 : block g127 8 504 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n510 : block g127 8 510 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n516 : block g127 8 516 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n522 : block g127 8 522 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n528 : block g127 8 528 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n534 : block g127 8 534 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n540 : block g127 8 540 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n546 : block g127 8 546 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n552 : block g127 8 552 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n558 : block g127 8 558 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n564 : block g127 8 564 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n570 : block g127 8 570 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n576 : block g127 8 576 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n582 : block g127 8 582 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n588 : block g127 8 588 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n594 : block g127 8 594 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n600 : block g127 8 600 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n606 : block g127 8 606 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n612 : block g127 8 612 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n618 : block g127 8 618 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n624 : block g127 8 624 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n630 : block g127 8 630 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n636 : block g127 8 636 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n642 : block g127 8 642 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n648 : block g127 8 648 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n654 : block g127 8 654 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n660 : block g127 8 660 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n666 : block g127 8 666 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n672 : block g127 8 672 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n678 : block g127 8 678 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n684 : block g127 8 684 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n690 : block g127 8 690 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n696 : block g127 8 696 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n702 : block g127 8 702 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n708 : block g127 8 708 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n714 : block g127 8 714 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n720 : block g127 8 720 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n726 : block g127 8 726 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n732 : block g127 8 732 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n738 : block g127 8 738 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n744 : block g127 8 744 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n750 : block g127 8 750 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n756 : block g127 8 756 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n762 : block g127 8 762 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n768 : block g127 8 768 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n774 : block g127 8 774 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n780 : block g127 8 780 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n786 : block g127 8 786 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n792 : block g127 8 792 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n798 : block g127 8 798 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n804 : block g127 8 804 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n810 : block g127 8 810 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n816 : block g127 8 816 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n822 : block g127 8 822 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n828 : block g127 8 828 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n834 : block g127 8 834 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n840 : block g127 8 840 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n846 : block g127 8 846 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n852 : block g127 8 852 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n858 : block g127 8 858 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n864 : block g127 8 864 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n870 : block g127 8 870 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n876 : block g127 8 876 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n882 : block g127 8 882 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n888 : block g127 8 888 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n894 : block g127 8 894 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n900 : block g127 8 900 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n906 : block g127 8 906 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n912 : block g127 8 912 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n918 : block g127 8 918 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n924 : block g127 8 924 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n930 : block g127 8 930 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n936 : block g127 8 936 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n942 : block g127 8 942 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n948 : block g127 8 948 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n954 : block g127 8 954 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n960 : block g127 8 960 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n966 : block g127 8 966 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n972 : block g127 8 972 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n978 : block g127 8 978 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n984 : block g127 8 984 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n990 : block g127 8 990 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n996 : block g127 8 996 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n1002 : block g127 8 1002 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n1008 : block g127 8 1008 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n1014 : block g127 8 1014 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n1020 : block g127 8 1020 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n1026 : block g127 8 1026 4 = true := by decide +kernel
theorem g127B8 : block g127 8 0 1030 = true := (@block_merge g127 8 0 516 514 (@block_merge g127 8 0 258 258 (@block_merge g127 8 0 126 132 (@block_merge g127 8 0 60 66 (@block_merge g127 8 0 30 30 (@block_merge g127 8 0 12 18 (@block_merge g127 8 0 6 6 g127P8n0 g127P8n6) (@block_merge g127 8 12 6 12 g127P8n12 (@block_merge g127 8 18 6 6 g127P8n18 g127P8n24))) (@block_merge g127 8 30 12 18 (@block_merge g127 8 30 6 6 g127P8n30 g127P8n36) (@block_merge g127 8 42 6 12 g127P8n42 (@block_merge g127 8 48 6 6 g127P8n48 g127P8n54)))) (@block_merge g127 8 60 30 36 (@block_merge g127 8 60 12 18 (@block_merge g127 8 60 6 6 g127P8n60 g127P8n66) (@block_merge g127 8 72 6 12 g127P8n72 (@block_merge g127 8 78 6 6 g127P8n78 g127P8n84))) (@block_merge g127 8 90 18 18 (@block_merge g127 8 90 6 12 g127P8n90 (@block_merge g127 8 96 6 6 g127P8n96 g127P8n102)) (@block_merge g127 8 108 6 12 g127P8n108 (@block_merge g127 8 114 6 6 g127P8n114 g127P8n120))))) (@block_merge g127 8 126 66 66 (@block_merge g127 8 126 30 36 (@block_merge g127 8 126 12 18 (@block_merge g127 8 126 6 6 g127P8n126 g127P8n132) (@block_merge g127 8 138 6 12 g127P8n138 (@block_merge g127 8 144 6 6 g127P8n144 g127P8n150))) (@block_merge g127 8 156 18 18 (@block_merge g127 8 156 6 12 g127P8n156 (@block_merge g127 8 162 6 6 g127P8n162 g127P8n168)) (@block_merge g127 8 174 6 12 g127P8n174 (@block_merge g127 8 180 6 6 g127P8n180 g127P8n186)))) (@block_merge g127 8 192 30 36 (@block_merge g127 8 192 12 18 (@block_merge g127 8 192 6 6 g127P8n192 g127P8n198) (@block_merge g127 8 204 6 12 g127P8n204 (@block_merge g127 8 210 6 6 g127P8n210 g127P8n216))) (@block_merge g127 8 222 18 18 (@block_merge g127 8 222 6 12 g127P8n222 (@block_merge g127 8 228 6 6 g127P8n228 g127P8n234)) (@block_merge g127 8 240 6 12 g127P8n240 (@block_merge g127 8 246 6 6 g127P8n246 g127P8n252)))))) (@block_merge g127 8 258 126 132 (@block_merge g127 8 258 60 66 (@block_merge g127 8 258 30 30 (@block_merge g127 8 258 12 18 (@block_merge g127 8 258 6 6 g127P8n258 g127P8n264) (@block_merge g127 8 270 6 12 g127P8n270 (@block_merge g127 8 276 6 6 g127P8n276 g127P8n282))) (@block_merge g127 8 288 12 18 (@block_merge g127 8 288 6 6 g127P8n288 g127P8n294) (@block_merge g127 8 300 6 12 g127P8n300 (@block_merge g127 8 306 6 6 g127P8n306 g127P8n312)))) (@block_merge g127 8 318 30 36 (@block_merge g127 8 318 12 18 (@block_merge g127 8 318 6 6 g127P8n318 g127P8n324) (@block_merge g127 8 330 6 12 g127P8n330 (@block_merge g127 8 336 6 6 g127P8n336 g127P8n342))) (@block_merge g127 8 348 18 18 (@block_merge g127 8 348 6 12 g127P8n348 (@block_merge g127 8 354 6 6 g127P8n354 g127P8n360)) (@block_merge g127 8 366 6 12 g127P8n366 (@block_merge g127 8 372 6 6 g127P8n372 g127P8n378))))) (@block_merge g127 8 384 66 66 (@block_merge g127 8 384 30 36 (@block_merge g127 8 384 12 18 (@block_merge g127 8 384 6 6 g127P8n384 g127P8n390) (@block_merge g127 8 396 6 12 g127P8n396 (@block_merge g127 8 402 6 6 g127P8n402 g127P8n408))) (@block_merge g127 8 414 18 18 (@block_merge g127 8 414 6 12 g127P8n414 (@block_merge g127 8 420 6 6 g127P8n420 g127P8n426)) (@block_merge g127 8 432 6 12 g127P8n432 (@block_merge g127 8 438 6 6 g127P8n438 g127P8n444)))) (@block_merge g127 8 450 30 36 (@block_merge g127 8 450 12 18 (@block_merge g127 8 450 6 6 g127P8n450 g127P8n456) (@block_merge g127 8 462 6 12 g127P8n462 (@block_merge g127 8 468 6 6 g127P8n468 g127P8n474))) (@block_merge g127 8 480 18 18 (@block_merge g127 8 480 6 12 g127P8n480 (@block_merge g127 8 486 6 6 g127P8n486 g127P8n492)) (@block_merge g127 8 498 6 12 g127P8n498 (@block_merge g127 8 504 6 6 g127P8n504 g127P8n510))))))) (@block_merge g127 8 516 258 256 (@block_merge g127 8 516 126 132 (@block_merge g127 8 516 60 66 (@block_merge g127 8 516 30 30 (@block_merge g127 8 516 12 18 (@block_merge g127 8 516 6 6 g127P8n516 g127P8n522) (@block_merge g127 8 528 6 12 g127P8n528 (@block_merge g127 8 534 6 6 g127P8n534 g127P8n540))) (@block_merge g127 8 546 12 18 (@block_merge g127 8 546 6 6 g127P8n546 g127P8n552) (@block_merge g127 8 558 6 12 g127P8n558 (@block_merge g127 8 564 6 6 g127P8n564 g127P8n570)))) (@block_merge g127 8 576 30 36 (@block_merge g127 8 576 12 18 (@block_merge g127 8 576 6 6 g127P8n576 g127P8n582) (@block_merge g127 8 588 6 12 g127P8n588 (@block_merge g127 8 594 6 6 g127P8n594 g127P8n600))) (@block_merge g127 8 606 18 18 (@block_merge g127 8 606 6 12 g127P8n606 (@block_merge g127 8 612 6 6 g127P8n612 g127P8n618)) (@block_merge g127 8 624 6 12 g127P8n624 (@block_merge g127 8 630 6 6 g127P8n630 g127P8n636))))) (@block_merge g127 8 642 66 66 (@block_merge g127 8 642 30 36 (@block_merge g127 8 642 12 18 (@block_merge g127 8 642 6 6 g127P8n642 g127P8n648) (@block_merge g127 8 654 6 12 g127P8n654 (@block_merge g127 8 660 6 6 g127P8n660 g127P8n666))) (@block_merge g127 8 672 18 18 (@block_merge g127 8 672 6 12 g127P8n672 (@block_merge g127 8 678 6 6 g127P8n678 g127P8n684)) (@block_merge g127 8 690 6 12 g127P8n690 (@block_merge g127 8 696 6 6 g127P8n696 g127P8n702)))) (@block_merge g127 8 708 30 36 (@block_merge g127 8 708 12 18 (@block_merge g127 8 708 6 6 g127P8n708 g127P8n714) (@block_merge g127 8 720 6 12 g127P8n720 (@block_merge g127 8 726 6 6 g127P8n726 g127P8n732))) (@block_merge g127 8 738 18 18 (@block_merge g127 8 738 6 12 g127P8n738 (@block_merge g127 8 744 6 6 g127P8n744 g127P8n750)) (@block_merge g127 8 756 6 12 g127P8n756 (@block_merge g127 8 762 6 6 g127P8n762 g127P8n768)))))) (@block_merge g127 8 774 126 130 (@block_merge g127 8 774 60 66 (@block_merge g127 8 774 30 30 (@block_merge g127 8 774 12 18 (@block_merge g127 8 774 6 6 g127P8n774 g127P8n780) (@block_merge g127 8 786 6 12 g127P8n786 (@block_merge g127 8 792 6 6 g127P8n792 g127P8n798))) (@block_merge g127 8 804 12 18 (@block_merge g127 8 804 6 6 g127P8n804 g127P8n810) (@block_merge g127 8 816 6 12 g127P8n816 (@block_merge g127 8 822 6 6 g127P8n822 g127P8n828)))) (@block_merge g127 8 834 30 36 (@block_merge g127 8 834 12 18 (@block_merge g127 8 834 6 6 g127P8n834 g127P8n840) (@block_merge g127 8 846 6 12 g127P8n846 (@block_merge g127 8 852 6 6 g127P8n852 g127P8n858))) (@block_merge g127 8 864 18 18 (@block_merge g127 8 864 6 12 g127P8n864 (@block_merge g127 8 870 6 6 g127P8n870 g127P8n876)) (@block_merge g127 8 882 6 12 g127P8n882 (@block_merge g127 8 888 6 6 g127P8n888 g127P8n894))))) (@block_merge g127 8 900 66 64 (@block_merge g127 8 900 30 36 (@block_merge g127 8 900 12 18 (@block_merge g127 8 900 6 6 g127P8n900 g127P8n906) (@block_merge g127 8 912 6 12 g127P8n912 (@block_merge g127 8 918 6 6 g127P8n918 g127P8n924))) (@block_merge g127 8 930 18 18 (@block_merge g127 8 930 6 12 g127P8n930 (@block_merge g127 8 936 6 6 g127P8n936 g127P8n942)) (@block_merge g127 8 948 6 12 g127P8n948 (@block_merge g127 8 954 6 6 g127P8n954 g127P8n960)))) (@block_merge g127 8 966 30 34 (@block_merge g127 8 966 12 18 (@block_merge g127 8 966 6 6 g127P8n966 g127P8n972) (@block_merge g127 8 978 6 12 g127P8n978 (@block_merge g127 8 984 6 6 g127P8n984 g127P8n990))) (@block_merge g127 8 996 18 16 (@block_merge g127 8 996 6 12 g127P8n996 (@block_merge g127 8 1002 6 6 g127P8n1002 g127P8n1008)) (@block_merge g127 8 1014 6 10 g127P8n1014 (@block_merge g127 8 1020 6 4 g127P8n1020 g127P8n1026))))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n0 : block g127 9 0 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n6 : block g127 9 6 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n12 : block g127 9 12 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n18 : block g127 9 18 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n24 : block g127 9 24 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n30 : block g127 9 30 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n36 : block g127 9 36 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n42 : block g127 9 42 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n48 : block g127 9 48 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n54 : block g127 9 54 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n60 : block g127 9 60 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n66 : block g127 9 66 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n72 : block g127 9 72 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n78 : block g127 9 78 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n84 : block g127 9 84 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n90 : block g127 9 90 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n96 : block g127 9 96 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n102 : block g127 9 102 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n108 : block g127 9 108 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n114 : block g127 9 114 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n120 : block g127 9 120 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n126 : block g127 9 126 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n132 : block g127 9 132 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n138 : block g127 9 138 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n144 : block g127 9 144 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n150 : block g127 9 150 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n156 : block g127 9 156 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n162 : block g127 9 162 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n168 : block g127 9 168 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n174 : block g127 9 174 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n180 : block g127 9 180 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n186 : block g127 9 186 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n192 : block g127 9 192 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n198 : block g127 9 198 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n204 : block g127 9 204 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n210 : block g127 9 210 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n216 : block g127 9 216 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n222 : block g127 9 222 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n228 : block g127 9 228 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n234 : block g127 9 234 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n240 : block g127 9 240 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n246 : block g127 9 246 5 = true := by decide +kernel
theorem g127B9 : block g127 9 0 251 = true := (@block_merge g127 9 0 126 125 (@block_merge g127 9 0 60 66 (@block_merge g127 9 0 30 30 (@block_merge g127 9 0 12 18 (@block_merge g127 9 0 6 6 g127P9n0 g127P9n6) (@block_merge g127 9 12 6 12 g127P9n12 (@block_merge g127 9 18 6 6 g127P9n18 g127P9n24))) (@block_merge g127 9 30 12 18 (@block_merge g127 9 30 6 6 g127P9n30 g127P9n36) (@block_merge g127 9 42 6 12 g127P9n42 (@block_merge g127 9 48 6 6 g127P9n48 g127P9n54)))) (@block_merge g127 9 60 30 36 (@block_merge g127 9 60 12 18 (@block_merge g127 9 60 6 6 g127P9n60 g127P9n66) (@block_merge g127 9 72 6 12 g127P9n72 (@block_merge g127 9 78 6 6 g127P9n78 g127P9n84))) (@block_merge g127 9 90 18 18 (@block_merge g127 9 90 6 12 g127P9n90 (@block_merge g127 9 96 6 6 g127P9n96 g127P9n102)) (@block_merge g127 9 108 6 12 g127P9n108 (@block_merge g127 9 114 6 6 g127P9n114 g127P9n120))))) (@block_merge g127 9 126 60 65 (@block_merge g127 9 126 30 30 (@block_merge g127 9 126 12 18 (@block_merge g127 9 126 6 6 g127P9n126 g127P9n132) (@block_merge g127 9 138 6 12 g127P9n138 (@block_merge g127 9 144 6 6 g127P9n144 g127P9n150))) (@block_merge g127 9 156 12 18 (@block_merge g127 9 156 6 6 g127P9n156 g127P9n162) (@block_merge g127 9 168 6 12 g127P9n168 (@block_merge g127 9 174 6 6 g127P9n174 g127P9n180)))) (@block_merge g127 9 186 30 35 (@block_merge g127 9 186 12 18 (@block_merge g127 9 186 6 6 g127P9n186 g127P9n192) (@block_merge g127 9 198 6 12 g127P9n198 (@block_merge g127 9 204 6 6 g127P9n204 g127P9n210))) (@block_merge g127 9 216 18 17 (@block_merge g127 9 216 6 12 g127P9n216 (@block_merge g127 9 222 6 6 g127P9n222 g127P9n228)) (@block_merge g127 9 234 6 11 g127P9n234 (@block_merge g127 9 240 6 5 g127P9n240 g127P9n246))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P10n0 : block g127 10 0 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P10n6 : block g127 10 6 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P10n12 : block g127 10 12 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P10n18 : block g127 10 18 3 = true := by decide +kernel
theorem g127B10 : block g127 10 0 21 = true := (@block_merge g127 10 0 12 9 (@block_merge g127 10 0 6 6 g127P10n0 g127P10n6) (@block_merge g127 10 12 6 3 g127P10n12 g127P10n18))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P11n0 : block g127 11 0 1 = true := by decide +kernel
theorem g127B11 : block g127 11 0 1 = true := g127P11n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127T : checkedTables g127 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g127 0 0 0 = true)
  · exact (rfl : block g127 1 0 0 = true)
  · exact (rfl : block g127 2 0 0 = true)
  · exact (rfl : block g127 3 0 0 = true)
  · exact (rfl : block g127 4 0 0 = true)
  · exact g127B5
  · exact g127B6
  · exact g127B7
  · exact g127B8
  · exact g127B9
  · exact g127B10
  · exact g127B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K126) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 12 := lower_forest (g:=g127) (i:=0) (hints:=1091) (before_sound K126 V126) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem restricted : Lower true sevenInputs graph 12 := by
  have e : graphGoal 127 = graph := by decide +kernel
  rw [← e]
  exact low127

theorem excludesEleven : Impossible true graph 11 sevenInputs.toFinset := by
  intro k small run
  have steps := list_run run sevenInputs (by decide +kernel) rfl
  obtain ⟨q, bank, built, hit, limit⟩ := contraction (observe_proper graph_proper)
    steps (sevenInputs.map observe) Reach.start (fun _ h => Or.inl h)
  have bound := restricted q bank built hit
  omega

end PEqualNP.Outside.L_meta_10892

theorem PEqualNP.Outside.L_meta_10892 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact PEqualNP.Outside.L_meta_10892.replaceShort PEqualNP.Outside.L_meta_10892.excludesEleven gates o fit correct
