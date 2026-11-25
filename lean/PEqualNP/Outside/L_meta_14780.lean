import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_14780

open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 256
def zero : Sig := 0
def one : Sig := BitVec.allOnes 256
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

def bit (i : Fin 256) (a : Sig) : Bool := a.getLsbD i.val
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
lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
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

lemma extract {u target} (gs : List Gate) (w : List Sig)
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

lemma b_read (i) (w : List Sig) (j : Nat) :
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

lemma execute_bits (gs : List Gate) (i) (w : List Sig)
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

abbrev Row := Fin 256
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

def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r

def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p

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
  if h : r.val < 256-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(256-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 256 (256-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 256-d.val <;> simp [shifted,h,r.isLt]

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

abbrev Cut := Sig × Nat × List Sig

def cutTest (c : Cut) (k : Nat) (ws : List Sig) : Bool :=
  decide (k < c.2.1 + ws.countP (isMaskedConstant c.1)) &&
    ws.all fun w => masked c.1 w == zero || c.2.2.contains (masked c.1 w)

def CutGood (T : Sig) (c : Cut) : Prop :=
  ∀ k ws, ws.Nodup → cutTest c k ws = true → Impossible true T k ws.toFinset

theorem cut_good {T d raw L} (s : Slice true raw T d L) (cs : List Choice)
    {pool} (hp : makePool true d raw cs = some pool) (afford : cs.length ≤ L) :
    CutGood T (d,L-cs.length,pool.map (masked d)) := by
  intro k ws nd checked
  simp only [cutTest,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at checked
  apply poolCut_sound s cs hp nd
  apply Bool.and_eq_true_iff.mpr
  refine ⟨decide_eq_true (by omega),List.all_eq_true.mpr ?_⟩
  intro w hw
  rcases Bool.or_eq_true_iff.mp (checked.2 w hw) with hz | hm
  · simp [availableB,hz]
  · have mem := List.contains_iff_mem.mp hm
    obtain ⟨v,hv,eq⟩ := List.mem_map.mp mem
    have yes : ((pool.map (masked d)).any fun z => z == masked d w) = true :=
      List.any_eq_true.mpr ⟨masked d v,List.mem_map_of_mem hv,beq_iff_eq.mpr eq⟩
    simp [availableB,yes]

def properB (w : Sig) := w != zero && w != one
theorem proper_of (w : Sig) (h : properB w = true) : proper w := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h

def bothFlags : List Bool := [false,true]
theorem has_flag (b : Bool) : b ∈ bothFlags := by cases b <;> decide

def moves (ws : List Sig) (k : Nat) (a b : Sig) : List (List Sig) :=
  ([0,1,2,3] : List Nat).flatMap fun d =>
    let z := bin d a b
    if properB z && !ws.contains z then
      bothFlags.flatMap fun ka =>
        (bothFlags.map fun kb => childTwo ws a b d ka kb).filter fun v => decide (v.length ≤ k)
    else []

def children (ws : List Sig) (k : Nat) : List (List Sig) :=
  ws.flatMap fun a => ws.flatMap fun b => if a < b then moves ws k a b else []

theorem listed {ws : List Sig} {k a b d ka kb} (ha : a ∈ ws) (hb : b ∈ ws)
    (ab : a < b) (legal : allowed true d) (fresh : bin d a b ∉ ws) (pr : proper (bin d a b))
    (short : (childTwo ws a b d ka kb).length ≤ k) : childTwo ws a b d ka kb ∈ children ws k := by
  apply List.mem_flatMap.mpr
  refine ⟨a,ha,List.mem_flatMap.mpr ⟨b,hb,?_⟩⟩
  rw [if_pos ab]
  have dm : d ∈ ([0,1,2,3] : List Nat) := by
    rcases allowed_four legal with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> decide
  apply List.mem_flatMap.mpr
  refine ⟨d,dm,?_⟩
  have ready : (properB (bin d a b) && !ws.contains (bin d a b)) = true := by
    simp [properB,pr.1,pr.2,fresh]
  dsimp only
  rw [if_pos ready]
  exact List.mem_flatMap.mpr ⟨ka,has_flag ka,List.mem_filter.mpr
    ⟨List.mem_map_of_mem (f:=fun kb => childTwo ws a b d ka kb) (has_flag kb),decide_eq_true short⟩⟩

theorem swapped {ws : List Sig} {a b d} (h : allowed true d) (ka kb : Bool) :
    (childTwo ws a b d ka kb).Perm (childTwo ws b a (flipOp d) kb ka) := by
  unfold childTwo
  rw [bin_flip h a b,List.erase_comm a b]
  apply List.Perm.cons
  cases ka <;> cases kb <;> simp [kept,List.Perm.swap]

theorem by_children {T k ws} (nd : ws.Nodup) (absent : T ∉ ws)
    (h : ∀ w ∈ children ws k, Impossible true T (k-1) w.toFinset) : Impossible true T k ws.toFinset := by
  apply enum_step nd absent
  intro a ha b hb d leg ka kb ne fresh pr short
  rcases lt_or_gt_of_ne (show a.toNat ≠ b.toNat from fun e => ne (BitVec.eq_of_toNat_eq e)) with ab | ba
  · exact h _ (listed ha hb ab leg fresh pr short)
  · have p := swapped leg (ws:=ws) (a:=a) (b:=b) ka kb
    have e := bin_flip leg a b
    have other := listed hb ha ba (flip_flip leg).1 (e ▸ fresh) (e ▸ pr)
      (ka:=kb) (kb:=ka) (p.length_eq ▸ short)
    have eq : (childTwo ws a b d ka kb).toFinset = (childTwo ws b a (flipOp d) kb ka).toFinset := by
      ext w
      simpa only [List.mem_toFinset] using (p.mem_iff (a:=w))
    rw [eq]
    exact h _ other

def sameWires (ws vs : List Sig) := ws.all vs.contains && vs.all ws.contains
theorem same_wires {ws vs} (ok : sameWires ws vs = true) : ws.toFinset = vs.toFinset := by
  obtain ⟨l,r⟩ := Bool.and_eq_true_iff.mp ok
  ext a
  simp only [List.mem_toFinset]
  exact ⟨fun ha => List.contains_iff_mem.mp (List.all_eq_true.mp l _ ha),
    fun ha => List.contains_iff_mem.mp (List.all_eq_true.mp r _ ha)⟩

abbrev Cuts (T : Sig) := List {c : Cut // CutGood T c}
abbrev Links (T : Sig) (k : Nat) := List {ws : List Sig // Impossible true T k ws.toFinset}

def closeCase (T : Sig) (k : Nat) (cuts : Cuts T) (links : Links T k) (ws : List Sig) (code : Nat) :=
  if code < 65536 then
    let r := Fin.ofNat 256 (code % 256)
    let s := Fin.ofNat 256 (code / 256)
    (bit r T != bit s T) && ws.all (fun w => bit r w == bit s w)
  else if code < 131072 then
    match cuts[code-65536]? with
    | none => false
    | some c => decide ws.Nodup && cutTest c.val k ws
  else
    match links[code-131072]? with
    | none => false
    | some v => sameWires ws v.val

theorem close_ok {T k cuts links ws code} (ok : closeCase T k cuts links ws code = true) :
    Impossible true T k ws.toFinset := by
  unfold closeCase at ok
  split at ok
  · simp only [Bool.and_eq_true,bne_iff_ne,List.all_eq_true,beq_iff_eq] at ok
    intro n _ run
    obtain ⟨w,hw,ne⟩ := live_row_difference run ok.1
    exact ne (ok.2 w (List.mem_toFinset.mp hw))
  · split at ok
    · split at ok
      · contradiction
      · rename_i c _
        obtain ⟨nd,good⟩ := Bool.and_eq_true_iff.mp ok
        exact c.property k ws (of_decide_eq_true nd) good
    · split at ok
      · contradiction
      · rename_i v _
        rw [same_wires ok]
        exact v.property

def checkMoves (T : Sig) (k : Nat) (cuts : Cuts T) (links : Links T k) :
    List (List Sig) → Nat → Bool
  | [],_ => true
  | ws::rest,data => closeCase T k cuts links ws (data % 262144) &&
      checkMoves T k cuts links rest (data / 262144)

theorem moves_ok {T k cuts links vs data} (ok : checkMoves T k cuts links vs data = true) :
    ∀ w ∈ vs, Impossible true T k w.toFinset := by
  induction vs generalizing data with
  | nil => simp
  | cons v vs ih =>
    obtain ⟨closed,tail⟩ := Bool.and_eq_true_iff.mp ok
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hm
    · exact close_ok closed
    · exact ih tail _ hm

def checkNode (T : Sig) (k : Nat) (ws : List Sig) (cuts : Cuts T) (links : Links T (k-1)) (data : Nat) :=
  (decide ws.Nodup && !ws.contains T) && checkMoves T (k-1) cuts links (children ws k) data

theorem node_ok {T k ws} (cuts : Cuts T) (links : Links T (k-1)) (data : Nat)
    (ok : checkNode T k ws cuts links data = true) : Impossible true T k ws.toFinset := by
  obtain ⟨head,tail⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨hn,hm⟩ := Bool.and_eq_true_iff.mp head
  exact by_children (of_decide_eq_true hn) (by simpa using hm) (moves_ok tail)

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
def input (i : Nat) := inputs.getD i zero
def selected (m : Nat) := (List.range 8).filter (fun i => m.testBit i)
def roots (m : Nat) := (selected m).map input

def goalAt (m : Nat) : Sig :=
  let x := fun i => if m.testBit i then input i else zero
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7)

def fixes (q : Nat) : List Move :=
  ((List.range 8).filter fun i => !(q.testBit i)).map fun i =>
    (zero,input i,Fin.ofNat 256 (1 <<< i))

def domain (q : Nat) : Sig :=
  ((List.range 8).filter fun i => !(q.testBit i)).foldl (fun d i => d &&& neg (input i)) one

def tests (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun i =>
    let r := 1 <<< ((hints >>> (4*i)) % 16)
    (input i,Fin.ofNat 256 r,Fin.ofNat 256 (r ||| (1 <<< i)))

def Claim (m L : Nat) : Prop := Lower true (roots m) (goalAt m) L

def essTest (m hints : Nat) :=
  (properB (goalAt m) && checkEssential (goalAt m) (roots m) (tests m hints)) &&
    ((tests m hints).map Prod.fst == roots m)

theorem fromSearch {m k} (hints : Nat) (checked : essTest m hints = true)
    (no : Impossible true (goalAt m) k (roots m).toFinset) : Claim m (k+1) := by
  simp only [essTest,Bool.and_eq_true,beq_iff_eq] at checked
  have ok := checked.1.2
  apply lower_impossible (proper_of _ checked.1.1) (essential_plain ok).1 (essential_plain ok).2 _ no
  intro w hw
  apply essential_ok ok w
  rw [checked.2]
  exact List.mem_toFinset.mpr hw

def liftTest (m q a b e hints : Nat) :=
  ((checkLift (fixes q) (goalAt m) (roots m) (roots q) (goalAt q) (tests e hints) &&
    properB (goalAt m)) && properB (goalAt q)) &&
      decide (b ≤ a+((tests e hints).map Prod.fst).toFinset.card)

theorem fromLift {m q a} (b e hints : Nat) (lower : Claim q a)
    (ok : liftTest m q a b e hints = true) : Claim m b := by
  simp only [liftTest,Bool.and_eq_true,decide_eq_true_eq] at ok
  have lb := lift_ok ok.1.1.1 (proper_of _ ok.1.1.2) (proper_of _ ok.1.2) lower
  exact fun p bank hr ha => ok.2.trans (lb p bank hr ha)

def poolFor (q : Nat) (extra : Option Choice) : List Sig :=
  match extra with
  | none => roots q
  | some c => choiceVal c :: roots q

def ruleTest (m q L : Nat) (e : Option Choice) : Bool :=
  (((checkMap (fixes q) (roots q) (goalAt m) (roots q) (goalAt q) &&
    (movedWord (fixes q) (domain q) == one)) && properB (goalAt q)) &&
    (makePool true (domain q) (roots q) e.toList == some (poolFor q e))) &&
    decide (e.toList.length ≤ L)

def ruleFor (m : Nat) {q L} (lo : Claim q L) (e : Option Choice)
    (ok : ruleTest m q L e = true) : {c : Cut // CutGood (goalAt m) c} := by
  refine ⟨(domain q,L-e.toList.length,(poolFor q e).map (masked (domain q))),?_⟩
  simp only [ruleTest,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at ok
  exact cut_good (slice_correct ok.1.1.1.1 ok.1.1.1.2 (proper_of _ ok.1.1.2) lo)
    e.toList ok.1.2 ok.2

def cuts146 : Cuts (goalAt 146) := []

def state146_0 : List Sig := roots 146
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude146_0 : Impossible true (goalAt 146) 3 state146_0.toFinset :=
  node_ok cuts146 [] 0x24040120224000820224200900024040908024040820204808120220808121020800901020a00820020808828020808901004840121004808828004800908004840120004808121004808908020a008280 (by decide +kernel)

theorem lower146 : Claim 146 4 :=
  fromSearch 268501056 (by decide +kernel) exclude146_0

def cuts202 : Cuts (goalAt 202) := []

def state202_0 : List Sig := roots 202
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude202_0 : Impossible true (goalAt 202) 3 state202_0.toFinset :=
  node_ok cuts202 [] 0x308088202209088202220008800220208202120004800120208880208008200208088808128204808120284808129004840121084840 (by decide +kernel)

theorem lower202 : Claim 202 4 :=
  fromSearch 318791792 (by decide +kernel) exclude202_0

def cuts216 : Cuts (goalAt 216) := []

def state216_0 : List Sig := roots 216
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude216_0 : Impossible true (goalAt 216) 3 state216_0.toFinset :=
  node_ok cuts216 [] 0x120208808241404808240009000240408808160204808120604808220008800220209010120004800120208880121005840121404840 (by decide +kernel)

theorem lower216 : Claim 216 4 :=
  fromSearch 856121344 (by decide +kernel) exclude216_0

theorem lower154 : Claim 154 5 :=
  fromLift 5 8 268529728 lower146 (by decide +kernel)

def rule218_0 : {c : Cut // CutGood (goalAt 218) c} :=
  ruleFor 218 lower146 none (by decide +kernel)

def rule218_1 : {c : Cut // CutGood (goalAt 218) c} :=
  ruleFor 218 lower202 none (by decide +kernel)

def rule218_2 : {c : Cut // CutGood (goalAt 218) c} :=
  ruleFor 218 lower216 none (by decide +kernel)

def rule218_3 : {c : Cut // CutGood (goalAt 218) c} :=
  ruleFor 218 lower154 none (by decide +kernel)

def rule218_4 : {c : Cut // CutGood (goalAt 218) c} :=
  ruleFor 218 lower154 (some (0,input 3,input 7)) (by decide +kernel)

def cuts218 : Cuts (goalAt 218) := [rule218_0,rule218_1,rule218_2,rule218_3,rule218_4]

def state218_0 : List Sig := [0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 1,input 4,input 3,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude218_0 : Impossible true (goalAt 218) 5 state218_0.toFinset :=
  node_ok cuts218 [] 0xc202208088242208088800220008808208084800120004808222001a0204808120a048084840129084a42121001202208089010048081202148085818048089080208088808208088808128284808128284808048401a10048601210048081210400048280208088808208088808128284808128284808 (by decide +kernel)

def state218_1 : List Sig := [0xffff0000ffff0000ffff0000ffff0000cccc0000cccc0000cccc0000cccc,input 1,input 7,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude218_1 : Impossible true (goalAt 218) 4 state218_1.toFinset :=
  node_ok cuts218 [] 0x340009000241009000120004800120208880260009000240209000048005200128281200048001a0004820120004800900020808120004808480814808120204808120a06808120204808900020808900020a001200048081200 (by decide +kernel)

def state218_2 : List Sig := [0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 1,input 7,input 3,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude218_2 : Impossible true (goalAt 218) 5 state218_2.toFinset :=
  node_ok cuts218 [⟨state218_1,exclude218_1⟩] 0xc202208088242208084808128284a0a1202012021480848180480812022080890800480a0000048081202400044800120004808222001a0204808120a048088a0220808820a208084840129084a42121008808128284808128284808048089080048088280129084840129084840208088280220281210 (by decide +kernel)

def state218_3 : List Sig := [0xffffffffffffffff3333333333333333ffffffffffffffff0000000000000000,input 1,input 7,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude218_3 : Impossible true (goalAt 218) 4 state218_3.toFinset :=
  node_ok cuts218 [] 0x48088202241401202048085202120601202068081202048281202228088202208288202120004800120210000048001200048089080048401a10048601210208008200208081210128204808120284808308088202209088202 (by decide +kernel)

def state218_4 : List Sig := [0x3333333333333333333333333333333300000000000000000000000000000000,input 1,input 7,input 3,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude218_4 : Impossible true (goalAt 218) 5 state218_4.toFinset :=
  node_ok cuts218 [⟨state218_3,exclude218_3⟩] 0xc202208088242208081202148084818048081202208089080048084800120004808222001a0204808120a048088a0220808820a208084a0812020480a1202012000480012022420012100684012180484082002080812104000c4808800004808242001202242001202222004840222004840220208280 (by decide +kernel)

def state218_5 : List Sig := [0x3333333333333333333333333333333333330000333300003333000033330000,input 4,input 7,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude218_5 : Impossible true (goalAt 218) 4 state218_5.toFinset :=
  node_ok cuts218 [] 0x30800820020900820012000480012020888022800820020820820006800120004820120004800520016060120004800820024040120004840480814840480804840121806840121022020820024040820020a001200048401200 (by decide +kernel)

def state218_6 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 1,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude218_6 : Impossible true (goalAt 218) 5 state218_6.toFinset :=
  node_ok cuts218 [⟨state218_5,exclude218_5⟩] 0x4808240409050120204808160605818120204800120004808222009810240409018240404840161405850121004840161405850121004a0812020480a12020121006840121804840121024040828004840828004840121020a020000048401210400088202160604808160604808240409080220601202 (by decide +kernel)

def state218_7 : List Sig := [0xffffffffffffffff0000ffff0000ffffffffffffffffffff0000000000000000,input 4,input 7,input 1,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude218_7 : Impossible true (goalAt 218) 4 state218_7.toFinset :=
  node_ok cuts218 [] 0x260409010240609010068081202048281202120004800120210000048401a10048601210048409010209081210048001200048088280128204808120284808240009000240401202048085202120601202208088202209084808 (by decide +kernel)

def state218_8 : List Sig := [0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000,input 4,input 7,input 1,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude218_8 : Impossible true (goalAt 218) 5 state218_8.toFinset :=
  node_ok cuts218 [⟨state218_7,exclude218_7⟩] 0x4808240409050120204800120004808222009810240409018240401a0204808120a048084a0812020480a12020121006840121804840121024040828004840120004800120220a0012021480848180480890002404012024000c480880000480822200484022200484020a00121020a001210208089080 (by decide +kernel)

def state218_9 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude218_9 : Impossible true (goalAt 218) 4 state218_9.toFinset :=
  node_ok cuts218 [] 0x48089040241401202160004800120404800048001200048088280048408240209081210128004800120084800220004840048085840048084840048404a40048404840122008840121010004 (by decide +kernel)

def state218_10 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,input 1,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude218_10 : Impossible true (goalAt 218) 5 state218_10.toFinset :=
  node_ok cuts218 [⟨state218_9,exclude218_9⟩] 0x9050048081202209089080241009050242009050209081202048085818048081202120205242148085818149084818120201202048081a0a121001a02048085850048081a0a16140120a04808484004809000012100484020908888022101000022200488020908484012100480880000480040000484012000480812100480840001000040000120220a00120024200121004800120204840120224200828020a004a42048401210121001a18068404a4206860121812100121004840824204840121024140828020900824220a008242241401210048404a0a048404a08120205250120204a0a14940480a1202012101202100034000c8202 (by decide +kernel)

def state218_11 : List Sig := roots 218
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude218_11 : Impossible true (goalAt 218) 6 state218_11.toFinset :=
  node_ok cuts218 [⟨state218_0,exclude218_0⟩,⟨state218_2,exclude218_2⟩,⟨state218_4,exclude218_4⟩,⟨state218_6,exclude218_6⟩,⟨state218_8,exclude218_8⟩,⟨state218_10,exclude218_10⟩] 0x4000cc24212020c2024000c82024000c82024000cc2428001482424000c82021202082028001090100480890004000482022420090008000c90102420090104000482020480812024000c58180480812024000c48081490852024000c58181490848184000c48080480812024000088081210088004000082022220088004000088082220088084000082021210082024000c48082220048004000d00001210048004000c48081210048084000d0003222008880400001a0a121001a02400001202161401202400001a0a16140120a40000120212100120280008820204840820040008880820a00820080004820220a0082024000888080484088084000c4a0a048404a084000c48081494048084000c4a0a14940480a4000c480804840480840004120220a00120040008908004840120080000120204840120240004908020a008280400004a42048401210400004840068601a10400004a42068601218400004840048401210 (by decide +kernel)

theorem lower218 : Claim 218 7 :=
  fromSearch 318857280 (by decide +kernel) exclude218_11

def cuts198 : Cuts (goalAt 198) := []

def state198_0 : List Sig := roots 198
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude198_0 : Impossible true (goalAt 198) 3 state198_0.toFinset :=
  node_ok cuts198 [] 0x308088202209088202210008400210108202110004400110108480208008200208088404118104404110184404119004440111084440 (by decide +kernel)

theorem lower198 : Claim 198 4 :=
  fromSearch 301991536 (by decide +kernel) exclude198_0

def cuts212 : Cuts (goalAt 212) := []

def state212_0 : List Sig := roots 212
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude212_0 : Impossible true (goalAt 212) 3 state212_0.toFinset :=
  node_ok cuts212 [] 0x110108404241404404240009000240408404150104404110504404210008400210109010110004400110108480111005440111404440 (by decide +kernel)

theorem lower212 : Claim 212 4 :=
  fromSearch 570885632 (by decide +kernel) exclude212_0

theorem lower150 : Claim 150 5 :=
  fromLift 5 4 268502848 lower146 (by decide +kernel)

def rule214_0 : {c : Cut // CutGood (goalAt 214) c} :=
  ruleFor 214 lower146 none (by decide +kernel)

def rule214_1 : {c : Cut // CutGood (goalAt 214) c} :=
  ruleFor 214 lower198 none (by decide +kernel)

def rule214_2 : {c : Cut // CutGood (goalAt 214) c} :=
  ruleFor 214 lower212 none (by decide +kernel)

def rule214_3 : {c : Cut // CutGood (goalAt 214) c} :=
  ruleFor 214 lower150 none (by decide +kernel)

def rule214_4 : {c : Cut // CutGood (goalAt 214) c} :=
  ruleFor 214 lower150 (some (0,input 2,input 7)) (by decide +kernel)

def cuts214 : Cuts (goalAt 214) := [rule214_0,rule214_1,rule214_2,rule214_3,rule214_4]

def state214_0 : List Sig := [0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 1,input 4,input 2,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_0 : Impossible true (goalAt 214) 5 state214_0.toFinset :=
  node_ok cuts214 [] 0xc202208088242208088400210008404208084400110004404212001602048081206048084440119084642111001202208089010048081202148085414048089080208088404208088404118184404118184404048401610048501210048081210400048280208088404208088404118184404118184404 (by decide +kernel)

def state214_1 : List Sig := [0xffff0000ffff0000ffff0000ffff0000cccc0000cccc0000cccc0000cccc,input 1,input 7,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_1 : Impossible true (goalAt 214) 4 state214_1.toFinset :=
  node_ok cuts214 [] 0x34000900024100900011000440011010848025000900024010900004800520011818120004800160004810120004800900020808120004808440414808120204808120605808120204808900020808900020a001200048081200 (by decide +kernel)

def state214_2 : List Sig := [0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 1,input 7,input 2,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_2 : Impossible true (goalAt 214) 5 state214_2.toFinset :=
  node_ok cuts214 [⟨state214_1,exclude214_1⟩] 0xc2022080882422080844041181846061101012021480844140480812022080890800480a0000048081202400044400110004404212001602048081206048088602208088206208084440119084642111008404118184404118184404048089080048088280119084440119084440208088280210181210 (by decide +kernel)

def state214_3 : List Sig := [0xffffffffffffffff3333333333333333ffffffffffffffff0000000000000000,input 1,input 7,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_3 : Impossible true (goalAt 214) 4 state214_3.toFinset :=
  node_ok cuts214 [] 0x48088202241401202048085202110501202058081202048181202218088202208188202110004400110110000048001200048089080048401610048501210208008200208081210118104404110184404308088202209088202 (by decide +kernel)

def state214_4 : List Sig := [0x3333333333333333333333333333333300000000000000000000000000000000,input 1,input 7,input 2,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_4 : Impossible true (goalAt 214) 5 state214_4.toFinset :=
  node_ok cuts214 [⟨state214_3,exclude214_3⟩] 0xc2022080882422080812021480844140480812022080890800480844001100044042120016020480812060480886022080882062080846041101044061101012000480012022420012100584012140484082002080812104000c4404800004404242001202242001202212004440212004440210108280 (by decide +kernel)

def state214_5 : List Sig := [0x3333333333333333333333333333333333330000333300003333000033330000,input 4,input 7,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_5 : Impossible true (goalAt 214) 4 state214_5.toFinset :=
  node_ok cuts214 [] 0x30800820020900820011000440011010848021800820020810820005800120004810120004800520015050120004800820024040120004840440414840440404840121405840121021010820024040820020a001200048401200 (by decide +kernel)

def state214_6 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_6 : Impossible true (goalAt 214) 5 state214_6.toFinset :=
  node_ok cuts214 [⟨state214_5,exclude214_5⟩] 0x440424040905011010440415050541411010440011000440421200941024040901424040444015140545011100444015140545011100460411010440611010121005840121404840121024040828004840828004840121020a020000048401210400088202150504404150504404240409080210501202 (by decide +kernel)

def state214_7 : List Sig := [0xffffffffffffffff0000ffff0000ffffffffffffffffffff0000000000000000,input 4,input 7,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_7 : Impossible true (goalAt 214) 4 state214_7.toFinset :=
  node_ok cuts214 [] 0x250409010240509010058081202048181202110004400110110000048401610048501210048409010209081210048001200048088280118104404110184404240009000240401202048085202110501202208088202209084404 (by decide +kernel)

def state214_8 : List Sig := [0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000,input 4,input 7,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_8 : Impossible true (goalAt 214) 5 state214_8.toFinset :=
  node_ok cuts214 [⟨state214_7,exclude214_7⟩] 0x440424040905011010440011000440421200941024040901424040160204808120604808460411010440611010121005840121404840121024040828004840120004800120220a0012021480844140480890002404012024000c440480000440421200444021200444020a00121020a001210208089080 (by decide +kernel)

def state214_9 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_9 : Impossible true (goalAt 214) 4 state214_9.toFinset :=
  node_ok cuts214 [] 0x48089040241401202150004400110404400048001200048088280048408240209081210118004400110084400210004440048085440048084440048404640048404440112008440111010004 (by decide +kernel)

def state214_10 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_10 : Impossible true (goalAt 214) 5 state214_10.toFinset :=
  node_ok cuts214 [⟨state214_9,exclude214_9⟩] 0x905004808120220908908024100905024200905020908120204808541404808120211010524214808541414908441411010120204808160611100160204808545004808160615140120604808444004809000011100444020908848021101000021200448020908444011100440480000440040000444011000440411100440440001000040000120220a00120024200121004800120204840120224200828020a00464204840121011100161405840464205850121411100121004840824204840121024140828020900824220a0082422414012100484046060484046041101052501101046061494044061101012101101100034000c8202 (by decide +kernel)

def state214_11 : List Sig := roots 214
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_11 : Impossible true (goalAt 214) 6 state214_11.toFinset :=
  node_ok cuts214 [⟨state214_0,exclude214_0⟩,⟨state214_2,exclude214_2⟩,⟨state214_4,exclude214_4⟩,⟨state214_6,exclude214_6⟩,⟨state214_8,exclude214_8⟩,⟨state214_10,exclude214_10⟩] 0x4000cc24211010c2024000c82024000c82024000cc2428001482424000c82021101082028001090100480890004000482022420090008000c90102420090104000482020480812024000c54140480812024000c44041490852024000c54141490844144000c44040480812024000084041110084004000082022120084004000084042120084044000082021110082024000c44042120044004000d00001110044004000c44041110044044000d000321200848040000160611100160240000120215140120240000160615140120640000120211100120280008820204840820040008840420a00820080004820220a0082024000884040484084044000c46060484046044000c44041494044044000c46061494044064000c440404840440440004120220a00120040008908004840120080000120204840120240004908020a008280400004642048401210400004440058501610400004642058501214400004440048401210 (by decide +kernel)

theorem lower214 : Claim 214 7 :=
  fromSearch 302057024 (by decide +kernel) exclude214_11

theorem lower246 : Claim 246 8 :=
  fromLift 8 32 304153920 lower214 (by decide +kernel)

def cuts172 : Cuts (goalAt 172) := []

def state172_0 : List Sig := roots 172
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude172_0 : Impossible true (goalAt 172) 3 state172_0.toFinset :=
  node_ok cuts172 [] 0x90108404220a024042200088002202084040b0102404090302404210008400210108808090002400090108480090802c20090a02420 (by decide +kernel)

theorem lower172 : Claim 172 4 :=
  fromSearch 538998016 (by decide +kernel) exclude172_0

theorem lower236 : Claim 236 5 :=
  fromLift 5 64 572548352 lower172 (by decide +kernel)

theorem lower230 : Claim 230 5 :=
  fromLift 5 32 304088432 lower198 (by decide +kernel)

def cuts108 : Cuts (goalAt 108) := []

def state108_0 : List Sig := roots 108
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude108_0 : Impossible true (goalAt 108) 3 state108_0.toFinset :=
  node_ok cuts108 [] 0x90104404120a024041200048001202044040b0102404090302404110004400110104808090002400090104440090802c20090a02420 (by decide +kernel)

theorem lower108 : Claim 108 4 :=
  fromSearch 35677440 (by decide +kernel) exclude108_0

theorem lower206 : Claim 206 5 :=
  fromLift 5 4 302016112 lower202 (by decide +kernel)

theorem lower174 : Claim 174 5 :=
  fromLift 5 2 270562672 lower172 (by decide +kernel)

def rule238_0 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower202 none (by decide +kernel)

def rule238_1 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower236 none (by decide +kernel)

def rule238_2 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower230 none (by decide +kernel)

def rule238_3 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower108 none (by decide +kernel)

def rule238_4 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower206 none (by decide +kernel)

def rule238_5 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower174 none (by decide +kernel)

def cuts238 : Cuts (goalAt 238) := [rule238_0,rule238_1,rule238_2,rule238_3,rule238_4,rule238_5]

def state238_0 : List Sig := roots 238
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_0 : Impossible true (goalAt 238) 6 state238_0.toFinset :=
  node_ok cuts238 [] 0x3090844043080882024001482023090900032090882021101082022888824042880882024001082022888900032088882020901082021a0a024040901044044001444041a0a10005120a044040901024042202048402200082022220088002202088802202082021210082021202088801200044041210048001202048401202044042220044040b03048400b01024041a18024040b03068600903024041210024042101024202100082022120084002101084802101082020908082021101024201100048081110044001101044401101048080908048080901044400900100000908024000901024200901100041110044404000824200908048400b0a02c20400002c28090a0484009080242020809000320800840420a00820020808828020808840440004840411818828011810440430b00440411818c2c011018440420a00440409818828009810240428a80240409818a2a009018240420a00240412908828012900484040008484012909000212108484020a00484009888828009880242040004242009889000009088242020a002420 (by decide +kernel)

theorem lower238 : Claim 238 7 :=
  fromSearch 304113008 (by decide +kernel) exclude238_0

theorem lower222 : Claim 222 8 :=
  fromLift 8 4 302081600 lower218 (by decide +kernel)

def cuts166 : Cuts (goalAt 166) := []

def state166_0 : List Sig := roots 166
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude166_0 : Impossible true (goalAt 166) 3 state166_0.toFinset :=
  node_ok cuts166 [] 0x288088202208888202210008400210108202090002400090108480208008200208088404098102404090182404098802420090882420 (by decide +kernel)

theorem lower166 : Claim 166 4 :=
  fromSearch 270534000 (by decide +kernel) exclude166_0

def cuts180 : Cuts (goalAt 180) := []

def state180_0 : List Sig := roots 180
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude180_0 : Impossible true (goalAt 180) 3 state180_0.toFinset :=
  node_ok cuts180 [] 0x90108404240c024042400090002404084040d0102404090502404210008400210109010090002400090108480090803420090c02420 (by decide +kernel)

theorem lower180 : Claim 180 4 :=
  fromSearch 539428096 (by decide +kernel) exclude180_0

def rule182_0 : {c : Cut // CutGood (goalAt 182) c} :=
  ruleFor 182 lower146 none (by decide +kernel)

def rule182_1 : {c : Cut // CutGood (goalAt 182) c} :=
  ruleFor 182 lower166 none (by decide +kernel)

def rule182_2 : {c : Cut // CutGood (goalAt 182) c} :=
  ruleFor 182 lower180 none (by decide +kernel)

def rule182_3 : {c : Cut // CutGood (goalAt 182) c} :=
  ruleFor 182 lower150 none (by decide +kernel)

def rule182_4 : {c : Cut // CutGood (goalAt 182) c} :=
  ruleFor 182 lower150 (some (0,input 2,input 7)) (by decide +kernel)

def cuts182 : Cuts (goalAt 182) := [rule182_0,rule182_1,rule182_2,rule182_3,rule182_4]

def state182_0 : List Sig := [0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 1,input 4,input 2,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_0 : Impossible true (goalAt 182) 5 state182_0.toFinset :=
  node_ok cuts182 [] 0xa2022080882222080884002100084042080824000900024042120016020480812060480824200988826220908012022080890100480812020c8083414048089080208088404208088404098182404098182404048401610048501210048081210400048280208088404208088404098182404098182404 (by decide +kernel)

def state182_1 : List Sig := [0xffff0000ffff0000ffff0000ffff0000cccc0000cccc0000cccc0000cccc,input 1,input 7,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_1 : Impossible true (goalAt 182) 4 state182_1.toFinset :=
  node_ok cuts182 [] 0x2c00090002408090000900024000901084802500090002401090000480032000981812000480016000481012000480090002080812000480824040c808120204808120605808120204808900020808900020a001200048081200 (by decide +kernel)

def state182_2 : List Sig := [0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 1,input 7,input 2,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_2 : Impossible true (goalAt 182) 5 state182_2.toFinset :=
  node_ok cuts182 [⟨state182_1,exclude182_1⟩] 0xa2022080882222080824040981826060901012020c80824140480812022080890800480a0000048081202400042400090002404212001602048081206048088602208088206208082420098882622090808404098182404098182404048089080048088280098882420098882420208088280210181210 (by decide +kernel)

def state182_3 : List Sig := [0xffffffff33333333ffffffff33333333ffffffff00000000ffffffff00000000,input 1,input 7,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_3 : Impossible true (goalAt 182) 4 state182_3.toFinset :=
  node_ok cuts182 [] 0x48088202240c01202048083202090501202058081202048181202218088202208188202090002400090110000048001200048089080048401610048501210208008200208081210098102404090182404288088202208888202 (by decide +kernel)

def state182_4 : List Sig := [0x3333333333333333333333333333333300000000000000000000000000000000,input 1,input 7,input 2,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_4 : Impossible true (goalAt 182) 5 state182_4.toFinset :=
  node_ok cuts182 [⟨state182_3,exclude182_3⟩] 0xa2022080882222080812020c80824140480812022080890800480824000900024042120016020480812060480886022080882062080826040901024060901012000480012022420012100584012140484082002080812104000c2404800002404242001202242001202212002420212002420210108280 (by decide +kernel)

def state182_5 : List Sig := [0x3333333333333333333333333333333333330000333300003333000033330000,input 4,input 7,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_5 : Impossible true (goalAt 182) 4 state182_5.toFinset :=
  node_ok cuts182 [] 0x2880082002088082000900024000901084802180082002081082000580012000481012000480032000d05012000480082002404012000484024040c840240404840121405840121021010820024040820020a001200048401200 (by decide +kernel)

def state182_6 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_6 : Impossible true (goalAt 182) 5 state182_6.toFinset :=
  node_ok cuts182 [⟨state182_5,exclude182_5⟩] 0x24042404090300901024040d05034140901024000900024042120094102404090142404024200d0c034300908024200d0c0343009080260409010240609010121005840121404840121024040828004840828004840121020a0200000484012104000882020d05024040d0502404240409080210501202 (by decide +kernel)

def state182_7 : List Sig := [0xffffffff0000ffffffffffff0000ffffffffffff00000000ffffffff00000000,input 4,input 7,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_7 : Impossible true (goalAt 182) 4 state182_7.toFinset :=
  node_ok cuts182 [] 0x250409010240509010058081202048181202090002400090110000048401610048501210048409010208881210048001200048088280098102404090182404240009000240401202048083202090501202208088202208882404 (by decide +kernel)

def state182_8 : List Sig := [0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000,input 4,input 7,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_8 : Impossible true (goalAt 182) 5 state182_8.toFinset :=
  node_ok cuts182 [⟨state182_7,exclude182_7⟩] 0x240424040903009010240009000240421200941024040901424040160204808120604808260409010240609010121005840121404840121024040828004840120004800120220a0012020c80824140480890002404012024000c240480000240421200242021200242020a00121020a001210208089080 (by decide +kernel)

def state182_9 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_9 : Impossible true (goalAt 182) 4 state182_9.toFinset :=
  node_ok cuts182 [] 0x48089020240c012020d0002400090402400048001200048088280048408220208881210098002400090082400210002420048083420048082420048402620048402420092008420090810004 (by decide +kernel)

def state182_10 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_10 : Impossible true (goalAt 182) 5 state182_10.toFinset :=
  node_ok cuts182 [⟨state182_9,exclude182_9⟩] 0x90300480812022088890802408090302420090302088812020480834140480812020901032220c80834140c88824140901012020480816060908016020480834300480816060d0c0120604808242004809000009080242020888848021081000021200248020888242009080240480000240040000242009000240409080240440001000040000120220a00120024200121004800120204840120224200828020a002622048401210090801614058402622058501214090801210048408222048401210240c0828020880822220a008222240c012100484026060484026040901032300901026060c8c024060901012100901100034000c8202 (by decide +kernel)

def state182_11 : List Sig := roots 182
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_11 : Impossible true (goalAt 182) 6 state182_11.toFinset :=
  node_ok cuts182 [⟨state182_0,exclude182_0⟩,⟨state182_2,exclude182_2⟩,⟨state182_4,exclude182_4⟩,⟨state182_6,exclude182_6⟩,⟨state182_8,exclude182_8⟩,⟨state182_10,exclude182_10⟩] 0x4000ca22209010a2024000c82024000c82024000ca2228001482224000c82020901082028001090100480890004000482022420090008000c90102420090104000482020480812024000c34140480812024000c24040c88832024000c34140c88824144000c24040480812024000084040908084004000082022120084004000084042120084044000082020908082024000c24042120024004000d00000908024004000c24040908024044000d00032120084804000016060908016024000012020d0c012024000016060d0c0120640000120209080120280008820204840820040008840420a00820080004820220a0082024000884040484084044000c26060484026044000c24040c8c024044000c26060c8c024064000c240404840240440004120220a00120040008908004840120080000120204840120240004908020a008280400002622048401210400002420058501610400002622058501214400002420048401210 (by decide +kernel)

theorem lower182 : Claim 182 7 :=
  fromSearch 270599488 (by decide +kernel) exclude182_11

theorem lower190 : Claim 190 8 :=
  fromLift 8 8 270628160 lower182 (by decide +kernel)

theorem lower126 : Claim 126 6 :=
  fromLift 6 18 35743040 lower108 (by decide +kernel)

theorem lower244 : Claim 244 5 :=
  fromLift 5 32 572982528 lower212 (by decide +kernel)

theorem lower220 : Claim 220 5 :=
  fromLift 5 4 570910208 lower216 (by decide +kernel)

theorem lower188 : Claim 188 5 :=
  fromLift 5 8 539456768 lower180 (by decide +kernel)

def rule252_0 : {c : Cut // CutGood (goalAt 252) c} :=
  ruleFor 252 lower216 none (by decide +kernel)

def rule252_1 : {c : Cut // CutGood (goalAt 252) c} :=
  ruleFor 252 lower244 none (by decide +kernel)

def rule252_2 : {c : Cut // CutGood (goalAt 252) c} :=
  ruleFor 252 lower236 none (by decide +kernel)

def rule252_3 : {c : Cut // CutGood (goalAt 252) c} :=
  ruleFor 252 lower220 none (by decide +kernel)

def rule252_4 : {c : Cut // CutGood (goalAt 252) c} :=
  ruleFor 252 lower108 none (by decide +kernel)

def rule252_5 : {c : Cut // CutGood (goalAt 252) c} :=
  ruleFor 252 lower188 none (by decide +kernel)

def cuts252 : Cuts (goalAt 252) := [rule252_0,rule252_1,rule252_2,rule252_3,rule252_4,rule252_5]

def state252_0 : List Sig := roots 252
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude252_0 : Impossible true (goalAt 252) 6 state252_0.toFinset :=
  node_ok cuts252 [] 0x3414044041101084044001484043414100042414084041101044042a0a024040901084044000c84042a0a10004220a084040901024041a0a024040901044044001444041a0a10005120a0440409010240424041000424000840424200900024040908024040840440008840415050908015010440434300440415050d0c01105044042420044040d05090800d01024042c28024040d050b0a00905024042420024042202048402200084042220088002202088802202084041210084041202088801200044041210048001202048401202044042220044040b03048400b01024041a18024040b03068600903024041210024044000848401210090801614058404000458501214090801210048402101024202100088082120084002101084802101088080908088081101024201100048081110044001101044401101048080908048080901044400900100000908024000901024200901100031110044404000824200908090800d0c03420400003430090c090800908024204000424200908048400b0a02c20400002c28090a04840090802420 (by decide +kernel)

theorem lower252 : Claim 252 7 :=
  fromSearch 573007104 (by decide +kernel) exclude252_0

theorem lower158 : Claim 158 6 :=
  fromLift 6 4 268531520 lower154 (by decide +kernel)

def rule254_0 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower218 none (by decide +kernel)

def rule254_1 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower246 none (by decide +kernel)

def rule254_2 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower238 none (by decide +kernel)

def rule254_3 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower222 none (by decide +kernel)

def rule254_4 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower222 (some (1,input 1,input 4)) (by decide +kernel)

def rule254_5 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower190 none (by decide +kernel)

def rule254_6 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower190 (some (1,input 1,input 4)) (by decide +kernel)

def rule254_7 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower126 none (by decide +kernel)

def rule254_8 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower108 none (by decide +kernel)

def rule254_9 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower236 none (by decide +kernel)

def rule254_10 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower190 (some (3,input 1,input 4)) (by decide +kernel)

def rule254_11 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower252 none (by decide +kernel)

def rule254_12 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower190 (some (2,input 1,input 4)) (by decide +kernel)

def rule254_13 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower218 (some (1,input 1,input 4)) (by decide +kernel)

def rule254_14 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower246 (some (1,input 1,input 4)) (by decide +kernel)

def rule254_15 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower190 (some (3,input 1,input 7)) (by decide +kernel)

def rule254_16 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower218 (some (1,input 1,input 7)) (by decide +kernel)

def rule254_17 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower246 (some (1,input 1,input 7)) (by decide +kernel)

def rule254_18 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower190 (some (2,input 1,input 7)) (by decide +kernel)

def rule254_19 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower222 (some (1,input 1,input 7)) (by decide +kernel)

def rule254_20 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower190 (some (1,input 1,input 7)) (by decide +kernel)

def rule254_21 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower190 (some (0,input 1,input 7)) (by decide +kernel)

def rule254_22 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower218 (some (3,input 1,input 7)) (by decide +kernel)

def rule254_23 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower246 (some (3,input 1,input 7)) (by decide +kernel)

def rule254_24 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower190 (some (1,input 5,input 7)) (by decide +kernel)

def rule254_25 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower190 (some (2,input 5,input 7)) (by decide +kernel)

def rule254_26 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower214 (some (3,input 1,input 7)) (by decide +kernel)

def rule254_27 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower222 (some (3,input 1,input 7)) (by decide +kernel)

def rule254_28 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower146 none (by decide +kernel)

def rule254_29 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower182 (some (3,input 1,input 7)) (by decide +kernel)

def rule254_30 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower238 (some (3,input 1,input 7)) (by decide +kernel)

def rule254_31 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower190 (some (3,input 4,input 7)) (by decide +kernel)

def rule254_32 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower190 (some (2,input 4,input 7)) (by decide +kernel)

def rule254_33 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower218 (some (1,input 4,input 7)) (by decide +kernel)

def rule254_34 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower246 (some (1,input 4,input 7)) (by decide +kernel)

def rule254_35 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower222 (some (1,input 4,input 7)) (by decide +kernel)

def rule254_36 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower190 (some (1,input 4,input 7)) (by decide +kernel)

def rule254_37 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower190 (some (0,input 4,input 7)) (by decide +kernel)

def rule254_38 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower218 (some (3,input 4,input 7)) (by decide +kernel)

def rule254_39 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower246 (some (3,input 4,input 7)) (by decide +kernel)

def rule254_40 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower214 (some (3,input 4,input 7)) (by decide +kernel)

def rule254_41 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower222 (some (3,input 4,input 7)) (by decide +kernel)

def rule254_42 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower182 (some (3,input 4,input 7)) (by decide +kernel)

def rule254_43 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower252 (some (3,input 4,input 7)) (by decide +kernel)

def rule254_44 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower252 (some (1,input 5,input 7)) (by decide +kernel)

def rule254_45 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower222 (some (2,input 1,input 7)) (by decide +kernel)

def rule254_46 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower238 (some (1,input 5,input 7)) (by decide +kernel)

def rule254_47 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower246 (some (1,input 5,input 7)) (by decide +kernel)

def rule254_48 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower222 (some (2,input 4,input 7)) (by decide +kernel)

def rule254_49 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower222 (some (1,input 6,input 7)) (by decide +kernel)

def rule254_50 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower218 (some (1,input 6,input 7)) (by decide +kernel)

def rule254_51 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower182 (some (1,input 5,input 7)) (by decide +kernel)

def rule254_52 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower252 (some (1,input 6,input 7)) (by decide +kernel)

def rule254_53 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower246 (some (1,input 6,input 7)) (by decide +kernel)

def rule254_54 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower238 (some (1,input 6,input 7)) (by decide +kernel)

def rule254_55 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower190 (some (0,input 3,input 7)) (by decide +kernel)

def rule254_56 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower190 (some (3,input 3,input 7)) (by decide +kernel)

def rule254_57 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower182 (some (0,input 2,input 7)) (by decide +kernel)

def rule254_58 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower150 (some (0,input 2,input 7)) (by decide +kernel)

def rule254_59 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower182 (some (2,input 5,input 7)) (by decide +kernel)

def rule254_60 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower214 (some (1,input 6,input 7)) (by decide +kernel)

def rule254_61 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower158 none (by decide +kernel)

def rule254_62 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower158 (some (3,input 2,input 7)) (by decide +kernel)

def rule254_63 : {c : Cut // CutGood (goalAt 254) c} :=
  ruleFor 254 lower158 (some (3,input 3,input 7)) (by decide +kernel)

def cuts254 : Cuts (goalAt 254) := [rule254_0,rule254_1,rule254_2,rule254_3,rule254_4,rule254_5,rule254_6,rule254_7,rule254_8,rule254_9,rule254_10,rule254_11,rule254_12,rule254_13,rule254_14,rule254_15,rule254_16,rule254_17,rule254_18,rule254_19,rule254_20,rule254_21,rule254_22,rule254_23,rule254_24,rule254_25,rule254_26,rule254_27,rule254_28,rule254_29,rule254_30,rule254_31,rule254_32,rule254_33,rule254_34,rule254_35,rule254_36,rule254_37,rule254_38,rule254_39,rule254_40,rule254_41,rule254_42,rule254_43,rule254_44,rule254_45,rule254_46,rule254_47,rule254_48,rule254_49,rule254_50,rule254_51,rule254_52,rule254_53,rule254_54,rule254_55,rule254_56,rule254_57,rule254_58,rule254_59,rule254_60,rule254_61,rule254_62,rule254_63]

def state254_0 : List Sig := [0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 1,input 4,input 2,input 3,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_0 : Impossible true (goalAt 254) 8 state254_0.toFinset :=
  node_ok cuts254 [] 0xc24211010c20220809000620808c24240020824220808440420808a22209010a20220809000420808a222400208222208082404208086828090102404110110006110106828400184828110102404090108808121008800208088880220008808222008808208084840208084808222004800110104840120004808121004808110108880110102c0c121002c04090106860090102c0c1a180240c090104840090101a0a121001a02048085850048081a0a16140120a04808484004809000e121004840400044a4212909000e129084a4240004484012100840409080840020808848021000840421200840420808242020808440409080440012020444011000440411100440412020242012020240411100240040034242009000240409080240440010444011101000e090802420121002c280b081000d0b0a024281210024200908016060908016020480834300480816060d0c0120604808242004809000d09080242040000262209889000d0988826224000024200908090100480812022080900022080890104002090102080812020480854140480812021101052421480854141490854141101012020480834140480812020901032220c80834140c888341409010120204809000c4002c90802080812102080884044002c84042080900082080884040484084041181812101181844041494044041181852501181844040484044040981812100981824040c8c02404098183230098182404048402404129081210048404840068601a10129081a1804860484004840121009888121004840242005850161009888161404850242004840121004809000204809000b04840121040009000240009000a4000882802080900072080884044002484042080900082080884044001c84041181900051181844044001844041181900061181844044001444040981900030981824044001024040981900040981824044000c2404 (by decide +kernel)

def state254_1 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f000000000f0f0f0f000000000,0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0,0xffff0000ffff0000ffff0000ffff0000cccc0000cccc0000cccc0000cccc,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_1 : Impossible true (goalAt 254) 4 state254_1.toFinset :=
  node_ok cuts254 [] 0x34000900024100900004800520011818120004800160004810120004800900020808120004808440414808120220a001200048081200048081206058081202048089000208089000110004400110108480090002400090109000 (by decide +kernel)

def state254_2 : List Sig := [0xfffffffffffffffff0f0f0f000000000fffffffffffffffff0f0f0f000000000,0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0,0xffff0000ffff0000ffff0000ffff0000cccc0000cccc0000cccc0000cccc,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_2 : Impossible true (goalAt 254) 4 state254_2.toFinset :=
  node_ok cuts254 [] 0x4800900020808120004800160004810120004800520009818120004808900020808900020a001200048081200048081206058081202048082404148081202250009000240109000090002400090108480340009000241009000 (by decide +kernel)

def state254_3 : List Sig := [0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000,0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0,0xffff0000ffff0000ffff0000ffff0000cccc0000cccc0000cccc0000cccc,input 1,input 7,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_3 : Impossible true (goalAt 254) 5 state254_3.toFinset :=
  node_ok cuts254 [⟨state254_1,exclude254_1⟩,⟨state254_2,exclude254_2⟩] 0xd000240009040240001200148004606048001200240008202048001200058001204048001200090102606048001202110105202048081202240008202240008280048001202048001202048181602048081202090102606048084400110004404212009400240009004240002404110120001090102404240020000240002400 (by decide +kernel)

def state254_4 : List Sig := [0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0,input 2,0xffff0000ffff0000ffff0000ffff0000cccc0000cccc0000cccc0000cccc,input 1,input 7,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_4 : Impossible true (goalAt 254) 6 state254_4.toFinset :=
  node_ok cuts254 [⟨state254_3,exclude254_3⟩] 0xd00024000904024000240411010482809010b0002400090202400012001480046060480012000c8002606048001200240008202048001200058101604048001200068001604048001202110105202048081202090103202048081202240008202240008280048001202048001202058181606048081202058181a02048084404110204404120102404090202404800009404240009404240002420120004800110108880090106840090104840260009000250109000 (by decide +kernel)

def state254_5 : List Sig := [0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00,input 2,0xffff0000ffff0000ffff0000ffff0000cccc0000cccc0000cccc0000cccc,input 1,input 7,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_5 : Impossible true (goalAt 254) 6 state254_5.toFinset :=
  node_ok cuts254 [] 0xd00024000904024000240411010482809010b0002400090202400012001480046060480012000c8002606048001200240008202048001200058001204048001202110105202048081202090103202048081202240008202240008280048001202048001202048181602048081202048281a02048084400110004404120202400090002404111009400240009004240004800120004808110104840090104860090109800240009008240001a00048001208048002428 (by decide +kernel)

def state254_6 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f000000000f0f0f0f000000000,input 2,0xffff0000ffff0000ffff0000ffff0000cccc0000cccc0000cccc0000cccc,input 1,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_6 : Impossible true (goalAt 254) 5 state254_6.toFinset :=
  node_ok cuts254 [⟨state254_1,exclude254_1⟩] 0x340009000241009000120004800120204404260009000240209000048005200118181200048001a0004820120004800160004810120004800900020808120004808440414808120204808120a06808120220a001200048081200048081206058081202048089000208089000110004400110104808111004840800004440090002400090109000 (by decide +kernel)

def state254_7 : List Sig := [0xfffffffffffffffff0f0f0f000000000fffffffffffffffff0f0f0f000000000,input 2,0xffff0000ffff0000ffff0000ffff0000cccc0000cccc0000cccc0000cccc,input 1,input 7,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_7 : Impossible true (goalAt 254) 5 state254_7.toFinset :=
  node_ok cuts254 [⟨state254_2,exclude254_2⟩] 0x260009000240209000120004800120202404048001a0004820120004800900020808120004800160004810120004800520009818120004808120a06808120204808900020808900020a001200048081200048081206058081202048082404148081202091002c40800002440250009000240109000090002400090104808340009000241009000 (by decide +kernel)

def state254_8 : List Sig := [0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000,input 2,0xffff0000ffff0000ffff0000ffff0000cccc0000cccc0000cccc0000cccc,input 1,input 7,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_8 : Impossible true (goalAt 254) 6 state254_8.toFinset :=
  node_ok cuts254 [⟨state254_6,exclude254_6⟩,⟨state254_7,exclude254_7⟩,⟨state254_3,exclude254_3⟩] 0xd000240009040240004800120004808110109800240009008240001200148004606048001200068001208048001200240008202048001200058001204048001200090102606048001202110105202048081202048281a020480812022400082022400082800480012020480012020481816020480812020901026060480844001100044041202044401210200021110094002400090042400024041101200010901024040b010240c090102404240020000240002400 (by decide +kernel)

def state254_9 : List Sig := [0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,input 2,0xffff0000ffff0000ffff0000ffff0000cccc0000cccc0000cccc0000cccc,input 1,input 7,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_9 : Impossible true (goalAt 254) 6 state254_9.toFinset :=
  node_ok cuts254 [] 0xd000240009040240004800120004808110109800240009008240001200148004606048001200068001208048001200240008202048001200090002602048001202110105202048081202048281a020480812022400082022400082800480012020480012020900026020900024001900044040900024000b0002408090002400240009404090002404120204404090102404090302c04090102404240009404240001604048001604048002404048081606048084440 (by decide +kernel)

def state254_10 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,0xffff0000ffff0000ffff0000ffff0000cccc0000cccc0000cccc0000cccc,input 1,input 7,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_10 : Impossible true (goalAt 254) 6 state254_10.toFinset :=
  node_ok cuts254 [] 0x9800240009008240004820120804828222002c0409010240c0901024200b0802428090809400240009004240002420110802440090802400090002404212001200068001208048001200058001204048001200240008202048001200148804a2a0480012000c8002606048001202048281a02048081202048181602048081202240008202240008280048001202048001202120a0522204808120209010320204808d02024000b0402400044042c0009000240809000 (by decide +kernel)

def state254_11 : List Sig := [0xffffffff000000000000000000000000ffffffff00000000,input 6,0xffff0000ffff0000ffff0000ffff0000cccc0000cccc0000cccc0000cccc,input 1,input 7,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_11 : Impossible true (goalAt 254) 6 state254_11.toFinset :=
  node_ok cuts254 [] 0x98002400090082400048001200048081101024200b0802428090809400240009004240004400110004404120201200068001208048001200058001204048001200240008202048001200148004606048001202048281a0204808120204818160204808120224000820224000828004800120204800120211010520204808d0002400090402400024040b010240c09010240009000240411100b000240009020240003200048002606048002404048083202048084828 (by decide +kernel)

def state254_12 : List Sig := [0xffff0000ffff0000ffff0000ffff0000cccc0000cccc0000cccc0000cccc,input 1,input 7,input 2,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_12 : Impossible true (goalAt 254) 7 state254_12.toFinset :=
  node_ok cuts254 [⟨state254_4,exclude254_4⟩,⟨state254_5,exclude254_5⟩,⟨state254_8,exclude254_8⟩,⟨state254_9,exclude254_9⟩,⟨state254_10,exclude254_10⟩,⟨state254_11,exclude254_11⟩] 0x3410044043400090004002090003410100082410090001101090001a0a024040901044048001444041a0a20004120a044040901024042c08024042c00090004002090002c08100082408090000901090001202088801200044041210048001202048401202044042220044040b03048400b01024041a18024040b03068600903024041210024042602048402600090002220090002602088802402090001210090001101024201100048081110044001101044401101048080908048080901044400900200030908024000901024200901200021110044408000424200908048400b0a02c20800002c28090a048400908024202501024202500090002120090002501084802401090000908090001181812000480044041490052001181852401181844040480012000981812000480024040c8803200098183220098182404048001200129081200048004840068201a00129081a0804820484004800120009888120004800242005810160009888160404810242004800120020808120004800900020a0090002080882802080890000480012001181812020480844041490844041181852421480844040480812020981812020480824040c88824040981832220c808240404808120212908120204808484006828120a129081a0a06808484004808120209888120204808242005818120609888160605808242004808120220808120204808900024200900020808908020808900004808900020a00908020a00120004808120020a001202048081200242001200 (by decide +kernel)

def state254_13 : List Sig := [0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 1,input 7,input 2,input 3,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_13 : Impossible true (goalAt 254) 8 state254_13.toFinset :=
  node_ok cuts254 [⟨state254_12,exclude254_12⟩] 0xc24211010c20220809001420808c24240020824220808440420809001411010440440014460611819001411818460640014440411010682809010240411011001411010682840050482811010240409010a22209010a20220809001320808a2224002082222080824042080900130901024044000c26060981900130981826064000c24040901054140480812021101052421480854141490844141101012020480834140480812020901032220c80834140c8882414090101202048090008048081202208089080208090008242009080208081202048090008400220000400081202048090008048081202400090008400084808222004800110104840120004808121004808110108880110102c0c121002c04090106860090102c0c1a180240c090104840090101a0a121001a02048085850048081a0a16140120a048084840048088a0a121008a02208088880208088a0a22200820a208084840208090011121004840400044a42129090011129084a424000448401210044040908044001202044401100044041110044041202024201202024041110024004004024200900024040908024044004c44401110016060908016020480834300480816060d0c01206048082420048090011090802420121002c280b08100100b0a024281210024200908086060908086022080884802080886062120082062080824202080900100908024204000026220988900100988826224000024200908100124002c840411818828011818440430b00440411818c2c011818440420a00440409818828009818240428a80240409818a2a009818240420a0024040480882800480890804002c908004809000804808908020a00828012908828012908484040044484012909001112908484020a00484009888828009888242040040242009889001009888242020a00242020809000720809000b20a0082804002d000b21019000f4001c1210 (by decide +kernel)

def state254_14 : List Sig := [0xffffffffffffffffffffffff33333333ffffffffffffffffffffffff00000000,input 6,input 1,input 7,input 2,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_14 : Impossible true (goalAt 254) 6 state254_14.toFinset :=
  node_ok cuts254 [] 0x12022080890300480812021488848380480812020c8082414048081a0204808120a048088a0220808820a208084820120804828222002c0409010240c0901016020480812060480824200b0802428090808602208088206208082420110802440090802400090002404400001200048001202242001210068401218048401210058401214048408200208008202048401210120a0482a04840260409010240609010c22220808a242208084404288088202208888202 (by decide +kernel)

def state254_15 : List Sig := [0xffffffff333333330000000000000000ffffffff00000000,input 6,input 1,input 7,input 2,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_15 : Impossible true (goalAt 254) 6 state254_15.toFinset :=
  node_ok cuts254 [] 0x1202208089030048081202148084414048081a0204808120a048088a0220808820a2080848001200048081101016020480812060480824200b080242809080860220808820620808440011000440412020120004800120224200121006840121804840121005840121404840820020800820204840460411010440611010c2022080882422080832020480824140480824040b010240c09010240009000240411100a202208088222208082404098102406090104828 (by decide +kernel)

def state254_16 : List Sig := [0xffffffff33333333ffffffff33333333ffffffff00000000ffffffff00000000,input 1,input 7,input 2,input 3,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_16 : Impossible true (goalAt 254) 7 state254_16.toFinset :=
  node_ok cuts254 [⟨state254_14,exclude254_14⟩,⟨state254_15,exclude254_15⟩] 0x3090844043080882024001c8202309090007209088202110108202150501202048084404149085202150505242110504404048081202240c01202048088202242008202240c09080240c082020480812020d05012020480824040c88832020d05032220905024040480812021202088801200044041210048001202048401202044042220044040682848400680812021614012020682858500482812021210012022282848402280882022220082022282888802082882021210082020b03048400b01024041a18024040b03068600903024041210024041101024201100048081110044001101044401101048080908048080581824200580812020d0c012020581834300481812020908012024006824200908048400b0a02c20400582c28090a0484009080242021818242021808820221200820221818848020818820209080820209010444009001000009080240009010242009011000011100444011818121011810440414940440411818525011018440404840440404808a28004800908004840120004808121004808908028a009080129081210048404840068601a10129081a1804860484004840121009888121004840242005850161009888161404850242004840121020808121020800882828a00820020808a2802080888280484012100981812100981024040c8c024040981832300901824040484024041a0a024040901044048000444041a0a20000120a04404090102404288882404288088202400648202288890018208888202090108202 (by decide +kernel)

def state254_17 : List Sig := [0xfffffffffffffffff3f3f3f333333333fffffffffffffffff0f0f0f000000000,0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0,input 1,input 7,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_17 : Impossible true (goalAt 254) 4 state254_17.toFinset :=
  node_ok cuts254 [] 0x4808820224140120204808520209050120204800120004808908020800820020808121004840161004850121009810240409018240405808120204818120221808820220818820209000240009011001c308088202209088202 (by decide +kernel)

def state254_18 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f000000000f0f0f0f000000000,0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0,0xffffffffffffffff3333333333333333ffffffffffffffff0000000000000000,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_18 : Impossible true (goalAt 254) 4 state254_18.toFinset :=
  node_ok cuts254 [] 0x48085202110501202048088202090501202048001200048089080118104404110184404048401610048501210208008200208082404308088202209088202058081202048181202110004400110102480090002400090108202 (by decide +kernel)

def state254_19 : List Sig := [0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000,0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0,0xffffffffffffffff3333333333333333ffffffffffffffff0000000000000000,input 1,input 7,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_19 : Impossible true (goalAt 254) 5 state254_19.toFinset :=
  node_ok cuts254 [⟨state254_17,exclude254_17⟩,⟨state254_18,exclude254_18⟩] 0x120220808905004808120214808441404808120004800120224200820020800820204840460411010440611010121005840121404840260409010240609010c2022080882422080816020480812060480886022080882062080844001100044044007024040480824140480824042080a0001208082404110120000090102400 (by decide +kernel)

def state254_20 : List Sig := [0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0,input 2,0xffffffffffffffff3333333333333333ffffffffffffffff0000000000000000,input 1,input 7,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_20 : Impossible true (goalAt 254) 6 state254_20.toFinset :=
  node_ok cuts254 [⟨state254_19,exclude254_19⟩] 0xa2022080882222080824041101048280901012020c808241404808120220808905004808120214808441404808260409010240609010120004800120224200820020800820204840460411010440611010121005850161404840121006840161404840c20220808824220808240409020240480000160604808160604808860620808860620808440411020440412010242009010684009010484006808120205818120222808820221818820212000480011011001c (by decide +kernel)

def state254_21 : List Sig := [0xfffffffffffffffff3f3f3f333333333fffffffffffffffff0f0f0f000000000,input 2,input 1,input 7,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_21 : Impossible true (goalAt 254) 5 state254_21.toFinset :=
  node_ok cuts254 [⟨state254_17,exclude254_17⟩] 0x48088202241401202048085202090501202068081202048281202228088202208288202120004800120202404048001200048089080048401a10048601210208008200208081210048401610048501210098102404090182404058081202048181202091002c40800002440218088202208188202090002400090104808308088202209088202 (by decide +kernel)

def state254_22 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f000000000f0f0f0f000000000,input 2,0xffffffffffffffff3333333333333333ffffffffffffffff0000000000000000,input 1,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_22 : Impossible true (goalAt 254) 5 state254_22.toFinset :=
  node_ok cuts254 [⟨state254_18,exclude254_18⟩] 0x48085202110501202048088202090501202068081202048281202120004800120204404228088202208288202048001200048089080048401a10048601210118104404110184404048401610048501210208008200208082404308088202209088202058081202048181202111004840800004440110004400110104808090002400090108202 (by decide +kernel)

def state254_23 : List Sig := [0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000,input 2,0xffffffffffffffff3333333333333333ffffffffffffffff0000000000000000,input 1,input 7,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_23 : Impossible true (goalAt 254) 6 state254_23.toFinset :=
  node_ok cuts254 [⟨state254_21,exclude254_21⟩,⟨state254_22,exclude254_22⟩,⟨state254_19,exclude254_19⟩] 0x1202208089050048081202148084414048081a0204808120a048088a0220808820a20808480012000480811010120004800120224200121006840121804840820020800820204840460411010440611010121005840121404840260409010240609010c2022080882422080816020480812060480844401210200021110086022080882062080844001100044041202024040480824140480824040b010240c0901024042080a0001208082404110120000090102400 (by decide +kernel)

def state254_24 : List Sig := [0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,input 2,0xffffffffffffffff3333333333333333ffffffffffffffff0000000000000000,input 1,input 7,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_24 : Impossible true (goalAt 254) 6 state254_24.toFinset :=
  node_ok cuts254 [] 0x1202208089050048081202148084414048081a0204808120a048088a0220808820a20808480012000480811010120004800120224200121006840121804840820020800820204840460411010440611010260009000240209000c2022080882422080824000d00016060900024000b0002408090002400208088606090002400190004404090002404048083404048082404090302c04090102404208088606208082404090182604090102404120204404090104440 (by decide +kernel)

def state254_25 : List Sig := [0xff00ff00ff00ff003300330033003300ff00ff00ff00ff0000000000000000,0xffffffffffffffff3333333333333333ffffffffffffffff0000000000000000,input 1,input 7,input 2,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_25 : Impossible true (goalAt 254) 6 state254_25.toFinset :=
  node_ok cuts254 [] 0xa2022080882222080868001200048201200012020c8082414048081202208089050048085800120004810120002400090002404111001602048081206048088602208088206208084c00120004804120002604090102406090101200048001202242001210058401214048408200208008202048404a0012000480212000480022000c242120004840090106840090104840048085840048084440090804440090804840208088840208084840048404a40048404404 (by decide +kernel)

def state254_26 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f030303030f0f0f0f0f0f0f0f0f0f0f0f000000000,0xffffffffffffffff3333333333333333ffffffffffffffff0000000000000000,input 1,input 7,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_26 : Impossible true (goalAt 254) 5 state254_26.toFinset :=
  node_ok cuts254 [] 0x4808820224140120204808520212060120206808120204828120222808820220828820212000480012021001c048001200048089080048401a10048601210208008200208081210128204808120284808098002400090082400308088202209088202090003400090402400090002c00090202400090008202112002400090004400091002400 (by decide +kernel)

def state254_27 : List Sig := [0xfff0fff0fff0fff0f3f0f3f0f3f0f3f0fff0fff0fff0fff0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffff33333333ffffffffffffffffffffffff00000000,input 1,input 7,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_27 : Impossible true (goalAt 254) 4 state254_27.toFinset :=
  node_ok cuts254 [] 0x48088202240c0120204808320209050120204800120004808908020800820020808121009810240409018240404840161004850121028808820220888820205808120204818120221808820220818820209000240009011001c (by decide +kernel)

def state254_28 : List Sig := [0xff00ff00ff00ff003300330033003300ff00ff00ff00ff000000000000000000,0xffffffffffffffffffffffff33333333ffffffffffffffffffffffff00000000,input 1,input 7,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_28 : Impossible true (goalAt 254) 5 state254_28.toFinset :=
  node_ok cuts254 [⟨state254_27,exclude254_27⟩] 0x12022080890300480812020c808241404808160204808120604808860220808820620808240009000240440070242012082000009080120004800120224200121005840121404840820020800820204840260409010240609010121012080482204840a202208088222208084820048084830048084820208084880208084800 (by decide +kernel)

def state254_29 : List Sig := [0xffffffffffffffffffffffff33333333ffffffffffffffffffffffff00000000,0xffffffffffffffff3333333333333333ffffffffffffffff0000000000000000,input 1,input 7,input 2,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_29 : Impossible true (goalAt 254) 6 state254_29.toFinset :=
  node_ok cuts254 [⟨state254_26,exclude254_26⟩,⟨state254_28,exclude254_28⟩] 0x12022080890500480812021488848380480812020c8082414048081a0204808120a048088a0220808820a208084820120804828800042c0409010240c0901016020480812060480824200b0802428090808602208088206208082420110802440090802400090002404800001200048001202242001210068401218048401210058401214048408200208008202048401210120a0482a04840260409010240609010c22220808a242208084404288088202208888202 (by decide +kernel)

def state254_30 : List Sig := [0xcccccccc000000000000000000000000ffffffff00000000,0xffffffffffffffff3333333333333333ffffffffffffffff0000000000000000,input 1,input 7,input 2,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_30 : Impossible true (goalAt 254) 6 state254_30.toFinset :=
  node_ok cuts254 [] 0x1202208089050048081202148084414048081a0204808120a048088a0220808820a2080848001200048081101016020480812060480824200b080242809080860220808820620808440011000440412020120004800120224200121006840121804840121005840121404840820020800820204840460411010440611010c2022080882422080832020480824140480824040b010240c09010240009000240411100a202208088222208082404098102406090104828 (by decide +kernel)

def state254_31 : List Sig := [0xffffffffffffffff3333333333333333ffffffffffffffff0000000000000000,input 1,input 7,input 2,input 3,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_31 : Impossible true (goalAt 254) 7 state254_31.toFinset :=
  node_ok cuts254 [⟨state254_20,exclude254_20⟩,⟨state254_23,exclude254_23⟩,⟨state254_24,exclude254_24⟩,⟨state254_25,exclude254_25⟩,⟨state254_29,exclude254_29⟩,⟨state254_30,exclude254_30⟩] 0x2888824042880882024001c82022888900072088882020901082021a0a024040901044048001444041a0a20004120a044040901024040d05012020480824040c88832020d05032220905024040480812022414012020480882022420082022414090802414082020480812021505012020480844041490852021505052421105044040480812020b03048400b01024041a18024040b03068600903024041210024040682848400680812021614012020682858500482812021210012022282848402280882022220082022282888802082882021210082021202200031200044041210048001202048401202044044007444040901044400900200020908024000901024200901200011110044400581824200580812020d0c012020581834300481812020908012024007424200908048400b0a02c20800002c28090a048400908024202181824202180882022120082022181884802081882020908082021101024201100048081110044001101044401101048080908048080981812100981024040c8c0240409818323009018240404840240404808c28004800908004840120004808121004808908030a009080129081210048404840068601a10129081a1804860484004840121009888121004840242005850161009888161404850242004840121020808121020800905030a00820020808c280208089050048401210118181210118104404149404404118185250110184404048404404309084404308088202400148202309090005209088202110108202 (by decide +kernel)

def state254_32 : List Sig := [0x3333333333333333333333333333333300000000000000000000000000000000,input 1,input 7,input 2,input 3,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_32 : Impossible true (goalAt 254) 8 state254_32.toFinset :=
  node_ok cuts254 [⟨state254_16,exclude254_16⟩,⟨state254_31,exclude254_31⟩] 0xc24211010c20220809000f20808c2424001c824220808440420808682809010240411011000f1101068284003c482811010240409010a22209010a20220809001b20808a2224001c82222080824042080854140480812021101052421480854141490844141101012020480834140480812020901032220c80834140c8882414090101202048090007048081202208089080208090008242009080208081202048084808222004800110104840120004808121004808110108880110102c0c121002c04090106860090102c0c1a180240c090104840090101a0a121001a02048085850048081a0a16140120a048084840048088a0a121008a02208088880208088a0a22200820a2080848402080844040908044001202044401100044041110044041202024201202024041110024004005824200900024040908024044006c44401110016060908016020480834300480816060d0c01206048082420048090017090802420121002c280b08100160b0a024281210024200908086060908086022080884802080886062120082062080824202080846060484046041101052501101046061494044061101012101101026060484026040901032300901026060c8c0240609010121009010120240078120024200121004800120204840120224201001e242004a42048401210121001a18068404a4206860121812100121004840262204840121009080161405840262205850121409080121004841000b4002c820020809000720809000b0484012104003d00054001444044003c44044001d000f8000444044001444044006d00034000c24044006c24044001d001b8000024044000c24042420100022420012024001c12022420100082420012024000812022220100012220048404005c48402220100172220048404000448402120100002120024204005824202120100162120024204000024204002d0015210110007400508280 (by decide +kernel)

def state254_33 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f000000000f0f0f0f000000000,0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0,0x3333333333333333333333333333333333330000333300003333000033330000,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_33 : Impossible true (goalAt 254) 4 state254_33.toFinset :=
  node_ok cuts254 [] 0x30800820020900820004800520015050120004800820024040120004840440414840440420a001200048401200048401214058401210210108200240408200110004400110108480058001200048101200090002400090108200 (by decide +kernel)

def state254_34 : List Sig := [0xfffffffffffffffff0f0f0f000000000fffffffffffffffff0f0f0f000000000,0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0,0x3333333333333333333333333333333333330000333300003333000033330000,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_34 : Impossible true (goalAt 254) 4 state254_34.toFinset :=
  node_ok cuts254 [] 0x480082002404012000480052000d050120021010820024040820020a001200048401200048401214058401210048402404148402404218008200208108200058001200048101200090002400090108480308008200209008200 (by decide +kernel)

def state254_35 : List Sig := [0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000,0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0,0x3333333333333333333333333333333333330000333300003333000033330000,input 4,input 7,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_35 : Impossible true (goalAt 254) 5 state254_35.toFinset :=
  node_ok cuts254 [⟨state254_33,exclude254_33⟩,⟨state254_34,exclude254_34⟩] 0xc200208008240208001200148005414048001200208009010048001210110105210110108404208009010208008280048001210048001210048501610048401210090103414090104400110004404212008600208008204208001600048001204048002404110120001090102404208020000208002404048003414048002400 (by decide +kernel)

def state254_36 : List Sig := [0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0,input 2,0x3333333333333333333333333333333333330000333300003333000033330000,input 4,input 7,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_36 : Impossible true (goalAt 254) 6 state254_36.toFinset :=
  node_ok cuts254 [⟨state254_35,exclude254_35⟩] 0xc20020800824020800240411010482809010a2002080082202080012001480054140480012000c8003414048001200208009010048001210110105210110101210090103210090108404208009010208008280048001210048001210058501614048401210058501a10048404404110204404120102404090202404800008604208008604208001604048001604048002420120004800110108880090106840090104840228008200218108200068001200058101200 (by decide +kernel)

def state254_37 : List Sig := [0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00,input 2,0x3333333333333333333333333333333333330000333300003333000033330000,input 4,input 7,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_37 : Impossible true (goalAt 254) 6 state254_37.toFinset :=
  node_ok cuts254 [] 0xc20020800824020800240411010482809010a2002080082202080012001480054140480012000c8003414048001200208009010048001210110105210110101210090103210090108404208009010208008280048001210048001210048501610048404400110004404120202400090002404111008600208008204208001600048001204048004800120004808110104840090104860090108a00208008208208001a00048001208048001218048401a10048402428 (by decide +kernel)

def state254_38 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f000000000f0f0f0f000000000,input 2,0x3333333333333333333333333333333333330000333300003333000033330000,input 4,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_38 : Impossible true (goalAt 254) 5 state254_38.toFinset :=
  node_ok cuts254 [⟨state254_33,exclude254_33⟩] 0x30800820020900820012000480012020440406800120004820120022800820020820820004800520015050120004800820024040120004840440414840440404840121806840121020a001200048401200048401214058401210210108200240408200110004400110104808111004840800004440058001200048101200090002400090108200 (by decide +kernel)

def state254_39 : List Sig := [0xfffffffffffffffff0f0f0f000000000fffffffffffffffff0f0f0f000000000,input 2,0x3333333333333333333333333333333333330000333300003333000033330000,input 4,input 7,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_39 : Impossible true (goalAt 254) 5 state254_39.toFinset :=
  node_ok cuts254 [⟨state254_34,exclude254_34⟩] 0x2280082002082082000680012000482012001200048001202024040480082002404012000480052000d050120004840121806840121021010820024040820020a001200048401200048401214058401210048402404148402404091002c40800002440218008200208108200058001200048101200090002400090104808308008200209008200 (by decide +kernel)

def state254_40 : List Sig := [0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000,input 2,0x3333333333333333333333333333333333330000333300003333000033330000,input 4,input 7,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_40 : Impossible true (goalAt 254) 6 state254_40.toFinset :=
  node_ok cuts254 [⟨state254_38,exclude254_38⟩,⟨state254_39,exclude254_39⟩,⟨state254_35,exclude254_35⟩] 0xc200208008240208004800120004808110108a00208008208208001a00048001208048001200148005414048001200208009010048001210110105210110101210048601a100484084042080090102080082800480012100480012100485016100484012100901034140901044001100044041202044401210200021110086002080082042080016000480012040480024041101200010901024040b010240c090102404208020000208002404048003414048002400 (by decide +kernel)

def state254_41 : List Sig := [0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,input 2,0x3333333333333333333333333333333333330000333300003333000033330000,input 4,input 7,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_41 : Impossible true (goalAt 254) 6 state254_41.toFinset :=
  node_ok cuts254 [] 0xc200208008240208004800120004808110108a00208008208208001a00048001208048001200148005414048001200208009010048001210110105210110101210048601a100484084042080090102080082800480012100480012100900034100900024001900044040900024000b0002408090002400208008604090002400048001604048002404120204404090102404090302c04090102404208008604208001604048001604048002404048401614090104440 (by decide +kernel)

def state254_42 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,0x3333333333333333333333333333333333330000333300003333000033330000,input 4,input 7,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_42 : Impossible true (goalAt 254) 6 state254_42.toFinset :=
  node_ok cuts254 [] 0x8a00208008208208001a00048001208048004820120804828222002c0409010240c0901024200b08024280908086002080082042080016000480012040480024201108024400908024000900024042120012002080090100480012001488058380480012000c8003414048001210048601a10048401210048501610048408404208009010208008280048001210048001210120a0523004840121009010321009010c22020800a240208004404288008200208808200 (by decide +kernel)

def state254_43 : List Sig := [0xffffffff000000000000000000000000ffffffff00000000,input 6,0x3333333333333333333333333333333333330000333300003333000033330000,input 4,input 7,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_43 : Impossible true (goalAt 254) 6 state254_43.toFinset :=
  node_ok cuts254 [] 0x8a00208008208208001a000480012080480048001200048081101024200b0802428090808600208008204208001600048001204048004400110004404120201200208009010048001200148005414048001210048601a1004840121004850161004840840420800901020800828004800121004800121011010521011010c2002080082402080024040b010240c09010240009000240411100a200208008220208003200048003414048002404048403210090104828 (by decide +kernel)

def state254_44 : List Sig := [0x3333333333333333333333333333333333330000333300003333000033330000,input 4,input 7,input 2,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_44 : Impossible true (goalAt 254) 7 state254_44.toFinset :=
  node_ok cuts254 [⟨state254_36,exclude254_36⟩,⟨state254_37,exclude254_37⟩,⟨state254_40,exclude254_40⟩,⟨state254_41,exclude254_41⟩,⟨state254_42,exclude254_42⟩,⟨state254_43,exclude254_43⟩] 0x3090044043080082004002082003090100082090082001101082001a0a024040901044048001444041a0a20004120a044040901024042888024042880082004002082002888100082088082000901082001202088801200044041210048001202048401202044042220044040b03048400b01024041a18024040b03068600903024041210024042282048402280082002220082002282088802082082001210082000682048400680012001614012000682058500482012001210012001101024201100048081110044001101044401101048080908048080901044400900200030908024000901024200901200021110044408000424200908048400b0a02c20800002c28090a048400908024202181024202180082002120082002181084802081082000908082000581024200580012000d0c012000581034300481012000908012001505012000480044041490052001505052401505044040480012000d05012000480024040c88032000d05032200d05024040480012002404012000480082002420082002404090802404082000480012001505012100484044041494044041505052501484044040484044040d05012100484024040c8c024040d05032300c8402404048402404161401210048404840068601218161401a180684048400484012100d0c012100484024200585012140d0c0161405840242004840121024040121021010820020a00820024040828024040820004840820024200828020a00120004840120024200121004840120020a001200 (by decide +kernel)

def state254_45 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 1,input 2,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_45 : Impossible true (goalAt 254) 8 state254_45.toFinset :=
  node_ok cuts254 [⟨state254_44,exclude254_44⟩] 0xd05011010440424041002424040d05040020905024040440411011002411010440440014541415051002415050541440014440411010682809010240411011002411010682840090482811010240409010b03009010240424041002324040b0304002090302404024040901100230901024044000c34140d05100230d05034144000c2404090104808222004800110104840120004808121004808110108880110102c0c121002c04090106860090102c0c1a180240c0901048400901098181210098102404088802404098182220090182404048402404100221210048402420058501614100221614058502420048401210100221210048404000458501614100221614058504000448401210044040908044001202044401100044041110044041202024201202024041110024004008424200900024040908024044008c4440111010022090802420121002c280b08100210b0a024281210024200908094140908094102404084802404094142120090142404024202404100210908024202420034300d0c100210d0c034302420024200908100210908024204000034300d0c100210d0c034304000024200908046060484046041101052501101046061494044061101012101101026060484026040901032300901026060c8c02406090101210090104a42048401210121001a18068404a4206860121812100121004840262204840121009080161405840262205850121409080121004841000804840121024040828024041000820a00828024040121004841000220a00828024200121004841000804840121024200828020a0100084002200004002c12100484100080484012104002d00084002d002040008820215050908015050440434300440415050d0c01505044042420044040d05090800d05024042c28024040d050b0a00d050240424200240424041000724041000224200908040009000221051001f4001c1202 (by decide +kernel)

def state254_46 : List Sig := [0xffffffffffffffffffffffff0000ffffffffffffffffffffffffffff00000000,input 6,input 4,input 7,input 1,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_46 : Impossible true (goalAt 254) 6 state254_46.toFinset :=
  node_ok cuts254 [] 0x9810240409018240401a0204808120a048084820120804828222002c0409010240c0901024200b080242809080941024040901424040160204808120604808242011080244009080240009000240440000121006840121804840121005840121404840121024040822204840120004800120220a001210120a0482a0484026040901024060901090002400090100480812021488848380480812020c808241404808c222240408242240404404208088202208882404 (by decide +kernel)

def state254_47 : List Sig := [0xffffffff0000ffff0000000000000000ffffffff00000000,input 6,input 4,input 7,input 1,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_47 : Impossible true (goalAt 254) 6 state254_47.toFinset :=
  node_ok cuts254 [] 0x9810240409018240401a0204808120a0480848001200048081101024200b080242809080941024040901424040160204808120604808440011000440412020121006840121804840121005840121404840121024040822204840120004800120220a00460411010440611010900024000901004808120214808441404808c20230808c2421101024040b010240c090102400090002404111002404098102406090108202208088222090103202048082414048084828 (by decide +kernel)

def state254_48 : List Sig := [0xffffffff0000ffffffffffff0000ffffffffffff00000000ffffffff00000000,input 4,input 7,input 1,input 2,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_48 : Impossible true (goalAt 254) 7 state254_48.toFinset :=
  node_ok cuts254 [⟨state254_46,exclude254_46⟩,⟨state254_47,exclude254_47⟩] 0x3414044041101090104001c90103414100072414090101101044041202088801200044041210048001202048401202044042220044042606048402604090102220090102606088802406090101210090100682848400680812021614012020682858500482812021210012020b03048400b01024041a18024040b0306860090302404121002404110102420110004808111004400110104440110104808090804808400a024200908048400b0a02c20400982c28090a048400908024202505024202504090102120090102505084802405090100908090100581824200580812020d0c01202058183430048181202090801202090104440090010000090802400090102420090110000111004440118181210118104404149404404118185250110184404048404404129081210048404840068601a10129081a1804860484004840121009888121004840242005850161009888161404850242004840121020888121004840901020a00901020888828020888901004840121004808828004800b08004840120004808121004808b08020a0082800981812100981024040c8c024040981832300901824040484024041505012020480844041490852021505052421105044040480812022404012022400082222c200900024040b0802404082220480812020d05012020480824040c88832020d05032220905024040480812021a0a024040901044048000444041a0a20000120a04404090102404208882404208089010400648202208890018208889010090102404 (by decide +kernel)

def state254_49 : List Sig := [0xfffffffffffffffff0f0ffff0000fffffffffffffffffffff0f0f0f000000000,0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0,input 4,input 7,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_49 : Impossible true (goalAt 254) 4 state254_49.toFinset :=
  node_ok cuts254 [] 0x4840901020908121004800120004808828004840161004850121009810240409018240424000900024040120204808520209050120225040901024050901005808120204818120209000240009011001c208088202209082404 (by decide +kernel)

def state254_50 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f000000000f0f0f0f000000000,0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0,0xffffffffffffffff0000ffff0000ffffffffffffffffffff0000000000000000,input 4,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_50 : Impossible true (goalAt 254) 4 state254_50.toFinset :=
  node_ok cuts254 [] 0x48001200048088280118104404110184404048401610048501210098102404090182404048085202110501202240009000240401202208088202209082404058081202048181202110004400110102480090002400090109010 (by decide +kernel)

def state254_51 : List Sig := [0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000,0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0,0xffffffffffffffff0000ffff0000ffffffffffffffffffff0000000000000000,input 4,input 7,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_51 : Impossible true (goalAt 254) 5 state254_51.toFinset :=
  node_ok cuts254 [⟨state254_49,exclude254_49⟩,⟨state254_50,exclude254_50⟩] 0x121024040824204840120004800120220a004604110104406110101210058401214048402604090102406090109000240009010048081202148084414048088202208088242110109410240409014240401602048081206048084400110004404400702404240420001090102404048082414048082404110120000090102400 (by decide +kernel)

def state254_52 : List Sig := [0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0,input 2,0xffffffffffffffff0000ffff0000ffffffffffffffffffff0000000000000000,input 4,input 7,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_52 : Impossible true (goalAt 254) 6 state254_52.toFinset :=
  node_ok cuts254 [⟨state254_51,exclude254_51⟩] 0x240424040903009010240411010482809010260409010240609010121024040824204840120004800120220a0046041101044061101012100585016140484012100684016140484012020c808241404808900024000901004808120214808441404808820220808824211010240409020240480000941424040941424040160604808160604808440411020440412010242009010684009010484026040901025050901006808120205818120212000480011011001c (by decide +kernel)

def state254_53 : List Sig := [0xfffffffffffffffff0f0ffff0000fffffffffffffffffffff0f0f0f000000000,input 2,input 4,input 7,input 1,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_53 : Impossible true (goalAt 254) 5 state254_53.toFinset :=
  node_ok cuts254 [⟨state254_49,exclude254_49⟩] 0x260409010240609010068081202048281202120004800120202404048401a10048601210048409010209081210048001200048088280048401610048501210098102404090182404240009000240401202048085202090501202091002c40800002440250409010240509010058081202048181202090002400090104808208088202209082404 (by decide +kernel)

def state254_54 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f000000000f0f0f0f000000000,input 2,0xffffffffffffffff0000ffff0000ffffffffffffffffffff0000000000000000,input 4,input 1,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_54 : Impossible true (goalAt 254) 5 state254_54.toFinset :=
  node_ok cuts254 [⟨state254_50,exclude254_50⟩] 0x680812020482812021200048001202044040b0102404090302404048401a10048601210048001200048088280118104404110184404048401610048501210098102404090182404048085202110501202240009000240401202208088202209082404111004840800004440058081202048181202110004400110104808090002400090109010 (by decide +kernel)

def state254_55 : List Sig := [0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000,input 2,0xffffffffffffffff0000ffff0000ffffffffffffffffffff0000000000000000,input 4,input 7,input 1,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_55 : Impossible true (goalAt 254) 6 state254_55.toFinset :=
  node_ok cuts254 [⟨state254_53,exclude254_53⟩,⟨state254_54,exclude254_54⟩,⟨state254_51,exclude254_51⟩] 0x9810240409018240401a0204808120a04808480012000480811010121006840121804840121024040824204840120004800120220a0046041101044061101012100584012140484026040901024060901090002400090100480812021480844140480882022080882421101044401210200021110094102404090142404016020480812060480844001100044041202024040b010240c090102404240420001090102404048082414048082404110120000090102400 (by decide +kernel)

def state254_56 : List Sig := [0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,input 2,0xffffffffffffffff0000ffff0000ffffffffffffffffffff0000000000000000,input 4,input 7,input 1,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_56 : Impossible true (goalAt 254) 6 state254_56.toFinset :=
  node_ok cuts254 [] 0x9810240409018240401a0204808120a04808480012000480811010121006840121804840121024040824204840120004800120220a0046041101044061101026000900024020900090002400090100480812021480844140480882022080882421101024000b00024080900024002404094140900024000d0001606090002400190004404090002404090302c04090102404090182604090102404240409414090102404048083404048082404120204404090104440 (by decide +kernel)

def state254_57 : List Sig := [0xff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff0000000000000000,0xffffffffffffffff0000ffff0000ffffffffffffffffffff0000000000000000,input 4,input 7,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_57 : Impossible true (goalAt 254) 6 state254_57.toFinset :=
  node_ok cuts254 [] 0x2404240409030090106800120004820120002400090002404111009410240409014240401602048081206048084c0012000480412000260409010240609010121005840121404840121024040824204840120004800120220a004a001200048021200012020c8082414048089000240009010048085800120004810120004800220008242120004840090106840090104440090804440090804840048404a40048404840240408840240404840048085840048084404 (by decide +kernel)

def state254_58 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000,0xffffffffffffffff0000ffff0000ffffffffffffffffffff0000000000000000,input 4,input 7,input 1,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_58 : Impossible true (goalAt 254) 5 state254_58.toFinset :=
  node_ok cuts254 [] 0x26040901024060901006808120204828120212000480012021001c048401a10048601210048409010209081210048001200048088280128204808120284808098002400090082400240009000240401202048085202120601202208088202209084808090002c00090202400090009010112002400090003400090402400090004400091002400 (by decide +kernel)

def state254_59 : List Sig := [0xfff0fff0fff0fff0f0f0fff0f0f0fff0fff0fff0fff0fff0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffff0000ffffffffffffffffffffffffffff00000000,input 4,input 7,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_59 : Impossible true (goalAt 254) 4 state254_59.toFinset :=
  node_ok cuts254 [] 0x4840901020888121004800120004808828009810240409018240404840161004850121024000900024040120204808320209050120220808820220888240425040901024050901005808120204818120209000240009011001c (by decide +kernel)

def state254_60 : List Sig := [0xff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000000000000000,0xffffffffffffffffffffffff0000ffffffffffffffffffffffffffff00000000,input 4,input 7,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_60 : Impossible true (goalAt 254) 5 state254_60.toFinset :=
  node_ok cuts254 [⟨state254_59,exclude254_59⟩] 0x941024040901424040160204808120604808240009000240440070242012082000009080121005840121404840121024040822204840120004800120220a0026040901024060901012101208048220484090002400090100480812020c8082414048088202208088222090104820240404880240404820048084830048084800 (by decide +kernel)

def state254_61 : List Sig := [0xffffffffffffffffffffffff0000ffffffffffffffffffffffffffff00000000,0xffffffffffffffff0000ffff0000ffffffffffffffffffff0000000000000000,input 4,input 7,input 1,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_61 : Impossible true (goalAt 254) 6 state254_61.toFinset :=
  node_ok cuts254 [⟨state254_58,exclude254_58⟩,⟨state254_60,exclude254_60⟩] 0x9810240409018240401a0204808120a048084820120804828800042c0409010240c0901024200b080242809080941024040901424040160204808120604808242011080244009080240009000240480000121006840121804840121005840121404840121024040824204840120004800120220a001210120a0482a0484026040901024060901090002400090100480812021488848380480812020c8082414048088222240408242240404404090109010240c02404 (by decide +kernel)

def state254_62 : List Sig := [0xffff0000000000000000000000000000ffffffff00000000,0xffffffffffffffff0000ffff0000ffffffffffffffffffff0000000000000000,input 4,input 7,input 1,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_62 : Impossible true (goalAt 254) 6 state254_62.toFinset :=
  node_ok cuts254 [] 0x9810240409018240401a0204808120a0480848001200048081101024200b080242809080941024040901424040160204808120604808440011000440412020121006840121804840121005840121404840121024040824204840120004800120220a0046041101044061101090002400090100480812021480844140480882022080882421101024040b010240c090102400090002404111002404098102406090102404240409030090103202048082414048084828 (by decide +kernel)

def state254_63 : List Sig := [0xffffffffffffffff0000ffff0000ffffffffffffffffffff0000000000000000,input 4,input 7,input 1,input 2,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_63 : Impossible true (goalAt 254) 7 state254_63.toFinset :=
  node_ok cuts254 [⟨state254_52,exclude254_52⟩,⟨state254_55,exclude254_55⟩,⟨state254_56,exclude254_56⟩,⟨state254_57,exclude254_57⟩,⟨state254_61,exclude254_61⟩,⟨state254_62,exclude254_62⟩] 0x2c0c024040901090104001c90102c0c10007240c090100901024041a0a024040901044048001444041a0a20004120a044040901024040b03048400b01024041a18024040b0306860090302404121002404260604840260409010222009010260608880240609010121009010068284840068081202161401202068285850048281202121001202120220003120004404121004800120204840120204404400a84404090104440090020002090802400090102420090120001111004440400a824200908048400b0a02c20800002c28090a048400908024202505024202504090102120090102505084802405090100908090100581824200580812020d0c012020581834300481812020908012021101024201100048081110044001101044401101048080908048080981812100981024040c8c02404098183230090182404048402404129081210048404840068601a10129081a1804860484004840121009888121004840242005850161009888161404850242004840121020908121004840901020a00901020908828020908901004840121004808828004800d08004840120004808121004808d08020a0082801181812101181044041494044041181852501101844040484044040d05012020480824040c88832020d050322209050240404808120224040120224000824234200900024040d080240408242048081202150501202048084404149085202150505242110504404048081202209084404208089010400148202209090005209089010110104404 (by decide +kernel)

def state254_64 : List Sig := [0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000,input 4,input 7,input 1,input 2,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_64 : Impossible true (goalAt 254) 8 state254_64.toFinset :=
  node_ok cuts254 [⟨state254_48,exclude254_48⟩,⟨state254_63,exclude254_63⟩] 0xd05011010440424041001f24040d0504001c905024040440411010682809010240411011001f1101068284007c482811010240409010b03009010240424041002924040b0304001c9030240402404090104808222004800110104840120004808121004808110108880110102c0c121002c04090106860090102c0c1a180240c090104840090109818121009810240408880240409818222009018240404840240401a0a121001a02048085850048081a0a16140120a048084840048084404090804400120204440110004404111004404120202420120202404111002400400982420090002404090802404400a44440111010027090802420121002c280b08100260b0a024281210024200908094140908094102404084802404094142120090142404024202404016060908016020480834300480816060d0c012060480824200480846060484046041101052501101046061494044061101012101101026060484026040901032300901026060c8c02406090101210090104a42048401210121001a18068404a4206860121812100121004840262204840121009080161405840262205850121409080121004841000704840121024040828024041000820a00828024040121004840120220a001200400ac121004800120204840120240008828020a0054140480812021101052421480854141490844141101012020480834140480812020901032220c80834140c88824140901012020480900024000890002404100072404100020480812024007d00054001444044007c44044001d001f800044404400144404400a500034000c2404400a424044001d00298000024044000c24042220100012220048404009c484022201002722200484040004484021201000021200242040098242021201002621200242040000242020a01000b20a0012104001c121020a01000820a0012104002c1210400090025208090007400909080 (by decide +kernel)

def state254_65 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff0000cccc0000ffff0000cccc,input 1,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,input 2,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_65 : Impossible true (goalAt 254) 6 state254_65.toFinset :=
  node_ok cuts254 [] 0x44042088882621101044040d01068280d0104800120004808110108820220808828208883c040d010340c0d01044001100044041202024200b08024280908024202108024800908034000d0003404111009000048005200118181200048001a0004820120004800160004810120004800822020888120004800320009018120004808440414808120204808120a0680812020480812060580812020480890302408012020480824040c808120220a001200048081200 (by decide +kernel)

def state254_66 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc,input 1,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,input 2,input 3,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_66 : Impossible true (goalAt 254) 7 state254_66.toFinset :=
  node_ok cuts254 [⟨state254_65,exclude254_65⟩] 0x44042088882621101044040981868281101044041181846061101012021480844140480812022408090300480812020c80812220480a0000048081202400b84800120004808110101a0204808120a048088820220808828208882e0609818260e098184840129084a421210044001100044041202016020480812060480824200b0802428090802420210802480090802602098082606111004440090802420111008202400b424041181844041181844040480832200480882800c8c03a300c8e03230098802420090882420208808220208888828098183230090181210 (by decide +kernel)

def state254_67 : List Sig := [0x3333333333333333333333333333333333333333000000003333333300000000,input 1,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,input 2,input 3,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_67 : Impossible true (goalAt 254) 7 state254_67.toFinset :=
  node_ok cuts254 [] 0x1101082222098844041101026061a0a04404048085202110501202048089020240c01202048083202048881202120004800120204404068081202048281202220808820220a082220b8182606098382606110004400110104808058081202048181202090802c20090a02420090808420092002420098082602098184440208084604110104406110101200048001202242001210068401218048401210058401214048401210220a082220484026040981812101a0a044041a0a044042420012022420012021a18048401a1804840090802622090802622220a08222220a08222090103230 (by decide +kernel)

def state254_68 : List Sig := [0x3333333333333333333333333333333333333333333300003333333333330000,input 4,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,input 2,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_68 : Impossible true (goalAt 254) 6 state254_68.toFinset :=
  node_ok cuts254 [] 0x4404208888262110104404098106828098104800120004808110108820220808828208882e0409810260c098101a000480012080480044001100044041202024200b0802428090802420210802480090802600098002604111001600048001204048008200048005200150501200048009020240c012000480032000905012000484044041484044040484012180684012100484012140584012100484082222088012100901024040c840260420a001200048401200 (by decide +kernel)

def state254_69 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000,input 4,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,input 1,input 2,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_69 : Impossible true (goalAt 254) 7 state254_69.toFinset :=
  node_ok cuts254 [⟨state254_68,exclude254_68⟩] 0x44042088882621101044040d0506828110104404150505414110104800120004808110108820220808828208883c140d050341c0d0503a220c888322a0c88848401614058501210044001100044041202024200b08024280908024202108024800908034100d04034141110024200d08024300908044400908024201110046041101044061101012100684012180484012100584012140484012102088082220484012100c840123004840322004840121020a020000048401210400b09010400c02404150504404150504404240809020240c032220d0503222090501202 (by decide +kernel)

def state254_70 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff000000000000ffff00000000,input 4,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,input 1,input 2,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_70 : Impossible true (goalAt 254) 7 state254_70.toFinset :=
  node_ok cuts254 [] 0x1101082222098844041101034141a0a04404120004800120204404220808820220a082220f05034140d0703414068081202048281202110004400110104808090802c20090a024200908084200920024200d04034100d0504440058081202048181202118104404110184404048401a10048601210048401610048501210048408220208881210048403210048c012100480012000480882802404012021480844140480812022088890300480832020d05012021a0a044041a0a044041a18048401a180484009080343009080343020a00121020a001210208889030208889030090103222 (by decide +kernel)

def state254_71 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_71 : Impossible true (goalAt 254) 6 state254_71.toFinset :=
  node_ok cuts254 [] 0x12020c8082414048081202241809070048085800120004810120001602048081206048082400090002404111002420211806480090804c0012000480412000120004800120220a001210058401214048402604090102406090101210209808262048404a00120004802120006800120004820120008242220804840048085840048084440090804440090804840048404a400484048400901068400901048401a2008860121004404 (by decide +kernel)

def state254_72 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 1,input 2,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_72 : Impossible true (goalAt 254) 7 state254_72.toFinset :=
  node_ok cuts254 [⟨state254_71,exclude254_71⟩] 0xd05012020480824040c88832020d0503222090502404048081202241c01202048088262242009060241c09080241c082620480812021505012020480844041490852021505052421105044040480812020682848400680812021614012020682858500482812021210012020b03048400b01024041a18024040b0306860090302404121002404400cc4840121008262222008860400cc88801a2008262121004840120220000120004404121004800120204840120204404400cc44040581824200580812020d0c01202058183430048181202090801202400cc24200908048400b0a02c20400c82c28090a04840090802420090104440090010032090802400090102420090110032111004440400c82420090808262212008460400c8848019200826209080242011010242011000480811100440011010444011010480809080480804808828004800908004840120004808121004808908020a008280129081210048404840068601a10129081a180486048400484012100988812100484024200585016100988816140485024200484012100981812100981024040c8c0240409818323009018240404840240420988121004840907020a0082602098882802098890700484012101181812101181044041494044041181852501101844040484044041a0a024040901044044006444041a0a10018120a04404090102404400650031209090018400608222 (by decide +kernel)

def state254_73 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,input 1,input 2,input 3,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_73 : Impossible true (goalAt 254) 8 state254_73.toFinset :=
  node_ok cuts254 [⟨state254_66,exclude254_66⟩,⟨state254_67,exclude254_67⟩,⟨state254_69,exclude254_69⟩,⟨state254_70,exclude254_70⟩,⟨state254_72,exclude254_72⟩] 0x40060c26211010440440060822240060822240060c2628001082624006082221101044044006100181101044044006024041a0a024044006100181a0a048284006024041101024044006054140480812024006044041490852024006054141490844144006044040480812024001c9030048081202400b88222242009020400209030242009030400b882220480812028000c3414048081202400b824040c88832028000834140c8882414400b82404048081202400604808222004800400604404121004800400604808121004808400604404222004404400bc1a0a121001a02400bc1202161401202400bc1a0a16140120a400bc1202121001202400bc8828121008820400bc8222222008820400bc8828222008828400bc8222121008222400bc2c0c121002c04400bc24041a1802404400bc2c0c1a180240c400bc24041210024044006044040908044004006048081110044004006044041110044044006048080908048084000016060908016024000012020d0c012024000016060d0c01206400001202090801202400bd002f090802420400bc48400b0a02c20400bd00000b0a02428400bc4840090802420400010000090802420400008222212008420400010000212002480400008222090802420400002404111002400400010000090802400400002404090802404400010000111004440400604606048404604400604404149404404400604606149404406400604404048404404400b8120220a001200400b09080048401200400201202048401202400b8908020a008280400bc4a42048401210400bc4840068601a10400bc4a42068601218400bc48400484012104000026220484012104000024200585016104000026220585012144000024200484012104001c8222048401210400b0882820a00822040020822220a008222400b08828048401210800042606048402604400b024040c8c024048000026060c8c02406400b024040484024044000d00194000c8202 (by decide +kernel)

def state254_74 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00cc00cc00cc00cc,input 1,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,input 2,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_74 : Impossible true (goalAt 254) 6 state254_74.toFinset :=
  node_ok cuts254 [] 0x24042090882620901068001200048201200012020c8082414048081202241009050048085800120004810120002400090002404111001602048081206048082420211004480090804c001200048041200088000b8102404098182404068001a00048088280068401e10068501a10068408240209081a1012800480011018480009818240409818240404808120a048081a02098882420098882420121004880221004840110104800128084800048401210129001a10 (by decide +kernel)

def state254_75 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000cccc0000cccc,input 1,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,input 2,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_75 : Impossible true (goalAt 254) 6 state254_75.toFinset :=
  node_ok cuts254 [] 0x2404209088262090102404150105828090102c0409010240c0901048402210048801210058001600058081501024000900024041110024200b0802428090802420211004480090805400150005404160209000048003200098181200048001a000482012000480016000481012000480082402090812000480052001101812000480824040c808120204808120a06808120204808120605808120204808905024100120204808440414808120220a001200048081200 (by decide +kernel)

def state254_76 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc,input 1,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,input 2,input 3,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_76 : Impossible true (goalAt 254) 7 state254_76.toFinset :=
  node_ok cuts254 [⟨state254_74,exclude254_74⟩,⟨state254_75,exclude254_75⟩] 0x2404209088262090102404118184a2a0901024040981826060901012020c80824140480812022410090500480812021480812420480a0001048081202400d82c0409010240c090101a0204808120a048084840221004880121004a02128084a0a1181a0000121004840400d424000900024041110016020480812060480824200b0802428090802420211004480090804602118084606128282420098882622090808202400484404098182404098182404048085240048088280129004840121084840098882420098882420209008240209085250118185250110181210 (by decide +kernel)

def state254_77 : List Sig := [0xffffffff33333333ffffffff33333333ffffffff33333333ffffffff00000000,input 1,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,input 2,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_77 : Impossible true (goalAt 254) 6 state254_77.toFinset :=
  node_ok cuts254 [] 0x12022410090500480812021480848380480812020c8082414048081a0204808120a048084840221004880121004a02128084a0a118182c0409010240c0901016020480812060480824200b0802428090802420211004480090804602118084606128282400090002404119088202048001200048089080048401a1004860121004840161004850121004840a240209081210118104604118181210098102404090182404090108242241402404090104404120a02404 (by decide +kernel)

def state254_78 : List Sig := [0x3333333333333333333333333333333333333333333333330000000000000000,input 1,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,input 2,input 3,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_78 : Impossible true (goalAt 254) 7 state254_78.toFinset :=
  node_ok cuts254 [⟨state254_77,exclude254_77⟩] 0x90108242209882404090104606128a824040480832020905012020480890402414012020480852020490812020b0102404090302404068081202048281202121008840122004840128084a02128284606090002400090104440058081202048181202090802c20090a02420090808440112002420118084602118184a0a208082604090102406090101200048001202242001210068401218048401210058401214048401210241408242048404604118181210400c42404800002404242001202242001202121004a42121004a42111002420111002420241408242241408242110105250 (by decide +kernel)

def state254_79 : List Sig := [0xf0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0f0f0f0f0f0f0f0,input 2,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_79 : Impossible true (goalAt 254) 6 state254_79.toFinset :=
  node_ok cuts254 [] 0x901082422098824041a0004800120804800048083202090501202048089040241401202160004800120404800098102404090182404048001200048088280048408240209081210128004800120084800048401614058501210048401614058501210220002404191002404111001606048081606048084440211004480111004404120004404120002420090104860090104840058181202058181202121004880221004840110104800110104800 (by decide +kernel)

def state254_80 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf000f000f000f000f000f000f000f000f000f000f000f0000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_80 : Impossible true (goalAt 254) 5 state254_80.toFinset :=
  node_ok cuts254 [] 0x68001200048201200024000900024042090812020c808241404808580012000481012000120205808120604808260409010240609010120004800120220a004a00120004802120001210058401214048404840090106840090104840048085840048084840048404a40048408206121002420111002420110004400110104800 (by decide +kernel)

def state254_81 : List Sig := [0xfffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f000000000,0xf000f000f000f000f000f000f000f000f000f000f000f0000000000000000,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_81 : Impossible true (goalAt 254) 4 state254_81.toFinset :=
  node_ok cuts254 [] 0x480890402414012020d000240009040240004800120004808828004840824020908121009800240009008240021000244004808344004808244004840264004840244009200844009101003a (by decide +kernel)

def state254_82 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f000000000f0f0f0f000000000,0xf000f000f000f000f000f000f000f000f000f000f000f0000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_82 : Impossible true (goalAt 254) 4 state254_82.toFinset :=
  node_ok cuts254 [] 0x540011000441011000340009000241009000120004800120220a004600110004402110002600090002402090004440048085440048084440048404640048402480111002400191002400090004400209082400 (by decide +kernel)

def state254_83 : List Sig := [0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000,0xf000f000f000f000f000f000f000f000f000f000f000f0000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_83 : Impossible true (goalAt 254) 5 state254_83.toFinset :=
  node_ok cuts254 [⟨state254_81,exclude254_81⟩,⟨state254_82,exclude254_82⟩] 0x120224100905004808540011000441011000120004800120220a001210209008242048404600110004402110002600090002402090008400111001202151001202111001210119001210111004480211004440400e86440090003400090402400090008242800042400090004400800002400 (by decide +kernel)

def state254_84 : List Sig := [0xf000f000f000f000f000f000f000f000f000f000f000f0000000000000000,input 2,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_84 : Impossible true (goalAt 254) 6 state254_84.toFinset :=
  node_ok cuts254 [⟨state254_80,exclude254_80⟩,⟨state254_83,exclude254_83⟩] 0x24042090882620901068001200048201200012020c808241404808120224100905004808580012000481012000260409010240609010120004800120220a001210209008242048404a001200048021200012100584012140484088000900024000901200010580812020481812020908082428000024201100044001101048001210024041a1002404121001202161001202121001210129001210121004880221004840400e44440 (by decide +kernel)

def state254_85 : List Sig := [0xf0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000000000,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_85 : Impossible true (goalAt 254) 5 state254_85.toFinset :=
  node_ok cuts254 [] 0x48089040241401202160004800120404800048001200048088280048408240209081210128004800120084800098002400090082400220004840048085840048084840048404a4004840484012200884012101003a111002400111002400090003400090402400090008440112002400090004800111002400 (by decide +kernel)

def state254_86 : List Sig := [0xffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_86 : Impossible true (goalAt 254) 6 state254_86.toFinset :=
  node_ok cuts254 [⟨state254_85,exclude254_85⟩] 0x12022410090500480858001200048101200012020c8082414048081602048081206048082420211004480090804c0012000480412000240009000240480000120004800120220a001210058401214048401210209008242048404a001200048021200026040901024060901088001a10012021e10012021110024201110024201a10012101a90012101a10068802a1006840400cc484009011003b2090824041a0004800120804800 (by decide +kernel)

def state254_87 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 2,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_87 : Impossible true (goalAt 254) 6 state254_87.toFinset :=
  node_ok cuts254 [⟨state254_80,exclude254_80⟩] 0x1a00048001208048002890824040901082420480832020905012021600048001204048000480816060581812020981024040901824040480012000480882801280048001200848000484016140585012100484016140585012101210024041a1002404121001202161001202121001210129001210110104840800004480121004840122008840121002404192002404112001606048081606048084c04120004c04120002420220004800130104800 (by decide +kernel)

def state254_88 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000,input 2,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_88 : Impossible true (goalAt 254) 6 state254_88.toFinset :=
  node_ok cuts254 [] 0x68001200048201200012020c808241404808580012000481012000260409010240609010120004800120220a004a00120004802120001210058401214048404840090106840090104840048085840048084840048404a40048404404111002420111002420121004880221004840090002400090104440058081202048181202130004800120104800209082404209882404241001202241401202209001210209081210220004480 (by decide +kernel)

def state254_89 : List Sig := [0xff00fff0fff0ff00ff00fff0fff0ff00ff00fff0fff0ff00000000f0f0f0f0,input 2,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_89 : Impossible true (goalAt 254) 5 state254_89.toFinset :=
  node_ok cuts254 [] 0x120224100905004808580012000481012000120004800120220a001210209008242048404a001200048021200026000900024020900088000900034000581824000900084401120024000900048001101024000901012020d0101202090102406098102404090104880221002404090104800110104800111002400090102400 (by decide +kernel)

def state254_90 : List Sig := [0xffffffffffffffffffffffffffffffff00000000f0f0f0f000000000f0f0f0f0,input 2,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_90 : Impossible true (goalAt 254) 5 state254_90.toFinset :=
  node_ok cuts254 [] 0x580012000481012000120209010340404808120004800120220a004a00120004802120002600090002402090002406090102604090104840048085840048084840048404a40048404404121002400191002400121002404221002404090003400058182400090004800130102400090004440090102400220004800130104800 (by decide +kernel)

def state254_91 : List Sig := [0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,input 2,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_91 : Impossible true (goalAt 254) 6 state254_91.toFinset :=
  node_ok cuts254 [⟨state254_89,exclude254_89⟩,⟨state254_90,exclude254_90⟩] 0x120224100905004808580012000481012000120004800120220a001210209008242048404a001200048021200026000900024020900088001210012021610012021210012101290012101210048802210048401101048400900064400900024000d0001606090002400291006480090002400120004c040900024040480834040480824040901826040901024042090a0001090102404120004c04120002404121020000090104440 (by decide +kernel)

def state254_92 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_92 : Impossible true (goalAt 254) 5 state254_92.toFinset :=
  node_ok cuts254 [] 0x48089040241401202160004800120404800048001200048088280048408240209081210128004800120084800098002400090082400220004840048085840048084840048404a4004840484012200884012101003a111002400111002400090003400090402400090008440112002400090004800111002400 (by decide +kernel)

def state254_93 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000,input 7,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_93 : Impossible true (goalAt 254) 6 state254_93.toFinset :=
  node_ok cuts254 [⟨state254_92,exclude254_92⟩] 0x12022410090500480812021208048300480812020c808241404808160204808120604808242021100448009080242012080444009080240009000240480000120004800120220a001210058401214048401210209008242048401210120804822048402604090102406090108820400ec4840048085840048084440090804440090804840048404a40048404840122008840121010033400ec4800 (by decide +kernel)

def state254_94 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,input 1,input 2,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_94 : Impossible true (goalAt 254) 7 state254_94.toFinset :=
  node_ok cuts254 [⟨state254_79,exclude254_79⟩,⟨state254_84,exclude254_84⟩,⟨state254_86,exclude254_86⟩,⟨state254_87,exclude254_87⟩,⟨state254_88,exclude254_88⟩,⟨state254_91,exclude254_91⟩,⟨state254_93,exclude254_93⟩,⟨state254_71,exclude254_71⟩] 0x289882404090108242400f082422898a00072098882420901024041a08024041a0004800400f048001a08200061208048000901048000d05012020480824040c88832020d050322209050240404808120224140120204808824224200904024140908024140824204808120216040120216000480014908480016040524212040480004808480009010444009002000509080240009010242009011003c1110044400581824200580812020d0c012020581834300481812020908012028001024200908082422120084408000c84801120082420908024201301024201300048001110048001301044401201048000908048000981812100981024040c8c0240409818323009018240404840240404808828004800908004840120004808121004808908020a00828009888121004840242005850161009888161404850242004840121020908121004840905020a008240209088280209089050048401210128081210128004800149404800128085250120084800048404800400e1003822001003c1210048400901068600901200021a1806840090104840090105242121004840048085850048085242161405840048084840048084440121004440090820001090804440800004440090804840090805250121004840048404a42048405250129084a40048404840048408242121004840400e08880122008242222008840400e04840121010035400dc4404 (by decide +kernel)

def state254_95 : List Sig := [0x3333333333333333333333333333333333333333333333333333000033330000,input 4,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,input 2,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_95 : Impossible true (goalAt 254) 6 state254_95.toFinset :=
  node_ok cuts254 [] 0x2404209088262090102404118104a28090102c0409010240c090104840221004880121004a00128004a08118101a000480012080480024000900024041110024200b08024280908024202110044800908046001180046041282016000480012040480082000480032000d05012000480090402414012000480052001105012000484024040c840240404840121806840121004840121405840121004840824220900121011010440414840460420a001200048401200 (by decide +kernel)

def state254_96 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff0000,input 4,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_96 : Impossible true (goalAt 254) 6 state254_96.toFinset :=
  node_ok cuts254 [] 0x2404209088262090106800120004820120002400090002404111002420211004480090804c00120004804120001e02068081a06068082604090102406090101210058401214048401210209008242048404a00120004802120001a00068001a0220a008800068083a020d0501a02068089040241401a021600048001105048000d05024040d05024040d0c024200d0c02420048401218048401a10121004880221004840110104800160404800048081202161001a02 (by decide +kernel)

def state254_97 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000,input 4,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,input 1,input 2,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_97 : Impossible true (goalAt 254) 7 state254_97.toFinset :=
  node_ok cuts254 [⟨state254_95,exclude254_95⟩,⟨state254_96,exclude254_96⟩] 0x24042090882620901024041505058380901024040d0503414090102c0409010240c090104840221004880121005810160405818150504840161004850121020001121004840400d424000900024041110024200b08024280908024202110044800908054101504054141606024200d0c034300908024200d0c0343009080260409010240609010121006840121804840121005840121404840121020900824204840121014840125004840524004840121020a020000048401210400d090104008044040d05024040d0502404241009040241405242150505242110501202 (by decide +kernel)

def state254_98 : List Sig := [0xffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff00000000,input 4,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,input 1,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_98 : Impossible true (goalAt 254) 6 state254_98.toFinset :=
  node_ok cuts254 [] 0x4840221004880121005810160405818150501a0204808120a048082c0409010240c0901024200b080242809080242021100448009080541015040541416060160204808120604808240009000240415140121006840121804840121005840121404840121020900824204840121014840482a04840120004800120220a00260409010240609010901004808b040241401202048085202150501202048083202090501202090109050209082404090104404120a02404 (by decide +kernel)

def state254_99 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000,input 4,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,input 1,input 2,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_99 : Impossible true (goalAt 254) 7 state254_99.toFinset :=
  node_ok cuts254 [⟨state254_98,exclude254_98⟩] 0x90108242209882404090105414160e024040b0102404090302404121008840122004840160405810160605414068081202048281202090002400090104440090802c20090a02420090808440112002420150405410150505818058081202048181202098102404090182404048401a100486012100484016100485012100484082402090812100484052100494012100480012000480882802404012020c8082414048081202209089050048085202150501202400c4240480000240412100585012100585011100242011100242020a00121020a001210209089050209089050110105242 (by decide +kernel)

def state254_100 : List Sig := [0xf000f000f000f000f000f000f000f000f000f000f000f0f0f0f0f00000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_100 : Impossible true (goalAt 254) 4 state254_100.toFinset :=
  node_ok cuts254 [] 0x48089020240c012020d000240009040240004800120004808828004840822020888121009800240009008240021000242004808342004808242004840262004840242009200842009081003a (by decide +kernel)

def state254_101 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_101 : Impossible true (goalAt 254) 5 state254_101.toFinset :=
  node_ok cuts254 [⟨state254_100,exclude254_100⟩] 0x120224080903004808340009000241009000120004800120220a0012102088082220484026000900024020900012101208048220484084000908012020d0801202090801210098801210090802480210802420400e82420800004820090804820048084830048084820220804880120804c00 (by decide +kernel)

def state254_102 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,input 1,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_102 : Impossible true (goalAt 254) 6 state254_102.toFinset :=
  node_ok cuts254 [⟨state254_101,exclude254_101⟩] 0x48089040241401202048085222120e012020d0002400090402400068081202048281202121008840122004840120804820120a200000b0002400090202400048001200048088280048401a10048601210048408240209081210048404828120a8121009800240009008240020889003e110002420048083420048082420090a02c20090802420048402620048402420112008440090802420091004420090810032 (by decide +kernel)

def state254_103 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_103 : Impossible true (goalAt 254) 5 state254_103.toFinset :=
  node_ok cuts254 [] 0x120224100905004808580012000481012000120004800120220a001210209008242048404a00120004802120002e000b0002c020b00088000c80812020488812020c8401210048c01210121004880221004840400e84800120804800090002400090802c000b0003c000b0402c000b0008440112002c000b0004800091002c00 (by decide +kernel)

def state254_104 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_104 : Impossible true (goalAt 254) 6 state254_104.toFinset :=
  node_ok cuts254 [⟨state254_103,exclude254_103⟩] 0x48089040241401202048085222120e01202048083a020b05012020580812020481812020908084401120024200908044200910024200b0002c000b0120000048001200048088280048401610048501210048408240209081210048404828120a812100b8102c040b0182c0420889003f120003222048083222048082420090a024200b0803230048403230048404840122008840121010033120a04820120802404 (by decide +kernel)

def state254_105 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,input 1,input 2,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_105 : Impossible true (goalAt 254) 7 state254_105.toFinset :=
  node_ok cuts254 [⟨state254_102,exclude254_102⟩,⟨state254_104,exclude254_104⟩,⟨state254_93,exclude254_93⟩] 0x9050048081202209089080241009050242009050209081202048085838048081202120a05242148885838149084838120a012020480834140480812020901032220c80834140c8882414090101202048081a0a121001a02048085850048081a0a16140120a048084840048090033121004840209088880221010033222004880209084840121004828800084820400cc4840120804828121004828400cd0033400cc2c0c800042c04090104840090102c0c12100240c0901100330901016060908016020480834300480816060d0c01206048082420048090033090802420121002c280b08100320b0a02428121002420090810032090802420209088480211010032212004480209082420090810032090802420120a04440110810032111002440120a02420090802404800002400400c82420090002404090802404400c90032400c8120220a00120024200121004800120204840120224200828020a004a42048401210121001a18068404a4206860121812100121004840262204840121009080161405840262205850121409080121004840824204840121024140828020900824220a008242241401210048404a2a048401210120a05250120a04a2a14940482a120a012100484026060484026040901032300901026060c8c0240609010121009011001840060822240065003d400650019400c44404 (by decide +kernel)

def state254_106 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,input 1,input 2,input 3,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_106 : Impossible true (goalAt 254) 8 state254_106.toFinset :=
  node_ok cuts254 [⟨state254_76,exclude254_76⟩,⟨state254_78,exclude254_78⟩,⟨state254_94,exclude254_94⟩,⟨state254_97,exclude254_97⟩,⟨state254_99,exclude254_99⟩,⟨state254_105,exclude254_105⟩,⟨state254_72,exclude254_72⟩] 0x400c4a262090102404400c48242400c48242400c4a262800188262400c48242090102404400c46828090102404400c44404400c44404400c46828800144828400c44404090102404400c43414048081202400c424040c8883202400c434140c8882414400c424040480812024001c9050048081202400d88242242009040400209050242009050400d88242048081202800105414048081202400d844041490852028000c5414149084414400d84404048081202400c42c0c121002c04400c424041a1802404400c42c0c1a180240c400c42404121002404400d41a0a121001a02400d41202161401202400d41a0a16140120a400d41202121001202400d50035121004840400d48242222008840400d50035222004880400d48242121004840400d44808800084800400d44404121004800400d44808121004808400d44404400d44404400c42404111002400400c50032090802400400c42404090802404400c50031111004440400c81606090801602400c812020d0c01202400c816060d0c01206400c81202090801202400d50035090802420400d448400b0a02c20400d500320b0a02428400d44840090802420400c90032090802420400c88242212008440400c90032212004480400c88242090802420400c84404090804400400c84808111004400400c84404111004404400c84808090804808400c42606048402604400c424040c8c02404400c426060c8c02406400c42404048402404400d8120220a001200400d09080048401200400201202048401202400d8908020a008280400d44a42048401210400d44840068601a10400d44a42068601218400d44840048401210400c82622048401210400c82420058501610400c82622058501214400c824200484012104001c8242048401210400d0905020a00824040020824220a008242400d09050048401210800044606048404604400d04404149404404800004606149404406400d04404048404404400150005400148202 (by decide +kernel)

def state254_107 : List Sig := roots 254
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude254_107 : Impossible true (goalAt 254) 9 state254_107.toFinset :=
  node_ok cuts254 [⟨state254_0,exclude254_0⟩,⟨state254_13,exclude254_13⟩,⟨state254_32,exclude254_32⟩,⟨state254_45,exclude254_45⟩,⟨state254_64,exclude254_64⟩,⟨state254_73,exclude254_73⟩,⟨state254_106,exclude254_106⟩] 0x40014c24211010c20240014820240014820240014c2428001882424001482021101082024000ca22209010a2024000c82024000c82024000ca2228001482224000c82020901082024001468280901024044001444044001444044001468284001448284001444040901024048001090100480890004000882022420090008000c90102420090104000882020480812024001454140480812024001444041490852024001454141490844144001444040480812024000c34140480812024000c24040c88832024000c34140c88824144000c24040480812024000488081210088004000482022220088004000488082220088084000482021210082024001448082220048004001444041210048004001448081210048084001444042220044044000c2c0c121002c044000c24041a18024044000c2c0c1a180240c4000c2404121002404400041a0a121001a02400041202161401202400041a0a16140120a4000412021210012024000084040908084004000082022120084004000084042120084044000082020908082024001444040908044004001448081110044004001444041110044044001448080908048084000c24041110024004000d00000908024004000c24040908024044000d00031110044404000016060908016024000012020d0c012024000016060d0c012064000012020908012024000500010908024204000448400b0a02c204000500000b0a024284000448400908024208000882020484082004002c840420a00820080004820220a0082024002c84040484084044001446060484046044001444041494044044001446061494044064001444040484044044000c26060484026044000c24040c8c024044000c26060c8c024064000c240404840240440008120220a0012004002c908004840120080000120204840120240008908020a008280400044a42048401210400044840068601a10400044a42068601218400044840048401210400002622048401210400002420058501610400002622058501214400002420048401210 (by decide +kernel)

theorem lower254 : Claim 254 10 :=
  fromSearch 304178496 (by decide +kernel) exclude254_107

open PEqualNP.CircuitLowerBounds

def graph : Sig := goalAt 255
theorem graph_proper : proper graph := by unfold proper; decide +kernel

def edgeList : List Nat := [0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7]
def target (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edgeList.length / 2,
    (List.ofFn x).getD (edgeList.getD (2*i) 0) false = true ∧
    (List.ofFn x).getD (edgeList.getD (2*i+1) 0) false = true)

def smallCircuit : Circuit := ⟨[⟨.or,[6,7]⟩,
  ⟨.or,[1,4]⟩,
  ⟨.or,[0,2]⟩,
  ⟨.or,[5,8]⟩,
  ⟨.or,[0,8]⟩,
  ⟨.and,[1,4]⟩,
  ⟨.and,[10,11]⟩,
  ⟨.and,[3,12]⟩,
  ⟨.and,[9,7]⟩,
  ⟨.or,[13,14]⟩,
  ⟨.or,[17,15]⟩,
  ⟨.or,[18,16]⟩],19⟩

theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel

theorem witnessSize : smallCircuit.gates.length = 12 := rfl

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

def eightInputs : List Sig := roots 255
def sampleEight (r : Row) (i : Fin 8) : Bool := bit r (eightInputs.getD i.val zero)
theorem eightList : List.ofFn (fun i : Fin 8 => eightInputs.getD i.val zero) = eightInputs := rfl
theorem eightSampled (r : Row) : List.ofFn (sampleEight r) = eightInputs.map (bit r) := by
  rw [←eightList,List.map_ofFn]
  rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem eightTable : ∀ r : Row, bit r graph = target (sampleEight r) := by decide +kernel

theorem eightEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates eightInputs).getD i zero) =
      (C.wires (List.ofFn (sampleEight r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),eightSampled]
  rfl

def lowRow (i : Fin 8) : Row := Fin.ofNat 256 (1 <<< ([3, 4, 5, 0, 1, 0, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 256 ((1 <<< i.val) ||| (1 <<< ([3, 4, 5, 0, 1, 0, 0, 0] : List Nat).getD i.val 0))

set_option maxHeartbeats 1000000 in
theorem allEightRequired :
    (∀ i : Fin 8, bit (lowRow i) graph ≠ bit (highRow i) graph) ∧
    (∀ i j : Fin 8, i ≠ j →
      bit (lowRow i) (eightInputs.getD j.val zero) =
      bit (highRow i) (eightInputs.getD j.val zero)) := by decide +kernel

theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k eightInputs.toFinset := by
  have goalEq : (execute C.gates eightInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (eightEval C legal C.output r).trans ((computes (sampleEight r)).trans (eightTable r).symm)
  have out := get_rep (u:=true) (execute C.gates eightInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates eightInputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : eightInputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ eightInputs) : ∃ i : Fin 8, eightInputs.getD i.val zero = a := by
    rw [←eightList] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = eightInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run eightInputs (eightInputs.getD i.val zero) sub (lowRow i) (highRow i)
        (allEightRequired.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply allEightRequired.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨k,hk,eq ▸ run⟩

theorem replaceShort
    (lower : Impossible true graph 10 eightInputs.toFinset) (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 8 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 8 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 12 ≤ gates.length
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

theorem lowerGraph : Impossible true graph 10 eightInputs.toFinset :=
  (ruleFor 255 lower254 none (by decide +kernel)).property 10 eightInputs
    (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_14780

open PEqualNP.Outside.L_meta_14780 in
theorem PEqualNP.Outside.L_meta_14780 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort lowerGraph gates o fit correct
