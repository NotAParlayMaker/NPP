import PEqualNP.Defs

/-
L-meta-2541. The sign on the distinguished input can be given to the circuit
for free. This proof establishes the lower bound even with unrestricted use
of that input.

The circuit normalization, 512-row restriction and separation lemmas,
packed verifier, and unsigned induced-subgraph certificates below are from
the checked proof of L-meta-1667 by @loris-olsem, PR #4332, commit
78e692de1384bfc0954186b781f1c251f6a1090f. The original file has Git blob
fc4ba1121de31fdfa08b135ece199d4d4a9852e8. The signed forests and their
geometric reductions are new. The three smaller forests prove all polarity
orbits on the seven-vertex theta. Removing an essential leaf then supplies
the eight-vertex cofactor bounds for the nine-vertex forest.
-/
namespace PEqualNP.Outside.L_meta_2541.SignedProof
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

inductive Live (target : Sig) : Nat → Nat → Finset Sig → Prop
  | stop (hp : proper target) : Live target 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) :
      Live target (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) :
      Live target (k+1) t (insert a (insert b U))

private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩


def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

private lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live target k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live target k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
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
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live target k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,u,T,by simp; omega,hu,hT⟩

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]

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
      change bit i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
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

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop := v ∈ pool ∨ Constant v

def supply {R} (pool xs : List (Wire R)) := ∀ a ∈ xs, Available pool a

inductive Reach {R} (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | start : Reach roots 0 roots
  | one {p bank a} : Reach roots p bank → Available bank a →
      Reach roots (p+1) (inv a :: bank)
  | two {p bank a b} (op : Bool) : Reach roots p bank → Available bank a →
      Available bank b → Reach roots (p+1) (combine op a b :: bank)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

inductive Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop
  | stop : Run goal 0 [goal]
  | perm {s xs zs} : xs.Perm zs → Run goal s xs → Run goal s zs
  | one {s a rest} (save : Bool) : Run goal s (inv a :: kept save a rest) →
      Run goal (s+1) (a::rest)
  | two {s a b rest} (op ka kb : Bool) :
      Run goal s (combine op a b :: kept ka a (kept kb b rest)) →
      Run goal (s+1) (a::b::rest)

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available bank a) (hb : Available bank b) :
    Available bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩

theorem available_cons {R} {bank v} (w : Wire R) (h : Available bank v) :
    Available (w::bank) v := by
  exact h.elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr

theorem extend_one {R} (roots : List (Wire R)) {p bank a} (hp : Reach roots p bank)
    (ha : Available bank a) :
    ∃ q next, Reach roots q next ∧ Available next (inv a) ∧
        (∀ v, Available bank v → Available next v) ∧ q+cost a ≤ p+1+cost (inv a) := by
  classical
  by_cases c : Constant a
  · exact ⟨p,bank,hp,Or.inr (inv_constant c),fun _ h => h,by simp [cost,c,inv_constant c]⟩
  · exact ⟨p+1,_,Reach.one hp ha,Or.inl (by simp),fun _ h => available_cons _ h,by simp [cost,c]⟩

theorem extend_two {R} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q next ∧ Available next (combine op a b) ∧
        (∀ v, Available bank v → Available next v) ∧
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

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach roots p bank) (hs : supply bank ws) :
    ∃ q next, Reach roots q next ∧ Available next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @one s a rest save _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_one roots hp (hs a (by simp))
    have ht : supply T (inv a :: kept save a rest) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · exact inc v (hs v (List.mem_cons.mpr (mem_kept hh)))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a rest save
    rw [mass_cons] at hl ⊢
    exact ⟨q,W,hW,hv,by omega⟩
  | @two s a b rest op ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_two roots op hp (hs a (by simp)) (hs b (by simp))
    have ht : supply T (combine op a b :: kept ka a (kept kb b rest)) := by
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

theorem restrict_run {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws) :
    Run (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | one save _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    exact Run.one save ih
  | two op ka kb _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    cases op
    · exact Run.two false ka kb ih
    · exact Run.two true ka kb ih

theorem projected_bound {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach roots p bank) (hs : supply bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach roots q bs → Available bs (restrictRows rows goal) → L ≤ q) :
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

theorem obs_bin (d : Bool) (a b : Sig) :
    observe (bin d a b) = combine d (observe a) (observe b) := by
  funext r
  cases d <;> exact bit_bin _ _ _ _

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {T : Sig} {k u S} (h : Live T k u S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run (observe T) k (v.map observe) := by
  classical
  induction h generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @unary k u U a ha fresh _ ih =>
    let rest := (U.erase a).toList
    let save := decide (a ∈ U)
    let tail := kept save a rest
    have er : rest.toFinset = U.erase a := by simp [rest]
    have hm : a ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have ht : tail.toFinset = U := by
      rw [show tail=kept save a rest by rfl,kept_fin,er]
      by_cases hh : a ∈ U <;> simp [save,hh]
    have nd := kept_nd save a rest hr hm
    have hf : neg a ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz))
    have progress := ih (neg a::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    rw [List.map_cons,map_kept,obs_neg] at progress
    have perm : (a::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨hm,hr⟩) hv
      simp [er,eqv]
    exact Run.perm (perm.map _) (Run.one save progress)
  | @binary k u U a b d ha hb hab fresh _ ih =>
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
    change Run _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d ka kb progress)


theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_bin (d : Bool) (f g : Wire Row) :
    table (combine d f g) = bin d (table f) (table g) := by
  rw [←table_observe (bin d (table f) (table g)),obs_bin,observe_table,observe_table]

theorem available_rep {bank : List (Wire Row)} {a} (h : Available bank a) :
    represented (bank.map table) (table a) := by
  rcases h with hm | ⟨b,rfl⟩
  · exact Or.inl (List.mem_map_of_mem hm)
  · apply Or.inr
    cases b
    · have z : table (fun _ => false) = zero := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_zero ⟨j,hj⟩).symm
      exact fun hp => hp.1 z
    · have z : table (fun _ => true) = one := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_one ⟨j,hj⟩).symm
      exact fun hp => hp.2 z

theorem inv_rep {w a} (ha : represented w a) :
    represented w (neg a) ∨ witness w (neg a) := by
  rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr fun h => h.2 neg_laws.1)
  · exact Or.inl (Or.inr fun h => h.1 neg_laws.2)
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)

theorem pull_cons {w : List Sig} {z : Sig} {T k t S} (h : Live T k t S)
    (hz : represented w z ∨ witness w z) (hs : ∀ a ∈ S, a ∈ z::w) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live T k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  apply pull_gate h hz
  intro a hm
  simpa [or_comm] using hs a hm

theorem reach_live_sub {roots : List (Wire Row)} {p bank}
    (h : Reach roots p bank) {T k t S} (run : Live T k t S)
    (sub : ∀ a ∈ S, a ∈ bank.map table) :
    ∃ l v U, l ≤ p+k ∧ Live T l v U ∧ ∀ a ∈ U, a ∈ roots.map table := by
  induction h generalizing k t S with
  | start => exact ⟨k,t,S,by omega,run,sub⟩
  | @one p bank a h ha ih =>
    rw [List.map_cons,table_inv] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (inv_rep (available_rep ha)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,table_bin] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (bin_rep d (available_rep ha) (available_rep hb)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩

theorem reach_live {roots : List Sig} {p bank T} (hp : proper T)
    (h : Reach (roots.map observe) p bank) (hit : Available bank (observe T)) :
    ∃ k t S, k ≤ p ∧ Live T k t S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,v,U,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,v,U,by omega,hr,?_⟩
  simpa [List.map_map,Function.comp_def,table_observe] using hs

theorem live_row_difference {T k t S} (h : Live T k t S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @unary k t U a hp hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · refine ⟨a,by simp,?_⟩
      exact fun he => hd (by rw [bit_neg,bit_neg,he])
    · exact ⟨v,Finset.mem_insert_of_mem hu,hd⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {T k t S} (h : Live T k t S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def seed : Sig := 0x88888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed_table : ∀ r : Row, bit r seed = (sample r 0 && sample r 1) := by decide +kernel
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

def neighbor (i : Fin 9) : Nat := [4,2,1,2,3,0,1,2,3].getD i.val 0
def absentRow (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighbor i)
def presentRow (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor i))

theorem seed_witness : ∀ i : Fin 9,
    (bit (absentRow i) graph != bit (presentRow i) graph) &&
    ((inputs++[seed]).all fun w => w == inputs.getD i.val zero ||
      bit (absentRow i) w == bit (presentRow i) w) = true := by decide +kernel

theorem all_roots {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ inputs++[seed]) :
    S=inputs.toFinset ∨ S=(inputs++[seed]).toFinset := by
  have all (i : Fin 9) : inputs.getD i.val zero ∈ S := by
    have cut := seed_witness i
    simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne,List.all_eq_true,
      Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at cut
    apply raw_required h _ _ sub (absentRow i) (presentRow i) cut.1
    exact fun v hv hne => (cut.2 v hv).resolve_left hne
  have needed : inputs.toFinset ⊆ S := by
    intro v hv
    have hm := List.mem_toFinset.mp hv
    rw [←input_list,List.mem_ofFn] at hm
    obtain ⟨i,rfl⟩ := hm
    exact all i
  by_cases hseed : seed ∈ S
  · right
    ext w
    constructor
    · exact fun hw => List.mem_toFinset.mpr (sub w hw)
    · intro hw
      have hx := List.mem_toFinset.mp hw
      simp only [List.mem_append,List.mem_singleton] at hx
      exact hx.elim (fun h => needed (List.mem_toFinset.mpr h)) (fun e => e ▸ hseed)
  · left
    exact Finset.Subset.antisymm (fun w hw => by
      have hx := sub w hw
      simp only [List.mem_append,List.mem_singleton] at hx
      rcases hx with hin | rfl
      · exact List.mem_toFinset.mpr hin
      · exact False.elim (hseed hw)) needed

theorem initial_live (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 1))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 15) :
    ∃ k t, k ≤ 14 ∧ (Live graph k t inputs.toFinset ∨ Live graph k t (inputs++[seed]).toFinset) := by
  have headEq : (execute C.gates inputs).getD 9 zero = seed := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal 9 r).trans ((first (sample r)).trans (seed_table r).symm)
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have out := get_rep (execute C.gates inputs) C.output
  rw [goalEq] at out
  have targetIn := out.resolve_right (fun hn => hn graph_proper)
  cases hgs : C.gates with
  | nil =>
    rw [hgs] at headEq
    exact False.elim (seed_nonzero headEq.symm)
  | cons g gs =>
    have eq0 : gv inputs g = seed := by
      rw [hgs] at headEq
      change (execute gs (inputs++[gv inputs g])).getD 9 zero = seed at headEq
      obtain ⟨l,hl⟩ := exec_extends gs (inputs++[gv inputs g])
      rw [hl] at headEq
      exact headEq
    rw [hgs] at targetIn
    change graph ∈ execute gs (inputs++[gv inputs g]) at targetIn
    rw [eq0] at targetIn
    have tailLegal : ∀ gate ∈ gs, gate.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ gate.inputs.length≤2 := by
      intro gate hg
      apply legal
      rw [hgs]
      exact List.mem_cons_of_mem _ hg
    obtain ⟨k,t,S,hk,run,hs⟩ := extract gs _ tailLegal graph_proper targetIn
    have len : gs.length+1 ≤ 15 := by simpa [Circuit.size,hgs] using small
    refine ⟨k,t,by omega,?_⟩
    rcases all_roots run hs with h | h
    · exact Or.inl (h ▸ run)
    · exact Or.inr (h ▸ run)


def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_neg (f : Row → Row) (a : Sig) : rename f (neg a) = neg (rename f a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (neg a)) = bit ⟨j,hj⟩ (neg (rename f a))
  rw [bit_rename,bit_neg,bit_neg,bit_rename]
theorem rename_bin (f : Row → Row) (d : Bool) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (bin d a b)) = bit ⟨j,hj⟩ (bin d (rename f a) (rename f b))
  rw [bit_rename,bit_bin,bit_bin,bit_rename,bit_rename]
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
theorem live_rename {T k t S} (h : Live T k t S) (f : Row → Row) (onto : Function.Surjective f) :
    Live (rename f T) k t (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @unary k t U a hp hf _ ih =>
    have fresh : rename f (neg a) ∉ (insert a U).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_neg] at fresh ih ⊢
    exact Live.unary (pp _ hp) fresh ih
  | @binary k t U a b d ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {T k t S} (h : Live T k t S) (none : t=0) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih none
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      cases d <;> cases p : bit r a <;> cases q : bit s a <;>
        cases u : bit r b <;> cases z : bit s b <;> simp_all
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map observe) p bank → Available bank (observe T) → L ≤ p

def Impossible (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k t, k ≤ cap → ¬Live T k t S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {roots T L} (hp : proper T)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,t,S,hk,run,hs⟩ := reach_live hp h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k t (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : represented ([] : List Sig) v := by
    have avail : Available ([] : List (Wire Row)) (observe v) := Or.inr ⟨b,h⟩
    simpa only [List.map_nil,table_observe] using available_rep avail
  exact (hr.resolve_left (by simp)) hv

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

theorem lower_slice {roots other : List Sig} {T G : Sig} (pT : proper T) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live pT hh ha
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
  have supp : supply (other.map observe) ((front.map observe).map (restrictRows r)) := by
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



def childOne (ws : List Sig) (a : Sig) (keep : Bool) : List Sig :=
  neg a :: kept keep a (ws.erase a)
def childTwo (ws : List Sig) (a b : Sig) (d ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : ∀ a ∈ ws, ∀ keep, neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      Impossible T (cap-1) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset := by
  classical
  intro k t hk h
  generalize he : ws.toFinset = S at h
  cases h with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @unary k t U a ha hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh : neg a ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let keep := decide (a ∈ U)
    have er := erase_fin hn a
    have rest : (kept keep a (ws.erase a)).toFinset = U := by
      rw [kept_fin,er,he]
      by_cases hm : a ∈ U <;> simp [keep,hm]
    have nd : (childOne ws a keep).Nodup := by
      have na : a ∉ ws.erase a := hn.not_mem_erase
      have nk := kept_nd keep a (ws.erase a) (hn.erase _) na
      refine List.nodup_cons.mpr ⟨?_,nk⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h))
    have eq : (childOne ws a keep).toFinset = insert (neg a) U := by simp [childOne,rest]
    have sc := (live_size tail).2
    have len : (childOne ws a keep).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact oneStep a am keep fresh hz len k t (by omega) (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail =>
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
    have sc := (live_size tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) (eq.symm ▸ tail)

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

theorem cover_sound {T k t S} (h : Live T k t S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → t=0) :
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

theorem cover_required {T cap ws k t} (h : Live T k t (List.toFinset ws))
    (hk : k ≤ cap) (hn : ws.Nodup) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (decide (ws.length=cap+1)) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  intro hh
  have eq := of_decide_eq_true hh
  have bound := (live_size h).2
  rw [List.toFinset_card_of_nodup hn] at bound
  omega



def Slice (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach (roots.map observe) p bank → Available bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m)

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

def poolSupply (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available bank (restrictRows f (observe a))

theorem availableB_sound {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply f bank pool)
    (check : availableB d pool a = true) : Available bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with (hz | ho) | ⟨v,hv,he⟩
  · exact Or.inr ⟨false,masked_zero dom hz⟩
  · exact Or.inr ⟨true,masked_one dom ho⟩
  · exact masked_eq dom he ▸ supplyB v hv

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) :=
  if c.1=2 then neg c.2.1 else bin (c.1==1) c.2.1 c.2.2
def choiceOK (d : Sig) (pool : List Sig) (c : Choice) :=
  availableB d pool c.2.1 && (c.1==2 || availableB d pool c.2.2)

theorem pay_choice {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d pool c = true) :
    ∃ next, Reach roots (q+1) next ∧ poolSupply f next (choiceVal c :: pool) := by
  have ok : availableB d pool c.2.1 = true ∧ (c.1==2 || availableB d pool c.2.2) = true := by simpa only [choiceOK,Bool.and_eq_true] using valid
  have ha := availableB_sound dom hs ok.1
  let z := restrictRows f (observe (choiceVal c))
  have hz : Reach roots (q+1) (z::bank) := by
    by_cases unary : c.1=2
    · change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_pos unary,obs_neg]
      exact Reach.one hp ha
    · have hb : availableB d pool c.2.2 = true := by simpa [unary] using ok.2
      have hz' := Reach.two (c.1==1) hp ha (availableB_sound dom hs hb)
      change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_neg unary,obs_bin]
      have comm (b : Bool) (v w : Wire Row) : restrictRows f (combine b v w) = combine b (restrictRows f v) (restrictRows f w) := by cases b <;> rfl
      rw [comm]
      exact hz'
  refine ⟨_,hz,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact Or.inl (by simp [z])
  · exact available_cons _ (hs _ hm)

def makePool (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK d pool c then makePool d (choiceVal c::pool) cs else none

theorem makePool_sound {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {result} (ok : makePool d pool cs = some result) :
    ∃ next, Reach roots (q+cs.length) next ∧ poolSupply f next result := by
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

def poolCut (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB d pool)

theorem poolCut_sound {raw T d L} (slice : Slice raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut d L cap cs.length pool ws = true) :
    Impossible T cap ws.toFinset := by
  intro k t hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply bank ((ws.map observe).map (restrictRows f)) := by
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
theorem freeWord_ok {roots w} (ok : freeWord roots w = true) :
    Available (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr ⟨false,funext bit_zero⟩
  · exact Or.inr ⟨true,funext bit_one⟩
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (pG : proper G) (hL : Lower base G L) : Lower raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower base G L) :
    Slice raw T d L := by
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
  xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok _ hm)

theorem lower_count {raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live properT hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := (live_size run).2
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower base G L) :
    Lower raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT properG _ eq supp _ (essential_ok ok.1.2) _ L low
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
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
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

def supportPairs (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,0,Fin.ofNat 512 (1 <<< i))

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
theorem size_of {m hints L} (h : assertSize m hints L = true) :
    Lower (vars m) (graphGoal m) L := by
  simp only [assertSize,Bool.and_eq_true,decide_eq_true_eq] at h
  intro p bank hr ha
  exact h.2.trans (lower_count (proper_of _ h.1.1) _ h.1.2 p bank hr ha)

abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig :=
  if m=1023 then graphGoal m &&& ~~~seed else graphGoal m
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (vars m) (chartGoal m) (vars free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (vars free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice (vars m) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  obtain ⟨z,o,q,s,L⟩ := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  change (((properB G && checkMap ms (vars m) (chartGoal m) (vars free) G) &&
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

def relabelOK (old rep : Nat) (swaps : List Nat) :=
  properB (graphGoal old) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (vars old) (graphGoal old) (vars rep) (graphGoal rep)
theorem relabel_of {old rep L swaps} (ok : relabelOK old rep swaps = true)
    (h : Lower (vars rep) (graphGoal rep) L) : Lower (vars old) (graphGoal old) L := by
  simp only [relabelOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1) (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower (vars q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he


structure BoundPool where
  domain : Sig
  bound : Nat
  paid : Nat
  wires : List Sig

def ValidPool (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach (roots.map observe) q ws → Available ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach (roots.map observe) c.paid bank ∧ poolSupply f bank c.wires ∧ True

theorem build_valid {raw T d lb} (h : Slice raw T d lb) (cs : List Choice) {ws}
    (build : makePool d raw cs = some ws) : ValidPool raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa using hr,hs,trivial⟩

theorem valid_exclude {raw T c} (valid : ValidPool raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB c.domain c.wires a = true)
    (buy : if paid then choiceOK c.domain c.wires choice = true
       else availableB c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible T k (choiceVal choice :: rest).toFinset := by
  intro t num ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach (roots.map observe) n out)
      (zs : poolSupply f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply out ((ws.map observe).map (restrictRows f)) := by
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
    · have avail := availableB_sound dom hs (known _ hm)
      rcases avail with mem | con
      · have ha : availableB c.domain c.wires a = true := known _ hm
        have point : ∀ u ∈ c.wires, Available out (restrictRows f (observe u)) :=
          fun u hu => hc u (List.mem_cons_of_mem _ hu)
        exact availableB_sound dom point ha
      · exact Or.inr con

def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB c.domain c.wires)) && (!extra || choiceOK c.domain c.wires op)

theorem scalarPoolCut_sound {raw T c} (valid : ValidPool raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut c k rest op = true) :
    Impossible T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {raw T d L cs c} (slice : Slice raw T d L)
    (h : materialize raw cs d L = some c) : ValidPool raw T c := by
  unfold materialize at h
  cases he : makePool d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he


abbrev Bits := BitVec 768
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 768 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 768 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 768 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 768 → Row) (x : Decor) := x.2 = pairSig r s x.1
def dneg (x : Decor) : Decor := (neg x.1,~~~x.2.1,~~~x.2.2)
def dbin (d : Bool) (x y : Decor) : Decor :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)

theorem ofRows_neg (r : Fin 768 → Row) (a : Sig) : ofRows r (neg a) = ~~~ofRows r a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (neg a) ⟨j,hj⟩
  rw [bit_neg,←ofRows_bit r a ⟨j,hj⟩] at h
  simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
theorem ofRows_bin (r : Fin 768 → Row) (d : Bool) (a b : Sig) :
    ofRows r (bin d a b) = if d then ofRows r a ||| ofRows r b else ofRows r a &&& ofRows r b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  cases d <;> simpa only [Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_or] using h
theorem faithful_neg {r s x} (h : faithful r s x) : faithful r s (dneg x) := by
  change x.2 = _ at h
  simp only [faithful,dneg,pairSig,ofRows_neg, h]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  cases d <;> simp only [faithful,dbin,Bool.false_eq_true,ite_false,ite_true,pairSig,ofRows_bin,hx,hy]

def codeDecor (op : Nat) (x y : Decor) := if op=2 then dneg x else dbin (op==1) x y
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
    decodeBank k (bits >>> 10) (ws++[codeDecor ((bits >>> 8) &&& 3) a b])
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
      unfold codeDecor
      split
      · exact faithful_neg (faithful_get base _)
      · exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 768) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 768) (j : Fin 9) :
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
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 768) :
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
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut p k rest op)

theorem closeChild_sound {raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

abbrev CovPair := Cov × Cov
def preCov (ws : List Decor) : CovPair := (coverage false ws,coverage true ws)
def getCov (c : CovPair) (d : Bool) := if d then c.2 else c.1
theorem get_preCov (ws) (d : Bool) : getCov (preCov ws) d = coverage d ws := by cases d <;> rfl
def restCov (v : Cov) (a b : Bits) (un ka kb : Bool) :=
  if un then (if ka then v.1 else takeOne v a) else
    if ka then (if kb then v.1 else takeOne v b)
    else if kb then takeOne v a else takeTwo v a b
def opKeep (un ka kb : Bool) (a b : Decor) (ws : List Decor) :=
  if un then delOne ws a ka else delTwo ws a b ka kb

theorem rest_coverage {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws)
    (un ka kb d : Bool) (ne : un=false → a≠b) :
    (coverage d (opKeep un ka kb a b ws)).1 =
      restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) un ka kb := by
  rw [get_preCov]
  cases un
  · exact cover_two d a b ha hb (ne rfl) ka kb
  · exact cover_one d a ha ka

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    (opKeep un ka kb a b ws).Sublist ws := by
  cases un
  · exact (delOne_sub _ _ _).trans (delOne_sub _ _ _)
  · exact delOne_sub _ _ _
theorem len_keep (ws : List Decor) (a b : Decor) (un ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : un=false → a≠b) :
    (opKeep un ka kb a b ws).length =
      ws.length - (if ka then 0 else 1) - (if un || kb then 0 else 1) := by
  cases un
  · have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm (ne rfl))).mpr hb
    cases ka <;> cases kb <;> simp [opKeep,delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
  · cases ka <;> cases kb <;> simp [opKeep,delOne,List.length_erase_of_mem ha]

def movedDecor (op : Nat) (a b : Decor) := codeDecor op a b
def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)
theorem moved_full (op) (a b : Decor) :
    (movedDecor op a b).1 = choiceVal (movedChoice op a b) := by
  by_cases h : op=2
  · simp [movedDecor,codeDecor,h,dneg,choiceVal,movedChoice]
  · cases hh : op==1 <;> simp [movedDecor,codeDecor,h,hh,dbin,choiceVal,movedChoice]
theorem moved_faithful {r s a b} (ha : faithful r s a) (hb : faithful r s b) (op : Nat) :
    faithful r s (movedDecor op a b) := by
  unfold movedDecor codeDecor
  split
  · exact faithful_neg ha
  · exact faithful_bin _ ha hb

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let un := op==2
  let len := 1+(n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len>cap then true else
    let d := len==cap
    let rs := restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (opKeep un ka kb a b ws).map Prod.fst
      closeChild pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (movedDecor op a b).1 :: (opKeep (op==2) ka kb a b ws).map Prod.fst
theorem evalMove_sound {raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov ws,pools,links) op a b (movedDecor op a b) ka kb = true) :
    Impossible T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := movedDecor op a b
  let rest := opKeep (op==2) ka kb a b ws
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k t hk h
  have hsz := (live_size h).2
  change child.toFinset.card + t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h hk ndc (pair_sep pairs)
  have ce : cap-1+1=cap := by omega
  rw [ce] at sep
  let d := child.length==cap
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz := rest_coverage ha hb (op==2) ka kb d ne
  have hf := moved_faithful (faith _ ha) (faith _ hb) op
  have deq : decide (child.length=cap) = (child.length==cap) := by by_cases he : child.length=cap <;> simp [he]
  change covered (decide (child.length = cap)) (pairSig r s) child = BitVec.allOnes 768 at sep
  rw [deq] at sep
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 768) = false := by simp [sep]
  change (if (_ != _) then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  have val := moved_full op a b
  change z.1 = _ at val
  change Live T k t child.toFinset at h
  have nd' := ndc
  change (z.1::rest.map Prod.fst).Nodup at nd'
  change Live T k t (z.1::rest.map Prod.fst).toFinset at h
  rw [val] at nd' h
  exact closeChild_sound pv lv nd' test k t hk h


def testPair (ctx : NodeContext) (a b : Decor) (d : Bool) :=
  let op := if d then 1 else 0
  let z := movedDecor op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
  let z := movedDecor 2 a a
  evalMove ctx 2 a a z false false && evalMove ctx 2 a a z true true &&
    bs.all (fun b => testPair ctx a b false && testPair ctx a b true)
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_unary {ctx ws} (h : testAll ctx ws=true) {a : Decor} (ha : a∈ws) (keep : Bool) :
    evalMove ctx 2 a a (movedDecor 2 a a) keep keep=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · cases keep
      · exact h.1.1.1
      · exact h.1.1.2
    · exact ih h.2 hm

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) (d : Bool) : testPair ctx a b d=true ∨ testPair ctx b a d=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left
      cases d <;> first | exact (h.1.2 b bm).1 | exact (h.1.2 b bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · right
        cases d <;> first | exact (h.1.2 a haTail).1 | exact (h.1.2 a haTail).2
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb = true := by
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
    (ha : a ∈ ws) (hb : b ∈ ws) (un ka kb : Bool) (v : Sig) :
    v ∈ (opKeep un ka kb a b ws).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (un=true ∨ v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  cases un <;> simp only [opKeep,Bool.false_eq_true,ite_false,ite_true,delTwo,List.mem_map,
    mem_delone wn,mem_delone dn,or_false,false_or,true_or,and_true] <;> constructor
  all_goals
    first
    | rintro ⟨w,hw,rfl⟩
      first
      | exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
      | exact ⟨⟨_,hw.1,rfl⟩,hw.2.imp (fun ne eq => ne (unique_value nd hw.1 ha eq)) id⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
      exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1⟩
      exact ⟨w,⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem unary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a : Decor} (ha : a∈ws)
    (keep : Bool) :
    (moveFront ws 2 a a keep keep).toFinset = (childOne (ws.map Prod.fst) a.1 keep).toFinset := by
  ext v
  simp only [moveFront,childOne,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha ha,keep_mem,nd.mem_erase_iff,movedDecor,codeDecor,dneg,ite_true,
    Nat.reduceBEq,true_or,and_true]
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  by_cases e : v=a.1 <;> cases keep <;> simp_all

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d ka kb : Bool) :
    (moveFront ws (if d then 1 else 0) a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv := List.mem_map_of_mem (f:=Prod.fst) hb
  cases d <;> simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,movedDecor,codeDecor,dbin,
    Bool.false_eq_true,Nat.reduceBEq,ite_true,ite_false,false_or]
  all_goals by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap (v : List Sig) (nd : v.Nodup) (a b : Sig) (d ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a d kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_comm d b a]
  tauto

theorem node_sound {raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov ws,pools,links) ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k t hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    cases h
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  · intro v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    have hf := unary_front nd ha keep
    rw [←hf]
    exact evalMove_sound pairs faith nd ha ha (by simp) hc' pv lv pro fresh (all_unary checks ha keep)
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
    have ab : a≠b := fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : testPair (cap,ws.length,ws,preCov ws,pools,links) a b d = true) :
        Impossible T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
      rw [←binary_front nd aa bb ne']
      have eq : (movedDecor (if d then 1 else 0) a b).1 = bin d a.1 b.1 := by cases d <;> rfl
      exact evalMove_sound pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv
        (eq ▸ pr) (eq ▸ fr) (testPair_at test ka kb)
    rcases all_binary checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · rw [childTwo_swap _ nd]
      exact one b a hbW haW (Ne.symm ne) kb ka (bin_comm d a.1 b.1 ▸ pro)
        (bin_comm d a.1 b.1 ▸ fresh) hh


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
theorem rotate_excluded {T n} {ws : List Sig} (hi : Impossible T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k t hk h
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
  exact hi k t hk run

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
  let row := (h/nb+sh)%slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots)%16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none


inductive IndexTree (α : Type) where
  | leaf (items : List α)
  | fork (pivot : Nat) (left right : IndexTree α)
def IndexTree.read {α} : IndexTree α → Nat → Option α
  | .leaf xs,i => xs[i]?
  | .fork pivot a b,i => if i<pivot then a.read i else b.read (i-pivot)
def IndexTree.values {α} : IndexTree α → List α
  | .leaf xs => xs
  | .fork _ a b => a.values ++ b.values
theorem IndexTree.read_mem {α} (tree : IndexTree α) {i x} (e : tree.read i=some x) :
    x ∈ tree.values := by
  induction tree generalizing i with
  | leaf xs => exact List.mem_of_getElem? e
  | fork pivot a b ia ib =>
    simp only [IndexTree.read] at e
    split at e
    · exact List.mem_append_left _ (ia e)
    · exact List.mem_append_right _ (ib e)

structure Forest where
  mask : Nat
  cap : Nat
  samples : Nat → Bits × Bits
  cols : IndexTree ColumnInfo
  autos : Array (List Nat)
  levels : Nat → Packing
  index : Nat → Nat → Option (Nat × Nat)

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  let nonedge := dneg (dbin false (ws.getD 0 defaultDecor) (ws.getD 1 defaultDecor))
  if g.mask=1023 then ws.map (fun w => dbin false w nonedge) else ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  have base := raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  intro a ha
  unfold wiresOf at ha
  split at ha
  · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ha
    exact faithful_bin false (base w hw) (faithful_neg (faithful_bin false
      (faithful_get base 0) (faithful_get base 1)))
  · exact base _ ha

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  if m=1023 then liftGoal m v &&& ~~~(v 0 &&& v 1) else liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  by_cases e : m=1023
  · have u := asRow_bit v i (0 : Fin 9)
    have w := asRow_bit v i (1 : Fin 9)
    have h := bit_liftGoal m v i
    change (inputs.getD 0 zero).getLsbD (asRow v i).val = (v 0).getLsbD i.val at u
    change (inputs.getD 1 zero).getLsbD (asRow v i).val = (v 1).getLsbD i.val at w
    have seedEq : seed = inputs.getD 0 zero &&& inputs.getD 1 zero := by decide +kernel
    simp only [chartGoal,chartSamples,e,ite_true,bit,seedEq,BitVec.getLsbD_and,
      BitVec.getLsbD_not,(asRow v i).isLt,i.isLt,decide_true,Bool.true_and,u,w] at h ⊢
    rw [h]
  · simpa only [chartGoal,chartSamples,e,ite_false] using bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 768) (hq : chartSamples m q = 0) :
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
  (g.cols.read idx).bind fun ci =>
    materialize (vars g.mask) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols.read i with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (g.cols.read_mem e)

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
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))

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
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t u lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    cases h
    exact hT (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
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
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 768) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.values.all (fun c => colCheck g.mask c prior) &&
  g.autos.toList.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset := by
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
theorem root_index {g top prior k i ws} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

theorem lower_discard {g prior ci hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck g.mask ci prior = true)
    (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask)
    (nd : (vars g.mask).Nodup)
    (cut : poolCut (subcube ci.1 ci.2.1) ci.2.2.2.2 g.cap 0 (vars g.mask) (vars g.mask)=true) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (poolCut_sound (col_sound ci prior low ok) [] rfl nd cut)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (relabels : List (Nat × List Nat)) :=
  relabels.map (fun v => (v.1,L)) ++ old
theorem extendKnown_ok {old L m relabels} (previous : Known old)
    (main : Lower (vars m) (graphGoal m) L)
    (ok : relabels.all (fun v => relabelOK v.1 m v.2) = true) :
    Known (extendKnown old L relabels) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact relabel_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known [] := by simp [Known]
def lanePlace (v : Nat) (upper : Nat) := 2^769*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^769 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
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

def fullMarks (r packed : Nat) := ((packed+r) >>> 768) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (769*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^769)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 769*(i+1)-769=769*i := by omega
      have ge : ¬769*(i+1)<769 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 768 = (a==BitVec.allOnes 768) := by
  by_cases h : a=BitVec.allOnes 768
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^768-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^768 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (769*i) =
      (f xs[i]==BitVec.allOnes 768) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^769*u+x+(2^769*v+1)=2^769*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^769 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬769*(i+1)+768<769 := by omega
      have di : 769*(i+1)+768-769=769*i+768 := by omega
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

def packedOp (full : Nat) (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=2 then (full ^^^ a.1,full ^^^ a.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else (a.1 &&& b.1,a.2 &&& b.2)
theorem top_xor (a : Bits) : BitVec.allOnes 768 ^^^ a = ~~~a := BitVec.allOnes_xor
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp (units xs.length*(BitVec.allOnes 768).toNat) op
      (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (movedDecor op (a x) (b x)).2) xs := by
  by_cases un : op=2
  · simp only [packedOp,un,ite_true,packedSig,broadcast,lanes_xor,top_xor,movedDecor,codeDecor,dneg]
  · by_cases one : op=1 <;> simp [packedOp,un,one,packedSig,lanes_or,lanes_and,movedDecor,codeDecor,dbin]

def takePacked (c : PackedCov) (a b : Nat) (un ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if un then (if ka then c.1 else without1 a)
  else if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (un ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) un ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) un ka kb) xs := by
  cases un <;> cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (movedDecor op a b) ka kb
def combField (c : NodeContext) (d un ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov (getCov c.2.2.2.1 d) (column d a.2) (column d b.2) un ka kb |||
    column d (movedDecor op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 769) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (769*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
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
      apply ih (mask:=mask >>> 769) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs,packedCov (fun c => c.2.2.2.1.2) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

def availableMasked (p : BoundPool) (m : Sig) :=
  m==zero || m==p.domain || (p.wires.map (masked p.domain)).any (fun v => v==m)
theorem available_mask (p : BoundPool) (x : Sig) :
    availableB p.domain p.wires x = availableMasked p (masked p.domain x) := rfl

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

theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b (un || kb) ≤
    (opKeep un ka kb a b ws).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  cases un <;> simp only [opKeep,delTwo,Bool.false_eq_true,ite_false,ite_true,
    Bool.false_or,Bool.true_or] <;> first | omega | simp [constantLoss]; omega

abbrev QuickPool := BoundPool × Nat × Bool
def summarizePool (ws : List Decor) (p : BoundPool) : QuickPool :=
  (p,ws.countP (fun w => isMaskedConstant p.domain w.1),
     ws.all (fun w => availableB p.domain p.wires w.1))
def fastCost (s : QuickPool) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) :=
  if !s.2.2 then false else
  let p := s.1
  let un := op==2
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := choiceVal (movedChoice op a b)
  let zm := masked p.domain z
  let zc := isMaskedConstant p.domain z
  let cm := s.2.1 - constantLoss const a ka - constantLoss const b (un || kb) + zc.toNat
  let free := zc || zm==masked p.domain a.1 || zm==masked p.domain b.1
  decide (k+p.paid+(!free).toNat < p.bound+cm)

theorem fastCost_good {p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws)
    (h : fastCost (summarizePool ws p) k a b op ka kb=true) :
    scalarPoolCut p k ((opKeep (op==2) ka kb a b ws).map Prod.fst) (movedChoice op a b)=true := by
  let z := choiceVal (movedChoice op a b)
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let free := isMaskedConstant p.domain z || masked p.domain z==masked p.domain a.1 ||
      masked p.domain z==masked p.domain b.1
  let rest := opKeep (op==2) ka kb a b ws
  have ck := keptCount const ws a b (op==2) ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b ((op==2) || kb) ≤ rest.countP const at ck
  by_cases all : ws.all (fun w => availableB p.domain p.wires w.1)=true
  · have hav := List.all_eq_true.mp all
    have ready : free=true → availableB p.domain p.wires z=true := by
      intro f
      simp only [free,Bool.or_eq_true,beq_iff_eq] at f
      rcases f with (zc|za)|zb
      · simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
        exact Or.inl zc
      · rw [available_mask,za,←available_mask]
        exact hav _ ha
      · rw [available_mask,zb,←available_mask]
        exact hav _ hb
    have extra : (!availableB p.domain p.wires z).toNat ≤ (!free).toNat := by
      cases hf : free <;> cases he : availableB p.domain p.wires z <;> simp_all
    have hs : (rest.map Prod.fst).all (availableB p.domain p.wires)=true := by
      apply List.all_eq_true.mpr
      intro _ hm
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
      exact hav w ((keep_sub ws a b (op==2) ka kb).subset hw)
    have opOK : choiceOK p.domain p.wires (movedChoice op a b)=true := by
      simp [choiceOK,movedChoice,hav _ ha,hav _ hb]
    simp only [fastCost,summarizePool,all,Bool.not_true,Bool.false_eq_true,ite_false,decide_eq_true_eq] at h
    change k+p.paid+(!free).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b ((op==2)||kb)+(isMaskedConstant p.domain z).toNat) at h
    dsimp only [rest] at hs
    simp only [scalarPoolCut,hs,opOK,Bool.or_true,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
    change k+p.paid+(!availableB p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
    cases hc : isMaskedConstant p.domain z <;> simp [hc] at h ⊢ <;> omega
  · simp [fastCost,summarizePool,all] at h

def quickAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  (c.2.2.2.2.1.map (summarizePool c.2.2.1)).any (fun s => fastCost s (c.1-1) a b op ka kb)

theorem quickAt_good {c i j op ka kb} (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length)
    (h : quickAt c i j op ka kb=true) : checkAt c i j op ka kb=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
  have closed := fastCost_good (mem _ hi) (mem _ hj) ok
  have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut p (c.1-1)
      ((opKeep (op==2) ka kb (contextWire c i) (contextWire c j) c.2.2.1).map Prod.fst)
      (movedChoice op (contextWire c i) (contextWire c j)))=true :=
    List.any_eq_true.mpr ⟨p,hp,closed⟩
  simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
  repeat' split
  all_goals rfl

def fallbackAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  (if i<c.2.2.1.length ∧ j<c.2.2.1.length then quickAt c i j op ka kb else false) ||
    checkAt c i j op ka kb
theorem fallback_sound {c i j op ka kb} (h : fallbackAt c i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    next yes => exact quickAt_good yes.1 yes.2 h
    next => contradiction
  · exact h
def batchMove (b : Batch) (xs : List NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,u,v) := b
  let un := op==2
  let len := 1+(n-(if ka then 0 else 1)-(if un || kb then 0 else 1))
  if len>k then true else
    let d := len==k
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp (r*(BitVec.allOnes 768).toNat) op a b'
    let cov := if d then v else u
    let mask := fullMarks r (takePacked cov (packedColumn d a) (packedColumn d b') un ka kb ||| packedColumn d z)
    onMarks (fun c => fallbackAt c i j op ka kb) mask xs

theorem batchMove_at (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n)
    (pass : batchMove (makeBatch k n xs) xs i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1))
  let d := len==k
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] d (op==2) ka kb op i j != BitVec.allOnes 768 then true
      else if !properB (movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((opKeep (op==2) ka kb (contextWire xs[q] i) (contextWire xs[q] j) xs[q].2.2.1).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,len,d,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := if d then packedCov (fun c : NodeContext => c.2.2.2.1.2) xs
            else packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn d a) (packedColumn d b) (op==2) ka kb |||
        packedColumn d (packedOp (r*(BitVec.allOnes 768).toNat) op a b))) xs) = true at pass
    rw [if_neg small] at pass
    have chosen : cov = packedCov (fun c => getCov c.2.2.2.1 d) xs := by
      dsimp only [cov]
      cases d <;> rfl
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,chosen,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] d (op==2) ka kb op i j = BitVec.allOnes 768
    · apply fallback_sound
      apply marked_ok _ _ _ q hq _ pass
      rw [mark_at _ _ _ hq]
      exact beq_iff_eq.mpr hit
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]


def batchPair (b : Batch) (xs : List NodeContext) (i j op : Nat) :=
  let f := batchMove b xs i j op
  f false false && f true false && f false true && f true true
def batchRow (b : Batch) (xs : List NodeContext) (i : Nat) (js : List Nat) :=
  batchMove b xs i i 2 false false && batchMove b xs i i 2 true true &&
    js.all (fun j => batchPair b xs i j 0 && batchPair b xs i j 1)
def batchRows (b : Batch) (xs : List NodeContext) : List Nat → Bool
  | [] => true
  | i::js => batchRow b xs i js && batchRows b xs js

theorem batchRows_at (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows (makeBatch k n xs) xs js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    have check := @batchMove_at k n xs
    refine ⟨⟨⟨check hi hi hq budget arity allRows.1.1.1,check hi hi hq budget arity allRows.1.1.2⟩,?_⟩,
      ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    have both := allRows.1.2 j hj
    have opCheck (d : Bool) (pass : batchPair (makeBatch k n xs) xs i j (if d then 1 else 0)=true) :
        testPair xs[q] (contextWire xs[q] i) (contextWire xs[q] j) d=true := by
      simp only [batchPair,Bool.and_eq_true] at pass
      simp only [testPair,Bool.and_eq_true]
      exact ⟨⟨⟨check hi hj' hq budget arity pass.1.1.1,check hi hj' hq budget arity pass.1.1.2⟩,
        check hi hj' hq budget arity pass.1.2⟩,check hi hj' hq budget arity pass.2⟩
    exact ⟨opCheck false both.1,opCheck true both.2⟩

def runBatch (k n : Nat) (xs : List NodeContext) :=
    batchRows (makeBatch k n xs) xs (List.range n)
theorem runBatch_at {k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hn : xs[q].2.2.1.length=n)
    (pass : runBatch k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha (List.range n) (fun _ => List.mem_range.mp) pass
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
  (k,ws.length,ws,preCov ws,rules,ls)


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
def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  (List.range len).all (fun d =>
    let i := lo+d
    batchRow b xs i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (makeBatch k ar (contexts g k start n)) (contexts g k start n)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)

theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (makeBatch k ar xs) xs (List.range' lo num)=true := by
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
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hn (cutsRun h)

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
def g15d3 (i : Nat) : Nat := 0xf
def g15l3 : Packing := (1,0,0,0,1,0,0,g15d3)
def g15samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbaf3ea78de4d799d,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff450cc90c3c245919),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdf7ff8fe9f9b7ed5,0x20812421801324c4),(0xefbdbf97f9f6bf6a,0x102a401415600a0a),(0xf3a9d7437375f5ba,0xfc028ab620235b0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def g15columns : IndexTree ColumnInfo := (.leaf [])
def g15autos : Array (List Nat) := #[[],[33,48]]
def g15levels : Nat → Packing
  | 3 => g15l3
  | _ => emptyPacking
def g15index : Nat → Nat → Option (Nat × Nat)
  | 3 => fun _ => none
  | _ => fun _ => none
def g15 : Forest := ⟨15,3,fun j => g15samples[j]?.getD (0,0),g15columns,g15autos,g15levels,g15index⟩
def key31l6 (i : Nat) : Nat := 0x820007028af371d000003180048302e380000000003819155875690d58000003d
def g31d5 (i : Nat) : Nat := 0x84001e90fd02fd01fa00
def g31l5 : Packing := (3,1,3,0,4,4,0,g31d5)
def g31d6 (i : Nat) : Nat := 0x11a20bf
def g31l6 : Packing := (1,0,3,2,4,0,0,g31d6)
def g31samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdafffab2d55fb9f999d9ceeefacb357b78f9ce2bb554a3bac97b2a9d65,0x250142092220460600407048c382809c2160e048740030a88143281c44),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef5dfed46f26fea572a7ba9effd7341aff97ad1ab5bd2d547d6793334b,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff90aa211010d10141c4300836206168204010183680184d04682483210b),(0x73ef3f3c8ff8df3fe567b556c9567ffcd665219778a6bd6e36bfd946ac,0xc10d0c3000214920a0d648109801012344d60802686b04210115006a4),(0x7c7fd57b7ffa3476e74d6f3fc4bddbd44dc213c5eb8bdea95bf6ee7492,0x38022048645c06490200044a25241818912934541000824c322ae5002),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8fe76ff6451fda6ff84b6daf38f5bb6f6a5ee88a4d6be3f71c64aa3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8076989008882001270e063010011622500c04308a174300141c40a239),(0,0),(0,0),(0,0),(0,0)]
def g31columns : IndexTree ColumnInfo := (.fork 2 (.leaf [(1,0,30,0,4),(2,0,29,0,4)]) (.leaf [(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)]))
def g31autos : Array (List Nat) := #[[],[50,65],[66,16],[67,50,33,16],[67,32],[67,66,49,32],[33,48],[67,50,65,48],[67,66,65,64],[49,64]]
def g31levels : Nat → Packing
  | 5 => g31l5
  | 6 => g31l6
  | _ => emptyPacking
def g31index : Nat → Nat → Option (Nat × Nat)
  | 5 => fun _ => none
  | 6 => lookupWord 5 25 2 10 2 4 (key31l6)
  | _ => fun _ => none
def g31 : Forest := ⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index⟩
def g47samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffddffff5cfaafae7dd35b9ce7bbffd6b6b7b7cfbb8d3b7ad85ddf257b56b575,0x2200a042011011800c00803812181c2009c1061c0107200c09440143143444),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeebefed537937fcb8ab173daa7df7f7691aff9776b2b7dcb92a3f3678b2b59,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9149112428688034a38448020d64a21d120601022ea84882b022a624830919),(0x77db9fef67fc77f3ffe6e3dd55f86b6fffcab66472f7c57fb768dabfad4eae,0x820641080010508440806b120004c020121a4ec1002247c020840112806a4),(0x78ebe4ae9ffd0d576de696b3cff805db7d426c00d8ded437ed436ff6f66c92,0x71419416322f057a950700411b6b328381c4110e8d4580325370f22d66812),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0bf9ebdb2287acd4afec26dbb6d98eabb3768bb508ca4b7f1fdd1c709a3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80f74f1424444852a26637058ca3a012d22680c12e48c8e17411561c608a3b),(0,0),(0,0),(0,0)]
def g47columns : IndexTree ColumnInfo := (.leaf [(8,0,39,0,4)])
def g47autos : Array (List Nat) := #[[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index⟩
def g55samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)]
def g55columns : IndexTree ColumnInfo := (.leaf [(16,0,39,0,4)])
def g55autos : Array (List Nat) := #[[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest := ⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index⟩
def g63samples : Array (Bits × Bits) := #[(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)]
def g63columns : IndexTree ColumnInfo := (.leaf [(32,0,31,0,7)])
def g63autos : Array (List Nat) := #[[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index⟩
def g111d6 (i : Nat) : Nat := 0x120ff
def g111l6 : Packing := (1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits) := #[(0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444),(0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909),(0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452),(0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac),(0,0),(0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9),(0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6),(0,0),(0,0)]
def g111columns : IndexTree ColumnInfo := (.leaf [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)])
def g111autos : Array (List Nat) := #[[],[83,32]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
def g119samples : Array (Bits × Bits) := #[(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)]
def g119columns : IndexTree ColumnInfo := (.leaf [(4,0,115,0,5)])
def g119autos : Array (List Nat) := #[[],[84],[98],[84,98],[101,66,16],[101,100,66,16],[101,84,82,16],[100,82,16]]
def g119levels : Nat → Packing
  | _ => emptyPacking
def g119index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g119 : Forest := ⟨119,5,fun j => g119samples[j]?.getD (0,0),g119columns,g119autos,g119levels,g119index⟩
def key189l7 (i : Nat) : Nat := 0xa81337040d4b600002948880000590cc33d41450272020001b1
def g189d6 (i : Nat) : Nat := 0x82000f487f40bfa03fa00
def g189l6 : Packing := (3,1,3,0,4,4,0,g189d6)
def g189d7 (i : Nat) : Nat := 0x1f5859bf
def g189l7 : Packing := (1,0,3,2,4,0,0,g189d7)
def g189samples : Array (Bits × Bits) := #[(0x76b7b935ad7f6fd4d735f26d2df10ff4361bcad97bdde979efcd6e58b7554d7ea7eff73e73de92e56562d7533a4ef3de34b1f6acf1d6e216666babd43dbaabce3ad8d545ed4e53771cb4e6d84ab365f9722155b0decf672135d0ab0e8aab3265,0x8404642124899480a2a81184400c4494a40542200633c0114901482008a100b4c40690c02a500485280025a8300be5004d078022244028e4a0122910034dd0088624c002500565400b4701a401901a06a801c60d40e430038408b0c08aa0264),(0,0),(0xb725f7b34edfbeffaf8e64c99fca263eeb8ebd6e6efba6759d07fff35f0d57cf0f1af1c8e8596f2d9f9a363b65aade972ff9af593499366f72b4e55d5e6f961954d5fce693a74e66d370dbbd59357a0ab5d8c2e2b4913d9ddc0ac963246654eb,0x2019084c910042485050a84580141012107000421c10cd02a29a004c0424911090cb1414ac1a4012048a60a1130c00921224ba8854044c203120d1318881010110848d88109408245548f0845c253042044cc0e02091152804424943044214c9),(0x6b3b37beb0d3b3db67cafb77eb9e1dd789aebdb18d1db77732f653e35977f97f4dd313687fb67a399a5d29e7c5c2df2ae361e9d1a8a6a7bdf9b41bf76bf3c59c972736ba642a6ec8e10ddd388a5d8a2fef454b2f6c5cd8cb4dafd1a5458caf32,0x84c42401462a8882042c15880121e0040f09501440a3008044047580824b00c92204cb801220a2e8d004050a8c13a8082552010080e322ce0002224042220e86c96110212062d680201609100358082de8010e0a0c4e080169249024018caa32),(0xeed4ecfef66eeb7efebdd9aee7077cf1671b7b7a97dfdfd372d0ed94ede3ade9c50737565e265d36d07689d4ac4faafe5abbfdc5676e89f79f8f9a623b38502f3db98ff0fa982b81b88d0790fae9d8d74f74351d5187af7a955e769667c1914c,0x112b0124099000041080680538580102a03620812918016ca82b084951200b0011391441e40a1406003a00a460640102802906c05910d52121d05c00b8012058249003c452192901d049060038a0e052051c011422a1a0780618649266411108),(0xd9cafe65094bbf5f7264b7bbce3ffbefdc6762cbb35969c8ac2ddbae62ff5a5f3ee2cea13be5ccd265ed5a725a1921f7f9e712e69e98fb2d45e97fd5f2e0abe4f3f7676b375491bf662220c7ec1235aaa52f7b260bfdf8f023b73c589c1c3f19,0x2215018860a440b0408528403b942810a5b0009c1c080302094a000184016510830b02e2ac10b810014a60046c8c012e120b028809b84c0105208c4e88802201101131880274018a550300819c02301e012cc3000b90a8a80382305084143519),(0,0),(0xe9cbc8feffb7f8e7b8d17ff4f26deb6af5fadcfef4fa8da189aed6c66eadfbba567e7aa58acda76b57bfee9d03799233ac5e277f4fab9af55d736c18d65d30adcab7ab9d1b9dcbcc02d24b67373e9182d29baedd99bcc115aa3d04dc337a48be,0x1420360100482d00252a00a2440945244a022b202187302c44004bb2035a00002400090800450025fa000d1a80010240a950404582409154ca522280124a1c0c672a40054909a2500214036203d800a092812c0514244211e81d048c33284826),(0,0)]
def g189columns : IndexTree ColumnInfo := (.fork 4 (.leaf [(1,0,188,0,5),(12,0,177,0,4),(16,0,173,0,5),(17,0,172,0,4)]) (.leaf [(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]))
def g189autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32],[82,48],[84,115,82,48],[117,116,115,114,64],[83,114,64],[116,50,80],[117,84,67,50,80],[84,115,66,112],[66,112]]
def g189levels : Nat → Packing
  | 6 => g189l6
  | 7 => g189l7
  | _ => emptyPacking
def g189index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 5 18 5 10 2 4 (key189l7)
  | _ => fun _ => none
def g189 : Forest := ⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index⟩
def g127samples : Array (Bits × Bits) := #[(0x27ec63be833e95d9cd8b1b0f8c7b949b955ab7ff06f2f46fb53d19a8b89e2cf938ea5b637a679113a99b1a558cf5d3757100e2a2d92956b1df648864a3a84cf9f5aafcc4980f547cd2d2abacb351593072ded0ca36876c216b176a15583d3069,0x215000b22a840210400a1040082a19401000220004808d00802008c02014082088420800402688520818425544410445400040805130408104600820a3600c001020e0440008143510802b10a111102142440000168440214816081150281060),(0xd1272c7d4d43f0bd72e56dab39ddfe7c6a407c139e413a8c95b2f6c7134bd9d2e6151acc0f6f6e61aecc859cb80ab9d38d1f9c08bbd08127631b9fb156aefb042a9049abe4f27cdb8815184a3fa2b5dede495570df2830da3c38c46cf1426d13,0x806000d540888802080408280406213088804000000320c048631024209804006241648090164a10080940a08001912a8109004a2408004431a0101080453200880088a80c0004a880100481a02008819080040c10830122428406420422c11),(0x3757a63bdee4ba3fd3e2275cd925bbac4327c3605b6a92ba668b6b375f5956a61c0ee4c8b6382a0c726a8d674c1d24e187c7697b46618e9a3259ec9e635cb1935494676727a9c6a3df6b34450ca72f271676b8367562d5a985429aaa9a64d626,0xe190134200c030558e6885084d0788a40161e860830e0412a109c61098d030850809a9902628890c322a09e446182064058721691005078a1841cc5c6248a09654242521162044855722240404692506023498262462c48981029a8a9a244222),(0x7c12f7ae7cb67a121957d4766ab145360dad0baa714fd5dd4ad95b9245e39e4cff88a61691dd24ee5570ea624367b54a6aea5375c626bc6f4082772e38770d5a1955fa1dcb198b20afa8d659c70c9ab5dbb42b955b55e374e0f839c3068a9694,0x100b203118264280010702e3020864421484020c18c0438c4090018044060d7096401604915660c20151c00201478d0220604290c2020821402022221025140809114a0c4919231288809339110498f1918002911b15216460582041008a9494),(0x5f0ed2cab79191489f9794fa9f865222c0c45f4f23977137ba6ec87e2fb718cbcb3281372d8190b9e5b2713c276012285f3b185c628f375c96ee95cada25845527c7ad5b31bc018c667be7de6cdf9480211b73e5e0fc0e1e03a683a80feb2399,0x4e04900c0410144f3ce0e018c1840020605099a3823d30032c4ce03413c1e08c412481b32c810028f486342022205010179b1c44008d375c030cd5d908008055e282051134c40088667900c444ea04000013f960e0680e1a03a083a80f412309),(0x64ed11ab034e6565aa5f6f0a73fb2abb553e90eaf5f2056f4f2ad1a6a7112f3107edc462d825611a42150349a39be3bcbdfa3bf68749fd950e410251758bd0aaed7e1f93ab81b400f6cd22629068e5bc2da9dbde283bbf115009f3b1a197a662,0x46299909050b25a18c71e62a5095c63ecb8f04a3c26b60b927cda532c109201915ade64b3091412042050108b390e3bab9cb9877060097580a090251508bf2aae7571e1ba185a2088a6c00621068c596ada8d9f5a83bbf101009f3a0a197a602),(0xed72aa63cb994444b8dcf183254b4e7cee24db3ad729ab4a1ba98c700af5e5480459e832e1cc5750368c89edf172492ed4565f186db3259850f427f3943aea1f7b1d745054d56ed5059c9e36e00b68fdae413f628aa9c64ad98b04d0b38dd9ac,0x4400b2628be723745844a119668f0ccc9303b92a933d014173710ec9a0c0658c41596832a4cc13563c0629c5d4a2402c44020f584d31651810e10cda143b2c95631f726414156f15141896b3a1182c75a6e53b222aa1c648d9830490938dd1ac),(0,0),(0,0)]
def g127columns : IndexTree ColumnInfo := (.leaf [(32,0,95,0,8)])
def g127autos : Array (List Nat) := #[[],[101,66,16]]
def g127levels : Nat → Packing
  | _ => emptyPacking
def g127index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g127 : Forest := ⟨127,8,fun j => g127samples[j]?.getD (0,0),g127columns,g127autos,g127levels,g127index⟩
def key191l10 (i : Nat) : Nat := 0xa2d43b28d7001ab368009df79a6668d8a485480048c00a24000002900046192841e000000005078511fa7b8000001d8000000000050332001c2200008044
def key191l9 (i : Nat) : Nat := 0xb5d65558d2140ea31b806b286019a820212fb2e35aa613228a5a077246e6fc20ca1a41bb2d080a9c3e39f318874648000323b01b537426ceae26842215792e4b19e71cc72290229e7cad73d5f333056000d205f83e366a30000000d49821b1f1088000bb771a5c8c0000000000eb0000e0cb6ac6bec3c000c1b800347e18451880000012040006004d1cd8e0000001866e151a0000282800081e2a5e9518b100010bc00000030815564ae0000000000000ba722a1a34000000e6c5a954a6f09e6780014941d61a7112de27d595e7f09e40be3dc9678ab0bf3d70002c438a3dd4912345fe50900b4e481ecbbcceb07786be83e621d46430465b9b583a98309000098f882ae3a444b1d707c001bdad01b2c800179a0001f6d90464c82da1658b094500004b589e042e51604dd58429e06b90ff614389938aaeb6d12bb049522a72f25c09129e0463116174d50c3960b150c0a182d435d81d03dcbc0b346f3525916e494182a5649d22c9002ab560902d0004c5bd2828ce425700001e0842090d9c2ec56f6a2934aac61902201440c3800d7464005040d9808000b00120008008026140608781000c78f2e086830a0c98000580830000a023a002141e004000c001040a00380
def key191l8 (i : Nat) : Nat := 0x18cd14b25011e7225b26001876a3412158c6fc726c2320d6e3243bdd05603f1613ebb0007f7c604089b00125f5892200bf9421800b5e245039f1cf3cb8436d7f2000047800310000002025492575bf0012c00000042000001b8021c00800c01d000c080081
def key191l7 (i : Nat) : Nat := 0x2c
def g191d6 (i : Nat) : Nat := 0x47d6448788a00
def g191l6 : Packing := (1,4,6,0,2,0,0,g191d6)
def g191d7 (i : Nat) : Nat := 0x1021aae2c480c58812165850610304200048200685020d100000000000200100000fce5cec0b2a49f918c877974664f4a45403b36312c2722140f0a0500fd51548d13edd3641903fd51544d03fe92540d02df57305d02ff10305d02df4179dd02bf5819dd02df5819dd029fd819dd02df5155cd019fe885c901fe92440901ff114409019fc8788a009bd849dd039f5819dd02ed6668ce11f56558ce119f47840a11f3a5591200eda668ce00f5a558ce00bb9841ca00fca3388a00fb24484600fd23384600fe22284600
def g191l7 : Packing := (28,3,6,0,2,8,0,g191d7)
def g191d8 (i : Nat) : Nat := 0x850910304081c2440c0e2128f09183458e0d563c424bf1e12406128b1c7846402045834a31022c1244b4112285081c2449f022410c0418818084041a2060210127868c180849614f082043003c28008103c00a001050011a0c10d03085c404064a2030a0610180108a409488504804aab1e40a0610805408d7f063c2499716b62841c098f1800a084818401971629005810a08556544b736241080077f04053c18a8a2824181120efe78c80844603045000e102828008e8b070510443840106263000efe5858a100024042202241d09811e292070e043021810a5c588002801000c0052e2c5001418110006003021810c08516144821810a085042001810afc7897e3c49e14f0a7850604482184f83a8258107f37d67c179c77f77274572070b6f66e16cc6bf6aa69568066b64e63962c61f61a60d5f85e35ce5b95ac59758256d55053b50e4f94d44bf4a247d45843b4264113e43d73ca3b53a039338635934432f3122d52c02b328e27925c24f22a21d1f81db1be1b11a419718217516815b14e13912c11710a0fd0f00e30d60c10b40a709a08d08007305e04903c02f02200d000ffa4c91ffd0548ffe93227ff41513ffa4c81ffd1640ffe83207ff49503ffa2a81ffd0540ffea2a05ff4d502ffae6817fd2340bfe89a05ff40d02ffa2e817fe7740bfe9b203ff51501ffa6a80ffd24407fe91a03ff5cd01ffa0680ffd72407fe81203ff4da00ffa47007fd13803fe89401ff88a00bfceea2dfe774d6febb247f74d923bfcee91dfd7644efebaa27fd45513bfcee89fdd2344efebb207f74d903bfaea81fdd3540eff3ba07f744d03fba4d19fdd168cfee83467f749633fba2b19fdd058cefeb9a05fe40d02fbc66817f41740aff3ba057f5cc02fbc66015fd7100afeba203fd45101f7c8880dfd73407ef19a037f5c901ff20480dfe77407faa2c23fd4d611fea4708ff503847fa81423fd00a11ff209007be44803fc81c01f78ce00ff205007f901803fb08c01fe4da00ff28b007f935803fc92401fe45200ff247007f913803fc89401fe1ca00ff445006de668cfaf2ac67f58ce11f7489007da33803f511401fc84600
def g191l8 : Packing := (100,2,6,5,2,12,0,g191d8)
def g191d9 (i : Nat) : Nat := 0x180327c7c11a70600f8f1304b1c05f0c3c541303017c38f1204e0ef8f13040180df9e0e080325463418a006077cbcf0238c0ef961b3c041381be3e0900df9e30006fcf825f86eb1755933dd9099319085000ff517fd35ff48ffd13ff40ffd02ff00bfd01ff803de33fd847fa00
def g191l9 : Packing := (12,1,6,7,2,9,0,g191d9)
def g191d10 (i : Nat) : Nat := 0x1f3c11ff
def g191l10 : Packing := (1,0,6,4,2,0,0,g191d10)
def g191samples : Array (Bits × Bits) := #[(0x6acfda3c2cb83a92b793db4cbe83faea9cb2634793e21db352fb83fe8df2bc07a86d83614e9e1d6652f73c866931a299021d0d35cea03b8bca899a3ae9b0852968ae39aed598c502d3cc66c95e3918558ba9636cd1546c95b4522b12e41c6251,0x8027018c1220821109402382a0c04040242201142810004800310a01021028020024504420900008134444101889108100844480011218a0808a088000429588a002494484002118004005c4110108908c2000154441190520210a0142200),(0x7913ceb593e8bd03514889e55f4c93639759259376fb3230720c9a865196f27cc74c193b9b758265cc3f7b6a39d891145642471fe1a3e402ed12036d66f3fc532a7d00122732be1cd6f8a0d631223ddb153772d463789a2c383ce02e7842d163,0x88036081c60419a2c82401d04754b2b302101402821d5c654204040641a4c69d42c491108805a675482c4b1a3210132646402113b58224122512010966d1b044833550122312b410427aa086012a6ec1101538c042289a0c282ca02a5842d161),(0x557693cafd0fd9424efb95e75ddf8ed5bd78c8ecb52fa208a8d45cb3574ccaab77d93b1e650b4399e9518160864e914bee471a4d6078d8cd3710b8c5462d299957d5836e24a95a7b253cdb2e6196070b78eaa32a2b4a267149c447650cd138a6,0x10c082401088400012d0c4008000004018ca8080142020182010002082500860100b028600824082a011044180428040210612040030c884904098c2002801191040822880a108c8040449084010010648220108084220210140474504110882),(0x9c642d62a2f2f7ba22bc048df67d49f5212576be5994f8cdc5e270babb8959b792802cb3e87f90d4054ae918d4ab1ce241d9cf541d5d16b72277276810cef58c9e0f2a3137066d66292bcd81a96583d025d9fd03afbb585aa2b81e898b063d44,0x8024093988519a8e002822a41919198600217873085849c0c483198871885081c08060615e498874054ab3104029780240914c50140c132321226228088464808a9608100702c12708ba84812c642a102598ac01a5195852a098180889063544),(0xd23eefb5d75806b89dcda38864b64661c9f5e2babc176a70b2d3a56f26f32e727e31fe7789e6e58a36284c9dbcb30e74d59821a10b67441120e71511dbf31ab50b42210b3baf1a3e4c47734dcff8958cfd1109f7ce27c18a062741ac46d7cd91,0x7413208444084451d48501104604c068b3980408840422121160844600658c78341c18180024668a9220480b8c940760b50821038273441010c51501633a18440140258228a50a1044455344031a81ae1001013e42228188062541a446c1c891),(0x44ee3263ec00331534507b30f50239085a477dc26fc97fafdd3677e1adedabf5a6627a917685fed951e16b05c441608531a6eebab7bf0ffa2c9d6923c000425ae070ded9cbf43ff0702d561449016826463c1cddf881bbc98109fdb0912bda0a,0x5c9601812402000310c10a308504200a188ca4d220b13a418220c4ac1700cc49329049900289169c4a408a09044020043184b638a739649c2011540242004250a0701ac901871eb02048c310010048264632184cec01aac801096da0110b580a),(0,0),(0x3ab08ab4b6d74c50e56bc9651caf5894b179e03465572acbdca5615696769c27053d6dc580568c9318a62a712d4d06df8fcf0933a8a96615b24c8891d85dee28deccf746ecda09546a23c7138dbf2215a9d969340b49504d34d905859a5a4fc,0x8020482e4971b288ed202044508b9ca5050108094844412451461041282e3192c9648008d0242841110660a6538444294c484083188002614b0e00011891a8820d8e45006648e00548a230c32acf32918089829300b41504d204901848a4a474),(0,0)]
def g191columns : IndexTree ColumnInfo := (.fork 19 (.fork 9 (.fork 4 (.leaf [(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5),(4,0,187,0,7)]) (.fork 2 (.leaf [(6,0,185,0,5),(8,0,183,0,8)]) (.leaf [(0,8,163,20,6),(10,0,181,0,5),(12,0,179,0,5)]))) (.fork 5 (.fork 2 (.leaf [(4,8,163,16,5),(14,0,177,0,4)]) (.leaf [(16,0,175,0,8),(0,16,166,9,6),(1,16,166,8,5)])) (.fork 2 (.leaf [(19,0,172,0,4),(24,0,167,0,7)]) (.leaf [(16,8,163,4,5),(8,16,166,1,5),(25,0,166,0,4)])))) (.fork 9 (.fork 4 (.leaf [(9,16,166,0,4),(20,8,163,0,4),(32,0,159,0,8),(1,32,30,128,5)]) (.fork 2 (.leaf [(35,0,156,0,4),(40,0,151,0,5)]) (.leaf [(48,0,143,0,5),(56,0,135,0,4),(128,0,63,0,8)]))) (.fork 5 (.fork 2 (.leaf [(130,0,61,0,5),(4,128,27,32,5)]) (.leaf [(136,0,55,0,5),(160,0,31,0,7),(128,32,30,1,5)])) (.fork 2 (.leaf [(32,128,27,4,5),(161,0,30,0,4)]) (.leaf [(129,32,30,0,4),(164,0,27,0,4),(36,128,27,0,4)])))))
def g191autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
def g191levels : Nat → Packing
  | 6 => g191l6
  | 7 => g191l7
  | 8 => g191l8
  | 9 => g191l9
  | 10 => g191l10
  | _ => emptyPacking
def g191index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 1 3 0 6 0 2 (key191l7)
  | 8 => lookupWord 17 64 6 11 5 2 (key191l8)
  | 9 => lookupWord 68 242 7 13 7 2 (key191l9)
  | 10 => lookupWord 9 46 4 10 4 2 (key191l10)
  | _ => fun _ => none
def g191 : Forest := ⟨191,10,fun j => g191samples[j]?.getD (0,0),g191columns,g191autos,g191levels,g191index⟩
def g251samples : Array (Bits × Bits) := #[(0x7c5b1073c997e37379da30f398119ee6fb6b9ec3f472bcb960b6e16b764eab308775a6f93b85666e9d3190b2b24d642ca5712b6de7ab3f7906c1699135342a691b3ae0a5aa4ef7bb316cf861cfcc30541d6a6cc4992b1a999615c8e8d911c1e1,0x2118206040004a02130d09680103a002090a061080141a8c00302460220208340600a251588102029c90b010225400202065234404234e080480294178042009180840240246b20a0024c060c50410001a48a084882a181106058840c1114140),(0xcce5a5f376b735aeaefe578ced15d32ecca61663a9af3bd1860bc21b19116b79223f9d41251db7915d2d676e62aaa4f819f9d341f91890478f7c179edecb18b88452ff03ce59b2503e9c1117dab8cd95ebc956b7a216470f30e3a2b3ec2d18bb,0x4842cb022293909020208080c0985104462050200a232050248f580a09002349282c0500277025a04229050a00aa2098018840837118b0c40a78400806c358a084123a0140090810bc8810142aa8e601010152222014470a10a222b02c2818b9),(0,0),(0x615f43b7c5899d56d0ed540d07e5651da134ed341e9bc1f74f237fc0ae8a342e74d0d54381c29b89aafb968c73300f2ad24e70d94c925aaf7c71d97b8e42ee34b1eb0d1c78f57307cdbb8ab0333b96f243ce283ea4988c525a6cf93575cb22d6,0x600508638c1a9f0381c44ce96aa5f40532886e32158a42c5402a7e6c4a89343c9410964685c08b09acb0120c353c06229a6c00c94c92de87444159522882ae0499430c1549527146cd2ac810537252985246622c84980c521a4cf835558922d2),(0x743743261165c64a5893c74b56706899b56f313d76fa70640bd59bea9f4cd6cd40c9796a92725dcea2baccf628444b5fc70e36349d152cf473b98c6d967cf8571ea4949a30a5a9a67c52f2db3fa12e66e966315b35ec80fa603e034c2e56ad7c,0x8e228200012500a04432a202145800c8c044118122412020998581138524c38140cb492802205484420a48e00002411d45001410a1402070b13084088559515204a0a28a24a10ca03050168720812c4621201151314480a8603203082a468c2c),(0xf3d9bb1a8ffcdc97c518eaf4c8cf14e122f0fafd99d5fdca7ef0f64eebb658a39d280ab679b66835384c18039df39cc970c09cab32e75b6d986af50aa1e14f67f56dcf6f41924d79e9e39f3990e7fa0a34138f4a5e417d209f607f101fc4fe09,0x9201861738918010c41062040c8818244620088911c0e1638783100880a45083c120082600262524204640020401ded90000982b30080131d06c4002816148a041658f0100904561e8880e0910f0e60220020e2216414120916065101cc4aa09),(0x8c34b489b6743f0cbbb4f14fa7d16d9fa49b993f9ba2b3789eb911d5e1cd7a6f64e2a177140a8013c504eb6dd8b5e7f7e94f5a351463882a81261e97691b96dcefd6ddbc37c1e3432aa0876640524995f6a595fd43d7d81429dbe94302afe942,0x269c30c1984c0e0408d2577d35632830a8c6a4165540daa693102041644d9ca647426045188a80110514e824d9155760ee46136c04410a2a918614976910825e2b85c52c35a0b36b4200852245520814f6b484dd43c398142959c9430287e142),(0x1bb2ab4aa0e85ba9e596de5ec3ce129b01134cce9757f2d674620576a8bd96bf3a893c9457f0a28da9ccac591d7731877093a6c205d64d4c2bcaa6363cd0b55e770f7a466dfb2a9c82572d4ce3aa90cf64d9c30549ce2fe50b809671629a567c,0xd9639e04222012901869c59f133e18908110146a61f169c201c69140019863c2e851098d7d900098988b54119762026501322c440c64c4e0e9086343c860556368a70222d632a1a145321c6e30c00cc44fdf181498e2ec50a809261621a5474),(0,0)]
def g251columns : IndexTree ColumnInfo := (.leaf [(8,0,243,0,7)])
def g251autos : Array (List Nat) := #[[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index⟩
def g255samples : Array (Bits × Bits) := #[(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)]
def g255columns : IndexTree ColumnInfo := (.leaf [(64,0,191,0,11)])
def g255autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
def g255levels : Nat → Packing
  | _ => emptyPacking
def g255index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g255 : Forest := ⟨255,11,fun j => g255samples[j]?.getD (0,0),g255columns,g255autos,g255levels,g255index⟩
def key383l12 (i : Nat) : Nat := 0xf8400002630000023000000000000000000b83d5688000000000341000030000000000814000015d0000000210344000018d003b10000000000e080000000e70005c3803500091000000000008
def key383l11 (i : Nat) : Nat := 0x404c001fd7a0dd080d1200990f207c017043e0ac430a491c9aec7438f32422a414035a0e000e6f384202824e3e5491f317a0090ee161490000d0e481ce32000c4b9104c1860ad6100030920000000003c06000000722ae38f1200000035c780290bd08d23d219503209024ec0512fd44dc0985ef07266b48508d728f004824e9809324688ad260642ee33843c9e425582082c2260138002f8f81ac0c0002216a57414583e222000012800202204f00400024f34c01300e78608380c041012080080846040
def key383l10 (i : Nat) : Nat := 0x8a7028008f8208641c25de616202731427f0aa3ea6a9bc18603a40bac46606be46000184a7c7d25a0000000b98af69a264a6b01ac3b3a21709000001146294f5b28f5117b2b2368000000119a0000000503689a2858e10b056a96282c8039064ce4000005a1824c4b68b4a1ca0160003a96c1c5108908a005faaaa16a13000042ba8544116a040004b6aa18802880c23178071841517e2559911705a04117c6495c00000000085d314e242a96a0880000a01fc56687256502c84968668866a1180000003d68390f815a1fa922000012b8020000c2a6caf0234475dcf201fa032887c28e092c47a60725df80221bc02a000007a61e192100d1c1f61f683d817642e40874ab202e012c0cd05141d60b104cb094626909c0000000c0e573a858d7326a6285e00010ac0007468e22e50bc16f60921b5c8f41249001273800322800110cb04e0005728622182280ff076809bc29a93800081a596455d1053c0607cc3a5870000108081400524002801c04219100c0821c60cc13c0c2030a201001e00285000001f020030024000800c08280
def key383l9 (i : Nat) : Nat := 0x6977b1303806491384c288005f480044300b4273a470aef249bb09d0238c000000000000000603688ce51876813ab9e6c881d7b37687df408050502a181c84000606800000000000000424bbbaa9612800409100800346576b8a520800702905aa985610b9a10486080010008502020c0020a18085
def g383d8 (i : Nat) : Nat := 0x7c610014028800000000000000302080140040000000a09b827d78736e69645f5a55504b4637322d1e19140f0a0500cef45d94a2103afbaa93760801f7445d0744d03aaf69017618038fb68a9960d01ad76949760c01af34a89760c01af64289760c01adb6943760801aeb69037608018fb6683760801af94683760801afa42837608018ef690988ce009fcaa9190de009fa68a9944e009deaa99504e009deaa99520e009ee690988ce00be6690178ce00be6690918ce00be6690988ce00bf84a83784600bbc6989384600f749de3384600
def g383l8 : Packing := (25,4,6,0,3,8,0,g383d8)
def g383d9 (i : Nat) : Nat := 0x2dd0028c0601f18c02041010022160ac183c0004580028bb3c71c058816e807460680741c30700441602883bd0180c08009e92a09189248391a905315048c4c0a178c440a1c344e20480c5e3ec8c4124f1f67a1c70097c7d918050801b86cae3f18d8123489e81e3f187030392c68303e84a0683078305e30e0607e38f83c60f060a511f174250341f8c5e031010ee21078c3c161c0cee22050c28801004142c00504800c7c3000f402160a08ae97100120112003c70a082689408970b120030209083000c003000838e14007c610001c70838e1020020212004000023e3ec8cb8e14489e2f1a14a23e23d15c47a2b88f457115cca2f195c5e3ecf438e4f9debbcbf80ec1d2799709dd3b93626add2d9db38e63c8786afd5e3b876b2cad6ca75446864ec9992b24646c8990d60abf57bcf1dd3b7e6bccf98f3075e0b6565abd55ea85452734dc95d24a3b45a858ff9f13c6754e39b9356698cc18a2f85dcb916d2be568a61472724d08e918226438650b3138214370570800a4005ff65c1840f7fa2f442077fd9720d01dfe9bd1080dffa6537006ffd329bc017fd9704e009fe44a2e81ddf6541840f7ea300c2077bd94a2103ddeca51081cff6468840ffb20e89a07fd41844d03def4422681cff6241700f5fa2ec3007afc1761803d7e8cb0c01cff65d8100f7ea2ec08073fe99604039fe44a6e80cff65d834067fd32c1a03bdd8320d019fec4a0680cff64e884067fb121b8033fd9760c01dee9bb0600ef70dd830067fd32c1803bdd9760c01dee4bb0600ef7a65830077da6ec1003bec37608019fe44a6f005ef65037802fda521bc017f5190de00bfc8486f004ff22513802efb2a09c017f90904e00bfccba07007f644d03803fb20719c013fc988ce00bfcc9a03007fc406118027f93108c017f8894de00bfd4ca6f005fe46437802ff32e89c01ff11744e00bfc44a27005fea6513802ff32e09c017f99720e00fec89907005fe64483803fb26f19c01fd9138ce00bfc4c467007f645e33803fb02f19c01fd8918ce00fec4c467005fe64c81803fb46640c01ff11384600fed19c23005fe26211803fe26f08c01ff03784600ff849c23007fc8ce11803fe13108c013bd94a210397f4cb0c01cf7a6583006f73281bc017e9290de00bf88c86f005de65413802ef32a41c01fd23384600
def g383l9 : Packing := (91,3,6,5,3,11,0,g383d9)
def g383d10 (i : Nat) : Nat := 0xb1c029771ece80316e3a8b78f40771ca00d1002da03a69a8d16d01d28d4d3292968b98ba7f8c288f4271a30301042b0c2ce3d9d0c753d16f1a58de8639cbb8c715c8d44b554a1a9a3e0a89a12200921586544f91de7c3c6840c59058fc73e70a427a578082339c40459aa8af185209a7d34148d4cb55354aae60605689f215010071ece816c5e382c02c0800b78f67401b1c150a01655c62e06083462ae3d9d02d06c70541505820071ece801e380c14030a8b4a07c8d48497c63f8e66a4b4202e31fc73a14025b571ece863a00201e95c8d50005c7b3a084978e980d957652718d2b8da90a038f655cc3ed026a4b80d9d0683120b8d0ca07c4503e24b0080e3d9d0c73a100400171ece863a2041f8deb9e05d31c9dc29ad59e194d8397a571169d5a94d53c132d2591c5050edce08cf4b60acc9f89047f075c62859452044c3f83242b025c208114003ff45d03ffd1840fff06103ffe8840fff44d03ffd1700fff05c03ffd37407ff60d01ffc83407ff40d01ffe88407ff4dc01ffc37007ff4de00ffc37803ff44e00ffc13803ff8ce00ffe11802ffa2103fdd1340eff60403bfd83406ffa2101bfd83007fe40e00ff901803fe4de00ff837803fe44e00ff813803fe20e00ffa33803fe20600ffa11802bf61803bdd83006fb60801fda33803fc84600
def g383l10 : Packing := (41,2,6,7,3,12,0,g383d10)
def g383d11 (i : Nat) : Nat := 0x540b1d9a02e3804632e686a85e3b342382008507c4a8582c71cf98063b342397069da95ca003fe81ffc03ffa03ff007ff007fa00
def g383l11 : Packing := (6,1,6,6,3,8,0,g383d11)
def g383d12 (i : Nat) : Nat := 0x11b280e4ff
def g383l12 : Packing := (1,0,6,3,3,0,0,g383d12)
def g383samples : Array (Bits × Bits) := #[(0x22c0d3a3723e453b61b292904161c19166ba4156452239cb2ce776d1285888036922ca069735ba1c39466bb49cb80c880d6801ee650cd2ea8938a452f08d3169a1612a59384753bad95626662c63076161205bac29b905015369815a61884cb1,0x22a042a308281022412222104041018102a0455c0820218028210490004898014122a802062510400900403480940c80084001804506910881200012c0203148e041211030641239500420000c630440212052a0291101014268811220880c80),(0x3e4782180591e1e8ca415c93fb0e30440ddb7b080a80044a5e58703417b0ed0da2975b6df4e0151155ba1024096257dc7280e61c3739c9924483ab0a0d0a407f268250f5cf15b48886f76ba0ccf46838068d8de07060e07838bc1a040b61c283,0x9028018810161088ac0504223081040850928000290004c425070241b00400822080144b0c0241004a20000482053184202c40808184882448102000d0800b3040a404084018c8080110220c214483800898940502040781814120409604201),(0xc3b0d0243e2c92704a6d0bb89a642e3e324709614c855ba1b03c2574c53f0c84bca3b709607618aaaaca1686a79e094292d1a5b2e1a729d1ef4c761d2455891cd68664af136132ce19aaa19e6c55a2caed1460758145348a6cc923aa16a49516,0xc22070243c088a32102908b09820ae3610c20125cc051d809026055084360c62d8a3320940364922a8484682858e00c384d420b061233141a94434152055010c599024a50348105611a2a11e2441a2c2e41460350145348264c921aa12049512),(0x4138264952b1d12493a4452d72585b389605825093cff11edb60090262cf75191c382db2876b8a708e04945dba40fc5c0117030382d504a579e551698e39d387601c521a9a75d96750089c8958b895e01b82b803f01d0be08606741604bc230c,0x1080c0b03b031008084040c42504188060180103100c00a0a40008040890111041009902b010250040410442a404c140103030210c08ca050a00048c0a8c022200c1018d83149210000148108b815200b021800b00809600202141404b82204),(0x7a0c641d50044e150338db871c0d9c6d8b49b017941b1c71c485efc79a14e6ae159b09d8c200cd085276a758cd18f3623c4db7d00870524c281de7f5fe3e2adc1756b294808a0882ea6a1f2df107bc01d0df010f4d40469e2105ef94c107b239,0xd004201450464809021899a3188eb82288483003841b1c31c500f247991664ae92090048c000c90e723223084509b040f48cd45008304046281cf3843e140e8407928284000804822b6a8b24f004a801d0dd010f4440469e21056a80c1079039),(0xcc62da0a5fa8f5e2c996caf343c42faac6de9a345ff56a94813a6425060416282f4d23c281526277465dd835f65817a533b901ad51024edaaa84a94a69219208d911c25be8aad34a7f39eda22807bafd8e8540012ec5ecf42900c6dcd341c02,0x8452d0021128d5c8c9144a91d1c007ab845a00141d69e1982122246c02041428290423d28902225305595421e41c17a5023985a908040a15a0c4800269208200d9018058b1aa90485c38f99a2803baf58c8040010ec1ece00900c4d4d341002),(0xdaef1c77688221978d1e0c4ad4cf460c43747468370c9781a044ccfb808507cfc7550e6f05834be93d3c1e4e94918217a4e0da637baa95002472c84f89f63e421033ad28de7ab208228bfb0281a229d272553696158289b300da2c9976c32464,0x92e959624882001701040c005417432c02544069252c9701a0048cc280a00e56d4150e31071309c931151f4c9213080304e00a4233c09500a002c04d90b29c403071012c5a3a310c128ab91220a221c27244349605808983008a2c9966812464),(0,0),(0x941a1aee99450a81362f36506691ad42486aa7b56b55a36c2710c35afdccd2f0604110c2892f54d343a9228b60c516b3ea6e18394813263b179331842a516d8adc29c7c000c846f164b52014130d4016a078833106127956c94690a3b81ad1d8,0x4120210904c02803268a2402080b401402a07040a01006405204110294490a020401002d0205402c22800a1400c2280a20c04a14813021a0411310009012188c000460020c0069060300020050540108030832102126010c94480229002c198)]
def g383columns : IndexTree ColumnInfo := (.fork 29 (.fork 14 (.fork 7 (.fork 3 (.leaf [(1,0,382,0,9),(0,1,332,50,7),(2,0,381,0,9)]) (.leaf [(0,2,312,69,7),(3,0,380,0,6),(2,1,332,48,6),(1,2,312,68,6)])) (.fork 3 (.leaf [(4,0,379,0,11),(5,0,378,0,7),(7,0,376,0,5)]) (.leaf [(5,2,312,64,5),(8,0,375,0,9),(0,8,99,276,7),(12,0,371,0,8)]))) (.fork 7 (.fork 3 (.leaf [(13,0,354,0,4),(14,0,369,0,5),(16,0,367,0,11)]) (.leaf [(17,0,366,0,8),(18,0,365,0,7),(19,0,364,0,5),(18,1,332,32,5)])) (.fork 4 (.leaf [(24,0,359,0,8),(25,0,358,0,5),(28,0,355,0,7),(20,8,99,256,5)]) (.leaf [(32,0,351,0,11),(33,0,350,0,8),(32,1,332,18,6),(35,0,348,0,5)])))) (.fork 15 (.fork 7 (.fork 3 (.leaf [(34,1,332,16,5),(44,0,339,0,5),(49,0,334,0,7)]) (.leaf [(48,1,332,2,5),(33,16,326,8,5),(56,0,327,0,5),(64,0,319,0,11)])) (.fork 4 (.leaf [(65,0,318,0,7),(66,0,317,0,8),(67,0,316,0,5),(65,2,312,4,5)]) (.leaf [(70,0,313,0,7),(34,64,29,256,5),(256,0,127,0,9),(0,256,23,104,7)]))) (.fork 7 (.fork 3 (.leaf [(264,0,119,0,6),(256,8,99,20,6),(8,256,23,96,6)]) (.leaf [(268,0,115,0,5),(260,8,99,16,5),(280,0,103,0,5),(272,8,99,4,5)])) (.fork 4 (.leaf [(288,0,95,0,8),(289,0,94,0,5),(40,256,23,64,5),(304,0,79,0,5)]) (.leaf [(320,0,63,0,8),(322,0,61,0,5),(258,64,61,0,5),(352,0,31,0,7)])))))
def g383autos : Array (List Nat) := #[[],[84,131,98],[101,66,16],[100,131,82,16],[82,129,48],[101,100,131,98,129,48],[100,49,128],[101,84,131,66,49,128]]
def g383levels : Nat → Packing
  | 8 => g383l8
  | 9 => g383l9
  | 10 => g383l10
  | 11 => g383l11
  | 12 => g383l12
  | _ => emptyPacking
def g383index : Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 17 68 7 12 5 3 (key383l9)
  | 10 => lookupWord 57 200 7 14 7 3 (key383l10)
  | 11 => lookupWord 30 108 6 13 6 3 (key383l11)
  | 12 => lookupWord 6 61 1 10 3 3 (key383l12)
  | _ => fun _ => none
def g383 : Forest := ⟨383,12,fun j => g383samples[j]?.getD (0,0),g383columns,g383autos,g383levels,g383index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low3 : Lower (vars 3) (graphGoal 3) 1 := size_of (hints:=1) (by decide +kernel)
end PEqualNP.Outside.L_meta_2541.SignedProof

namespace PEqualNP.Outside.L_meta_2541.SignedProof
def maps3 : List (Nat × List Nat) := []
def known3 := extendKnown [] 1 maps3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid3 : Known known3 := extendKnown_ok baseKnown low3 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low7 : Lower (vars 7) (graphGoal 7) 2 := size_of (hints:=257) (by decide +kernel)
def maps7 : List (Nat × List Nat) := []
def known7 := extendKnown known3 2 maps7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid7 : Known known7 := extendKnown_ok valid3 low7 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom15 : graphValid g15 (boundsBefore known7) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s15_3_0 : block g15 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl15_3 : block g15 3 0 1 = true := s15_3_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables15 : checkedTables g15 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g15 0 0 0 = true)
  · exact (rfl : block g15 1 0 0 = true)
  · exact (rfl : block g15 2 0 0 = true)
  · exact bl15_3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low15 : Lower (vars 15) (graphGoal 15) 4 :=
  lower_forest (g:=g15) (i:=0) (hints:=8449) (before_sound known7 valid7) geom15 tables15 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps15 : List (Nat × List Nat) := [(15,[]),(23,[32,67]),(27,[16,66]),(29,[65,50]),(30,[64,65,66,67]),(39,[32,67,84]),(57,[32,65,82,83]),(78,[64,33,67,84,101]),(99,[16,33,66,83,100,101]),(135,[67,84,101,118]),(156,[64,81,83,101,118]),(163,[16,66,83,100,101,118]),(165,[65,50,83,100,101,118]),(166,[64,65,66,83,100,118]),(172,[64,81,82,67,100,101,118]),(177,[16,65,82,99,118]),(198,[64,83,100,117]),(281,[65,82,83,101,118,135]),(305,[16,65,82,99,118,135]),(312,[64,81,98,83,118,135]),(326,[64,66,83,100,117,135]),(330,[64,65,82,100,117,135]),(332,[64,81,66,83,100,117,118,135]),(344,[64,81,98,83,117,118,135]),(353,[65,82,99,116,117,135]),(354,[64,65,82,99,116,101,118,135]),(396,[64,81,82,83,100,117,134,135]),(424,[64,81,98,67,116,101,134]),(480,[64,81,98,115,132,101,134])]
def known15 := extendKnown known7 4 maps15
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid15 : Known known15 := extendKnown_ok valid7 low15 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low45 : Lower (vars 45) (graphGoal 45) 3 := size_of (hints:=8965) (by decide +kernel)
def maps45 : List (Nat × List Nat) := []
def known45 := extendKnown known15 3 maps45
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid45 : Known known45 := extendKnown_ok valid15 low45 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low51 : Lower (vars 51) (graphGoal 51) 3 := size_of (hints:=1) (by decide +kernel)
def maps51 : List (Nat × List Nat) := []
def known51 := extendKnown known45 3 maps51
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid51 : Known known51 := extendKnown_ok valid45 low51 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom31 : graphValid g31 (boundsBefore known51) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_0 : block g31 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_1 : block g31 5 1 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_5 : block g31 5 0 3 = true := (@block_merge g31 5 0 1 2 s31_5_0 s31_5_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_6_0 : block g31 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_6 : block g31 6 0 1 = true := s31_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables31 : checkedTables g31 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact (rfl : block g31 4 0 0 = true)
  · exact bl31_5
  · exact bl31_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low31 : Lower (vars 31) (graphGoal 31) 7 :=
  lower_forest (g:=g31) (i:=0) (hints:=8449) (before_sound known51 valid51) geom31 tables31 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps31 : List (Nat × List Nat) := [(31,[]),(167,[83,100,101,118]),(313,[81,98,99,84,118,135]),(334,[80,81,82,83,100,117,135]),(355,[82,99,116,117,118,135]),(428,[80,97,82,99,116,101,134])]
def known31 := extendKnown known51 7 maps31
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid31 : Known known31 := extendKnown_ok valid51 low31 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47 : Lower (vars 47) (graphGoal 47) 5 :=
  lower_discard (g:=g47) (ci:=(8,0,39,0,4)) (hints:=8449) (before_sound known31 valid31) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps47 : List (Nat × List Nat) := [(47,[]),(61,[65,50]),(94,[64,65,66,67,101]),(151,[67,84,101,118]),(173,[48,65,50,83,100,118]),(181,[65,50,99,84,118]),(185,[16,65,98,83,101,118]),(188,[64,97,98,67,84,118]),(227,[16,66,99,116,117,118]),(230,[64,65,66,99,116,101]),(301,[48,65,82,100,118,135]),(331,[80,81,66,100,117,118,135]),(339,[66,99,84,117,118,135]),(345,[80,65,98,67,84,117,118,135]),(346,[64,49,98,67,84,117,135]),(358,[64,65,82,99,116,101,118,135]),(369,[65,98,115,84,118,135]),(422,[64,81,66,99,116,117,134]),(440,[64,97,114,67,84,117,134]),(454,[64,66,99,116,133,118,135]),(460,[64,97,66,99,116,133,135]),(482,[64,49,98,115,132,133,135]),(484,[64,97,82,115,132,101,118,135])]
def known47 := extendKnown known31 5 maps47
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47 : Known known47 := extendKnown_ok valid31 low47 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low55 : Lower (vars 55) (graphGoal 55) 5 :=
  lower_discard (g:=g55) (ci:=(16,0,39,0,4)) (hints:=257) (before_sound known47 valid47) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps55 : List (Nat × List Nat) := [(55,[]),(79,[64,65,66,67,101]),(103,[16,66,100,101]),(115,[50,99]),(143,[32,67,101,118]),(174,[48,65,50,83,100,118]),(179,[65,50,99,84,118]),(206,[48,50,67,100,117]),(286,[48,33,101,118,135]),(316,[48,97,66,84,118,135]),(327,[64,65,82,100,117,135]),(348,[48,97,66,84,117,118,135]),(364,[48,97,99,116,118,135]),(376,[48,97,114,99,116,118,135]),(398,[48,65,50,67,100,117,134]),(433,[16,49,98,115,100,117,134,135])]
def known55 := extendKnown known47 5 maps55
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid55 : Known known55 := extendKnown_ok valid47 low55 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63 : Lower (vars 63) (graphGoal 63) 8 :=
  lower_discard (g:=g63) (ci:=(32,0,31,0,7)) (hints:=8449) (before_sound known55 valid55) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps63 : List (Nat × List Nat) := [(63,[]),(95,[16,66,101]),(159,[32,67,101,118]),(175,[32,83,100,118]),(183,[99,84,118]),(231,[16,66,99,116,117,118]),(317,[32,97,82,83,100,118,135]),(350,[96,33,99,84,117,135]),(359,[16,82,99,116,118,135]),(366,[96,49,116,118,135]),(371,[98,115,84,135]),(377,[48,97,114,99,116,117,118,135]),(429,[80,97,116,134,135]),(430,[96,81,98,83,116,134]),(441,[16,97,114,116,101,134,135]),(444,[96,113,114,99,84,101,134]),(462,[96,98,67,116,133,135]),(492,[96,113,115,132,133,134])]
def known63 := extendKnown known55 8 maps63
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid63 : Known known63 := extendKnown_ok valid55 low63 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom111 : graphValid g111 (boundsBefore known63) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s111_6_0 : block g111 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl111_6 : block g111 6 0 1 = true := s111_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables111 : checkedTables g111 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0 = true)
  · exact (rfl : block g111 1 0 0 = true)
  · exact (rfl : block g111 2 0 0 = true)
  · exact (rfl : block g111 3 0 0 = true)
  · exact (rfl : block g111 4 0 0 = true)
  · exact (rfl : block g111 5 0 0 = true)
  · exact bl111_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low111 : Lower (vars 111) (graphGoal 111) 7 :=
  lower_forest (g:=g111) (i:=0) (hints:=16785665) (before_sound known63 valid63) geom111 tables111 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps111 : List (Nat × List Nat) := [(187,[16,97,66,83,100,101,118]),(190,[64,97,98,67,84,118]),(215,[67,84,117]),(222,[64,65,66,67,117,118]),(238,[64,65,66,99,116,101]),(243,[16,66,115,100,101]),(318,[64,81,66,83,100,118,135]),(349,[80,65,98,67,84,117,118,135]),(365,[48,65,82,116,135]),(378,[64,49,114,67,84,101,118,135]),(413,[48,65,50,67,117,134]),(437,[65,50,115,84,134]),(455,[96,98,67,116,133,135]),(476,[64,113,66,115,100,133,118,135]),(490,[64,49,114,99,132,133,118,135]),(497,[65,114,131,84,134,135]),(504,[64,113,130,67,84,133,135])]
def known111 := extendKnown known63 7 maps111
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid111 : Known known111 := extendKnown_ok valid63 low111 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low119 : Lower (vars 119) (graphGoal 119) 6 :=
  lower_discard (g:=g119) (ci:=(4,0,115,0,5)) (hints:=16777473) (before_sound known111 valid111) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps119 : List (Nat × List Nat) := [(119,[]),(207,[64,65,66,67,117,118]),(380,[48,113,66,84,101,135]),(414,[48,65,50,67,117,134])]
def known119 := extendKnown known111 6 maps119
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid119 : Known known119 := extendKnown_ok valid111 low119 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom189 : graphValid g189 (boundsBefore known119) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_0 : block g189 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_1 : block g189 6 1 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_6 : block g189 6 0 3 = true := (@block_merge g189 6 0 1 2 s189_6_0 s189_6_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_7_0 : block g189 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_7 : block g189 7 0 1 = true := s189_7_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables189 : checkedTables g189 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g189 0 0 0 = true)
  · exact (rfl : block g189 1 0 0 = true)
  · exact (rfl : block g189 2 0 0 = true)
  · exact (rfl : block g189 3 0 0 = true)
  · exact (rfl : block g189 4 0 0 = true)
  · exact (rfl : block g189 5 0 0 = true)
  · exact bl189_6
  · exact bl189_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low189 : Lower (vars 189) (graphGoal 189) 8 :=
  lower_forest (g:=g189) (i:=0) (hints:=536879876) (before_sound known119 valid119) geom189 tables189 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps189 : List (Nat × List Nat) := [(189,[]),(347,[65,66,115,84,101,118,135]),(486,[16,66,99,132,133,134,135])]
def known189 := extendKnown known119 8 maps189
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid189 : Known known189 := extendKnown_ok valid119 low189 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low250 : Lower (vars 250) (graphGoal 250) 5 := size_of (hints:=1366507616) (by decide +kernel)
def maps250 : List (Nat × List Nat) := []
def known250 := extendKnown known189 5 maps250
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid250 : Known known250 := extendKnown_ok valid189 low250 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low127 : Lower (vars 127) (graphGoal 127) 9 :=
  lower_discard (g:=g127) (ci:=(32,0,95,0,8)) (hints:=16785665) (before_sound known250 valid250) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps127 : List (Nat × List Nat) := [(127,[]),(223,[64,65,66,67,117,118]),(247,[115,84]),(375,[98,115,84,135]),(381,[48,113,82,135]),(382,[112,49,66,115,84,101,135]),(415,[48,65,50,67,117,134]),(446,[112,81,114,83,100,134,135]),(478,[112,65,114,67,100,133,135]),(493,[80,113,50,132,135]),(499,[65,114,131,84,134,135]),(505,[64,113,130,131,132,133,135]),(508,[112,129,66,115,84])]
def known127 := extendKnown known250 9 maps127
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid127 : Known known127 := extendKnown_ok valid250 low127 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom191 : graphValid g191 (boundsBefore known127) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_6_0 : block g191 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_6 : block g191 6 0 1 = true := s191_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_0 : block g191 7 0 13=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_1 : block g191 7 13 15=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_7 : block g191 7 0 28 = true := (@block_merge g191 7 0 13 15 s191_7_0 s191_7_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_0 : block g191 8 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_1 : block g191 8 7 61=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_2 : block g191 8 68 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_8 : block g191 8 0 100 = true := (@block_merge g191 8 0 68 32 (@block_merge g191 8 0 7 61 s191_8_0 s191_8_1) s191_8_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_0 : block g191 9 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_1 : block g191 9 3 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_9 : block g191 9 0 12 = true := (@block_merge g191 9 0 3 9 s191_9_0 s191_9_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_10_0 : block g191 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_10 : block g191 10 0 1 = true := s191_10_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables191 : checkedTables g191 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g191 0 0 0 = true)
  · exact (rfl : block g191 1 0 0 = true)
  · exact (rfl : block g191 2 0 0 = true)
  · exact (rfl : block g191 3 0 0 = true)
  · exact (rfl : block g191 4 0 0 = true)
  · exact (rfl : block g191 5 0 0 = true)
  · exact bl191_6
  · exact bl191_7
  · exact bl191_8
  · exact bl191_9
  · exact bl191_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low191 : Lower (vars 191) (graphGoal 191) 11 :=
  lower_forest (g:=g191) (i:=0) (hints:=536879361) (before_sound known127 valid127) geom191 tables191 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps191 : List (Nat × List Nat) := [(191,[]),(319,[65,50,135]),(351,[64,65,66,67,101,135]),(367,[80,81,66,100,117,118,135]),(379,[81,98,118,135]),(431,[48,65,50,83,100,134,135]),(445,[48,97,82,134]),(487,[16,66,99,132,133,134,135]),(494,[96,65,98,67,132,117,134])]
def known191 := extendKnown known127 11 maps191
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid191 : Known known191 := extendKnown_ok valid127 low191 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low251 : Lower (vars 251) (graphGoal 251) 8 :=
  lower_discard (g:=g251) (ci:=(8,0,243,0,7)) (hints:=1358970881) (before_sound known191 valid191) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps251 : List (Nat × List Nat) := [(251,[]),(254,[32,67,117]),(471,[16,66,67,100,133,134,135]),(501,[16,33,50,131,100,133,118]),(506,[32,49,130,100])]
def known251 := extendKnown known191 8 maps251
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid251 : Known known251 := extendKnown_ok valid191 low251 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower (vars 255) (graphGoal 255) 12 :=
  lower_discard (g:=g255) (ci:=(64,0,191,0,11)) (hints:=553656577) (before_sound known251 valid251) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps255 : List (Nat × List Nat) := [(255,[]),(479,[64,65,66,67,133,134,135]),(503,[16,66,131,100,101,135]),(507,[81,130,118]),(509,[48,129,82]),(510,[128,65,130,67,100,117])]
def known255 := extendKnown known251 12 maps255
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known known255 := extendKnown_ok valid251 low255 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom383 : graphValid g383 (boundsBefore known255) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_0 : block g383 8 0 23=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_1 : block g383 8 23 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_8 : block g383 8 0 25 = true := (@block_merge g383 8 0 23 2 s383_8_0 s383_8_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_0 : block g383 9 0 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_1 : block g383 9 9 75=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_2 : block g383 9 84 7=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_9 : block g383 9 0 91 = true := (@block_merge g383 9 0 84 7 (@block_merge g383 9 0 9 75 s383_9_0 s383_9_1) s383_9_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_0 : block g383 10 0 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_1 : block g383 10 5 16=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_2 : block g383 10 21 20=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_10 : block g383 10 0 41 = true := (@block_merge g383 10 0 21 20 (@block_merge g383 10 0 5 16 s383_10_0 s383_10_1) s383_10_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_0 : block g383 11 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_1 : block g383 11 1 5=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_11 : block g383 11 0 6 = true := (@block_merge g383 11 0 1 5 s383_11_0 s383_11_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_12_0 : block g383 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_12 : block g383 12 0 1 = true := s383_12_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables383 : checkedTables g383 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g383 0 0 0 = true)
  · exact (rfl : block g383 1 0 0 = true)
  · exact (rfl : block g383 2 0 0 = true)
  · exact (rfl : block g383 3 0 0 = true)
  · exact (rfl : block g383 4 0 0 = true)
  · exact (rfl : block g383 5 0 0 = true)
  · exact (rfl : block g383 6 0 0 = true)
  · exact (rfl : block g383 7 0 0 = true)
  · exact bl383_8
  · exact bl383_9
  · exact bl383_10
  · exact bl383_11
  · exact bl383_12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low383 : Lower (vars 383) (graphGoal 383) 13 :=
  lower_forest (g:=g383) (i:=0) (hints:=12901687553) (before_sound known255 valid255) geom383 tables383 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps383 : List (Nat × List Nat) := [(383,[]),(447,[65,50,131,84,118,135]),(495,[80,81,82,83,116,133,118])]
def known383 := extendKnown known255 13 maps383
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid383 : Known known383 := extendKnown_ok valid255 low383 (by decide +kernel)
def hashdeadl14 (i : Nat) : Nat := 0x4592c8500000000002800049a6c68a83340e9800000aa00684000000054a001bcc7001e180000682000000000000001d46a1840000003a00000001c
def hashdeadl13 (i : Nat) : Nat := 0x301a0007b2f00e0aa2992094818000e2e0000000269e056438000000000d33e40e4a200074d00000000000003b10001e0240a9bd45d962582900000000000001430001e1400000fc03b84a000614e69108a1108000810000d04c9d0000000408800000160f24180010b9d040003080001e0c000000000001997f401183740ee12000000000080d312c00102c00000000012070000000001d35000308c000a4c0001b30000000cb3800183000070f0000001abcc008002c8cc133000000000000000000000020b000000064ec0a00000f8000cc5000105d8204160001a38001c1c467309c000000a7700000016de30f80000008380b08e000d3001
def hashdeadl12 (i : Nat) : Nat := (if i<1 then 0x7b02c3200425d610a000042a0327300000000106b33757005e04600006037d811679d009461963480703e1077f067f2582384275d80a540a20109b59b4006305d00000000ab6dfb0bf59ec084c806986b30597776440b146b100c50a956520000878e0000747c463e108bc029e7600000395ef090d06800000000f0550000d0b1e4af00000000f324d141840ca4380000000051505017000067300000e779907b0000e77730641201ea62a089a48ff0924111e9a7a041b2a180aee462f29d9b47b01eb0427030e02a5973605b9086f08d5081d04bb014363000006038c0b6d110106cc731308e0023a07fb1305601ba1839b4c088a10b88011043e427e75a600831464016903d3ba52b1ec095000ec050b011b0730478f11a0000755e331ef63db004a00a000069a91680e225f60f90092a9d0000764650a40000c591f95ac03baa33c5a1283d11871a6d2772c01c1057280f201f5012328b908232a5505e000fe02b507cf0809817c267c05c9528506d997696872194b206264030ad402d007d586d7228701d30605840f67838625a51443ce034d47ed45f704cb08730a1794e1252000070330000b56f0000b0b4000000000000a842e047609d406ae26b67b08a4de12aa0a34019000000000000b664342c50b50000c0af924dc9aa401870366002b26d00000000841e0000000060986614000000000000783ae10d980ee051d0ab4022a615808f0000a0832619a148d81500007000e007d616b032d01b483f163f00104028276b2015141030631049a027580cd0a7a05ab977802fb09ff07a97899053b0a80816e83be0790a1b809b8b460a4f0000178b0000847be03cf139a1170000b07850b3605408416262696b908af0aa7b1f5b446070d024601a42492101d496f4b4e035922127ab0000e18600008284831c00440000f031500310656013b071b045b25b4113766b5b4c6b0800008291b4888a50000000000000e38b0000225eb04d807230618425c0b097ae226f809e00000000f00d93480485e88728040000b11c3039204e9432711f445c905f004a300b97ada05680211292f09a7b1a696f3106704f19748066703f00000204d074ba20a118f025458794596091a06f000065946020913b783e342dd08c819b5b452076c21dc075e0991a4a183c3b19d7a750a68058c8379643a487b408d0523762d062b422e0b2d47fc0ac224a46231a5dca3b6069a4390000768a5433e07e0000da410b00003102090604000a010a1f88080000080d030b0c310304001300040113030203141f0c0001000232030b0801010a010007110002020208010605020401010119010b0304070203070506000210070d110100150b0a0504051d050002020b05000c0402003d0e1500260200020108040b03090500060204000d0602010100180501000001030f04 else 0xe0a0512830933085c048e216509713746026a02ec09cb040548400000268f701103ac254729fc29e8096145a39ab47552144806e00019612b7b4491ea44bc1)
def hashdeadl11 (i : Nat) : Nat := 0x5b144463e05aea749a36008e0000f05f008fc82400000000057a08357304bb42c02b0000807cd1701823000007095811411b96631031e07218223334c77b980e8010305dd000180820521064ca3ef0420000409b626cd483a833f03ac022e048a008f80a513f0000db73410f3393ca38834018881012b081c465a02c6142704300002631809700000000715300007115b00dd054b2886014000054161b183099000000000129f0870000a24110110427972915960000477d5b457113518aa01a00007134a023d08a1053002d678ef06b604a6076520f5468b025698fe62d5060c1370000e07eb793c95be02a510198285417000000000000000000005b72220ea00f9098e036e09602120000503908396112556c56084a3a211d0342f0784635707b4293308d0624205556235211962a72516903a0190235010e7765e07d5784f16feb3c248834149073d088b0134091f720f0803275f0052809446ed494b01b1b0305939136b20cf495111aba390000db890950e9807026e609a0205015880ba66b8778d4967988f077f007110cd289d0160000e278401d0000000000000000f032027400000000a08c6209804c4030102eb368a33f3b1d798e0000538a70215061a44e228300000000000000000000d01710838075e4517067406f00000000609a00003253a089a4002093b00a8125000090790000c0599583180c00000000c0411830f1160047224900000000906992725046700b000050511a67544b00000407c35bb06d0000504d3821ca470002762e0000cb1760948827b10a603b4009e06552019464444f9688a0286169097ab82524185057db2feb3d000e6303670ac01e70822426b090d664c05cf764008be03c365d6a2549347068706a71244461f086277c5780380d698dd120b27c20626037d807f403502fe1110000ea6e5071301cb0388044704f411c809595011003b20deb1a98372208b0561092820a91190049704bb03ec070670890335001a03f64504063613c50294b430832441aba46e146c8120193598c103df8314066401fd460e0745084044c100c7760b24b824f4006205b0000563070507a7c9058000000006a440000506e3040e97d006cd027646a6207807fb0450138e56fa018704e8482e0356085662f762c5b3be05eb81f1004f836000000000000000046203a6ac89692730000b034807a613d00008145702433536a79b0407805012a04e80082c50a0c0e782286421a0e4c00400004833a1491a02243880c0851202004211c6408c1835c192e081800c39681005000c04e408002001860c34c8040000000400008087400400100892c38005148410524200800478080001438126000000020022
def hashdeadl10 (i : Nat) : Nat := 0x1c05302000382d2ecf474c3a08f618409ea54931a0a2272b385214e934380040192451090d15cc0564307983441ce005970002c06068f08a82680cc070001a2c5d4a1440400018207150002808001022205d856c41e1700072d518800084a2900000a334a12801820030b1a27
def hashdeadl9 (i : Nat) : Nat := 0x202e0
def deadd8 (i : Nat) : Nat := 0xa24b7baf6624ad253281df927589c4d52540d02
def deadl8 : Packing := (2,6,7,0,4,3,0,deadd8)
def deadd9 (i : Nat) : Nat := 0x17a6100d01602e1f830400f202c200003405840f980801c0010720e8006a183c001d000f8007c00200001509fc5a0b0071b79b2bc5ba99429c459e8d258238d84a14078280a00a7becc495a4a6503c6fdb66689a4d50287fcbc661a544d029ef9c6aed1840d02bed9c626d3540d02ff49184d52540d02ff489c4d52540d02d7f11826d1540d02ffc1184951340d029f6cbc4a1354950195fdc7aed2564d01ff49384d52540901ff61384951540901ef4935496aa40d02df49b54951340d02f7493549503a6502bf62cc4951540901ef6125456aa40901f7612545502a6501fb61284612545600fbc1284612344e009dd9c7aed258ce009ee9c6aed1888a009df1c7aed2584600ff42558ce2284600
def deadl9 : Packing := (25,5,7,1,4,9,0,deadd9)
def deadd10 (i : Nat) : Nat := (if i<1 then 0x2693540b3fecd1349aa055ff26d1a4d502cffb30d2a26815ffabb4610340bfec8c26a81a05ff626d3540d02ffd23092a06817ff1184550340abff5da6b4ca059ff4d5a1a65029ff9569426a80cffdb8aa9354067fed95549aa03fdb4a13549501affb7092b2680e7fda849593407bf69424ac9a035ffaed2564d01cffab15532680e7fd25aa993406bfedc26ac92035ffaed3564901cffab0d1b2480e7fd38aa9924073fe9ad54c92037fe6e13540901fef2b09aa0480ffd9384d502406ffd5da6a81203ffa4e12540901ffe2708aa0480f7f95864d02406bff5da714ca03df74e135a6501affd769ad3280d7febb49699407bbe9aa4b4ca035ff6e123a6501efda5091d3280d7fdb548e99406bff5da474ca039ef495a4a65038ffb63553308167f9b0aa998408bff5dd54cc2053bf6daaa461028ffb6a4d2268157fabb6610340bbf4cc24a81a055fe26d1540d02cff33155206816fd935aa90340b7f492d5481a057f66d51340d02ff924a89a06816fdaaa44d0340b3fcd42074ca05df64d503a6502efd24a81d328157fabb40e9940bbec89a074ca059fd461a1a65029bfb6f5524a80c7febb6a1934063fedc554c9a031ff6d6aa64d01cf7b695532680c7fdb2aa9934073fcd8554c9a031ffaeda8649018ffb6ad1b2480c7febb68d92406ff55da4a81203fda4d52540901fee34a8aa0480f7e92564d02406bfd5db2681203bfa496aa40901dfe22b5520480e7f993aa902407bf492a054ca03dfc45502a65019ff36755251004ff9b1aa928802ff55da5092c01efa4a11849600dfd2515524b007f692849515803fb88c24a8ac017deaed2545600def55492a2b004ffabb6a123802ff55da5091c01efa4a11848e00dfd25155247004ffabb6a1138027fc55a5089c01afe6a12844e00bfe5768c227007bf128461138027fd5db4a89c01bde6952544e00dfe23155227004ff9b8aa9138027fcdad5489c013fe6caaa44e00ff925091a27007fd11848d13802fed5da4689c01bf6aa92344e00bfb57692c67005fdabb45633803fac92a2b19c013feaeda844a009ff370d2a25004ffabb695128027fcdc346894013fe6d5a344a009ff576d1a25006ff1a844d12802ff95da2689401bf66963344a00dfe22755225006fda33aa912802ff55da71114017faaed1888a00bfd3709ac45007fc9384d622802ff55da6b114017fa6e11388a00ffc23089c45007bea8844e22802ff4daa27114017faaed1388a00bfe5769c423007fd1384d611802ff95da6b08c017fcaed2584600fee26a92c23005ff1b848e11803ff09424708c017fc6d52384600bfe57691c23007fd1588ce11803fe89446708c01ff44963384600ffc27111423007fe13588a11803fa49aa4a81a05fd849515409019bf36f5524b007bd2888ce11803df14444508c01ff08ce2284600 else 0x4000888405e986c113905805080340b02e1f06087905c2003f080d05c2010004400c0288128f50060048004020800804100127c503a3f6c170230c990618643002074409038882341900e30020304004060800870140c00228180045c08224a09086c45817020801a183810008ad48702001100108e2b0c1c0800456383810230b0200117dff6de0be2c10281f00a20021f8a108140c707c503e3f8bed83901520010dd505020c988c1183426000e000e00086905c20a40d058002020340034003c1834002fd2040bdb798060306e1b00c84f01a5f8a10bc3024202bf0c090605c00880505210010fc506e1cc0693effc5f6de600097e28190cc11092183f1414080603412860a40cc6004380038003800340034003c003c0020e00107000f000801c0020e00100f78ee2192287800ec3041c003c00361820e001f8a1e001e001e00100000b0411ef1dc4377ae886cc5917b60fc50f000d8e083e2840000016a420f6c1b1c100000b521002c30416383f1420003e284000100c4aca220cd523db61a02c91b20b40600a0dbf169c61a02c9f6de60578fe2fb6f303f8bedbcc0fe2fb6f303d0acfaceacb9c93c83c68c63c53c38c1dc02bd1bb6b9bb96b70b4ab24b09aeeac8aada92a77a5ca41a31a169fb9eb9e69e19d19b69a698b97096094593591a8ff8c38a889887284c81b80b7f07bf7af79f78f7747597497397297197096f96de6b867c64b62560a5ef5df5ae5725415315164fb4d54c54b54a549548547546545545044043b42b41b4164114013fc3ec3e73cc3a639639138137136135c34c33c32c31c30c3073022fd2f82e82cd2b229728727726725725224223d23823322e2292192142041f41ef1ea1e51e01d01cb1c61b61b11a119118c18718217216d16810009807204c026000affd7692d3281defdb6)
def deadl10 : Packing := (156,4,7,5,4,12,0,deadd10)
def deadd11 (i : Nat) : Nat := (if i<1 then 0x86120d08111f407ad1db072b1c206d11ab867718d8613174859115b85231388497118042910183c50e603570c082b709d822b07a8195055010902a80410003ffd1849503fff6692540fffd2546503fff4613540bffd9a4d502fff2693540bffd1a4d502fff4619340bffd3546502fff4d69940bffd9a4e101fff6a135407ffd284d501fff4a935407ffd9a4d501fffaa935407ffd3849501fff4e925407ffd9a49501fff56123407ffd9a48d01fff56193407ffd2864d01fff49593407ffd5864901fff4e192407ffd3564901bff6a11940f7fd9846503dff6551940effeaa46503dff4a51940f7fd25a6503bffaa99840b7fd1a66102dffaa99840b7fd9a46102bffaa91840bbfd9846102dff6619340affda564d02dff6559340affeaa64d02bff6951340bfdd9344d02ffe6a10340bff99840d02ffe4610340bff9a540d02ffe6550340bff91540d02ffe4690340affda846502dff6611940affda346502dff64d1940bff90346502dff6629940b7fd93a6502ffe40e9940b7fd18a6502dff4d69940b7fd13a6502dff66935406ffeaa4d501dff66925406ffeaa49501fdf4d525406ffda864d01dff66193406ffeaa64d01dff561934077fda864d01dff4a1934077fda564d01dff495934077fd2a64d01dffaa993406ffda864901dff66192406ffda564901dff65592406ffda364901dff64d924077fd3864901dff6a1924077fd3564901dff68d92407ff95840901ffe4e102407ff9a840901ffe66102407ff93540901ffe69502407ff99540901ffe68d02407ff99340901dff4e2994077fd35a6501dff496994077fd23a6501ffe4e928803ff91a4a200ffeaa928803ff9a849600ffe46125803ff93a49600ffe46925803ff92845600ffe4e915803ff92a45600ffe6a123803ff91848e00ffe69523803ff91548e00ffe46923803ff9a844e00ffe4a113803ff9a544e00ffe49513803ff92a44e00ffeaa913803ff95844a00ffe4e112803ff9a844a00ffe4d512803ff9a544a00ffe68d128027feaa661029ff2693540a7fc9a44d02dfe6610340bfd93540d02ffa4950340affaaa40d02ff644d0340a7fda8a6502dfe40e9940a7fda3a65029ff6869940a7fda864d019ffaa9934067fda8649019ff68d924067feaa64901ffa49502407ff11540901dfe64d02406ffaaa40901dfe40a99406ffaaa4a200ffa4a125802ffaaa49600bfeaa915803f792545600bfe6a123803fe92848e00bfeaa923802ff9a844e00ffc46113802ff9a544e00bfeaa913803fd92344e00ff649633803fd9158ce00bfe6a112802ff9a544a00bfe68d12803ff11344a00ff68cd12802ffaaa44a00ffa4e222803fe91888a00ffa4d622803fe91388a00ffc4e211803ff13584600ffc49611803ff123846009ef6929940fbea8888a00ff48ce11803fe22284600 else (if i<2 then 0x6718d1b071686b63b38c6ac837ab208143ea5f4a804c20460a84911c7405186a093027a82ae19d57d066c694fa70dcc0ac4ea478ce31a1ecaeaf303c8c241ac2f19b38c69c83fbee47302190238ea2305424c6856399d2085637d12388c0c16cbeff1d208076416c80b40c0049e29d5208144b23f46802b201800c183275231bc58d5919c2ba9ed854030806003067bf9c352078df64634afd056e600c20020b418eaf319c182b832c8683382f1c2de703e3ac80ac412003efc19433aad06707f7f38754282036168bdf159a0ce09fa590158824f17a919786904bef86bc33ab209458f7dd8e39c8904deff5232b9120958e0b701b7e8611b1e288d8776dd9609e2b1c2f1582105b80098e0b90124824976d090cd009250909820be81c002d484d8f144c3068ea08444c12222609117812260911961224208de83785dd4e900b63480dfc5edb981b80c307224fbfd4f301f09477d2a0d202e2010188cddb353cc69017202256222f7fb60add5a80164f6c116903054660bb98d200c6e0e18f8afa73037818602100ed9a0d20beff8bdb752d00186f7fc5ea78e6e01e33bfe2f534770c056718d202388c2401066f7fc5ea68ee1b388131a6862ef8df646718d182bf7fa963ac8ce31a3fbfe2f6dd4f31c70187010d8f7c2b7561a05a04ce121581816fbfdb3530d74005590a1982b682c8ce0be2f6dcc0184f14410307c705b875e98d59067d2d5c686717058176d8d1b06f7c92f17b6e602d3634e457030b7007d2a0b20be2be9500fdf0b7b6c68d029b1803bfe2d415c1bc57d2a01fbfc3600ead415c1bdf363c5c6a8eae0d8d3915c0fdfe0b00ed9a9a81c83fbfc3600ead40dc1ba9e3b0e77f1ab22b839c4d4e356457053ab00682c8ae0bdb341640fdfea700682c8ae0dd49c58d1bc4ea782c02c87d1a03753c751d873bf64634dc23dfe0a86c03b6755a03fbfd4e0164340dc1a82ea786c03c57d1a03fbfc36015c3aad01bdfe3a8ec3ab86a71a7211eff5380570d03906f7fc5edba9e1b82040ec751d87590fa7538d71ddc2586a198ec1bdff16b8ea71ae195efb915c7ab8d74068ed23878d423198bda2f18b3a2a189fa24788e221f881a1e387521a785ea14384820fd83ba0cb82a2071816203f8099ff97ee1f8b7d29f137b21e9179b9e377829ddd76c1d8d7581d3373c9cb17239c6170f9bfd6f41ba36e01b536c99af96b31a9f69c9a4568619f5665990f63618ab610981f5f517935dc17435c0969959b163558495c7566954f54b14f552f949151914374f393a14ce130b4b2929349c124347e11cb46c9185456112143a90a941c9063415103b4088ff53f70fc33ea8f9b3e30f7d3d68f4b3cc8f233c50f053bd8edd3b38eb53a70e8339d0e5b3930e3d37a0da73570d2f3368c7b3160c0d2f30b952d50b132af8a3727d89ab2580901226 else 0x6c244e0445e2e80648bc5050262048e47300a0565ed8f60346f5d8ae98260a0c0068580a0c27015b807c906026158e08c030604c2b2a82103cee10cc378bc503c5a1a381a3a2d03cb121b082409e29104f14d80b00b29b02601632490481068e0401093981802127303093987200a0aca00c1820060c1003060ba9e62b81ec8b40d15c753cc0a26ae1d5e606624740ac47cc0483c9bdf72398ae02b28b1eff6cec705e2c44719c65bd0520ccbd4b702a0c67030651f4282f8a37f6c0f90083dbc507c95c01a2901847d2a015c7efbab500764fd1d5a800524460a84613d40171bdf12bb67568e07cc1703e060df4d22a00b883dd40220c2777c2ed22a06e0defe90110884fd1d5a800526915008831e748a802e219d5c0560f91f4ea40c1509ef89ad00884fd0566800c25702b3400611df1500c10c813b1c0f00a44001e0b8625494a83ec3b7532876c0fa40c07c018307cf7fb66a40f0d782d231a682c8a82a1e8185ce3c519b1a206a008183e7be5a8cd9c5ab50287af14281809827bfc7))
def deadl11 : Packing := (183,3,7,8,4,14,0,deadd11)
def deadd12 (i : Nat) : Nat := 0x226c48bbfb654c3991828d28cddfe2ea731865c0891b87a0bb538ea405a3487b1d9bfa906e3a90b8064694310477f6ca947523051a4f7f6c2ed4a3a91828d23bfa90b0351c15a42e0191a577f8ab8d4e631c0c3f7e91b6d4c6b1c0c3811c4dfe2ea51d869c41234a020c7bed54772271048d2408d8efaa71cc89c4123490277f528e4932271048d27e9c5d4a830c011d1fe8c8d4907400c377f8bb6d4e1b04223bd3538ea46e23461177f6da950523047efedb538ea4608191a477f8ba94761a711a3f7f538e644e0191a3f7f5398d032019383963e9c516e8018413c39e9a98d63991b83b6205dfdb2a635a0646093df6ac6b41c816ae0f00efedb52a0493230488077f8ba95061970704f7f531ac732112b842091d02eff176da98d61b04a4140bbec8db6a6358ec1250d06eff1571a98d6830c994a8fd8b08517fb7ae74f70b6c76686125bc5665224e74a34684243d739334f30b2c728322d1e919c15810b0ac056000ffe92a07ffd1940fffb30817ff46102ffe9aa05ffd9340bffa26817ff46502fff4ca05ffd38407ffa6a80fff49501ffe91a03ffd93407ffb2480dffa6503bfecc205ff90340affd32815ff64d01bfec9203ff902406ffd3280ffe4a200ffc92c01ff915803ff247007fe44e00ffc89401fda33803fd445007fc84600
def deadl12 : Packing := (32,2,7,8,4,12,0,deadd12)
def deadd13 (i : Nat) : Nat := 0x22dfc5b6a90e86821a4efdb54c724410d1f7f16a63a18e01069005bf8b6d52351d0d049cf924d00ffd03ffd02ffd01ffa00
def deadl13 : Packing := (4,1,7,5,4,8,0,deadd13)
def deadd14 (i : Nat) : Nat := 0x17e2b6526070604013ff
def deadl14 : Packing := (1,0,7,2,4,0,0,deadd14)
def deadsamples : Array (Bits × Bits) := #[(0xf854605d026923a5a16008862c9d18d42fd85e54d221898f1e440284a107a02910c3e03c06c40d2642ca74f54627022c11e389d9b43b30c961ca72386ce81500aa210d1ba1a121108a6c99348979d054ac200727ac054c0970110780155ad581,0x6844620d0040231585204884208800c4270824141201090814040082a10700282003e02402c4084602ca04a440240a1091218919100a2084314a220840a00480aa210819a02120100a4409048968c05484200702a805440920100380144a9480),(0x80b20c31f72bfc4e1481d27000d43c9c5bd438a9c5e0286040f054f111d001ce10920229bde170b8d339029e2bcac4cd494fb74d1052452141a61c5b9ca1e642f40c600258428f0e5c00df481e03202a204cd465e10fe01206e82c7b03150603,0x80100c30e6089040109182600012282018c41889c5e0204002b0604000c009861080028b1c2120a0d12000120908c00d005a724402504200402010501c01c208540860025840090e1400964816012008204cd0254102a00206a0247b01150201),(0x12ce100c308544478a85796a2341d206e4242e31335abb35943abb40be28c8e05c4c115123137950052a02a9ba0d31c096458c656cc338623e92230683d8962194d5145c2aa62229438824d8e06246d0cd124850733918c390189888a426380a,0x10ca0000108540870900790a0240900460282200221a991490081a0028289000cc41010021184410080a0a28a20020c0200184206c0128621092200a03d8103080d5145c02a2022143880090804206d04d100840322918c190088800a4221002),(0x8628ebbd17000228c83c0291b729e17b3643984a392a815889878936d04e41b82b8e28807cc302855ead3105d9868885c748c2b0724ae81086518e259124cd4278a18b4aa01db88524c3a3435a0814469349110c18f0c24c2a8052bd88818268,0xc2206a1d05000020401c0090e509051303449848110100480001811490070429238c000818c508010485900541c68805c240409012420000024186258024450270208b02a00da0842041a3414a08100690490104085040042a8052bc00818028),(0xbc8ccda8781e4d8151cd3cf93a4a0a01509a42078c1bc4a783ea4aec6c7bbbd02ef85be130b1750bcd872a062d01842a34826040203d5b99ac8899721d47b82106b4f88001d04ee6f42e103eb14e0a090b95e84905a08ef7a2230402e2b14bc5,0x148981a0109a5c8210c1a4690a42220050930202c418c4a7837a48680e50b9d00c601bc02020f518c9002a002c1124282402304220255b598c9019921c51b8010494708001d04e62d42a103a30060a090b94e84905a08af280230402e2304b45),(0xd3b19712becef4647857054f8773c68492608a46265cd6cd0106c449284294958830b40e8328a4102841c46a63b66493288c7290c714876750b08cb0eb0a532e014ce7e24f9c08720240400006971f885be46b00080a21145aa7f52cf42a8012,0x92218c003e8654007015040a0c73c50280c0084821449285810a8400004080918c301008002824100801c000230200c0688c40804110046300b00cb28307502a0004c5624f9c086200004000021315805bc46800000a00145205f42ce0200002),(0x3145d24845746a93b60987114c89950ee90ab5809889781e716b0d141d9e036fea797f20c896480c8b565809c5575a81eabcad03980701be24b7e8d7401960b32336416db2f0c4c050f169960250e8b311988b92828b0074bd455ad232c2112c,0x2307720c00346283a400011d4c09950fa108a4001a095004514a0014181e2261ab3d3060c0d6480a2ac41009e4571880ea848181d90321bc24d38a860208103323340169a2b084c040f169960050c8b211800b9082890074b8455a803282012c),(0x49615339cc24bb41a658244591d020101222d0f578b5376254a121290a30cd5c4e2ad1d6dabfa9e032f022500c91031b32331a7a9ace0ca4e96243014a4009cd0d2a3210b66014de852533c420acc80ff443ad9cc5d0f4808cd621151170ac54,0x4900539a4030aa408668006591882010120251355ca1242200a1212102144d6e020a42d6d2878b6832b420400cb9813312321a4a924e408ce04943054c0001c10d2a2200b040149c8425334420acc80fa003859cc5d0e4000cd201111150ac54),(0x2108654280dbc21c532263cad6a2ab60a053058994f658a43b3dd89384745a04932387065124c385d01899e2cc083e3c1e3327061d61ca921a4965c8583262f4485320b5c04953298d1f02098424a39520b6148b236021a80528c3236c545ab4,0xc0001428049001c03a04a4012802a200013019184320c200a34088304a0580410028702010083a440180cc2080827381411260a0400ca0098085048489022c408432094004053098d0e0008842422012032140b21202188052801030c545a90)]
def deadcolumns : IndexTree ColumnInfo := (.fork 63 (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12)]) (.leaf [(0,2,440,69,8),(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12)])) (.fork 4 (.leaf [(0,4,369,138,8),(5,0,506,0,8),(6,0,505,0,9),(4,2,440,65,7)]) (.leaf [(2,4,369,136,7),(7,0,504,0,7),(5,2,440,64,6),(8,0,503,0,12)]))) (.fork 8 (.fork 4 (.leaf [(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8),(12,0,499,0,9)]) (.leaf [(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7),(10,4,369,128,6)])) (.fork 4 (.leaf [(15,0,480,0,4),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11)]) (.leaf [(16,1,460,34,7),(19,0,492,0,8),(16,4,353,138,7),(21,0,490,0,7)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(21,2,424,64,5),(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8)]) (.leaf [(9,16,486,0,8),(27,0,484,0,5),(11,16,484,0,5),(24,4,353,130,6)])) (.fork 4 (.leaf [(29,0,482,0,5),(26,4,353,128,5),(32,0,479,0,12),(0,32,94,385,8)]) (.leaf [(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(34,1,460,16,6)]))) (.fork 8 (.fork 4 (.leaf [(36,0,347,0,8),(39,0,344,0,4),(40,0,471,0,8),(49,0,462,0,8)]) (.leaf [(48,1,460,2,6),(50,1,460,0,5),(56,0,455,0,7),(64,0,447,0,13)])) (.fork 4 (.leaf [(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8)]) (.leaf [(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7)]))))) (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(74,4,305,128,5),(80,0,431,0,11),(83,0,428,0,7)]) (.leaf [(96,0,415,0,9),(96,1,396,18,6),(98,1,396,16,5),(128,0,383,0,13)])) (.fork 4 (.leaf [(128,1,332,50,7),(3,128,344,36,6),(132,0,379,0,11),(4,128,347,32,9)]) (.leaf [(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6),(133,2,312,64,5)]))) (.fork 8 (.fork 4 (.leaf [(136,0,375,0,9),(128,8,99,276,7),(140,0,371,0,8),(132,8,99,272,6)]) (.leaf [(138,4,369,0,5),(144,0,367,0,11),(152,4,353,2,5),(160,0,351,0,11)])) (.fork 4 (.leaf [(160,1,332,18,6),(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8)]) (.leaf [(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5),(192,0,319,0,11)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8),(260,0,251,0,8)]) (.leaf [(264,0,247,0,9),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7)])) (.fork 4 (.leaf [(260,8,227,16,6),(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5)]) (.leaf [(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6)]))) (.fork 8 (.fork 4 (.leaf [(296,0,215,0,7),(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6)]) (.leaf [(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11),(256,64,189,2,9)])) (.fork 4 (.leaf [(322,0,189,0,8),(258,64,189,0,8),(324,0,187,0,7),(324,8,163,16,5)]) (.leaf [(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)]))))))
def deadautos : Array (List Nat) := #[[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]
def deadlevels : Nat → Packing
  | 8 => deadl8
  | 9 => deadl9
  | 10 => deadl10
  | 11 => deadl11
  | 12 => deadl12
  | 13 => deadl13
  | 14 => deadl14
  | _ => emptyPacking
def deadindex : Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 1 3 0 9 1 4 (hashdeadl9)
  | 10 => lookupWord 17 61 5 13 5 4 (hashdeadl10)
  | 11 => lookupWord 124 434 7 16 8 4 (hashdeadl11)
  | 12 => lookupWord 137 475 8 16 8 4 (hashdeadl12)
  | 13 => lookupWord 26 148 3 13 5 4 (hashdeadl13)
  | 14 => lookupWord 7 47 1 10 2 4 (hashdeadl14)
  | _ => fun _ => none
def dead : Forest := ⟨511,14,fun j => deadsamples[j]?.getD (0,0),deadcolumns,deadautos,deadlevels,deadindex⟩
set_option maxHeartbeats 0 in
theorem geomdead : graphValid dead (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead8_0 : block dead 8 0 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead8 : block dead 8 0 2=true := sdead8_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_0 : block dead 9 0 12=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_12 : block dead 9 12 13=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead9 : block dead 9 0 25=true := (@block_merge dead 9 0 12 13 sdead9_0 sdead9_12)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_0 : block dead 10 0 6=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_6 : block dead 10 6 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_42 : block dead 10 42 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_78 : block dead 10 78 35=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_113 : block dead 10 113 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_149 : block dead 10 149 7=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead10 : block dead 10 0 156=true := (@block_merge dead 10 0 149 7 (@block_merge dead 10 0 113 36 (@block_merge dead 10 0 78 35 (@block_merge dead 10 0 42 36 (@block_merge dead 10 0 6 36 sdead10_0 sdead10_6) sdead10_42) sdead10_78) sdead10_113) sdead10_149)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_0 : block dead 11 0 4=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_4 : block dead 11 4 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_40 : block dead 11 40 15=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_55 : block dead 11 55 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_91 : block dead 11 91 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_127 : block dead 11 127 29=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_156 : block dead 11 156 27=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead11 : block dead 11 0 183=true := (@block_merge dead 11 0 156 27 (@block_merge dead 11 0 127 29 (@block_merge dead 11 0 91 36 (@block_merge dead 11 0 55 36 (@block_merge dead 11 0 40 15 (@block_merge dead 11 0 4 36 sdead11_0 sdead11_4) sdead11_40) sdead11_55) sdead11_91) sdead11_127) sdead11_156)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_0 : block dead 12 0 3=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_3 : block dead 12 3 14=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_17 : block dead 12 17 15=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead12 : block dead 12 0 32=true := (@block_merge dead 12 0 17 15 (@block_merge dead 12 0 3 14 sdead12_0 sdead12_3) sdead12_17)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead13_0 : block dead 13 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead13_1 : block dead 13 1 3=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead13 : block dead 13 0 4=true := (@block_merge dead 13 0 1 3 sdead13_0 sdead13_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead14_0 : block dead 14 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead14 : block dead 14 0 1=true := sdead14_0
theorem tablesdead : checkedTables dead 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block dead 0 0 0 = true)
  · exact (rfl : block dead 1 0 0 = true)
  · exact (rfl : block dead 2 0 0 = true)
  · exact (rfl : block dead 3 0 0 = true)
  · exact (rfl : block dead 4 0 0 = true)
  · exact (rfl : block dead 5 0 0 = true)
  · exact (rfl : block dead 6 0 0 = true)
  · exact (rfl : block dead 7 0 0 = true)
  · exact alldead8
  · exact alldead9
  · exact alldead10
  · exact alldead11
  · exact alldead12
  · exact alldead13
  · exact alldead14
theorem dead_start {prior : Nat → Nat}
    (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid dead prior=true) (checks : checkedTables dead 14) :
    Impossible graph 14 inputs.toFinset := by
  have noRun := root_index (g:=dead) low geometry checks (k:=14) (by decide)
    (i:=0) (ws:=inputs) (by decide +kernel)
  have tgt : targetOf dead=graph := by decide +kernel
  exact tgt ▸ noRun

end PEqualNP.Outside.L_meta_2541.SignedProof

namespace PEqualNP.Outside.L_meta_2541.SignedProof

-- Negate the designated raw coordinate before the first circuit gate.
def signRoots (m j : Nat) := (selected m).map (fun (i,a) => if i=j then neg a else a)

def chartRaw (m : Nat) (c : ColumnInfo) :=
  if c.2.2.1 ≥ 1024 then signRoots m (c.2.2.1-1024) else vars m
def signedRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols.read idx).bind fun ci =>
    materialize (chartRaw g.mask ci) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem signedRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols.values, Slice (chartRaw g.mask ci) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : signedRule g ops depth bank i paid = some c) :
    ValidPool (vars g.mask) (targetOf g) c := by
  unfold signedRule at h
  cases e : g.cols.read i with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    have v := materialize_sound (cols ci (g.cols.read_mem e)) h
    exact v

def signedNode (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => signedRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList ++
    ((g.index k (tag+2^100)).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls) ws)

theorem signedNode_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols.values, Slice (chartRaw g.mask ci) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : signedNode g k i = true) : Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [signedNode,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t u lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    cases h
    exact hT (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact signedRule_sound g cols h
  · intro tag xs hx
    have one (u : Nat) (hh : xs ∈ ((g.index k u).bind (linkedSet g (k-1))).toList) :
        Impossible (targetOf g) (k-1) xs.toFinset := by
      have e : ((g.index k u).bind (linkedSet g (k-1)))=some xs := by simpa using hh
      obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
      exact linkedSet_sound g _ names (prior (by omega)) h
    exact (List.mem_append.mp hx).elim (one tag) (one (tag+2^100))


def signedBlock (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => signedNode g k (start+n) && signedBlock g k start n
theorem signedBlock_at {g k start n} (h : signedBlock g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    signedNode g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [signedBlock,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem signedBlock_merge {g k start a b} (h : signedBlock g k start a=true)
    (h' : signedBlock g k (start+a) b=true) : signedBlock g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [signedBlock,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,signedBlock,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def signedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, signedBlock g k 0 (g.levels k).1 = true

-- Induction over the number of gates left in the computation.
theorem signedForest (g : Forest) (top : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ c ∈ g.cols.values, Slice (chartRaw g.mask c) (targetOf g) (subcube c.1 c.2.1) c.2.2.2.2)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (rows : signedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset := by
  intro k
  induction k with
  | zero =>
    intro hk i hi
    exact signedNode_sound g 0 i samples cols names (by omega) (signedBlock_at (rows _ hk) i (by omega) (by omega))
  | succ k ih =>
    intro hk i hi
    exact signedNode_sound g _ i samples cols names (fun _ => by simpa using ih (by omega))
      (signedBlock_at (rows _ hk) i (by omega) (by omega))

theorem signedRoot (g : Forest) (roots : List Sig) (L : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ c ∈ g.cols.values, Slice (chartRaw g.mask c) (targetOf g) (subcube c.1 c.2.1) c.2.2.2.2)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (rows : signedTables g L) (index : indexedRoot g L 0 roots = true) :
    Impossible (targetOf g) L roots.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at index
  rw [←sameWords_sound index.2]
  exact signedForest g L samples cols names rows _ (by omega) _ index.1

def signedPairs (m j hints : Nat) : List (Sig × Row × Row) :=
  (graphPairs m hints).map (fun (a,r,s) => (if a=inputs.getD j zero then neg a else a,r,s))
theorem signedLower {m j hints L}
    (hp : properB (graphGoal m) = true)
    (es : checkEssential (graphGoal m) (signRoots m j) (signedPairs m j hints)=true)
    (all : (signedPairs m j hints).map Prod.fst = signRoots m j)
    (run : Impossible (graphGoal m) L (signRoots m j).toFinset) :
    Lower (signRoots m j) (graphGoal m) (L+1) := by
  apply lower_impossible (proper_of _ hp) _ run
  intro a ha
  apply essential_ok es a
  rw [all]
  exact List.mem_toFinset.mpr ha

end PEqualNP.Outside.L_meta_2541.SignedProof

namespace PEqualNP.Outside.L_meta_2541.SignedProof
def signedContextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => signedRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList ++
    ((g.index k (tag+2^100)).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov ws,rules,ls)


theorem signedFrom_context (g : Forest) (k i : Nat) :
    signedNode g k i = (prelim (targetOf g) (signedContextOf g k i) &&
      (if k=0 then true else testAll (signedContextOf g k i) (signedContextOf g k i).2.2.1)) := rfl

theorem signedMakeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → signedNode g k i = true) :
    signedBlock g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [signedBlock,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩

def signedContexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (signedContextOf g k)
def signedHeader (g : Forest) (k start n ar : Nat) :=
  (signedContexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
def signedRowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := signedContexts g k start n
  let b := makeBatch k ar xs
  (List.range len).all (fun d =>
    let i := lo+d
    batchRow b xs i (List.range' (i+1) (ar-(i+1))))
theorem signedRowCut_at {g k start n ar lo len} (h : signedRowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (makeBatch k ar (signedContexts g k start n)) (signedContexts g k start n)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem signedRowCut_merge {g k start n ar lo a b}
    (h : signedRowCut g k start n ar lo a=true) (t : signedRowCut g k start n ar (lo+a) b=true) :
    signedRowCut g k start n ar lo (a+b)=true := by
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact signedRowCut_at h (lo+j) (by omega) (by omega)
  · exact signedRowCut_at t (lo+j) (by omega) (by omega)

theorem signedCutsRun {g k start n ar} (h : signedRowCut g k start n ar 0 ar=true) :
    runBatch k ar (signedContexts g k start n)=true := by
  let xs := signedContexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (makeBatch k ar xs) xs (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := signedRowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem signedCutsBlock {g k start n ar} (hd : signedHeader g k start n ar=true)
    (h : signedRowCut g k start n ar 0 ar=true) : signedBlock g k start n=true := by
  apply signedMakeBlock
  intro i lo hi
  let xs := signedContexts g k start n
  have hm : signedContextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [signedFrom_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hn (signedCutsRun h)

def signedBoxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => signedRowCut g k start n ar lo num=true
  | d+1 => signedBoxes g k start n ar lo (num/2) d ∧ signedBoxes g k start n ar (lo+num/2) (num-num/2) d
theorem signedBoxesCut {g k start n ar lo num d} (h : signedBoxes g k start n ar lo num d) :
    signedRowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := signedRowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v

def signedCells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => signedHeader g k start n ar=true ∧ signedBoxes g k start n ar 0 ar rows
  | d+1 => signedCells g k start (n/2) ar rows d ∧ signedCells g k (start+n/2) (n-n/2) ar rows d
theorem signedCellsBlock {g k start n ar rows d} (h : signedCells g k start n ar rows d) :
    signedBlock g k start n=true := by
  induction d generalizing start n with
  | zero => exact signedCutsBlock h.1 (signedBoxesCut h.2)
  | succ d ih =>
    have v := signedBlock_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

end PEqualNP.Outside.L_meta_2541.SignedProof

namespace PEqualNP.Outside.L_meta_2541.SignedProof
def theta0Columns : IndexTree ColumnInfo := (.fork 5 (.fork 2 (.leaf [(0,0,0,0,11),(2,0,189,0,8)]) (.leaf [(8,0,183,0,8),(16,0,175,0,8),(32,0,159,0,8)])) (.fork 2 (.leaf [(128,0,63,0,8),(1,0,190,0,7)]) (.leaf [(24,0,167,0,7),(160,0,31,0,7),(0,16,166,9,6)])))
def theta0D6 (i : Nat) : Nat := 0x1e00af812a10d414c600
def theta0D7 (i : Nat) : Nat := (if i<1 then 0x7807c03e01f00f807c0200000000000f0080000001e01f00f25c6f01b9ecdacea9a7e859ee6195e4d8ce1983e057edf175dcd70db96bda566d9161d7d5cd6957d454ad2145d0d40cf93bce536cd131cbd2cca927c9522c811dc6d18c5913c450ac2105c0d00bf8fbbe4f6bc0e9b8cdcb58cfb24c2af0b5accb0ab8abaa4a6a90a1a7c98a488fa348aa2085a0c809f87b9e4769d0719bc6c9a867994629805994c4c9183f8e4368d0318bc2c8a827894228701985c148480f83406801799391a244802f32720c489004ee5242858e009f88c850b1c013f1191e16380277292142a7004fca651814e00d3d2aad021c01ab9545a0438025f532b4087006d658d5810e009bd4cab021c01b6a554a043803752a894087006f258d2810e009f54ca5021c01b7255460438027e5328c0870065e9557810e009dca48f119c017994919633802f925232c67005f4464658ce00aecbc8cb19c01e9a6691233803e34ab22467005e6524588ce00bcca483119c01799491e2338027b11319a85006b69983850a00dad2a870a1401b99540e1428027b273442850069e9995810a00d9ca12b02140137a99560428034f4aab4065006b64c9680ca0097d4cad019401a7a66560328026f532ac065006ae999480ca00d9d2aa9019401af266460328036e4aa8c065006f44c9180ca009f94ca30194018fa665e0328032f4aabc065005f20e54288a00bb4ac885114016e9690ca22802ed2b219445005ea5243288a00bf08c865114015e9790ca228027e2323c445005f84645388a00bb4ac887114017e11910e228027d31221c45007b299a3388a00fa52ac6711401f8a448ce22802fc2323c445005ea4a44350600bcc1ca84a0c011f879561418026f2b214283005f24a4434c600fc821a8298c013e8295a1318025f2d214263004de564284c6009dca485098c01aba6652021803674aaa4043006e68cd4808600dd51129010c013ba99520218035b4cc9c043006d69553808600dcd2227010c01bca224e0218037a2a29c043006f45053808600de890a7010c013da994e02180337488bc043006768cd7808600cf5112f010c01f325591211802de2d221c23005dc5644384600bf09488708c015f17910e11803da4cd19c23007d49563384600fc92246708c017d03950a11802ee2b221423005bc5a43284600bb8ac86508c017b1490ca11802be2f219423007f08ce2284600bd494886a3c0179839509478026f2b21428f004ee5242851e009bcac8509bc013b9490a1378035e4cc8c06f006dc955180de00df1112301bc013f299460378027b11319a4f006b69983849e00dad2a87093c01bca220e1278037a4221c24f006ce5614809e00d5d3329013c01b3a555202780373466a404f006ea8894809e00dd908a9013c013ba9952027802fa27210a2f004ee5242845e00 else 0xe00f007c03c010038020e00801c01e00800007804000000000000003803c0100000000000000000000000000001e010000000000e00f004243c01e00f007803c01e00f00400000000001c01e0080000000000000000000000)
def theta0I7 (i : Nat) : Nat := 0x3800
def theta0D8 (i : Nat) : Nat := (if i<1 then 0x9634ca00fda334ca00fe9424ca00bf9684ca00bf9584ca00bf9484ca00bf8784ca00bfa884ca00efa660ca00f7a550ca00fd9320ca00bf9680ca00bf9580ca00bf9180ca00fba4488a00fda3388a00fe94288a00fe84288a00fe93288a00fe83288a00bf94888a00bf93888a00bf91888a00bf87888a00fe96388a00fe86388a00fe95388a00fe85388a00fe94388a00fe84388a00fea3388a00fe97888a00fe87888a00efa6650600f7a5550600fba4450600fb84350600fda3350600fb94250600bf95850600bf82850600bf87850600bfa8850600efa6610600f7a5510600bf96810600bf95810600bf92810600efa664c600f7a554c600fba444c600fd8434c600fda334c600fd9324c600fea224c600ff1514c600ff1414c600bf9684c600bf9584c600bf9484c600bf8284c600bf8784c600bfa884c600efa660c600f7a550c600fea220c600bf9680c600bf9580c600bf9280c600fba4448600fda3348600fea2248600ff13148600bf94848600bf93848600bf87848600bfa8848600fba4408600fda3308600fea2208600ff14108600ff12108600bf94808600bf93808600fba4484600fda3384600fea2284600ff14184600ff13184600ff12184600bf82884600bf87884600ff15484600ff05484600ff24484600ff16384600ff06384600ff15384600ff05384600ff14384600ff04384600ff23384600ff14284600ff04284600ff13284600ff03284600ff22284600ff04884600ff03884600ff02884600ff07884600efa6651e00f7a5551e00fba4451e00fb84351e00fda3351e00fb94251e00fea2251e00ff21151e00bf82851e00efa6611e00f7a5511e00fb95411e00fea2211e00fb94111e00ff21111e00bf96811e00bf95811e00bf92811e00bf91811e00efa664de00f7a554de00fba444de00fda334de00fea224de00ff2114de00bf8284de00efa660de00f7a550de00fd9630de00fd9530de00fea220de00fd9310de00ff2110de00bf9680de00bf9580de00bf9280de00bf9180de00fba4449e00fda3349e00fea2249e00ff21149e00fba4409e00fda3309e00fe94209e00fea2209e00fe92109e00ff21109e00df92709e00fb94809e00bf94809e00bf93809e00bf91809e00bfa8809e00fba4445e00fda3345e00fea2245e00ff13145e00ff02145e00ff21145e00bf82845e00fba4405e00fda3305e00fea2205e00ff14105e00bf94805e00bf93805e00bf92805e00f3a5591200bf11814e00af96810e00b795810e00be92810e00bf11810e009f97810e00eda668ce00f5a558ce00f9a448ce00bd83850a00b795810a00af9680ca00b79580ca00bb9480ca00bf1180ca009f9780ca00fca3388a00bb94808600bd938086009f97808600fb24484600fd23384600fe22284600bf1180de00bd83849e00bb94809e00 else (if i<2 then 0x24189c090b004000600e00e008000c04858090b00780700498490418020c01c0100000003007804000000022101108000011080000000007008380400e010038041c020e01e01e0485c020000000702420038078041c02443c03c03c090b804b84000130838041c0200700f00f00f00f0284c6000381217008381110000e01e01e01e01c14180f0703050b92370c04c91386026489c3013244e18099221324087828301e0a0c07828301f0c05c9138602e4c9c3017244e180b92270c05c9138602e4885c9021e0a0c07c30111f0c04464408b050603c14180f050603e05c90f817243e01c5ec52c46c3ac2ec29c1dc11c0cc07c02bfdbf8bf3beebcdbc1bb5ba9b9db98b85b80b6db5ab4eb42b36b2ab25b19b0db01af5ae9addad1abeab2aadaa8aa3a97a8ba86a81a75a70a6ba66a61a5ca57a52a4da48a43a30a1da119fe9f99df9d39c79bb9b69aa9a599998d98197c97797295f95a94793b92891c9109048f88ec8e78db8cf8c38be8b98b48af8aa8a589988d88187587086b86686185c85785284d84884383e83982d8288158097f67ea7de7d97d47c87bc7b07ab7a67a179579077d77876575274673a72e70d6fa6ee6e96e46df6d36c76bb6b66b16ac69968667a66e66265664a64563963462861c61761260d6086035fe5f25e65e15dc5d75d25cd5c85bc5b75ab5a65a159c59758b58658157c57757256d56856355755254654153c53052b52651a5155095044f84ec4d94cd4c84c34be4b94b44af49c49749248647a47546945d45144543242641a41541040b3ff3fa3ee3e93dd3d83d33c73bb3af3a338938437f37a36735b35634333e33933432831c3103042ea2bb29a27925823721d2031e91cf1ae18d16c14b12a1090ef0d50bb0a108e07405a04002600c000bf82855200bf87855200bfa8855200bf92815200bf91815200fb95491200bf82891200bf87891200fba5591200fb86891200fb85891200fb82891200fb81891200fb87891200fba4458e00bf82858e00bf87858e00bfa8858e00bf92818e00bf91818e00f7a5554e00f795454e00fba4454e00fd96354e00bf82854e00bf87854e00bfa8854e00bf92814e00bf91814e00f7a5550e00bf96850e00bf95850e00f7a5510e00fb95410e00fd96310e00bf96810e00bf95810e00bf92810e00bf91810e00f7a558ce00fd9638ce00fd9538ce00bf8288ce00bf8788ce00fda668ce00fd9658ce00fd8658ce00fda558ce00fd9648ce00fd9548ce00fd8688ce00fd8588ce00fd8288ce00fd8188ce00fd8788ce00efa6650a00f7a5550a00fb96450a00fb95450a00fba4450a00fb94350a00fda3350a00bf95850a00fd83850a00bf87850a00bfa8850a00efa6610a00f7a5510a00fb94210a00bf96810a00bf95810a00bf91810a00efa664ca00f7a554ca00fba444ca00fd else 0xc05098f8070070070041803c0200000000301524189c038038038020c04840c05058090b80700700700418038025038038038038038090b004000600f00800482000000000000602a2c05045c380908180a921e00f00e0080a04180380380200030151030121600e02a2c01e01c012a12810600e00e0080000001803803803c020000000000000018020c04458038088b80700400c01c01c0100018020c04440c04858090b007007007011))
def theta0I8 (i : Nat) : Nat := 0x1d108000060a9c49f166074641e01521d68760000000c911c42c20b56981aac81c42c000d412423613146921b1c58415cc5334d58660000822914103ce4ae864f038000d0ce46ff137836000005a60d202f260000000000000000000000105f0002c3514b7c62718e426407ee1850e407fc480000f00a9030000c1a81f342d000086b00000000001873000181e00000000000000000084e903f01bd05e81154039060000000e1bbc12000005d0000000c0e9c10e12844880efc52c151c2bc14744b84c6468e15845ca115c0af4bbc798030000b03445b0002c550000805911905ee40696c9010000f072807502d414701800071c800000028160000000a0b00000000467c196c190000000000150cc91c0000000000b0dc0000000000402400004c000071b583d8113136c42944034cd44781c7c7765b980321e904f510c000518196a60a3427a1ec000e4a0478000000070040000000413f0ca02e000000090c6425b4a5830d5b711871fb408b20231860f9a45406346175ad421c0e2509e1f400010934296000c7020fec414806400470012451c000020005200a25e0c464310020b00044314802f00040500c28e200340004086
def theta0D9 (i : Nat) : Nat := 0x20c15513452191060c28ba68a43260c155174d1491060aa89a290c88306155d148644182aa268a43220c18517452191060aa8ba68a43260c1345218d060aa8ba68a488305544d148644182e9a290c78305544d148644182e8a431a0c15513452191060aa89a290c88305d344634182aa268a43220c1745218d060aa89a290c8c2044624182aa268a47c1551345218f82e9a290c6c1551345218f82e8a431705544d14863e0aa89a290c7c1551345218f82230e0c174d02c182e9205c204078408a04bb367ab4d349ff32a4ac5a862ff1e3b986c6ce982ad054e9c924a143ee720cc970282478778c01221e82b83403a003fcaa401fe15200ff489007f963803fc31c01fe54e00ff0a7007f943803fc21c01fe8ce00ff285007f842803fc99401fe0ca00ff445007f941803fc20c01fe4c600ff063007f921803fc10c01fe84600ff28f007f847803fc9bc01fe0de00ff24f007f827803fc8bc01fe05e00f7489007da33803f511401fc84600
def theta0I9 (i : Nat) : Nat := (if i<1 then 0x5d6078000000048a2000120c9878a23481a1c258000708ef15a017800000000000000045e0000500a4a0ba4b78baa40249ebc19800084398afb84242ae00000116831903a20dc0000000000054d3582741f704fc05a88c9c5e80b20001a1cb86b98a30000000000010874d2c0001404d0ae0001624187d000001b7e44ac2962bcb4a96444c3d189c44c7ebac83430089229c10ac00d00ff080232546af25700000003c881a68691600021000000315783cc8130000f0960000000681f0000c38000020cf0001a225c1a78f600002054000000005ea03e400020c580fa0003c45f8f20001e2fa07df883000023a382aaae7a027c2760236816a95db02603d80002173aac1b28dc263122237ac1cb051519800024051a53b0ec000000000000000000000000000000000000058730000ac258805917744f6286d45890c0000000315cc07021cea2480001220a15e0000077ea3800000001c6ca90a220b6abf53f464601480000c810000813e8237e236a610000000201bb8c400c28300a2b80000001a1280000000921f22d7d74000004ee484bd6ed854000024180178a83f59f890c000510700014b540000000000068200000000a0b168ac00030028190e92a03140c6303200000007ae9000160c0000530300000001801805c00010425c36600cf538000302fe24f000000000000000c5f2621532bcaa1e052e34ec2c80000001625c25a0000f4d4000001c589ba07a000288410692590a29b46a12070000eb3800060ce119403d4000281c000162011210000b154000340b9a95e1be000000000000000c26096a000000000003d248000806249b800030a701d7805246d72f671976813481d882322cea6c000181d000142fc10ec2860000e3c0000286ae0c0616c80962ab001c0000000000081dd20b157378b3c001822055056ae0001823247f70c744a2eac5170411334d60002516886d0000a124c505094f451e3fe910ba25f185c268023d0b0060440fd92e830030b42457566309ed031699641ad027d466a08153f9071e153634a472f8cda0a0237351e806ff1870bc1d87c8fd90f200000002abd04c801f804a82f8516cc266122d01ad4c0a03613c1a0930a600000000101a11f4904000000051f0a045405a8eae15061dc00068b101f80000000702504e8000316f8000f5d48aa800038ed3524e3ddc219a8da1a3815b92e481e000122d2d59422c4588000095c48b82051022940dc63f0001a085471a07c000000000003a790a2000402080830204004040410008086950028400001c4002e2c3030604680180c086002029f8200207043c080060c30964100860210402000418200285110a002060414001104918000000030230200000c004040c02b000488114502800a0001504300010e084000034187020800008003060204001020c202 else 0xc7110e9b16e013183a50a5006ce0b9c3fa83b80ca00008408000387ee1059295c5160ea0001e59800090cce120003a8e4447f6411d5d721ec5f4e19286c0000f158099c95db0dd621c243683c0000f48c4815c76509394f960ac0156aef00016b0e035985751820041c858000a519613b55bfa87752da011d42382420ced07d470984d00018c4b13a80001d17401a97b800061ac899a84338e6546e00000000000608940880003256a0460003d6f00000000000005d800021e800000004)
def theta0D10 (i : Nat) : Nat := 0x20013fa00
def theta0I10 (i : Nat) : Nat := 0x84a91c85445c757c43a13103b0bf1eb0fa10355000b0770d00060c71d54fd5a000000000000000f0665b91500080e00000014812020131900000075881b10915021150054214bc18c12317516f1ab1fe08451c56000e04000002359c5260595f000e2100a714249313212006080027030be01
def theta0Index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 1 2 1 7 1 2 theta0I7
  | 8 => lookupWord 54 227 6 14 8 2 theta0I8
  | 9 => lookupWord 140 584 7 15 9 2 theta0I9
  | 10 => lookupWord 22 69 4 12 6 2 theta0I10
  | _ => fun _ => none
def theta0Levels : Nat → Packing
  | 6 => (1,5,4,0,0,1,0,theta0D6)
  | 7 => (131,4,4,0,0,10,0,theta0D7)
  | 8 => (280,3,4,0,0,12,0,theta0D8)
  | 9 => (34,2,4,0,0,11,0,theta0D9)
  | 10 => (1,1,4,0,0,1,0,theta0D10)
  | _ => emptyPacking
def theta0Pack : Forest := ⟨191,10,g191.samples,theta0Columns,g191.autos,theta0Levels,theta0Index⟩
end PEqualNP.Outside.L_meta_2541.SignedProof
namespace PEqualNP.Outside.L_meta_2541.SignedProof
def theta1Columns : IndexTree ColumnInfo := (.fork 4 (.leaf [(0,0,0,0,11),(2,0,189,0,8),(8,0,183,0,8),(16,0,175,0,8)]) (.fork 2 (.leaf [(32,0,159,0,8),(128,0,63,0,8)]) (.leaf [(24,0,167,0,7),(160,0,31,0,7),(0,8,163,20,6)])))
def theta1D6 (i : Nat) : Nat := 0x21f6aa1e5281c211
def theta1D7 (i : Nat) : Nat := 0x8400e00f007803c0107007802000000000000000000000e0161700780584007007802000020200000000000003802000000000000000000000e16f771abcf647097fb9596c15bab5469947a14f67133974a6491f8d45620fb77365a8cf612d560ab53265288f45215007b3b1c4d86731154a04b231047837190b450230f064280f05014015f6991e1208467ed323c24108e7da6478482119daa4850b1c233f1090a1638465ead2042a708ed558d5810e119bb4cab021c23bb154420438477a2c68408708cfca650810e11bcaa48cb19c237c52919633846fa21232c6708fc5956448ce11bcaa48b119c23a76555a0408465ed32b408108e9d9995810211d9aa02b02042337699560408475accc9c08108ed59553810211d733325020423b66554a0408467cd329408108ced226444c211b6ab486498423755590c930846f2a921926108ead998484c211d9b2a89098423b95631213084676a934426108e9d955680c211d6a982d0184232f6995a0308463e8f29c24108e758cc78482118fb4c8f090423de027480708463e8f2940e108dbc5a44080211bb8ac881004237d13910200846fc2522040108dec1253080211b78b4861004235f0794820084676a921440108fcc9564480211b78b4887004237715910e00846fc25221c0108cfc6244380211f693346700423f52558ce00847f248919c0108df40e54280211bb8ac885004236f1690ca00846ee2b21940108dec52432802119f8c486500423fc23388a00846fa0729440108dec5242880211
def theta1I7 (i : Nat) : Nat := 0x0
def theta1D8 (i : Nat) : Nat := (if i<1 then 0x3c0200000002108108400001084000000002108000e180992270c04c913050603c14180f050603e180b13270c0589938602c4c9c3016264e180b13270c0589101828301e0a0c07828301ef0dc9b2b5f6b2d4da4f43e74cd197328644c718971061bc1f80efbdf2bdb76aeadd0b9771ae0dbcb6f6cad6da8b39642c2578ae75baadd56aa35169cd2da43456814ef9d537a694c69832f25bca49231fa3945f8990e60fc0c800fd1f0bd5792ef5dc3b374ee6dc7b8a6eed91afb53680ced9b32a63cc658a30f606bdd722d8598b015dab6562a955029b52ca45462804e89692724247a8e119a2e4528910c21340e808fe9f83e679cf11dd3b074ce71c93886e0d99ae352620b394d2664647c0d716c2543a05309c0d00d000bf42858e11bf47858e11bf40858e11bf68858e11bf52818e11bf50818e11fd56354e11bf47854e11bf40854e11bf68854e11bf50814e11bf55850e11fd56310e11bf55810e11bf50810e11fd5638ce11fd5538ce11bf4288ce11bf4788ce11bf4088ce11fd6668ce11fd5658ce11fd4658ce11fd6558ce11fd5648ce11fd5548ce11fd4688ce11fd4588ce11fd4288ce11fd4788ce11fd4088ce11ef6660de11f76550de11bf5680de11bf5580de11bf5280de11bf5080de11ef66650211f765550211fb55450211fb64450211fd63350211fb44750211bf55850211bf42850211bf47850211bf68850211ef66610211f765510211fb54010211bf56810211bf55810211bf52810211ef6664c211f76554c211fb6444c211fd5634c211fd5534c211fd5434c211fd6334c211fd4324c211fd4374c211ff1404c211bf5684c211bf5584c211bf5484c211fb4484c211bf4284c211bf4784c211bf6884c211ef6660c211f76550c211fd5300c211bf5680c211bf5580c211bf5280c211fd63348211ff13048211bf53848211df47848211bf47848211bf68848211fd63308211ff12008211bf53808211bf68808211fb6441c211fd6331c211df4271c211ff1201c211bf5481c211bf5381c211bf5281c211bf4281c211bf6881c211fb64480211fd63380211ff14080211ff04080211ff13080211ff03080211ff12080211ff02080211ff07080211bf54880211bf53880211bf52880211bf42880211bf47880211ff15480211ff05480211ff24480211ff16380211ff06380211ff15380211ff05380211ff14380211ff04380211ff23380211ff14280211ff04280211ff13280211ff03280211ff22280211ff04780211ff03780211ff02780211ff14880211ff04880211ff13880211ff03880211ff12880211ff02880211ff07880211b755810e11bf10810e11ed6668ce11f56558ce11f96448ce11af56810211b755810211bd53810211be52810211bb4484c211af5680c2119f47848211fb24480211fd23380211fe22280211 else 0xc0549012700e02a48780380380380a0b8070141600e00e00e00e00e02620030078070040042484000000000000700f00f00f0080180a0800e01c01c01e01c018254504a0818038038020003015160282c04c458380b0b816160242c05098f0131600e00e0242e01c012a100300700700418090b013103807001100180380200038078078131700f00f008000421000000600e00e02a48780)
def theta1I8 (i : Nat) : Nat := 0x2d38a190000000c5e0004208002c6840cd01800100c000000689fc28000e0d5c1c000000f0c74eb212000593c0354442375830000c6c000b120002840000000000000178a0000000000000000304c0000007009811c1383039a40a2e1ea1e00bf8a8b6900f0080c0ac7d83c286f497900c0a44892dd639615d02e8b3c52a1d51d1002c390117010ed981de1fe82486d84d838a5f9c41862000d1f800304b2420002670000e2b0c1681c00000000042280000000002c4bd0303590b2c9a076440516f02dd05a2e719a0cac1063900070f52100000004ad4001a21582a08c000000000004a10002412cc04e8c70c02c30521902c00180030410c00c01c1519
def theta1D9 (i : Nat) : Nat := 0x20c155134813c182eaac90278305544d204f060ba8b2409e0c155164d20510609a409618305545934814e0b240920c155134813c182c9a409a0c155134813c182c90258305544d204f060aa89a409f05544d204d0c182aa269028860c16490343840812e9aea8b97227811c96b17d55125408d32907b1181d003fab1c23fd18e11feaa708ff453847faa1c23fd10e11fec6708ff437847faa0423fd10211fea6108ff430847fa90423fd08211fe8e108ff600847eb19c23fc80211
def theta1I9 (i : Nat) : Nat := 0x496b92011b7484106dc8921b8000000052c69b6c62612ac94344a57f2104000319c0450000000000221cb90aa163d9238e0002a48923fc72e01d43d5919f403960806b80800031edc56000014e18fa050610f1320000125b096a865454000d07744f81940096a24942160387ae0fc647000390271ddc0d81c4000000000060ab066d62357e99f20201520b8ce0e0000d1d692110fbc5a30e988d000377f0000a1980ef434000321d000017c521400042000000000000b47ea4012200000001933cd6c870a0440002028000d639460e8d577d6d0826c0000c5770c9881007a91ca57ea27b45d84e508613d8071c59000042ec193469a14977410df06b1df96419030000b489e26cdb9f5e42334555d2185b00bf47fc07dc05186c47419a701790d5c49e063478000138400000001453c22000000070a40000e24000a4ac08ba11d4820150000306b547c9aa4534238c5d000000050c0000b12e001ed18134a136858718685fa05151a0a2304c19ef13ef1f5c2d022b40b600c051b043653d000000e44c0000000c16c974000509c93001a078a000000081b09540001e3b64e6185d04800000032200012d6500000000000e870000000e5700000003c8731100000001479000000044d4000a1fbc28d03940810aec2cf1bc36d110183955bd002000000000001462240000647a74db86a975b20d62e4894042324d063000287c724a20e9500000d21b85c0066721cdec21f303d41348be20dc4c74330861d18f05553af121c24a1ce431e178000308e891f09b3470000b22947503cb404b54000351b91da86a611ac3644000044b0ca02d9c11c21b8740a180468c634515424435504418210900309400400250e10a1800061015830891121413c004a180050
def theta1D10 (i : Nat) : Nat := 0x40201bf611
def theta1I10 (i : Nat) : Nat := 0x121e23d6b00159c13b0d50800000000cc20040078b001c3c87409c58000e8f80001aa800000000003418c2d5d085a5800c811a816aa9b100000000029062800541e4c831e1a2810a8aca836992001ab4049000f28735910012bcc11c69080208c21600031044810020
def theta1Index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 1 2 1 7 1 2 theta1I7
  | 8 => lookupWord 35 140 6 13 7 2 theta1I8
  | 9 => lookupWord 72 334 6 14 8 2 theta1I9
  | 10 => lookupWord 20 67 5 11 5 2 theta1I10
  | _ => fun _ => none
def theta1Levels : Nat → Packing
  | 6 => (1,5,4,0,0,1,0,theta1D6)
  | 7 => (67,4,4,0,0,9,0,theta1D7)
  | 8 => (149,3,4,0,0,11,0,theta1D8)
  | 9 => (18,2,4,0,0,10,0,theta1D9)
  | 10 => (1,1,4,0,0,1,0,theta1D10)
  | _ => emptyPacking
def theta1Pack : Forest := ⟨191,10,g191.samples,theta1Columns,g191.autos,theta1Levels,theta1Index⟩
end PEqualNP.Outside.L_meta_2541.SignedProof
namespace PEqualNP.Outside.L_meta_2541.SignedProof
def theta3Columns : IndexTree ColumnInfo := (.fork 5 (.fork 2 (.leaf [(0,0,0,0,11),(2,0,189,0,8)]) (.leaf [(8,0,183,0,8),(16,0,175,0,8),(32,0,159,0,8)])) (.fork 3 (.leaf [(128,0,63,0,8),(1,0,190,0,7),(24,0,167,0,7)]) (.leaf [(160,0,31,0,7),(0,8,163,20,6),(0,16,166,9,6)])))
def theta3D6 (i : Nat) : Nat := 0xf007c01e0b914a865585518cee510a1956154633
def theta3D7 (i : Nat) : Nat := (if i<1 then 0x40888a33bc6a48cb114677c519196228cef921232c4519cf36246588a33bc6a48af114677c519162228cee98b28444519db35a40888a33b66948cab0c676d909195618ce6bab2142c319ce752428586339ec84850b0c6774d29195518ceeb21232aa319d971a55254633f2a32ac2a8c6739d491e1518ce73a92142a319cb75a408546339cea4810a8c673cd29021518ce7b012ac28319cd7564285063396eb4810a0c6735d59021418ce79a520428319ea7999481c633d8f2aa9038c67b8e22520718ce73d32a40e319c771e54848633d67112d010c67ad5515a0218cf5aa82b404319eb5485680863396f4cad010c67b4e22560218ce6bd32ac04319ea79994808633dc71129010c6739e99520218cf5b4cc8404319ef28890808633de8a8a1010c67bd141420218ce7b5328404319de55246584633be2948cb08c677d109196118cfe2cab2242319de55245784633baaac8c508c677954918a118cefa2123142319db51a55284633bcaa48a508c675d47950a118cfd8ccd1142319cd72265558233b2eac8c4b046769d49189608cedaa32312c119ec79105858233da7110b0b0467a5d61161608cf6ac222c2c119cd756688582339e6c4c4428467a9e445a0508cf4baa4b40a119eb38896814233d6b08ad028467b1d52520508cf71c44a40a119ee58454814233d8ea82902846739e99520508cf71c88940a119ef184528142339e74ca5028467b9644460508cf6aaa48c0a119ef18891814233daaa8230284673d699460508ce7a91308a4119c771e54848233d6b3303090467b5655061208cf72c880c24119ef188818482339ea8cd10904673cd89888108cf4bcaab402119ea79116804233d67112d0084672de995a0108cf63c88ac02119ed38895804233daab0ab008467b5510560108ce6bd32ac02119ea79994804233d8f2aa9008467b8e22520108cf72ac2a402119ee544148042339cf4ca9008467ace664a0108cf69caa9402119ee39112804233de2b0a50084673ce994a0108ceeb0b2b040119db65a45080233bcca48a1004677c929142008cefa2322840119df40652080233b6cb48210046775959042008cef32920840119df24a410802339cea48f1004671dc794a2008ce6bab21440119ce75242880233bcca48cb004677c929196008cefa23232c0119cf66246580233f4d3348900467f1a55912008cef32922bc0119dd65646280233bcca48c5004677d11918a008ce7b3123140119db61a55280233bcca48a5004675d87950a008cfd94cd1140119fd29562280233fc52244500467799491c6008cedb2d210c0119dd65642180233bcca4843004673d989086008cfda4cd08c0119fd49561180233fc92242300467fc222846008cefa2323440119de65247880233b6c34a51004675d8794a2008ceeb2b21440119de65242880233 else 0x1c01e00f007803c01e0080000000007807803c010002421210000000000070040000000003803c01e00f007803c01e00f007803e01e00f007803c01e00f007803c01e008000004841c01e00800000000003803c0100000000000000000380605c01e0181001c010700400e0181001c03020000000000e018100000048400003802000000003802000000e00800000380200000000000003c020c1e00f0040000000000000000000000000000000000000002cd595b2162ebf571ac955ea553da714ce97529a4947e8d515a113ee774e99c935e654c59812ee5b4b195929e5149d92122e434818f91de3946d8d116e2744186909e0d40d800fcdf33d9798efdd93a5730e2dbf3716d8d9db135d6a0d2d9f331658c9d9131d630c4d87309608bdd752e55c0b6d6b2d1598b1d612bd570acd572a9548a3d4126d4d098d2b2514888fd1d22544086d032013f87dcf91ed3d078cef1c93886fcdd1b535068ccf19932861cc117d2f05ccb71692c855ca914d29050c9f13125849c9111d23042c831011f83dc790ed1d038c6f0d91a831c5d0ad14026c4b09111821c4107d0f01cc370690c817c2d0550a012c230410780dc1902d05008c0f01902803c0500500139e99520658ce79d32940cb19cf5a6518196339ed4ca1032c6735d590a1648cee9a5232aa919dd6424655523396eb4810aa4673cd29021548ce7aa32042a919de54646591233bcc848cb22467e1e66956448ce73d32a40af19ce7a654818a33d6ab1230314673d699460628ce7b532840c519dc75245754a33d2eaa0d0a94672dd69a21528cf63aa4a40a519ce7a654814a338ee3cad0a14671dc79561428cf1bccc3c28519c77a647850a33ba6ac8c51146778d4918a228cef8a323144519df24246288a33b6634aa51146778d4914a228ceb98f2a144519cb75a)
def theta3I7 (i : Nat) : Nat := 0x7032
def theta3D8 (i : Nat) : Nat := (if i<2 then (if i<1 then 0xe5558233edd6458233f9e4458233edc6758233edc6258233fce2258233edd6158233fd61158233f5c5858233bdc7858233bdc2858233bde8858233f9e4418233fce2218233fd61118233edd6018233bdd4818233bdd2818233bdd1818233f5e5554233f5d5454233f9e4454233fce2254233f5d5154233fd61154233fd96054233bdd6854233bdc7854233bdc2854233bde8854233f9e4414233f5d5214233fce2214233fd61114233f5d5014233bdd4814233bdd2814233bdd1814233ede6650233f5e5550233f9d5450233fce2250233f9d4150233fd61150233bdd6850233bdd5850233bdc2850233bde8850233ede661c233f5e551c233fce221c233fd6111c233bdd681c233bdd581c233bdd281c233bdd181c233bde881c233ede6648233f5e5548233f9e4448233fcd5248233fcd4248233fce2248233fcd2148233fd61148233fd96048233fd87048233bdd6848233bdd5848233bdd4848233bdc7848233fd41848233bde8848233ede6608233f5e5508233f9e4408233fce2208233fd61108233fcd2008233fd92008233bdd6808233bdd5808233bdd4808233bdc7808233bdd1808233bde8808233ede6644233f5e5544233f9e4444233fce2244233fd55144233fd54144233fd61144233fd92044233bdd6844233bdd5844233bdd4844233bdc7844233bdd2844233bdc2844233bde8844233ede6604233f5e5504233f9e4404233fce2204233fd56104233fd51004233bdd6804233bdd5804233bdd4804233bdd2804233ede6680233f5e5580233f9e4480233fce2280233fd61180233fd96080233fd86080233fd95080233fd85080233fd94080233fd87080233fd92080233fd82080233fd91080233fd81080233bdd6880233bdd5880233bdd4880233bdc7880233bdd2880233bdc2880233bdd1880233fda6680233fd96580233fd86580233fda5580233fd96480233fd95480233fd86780233fd85780233fd96280233fd86280233fd95280233fd85280233fd94280233fd87280233fda2280233fd96180233fd86180233fd95180233fd85180233fd94180233fd87180233fd92180233fd82180233fda1180233fd96880233fd86880233fd95880233fd85880233fd94880233fd87880233fd92880233fd82880233fd91880233fd81880233b9d4819633bcd2819633bd51819633bd90819633f1e5591233b9d4815e33b5d5818a33b9d4818a33bd51818a33bd90818a33adc6854a33b9d4814a339dc7850a33ece6688a33b9d481c633add6808633b5d5808633b9d4808633bd90808633ed66684633f565584633f964484633fc62284633b5c5858233add6814233b9d4814233bcd2814233bd51814233bd41848233add6804233b5d5804233b9d4804233bcd2804233eda6680233f5a5580233f9a4480233fca2280233fd21180233 else 0x5b027010406802700d0034000bdc7899a33bdc2899a33bdc0899a33edc7899a33bdd4819633bdd2819633bdd1819633bdd0819633bdc7895633bdc2895633bdc0895633f5c7895633ede6659233f5e5559233bdc2859233bdc0859233bde8859233ede6655233f5c6555233f5e5555233f9d6455233bdd6855233bdc2855233bdc0855233bde8855233f9d6591233f9c6591233f9e5591233bdd2819e33bdd1819e33bdd0819e33bdd2815e33bdd1815e33bdd0815e33ede6658a33edc6758a33bdc7858a33bdc0858a33bde8858a33edd6218a33bdd4818a33bdd1818a33bdd0818a33f5d6554a33f5e5554a33f5d5454a33f5c5754a33fcd6254a33bdd6854a33edc6854a33bdc7854a33bdc0854a33bde8854a33f5d5214a33bdd4814a33bdd1814a33bdd0814a33ede6650a33f9d6450a33f9d5450a33bdd6850a33bdd5850a33ddc7850a33bdc0850a33bde8850a33ede661ca33f5e551ca33bdd681ca33bdd581ca33bdd181ca33bdd081ca33bde881ca33ede6688a33fcd6288a33fcc6288a33fcd5288a33fcc5288a33fcd4288a33fcc7288a33bdd6888a33bdd5888a33bdd4888a33bdc7888a33bdd1888a33bdd0888a33bdc0888a33fce6688a33fcd6588a33fcc6588a33fce5588a33fcd6488a33fcd5488a33fcc6788a33fcc5788a33fcd6888a33fcc6888a33fcd5888a33fcc5888a33fcd4888a33fcc7888a33fcd1888a33fcc1888a33fcd0888a33fcc0888a33ede6658633edc6558633edd6258633fce2258633bdc7858633bdc2858633bdc0858633bde8858633fce2218633bdd4818633bdd2818633bdd0818633f5c6554633f5e5554633f9e4454633f5d5254633fce2254633fd56154633bdd6854633bdc7854633bdc2854633bdc0854633bde8854633f9e4414633fce2214633bdd4814633bdd2814633bdd0814633ede6650633f5e5550633f9d4250633fce2250633fd56150633bdd6850633bdd5850633bdc2850633bdc0850633bde8850633ede661c633f5e551c633fce221c633fd5511c633bdd681c633bdd581c633bdd281c633bdd081c633ede6648633fce2248633fd56148633fd47148633bdd6848633bdd5848633bdd4848633bdc7848633bdc0848633bde8848633ede6608633fce2208633fd55108633fd54108633fd52108633bdd6808633bdd5808633bdd4808633bdd0808633ede6684633f5e5584633f9e4484633fce2284633fd56184633fd55184633fd54184633fd52184633bdc7884633bdc2884633bdc0884633fd66684633fd56584633fd46584633fd65584633fd56484633fd55484633fd46784633fd45784633fd56284633fd46284633fd55284633fd45284633fd54284633fd47284633fd62284633fd46884633fd45884633fd47884633fd42884633fd40884633ede6658233edd6558233f5) else (if i<3 then 0x110000000000700e00e0080088888000000044444000000000000180e0282060262070302c06040c04440c01e01c05458030830830820c01c01c010602620030111030141600f00e00e00c2262c06050830888818038038020060282060222060282c01c01c0100000e01e01e01e01e01000180a0b0131030111030151700e02844780a911e0222e01c01c01000000001803803803c038038020000180a0b013103011160282c01c01e01c01c044580308a8a114142262841c010600e00e00e0222000000011040882000000441c01c01c01e01c05458038020022080000000882000000000000000882000000000000038602a509c3015284e180a94270c054a13050603e060a0f86030549c30182a4e180c15270c060a9386030549c3018284121c5828301f0222e18088f860223e18088f860223c14180f050603c14180f050603e180c14270c060a1386030509c3018284e180c14270c0447c30111f0c0447c30111f0c0447828301e0a0c07828301e0a0c07828301ce1a6f536e9b4cd7669533e995cc7e6273079814bf65f12e5965cafe5752ae954ca5a515270927c90e47d22b913486a41d2028fb47aa3bd1d98e6c70636b1a98d246623191808b6c58629d142897c48e22f10b87c43b21cf0db867c30e17d0ab84c42320f306d82d411e08503d818c07a024fff7f9bfb9fd2fdd7ec3f4df9cfc97debec5f4af997c6bdcdec0f5b7ab3d29e8af4079dbcd9e62f2c793bc89e3af18789bc39e12efd778bbb1dc0ecd7643af1d36e8173ab9c1cc8e587263901c76e36711b879c16dff6f9b781b7edb36d736a5b3ad916c2b601af6d686b1b541a88d38692b4119f0cf367733a59bacd1662b2e594cca164e32258fac7162f314988cc33613b051810bfc5f82fad7bebd35e3aed175ebaa5d2ae81736b965c8ae31700b745b42d8d6bcb4b5a32d05678b375992cb5634b155882c2d60cb0157e2bdd5e4aed5742b71592ac4558aab1532a86540a9b94d2a5d528a8f9464a2650d28394129fd4f8a7953c09cd4e4270d3609ab4cc26313009744b42555284936491a47922490647d23d51e08dd46c23151808ad450a25511288443fa1e90ea86942ea14508a83941a20bd0548174021ffcfd87e73ea1f20f5c7943c09dd4ed275d3ac1d4ce9c7493a21cfce7472e3911c58e146fe3791bb4dd06e336f1b2cd706b33501a34d026753349974c9463e3159860c0a5f92f697a0bb85d02e216c4b585a72d11674b305932c39608aec5712b6159cac455d2a89514a7252d2909438a044f627893b09c04db26b13449984c726112d89624ac253928893a498249923891248423f91e88dc469232117c8b4455228112c88c44121e10dc82c3f51ea0ecc73237f1af0cf46382fb16d0ae454c28c13c897c48a22b10887dc3ba1c30d486202ce14609284101d40d0 else 0x1c038038020c01c054580380a0b807007004000602a2c04c10f00418020c0505803809941e026501130040889881c03c03c03c03c03c020e01e01c01c010600e00e00e02a2301c04c5c0380a0b007007807014160083007007004180a8b0141600e02a2141c04c58010800e01e0545c03c088b8040044100000c01c01c01e01c01c04ca0f002100088200000000000000004e14410600e02220700e02a44113011043c010600e00e00e0080180888180a0b007807011160284411300400c01c01c010030111030131600e00e0222c04c88226008000e01e01e01e01e044400602a2e01c01c0545803c038088b0061151420e00e008300700700701))
def theta3I8 (i : Nat) : Nat := 0x342b32cfc2700014a860ed098b29109dd25c8a6419106d4144b640001c650000000000385412f3c124184c01626843eb0dc000821c00080940000000c1d0000066000000084e00007000000f06006b62440000002c4b12edc39c46c000f26c000b288c4550b800002340000000cb200018c080f04349135c9f000376d0003821f3054175164000021a809c04045300018150901230000280681bbc3052d1c7bf1a586a20808bd3128000d2d40002283863dc2000070cc8420002a4ea27304e000205a518288fe23800060bfc5672adc92d983047e04f04328f400000000000002c2661cc819a07d85e4189040913c0007206c72b86985b95e3c84f19c000c11201ed1d40000002c7080c9c48000000031b000871f000040e802a02b848b1200000c173c8291bc4790002c95012647ad1d00780000000000000000020b801dc0000000000a2a8450496ac7112d98bf000000000010353297cc251300ad116385f621507e2118c03e06e47df0a18a3520c0000002c7f1230000d2a4e51c2dc00000014b9b224000d0fc80ef9b461b32be802925380fe14b4961014f31522300c32eb831b156c240001838522800000010b00010000f81fc990002090000281cd284c0b80a60ac924d81660d9b41000102c0000000000042d12780000001457702803d00034a7d2fab1a9050000508800021068b10000000e03501a00036b72176c231cddc11101dc7691a000000815402000085024c119628d1642c40441c91000010490400440430000823802020800011811820040000c1044087484042082
def theta3D9 (i : Nat) : Nat := 0x450609b0aa888498304d8554442441826aa888478a0c136155110930609aaa2238488a0c13554447093826c2aa223848c1361444708f0609aaa2211e0c136155110910609aaa2211e0c136144423c1826aa888e12304d55111c23cf141826aa888498304d551108f060c2a88468304d551108f060c2888468a0c1355444709382238448304d551108f84088448a0c1355444f0609aaa2211e0c136155110910609aaa2211e0c136144423c1826aa888e12304d55111c23c1826aa888478304d551108f0609aaa2211f08110893c50609aaa2212678a0c185503cf141830a2078a0c1340734f14182059e283045034f1418205eb1c8f7a6b9d099270a5e5b6d606a95239dd2fe42455858ff5ea3996f8d35983015a4a753723f41476cd617d29c4c47b0c71301bc26023001f799a33fbacb19fdc658cfef2ac67f759233fbaa919fdc678cfee2bc67f758a33fb8c519fdd528cfee29467f750a33fb8e519fde228cfeeb0c67f718633fbaa319fdc518cfeea0c67f71c633fba4319fdc218cfef08c67f758233fb8c119fdd508cfee28467f750233fb8e119fdd208cfee10467f744233fb82119fde008cf6f33467d795633f3c8919fce228cfeb08c67f680233
def theta3I9 (i : Nat) : Nat := (if i<1 then 0xb0000000241bf95e3219242e25ba8441080e0f00006aa69152653f018797c00000000000700503020003478514c0000419143af171000000030629049000000000004973f1cc548003f58c10000a07800000005d3740d54a07126f041c19d416b058201f8528c2dc83262734231442513d201a23a8000000060d302fb0c440bb9312997006b08b8c002000000050e8e02400010290000c0be0000000119070dba3b4000396620afa5e1803a8e7513763e08bac930800940ee48a396a3046a48ccb47016406c519440460c8b18fe1a000079169130c5cb87fa91046aa00024b0d0620001c4d04c60000f0fe61a9061b16ce2b061b0c10b809719d057c000488ef156e58e880518331ef44a000038bf723084c7484c851f29224948b778346235247b40c78337151e518c132893b1c321554230ea500008313099487021fa843f0bb8000b2bb824000078d140bcac4a09649470000000000000002049e4b603cc0d0420c0000081e08830a0044b4ae605c0000c47ec14e1290000000384068ded0ef00a94aa5f1101b903518718000021162978567141d09922f708cb8fb9167213985be905526e7d528418000913240e4000000000000001c218000a082000289f9060215f2252ca20000000101cd880817ff95d636000058ad000000038ad800030a74258000229c10e4e64ef3338650001a09c00070dd000081d900b80007245659541ed186f1120003cbdd57bf0dd84f103e1d17a2a4e043c9d318e72d68566021718720518337038b0eb517924d4092291cf03b83b946d00631981062a04d60e000000000401194e0001463c0160000c2ae22c4000716d00000000000189543000000000514bf07e000104e110d810c256982280000000032a8128000f1d3064646a80590001a4ed08b8000000071d0469335d000120500000000c2f4240898478a13075c06ec5d3402e122222d0cac838f1732614464f0cb0000a5bc00060c00000621fc4f8000429bc481826f81a90a964f8482142100008070000418bb304c54f07f6019000000000000000000000014a120a202e8a544c58516900016274000000042e0e59c03300000000000389580008291e1680000000000161ae8a2c83100006543c7d000000000044c4080007325c28dc8e98aeb3080002897000042ab617707909648286000000078ec421400000b168b20001c02903e8000a0074299042f97d61df833c000291b0000000000068a7601d5c1f85aa1360001a1d000070f5bceb80ae417910e202a000000f80001423058409826c408020000e00b34600240000640200310008204404700400018404404300018000114680600400100c0934c418901100914c0160c300f4830000c50002c404508008d0420ca04004014a00b60004100e04000c0011003440001c100438e140002008640042 else 0xe4a800040cc7140044f093800061e9a4e000000000001658288a995691eda1bfc630000632c42d0000087aec078032869f8c23328427984900000001716fc1710aa000181580000000000000000000000cd986635cbf112fac43612b43c08f321c9012c000000062436366472b89701f8000000000000000000147ce0a4e9940000000000070440000000697990260000046f93361c5e018000283ed114000000068d7b1040001c6de84f0001637c0000000000001ec00008b6008e00000000911120fe5db40030f1111fa12243088)
def theta3D10 (i : Nat) : Nat := 0x81c4023de33
def theta3I10 (i : Nat) : Nat := 0x1c3c00001c00000000302449ec68000002c82086043014000000c6e08a80d46509005c850054c3000000000000000000000289400000003649800800000000281b82348ec7385b449876c4f42dc6341287d005000c394298a1c790440028908006080c70050200800
def theta3Index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 1 3 1 7 1 2 theta3I7
  | 8 => lookupWord 71 298 6 14 8 2 theta3I8
  | 9 => lookupWord 144 599 6 15 9 2 theta3I9
  | 10 => lookupWord 18 62 5 12 6 2 theta3I10
  | _ => fun _ => none
def theta3Levels : Nat → Packing
  | 6 => (2,5,4,0,0,4,0,theta3D6)
  | 7 => (195,4,4,0,0,11,0,theta3D7)
  | 8 => (407,3,4,0,0,13,0,theta3D8)
  | 9 => (41,2,4,0,0,11,0,theta3D9)
  | 10 => (1,1,4,0,0,1,0,theta3D10)
  | _ => emptyPacking
def theta3Pack : Forest := ⟨191,10,g191.samples,theta3Columns,g191.autos,theta3Levels,theta3Index⟩
end PEqualNP.Outside.L_meta_2541.SignedProof
namespace PEqualNP.Outside.L_meta_2541.SignedProof
def nineColumns : IndexTree ColumnInfo := (.fork 29 (.fork 14 (.fork 7 (.fork 3 (.leaf [(0,0,0,0,15),(16,0,495,0,13),(64,0,447,0,13)]) (.leaf [(128,0,383,0,13),(1,0,510,0,12),(2,0,509,0,12),(2,0,1024,0,12)])) (.fork 3 (.leaf [(4,0,507,0,12),(4,0,1024,0,12),(8,0,503,0,12)]) (.leaf [(8,0,1024,0,12),(32,0,479,0,12),(32,0,1024,0,12),(256,0,255,0,12)]))) (.fork 7 (.fork 3 (.leaf [(256,0,1024,0,12),(17,0,494,0,11),(24,0,1024,0,11)]) (.leaf [(66,0,1024,0,11),(80,0,431,0,11),(80,0,1024,0,11),(132,0,1024,0,11)])) (.fork 4 (.leaf [(144,0,1024,0,11),(160,0,1024,0,11),(192,0,319,0,11),(192,0,1024,0,11)]) (.leaf [(320,0,1024,0,11),(0,16,486,9,10),(0,64,189,258,10),(3,0,508,0,9)])))) (.fork 14 (.fork 7 (.fork 3 (.leaf [(6,0,505,0,9),(12,0,499,0,9),(8,16,486,1,9)]) (.leaf [(2,64,189,256,9),(96,0,415,0,9),(4,128,347,32,9),(136,0,375,0,9)])) (.fork 3 (.leaf [(264,0,247,0,9),(288,0,223,0,9),(0,2,440,69,8)]) (.leaf [(5,0,506,0,8),(9,0,486,0,8),(19,0,492,0,8),(25,0,486,0,8)]))) (.fork 7 (.fork 3 (.leaf [(9,16,486,0,8),(0,32,94,385,8),(49,0,462,0,8)]) (.leaf [(70,0,441,0,8),(134,0,377,0,8),(164,0,347,0,8),(36,128,347,0,8)])) (.fork 4 (.leaf [(258,0,189,0,8),(280,0,231,0,8),(322,0,189,0,8),(258,64,189,0,8)]) (.leaf [(7,0,504,0,7),(21,0,490,0,7),(35,0,476,0,7),(273,0,238,0,7)])))))
def nineD9 (i : Nat) : Nat := 0x3e0020000000001f8010000007c004000000000000f800fc0040000000000000000089c39faf879bb9d2e46fb69aac45fae96ab055a692a9045a19027c3b9c8da682b918823c1b8c85a28118783214078280a00c7b92aa384dd54b14018fd2334709baa9628021df19a9d2d7553030073369de335aeaa60600e75522444b5d54c0c018cfa775b09baa9818031db466b6137553030063ba8896c26eaa60600c76d19ad95db14b8c01fb22446095260551803f68466c12a4c0aa3005ed8275825498154600f5b056b04a9302a8c017b62dd6095260551803b6c304a9576c0aa3007ad860952606aa54600e1f5444444dab4a0c018db97c530ab609318035f82385630499263005b725f4ac609324c600f5e056b049930298c017bc0ad6093260531802f785bac1264c0a63006ef060acc4c9814c600ede0c12655db0298c016bc8ad609326293180319f4eeb6576c52630062faa212caed7a4c600c7b4a9178c12b498c01eb61825498156931803d7830499303552630063ae9116caed8a48600c4fd442f95dab490c018dba445f2bb569218031bb466be576ad2430067cc9554c26d8284600fda0c1aa6c12a508c013f60cd54d8254a118033b6488be576a94230067748cd7caed52846008ef8be9395daa508c011df17db315b4ca11803f645112ac8911423007ed0a22558ce2284600
def nineD10 (i : Nat) : Nat := (if i<4 then (if i<2 then (if i<1 then 0x9ff15caed84846009ff12caed8484600dbf288aed5484600bfb2cc6164484600ddf27726d8384600dfd15326d83846009ff17c26d83846009ff15c26d83846009ff12c26d83846009ff2cc26d8384600ddf277aed83846009ff17caed83846009ff12caed83846009ff09caed8384600bdf09c61d73846009ff09c62d73846009ff2cc62d7384600dbf28826d73846009ff18c26d73846009ff2cc26d7384600ddf187aed73846009ff18caed73846009ff09caed7384600bfd09c61e3384600bfd2cc61e3384600ff32559118284600bbf2cc60d8284600fbd18354d82846009ff0bc54d8284600bfb14c26d8284600df725526d8284600dfd23326d82846009ff15c26d8284600dfb14c26d82846009ff13c26d82846009ff2cc26d8284600dfb244aed8284600dbf183aed8284600dfd233aed82846009ff15caed82846009ff13caed82846009ff09caed82846009ff0bc6115284600fbb2889115284600dfb18b91152846009ff0bc60d5284600fbd2888cd5284600ffa2446095284600fbe1836095284600ff61536095284600ffc2336095284600bfe09c6095284600bfe2cc6095284600dbf28826d5284600dfd23326d52846009ff18c26d52846009ff13c26d52846009ff2cc26d5284600bdf17caed5284600dfb244aed5284600dfd233aed5284600dfe182aed5284600ddf17caed52846009ff13caed52846009ff09caed52846009ff0bc6154284600fbb2885514284600df725562d4284600dbf28856d4284600dbf288aed4284600df7255aed42846009ff18caed42846009ff15caed42846009ff0bc6153284600bfe2cc60932846009ff09c62d32846009ff2cc62d3284600dbf28856d3284600dfe18256d32846009ff18c56d32846009ff09c56d32846009ff2cc56d3284600dbf28826d3284600df725526d32846009ff18c26d32846009ff15c26d32846009ff2cc26d3284600dbf288aed3284600dfe182aed32846009ff18caed32846009ff15caed32846009ff09caed3284600ff62556122284600bfe2cc6122284600fbe2885522284600ffa1845522284600bfe18c5522284600bfe2cc5522284600ffa1859122284600bfe09c60e2284600bfe2cc60e2284600fbe28854e2284600ffc18354e2284600bfe18c54e2284600bfe09c54e2284600bfe2cc54e2284600ffc1858ce22846008ff11c26eaa58a00ccfa775aeaa60600ceba445aeaa60600ceda335aeaa60600ceea225aeaa606008ef96c26eaa606008ef96caed8a5c600fb61825498154600c7ea2226d5a506008df97c2ad824c600fbc1824c9814c6008ef96caed8a4c6008fe92caed7a4c6008ef96caed8a486008df97caed5a48600f9d2889de33846009fb14c26d82846009df17caed5284600fba2889122284600ff22559122284600ff42558ce2284600 else 0x8ff89c5eeaa4c600cbfa8856eaa4c600cfea2256eaa4c600cff18156eaa4c6008ff89c56eaa4c600efc9324aeaa4c600cbfa884aeaa4c600cfe9524aeaa4c6008ff98c4aeaa4c6008ff95c4aeaa4c6008ff89c4aeaa4c600afb94c26eaa4c600cbfa8826eaa4c600cdfa7726eaa4c600cf7a5526eaa4c600cfea2226eaa4c6008ff98c26eaa4c6008ff95c26eaa4c600cfb94c26eaa4c6008ff92c26eaa4c6008ff93c2ad85486008ff95c2ad8448600afb8ac61644486008ff9ac26d83486008ff95c2ad83486008ff9ac26d5348600cbfa882ad53486008ff98c2ad53486008ff9acaed5348600afd8ac6163348600bfe12caed3148600dbf288aed3148600dfe12caed31486009ef96caed8a486009ff11caed8a486008ff8bc54d8a48600aff2cc4c58a48600cf7a5526d8a48600cfda3326d8a486008ff95c26d8a486008ff93c26d8a486008ffacc26d8a48600aef96caed8a48600aff11caed8a48600cfba44aed8a48600cff131aed8a48600cbf98caed8a48600cef96caed8a486008ff95caed8a486008ff93caed8a48600cfe92caed8a48600cff11caed8a486008ff89caed8a486009df97caed5a48600ebba889115a48600cfba4462d5a48600cfda3362d5a486008ff89c62d5a486008ffacc62d5a48600a7f89c52d5a48600cbfa8826d5a48600cfda3326d5a486008ff98c26d5a486008ff93c26d5a486008ffacc26d5a48600adf97caed5a48600cbfa88aed5a48600cfba44aed5a48600cfda33aed5a486008ff98caed5a48600cdf97caed5a48600cf795caed5a486008ff93caed5a48600cfe92caed5a48600cff11caed5a486008ff89caed5a4860097f89c56d4a486009fe92caed3a486008ff89c62d3a486008ffacc62d3a48600cbfa8856d3a486008ff98c56d3a486008ff89c56d3a486008ffacc56d3a48600cbfa8826d3a48600cf7a5526d3a486008ff98c26d3a486008ff95c26d3a486008ffacc26d3a48600afe92caed3a48600cbfa88aed3a486008ff98caed3a486008ff95caed3a48600cfd93caed3a48600cfe92caed3a48600cff11caed3a486008ff89caed3a48600eb7a889549a48600ebda888cc9a48600ef5a558cc9a48600cf7a5562c9a48600cfda3362c9a486008ffacc62c9a48600cbfa8856c9a48600cfda3356c9a486008ff98c56c9a486008ffacc56c9a48600cbfa884ec9a48600cf7a554ec9a486008ff98c4ec9a486008ff95c4ec9a486008ffacc4ec9a48600cbfa88aec9a48600cf7a55aec9a48600cfda33aec9a48600ebba88912aa486008ff8bc54eaa48600ebf2884c6aa48600aff2cc4c6aa48600cfba4462eaa48600cff13162eaa48600cbfa8856eaa48600cfba4456eaa48600cfda3356eaa48600cbfa884eeaa48600cbfa8826eaa48600cf7a5526eaa48600cfda3326eaa48600) else (if i<3 then 0xcfb94c2ad824c6008ffacc2ad824c6008ff9acaed824c6008ff8acaed824c600afe8ac609524c6008ff9ac26d524c600cbfa882ad524c6008ff98c2ad524c6009df97caed524c6008ff8acaed524c600ffc11c609324c600efc8ac609324c600bfc8ac609324c600bfcacc609324c600dbda8826d324c6009fdacc26d324c600dfc982aed324c6009fd89caed324c600bbf09c609814c600ebf0ac609814c600bbf0ac609814c600bbf2cc609814c600fbe182549814c600bfd09c4c9814c600bfd2cc4c9814c600bef16caed814c600ddf277aed814c600dbf182aed814c600dfd132aed814c600dfe222aed814c600def16caed814c6009ff12caed814c600abf8ac6098a4c600fbc9824c98a4c6009ef96caed8a4c600abfacc6098a4c600ebe9825498a4c600cdfa7726d8a4c600cfea2226d8a4c6008ff95c26d8a4c6008ff92c26d8a4c6008ffacc26d8a4c600aef96caed8a4c600cdfa77aed8a4c600cbf982aed8a4c600cbf98caed8a4c600cef96caed8a4c6008ff95caed8a4c600cfd93caed8a4c6008ff92caed8a4c600cff11caed8a4c6008ff89caed8a4c600adf8ac61d7a4c6009fe92caed7a4c600adf89c61d7a4c6008ff89c62d7a4c600cbfa8826d7a4c6008ff98c26d7a4c6008ffacc26d7a4c600cbfa88aed7a4c6008ff98caed7a4c600af78ac5495a4c6009ff11caed5a4c6008ff8bc6095a4c600ebea888895a4c600ebf1826055a4c600ef71526055a4c600efe2226055a4c600aff2cc6055a4c600cfea2226d5a4c6008ff92c26d5a4c6008ffacc26d5a4c600cfea22aed5a4c600cff181aed5a4c600cfd93caed5a4c6008ff92caed5a4c600cff11caed5a4c6008ff89caed5a4c6008ff8bc61c9a4c600e9fa889dc9a4c6008ff8bc6089a4c600ebea888889a4c600ef6a558889a4c600cdfa7762c9a4c600cf7a5562c9a4c600cbf98262c9a4c600cfea2262c9a4c6008ffacc62c9a4c600cbfa885ec9a4c600cbfa8856c9a4c600cf795256c9a4c600cfea2256c9a4c6008ffacc56c9a4c600cbfa884ac9a4c600cf7a554ac9a4c6008ff98c4ac9a4c6008ff95c4ac9a4c6008ffacc4ac9a4c600cbfa88aec9a4c600cdfa77aec9a4c600cf7a55aec9a4c600cfea22aec9a4c6008ff98caec9a4c6008ff95caec9a4c6008ff92caec9a4c600c7f89caec9a4c600dbf18162eaa4c600cbf98a62eaa4c600cf795a56eaa4c600dfc9324aeaa4c600c7f89a26eaa4c6008ff8bc61eaa4c600e9fa889deaa4c6008ff8bc60aaa4c600efc9824caaa4c600afd89c4caaa4c600afdacc4caaa4c600ebea8888aaa4c600edf277606aa4c600ebf182606aa4c600efd132606aa4c600efe222606aa4c600aff2cc606aa4c600ebf18162eaa4c600cdfa7762eaa4c600cfea2262eaa4c6008ff89c62eaa4c600cbfa885eeaa4c600 else 0xcef89c5aeaa60600cfba4456eaa606008ff89c56eaa60600cdfa774eeaa60600cbf9824eeaa60600cfea224eeaa606008ff89c4eeaa60600cfba444aeaa60600cfda334aeaa606008ff89c4aeaa60600cef96b26eaa60600aff11c26eaa60600cdfa7726eaa60600cfda3326eaa60600cfea2226eaa60600cef96c26eaa606008ff95c26eaa606008ff93c26eaa606008ff92c26eaa60600cff11c26eaa606009dfacc26d875c600bdd89c61e335c600cfda3326d8a5c6008ff93c26d8a5c6008ffacc26d8a5c600cfda33aed8a5c6008ff93caed8a5c600ebda888cc9a5c600cfda3362c9a5c6008ffacc62c9a5c600cbfa884ec9a5c6008ff98c4ec9a5c6008ffacc4ec9a5c600cbfa88aec9a5c600cfda33aec9a5c600adf89c61eaa5c600edd9878ceaa5c600cfda3362eaa5c6008ff89c62eaa5c600cbfa884eeaa5c600cdf9874eeaa5c6008ff89c4eeaa5c600cbfa8826eaa5c600cfda3326eaa5c6008ff98c26eaa5c6008ff93c26eaa5c600fbaa8888a44546009fb94c26d82546008ff9ac26d8254600afb94c2ad8254600cfba442ad8254600cfda332ad82546008ff93c2ad82546008ff9acaed8254600cbfa882ad42546008ff98c2ad42546008ff9ac26d32546008ff98c2ad3254600ffa2229118154600fbb2446098154600fbd2336098154600bbf09c6098154600ebf0ac6098154600bbf2cc6098154600ff32445498154600ff52335498154600fbe1824c98154600dfd23326d8154600df715226d8154600dfe22226d81546009ff2cc26d8154600bef16caed8154600dfb244aed8154600dfd233aed8154600dbf182aed8154600df7152aed8154600def16caed81546009ff09caed8154600d7ea2226d4a54600d7f18126d4a5460097facc26d4a546009ff11caed3a54600a7f89c5292a5460097f89c52d2a546009df97caed2a54600ebea888889a54600efca338889a54600cfea224ec9a546008ffacc4ec9a54600cbfa884ac9a54600cfda334ac9a546008ff98c4ac9a546008ff93c4ac9a546008ffacc4ac9a54600cfda33aec9a54600cfea22aec9a54600a7f89c52aaa54600efaa22912aa546008ff8bc60aaa54600efb244606aa54600efd233606aa54600ebf182606aa54600ef7152606aa54600aff09c606aa54600aff2cc606aa54600cff1814eeaa54600cfba444aeaa54600cfda334aeaa54600cfda3326eaa54600cfea2226eaa54600cfb94b2ad8250600a7f89c6ad52506009df97caed52506008ff8bc6095a50600ebea888895a50600c7f98226d5a50600ebea8888aaa506008ff9ac26d874c6008ffacc2ad874c6008ff9acaed874c6009ff11c26d824c6008ff9ac26d824c600cff11b2ad824c600adf97c2ad824c600afb94c2ad824c6009df97c2ad824c600cdf97c2ad824c6008ff95c2ad824c600)) else (if i<6 then (if i<5 then 0x8ff91c26eaa60a009ef95caed6358a00aefacc58c9a58a00cfda3356c9a58a008ffacc56c9a58a00cf7a554ec9a58a008ffacc4ec9a58a00cf7a55aec9a58a00cef963aec9a58a00cfda33aec9a58a008ff89c56eaa58a008ff89c4eeaa58a00cf7a5526eaa58a00cfda3326eaa58a008ff95c26eaa58a008ff93c26eaa58a00bfa94c26d824ca00bfc93caed824ca00dfc93caed824ca009fd93caed8a4ca008ff91c26d8a4ca008ffacc26d8a4ca00afd93caed8a4ca00cfd93caed8a4ca00cfe92caed8a4ca008ff91caed8a4ca008ff89caed8a4ca009fe92caed6a4ca008ff95c26d6a4ca008ffacc26d6a4ca008ff95caed6a4ca009df97caed5a4ca009fe92caed5a4ca009fe92caed1a4ca008ffacc62c9a4ca00cbfa8856c9a4ca00cefa6656c9a4ca008ffacc56c9a4ca00cbfa8846c9a4ca008ffacc46c9a4ca00cbfa88aec9a4ca00cefa66aec9a4ca00afeacc60aaa4ca008ff89c62eaa4ca008ff89c5aeaa4ca00cefa6656eaa4ca00cfe98256eaa4ca008ff89c56eaa4ca008ff89c46eaa4ca00afb94c26eaa4ca00afd93c26eaa4ca00cbfa8826eaa4ca00cefa6626eaa4ca008ff98c26eaa4ca008ff95c26eaa4ca00cfb94c26eaa4ca00cfd93c26eaa4ca008ff91c26eaa4ca009fe95caed8488a009fe91caed8488a009ff11c26d73606008ff9ac26d7360600bbb94c26d8260600dbda3326d8260600dbb94c26d82606009bfacc26d8260600bbf11caed8260600dbba44aed8260600dbf11caed82606009bf89caed8260600fbaa446095260600bbe89c6095260600bbeacc6095260600cfba442ad5260600cfda332ad52606008ff93c2ad52606008ff95c2ad4260600bbeacc60932606008ff9ac26d32606008ff95c2ad3260600dbe982aed32606009ff11caed7a606009bf98caed3a606009ff11caed2a60600edda778cc9a60600efca338889a60600cfda335ec9a60600cfda3356c9a60600cfea2256c9a606008ffacc56c9a60600cdfa774ec9a60600cfea224ec9a606008ffacc4ec9a60600cfda334ac9a606008ff95c4ac9a606008ff93c4ac9a606008ffacc4ac9a60600cdfa77aec9a60600cfda33aec9a60600cfea22aec9a60600dcfa775aeaa60600deba445aeaa60600deda335aeaa60600daf9825aeaa60600deea225aeaa60600cef97a5aeaa60600cef95a5aeaa60600cef94a5aeaa60600cef93a5aeaa60600cef92a5aeaa60600edda778ceaa60600ebba4460aaa60600abf89c60aaa60600abfacc60aaa60600ebe98254aaa60600ebe9824caaa60600efaa4488aaa60600cfda335eeaa606008ff89c5eeaa60600ecfa775aeaa60600eeba445aeaa60600eeda335aeaa60600eaf9825aeaa60600eeea225aeaa60600cef9735aeaa60600cef9525aeaa60600cef9425aeaa60600cef9325aeaa60600 else 0x93f64e993564c192b649990b63ed8e0636d8cb63198b6629989661ed86b6199856611983660418005f697b45e917945db975e5d3973e5cb97135be16e85b356c85b0d6be5ae56b45a9169f5a696955a1567559c1655594164b591964158f163758c9617581d602579d5e257755cd56f55ad564958d562158355cd563557954e5525523547950e53cd4e353794c352cd4ae527949951f9463517944e50f942e50a542450253f94fd13ef4fa93da4f553ba4e7d39a4d793594d513444cd13194c252ee4ba52e44b252c44ad12af4aa928449a5259495124f492924548d521a48291fa47a91cf46d11a4465118445fd16f45a91654555150452d146450513c44b1127448911d44090fd43b50dd43350c842e10b342b908841e105d410903240890124008ff23f88fd23f08fb23e88f923e34f7d3db4f523d34f3d3c88f1d3c34f083c0cef33b60ec83b0cebe3ae4ea93a64e8939b8e533938e493910e343890e14383ce0a37bcddf373cdb43664d89358cd48350cd3e348cd13340cce8338ccde3364cc932e4cb43290c9f3268c7f31bcc543110c293064bf32f8cbc82f0cbbe2e8cb932e0cb682d8cb532d0cb3e2ce4b342c64b142c3cb0a2be8aea2b3caca2b14aaa2a68a952a40a752994a552940a4b2918a412898a212844a0c281ca0227f49f827cc9ee27a49e4277c9da27549d0272c9c627049bc26dc9b226b49a8268c9932638989261097f25e897525c096b256c956254494c251c942244490c241c8f723c88ed23a08d8234c8ce23248c422fc8ba22d48a52254890220087021ac86621588512130847210883d20e0833208c81e2064814203c80a20148001fc07e01f407cb1f187c11ef07b71ec87ad1ea07981e207781dcc76e1da47641d7c75a1d547501d2c7461d047311cb07271c887121c347081c0c6fe1be46f41b906df1b686d51b4068918dc5f016d0578151c4df12344300ef436b0c642b1097c20d0694153045c0ba0174000cfea2256c9a58e008ffacc56c9a58e008ffacc4ac9a58e00cfea22aec9a58e008ff95caec9a58e008ff92caec9a58e008ff89c56eaa58e008ff95c4aeaa58e008ff89c4aeaa58e00cfea2226eaa58e008ff95c26eaa58e008ff92c26eaa58e009fd93caed4a60a009ef96caed1a60a00df9a3352c9a60a00cfb93a52c9a60a00cfb91a52c9a60a009fbacc52c9a60a00ef9a3352c9a60a00afbacc52c9a60a00cfb94b4ec9a60a008ffacc4ec9a60a00cfb94b46c9a60a00cfda3346c9a60a008ffacc46c9a60a00cfb94baec9a60a00cfda33aec9a60a008ff93caec9a60a008ff91caec9a60a00c7f89caec9a60a00afb94c26aaa60a00c7f89a26eaa60a008ff89c4eeaa60a00cfba4446eaa60a008ff89c46eaa60a00afe92c26eaa60a00cfda3326eaa60a008ff93c26eaa60a00cfe92c26eaa60a00) else (if i<7 then 0x7c00b4207c00c430c43083e00400f00f0c258fc007c004317c00b42f8018561856185618561f801f801f801f801f001f00107c00f800fc0086207800f80084207800801e003e00200bc0040007c00fc00fc00f800842f0010040003c007c007c00400f8016c5e00390c310e210a21c4217c00f800b61887c50130800f801085f003f003e0021880007800f80083c00400f8018842683e00200be007c005b14430f800861087f003e00310800f801085f003f003e0020081e003e0020003e005a1000088418841f8016c4007c00842f801003e004217c00fc00800007800b620147080000000000000000000000000002ac200000000002ac20000001563346486020002ac200006084000000006c30ac30836186658400996100000000030c2000000002638664866184000000000261846684618400000000000000ab08000396100000000e584000038cd8fe29d0be00603706985e01cab96728f00fc1a6178072ae41e01b834c2f00e41e017834c2f00e51e016c7f06f8016c9c578b68ee29c1ba1f80f807093847c07c03281c03a0383c1ad19c4383711e82e51e0234770ae21a2383711f01f00388625510c23e03e01940bc1d0fa3b85710e0de03e01c23e96e15c4383711d87e03e01884e8ee11c5383780f80708fa3384706e23e03e01c33d96d2165388f80d81d02e03c04e8ed11a5388fc0e802acfa2388f80e8070cb6434a711f01b03a05c07808b21a5388f80d81d02e03c04590d29c47c06c0e81701e0227539d0e7339cba71e9c3a6fe9b8e6c89ae26a89a6268899e2673998e648990e63e98ba61e983a5fe97e65e9973a5be968e58895e25689562548950e53394ba529946651494124ff93ea4f593964e093424cb931a4c192c64a19272497921e477917244c911e42c907240c8fc63ec8f9e3d78ef23a18e463818dc63618d1a32b8c6e3168c463018bf22ec8b9e2e28b4a2b78a9e2a28a7628d89f626d89a2258892223888a2218884e20387fa1f9874e1b88676198862218385ce16e85a6164857e14f852a1458502130848211b84020f083ae0d082d609a8256090822e086820607181b2067815e05280de027805e01280360087fe1fe87f61fbd7eb5f927dddf5c7d31f317cb1f277c89f127c35f087c0defe7bb9ee97b91edf7b69ed57b15eaa7a69e8a79e9e757995e60796de567919e4178f1e2c7871e177849e0d7821df877a1dd87721dc376f9db976d1da47651d8f75fdd7a75a9d4f7529d2f747dd1a7455d10742dd0673d9cf173b1cdc735dcd27309cb272b5c9d7235c7d71b5c5d7135c3d70b5c1d7035bfd6fb5be86f8dbd36f39bc96f11bbf6ebdbaa6e69b956e41b756dc1b6b6d99b616d71b576d49b376a35a72695da4768dda3268b5a286861a0867e19d266dd99c665d992660997d65b5968658d95e65659546511 else 0x1f003f0020f801f801f801f0010c5f002d0a1587e007e007c007c0041f003f01e108000821f801f801f80107c00fc008228821f801045f0020894207e0042007e0041f002007c0083e0040007c0083e0040007c00fc00801f003f003c2be00bc0041e00200be007e007c00401001e003f002d0bc004017c00fc00f800f800f800802f001005f002007c0083e004002921f801685f002007c00fc00fc008215861587e007e007e0041f00200742f801347f00210b837c0103e0041e00200001f0020003c007c0041f00210bc0041e00200bc0040178008020000007c00801f0020f8010c5f003f0020002210621062107c034514420f800ae2f001845e00290bc007c006e1000028a100000f8010000007800f807862f001f001f80107c008000f801003e007e00400003e007e007e007e00400003e007e0041e00208841f8016c40f801085f002000000f801003e00400f801f80107c00fc00f800841085f0f800f800c470f800fc00f800e4b0801f00200001e0020f80100386780100000000069609850a74ac8ff1de2b48788e23f0fe17c0d83610160267f800802d8609842683e0020003e00621862187e00430843f8010c5f0031080031e1078008000000a5840000000d284685e003e002d08106820f801f001f001f801245f0020f001f001f001e15a23c00fc00785688f003f0010c208fc007c007c007108e3f80188e1f001f001f001885e01248924846382b10000003e0040007800fc0083857801000000000f0031c5e0020f0011c4007c00fc00fc00f8008420001e003e0020f00107c00b616860f001c8ff005f0020f801085f0020f00107800802f0016840f001f00189a1003e004317c008000f00107c00b42f8013440f801882d04908e500221062107e004714420fc00b62003e0047103e00400f80108020fe004317c00800007c00fc00862f8015081f001f001005e00200bc0042007c0041e0020014508000000a484000)))
def nineI10 (i : Nat) : Nat := 0x3602902800c72100000000000000240300000000000c24f0ae4430001c01307400000000000001c0f000240b0084000f01381f605fc448117c19000282a310a020c01c000611f54b9613c00202218910240002098429205800000024158016406108e80d904a810e062422d051025d00a01ef813c5d1068000000241b90390130070827c045c2818d0c1a000400561091c1000247
def nineD11 (i : Nat) : Nat := (if i<7 then (if i<3 then (if i<1 then 0x60551802ff95db02a8c015fe26d4a54600dfb4664d2a3006fea22269518027fc9d934a8c013fe4ac9a546009ff5764d2a3006fba44aa9518037ed19d54a8c01bfc606aa546009ff277552a3004ff92baa9518027fc4dd54a8c01eeea214250600f7d51111283007fa984889418037f511314a0c01bfa8895a50600d7f51155283006fea22aa9418027fc55b0e98c01e7ea22774c6009ff156c1263004ff8ab54931803fe4c126498c017f626d324c600bfb57699263007bea8888931803ef93bb0298c01efc609814c600ffa264c0a63007fe22260531802ff95db0298c01b7e9dd8a4c600d7f304c5263004ff89b629318027fd5db1498c01afea217a4c600dbf30ebd263004ff98b5e9318027fc4daf498c013feaed7a4c600dfd444ad263006ff181569318027fc4dab498c013feaed5a4c600d7f5104d263006dfa77269318037bd2a93498c01bfa8889a4c6009ff3164d263004ff97b269318027fcad93498c013fe4ac9a4c6009ff5764d263006bfa88aa9318036fd3bd5498c01bf64caaa4c600dfd44555263006ff181aa9318027fcc5d5498c013fe5eeaa4c6009ff2b755263004ff92baa9318027fc4dd5498c013fe2ad85486009ff156c2243007bba88911218027fc55b0690c013fe2ad5348600f7e51098a43005ff2bb4c5218037dd2231490c01bfc4c58a486009ff136c5243004ffabb629218035fd442b490c01bee9115a48600dfb466ad243004ff98b569218027fc4dab490c013feaed5a48600d7f510a5243006bfa884e9218027fcc5a7490c013fe56d3a486009ff1369d243004ffabb4e9218035fd4413490c01bde9549a48600dfb4664d243004ff98b269218027fcad93490c013fe4ec9a486009ff5764d243006bfa88aa9218037dd2255490c01bf68ceaa48600dfe26355243004ff98baa9218027fcadd5490c013fe4eeaa486009ff13755243005ff2bb61211803df9442a908c01fec6115484600bfe316aa423005ff2bb55211803fd8c2c8908c01f7c9dd8384600bfe136c1c23005ff2bb60e11803ef8c3ae708c017fc62d7384600bfe136b9c23005ff2bb5ce11803fe8c3c6708c01fec9118284600f7e306c1423007fd23360a11802ff84db0508c017fcaed8284600ff6488a9423007fd23354a11803ff0c12a508c017fc26d5284600bfe576a9423007bf28850a11803fb92aa8508c01fec5514284600bfe316a1423005ff15b50a11802ff95da8508c01efca213284600ffc30499423005ff18b4ca11802ff8ada6508c017fc26d3284600bfe57699423007fe18488a11803ff0aa44508c01ff860e2284600ffc2a711423004fb94b26982803dd544489114013be5aeaa606008ff136ad283007bb28891211803f992ac8908c01ef4a223384600fba4ef19c23007be28888a11803fd12244508c01ff08ce2284600 else (if i<2 then 0x17fe4ec9a48600dff30a4d243006ff983269218037fca993490c01bfe62c9a48600dff2b64d243006ff93b26921803dfd4455490c01fee912aa48600ffb46755243007ff131aa9218037fcc555490c01bfe56aaa48600dff29555243006ff93aaa9218037fcc2d5490c01bfe612aa48600dff2a955243006ff983aa9218037fca9d5490c01ffc5ed8384600ffe256c1c23007ff09b60e11803ff95db0708c01ffc62d7384600ffe136b9c23007ff2bb5ce11803ff8aa30508c01ffc54d8284600ffe2b6c1423007ff14b60a11803ff89db0508c01ffc26d8284600ffe576c1423007ff18454a11803ff8c1aa508c01ffc52d5284600ffe276a9423007ff09b54a11803ff95daa508c01ffc6154284600ffe30a99423007ff18b4ca11803ff8ada6508c01ffc26d3284600ffe57699423006fea22269638027fcad934b1c013fe4ac9a58e009ff5764d2c7004ff95baa9638027fc95d54b1c013fe26eaa58e00bf72964d305006fda33269828037dca5934c14013fe4ec9a60a009ff2364d305004ffabb269828037dd22554c14013fe4eeaa60a009ff23755305004ff89baa982802f7d5dac6b1401bde9549a58a00ddf2c64d2c5006fda33269628027fcad934b14013fe4ec9a58a009ff5764d2c5006ef963aa9628027fcadd54b14013fe4eeaa58a009ff137552c5004ff98baa9428027fcadd54a14013fe46eaa50a00bfd576c1265004ff89b629328027fd5db14994013fe26d6a4ca009ff576b5265006bfa882693280377d33134994013fe62c9a4ca009ff2d64d265004ff95b269328027fc8d934994013feaec9a4ca00ddf4cd55265006fe982aa9328027fcc5d54994013fe5aeaa4ca009ff2b755265004ff91baa9328027fc4dd54994017faaed8488a009ff156b9b03007dda778cd81803ddd22304c0c016fe26d8260600b7f576c1303007be982549818027fc55aa4c0c013fe2ad4260600f7d30499303004ff8ab4c981803fd522444c0c01b7e9dc9a60600dfb4664d303006fea22269818027fcbd934c0c013fe56c9a606009ff2764d303004ff92b269818027fd5d934c0c017be5aeaa60600dbf4ef55303006fba44aa9818037ed19d54c0c01afe60aaa60600dfd44555303004ff97baa98180377cb5d54c0c013fe56eaa606009ff27755303004ff92baa9818027fc4dd54c0c0177e26d875c600bbf576c3ae3004ff8ab60d71803eecc3c66b8c01bf68cd8a5c6009ff136c52e3004ffabb629718035fd44134b8c01bf68cc9a5c6009ff3164d2e3004ff93b269718027fd5d934b8c01afea22aa5c600dbf30f552e3006fda33aa9718027fcc5d54b8c013fe4eeaa5c6009ff137552e3007faa22911518027fc55b04a8c013fe2ad42546009ff156992a3007fb24460551803fe919b02a8c01efc6098154600fee2a4c0aa3005ff09b else 0xa4c5263006ff97b629318037fcadb1498c01bfe4ad8a4c600dff136c5263006ffabb62931803dfd442f498c01f7e61d7a4c600ffe302bd263006ff98a5e931802ffcc5af498c017fe26d7a4c600bff576bd263006ff89b5e931803dfd442b498c01fde5495a4c600ffb264ad263007fea2256931803ff8c0ab498c01bfe6295a4c600bff136ad263005ffabb569318037fcc12b498c01bfe4ad5a4c600dff136ad263006ffabb56931803dfd4425498c01ffc6052a4c600dff31495263006ff95a4a931802ffcc5a5498c017fe56d2a4c600bff13695263005ffabb4a931803dfd4413498c01f7e9dc9a4c600fef4aa4d263007fd93226931803ff51113498c01ffc6049a4c600dff3144d263006ff97a269318037fcad13498c01bfe4a89a4c600bff3164d263005ff97b26931802ffcad93498c017fe4ac9a4c600bff5764d263006ff987269318037fcc113498c01bfe5489a4c600dff3164d263006ff97b269318037fcad93498c01bfe4ac9a4c600dff5764d263007bfa88aa931803efd3bd5498c01ff64caaa4c600ffd44555263007ff181aa9318037fcc555498c01bfe5eaaa4c600dff2b555263006ff92aaa9318037fc4d55498c017fe62eaa4c600bff2f755263005ff95baa931802ffc95d5498c017fe26eaa4c600dff30f55263006ff982aa9318037fca955498c01bfe62eaa4c600dff2f755263006ff95baa9318037fc95d5498c01bfe26eaa4c600bff576c2243007bfa8855121803fdcc22a890c017feaed5448600ff730b22243005ff89b60d218037fcd5b0690c017feaed8348600f7f510a9a43007fd98354d21802ffc4daa690c01bfe6ad5348600dff156a9a43005ffabb54d21803fecc2c6690c01ffc6153148600ffe31698a43007ff15b4c521803ff84da6290c01ffcaed3148600ff7488c5243007ff13162921802ffc4db1490c017feaed8a48600dff2a8c5243006ff953629218037fcadb1490c01bfe52d8a48600dff276c5243006ff89b629218037fd5db1490c01efea215a48600ff7488ad243007fda3356921803ff898ab490c01bfe6295a48600bff316ad243005ff89b56921802ffd5dab490c01bfe6115a48600dff306ad243006ff98b569218037fca5ab490c01bfe4ed5a48600dff136ad243006ffabb56921803dfd4429490c01fde9554a48600dff314a5243006ff95a52921802ffcc5a9490c017fe56d4a48600bff576a5243006ff98552921803dfd4427490c01bfe6293a48600dff2b49d243005ff98b4e921802ffcada7490c017fe26d3a48600bff5769d243006ff9854e9218037fcc5a7490c01bfe56d3a48600dff1369d243006ffabb4e921803dfd4413490c01fde9549a48600ffb4664d243007ff131269218037fcc513490c01bfe5689a48600dff2744d243005ff98b26921802ffcad93490c)) else (if i<5 then (if i<4 then 0x1802ffcbd934c0c017fe56c9a60600bff2764d303005ff92b269818037fcb9934c0c01bfe5489a60600dff2644d303006ff97b269818037fcad934c0c01bfe4ec9a60600dff2564d303007dfa77aa981803fdd22554c0c01ff68ceaa60600f7f30555303007fea22aa9818037fcbd554c0c01bfe56aaa60600dff29555303006ff93aaa9818037fc95554c0c017fe26eaa60600dff2e755303006ff952aa9818037fca1554c0c01bfe4caaa60600dff13755303007df89b61d71802ffc4db06b8c01bfe6ad835c600bff576c1ae3007fda3362971802ffc4db14b8c01bfe26d8a5c600f7f5109d2e3005ff89b4e971803dfd44134b8c01f7e61c9a5c600ffb4664d2e3006ff98a269718037fc9d134b8c017fe62c9a5c600bff2764d2e3006ff983269718037fcc5934b8c01bfe4ec9a5c600f7f511552e3007fda33aa9718037fcc1d54b8c01fee9118254600ffb466c12a3005ff89b609518037fcd5b04a8c01bfe2ad8254600bff576c12a3007bfa8850951802ffcc5a84a8c017feaed4254600ffd304992a3005ff98b4c951802ffc4da64a8c01bfe6ad3254600bff576992a3007ff14260551803ff899302a8c01ffc52d8154600ffe276c0aa3007ff12b60551803ff84db02a8c01ffcaed8154600ff7284a52a3007fea2252951803ff8c0a94a8c01dfe26d4a54600bff576a52a3007ff1814e951802ffc4da74a8c017feaed3a54600ff7488952a3007fda334a951803ff8c0a54a8c01bfe6292a54600dff294952a3006ff93a4a951802ffcc5a54a8c017fe52d2a54600bff276952a3005ff89b4a951802ffd5da54a8c01ff68cc9a54600ffd4444d2a3007ff181269518037fc9d134a8c01bfe4a89a54600bff2764d2a3005ff92b269518037fcc1134a8c01bfe4c89a54600dff2764d2a3006ff92b26951803fdd22554a8c01ff68ceaa54600ffe303552a3006ff94aaa9518037fc9d554a8c01bfe4aaaa54600dff305552a3006ff942aa9518037fc99554a8c01fee52d8250600dff356c1283006ff8ab60941802ffd5db04a0c01efea215250600ff7308a9283007fe982549418037fcd5aa4a0c017feaed5250600dff2a4c5283006ff982569418037fcc1554a0c01bfe54aaa50600bff136c3a63006ff8ab61d31802ffc55b0e98c017feaed874c600ffe236c1263005ff89b609318037fcd5b0498c01bfe2ad824c600bff156c1263005ffabb60931803dfd442a498c01ffa609524c600bff136a9263006ff9ab54931802ffc55aa498c017feaed524c600ffb31699263007fd95b4c931803fec4da6498c01ff6aed324c600ffe2a4c0a63007ff17b60531803ff8adb0298c01ffc4ad814c600ffe136c0a63007ff2bb60531803efd3bb1498c01efe6098a4c600ffb264c5263007fea2262931802ffc4db1498c017feaed8a4c600dff2 else 0xe26d2a58e00ffd4444d2c7006ff95a269638037fc95134b1c017fe56c9a58e00bff2564d2c7005ffabb269638037fcad934b1c01bfe4ac9a58e00dff5764d2c7006ff89aaa963802ffcadd54b1c017fe4aeaa58e00dff2b7552c7006ff92baa963802ffd5da94c14017fe26d3a60a00bff5769d305007fba44469828037fcad234c1401bfe5291a60a00dff2748d305005ff89b46982802ffd5da34c1401ff68cc9a60a00dff2744d305006ff91a26982803fdca5934c14017fe4ec9a60a00bff2364d305005ffabb269828037fc9d934c1401bfe46c9a60a00dff5764d305007fba44aa9828037fca5554c1401bfe4eaaa60a00dff23555305006ff89aaa982802ffca5d54c14017fe4eeaa60a00bff23755305005ff89baa9828037fca5d54c1401bfe4eeaa60a00dff23755305006ff89baa982803f7c4dac6b14017fe26d5a58a00bff1369d2c5007f7a5526962803f7cb1934b1401ff68cc9a58a00dff2b44d2c5006ff93a26962802ffcad934b14017fe4ec9a58a00dff2b64d2c5006ff93b26962803ff4adb0499401ffa46d824ca00ffd136c1265007feabb60932802ffc4db14994017feaed8a4ca00dff236c5265006ff89b629328037fd5db14994017fe26d6a4ca00bff576b5265006ff89b5a932803f7d332b499401ffa6095a4ca00dff314ad265006ff96a56932802ffc4dab4994017feaed5a4ca00ffd3048d265006ff98a469328037fcad234994017fe26d1a4ca00bff5768d265007bfa8826932803f7d3313499401ffa6089a4ca00dff3144d265006ff96a269328037fcad13499401bfe4689a4ca00bff3164d265005ff96b26932802ffcad934994017fe46c9a4ca00dff3164d265006ff96b269328037fcad93499401bfe46c9a4ca00fdf4cd55265007fe982aa9328037fcc555499401bfe5aaaa4ca00dff2b555265006ff91aaa932802ffc4dd5499401bfe26eaa4ca00bff136b9b03005ffabb5cd81803dfcadb04c0c01efe52d8260600f7f276c1303007bf89b60981803dfd5db04c0c01fee9115260600ffb466a9303005ffabb50981802ffc4da64c0c01bfe6ad3260600bff57699303007fda335e981802ffc4daf4c0c017feaed7a60600ff7488ad303007bf98256981802ffc4dab4c0c017feaed5a60600f7f304a5303007fea22529818037fcad294c0c017feaed4a60600fbf4ee9d303007bf9824e981803ff511274c0c01bfe5e93a60600dff2b49d303005ff97b4e981802ffc4da74c0c017feaed3a60600ff748895303007fda334a9818037fcad254c0c01bfe5292a60600dff27495303005ff95b4a981802ffca5a54c0c017fe4ed2a60600bff13695303005ffabb4a981803efd3b934c0c01ff68cc9a60600f7f3044d303007fea22269818037fcbd134c0c01bfe5689a60600dff2744d303006ff92a2698) else (if i<6 then 0x3260725a324ef246323d7237322e7225b217f211b208f1fdb1f9f1f3b1ed71e731e0f1dab1d471cbb1c071ba31b3f1adb1a7719eb198718fb1847176b1707162b159f14eb140f130b1257115310ef108b0f870f230e970dbb0cdf0c030b4f0a9b0a0f095b08f7086b078f068b05ff052304470393035702cb023f02030177009b000eff5aff1efe92fe2efdcafd8efd02fc26fb72fb0efa82f9f6f91af8def8a2f866f802f7c6f712f6aef622f5bef582f4a6f3f2f33ef28af1d6f172f136f082eff6ef92ef2eeecaee8eee2aedc6eceaec86ebaaeb1eea6aea06e9a2e916e88ae7fee772e6bee5e2e556e4f2e43ee3b2e34ee2c2e20ee15ae0cee06ae006df7adf66df02de9ede12ddfedd9add36dcd2dc96dc32dc1edbbadb06da7ad9c6d912d8aed7d2d746d692d5ded57ad49ed3c2d30ed282d1ced16ad106d0a2cfeeceeace5ecdd2ccf6cc42cbb6cadaca26c972c8e6c80ac7cec792c6b6c5dac54ec4eac40ec382c346c26ac18ec12ac0c6c03abf86bf22be96be0abda6bd1abcdebca2bc66bbb2bb4ebac2ba86b9aab8f6b842b7deb77ab716b68ab626b5c2b55eb4fab496b392b2deb22ab19eb112b086affaaf6eaee2ae7eae42ae06adcaad66ad2aacc6ac62abfeabeaab86ab22aae6aaaaaa46a9e2a9a6a91aa88ea82aa79ea762a74ea712a6aea672a60ea352a0969e029b1e983a9556929a90a68dea8c1e89da8796850281f67f127c567a1277a674ea72f6703a6da66b126806659a628e5f825cee59925686537a51864f424cd64a42478644f242363ff23d363af238ae35f232e630ca2de62ada27f6251222a61f4a1c66195a17b6166214e6139210d60df20c7609ba06ae03f20185fef1fc35f9f1f7adf569f2adf019ece5e9b1e6cde529e21ddf11dccdd9e9d705d421d1b5cfc1cd55ca71c855c5c1c32dc071bdb5baf9b865b5d1b2c5afe1ad75aa91a785a479a1bd9eb19bcd98c19605946192bd91698fc58e718c7d8a39877d84c1827d80397d557a2177157521723d6f596cc56a81679d6559629d5fe15c8559295645533950554d994c454af149254641449d4349417d3fd93de53b5139d537913525329130752de12b4d2891262524a9223d1fd11d651aa918151581133d10810e3d0bf909650681034d01a8fe9cfcd0fa14f708f44cf168eeacebf0e90ce600e344e088dee4dcf0da5cd8e0d69cd430d1c4cf30ccc4ca80c814c5a8c2ecc080be3cbbf8b9b4b748b4b4b220af8cad48ab04a8c0a604a2f89fc49cb89a9c9790948491788f0c8bb088cc868883cc80707d647a5877ec7530731470806dc46ae067fc64f0634c60685dd45af057e45500538450f04e0c4b0047f445b042cc40103cb439d0382c35c0335430c02ddc2ad027ec250822241f901c5c1928166c133810040ca80974064003340002ffc4dab4b1c017f else 0xc3308c121045ad9763c8b45521445298362361d85c068160d08c738066ca8aa4306c4780d018e334c92515455214452983623c0680c7196619846090822be8aa4288a5306c4780d018c334c3308c1210457d154452983623e0680c7b086599a619846090822c2c9b1e90a2294c1b11e0340700cb334c730cc23048411654452983623c0581a0708c7b96e4b1ca2b20e1b84e0b0863ce88a5306c4780b034063dcd7258c5159070dc27058431e54452983623c0581a0396e4b1ca2b14c8386e1382c218f2a2294c1b11e02c0d01cd7258c5158a641c3709c1610c79633a6f19a3e1dc56118a70dc8f87e1781420b415c293e3347e2a90c2314e1b91f0fc2e02c0f0340b07847358e7029caf2da6f198768bc5721c472983787c0781e0f0888b84610b74c56cba338ed178ac4388e5306c47c3f0bc0d041a0ae34af19a2f1548711ca60d88f87e170160781a0583c239ac73814a578ed178aa4388e5306c47c3f0b80b03c0d02c1e11cb631c0a72d64f19a2d1548711ca60d88f87e170160781a0783c239ac73815b278ce3b45a2a90e2306c47c2e02c0f0340f07846599470dc0a71963e8bc57214452983623e1f85c0581e0681e0f08e6b1ce0538cb1f8ed178aa2294c1b11f0fc2e02c0f0340e1190701c19f1963f1da2d114a60d88f87e170160781a0783c2392c5320e053c30fc25bc1f7c16bc12fc053bf77bec3be5fbdfbbd97bce3bc57bba3bb3fba8bb9afb8fbb81fb7bbb6b7b5b3b4d7b44bb36fb333b2f7b293b22fb17bb0c7b013afafaf4baee7ae83adcfad6bacdfac7babefab3baaafa9fba997a8e3a857a7f3a767a6dba64fa613a587a54ba4e7a4aba3f7a343a2dfa27ba1c7a0eba0879fd39f479e939e079da39d179c639baf9b4b9ae79a339957987b97ef973b96af95fb951f949393df93a39367930392c7928b922791eb913790ab8ff78f438edf8e7b8e178db38d4f8c4b8bbf8b338a7f89f388ef886387d78723866f859384df847b83c7836382ff824b81bf815b80a7801b7f177e137d877cd37c1f7af37a17798b7887775b76cf75a375177413730f725b71a770a370176f8b6e876d836c7f6bcb6b176a8b69d768d3686f680b677f671b66b7662b65c76563648763ab62cf61f3616760db607760135faf5f4b5ee75e5b5dcf5d435c175b8b5ad75a23596f58bb580756db564f559b550f548353cf536b52df525351c7516350af50234fbf4f0b4ea74e1b4db74d534cc74bc34ae74a8349f74993492f48cb483f482b481747b3472746eb4687464b4597450b44a7444343df437b42ef428b4227417340973fbb3edf3ddb3d4f3d133c373bd33acf3a1b398f3903389f383b3787368335a734cb343f33db337732eb320f31d3319730e330572fcb2f172e3b2dd72d732ce72c5b2bf72b932a8f2a03297728c3285f27ab271f269))) else (if i<11 then (if i<9 then (if i<8 then 0x3623e0700c609a2188420808ea2b08c5306c47c063d8412c4d10c42104047515486118a60d88f81c03802589a2188420808fa3e4b92708c5306c464390bc0906848118e7004d851f26c93846298362321c85e048342408c638025c28f92e4dc2314c1b1190e42f0241a1204629c0126147e118a60d88f814231c258922188420808ea3f08c5306c47c0a118c1344910c4210404751f8462983623e0508c50962688621082023a8fc2314c1b11f02847005d12c4d1244510c42104048c5725c93a3c8ba2e118a60d88c8721701604830231ce009b392e4d9274791745c2314c1b1190e42e02c08118f641c070441a49726e8f22e8b846298362321c85c058120c08c5320e00933c2314e02c051d45629904191117449115b8462983623c0780c719a2e8b4258922388a218842086c024f08c5306c4780f018c32c5d1684d1244711443108410d8049e118a60d88f01e0314c81922e8962688e22886210821b0093c2314c1b11f011c63c8412c4d12443108410d9f4ad1f66d1d4860d88f01a0583c2380559966498e619846090822d695a3ec9a32c791690c1b11b0ec2e0340b0684639c033654660d88f01a0508e4b1c5592a4799666920ea568fa3290c1b11e0340b058e2acc931cc33088411634ad1f65d194860d88f01a0582e015a5599a6498e619846090822d695a3e90c1b11e02c0d02c172dc9631c76394570dc2610c19d9764d8f4748b455218362361701a05834232cca386e01873a3a8ac1b11f034063d8432cc730cc230484115f66d934552183623c0680e01966498e619846090822c6c7a2a90c1b11e034072d8e258cd324946d2d455214a60d88d87c0680c7196639846090822c296a2a94c1b11b0fc0d018f610cb334c730cc2304458d2d64d214a60d88d87c0680e01966698e619846090822ca8aa4306c4780b0340659cb71d8e5159470dc270584326565d9363d1d22d114a60d88d8761701a0508c7b20e038260ce88a5306c4780d018a640c931d565d8f4748b445298362361d85c068160d08c5320e01932a3a88a5306c47c0d018f610cb324c3308c121045859b63d114a60d88f01a0380559966498e619846090822cacdb268cb1e45a2294c1b11b0ec2e0340a118f641c0704c19d9b4658f22d114a60d88d8761701a058342314c838064ca8cc1b11e0340638cb334944d194452983623e0680c7b0866992619846090822c2cbb1e88a5306c4780d01c02accd324c730cc230484116547d9764c8b485114a60d88d8761701a0583c2508c738066ce8fb36c991690a2294c1b11b0ec2e0340b0784a118c700cb9d934452983623c0680c63085591e6598e483a8fa4288a5306c4780d02c1e118e2accb324c330884116547d214452983623c068160b185599a649866110822c68fb1e90a2294c1b11e0340b0784700ab32ccd324 else 0x1d85621836232170120c08cb328e1b8021c30ac4306c4780f0188650474d1d8560d88f80c7b08310962388621082023a8ec2b10c1b11e03c07006212c4710c42104047d2d25c8f856214a60d88d872170120c08c738026c247c2b10c1b11f038072d8e258941884d6d2d856214a60d88d87c0780c70c42588e21082024296c2a94c1b11b0fc063d8412c4d11c431084101214b615885298362361f81c0380310962688e2108202464da330ac4306c464390b809060462194700477d2d4661588701e031c8889a9a5a8cc2b06c47c0f058f6104d11c4310841011f4b5198562183623e0700e009a2388621082023e8f92e47c2b06c464390bc0906848118e7004d7d1f25c9b23e15836232178120d090232cca386e00871a3e4d91f0ac1b1190e42f0241a12046598c7004b851f25c9b8560d88c872178120d0902310ca38023c28fc2b06c47c0a118e1884b11c4310841011d47e1583623e0508cb328e18c42589a238862108202468fc2b06c47c0a11966304d11c4310841011d47e1583623e0508c43282589a2188420808ea3f0ac1b11f02847006212c4d11c4510c42104048497a4c8fa2c8b856218362321c856070120c08c738026ca4b9374991e45d170ac4306c4642e02c0906046599470dc010e983623c0580a4a8a88310ca08ea92e4dd2645d170ac4306c464390b80b024181188651c011e78562160700a4b1ca2a0c8889a22af0ac4306c4780f018e3346212c4911c4510c42104048e158860d88f01e032cca386618c42589a2388a21884208093c2b10c1b11f03806598c32c4d12447114431084101238562183623e1f81c0310ca18e2589a2388a21884208092c2b06c47c04a91c63d842106212c4d11c43108410ae34651d8462983623c07802e8b425892228862108202468fa3a90c2314c1b11e03c0b045d12c491144310841012547e97a4e8b486118a60d88e87a17016048360e08a6b1ce04e8ea2a90c2314c1b11e03c01744b1244510c42104048d19455218462983623e07002e89a2488a2188420809192647a2a90c231484780639c0549322d15486118a40d08f00e008e22b24b9268ec2314c1b1190e42e020463d90701c11061476118a701e0314c822224a68ec2314c1b11f018f6104b1244310841011d476118a60d88f01e03802d0962488621082023e2b9268cc2314c1b1190e42e02418118e7004d7c9b24d19846298362321c85c0408c7b20e038220c24da3308c5306c464390b809060462990700497d198462983623c0780c70b42488621082023a8cc2314c1b11f03c163d841344910c42104047d198462983623e0700e00b4268922188420808f8ae8f92e49a4308c5306c464390b80b0604639c0136325d15486118a60d88c872170120c08c738026be8aa4308c5306c4780f018e12c4310841011d45521846298) else (if i<10 then 0x47c9726c8f8a60d88c87a1c85e048342314e00931c5a8fc5306c4743f02846384b1244710c4210404862d47e2983623a1f81423142589a2388621082024316a3f14c1b11d0fc0a11c01bc4b1344911c4310841088049e2b8b49724c8fa2e2988c87a1c856070120c08c738026ca47c1b11b03804551672d8e5151450c62134437e2d25c9b23e8b8a62321e87217016048302314c838024cb15c5b14c1b11d0f80f018e3346f12c4911c4510c42104049e2d8a60d88e87c0780c5320648de2589a2388a21884208093c5b14c1b11d0fc04718f610841884b1344911c42106347e9ba4e19a2d2183623a1e85c058120d838228ec4328e04f0ca3a88a5306c4780f005a1244711443108410e02b012547e19485114a60d88f01e0582268922388a218842086e024f0ca2a90a2294c1b11f03801784d11c4510c42104048c9726e1947423c032ac7b20e02b1692e4dc328e8478062990701586423c0780c4328228708a3a11e03c0621941c07412c45562d8651d08f80c7b0825a3169370ca3a4581a11e01c01d04b11594ae19c768bc5521c460d88f87e178160956ec5a8f9370c91f06c464390bc0f0641a1204629c0126347c9b24e198362321c85e078320d0902310ca38023c716a3f0cc1b11f02846284d11c4310841011d47e1983623e0508c4328268922188420808ec5a8fc3306c47c0f06847004d1244711443108410e004969726c938648f22e8b8362321c85c05810232ac7b20e038220d316d2e4dc324791745c1b1190e42e02c09060462990700499e2d86581c0296c728a832222688a1c3316c3306c47c0e018a640c91344911c4510c421043801258660d88f81c0310ca18e2d09a2488e22886210821c0092c5b0cc1b11f011c4b58f2104d1244710c4210438845707d9323c8b085114a60d88f018231ce03b0fd2f4991f10a2294c1b11d0f42e02c0d07045358e70254452983623c05818225687a9ae4b1ca2a20e8af0f92e49a3b10c1b1190e42e034181188651c011e315e1f26c93466218362321c85c068302310ca38023c6298af15c3e4b92647d1710c1b1190e42e02c0907418118e7004dac5315e1f25c9b24e8b8860d88c872170160483a0c08c4328e008f5a5a8ec2b10a5306c46c3f038012c4d11c4510c4210404952da5e8fa2e15885298362361c87a1701606838229ac73813a3b0ac4288a5306c4780f004b1244711443108410ac049519856214452983623e07003809a2388a2188420809184306c4780f018e2504945114a60d88f80c7b0822a24991e10a2294c1b11e01c0178455e9723e8b856214452983623a1e85c0581a0e08a6b1ce04a4d9268ec2b10847806599470158562108f01e0310ca08a8a3a11e03c0441886505e1d049115726c934761588423c0310ca380a9368e9170ac4206847807007412445649723d else 0x4048d1f856118a781423182d89a2288621082023a8fc2b08c53c0a11866444b1344310841011d47e1584629e0508e00bc2d8962688e228862108202464b93749d1e4791710c231490f80b024181199645c2700429e1588581c0332a4a8ec72108a0bc2688edc2b10c2314e03c06658e3345e12c4911c4510c42104049615886118a701e0332c8b84610b62589a2388a21884208093c2b10c2314f0380630cb1785b1344911c4510c42104049615886118a781c030cc898a2f0962688e2288621082024b0ac2314f012a63c8416c4b1344510c421042b7d2747d9b4752184629c068160f08e01566599262986611824208f5a5b0ea2a90a5306c46c3e03c018c4b11c4510c4210404969724e8f8768b4552183623a1701606838232cca286e1b81391e45a2294c1b11e018f641c055114a60d88f80c7b0822a24d91e88a5306c4780700454d1983623c07804a0e03a228cc3a88a5306c4780f00701684911c4510c42104048d1f875214452983623c0781608e8258922288621082024a8aa4306c4780f0094178744e1d455214452983623c07802f0962388a21884208091d2f4991f0ed1688a5306c4743d0b80b030463d9070141706747c9724c8f8760d88c85e048342408cb328e1b8021c68f92e47c3b06c464390bc0906848118a700497d1f25c938760d88c872178120d0902310ca38023c28fc3b06c47c0a1196651c31884b1244710c42104048d1f8760d88f814232cc60922388621082023a8fc3b06c47c0a118a1884b11c4310841011d47e1d83623e0508c4328258922188420808ea3f0ec1b11f0284700741884b1244711443108410123a6f198768bc571183787c0781e0f08e118439085092f4d92647c3a45d1706c4642e02c09060465596651c370043a497a6c9323e1d22e8b8362321c85c05810232ac7b20e038220d24bd3647c3b4591706c464390b80b02418118a641c0126583623c0580a6a8ac43283a08ea8ae4bd3649c3a45d1706c464390b80b024181188651c011e78760d88f01e032acb328e1986310962488e2288621082024f4de330ed178ae2306f0f80f03c1e11111c9d8760d88f01e032cc61963a0b4258922388a21884208092c3b06c4780f018a640c91d06212c4911c4510c4210404961d83623c0780c4328638e82d0962488e2288621082024b0ec1b11f011c63d842106212c4911c43108417c2da3d1d0a60d88f80c7b086588a21b21585a4dd1e8e85306c4643e01c032c62114437e2d475154862983623a1f01e00c8258922388621082024b47a2a90c1b11e02c0459cb5358e515146e2d25c8f4762983623a1c85c048302314c838024c316a3b14c1b11d0fc063d8412c4911c431084101218ae2d4762983623a1f01e0380310962488e21082024716a3e4b92647c5306c4643d0e42f0241a118e7004d8e2d)) else (if i<13 then (if i<12 then 0x2f0ba3a1034206840f814228e6493c07085e0508e18fc00f814231c611085f0284630842781423144213c01745e00ba2f005d1780c73843f018c1780c50a47914523c8a291e451700a3b142e88e229b807085d1349c03862e8964e005a1047c00ba248f801945d1f00398b43e005a0b47c00c82e8f801744e185880b081334c9131c1610c311926188ad2ac40631c31314e0898a0b081334c71586558ac30d28e1b823a518a70c74a3082a50cb31c655840c7058c70c4c204c931c58cd1f25c9b22e1588c8721685e048342310ca38023c719a3f0ac47c3d0bc0a11966304d11c4510c42104048e3347e1588e85e0508c43282589a2288621082024318c668fc2b11d0bc0a11c012c4d11c4510c421041b01258ce1588623a1781c032cc6196268922388a21884208092c670ac4311d0bc0e0188650c712c4d11c4510c421040496318ce1588e85e031ec21082d8962688e22886208571c678cd1f0ee2b08c5386f0fc2f0284663347c978748b8462921c85e048342408c5380248571c678cc3b8ac2314e1bc3f0bc0a1178cd1f876118a781423142588a2188420808ea3f0ec2314f02846199112c4910c4210404763347e1d84629e0508e00962488e228862108202424bd3649d1e4791708c524390b80b020464d8f641c0704419e33876118a701e0782c5320648962488e2288621082024b0ec2314e03c0619913145a12c4911c4510c42104048e33876118a780c7b08420962488a2188420ba1992745a2a90c231484642e01c03345b11c427e3347c9b24c8b8462988c8721685e048342318e00971a3e45c2314f0284465cd6291112442663347c9726c8b8462988c8721685e048342314e00931c668fc2314c4742f02846304d1244510c4210404863347e118a623a1781423142589a2288621082024319a3f08c5311d0bc0a11c01b84b13449114431084106c049c8b84629c05808cb9aa3b14c8222a10b624884fc4f19c2314c4742e03c0630cb1b84d12447114431084101278ce118a623a1701e0314c8192370962688e2288621082024f19c2314c4742f018f6108416c4b1344911443106189e1f886118a701e0683c231c668962488e22886210821b856025713c3f10c2314e03c0d058c32c4d1244711443108410dc049e1f886118a701e0682c3322628962689222886210821b8093a664d91e8ec2b1082214e01c01244765334761584629e031ec20962288621082023a99a3b0ac4308c5380f01c012c4510c42104047d33856118a52361780c7b082589a2288621082024299c2b10c2314a46c2f03807005b12c4d11443104048d1f25c8b856118a4872178120d0902332c738026c28f92e4d9170ac231490fc09068481199645c2700428d1f856118a78142332c70962288621082023a8fc2b08c53c0a1199645c216c4b1344510c421 else 0xe07608780b054b638cd2d824d0b80b04841042d0a4dc0296c719a4f0184210745700248e88b0c5445862b0f8052ccd251161f00e119a639ac3e01c131cc12d1161f006498e5e00c33087c01862e00c31780c21083a23801c05d11cb4206840f81422966693c0324841f80e198e3f028462884278142310619085f003817802f0bc0628841f80c4386392e451497228b8052d8e12c450e0dc00b4208f80124381f00e188e1c13800e05c00b42086e4e005e0e07c028ac50f80525421f00a28b80168410a4914c57618ec3e01451f00658a94e01431f002d052390b8070c70168bc00b42e005a0a47c03862d0524f003c009a2e00cd1700310b805245e00562e01421700a488e3e00c71242b2700228a47b0c5c01962f00701529c02863e00c7148fc00e03c1b8063945260dc0318a2b865c1bc0160dc00bc2488e59278070c785700a4b844c2a11e0149708b85423c0292c43846c2bc052584261508f003a09a229a8eb085c018e2a3ac2e0145620c7351d610bc0610841d1dc00c83a09a590b8070c7011cb88f00c4386e11711e018c708988f00c43844c47c0610788f00320e84a22c31511c019a3a22c3e0149334b44587c0384669866e00c7308761f80c21864216c3e00631bc432d29e030861928c0f00c418e3e014531c7460780524cd1d19c03846599a5f0184210746700258704e003c0310e18fc06105c00702a203c0292668e88e01c2334c72d11c0196639380308544700618fc0610841d11c00bc2e88e5a1034206840f80a28a840f81422926693c07085e0310618fc0a105e007c0a118e308842f80e19864213c0a118c2109e0508c41084f0284114042780310bc00f80e18e02393c0639c21f80e18bc06305e03102f00324c8a2926451700a2b102488a5926451700a4b1c2488a5e01c21347c0310310864e004b1700238bc0610041f00268923e006210c7c0186258f80124471149e00500e056021780188431f00268b8070c7012c9c0292c70f8070c5c0318e18f80525456209e02548e3084e0073168716c562e00cb17002d05a307802e8b805085c00c82e8c1c01962f005d1700a18b800f002e88123f002c238051dc22611c028e3c23c051d842611c009222928eb08547585c028e6497c0610841d1dc00e8269242e005a0b49217002c4780631c3708b88f00c5384e09711e018a708988f80c20f11e00741749465862a32c31519618ac3e0147324946587c03846599a6e00c33087e0308420e8ce007012c382c87c00e62d1243e00641e29c031ce1b845c538070dc12629c0314e19314f01841e29c00e02e8705b043608780b05c2334c12f0160b86659825e00c93087c01862e02c1104370a4bc00ca2d0e8a0d15c0384669925a2b8070ccb324bc01842e00c31780c21083a2b80178492700328b80639c21f00c63863f0184170) else (if i<14 then 0x80a10b602138016c4b1f002d8922393806305c0292c40b64e02c11cc410dcb45780c21084a2b801905e124b435842a1ac2e01c332cc53585c0314e098a609a86b0b80324c52f80c21083a1b801d05d114b4207c00f80e10bc0a105e0508c51084f0284618842781421820213c06285e030c2f01c1149b238b806285a1049c00922e01c21147e00082e005a1047c009a2488e4e00471147e004e1c8084e01c11700a6a8ec5138051d861f80c20a49c23c01f80c21083f018421074207c051d8a1d081f01c317801f0284630842781423144213c06305e03142c2b80525c32615c0292c33845c2bc01615c009a2393c0610841d1dc00c8269380619c21f80c20b801905e1d85e03086112c2e006e1089e03082a32c31587c029266928cb0f8032ccd2d87c0384659845f0184210746700380964e01493347437006698a4a1b8070ccb314be0308420e86e005d11494206840f80a48bc00f801f01c317801f0284638842780e11843f02846308427814230c4213c06385e03842f018c1780c30a4991c5c0292c70bc2488e6e005e1347c00b6210f8070c5e12c9c00bc228fc01782809c2b010de0254c20f42f00631e85c00c6311306e014570c983700a2b14e09706e01456289837802c1b80134472587a10ac3d085a17002d06e4d0bc01787c02842d0b8017874262361d843c46c3f018430c84362361f003a8de219a8cc46c21d85c028a639311f0184210946623c00ca3a8961c1ec2e0145620c72e23615823b0b80b05c232cc13623c0582398ea208527a2b11b0874562361700a2b10639e8ac46c21d85c0386e1192619a8ab0b80708cb324d88f00639844c47c061084251588f003a8c8249a88c46c21d1188d843a22c2e01c232cc73585c0384e098e609a88b0b80708c931cd88f00619844c4780324c22623c01843c47c061084251188f003a8ba239b11a10588d082c47c0514788d082f01c21781423843f01c21780e10b11f01c330c842e23e0508c61085c47c0a118a210b88f81423104217c018c621f80e18e03f005e1780e18bc06305e03142f0188149b22e22393645c44726c8b888f11e014562074134453c9b22e223e01c2188432700e10e82593807085a1049c03843a0924e01c21d0472623e00ea3a0720e0087e00631887c0386380e84e005a0dc7c00bc3a0fc0471841d49837802f00641887c028ea10f801bc621d1d610bc06108410c988f80c20e8aa205e030842086490e8417814228a390e841780e10a43f01881f814231c61108219bc0a118a210432f80320bc0639c21f80c50a4590c522c862e006f1886007801c0b8050d421f001e003814561e00c91683827002d06e3e00c917001c0bc01785c02862e005e0e0725f00292f801619c0296e1130c8478052dc22e19c0296c43845c3211f014b610b86423c00e82688a6e00c7 else 0x3c0610841089e030842084490a841485e031c3f003e0508c61082117c0a1188210422f81420920213c06305e03102f005b17))))
def nineI11 (i : Nat) : Nat := (if i<2 then (if i<1 then 0x8810301003000003c254f04dc000000001824650350000500000457d605a9421d0000044230000200d2f0a66012fa110405378095e816b00000813e000000000000000000800f14121e05b8000080733c460106a680107030c402ec0a83ad0240478c44ab078301fc216a64287c056305c1905ea810760a3846900116d053b40504014e70108813be03a3c4482a0ca81bef0762c41850654425a70686810ec01b200d0d086200616037c0000b0a8d401d209f7c14b1040e823f702b7c1a32004ac5a63047dc076809578469316554023214f00000000034230704a9201b361640000000000000e08b40000000ec0000504300000c100bc06e001e00000d04e6043e000011c5900000000000276c087f038ac1f8d0393c443207aec18b702aec210e0971822cb07218258c014181dcd0664826b2023a013cd090ac1ed4015dc092b09f105c2d10ef815430a5401afe77df2028b08c64077000000000000014183b072b81797063c45860000000008089e41b300003429c5088c80af000000000921940000d11ab4263b80c40000707524421511c80000209d40000216c0000000000c217002fcc14a00002010a70a4bc014d04e08127c03798025b0516c159a00d80000104240000206e8000000000000000003a035000034129b03c5025d00000000090924000000002c8190000141517018e80c8000000000f0000000000000000000000000000000000000000000000001c18440a02c21a906c00000408f800000000282130000000000100101e71082c000070818c1280000381c3000000000911a00000000000000e09a4000000002c2240000301308059e00940032c0000000000000008a8419a104d1029f607c58007c1102426651900844b711bc00b23098581de40a9381b6a064f0222501f944759815fc08c106960534480b80000d050f80984058201e600001406000001c116d1179c013e0355863ca00b1016460295c07a00003866d6016c0000d083c6058000000000000000000000030065e0130501500003487340264068a8035ac4790000344360113d40eb000000000566f80000d02de4009b060001420840402412030b40030c62c210600200100c08700109d04d0442041c55400c81800c10c20044451c50011c200110b0883454010180060005c60801000000001d00c028200b6402000c30026c82404800c25c014214222530000e0410031810021070020010500470010031070c40050400400050440450c01401c02070000880000420c00c204008001038a0c104000000429204300f0410c01401001450001c00811433410008401010420012022501452440470c00001800000400000c90030020030421c40020800432410030821450400001410050c10830c70112c13470440851000002490c0009003000241300086004040 else 0x35e8018b06750214b11fb4001f05cec1751164801929048b426850453840181072c019500fa806de06ac85a38069b860d511614207c07a5c01ac0713c02a000024281c092280dc00003c29800001806f10a74043a61138000030a680000000004228d03a8c04e311bad5d88018ac0c7f1130428df097e809aa07d64404403060641603f20028c06dd0433c0866c278b0122c26d5a394000000001808fb09e400000000000006810800da2610c00000000000003046ec1bc106ca422000000000000940853900003881b0000000000000000000000300d8000000000210d3066b90114000080521802150574c2393809dc0470115401d70000000000000241fb8119682561165ac4560a0a0000060704000000001453a0057904202056c845a00000000000001013a0000342290000000000000081c5c117680a7d21af204d90933402670167455c011b7c20e40a9400001089b81ddf087c8046f07cb80f00012c000080a6c00005219de065e0660000000003c0f360a3d8097000020196514d80000103fd02966080080e000000c0b9000000000902f80000000000000000038135000000000000000000408cf40caf0518cc008074fc1151210ec0a4b06140000000038161501000000905f4000000002458a810f7420ce070b82098073a825100a2d404ad08eec68560855841fd06300000b054f8052c04d8025b00000000020a200000c10b00000f07e9409600003c0cc80110446b000028208811180000205f2814c501c4c05331a3c00000000200e72665102a200002459b7038e81820000342930000340f900001c1f4707e40000000000000009bc4038802810102c017dc00600000000010441c101e04210644e00b40000c090280a860150018d0000340d1c05a58022c09e88117308b800001054b423c809db4191e04f40283000014238f034d4270c0572067f903f405eb2813d80747031b8082e041541e50066c015f008d740d980885c176f0010427ea03f80000000000000404100000003bc4083a00cc00000000000000000100c50000054bd91a02014de115e44783027901e36019ac089f08440000f098bc1c7f00fc0000800d0000000002c0ce3037684c9f0210000000001688300000c0b8000000000000020282801a94245806ed401e9028981ad0000080bdb022e820ae009f447a00000057a601f40000e05dc00001038501068191481ee118ea00350000000000000000001015981d1202200000f042c0000507580000a09edc1b90000000000106800000000085c4902f00000b43f4000020176415500000000000000807200000000000003003900001829eb03c80000cb3f4000000001029000000000000002019f119bb802f0000241e800000000000000000000003017400000000030247c12e00000001f5076484530000201) else (if i<3 then 0x2073f03d18277d03b000003776c80dbb10c1c069714f84100a15a4c166000000000408d2c46400003800e000000285311fc00009058845ae0000000006046a8024e003e4186f0904204b71670401b64419c11dc144f81207099601ff100f641a7c078401c0203350474d044701eff086c000000001010f016b5c0cf007f5845c0000341507022a404371399c643605b00000705680000e02a4004f000000000000010832501600000d002f4168904b2c243e08da812d000034049b06c7819c00003024a60218000000003018a0000305b1e06f5c8180000000002205745ea0000040a6b105d024400001417f70144c476b02b2c0baa11ef4187e06bae88a800350125c06a340328077f9d9b2069180b6b07a80000000010291a03974085d0029c237062ee4294708954020219bf45a8f11dc00009031081f3c08ad81d2408058403013a380f800003c842d02cc0000000038149c04480000a20c40000000000000218ffc090a06d3c696000028452500dc805e0000000007206bc07c1213ec0f6f007240f7e09bbc16360203e040309d3c119e02c6c132009c4000000001c272002d3c442711b2c21c000000000d048dc18100003c24d8099c0000b0688c4e3902bac46340a29806b702c2c09c407b00253715dc0000003d68289000000000316d0441d202a800000000000000000000003621000000000201aa611f459da80938c16da02ef014431909c5bb7107ac24b0000000003170cc142d068000001072780fb000028264a0168000000001c0ed00000000021188000010a8400001084b85a03043581cd000000000b07d8000000000000000000484090287866600001c07fb06240000209fd60433055d0017005598165105e0e059f11174055000000000d026c00c900000000030a31858f000010416806fcc11c0000040fad096481cb414cf40161019dc42f10793807500001859a000000000f07c1c205c18fa412b0000000000000344500000111fa2080c00004053f005c0000001c6c10c40000f1524419e000000000004c4c09300000023d000012886400304171508bc859e00000c1d0e06d4ec1b711cf40e9808ebc2323073f444451032028600000c284f0639825e50193c0c2e075442a6600540000c719d0594900a5c447a2058c011606504118701e40000000030449c07fa445f000000000210fc014000000003aa11f00000a076800004000fe06a00002c260ab064413300000000000001402ba02d40000416954683000030190180cf8202c07dd024fe199c0000000022019201c38124f0a5c0000000031db6711c6406862003404d000000000000000000d0813c126311500000a07880000300c50470105be605a512bc0000617000000709b1420d105ef101900003007be06e111623051d800800000c247b05ca021eb0 else 0xda3830041f044e4081210e40000a156f40a30000341db00001a06ba01ce82730065f8095c8098000000003808d36137809f0000040020000000000000381ac000000000b03980000805f80000c05c00000709a80000d10b800000000300ee000000000000000000000018252b04fda025308580000000000000000000))
def nineD12 (i : Nat) : Nat := (if i<2 then (if i<1 then 0x63a2128c097a21f29be22fbd2f6d1ec0dd513a45f3b7e5c7c83f8a27055df15baff6feed32d8f3ae7354de9acd1339e8736b6614ca93921f1e2e30cc44d8497028df74bd5376eae6a5bc1b59367fac99d871af5f5b26ae454bea79f4ba68fd5138a0c93e667674e1e9a83314a59fca35927b213a3c646ca8bff14d22394383854d069605b3fe27dc2f87dea5bc4a76b6e98dcbeb8d66ff2dc71b1fb547689ecd81938b18261c8bff9790ae175a50b1755bbaa91537aa2f13e6a6de4c5c9545223a34644e4869d0579fc03da27740e709bfb36ba69dcce818f3302c5ce4b32957629204ea89621226229241b07c30eb21bbc33745f28aed13fc2460419074c0cba15dc25f040506aa0ab80ff0157014e0003ff95a58e00ffe4a963803ff89a58e00ffeaa963803ff94a60a00ffe4e982803ff91a60a00ffe26982803ffaaa60a00ffe56962803ff93a58a00ffe26962803ffaaa58a00ffe62932803ff96a4ca00ffe56932803ff91a4ca00ffe26932803ffaaa4ca00ffe5cd81803ff95260600ffe50981803ff93260600ffe5e981803ff95a60600ffe52981803ff93a60600ffe4a981803ff89a60600ffeaa981803ff9835c600ffe62971803ff93a5c600ffe26971803ffaaa5c600ffe60951803ff94254600ffe4c951803ff94a54600ffe4e951803ff92a54600ffe26951803ffaaa54600ffe60941803ff95250600ffe61d31803ff9824c600ffe54931803ff98a4c600ffe5e931803ff95a4c600ffe4a931803ff89a4c600ffeaa931803ff98548600ffe61121803ff95448600ffe60d21803ff95348600ffe62921803ff95a48600ffe52921803ff93a48600ffe26921803ffaaa48600bfe26963802ffaaa58e00fee91182802ff89a60a00bfeaa982803ef96358a00bfe26962802ffaaa58a00bfe62942802ffaaa50a00fbe99932803fe9824ca00bfe62932802ff96a4ca00bfe26932802ffaaa4ca00ffa61222803dfa7760600fee91181803fda3360600efe60981803fea2260600bfe26981802ffaaa60600efea2171803df9875c600ff68cd71802ff98a5c600bfe26971802ffaaa5c600fee91151803fda3354600ffc60551802ff89a54600bfeaa951803bfa8850600fee61141803fb94250600ffa88941802ff98a50600bfe56941802ffaaa50600efea2131803dfa774c600ff64c931803fea224c600ffc60531802ff98a4c600bfe5e931802ff95a4c600bfe26931802ffaaa4c600efea2121803fba4448600ff68cd21803ff13148600bfe62921802ff95a48600bfe52921802ff93a48600bfe26921802ffaaa48600ffc61211803ff15484600ffc60e11803ff17384600ffc60a11803ff15284600ffc50a11803ff13284600fb699a33803bea8888a00fba99a22803faa4488a00f7c9de11803fb24484600ff48ce11803fe22284600 else 0xe119a8e2d12c9247219085604d4561f8ea2e2a2188ca41a23c3e16038141c232d185a269248e43210ac09a8ac3f198ea2e2a2188ca41a23c3e16038141c2300964d2491c8642208a45604e65a9749c651e8b0a88623290688d0f87c2a16038141e0e1208cd473009baa5d36938ca3e3a8b0a886220d11e150b01c0a0f0709044b25186c021e7198ea2c1a23c3e160381c1c231d109423914211a5d36938cc751615108344687c3e150b01c0a0f07090463a2128c023e72d49c642a2188ca70f8580e070708cd471349211965a938ca2c2a2188ca41a23c3e160381c1c23351c4b2390c84410262938cc75161510c441a23c2c070383844b2518662259348e4220813149c75161510c46520d11e1f0b01c0e0e112ccb461348e4321104098cb527198ea2c2b11948344787c2e07051e84259348e4321104097cb527198ea2c2a2188ca41a23c3e160381c1c2300964d2391486422081354ba4e328f45c564211148344687c3e150b01c0a0f07090466a39804dcd2e9b49c651f1d45c5422290688d0f87c2a160381848223d20c06090734ba6e328f8ea2c22290688d0f87c2a16038141e0e1208c9452418049ce328f8e8445387c2c0703838464a2920492384638ca3d171590844520d11e1f0b01c0e0e119a8e259248642208ac098a3e3a8b8ac8422290688f0f8580e070708cb461349243211045604c6328f8ea2e2a11148344787c2c0703088f48304b44b2692486421581338ca3e3a8b088a41a23c3e160381c1c2325149025934864220812f8ca3e3a8b8a844520d11e1f0b81c147a10ba4b26924864220812f8ca3e3a8b8ac8422290688f0f8580e070708c02e92c9a492290c84411b0ac09cc65171588ca41a23c3e150301c0c22ad2a8f65b3592c74724186c260a108bbc75171588ca41a23c3e150301c0c22ad2a8f65b35928c63a4186c260a108bbcb6328b88ca41a23c3e150301c0e0e1196cd64b1d1c8a4830d84c14211758cc7517110688f0a8180e0707089665b3592c74524128c3613050845ce328b8ac841a23c3e150301c0e0e1196cd64b1d1c884a30d84c14211738ea2e2b210688f0f8540c0703838465b35928c63a2128c3613050845ce331d45c541a23c3e150301c0c22ad1ecb66b258e904425186c260a108bac663a8b0688f0f8540c0703838465b3592c745241109461b09828422e72d49c663a1510c46530dc3a060381c1c2261329161302993c651f1590844530d91e1f0a8180e0707089966a39814c651f1d8ac84222986e1d0301c0e0e11269948b09813c651f1d8a844530d91e1f0a8180e061126906030658cc75171590c441a23c2a060381c1c22552c9461b0278cc75171588ca41a23c3e150301c0c225520c060cb2d8cc751711948344787c2a060381c1c23251490604f198ea2e2b210688f0f8540c07038384) else (if i<3 then 0x84b24914864220812f938cd3719478762b21088a61b23c3e160381c1c23009649239148642208ac09cc651f1d45844530dc3c0703838466b2514902d9248e1908d6338ca3e3b15088a61a23c3a1703828f421b8964d24914864220de2719c651f1d8ac8422298688f0e8580e070708c03716c964d2491486422081391387e328f8a884222986c8f0f8580e050708cd4716896492290c842b026a270fc651f1d8a884222986c8f0f8580e050708c025934924521908822b026e974da4e328f8ea2c2a21088a61a87c3c070283c1c2411329161300859a4e321510c364787c2c070383844cb351c4d24852549c651e1510844530d91e1f0b01c0e0e1132cd4712c8a4321104098a4e328f8e854421114c370f01c0e0e1132916116c964d2290c8204c666938ca3e3a15088a61b23c3e1703828f42178964d2290c844102633349c651f1d0a884222986c8f0f8580e070708c02f12c9a472290c8441026f1947c54222986c8f0f8540c0703089355a3d96cd64a398a9061b09828423ee974da4e328f0ea2e2b2188834478542c070283c1c24112a964a30d8043d52e9b49c651e1d45c5623290688d0f87c2a16038184822551e906030483acb52e9b8ca3c3a8b88ca41a2343e1f0a8580e050783848232514906012758ca2e2b210688f0f8580e070708c7442508e458d2e9b49c643a8b8ac841a2343e1f0a8580e050783848231d10946011f396a6e321d45c5623290688f0f85c0e0a3d0874259248e4321104098cae5a9b8c875171590c46520d11e1f0b01c0e0e118074259248e4521908822b02762b16a5d271947a2e2b21888a41a2343e150b01c0a0f07090466a39804dd6328f45c5643110688f0b01c0e0e1196cd471889a450a8582968b52e9b8ca3e3a8b888a41a2343e150b01c0a0f07090464a2920c024e62b16c65171590c44520d11a1f0b01c0e0e119a8e3112c9247211040998b6331d45c5622290688d0f85c0e0a3d086f259349247219088378ac5b198ea2e2b21888a41a2343e160381c1c2300de62259349247219088204e52e9b498651f1d45c5623290688d0f87c2a16038184822551e906030483a8b52e9b0ca3e3a8b88ca41a2343e1f0a8580e05078384823251490601275958b52e198ac862329c3e160381c1c23351c4b26846716a5c331d45c5623290688f0f85c0e0a3d084d2491c8642208e0098cac5a970cc75171590c46520d11e1f0b01c0e0e11804d2491c8a4321104702b0276532b8ac3e9749c651e8b8a88623290688d0f87c2a16038141c24119a8e6013798ca2e2b11948344787c2c0703090466b251c5a26914561507842f8cc7517150688f0f8580e061208c963a21285a23914560f085a532b87d2e9b49c663a8b8a8841a2343e1f0a8580e0507090463a2128c023ee2b0fc65171510c46520d11e1f0b01c0a0 else (if i<4 then 0xa41a2343e160381c1c232d9ac963a292088613050862c45b198ec5622290688d0f85c0e0a3d96cd64b1d84c1421bc8768ac5b198ea2e2b111488d0f8580e070708cb66b258ec260a10de622290f549865160d11a1d0b01c0a0c1192c74722128c361305084b2691c8a38cd36930ca2c1a2343a160381848223d9ac94822128c361305085a2591c8a411b8e057ea6c328b0688d0e8580e050608cd63a2920884a30d84c14217896492391471b8663a8b8ac441a23c3e160381844aa3d9ac963a4186c260a12d168663a8b888344787c2c0703838466b258e8a4830d84c1425a198ea2e2a0d11e1f0b01c0e0e119ac963a2128c3613050958b4331d45c56220d11e1f0b81c147b3592c761b0982841c562d4b8663a8b8ac441a23c3e160381c1c233592c761b0982842591471987d2e9310834468742c0702830465b258e8e4425186c2421689a4722904522be43e9b498841a2343a1603814182335928c63a2128c361210e05a2591c8a41148afb4ba3d161510834468580e0506089665b1d1c9461b09828431134924521ea9745854420d11a1d0b01c0a0c1196c74722128c361305084d2491c8b9a6d161510834468742c0702830466a318e884a30d84c1421c096492391758ca2c2a21888344787c2c0703838465b358e8e61b098284ae331d4585443110688f0b01c0e0e112ccb66b1d109461b098284be3a8b0a886220d11e1f0b01c0e0e112ccb66a318ec361305096c663a8b0a8841a23c3e160381c1c232d9ac74425186c260a12d8cc751615888344787c2e07051ecb66b1d86c260a12749c663a8b0a886220d11e1f0b01c0e0e1196cd63b0d84c1421248b8a4d161114834468742c0702830465b25188e61b09828432974964d2391754ba4d161114834468742c0703090447b2d928e4830d84c1421ccba5a2691c8a4115fa9b49a2c22290688d0e8580e04111ecd64a3120c361305085d2d12c8e45208b457da5d161114834468742c0702830465b251c8a4830d84c142190ba4d2491c8bba6d161114834468742c0702830466b25188a4830d84c14217496492391758ca2e2a11148344787c2c0703838465b35928e61b098284ae3a8b8a844520d11e1f0b01c0e0e1196cd64a3186c260a12b8cc751715088a41a23c3e1603818447b2d9ac94830d84c1425b198ea2c22290688f0f8580e070708cb66b25149061b098284b6331d45c5422290688f0f85c0e0a3d96cd64b0d84c142176b8ca3e3a8b8a844520d11e1f0b01c0e0e1196cd64b0d84c1421748e451b6a3119cb527198e85623298688f0e85c0e0a3d084b2691c8a43211071188ce5a938cc742a2188ca61a23c3a160381c1c2300b64b2691c8a432110409ca5d36938ca3c3a8b8a844530d91a1f0f8542c0703090449a3d20c060907519a6e328f0ec54222986c8f0f85c0e0a3d0 else 0x119c742a2188c34478742c070383844b32d9a8c63a398ac360a10b788ce331d0a8861a23c3a160381c1c232d9ac762a2128c360a10b778c467198e856230d11e1d0b81c147b2d9ac762b0d828421563119a4e331d10c461a23c3a160381c1c232d9ac762b0d82842d924859c651e1d8a844530dc3e1603818449a3d96c962a2920c3613050978ce328f0e844530dc3e160381c1c232d92c54524186c260a12d8ca3c3b15088a70f8580e070708cb64b150c9161b098284ac6719478762a1114c370f85c0e0a3d96c962b0d84c14252334dc651f15088a61b87c2c0703838465b258ac361305084d23de2719c762a1114c34478742c0703838465b35928c62b0d82842dde338cc7422298688f0e8580e070708cb66b258a8a4830d82842dde338cc762a1114c34478742e07051ecb66b258ac360a10dc42b44e338ca3e3b1514c34478742c0703838465b3592c561b05086e2d91c85ac651e1510844530dc3e160381c1c226596cd4731586c260a12d8ca3e3a1510844530dc3c070383844cb2d9ac548b0d84c1425a8f8e854421114c370f8580e070708cb66a318ac361305095c651f1d0a8842229c3e160381c1c232d9ac54324586c260a12d8ca3e3a15088a61b87c2e07051ecb66b1586c260a10bd4a4e328f8e884222986e1f0b01c0e0e1196cd62b0d84c1421789247c52e8f0ea2c1a2342c070283044b32d8e8a4825186c260a10c67431134924521f2930ea2c1a2343a160381418232518c74425186c260a10e074259348e45d52e930ea2c1a2343a160381848223d96c94822128c36130508742d1348e45208dc57ea5c3a8b0688d0e8580e050608cb63a2920884a30d84c142178e84d2491c8bbc643a8b8ac441a23c2c070383844aa5996c963a5186c260a12d0ea2e2b110688f0f8580e0707089665b2518c761b098284ae321d45c56220d11e1f0b01c0c22551ecb64b1d20c361305096c643a8b888344787c2c0703838465b258e8a4830d84c14257190ea2e2a0d11e1f0b01c0e0e1196c963a2128c361305095c643a8b8ac441a23c3e1703828f65b258ec3613050874a537190ea2e2b110688f0f8580e070708cb64b1d86c260a10e47426917316a5d1e290688d0e8580e050608cb64b1d1c8a483098284321bcc44d2491487c8ac5b198ac44520d11a1f0b01c0e0e1196cd64b1d1cc260a10c578b6331d888)))
def nineI12 (i : Nat) : Nat := (if i<2 then (if i<1 then 0x605280000909a240e7b06f6c0f9607b202a078076828f8464ec2b50000201560000000007002601bc00000000070c14025cf026e0296a0ac3c811d12d1420e00002812980ae88108717dd0411f0357c0355072e85cf00003995e000024229000010222907a800000000180ae3000c000000000000000000c149201ac000000000000000000000000003c164d0450000021798000000000000012095811c0000000008686bc2d3c1b2441e400000000000000000000000000000001c2d200000000000003847e40368000000003c2110000041c5000000042b038dc07b60498808c40a7dc29b200a4c06ab025a84d0d0868000090209022090246816f30059c179108c58183411dd857960712404fc003dc0d3c0046401800000809a100e3844d9040d4045905b8000050129c0575804c0000e01560170815600000905cc0000d058a8281b0b7b80ef9058c0000e081482ac908e0c19bc0b03c1d940b8c0000d127282c1b14cdc22f8056a409090594c18b80681601e211b80000507700000b0bf9c2eb40a4bc2ae4084d41dea600c0000a079cc695f002b4219f144ac0af00003c57e10a440000000000000808374062c09fcc249513de4027209370431000000000000000000805314081a02f0c518a03e280f3a111f0030517dbc0df000000000b185880c9a0464823de0692c094f1a5c0000000008065a09d48444000000000f134800003143e017df06a40000a0be9428ce708801c200b68000000000000000003c099c045801f2f52a2029c30ad1044c3041502dbc0921c298b0ab4415d70a5180500194a900c10aaf806174000000000000000000000c03b000000000d03a00603c1086c00e60057026f40430c403b06c0401900003823c3004000009179442a8707d000000000000006139c000000000014e507530621158ec820700000013e50505430041a6bc08400002c41ff02ca0273209384239704b641ce503150001b01b60023407fc0112817e6c60c806ac01509064f52819078c4225b02db42260256332c0d2b0002093005040200070500360004000c170007040c0918020b4cb05c00080d0000069e2c0b05000000010203104004001e03020728161d0112050a01121d0027051300030b0104010a1a0a0a17030307020324050000000a1b0106021e0410070304000f000b2801010d01131606010e110c00040a0001001305100b0c070d00190006051111010a001d00040c04050b0a0007060a070426050d0d03080704040b0a0802010c1c21000006080a015914090d030c1902140b082003040c080006000800003004040505090712030b030a06001a000201070c040902000003001706000b01043202030110150507081b020002070e160d0f1700020e000800000d00000001090003010101000100001212000000000506080c else 0xc00000106a5a046059cc517504e4000000001824bb10c9816b42008c1b9ea5820201c0c0ac068e15fe042b2012140c21243e85ec72053a92d507000000b15e8004bc09f94510f183a9e7a803994574c097e012fc03c400005068580cc817fbc1256005301a8c803f0456401f00000d05de02f07030042fb207b800000805001240000180a10000102339101941470067000003035841959069d421b041f8000000bc80000307dbc62300095c044102480000101dc0000008ba82320000201ef00b52403dd68e842a4e0b23003f60b0e40f25028000008069640395842b81bb401a400000000240ce715d4000000000000050440d647818518021204ab429aa0a540000617d3c1fce032040d0a09b6c2e7719d80000606416003a1b5d02097019e80d7410c3810f70726c2ce000cfc0ea90165c57d1038400006017c064b007330098e022b402f104df801d6011a5c254031e42f7f1938019e302d701a200000c490c06100000db6f80000000000000c01d4584bf0b6006f000487855bf0a26816db029740b3e054ec2fd9152ac185b0799c2b97064a451f40b280000c180240ed700b8c1f7f044c000050aca80b1d07f60617f0bcdc07eb061dd822a0954000060a5f815520bc601c8b0ba184a20000206f2d03d582c9906300000101690134406454519c03b380b000000c17c803a6c1156052000004099981603063c857271061824a709640000a0adf0136c0797e020d0737c026912100000b02fc0000b070c000070500000000000000000000000000003829d0000100d4700c704cf803c000003082c0000741e94241000000000c16e341d13052e80c4000000000e071cc26510474422aa040800000102fc91f40707e83a409e000006075440bd00a0ac049000004261e04800000719340000e183fc02ad204a40f6b1076c178305f8813db1b1dc24f71b9d0664f0180080b505b242e0d03de82bfc00a2c1090000342712a5dd40174087942278041bc15930a884200b041c0000c0be74024d085dc1afb0a94000081b0f806350a1302d1501b0421f106080000b004cc2bc9150b807a40a42412800001c2ec0000000006032c0000d057bc2b34043541b780345409f000000000d1a6c8254000026107710b04087a00b341e8309c02853a0c0c027ad02780000000000000c200c0000000000000208da860a00000000000000000000002c1c6000000000000000000e0628000090bf00253e1082c27c4095c44271034982064159d813540515801c3146c02b8203f782aa20013428eb5136413b7024fc5e4403ad01186048c0000b6299812c50842840200000c1db006628412017f40085000000000a01bfc2f4202e244d4a0978c42ff1276061a0000000006b74980e22b17e411ab0a7a01220000001cfd08d3a814c845784880000045f3a00e8c28a) else (if i<3 then 0xb70b11c1aa41483c2c62046d009d403d3412b70bbd420270b95407ff11ccc10a8181805e200a65411740911c040f0740051d0000000d9810b6211a505a400001087041fbc050c014fe01520242708510189900db830400001c1d7b0990a113d0891010120a2d01d8f001e00a9105180000a105c0000a090c415b011bf011e00003413a000000000406740000d030c0000000000000901d8c269907888287409ac4277a0299407d00001026000412802b00000020c000000000701c005db208e898911076bc41c20650c21860be080acc804440e0e50084052000031a4a0000241721067e200c21090423000001817a0108ec10bf0bb80696201e2c1e9e0a00c043f1bbc8053646f841b8618c800dc708a040ddb08d501d600000c6dfeb64f85f8302ee8622b03ba05ef0000082ff100d3822de09c9c30100002c131d09440000000024051c123801b430ad80000502e80000a0aa4c6e40000201ba00002025200000000000000000000003c0a2e0b3642a300001864c6025500fbc0200000000000816aa016c00000059940ff40335c032d07e642be702340000b1b6c0000000000000418bfc6089022c0000f0619426e109580000000000000000000000d06cf41be90af44496000000000305ff4089000000000e0748c5e350813041b2207782a6902fa85f5c15dec2d0f040382d6008dd40a371479c1ca00b70000d307b701b2107ea2012c0aedc2c5105d10279b050b81f86047f02a19808b01eb20b5c0000709b300a43033d4037403f20263207cdc06ed17edc20f80395442820032c2cf000020020c099e42ea809f40000c05a1000221450000011144840d10854000000002e10fe00680000304fd852540049018dd07d480d8608b00000e1439c0b700003c0b496079812e8025d457070445841610a0c0000000000000920780000f1a63c0c17845ec2f51088501e0714700000d1250442a0000245fcd0666000881231415f5080d0138506b602d5d0b1f8130f093341df415e0825a90239c03cd054745e900002c44bb203005e0f00f8000011a6600aac02ad013cd01ca027b60bb68086e0a4dc15700ac4000000001c49e00001c2d9a0163861e013ed415240901a026201c7426a90135c2e6000000000c0a19c50bc0785025870829c088000000000a091b8613114594250f06d800009b033409c6208dc1d3a0b32415c2808c000021079694930abfc1f0606fc000000002c000003f881768043981ac000026109304cad05fa001a01b16015ac50d0186d0064f017141feb0378c1aea055145760000000000007800006020c000000001019a610a40000310b9857c00000023f0065ac08f0049c0000a036dc4725010442a7000000000d1b18000011ba80000e032b8285005100000b0698000080b2cc171c02e40000a11e0000070876025dc088 else 0x1c2e4309d1e11cb098ac1dd30bd8c2763122cc1f1a04ce02e99065dc42601346c17bf013905138019bc1808007c401bc0015c14d301d0c0a8f085a81a3e0a2202dd908f800fab091e42e180638c419f0560c161c0820c245b08edc22b000000000e12cc0515501e6c0adc0620c05e00001844561447c557f727642c24008a800b7847d00a790a3481757084bc5eab0b7fc50c70604004700003c02d6031a451a50175007310b8a004cc03904566906d6025))
def nineD13 (i : Nat) : Nat := 0x968c8e889486c380c0c1844b4d49474543424118190a101104cc9c645484348e1e1406060c225a6a4a3a2a1a1208c87040a0266323a2a421b0e030306112d35251d150d09044c64205044131191d150d238785018108969a928e8a86848226561e201028099998c8e8691c3c280c0c1844b4d4947454342410a10081404c4acb464548444a61e1406060c225a6a4a3a2a1a1208703088266323a2a42230a030306112d35251d150d090454585018441312b1d15211129878501818308969a928e8a8684822c180c220998c8e8a8894c3c280c0844b4d494745434241292b150f10061104d4b4647444a61e1406060c225a6a4a3a2a1a120850803088262323a2a430f0a030306112d35251d150d09042050184412f2d191d152111290d870181830884803026322338c8e8a88948691c3c280c08440411315108cc4ccb4647444a4348e1e1406060c224a005084e4e66323a2a421a470f0a030306111d00205252b2d191d152111298785018183088a800c232acb9fe93986c7a76da6155484733ae2f12541c712a095000ffcb1c01ff982803ff2c5007fe50a00ffc99401ff981803ff2e3007fe54600ffca0c01ff931803ff243007be99a00fdd22401fda33803fd445007fc84600
def nineI13 (i : Nat) : Nat := 0xe1700000d03a000080560000e0576009b0301014210a1054307c608400009063c080b1570000b733a073e1567104711d505d00028022703d90520000b0209188f02e112a8201a123e06c90252043013a40290000000000001083d0590000305e0000001bb12250850000312d0000b049811480390000000000000000501cf01f60550000910162080000407e114200006a19004b5126f075f00ef008511800236038b1290000303c00009079100bb032904d0000e074f06500001070f519500fe05b820b703f0000e1540000303b803100000000b03640170000f1342045a13310820000c0519808f062e06f0000000001618420d08e401341550000a13c9060f0249015105300008160f1632801e11ed601704af041f033b06da1070000810eb06a0000e00700000000d00d00000000800c00003103f08ca034c02d10420000c02c220ce026506400000000db202701502f613b510f313500000000703e20786016700ac011f01d00008072705ae17b404fd01ea086000000002162b1150000b15f0040c05c880cf1020000b0010000701a00000200a061904c710c704800004044206e000040690000c02700000000000036330000606b0000f05f407d00000000b04700007005b62ea16af132202b0000f02101170000108a880b20190000a018a07600000000102a010be10d000050663004b07b000091390000000000006028e010801280884000e089d06860870050b07fb006a07a604ed0350000c166d077c081e08b00000000906700000058b5351003b046508d2169000070378119e13dc0714d412210050a10510400000d09e44404104204014c08021304000900010a0022432831820c30c1100045040
def nineD14 (i : Nat) : Nat := 0x4385020982654c961838510105031100126ffa00
def nineI14 (i : Nat) : Nat := 0x105786787d06a844c6c00000245ac10851030804474000040003034002c1800207142b80082fc5dc0943b41f02503c814000000000c21c0d2908844
def nineIndex : Nat → Nat → Option (Nat × Nat)
  | 9 => fun _ => none
  | 10 => lookupWord 18 77 6 14 6 4 nineI10
  | 11 => lookupWord 329 1311 6 18 10 4 nineI11
  | 12 => lookupWord 286 1317 8 18 10 4 nineI12
  | 13 => lookupWord 58 290 6 16 8 4 nineI13
  | 14 => lookupWord 10 37 3 12 4 4 nineI14
  | _ => fun _ => none
def nineLevels : Nat → Packing
  | 9 => (44,6,6,0,0,9,0,nineD9)
  | 10 => (679,5,6,0,0,14,0,nineD10)
  | 11 => (774,4,6,0,0,16,0,nineD11)
  | 12 => (143,3,6,0,0,15,0,nineD12)
  | 13 => (16,2,6,0,0,12,0,nineD13)
  | 14 => (1,1,6,0,0,1,0,nineD14)
  | _ => emptyPacking
def ninePack : Forest := ⟨511,14,dead.samples,nineColumns,dead.autos,nineLevels,nineIndex⟩
end PEqualNP.Outside.L_meta_2541.SignedProof

namespace PEqualNP.Outside.L_meta_2541.SignedProof
open PEqualNP.CircuitLowerBounds

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 32768 in
theorem geomPairs {g : Forest} {prior} (ok : graphValid g prior=true) :
    properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) := by
  simp only [graphValid,Bool.and_eq_true,beq_iff_eq] at ok
  exact chart_pairs ok.1.1.1 ok.1.1.2

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 32768 in
theorem geomAutos {g : Forest} {prior} (ok : graphValid g prior=true) :
    ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows)=true := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true] at ok
  exact ok.2

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 32768 in
theorem standardSlice (g : Forest) (p : Nat → Nat) (lo : ∀ q, Lower (vars q) (graphGoal q) (p q))
    (ok : graphValid g p=true) (c : ColumnInfo) (hc : c ∈ g.cols.values) :
    Slice (vars g.mask) (targetOf g) (subcube c.1 c.2.1) c.2.2.2.2 := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true] at ok
  exact col_sound c p lo (ok.1.2 c hc)

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 32768 in
theorem rawNineLower : Lower (vars 511) (graphGoal 511) 15 := by
  exact lower_forest (g:=dead) (i:=0) (hints:=13438558465) (before_sound known383 valid383)
    geomdead tablesdead (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 32768 in
theorem theta0ColumnsValid : ∀ c ∈ theta0Pack.cols.values, Slice (chartRaw 191 c) (targetOf theta0Pack) (subcube c.1 c.2.1) c.2.2.2.2 := by
  intro c hc
  change c ∈ [(0,0,0,0,11),(2,0,189,0,8),(8,0,183,0,8),(16,0,175,0,8),(32,0,159,0,8),(128,0,63,0,8),(1,0,190,0,7),(24,0,167,0,7),(160,0,31,0,7),(0,16,166,9,6)] at hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact slice_correct (ms:=[]) (base:=vars 191) (G:=graphGoal 191)
      (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) low191
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice g191 _ (before_sound known127 valid127) geom191 (2,0,189,0,8) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice g191 _ (before_sound known127 valid127) geom191 (8,0,183,0,8) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice g191 _ (before_sound known127 valid127) geom191 (16,0,175,0,8) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice g191 _ (before_sound known127 valid127) geom191 (32,0,159,0,8) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice g191 _ (before_sound known127 valid127) geom191 (128,0,63,0,8) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice g191 _ (before_sound known127 valid127) geom191 (1,0,190,0,7) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice g191 _ (before_sound known127 valid127) geom191 (24,0,167,0,7) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice g191 _ (before_sound known127 valid127) geom191 (160,0,31,0,7) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice g191 _ (before_sound known127 valid127) geom191 (0,16,166,9,6) (by decide +kernel)
  exact False.elim (List.not_mem_nil hc)
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 32768 in
theorem theta0Lower (cert : signedTables theta0Pack 10) : Lower (signRoots 191 0) (graphGoal 191) 11 := by
  apply signedLower (hints:=536879361) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact signedRoot theta0Pack (signRoots 191 0) 10 (geomPairs (g:=g191) geom191) theta0ColumnsValid (geomAutos (g:=g191) geom191) cert (by decide +kernel)
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 32768 in
theorem theta1ColumnsValid : ∀ c ∈ theta1Pack.cols.values, Slice (chartRaw 191 c) (targetOf theta1Pack) (subcube c.1 c.2.1) c.2.2.2.2 := by
  intro c hc
  change c ∈ [(0,0,0,0,11),(2,0,189,0,8),(8,0,183,0,8),(16,0,175,0,8),(32,0,159,0,8),(128,0,63,0,8),(24,0,167,0,7),(160,0,31,0,7),(0,8,163,20,6)] at hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact slice_correct (ms:=[]) (base:=vars 191) (G:=graphGoal 191)
      (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) low191
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice g191 _ (before_sound known127 valid127) geom191 (2,0,189,0,8) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice g191 _ (before_sound known127 valid127) geom191 (8,0,183,0,8) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice g191 _ (before_sound known127 valid127) geom191 (16,0,175,0,8) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice g191 _ (before_sound known127 valid127) geom191 (32,0,159,0,8) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice g191 _ (before_sound known127 valid127) geom191 (128,0,63,0,8) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice g191 _ (before_sound known127 valid127) geom191 (24,0,167,0,7) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice g191 _ (before_sound known127 valid127) geom191 (160,0,31,0,7) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice g191 _ (before_sound known127 valid127) geom191 (0,8,163,20,6) (by decide +kernel)
  exact False.elim (List.not_mem_nil hc)
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 32768 in
theorem theta1Lower (cert : signedTables theta1Pack 10) : Lower (signRoots 191 1) (graphGoal 191) 11 := by
  apply signedLower (hints:=536879361) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact signedRoot theta1Pack (signRoots 191 1) 10 (geomPairs (g:=g191) geom191) theta1ColumnsValid (geomAutos (g:=g191) geom191) cert (by decide +kernel)
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 32768 in
theorem theta3ColumnsValid : ∀ c ∈ theta3Pack.cols.values, Slice (chartRaw 191 c) (targetOf theta3Pack) (subcube c.1 c.2.1) c.2.2.2.2 := by
  intro c hc
  change c ∈ [(0,0,0,0,11),(2,0,189,0,8),(8,0,183,0,8),(16,0,175,0,8),(32,0,159,0,8),(128,0,63,0,8),(1,0,190,0,7),(24,0,167,0,7),(160,0,31,0,7),(0,8,163,20,6),(0,16,166,9,6)] at hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact slice_correct (ms:=[]) (base:=vars 191) (G:=graphGoal 191)
      (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) low191
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice g191 _ (before_sound known127 valid127) geom191 (2,0,189,0,8) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice g191 _ (before_sound known127 valid127) geom191 (8,0,183,0,8) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice g191 _ (before_sound known127 valid127) geom191 (16,0,175,0,8) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice g191 _ (before_sound known127 valid127) geom191 (32,0,159,0,8) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice g191 _ (before_sound known127 valid127) geom191 (128,0,63,0,8) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice g191 _ (before_sound known127 valid127) geom191 (1,0,190,0,7) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice g191 _ (before_sound known127 valid127) geom191 (24,0,167,0,7) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice g191 _ (before_sound known127 valid127) geom191 (160,0,31,0,7) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice g191 _ (before_sound known127 valid127) geom191 (0,8,163,20,6) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice g191 _ (before_sound known127 valid127) geom191 (0,16,166,9,6) (by decide +kernel)
  exact False.elim (List.not_mem_nil hc)
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 32768 in
theorem theta3Lower (cert : signedTables theta3Pack 10) : Lower (signRoots 191 3) (graphGoal 191) 11 := by
  apply signedLower (hints:=536879361) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact signedRoot theta3Pack (signRoots 191 3) 10 (geomPairs (g:=g191) geom191) theta3ColumnsValid (geomAutos (g:=g191) geom191) cert (by decide +kernel)
def ThetaFamily := ∀ j ∈ ([0,1,3] : List Nat), Lower (signRoots 191 j) (graphGoal 191) 11

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 32768 in
theorem allTheta (a : signedTables theta0Pack 10) (b : signedTables theta1Pack 10) (c : signedTables theta3Pack 10) : ThetaFamily := by
  intro j hj
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl | rfl
  · exact theta0Lower a
  · exact theta1Lower b
  · exact theta3Lower c
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 32768 in
theorem cut487 (theta : ThetaFamily) : Lower (signRoots 487 0) (graphGoal 487) 11 := by
  exact lower_map (ms:=([115,83,82,130,99,66,16] : List Nat).map swapRows) (base:=signRoots 191 1) (G:=graphGoal 191)
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) (theta 1 (by decide))
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 32768 in
theorem cut445 (theta : ThetaFamily) : Lower (signRoots 445 0) (graphGoal 445) 11 := by
  exact lower_map (ms:=([129,82,97,48] : List Nat).map swapRows) (base:=signRoots 191 3) (G:=graphGoal 191)
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) (theta 3 (by decide))
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 32768 in
theorem cut431 (theta : ThetaFamily) : Lower (signRoots 431 0) (graphGoal 431) 11 := by
  exact lower_map (ms:=([113,129,97,82,32,65,48] : List Nat).map swapRows) (base:=signRoots 191 3) (G:=graphGoal 191)
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) (theta 3 (by decide))
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 32768 in
theorem cut379 (theta : ThetaFamily) : Lower (signRoots 379 0) (graphGoal 379) 11 := by
  exact lower_map (ms:=([130,50,81,115,98,65] : List Nat).map swapRows) (base:=signRoots 191 0) (G:=graphGoal 191)
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) (theta 0 (by decide))
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 32768 in
theorem cut367 (theta : ThetaFamily) : Lower (signRoots 367 0) (graphGoal 367) 11 := by
  exact lower_map (ms:=([128,16,64,100,80,113,33,48] : List Nat).map swapRows) (base:=signRoots 191 3) (G:=graphGoal 191)
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) (theta 3 (by decide))
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 32768 in
theorem cut351 (theta : ThetaFamily) : Lower (signRoots 351 0) (graphGoal 351) 11 := by
  exact lower_map (ms:=([133,117,101,33,48] : List Nat).map swapRows) (base:=signRoots 191 3) (G:=graphGoal 191)
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) (theta 3 (by decide))
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 32768 in
theorem cut319 (theta : ThetaFamily) : Lower (signRoots 319 0) (graphGoal 319) 11 := by
  exact lower_map (ms:=([135,50,65] : List Nat).map swapRows) (base:=signRoots 191 0) (G:=graphGoal 191)
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) (theta 0 (by decide))
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 32768 in
theorem cut191 (theta : ThetaFamily) : Lower (signRoots 191 0) (graphGoal 191) 11 := by
  exact lower_map (ms:=([] : List Nat).map swapRows) (base:=signRoots 191 0) (G:=graphGoal 191)
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) (theta 0 (by decide))
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 32768 in
theorem cut509 (theta : ThetaFamily) : Lower (signRoots 509 0) (graphGoal 509) 12 := by
  exact lift_ok (ms:=fixRows 64 0) (base:=signRoots 445 0) (G:=graphGoal 445)
    (xs:=[(inputs.getD 6 zero,256,320)]) (by decide +kernel)
    (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) (cut445 theta)
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 32768 in
theorem cut507 (theta : ThetaFamily) : Lower (signRoots 507 0) (graphGoal 507) 12 := by
  exact lift_ok (ms:=fixRows 128 0) (base:=signRoots 379 0) (G:=graphGoal 379)
    (xs:=[(inputs.getD 7 zero,32,160)]) (by decide +kernel)
    (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) (cut379 theta)
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 32768 in
theorem cut503 (theta : ThetaFamily) : Lower (signRoots 503 0) (graphGoal 503) 12 := by
  exact lift_ok (ms:=fixRows 16 0) (base:=signRoots 487 0) (G:=graphGoal 487)
    (xs:=[(inputs.getD 4 zero,1,17)]) (by decide +kernel)
    (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) (cut487 theta)
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 32768 in
theorem cut479 (theta : ThetaFamily) : Lower (signRoots 479 0) (graphGoal 479) 12 := by
  exact lift_ok (ms:=fixRows 128 0) (base:=signRoots 351 0) (G:=graphGoal 351)
    (xs:=[(inputs.getD 7 zero,4,132)]) (by decide +kernel)
    (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) (cut351 theta)
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 32768 in
theorem cut255 (theta : ThetaFamily) : Lower (signRoots 255 0) (graphGoal 255) 12 := by
  exact lift_ok (ms:=fixRows 64 0) (base:=signRoots 191 0) (G:=graphGoal 191)
    (xs:=[(inputs.getD 6 zero,2,66)]) (by decide +kernel)
    (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) (cut191 theta)
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 32768 in
theorem nineColumnsValid (theta : ThetaFamily) : ∀ c ∈ ninePack.cols.values, Slice (chartRaw 511 c) (targetOf ninePack) (subcube c.1 c.2.1) c.2.2.2.2 := by
  intro c hc
  change c ∈ [(0,0,0,0,15),(16,0,495,0,13),(64,0,447,0,13),(128,0,383,0,13),(1,0,510,0,12),(2,0,509,0,12),(2,0,1024,0,12),(4,0,507,0,12),(4,0,1024,0,12),(8,0,503,0,12),(8,0,1024,0,12),(32,0,479,0,12),(32,0,1024,0,12),(256,0,255,0,12),(256,0,1024,0,12),(17,0,494,0,11),(24,0,1024,0,11),(66,0,1024,0,11),(80,0,431,0,11),(80,0,1024,0,11),(132,0,1024,0,11),(144,0,1024,0,11),(160,0,1024,0,11),(192,0,319,0,11),(192,0,1024,0,11),(320,0,1024,0,11),(0,16,486,9,10),(0,64,189,258,10),(3,0,508,0,9),(6,0,505,0,9),(12,0,499,0,9),(8,16,486,1,9),(2,64,189,256,9),(96,0,415,0,9),(4,128,347,32,9),(136,0,375,0,9),(264,0,247,0,9),(288,0,223,0,9),(0,2,440,69,8),(5,0,506,0,8),(9,0,486,0,8),(19,0,492,0,8),(25,0,486,0,8),(9,16,486,0,8),(0,32,94,385,8),(49,0,462,0,8),(70,0,441,0,8),(134,0,377,0,8),(164,0,347,0,8),(36,128,347,0,8),(258,0,189,0,8),(280,0,231,0,8),(322,0,189,0,8),(258,64,189,0,8),(7,0,504,0,7),(21,0,490,0,7),(35,0,476,0,7),(273,0,238,0,7)] at hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact slice_correct (ms:=[]) (base:=vars 511) (G:=graphGoal 511)
      (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) rawNineLower
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (16,0,495,0,13) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (64,0,447,0,13) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (128,0,383,0,13) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (1,0,510,0,12) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (2,0,509,0,12) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact slice_correct (ms:=fixRows 2 0) (base:=signRoots 509 0) (G:=graphGoal 509)
      (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (cut509 theta)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (4,0,507,0,12) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact slice_correct (ms:=fixRows 4 0) (base:=signRoots 507 0) (G:=graphGoal 507)
      (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (cut507 theta)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (8,0,503,0,12) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact slice_correct (ms:=fixRows 8 0) (base:=signRoots 503 0) (G:=graphGoal 503)
      (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (cut503 theta)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (32,0,479,0,12) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact slice_correct (ms:=fixRows 32 0) (base:=signRoots 479 0) (G:=graphGoal 479)
      (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (cut479 theta)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (256,0,255,0,12) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact slice_correct (ms:=fixRows 256 0) (base:=signRoots 255 0) (G:=graphGoal 255)
      (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (cut255 theta)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (17,0,494,0,11) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact slice_correct (ms:=fixRows 24 0) (base:=signRoots 487 0) (G:=graphGoal 487)
      (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (cut487 theta)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact slice_correct (ms:=fixRows 66 0) (base:=signRoots 445 0) (G:=graphGoal 445)
      (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (cut445 theta)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (80,0,431,0,11) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact slice_correct (ms:=fixRows 80 0) (base:=signRoots 431 0) (G:=graphGoal 431)
      (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (cut431 theta)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact slice_correct (ms:=fixRows 132 0) (base:=signRoots 379 0) (G:=graphGoal 379)
      (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (cut379 theta)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact slice_correct (ms:=fixRows 144 0) (base:=signRoots 367 0) (G:=graphGoal 367)
      (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (cut367 theta)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact slice_correct (ms:=fixRows 160 0) (base:=signRoots 351 0) (G:=graphGoal 351)
      (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (cut351 theta)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (192,0,319,0,11) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact slice_correct (ms:=fixRows 192 0) (base:=signRoots 319 0) (G:=graphGoal 319)
      (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (cut319 theta)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact slice_correct (ms:=fixRows 320 0) (base:=signRoots 191 0) (G:=graphGoal 191)
      (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (cut191 theta)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (0,16,486,9,10) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (0,64,189,258,10) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (3,0,508,0,9) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (6,0,505,0,9) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (12,0,499,0,9) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (8,16,486,1,9) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (2,64,189,256,9) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (96,0,415,0,9) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (4,128,347,32,9) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (136,0,375,0,9) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (264,0,247,0,9) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (288,0,223,0,9) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (0,2,440,69,8) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (5,0,506,0,8) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (9,0,486,0,8) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (19,0,492,0,8) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (25,0,486,0,8) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (9,16,486,0,8) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (0,32,94,385,8) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (49,0,462,0,8) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (70,0,441,0,8) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (134,0,377,0,8) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (164,0,347,0,8) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (36,128,347,0,8) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (258,0,189,0,8) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (280,0,231,0,8) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (322,0,189,0,8) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (258,64,189,0,8) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (7,0,504,0,7) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (21,0,490,0,7) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (35,0,476,0,7) (by decide +kernel)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact standardSlice dead _ (before_sound known383 valid383) geomdead (273,0,238,0,7) (by decide +kernel)
  exact False.elim (List.not_mem_nil hc)
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 32768 in
theorem signedNineImpossible (theta : ThetaFamily) (cert : signedTables ninePack 14) :
    Impossible graph 14 (signRoots 511 0).toFinset := by
  have noRun := signedRoot ninePack (signRoots 511 0) 14 (geomPairs (g:=dead) geomdead) (nineColumnsValid theta)
    (geomAutos (g:=dead) geomdead) cert (by decide +kernel)
  exact (show targetOf ninePack=graph by decide +kernel) ▸ noRun

end PEqualNP.Outside.L_meta_2541.SignedProof

namespace PEqualNP.Outside.L_meta_2541.SignedProof
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta0B6_0 : signedBlock theta0Pack 6 0 1=true := by
  apply signedCellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta0Layer6 : signedBlock theta0Pack 6 0 1=true := theta0B6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta0B7_0 : signedBlock theta0Pack 7 0 24=true := by
  apply signedCellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta0B7_24 : signedBlock theta0Pack 7 24 24=true := by
  apply signedCellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta0B7_48 : signedBlock theta0Pack 7 48 24=true := by
  apply signedCellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta0B7_72 : signedBlock theta0Pack 7 72 24=true := by
  apply signedCellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta0B7_96 : signedBlock theta0Pack 7 96 24=true := by
  apply signedCellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta0B7_120 : signedBlock theta0Pack 7 120 11=true := by
  apply signedCellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta0Layer7 : signedBlock theta0Pack 7 0 131=true := (@signedBlock_merge theta0Pack 7 0 120 11 (@signedBlock_merge theta0Pack 7 0 96 24 (@signedBlock_merge theta0Pack 7 0 72 24 (@signedBlock_merge theta0Pack 7 0 48 24 (@signedBlock_merge theta0Pack 7 0 24 24 theta0B7_0 theta0B7_24) theta0B7_48) theta0B7_72) theta0B7_96) theta0B7_120)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta0B8_0 : signedBlock theta0Pack 8 0 24=true := by
  apply signedCellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta0B8_24 : signedBlock theta0Pack 8 24 3=true := by
  apply signedCellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta0B8_27 : signedBlock theta0Pack 8 27 24=true := by
  apply signedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta0B8_51 : signedBlock theta0Pack 8 51 24=true := by
  apply signedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta0B8_75 : signedBlock theta0Pack 8 75 24=true := by
  apply signedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta0B8_99 : signedBlock theta0Pack 8 99 24=true := by
  apply signedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta0B8_123 : signedBlock theta0Pack 8 123 24=true := by
  apply signedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta0B8_147 : signedBlock theta0Pack 8 147 24=true := by
  apply signedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta0B8_171 : signedBlock theta0Pack 8 171 24=true := by
  apply signedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta0B8_195 : signedBlock theta0Pack 8 195 24=true := by
  apply signedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta0B8_219 : signedBlock theta0Pack 8 219 24=true := by
  apply signedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta0B8_243 : signedBlock theta0Pack 8 243 24=true := by
  apply signedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta0B8_267 : signedBlock theta0Pack 8 267 13=true := by
  apply signedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta0Layer8 : signedBlock theta0Pack 8 0 280=true := (@signedBlock_merge theta0Pack 8 0 267 13 (@signedBlock_merge theta0Pack 8 0 243 24 (@signedBlock_merge theta0Pack 8 0 219 24 (@signedBlock_merge theta0Pack 8 0 195 24 (@signedBlock_merge theta0Pack 8 0 171 24 (@signedBlock_merge theta0Pack 8 0 147 24 (@signedBlock_merge theta0Pack 8 0 123 24 (@signedBlock_merge theta0Pack 8 0 99 24 (@signedBlock_merge theta0Pack 8 0 75 24 (@signedBlock_merge theta0Pack 8 0 51 24 (@signedBlock_merge theta0Pack 8 0 27 24 (@signedBlock_merge theta0Pack 8 0 24 3 theta0B8_0 theta0B8_24) theta0B8_27) theta0B8_51) theta0B8_75) theta0B8_99) theta0B8_123) theta0B8_147) theta0B8_171) theta0B8_195) theta0B8_219) theta0B8_243) theta0B8_267)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta0B9_0 : signedBlock theta0Pack 9 0 4=true := by
  apply signedCellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta0B9_4 : signedBlock theta0Pack 9 4 24=true := by
  apply signedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta0B9_28 : signedBlock theta0Pack 9 28 6=true := by
  apply signedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta0Layer9 : signedBlock theta0Pack 9 0 34=true := (@signedBlock_merge theta0Pack 9 0 28 6 (@signedBlock_merge theta0Pack 9 0 4 24 theta0B9_0 theta0B9_4) theta0B9_28)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta0B10_0 : signedBlock theta0Pack 10 0 1=true := by
  apply signedCellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta0Layer10 : signedBlock theta0Pack 10 0 1=true := theta0B10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta0Table : signedTables theta0Pack 10 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact theta0Layer6
  · exact theta0Layer7
  · exact theta0Layer8
  · exact theta0Layer9
  · exact theta0Layer10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta1B6_0 : signedBlock theta1Pack 6 0 1=true := by
  apply signedCellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta1Layer6 : signedBlock theta1Pack 6 0 1=true := theta1B6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta1B7_0 : signedBlock theta1Pack 7 0 24=true := by
  apply signedCellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta1B7_24 : signedBlock theta1Pack 7 24 24=true := by
  apply signedCellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta1B7_48 : signedBlock theta1Pack 7 48 16=true := by
  apply signedCellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta1B7_64 : signedBlock theta1Pack 7 64 3=true := by
  apply signedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta1Layer7 : signedBlock theta1Pack 7 0 67=true := (@signedBlock_merge theta1Pack 7 0 64 3 (@signedBlock_merge theta1Pack 7 0 48 16 (@signedBlock_merge theta1Pack 7 0 24 24 theta1B7_0 theta1B7_24) theta1B7_48) theta1B7_64)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta1B8_0 : signedBlock theta1Pack 8 0 15=true := by
  apply signedCellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta1B8_15 : signedBlock theta1Pack 8 15 24=true := by
  apply signedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta1B8_39 : signedBlock theta1Pack 8 39 24=true := by
  apply signedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta1B8_63 : signedBlock theta1Pack 8 63 24=true := by
  apply signedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta1B8_87 : signedBlock theta1Pack 8 87 24=true := by
  apply signedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta1B8_111 : signedBlock theta1Pack 8 111 24=true := by
  apply signedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta1B8_135 : signedBlock theta1Pack 8 135 14=true := by
  apply signedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta1Layer8 : signedBlock theta1Pack 8 0 149=true := (@signedBlock_merge theta1Pack 8 0 135 14 (@signedBlock_merge theta1Pack 8 0 111 24 (@signedBlock_merge theta1Pack 8 0 87 24 (@signedBlock_merge theta1Pack 8 0 63 24 (@signedBlock_merge theta1Pack 8 0 39 24 (@signedBlock_merge theta1Pack 8 0 15 24 theta1B8_0 theta1B8_15) theta1B8_39) theta1B8_63) theta1B8_87) theta1B8_111) theta1B8_135)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta1B9_0 : signedBlock theta1Pack 9 0 2=true := by
  apply signedCellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta1B9_2 : signedBlock theta1Pack 9 2 16=true := by
  apply signedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta1Layer9 : signedBlock theta1Pack 9 0 18=true := (@signedBlock_merge theta1Pack 9 0 2 16 theta1B9_0 theta1B9_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta1B10_0 : signedBlock theta1Pack 10 0 1=true := by
  apply signedCellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta1Layer10 : signedBlock theta1Pack 10 0 1=true := theta1B10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta1Table : signedTables theta1Pack 10 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact theta1Layer6
  · exact theta1Layer7
  · exact theta1Layer8
  · exact theta1Layer9
  · exact theta1Layer10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta3B6_0 : signedBlock theta3Pack 6 0 2=true := by
  apply signedCellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta3Layer6 : signedBlock theta3Pack 6 0 2=true := theta3B6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta3B7_0 : signedBlock theta3Pack 7 0 24=true := by
  apply signedCellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta3B7_24 : signedBlock theta3Pack 7 24 24=true := by
  apply signedCellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta3B7_48 : signedBlock theta3Pack 7 48 24=true := by
  apply signedCellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta3B7_72 : signedBlock theta3Pack 7 72 24=true := by
  apply signedCellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta3B7_96 : signedBlock theta3Pack 7 96 24=true := by
  apply signedCellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta3B7_120 : signedBlock theta3Pack 7 120 24=true := by
  apply signedCellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta3B7_144 : signedBlock theta3Pack 7 144 24=true := by
  apply signedCellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta3B7_168 : signedBlock theta3Pack 7 168 24=true := by
  apply signedCellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta3B7_192 : signedBlock theta3Pack 7 192 3=true := by
  apply signedCellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta3Layer7 : signedBlock theta3Pack 7 0 195=true := (@signedBlock_merge theta3Pack 7 0 192 3 (@signedBlock_merge theta3Pack 7 0 168 24 (@signedBlock_merge theta3Pack 7 0 144 24 (@signedBlock_merge theta3Pack 7 0 120 24 (@signedBlock_merge theta3Pack 7 0 96 24 (@signedBlock_merge theta3Pack 7 0 72 24 (@signedBlock_merge theta3Pack 7 0 48 24 (@signedBlock_merge theta3Pack 7 0 24 24 theta3B7_0 theta3B7_24) theta3B7_48) theta3B7_72) theta3B7_96) theta3B7_120) theta3B7_144) theta3B7_168) theta3B7_192)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta3B8_0 : signedBlock theta3Pack 8 0 24=true := by
  apply signedCellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta3B8_24 : signedBlock theta3Pack 8 24 14=true := by
  apply signedCellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta3B8_38 : signedBlock theta3Pack 8 38 24=true := by
  apply signedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta3B8_62 : signedBlock theta3Pack 8 62 24=true := by
  apply signedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta3B8_86 : signedBlock theta3Pack 8 86 24=true := by
  apply signedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta3B8_110 : signedBlock theta3Pack 8 110 24=true := by
  apply signedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta3B8_134 : signedBlock theta3Pack 8 134 24=true := by
  apply signedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta3B8_158 : signedBlock theta3Pack 8 158 24=true := by
  apply signedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta3B8_182 : signedBlock theta3Pack 8 182 24=true := by
  apply signedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta3B8_206 : signedBlock theta3Pack 8 206 24=true := by
  apply signedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta3B8_230 : signedBlock theta3Pack 8 230 24=true := by
  apply signedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta3B8_254 : signedBlock theta3Pack 8 254 24=true := by
  apply signedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta3B8_278 : signedBlock theta3Pack 8 278 24=true := by
  apply signedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta3B8_302 : signedBlock theta3Pack 8 302 24=true := by
  apply signedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta3B8_326 : signedBlock theta3Pack 8 326 24=true := by
  apply signedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta3B8_350 : signedBlock theta3Pack 8 350 24=true := by
  apply signedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta3B8_374 : signedBlock theta3Pack 8 374 24=true := by
  apply signedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta3B8_398 : signedBlock theta3Pack 8 398 9=true := by
  apply signedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta3Layer8 : signedBlock theta3Pack 8 0 407=true := (@signedBlock_merge theta3Pack 8 0 398 9 (@signedBlock_merge theta3Pack 8 0 374 24 (@signedBlock_merge theta3Pack 8 0 350 24 (@signedBlock_merge theta3Pack 8 0 326 24 (@signedBlock_merge theta3Pack 8 0 302 24 (@signedBlock_merge theta3Pack 8 0 278 24 (@signedBlock_merge theta3Pack 8 0 254 24 (@signedBlock_merge theta3Pack 8 0 230 24 (@signedBlock_merge theta3Pack 8 0 206 24 (@signedBlock_merge theta3Pack 8 0 182 24 (@signedBlock_merge theta3Pack 8 0 158 24 (@signedBlock_merge theta3Pack 8 0 134 24 (@signedBlock_merge theta3Pack 8 0 110 24 (@signedBlock_merge theta3Pack 8 0 86 24 (@signedBlock_merge theta3Pack 8 0 62 24 (@signedBlock_merge theta3Pack 8 0 38 24 (@signedBlock_merge theta3Pack 8 0 24 14 theta3B8_0 theta3B8_24) theta3B8_38) theta3B8_62) theta3B8_86) theta3B8_110) theta3B8_134) theta3B8_158) theta3B8_182) theta3B8_206) theta3B8_230) theta3B8_254) theta3B8_278) theta3B8_302) theta3B8_326) theta3B8_350) theta3B8_374) theta3B8_398)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta3B9_0 : signedBlock theta3Pack 9 0 6=true := by
  apply signedCellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta3B9_6 : signedBlock theta3Pack 9 6 24=true := by
  apply signedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta3B9_30 : signedBlock theta3Pack 9 30 11=true := by
  apply signedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta3Layer9 : signedBlock theta3Pack 9 0 41=true := (@signedBlock_merge theta3Pack 9 0 30 11 (@signedBlock_merge theta3Pack 9 0 6 24 theta3B9_0 theta3B9_6) theta3B9_30)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta3B10_0 : signedBlock theta3Pack 10 0 1=true := by
  apply signedCellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta3Layer10 : signedBlock theta3Pack 10 0 1=true := theta3B10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem theta3Table : signedTables theta3Pack 10 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact theta3Layer6
  · exact theta3Layer7
  · exact theta3Layer8
  · exact theta3Layer9
  · exact theta3Layer10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB9_0 : signedBlock ninePack 9 0 24=true := by
  apply signedCellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB9_24 : signedBlock ninePack 9 24 20=true := by
  apply signedCellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineLayer9 : signedBlock ninePack 9 0 44=true := (@signedBlock_merge ninePack 9 0 24 20 nineB9_0 nineB9_24)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB10_0 : signedBlock ninePack 10 0 21=true := by
  apply signedCellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB10_21 : signedBlock ninePack 10 21 24=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB10_45 : signedBlock ninePack 10 45 24=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB10_69 : signedBlock ninePack 10 69 24=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB10_93 : signedBlock ninePack 10 93 24=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB10_117 : signedBlock ninePack 10 117 24=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB10_141 : signedBlock ninePack 10 141 24=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB10_165 : signedBlock ninePack 10 165 24=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB10_189 : signedBlock ninePack 10 189 24=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB10_213 : signedBlock ninePack 10 213 24=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB10_237 : signedBlock ninePack 10 237 24=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB10_261 : signedBlock ninePack 10 261 24=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB10_285 : signedBlock ninePack 10 285 24=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB10_309 : signedBlock ninePack 10 309 24=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB10_333 : signedBlock ninePack 10 333 24=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB10_357 : signedBlock ninePack 10 357 24=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB10_381 : signedBlock ninePack 10 381 24=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB10_405 : signedBlock ninePack 10 405 24=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB10_429 : signedBlock ninePack 10 429 24=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB10_453 : signedBlock ninePack 10 453 24=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB10_477 : signedBlock ninePack 10 477 24=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB10_501 : signedBlock ninePack 10 501 24=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB10_525 : signedBlock ninePack 10 525 24=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB10_549 : signedBlock ninePack 10 549 24=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB10_573 : signedBlock ninePack 10 573 24=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB10_597 : signedBlock ninePack 10 597 24=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB10_621 : signedBlock ninePack 10 621 24=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB10_645 : signedBlock ninePack 10 645 24=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB10_669 : signedBlock ninePack 10 669 10=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineLayer10 : signedBlock ninePack 10 0 679=true := (@signedBlock_merge ninePack 10 0 669 10 (@signedBlock_merge ninePack 10 0 645 24 (@signedBlock_merge ninePack 10 0 621 24 (@signedBlock_merge ninePack 10 0 597 24 (@signedBlock_merge ninePack 10 0 573 24 (@signedBlock_merge ninePack 10 0 549 24 (@signedBlock_merge ninePack 10 0 525 24 (@signedBlock_merge ninePack 10 0 501 24 (@signedBlock_merge ninePack 10 0 477 24 (@signedBlock_merge ninePack 10 0 453 24 (@signedBlock_merge ninePack 10 0 429 24 (@signedBlock_merge ninePack 10 0 405 24 (@signedBlock_merge ninePack 10 0 381 24 (@signedBlock_merge ninePack 10 0 357 24 (@signedBlock_merge ninePack 10 0 333 24 (@signedBlock_merge ninePack 10 0 309 24 (@signedBlock_merge ninePack 10 0 285 24 (@signedBlock_merge ninePack 10 0 261 24 (@signedBlock_merge ninePack 10 0 237 24 (@signedBlock_merge ninePack 10 0 213 24 (@signedBlock_merge ninePack 10 0 189 24 (@signedBlock_merge ninePack 10 0 165 24 (@signedBlock_merge ninePack 10 0 141 24 (@signedBlock_merge ninePack 10 0 117 24 (@signedBlock_merge ninePack 10 0 93 24 (@signedBlock_merge ninePack 10 0 69 24 (@signedBlock_merge ninePack 10 0 45 24 (@signedBlock_merge ninePack 10 0 21 24 nineB10_0 nineB10_21) nineB10_45) nineB10_69) nineB10_93) nineB10_117) nineB10_141) nineB10_165) nineB10_189) nineB10_213) nineB10_237) nineB10_261) nineB10_285) nineB10_309) nineB10_333) nineB10_357) nineB10_381) nineB10_405) nineB10_429) nineB10_453) nineB10_477) nineB10_501) nineB10_525) nineB10_549) nineB10_573) nineB10_597) nineB10_621) nineB10_645) nineB10_669)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB11_0 : signedBlock ninePack 11 0 11=true := by
  apply signedCellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB11_11 : signedBlock ninePack 11 11 24=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB11_35 : signedBlock ninePack 11 35 24=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB11_59 : signedBlock ninePack 11 59 24=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB11_83 : signedBlock ninePack 11 83 24=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB11_107 : signedBlock ninePack 11 107 24=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB11_131 : signedBlock ninePack 11 131 24=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB11_155 : signedBlock ninePack 11 155 24=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB11_179 : signedBlock ninePack 11 179 24=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB11_203 : signedBlock ninePack 11 203 24=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB11_227 : signedBlock ninePack 11 227 24=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB11_251 : signedBlock ninePack 11 251 12=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB11_263 : signedBlock ninePack 11 263 24=true := by
  apply signedCellsBlock (ar:=11) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB11_287 : signedBlock ninePack 11 287 24=true := by
  apply signedCellsBlock (ar:=11) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB11_311 : signedBlock ninePack 11 311 24=true := by
  apply signedCellsBlock (ar:=11) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB11_335 : signedBlock ninePack 11 335 24=true := by
  apply signedCellsBlock (ar:=11) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB11_359 : signedBlock ninePack 11 359 24=true := by
  apply signedCellsBlock (ar:=11) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB11_383 : signedBlock ninePack 11 383 24=true := by
  apply signedCellsBlock (ar:=11) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB11_407 : signedBlock ninePack 11 407 24=true := by
  apply signedCellsBlock (ar:=11) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB11_431 : signedBlock ninePack 11 431 24=true := by
  apply signedCellsBlock (ar:=11) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB11_455 : signedBlock ninePack 11 455 24=true := by
  apply signedCellsBlock (ar:=11) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB11_479 : signedBlock ninePack 11 479 24=true := by
  apply signedCellsBlock (ar:=11) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB11_503 : signedBlock ninePack 11 503 24=true := by
  apply signedCellsBlock (ar:=11) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB11_527 : signedBlock ninePack 11 527 24=true := by
  apply signedCellsBlock (ar:=11) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB11_551 : signedBlock ninePack 11 551 24=true := by
  apply signedCellsBlock (ar:=11) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB11_575 : signedBlock ninePack 11 575 24=true := by
  apply signedCellsBlock (ar:=11) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB11_599 : signedBlock ninePack 11 599 24=true := by
  apply signedCellsBlock (ar:=11) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB11_623 : signedBlock ninePack 11 623 24=true := by
  apply signedCellsBlock (ar:=11) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB11_647 : signedBlock ninePack 11 647 24=true := by
  apply signedCellsBlock (ar:=11) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB11_671 : signedBlock ninePack 11 671 24=true := by
  apply signedCellsBlock (ar:=11) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB11_695 : signedBlock ninePack 11 695 24=true := by
  apply signedCellsBlock (ar:=11) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB11_719 : signedBlock ninePack 11 719 24=true := by
  apply signedCellsBlock (ar:=11) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB11_743 : signedBlock ninePack 11 743 24=true := by
  apply signedCellsBlock (ar:=11) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB11_767 : signedBlock ninePack 11 767 7=true := by
  apply signedCellsBlock (ar:=11) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineLayer11 : signedBlock ninePack 11 0 774=true := (@signedBlock_merge ninePack 11 0 767 7 (@signedBlock_merge ninePack 11 0 743 24 (@signedBlock_merge ninePack 11 0 719 24 (@signedBlock_merge ninePack 11 0 695 24 (@signedBlock_merge ninePack 11 0 671 24 (@signedBlock_merge ninePack 11 0 647 24 (@signedBlock_merge ninePack 11 0 623 24 (@signedBlock_merge ninePack 11 0 599 24 (@signedBlock_merge ninePack 11 0 575 24 (@signedBlock_merge ninePack 11 0 551 24 (@signedBlock_merge ninePack 11 0 527 24 (@signedBlock_merge ninePack 11 0 503 24 (@signedBlock_merge ninePack 11 0 479 24 (@signedBlock_merge ninePack 11 0 455 24 (@signedBlock_merge ninePack 11 0 431 24 (@signedBlock_merge ninePack 11 0 407 24 (@signedBlock_merge ninePack 11 0 383 24 (@signedBlock_merge ninePack 11 0 359 24 (@signedBlock_merge ninePack 11 0 335 24 (@signedBlock_merge ninePack 11 0 311 24 (@signedBlock_merge ninePack 11 0 287 24 (@signedBlock_merge ninePack 11 0 263 24 (@signedBlock_merge ninePack 11 0 251 12 (@signedBlock_merge ninePack 11 0 227 24 (@signedBlock_merge ninePack 11 0 203 24 (@signedBlock_merge ninePack 11 0 179 24 (@signedBlock_merge ninePack 11 0 155 24 (@signedBlock_merge ninePack 11 0 131 24 (@signedBlock_merge ninePack 11 0 107 24 (@signedBlock_merge ninePack 11 0 83 24 (@signedBlock_merge ninePack 11 0 59 24 (@signedBlock_merge ninePack 11 0 35 24 (@signedBlock_merge ninePack 11 0 11 24 nineB11_0 nineB11_11) nineB11_35) nineB11_59) nineB11_83) nineB11_107) nineB11_131) nineB11_155) nineB11_179) nineB11_203) nineB11_227) nineB11_251) nineB11_263) nineB11_287) nineB11_311) nineB11_335) nineB11_359) nineB11_383) nineB11_407) nineB11_431) nineB11_455) nineB11_479) nineB11_503) nineB11_527) nineB11_551) nineB11_575) nineB11_599) nineB11_623) nineB11_647) nineB11_671) nineB11_695) nineB11_719) nineB11_743) nineB11_767)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB12_0 : signedBlock ninePack 12 0 8=true := by
  apply signedCellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB12_8 : signedBlock ninePack 12 8 24=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB12_32 : signedBlock ninePack 12 32 24=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB12_56 : signedBlock ninePack 12 56 22=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB12_78 : signedBlock ninePack 12 78 24=true := by
  apply signedCellsBlock (ar:=11) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB12_102 : signedBlock ninePack 12 102 24=true := by
  apply signedCellsBlock (ar:=11) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB12_126 : signedBlock ninePack 12 126 17=true := by
  apply signedCellsBlock (ar:=11) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineLayer12 : signedBlock ninePack 12 0 143=true := (@signedBlock_merge ninePack 12 0 126 17 (@signedBlock_merge ninePack 12 0 102 24 (@signedBlock_merge ninePack 12 0 78 24 (@signedBlock_merge ninePack 12 0 56 22 (@signedBlock_merge ninePack 12 0 32 24 (@signedBlock_merge ninePack 12 0 8 24 nineB12_0 nineB12_8) nineB12_32) nineB12_56) nineB12_78) nineB12_102) nineB12_126)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB13_0 : signedBlock ninePack 13 0 5=true := by
  apply signedCellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB13_5 : signedBlock ninePack 13 5 11=true := by
  apply signedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineLayer13 : signedBlock ninePack 13 0 16=true := (@signedBlock_merge ninePack 13 0 5 11 nineB13_0 nineB13_5)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineB14_0 : signedBlock ninePack 14 0 1=true := by
  apply signedCellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineLayer14 : signedBlock ninePack 14 0 1=true := nineB14_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nineTable : signedTables ninePack 14 := by
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
  · exact nineLayer9
  · exact nineLayer10
  · exact nineLayer11
  · exact nineLayer12
  · exact nineLayer13
  · exact nineLayer14
end PEqualNP.Outside.L_meta_2541.SignedProof

namespace PEqualNP.Outside.L_meta_2541.SignedProof
open PEqualNP.CircuitLowerBounds

def polarityRoots (b : Bool) := signRoots 511 (if b then 0 else 9)

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 32768 in
theorem bitRoots : ∀ (b : Bool) (r : Row), (polarityRoots b).map (bit r) =
    List.ofFn (fun j : Fin 9 => if j=0 then b != sample r 0 else sample r j) := by decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 32768 in
theorem polarityEssential (b : Bool) : ∀ a ∈ polarityRoots b, Essential graph (polarityRoots b) a := by
  let j := if b then 0 else 9
  let hs := signedPairs 511 j 13438558465
  have check : checkEssential graph (polarityRoots b) hs = true := by cases b <;> decide +kernel
  have all : hs.map Prod.fst = polarityRoots b := by cases b <;> decide +kernel
  intro a ha
  apply essential_ok check a
  rw [all]
  exact List.mem_toFinset.mpr ha

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 32768 in
theorem polarityImpossible (theta : ThetaFamily) (cert : signedTables ninePack 14) (b : Bool) :
    Impossible graph 14 (polarityRoots b).toFinset := by
  cases b with
  | false => exact dead_start (before_sound known383 valid383) geomdead tablesdead
  | true => exact signedNineImpossible theta cert

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 32768 in
theorem signedEvaluation (b : Bool) (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates (polarityRoots b)).getD i zero) =
      (C.wires (List.ofFn (fun j : Fin 9 => if j=0 then b != sample r 0 else sample r j))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (legal g hg).1),bitRoots]
  rfl

-- Every coordinate is essential, so a normalized live computation must start with every raw wire.
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 32768 in
theorem signedMismatch (theta : ThetaFamily) (cert : signedTables ninePack 14)
    (C : Circuit) (b : Bool) (legal : PEqualNP.MetaComplexity.FanInTwo C) (small : C.size≤14) :
    ∃ x : Fin 9 → Bool, PEqualNP.MetaComplexity.circuitFun 9 C
      (fun j => if j=0 then b != x 0 else x j) ≠ edge x := by
  by_contra! computes
  have out : (execute C.gates (polarityRoots b)).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (signedEvaluation b C legal C.output r).trans ((computes (sample r)).trans (edge_table r).symm)
  rw [List.getD_eq_getElem?_getD] at out
  have hm : graph ∈ execute C.gates (polarityRoots b) := by
    cases h : (execute C.gates (polarityRoots b))[C.output]? with
    | none => simp only [h,Option.getD_none] at out; exact False.elim (graph_proper.1 out.symm)
    | some v => simp only [h,Option.getD_some] at out; exact out ▸ List.mem_of_getElem? h
  obtain ⟨k,t,S,hk,run,sub⟩ := extract C.gates (polarityRoots b) legal graph_proper hm
  have he : (polarityRoots b).toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun ha => ?_,sub a⟩
    obtain ⟨r,s,hd,hs⟩ := polarityEssential b a ha
    exact raw_required run (polarityRoots b) a sub r s hd hs
  rw [←he] at run
  exact polarityImpossible theta cert b k t (hk.trans small) run
end PEqualNP.Outside.L_meta_2541.SignedProof


theorem PEqualNP.Outside.L_meta_2541 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → (List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.inputs.contains (0 : ℕ)) x1.gates).length ≤ (1 : ℕ) → ∃ (x6 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x7 : Fin (9 : ℕ)) => if x7 = (0 : Fin (9 : ℕ)) then x2 != x6 (0 : Fin (9 : ℕ)) else x6 x7) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro C b legal small _
  exact PEqualNP.Outside.L_meta_2541.SignedProof.signedMismatch
    (PEqualNP.Outside.L_meta_2541.SignedProof.allTheta PEqualNP.Outside.L_meta_2541.SignedProof.theta0Table
      PEqualNP.Outside.L_meta_2541.SignedProof.theta1Table PEqualNP.Outside.L_meta_2541.SignedProof.theta3Table)
    PEqualNP.Outside.L_meta_2541.SignedProof.nineTable C b legal small
