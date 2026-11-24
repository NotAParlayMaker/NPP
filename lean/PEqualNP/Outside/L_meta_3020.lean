import PEqualNP.Defs

/-
L-meta-3020. The prescribed OR and the AND of at most two wires give 55
initial truth-table profiles and 40 search roots. Setting input 1 to
false leaves an eight-input graph. A 299-state certificate proves that
the free OR leaves its lower bound at twelve. The checked 828-state
clipped-graph certificate gives six further restrictions by symmetry. A
2,195-state forest excludes every thirteen-gate suffix.

The circuit normalization, finite restrictions, and unsigned subgraph
certificates are from L-meta-1667 by @loris-olsem, PR #4332, commit
78e692de1384bfc0954186b781f1c251f6a1090f, original file blob
fc4ba1121de31fdfa08b135ece199d4d4a9852e8. The batched row verifier
builds on our L-meta-2541, PR #7376. The 299-state and 2,195-state forests and the root profiles
here are specific to the two prescribed gates.
-/
namespace PEqualNP.Outside.L_meta_3020.Search
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
def orPath (levels : Nat → Packing) : Nat → Nat → Nat → Nat × Nat
  | 0, _, _ => (0, 0)
  | 1, _, _ => (288, 0)
  | 2, k, i =>
    let (_,_,_,_,_,_,_,data) := levels k
    let v := packedAt data (i*21) 21
    (288 ||| ((v &&& 1023) <<< 10), v >>> 10)
  | d+3, k, i =>
    let (_,_,_,p,_,_,_,data) := levels k
    let v := packedAt data (i*(12+p)) (12+p)
    let op := v &&& 1023
    let (prev, live) := orPath levels (d+2) (k+1) ((v >>> 10) &&& ((1 <<< p)-1))
    let keep := v >>> (10+p)
    let a := 1 <<< (op &&& 15)
    let b := 1 <<< ((op >>> 4) &&& 15)
    let l := if keep &&& 1 = 0 then live - (live &&& a) else live
    let m := if keep &&& 2 = 0 then l - (l &&& b) else l
    (prev ||| (op <<< (10*(d+2))), m ||| (1 <<< (11+d)))

def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,format,data) := g.levels k
  let (ops,live) := if format = 78 then orPath g.levels depth k i else
    let len := 10*storedDepth g depth
    let width := len+raw.length+depth
    let recp := packedAt data (i*width) width
    (recp &&& ((1 <<< len)-1),recp >>> len)
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive live bank)

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

def orHint (bits : Nat → Nat) (first count sw cw depth : Nat) :
    Nat → Nat → List (Nat × Nat) → List (Nat × Nat)
  | 0, _, tail => tail
  | fuel+1, code, tail =>
    if code < count then
      let t := packedAt bits (first + code*(cw+depth)) (cw+depth)
      (t &&& ((1 <<< cw)-1),t >>> cw) :: tail
    else
      let pos := first + count*(cw+depth) + (code-count)*(2*sw)
      let v := packedAt bits pos (2*sw)
      orHint bits first count sw cw depth fuel (v &&& ((1 <<< sw)-1))
        (orHint bits first count sw cw depth fuel (v >>> sw) tail)

def orReadHints (g : Forest) (k i : Nat) : List (Nat × Nat) :=
  let (num,d,cw,p,sw,ow,format,data) := g.levels k
  if format = 78 then
    let base := num*(if d=2 then 21 else 12+p)
    let book := base+num*ow
    let pos := book+packedAt data (base+i*ow) ow
    let count := packedAt data book 14
    let size := packedAt data pos 6
    (List.range size).foldr (fun j acc =>
      orHint data (book+14) count sw cw d 20 (packedAt data (pos+6+j*sw) sw) acc) []
  else
    let base := num*(10*storedDepth g d+(wiresOf g).length+d)
    let pos := base+num*ow+packedAt data (base+i*ow) ow
    getPairs data cw d (packedAt data pos 5) (pos+5+format)

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
end PEqualNP.Outside.L_meta_3020.Search
namespace PEqualNP.Outside.L_meta_3020.Search
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

end PEqualNP.Outside.L_meta_3020.Search
namespace PEqualNP.Outside.L_meta_3020.Search

def signRoots (m j : Nat) := (selected m).map (fun (i,a) => if i=j then neg a else a)

def chartRaw (m : Nat) (c : ColumnInfo) :=
  if c.2.2.1 ≥ 3072 then vars m ++ [bin false (inputs.getD ((c.2.2.1-3072)/16) zero) (inputs.getD ((c.2.2.1-3072)%16) zero)] else
  if c.2.2.1 ≥ 2048 then vars m ++ [bin true (inputs.getD 0 zero) (inputs.getD 2 zero)] else
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
  let rules := (orReadHints g k i).filterMap (fun (a,b) => signedRule g ops depth bank a b)
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

end PEqualNP.Outside.L_meta_3020.Search
namespace PEqualNP.Outside.L_meta_3020.Search
def signedContextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let rules := (orReadHints g k i).filterMap (fun (a,b) => signedRule g ops depth bank a b)
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

end PEqualNP.Outside.L_meta_3020.Search
namespace PEqualNP.Outside.L_meta_3020.Search
def orColumns : IndexTree ColumnInfo := (.fork 51 (.fork 25 (.fork 12 (.fork 6 (.fork 3 (.leaf [(0,0,0,0,15),(16,0,495,0,13),(64,0,447,0,13)]) (.leaf [(128,0,383,0,13),(1,0,510,0,12),(2,0,2050,0,12)])) (.fork 3 (.leaf [(4,0,507,0,12),(8,0,503,0,12),(32,0,479,0,12)]) (.leaf [(256,0,255,0,12),(17,0,494,0,11),(24,0,487,0,11)]))) (.fork 6 (.fork 3 (.leaf [(66,0,445,0,11),(132,0,379,0,11),(144,0,367,0,11)]) (.leaf [(160,0,351,0,11),(192,0,319,0,11),(320,0,191,0,11)])) (.fork 3 (.leaf [(0,16,486,9,10),(0,64,189,258,10),(3,0,508,0,9)]) (.leaf [(6,0,505,0,9),(12,0,499,0,9),(8,16,486,1,9),(2,64,189,256,9)])))) (.fork 13 (.fork 6 (.fork 3 (.leaf [(96,0,415,0,9),(4,128,347,32,9),(136,0,375,0,9)]) (.leaf [(264,0,247,0,9),(288,0,223,0,9),(256,64,189,2,9)])) (.fork 3 (.leaf [(0,1,460,50,8),(0,2,440,69,8),(0,4,369,138,8)]) (.leaf [(5,0,506,0,8),(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8)]))) (.fork 6 (.fork 3 (.leaf [(19,0,492,0,8),(25,0,486,0,8),(9,16,486,0,8)]) (.leaf [(0,32,94,385,8),(36,0,347,0,8),(40,0,471,0,8)])) (.fork 3 (.leaf [(49,0,462,0,8),(67,0,444,0,8),(70,0,441,0,8)]) (.leaf [(134,0,377,0,8),(140,0,371,0,8),(164,0,347,0,8),(36,128,347,0,8)]))))) (.fork 25 (.fork 12 (.fork 6 (.fork 3 (.leaf [(258,0,189,0,8),(260,0,251,0,8),(280,0,231,0,8)]) (.leaf [(322,0,189,0,8),(258,64,189,0,8),(2,1,460,48,7)])) (.fork 3 (.leaf [(4,2,440,65,7),(2,4,369,136,7),(7,0,504,0,7)]) (.leaf [(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7)]))) (.fork 6 (.fork 3 (.leaf [(21,0,490,0,7),(32,1,460,18,7),(1,32,94,384,7)]) (.leaf [(35,0,476,0,7),(74,0,437,0,7),(133,0,378,0,7)])) (.fork 3 (.leaf [(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7)]) (.leaf [(273,0,238,0,7),(256,32,94,129,7),(32,256,151,72,7),(296,0,215,0,7)])))) (.fork 13 (.fork 6 (.fork 3 (.leaf [(5,2,440,64,6),(10,4,369,128,6),(34,1,460,16,6)]) (.leaf [(66,1,396,48,6),(96,1,396,18,6),(260,8,227,16,6)])) (.fork 3 (.leaf [(257,32,94,128,6),(40,256,151,64,6),(288,16,198,9,6)]) (.leaf [(21,2,424,64,5),(29,0,482,0,5),(69,2,440,0,5),(74,4,305,128,5)]))) (.fork 6 (.fork 3 (.leaf [(133,2,312,64,5),(138,4,369,0,5),(276,8,227,0,5)]) (.leaf [(273,32,78,128,5),(324,8,163,16,5),(321,32,30,128,5)])) (.fork 3 (.leaf [(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)]) (.leaf [(15,0,480,0,4),(39,0,344,0,4),(0,0,3128,0,15),(0,0,3160,0,15)]))))))
def orD9 (i : Nat) : Nat := 0xc928710d11900419050b7ea6d8b09098bee68546259d1053d3825bed1c2058b8422b7928454174df92f18e7246ef9e61eb6e9bc4a23b43300570100ae04d02600f007713211904ca26202f01710a8455022411008893629b88d146883421a00bc03441b68b2c4962350f687743f01ba0bb05c82dc16a0ad05482f60eb06583ec16e0a305f80ec06e01f00018a8b582aa554aa9552aa5aeaa96baaa554aa9552aa5aeb5d55311d54bab516eae14c29552aa554aa9552aa554aa9792f25e4bc951711d54c47552aa554aa9552a2d54aa9552ead54aa9552aa623aa98530a5f6bed552f25e4bab552aa554aa9552aa545b7b6baaa554adf552aa5aeb39672aa554aa9552aa554aa9552aa554aa9552aa554aa9552aa554aa9552c3d6fac1552a2cec5523ae334e70bd39b334e3da33855d177da537554cdd1439de548d89a35dc68d76da51c2b756c1a8340574d011d337474ca0bd59d6a0c4d5d2fe2f4be5a72f36a0bcda7c03a20b88bd2de2f658d872cf698ae9a72b52f4acccd2a92f4aa0bd2a22f4a7ccd28f69ca1d9690e61c9cd5d4e46a1391a625c699381754df6a08e1a7232699209a82106a48296d1f76b47c1ad1e66b4769ad1d05b47413d006a20016881b55746d51d1b069c6a95d1aa474694bd19d698012880049dc012660049545d9ac003a205b0bd16b2f4565a51456b44855210069c3d9ad0f5334391a60df69800a99002a21009970029dc00a66002b742f1a50bc6b42eda50ad5482b152001a2000677001998006550a5694295a109e694259a5093684220cd08269c209a60726b4002dd
def orD10 (i : Nat) : Nat := (if i<3 then (if i<1 then 0x98039a200e2994386600e28843865c0e277038b30665a719869c0de994376600de8843765c0de770379980decc196698655a619369864da5192698649a51926b0645a6191694645ac1914f0641a61906950d998036a20635a718c69c625a74356600d6884346600d288034b3060da718269c601a617f6980ce880339980ce55033b300ca880329dc0ca660329540cacc031a200c6558315480c288030b300be8802f9dc0becc17069c5b9a716e6985ad9816a6605a8bc1686605a193167670599a71666985919716269857da715c69c561a7158698559a71566985559515564c555521554305515215467054da71536980ba8802eb300b68802d9dc0b6cc14d69c531a714a69c529a602ca200b27742c6580b26602c954525a614869c521a6148694521a142b6600ae8802bb310a99802aa210a99702a9dc0aacc14069c500bc13f69c4f5a713d6984f1a713c6980a6880299dc0a6660299540a6cc13b69c4eda613b6944dda71376980a288028b304c5a61306984bda6027a2009e664275d409e55027b304b9a612e6944b97512c6984b19312b6984ada112b5c44a9a612a64c48da611b69409699024a2008e88022a6408a8842265c08a77021a640868842165c08677021998086cc110694435a5020a640828842065c082770209990802c10a69407e9901fa2107d9701f9dc07e6641f69607d7501f95507c7c01fb3007a8801e999079a501e9540768801d9dc0766601d956075521096844219710669441952106684419ac01ca200727701c999071a501c9560717181c57006e8841b65c06e7701b99906da501b95606d5201aa6406a8841a65c06a7701a999069a501a9560695201a889069a141a48406a11019a20066cc018a2006277018b303eda70fa69c3e1a70f86983dda70f76983dda50f669c3d9a60f66943d9520f569905d98017a2105998016a2005acc0f069c3bda70ed69c3b5a60ec69c3b1a6015a2005666015954056cc0eb69c3ada60eb6943a18b8146320511c012b30046cc0d86a0361ac0d5660350bc0d26b0345ac0d15b2040bc010b3033dac0ce6b03396c0c36b030d1c00fb302f5ac0bb6a02edac0ba6a403a8880e6302cd2b00da200366600db300328800c998032cc0a9684299980a6270295980a4684291ac0a36b002ecc09b6a026dac09a6a4260bc0976a60298c009b302359808c6602309c008a650209c007a6501d98007a2022198006a6501998006a2001a66005a6501598005a20016660058441f9a807e6801f9ac07467001299004a2001266004b3000e99003a2100d9600399900d2c003b3000a99002a2000a66002b301a9a206a684006cc0666a0199ac0656a4189a9000a6500198000a2000266000b30181a905e684179ac05d684175ac05c6a4171a205a6b01415c0504700e9ac0392f007da501c6840398c else (if i<2 then 0x7eccc39a21671a8c38a230e187c386330e17cc385730e10c5996a0ce1a7338698ce1ac33769b0dd87c375d8cd9a8336699659a899661d659a6335698cd596334698cd1ac3344f1649a832d65b0c688c316145d6ccc30a230bd8732969c5becc3276a0c9da7327698c9da53276b0c99a632569cc91a63216a0c85a7321698c84bc3206a0c81a7320698c81a55686565a15256765659d525656a2591875626a157da831b659571a855c694c64bc55b66156998559660c5da65586a0c59a65566a1555985556565555255466154da8152b330ba88c2d61d535a831369d52d9614bb30c45a831169cc45a6311694c45ac310698c3da730f658c39a6c2ca230b187c2c61b0b176c2c6170b175c2c5970b2555496a252587549695521a830b69cc25a7309698c21a7308698c21a530769cc1da630669cc19a6136b304d2ccc28a230a18cc282330a15cc28b30c11a63046b04cacc5316a14c5a63036a0c0da6303694c0dac5306a14c1a6302698c09ac52e6a14b9a652d5d54b1a852b6a14ada652b6954ad75529660bf9a72fe698bf5a72fc69cbf1a62fb69cbe9a7526661495982f669cbd1a62f369cbcda62f269948da82f169cbc5a62f069cbbda72ef698402ccc19a23061874fb6a0bb1a74f96583e6cc2ea6a0ba9a72ea698ba9a52ea6b0ba5a62e869cba1962e76993dda84f76953d9a84f66963d9524f56a23a11c8e622e3811c2e4270b8c9c0dea64b81a90d4b30b79ac8d147031acc0c2b30b6dac0c1a6430299c0ea20b5dac0aeb3303688c0d61b03288c0c61b0308c2d4684b51ab2d46b12a5a80a8b30b491c2d06a4b3da92ce6a4b396c2cc6a4b2da988d471221864881b0222cc88760621d8c071b30b05acc0426301288c0461b00e88c0361b00a88c02618af9ac2bd0f0aed7c2bb5b0ae5ac45a6b11690c059b30acd982a62f0a8dac2a3530a759c2966b0162cc292660a3d9828d660a318c057b30a25982876609f19827c64c15acc2776609d1982635d0969ac2516949355324c50c929a123a6948e952239508156cc2346608c59822a6b089dac2265b08993c052b3088998051a651449c050a2113d9804fa20136cc2126601329944c27012e882116711299804aa20126888496321255c20f5f083d5c20f4b083d1c20f4308312c048a6512198048a21121970489dc11e884470b011ecc20169c801a72006b08011c1fc69c7e5ac046a6511998046a211182c046b30116881e42f0112880449dc112cc1e269c781a61e06b077da71df69877dac1df5f010e66042b30106661d769c75da61d5698749a71d069c735a61cc6b0102994406601028803fa650fd9803fa210fd9703f9dd0fc9c03fb30715a71c469c70da61c34f0709a61bb6b00f68803ca200f27703ba200ee7703b9986adac03aa200ea7703a9980ea5543a6b10e94c039a650e5 else 0x59464acb3e167c2cf859f0b3e228e4084875d165167c451c88dd0eb992b2cf885dd0a2167c2cf859f0b3e167c2cf859f0b3e167c2cf859f0b3e167c2cf859f0b3e167c2cf859f0b3e167c2cf859f0b3e167c2cf859f0b3e167c2cf859f0b3e167c2cf859f0b3e167c2cf859f0b3e167c2cf859f0b3e167c2cf859f0b3e167c2cf859f0b3e167c2cf859f0b3e167c2cf859f0b3e167c2cf859f0b3e167c2cf859f0b3e167c2cf859f0b3e167c4234846908d211a42348378f479e8f3d1e8240f6120423fd67facfc11f073d845ad4b3e16b52cf859f0f47967c3cb85b7cb3e167c2cf859f0b3e167c3c525a08b41167c3bc87790b5a9b562d6a68a8b3e1d842d6a7610e5499012d6a5ad4c8099013a5a72a4b5a96b52dbe5ad4b3e1c37378a6eb4b9e173c2d6a5ad4b5a9b562d6a6c68d6f1ab4350260d4d1516b52dbe5ad4b3e1a002cf86758b5a967c32566644b3e19012cf864acc80995e2cf864acc80990131ae5ad4b3e167c2cf862b4c3898352ff25ad4b5a96b52d6a5ad4b5a97ab2d6a5dbcb5a96b52e785cf0b5a96b52d6a5ad4b6f96b52cf859f0b3e16df2e245c48b3e167c2dbe5ad4b5a96822cf85948b1415b62b6c5630a8894d529aa51b1ac571ab1571aad972a7b31a91a56a3694f39973cd4b0a7a9969e65da79943c9694f255229da65a759429db30f19ac3bb670a22cc3ba65cee99c3b9670ee19ca845eca12cc3b468ced1ac3ac2f19f99567d6959f19567b6559e9a526db319a5956695d5999956665d599974266b31995a33a9694ea5a33a9548ea5ac66368d98d7366350e98d5c662655989756625d198973a62509985a33a069596da5256b31951a7654695945a5650695935a3a4d50d931a764c69592d94a4b54e92d43a4b54a92d42396694e59a13966b1929a5a4a549921a164769691d52242b308facc38f694e3da338f6b18f1a5a3c5d58f1a463c68d8f15363b69d8eda5a3b5d28ed5463b68d8ed43a3b5718e9a563a68d8e5a563968e8e55263868d8dda5a375488b299222a64886cc3826b084a99c4ba20846cc210a6584197a0f5f283d5c20da6583597a0c630816cc6016a1801a81ffa657fc2c1fea657f9971fda657f5975fa6a0dd8bc3752f17b41c1edb30dc17c3705b0dc12c370470dc10c36e6587a6995e965d7a5969e963079accc45a20d98bcc44a2311187c446331117cc445731110c36569cd95a63656b0d91a636369cd8da63636b1781a85df6a0d89ac1dca6476e993606a076a995da65d769875da270d75a835d69c766995d965d765875d9658d6da835b698762995d865d761961d8b30d65a735969a759875d56a0d51a63536b0d44bc1d4a65751981d3a6574d9734f69d749a85d2070d39a734c658d2da634a6a0d29a734a658746995d165cd25a75d06a0d21a734769cd15a73446b073e995cf2706)) else (if i<5 then (if i<4 then 0x99796528b90f681f871e5c33ad1720f2e211a42351654c95c01675a713851d145268ab31565e65c3377fc71499daa3da02cf85c4a270bad37ac912ba239386042348469c9dbccb887f018508d41ae42350186030c0614234a305e65a11a463101850a243d02cf88c62030be397c7259f1442c40387a10e9a1b9c33777205ad4b5ac2d185a30941fa0b93b2e24e39dc73971271cf0c10f14c2d184170a32146425084169aadfd3be0f82189cb20ec40be835cea5cc95ba64786464ae0d741727e1cfc39be83dd374c87a3e0a44148821902f9f07bc9880c30186030968280c2f0ca030a31880c3018518c406180c30186045c03780c300de030c03780c30186030c037802cff8dfd398d77a50fdd1f8718d731ae59f1d87bf417e1cfc38c80990132026405f69190132028c60c80ae647d50faa118c190146306404b3e167c46306404b3e167c77fe59f0b3e29157cd8f8e5f07bdd37b408511eb221447a50f3d56483ccb7168635de4c3c982ca4f261d03ba3a740ef171e2e16b52d6a5ad4b4116b578645ad518c16b52d6a8c60b5abbff77aaee41daa16b5320259f0c80bb0f31aee0b4b3e388a75a6ea5dc453a647342e8e9d03b9cb7276e4ed997b9a1386edfe9c73b7d02c50e5b9c9d967c722259f1bfd38e77114ba5dc16b8b47114e181c16ac903202dfe9be819016f286404b5a96b52cf859f0b3e167c2cf8635cc6b967c2cf859f0b3e167c2cf859f0b3e167c31aed0f5b95b6e659fe59f0b3e167c2cf859f0b3e167c2cf859f1b4c167c2cf859f1b209a006bd4d5e1a6535333f047c1da65167c2cf859f1a1e96b5598659f19b116b52d6a6405a0516b52cf8cd88b5a96b5665e5ad597096b52cf85ad5925b24b6268c4d18feb1a66268c398b5a96b52cf85ad4b3e211a61308469820afcf5ef0bc3d5fa16b52d6a5ad4b3e2ed32cf8b3fd74ba3182d6a8c617322e165c2cb6016c01d2d5a64b3fd661ac904a8093c92792c3957e85b7cb5a96b52d6a59f0b5a96b52cf85ad4b3e16b52cf87a3cb3e19012cf86404b3e167c2cf859f0b3e167c2cf85630b3e167c2cf859f0b3e167c5782adcd08d16b5565c8469597211a4234ab5cb6f96b555128469544a11a4234846952b16df53b6a76d4c6a98d527e59f0b3e167c522a5ad4b5aa8eb2cf8a304b3e28852d6a59f0b5a967c2cf87a3cb3e16df2cf859f0b3e167c2cf859f0b3e167c2cf859f108d211a50805ad4b5a96b52d6a5ad4b5a96b52d6aa01140227ad4ca859f0bfca54049e49dc527920de4a809cb1307a6e74d569950b3e260f4b7095f0bfca54049e4846908d211a4234846925b16df2dbe5b7d08d211a48e2846908d242347aa8f551eaa3d52d6a59f0b3e16b52cf85ad4b3e167c2d6a8e88b3e1e5c2dbe59f0b3e167c2cf859f0b3e167c3d1e7a3cf47a34242ee8c6118c228e4 else 0x22cf8c431f74048187e3e220ae26050c461b9cd166386b859f7dbb3acd19220770c71b7c61560532862a8dc89688bc51be5ce2ca54b1d067e8b9b8766b1c9a36e65269749a4b2491496371b8d46e2e2c8bc5e1d15872a210fd7e10940275021530a145904fb313d564e8ea33b00aec52b0a088a2af27eba45aad3e93301c1146c4a169c04d2d10198388ca4226782a9a87a5e3d5cac9044238234cc412f8d0a0082099852290e0701418044c2893898289187f381065a3296cda5e7232110c6b62b18c82471c4721d0c6fb6db2df62b5d8ad75b1d4ce6d2f874170e6f8c912b63a9c4c62b0f02c071b8643a18d96ba30c8672b030091c8da24be0c60c40be0b80b60b40b20b00ae0ac0aa0a80a60a40a209e09a09809708e08e08c08a08808608208007e07c07a07907607607407207016e06e06c166067265064c64a64864664464264065262262c6006125e05f25c05d25b25825805705485445405405305085045025005004a04804704444404504284244204214004043e03e23c13c13a03a038936536137435235034c34a3483463443423403413203223013012e02e02c02b026c26826426226126027024524025d23b23523323122d22b22a22922522322222122022321d1f91f51f31ed1eb1e71e31eb1c31de1b61b21b01ae1aa1a61a41a21a01a118019d17917517316d16916317e15a15614a15d13b13513313112d12b12912712512312212112013d11b11911511311110f10d10b10710510310110011d0fc0f90f50f30f10f00ed0eb0e90e80e70e50e40e30e10e00fe0dc0da0d80d60d40d20d00ce0cc0c80c60c40c20c00de0bc0ba0b80b60b20b00ae0ac0aa0a80a60a40a20a00be09c09a09809609209008e08a08808608208009f07d07b07707306f06d06b06706506306106007f05d05b05905705305205104f04b04904704604504404304104005f03d03b03302d02702502003f01b01700f00096a8c1908ee81da0543a686e6e444b29443f7996bb4e030c0613cb8af04f2e1e5c2e78f9b1c88c10c82185cf2423ba0770c0e39cd0044ae518312ba0ec46a63202faa240ebea82cf91decc80c7f37ee9211e1e8190131aeaf0547598d7860859f0d0047f32cf859f0b3e46a68fe6e181dff99012cf8a455475c81d903aef55f54167c2cf85c49d3247ae7342faa1f5418d76f291498b5a96b546311654b5a990151d6ef54b3e167c903a5c48b3e42d131ae59f0b3e19012cf859f23bda91531ae635e3f9958c71cee8e9f1cb8e733ace8e9c9db93b8f5d18111d13d6479eb19ce36cb96e802d1dede2e3c5c7276f3d6320443f8e90f0c9c9dc7158e2b1c5638ac7158b2af32dc9dc403887ee5b9cb7417272dd0c12045c6d98d4d1a99fa0c6738c8111c9f543ea87d510521cb71e5c806e8469c88a11a33acb990d5a39cb8c0900dd) else (if i<6 then 0x69135914d46cce8ba39a3f1ebd43dbe61f4756b9147a68d21eda66a959898065a21dcd2a9316ad449f4be792d0b1d4dfc1af96cb3b2524f04ba52c00b60b31001ac44120332076dc1003a4b208dc621d40a3240330a9d4d1516626b033f9903b07518898860f46b11019904a1d8b41d086ac5e845642b846b70b6eb278d4388ae5baeb056aa9afb7a83935c235b9fcc8255d5aaa692c9234600e629d35d8a391487101ba3935a0fd63a4a18402d621b214b602f865ccc90d80698087a3c883609246eef6a3036892d5e1d5839e8e2924a36a60a2a0d8361a1f499b33e2c046f73a48b0e618a81b10b18eed91850011288c3e2cec8c2796a4d492ca190013f89aa0fa78b3696ff10039f37bbbd028c855ea3841249638ea9f9002130001e0c1406543f40800c318a902364196c2a06b05f7fb1e49208db7c9a6552c1208e5ded438018d1588acc531c09dccc1f9b286c520c6254f1b20127a18e19ac17da2ff76b2686c524c6cc2709538697e50c8b917e4f1b8a8a2a9d918028419a81f4322fa721d4236e52d25a724b1c89c388231ce5a224e24686f721d32487bec4743758ec6108441178ec41a8cdbc5a6fb486224c45b127abcd8a3d1eb5056acba2e357102444598e1b05bec109a39ba00ca4a568622104c23065cba843910bec7c03edd6c51c36441997efd4218c6ce20901b0396adfa2e49128ac75cc9b010a1d16416c31db51279b7d7a4d1efd13863148e35303154b043ad431fec20866d2c1d0ea310440cd59a2c9870d456613880151cccc713bd99b565db06374220894a64b699f268dccc82a051733a5b0a85579c2a15649bf441332b15691a800b42146e62681b352f4a6f9028b989a074a930c28a50ec923a6d49a18c526af51b308d38fc6349e49402ae27fb0822aca8074226746286a18190b84229106a009d0881220669724c00c44a5341faec63c718a45a65ac724bf24d1c62910320ce576c97eb0649342482ad449a9f8c1be44e190b1c16b246a0aa7511a1049974be47e390a3488988193e95278e0e022200484331404226fb5da6280830328accc50eda0f43bbfafb0a3a8704af3fd9d587c8bb66ca506ece5a6b30af13ac1e14951a36a60ac206c347f8cb5985236dcf8e662f16a602710062001ec5dbe7530553b2a8dc89688bc51bedb9f594cb458822228704008bdfe7164ad93372030872d58b8c1ba2b8173141c0d378bb91be205d3f2d6c95852259cb5237237efebec2929b3cae0ea2328f51562894d390d0f5786919c7a40d0851d8b8a28009f4b8781406282944c4278c89ce612e33c8b95844c4f1062e84cc06b8abecf3eb256c642e092b3fa756c6459c68a4018855843922e071a28be20e418866027000722860625a9108021a89c0259140444008004011046410158a009c4a2e16086055aa8ec26050c461bcc5 else 0x283218cd458165529944984299449a4810a625641a9491b6f8e9b02b9d24e616e4b73b1a1ae2d89a91f77af853eab04613522d8614540da12348b692d2a22f3814516f54aa0f0290830a692c6a7431847eb906c696c31107e9e361a8530858d9765b030638132411e870a541fae8d20e6a9587211848025110a26b788548785b0c6f361a1be6714a5021f9a41b6c18e0fa7e3198a29b5f2f03408f990c7df76c16e6703eb121ceb1940cd11b2a4c29c0f8e6861d450d89c8222bdc3a0e395046ca8641cac31104e33209ec791b1c2c251ec6dae29c2de6d348854638825cbf2b0c613ecb25c210cc2251101872311082610b0c237126f90282956950b6146b0063bf041a9861940119aaca00654293858ab61466217e4965cdf18507f1116ae82abce03211c385139fc9f2e870a286504a4f26728c2611cb23623f257266cb14703148a07d6331450d8525cd7103644138608222184e142e8b81c286c646c35c556c306ca242579fc3032bc9eae5437c5ac1bcd90e10a651b09f4f029c1e24f30aa16c31cab5245b0844314a24ec514885e745f042a0f4d6b9923cd6c3910a2411f850d23198e032263f62b131c321408b0d6c0c1884e1650f476e418a6411d23e36293d91763a884f7fb89b2561488422ec6a2eb618a6df6bce0414098f9173a8aa8752d94a6714be5d2d96043d4cdaed212b0ff1e411b2286cef3269086538188d420607e3c1da3852917cba122d0a5230102f2214914128f475c635b6a5843201e572a90b89b6b32d60809faccea38ad8eb020901b839b5c8a2c45b6bf661181934fc7331893e9a9f96b9447af53a)))
def orI10 (i : Nat) : Nat := 0x1e13a414701320346196424500860af615b023f04c54c2a8d3425d007b04be99141e204410d00000000000030b78107c17f82c00004190000301b0000000300a986780ba0002c3100000000000000038040000e179826b84f300780700000039702888d9828c0420000c038000601e901a0000000000040ab018141af027f0052004000685a00000000c10c82ba0b12046804e812c0bf216400058409075209b02a2845905d001440b1822f05a00c5410103e000000dac05302ad0202143c34c83794c0e8dc80e9a5f0001210c81a6053c032000380c000094bda0a600bd046f07f214b11c6832d03fa03181ef00fe0cca170000203854c460ce425684910c60000000503b404740c2c30c00be0d5a093c003806341c4060210c84000660001010050a00085043848602000180144480
def orD11 (i : Nat) : Nat := (if i<5 then (if i<2 then (if i<1 then 0x78356f062de0d1bc1d76546a0a8d3951a62a3265369ca6d314d932934c52694a4c987e994fb509f6603f4427d970fcee9f6993ecb07e664fb4b1f5d43f2ac7d934f9369f1ed3e0587ebb4f3301ea213ccb07a664f32a1e9563cc1479524eb509d6603b44275a64eb2c1d9993ad2a75950ecaa9c6603944271970e4ee9c6583933271950e4ab1c54936d406e884db4e1b9dd36d306e664db4a1b954a2d41459828b4e51698a2c9945a128b565166ca0cb941a6283265066c9ed393da627b2c4f64c9ed593d9b2734e4e6989cd293995273264e5489cd0939ab273369a6a03544269a70d4ee9a69934cb06a664d34a1a95634b8c695b4cb50996603344265a74cb2e199dd32d3265960cccc9969532ca866558caa44d69c9ad31359326b36986a03144261a60c4cc9869530caa61750c4ab1854930d0a61714c2421884498d3931a6263264b69c96d312d9325b36976602f4425d960bccc976952eca85e558baa5176022eb045d50c133182a2304c3e0996c130d825db04cae0985c12eb82597052ae0982c12c58254b04c0e0971c12c38254704c5e097bc12d78256f048da59a80b5109669c2d3ba59a64b32c169992cd285a558b2a5165462cbda55a84ab3015a212ad3255960accc956952aca856558aaa414aef02c5e048bc0ad78146f035d929a989b17135ae268d84a994933612aec92d4925a824b56916a122d5846bb243524866090d591da923b50476608e4da41a9085329026c1f4ca3d9807d100faec8cd4919a6233568e6a01d442381b07576456a48ad3115ab22b368d6a41b4ca35a846b300da20194ca3198065108c65819332319b462160caec88d4911a1223568b6a0174422da605ccc8b6ac175d90da921b304368486d590d9b21936426a484cb109ab213368a6a4154ca29a8453300aa2114d322996054cc09a6512cc0268844b2c0999912c882611c053380663004c60288c032d8061b00c8e0181c02c38062f00b5e011b20b52416a082d1105a020b564166c80d4901a6203444068080d58fda91fb443f6847ed00fdab4435208a6510d4022884434c886581133221a24435608aed0ed481e9943b50876600f4421da643b2c079990ed101e2243b42876450e9081e111f35606aec74cc0dd981b330346605ecc0b9ab02d32856600b442142b02d7604a6508cc012884232e049dd084d812bb1334e2569c46d388da611356225ac449d885a710b4c03a20073b80e6601caa03aec3ed387da60fb4a1e69c3ad3875a60eb261c64c388586da70db4c1a69c34d3069a10cb4e1969832c9861a60c32602a64054420997014ee0299904d280a55812a40288904d0a09210142202aec2cd3859a60ab4e156982ac9806bb09b56116a022d5841a906b520c26c16d082dab0535200a6500cc00288004cc00844015d821a204342086ac0ed481da2 else 0x99b0cb361a56c32ad86acb15db5da8abb0ed7699aecb55d8b2b532d66a1accc35997ab32d5661aacbb359a56b32b56615accdb589bab317565ecad5d956996ab50d5699aacb351a569b50d3695a6b2b49a86934b9fa233ec3e7d86cfaed9f6173eb2e7c8bce5119c61f38c367176ce30b9c5d738b2e7255cdd119b61f36c366d76cdb0b9b5d736b2e6e5568b50d1695a2cad4552683515061da0d2b3da867b4ace6a19ccc339a56732b4e54b354466987cd30d9a5db34c2e6975cd2cb9a9559ad4335a666b2ccd6959acab3585a6aa44daef314466186cc30b9859598d4331986634acc65598b2d3152a63014c62d96d432d9865b4ccb65996d2d2d52a5b00cb66e96c5d2d6b25d7796a232cc3e5986cb2ed966172cbae5965cb4ab92a6724cde496bc92379242d92d45211b63b5247a658cd4315a922d338ca2318c3311a8621318ba2316c362c8b61b5243a6586d430d86618d643aed84d450981a131789a2312c36258160b50c168980d4301a25fb50bf68b104c62288c430c3daef0ca5e193bc30778646f0d5daeda734b306966d74d3ae9971d4ee39a6572cb8e6775cb28399127295ce50b1cd766866170d38e2775c34a3891170d1ae04b1c57667660cecb99d9b333306668cccd59999b32b306566cc8cc191a33232637a666ecc2dda75bb2e379dd6ed2add951bcaab76506f222dc9b5b816b66506d222d9931b466b56906b222d5a31ac6663660c6ca18d9b313306268cc4c9989a1313566266d68d22d1941a488b468d68c98d23359b4ab3654672aacd9319c6633aed64d2ac995592ea3295564d22c97419488b268d64b98ca3399284b268564b88ca1130b3061600c0cc181803033631a6662cc2c5a718ceeb1694632aac59418c88b168e62a9cc54318c66b160a62a94c54258b42b14c46308cc57b58896b10ac635dac1a7184eeb0694612aac1a418488b068c6119cc152982853054660a0cc17b98276af6955eca8be5557b46af64c5f19cbd5216d332d4ae5a858b6bb563502caecbcd41799815d32ab26d54cc0aa88c2b3185a2152d40a6882eb36a86a150cc0a28813d32a76604f4429d9713cef274ae4e8589ebbc233184a2308c3e118bc2117845ef08ade105bc22578446f0885e12bb2e34e5c6994cd409a885334e269dd4c0d89abb2db4e5b698b6d596d9b2d34c5a66c4b4ca95a852b3025a214ad3a959712cee24a6548cc092885232e249dd48cb09266922572442c495d965a72cb4ca36a0474408e7751b4c2399946d2a8c7b11d762299a44b5961a82c34e58698b0d2961ab2c33657698aecd959a72b34c56658acd59599b2ab4c55694aaca8869950b50a166043442859710ceea169942cb0866650936a10ad40cc082885032c2099940ca882551057783a2306c3e0d86c1aed8361706bae0d65c1cab8362f0645e0d7bc1ad) else (if i<3 then 0xdfc2e62ee5e6ddf2a352e3dac312e4c2bb02e3da792ae2f2e20abb02e0d2db96dfc2d746dedad92ebb02d92eddf2dc7edb96c612c5cac85edb128a66897ec2b6c612c5cada02d92e834ac1ea9e26d8d2d806a6f2c2b686a2a6f2d862d8069e26cc9ecefed7469e26cd56d6c2c6d2d5dad56ad34ad432d29ec6d2d432d34ad29ed1dec6d2d0cecfe6bb02cefece52bb02cd569e26c1eaccfac1eacb2eccfac1eacc9ecc2ecb8acc2ecbe6bb02bb02cb8abb02bb02cb2ebb02bb02bb02ca76cae6bb02ca769e26bb02bb02bb02ca2eca2eca2eca2eca2ec96ec5cac85ec7da8a66c742c6d2c612c5cac4bac40ec312834a842ac1a2c2b686a2842ac232c1eac1a2849abf9698fac07e98fa9a52bf96bb22be72b3fabe72b02aadcebdc6aaeeaa2ebcdebbe2a696a59abb22bb02ba569156b9e6b962949a9ede850ab906b18ab7a6b736abaeaaeeb2feb64ea84ab606b50ab3fa972ab2fe92169f269ede850a842a850a9e26b18ab02a8c4aaeca87deadcead22abaeaaeeaa2ea9bea84aa6f2a73aa6f2a696a59aa132a022a476a352a26aa26aa132a02292169f269ede9e6e842a850a9e2686fe86a29e269d029d029b969c1a9b969c1a9b96997e983a9ad69ad69a529ad69a52997e997e983a98fa983a972a967e90468e4e9596949a93768d02904693769216915690468f728e4e8d028c928c4a8b4e89368a66897e8936884e5c1e87de87de876e842a876e842a86fe86a2842a861e85ae8552850a849a842a818e83a6834a834a82ee6cd66532818e7ae6807e7ffa7efe7bf67db27db27a3a7cde7bf67ae67a3a792a78a677aa77aa636276fe763e6db66d3275f66b3675f675f668ea74e674e673ea73167242667671d2717670b66ff66f366e4e67366e4e6db66d326cd66c166bce6a7668666b366b36686669f2686669826a7669f2698268ea686667e26736667665de6532644a636262de609e625a625a61865cca609e5b9a5f1e5fca5e725e725f1e5e725dc65cca5c1e5b9a5b17be95772ba6e57bdcab7b946dd0d2ba195dc2e8e7695cecab9d9473ae8e768ccf5d99a9973328e668eccb9b99abb333666aedcad3b959772b4ae5656cabdd955b7234ee465dc8d2b9195db2e9b65cf6ca9ed943db467b55d36ab9ed553daa87b58cdc6d2b8d9571b46e364dc4d2b899571347b255364a9ec943d9466e1695c2d1b859330d76e0695c0cad8153b02a16056f62caec575d8cabb15d362aa6c552d8ae3b154762a0ec175d84abb05d360aa6c173d82a7b050f6119eb57bd6ad7ad56f5a8deb50b6fb505ea6755446a6886eb505daef4ec3b71a8d330e5ba65b6d3b6d976d350da662b4c3d698bd2331a4a2348c3e9196d230da45db48c5e908bd22f7a45af4895e911bd2217a4aedb2d4365a5d1d11a361f46c368d76d191658a65b0d4361976c30ed86 else (if i<4 then 0x68e7687717d682ef4dab59d7471359d68937680744e3641afac7662b4ff75e6f6747390766d7548756e7662b65a762ff628f6523648b641b4a934a9346a3537f52d338636383638362ff62ff62ff628f620b61876103607f43db4c7b600f5f775ef35deb51de9b9751df516f5e6f5deb5d7b5bc75b075cf75c735bc75b075a6f58e359d7471359d74277596758e3460b583757c754175757548756e75627558f550b54875417537f52d3524f479751df51df51df38bf51df51df516f5113508f4ff74f734e42cae74edb4e434daac6d2c6d2c6d33a934d274c7b4bf7173f4b9b4b174a934a23487749b3494348d348d30c7af10f4877487747f34796b60747130ea738bf46a33f5f460b4552ccfb45af45af455344e343574207445f43db261ab963435742e742774207416f416eb90740ff40533fe33f5f3edb3d3b3e433dbf3d3b3ca33c333b9b3b2b39fb3a9339fb39773977390738beb73683a6bb028c4abb029e268c4b362ebb03327ad8d29edebb03133b0a6f38632f9a85af375306731846c1a3362eca2ee7528c4b35831fff3422bb03338b327abb03317efeaf29aabb032c42bb02876e850a9edebb02d8d29edebb02d862c1eabb029edebb033122b9072f9ac5caef7ac5cb2e4e8c4b2e4e8c4abb032d672c42bb032abb1b9f2abadc7f29ab294e9edebb02d862850abb02861ecb8a86fe8c4a86ff28cad34ad433280a850b1e2f280a850ad5db268a850b274ad34b268a850abb02cc2eca77261b255a8c4acc2f1f52ca2f210eca2f221eca2f249b239f22deca2ee5e71caf221f210f19a6ca2f1ab71ffee5e68c4b1f5289368b4e89371e2e8936c96e8936c4bb1dbf1caf1b9f1ab719a6d862c1eabb02d862850abb02f1ef0be307bf06731847145f0ceb17d6c1ea86a3173f162ed56b156ec07f145f041efdc6834b041ecae7133ab7a6db130902db1307beb64f0513126712670f170fff10ab11cf0fff11cf10ab0fff0fff0f16d0cf0dfaeacab606e9bb0ea6b50b0226dfc30dfabcdf0ceacfe6fb4b0c7b09fee862cae6d8d2fac6e8630be2eceb08a70a6f09ff090308a707bf067305126ff7048eeacb041e849ae8bec6d30386f32b022701a300bb000edfc2d747000efeaefdc6ce52fcf2dfc2e2f2fc6ee0d2fb4ace52c232fac686a2834ac1ea9e26d806a6f2c2b686a2a6f2f536f0b2bb02bb02c1a2bb02e5e6bb02fa56bb02bb02bb02bb02bb02bb02bb02bb028c4af2e28c4a75f6f9e6bb028c4af9e67242cefee62e9e26cefee4c2bb02e62e7242f192f0b2f74ef8aec5caf8aedb12f74ef6b6c2b6f5bada02f536cb2ef412f32abb02f0b2f2e2c1a2c1a2c1a2cbe6cbe68552f25e834af1eef192c2b686a2f192c232f10ef0b2ef7ac5caee6a7176ee6aedfaeceac5caebc6eaca8936e9ba849ae8bee862e7528936dedae20a else 0xc02239bb18daa595914d988605745c54d281403fd3e64d3246512324c82f0b7060a34e4a00f0974d04b1143c110340ac2913828068185c40c114032e56d4ed660a14d081274751b424ff41cff3f8ed518c1239932245417c541604d280472d8380e0300f82d5f57219d6c1c966595541d9324d92b4d4ed4e0c01d85b5a051550481b83407c115298209175175693ecc82585f1844b4ac3554831150245253040cff3fccd0ac0f4a9630fd59175584b14f1952e46d1a4690f4410f334cb3b8b61d85152c32058081bd4c334be57c0d18d5c334c80743c0901610d450ad441113d505305615b2715e231554cd47058c60f03b49c8418c571544a0fc370a41b1a05b1bc4615c28050064ed290dc2f4b4220a01a4b13a1d12e2bca12706810439318af230744e835088140680c119371083a19c5a0b9284a9274f12f1d04e0ec330740f334b51103c0b812148471183e3f8cd0f03412c26228721143d32cc81c84b0f8360b01e3fcfe1c861184561442c098180103e0600a1644e14c4807810040450b8201584b0801204804fca18c310610c017c2f05d0b61682c8580ae1582a8540a61482885009e1382684c0961282484808e118228440861082084007e0f81e83c0760e81c83826e2dc1b93616c2d41a1331660ce192322640c8988318608c098030a5e4bc1792e05c4b41692c0580ac150298508a09402884e49c1392604a09011c2244408a108211400800f91e13d0750e89d03b0710e09c03906d0d89ba350698d21a23406a0ca191320648c09882e25e0b21622c0588a81522805209a1322624c09a9212404b48d91922e4588a9132244448811b20e40c8090d1f63e47b8f51e63c47b8e31c23b86d0d81ac350690d01b6328638c3184304600cd1762e45b8b51662c45f0aa14c290510a015c2744d89a1322604b89612a250498921222404e88b1122204388510820c4088011a1f03d8790f01dc3a8740e61c43807e0d81a8340660c81883006e0b81682c0560a81482805e098128240460881082004f07c0f41d83a0720dc1b0350680cc190310600fc1702d0560a81482704c094120230440841002f03c0740d81a03205c0b01502804c0901102007c0580700a00c0024f7d377cc76ebb294f294ec23371ab748756277c577c5776d3739377437bfb78e37b8a9e6f6956f1ef08a77b1b75b7763b75b77a837a8379ff445f797b78e3785f5c72edfb785f77c7708f7743742b76d37323763b75b7751f748766d7742b7393729f7323708f729f51134a234d2747f3722f4bf728cac7db71ab3122b9e7701f711371134edb708f65236f86d807701ed8076f876cf29edefa566cd76f2af2e345af6f2b6ebaf2e367476e0f4dab583762ff6d776cf36c8368076bd75967558f648b4b1762fef25f6b536a4b49436acf6a4b687769c76957687768e76877))) else (if i<8 then (if i<6 then 0x1383fa83143692070a4046065f51903a40e25c27d0fc96a5747483c73e8085d9550c98ea576383c4e1d08d8fe280949a730d93d4e0382eda539d43580babc5a979cf301b869470baae16a5e894fe18036d5b43f8449d3f2342b9d8444e11c80098813841c35184d0a00287d0711c70103451802854307e68311c90e8703f8d43344719460e8303fa831546358ac136133fa7e1d463584d91cd434466a446509cfa02aa1a3a95d6b4e0a33e6364f88521379d46e6c9946e0a380095aa726c84b300a3800700d9025d897e4f4334a921bfa20ac009ba8ba26282010de082dbf56801688001210e4f8a0806c52dbf568bf46dd850060101d00ec7170131981575e759d0650ca027616b14a6fc9b19c3c56912425b680437820b6053f59c3326463449a73214028040d288681c784c30500801288681c7008d43460d2260568ab1069a3f4a99488606570715a0e17aa6a988bdf650159318197dab104af5e9059888012724f6c72a437180400ec67a8a90bc64d2a4942810925487a4564243602086fa03469fd111dd26dd2771c75d9c1819be4e5bd2c5bd4b5ba32db922dae5a9a40b58f2858c4b58b51d8770d7e65d7e66d6d25d666a54c49d4c6154a4d147159473f9434e5401153da3d39649365a1364a52f0b9274851c4751a6a11581109441094390941d064250341503440ff404ff410fe518f04b8f0158ef86cee410ed73ce93f8e44d4db374db138da3b8d81c4d8020d8400d759cd6360d3400d0438cd3b4cd344cd17cbf4bcb73a4b72d8ad344a92d4a76cca4150a113c9a2848f5a88d638832e88300c832e4825206f00c6e12854104541684f0f04e0084b150490a0493184830c482fc481244803c4413843714410c8413203f5b03c5203c1183c00c3c10c3b5343a1883a6ac392c038170375743600c34640337b8302f82f2942f5a02c4cc26548221141d0481d704144b4142bc140ac0359002068020300284a0a76e09229d665dd43bdcb5ddc05e5b9075a45a98e1518d739870b9637094b4751c4711b2bd1a471184650f400fe3f8fc224ee090ee3f0d23ecd136cd040cc8158c4628bf5c0be5ccb53b8af4e4a9650a32fca1100a160ca0184960ac832e0817c8602885e3185d0e8541944e1c4492b4480904817047204421983c0083a58439294371143455833108320fc2f1340209de1095e008ddf085de41dbc769ac6858d4717b00976181611714041d3e335394711a4590f4510f43d0e420fe41cfe3f4fb36ccd334c9184c012cb731cb0568a30e8a3334a00a0815e07f284482d44711444104405243e4b03d0d83c0ac3c1383310431100300741b0640b05c090540704c05069b759da01019d1d19b6718f425841b96b4a561319540414f0f1455294422929058f94e0ef664b7184b7284942dc801144e174480d04310c330a0260300a1 else (if i<7 then 0x1b44d0f610d28febc48200f1675c96d80e0b7cc5e0e21c5e9d834a3f2f940443c5417d0a40d5b41a1882702cfa964144418434abd45495303c59e5b82df32fe9ba62ba500c5265f59c42329018bcc820697656f071dc008c62c954631135e9018be3f2c4a060126683c969511764b3ed390dc97a41d56a6843d03a60fc33499815aad90f32055bc2a0700e4ec56ad0963e8c717a4aa6d354e4be6f4374a140a80e069ab790153e4af44cfeaf0373445831310de99695162c4ace482a0a687438825134429b4d6a932b707466568ce584fa3de6a5edd88bcc90dce522b719e14569613e8a15a69f4faba2d60d39a3145c0590f728a443e51969ea92c7d6696b7ca0282abb425f83c6ba28077960133da3145c019d641e9f30e0f946d097e0a035c37516f06c3b259f38743808c07af4c97861180300cb712a303f8514210068352190232b10086252e0b0c21c6e98b5003f38046408cac41a96e0b9298b500372c34139c412d203fc6b00998e4304b6343fcd132095256771dc20eab51834b007b8e430aed1069e2e988a7a5dc26639ad4b119494fec08e52d3ecd4320be241226d6c75df29152d3ee2628093170133412766c61791143d8494c8049d91b8660d2432856962cbe580bace558544162a444657a429a732140319a1b942071d180952094091ae4b62c2f04ce1a59c0441d1ba140715a584967557f0190f5c0a060110109b669d7b1d2d464c896095259a1b93d7444a7a92d4450332ca9948d52469adc1db1838a68d27d95929d9668665088a599611046b0c151176b5564e520697646e4f48a185d6058157558c8b0b12820d403c6acaf32037164642cf40db56acb7104fa89d1040cfd35d70844c0493d069ab28de42bd7c334a7844b70d880f25d774fa0e2a13fcfd320b6ce6d49435243c855992adea2bcfd320a5564b00c02418a9294500c3312a673345958650ccb328c56b4437c44a1256100cd308a90bc6141e5008411c4500c325e65312499184a0dad0cc0209830145000c33060c0149a1940242cf417069c8977d50211e6150944d446fc976d0307251f4590d4250841d02aa8a027601b1516a574a58ea2e49958a5c0911b425357b0dabe962f4b918c0219a91bd3751a0e1fcbb429a535d431f8c49a3a5d01d519ae80dd0319224757c4590981d9f41275d146ae61f0e8168ddf9280aabc2b690a422c280088141ced2d4b6fc2ba58ea2e6c42596e3e4a1a72aa11cd0baae8f8a418c02438a021275d09b1f5d25ae916e21746d7b4d4b536ae26c1d00dcf6e066fc8d52a614e2805b9a841d952d59f323a5d2426891a439a57c08118454e1a2439a5374cd2a495194d84c39cd372345a0d1382eda841d9539cdc50cd9cd370d138482a041d044d4dd50c3f31284dc443307f1c048696282a4a521379d5b26507f654db8a03f2a7511 else 0x80c050ac4410c18100310c28108413b46011c4104ed11e726a065714d0e0c62b5c94929e7e8d04e6163de7af8810e14e4717c441f9389392d4a036483d90f388cd15e7819c2a4c38870536a1164569ea9c4735e71d21a5c9450c8536a11041135370cb2d4e16a618ed8a2bc530511a426a711c3731287483c7bd99905870924a8e0fe2d43734126383c06a3b740af14d7ca9d9f0dcc6b41b00931119a6d63b152278611945d167ea2d4e65836a34de775ae253e4f2319918110a4d4f85cce074287a839e18e39a765adb4300a325a4c4757b6f03f3a40798290ee055e0f97f91669dec2e3d5ad380e4961ea4c8dd3e280372e4019d641e8383e51c4597a424a02d6a26c5a5bd381e9d51e17f01a37a5cdb7c1803d284c2c15adcf301b82ec485ee9d655433660650af17453a7e977e28e5cc372d4852834650b70e26aa7e327d8372d489bdb56d0c4300a12798c7f91843d048ce2d8fcb583529016f06cf00ee052d9fe3fcdb67cb0743406ca471026183e5dde80d443718893959e4757b7e54336400f25d1059d7f97a4119536ca00dc672c4110034a4c4300fe15ad0f02873448f5d7894c664604a76072f89882ca93d1c41d4318120ae7606897b2a4f7f907a25432c456c67471018149c1d868145566c4b90cc56104898c0308e0b53e200e897b29528c4228e23235cb52d7783d4b0e489b211a50c85dd2c6c4330e9520c11c2d4904930b046e509386e0241fc484693550cd9e27775db4258907054e41df00bcb6a537b05d7651b81fc48425958a0b9e27775e257b522b0e0721327a2558544125a050e11b4599511cc6c03a2fcc812560ce630c04110425c0c22f856c0ed5c030cd5752cc810340a1ff0bc41155f0c0303c340a042120599a4610836d5ce104af8ccfd35d7084494a13d7bd99905e41fcaf474ed9f47e0dcd11542008420984919974add377438a85101c45798b99b418153d739e489e977e1ff9f61126a8974020c9c1d8684c92c74e94104ee0c125a81103577658333bcee6757b8c885dc1e621d357081099ee10038468b53003722476dc403c031585414ccd19ad794280c0f7943a0d8559cf02f4b9265be5d8bb4b519429792a4e7a5672b1c284eb66ea2e898470dcb082b30e83917e1d9112346e34761f87d94039d9199dc00a245a5736008614670755a259542516943539600b5254c0f02a0700e4ec56ad22a762a9309b668035ae5aaed0f62c472684058556a2a5a63432ca9600800c447345e2f8500c4e128a22545d18041444b1284935675c9ac5700c0e82702c96058153e61c46d13af110f0b42926d2bc55a89b0744e1b55a6618c40d70580b9f20c7d03505c36209b7883a0e4c728aa13fdb631c3751e291c18058e3385f3876446eabd3541670118508a4d1d6258957564b888c0816f542b1008625da0b9641548d)) else (if i<9 then 0xd4b5157ed0c40cd05ccc010440a267103c2697d57dac15c4c6a86d0ea19360383d406461023f8cb4e6f9840c1b6b0364b71b1e41268a460fe341390dd0a98450d564130d81ac3847117274ba994f03e6e0343b1c66c5b8d867aa245c5c394813db5184c40e0ad726357f1088ccfd3f0fb341f62f8374e515f83ca54da0ee3c3619e471088b45c3403714d05cc4840330c11542c5c199283c0c108560288921ac825920783d6c4339911e8d502259283d4b12c39b211835d43249b999cc320be16517a2552066c63438121fa244425ec954a199a1003502f25530b20fa50ee0c11e455147ee895ccca953a0cdc51c5217f10235c9a953a79664864d81011e46091103a25ec9548ee86124451004d4d18a4d4a93fa954f795c51c4df4912146514420d509efac24154a18a883721e603097aacb793d18408d7320b52946a0dcea99d3991183f8554d3255a8d0ce941068c76d18455fc8c8d649c074c0c27c0aa1c388d50f7e8d7340d649569b9457bc265e04047918a24b5a19674c3a12c392d9e38d5fc8ccd72f8d614679e874868c5008f58909e63119436282a61660119246117c5d334501045128160c0a117474a220555723c2745b45797024176387b0d4a130518b958a5c85d3550c91696c20c3c8ee2a0891c43509698c811cd9349a768da6b2c41241646919801b685813396a519ae5d896740c67b50e81caae2b9206bfb0e9c8887ae1ae20576259d0754941217c438ff35df03ab86b86dafe3743a0028085aa3e292b987ebf46d7b4269c888b9f0024f0b72bc58f56b6d0969310e41e2222b27880225a3c679a84597a429a75e59f35ad1101b10a71143681ac46853e4e6011c9a1d17d06c0d3696d6f8810e9a21268c0891c41cd0321200c5900a212245936be87e1b058ee5397c459a636db630590085da1446149b52a3e20598630fd5e4be564bab67a868c53046d0c849ad9033eceb8a4b52a560418526c5a8f8027558c5f1fd4128e7fcb52805260013463d0f138059ed81c6116490a4b900856683c4d2b4224db11c7ac9e23c002814ec38ce137d9e4757c5e9a736d7067d1840f02ba0c060161812909af2260576d1aa75a53359f2ead4e0b79a9fb7628e5cc8ab44f25db42849e7242256dfb425044022d7fcb56011ac9b13c23c5e03846d1069cdb7b0b5dd7e6c48917d756791b441ec2a4219cf0a4ec37c069082b0755f3c05f618085e038a64db2d59f39ad06c282dc243b460f06135e7e11c51d028030d79f8565de80d4f010c280e826688eea8110434ff2d4f0483e1683406aac0e43114d7c4390d41184371792d515dcf010c1aa4d1da647525370d2ac0e43168915410ff3ac3f3004841c4128533b467a5327a1c41b43a0c831688ec0c11b4399539280f9775f85a10dc62252546e992c74628cb0c590c8543fced5e4600c43090 else (if i<10 then 0x40f9ac08101081844184d89fd1e465141c2b111cd218b635c6508424cc490e0550861360ad43cfe35c755d4b4257310288385f3422915b19d04318c242ec5d3348788a40a1652857c50c70f0427358a2d8141a7c7d16e2d91a149b719cb104247311d2d48164631505d456851859265cc481164386164910a2319e543186315269454dd35c610a3143904a1856c20e151047fc515048410dd7dc57284a2591f60c5114656c04a17d083fced36c91162b9a50f60c5235dd594c32848846ccd21ca2e5f1224b64746112212c8a143ccd19ca2e4902d8c6458ff1dca2dc545e1071451114280e84a9eca01c452d8b27b4ff50c6116959c41660c5168447d68214ccd185ab081614d1a33467ae957c4540591a1834159163fcf45e460d44305a233b450ac347d4bf3fccb0fc70adb20c45436c3f19c812c544b6927dc672189150ec45684196418c381753e156424679440e22d465904230cbb5e943196422c282211d4429050c8590992c9cc0511a440e23349590571083814d034f87115f4240242d8af3f87729f4258892d851158917dd02bd35182b5bc5f17422424cd0dc85bc563d9fd4f855bc4e98d7a3345114cf6899e2d45110568c4bb0891d43ce450c92487d886791e10f2d471f4562847846cfe188d7d4bf2210f50c6939b00e17a3fc55bc5414c14411f70dc7144455bdb0058383b4db20519b8329c104a1067204b3ba362d4572129411a533456c8416842f12c2259652845d42c67ac4e7c58a0590e3fc7110564591542d7018330a27078d15450ff1deb0a05f1010b3fc3f1c450acb96245f425071e4e1100c151654206074569ed203fce2380cd2045510449ac1642060744178d20124e1089017d652d461143a2585488d161844624c02fcc816c2058a146cde15eb165f19ed8315b29c1e3a482f15eb152233fc41145437c4037a621aa810d893e44115e612c962bcff19b37d2302851d15b3109293bc540e0fe1c1a31d095cc483a8261229104ba09c9424cd161a128490905e69865be21890143fd70185196c387250f4046262597311a41851144b2fdbc320519c4e12c5d8d051358928895178af42475bcf64658b0dc50744e128f71790f424fe216f3dd092f83714506cc4b058b08d86144500f0f343d09187c300c72847846d121c50058c71e4c646c6140f7288f67b5091a6518c620c05d464d11e6526030730c816650683a0c1198b8c81db217c5e8b253141d071f562a240522c1c1d0d01c10a238982f1d3d12cc01022c94860f04b30dfb36c5aa0436243728c10096511859e865314811249e5a4fd350cb2f959366f5106e0f1efac24161c2486006a8902170e1696c6d6c961e199a0d022515fa8d00a3c360d52d8aa0e12143d0c420d05e45c45685fa8d15c497b8b51d925f98213829034da9b175a319e3405c3585168977345 else 0x191331510d430513887a2c9e2145194b98c0e82d851946045a8510611252da18cd14757189e1c12114d82d9e32785d450cd1c4f0d1c685d07334613c348ac549a4cd18656c0493611e421021d6421c73278851c065904c0c8383d8483347734e82d8302ec5d186136471a2a7f14758acc32787045ccd1c65368281c6872d8612e8b2fc9e0190f33471946121808a1e7f43c719428185fa102b50a6708a86334371c2b624495e0fe142b624245e10735c699a2b30cc80bc511))))
def orI11 (i : Nat) : Nat := (if i<2 then (if i<1 then 0xa70232548259033d0d004085309d40000000010238802f8031ad0be3419500001920b00000c32b000000000109ccc39790d780000000035369003a0c064d0cb6c15370cc80000302ae103e308b0c05894790817350134938df0c8202aa504020358103d3c375a00a7c1930000253af947740000e480000000000051f7a0dec00007090483a3e07d9c15f30213823700000000000000000090529c1c140338436c80581c10900003100dd0b5ec0a720a8ec27b20da840049044101702043502c970932026b50ca79024905ef00389069e821010230000050b7b900a00002003cb4e04414c2064400681008101e410c0b02594015a8200d09ea938c60950c24ba47e18039b0a70415aa074a4348a0291c2c1f00c5439fe4e60407cc002400009041a02e4804b90366d0c60c197409e5010c00002836350c1d01d130ac80000f4dc9825dc058a02fb201b5c2dd00003004aa03bb435040d4c00000000342225092ac370801e80000a347e021ea0bd4038fd04be830cf4dfa419ee0002812de07d003493087f0093a07f400002027c82d0f0d8a83ba603db936c70d0701cb10e165014c089802cc00002406be40f000af5008981ca9033f0392347a903b0f005701924403ec2c5e4dcfd202a481f8292240e00308005bf81b7b4042839d30ec782f1b0d1940caa03cc823e000038042f07bb1039e0300829690246c2195083880e100003c3166028e4150b4de6c2e3b055b82dc00579c2083081a40fac020f438740c49018e7015180465007f00490000300e210caa433f502b80283807e21366f09100000e063ed353f0a3cc01740021c31f806f9c3aa00cdf02421020901af3024a40d990576021ac0ab2c14e9037b4168b023fd35f00000417850bf082af10228000000003c25020afa138390a3bc063a06c98287b089642b9103ddc007001c40000e02b64061709b0000020a62c37d1009ac10e10b68000000ab711e570046c300408f7c1a9102fc936320db5002c60270c17fa4ecbc0d7e068200fe1048741c0c008f40aad042e031e3057241d90e750cd2230508030e070002090b010d000f3e394951010b06771107b454020101042f0216151fa3000109290100050000682a170a3000000004120318021c00150108501500060a190c01150e24021d02180b020e03004208007008191605358e002b04470238740e0b31043e030e06100a0b621402002100010402021a1d06020b0007030003000108000c0f060b0b03340506bb130700010f013108530306040318000900030003080216000b010e070a0006083618050b011101125213010001070303020b00014501090e000d0c00031a040a061f270e0601180c13011903010f030b160d1402013c2014130b00022301110002060602041d01190c00080525030900080002080f0000010012000f08 else 0x808046c0000000000000a06d00000000000000c40540000c097f01e090e0b038e402f00000f03bd139ae0a200000c034a0175540f40000b001800009059682c60000140d5e4044000000003407d301df430fe05f14347d0bfdc352f40ec834a50cf351df30041c12b00000000000001c1ea00001405b1030c032650d944297a0b5503b620e0cc32e308d4c22f0000001712026400000000182ab9046202582073400000405dc06ef0aef437930bf9c1034033240217019a8172005f40000f041c0000047a1920c902f602f23407000000000041a40000001294005bc143000008371102954076b0bb3401b60bba42e7d022000005078a800e00000c19c20d7d0134303680000e08c200d13079841b1d0ec9828570ac08239c09190027a07178122909c5c377000028249e010c0000d088d01dbd061b40c28068d5397f0e80815980e21c06900003833150b6f036b60d0b01c250b47c31d204e3c2fdf04a3027600003034fa0610c1de0095e027ed03140000a0c6d005ff021d402ab0b954098007954151604cf434ca07e9936794d8b033500003c267b0142029a7080cc2a100000818b00003836eb08840000000024137a025a039854773c12c00000c3ae60abb91f0a078e004cd4e9f1396a4d708368c06894314e01ab802be0816c0cb0000283842095891d920e31800f1049e025bd07874277403500116a0bafc01c30cd002d8f0dce827d004c800007044940017053ec35140c900000e086c91e274e080000905a602f7c0dd200bae0b64000040a7b439914e6c00e6900e9c356c074f826400002c2722079c0000502ecc16a0040940600000000000000081b59409c80b4f40e8000000be4000070754135bd0b48000020659014590299405590e95837c300481361b47bc00000000242cf50b5b81cc50997434ec0275c39bf0cb18074d004c00b700000c338d014b830a70cbc0000607b60224e4e79c0ff00000000000000137c907c0c024a08afc22a306e4000000915102b60ad40000a033411e130e43432540123420f00003120344086816c000010268d0eb0d20570d7540e7500b8000000002c189047a4420d8021b424fd085e825a7034282ba00b2b8357d06cfc209705211018a0dbc003300002d389a06ad82bff05840000c0304831900cec804500000826100002434420e90005e900780000103a6c30670a74000030601c2f6748340000309f04095308ef830e7077c4142a02c940dd00000803e008a40000f09380000a073fc207e084901da8402c000010d834040f03d74262d04c40000708cc0000c4eb3c1462061e400c4080ad387d0a400000a01b3413d80cda40e590067501e00207c1b80082c000090ba8000080e37c37a40e5282600000200ebd0c1580ac5068503af00001c1d60000183a1f012cd040c07ed4030708fe0124b07) else (if i<3 then 0x16bd02240a0080d314e71935e407600053803c9901d20e2bd036e0c8f4047901fb013c3037d00a2e06c341a634dd2039c30096437650651c0b8540984227e4095822070312005160a650144a098c0000101cdc317904749356c047c403f60c2f520620b2142c430470000510ca3813a506da00e080aa6c115c0ace806fc08f1c291c0a57c2c7d0d658072f407d425360cce037fb4d94c2b8947fdc0d8404db0067609fe429f209d001f100c8943a21099940b6a058f015be0c4581350000041ef00e45426f50469c3b3807c9c05ca010541fff09540000c02c0015760719c3b5e0a51c39e000030032e0a0781ce70b0e802800001805dc4daf41f9f04c1402d90d70c1477031a013f1066e4075e0be80000000030177d09a6417690a6dc35aa0aa00000a0423c03760060c21d0000301c7305eb43b9d02cec1dc1000c0000f03208211d015c0000303e7c286207100000606a9d023d02404140605510396d0450405900003c1e8800bc000040829032770c840000740fc000010cc3422e60ce5400260b8880e4c0ea4013eb0ed2c313a0e2d00fb70bc080fc50add408ec07fb010590d0d82df00001c16634e54c22d306b98182b0d1500ea705b4001a5466a1391240c8000000b00537b40446818a000028231000000000a48060062901e6937f34e85c37820af4000000002c204000000000000000000e0920000024e9800000000000005064000000026ac39a00001c2d4f02a40000d0d900000000031360000038094b06f3816b1476983a8e05fbc0e3301ed5037000018240a4829935df40a0000000000c04400000000000002c0785049800000000002c200003c19ac050582f300001000a000000000640300247000000000b0664000060483c1ba000000000e4d54000000c04000080410821c00003815510b3983ad000000000d08d000007063641bbc0c1201ec70a4c0000000000000c037242a060196038190c34000034d91c12530a9c42cd0000000000000180a1000000000606b2424de054b937ac00d0000000000052f00000000000000000000e9b91dbd066381bf202a2c1c8600d682e0000009388006b7c25cb0a11c26ed090c000040590000020ee1c04ee0534120400003022810bb782b6806940000b40234303c044f828200000c216d0e240000507dfc03d40c54833a9035903a750ba1c1bdb0d9f800d90282821500001026de0236403b90bbf02a614ec4000080604000050a2442a250eac028c000004251f0e575371f0a2ec014306300000904e701dd00000413be0cf890345002e81eb00002500900001c1f30000000001031c00004043c00000000342d350860000070edec07f00001408b000000000c0ad000b5505e5414be084c81f580df940f8c40d682e630b84000000467936f0000342bc008300000000038174e027a83 else 0xc482113840000113b700327c33d205264036c0d2c8089b045cd19b0000000000070c435b0000242361026c407000000000050ba5c15814e385016904aac1fc00000000074d698183709480000e097942147013ec0f030740836120e4d427820a908372d025d538bf067dc080106769012b06a1d02000001d377d0a2a0167409abc201403b6418540d51831ca03f4801d50724810110b2dc31020d3642b17075e80db30a37c369a04285359c048dc11e40e180000002c502f4547c6c2a570750c3090000100b9c08eb4188e05ba83554404e80f1303b3827010))
def orD12 (i : Nat) : Nat := (if i<1 then 0x882aea65486a1c19653ce1a6e512dc36600464b17e2a818007982c5c0a0d98c4192358a340c0fd96803c974b457829c867b88a1c943b9bcdca1591401190798a411629d988c003c82e63a5e8c632188b25228be097490d7224670a867ba35e8c62e96446437e10803cb5c902d5b86c20090118c446b892e5d6e85c72343024f07b3bce0e838390e6e11fb8110dc5636d6ed23bb3d62c541a09007a3d1e0f0773a9ccec7262bb1ac545e149aa4f279214c3d4f0c55e241b0905e1c518612e0a058112ad964b5870d1683306eca2030d6cc2512f05eaf43298e0a235a84f6761f8d97ad31b32c2cc2170916e1f47ac574aa1c29d14994aa28b05753958aa52280f0d4bb0fac94eb05c29cdc6b5e9a960301589968bf60ab48c9d51a4d108f381a82ab50b2a060ae542ac54250f86d48034426ce06d32164bc59449506c2e4f0b05023430581c071725c588b0d85c44904628040934fa4826921c22d349010a392c9a43a5916890b21c4811088286820359a8d4590c9145413208e0622c1c09c101e1a8880c211e8d45224008f4582710070381806014260c0f06810010e864441e108744e140a0341a060b03c1e08f946016859160571585515053148511404f1384d1304b1244711845110421003f0f83c0ed372dd362d8b50c9300c12f0ad280a02749825090220841f8741d8709c0701b4681a2641905c1644c9304c92a4591444916428f63c8f63b0d4340d6310ca2d8b22f0a4280ac26896250922409a2208620880228781d8721c07c1a0641806c160541405c120441004e0f03a0d8340c8300f82c0a826090220802e0701a0581404810078060008779426ae76c65679aba6ae983e60f959e5678e3631b8fb651086f23ed8e364958fb61bc88de4958c6e4958aa63ed8e362a98aa631b8aa607588de1bc7f3611d847572481d5f1c7f35fcd7c71493641db8f7941d3f5019db174fd79f48ed9555625c2572c90e570959d06e3d9d059fdb026a895f26c09aa2695179f67419d0655590760458a7604579f5c916d659fd5f256250e554a4f29524d4064e091c94ab538247252ad48ed1c945150e541ccfe9407101c3fa4f9b3ca4ee4e75d39d93e75cf9d53e750f9e33e75079d31e75439d30e06638288e061f8196e061b8176e06578185e05d78165e09578182e058b8152e06078171e05878151e06038160e05437299dc6637098dca237196dc61b7191dc6077161dc6037160dc4409e99a76619da4676509e446768d9d93278cd9da1676449e11676029d70a74c29d10278008299606a1819820a2181a76065c82776069981962099981a5606558095209568193a054981322088981a1606458121208468170604c281102080171a91ca6571a85c66072885c69971961c99971a15c64472115c68271101c8009d982069c81a62064c81301c6a471a0 else 0xbe648511256553ad90de01a01c6e1354cee10865d65f2e3208ede01a0cfee338b4c368af992fb5532990b4401f1c6753a1c58c645db542e905936ac032c1861c054289532420cc31e3d504767f1c944fa0f9a0f4da7174b0213a8c2d47aa910a8440bf6144f0da4be768e986f505408ed0b0d94be76b0c78c86f02902758507c2e62fa0cc3641a0488340bf58cfa5918be4f2cdb6ea57a5cfa7a822f1ae62f970d161abc92f140a00ecfe35af0d0b26c2a074f2cc0ccc66ab488e705925e3046ba2a658bf15430569a4cee73425e02ff7eb3cb2d70da40819079f8cd568d1ce0b24ad01480801cd9e570ba4a6193f042191d0c15a396402de2823d1e4f1042bac9344259624618b6154401f3acbe3c640b822033f9f8ec6d3513d66fb25b28e203acc6d4578b94a80719c5c24f16a307772a86e25028006824019b4bc63dd1ac90a22518371288048803dc24a4173d8e8d64bed184009801a8f208a0d7aa10b9edf228dc60051a14c8e43701fceb097c8cda4837c8a40488f0d0497040902c67d3e076d23dbeed7535038a481205caf8282cdc56019600c00028874bb5d40057a1508823e9d4e50b2608ce83918709d7daa854000e0a4d4640d9aa65890d72245ea84ae4299203c103d142582912c3e531c6a90562e91c401500078200c211050b0fa0e9200a8386621b818c605dbe5a46399521a4f3bc32c30e25cf4a26b86cd730d434da0ca4d42c0220f0618000382e3a9a836483db89c6d90026006a0802283382849e173d7c340c10dbcc62e964aed50b96c70f22d741d003c8e0a10b94df87239940073c3505013b9c0dc6d720b56e837d8a451b8c04a2f3294c870840425f3053dbed066830d24a79c3414823933c90b7398e981940c8a0c0e02cd04e24c21047a7f9d8de6c2d9649a4)
def orI12 (i : Nat) : Nat := (if i<2 then (if i<1 then 0x684038c000040500810a00001c09f90c34000070a2c010b00000000040a584191006c9826e1069f017b0000000003054b8184d0a700000c098b80c300001d299d0e5d419850d74803e00f49833e94f4982f7f044c829470002018e608eec390001c4000060a6a00d2041b892b040b4842a580f1b423f000000000849ffc0d6702a280f800bc0822350dcc000080cec0000000000000b0506407c000000000b06cc0000f0b9780dba02fc811500000420150a28000030ed3926b80b2c0000b0f540000d0a4c422c00001c24fb0904c11f00b62420da49b0c290206a3015750b88c3ab90774c04cc073c42a6c017b8224a0afc93c41013953b88416780430089e03752041540f9a0608c13430f294338c4f014355806ff035e541e443875062c83af00001007ff0b1e03bb00a481073000000000b00200000601a8c04f704fc415df4a400000f0e3a9081707664344d0d1902c310346400a00003003dd0c7c000040f0f415a000028168d4e6c408b9081bc2ef80ce540f7905959242f04cd82eb000000000000000000000000000a06ac000000002804b0000283dad05b400004082cd06dc4ea400003019b035600110000000000000000000026bd012803a3608f3c13044e46028ca05980000f028382e800002c2dee04680000941c64220f419602ee00002c036000035068a0d240000e0353c1e56490cc14a00000000000001504204ec40000040040000d0831030ad0bcc00003097540d7c026b400be0b3c0000e48d6809d740240000108c4034a00000c268f0782405500001824ab06f90273e052d508880070825a40c1f439bd025b021c609440000f0c12828374efdc0cbf025140cd90c5cd2bf106b2807d40145c2e10000392c6b070c0000f0bec000000960c27000001c196203565094000000000000000000d0055d096741dc0000800750177306a481b170e99d3940000183a7241d8000000030203000624071704050805050401110403080400260320002506041e2b02000802253500280b4400000502120c1f11011531150f010100002a030100120108030107020010040a4d04042542000502020300030100181503011e1f1d1602190405231200340415000005162a1b07040810000d0400010d1a0c091b030301030a03051305040508050f2f0d13032100002a0206000d0039560028040112290a101e0408141303000d1d021c00320902010d5f080302010800090a0400020a12070e010000002b830004030a1b01043f12042d000800020d0e0013040f01230202000401090d000103170c160400000901000009001c0e071500070308100801080004180201170512006225010a00030903170403021f0501160a2c16000a010000180001001400071301010201240705030a0901050100020a010300010e1400000001000f030200 else 0x50c9d50628011c0000a0640000000003925f9423b00c4d0857c1f480923c25004a8b8048f0208907b00a5f139df0278823aa0625401f907fac1b9c068d427600d65c3207081403a59067a837a04f3ec0b660449821700003810e20d454074b419f42661022943261055992c4f0df141e2e0471000c40df6c31ee4776009c000030211e0041c12200002c19760dfb037230d6000f000002c0cf3093a82712025e401830f61828150b240000d420c0000f0e2881f390478c161d000e5041505fd539ca077b4267000000000204f00000b011a00ff40d31c2f164ecd821f7032b9260f49ed00fe54907d09230e7482ba7006c42e7509de827f8045982f8c0cdd409290a0853a0e06199074a0a7c0000a007982af80cd303bf50b148118b051801016098e43b640327825e9016dc0f1a04bf83760000193c3c4ac9c0dc20e4d800550d94d274704e00181005c503350000202f550292c35f10224831c0000000000000101e8b082ac26a70efb4398e0ce9011940f400000d04fa411b30b01808680c01424490f6400000000282ff54939c3ba541749262f09f64289e02d74054d0ef20366804e542e3804409295000000000000000000a0b0740b0c069993bc80bd0000044a4cc0ef504ca81f834a7b40c674eb100a5f03aa83c8e0d73d2c90000242a900001d28730da403cd00000c1aac05c2907800002c1ffd04eec155a4f27c3a8203f40000000000080606f0000070714000040900802d70e23c25660ab4000000000000080b53406fe01f883d7a0bf1d282501d4000000002010fe4925412ef01b1839970c200000c40238336a0c3bc1c12099400003090c8032e0b66c33fd05404151b00640000407600000601a3c05aa40104076b0ee1c0bea40280000000000000d0f30000040a75924ce0c080000b058d82b9d0cf081eda0b9881e90000352598019503090084c000080b3641d5000004058a0dc781c60000303290000112a06400fc395b091a4001102b5c2a890362c32c2492c000040d3c000000001c21a80c16008e701ba036a0000193d50000312c02422f0164649cc0000a0403438310650817d0000000001029ec3b02066703ac40ec800000000000007041c0000f0ca800bc0000193cb34b04000000000000000001c12aa0710000030e8b82c690384000000001c2dc000000000000000000000000000d0c6f52bb00000c1f7348f1906f9420841df30b09c04100002030324e6a423600002813a00003906cb053f524480982419ae0f3c012000d8c52c50000092840000013a2f008a417cf0d200000400dc0000c08b5c0735048c000000002c37894ed482088044702bcf05e20232f0bda806d0000000007060c0000000000000507b3800e00000000000001002e0000181af000000000000000000000000000d08f842786496f83) else (if i<3 then 0x3747082701f200ac380f4748d0024c10f47c038101cb53c1e4af5c25fa072201d37094fd05530b9001fb34aa0810660c6400000000001cdc423dc2bde0bb1c1754055341c710cb80000301c38114409d0000020301417af009303d49419a4216c015a908750954000040f16c14e106eb127280c600000c0681c321b0491809b10af802b3300cc4370c099040cc507bf012510bb4c23960aac000000001804054b0d838da0db0c295f4a50000000000c0e950f0802b7b01a6c1e160874810350d4c0029d496a02872401ec3bd20848c013e0188802340d1f82a370b2302ce702120316400d3c3c4402c601ee70531c167100aa5002c04868284d049cc2cc50a38423390256002764e8452c800000d095e04a1419c0015c41b630615024250cf7c386d0e140000c037f927cf01494354c0d92808c40d2f40aed0d68408d449469072804d6c391d05af1000804b2107f80a9dd39e900a081da702ad034e805e6022ef010a038c005150067e0d43529bc0513d393202e0c0830093400b38066c82a190019c313705ba9258e03b000003498541cb80ed40000904764261f0d880000801e1427a0000080d9b0046c18da0a17822b000000000f4f46425c80e100000242294272601eb1070000030323106d78367703cfc234b0d14000000003001a548c00000000000180349b4000080bca83140000182a490f04403920012128380f3b523a000035279000000000903b9c14310964000000003505c90ec7c3c7d04f6c08fa0eb682ae70b5481d650e3f0031205bf82ca84a4681d0d0e7e82fe549c70279a057e438b80cc4106180d8281d460124000040b13835be4ede93ca24225826c501ae1278841939275c0ecd01c0b03754131b0cc8824914eaa42d3903ae8142508134193f0898420380eb8000010dec019fe0d04015ed0ab1d090000014099000010222d0240c0b4000011398e0498407930ca382b8000018035e06324149000b352aa90d4a82300000100aa000000000c0839824bb49dd026900003938f00000928810581c2dab03d4000060b80c02be02ec0000e0e0800009039e505f007ea129200002003cb0c9543420000000000000100da00003128a000000000903a00000106f501db0073882d13095040812418c0129000030219a0080c25ba086f81cad0be540de50cae40875061c00001000901f52079e01ae601dec299c091cc0c8d0bebc09870c8bd28930e70000000001d25d00000000024f4ec2b6d052302383495b53c5c4ad081470000000001042700e60000201d764ec241a4f0808000060e694102607e402df0000040f600000400700000c218d4a8601f6500849069f0c0782a02024c03c0701768136c08f71093b068781fd806e241f1300e8c36114e6400000000042910000000001056401950000241e300000d257848da81a500 else 0x3820fd0e5b017e30a024298000000000000000000204dc805370baac2750000000009038800005045ed396c49db83120000201e4907ac4045b0eaa9397f0de540a1a081c0000600bc0000d005900e5b0d34410860e900000308a5439e44ae1c0b7009f00000b0ddd40b9506ec000020edc0000a4aa40000441f1026dc03cb815b00317c2a23031c926a00002c10400002428d60c3fc36d108bd001200001416ce05d80000a49a1c31dd095fc1c210167034330770c0c10000282aa505d00315c08df422a105cdc2e9a0339d2b590e83837fe0c900000d4ac6c0fb80e50000000001c214f0cc003d6000000000d0c6a92c200002d08c70a3c0000000000000b0e49d3ba000000000f4161003f000000000000000000f4ec800000000180afc0b43c288a00364380704ac908d0000241ea00002418a0000000d0c0052406070cb40000a0885123850e069006903b780e40079b00a20000002d600000928604af0000004f65c2d700000c03bd0878905e10ccc80fc701ed03a100688c29b2063d805c90bf5c245809f80000209ec0311842cc0000c4f084286f0dad43a940aca8235f4ef6816900003c3d30000241b000002029e00003836f302e8c085102f4000000000000000000000000000000040621527a10193c172848ed015310ee6830b4003c13ad70382c15c00000c0619034f10912495680acb09be01622024783cbd02a7404db05aa012d20e2780fa30727c01740c18000060f2443570000041cce074400002080300a310cbd139204a140000e06740310602c8d2a7d0ac6002510c309296c064a003020ad6022570949014d2017c0000c08a0410d70431507de07c041d294a0001adf06dc415800000000030221802640db8000050024000000aee0210d0ad3c2ddf029800000000042dbe07f2c063d0d000000403084050706d10))
def orD13 (i : Nat) : Nat := 0x156703db44fb8cafa513cd2c91ea96703ceb5b1d8d3142fb8cafa36c2daa95e3a1826689d8e970d78d66025b7ecdb0b6a6604db7a371980d9d8806184288202004ae4a5c6d87d69a250c40838692079648a58fe5721107e3b11074389147c35170a84a241308440210e078301a0a058201307034180f05024100b03014080701004000002bece51b3e338ce338cfb3cd717b3f358ceedbb6cf8ceedbb717b3eed8ceedbb6eda4ecf8ce33a4e698ce338ce518ce3388621ffe4c7ff25bff90dffc94ffe427ff1d3ff8c9ffc93ffe41fff1cfff8c7ffc53ffe21fff247ff903ffc61ffe20fff0c7ff901ffc70ffe307ff143ff881ffc30ffe107ff042ff9317fc96bfe4a5ff192ff9277fc91bfe305ff102ff861fec20bfe105ff041ff8007fc00
def orI13 (i : Nat) : Nat := 0xb04000000002067f0b000010000000b0cda04fd30f86074c4000342ec842000060d1c0de04ac0bce0a6000800050740000000682f10980000000700d7028c18c0000000000000000000000a4c8c98c429b04eb4ce000051fc85bd01c0000818083ec02a4067027e82bc08c00030327a380001a073c151011f00981379340a0834732155c1170331093a90542470310000a140000003800000000c1c802e740ea8c0821e8591025c08d11e0816c03d805fc340000d04f21874311a604088000281b882500000002932883bc413c8dd804a80b40ada8c800570057475411e806705a004c000001ff84034620000000404bf0b901a48293845703120760195a2f90afe03d41662000001e903410b806d05a0151814303d40be806bc121233b0216196803a851906b28eec011836a082000281e101fc007c02030c60420230010810020833020c80430002800028400000970c03050870410c6000088
def orIndex : Nat → Nat → Option (Nat × Nat)
  | 9 => fun _ => none
  | 10 => lookupWord 32 149 7 15 7 4 orI10
  | 11 => lookupWord 274 1340 8 18 10 4 orI11
  | 12 => lookupWord 330 1517 8 18 10 4 orI12
  | 13 => lookupWord 47 169 6 15 7 4 orI13
  | _ => fun _ => none
def orLevels : Nat → Packing
  | 9 => (107,6,7,10,6,11,78,orD9)
  | 10 => (955,5,7,10,9,15,78,orD10)
  | 11 => (987,4,7,7,10,16,78,orD11)
  | 12 => (106,3,7,6,9,14,78,orD12)
  | 13 => (40,2,7,0,6,10,78,orD13)
  | _ => emptyPacking
def orPack : Forest := ⟨511,15,dead.samples,orColumns,dead.autos,orLevels,orIndex⟩
end PEqualNP.Outside.L_meta_3020.Search
namespace PEqualNP.Outside.L_meta_3020.Search
def miniColumns : IndexTree ColumnInfo := (.fork 28 (.fork 14 (.fork 7 (.fork 3 (.leaf [(0,0,255,0,12),(64,0,191,0,11),(8,0,247,0,9)]) (.leaf [(32,0,223,0,9),(0,64,189,2,9),(128,0,127,0,9),(1,0,254,0,8)])) (.fork 3 (.leaf [(2,0,189,0,8),(4,0,251,0,8),(16,0,231,0,8)]) (.leaf [(66,0,189,0,8),(2,64,189,0,8),(24,0,231,0,8),(160,0,95,0,8)]))) (.fork 7 (.fork 3 (.leaf [(0,8,227,20,7),(0,16,230,9,7),(0,32,94,129,7)]) (.leaf [(17,0,238,0,7),(33,0,222,0,7),(65,0,190,0,7),(12,0,243,0,7)])) (.fork 3 (.leaf [(68,0,187,0,7),(40,0,215,0,7),(1,16,230,8,6)]) (.leaf [(1,32,94,128,6),(1,64,188,2,6),(4,8,227,16,6),(4,64,185,2,6)])))) (.fork 14 (.fork 7 (.fork 3 (.leaf [(8,16,230,1,6),(16,8,227,4,6),(128,8,99,20,6)]) (.leaf [(128,32,94,1,6),(64,128,27,36,6),(9,0,230,0,5),(6,0,185,0,5)])) (.fork 3 (.leaf [(67,0,188,0,5),(3,64,188,0,5),(9,16,230,0,5)]) (.leaf [(17,32,78,128,5),(65,16,166,8,5),(65,32,30,128,5),(161,0,94,0,5)]))) (.fork 7 (.fork 3 (.leaf [(129,32,94,0,5),(70,0,185,0,5),(6,64,185,0,5)]) (.leaf [(82,0,173,0,5),(194,0,61,0,5),(20,8,227,0,5),(68,8,163,16,5)])) (.fork 3 (.leaf [(132,8,99,16,5),(68,128,27,32,5),(132,64,57,2,5)]) (.leaf [(40,16,198,1,5),(144,8,99,4,5),(144,32,78,1,5),(96,128,27,4,5)])))))
def miniD5 (i : Nat) : Nat := 0x1e241524c0890696948153
def miniD6 (i : Nat) : Nat := 0x2943c92549302256948153ee41524c01a5a52054f8b44c0890696948153
def miniI6 (i : Nat) : Nat := 0x2800
def miniD7 (i : Nat) : Nat := 0x3830b8508000001c2b8c1000c182e0c2e302e0c3052447c104205cb95756b61574d430d02f8d8b89878019b35cd2a0656054f372b8a540cac0a9e6e5314a81958153f692a498112902a7f92549305a52054f96c98112b4a40a9eed1300696948153c5eb120d2d2902a78bd2241a5a52054f17b44034b4a40a9e2f5840696948153cdaae60d2d2902a78bd6001a5a52054f36a98034b4a40a9c39c9b528824c153
def miniI7 (i : Nat) : Nat := 0xc0000001b9a462
def miniD8 (i : Nat) : Nat := 0x108081001830e181010200840008703092c128b410c82c189850804408828185e1060614081710080c08040681818541858181000c2b18200008305830b18160c3a085820b00611080388010c8283b183904320864108c520b042905831482c28a416084c6068350440a31c12047e0a0a811060e04a0e85e0b018a0383e082e0d0dc00b801250880882c05cbc2e0dc608e138441400e8f048f22017068b017820e05e4f041a06078470b837182380e6d00360ab9d6ead356aa5d3ca5b4a28cd0a9e338a64cba96b24a41c7e8df15a1ec1a816fc9f6be879ef29e2bc0762e89c9b846d6d499cb2a60ebe174ad056ea7942a6c4ba9111fa1c366690c09722c64b06b8a00e6140078008ff46a99611538ff2698484553cbfa216984553cbf6116984553db75cd6984553abf5aa11601538ff26a11601538ff46a9960153cbf5a929201538ffaa92920153f37589735c153f375d17358153abf4288258153db75cc1958153dbd5c41958153dbd4c419581539bf4a81958153f8f5516250153af7468824c153bb75aa114c153eb7209604c1538ff26984481538ff2698148153f765cd7048153fb65813048153ef64c08948153fb64c16948153cbf6256948153cbf2256948153bbd0696948153cbfa216948153cbf6116948153db75cd6948153cbf6016948153db74c16948153aef5288244153afd4688244153afe42882441538ff6688244153ebe6016044153ebea216044153ebe61d6044153ebe6116044153f9e5516044153fb65cd6044153ebe6096044153f9e5496044153fbc5056044153fb65813044153fda5492044153ebe5818944153f475d1545cd538ef26a44601538ef52a9960153c7d845792015387faa97920153aaf52882581539bb4a81958153ae7528824c153fc6551404c153fd254930481539bd0696948153aee5288280153
def miniI8 (i : Nat) : Nat := 0x1c7cb001814e0001267900f08ac8009354cdcc00e38000004201800902f40018a21d847141710060
def miniD9 (i : Nat) : Nat := (if i<1 then 0xcc82e1fcc7e51ea87541bf869618285b4155450812804260e8c3290abc23506ec1a4065817f05c41630578159052c13404bc118044c0fc03700ce02dc0b2026c096022007a00037fae3442a7bfc1961153fee0cae6a9eff61d4154ffbae6a0aa7bfd8150553dff44422a9eff6121154ffbae708aa7bfd7160153dfea0b00a9eff8458054f7f832c02a7bfd7220153dfeb8900a9f7f5d17054fbfae6b82a7dfd715c153f7eba2c0a9fbf5cd6054fdfa84b02a7efd7158153f7ea0ac0a9fbf4c56054fdfac4a82a7fdd7350153f7eb1280a9fbf5813054ffbae2982a7fdd414c153fef08a60a9ff70653054f7fd10902a7bfd8448153feeb9a40a9eff6052054f7fb00902a7ff97048153f7eb0240a9ff74c12054f7fb12902a7bfc8948153bfebca40a9fbf5a52054effd32902a77fd1908153dff44220a9eff61d1054f7fb08882a7f7d5444153feeb9a20a9eff6091054f7f904882a7efd6244153fbea9220a9eff6051054ffea82882a7bfd8044153f7eb0220a9ff74c11054fff240882a7bfd8944153bfebca20a9dff4a51054effd32882a77fd2904153dfe41400a9fbf58a0054e7fd32c22a73fd895d153ddf44488a9eef61e4454fb7cef222a7bde885cd53eeeba2e6a9fd75517354ff3c88b9aa77de995cd53deec3c66a9f779de3354f77c88c0aa7bde33605539ff4cb02a9cff6254154e7fb1298aa7bf58184553b7eb4c22a9efda221154f7eb0908aa7fb64484553feab9c22a9ff58ce1154f7e91308aa7ef56984553cff3bb00a9edf9558054f6faa8c02a7bbe4460153deeb9b00a9ef78cd8054f7ec22c02a7bbc49601539ff4cb00a9e7f9dc8054f7ec22402a73fd79201539fe94900a9cff4648054f3fb0eb82a7ddd735c1539fec4ae0a9ebfa216054f5fb0eb02a7cfe7758153f3f2aac0a9ebf6116054fcfaa8b02a7ebe4458153f6eb9ac0a9fb78cd6054f5fb04b02a7afc8258153d7ec0ac0a9fbd8456054f5fb00b02a76fc1958153b7f4cac0a9fcf5514054e7fb12a02a73fd894c153def44260a9ef761d3054fbbcee982a7f5e554c153deec2260a9fd75513054ff3c88982a7bdc824c153f6eb1260a9fd75493054f7bb02982a7fd6114c153f6eb0260a9ff65013054f7b912982a77dd794c153fae2ca60a9fe71253054efbd32982a7fd930481539fec4a40a9dbf5a52054e7fb12102a76fd6908153bee9c840a9fbe5811054e7fb12882a73fd8904153afebc820a9dbf5a41054eefab2082a77bd4904153bee9c820a9dfb4a41054f7f301002a7ef96080153fec98400a9efea220054f7f30f002a7dfa7780153fbd2ac00a9efe6120054fef2a9002a7fba4480153fecb9c00a9ff68ce0054f7f305002a7bf88280153f7cb1400a9fde54a0054ffd445002a7bf98180153ff908c00a9efe2260054ffb073002a71fd7920153 else (if i<2 then 0xf03c12040404034050b018300e00bf820f0b820201a028181c015433828d258241010028181c015d01022c2e30884720864360403a6801a00414041881c0420b8018630050c600a0b82e0a303e250e8bc12100c2d80184e0f828d0e8a83405060394c0060a18c01637828c16868300e3f05801e078241010038680a160c03802e8240d8005241206c01e0b078ce0a34640f1004412081501c2c0506818040300d3820f1004412040801c240503008060e00bf8224078804611048202012028180403070061c1440c82e160681830881f0518371a0a80a16068095c1048200e1a0c03802844a210e9642b010483098a0080662251087098a02e04030612c00b0028843a144e130b8100c184e17048246094502a0c21801c1a151a83460a8cc00a250e85098a02e041501830a4421d0a82418cc442c0b8100cb44a210a4b2384c2e04030614c00d05128843a1518280b8a830015e160d8ca091c8227110a00ea60070b02e087054160c00c189e085c10070d0141c014433828d048200e120d0141c015b003c144074340d030601c881b004c0018b82880b8680c18060391c1128745e020c00c18881b005c1440c45e170d008f034aa20602f0d1b8226150680418019f82880e8680c18071e06c0140f06261405c5412030613c10e898222f1a008300c4c33828846b010623088681a0601839bc146874541a01838e0e0898221a06038cc00c23822f0d008306e082420070d014300e00a6118583631144b2211c089e085012080801c24050303802bc2e31144b2211c82140b81010120d01830fe0850101203008300307260f85c6211824b208b04618570412080d014300e00a3824b250241010038140c0e00af1981e092c94291585c54070901830dc2e318244251043617020a80e1203061d85c6607824b2507c5610038480c026e1703c125928560f088a80e1203061b85c0f05184b2501c340601060060e6e171981e092c942b0b8a80e1203061b40460a801a020c5400d0020050034041081404188140428a8084410e801a020840a020440e007801e060b078ce08a4642011844241603363658d823528ca63008b5e2c08aca2a489ca24988ca22487ca1c0865e16e851612584160d382aa081818604a80860017f61fb87e3df787d85f4a7c61ee67ad1e9479ade4b78ade147819dd4773ddaf7619d667519d26743dcf8733dc9d71d1c547089c0b6f89bb06e65b826d89b396c65af96ad5a7169219d765e196a657195765258e1620986b617584f612983360717905cc56c95ac965c593964058ed624587d60857e95e3573156455594f753814c952154024f653b94c01274477d19244cd0e641d501f40450033eb4f603d48f173c24eaa3908de33754d6d3438d0032a8c5d2fd4be72e68b832db0b1f2b48abb29dca3c27e09b4267494723c487720 else 0x8b3042c0e2020a1a08b4120e25050616061219414082480707080e1418618c1170141c5608b4120e24300e216860903100a80c58240d822003144a1d0b8309030b0340448b40c941822584a171a151a831a5904250b860a854b0a03044b2305017220c96281c0834288a0c682a24445e1a1c0e1812031206c1070e06c11a0389030b08460e10581c20b8680c1807150637150681c54092c341807151808070c8a3215068916608606830b06068546090811b8a82c0307140410b0386410b0601c4a08581c3a088c1c3a088c1c3a0a08541418a8285118389414220858082c5896300d1282820b0e8281258181c5460305414601c1c48b10450060c168283112c942e0a3102320858060e21042c0e19102c0e192c882b08058300e3c0a82844105c10063c5a0d02181219c1600782e08038680a06060059c10785c1010038680c0e00aa801a0040c00f0512830e8bc68050b034040c5c17821f0e8bc540d0100c18a81b004c00d002080b00501600b82c0))
def miniI9 (i : Nat) : Nat := 0x33940000004698c800289dcec000ce8fef427c604c606c051cf800270182f8b0001c1ece544efb40000020b8003b7e470001821f400000aabe78784980000030340054d536c88344902b3ebf73c97f60cdd3b34a3c324ccf64002334f6800308603a88fb1180d875f7b8920f3811018bcbcae4bf48b40045800080b8420f641683c0038d800000177487f0e24b74540033928d0c464a531906545c0013af8c00000000019163430103058183084104047012000403
def miniD10 (i : Nat) : Nat := 0x46e0a522a08a08090d0b0c0607362a07052904d8d4c83c4450d02448581434080c303ab1507038294822824340a2c1a0406181d08d8cc14a45411410121a16180c0e742c140e0a2a09687888a1a048803890b0101860752160705150450281c486858080c3039f0b19038296948e8a825646280e242c04061928d8cc14a45411410121a16180c0e7454640e0a5209499100a1a150b028683010c018607562a16320705291504404858341808303a1150b0382948a821e4c22286812202c0c043006181d58a8581c14a4541141a160602030c0e7c542c640e0a522a09a04080d0b03010c0186074e2a1632070529150498505c20a84048681808600c303ad0b1983028a82462868200e2c0c043006181d2858c81c14b4a45412b26172a100712060218030ea4542c640e0a522a08a0b9508090b03010c0186075237020a0e330500c498bcd02420a8401c6858141808600c380731b81050782622e1054200e340a0c181c0318a85c0828381c14011090c5c1e0a297950d028b06818607322a17020705005058080c3171b810507198294626a4c5e12105420340a0c301c03585c082838c81c140074c6e04141c660989a93178484150803890d02860700d637020a0e33048c441048145818080c0612d0b1b0507189688264c50085414240c3118d83c13135262f2a121a160618030c0e84542e04141c640e0a0032bdb3aff8eb71748328f03ae66bb299e6ea4f6281fadd59ac58314fd2c9154fc0e4cb98a647b059c368154003ff61153ffd7454fff5cd53ffd8154fff50553ffd3154fff84553ffd8054fff5c153ffd5054fff50153ffd3054fff48153ffc2054fff44153ffc1054fff80153bfe8854eff61153fbe4454ff75cd53fde3354eff60553ff61154eff60153bfc8054fbf58153fdd3054ffe80153
def miniI10 (i : Nat) : Nat := 0x1d4a394321f05a909bc2ec11cf037dcc49572d50b7119002c0cb449389be80f9d7f8a5b184000acd84500000f85a0c2f550000000000136abe4e89e20e60b1000000000000002e9544afd280005290000fdc008a0001c219e214b042d80000000c12c0e342a000287f8daf434bddb49842117b2eda28805008892d1ccc96de564a90000491a1d2f977149837e28c00000000000288000e2bccb87ed14a71286712313c000e19589dccb23a4f2bab7d0e1ac7edcebea701a87b60e11f5142230230001876e12c00041af082000188d000385c62240006058000000000072b1886b10ff4000010ad0002b5ef2700b40000000b15e7b18d9b842026d745407cb1dee4a40be15abb0221700ab2c9048ce2afae414e34731898241e0e7082e0940131b4000e07905b20400002cdc0000000000000031f0000000fc34000c2a00008124000720483dc1c40002c3c0000002c63f07006800018111269c8351b800000000140dc9f59d068000c0e939fad680000055b6950d4000cd040722282f9da01c000000000081ea8440001b07000301dce6cc4ea161499000200ca1f1348c2a80003145854000143c90d80000000c2b40fec9041dc08e4015b092cc3045e118413c038000019a80dd0bc804c1664b9c233841917d419ecff05eec40000b0c70098d24c7bc1a6f348ccbc67e22e0205e84000b088000327ff4b0001b5b506df068c1084c2d8000000000000000b110000000c2500006d8542d0000ca6d0c800032cfc33323c875000000000000257e62079c1e285d4e2c00092ad818b1b2724000134db25c03e0003f2f0000000f13400001540000003803d01b87d7cd4800a102b3e00014170002829000000000020608023c6ffddec3bf1c0000000000000030280000000f09c000000000fd0441010ca2c004504009318000438138f0505841ce00049504600030010c30f00310401300018008505d0c30800c714004608008d00400608400b040040101080
def miniD11 (i : Nat) : Nat := 0x411414b0d040c6014c0002983fea9bfd53
def miniI11 (i : Nat) : Nat := 0x1345610013d44af8392de603bc6c0140027e290adc001c900071dc0946000a0e00139199ec4c1776904ff020105b130015a93d01c00159179d111d346d4b8007c0220fa50d21fe26b88e3fcfe52c081a000000c30c658805008c0110082001aa
def miniIndex : Nat → Nat → Option (Nat × Nat)
  | 5 => fun _ => none
  | 6 => lookupWord 1 2 1 7 1 2 miniI6
  | 7 => lookupWord 1 7 1 8 2 2 miniI7
  | 8 => lookupWord 6 29 5 10 4 2 miniI8
  | 9 => lookupWord 23 109 6 12 6 2 miniI9
  | 10 => lookupWord 89 371 6 14 8 2 miniI10
  | 11 => lookupWord 19 62 5 11 5 2 miniI11
  | _ => fun _ => none
def miniLevels : Nat → Packing
  | 5 => (1,7,6,0,0,1,0,miniD5)
  | 6 => (3,6,6,0,0,4,0,miniD6)
  | 7 => (15,5,6,0,0,8,0,miniD7)
  | 8 => (63,4,6,0,0,11,0,miniD8)
  | 9 => (186,3,6,0,0,14,0,miniD9)
  | 10 => (29,2,6,0,0,12,0,miniD10)
  | 11 => (2,1,6,0,0,5,0,miniD11)
  | _ => emptyPacking
def miniPack : Forest := ⟨255,12,g255.samples,miniColumns,g255.autos,miniLevels,miniIndex⟩
end PEqualNP.Outside.L_meta_3020.Search
namespace PEqualNP.Outside.L_meta_3020.Search

def mkOrExtra (a b : Nat) := bin true (inputs.getD a zero) (inputs.getD b zero)
def mkOrRoots (m a b : Nat) := vars m ++ [mkOrExtra a b]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem miniPairs : properPairs (targetOf miniPack) (asRow fun j => (miniPack.samples j).1)
    (asRow fun j => (miniPack.samples j).2) := by
  apply chart_pairs <;> decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem miniAutos : ∀ p ∈ miniPack.autos.toList, autoOK (targetOf miniPack) (p.map swapRows)=true := by
  decide +kernel

def miniColValid (c : ColumnInfo) := decide (c.2.2.1<1024) && colCheck 255 c (boundsBefore known383)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem miniColsValid : miniPack.cols.values.all miniColValid=true := by
  apply listPieces_all (d:=3)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel

theorem miniColumnsSound : ∀ c ∈ miniPack.cols.values, Slice (chartRaw miniPack.mask c) (targetOf miniPack)
    (subcube c.1 c.2.1) c.2.2.2.2 := by
  intro c hc
  have q := List.all_eq_true.mp miniColsValid c hc
  simp only [miniColValid,Bool.and_eq_true,decide_eq_true_eq] at q
  simp only [chartRaw,show ¬c.2.2.1≥3072 by omega,show ¬c.2.2.1≥2048 by omega,show ¬c.2.2.1≥1024 by omega,ite_false]
  exact col_sound c _ (before_sound known383 valid383) q.2

def miniHints : List (Sig × Row × Row) := [(inputs.getD 0 zero,2,3),(inputs.getD 1 zero,1,3),(inputs.getD 2 zero,2,6),(inputs.getD 3 zero,36,44),(inputs.getD 4 zero,1,17),(inputs.getD 5 zero,9,41),(inputs.getD 6 zero,2,66),(inputs.getD 7 zero,4,132)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem miniHintsOK : checkEssential (graphGoal 255) (mkOrRoots 255 3 5) miniHints=true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem miniLower (rows : signedTables miniPack 11) : Lower (mkOrRoots 255 3 5) (graphGoal 255) 12 := by
  intro p bank reach hit
  by_contra! short
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live (proper_of _ (by decide +kernel)) reach hit
  have needed : (vars 255).toFinset ⊆ S := by
    intro a ha
    have words : miniHints.map Prod.fst = vars 255 := by decide +kernel
    rw [←words] at ha
    obtain ⟨r,s,diff,iso⟩ := essential_ok miniHintsOK a ha
    exact raw_required run _ _ sub r s diff iso
  have low := signedForest miniPack 11 miniPairs miniColumnsSound miniAutos rows 11 (by omega)
  have hbase (i : Nat) (w : List Sig) (idx : indexedRoot miniPack 11 i w=true) :
      Impossible (graphGoal 255) 11 w.toFinset := by
    simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
    rw [←sameWords_sound idx.2]
    exact low i idx.1
  by_cases useOr : mkOrExtra 3 5 ∈ S
  · have same : S=(mkOrRoots 255 3 5).toFinset := by
      apply Finset.Subset.antisymm
      · exact fun a ha => List.mem_toFinset.mpr (sub a ha)
      · intro a ha
        simp only [mkOrRoots,List.mem_toFinset,List.mem_append,List.mem_singleton] at ha
        rcases ha with raw | rfl
        · exact needed (List.mem_toFinset.mpr raw)
        · exact useOr
    rw [same] at run
    exact hbase 1 _ (by decide +kernel) k t (by omega) run
  · have same : S=(vars 255).toFinset := by
      refine Finset.Subset.antisymm ?_ needed
      intro a ha
      have member := sub a ha
      simp only [mkOrRoots,List.mem_append,List.mem_singleton] at member
      rcases member with raw | rfl
      · exact List.mem_toFinset.mpr raw
      · exact False.elim (useOr ha)
    rw [same] at run
    exact hbase 0 _ (by decide +kernel) k t (by omega) run

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem deletionOneSlice (rows : signedTables miniPack 11) :
    Slice (mkOrRoots 511 0 2) (graphGoal 511) (subcube 2 0) 12 := by
  exact slice_correct (ms:=([82,129,48] : List Nat).map swapRows ++ fixRows 2 0)
    (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (miniLower rows)

end PEqualNP.Outside.L_meta_3020.Search
namespace PEqualNP.Outside.L_meta_3020.Search
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem miniR5_0 : signedBlock miniPack 5 0 1=true := by
  apply signedCellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
theorem miniLayer5 : signedBlock miniPack 5 0 1=true := miniR5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem miniR6_0 : signedBlock miniPack 6 0 3=true := by
  apply signedCellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
theorem miniLayer6 : signedBlock miniPack 6 0 3=true := miniR6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem miniR7_0 : signedBlock miniPack 7 0 1=true := by
  apply signedCellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem miniR7_1 : signedBlock miniPack 7 1 14=true := by
  apply signedCellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
theorem miniLayer7 : signedBlock miniPack 7 0 15=true := (@signedBlock_merge miniPack 7 0 1 14 miniR7_0 miniR7_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem miniR8_0 : signedBlock miniPack 8 0 12=true := by
  apply signedCellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem miniR8_12 : signedBlock miniPack 8 12 51=true := by
  apply signedCellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
theorem miniLayer8 : signedBlock miniPack 8 0 63=true := (@signedBlock_merge miniPack 8 0 12 51 miniR8_0 miniR8_12)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem miniR9_0 : signedBlock miniPack 9 0 1=true := by
  apply signedCellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem miniR9_1 : signedBlock miniPack 9 1 117=true := by
  apply signedCellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem miniR9_118 : signedBlock miniPack 9 118 68=true := by
  apply signedCellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
theorem miniLayer9 : signedBlock miniPack 9 0 186=true := (@signedBlock_merge miniPack 9 0 118 68 (@signedBlock_merge miniPack 9 0 1 117 miniR9_0 miniR9_1) miniR9_118)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem miniR10_0 : signedBlock miniPack 10 0 12=true := by
  apply signedCellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem miniR10_12 : signedBlock miniPack 10 12 17=true := by
  apply signedCellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
theorem miniLayer10 : signedBlock miniPack 10 0 29=true := (@signedBlock_merge miniPack 10 0 12 17 miniR10_0 miniR10_12)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem miniR11_0 : signedBlock miniPack 11 0 1=true := by
  apply signedCellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem miniR11_1 : signedBlock miniPack 11 1 1=true := by
  apply signedCellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
theorem miniLayer11 : signedBlock miniPack 11 0 2=true := (@signedBlock_merge miniPack 11 0 1 1 miniR11_0 miniR11_1)
theorem miniTables : signedTables miniPack 11 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact miniLayer5
  · exact miniLayer6
  · exact miniLayer7
  · exact miniLayer8
  · exact miniLayer9
  · exact miniLayer10
  · exact miniLayer11
end PEqualNP.Outside.L_meta_3020.Search
namespace PEqualNP.Outside.L_meta_3020.Search
def clippedInputs := inputs.map (fun a => a &&& ~~~seed)
def clippedGraph := graph &&& ~~~seed
def clippedPairs : List (Sig × Row × Row) := List.ofFn (fun i : Fin 9 =>
  (clippedInputs.getD i.val zero, absentRow i, presentRow i))
theorem clippedLower (impossible : Impossible clippedGraph 13 clippedInputs.toFinset) :
    Lower clippedInputs clippedGraph 14 := by
  apply lower_impossible (by unfold proper; decide +kernel) _ impossible
  have es : checkEssential clippedGraph clippedInputs clippedPairs=true := by decide +kernel
  have all : clippedPairs.map Prod.fst = clippedInputs := by decide +kernel
  intro a ha
  apply essential_ok es a
  exact List.mem_toFinset.mpr (all.symm ▸ ha)

def clipBy (m : Sig) (r : Row) : Row := if bit r m then 0 else r
def clipRow := clipBy seed
theorem clip_general (a m : Sig) (origin : bit 0 a = false) :
    rename (clipBy m) a = a &&& ~~~m := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let r : Row := ⟨j,hj⟩
  change bit r (rename (clipBy m) a) = _
  rw [bit_rename]
  have e : (a &&& ~~~m).getLsbD j = (bit r a && !(bit r m)) := by
    simp only [bit,r,BitVec.getLsbD_and,BitVec.getLsbD_not,hj,decide_true,Bool.true_and]
  rw [e]
  by_cases h : bit r m=true
  · simp only [clipBy,h,ite_true,origin,Bool.not_true,Bool.and_false]
  · have v := Bool.eq_false_iff.mpr h
    simp only [clipBy,v,Bool.false_eq_true,ite_false,Bool.not_false,Bool.and_true]
theorem clip_word (a : Sig) (origin : bit 0 a = false) :
    rename clipRow a = a &&& ~~~seed := clip_general a seed origin
theorem seedSlice (lower : Lower clippedInputs clippedGraph 14) : Slice inputs graph (~~~seed) 14 := by
  have gg := clip_word graph (by decide +kernel)
  have go : restrictRows clipRow (observe graph)=observe clippedGraph :=
    (observe_rename _ _).symm.trans (congrArg observe gg)
  refine ⟨clipRow,clippedInputs,?_,?_,?_,?_⟩
  · intro r
    by_cases h : bit r seed=true
    · rw [clipRow,clipBy,if_pos h]
      decide +kernel
    · have e : bit r seed=false := Bool.eq_false_iff.mpr h
      rw [clipRow,clipBy,if_neg h]
      simpa only [bit,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and,Bool.not_false] using congrArg Bool.not e
  · intro a ha
    have orig : inputs.all (fun w => !(bit 0 w))=true := by decide +kernel
    have z : bit 0 a=false := by simpa using (List.all_eq_true.mp orig a ha)
    rw [←observe_rename,clip_word a z]
    exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem ha))
  · rw [go]
    exact observe_proper (by unfold proper; decide +kernel)
  · rw [go]
    exact lower

theorem seedFloorViaClip (rawCase : Impossible graph 14 inputs.toFinset)
    (clippedCase : Impossible clippedGraph 13 clippedInputs.toFinset) :
    Lower (inputs++[seed]) graph 15 := by
  intro p bank reach hit
  by_contra! small
  obtain ⟨k,t,S,le,run,sub⟩ := reach_live graph_proper reach hit
  rcases all_roots run sub with e|e
  · exact rawCase k t (by omega) (e ▸ run)
  · have hi := poolCut_sound (seedSlice (clippedLower clippedCase)) [] (by rfl)
      (ws:=inputs++[seed]) (by decide +kernel) (cap:=14) (by decide +kernel)
    exact hi k t (by omega) (e ▸ run)

def seedPair (a b : Nat) := bin false (inputs.getD a zero) (inputs.getD b zero)
theorem seedPairSlice (a b : Nat) (swaps : List Nat) (low : Lower (inputs++[seed]) graph 15)
    (mapOK : checkMap (swaps.map swapRows) (vars 511++[seedPair a b]) (graphGoal 511) (inputs++[seed]) graph=true)
    (domain : movedWord (swaps.map swapRows) (subcube 0 0)=one) :
    Slice (vars 511++[seedPair a b]) (graphGoal 511) (subcube 0 0) 15 :=
  slice_correct mapOK domain graph_proper low
end PEqualNP.Outside.L_meta_3020.Search
namespace PEqualNP.Outside.L_meta_3020.Search
def hashrestrictedl13 (i : Nat) : Nat := 0x3266d629c3000cc09800002c5a916a703a921aa561d5132e8d2800000381db0ef80ad078788712ce0036333c001b9c02082090848
def hashrestrictedl12 (i : Nat) : Nat := 0x62203295be14261132f30f3f1b40f70c8570ea66463a299d46c1ba2855693691546f740aeb454505f848713832723d0330abaef704500000000000000000002246c7f88ca8ddb1706419d9dfb457c0dd31f15082e0960004df3cf70400398003d17a2e309f11f451c7ee3c12b621bf3c50e3a1244b5ac092482789280c6564dc983c8302b1b20b118a5000015fc042239f2935ba13ff30f307a60f4e277ab838768f4897601ade5b3cc02721800000040b41f3cd8ce1d764963e1314d739b00162400126810b794f6be00053524d7cba0002ad8002c0325551ae8fc431233c90982be9e00000000034280009902110cb80007548254000000f1d800124d8a5e47463801066bfc798d0000b73042ca022e292214900000004943bd408c0000000005cc584c000c8b8002534e7c000622267486115380024940580007aa1947a4c4a8696fd33d25c0d7104063e0ecbc168c6eab8544eeabead2c83731524e6b306c0d0e1c4a7181079a312f870459c1949b742b43a40fe50dc8574d5a519b98ac54ed289cdc149c2f696baac46c504797113ed0d22df2d4cbc0010484160000231227702a9c9c08c67c09295f541c2a112421e513a8f00011e703768da14b1f5e046066c37470001c9cc81a1a4000000510127b5220000000000d36c76a3a000140e000bcd80000011496038b063a005800610001005489e36724000a60786185c2900f1439b5a08b00124c018022858000b4043180008626004825c0c3870a0401806148870c0c2800a1c3000204301042c184
def hashrestrictedl11 (i : Nat) : Nat := (if i<1 then 0xc1b5add011e81124450c3ea5c13b407274e85915c39d0c00d88150e791cb40c5ed0c9bc327aa27eaf919d389c944f96acc45d60131309832800061abc19ca1a4c1d63eea14d209bd4671f0d0b02441110c09b33efc4f51da0000b07025cc9514b49258c00031997106d7b9cd81924a9f310828f818760000e191c99000000000003c6748ccd83f61af88250ca20c7406f80b840f38420000000618f13b1c0566de0000e0c0f76ea068c9f000000000000000b08f84d10dfb9e83925f70bca615e2916002e24fa61bb0372c1d143f64027237829967ee939f3dee31c00000e3f34eb15d470c5b700000003c68d44dc92200014ab7042d2b40002c5ec1ff9a2ec6a9e74800083ceb3624fb000061a6c4ac00059eef16e8007671adcac30eb5bd44cb886a986177d43778cf48a98407230706a6381a2a4e0870d21b38c202425f0cdc306c2712be900000018364000007f2891b2c60fdf0b1a1cd902ce4381890000855c08ef965c0cc21740a2f4a348d6e07a85f392de2e6000149d2d3c000144d5e0630336149c066c3cd9e95ad1b67f882f84c000b65da09869a8f057d379cd3000000002510000140453188564caf59619bc2000369a8000c22253d988b398a005575548da85f7716bc3218e73813c182a76446dd8bf43ba17b6c90096b702db0228032040c0c46358cb8bc47313502614e601de5b0da634c5098b3d23e76a7ce32992c358a4312add05b207d43b38d0dd44437a8171cfed8fee80cc26d4ca95887173c2ca02fb9afe15dc41d44ec075e091c7240149046b82904568723010ba66a4ba894c0456ab1c6db691e07c012216d5cc7716e489624da25f10c3c24324eea150da582970791c75507ab0d0516b857f474403ec610805485443c005e6ceb945c12a7e10e8113db9f2db12a8ca42cb503e6e25842b8da6d070768b8c409b113c3201f6cec1500369116ee5dcc944a3b4074c6b8968081c2034cd1d146a225225e894190a10d356ae8cb006f71f900334282c7f239bf02a25269a27017a59c0128832000041c02040080e1472868001f0095000440200c2e060a23e1e005200c0c055409c08522004856221b00800010195c12050880408001100434080d8d800061a01000260d84c0003100100400038ac1c0a0a0000409080440a022e0282057090000001028000a080007824001401400103284c4e0e0a02c0605000241603010201c1e008006225018000a080180c060509814027800018060a2000002061e00c00010080000161e014000100008cc10010000a01030080002020381c160703000080300002b8040086e0400020041a038003e00000000a000100c001a039241a07000402a7604800063c080001c004301c040f000300200098100600010200a000081000010180c0412060cc0200018040e08050000001068180000 else 0x489ce72c899bc2511f5c1598b925a35b9ae653cb109e5f402873f05291c33b2dd1ba2b6d9035bb923a18bec0ad407ba22110058442b66676ea4108c651182690038402ca031f4d80b491c40a3727d44a979ad13a17254c75e93ff0e4e65eef998f768124661089d034b11a87c7828f51a321333cb64b81be00b2129ac5a0170712a40b400000000001a53445400000001b4502d89885f28e923caf479d40000d3110c58c620001f240000753db8dbc4946fdf181221bd1bf8babcafc094d39843624b4f1bd94788e50000301f27058ba44660001d1c00001cbad8d40001cb7c9a0000112c9496087342b1e5fc000692a7a4184bc0003cb6104800008ce8000836e72b000000004ba957fac930000000000032f1d0c5f23803d80003cc7f335832c00041eb71de067000079ea03d822d80006835233dc7b4000503a49700000c4954b3e03560ee879104993000000ca4c8413189253f4d991d6d9efc5524075090b051280a447e014c0b40002c53d17800000003087800049dcf396a1f60ddc21ce1e00000000c184d3a800010e900000002470685e000000000fce531d04d437148021dfa8eb66e0885a4dcc079f0884aed1f8a07f03f400048a0c17702b26451117000023d544a295bd262b1104c298208b0682f2a90bc6c892731940004027c8c7e48b20da14a721000022af8000a0aba186c8304f34bf3d2f1010999f71ddc1630d934f49b00a6426e20000ba30000346f80002008000286d7464e2870608cd2f4bd0000000000079ba000016f80000000c1b0927000058c90000621f8bdd037d1e733d6e3ba082eb7a822fc11b17a4025122e838d138d3a5455745d7d272283a5b30a161e2fbc083eee308503f1f327572e1d893ab8060bf20f01f2f24f1236696b1c5c011c48ce4cc036ec0165a90e8d530a234e13e83da05241e285f24e4111831e1b51523991c2f327f39d252c456c941f6502004db6000187980000000b0ee948800000005357678ca7800000000c6b8c1c882ea0386539ecf301100000001cc8f1fcd38e83fde75ecf1abe2f41a87118c0000190aeec2f1fa000000020518000e2c9022a2c680007281149409be19b209c000000000006885379cc5500000233e3d1c4249a92102f5834c300000144561000064237b7e00024b30000193794a64558000f061f2c306a10d07278000222619776930d7158ee717e0000000062f800081daa581caffc2419bb1128eda70027a4975bb8ff388e6b8f)
def hashrestrictedl10 (i : Nat) : Nat := 0x3152b8edb964ef3fc0c002b256fa5d1f878a5d56740ea51c00022340dc4b0003eac9d5d400034d790510dc3c33ad4d0068cfa54001d0b28349000000028fd024f40021a241478b668000000001477eb62bc002881a5da7ace99448e01871c5990982c65871cf9d2f86b194c5fc400c91340004a92c29a5821daad648c28861ca11953c15e698c6e253a761981b76a800224763097b968001588202eeaef5917ad12ca0445b0d624b699e17cca2e5869d4db060a6c71f89b576931cd3c481bc45192bcfecad02fcbbce7eb208fc78418c4ec10acc8584024ed827ad8c3689f94815a526513438b200000000034f2c1c91c00197045400023c0018bc002228c8ba964c4003c7f5ae16de0982a13b1cf40912358e097e240012c6831a900002189a4bd0790f1b806700364004104b99f041082101206060007acd0010810466420400010000c0002
def restrictedd9 (i : Nat) : Nat := (if i<1 then 0x1a30c230c230c020c23080128141000884160711871185118416842b0371056085608000a42010200000000000000000000000000000000000007800f800b8008000f001078008000078008000000000001e002000000000000000000388e0f7ede774dbf6ad9760d6f56d4741cf32cc7317c4b0dc2303bfaf9bd2efbaae5b56c5ad6a5a56909d6709825090230882107d5e5755d072dbb6ada66859c65d926358860d7e5e5745bd6a5956056d565454c51d424f5384cd2e4a52447d1a455053d4e5380db358c6304b12b0a72889d2348820c7e1e4741bc6a1946016c4b118410f0370c82d0a023078190500f028050029ff5da70cc04f4ffaed3a66027aefd769c32a13f57d784e19509e3ff5db50c984f5f7aed3864c27ebbaf09c32613d7debb6a19309faeebc350c984f5fdaed3846427ebeaf09c23213d7fabb4e10909f5ee9c35014a6b57faed3825d258ffb704d26e92e5fda825c394972febd2714ca4b1ffaeda864c25f3daf0942ae91fdcd784a13748fde69c2509aa474ffaed5866023a7fd76ad33011d5febb5619708ebfb5dab08c8475feaed58424238ffb7054a6b1155ecb7695290e2abf5daf0ca84f577aed7864c27cbbaf15532613d5f6bb5e11909e6f75da541c4ef1fe42c9a5e135b79a564c2709ac5fc9b69c384962fedd0704ba4b56f6d03825d25abda561c12e92d5f90b0e097497da69c2509aa4b5d726d374d525fa9a6e93a6a92f55c970e535496ee6db874942477f146c3a4a123f39af09426e91c5fcab9dd9548e2febdd54caa4747f6dc5a66023a5fb6c2d33011d3dd3b1699808e9fa8d8b4cc0474fe42c5a660238bfb742c32e11d5dd3b1619708eabedb8b0ca84755f6dca865423acfb6c5432a11d75d3b2a19508ebb695950ca8475dd46ca865423aef2165432a11d5bdb71619408eb5edb0b0ca0475e74ec5865023af5a562c32811d5f5b71611908eb7adb0b08c8475f54ec5846423afca562c23211d7f10b1611908eafcdb8b0848475be6d85842423afb2762c21211c7f9ab1610908ebf4958b0848475fc46c5842423b3bb702ba6f19ddcd2b15d378ceeec858ae9bc673f3aed2a1623397bd76d40af19cbdebb6a0278cf6aebc34a13c67ad7a21a509e33dbaaf08d04f19ebd688468278cf5ed4421413c67a77a20a7496339bb9573ba4b19cddd7baa9258ce2febd9532ac4537baeda7226229f9d769d0b1114deebb69c3888a7b75db4a1c44573b6d8389de22badb6a1c4ef115dadb40e27788aef28d8713bc4577a42c389de229bdaf654cab115d6d7b2a65588aeb6db8752ac457da6c03a95622badb6e1c4ab115f2db40e25588afb4858712ac457736dc898ce22bf8b6244c67115dcdb71623388af66db0b119c457f146c588ce22bf92162c4671179ce889de3388bda7444ab19c45f539de558ce22 else 0x490802b042484000000000)
def restrictedl9 : Packing := (118,4,7,0,1,10,0,restrictedd9)
def restrictedd10 (i : Nat) : Nat := (if i<2 then (if i<1 then 0xefdd2a16233bf72a5288cfbdc894a233ff30a5288cefdeaa4a233ef75e1288cefdda50a233bf72a6888cfbdd78a2233ef7562888cfbdd28a2233ef72a6888cfbdc7aa2233ef716a888cfbdc2aa2233bf76a1578cfddd7855e33bf76a0578cefdda849e33ef7a21278cfddd7809e33bf76a0278cfbde8809e33bf72a6778cfddd789de33ef7a22778cfddca99de33f77226778cfddc8a9de33f77562778cfddd289de33f77a22778cefdca949633fd7165258cefdda849633ff34a1258cfbde8849633bf769d258cfddca749633fd755d258cffcd2749633f779dd258cefdeaa49633bf76a0258cfbde8809633b7f69c5888aefda616222bef5285888afdd3a16222bfb4a85888aff51a16222bfe4285888a7fca94e222efb4e12888a7fca9a2222efb4a28888b3fca9a22229ff2a53588afeda849622efba212588bf6d35496229ff2a65588bf6d2595622bfb6a12388bbee8848e22bfb6952388bfcd288ce22ef7a223388bfcd258ce22bfb6948988afeda322622bfb6a05988afeda316622bfb6a03988afeda50e622bfbaa97888afeca956222bfbaa95888bbed7856222bfb4e85888afeca94e222efb2253888afeeaa4e222bfb69c3888afeda50e222bfb2a68888bbed78a2222efb5628888bbed38a2222efb2a68888bbec59a2222efb0e68888bbec5aa2222efb0ea8888afeda855e22f7b5e15788bbee8855e22bfb6a13788bded784de22efba213788afeeaa4de22f7b5627788bded389de22f7b0e27788bdee889de22bfb2a53588bf6c594d622bfb6a13588bf6d584d622ff34e13588bbee884d622bfb69d3588bfcd374d622f7b9dd3588afeeaa4d622bfb6a03588bbee880d622bfb2a65588bf6d5895622efba225588bf6d3595622fdb2a65588bf6c8a95622fdb0ea5588bf6d3895622fdb0e25588bf6d3795622ff34e23388bbee888ce22ff34de3388bdee778ce22ff34d63388bf6e558ce22ff32263388bfcc598ce22ff322a3388bfcc5a8ce22ff35e23388bfcd588ce22ff31623388bfce888ce22ff355e3388bfce558ce2297faa9970e27eeaa4a4388ffaa99809f57d7865427d775e19309e7deaa64c27d7d5e11909edbda40e277b7b4a8389dedf90a0e27797f26a774965fd7aa65258ffaa99808e77eaa65423bf5468788ceddda716233bb7698588cefcd2a16233bf5468588cefd90a16233af76a0578ceedda615e33bf34a8578cefd51a15e33bf6428578cebdda809e33bb7698278cef5da509e33bf5468278cefd90a09e33e77a22778ceddca749633bb7698258cededa722622bf96848988adeda716222bbb6985888afad4a16222bf34e85888afe51a16222bfa4285888adeda70e222bbb6983888af6da50e222beb6903888afe51a0e222bfa4283888b9ee889de22f5b9de5588bbce888ce22f739de3388bf4e558ce22 else 0x7b7f69c3849eefda60e127bdf6943849efbda40e127bfb4a83849eff51a0e127bfe4283849edfeaa4dd27b7faa97809e7feaa66027cff4e19809f3fd3a66027cffaa99809f77d3865427d7f5e19309e7fda864c27df74e19309f7dda864c27dfd4e11909f7f938424279ff2a5389dedfda70e277bef690389defed2a0e277bfe428389dedfda84de77b7f6a0399dedfca94e277b7faa9389dedfd2a0e2779ff269784d73fd9826135b7f69c984d6efda626135bfb4a8984d6ff51a26135bfe428984d7f5c5a4e135bf7aa9384d7bdc984e1359ff269284d7bdd384a135d7f5e1974d67feaa65d35bf76a1374d7ddd784dd35bf7aa9374d7ddd3749d35f774e2774d6efda60a535dfb4a4294d67fd8aa65359ff5ea994d67fd2aa6535df74e2994d77dd37a6535d7f9de994d73fd984a0359ff6a1290d77ed284a4359ff26938496dfda70e1259ff6a438496fbda40e125bfb4a838496ff90a0e1259ffaa9974975fd3825d25d7f0e0974967fc9a4dd25f7b4dd27496dfc9a9dd25d7f25d394975fc970e525df74e439496dfd7aa6525d7f25e994967fd7aa6525d7f5ea994967fd3aa6525dfb49e994975fe77a6525fd74e135497f6d284d525bdf69d35497d7c974d525fd74dd35497f6d274d525f5f9dd35497f6c2a4d525bdfaa935497f5c394d525ddfa65354967fda864c25df74e1930967feaa661239ff6692848ffcc3a4a123bfbaa92848fbed784a123efb4e12848e7fda865d239ffaa99748fddd784dd23ff34a13748efdeaa4dd23d7f6627748fded289dd239ff6a19548f7ed28655239ff69d9548f5fca765523df74dd9548f5fe77655239ffaa99548e7fd9a49523dfb4a29948f7dd37a6523d7f9de9948e7fd9a160239ffaa99808f3fd5866023cff1619808f3fd5a66023cff1699808f3feaa66023d7f5619708f5fc5865c239ff6a19508f77d5865423ddf1619508e7feaa65423ddf6a19508f77ca865423ddfaa99508f7bd5865023def1619408f7f55846423dfd1611908f7f95842423dfe1610908e7fca95e233bf74e8788ceff51a1e233b7f69c588ceefda616233bf74e8588cefed2a16233bfd468588ceff90a162339ff2a5288cfbdd384a2339ff2a6888cfbdd38a2233aff6a0578ceefda615e33bf74e8578cefed2a15e33bfd468578ceff90a15e33bf76a1378cfddd784de33f7715d378cfddd3749e339ff2a6778cfddd379de33d7f2a6778cfddd389de33bf76a1358cff5d584d633bf769d358cfdde774d6339ff2a5258cedfca749633fd74d5258cefdda848e33ff34a1238cefdda748e33f779dd238cefdda548e33bf769c898cefdda522633bf7688898cefdda81e633bf76a0598cefdda216633bf76a0298cefdda50a633bf72a5788cfddc795e233bf7aa9788cefdca956233fd7165588cefdeaa56233ef75e1588c) else (if i<3 then 0x30e3d38b8e1f3840e0137c8de33750dc536d8da73660d8935e8d613548d4334d0d253458cfd33b8cdf3368cd53340ccb3318cc132c8ca33228c7b31b0c673138c3f3098c173048c0d3020c032ff8bf92fd0bef2f80bd12ee0b9f2e68b8b2df0b632d28b452cd8b272c38aeb2b20aa52a08a692918a2327d89e727389c926e8997262097925a8951250893324b891f246891524188f723a08d923288bb22b089d223887f2198857212083920a881b20307fd1fe07f31fb87e91f907df1f687d51f187ad1ea07991e0077b1db07671d887531d3873f1cc07211c206ef1ba86db1b086bd1ab869f1a6868b1a1868119f067719c866d19a064f1928645190063b18d863118b0627188861d183860918105eb17985e117705c316a8591156852314284d312e84a11220465109040b0fc83cf0ed839d0e1036b0d483390c582fd0b902cb0ac828f09d825d091022b08481ef07581b30668181057814504b011303e80e103200af025807d019004b00c80190002ffeaa5e538bffaa9294e37fd794a538dff565294e37fd590a538bff694294e37fd79a6538dff4a6994e37fc7aa6538dff0aa994e2ffd5a26137bffaa9384df7fd984e137f7f5e1384df7fd38a6537dff6693849effeaa4e127bff6943849fdfd384dd27dff6693809effeaa4e027f7f5e13809f7fd3a66027dff4e19809effeaa4e277bff4a8984d6ffeaa4e135ff75e9384d7fdc9a4e135ff74a9384d7fdc2a4e135ff7aa9384d7fdd384a135dff4e1974d6ffda84dd35f7f5e1374d7fdd384dd35bffaa9374d7fdd284dd35bff6a1274d7fdd3849d35f7f4dd274d77fd980a535ff74e0294d6ffda80a535dff4e2994d77fd28a6535dff4de994d77fd27a6535dff66938496ffeaa4e125dff4e197497dfd3825d25ffb4e127496ffda80e525dff4e299497f7d384d525dff66938096ffeaa4e025bffaa97848f7fc5a66123dff5e19848effeaa4e123dff6613848ffec5a4a123ffb5e12848ffed384a123f7f5e15748f7fd9855d23ffb4a15748f7fd5865d23dff4e19748effda84dd23f7f5e13748ffdd384dd23ff75613748f7fd3865523bff6a13548ff7d584d523dff6613548ffdd384d523ffb4a13548effda74d523dff65d3548ffdd374d523bffaa93548f7fd78a6523dff5629948f7fd57a6523bffaa95808f7fd5a66023dff5619808effeaa5e233bffaa9588cfbfd7856233bff6a1578cfdfd7855e33bff6a0578ceffeaa56222bff4e85888affeaa4e222bff6a13588bf7d584d622ff74e13588affeaa4d622d7f5e4794e37ed290a5389ff5ea994e27fd2aa65389ffaa9970e35fd2a65c38d7faa9970e37eda74a438dfb695290e27feaa66137cff660984deff51a26137e7f261784de7fd9a4e1379ff62a994de7fd5aa65379ff4aa994df5fd78a65379ffaa9980de7fda90e12 else (if i<4 then 0x620b02410380083800c161e00200d80e144216098320e03170010183c0040544502e003c007800f001e003c0078009501e003c007800f001e003c0048f83c5c007800f001e003c0048380c5c00780080000000678780091f078b800f001019ea78b80099f060b80080000000007001e00254450223e0f103800f00120e03111f07881c00780099f0608c41041419880e1723334b403466267e0a0c360105918a00a0cc40533f1a7e1d88c07120308a007081c004160502d1c5018a0301843603849407800822808009407800f001e003c007800f001e003c00780091f078b800f001e003c007800f001e0020000000001c0048f83c40e00245c1620700100026083800f001e00245c16223e0f10380091f07881c0078008380080000000023d031000000000000046040040c8c1000093a0b149d058a188e4424c0d0c04e1c95ce81a1809c392c311c88ce81a1809c39299c4588ce22c44599c20443f0e46140ac16a51cbf1068fe0b147f0588ce2fcb9199c5c88ce2e44671722338b911726708bf24c467950498cbf24c45f926224cbf11305c88cf20cb919305c88982e445c9302e5f88117e5c88cf20cb9199dc4082833b88199c5c88ce2e445899c460cce2e446717222e4ce119c4588ce22c46711623388b119c45888b3385cbf102e5f88172fc40b97e205cbf102b01abedaf7abc5aedab9dae12b6bad72b4dacd2b1bac5ab07abbaae9ab42ab7aaa2aa3aa02a71a9b2a5da912a2ba84aa03a7d29dba6e299fa61a977a5a294fa502927a43a8eba34a8b9a282873a16a841a0a280f9fda7e79f3a7b59e4a7799d5a73d9c9271f9bf26e39b7a6cf9ada6b19a3a67f99c26619922639988261197e25df96f259995da55d953a535944a50393d24e5935a4bd929248b91ca44f912a43b908a4098fea3e18f4a3b98e823878dba3558d1a3238c2a3058c022dd8aea2a18a2226f895a23387f21f7872a1c5868a18985c2157852212584320f3836a0c182a208f81da05d813a0358049ff97f81fbd7e91f777d79f457cb1f137be9ed77af9e9b79e1e557919e3778a1e197829ddd7761dbf7671d797581d3d74e1d297469ccf7211c6b7121c257031bfd6f91bcb6ea1ba36dd9b5d6ce9b2b6c71b0d6bd1adb6ae1a9569c9a4f68d9a0967999cd66d1991659194b64f192364018fb63618bf629988d61d1865615983360698015f797c55eb17935de976b5d7174d5cd171b5b916cb5b196b75a7967b596163f587160357d15e557315b3566958155a154554d951353c14e153494c3528147d519144150a14054f893c94e9938d4d8133d4c9130b4ba12cf4ab128949c124d48d121147911d546c918f45b1149449910343810b3426907741c90454088fff3f70fb93e58f873de0f693d40f373cc8f233c78f0f3c00ef13bb0ed33ac0e973a20e7939a8e6539 else 0x582a8a06140454040420c50584361244d1848200804108c11482160642c8c24100050848160800204c2050071406100052788e333c2080c391848205007161e0809310a1e143e4e10162486c301446121e248a310c6210502414621c3c10106e1688140cc071a1e2b081401c467c18243ccf030492028248810050402092204014100808092308081b08040d840880e248e0f15841b00e248c3601050180e200052788e3010061012808040208067a19278e0b080a12c4202562242c20205828a020105a280c2d12070185a328e230dc622446038c04008402840403c447a07018c490a5012c4294040201040240c281804140c020a4f0404b18203080a1208050404588405154458870b1544010082c0c141004020802010403848f1220f18040208000600f118610846230c2c0ac41601c20b02b1058070a446742d18581e0aa0b0565019dc40ac161000482a1b8c220b0419858209c0e14161118188c461601c24a0351650070b2803859401c24a00e1250070b2803840304cf93c402028280e188e450c47220c05063c71cc30209f970e60624311c8a188e450c47228623914311c893ee203718581208c40683a18941662a34544a0b07c007800f001e003c00448010570508015814132e2b0283e045605062b0282e04141586002c2060424b3c0c13f0c1401438182786e67a1803892711037109820c62303c560dc62b06e202c254078243e0f119e540283004601029cb90320ac41189c0a0c0b08161e0020285a20882d100b0285a3147880d861be3a168c2e1241b18a6168845317150b486203e168c3603851fc7220401b0c071f8581bf1040c42d10081a7856127e08516302720d822304804105a12081103841b00e200c294040715b88180e2b0802158501c0c2b0c560dc4038ac240e0312062b080608ac140c31fc26284e3f10480e021c001c50802f10003085bcb880533c2d182bc406a30b00414061bf1030b788100c1e00285c1620b8191088168b971304210ac208c290dc7c004241301b18880c972300c3018780099e8606c31183186071fc162e5e0c0e071fc162e5e0c0e061c08cca8e3f82c5cbc181c0c1a0ec40340cca8764e5e0c0e060a02020683b172f0607030501010971fc163e5e0c0e071fc162a5e0c0e071fc162833970e07cba162a85a4e002250598a8cb1140141e462802833133f05066201c218f231401419880a67e308c480540e21070188180c4461803d128bd0b08251460e0c57c0c141e9c5881c315d030507a7172160f800c161830241c0)))
def restrictedl10 : Packing := (515,3,7,7,1,14,0,restrictedd10)
def restrictedd11 (i : Nat) : Nat := (if i<1 then 0x40b1f899d0bcbe2090b58aa32f882b3a5197c411623fc40d1f28cbe209280365f1048001fe07eb9f857d4df337be1ec6799de3e7879df57731dac75a1d4874a1cf67335c8970cdbf86f61b8b6d89b396c41ae76af9a716945a3168219df66d998d654990562bd86b61098195fe57d05ec17875d317115b7d6b65a5963758155c1561953053d54b15245456506d3d74e713734cbd2f44ac127548a11f646ed17744850cb428907940f90153fd4fcc3eb0f713d20f043b24ea039dce2137bcdc6362cd6234e4d1032e8c6d3110c092f38b9c2da8b412bf4acb2a88a79291ca15278c9b1264497a256893a248c8f1232089621b483b20487e01f007971ddc74e1c946f31b28698199863418505e217085ab165056b14e451013784b5120c46c110c4110fc43bf0e343640cec3120ba42c90aa42800980240088020007801c9068018905c815204ec12404340f6033409b01c805200a4000ffebca71ffc794e3ffa529c7ff0a538fff4ca71ffd984dfff9309bfff5e137ffe9c26fffd594dfffa529bfffa6537ffe9c24fffc3849fffa7013fff4e277ffe1c4efffd784d7ffb309afff26135ffe9c26bffd284d7ffb2e9afff4dd35ffe93a6bffd294d7ff8529afffa6535ffe9406bffd38497ff87092fff65d25ffe9ba4bffd39497ff87292fffa6525ffe9aa4bffd38097ffaf091fff56123ffecc247ffd3848fffa5091fff55d23ffecba47ffd3748fffb2a91fff4d523ffe92a47ffd5808fff8b011fff5e233ffe3c467ffd588cfff8b119fff4a233fff44467ffd578cfff8af19fff49e33fff3bc67ffd258cfffab1117ff16222ffe9c445ffe8888bffa6b117ff95622bff4ca717fd970e2ffa521c5ff66137efebc26f7fe994deffb301bf7f4dd27efebc04f7fd9809effb2613f7f4de77efe1ccefdfd389dfbf8713bff74e135bfecba6bfdd374d7bfcee9adffa6535bfecc06b7fd290d6ffb2e92f7f25d25ff693a4bdfe77496ffd3292fdf4d525bfec984b7fd9848ffda5091dff65d23fee9ba47dfe7748effb2a91dffa6523bfecc0477fd9508ffba7119ff74de33eff3bc67fdd358cffba4719ff722633fee3cc67fdc598cffb85319ff75e233fee3c467fdd588cffb8b119ff74a233fee14467fde888cffbaaf19ff715e33fee93c67fdc278cffbcef19ff749633fee12c67fed2888b7fd11117fb49622ff691c45fde3388bfd913117fb16622ff61cc45fed7888bfdab1117fb16222ff69c445fec3888bfdd11117fb55e22ff69bc45fed3588bfd86b117fb95622ff719c455fd970e2f7b281c5fb4a438bfc848717f9090de7fb3013dbf65827bbeca84f7bd9409efbb2613dfd46427bfc8484f5fc97496f7b2812cff66023afecb8476fd9608eefb2a11def65023bfa8c8477f90908f7bd1119f779de33df744445dee7788bedcab117f38ce22 else 0xb1546232e4232fd72347aa3102dcb941846862fc8b12201b10512b3b103718319d0cc0158586059399d0b1b94482847b389d0f940b711975338a83915107e33160c0b23198b088f87e227e49422c3634a93c188c0333e727234fe723670b272341c0f2e56c4150797248ec80c09c4f2f0c2b050e1018a0d9c4e98c0f2e0b4850a1971695b106541507236720e9d03188b72e0b40429cbf1c9072989c95880c862fc28402c3cac142123119716914637919180e56cbe210ce260b46391b06c623518dc5a41c952722d20fc6c1bc4100436878b481805926308b1c992a4827831180667ce500647810485687c1b103f481853060815711973a551e2f03116397c40188b920018604242e47e41f8b0083168ff1006233c7f3fc00bc0c667afa9e1003620cce1f8280d80293c213f85906ccf860c0c832a8c5630316c2e0d9750160ace162e4a2d543209128cbc2ce0741b39630386192605829399c0341c4c5a958a0d9d3181c2cc832465d7303858b4ec8862fc68fa72fe1f0b07199c83a72c6070b33380b05a704d262d392116c885e227e61b1463093223d9e4f87947113f3a3d16ce87c2e506675391e0f0a4ff1076722e9cb985c0cc0f1302e9c4685e5f108240dc0c4e059450a8271200d88303c04ce858df2f883938168f81b3a1637cbe2124805892622d85ca32f884918623f0590662c1fe2084f67c1a30271c98a0060c0e4997030e46ce028fc724188fd1634789916cecbe20d2311b391642703d9c5687e5f107221255197858e4c56cb8dc724a740f2e392110040b98958290bcbe212481881b2e0b29232e061c9088052481c7e3931240e3f1c90ac071f8e494e858fc724220140656988b60797c42416032b0b51703cbe21048cb81872407b385b28cbe20c4e670b40d97c4189033160ff105160dc523fc4169d0f1fe20844141585b28cbe20e489465c0d88283c8c3f059088491f82c8b1419132e0b2b3906b1cb82cb4e87aa32f0b2b39508fcb82cb97036206ce05880abf5c8d6397060d7e0b101962cecbe20a05672fd724032c59d97c414190c672e48b10333b2f8828159cbfc411628385b3b10502e5d723064317e9320157f88183218985c919d0b5fae48ce032c72f88283218985c911e44030ff1056743e173fc4159c8f030ff1051f81b103a743e7e06c4159c28c40c30b910fd162478187f88201962cecbe20a0381b39724588199d97c41407036722c8b10340d9d8828fd7226723c7f8823380cb1cbe20b97032e46ce0340f2eb92b39639703620a4803138164240189c0b21200c4e0590900b03138831058fc6060c0e464f0300c724030607231886018303060723030607231c8183031f8e4448078fc1841f82c43f05889e28058c7e0b10fc1621f82c)
def restrictedl11 : Packing := (176,2,7,10,1,14,0,restrictedd11)
def restrictedd12 (i : Nat) : Nat := 0x3ca1382e5e20c900c9c1644e310b2897883189f858cc4fe2060c307234e0b3f39227019885cbc41920c41a5c2ca9c1662512f10648061839227079405834bc41cfc2c49c1e500d2e1664e0f0b063f88318944bc4102e5e206512f103ab68894e36865fc75da25d54046cde3249417c3a07400ffd38ffc38ffd37ffc37ffd27ffc27ffe77ffd35ffc35ffd25ffc25ffd23ffc23ffe33ffe22dfe77fde33fee22
def restrictedl12 : Packing := (18,1,7,8,1,10,0,restrictedd12)
def restrictedd13 (i : Nat) : Nat := 0x2e205ff
def restrictedl13 : Packing := (1,0,7,5,1,0,0,restrictedd13)
def restrictedsamples : Array (Bits × Bits) := #[(0x2453cb22a70c5210332d0323c4f091816008074685802218b0a040a85951203063c7820104a00f4044043c0602103430189d328898110230252a1a6191091910c502400a210d1b4342404213601a4179a0a93080184c00604b808838014ab4c0,0x84128080840952001208020380d091886008062614812210808040a8305120204205020002a00e0040803c0202102130188110809050921021000841098909008000200a21081b40424040122002416980a910801848002049008038014aa440),(0x38010540050a06740823408020148308f61f898520749c00206114422a45c041810382a7111a00398010040dd85c2c526408c5726262906d880208a40048627203c90b40c6000b0851c396005a40e024054013342210f0090374147b0214101,0x30050440000a12440023000220000308e40a080424609800044204402245c041000b83040018013180000518c848205240004142600200dc88120840004002020388234086000b08010386001a40e00401001334021070010350107b0014100),(0xe954138d16845cf0809c381bcb25b8406312488e2a15e5a88e390bb438c73756cd651d5dc0be5191c164c22c934de58064809b70398e12c2329e6270c5f2098d1f128854d5145c554c44a51c436c70628da1b449233338c61c80c4c88a458e05,0x685c0791148440500214091b4121a8000112410c2401e4280a100198280223524524040d0028512003642020116110808082994001060400121e0250c48208041f020c00d5145c054404851c404840420da0b440221228c60c8044400a448401),(0x85270525d40a6c09749a92e59c0c63aee160045320f00a46ddbcfce3812b9150562263c4b6d09c8360d8c5103c0c0a29d54c43b6144438c50f1929d0223a671b289950b8a18b49403b7214a61aa1aa08288d4d244898f212615402abd8906134,0x942200200008240930889060188441a8606000410070024394a28c0481211020120000c094900e084498c0000c1420085164028714403841050120000018631b008840b0208b01401b4210820aa0a208200d412408085000215402abc0106014),(0x4c090356ee92181ea517e38363793336c7875b054734f3e4eac1054a481cc37929e0f5256c6cf777a0f78b7898c5d45cf1ca845c0c2146a180081eb7336124b42cf70846b4f88003a09f9be1701f594e14122e57a285a277bd1118002e3453e2,0x4009031663968806814725886229260681157908430691a42a4501430808431929e0dd24680ea173a06603781083d4c4a00a805849210480c04816b6b26204c42637004494708003a09d8b61501d180614122e53a285a257940118002e2413a2),(0x187a486011fd20dd6eb1403434a7465c1bdbe8c1e15c153e1f7b0250891a679bb3404362492885293643168343a2908288713cc6d324e527cd33850ecc862651d94acb814ce7e09f3811c812040006963f10ef91b8080d08a2d53f92cf46a009,0x12484020116400532c91c0101424463003d36801c0541028337a8a0001221492a1604542000081012663020000a090808070004400060d2704108008c406065518ea0a8004c5609f38118800040002122b00ef11a0000c00a2902f82ce040001),(0x286a13a9ae4e707b0fcc4b105629749446e552ed8261c4530b29b8ab601892e079c5586941d3c06dfd7afe064592064ab960b8d5ad43d7eb06406037d26fc6e832c2cc336416f65e18b01478e4b0251d16646623d428c03a5ea2aed23388496,0x4466211a82440403a8b5c4a114461dc86006450e9000047530b29e88b001a12a0114450014183c44c6dbe6086059205299040bc958c41d6204348243792a654c11020cc334016b45610b01078e4b0051916446003d028803a5c22ae803308096),(0xf03632c8e85288ac990e2cf6aa92c54cccc2b6869960911646040052c3d78aa7d8953090a90a619ab1729a3f6efea7031e08a01a4818e6586b656c194b4c11829401734d2a32116cc02b7a292ae210ad901fd10eada5d3a40466b111510c2a2a,0x80209040a81a888c900a0424a292014e5404948219a001964484004244d5c82508803090a102289ad810885f6a1e2d431708201aec09e25868612c811b09518a8000704d2a220160802a72212aa210ad901f000e0da5d3200066901111082a2a),(0x888ae064ca397c1d040714a93422195181dc4314c898f2b5955e28316254eca290edeec1384e8b4121a30e329930e2d0226759821f183d898c6b39524d95ae0a24cbd285320b78092a4a628f884c425472a02d844c3610d4029463236c9175a,0x8809e056c8191804042290ac1180005180800300e812900480520030644424108029a04030540b0100010e101020e2002032410213982889842019402c110208204b1084320940080a4262870044424440200c840c1210c4029401030c91748)]
def restrictedcolumns : IndexTree ColumnInfo := (.fork 44 (.fork 22 (.fork 11 (.fork 5 (.fork 2 (.leaf [(1,0,510,0,12),(2,0,509,0,12)]) (.leaf [(5,0,506,0,8),(6,0,505,0,9),(2,4,369,136,7)])) (.fork 3 (.leaf [(9,0,486,0,8),(14,0,497,0,7),(10,4,369,128,6)]) (.leaf [(17,0,494,0,11),(18,0,493,0,9),(18,4,353,136,6)]))) (.fork 5 (.fork 2 (.leaf [(25,0,486,0,8),(9,16,486,0,8)]) (.leaf [(13,16,482,0,5),(26,4,353,128,5),(33,0,478,0,9)])) (.fork 3 (.leaf [(1,32,94,384,7),(37,0,346,0,5),(39,0,344,0,4)]) (.leaf [(49,0,462,0,8),(57,0,454,0,5),(65,0,446,0,9)])))) (.fork 11 (.fork 5 (.fork 2 (.leaf [(1,64,188,258,7),(66,0,445,0,11)]) (.leaf [(70,0,441,0,8),(66,4,305,136,6),(78,0,433,0,5)])) (.fork 3 (.leaf [(74,4,305,128,5),(14,64,177,256,5),(81,0,430,0,8)]) (.leaf [(82,0,429,0,8),(89,0,422,0,5),(97,0,414,0,6)]))) (.fork 5 (.fork 2 (.leaf [(98,0,413,0,7),(113,0,398,0,5)]) (.leaf [(129,0,382,0,9),(1,128,346,36,7),(130,1,332,48,6)])) (.fork 3 (.leaf [(133,0,378,0,7),(5,128,346,32,6),(134,0,377,0,8)]) (.leaf [(130,4,369,8,6),(6,128,345,32,6),(7,128,344,32,5)]))))) (.fork 22 (.fork 11 (.fork 5 (.fork 2 (.leaf [(142,0,369,0,5),(138,4,369,0,5)]) (.leaf [(145,0,366,0,8),(146,4,353,8,5),(153,0,358,0,5)])) (.fork 3 (.leaf [(161,0,350,0,8),(129,32,94,256,6),(33,128,346,4,6)]) (.leaf [(162,0,349,0,7),(35,128,344,4,5),(165,0,346,0,5)]))) (.fork 5 (.fork 2 (.leaf [(37,128,346,0,5),(166,0,345,0,5)]) (.leaf [(177,0,334,0,7),(161,16,326,8,5),(145,32,78,256,5)])) (.fork 3 (.leaf [(49,128,330,4,5),(193,0,318,0,7),(194,0,317,0,8)]) (.leaf [(198,0,313,0,7),(194,4,305,8,5),(70,128,281,32,5)])))) (.fork 11 (.fork 5 (.fork 2 (.leaf [(210,0,301,0,5),(225,0,286,0,5)]) (.leaf [(257,0,254,0,8),(273,0,238,0,7),(281,0,230,0,5)])) (.fork 3 (.leaf [(265,16,230,0,5),(289,0,222,0,7),(257,32,94,128,6)]) (.leaf [(305,0,206,0,5),(289,16,198,8,5),(273,32,78,128,5)]))) (.fork 5 (.fork 2 (.leaf [(321,0,190,0,7),(322,0,189,0,8)]) (.leaf [(258,64,189,0,8),(326,0,185,0,5),(330,0,181,0,5)])) (.fork 3 (.leaf [(266,64,181,0,5),(337,0,174,0,5),(321,32,30,128,5)]) (.leaf [(417,0,94,0,5),(385,32,94,0,5),(450,0,61,0,5)]))))))
def restrictedautos : Array (List Nat) := #[[],[100,131,82,16]]
def restrictedlevels : Nat → Packing
  | 9 => restrictedl9
  | 10 => restrictedl10
  | 11 => restrictedl11
  | 12 => restrictedl12
  | 13 => restrictedl13
  | _ => emptyPacking
def restrictedindex : Nat → Nat → Option (Nat × Nat)
  | 9 => fun _ => none
  | 10 => lookupWord 55 190 6 12 7 1 (hashrestrictedl10)
  | 11 => lookupWord 252 872 9 15 10 1 (hashrestrictedl11)
  | 12 => lookupWord 84 301 7 13 8 1 (hashrestrictedl12)
  | 13 => lookupWord 10 37 5 10 5 1 (hashrestrictedl13)
  | _ => fun _ => none
def restricted : Forest := ⟨1023,13,fun j => restrictedsamples[j]?.getD (0,0),restrictedcolumns,restrictedautos,restrictedlevels,restrictedindex⟩
set_option maxHeartbeats 0 in
theorem geomrestricted : graphValid restricted (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted9_0 : block restricted 9 0 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted9_36 : block restricted 9 36 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted9_72 : block restricted 9 72 19=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted9_91 : block restricted 9 91 27=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allrestricted9 : block restricted 9 0 118=true := (@block_merge restricted 9 0 91 27 (@block_merge restricted 9 0 72 19 (@block_merge restricted 9 0 36 36 srestricted9_0 srestricted9_36) srestricted9_72) srestricted9_91)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted10_0 : block restricted 10 0 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted10_36 : block restricted 10 36 16=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted10_52 : block restricted 10 52 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted10_88 : block restricted 10 88 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted10_124 : block restricted 10 124 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted10_160 : block restricted 10 160 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted10_196 : block restricted 10 196 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted10_232 : block restricted 10 232 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted10_268 : block restricted 10 268 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted10_304 : block restricted 10 304 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted10_340 : block restricted 10 340 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted10_376 : block restricted 10 376 34=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted10_410 : block restricted 10 410 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted10_446 : block restricted 10 446 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted10_482 : block restricted 10 482 33=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allrestricted10 : block restricted 10 0 515=true := (@block_merge restricted 10 0 482 33 (@block_merge restricted 10 0 446 36 (@block_merge restricted 10 0 410 36 (@block_merge restricted 10 0 376 34 (@block_merge restricted 10 0 340 36 (@block_merge restricted 10 0 304 36 (@block_merge restricted 10 0 268 36 (@block_merge restricted 10 0 232 36 (@block_merge restricted 10 0 196 36 (@block_merge restricted 10 0 160 36 (@block_merge restricted 10 0 124 36 (@block_merge restricted 10 0 88 36 (@block_merge restricted 10 0 52 36 (@block_merge restricted 10 0 36 16 srestricted10_0 srestricted10_36) srestricted10_52) srestricted10_88) srestricted10_124) srestricted10_160) srestricted10_196) srestricted10_232) srestricted10_268) srestricted10_304) srestricted10_340) srestricted10_376) srestricted10_410) srestricted10_446) srestricted10_482)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted11_0 : block restricted 11 0 27=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted11_27 : block restricted 11 27 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted11_63 : block restricted 11 63 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted11_99 : block restricted 11 99 9=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted11_108 : block restricted 11 108 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted11_144 : block restricted 11 144 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allrestricted11 : block restricted 11 0 176=true := (@block_merge restricted 11 0 144 32 (@block_merge restricted 11 0 108 36 (@block_merge restricted 11 0 99 9 (@block_merge restricted 11 0 63 36 (@block_merge restricted 11 0 27 36 srestricted11_0 srestricted11_27) srestricted11_63) srestricted11_99) srestricted11_108) srestricted11_144)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted12_0 : block restricted 12 0 3=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted12_3 : block restricted 12 3 15=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allrestricted12 : block restricted 12 0 18=true := (@block_merge restricted 12 0 3 15 srestricted12_0 srestricted12_3)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted13_0 : block restricted 13 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allrestricted13 : block restricted 13 0 1=true := srestricted13_0
theorem tablesrestricted : checkedTables restricted 13 := by
  intro k hk
  interval_cases k
  · exact (rfl : block restricted 0 0 0 = true)
  · exact (rfl : block restricted 1 0 0 = true)
  · exact (rfl : block restricted 2 0 0 = true)
  · exact (rfl : block restricted 3 0 0 = true)
  · exact (rfl : block restricted 4 0 0 = true)
  · exact (rfl : block restricted 5 0 0 = true)
  · exact (rfl : block restricted 6 0 0 = true)
  · exact (rfl : block restricted 7 0 0 = true)
  · exact (rfl : block restricted 8 0 0 = true)
  · exact allrestricted9
  · exact allrestricted10
  · exact allrestricted11
  · exact allrestricted12
  · exact allrestricted13
theorem restricted_start {prior : Nat → Nat}
    (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid restricted prior=true) (checks : checkedTables restricted 13) :
    Impossible clippedGraph 13 clippedInputs.toFinset := by
  have noRun := root_index (g:=restricted) low geometry checks (k:=13) (by decide)
    (i:=0) (ws:=clippedInputs) (by decide +kernel)
  have tgt : targetOf restricted=clippedGraph := by decide +kernel
  exact tgt ▸ noRun

end PEqualNP.Outside.L_meta_3020.Search
namespace PEqualNP.Outside.L_meta_3020.Search
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem seedCutFromLower (low : Lower (inputs++[seed]) graph 15)
    (tag : Nat) (h : tag ∈ [3073,3077,3090,3107,3128,3160]) :
    Slice (vars 511 ++ [bin false (inputs.getD ((tag-3072)/16) zero) (inputs.getD ((tag-3072) % 16) zero)])
      (graphGoal 511) (subcube 0 0) 15 := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact seedPairSlice 0 1 [] low (by decide +kernel) (by decide +kernel)
  · exact seedPairSlice 0 5 [118,130,81] low (by decide +kernel) (by decide +kernel)
  · exact seedPairSlice 1 2 [118,133,100,131,50,33,16] low (by decide +kernel) (by decide +kernel)
  · exact seedPairSlice 2 3 [118,116,83,130,49,32] low (by decide +kernel) (by decide +kernel)
  · exact seedPairSlice 3 8 [82,129,48] low (by decide +kernel) (by decide +kernel)
  · exact seedPairSlice 5 8 [116,50,129,80] low (by decide +kernel) (by decide +kernel)
end PEqualNP.Outside.L_meta_3020.Search
namespace PEqualNP.Outside.L_meta_3020.Search
theorem signedSeedCut (tag : Nat) (h : tag ∈ [3073,3077,3090,3107,3128,3160]) :
    Slice (vars 511 ++ [bin false (inputs.getD ((tag-3072)/16) zero) (inputs.getD ((tag-3072) % 16) zero)])
      (graphGoal 511) (subcube 0 0) 15 :=
  seedCutFromLower (seedFloorViaClip (dead_start (before_sound known383 valid383) geomdead tablesdead)
    (restricted_start (before_sound known383 valid383) geomrestricted tablesrestricted)) tag h
end PEqualNP.Outside.L_meta_3020.Search
namespace PEqualNP.Outside.L_meta_3020.Search
open PEqualNP.CircuitLowerBounds

def orFirst : Sig := bin true (inputs.getD 0 zero) (inputs.getD 2 zero)
def orPre := inputs ++ [orFirst]
def orArg (i : Nat) : Sig := if i=11 then one else orPre.getD i zero
def orSecond (a b : Nat) := bin false (orArg a) (orArg b)
abbrev OrProfile := Nat × Nat × Nat × List Nat
def orBuf (p : OrProfile) := orPre ++ [orSecond p.1 p.2.1]
def orMust (p : OrProfile) : List (Sig × Row × Row) :=
  (List.range 9).filterMap fun j =>
    let v := (p.2.2.1 >>> (10*j)) % 1024
    if v=0 then none else some (inputs.getD j zero,Fin.ofNat 512 (v-1),Fin.ofNat 512 (v-1+2^j))
def orMustWords (p : OrProfile) := (orMust p).map Prod.fst
def orOptions (p : OrProfile) := ((orBuf p).filter fun w => properB w && !(orMustWords p).contains w).eraseDups

def orPicks : Nat → List Sig → List Sig
  | _, [] => []
  | m, a::xs => if m % 2=1 then a::orPicks (m/2) xs else orPicks (m/2) xs

def orSelection (S : Finset Sig) : List Sig → Nat
  | [] => 0
  | a::xs => 2 * orSelection S xs + if a∈S then 1 else 0

theorem orSelection_lt (S) (xs) : orSelection S xs < 2^xs.length := by
  induction xs with
  | nil => simp [orSelection]
  | cons a xs ih => simp only [orSelection,List.length_cons,Nat.pow_succ]; split <;> omega

theorem orSelection_picks (S) (xs) : orPicks (orSelection S xs) xs = xs.filter (·∈S) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [orSelection,orPicks,List.filter_cons]
    by_cases h : a∈S <;> simp [h,Nat.mul_add_div,ih]

theorem orLiveProper {T k t S} (h : Live T k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

def orRootRule (g : Forest) (ws : List Sig) (r : Nat) : Bool :=
  if r % 2=1 then
    let a := Fin.ofNat 512 ((r/2)%512)
    let b := Fin.ofNat 512 (r/1024)
    (bit a graph != bit b graph) && ws.all (fun w => bit a w == bit b w)
  else match linkedSet g 13 ((r/2)%64,r/128) with
    | some v => sameWords v ws
    | none => false

def orProfileCheck (g : Forest) (p : OrProfile) : Bool :=
  checkEssential graph (orBuf p) (orMust p) && (List.range (2^(orOptions p).length)).all (fun m =>
    orRootRule g (orMustWords p ++ orPicks m (orOptions p)) (p.2.2.2.getD m 0))

theorem orProfileSound {g : Forest} (target : targetOf g=graph)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (known : ∀ i < (g.levels 13).1, Impossible (targetOf g) 13 (stateSet g 13 i).toFinset)
    (p : OrProfile) (hc : orProfileCheck g p=true)
    {k t S} (run : Live graph k t S) (small : k≤13) (sub : ∀ a∈S,a∈orBuf p) : False := by
  simp only [orProfileCheck,Bool.and_eq_true] at hc
  have mandatory : ∀ a∈orMustWords p, a∈S := by
    intro a ha
    obtain ⟨r,s,diff,iso⟩ := essential_ok hc.1 a (List.mem_toFinset.mpr ha)
    exact raw_required run _ _ sub r s diff iso
  let m := orSelection S (orOptions p)
  let ws := orMustWords p ++ orPicks m (orOptions p)
  have same : ws.toFinset=S := by
    ext a
    simp only [ws,m,orSelection_picks,List.mem_toFinset,List.mem_append,List.mem_filter,decide_eq_true_eq]
    constructor
    · rintro (h|h); exact mandatory _ h; exact h.2
    · intro h
      by_cases hm : a ∈ orMustWords p
      · exact Or.inl hm
      · right; refine ⟨?_,h⟩
        simp only [orOptions,List.mem_eraseDups,List.mem_filter,Bool.and_eq_true,properB,bne_iff_ne,
          Bool.not_eq_true']
        exact ⟨sub a h,orLiveProper run a h,by simpa using hm⟩
  have hc' := List.all_eq_true.mp hc.2 m (List.mem_range.mpr (orSelection_lt _ _))
  change orRootRule g ws _ = true at hc'
  unfold orRootRule at hc'
  split at hc'
  · simp only [Bool.and_eq_true,bne_iff_ne,List.all_eq_true,beq_iff_eq] at hc'
    obtain ⟨a,ha,diff⟩ := live_row_difference run hc'.1
    exact diff (hc'.2 a (List.mem_toFinset.mp (same ▸ ha)))
  · split at hc'
    next v eq =>
      have impossible := linkedSet_sound g 13 names known eq
      rw [target,sameWords_sound hc',same] at impossible
      exact impossible k t small run
    next => contradiction

end PEqualNP.Outside.L_meta_3020.Search
namespace PEqualNP.Outside.L_meta_3020.Search
def orProfiles : List OrProfile := [
(0,0,0x901403008020140a00815,[0,2]),
(0,1,0x901403008020140a01415,[0,2,4,28]),
(0,2,0x901403008020140000800,[2055,2061,2055,0,9241,9243,20523,2,2055,2061,2055,6,9241,8,520,30]),
(0,3,0x901403008020140a00815,[0,2,10,32]),
(0,4,0x901403008090140a00825,[0,2,12,34]),
(0,5,0x901403204020140a00815,[0,2,132,36]),
(0,6,0x901403008020140a00815,[0,2,14,38]),
(0,7,0x901403008020140a00815,[0,2,142,40]),
(0,8,0x901403008020140a00815,[0,2,134,42]),
(0,10,0x901403008020140a00815,[0,2]),
(1,1,0x901403008020140a00815,[0,2]),
(1,2,0x901403008020140a00815,[0,2,388,540]),
(1,3,0x901403008020140a00815,[0,2,390,44]),
(1,4,0x901403008020140a00815,[0,2,270,46]),
(1,5,0x901403008020140a00815,[0,2,262,556]),
(1,6,0x901501008020140a00815,[0,2,268,48]),
(1,7,0x901403008020140a00815,[0,2,398,558]),
(1,8,0x901403008020140a00815,[0,2,266,50]),
(1,9,0x901403008020140a10415,[0,2,16,52]),
(2,2,0x901403008020140a00815,[0,2]),
(2,3,0x901403008020448200815,[0,2,644,548]),
(2,4,0x901403008020140a00815,[0,2,654,552]),
(2,5,0x901403008020140a00815,[0,2,522,544]),
(2,6,0x901403008020140a00815,[0,2,526,550]),
(2,7,0x908403008020140a00815,[0,2,524,546]),
(2,8,0x901403008020140a00815,[0,2,646,554]),
(3,3,0x901403008020140a00815,[0,2]),
(3,4,0x901403008020140a00815,[0,2,780,54]),
(3,5,0x901403008020140a00815,[0,2,902,56]),
(3,6,0x901403008020140a00815,[0,2,910,58]),
(3,7,0x901403008020140a00815,[0,2,782,60]),
(3,8,0x2101403008020140a00815,[0,2,900,62]),
(3,9,0x901403008020440a00815,[0,2,18,64]),
(4,4,0x901403008020140a00815,[0,2]),
(4,5,0x901403008020140a00815,[0,2,1038,572]),
(4,6,0x901403008020140a00815,[0,2,20,66]),
(4,7,0x901403008020140a00815,[0,2,148,68]),
(4,8,0x901403008020140a00815,[0,2,1294,70]),
(4,9,0x901403008090140a00815,[0,2,22,72]),
(5,5,0x901403008020140a00815,[0,2]),
(5,6,0x901403008020140a00815,[0,2,1166,570]),
(5,7,0x901403008020140a00815,[0,2,1036,566]),
(5,8,0x901403008020140a00815,[0,2,1156,574]),
(5,9,0x901403204020140a00815,[0,2,530,576]),
(6,6,0x901403008020140a00815,[0,2]),
(6,7,0x901403008020140a00815,[0,2,404,578]),
(6,8,0x901403008020140a00815,[0,2,1292,74]),
(6,9,0x901403008020140a00815,[0,2,24,76]),
(7,7,0x901403008020140a00815,[0,2]),
(7,8,0x901403008020140a00815,[0,2,1422,582]),
(7,9,0x908403008020140a00815,[0,2,534,584]),
(8,8,0x901403008020140a00815,[0,2]),
(8,9,0x901403008020140a00815,[0,2,26,78]),
(9,9,0x901403008020140a00815,[0,2]),
(11,11,0x901403008020140a00815,[0,2])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem orProfilesPass : orProfiles.all (orProfileCheck orPack) = true := by
  apply listPieces_all (d:=3)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem orProfilesCover : ∀ a b : Fin 12, orProfiles.any (fun p => orSecond p.1 p.2.1 == orSecond a.val b.val)=true := by decide +kernel
end PEqualNP.Outside.L_meta_3020.Search
namespace PEqualNP.Outside.L_meta_3020.Search

theorem orPairs : properPairs (targetOf orPack) (asRow fun j => (orPack.samples j).1)
    (asRow fun j => (orPack.samples j).2) := by
  have h := geomdead
  simp only [graphValid,Bool.and_eq_true,beq_iff_eq] at h
  exact chart_pairs h.1.1.1 h.1.1.2

theorem orAutos : ∀ x ∈ orPack.autos.toList, autoOK (targetOf orPack) (x.map swapRows)=true := by
  have h := geomdead
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true] at h
  exact h.2

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem orRawFloor : Lower (vars 511) (graphGoal 511) 15 :=
  lower_forest (g:=dead) (i:=0) (hints:=13438558465) (before_sound known383 valid383)
    geomdead tablesdead (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def orBaseColumn (c : ColumnInfo) : Bool := decide (c.2.2.1<1024) &&
  (c == (0,0,0,0,15) || dead.cols.values.contains c)

def orSeedTags : List Nat := [3073,3077,3090,3107,3128,3160]
def orSeedColumn (tag : Nat) : ColumnInfo := (0,0,tag,0,15)
theorem orSeedMarkerHigh : ∀ tag ∈ orSeedTags, tag ≥ 3072 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem orBaseCheck : orPack.cols.values.all (fun c => (orSeedTags.map orSeedColumn).contains c || (c == (2,0,2050,0,12) || orBaseColumn c))=true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem orColumnsSoundWith
    (special : Slice (vars 511 ++ [bin true (inputs.getD 0 zero) (inputs.getD 2 zero)])
      (graphGoal 511) (subcube 2 0) 12)
    (signedSeedCut : ∀ tag ∈ orSeedTags,
      Slice (vars 511 ++ [bin false (inputs.getD ((tag-3072)/16) zero) (inputs.getD ((tag-3072)%16) zero)])
        (graphGoal 511) (subcube 0 0) 15) : ∀ c ∈ orPack.cols.values,
    Slice (chartRaw orPack.mask c) (targetOf orPack) (subcube c.1 c.2.1) c.2.2.2.2 := by
  intro c hc
  have h := List.all_eq_true.mp orBaseCheck c hc
  simp only [Bool.or_eq_true] at h
  rcases h with seedCase | chosen | h
  · obtain ⟨tag, ht, rfl⟩ := List.mem_map.mp (List.contains_iff_mem.mp seedCase)
    change Slice (chartRaw 511 (0,0,tag,0,15)) (graphGoal 511) (subcube 0 0) 15
    simp only [chartRaw,orSeedMarkerHigh tag ht,ite_true]
    exact signedSeedCut tag ht
  · have eq : c = (2,0,2050,0,12) := beq_iff_eq.mp chosen
    subst c
    exact special
  simp only [orBaseColumn,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,beq_iff_eq,List.contains_iff_mem] at h
  rw [chartRaw,if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  rcases h.2 with rfl | old
  · exact slice_correct (ms:=[]) (base:=vars 511) (G:=graphGoal 511) (by decide +kernel)
      (by decide +kernel) (proper_of _ (by decide +kernel)) orRawFloor
  · have h := geomdead
    simp only [graphValid,Bool.and_eq_true,List.all_eq_true] at h
    exact col_sound c _ (before_sound known383 valid383) (h.1.2 c old)

end PEqualNP.Outside.L_meta_3020.Search
namespace PEqualNP.Outside.L_meta_3020.Search
theorem orColumnsSound : ∀ c ∈ orPack.cols.values,
    Slice (chartRaw orPack.mask c) (targetOf orPack) (subcube c.1 c.2.1) c.2.2.2.2 :=
  orColumnsSoundWith (deletionOneSlice miniTables) signedSeedCut
end PEqualNP.Outside.L_meta_3020.Search
namespace PEqualNP.Outside.L_meta_3020.Search
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem orR9_0 : signedBlock orPack 9 0 56=true := by
  apply signedCellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem orR9_56 : signedBlock orPack 9 56 51=true := by
  apply signedCellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
theorem orLayer9 : signedBlock orPack 9 0 107=true := (@signedBlock_merge orPack 9 0 56 51 orR9_0 orR9_56)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem orR10_0 : signedBlock orPack 10 0 8=true := by
  apply signedCellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem orR10_8 : signedBlock orPack 10 8 216=true := by
  apply signedCellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem orR10_224 : signedBlock orPack 10 224 216=true := by
  apply signedCellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem orR10_440 : signedBlock orPack 10 440 71=true := by
  apply signedCellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem orR10_511 : signedBlock orPack 10 511 216=true := by
  apply signedCellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem orR10_727 : signedBlock orPack 10 727 216=true := by
  apply signedCellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem orR10_943 : signedBlock orPack 10 943 12=true := by
  apply signedCellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
theorem orLayer10 : signedBlock orPack 10 0 955=true := (@signedBlock_merge orPack 10 0 943 12 (@signedBlock_merge orPack 10 0 727 216 (@signedBlock_merge orPack 10 0 511 216 (@signedBlock_merge orPack 10 0 440 71 (@signedBlock_merge orPack 10 0 224 216 (@signedBlock_merge orPack 10 0 8 216 orR10_0 orR10_8) orR10_224) orR10_440) orR10_511) orR10_727) orR10_943)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem orR11_0 : signedBlock orPack 11 0 92=true := by
  apply signedCellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem orR11_92 : signedBlock orPack 11 92 216=true := by
  apply signedCellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem orR11_308 : signedBlock orPack 11 308 216=true := by
  apply signedCellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem orR11_524 : signedBlock orPack 11 524 179=true := by
  apply signedCellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem orR11_703 : signedBlock orPack 11 703 216=true := by
  apply signedCellsBlock (ar:=12) (rows:=0) (d:=2)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem orR11_919 : signedBlock orPack 11 919 68=true := by
  apply signedCellsBlock (ar:=12) (rows:=0) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
theorem orLayer11 : signedBlock orPack 11 0 987=true := (@signedBlock_merge orPack 11 0 919 68 (@signedBlock_merge orPack 11 0 703 216 (@signedBlock_merge orPack 11 0 524 179 (@signedBlock_merge orPack 11 0 308 216 (@signedBlock_merge orPack 11 0 92 216 orR11_0 orR11_92) orR11_308) orR11_524) orR11_703) orR11_919)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem orR12_0 : signedBlock orPack 12 0 7=true := by
  apply signedCellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem orR12_7 : signedBlock orPack 12 7 56=true := by
  apply signedCellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem orR12_63 : signedBlock orPack 12 63 43=true := by
  apply signedCellsBlock (ar:=12) (rows:=0) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
theorem orLayer12 : signedBlock orPack 12 0 106=true := (@signedBlock_merge orPack 12 0 63 43 (@signedBlock_merge orPack 12 0 7 56 orR12_0 orR12_7) orR12_63)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem orR13_0 : signedBlock orPack 13 0 1=true := by
  apply signedCellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem orR13_1 : signedBlock orPack 13 1 13=true := by
  apply signedCellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem orR13_14 : signedBlock orPack 13 14 26=true := by
  apply signedCellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [signedCells,signedBoxes,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub]
  repeat' apply And.intro
  all_goals decide +kernel
theorem orLayer13 : signedBlock orPack 13 0 40=true := (@signedBlock_merge orPack 13 0 14 26 (@signedBlock_merge orPack 13 0 1 13 orR13_0 orR13_1) orR13_14)
theorem orTables : signedTables orPack 13 := by
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
  · exact orLayer9
  · exact orLayer10
  · exact orLayer11
  · exact orLayer12
  · exact orLayer13
end PEqualNP.Outside.L_meta_3020.Search
namespace PEqualNP.Outside.L_meta_3020.Search
open PEqualNP.CircuitLowerBounds

def orGate (xs : List (Fin 11)) : Gate := ⟨.and,xs.map Fin.val⟩
def orBit (xs : List (Fin 11)) := gv orPre (orGate xs)
def orRowBase (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 2]
def orActual (xs : List (Fin 11)) (x : Fin 9 → Bool) := orRowBase x ++
  [GateOp.and.eval (xs.map fun j => (orRowBase x).getD j.val false)]

theorem orShape (xs : List (Fin 11)) (short : xs.length≤2) :
    ∃ a b : Fin 12, orBit xs = orSecond a.val b.val := by
  have arg (a : Fin 11) : orArg a.val = orPre.getD a.val zero := by
    simp [orArg,show a.val≠11 by omega]
  have unit : orArg 11=one := rfl
  cases xs with
  | nil =>
    refine ⟨11,11,?_⟩
    change one = bin false (orArg 11) (orArg 11)
    simp [unit,bin,one]
  | cons a xs =>
    cases xs with
    | nil =>
      refine ⟨a.castSucc,11,?_⟩
      change bin false (orPre.getD a.val zero) one = bin false (orArg a.val) (orArg 11)
      rw [arg,unit]
    | cons b xs =>
      cases xs with
      | nil =>
        refine ⟨a.castSucc,b.castSucc,?_⟩
        change bin false _ (bin false (orPre.getD b.val zero) one) = bin false (orArg a.val) (orArg b.val)
        simp only [arg,bin,one,Bool.false_eq_true,ite_false,BitVec.and_allOnes]
      | cons c cs => simp at short

theorem orInitBits (r : Row) : orPre.map (bit r) = orRowBase (sample r) := by
  simp only [orPre,orRowBase,List.map_append,List.map_singleton,sampled]
  simp [orFirst,bit,bin,sample]

theorem orEval (xs : List (Fin 11)) (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C) (i : Nat) (r : Row) :
    bit r ((execute C.gates (orPre++[orBit xs])).getD i zero) =
    (C.wires (orActual xs (sample r))).getD i false := by
  have head := execute_bits [orGate xs] r orPre (by
    intro g hg
    simp only [List.mem_singleton] at hg
    simp [hg,orGate])
  change List.map (bit r) (orPre++[orBit xs]) = orPre.map (bit r) ++ [_] at head
  have rowEq : (orPre++[orBit xs]).map (bit r) = orActual xs (sample r) := by
    simpa only [orGate,List.map_map,Function.comp_def,orInitBits,orActual] using head
  rw [←b_read,execute_bits _ _ _ (fun g hg => (legal g hg).1),rowEq]
  rfl

theorem orMismatch (rows : signedTables orPack 13) (xs : List (Fin 11)) (short : xs.length≤2)
    (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C) (small : C.size≤13) :
    ∃ x : Fin 9 → Bool, C.eval (orActual xs x) ≠ edge x := by
  by_contra! computes
  have out : (execute C.gates (orPre++[orBit xs])).getD C.output zero=graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (orEval xs C legal C.output r).trans ((computes (sample r)).trans (edge_table r).symm)
  rw [List.getD_eq_getElem?_getD] at out
  have hm : graph∈execute C.gates (orPre++[orBit xs]) := by
    cases h : (execute C.gates (orPre++[orBit xs]))[C.output]? with
    | none => simp only [h,Option.getD_none] at out; exact False.elim (graph_proper.1 out.symm)
    | some v => simp only [h,Option.getD_some] at out; exact out ▸ List.mem_of_getElem? h
  obtain ⟨k,t,S,hk,run,sub⟩ := extract C.gates (orPre++[orBit xs]) legal graph_proper hm
  obtain ⟨a,b,hab⟩ := orShape xs short
  obtain ⟨p,hp,eq⟩ := List.any_eq_true.mp (orProfilesCover a b)
  have hval : orSecond p.1 p.2.1=orBit xs := (beq_iff_eq.mp eq).trans hab.symm
  have target : targetOf orPack=graph := by decide +kernel
  apply orProfileSound target orAutos (signedForest orPack 13 orPairs orColumnsSound orAutos rows 13 (by omega))
    p (List.all_eq_true.mp orProfilesPass _ hp) run (hk.trans small)
  simpa [orBuf,hval] using sub

end PEqualNP.Outside.L_meta_3020.Search
theorem PEqualNP.Outside.L_meta_3020 :
∀ (x1 : List (Fin (11 : ℕ))),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin (11 : ℕ)) => x7.getD (↑x8) Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro xs short C legal small
  exact PEqualNP.Outside.L_meta_3020.Search.orMismatch PEqualNP.Outside.L_meta_3020.Search.orTables xs short C legal small
