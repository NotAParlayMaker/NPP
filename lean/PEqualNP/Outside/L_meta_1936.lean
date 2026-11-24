import PEqualNP.Defs

-- The circuit normalization, finite exclusions, and subgraph bounds are
-- adapted from L-meta-1920 and PressF10’s proof in PR 4332.
namespace PEqualNP.Outside.L_meta_1936
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
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

lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
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

lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp

lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
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

lemma gate_rep (w : List Sig) (g : Gate)
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
lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
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
lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]

lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

lemma run_bit (i) (g : Gate) (w : List Sig)
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
def seed4 : Sig := neg (inputs.getD 4 zero)

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed4_table : ∀ r : Row, bit r seed4 = !(sample r 4) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem seed4_nonzero : seed4 ≠ zero := by decide +kernel
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
def vertex (m j : Nat) := if m.testBit j then (if m.testBit 9 && j == 4 then neg (inputs.getD 4 zero) else inputs.getD j zero) else zero
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

def supportPairs (baseRow mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,Fin.ofNat 512 baseRow,Fin.ofNat 512 (baseRow ^^^ (1 <<< i)))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  let base := if m.testBit 9 && m.testBit 4 then 16 else 0
  (selected m).map fun (i,a) =>
    let r := base ^^^ (1 <<< ((hints >>> (4*i)) &&& 15))
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ^^^ (1 <<< i)))

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
def colFree (m z o : Nat) := (m &&& 511) ^^^ ((m &&& 511) &&& (z ||| o))
def chartGoal (m : Nat) : Sig := graphGoal m
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let baseRow := if m.testBit 9 && free.testBit 4 then 16 else 0
  let xs := supportPairs baseRow s
  let count := (xs.map Prod.fst).toFinset.card
  let drop := colFree free q 0
  let lz := if m.testBit 9 && drop.testBit 4 then drop &&& (511 ^^^ 16) else drop
  let lo := if m.testBit 9 && drop.testBit 4 then 16 else 0
  properB G && checkMap ms (vars m) (chartGoal m) (vars free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (vars free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows lz lo) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice (vars m) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  obtain ⟨z,o,q,s,L⟩ := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let baseRow := if m.testBit 9 && free.testBit 4 then 16 else 0
  let xs := supportPairs baseRow s
  change (((properB G && checkMap ms (vars m) (chartGoal m) (vars free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) _ hh.1 p bank hr ha)
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


abbrev BoundPool := Sig × Nat × Nat × List Sig
def BoundPool.domain (p : BoundPool) := p.1
def BoundPool.bound (p : BoundPool) := p.2.1
def BoundPool.paid (p : BoundPool) := p.2.2.1
def BoundPool.wires (p : BoundPool) := p.2.2.2

def ValidPool (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach (roots.map observe) q ws → Available ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach (roots.map observe) c.paid bank ∧ poolSupply f bank c.wires ∧ True

theorem build_valid {raw T d lb} (h : Slice raw T d lb) (cs : List Choice) {ws}
    (build : makePool d raw cs = some ws) : ValidPool raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [BoundPool.paid] using hr,hs,trivial⟩

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


abbrev Bits := BitVec 192
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 192 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 192 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 192 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 192 → Row) (x : Decor) := x.2 = pairSig r s x.1
def dneg (x : Decor) : Decor := (neg x.1,~~~x.2.1,~~~x.2.2)
def dbin (d : Bool) (x y : Decor) : Decor :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)

theorem ofRows_neg (r : Fin 192 → Row) (a : Sig) : ofRows r (neg a) = ~~~ofRows r a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (neg a) ⟨j,hj⟩
  rw [bit_neg,←ofRows_bit r a ⟨j,hj⟩] at h
  simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
theorem ofRows_bin (r : Fin 192 → Row) (d : Bool) (a b : Sig) :
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

def asRow (cols : Nat → Bits) (i : Fin 192) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 192) (j : Fin 9) :
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
  let x := fun j => if m.testBit j then (if m.testBit 9 && j == 4 then ~~~(v 4) else v j) else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 192) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then (if m.testBit 9 && j.val == 4 then ~~~(v 4) else v j.val) else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · by_cases hf : (m.testBit 9 && j.val == 4) = true
    · have hj4 : j.val = 4 := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hf; exact hf.2
      simp only [vertex, hh, hf, ite_true, bit_neg, BitVec.getLsbD_not, i.isLt, decide_true, Bool.true_and]
      exact congrArg Bool.not (asRow_bit v i ⟨4, by decide⟩)
    · simpa [vertex, hh, hf] using asRow_bit v i j
  · simp [vertex, hh, bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 192) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then (if m.testBit 9 && j == 4 then ~~~(v 4) else v j) else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
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

theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
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
  pools.any (fun p => scalarPoolCut p k rest op) || (links (keySet ws)).any (sameWords ws)

theorem closeChild_sound {raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨p,hp,ok⟩ | ⟨xs,hx,ok⟩
  · exact scalarPoolCut_sound (pValid _ hp) nd ok
  · rw [sameWords_sound ok]
    exact lValid _ _ hx

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
    if (rs ||| column d z.2) != BitVec.allOnes 192 then true else
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
  change covered (decide (child.length = cap)) (pairSig r s) child = BitVec.allOnes 192 at sep
  rw [deq] at sep
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 192) = false := by simp [sep]
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


abbrev IndexTree (α : Type) := List α
def IndexTree.leaf {α : Type} (items : List α) : IndexTree α := items
def IndexTree.fork {α : Type} (_ : Nat) (left right : IndexTree α) : IndexTree α := left ++ right
def IndexTree.read {α : Type} (tree : IndexTree α) (i : Nat) : Option α := tree[i]?
def IndexTree.values {α : Type} (tree : IndexTree α) : List α := tree
theorem IndexTree.read_mem {α} (tree : IndexTree α) {i x} (e : tree.read i=some x) :
    x ∈ tree.values := List.mem_of_getElem? e

abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × IndexTree ColumnInfo ×
  Array (List Nat) × (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (g : Forest) := g.1
def Forest.cap (g : Forest) := g.2.1
def Forest.samples (g : Forest) := g.2.2.1
def Forest.cols (g : Forest) := g.2.2.2.1
def Forest.autos (g : Forest) := g.2.2.2.2.1
def Forest.levels (g : Forest) := g.2.2.2.2.2.1
def Forest.index (g : Forest) := g.2.2.2.2.2.2

def wiresOf (g : Forest) :=
  rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a :=
  raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) := liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 192) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val :=
  bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 192) (hq : chartSamples m q = 0) :
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

def storedDepth (g : Forest) (depth : Nat) := if g.mask.testBit 10 then depth - 1 else depth
def restorePlan (g : Forest) (bits : Nat) :=
  if g.mask.testBit 10 then (bits <<< 10) ||| 512 else bits
def ruleCountWidth (g : Forest) := if g.mask.testBit 10 then 4 else 5
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := packedAt data (i*width) width
  let stored := recp &&& ((1 <<< len)-1)
  let ops := restorePlan g stored
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
  let nr := packedAt data pos (ruleCountWidth g)
  let st := pos+ruleCountWidth g+lw
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
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 192) &&
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
def lanePlace (v : Nat) (upper : Nat) := 2^193*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^193 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<193 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<193 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<193 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
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

def fullMarks (r packed : Nat) := ((packed+r) >>> 192) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (193*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^193)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 193*(i+1)-193=193*i := by omega
      have ge : ¬193*(i+1)<193 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 192 = (a==BitVec.allOnes 192) := by
  by_cases h : a=BitVec.allOnes 192
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^192-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^192 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (193*i) =
      (f xs[i]==BitVec.allOnes 192) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^193*u+x+(2^193*v+1)=2^193*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^193 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬193*(i+1)+192<193 := by omega
      have di : 193*(i+1)+192-193=193*i+192 := by omega
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
theorem top_xor (a : Bits) : BitVec.allOnes 192 ^^^ a = ~~~a := BitVec.allOnes_xor
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp (units xs.length*(BitVec.allOnes 192).toNat) op
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
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 193) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (193*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
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
      apply ih (mask:=mask >>> 193) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs,packedCov (fun c => c.2.2.2.1.2) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

def fallbackAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  let z := (movedDecor op a b).1
  !properB z || c.2.2.1.any (fun v => v.1 == z) ||
    closeChild c.2.2.2.2.1 c.2.2.2.2.2 (c.1 - 1)
      ((opKeep (op==2) ka kb a b c.2.2.1).map Prod.fst) (movedChoice op a b)

theorem fallback_sound {c i j op ka kb} (h : fallbackAt c i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  unfold fallbackAt at h
  rw [Bool.or_eq_true] at h
  rcases h with invalid | closed
  · simp only [checkAt, evalMove, invalid, ite_true]
    split_ifs <;> rfl
  · simp only [checkAt, evalMove, closed]
    split_ifs <;> rfl

def batchMove (b : Batch) (xs : List NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,u,v) := b
  let un := op==2
  let len := 1+(n-(if ka then 0 else 1)-(if un || kb then 0 else 1))
  if len>k then true else
    let d := len==k
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp (r*(BitVec.allOnes 192).toNat) op a b'
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
      if len>k then true else if combField xs[q] d (op==2) ka kb op i j != BitVec.allOnes 192 then true
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
        packedColumn d (packedOp (r*(BitVec.allOnes 192).toNat) op a b))) xs) = true at pass
    rw [if_neg small] at pass
    have chosen : cov = packedCov (fun c => getCov c.2.2.2.1 d) xs := by
      dsimp only [cov]
      cases d <;> rfl
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,chosen,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] d (op==2) ka kb op i j = BitVec.allOnes 192
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
  let nr := packedAt data pos (ruleCountWidth g)
  let st := pos+ruleCountWidth g+lw
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
def g15samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffff1,0xfffffffffffffffffffffffffffffffffffffffffffffff9),(0x16,0x4),(0xffffffffffffffffffffffffffffffffffffffffffffffef,0xa),(0xffffffffffffffffffffffffffffffffffffffffffffffe9,0xfffffffffffffffffffffffffffffffffffffffffffffff5),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
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
def g31samples : Array (Bits × Bits) := #[(0x2ad2,0x18c2),(0xffffffffffffffffffffffffffffffffffffffffffffc3a5,0xffffffffffffffffffffffffffffffffffffffffffffe305),(0x1876,0x72),(0xffffffffffffffffffffffffffffffffffffffffffffdfc9,0xffffffffffffffffffffffffffffffffffffffffffffde81),(0xffffffffffffffffffffffffffffffffffffffffffffe53f,0x213c),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
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
def g47samples : Array (Bits × Bits) := #[(0x7dd35b9ce7bbffd6b6b7b7cfbb8d3b7ad85ddf257b56b575,0x800c00803812181c2009c1061c0107200c09440143143444),(0xcb8ab173daa7df7f7691aff9776b2b7dcb92a3f3678b2b59,0x34a38448020d64a21d120601022ea84882b022a624830919),(0xf3ffe6e3dd55f86b6fffcab66472f7c57fb768dabfad4eae,0x8440806b120004c020121a4ec1002247c020840112806a4),(0x576de696b3cff805db7d426c00d8ded437ed436ff6f66c92,0x57a950700411b6b328381c4110e8d4580325370f22d66812),(0x0,0x0),(0xacd4afec26dbb6d98eabb3768bb508ca4b7f1fdd1c709a3f,0x52a26637058ca3a012d22680c12e48c8e17411561c608a3b),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g47columns : IndexTree ColumnInfo := (.leaf [(8,0,39,0,4)])
def g47autos : Array (List Nat) := #[[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index⟩
def g55samples : Array (Bits × Bits) := #[(0xfbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400701010180030103060043200102204010904888),(0x94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0x6a4e002420468a8a43140a00408d944460a4082569431231),(0xe4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x10206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0x0,0x0),(0xafa7a64bb677ab40beba463600362eda36f3357b7d763926,0xacc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0x5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xa549861b60b6727a22d48ac0b14da4445855161ae724b471),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g55columns : IndexTree ColumnInfo := (.leaf [(16,0,39,0,4)])
def g55autos : Array (List Nat) := #[[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest := ⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index⟩
def g63samples : Array (Bits × Bits) := #[(0x6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x53044a00410008802d0060013000c004400188120c206208),(0x5539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0xcc0858112c8207810e917400e423d0034024309910504e5),(0x84dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x80310832a5111106e902488a012c82618908a42202729212),(0xd2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x708e41084282480000c012150640581c30655a55288040a4),(0xd920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0xc2084761035a077101508a009ba22e00b822088521e1c51),(0x623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63columns : IndexTree ColumnInfo := (.leaf [(32,0,31,0,7)])
def g63autos : Array (List Nat) := #[[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index⟩
def g111d6 (i : Nat) : Nat := 0x120ff
def g111l6 : Packing := (1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffff9dad,0x1c24),(0xffffffffffffffffffffffffffffffffffffffffffffc953,0xffffffffffffffffffffffffffffffffffffffffffffc141),(0x36e2,0x24a2),(0x3e1c,0x5a1c),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffa2fd,0xffffffffffffffffffffffffffffffffffffffffffffe2d9),(0x421e,0x221e),(0x0,0x0),(0x0,0x0)]
def g111columns : IndexTree ColumnInfo := (.leaf [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)])
def g111autos : Array (List Nat) := #[[],[83,32]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
def g119samples : Array (Bits × Bits) := #[(0xc6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x8018000c4009400c9000c0062803a0400e00885042a10888),(0x7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x408406120184808104430800802442850101410609083421),(0xdd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x9910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0x0,0x0),(0xb7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x36011e712702bb816af81651c4b05c0701a6642cad046374),(0x10c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x2083e62199863ec06b43378157e41d3d00d937293850b261),(0x3b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0xb361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0x0,0x0),(0x0,0x0)]
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
def g189samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffff14bb3,0xd42b2),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffd5635,0xfffffffffffffffffffffffffffffffffffffffffff94225),(0xe65d8,0x60598),(0x2b866,0xb844),(0xfffffffffffffffffffffffffffffffffffffffffff385cd,0xfffffffffffffffffffffffffffffffffffffffffff2054d),(0x0,0x0),(0x4ba1e,0x4b812),(0x0,0x0)]
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
def g127samples : Array (Bits × Bits) := #[(0xd2d2abacb351593072ded0ca36876c216b176a15583d3069,0x10802b10a111102142440000168440214816081150281060),(0x8815184a3fa2b5dede495570df2830da3c38c46cf1426d13,0x880100481a02008819080040c10830122428406420422c11),(0xdf6b34450ca72f271676b8367562d5a985429aaa9a64d626,0x5722240404692506023498262462c48981029a8a9a244222),(0xafa8d659c70c9ab5dbb42b955b55e374e0f839c3068a9694,0x88809339110498f1918002911b15216460582041008a9494),(0x667be7de6cdf9480211b73e5e0fc0e1e03a683a80feb2399,0x667900c444ea04000013f960e0680e1a03a083a80f412309),(0xf6cd22629068e5bc2da9dbde283bbf115009f3b1a197a662,0x8a6c00621068c596ada8d9f5a83bbf101009f3a0a197a602),(0x59c9e36e00b68fdae413f628aa9c64ad98b04d0b38dd9ac,0x141896b3a1182c75a6e53b222aa1c648d9830490938dd1ac),(0x0,0x0),(0x0,0x0)]
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
def g191samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffff0901649528bca6895,0xa128a00508bc26084),(0xfffffffffffffffffffffffffffffff61047347514a1b071,0xfffffffffffffffffffffffffffffff02175722504019071),(0xe02c1a542bb27198a,0x71a808c421326088a),(0xfffffffffffffffffffffffffffffff0698182b92c9ed649,0xfffffffffffffffffffffffffffffff8854712992898d241),(0x16800cbac44618dfa,0x56800e92444210d3a),(0x185781a0f663d427c,0x185518e8e242d0258),(0x0,0x0),(0xfffffffffffffffffffffffffffffff9272e7035c1109323,0xfffffffffffffffffffffffffffffff8602e7031c0109121),(0x0,0x0)]
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
def g251samples : Array (Bits × Bits) := #[(0x316cf861cfcc30541d6a6cc4992b1a999615c8e8d911c1e1,0x24c060c50410001a48a084882a181106058840c1114140),(0x3e9c1117dab8cd95ebc956b7a216470f30e3a2b3ec2d18bb,0xbc8810142aa8e601010152222014470a10a222b02c2818b9),(0x0,0x0),(0xcdbb8ab0333b96f243ce283ea4988c525a6cf93575cb22d6,0xcd2ac810537252985246622c84980c521a4cf835558922d2),(0x7c52f2db3fa12e66e966315b35ec80fa603e034c2e56ad7c,0x3050168720812c4621201151314480a8603203082a468c2c),(0xe9e39f3990e7fa0a34138f4a5e417d209f607f101fc4fe09,0xe8880e0910f0e60220020e2216414120916065101cc4aa09),(0x2aa0876640524995f6a595fd43d7d81429dbe94302afe942,0x4200852245520814f6b484dd43c398142959c9430287e142),(0x82572d4ce3aa90cf64d9c30549ce2fe50b809671629a567c,0x145321c6e30c00cc44fdf181498e2ec50a809261621a5474),(0x0,0x0)]
def g251columns : IndexTree ColumnInfo := (.leaf [(8,0,243,0,7)])
def g251autos : Array (List Nat) := #[[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index⟩
def g255samples : Array (Bits × Bits) := #[(0x6270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x42400010c90428108414142154888803090a9048202086a0),(0x76974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x101041843090160043212902810201b054050081825c2101),(0xaa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x2a043c40824a60b20098024012185a048212646400810a02),(0x89eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x16b021a61259805924545098441a1c11120810b812e1184),(0xa1b45be11b7c00687be220f65622167c80c13fe90c415919,0xa89449e11258006869a220d60222163c80c12ea00c414819),(0x39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0x38b533460072d3ec490080008b50771c0014031517470802),(0xbf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xabcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x4a400915810c003602652424a380613ce19002e808a0e8),(0x0,0x0)]
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
def g383samples : Array (Bits × Bits) := #[(0x98b196c38b49cb24e,0x30c414c28b49c120c),(0x112d2f82d8cb6a69c4,0x1c118082d04b426840),(0x284389d0f21f9909a,0x284381d0e20b9809a),(0xffffffffffffffffffffffffffffffee4097fa73d4025621,0x182b83e031c4025620),(0xffffffffffffffffffffffffffffffe4d03c43822b0461b3,0xffffffffffffffffffffffffffffffe4d03c03820b002193),(0x18232e32a049a1e418,0x18232e32804120e410),(0x3e4f3d2466389928,0x2e6f3c2424289128),(0x0,0x0),(0xfffffffffffffffffffffffffffffff010c005ce1ed706d7,0xffffffffffffffffffffffffffffffe1d000014a1ad500c7)]
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
theorem s191_6_0 : block g191 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_6 : block g191 6 0 1 = true := s191_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
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
def deadsamples : Array (Bits × Bits) := #[(0x444c21378702b0db0e0814b904a9995007c262627006aac,0x62490513276021490a00143100819950058222423006224),(0xf830f9204029004936a756b0c5f0ee0a95f13040c4f80d01,0x1a6b24c000d08122070630c170e60215a11000c4f80d00),(0xf815358412022318cdc30ac7588a31b409136c8a39155671,0xf84414890900221815c020c7108a113408126c8a10055221),(0x2090c40853776228a32d74d8d11ea11f2a8d135c9748100,0x609a81270bf5002883096088c01ea01d2280015c9700100),(0xd6469c892069ef665e08b003b211622f05d7dc840f199e,0xd2478c890029e9664608b003b200622d05d5c8040f189a),(0xff0a000a49d054da210990bce928066275080053de575201,0xf80b4c8249814008251c10ace9200200750000529c571001),(0x2e190a3311f804a2c0438ad1605034cc802a05f09a9222a,0x2e19083311f024a8d00388d1405014cc002a05f0901020a),(0x6280004b2009020c140c912303160c3d2659a8962203852,0x7a00004b6009024c800c910001160c38265920162202852),(0x1820bcd24948c945229655202d754a50cd340a0124becb6,0x114036c044084b51081415202d214a008d140a00208ecb4)]
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
theorem dead_start : Impossible graph 14 inputs.toFinset := by
  have noRun := root_index (g:=dead) (before_sound known383 valid383) geomdead tablesdead (k:=14) (by decide)
    (i:=0) (ws:=inputs) (by decide +kernel)
  have tgt : targetOf dead=graph := by decide +kernel
  exact tgt ▸ noRun

abbrev DirectContext := Nat × Nat × List Decor × CovPair × (Choice → List Decor → Bool)
def directMove (c : DirectContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,close) := c
  let un := op==2
  let len := 1+(n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len>cap then true else
    let d := len==cap
    let rs := restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 192 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      close (movedChoice op a b) (z :: opKeep un ka kb a b ws)

theorem directMove_sound {T r s ws close cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (checkedClose : ∀ step ws, close step ws = true →
      (ws.map Prod.fst).Nodup → (∀ w ∈ ws, faithful r s w) →
      Impossible T (cap - 1) (ws.map Prod.fst).toFinset)
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : directMove (cap,ws.length,ws,preCov ws,close) op a b (movedDecor op a b) ka kb = true) :
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
  unfold directMove at test
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
  change covered (decide (child.length = cap)) (pairSig r s) child = BitVec.allOnes 192 at sep
  rw [deq] at sep
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 192) = false := by simp [sep]
  change (if (_ != _) then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  refine checkedClose _ _ test ndc ?_ k t hk h
  intro w hw
  rcases List.mem_cons.mp hw with rfl | hw
  · exact hf
  · exact faith _ (sub.subset hw)

def directPair (ctx : DirectContext) (a b : Decor) (d : Bool) :=
  let op := if d then 1 else 0
  let z := movedDecor op a b
  let attempt := directMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
theorem directPair_at {ctx a b d} (h : directPair ctx a b d = true) (ka kb : Bool) :
    directMove ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb = true := by
  simp only [directPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2


-- Project the available signals onto fixed-input subcubes. A bit in a recipe
-- selects a prior gate which must still be paid for inside the subcube.
abbrev Projection := ColumnInfo × Sig × List (Sig × Nat)

def searchColumns : List ColumnInfo := [
  (16, 0, 495, 0, 13), (64, 0, 447, 0, 13), (128, 0, 383, 0, 13), (1, 0, 510, 0, 12), (2, 0, 509, 0, 12), (4, 0, 507, 0, 12),
  (8, 0, 503, 0, 12), (32, 0, 479, 0, 12), (256, 0, 255, 0, 12), (17, 0, 494, 0, 11), (24, 0, 487, 0, 11), (66, 0, 445, 0, 11),
  (80, 0, 431, 0, 11), (132, 0, 379, 0, 11), (144, 0, 367, 0, 11), (160, 0, 351, 0, 11), (192, 0, 319, 0, 11), (320, 0, 191, 0, 11),
  (0, 16, 486, 9, 10), (0, 64, 189, 258, 10), (3, 0, 508, 0, 9), (6, 0, 505, 0, 9), (12, 0, 499, 0, 9), (8, 16, 486, 1, 9),
  (2, 64, 189, 256, 9), (96, 0, 415, 0, 9), (4, 128, 347, 32, 9), (136, 0, 375, 0, 9), (264, 0, 247, 0, 9), (288, 0, 223, 0, 9),
  (256, 64, 189, 2, 9), (0, 1, 460, 50, 8), (0, 2, 440, 69, 8), (0, 4, 369, 138, 8), (5, 0, 506, 0, 8), (0, 8, 227, 276, 8),
  (9, 0, 486, 0, 8), (10, 0, 501, 0, 8), (19, 0, 492, 0, 8), (25, 0, 486, 0, 8), (9, 16, 486, 0, 8), (0, 32, 94, 385, 8),
  (36, 0, 347, 0, 8), (40, 0, 471, 0, 8), (49, 0, 462, 0, 8), (67, 0, 444, 0, 8), (70, 0, 441, 0, 8), (134, 0, 377, 0, 8),
  (140, 0, 371, 0, 8), (164, 0, 347, 0, 8), (36, 128, 347, 0, 8), (258, 0, 189, 0, 8), (260, 0, 251, 0, 8), (280, 0, 231, 0, 8),
  (322, 0, 189, 0, 8), (258, 64, 189, 0, 8), (2, 1, 460, 48, 7), (4, 2, 440, 65, 7), (2, 4, 369, 136, 7), (7, 0, 504, 0, 7),
  (8, 4, 369, 130, 7), (4, 8, 227, 272, 7), (14, 0, 497, 0, 7), (16, 1, 460, 34, 7), (16, 4, 353, 138, 7), (21, 0, 490, 0, 7),
  (32, 1, 460, 18, 7), (1, 32, 94, 384, 7), (35, 0, 476, 0, 7), (56, 0, 455, 0, 7), (74, 0, 437, 0, 7), (83, 0, 428, 0, 7),
  (128, 1, 332, 50, 7), (133, 0, 378, 0, 7), (128, 8, 99, 276, 7), (198, 0, 313, 0, 7), (256, 8, 227, 20, 7), (8, 256, 151, 96, 7),
  (268, 0, 243, 0, 7), (273, 0, 238, 0, 7), (256, 32, 94, 129, 7), (32, 256, 151, 72, 7), (296, 0, 215, 0, 7), (324, 0, 187, 0, 7),
  (5, 2, 440, 64, 6), (10, 4, 369, 128, 6), (24, 4, 353, 130, 6), (34, 1, 460, 16, 6), (48, 1, 460, 2, 6), (66, 1, 396, 48, 6),
  (96, 1, 396, 18, 6), (3, 128, 344, 36, 6), (132, 2, 312, 65, 6), (132, 8, 99, 272, 6), (160, 1, 332, 18, 6), (260, 8, 227, 16, 6),
  (257, 32, 94, 128, 6), (40, 256, 151, 64, 6), (304, 0, 207, 0, 6), (288, 16, 198, 9, 6), (21, 2, 424, 64, 5), (27, 0, 484, 0, 5),
  (11, 16, 484, 0, 5), (29, 0, 482, 0, 5), (26, 4, 353, 128, 5), (50, 1, 460, 0, 5), (69, 2, 440, 0, 5), (74, 4, 305, 128, 5),
  (98, 1, 396, 16, 5), (133, 2, 312, 64, 5), (138, 4, 369, 0, 5), (152, 4, 353, 2, 5), (162, 1, 332, 16, 5), (172, 0, 339, 0, 5),
  (176, 1, 332, 2, 5), (180, 0, 331, 0, 5), (276, 8, 227, 0, 5), (273, 32, 78, 128, 5), (56, 256, 135, 64, 5), (324, 8, 163, 16, 5),
  (321, 32, 30, 128, 5), (388, 8, 99, 16, 5), (168, 256, 23, 64, 5), (224, 256, 23, 8, 5), (15, 0, 480, 0, 4), (39, 0, 344, 0, 4)]

def initProjection (c : ColumnInfo) : Projection :=
  let d := subcube c.1 c.2.1
  (c, d, inputs.map fun a => (masked d a, 0))

def projectionCode (p : Projection) (a : Sig) : Nat :=
  let d := p.2.1
  let v := masked d a
  if v == zero || v == d then 0 else
    ((p.2.2.find? fun b => b.1 == v).map Prod.snd).getD 0

def advanceProjection (i : Nat) (g : Choice) (p : Projection) : Projection :=
  let d := p.2.1
  let v := masked d (choiceVal g)
  if v == zero || v == d || p.2.2.any (fun w => w.1 == v) then p else
    let left := projectionCode p g.2.1
    let right := if g.1 == 2 then 0 else projectionCode p g.2.2
    (p.1, d, (v, left ||| right ||| (1 <<< i)) :: p.2.2)

def projectedRecipe (revPlan : List Choice) (selected : Nat) : List Choice :=
  (revPlan.reverse.zipIdx.filterMap fun (g, i) => if selected.testBit i then some g else none)

def recipeSize (code : Nat) : Nat :=
  let pairs := code - ((code >>> 1) &&& 0x5555)
  let fours := (pairs &&& 0x3333) + ((pairs >>> 2) &&& 0x3333)
  let eights := (fours + (fours >>> 4)) &&& 0x0f0f
  (eights + (eights >>> 8)) &&& 0x1f

def projectionClosed (cap : Nat) (revPlan : List Choice) (ws : List Sig) (p : Projection) : Bool :=
  let d := p.2.1
  let lb := p.1.2.2.2.2
  let budget := lb + ws.countP (isMaskedConstant d)
  if cap ≥ budget then false else
    let code := ws.foldl (fun acc w => acc ||| projectionCode p w) 0
    if cap + recipeSize code ≥ budget then false else
      let pay := projectedRecipe revPlan code
      match makePool d inputs pay with
      | none => false
      | some pool => poolCut d lb cap pay.length pool ws

theorem searchColumn_valid {c : ColumnInfo} (h : c ∈ searchColumns) :
    Slice inputs graph (subcube c.1 c.2.1) c.2.2.2.2 := by
  have sub : searchColumns.toFinset ⊆ dead.cols.values.toFinset := by decide +kernel
  have mem : c ∈ dead.cols.values := List.mem_toFinset.mp (sub (List.mem_toFinset.mpr h))
  have all := geomdead
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true] at all
  have slice := col_sound (m:=511) c (boundsBefore known383)
    (before_sound known383 valid383) (all.1.2 _ mem)
  have varsEq : vars 511 = inputs := by decide +kernel
  have goalEq : chartGoal 511 = graph := by decide +kernel
  rwa [varsEq,goalEq] at slice

def soundProjection (p : Projection) : Prop :=
  p.1 ∈ searchColumns ∧ p.2.1 = subcube p.1.1 p.1.2.1

theorem advanceProjection_valid (i : Nat) (g : Choice) {p : Projection} (hp : soundProjection p) :
    soundProjection (advanceProjection i g p) := by
  simp only [advanceProjection]
  split <;> exact hp

theorem projectionClosed_sound {cap : Nat} {revPlan : List Choice} {ws : List Sig}
    {p : Projection} (hp : soundProjection p) (nd : ws.Nodup)
    (closed : projectionClosed cap revPlan ws p = true) :
    Impossible graph cap ws.toFinset := by
  simp only [projectionClosed] at closed
  split at closed
  · contradiction
  · split at closed
    · contradiction
    · split at closed
      · contradiction
      · rename_i pool built
        obtain ⟨mem, geom⟩ := hp
        rw [geom] at built closed
        exact poolCut_sound (searchColumn_valid mem) _ built nd closed


def seed0 : Sig := neg (inputs.getD 0 zero)
def rootDecor := wiresOf dead
def seedChoice : Choice := (2, inputs.getD 0 zero, zero)
def seedDecor : Decor := dneg (rootDecor.getD 0 defaultDecor)
def initialProjections : List Projection :=
  searchColumns.map (fun c => advanceProjection 0 seedChoice (initProjection c))

def bothPolarities : List Decor := seedDecor :: rootDecor
def negPolarity : List Decor := seedDecor :: rootDecor.drop 1

theorem initialProjections_valid : ∀ p ∈ initialProjections, soundProjection p := by
  intro p hp
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
  exact advanceProjection_valid _ _ ⟨hc, rfl⟩

def posSample : Fin 192 → Row := asRow (fun j => (dead.samples j).1)
def negSample : Fin 192 → Row := asRow (fun j => (dead.samples j).2)

theorem validSamples : properPairs graph posSample negSample := by
  have g := geomdead
  simp only [graphValid,Bool.and_eq_true,beq_iff_eq] at g
  have eq : chartGoal 511 = graph := by decide +kernel
  rw [← eq]
  exact @chart_pairs 511 _ _ g.1.1.1 g.1.1.2

theorem seedDecor_faithful : faithful posSample negSample seedDecor := by
  exact faithful_neg (faithful_get (wires_faithful dead) 0) 

def inputsFlip0 : List Sig := seed0 :: inputs.drop 1
theorem seed0_witness : ∀ i : Fin 9, i.val = 0 ∨
    ((bit (absentRow i) graph != bit (presentRow i) graph) &&
     ((inputs++[seed0]).all fun w => w == inputs.getD i.val zero ||
       bit (absentRow i) w == bit (presentRow i) w)) = true := by decide +kernel

theorem witness0 :
    (bit (absentRow 0) graph != bit (presentRow 0) graph) &&
    ((inputs++[seed0]).all fun w => w == inputs.getD 0 zero || w == seed0 ||
      bit (absentRow 0) w == bit (presentRow 0) w) = true := by decide +kernel

theorem inputsFlip0_eq : ∀ w : Sig, w ∈ inputsFlip0 ↔
    (w ∈ inputs ∧ w ≠ inputs.getD 0 zero) ∨ w = seed0 := by
  have h1 : inputsFlip0.all (fun w => (inputs.contains w && w != inputs.getD 0 zero) || w == seed0) = true := by decide +kernel
  have h2 : inputs.all (fun w => w == inputs.getD 0 zero || inputsFlip0.contains w) = true := by decide +kernel
  have h3 : inputsFlip0.contains seed0 = true := by decide +kernel
  intro w
  constructor
  · intro hw
    have ha := List.all_eq_true.mp h1 w hw
    simp only [Bool.or_eq_true, Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq, bne_iff_ne, beq_iff_eq] at ha
    exact ha
  · rintro (⟨hwin, hne⟩ | rfl)
    · have ha := List.all_eq_true.mp h2 w hwin
      simp only [Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at ha
      exact ha.resolve_left hne
    · simpa only [List.contains_eq_mem, decide_eq_true_eq] using h3

theorem all_seed0_roots {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ inputs++[seed0]) :
    S = inputs.toFinset ∨ S = (inputs++[seed0]).toFinset ∨ S = inputsFlip0.toFinset := by
  have all_other (i : Fin 9) (hi : i.val ≠ 0) : inputs.getD i.val zero ∈ S := by
    have cut := (seed0_witness i).resolve_left hi
    simp only [Bool.and_eq_true, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at cut
    apply raw_required h _ _ sub (absentRow i) (presentRow i) cut.1
    exact fun v hv hne => (cut.2 v hv).resolve_left hne
  have other_in : ∀ w ∈ inputs, w ≠ inputs.getD 0 zero → w ∈ S := by
    intro w hwin hne
    rw [← input_list, List.mem_ofFn] at hwin
    obtain ⟨i, rfl⟩ := hwin
    have hi : i.val ≠ 0 := fun e => hne (by rw [e])
    exact all_other i hi
  have some4 : inputs.getD 0 zero ∈ S ∨ seed0 ∈ S := by
    have w4 := witness0
    simp only [Bool.and_eq_true, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at w4
    obtain ⟨v, hv, hd⟩ := live_row_difference h w4.1
    have hmem := (decide_eq_true_eq.mp w4.2) v (sub v hv)
    rcases hmem with (rfl | rfl) | heq
    · exact Or.inl hv
    · exact Or.inr hv
    · exact False.elim (hd heq)
  by_cases h4 : inputs.getD 0 zero ∈ S
  · by_cases hs : seed0 ∈ S
    · right; left
      ext w
      simp only [List.mem_toFinset, List.mem_append, List.mem_singleton]
      constructor
      · intro hw; simpa only [List.mem_append, List.mem_singleton] using sub w hw
      · rintro (hwin | rfl)
        · by_cases he : w = inputs.getD 0 zero
          · exact he ▸ h4
          · exact other_in w hwin he
        · exact hs
    · left
      ext w
      simp only [List.mem_toFinset]
      constructor
      · intro hw
        rcases List.mem_append.mp (sub w hw) with hin | hsing
        · exact hin
        · exact False.elim (hs (List.mem_singleton.mp hsing ▸ hw))
      · intro hwin
        by_cases he : w = inputs.getD 0 zero
        · exact he ▸ h4
        · exact other_in w hwin he
  · have hs : seed0 ∈ S := some4.resolve_left h4
    right; right
    ext w
    simp only [List.mem_toFinset, inputsFlip0_eq]
    constructor
    · intro hw
      rcases List.mem_append.mp (sub w hw) with hin | hsing
      · exact Or.inl ⟨hin, fun he => h4 (he ▸ hw)⟩
      · exact Or.inr (List.mem_singleton.mp hsing)
    · rintro (⟨hin, hne⟩ | rfl)
      · exact other_in w hin hne
      · exact hs


theorem rootDecor_faithful (w : Decor) (h : w ∈ rootDecor) : faithful posSample negSample w :=
  wires_faithful dead w h

theorem bothFaith (w : Decor) (h : w ∈ bothPolarities) : faithful posSample negSample w := by
  rcases List.mem_cons.mp h with rfl | hw
  · exact seedDecor_faithful
  · exact rootDecor_faithful w hw

theorem negFaith (w : Decor) (h : w ∈ negPolarity) : faithful posSample negSample w := by
  rcases List.mem_cons.mp h with rfl | hw
  · exact seedDecor_faithful
  · exact rootDecor_faithful w (List.mem_of_mem_drop hw)

theorem both_values : (bothPolarities.map Prod.fst).toFinset = (inputs ++ [seed0]).toFinset := by
  decide +kernel

theorem neg_values : (negPolarity.map Prod.fst).toFinset = inputsFlip0.toFinset := by decide +kernel


abbrev SearchState := List Choice × List Projection × List Decor

def startState (ws : List Decor) : SearchState :=
  ([seedChoice], initialProjections, ws)

def nextState (state : SearchState) (g : Choice) (ws : List Decor) : SearchState :=
  (g :: state.1, state.2.1.map (advanceProjection state.1.length g), ws)

theorem projectionsNext {st : SearchState} (h : ∀ p ∈ st.2.1, soundProjection p)
    (g : Choice) (ws : List Decor) :
    ∀ p ∈ (nextState st g ws).2.1, soundProjection p := by
  intro p hp
  change p ∈ st.2.1.map (advanceProjection st.1.length g) at hp
  obtain ⟨prior, hprior, eq⟩ := List.mem_map.mp hp
  rw [← eq]
  exact advanceProjection_valid _ _ (h prior hprior)

def stateWords (st : SearchState) : List Sig := st.2.2.map Prod.fst

def cutoff (cap : Nat) (st : SearchState) : Bool :=
  let words := stateWords st
  (sameWords words inputs && decide (cap ≤ 14)) ||
    st.2.1.any (projectionClosed cap st.1 words)

theorem cutoff_sound {cap : Nat} {st : SearchState} (h : ∀ p ∈ st.2.1, soundProjection p)
    (nd : (stateWords st).Nodup) (closed : cutoff cap st = true) :
    Impossible graph cap (stateWords st).toFinset := by
  simp only [cutoff, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at closed
  rcases closed with ⟨words, cap14⟩ | pruned
  · rw [sameWords_sound words]
    exact fun k t hk => dead_start k t (hk.trans cap14)
  · obtain ⟨p, hp, yes⟩ := List.any_eq_true.mp pruned
    exact projectionClosed_sound (h _ hp) nd yes

abbrev CheckedLink := Nat × List Sig

def link (st : SearchState) : CheckedLink := (keySet (stateWords st), stateWords st)

def validLinks (cap : Nat) (links : List CheckedLink) : Prop :=
  ∀ l ∈ links, Impossible graph cap l.2.toFinset

def viaLinks (cap : Nat) (st : SearchState) (links : List CheckedLink) : Bool :=
  cutoff cap st ||
    let words := stateWords st
    let key := keySet words
    links.any (fun l => key == l.1 && sameWords words l.2)

theorem viaLinks_sound {cap : Nat} {st : SearchState} {links : List CheckedLink}
    (valid : validLinks cap links) (ps : ∀ p ∈ st.2.1, soundProjection p)
    (nd : (stateWords st).Nodup) (tested : viaLinks cap st links = true) :
    Impossible graph cap (stateWords st).toFinset := by
  simp only [viaLinks, Bool.or_eq_true] at tested
  rcases tested with closed | found
  · exact cutoff_sound ps nd closed
  · obtain ⟨entry, hm, yes⟩ := List.any_eq_true.mp found
    simp only [Bool.and_eq_true] at yes
    rw [sameWords_sound yes.2]
    exact valid entry hm

def afterAnd (links : List CheckedLink) (g : Choice) (ws : List Decor) : Bool :=
  viaLinks 13 (nextState (startState []) g ws) links

def andPairAt (links : List CheckedLink) (ws : List Decor) (i j : Nat) : Bool :=
  directPair (14, ws.length, ws, preCov ws, afterAnd links)
    (ws.getD i defaultDecor) (ws.getD j defaultDecor) false

def AndChecks (links : List CheckedLink) (ws : List Decor) : Prop :=
  ∀ i j : Nat, i < j → j < ws.length → andPairAt links ws i j = true

def AndCertified (ws : List Decor) : Prop :=
  ∃ links, validLinks 13 links ∧ AndChecks links ws

def andMatrix (links : List CheckedLink) (ws : List Decor) : Bool :=
  (List.range ws.length).all fun i =>
    (List.range' (i + 1) (ws.length - (i + 1))).all fun j => andPairAt links ws i j

theorem andMatrix_sound {links : List CheckedLink} {ws : List Decor}
    (checked : andMatrix links ws = true) : AndChecks links ws := by
  intro i j lt hj
  have row := List.all_eq_true.mp checked i (List.mem_range.mpr (by omega))
  apply List.all_eq_true.mp row j
  rw [List.mem_range'_1]
  omega

theorem and_pair {links ws a b} (checked : AndChecks links ws)
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) :
    directPair (14, ws.length, ws, preCov ws, afterAnd links) a b false = true ∨
    directPair (14, ws.length, ws, preCov ws, afterAnd links) b a false = true := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hb
  have he : i ≠ j := fun h => ne (hi.symm.trans (h ▸ hj))
  have hi' : ws.getD i.val defaultDecor = a := (List.getD_eq_getElem _ _ i.isLt).trans hi
  have hj' : ws.getD j.val defaultDecor = b := (List.getD_eq_getElem _ _ j.isLt).trans hj
  have ord : i.val < j.val ∨ j.val < i.val := lt_or_gt_of_ne (fun h => he (Fin.ext h))
  rcases ord with lt | gt
  · have ok := checked i.val j.val lt j.isLt
    unfold andPairAt at ok
    rw [hi', hj'] at ok
    exact Or.inl ok
  · have ok := checked j.val i.val gt i.isLt
    unfold andPairAt at ok
    rw [hi', hj'] at ok
    exact Or.inr ok

set_option maxRecDepth 8192 in
theorem andChild {links : List CheckedLink} {ws : List Decor} (faith : ∀ w ∈ ws, faithful posSample negSample w)
    (nd : (ws.map Prod.fst).Nodup) (valid : validLinks 13 links) (done : AndChecks links ws)
    {a b : Sig} (ha : a ∈ ws.map Prod.fst) (hb : b ∈ ws.map Prod.fst) (ne : a ≠ b)
    (properZ : proper (bin false a b)) (fresh : bin false a b ∉ ws.map Prod.fst)
    (ka kb : Bool) : Impossible graph 13 (childTwo (ws.map Prod.fst) a b false ka kb).toFinset := by
  obtain ⟨da, haD, rfl⟩ := List.mem_map.mp ha
  obtain ⟨db, hbD, rfl⟩ := List.mem_map.mp hb
  have solve : ∀ op ws', afterAnd links op ws' = true → (ws'.map Prod.fst).Nodup →
      (∀ w ∈ ws', faithful posSample negSample w) →
      Impossible graph (14 - 1) (ws'.map Prod.fst).toFinset := by
    intro op ws' ok nd' faith'
    exact viaLinks_sound valid (projectionsNext (st := startState []) initialProjections_valid op ws')
      nd' ok
  have body (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a.1 ≠ b.1)
      (pr : proper (bin false a.1 b.1)) (fr : bin false a.1 b.1 ∉ ws.map Prod.fst)
      (ka kb : Bool)
      (checked : directPair (14, ws.length, ws, preCov ws, afterAnd links) a b false = true) :
      Impossible graph 13 (childTwo (ws.map Prod.fst) a.1 b.1 false ka kb).toFinset := by
    rw [← binary_front nd ha hb ne]
    exact directMove_sound validSamples faith nd ha hb (fun _ e => ne (congrArg Prod.fst e))
      (by decide) solve pr fr (directPair_at checked ka kb)
  rcases and_pair done haD hbD (fun e => ne (congrArg Prod.fst e)) with ok | ok
  · exact body da db haD hbD ne properZ fresh ka kb ok
  · rw [childTwo_swap _ nd]
    exact body db da hbD haD (Ne.symm ne) (bin_comm false da.1 db.1 ▸ properZ)
      (bin_comm false da.1 db.1 ▸ fresh) kb ka ok

theorem and_rep (w : List Sig) (pins : List ℕ) (hp : pins.length ≤ 2) :
    represented w (gv w ⟨.and, pins⟩) ∨
    ∃ a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧
      gv w ⟨.and, pins⟩ = bin false a b := by
  match pins with
  | [] => exact Or.inl (Or.inr (fun p => p.2 rfl))
  | [i] =>
    left
    change represented w (bin false (w.getD i zero) one)
    rw [(bin_laws _).1]
    exact get_rep w i
  | [i, j] =>
    let a := w.getD i zero
    let b := w.getD j zero
    change represented w (bin false a (bin false b one)) ∨ _
    rw [(bin_laws b).1]
    have rz : represented w zero := Or.inr (fun h => h.1 rfl)
    have ro : represented w one := Or.inr (fun h => h.2 rfl)
    rcases operand_cases (get_rep w i) with (az | ao | pa)
    · change a = zero at az
      left
      rw [az, bin_comm false, (bin_laws b).2.2.1]
      exact rz
    · change a = one at ao
      left
      rw [ao, bin_comm false, (bin_laws b).1]
      exact get_rep w j
    · rcases operand_cases (get_rep w j) with (bz | bo | pb)
      · change b = zero at bz
        left
        rw [bz, (bin_laws a).2.2.1]
        exact rz
      · change b = one at bo
        left
        rw [bo, (bin_laws a).1]
        exact get_rep w i
      · by_cases e : a = b
        · left
          rw [← e, (bin_laws a).2.2.2.2.1]
          exact get_rep w i
        · exact Or.inr ⟨a, b, pa.1, pb.1, pa.2, pb.2, e, by simp [gv, a, b, (bin_laws _).1]⟩
  | _ :: _ :: _ :: _ => simp at hp

def seedInputs : List Sig := inputs ++ [seed0]

theorem seed0_not_raw : seed0 ∉ inputs := by decide +kernel

theorem no_raw {k t S} (run : Live graph k t S) (small : k ≤ 14)
    (sub : ∀ a ∈ S, a ∈ inputs) : False := by
  have roots := all_seed0_roots run (fun a ha => List.mem_append_left _ (sub a ha))
  rcases roots with rfl | h | h
  · exact dead_start k t small run
  · refine seed0_not_raw (sub seed0 ?_)
    rw [h]
    simp
  · refine seed0_not_raw (sub seed0 ?_)
    rw [h]
    simp [inputsFlip0]

theorem no_short_seed {k t S} (run : Live graph k t S) (small : k ≤ 13)
    (sub : ∀ a ∈ S, a ∈ seedInputs) : False := by
  have liveSeed : witness inputs seed0 := by
    left
    exact ⟨inputs.getD 0 zero, by decide +kernel, by unfold proper; decide +kernel, rfl⟩
  obtain ⟨j, u, V, hj, live, hv⟩ := pull_gate run (Or.inr liveSeed) sub
  exact no_raw live (by omega) hv

theorem chosenChild {ws : List Decor} (nd : (ws.map Prod.fst).Nodup)
    {a b : Sig} {U : Finset Sig}
    (he : (ws.map Prod.fst).toFinset = insert a (insert b U)) :
    (childTwo (ws.map Prod.fst) a b false (decide (a ∈ U)) (decide (b ∈ U))).toFinset
      = insert (bin false a b) U := by
  let values := ws.map Prod.fst
  change (childTwo values a b false (decide (a ∈ U)) (decide (b ∈ U))).toFinset = _
  have er : ((values.erase a).erase b).toFinset = (values.toFinset.erase a).erase b := by
    rw [erase_fin (nd.erase _) b, erase_fin nd a]
  have ke : (kept (decide (a ∈ U)) a (kept (decide (b ∈ U)) b ((values.erase a).erase b))).toFinset = U := by
    rw [kept_fin, kept_fin, er, he]
    ext j
    by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j = a <;>
      by_cases jb : j = b <;> simp_all
  simp [childTwo, ke]

theorem seed_and_impossible (pins : List ℕ) (hp : pins.length ≤ 2)
    {k t S} (run : Live graph k t S) (small : k ≤ 13)
    (sub : ∀ a ∈ S, a ∈ seedInputs ++ [gv seedInputs ⟨.and, pins⟩])
    (bothChecked : AndCertified bothPolarities) (negChecked : AndCertified negPolarity) : False := by
  let z := gv seedInputs ⟨.and, pins⟩
  change ∀ a ∈ S, a ∈ seedInputs ++ [z] at sub
  by_cases sub0 : ∀ a ∈ S, a ∈ seedInputs
  · exact no_short_seed run small sub0
  push Not at sub0
  obtain ⟨v, hv, outside⟩ := sub0
  have hvz : v = z := (by simpa only [List.mem_append, List.mem_singleton] using sub v hv
    : v ∈ seedInputs ∨ v = z).resolve_left outside
  subst v
  have hz : proper z := live_proper run z hv
  rcases and_rep seedInputs pins hp with degenerate | ⟨a, b, ha, hb, pa, pb, ne, eq⟩
  · exact (degenerate.resolve_left outside) hz
  change z = bin false a b at eq
  let U := S.erase z
  have same : insert z U = S := Finset.insert_erase hv
  have subU : ∀ u ∈ U, u ∈ seedInputs := by
    intro u hu
    obtain ⟨different, needed⟩ := Finset.mem_erase.mp hu
    simpa [different] using sub u needed
  have zFresh : z ∉ insert a (insert b U) := by
    intro h
    rcases Finset.mem_insert.mp h with eq | h
    · exact outside (eq.symm ▸ ha)
    · rcases Finset.mem_insert.mp h with eq | h
      · exact outside (eq.symm ▸ hb)
      · exact outside (subU _ h)
  have front : Live graph (k+1) t (insert a (insert b U)) := by
    apply Live.binary (d := false) pa pb ne
    · exact eq ▸ zFresh
    · rw [← eq]
      exact same ▸ run
  have frontSub : ∀ v ∈ insert a (insert b U), v ∈ seedInputs := by
    simp only [Finset.forall_mem_insert]
    exact ⟨ha, hb, subU⟩
  have exclude (ws : List Decor) (faith : ∀ w ∈ ws, faithful posSample negSample w)
      (nd : (ws.map Prod.fst).Nodup) (check : AndCertified ws)
      (he : (ws.map Prod.fst).toFinset = insert a (insert b U)) : False := by
    have aMem : a ∈ ws.map Prod.fst := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bMem : b ∈ ws.map Prod.fst := List.mem_toFinset.mp
      (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fr : bin false a b ∉ ws.map Prod.fst := by
      intro h
      apply zFresh
      rw [eq]
      exact he ▸ List.mem_toFinset.mpr h
    obtain ⟨links, valid, checked⟩ := check
    have impossible := andChild faith nd valid checked aMem bMem ne (eq ▸ hz) fr
      (decide (a ∈ U)) (decide (b ∈ U))
    rw [chosenChild nd he, ← eq, same] at impossible
    exact impossible k t small run
  rcases all_seed0_roots front frontSub with raw | both | flipped
  · exact dead_start (k+1) t (by omega) (raw ▸ front)
  · exact exclude bothPolarities bothFaith (by decide +kernel) bothChecked (both_values.trans both.symm)
  · exact exclude negPolarity negFaith (by decide +kernel) negChecked (neg_values.trans flipped.symm)

theorem and_after_not (pins : List ℕ) (pinsLen : pins.length ≤ 2) (D : Circuit)
    (fan : PEqualNP.MetaComplexity.FanInTwo D) (small : D.size ≤ 13)
    (bothChecked : AndCertified bothPolarities) (negChecked : AndCertified negPolarity) :
    ∃ x : Fin 9 → Bool,
      let w := List.ofFn x ++ [!x 0]
      D.eval (w ++ [GateOp.and.eval (pins.map fun i => w.getD i false)]) ≠ edge x := by
  by_contra! correct
  let g : Gate := ⟨.and, pins⟩
  let gs := ⟨GateOp.not, [0]⟩ :: g :: D.gates
  let C : Circuit := ⟨gs, D.output⟩
  have fullFan : PEqualNP.MetaComplexity.FanInTwo C := by
    intro gate hm
    simp only [C, gs, List.mem_cons] at hm
    rcases hm with rfl | rfl | hm
    · simp
    · exact ⟨by simp [g], pinsLen⟩
    · exact fan gate hm
  have fullEval (x : Fin 9 → Bool) : C.eval (List.ofFn x) = edge x := by
    have read0 : (List.ofFn x).getD 0 false = x 0 := by simp
    change ((D.gates.foldl _ ((List.ofFn x ++
      [GateOp.not.eval ([0].map fun i => (List.ofFn x).getD i false)]) ++ [_])).getD D.output false) = _
    simp only [List.map_cons, List.map_nil, read0, GateOp.eval, List.headD_cons]
    exact Classical.not_not.mp (correct x)
  have target : (execute gs inputs).getD D.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C fullFan D.output r).trans ((fullEval (sample r)).trans (edge_table r).symm)
  have rep := get_rep (execute gs inputs) D.output
  rw [target] at rep
  have liveGraph := rep.resolve_right (fun bad => bad graph_proper)
  change graph ∈ execute (g :: D.gates) (inputs ++ [gv inputs ⟨.not, [0]⟩]) at liveGraph
  have first : gv inputs ⟨.not, [0]⟩ = seed0 := by decide +kernel
  rw [first] at liveGraph
  change graph ∈ execute D.gates (seedInputs ++ [gv seedInputs g]) at liveGraph
  obtain ⟨k, t, S, hk, run, hs⟩ := extract D.gates _ fan graph_proper liveGraph
  exact seed_and_impossible pins pinsLen run (hk.trans small) hs bothChecked negChecked

-- If both ordered input pairs need an inverter, its operand must reverse
-- both comparisons. The third comparison prevents a single operand doing so.
def rowBefore (ws : Finset Sig) (r s : Row) : Prop :=
  ∀ a ∈ ws, bit r a = true → bit s a = true

theorem rowBefore_binary {ws : Finset Sig} {a b : Sig} {r s : Row}
    (before : rowBefore (insert a (insert b ws)) r s) (d : Bool) :
    rowBefore (insert (bin d a b) ws) r s := by
  intro w hm hw
  rcases Finset.mem_insert.mp hm with rfl | mem
  · have ha := before a (Finset.mem_insert_self _ _)
    have hb := before b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    cases d
    · simp only [bit_bin, if_false, Bool.false_eq_true, Bool.and_eq_true] at hw ⊢
      exact ⟨ha hw.1, hb hw.2⟩
    · simp only [bit_bin, if_true, Bool.or_eq_true] at hw ⊢
      exact hw.imp ha hb
  · exact before w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem mem)) hw

theorem two_inverters {T : Sig} {k t : Nat} {ws : Finset Sig}
    (run : Live T k t ws) (budget : t ≤ 1) {p₁ n₁ p₂ n₂ : Row}
    (pos₁ : bit p₁ T = true) (neg₁ : bit n₁ T = false)
    (pos₂ : bit p₂ T = true) (neg₂ : bit n₂ T = false)
    (first : rowBefore ws p₁ n₁) (second : rowBefore ws p₂ n₂) (cross : rowBefore ws n₁ p₂) :
    False := by
  induction run with
  | stop h =>
    have impossible := first T (Finset.mem_singleton_self _) pos₁
    rw [neg₁] at impossible
    contradiction
  | @unary k t U a proper fresh tail ih =>
    have noMore : t = 0 := by omega
    have reversePair {p n : Row} (hp : bit p T = true) (hn : bit n T = false)
        (ordered : rowBefore (insert a U) p n) : bit p a = false ∧ bit n a = true := by
      obtain ⟨w, hw, p', n'⟩ := mono_row_difference tail noMore hp hn
      rcases Finset.mem_insert.mp hw with rfl | hw
      · simp only [bit_neg, Bool.not_eq_true', Bool.not_eq_false'] at p' n'
        exact ⟨p', n'⟩
      · have := ordered w (Finset.mem_insert_of_mem hw) p'
        rw [n'] at this
        contradiction
    have runFalse := (reversePair pos₂ neg₂ second).1
    have runTrue := cross a (Finset.mem_insert_self _ _) (reversePair pos₁ neg₁ first).2
    rw [runFalse] at runTrue
    contradiction
  | @binary k t U a b d properA properB different fresh tail ih =>
    exact ih budget (rowBefore_binary first d) (rowBefore_binary second d) (rowBefore_binary cross d)

def orderedRows (ws : List Sig) (p n : Row) :=
  ws.all (fun a => !bit p a || bit n a)

theorem orderedRows_sound {ws : List Sig} {p n : Row} (h : orderedRows ws p n = true) :
    rowBefore ws.toFinset p n := by
  intro a ha hp
  have value := List.all_eq_true.mp h a (List.mem_toFinset.mp ha)
  simpa only [hp, Bool.not_true, Bool.false_or] using value

def inversionWitness (T : Sig) (cap : Nat) (ws : List Sig) (data : Nat) : Bool :=
  let p₁ := Fin.ofNat 512 data
  let n₁ := Fin.ofNat 512 (data >>> 9)
  let p₂ := Fin.ofNat 512 (data >>> 18)
  let n₂ := Fin.ofNat 512 (data >>> 27)
  (decide ws.Nodup && decide (cap ≤ ws.length)) &&
    ((bit p₁ T && !bit n₁ T) && (bit p₂ T && !bit n₂ T)) &&
    ((orderedRows ws p₁ n₁ && orderedRows ws p₂ n₂) && orderedRows ws n₁ p₂)

theorem inversionWitness_sound {T : Sig} {cap : Nat} {ws : List Sig} {data : Nat}
    (yes : inversionWitness T cap ws data = true) : Impossible T cap ws.toFinset := by
  dsimp only [inversionWitness] at yes
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at yes
  obtain ⟨⟨⟨nd, count⟩, ⟨⟨p₁, n₁⟩, ⟨p₂, n₂⟩⟩⟩, ⟨⟨l₁, l₂⟩, cross⟩⟩ := yes
  intro k t hk run
  have sz := (live_size run).2
  rw [List.toFinset_card_of_nodup nd] at sz
  exact two_inverters run (by omega) p₁ n₁ p₂ n₂
    (orderedRows_sound l₁) (orderedRows_sound l₂) (orderedRows_sound cross)

def witnessBlock (f : Nat → Bool) (start : Nat) (count : Nat) : Bool :=
  (List.range' start count).all f

theorem witnessBlock_at {f : Nat → Bool} {start count i : Nat}
    (h : witnessBlock f start count = true) (lo : start ≤ i) (hi : i < start + count) :
    f i = true :=
  List.all_eq_true.mp h _ (List.mem_range'_1.mpr ⟨lo, hi⟩)

theorem forest_all_cases (g : Forest) (top : Nat) (prior : Nat → Nat) (early : Nat → Nat → Bool)
    (lower : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true)
    (special : ∀ k i, early k i = true → Impossible (targetOf g) k (stateSet g k i).toFinset)
    (tests : ∀ k ≤ top, ∀ i < (g.levels k).1, early k i = true ∨ nodeVerified g k i = true) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at geometry
  have samples := chart_pairs geometry.1.1.1 geometry.1.1.2
  have columns := fun x hx => col_sound x prior lower (geometry.1.2 x hx)
  intro k
  induction k with
  | zero =>
    intro hk i hi
    rcases tests 0 hk i hi with cut | pass
    · exact special 0 i cut
    · exact nodeVerified_sound g 0 i samples columns geometry.2 (by omega) pass
  | succ k ih =>
    intro hk i hi
    rcases tests (k+1) hk i hi with cut | pass
    · exact special (k+1) i cut
    · exact nodeVerified_sound g (k+1) i samples columns geometry.2
        (fun _ => by simpa using ih (by omega)) pass

-- The rows are reachable sets of live signals, with fixed-input cuts and references.
def andData9 (i : Nat) : Nat :=
  if i < 1 then
    0x6d972fa42c08b50436ea92d216045a821a75cde90b022d410fa8e822058116a0865cf41aae106b5043ae3a05530835a821d73902a3841ad410e39e815bc20d6a086d9b2fa42c06b50434ed9bd216035a821f52d0440b01ad410faa68220480d6a087dc340b02406b50436d397d2160456821b71cb690b022b410db565f48580d5a086dcb2da42c06ad0430f7a0d6f08356821f58d0440901ab410dbc6534bc80d5a0875a7408be116ad043ad5a035f08b56821d71d022d845ab410eb9680d6c22d5a0875e3406a6116ad0432f3a0d5308b56821d78d0227845ab410cbd68353c22d5a0875e540896116ad043af4a034b08b56821d7990223845ab410ebd480d1c22d5a08796741102416ad0434e796d20e0b56821a79ca690705ab410d3da4b48382d5a0869ee23a41c16ad043cb5a0880e0b56821e78d0240705ab410dba65b48580d4a086df223a42c06a5043eb1a088160352821a6dcbe90b05a9410d3ae5b48582d4a0869f525a42c16a50434fb11d2160b52821e59d0440b05a9410eb968156c20d3a0865eb41aae1069d043af1a05530834e82197cd06a9842a7410c3f6835bc2153a086db32fa42c089d0436e996d216044e821b7c49690b0227410dbe4474858113a0869f337a42c089d043eb1a08816044e821d6cd022f845a7410eb968156c22d3a0875d3408b61169d043af1a045708b4e82197ad06ab845a7410ebc68154c22d3a0865f341aa61169d043af4a054b08b4e821d7a902a3845a7410d3765f48582d3a0869db2da42c169d0434f994d2160b4e821a7e49690b05a7410d3f44748582d3a08796b41102c169d043cb9a088120b4e821e78d02c0905a7410dfb05b42c4c5210e75dc242b60568d0738e795b5b05b62829d56cc1ad81db1414ead660d5c0ed8a0a65eb41a9e10aad0532f720d4708556829b6acbe90b01ab414db965b48580d5a0a6dea23a42c06ad0536d717d2160156829b738b690b00ab414dbd44f4858055a0a65f341a9e10aa50532fb20d4708552829f51d0440d02a9414faa68220680d4a0a6db32fa42c06a50536e996d2160352829b7c49690b01a9414dbe44748580d4a0a7d6341102c06a5053ee1a068160352829d6cd01af840a9414faac822068054a0a6db62fa42c02a50536eb16d2160152829b7c89e90b00a9414dbe84b4858054a0a7d6641102c02a5053ee32068160152829f5c90440700a9414fba481a038054a0a7de240b01c02a5053caba0881a0b52829a6dcbe90b05a9414d3ae5b48582d4a0a69f327a42c16a50534fa92d2160b52829a7d88e90b05a9414f2ce8220582d4a0a79c740d02c16a50534db97d2060b52829e5d90440305a9414f3ac81a0182d4a0a79e640b00c16a50538cfa075b20b62819c73d02ad905b140ce3b680d6c82d8a0671dd404b6416c5033abc9326302b4e819
  else
    if i < 2 then
      0x9f13c2744e09b1342644c09712c2544a0931242444808f11c2344608b1142244408710c214420831042044007f0fc1f43e07b0f41e43c0770ec1d43a0730e41c43806f0dc1b43606b0d41a4340670cc194320630c41843005f0bc1742e05b0b41642c0570ac1542a0530a41442804f09c1342604b0941242404708c114220430841042003f07c0f41e03b0740e41c03706c0d41a0330640c41802f05c0b41602b0540a41402704c094120230440841001f03c0740e01b0340640c01702c0540a0130240440800f01c0340600b0140240400700c0140200300400400123fc9d631656283291fe4ead8adb1419497f2758c5957a0ca4f793ac62caa506527f49d6316546832a3dea6936d5b0428d9eb5349c6092a1464bfb1a4e2a6bd04326fd8d271535a82193eec6938a9a7410c9f76349c56d3a0864ff31a4e2a68504325bd4d272035e881935ea693901ad410c9cf5349c80d5a0864f3a9a4e4169d043479d4d2720b4e82193dca693901a1410cabe5b60c6058a0ca55f2db06236c50652cf96d831815e832973cb6c18c0ab4194bae5b60c6054a0ca5de2db063028d0652ef16d8318b4683296dca693901af440cb6e5f60c5494a20657729a4e406c50432db94d272035e821975ca693901ad410cbce5349c80d5a0865f329a4e4069d0432f994d2720b4e821f5e0c130298a541cdaf26342c4c52a0e61ef2ba5e2c6c5053eb498354d5262829f5b0a9302a8b1414cbae5b60c6054a0a7d6c304a92a2c5033a8fa065f05b62832957d06ad82db14196abc8191c16d8a0ca57e41a8e0b6c50658e7a052f1815a832973d06ab845ad4196a9e8158c06d6a0ca5cf41aae036b50652f720d4708b56832e7390340b05a3419636e810bc5497a2071bb4065e2a4bd103acba045b0525e881d66d01ad8292f440eb2e8116c16d7a2065b741aa60b6bd103ad9a044f05b5e88196ed06a782daf440eb6a8112c16d7a207597408b6056bd103acda035b02b5e881d69d022b815af440eb5680d5c0ad7a2075b3406a6056bd1032dba0d5302b5e881d6cd0227815af440cb768353c0ad7a2079b340901c16bd103ae9a035b05252881f69503c0b0129440fb6281e038094a207de140b01c04a5103cd3a078160b52881a75cb68a505a9440f36a81e0282d4a2079e540b01416a5103abc9326302b4e851c5f495b1815a7428ebe24c94c0ad3a14656f41aae106c5043a9ba045f05b62821d55d022d82db1410caee8354c16d8a0875734089e0b6c50432bda0d4f05b62821d5d5022582db1410ea9e8156c0ed8a08656f41aae076c5043ab3a055303b62821d5b902a381db1410eace8154c26d8a08657741aa6136c5043cb3a058120b62821b65cb690b022f410db6a4b4858117a087d2741102c08bd0432d7a0d570835e821d69d02a9841af410eb5c8151c20d7a08
    else
      0xe4208000000005c0c43e003f001f800fc007a003f001f800dc0c7a0037031b818dc0c6e0637031b818f80c7c063b811f018f80c7c063e031000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000009712d2584ac95129249c8f91721e41c7f8f71de39c6f8bd16a24c3884f05a02bf47c6f49e0bb073ee39beb6c6b6d299cb2862ec197aae45c0b716c2d45a0b31642c4580af15c2b4560ab1542a4540a714c294520a3144284500
def andLevel9 : Packing := (225, 6, 7, 0, 0, 11, 0, andData9)
def andHash9 (_ : Nat) : Nat :=
  0x3037c84768286812906b382770370070f3d2486880075848e8253c45201e706ff06bd860a833e84198237853c83c00708011807080708cd9581f7b690070b86c0070c84b18587b39d8324016885f681ee02910012866c824da4aeca7124db3d133b7202b685218222061804c405150039b335845d026f835ac21502e03cd5335182dd844a028f367c80d7d1a64d7e80c60104036785b2042d850b49d903eb85e78567830103bc02018341cbc382d1c2780423338983cc031e83b603d305be03f8527a802ad1af038884db85c701b201d38699b328857180088703815602ce04be0163053701ad023d04384a6302eb818a81a68677006806130405334481dc054b86210058063c049c02fd8441834c02bf0554007b85ca8636008506cb018583a183e141f7803703858503033733ab06ac04ab83690050808b831784094cc10228b39604fa06da817cd22606d302ad4cdd04a006e10ed58018812186950579843281be32b1ccae852d369986a6065b067e064c051f854580b9846e84618482004302a4821f00f152ea80fac4210242010f830985d40116858c806280cb335b009b013504ee04e58096827d059f81ff00ec01c632f505eb041404cf80ae00214bf2800300b4814983aeb2ae839f3d080664021001980145a4b5047f815b860100e784578190b2c0d3d406eccbba83f3804e04f2c19d0172065186400559056800db0594013e81ca440e862a06f305af820f05a202598299049180a20390826585dc32b9bb6c02f484d5832d83dd8681444485fb02c005ee30018050a7a0880418be3f054021f5e0085e1e091244e050108c0a00451d01c010d838000220824009e0180c020024015600e01818e41a37c40460018c08867c0305930370280002630045c08080100052470281c00480000536020030000015e0280003000000627002240800000002c03040000002018380015000440400
def andIndex9 : Nat → Option (Nat × Nat) := lookupWord 115 282 9 16 8 4 andHash9
def andData10 (i : Nat) : Nat :=
  if i < 18 then
    if i < 9 then
      if i < 4 then
        if i < 2 then
          if i < 1 then
            0x5282d510677f880a0b54419e9fa0881d8a067ade8220562819ed7a078158a0673de2f20562819ebda0880d8a067b7681e0362819ef5a0580d8a0673f62f20362819e9fa076098a067ade8158262819ebda036098a066afe8318262819ebe9828098a067afa8220262819edea078098a067bda8160262819efca038098a067afa2320262819cfe8bc8098a067afc8215162819edf2075458a067bdc8155162819efd2035458a067bf88095162819aff20c5458a06737e81e0b62819cf7a0582d8a0673f680e0b62819cbf98282d8a0673fa80a0b62819cbf8bc8217a067a7e821875e819eb7a088157a067af6822035e819edd98780d7a067bd6816035e819cfd8bc80d7a067a7e821725e819edda035c97a067afa822025e819efca038097a067afc821515e819efd2035457a066bfc831515e819cbfa0862d7a0673f680d8b5e819cbfa0882d7a0673f680e0b5e819cbf8bc8215a067a7e8220756819eb7a088155a067af68220356819edda0780d5a067bd68160356819cfd8bc80d5a067ade8215256819ed7a075495a067bd680d5256819af7a0c5495a067bda54a0256819ebea088095a067b7a81e0256819ef6a058095a067bf280e0256819ef685c8095a0673fa2f20256819cbfa0862d5a06737e81d8b56819cf7a0562d5a0673f680d8b56819cfea0262d5a0672fe8217b56819cfda035ed5a0672fe8220b56819cdfa0782d5a0673f680e0b56819cf795282d5a0673fa80a0b56819cbf8bc8213a067a7e822074e819eb7a088153a067b5e81e054e819cf78bc8153a067af6822034e819edda0780d3a067bd6816034e819ebda084c93a067b7681d324e819ef5a054c93a066bf6831324e819efc9328093a067afa822024e819edea078093a067bda816024e819efca038093a067bf20f2024e819cfe8bc8093a0672fe8218b4e819cdfa0762d3a0673de8158b4e819cfda0362d3a0673fa8098b4e819cbf98b22d3a0672fe8217b4e819cfda035ed3a0672fe8215b4e819cdfa0756d3a0673de8155b4e819cfda0356d3a0673fa8095b4e819cf795b16d3a067bf24c82b4e819cfe92b0ad3a0672fe8220b4e819cdfa0782d3a0673de8160b4e819cfd93282d3a0673fa80a0b4e819cbf8bc8212a067a7e822074a819eb7a088152a067b5e81e054a819cf78bc8152a067af6822034a819edda0780d2a067bd6816034a819cfd8bc80d2a067afa822024a819ef6a058092a067bf280e024a819cbfa0862d2a06737e81d8b4a819cf7a0562d2a0673f680d8b4a819cfea0262d2a0672fe8217b4a819cfda035ed2a0672fe8215b4a819cdfa0756d2a0673de8155b4a819cfda0356d2a0673fa8095b4a819cbfa084ed2a06737e81d3b4a819cf7a054ed2a0673f680d3b4a819cfea024ed2a0672fe8220b4a819cf7a0582d2a0673f680e0b4a819
          else
            0x53a0a7bdc816014e829efd2038053a0a7bf40f2014e829cff0bc8053a0a72fe8218b4e829cefa0662d3a0a73de8158b4e829cfda0362d3a0a73fc8058b4e829cf7a055ad3a0a73f680d6b4e829cbfa0856d3a0a73be8195b4e829cf7a0556d3a0a73f680d5b4e829cff20156d3a0a72fe8220b4e829cefa0682d3a0a73de8160b4e829cfd93182d3a0a73fc8060b4e829cbf8bc8211a0a7abe8220646829eb7a088151a0a7b9e81a0546829cf78bc8151a0a7af68220346829eeda0680d1a0a7bd68160346829efd01c80d1a0a73f62f20346829ebf2084c51a0a7bbc8193146829ef72054c51a0a7bf480d3146829aff20c4c51a0a7afc8220146829ef72058051a0a7bf480e0146829cbfa0862d1a0a73be8198b46829cf7a0562d1a0a73f680d8b46829cff20162d1a0a73de8156b46829cfda035ad1a0a72fe8215b46829cefa0656d1a0a73de8155b46829cfda0356d1a0a73fc8055b46829cbfa084ed1a0a73be8193b46829cf7a054ed1a0a73f680d3b46829cff2014ed1a0a72fe8220b46829cf7a0582d1a0a73f680e0b46829cff13182d1a0a67f68313b214199fea0c4ac85067e5e8220781419bd797c0ee0506775e8157b20c199dfa0c5ec8306773e81d6b20c19de7a055ac8306775e81d5b20c199f7a0c56c8306776e81d4b20c19df3a0552c8306777a81d2b20c19df6a054ac830667fa8312b20c19ddf20746c830677dc8151b20c19cdfa076ac830673de815ab20c19dbf20846c530672fe821ab14c19f9da0881e03066f765f08580c19bed96c21603066ff24b08580c19bfd11c21603066bf66b08580c19fb5a0881603067f5681e0580c19bfd11c16e030673de815ab20819cfda036ac820677b680d6b14819dbba0852c520676fc8211b14819dfd20346c520672fe821ab14819cfda036ac520676de8158b0c8199bfa0c62c3206767e8217b0c819dd7a055ec3206779e8156b0c819db7a0856c320667de8315b0c819dbba0852c320677ce8154b0c819dbf20846c320677dc8151b0c819cbfa086ac320673de815ab0c819f9ea0881e02066f7a5f08580819bee96c21602066fea5308580819bfc93c21602066ff84708580819afe9ac21602067eda8220580819fd6a0781602066f7a5f08380819bee96c20e02066fda5708380819bfa94c20e02066ff84708380819afe9ac20e02066ff84705380819afe9ac14e02067ef28220380819fdca0780e02067fd28160380819bde97c22e02066ff84705b80819f9f20881d51067edc8220554419fbd20880d51067f7481e0354419ff520580d51067edc8215254419fd720754951067fd480d5254419bf720c54951067fd854a0254419fbe20880951067f7881e0254419ff620580951067ff080e0254419ff605c809510676fc8220b54419ddf20782d510677f480e0b54419df71
        else
          if i < 3 then
            0xa7b9e815615a829eeda035856a0a7bda815215a829efca034856a0a7bdc816015a829efd2038056a0a73de8158b5a829cfda0362d6a0a73de8160b5a829cfda0382d6a0a72fe2f20856829eafa088195a0a7ade8216556829af7a0c5955a0a7ade8220556829ee7a068155a0a7ade8215356829ee7a0654d5a0a6bde8315356829ef595380d5a0a7af68220356829eeda0680d5a0a7bd62160356829ef596580d5a0a7bd68160356829ef585c80d5a0a73f62f20356829eb7a085455a0a7b9e8195156829ef5a035455a0a6bde8315156829ef71518055a0a7afc8220156829eef2068055a0a7bdc2160156829ef71658055a0a7bdc8160156829ef71538055a0a7bf480e0156829ef705c8055a0a73fc2f20156829cbfa0862d5a0a73be8198b56829cf7a0562d5a0a73f680d8b56829cff20162d5a0a73de8156b56829cfda035ad5a0a72fe8220b56829cefa0682d5a0a73de5960b56829cf795382d5a0a73f680e0b56829cf795182d5a0a73fc8060b56829ebb81c8214a0a7aee2f20852829ebba086154a0a7bae8198552829ebba085954a0a7aee8220552829eeba068154a0a7bce6160552829ef39658154a0a7bce8220552829ef39868154a0a7bce0720552829ef38bc8154a0a7aee8218352829eeba0660d4a0a7bce8158352829ebba0858d4a0a7bce8156352829ebba0854d4a0a7bae8195352829ef3a0554d4a0a7be68220352829ef998680d4a0a7be66160352829ef988580d4a0a7be65960352829ef9a0580d4a0a7aee8218152829eeba066054a0a7bce8158152829ef9a036054a0a7bce8148152829ef9a032054a0a7aee8216152829ef3a055854a0a7be680d6152829ebba085454a0a7bae8195152829ef3a055454a0a7be680d5152829ebba081454a0a7be680c5152829ebba084c54a0a7bae8193152829ef3a054c54a0a7aee8220152829ef3a058054a0a7be680e0152829efb1818054a0a7bec5460152829efb1318054a0a7bec8220152829efb1868054a0a7bec6160152829efb0858054a0a7bec5960152829efb2058054a0a7bec60e0152829efb1638054a0a7bec54e0152829efb08c8054a0a7bec1720152829efb0bc8054a0a7bce8148b52829efb20122d4a0a7aee8205b52829eeba0616d4a0a7bec8045b52829ebba0806d4a0a7bce8141b52829cfba0882d4a0a73ee61a0b52829cfb98582d4a0a73ee2160b52829cfb96582d4a0a73ee8160b52829cfb98182d4a0a73ee2060b52829cfb96182d4a0a73ee5460b52829cfb85182d4a0a73ee8060b52829cbf8bc8213a0a7abe822064e829eb7a088153a0a7b9e81a054e829cf78bc8153a0a7af6822034e829eeda0680d3a0a7bd6816034e829ebda084c53a0a7bb6819314e829ef5a054c53a0a6bf6831314e829efd1318053a0a7afc822014e829eef20680
          else
            0xc8311b20c29cf7a056ac830a76fa8212b14c29deea064ac530a72fe821ab14c29cefa066ac530a7eb68220680c29bdd97c216030a6fb65b08580c29bfc92c216030a6ff44708580c29afd9ac216030a7ed68220580c29fe5a06816030a7eba8220654829fb6a08815520a7f9a81a0554829fb6a0854d520a7f9a8195354829bf6a0c54d520a7fd254e0354829fbca0880d520a7fb281a0354829ff4a0580d520a7fd21720354829dbea0882d520a77ba81a0b54829df695382d520a77f280e0b54829ddda035ec810a77ce8154b20429df6a054ac810a77f280d2b20429cf7a056ac810a73f680dab20429fb6a08549510a7f9a8195254429ff4a03549510a6fda8315254429df695282d510a76fa8212b14429dfca034ac510a72fe821ab14429cfda036ac510a76fa8212b0c429df6a054ac310a72fe821ab0c429cf7a056ac310a7eba8220648429fb6a08815210a7f9a81a0548429df68bc815210a7ef28220348429feca0680d210a7fd28160348429ffc01c80d210a7ef88213148429fee2064c5210a7fd88153148429ffc2034c5210a6ff88313148429dbea0856d210a77ba8195b48429df6a0556d210a77f280d5b484299fea0c56d210a76fa8220b48429df6a0582d210a77f280e0b48429dfe13182d210a7fd85495180429fbe208486010a7fd88152180429ffc203486010a6ff85712180429faf20881a010a6f7c5f08580429bef16c216010a6fec5308580429bfd13c216010a6ff84b08580429aff1ac216010a7edc8220580429fe7206816010a6f7c5f08380429bef16c20e010a6fdc5708380429bfb14c20e010a6ff84b08380429aff1ac20e010a6ff84b05380429aff1ac14e010a7ef48220380429fed20680e010a7fd48160380429fbe20854a010a7fb88195280429ff620554a010a7fd854d5280429ffc20354a010a6ff82f15280429bfe20c54a010a7fd85485b80429eb7a088158a0a7b9e81a0562829cf78bc8158a0a7abe8198362829eb7a0560d8a0a6afe8318362829ebd98380d8a0a7af68220362829eeda0680d8a0a7bd68160362829cfd8bc80d8a0a7afa8215262829eeea065498a0a7bda8155262829efca035498a0a6bfa8315262829eafa066058a0a7ade8158162829ebda036058a0a6afe8318162829ebf1818058a0a7afc8220162829eef2068058a0a7bdc8160162829ebf1838058a0a7bf480e0162829efe1528058a0a7afc2320162829cff0bc8058a0a73de56c5b62829ebd9830ed8a0a73f64ec3b62829ebf18106d8a0a73fc46c1b62829cefa0682d8a0a73de8160b62829cbf98382d8a0a73f680e0b62829cbf98182d8a0a73fc8060b62829ee79658156a0a7ade822055a829cf78bc8156a0a7b9e815635a829eed96380d6a0a7af6822035a829eed96580d6a0a7bd6816035a829cfd8bc80d6a0
      else
        if i < 6 then
          if i < 5 then
            0x5380439bfd20c54e010e6bfc6b08280439ff515354a010e6fbc5b05280439bfd13c14a010e6bfc6b05280439fbe20880a010e7f7881e0280439fee20680a010e7fd88160280439ffc15380a010e7a7e822075a839ecfa076196a0e7ade822055a839ed7a078156a0e7b9e61a055a839cf78bc8156a0e7b3e81d625a839ee7a055896a0e7bba58a025a839ebea088096a0e7b7a81e025a839eee9868096a0e7bda816025a839cfe8bc8096a0e7b7681d315a839ef5a054c56a0e7bf2809315a839afda0c4c56a0e7b7c81e015a839ef72058056a0e7bf880a015a839cdfa0782d6a0e73de8160b5a839cfea0282d6a0e72fe2f2084a839e9fa0881d2a0e7abe822064a839ecfa078192a0e7ade822054a839ed7a078152a0e7b9e81a054a839cf78bc8152a0e7afa821824a839edea076092a0e7bba819824a839ef6a056092a0e6bfa831824a839ebea088092a0e7bba81a024a839ef6a058092a0e7af6821314a839edda074c52a0e7bb6819314a839ef5a054c52a0e7bf2809314a839afda0c4c52a0e7bf44c6014a839ebf2088052a0e7b7c81e014a839eef2068052a0e7bdc816014a839efe1828052a0e7bf880a014a839cff0bc8052a0e73be8198b4a839cfea0262d2a0e73fc8058b4a839cbfa085ed2a0e73be8197b4a839cff2015ed2a0e737e81d6b4a839cf7a055ad2a0e73fa8096b4a839cbfa0882d2a0e73be81a0b4a839cf7a0582d2a0e73fa60a0b4a839cff20182d2a0e7afc0720846839cbf8bc8211a0e7a7e8220746839eafa088191a0e7b3e81e0646839eb7a088151a0e7b5e81e0546839ee7a068151a0e73de2f20546839ebea088091a0e7b7a81e0246839eeea068091a0e7bda8160246839cfe8bc8091a0e7afc8218146839edf2076051a0e7bbc8198146839ef72056051a0e7bf88098146839aff20c6051a0e7afc8212146839edf2074851a0e7bbc8192146839ef72054851a0e7bf88092146839aff20c4851a0e7afc8220146839edf2078051a0e7bdc8160146839efe2028051a0e72fe8218b46839cdfa0762d1a0e73be8198b46839cf7a0562d1a0e73fa8098b46839cff20162d1a0e7afc6048b46839cbf98b22d1a0e72fe8217b46839cefa065ed1a0e73fc8057b46839cdfa075ad1a0e73de8156b46839cfea025ad1a0e73be8195b46839cfea0256d1a0e73fc8055b46839cf795b16d1a0e72fe8212b46839cdfa074ad1a0e73be8192b46839cf7a054ad1a0e73fa8092b46839cff2014ad1a0e7bf84842b46839cfe92b0ad1a0e72fe8220b46839cdfa0782d1a0e73be81a0b46839cf7a0582d1a0e73fa80a0b46839cff18182d1a0e73fc4860b46839bbe92c06e080a67f68313b214299ff20c46c850a7e9e8220681429de7a055ac830a67de8315b20c29df3a0552c830a77da8152b20c29df720546c830a67f
          else
            0x821ebba0854d4a087bce8155352821ef998580d4a087be62160352821ef9a0580d4a0873ee8220b52821cfb98582d4a0873ee2160b52821cfba0582d4a0872fe2f2084e821eb7a088153a0873de2f2054e821ebba088113a087bce816044e821ebda0860d3a087bd6815834e821ef9a0460d3a087bd6814834e821ebda0854d3a087bd6815534e821ef9a0454d3a087af6820534e821ebda0850d3a087bd6815434e821ebda0880d3a087bd6816034e821cbfa0862d3a0873de8158b4e821cfba0462d3a0873f680d8b4e821cbfa0856d3a0873de8155b4e821cfba0456d3a0873f680d5b4e821cbfa0826d3a0873de8149b4e821cbfa0882d3a0873de8160b4e821cfba0482d3a0873f660e0b4e821cfd95382d3a0873f650e0b4e821ebd89c8213a087af62f2084e821ebda086153a087af6822054e821ef59858153a087bd6822054e821ef58bc8153a087af6821844e821ef5a056113a087af6821544e821ef5a055513a087be6822044e821ef99858113a087be6216044e821ef9a058113a087af68218b4e821ef5a0562d3a087be68118b4e821ef5a0522d3a087be68108b4e821ebda0856d3a087bd68155b4e821ef9a0456d3a087af68205b4e821ef9a0416d3a087af68214b4e821ef5a0552d3a087af68209b4e821ef5a0526d3a087af68220b4e821ef5a0582d3a087be68120b4e821cfd98b82d3a0873f656e0b4e821cfd94b82d3a0873f68220b4e821cfd98582d3a0873f62160b4e821cfda0582d3a0873f66120b4e821cfd95482d3a0873f62320b4e821cfd85c82d3a0873f62720b4e821faea0881a020e7f3a81e0680839ddea025ec810e677e8317b20439ddda074ec810e77f28093b20439cdfa076ac810e73fa809ab20439dfca024ec510e67f68313b14439cfea026ac510e7ef4072084c439f9da0881d310e7eb6822064c439fcda07819310e7ef2822024c439fdca07809310e7fb281a024c439fbd208605310e7f7481d814c439fed206605310e7ff0809814c439bfd20c605310e7ef46048b4c439deda0656d310e77f28095b4c4399fda0c56d310e76f68220b4c439ddda0782d310e77b681a0b4c439dfca0282d310e77f46060b4c4399fd95c82d310e7ef48213148439fdd2074c5210e7fb48193148439ffc2024c5210e7ff00b13148439bfd20c4c5210e77f44c60b484399bfa0c62c210e767e8217b08439dafa085ac210e76de8215b084399f7a0c56c210e76f68213b08439cbfa086ac210e7ef48213180439fdd2074c6010e7ff08093180439bfd15c4c6010e7e7c8220780439faf20881a010e7f3c81e0680439bdf17c216010e6fbc5b08580439bfd13c216010e6ff84b08580439aff1ac216010e7f9c81a0580439fbd20854e010e7f7481d5380439fed20654e010e7fd46155380439ff520554e010e6ff42f1
        else
          if i < 7 then
            0xbf95b82d8a0872fe52e0b62821cbf93b82d8a0872fe8160b62821cbf95482d8a0872fe54e0b62821cbf85382d8a0872fe50e0b62821cbfa0382d8a0872fe1720b62821cbf83c82d8a0872fe2720b62821e9f89c8217a087a7e821855e821e9fa088157a087b5e616055e821ed7a088157a087a7e821845e821ed7a056117a087a7e821545e821ed7a055517a087b6e822045e821edb9858117a087b6e216045e821edba058117a087a7e821835e821ed7a0560d7a087b6e811835e821ed7a0520d7a087a7e821535e821ed7a0554d7a087b6e811535e821e9fa0814d7a087a7e821435e821ed7a0550d7a087a7e822035e821ed7a0580d7a087b7660e035e821edd95380d7a087abe272085a821eafa086156a087abe822055a821ee79858156a087b9e822055a821eafa086116a087b9e815845a821eafa085516a087b9e815545a821eeba088116a087bae616045a821eeb8858116a087bae816045a821eafa0860d6a087b9e815835a821eeba0460d6a087b9e814835a821eafa0854d6a087b9e815535a821eeba0454d6a087abe820535a821eafa0850d6a087b9e815435a821eafa0880d6a087b9e816035a821eed98380d6a087bb654e035a821eeda0880d6a087bb6616035a821eed88580d6a087bb6816035a821eed98480d6a087bb6552035a821eed89c80d6a0872fe2f20856821eb7a086155a087ade8220556821eb7a085515a087aee8220456821ef39858115a087bce2160456821ef3a058115a087ade8215356821ef3a0454d5a087ade8205356821ef595380d5a087af68220356821ef598580d5a087bd62160356821ef5a0580d5a087bd65520356821ef9a0480d5a0873f62f20356821cbfa0862d5a0873de8158b56821cfba0462d5a0873f680d8b56821cbfa0826d5a0873f680c9b56821cbfa0882d5a0873de6160b56821cf795482d5a0873ee8120b56821cf795382d5a0873f680e0b56821eb789c8215a087ade2f20856821eb7a086115a087bce8220456821eb7a0860d5a087bce8118356821eb7a0850d5a087ade8220356821ef598380d5a087bd68220356821ef598480d5a087bd62720356821ef58bc80d5a087ade8218b56821ef3a0462d5a087bd680d8b56821ef3a0422d5a087bd680c8b56821eb7a0852d5a087bd680d4b56821eb7a084ed5a087bce8113b56821ef5a034ed5a087ade8203b56821eb7a0826d5a087bd680c9b56821eb7a0882d5a087bce8120b56821ef5a0382d5a0873de62e0b56821cf794b82d5a0873de4ee0b56821cf7a0882d5a0873de6120b56821cf798382d5a0873de20e0b56821cf794382d5a0873de80e0b56821cf788c82d5a0873de0f20b56821eb7a088154a087aee2720852821ebba086154a087aee8220552821ef39858154a087bce8220552821ebba0860d4a087bce8158352
          else
            if i < 8 then
              0xb0ad3a1473f680c9b4e851cfba0482d3a1473f64ca0b4e851ef9a0480d2a1473f62f2034a851ebea086092a147bea811824a851efca036092a146bfa831824a851efaa048092a147bf280e024a851cfba0462d2a1473f680d8b4a851cfea0262d2a1473ee8113b4a851cfda034ed2a1473fa8093b4a851cfda0326d2a1473ee8120b4a851cfda0382d2a1473fa60a0b4a851f97a0881e050c73de815ab20831cbfa086ac520c7e7a8220780831fb6a08816020c7f5a81e0580831abf89c8218a0c7a7e8220762831eb7a088158a0c7b5e81e0562831cf78bc8158a0c7a7e81d8262831eb7a056098a0c6afe8318262831ebe9828098a0c7afa8220262831edea078098a0c7bda8160262831cfe8bc8098a0c737e81c9b62831cf7a0526d8a0c73fa8089b62831cdfa0782d8a0c73de8160b62831cbf98282d8a0c73fa80a0b62831e9fa0861d7a0c7ade822055e831e9fa085c97a0c7afa822025e831cbfa0862d7a0c72fe8209b5e831cf7a0526d7a0c72fe8220b5e831e9fa0881d5a0c7ade8218556831ed7a076155a0c6bde8318556831eb7a088155a0c7ade8215256831ed7a075495a0c6bde8315256831ef69528095a0c7afa8220256831edea078095a0c7bda6160256831ef6a058095a0c73fa2f20256831cbfa0862d5a0c737e81d8b56831cf7a0562d5a0c73fa8098b56831cbfa085ed5a0c72fe8209b56831cdfa0726d5a0c73fa8089b56831cbfa0882d5a0c737e81e0b56831cf798582d5a0c73de54a0b56831cfea0282d5a0c7a7e822074a831eb7a088152a0c7b5e81e054a831cf78bc8152a0c7afa821824a831edea076092a0c7bda815824a831afea0c6092a0c7afa822024a831ef6a058092a0c72fe8218b4a831cdfa0762d2a0c73de8158b4a831cfea0262d2a0c72fe8217b4a831cbfa0856d2a0c737e81d5b4a831cf7a0556d2a0c73fa8095b4a831cbfa0826d2a0c73de8149b4a831cbfa0882d2a0c73de8160b4a831cfe98282d2a0c6bee6b08581021fb3a08816040867de8315b20c21cf7a056ac830872fe821ab14c21afd9ac21603087ed68220580c21ff1a0581203087ade6160562821eb7a088158a0873de2f20562821eb7a056118a087aee8220462821ebb9858118a087aee2160462821ef3a058118a087ade8158362821ebba0460d8a087ade8148362821ebd98380d8a0873de8149b62821cbf98582d8a0873de8160b62821cbf98482d8a0873ee8120b62821cbf98382d8a087ade2f20562821eb7a055518a087aee8160462821eb7a0554d8a087aee8115362821eb7a0550d8a087ade8160362821ebd95380d8a087ade8155b62821ebba0456d8a087aee8105b62821eb7a0552d8a087ade8153b62821ebba044ed8a087af680d3b62821eb7a050ed8a087ade8149b62821eb7a0582d8a087aee8120b62821c
            else
              0x7a207b7680d525e881edba041497a207b7680c525e881edda035097a207b6e811325e881edda034c97a207b6e812025e881edda038097a207b7a50a025e881ede9328097a207b6e8115b5e881edba0416d7a207b7680d4b5e881edba044ed7a207b7680d3b5e881ed7a050ed7a207b6e8112b5e881edda034ad7a207b6e8102b5e881edda030ad7a207b5e8149b5e881edda0326d7a207b6e8120b5e881edda0382d7a20737e5520b5e881cdf95382d7a20737e50e0b5e881cdfa0382d7a20737e50a0b5e881cdf93282d7a207b6e81e0456881ef3a058115a207b5e81d5356881ef3a0454d5a206bde8315356881ef595380d5a207b5e81d5256881ef3a045495a206bde8315256881ef69528095a2073ee8117b56881cdfa0726d5a20737e81e0b56881cfba0482d5a2073de54e0b56881cf795282d5a207b5e81e0552881edea078094a207bda8160252881ef3a055cd4a207b6e81d5352881ef3a0554d4a207bce8157252881ef9a035c94a207b6e81d5252881ef3a055494a207be680d5252881ef9a031494a207b6e81d3252881ef3a054c94a207bce8160252881ef9a038094a207bea54a0252881efa9328094a207bea5d60252881efaa058094a207bea5ce0252881efa9538094a2073ee5d60b52881cfba0582d4a2073ee5ca0b52881cfb95282d4a2073ee14a0b52881cfba0282d4a207b6e81e044e881edda0754d3a207bd6815534e881ef9a0454d3a206bf6831534e881edda0780d3a206bf6272034e881edda074c93a207be6811324e881afda0c4c93a207bf24ca024e881edea078093a207bea812024e881efc9538093a207bf280e024e881cfe8bc8093a2073ee8117b4e881cfda035ed3a20737e81d5b4e881cf7a0556d3a2073ee8115b4e881cfda0356d3a2073fa8095b4e881cdfa0726d3a2073fa8089b4e881cdfa0782d3a2073f654e0b4e881cfd93282d3a2073fa80a0b4e881ed7a078152a2073de2f2054a881edba078112a207bce816044a881edda0780d2a207bd6816034a881ef9a0480d2a2073f62f2034a881edea075492a207bda815524a881efaa045492a207bf280d524a881afea0c5492a207b7a81d324a881ef6a054c92a207bea811324a881efca034c92a206bfa831324a881ef6a058092a207bea812024a881efca038092a2073ee8117b4a881cfda035ed2a20737e81d5b4a881cf7a0556d2a2073ee8115b4a881cfda0356d2a2073fa8095b4a881cdfa074ed2a2073de8153b4a881cfba044ed2a2073f680d3b4a881cfea024ed2a2073de8149b4a881cfda0326d2a2073de8160b4a881cfba0482d2a2073f680e0b4a881cfe95282d2a2073fa4ca0b4a881cfba046ac821473f680dab208519bfa0c62c32146bf6272034e851ef9a044c93a146bf6831324e851efc9328093a147bf24c82b4e851cfe92
    else
      if i < 13 then
        if i < 11 then
          if i < 10 then
            0xbb9e596055a832ee7a055856a0cb2fe8209b5a832cf7a0526d6a0cb3de8160b5a832eafa086156a0cbb9e616055a832ee789c8156a0cbb9e815815a832ee7a055456a0cbb9e816015a832eef1518056a0cbb9e8155b5a832eafa0816d6a0cbb9e8151b5a832ee7a0506d6a0cbabe8209b5a832ee7a0526d6a0cbb9e8160b5a832cef98582d6a0cb3be8160b5a832cef95182d6a0cbade8218556832ee7a066155a0cbb9e81a0556832ee7a065455a0cbbdc5460156832cbfa0862d5a0cb3be8198b56832cf7a0562d5a0cb3de8156b56832cefa0626d5a0cb3be81a0b56832cf798582d5a0cb3de5960b56832cf795182d5a0cbade8218156832ee7a066055a0cbbdc6060156832eb7a0862d5a0cbb9e8198b56832ee7a0646d5a0cbbdc8051b56832ee7a0626d5a0cbb9e81a0b56832cf798b82d5a0cb3de5ae0b56832cf791b82d5a0cb3de8220b56832cf798682d5a0cb3de6060b56832cf796182d5a0cb3de8060b56832cf788c82d5a0cb3de0720b56832cf789c82d5a0cbaee8218552832eeba066154a0cbbae81a0552832ef39858154a0cbbce5960552832ef3a088154a0cbbce61a0552832ef389c8154a0cbaee8218152832eeba066054a0cbbce8158152832ef3a055854a0cbbae8195152832ef3a055454a0cbbce8160152832efb1818054a0cbbec5460152832ee7a068151a0cb3de2f20546832ebf2086051a0cbbbc8198146832ef72056051a0cbbdc8156146832eef2065451a0cbbdc8155146832ef72058051a0cb2fe8218b46832cefa0662d1a0cb3de8158b46832cff20162d1a0cb3de8156b46832cefa0656d1a0cb3de8155b46832cff20156d1a0cb3de8149b46832cf7a0582d1a0cb3fc6060b46832cff15182d1a0cbafc8218546832eef2066151a0cbbbc81a0546832ef71858151a0cbbdc5960546832ef72088151a0cbbdc61a0546832ef709c8151a0cbbdc2f20546832ebf20862d1a0cbbbc8198b46832ef720562d1a0cbbdc8148b46832ef72055ad1a0cbbbc8195b46832ef720556d1a0cbbdc8149b46832ef720582d1a0cb3fc62e0b46832cff15b82d1a0cb3fc8220b46832cff18682d1a0cb3fc6160b46832cff16582d1a0cb3fc8160b46832cff08c82d1a0cb3fc1720b46832fd3a0781604207f6681e0480c81cfba046ac522073f680dab14881de7a055ac322067de8315b0c881df3a0552c322077dc8151b0c881cf7a056ac32207f6a81e0480881fdca0780e02207fd28160380881ff8a0480e02207b6e5d6045e881edba045cd7a207b765ce035e881edd97480d7a207be6812035e881edba045c97a207b7680d725e881cf7a0526d7a2073f680c9b5e881cfba0482d7a2073f680e0b5e881ed7a055517a207b6e816045e881ed7a0554d7a207b6e811535e881edd95380d7a207b76272035e881edba04549
          else
            0x8120b4e821ad797c2155a0a6b9e5b08556829af593c2155a0a6bdc4708556829eaba088194a0a6b6e5f08552829aeb96c2154a0a6be64f08552829afa92c2154a0a6bec4708552829eb3a088154a0a7b8e81a0552829eb9a0880d4a0a7ba681a0352829ef1a0580d4a0a6b6e5f08152829ebb2088054a0a7bac81a0152829ef32058054a0a7be480e0152829cbba0882d4a0a73ae81a0b52829cf3a0582d4a0a73ec8060b528298ef96c82d8a0673de56e0542882eafa066018a0cbabe8195062832eafa064418a0cbabe8190b62832cafe0682d8a0cb2fe5820b62832cbf95082d8a0cb2fe4420b62832ecfa066017a0cbb3e819505e832ecfa064417a0cb3be6020b5a832cef95082d6a0cb3be4420b5a832ee7a065415a0cbb9e8198056832ee7a064415a0cbb9e8190b56832ce7e0682d5a0cb3de6020b56832cf796082d5a0cb3de4420b56832eeba066014a0cbbae8195052832eeba064414a0cbbbc8191046832eef2066011a0cbbbc8195046832eef20642d1a0cb3bd81a0b46832cff18082d1a0cb3fc5820b46832cff15082d1a0cb3be8198b42832cefa0656d0a0cb3be8191b42832cdf95082d7a20737e4c20b5e881cdf92082d7a207b5e81d5056881edba075414a207b6e81d2052881edda074c13a207b7a81d204a881cdfa0756d0a20737e81d3b42881cfda034ed0a20737e81d2b42881cbf98b8210a1473f680d3b42851e9fa076018a0c7b5e81d5056831edea074812a0c72fe8218b42831cdfa0762d0a0c737e81d5b42831cdfa074ad0a0c72fe5420b62821cbf93082d8a0873de6020b56821cf793082d5a0873f66020b4e821cfd95082d3a087be6811314e882afda0c4c53a20bbf44c6014e882cfd93182d3a20bbdc8155146882efb2045451a20abfc8315146882efb2044c51a20bbf480d3146882aff20c4c51a20bbec8120146882cfba0456d1a20b3fc8055b46882cfba044ed1a20b3f680d3b46882cff2014ed1a20b3ee8120b46882cff15182d1a20b3fc4c60b46882eafa066158a0cbade6160562832eafa066058a0cbafc6060162832cefa0626d8a0cb2fe61a0b62832cefa0682d8a0cb2fe6160b62832cbf98182d8a0cbabe81a0562832eb79658158a0cbabe8195162832eb7a055458a0cbafc5460162832eafa0656d8a0cbade8155b62832eafa0616d8a0cbabe8191b62832ebf20146d8a0cbabe8189b62832eafa0682d8a0cb2fe5ae0b62832cbf95b82d8a0cb2fe46e0b62832cbf96582d8a0cb2fe8160b62832cbf96182d8a0cb2fe5460b62832cbfa0182d8a0cb2fe1720b62832cbf81c82d8a0cb2fe2720b62832e9fa086157a0cbb3e819855e832ecfa068157a0cbb5e616055e832ed79658157a0cba7e821815e832ecfa066057a0cbb3e819515e832ed7a055457a0cbb7c606015e832edf1518057a0c
        else
          if i < 12 then
            0x34a8198ffa0c62d2a0663fe6315b4a819cdf87c56d2a0663fe8315b4a8198ff98c4ed2a0663fe5713b4a8198ffa0c4ed2a066a7e5f05b62832aaf96c16d8a0caafc4705b62832a9f97c06d8a0cb2be81a0b628328ef8bc6056a0cab3e5f08b5a832ae795c22d6a0cabbc4708b5a832aaf98c06d6a0cab3e5f01b5a832ae795c06d6a0cb39e8160b5a832ad797c22d5a0cab9e5b08b56832af711c22d5a0cb39e81a0b56832ee3a068154a0cbb9c81a0546832adf17c22d1a0cb3bc81a0b46832cf720582d1a0cbb66812035e8818df8bc5497a206b3e5b0525e881a9f98c0c97a206b3e5b0325e881ad795c0c97a206b6e530325e881adf11c0c97a20637e6f0325e881acf96c16d7a206b6e5305b5e881add93c16d7a206b7a4b05b5e881acf96c0ad7a206b5e5702b5e881adb94c0ad7a206b764f02b5e881cdba0482d7a20737680e0b5e881ed3a078154a207b6681e0352881aeb96c1494a207b6a81e0252881ef2a058094a207be280e0252881cdba0782d4a2073ce8160b52881cfaa0282d4a206a7e5f08362821aaf96c20d8a086ade5708362821abb94c20d8a087ace8160462821a9f97c16d8a086abe5b05b62821abb94c16d8a086af64f05b62821abe92c16d8a086a7e5f03b62821aaf96c0ed8a086ade5703b62821abb94c0ed8a086afa4b03b62821abf11c0ed8a086aee5309b62821cb7a0582d8a0872ee8120b62821acf96c2157a086b7a4b0855e821e97a088157a087a6e822045e821ed3a058117a086b3e5b0835e821ad795c20d7a086b6e530835e821ade92c20d7a086b7c470835e8218df9bc20d7a086b3e5f0855a821aee92c2156a0863be6f0855a821ea7a088156a087aae822045a821ee3a058116a086b3e5f0835a821ae795c20d6a086bae530835a821aee92c20d6a086bbc470835a8218ef9bc20d6a087ab6822035a821ee5a0580d6a087ba6812035a821ad797c2155a086b9e5b08556821eb3a088115a086b5e5f08356821ae796c20d5a086bce5308356821af692c20d5a086bdc47083568218f79bc20d5a087ad68220356821ef1a0480d5a086b5e5f08b56821ae796c22d5a086bce5308b56821af593c22d5a086bda4b08b56821af711c22d5a0872de8220b56821cf3a0482d5a0873d680e0b56821adb97c2154a086bae5b08552821afa92c2154a086bec4708552821eb3a088154a087bc68160352821cbba0882d4a0873ce8160b52821add97c20d3a086bb65b0834e821af595c20d3a086be6530834e821add97c2153a086bb65b0854e821af994c2153a086bf24b0854e821afd11c2153a0863f66f0854e821eb5a088153a087ae6822044e821ef1a058113a086b765f08b4e821aed96c22d3a086bd65708b4e821af994c22d3a086bf24b08b4e821afd11c22d3a0872f68220b4e821cf5a0582d3a0873e6
          else
            0x29efd1814c53a0a63fe8318b4e8298ff98c56d3a0a63fe8315b4e829adf97c2151a0a6bbe5b08546829afb94c2151a0a6bf64f08546829afe92c2151a0a6bfc47085468298ff9bc2151a0a6b7e5f08346829aef96c20d1a0a6bde5708346829afb94c20d1a0a6bfa4b08346829aff11c20d1a0a63fe6f08346829aff11c14d1a0a63fe6f05346829efd1634c51a0a73fc4c58b46829cef86c62d1a0a63fe8318b46829cf796556d1a0a63fe6315b468298ffa0c56d1a0a63fe6313b468298ff95c4ed1a0a63fe8313b468298ff9ac82d870673f66b13b21419cfe9ac4ac850677dc4715b20c19cf79ac56c830673fa6b12b20c198ff9ac82d530663fe6b20b60819cdf87b6ad5206677e5f20b54819cbf9ac62c320677dc4715b0c819cf79ac56c32066f7c5f08354419bef16c20d51066fdc5708354419bfb14c20d51066ff84b08354419aff1ac20d510667fc6f08354419bf715c20951066bfc6b08254419ff618254951067fd85c95254419fd707c54951066efc6303254419bdf17c0c951066fbc5b03254419bf715c0c951066fec5303254419aff1ac0c9510667fc6f03254419aff11c14d8a0663fe6f05362819ebe9825498a066afe6305262819afb94c1498a066bfc47052628198ff9bc1498a067afa6093262819abf98c0c98a066b7e5f03262819af795c0c98a066bee5303262819aff11c0c98a0663fe6f03262819ebf1825458a067bdc5495162819cff15182d8a066bbe5b0835e819af795c20d7a066bee530835e819afe92c20d7a066bfc470835e819adf97c20d5a066bbe5b08356819af795c20d5a066bee5308356819afe92c20d5a066bfc47083568198ff9bc20d5a066bde57082568198ff9bc2095a067bda6095256819ef69725495a067b5e1f15256819abf98c0c95a066b7e5f03256819aef96c0c95a066bde5703256819afb94c0c95a066bfc47032568198ff9bc0c95a0663fe8318b568198ff8bc8213a0663fe2f1874e819adf97c2153a066bbe5b0854e819afd93c2153a066bfa4b0854e819aff11c2153a0663fe6f0854e8198ff8bc8153a0663fe2f1824e819afd93c2093a0663fe6f0824e819aef96c1493a066bf64f0524e819aff11c1493a0663fe6f0524e819efc9824c93a0663fe2f2024e819cbf98262d3a0663fe8318b4e819adf97c22d3a066bfa0b17b4e819cf795256d3a0663fe6315b4e8198ffa0c56d3a066afe6302b4e819adf97c0ad3a066bbe5b02b4e819af795c0ad3a0663fe6320b4e8198ff95c82d3a0663fe4b20b4e819adf97c2152a066bbe5b0854a819afb94c2152a066bf64f0854a819afe92c2152a066bfc470854a8198ff9bc2152a066b7e5f0834a819aef96c20d2a066bde570834a819afb94c20d2a066bfa4b0834a819aff11c20d2a0663fe6f0834a819aff11c14d2a0663fe6f05
      else
        if i < 15 then
          if i < 14 then
            0xa94c20d520a6ff84708354829afe9ac20d520a67fa6f08354829ff498354d520a73be1adab604299ef96c82d810a77da5495b20429dfa95252c810a67fa5712b20429cfe9526ac810a7fd85498154429df695256d310a63fe6b20b4c429df695256c310a67fa5712b0c429bde97c215210a6fba5b08548429bfa94c215210a6ff24f08548429bfe11c215210a6bfa6b085484299fe9bc215210a6f7a5f08348429bee96c20d210a6fda5708348429bfa94c20d210a6ff84708348429afe9ac20d210a67fa6f08348429bfe11c14d210a67fa6f05348429ffc1634c5210a63fe2f20562829ebd98358d8a0a63fe2f16362829ebd98354d8a0a63fe2f15362829abf98c14d8a0a6bfa4b053628298ff9bc14d8a0a63fe2f20362829ebe9835498a0a7bda54d5262829ebe9526058a0a7abe1b18162829ebf1815858a0a7bda5495162829ebf1815458a0a6afe6305162829afe92c1458a0a63fe6f05162829ebf1814c58a0a6afe63131628298ff8bc4c58a0a6afe6303162829afe92c0c58a0a63fe6f031628298ff8bc8058a0a6bbe5b05b62829afb94c16d8a0a6b7e5f03b62829aef96c0ed8a0a6bde5703b62829afb94c0ed8a0a6bfc4703b62829adf97c06d8a0a6bee5301b62829cfe95282d8a0a63fe5720b628298ff93c82d8a0a63fe4720b62829efe1314856a0a6bde4f08556829af791c2155a0a7b9e6196556829aef96c20d5a0a6bde5708356829afb94c20d5a0a6bfa4b08356829aff11c20d5a0a63fe6f08356829ef598354d5a0a6bde5b15356829af795c2055a0a6bee5308156829afe92c2055a0a63fe6f08156829ef71815455a0a6bde5b15156829af795c4c55a0a6bde57031568298ff9bc0c55a0a73de5958b56829cf795362d5a0a63fe8318b56829afba0c6154a0a6bee4f08552829afb91c2154a0a7bae6196552829ef39855954a0a6bee6316552829afba0c5954a0a6bee8318352829eeb98658d4a0a7be660d6352829afb98c58d4a0a6bee8316352829ef398554d4a0a7be660d5352829afb98c54d4a0a6bee5b15352829afba0c54d4a0a7aee6198152829eeb86c6054a0a6bee8318152829afb95c2054a0a6bee4f08152829efb1815854a0a6bee6316152829ef39655454a0a7bec6055152829afb98c5454a0a6bee5b15152829afba0c5454a0a6bee6305152829afb93c1454a0a7be658d3152829efb1814c54a0a6bee6313152829afb96c4c54a0a6bee5713152829afba0c4c54a0a6bee5708b52829afb91c22d4a0a6bee6305b52829afb96c16d4a0a6bee4705b52829afb98c06d4a0a6bee5701b52829adf97c2153a0a6bbe5b0854e829afd93c2153a0a6bfa4b0854e829aff11c2153a0a63fe6f0854e829adf97c2053a0a6bf64f0814e829afe92c2053a0a63fe6f0814e829afd93c1453a0a63fe6f0514e8
          else
            0x62d3a0863fe8318b4e821cf798556d3a0873de5515b4e821cfd98356d3a0863fe6315b4e8218ff89c56d3a0863fe8315b4e821cfd95326d3a0863fe6309b4e8218ff95c26d3a0863fe2720b4e821afd89c8213a086bf6271854e821afda0c6153a086bf6530854e821afd9bc2153a086bf6831844e821ef99845513a086bf6631544e821afda0c5513a087af66118b4e821afd89c62d3a086bf68318b4e821afd95c22d3a086bf65308b4e821ef598556d3a087bd65515b4e821cfd98b56d3a086bf66315b4e821afd89c56d3a086bf68315b4e821afd98c16d3a086bf65305b4e821ef998452d3a086bf66314b4e821afd95c52d3a086bf68314b4e821cfd95b26d3a086bf66309b4e821afd95c26d3a086bf62720b4e8219fd93c82d820e63fe6b20b60839cef86b6ad810e67be5b20b604398ffa0c6ac510e67f62f1824c439bfd11c209310e6bf66b0824c439bed96c149310e6ff4470524c439afd9ac149310e67f66f0524c439fbd186605310e7ef4609814c439fed06c605310e6f765f08b4c439bfc82c5ed310e77f46055b4c439bbd98c0ad310e6f765f02b4c439bed96c0ad310e6fd65702b4c439ffc1624c5210e77f44c58b48439dbd95362c210e72fe6b18b08439ddd9535ec210e77b654d6b08439df595356c210e77d64f15b08439cf79ac56c210e67f65713b08439cfd9536ac210e67f62f153804398ff8bc61d6a0e63fe2f2055a8398ff8bc6096a0e63fe2f2025a839efd1314856a0e63fe5720b5a8398ff92c82d6a0e6b7e5f0854a839aef96c2152a0e6bf64f0854a839afe92c2152a0e6bfc470854a8398ff9bc2152a0e7afa61d824a839ebe9826052a0e6b7e5f0814a839afd93c2052a0e6bfa4b0814a8398ff9bc2052a0e6bf64f0514a8398ff9bc1452a0e7bf2609314a839efd1814c52a0e7bf20b1314a839efd1314852a0e63fe8318b4a839cfd93182d2a0e63fe2f208468398ff8bc61d1a0e6b7e5f08546839aef96c2151a0e6bf64f08546839afe92c2151a0e6bfc47085468398ff9bc2151a0e63fe2f205468398ff8bc6091a0e6bfc47082468398ff9bc2091a0e6bbe5b05246839afd93c1491a0e6bfc47052468398ff9bc1491a0e63fe2f20246839ebf1866051a0e7afc6098146839eef06c6051a0e7bf85892146839aff18c4851a0e72fe6098b46839cef86c62d1a0e63fe8318b46839adf97c22d1a0e73fc6055b468398ffa0c56d1a0e63fe6312b468398ff95c4ad1a0e63fe8312b46839abf98c0ad1a0e6b7e5f02b46839aef96c0ad1a0e6bde5702b468398ff98c82d1a0e63fe5720b468398ff92c82d1a0e73f66b13b21429dfe12c46c850a73fc6b11b21429df692c56c830a73de6b15b20c29dfe12c46c830a73fc6b11b20c298ff9ac82d630a63fe6b20b54c29bee96c20d520a6fda5708354829bf
        else
          if i < 16 then
            0xa086afe8315362821abf9bc14d8a086afe5714362821abf89c80d8a087ade54d5b62821abf89c56d8a086afe8315b62821abf94c16d8a086afe4f05b62821ebb95452d8a087aee50d4b62821abf95c52d8a086afe8314b62821ebd9534ed8a0872fe52d3b62821abf95c4ed8a086afe5313b62821abf89c4ed8a086afe8313b62821abf95c0ed8a0872fe56c9b62821abf95c26d8a086afe4f09b62821abf89c82d8a086b7e272085e821adf89c6157a086b7e831855e821adfa0c6117a087b6e611545e821adf98c5517a086b7e831545e821e9f98460d7a086b7e271835e821adfa0c60d7a086b7e570835e821ed798554d7a087b5e551535e821edd98354d7a086b7e631535e821adf89c54d7a086b7e831535e821adf98c14d7a087b6e611435e821adf98c50d7a086b7e571435e821adf89c80d7a086bbe272085a821aef89c6156a086bbe831855a821aefa0c6116a087bae611545a821aef98c5516a086bbe831545a821eaf98460d6a086bbe271835a821aefa0c60d6a086bbe570835a821ee798554d6a087b9e551535a821eed98354d6a086bbe631535a821aef89c54d6a086bbe831535a821aef98c14d6a087bae611435a821aef98c50d6a086bbe571435a821aef89c80d6a086bde2718556821af7a0c6155a087bce6115456821af798c5515a086bde8315456821aef96c20d5a086bde5708356821afb94c20d5a086bfa4b08356821aff11c20d5a0863fe6f08356821ef598354d5a086bde6315356821af789c54d5a086bde8315356821af798c14d5a086bde5714356821cf795362d5a0863fe2718b568218ffa0c62d5a0863fe6309b568218ff93c26d5a086bde2720856821af7a0c6115a087ade6118356821af789c60d5a086bde8318356821af79bc20d5a087bce6114356821af798c50d5a086bde2720356821af789c62d5a086bde8318b56821af794c22d5a086bde4f08b56821ef398452d5a086bde6314b56821af7a0c52d5a087bd660d3b56821cf798b4ed5a0873de52d3b56821af798c4ed5a086bde5313b56821af789c4ed5a086bde8313b56821af798c0ed5a086bde6309b56821af793c26d5a086b7e5f08552821aef96c2154a086bfa4b08552821aff11c2154a086bee2720852821afb89c6154a086bee8318552821afba0c60d4a087bce6155352821ef998354d4a086bee6315352821afba0c54d4a086b7e5f0854e821aef96c2153a086bee530854e821afd93c2153a086bfa4b0854e821aff11c2153a0863fe6f0854e821ebd98460d3a086bf6271834e821afda0c60d3a086bf6570834e821ef598554d3a087bd6551534e821afd98c54d3a086bf6271534e821afda0c54d3a086bf6630534e821ef998450d3a086bf6631434e821afd95c50d3a086bf6272034e821cbf98462d3a0873f654d8b4e8218ff89c
          else
            if i < 17 then
              0xbee2715252881afba0c5494a207be65cd3252881afb97c4c94a206bee5713252881afba0c4c94a207bd6551534e881afd89c54d3a207bd654d524e881aef96c1493a206bee530524e881afd93c1493a2063fe6f0524e881efc9424c93a206bf6571324e881afd89c4c93a2063fe2717b4e881cf795256d3a2063fe2715b4e8818ffa0c56d3a2073f654c9b4e8818ff95c26d3a2063fe4b09b4e8818ff89c82d3a207bda5d5524a881ef69535492a207b7a1f1524a881afe89c5492a207bf25cd324a881afe95c4c92a206bfa271324a881cf795356d2a20737e1f15b4a8818ff89c56d2a2063fe8315b4a8818ff95c4ed2a2063fe2713b4a8818ffa0c4ed2a2073fa5489b4a8818ff95c26d2a2063fe4f09b4a8819fb94c26e031467ee5309b608518ff9ac26d821463fe6b20b608518ff9ac26d321472fe6b18b0c8518ff8bc6093a146bf64f0824e8518ff9bc2093a147bf2609324e851efc9424c93a146bf6631324e851afd89c4c93a1463fe2f2024e851abf98c0ad3a146b7e5f02b4e851aef96c0ad3a146bee5302b4e8518ff92c26d3a1463fe8309b4e8518ff92c82d3a1463fe2720b4e851aef96c20d2a146bde570834a851afb94c20d2a146bfa4b0834a851aff11c20d2a1463fe6f0834a851ebe9836092a146bfa271824a8518ff89c62d2a1463fe8318b4a851cfe9824ed2a1463fe6313b4a8518ff89c4ed2a1463fe8313b4a8518ff98c26d2a1463fe4f09b4a8518ff9ac26d870c63fe6b20b61c318ff9ac26d850c63fe6b09b608318ff9ac82d820c63fe6b09b54831cdf87b6ad520c677e5f20b54831abf89c6098a0c7afa6095262831abf98c1498a0c63fe6f052628318ff95c26d8a0c63fe4b09b628318ff89c82d8a0c6b7e271875e8318ff89c62d7a0c63fe6309b5e8318ff95c26d7a0c7ade61d8556831af789c6155a0c6bde57082568318ff9bc2095a0c7bda6095256831ef69725495a0c6bde6315256831ed787c5495a0c6bde27152568318ff89c62d5a0c63fe8318b568318ff89c5ed5a0c63fe6309b568318ff92c26d5a0c7afa61d824a831afe89c6092a0c63fe2718b4a8318ffa0c62d2a0c73fa6095b4a8318ff98c56d2a0c737e1f15b4a8318ff89c56d2a0c63fe8315b4a8318ff98c26d2a0c63fe5709b4a8318ff9ac26d850863fe6b09b60c21cf79ac56c830863fe6b09b54c218ff9ac82d530867ee5309b80c21abf89c8218a086afe2718562821abfa0c6158a086afe8318462821ebb9845518a086afe6315462821abf89c60d8a086afe8318362821abf95c20d8a087ade6155362821ebd98354d8a086afe6315362821abf98c14d8a0863fe6f05362821ebb98450d8a086afe6314362821cbf98526d8a0863fe5709b628218ff93c26d8a0863fe2720b62821abfa0c5518a087ade5515362821abf89c54d8
            else
              0x51b56832cf796b46d5a0cabde6311b56832af796c46d5a0cabde2711b56832af7a0c46d5a0cabde6301b56832cf791b26d5a0cabde6309b56832af796c26d5a0cabde4709b56832af789c82d5a0cabee2720852832afb89c6154a0cabee8318552832eeb9865954a0cbbce6156552832afb98c5954a0cabee2716552832afba0c5954a0cabee2720552832ebb9866054a0cbbae1b18152832afb89c6054a0cabee8318152832efb1815854a0cabee6316152832ef39655454a0cbbec6055152832afb98c5454a0cabee5b15152832afb89c5454a0cabee8315152832ebf1866051a0cbbbc1b18146832aff09c6051a0cabfc8318146832aff18c5851a0cbbdc5955146832aff18c5451a0cabfc5b15146832aff09c5451a0cabfc8315146832cbf98662d1a0cb3fc5858b46832cff15162d1a0cb3be1b18b468328ff89c62d1a0ca3fe8318b46832cf796556d1a0cb3fc6055b468328ff98c56d1a0ca3fe2715b468328ffa0c56d1a0cb3fc5449b468328ff98c26d1a0ca3fe5709b46832aff09c8211a0cabfc2718546832aff20c6151a0cbbbc6196546832ef71855951a0cabfc6316546832aff09c5951a0cabfc8316546832aff09c8151a0cbafc6198b46832eef06c62d1a0cabfc2718b46832aff20c62d1a0cabfc5708b46832cff18b5ad1a0cabfc6316b46832ef716556d1a0cb3fc62d5b46832aff18c56d1a0cabfc5b15b46832aff09c56d1a0cabfc8315b46832aff18c16d1a0cb3fc56c9b46832aff18c26d1a0cabfc5709b468328ff9ac26d732063fe6b09b54c818ff9ac82d532067ee5309b80c81adf9ac1ed522063fe6b09b54881cdf87b6ad5220677e5f20b548818ff9ac26d322073de6b15b0c881adf89c5cd7a20737e5d49b5e881cdf97326d7a2063fe5709b5e8818ff93c26d7a206b7e831545e881ed795454d7a206b7e271535e881adfa0c54d7a206b7e571435e881adf89c80d7a207b5e54d525e881edb9545097a207b6e50d425e881adf95c5097a206b7e831425e881ede9424c97a206b7e571325e881adf94c4c97a206b7e271325e881adfa0c4c97a206b7e2715b5e881adf94c16d7a206b7e4f05b5e881adf89c4ed7a206b7e5703b5e881adf94c0ad7a206b7e4f02b5e881cdf95b26d7a20737e4ec9b5e881adf95c26d7a206b7e4f09b5e881ef597354d5a206bde2715356881ef69725495a207b5e1f15256881af789c5495a206bde5713256881abf98c0c95a206b7e5f03256881aef96c0c95a206bde5703256881afb94c0c95a206bfc47032568818ff9bc0c95a2063fe2717b568818ff93c26d5a2063fe4b09b56881aef96c1494a206bee8317352881ef997354d4a206bee5f15352881afba0c54d4a207b6e5cd7252881ef39755494a207bce54d5252881efa9725494a206bee5f15252881edb87c5494a206
  else
    if i < 27 then
      if i < 22 then
        if i < 20 then
          if i < 19 then
            0x80c828ff9ac26d5120a5fe2715b504828ff9ac26d3120a3fe6b20b4c482efd1414c53a20abf6571314e882cfd93126d3a20a3fe4709b4e8828ff89c82d3a20abfc57131468828ff89c56d1a20a3fe8315b468828ff95c4ed1a20a3fe2713b468828ffa0c4ed1a20b3fc5449b468828ff95c26d1a20a3fe4f09b468828ff9ac26d850ca3fe6b09b59432aef9ac1ad810ca3fe6b09b60432cef86b6ad810ca7be5b20b604328ff9ac26d510caafe2720862832abf89c6158a0caafe8318562832eaf9865958a0cbade6156562832abf98c5958a0cbabe1b18162832abf89c6058a0caafe8318162832ebf1815858a0caafe6316162832ebf1815458a0caafe6315162832cbf98526d8a0cb2fe6049b628328ff95c26d8a0ca3fe4709b628328ff89c82d8a0caafe2716562832abfa0c5958a0caafe2720562832eb79655458a0caafe5b15162832abf89c5458a0caafe8315162832eaf9655ad8a0caafe2716b62832abfa0c5ad8a0cbade5955b62832abf96c56d8a0caafe2715b62832abfa0c56d8a0caafe5b05b62832abf91c16d8a0cbafc5851b62832ebf15146d8a0cb2fe5ad1b62832abf96c46d8a0cbabe1b11b62832abf95c46d8a0caafe2711b62832abfa0c46d8a0caafe5701b62832cbf95b26d8a0cb2fe46c9b62832abf96c26d8a0caafe5709b62832abf91c26d8a0caafe2720b62832adf89c8217a0cab7e271855e832adfa0c6157a0cbb3e619655e832ed79855957a0cab7e631655e832adf89c5957a0cab7e831655e832adf89c8157a0cba7e619815e832ecf86c6057a0cab7e271815e832adfa0c6057a0cbb7c605615e832adf98c5857a0cbb5e595515e832edf1815457a0cab7e631515e832adf96c5457a0cab7e271515e832adfa0c5457a0cabbe271655a8328ff89c62d6a0cb3be5949b5a8328ff98c26d6a0ca3fe5709b5a832aef89c8216a0cabbe271855a832aefa0c6156a0cabbe272055a832eef1815456a0cabbe631515a832aef89c5456a0cabbe831515a832aef89c62d6a0cabbe5708b5a832aef89c56d6a0cabbe6305b5a832aef95c06d6a0cb3be56c9b5a832aef98c26d6a0cabbe5709b5a832af789c6155a0cabde8318556832ee79865955a0cabde6316556832af789c5955a0cabde8316556832af789c8155a0cbbdc6055156832af798c5455a0cabde5b15156832af789c5455a0cabde8315156832cf796562d5a0ca3fe2718b568328ffa0c62d5a0ca3fe2716b56832cf795126d5a0ca3fe6309b568328ff91c26d5a0ca3fe2720b56832af789c8215a0cbade6198156832ee786c6055a0cabde2718156832af7a0c6055a0cbbdc6056156832af798c5855a0cabde2718b56832af7a0c62d5a0cabde4708b56832ee79865ad5a0cb3de62d6b56832af798c5ad5a0cabde2716b56832af7a0c5ad5a0cbbdc6
          else
            0x1cfe92056d2a0c61ff2715b4a831a7f89c8210a0c63fe6315b428318ff98c4ad0a0c63fe5712b4283187fdac26d850861ff6b09b54c2197bd4c26e030868ff2720862821a3fc9c6158a086a7f5f08362821aafd6c20d8a086adf5708362821abbd4c20d8a086afe4308362821abf98c5418a086afe6313062821cbf98082d8a0861ff2720b62821a3fc9c54d8a087af654d3062821abf95c4c18a0868ff2715b62821a9fd7c0ed8a086abf5b03b62821ab7d5c0ed8a086aef5303b62821abed2c0ed8a086afd4703b62821abf90c0ed8a0872fe56d0b62821abf95c42d8a086afe4f10b62821cbf90b82d8a0868ff2720b62821c3fc9c82d8a08697f272085e821a5fc9c6157a086b3f5b0835e821ad7d5c20d7a086b6f530835e821aded2c20d7a086b7d470835e821adf90c20d7a08637f6f0835e821a5fc9c54d7a087a7e821805e821e9f9856017a086b7e631505e821edd9534c17a086b7e631305e821adf95c4c17a0869bf272085a821a6fc9c6156a086b3f5f0835a821ae7d5c20d6a086baf530835a821aeed2c20d6a086bbd470835a821aef90c20d6a0863bf6f0835a821a6fc9c54d6a0869bf272035a821eafa086016a087abe615805a821aef98c5416a087bb654d305a821eeda034c16a086bbe631305a821aef95c4c16a0869df2718556821a77c9c54d5a087ade6158056821af798c5415a087bd654d3056821af795c4c15a0872fe6018b5682187fc9c62d5a0869df2720856821ad7d7c20d5a086b9f5b08356821af3d4c20d5a086bdb4b08356821af751c20d5a086bde43083568218f7dbc20d5a0869df2720356821eb7a086015a087bd680d3056821af798c4c15a087ade6018b56821a77c9c62d5a087bd64c13b56821a77c9c4ed5a086bde6310b56821af793c42d5a0869ef2720852821a7bc9c6154a087aee8218052821ebb9856014a086bee6315052821addd7c20d3a086bb75b0834e821af5d5c20d3a086be7530834e821afd90c20d3a0869f7271534e821afd98c4c13a086bf6571304e821cfd93056d3a0861ff2715b4e821cfd93082d3a0861ff2720b4e821a7dc9c8213a0869f7271854e821ebda086013a087af6615804e821afd98c5413a086b775f08b4e821aedd6c22d3a086bd75708b4e821af9d4c22d3a086bf34b08b4e821afd51c22d3a086bf64308b4e821a7dc9c56d3a0873f656d0b4e821afd98c42d3a086bf65710b4e821cfd90b82d3a0869f72720b4e821c7dc9c82d3a0869fe2720842821a7f89c6150a086b7e5f08342821aef96c20d0a086bde5708342821afb94c20d0a086bfa4b08342821aff11c20d0a0863fe6f08342821a7f89c54d0a0869fe2720342821cbfa0862d0a0872fe6158b428218ff98c56d0a0873f654d3b42821cfda034ed0a0863fe6313b428218ff95c4ed0a0867ee5309b
        else
          if i < 21 then
            0x9605ad5a0ca9df2716b56832ef711046d5a0ca9df2711b56832cf791b42d5a0cabde6310b56832af796c42d5a0cabde4710b56832cf790b82d5a0ca9df2720b56832c77c9c82d5a0ca9ef2716552832a7bc9c8154a0ca9ef2718152832a7bc9c5454a0cbaee6158052832ebb9816014a0cbbae5956052832eeb9615814a0cabee6316052832ef3a055414a0cbbce5455052832afb98c5414a0cabee5b15052832efb1514414a0cabee6311052832afb96c4414a0cabee5711052832a7f49c6051a0ca9fd2715146832ebf1816011a0cbbbc5856046832ef71515411a0cabfc6311046832aff16c4411a0cabfc5711046832cbf98062d1a0ca1ff2718b46832cf795056d1a0cb3fc4415b4683287fc9c56d1a0ca9fd2716546832a7f49c8151a0cbafc6158046832eef1655811a0cabfc6316046832ef72055411a0cabfc6315046832aff16c5411a0cbafc6018b46832a7f49c62d1a0cbbbc5816b46832ef715056d1a0ca9fd2715b46832cff15b42d1a0cabfc6310b46832aff16c42d1a0cabfc5710b46832a7f89c5950a0ca9fe2720542832a7f89c6050a0ca9fe2715142832cbf98562d0a0cb2fe6058b42832cf7a0556d0a0cb3de5455b428328ff98c56d0a0cb3fc5451b428328ff98c46d0a0ca3fe5711b4283287fdac26d732065ef5309b80c8187fdac26d5220697f271735e881a5fc9c80d7a20637f2f1525e881edd9534c17a207b7680d305e881adf95c4c17a207b7a549205e881adf95c4817a206b7e4f1205e881a5fc9c56d7a20697f2713b5e881adf90c0ed7a2069df2715256881ef59534c15a206bde5713056881ef69524815a206bde571205688187fc9c5ed5a2069ef2715252881edb9755c14a206bee5f15052881efa9524814a206bee5f12052881afb95c4814a206bf6571304e881afd93c4813a2061ff2717b4e881cfd93056d3a2073f64c20b4e88187fc9c82d3a2069fb271524a881afe95c4812a206bfa4f1204a881cfe92056d2a2061ff2715b4a881a7f89c80d0a2073f654d3b428818ff95c4ed0a2073fa5492b428818ff95c4ad0a2063fe4f12b42881c3fd8a26e081465ef5309b80c5197bd4c26d821461ff6b09b60851a7dc9c80d3a146bf64f1204e851cfd93082d3a1461ff2720b4e851a7ec9c6092a146bfa631204a85187fc9c62d2a1469fe2720842851adf97c20d0a146bbe5b08342851af795c20d0a146bee5308342851afe92c20d0a146bfc47083428518ff9bc20d0a1463fe6312b428518ff93c4ad0a1461ff6b09b61c3187fdac26d520c6afe6312062831cbf98082d8a0c61ff2720b62831a5fc9c61d7a0c61ff2718b5e831a77c9c5495a0c7ade6158056831af798c5415a0c7bda5492056831af795c4815a0c72fe6018b5683187fc9c5ed5a0c717f81c9b5683187fd2c26d5a0c6bfa631204a83
          else
            0x6d530863ff6b20b54c21abfe0c6158a086aff8318362821abfd5c20d8a087adf6155362821ebdd8354d8a086aff6315362821a7fc9c56d8a086aff8315362821eb7d5356d8a0878ff2715b62821abfe0c56d8a087af754d3b62821abfd5c4ed8a086aff8313b62821abfd5c0ed8a086b7f831855e821adfe0c60d7a086b7f570835e821ed7d8554d7a087b7760d535e821adfd8c54d7a086b7f831535e821aefe0c6156a086bbf831835a821aefd5c20d6a087b9f615535a821eedd8354d6a086bbf631535a821aefe0c54d6a086bdf8318356821afbe0c6154a0869ff272084e821a7fc9c6153a086bf7831834e821afdd5c20d3a087bd7615534e821afdd8c54d3a086bf7831534e821cfdd5362d3a0863ff8318b4e821afde0c6153a086bf78318b4e821afdd5c22d3a087bd76155b4e821cfdd8b56d3a086bf76315b4e821afde0c56d3a086bfe8318542821affa0c60d0a086bfe5708342821ef798554d0a087bf660d5342821aff98c54d0a086bfe831534282187fdac26d5120bbdc5455046882efd1314c11a20a1ff2715b46882a7f89c8150a20a3fe6f05342882cfd9314ed0a20b3fc5451b428828ff95c46d0a20a3fe4f11b4288287fdac26d650ca1ff6b09b6043287fdac26d510ca8ff2718162832abf98c5818a0caafe6315062832abf98c4418a0cb2fe6020b62832a3fc9c5958a0ca8ff2715162832eaf9655818a0cbabe5856062832eb79515418a0caafe5b15062832ebf1514418a0caafe5b11062832abf95c4418a0caa7f5f05b62832aafd6c16d8a0caafd4705b62832abf90c16d8a0ca8ff2711b62832cbf95b42d8a0cb2fe46d0b62832abf96c42d8a0caafe5710b62832abf91c42d8a0cb2fe42e0b62832a3fc9c82d8a0cb0ff2720b62832a5fc9c5957a0ca97f271815e832a5fc9c5457a0cba7e615805e832e9f9816017a0cbb3e595605e832ecf9615817a0cab7e631605e832ed79515417a0cab7e631505e832adf96c5417a0cbb7c545105e832adf98c4417a0cab7e5b1105e832adf95c4417a0ca9bf271655a832a6fc9c8156a0ca3bf2f1815a832a6fc9c5456a0cbabe615805a832eaf9816016a0cbb9e815505a832ee79515416a0cabbe631505a832eef1514416a0cabbe631105a832aef95c4416a0cab3f5f08b5a832ae7d5c22d6a0cabbd4708b5a832aef90c22d6a0ca9bf2715b5a832aef90c16d6a0ca9df2716556832a77c9c5455a0cbade6158056832ee79655815a0cabde6315056832af796c5415a0cbbdc5451056832af795c4415a0cb2fe6018b5683287fc9c5ad5a0cb3de5420b5683287fc9c82d5a0ca9df2718156832eb79816015a0cbb9e5856056832af798c5815a0cabde6311056832af796c4415a0cbade6018b56832ad7d7c22d5a0cab9f5b08b56832af751c22d5a0cabde4308b56832ee7
      else
        if i < 24 then
          if i < 23 then
            0xd800d700d600d500d400d300d200d100d000cf00ce00cd00cc00cb00ca00c900c800c700c600c500c400c300c200c100c000bf00be00bd00bc00bb00ba00b900b800b700b600b500b400b300b200b100b000af00ae00ad00ac00ab00aa00a900a800a700a600a500a400a300a200a100a0009f009e009d009c009b009a0099009800970096009500940093009200910090008f008e008d008c008b008a0089008800870086008500840083008200810080007f007e007d007c007b007a0079007800770076007500740073007200710070006f006e006d006c006b006a0069006800670066006500640063006200610060005f005e005d005c005b005a0059005800570056005500540053005200510050004f004e004d004c004b004a0049004800470046004500440043004200410040003f003e003d003c003b003a0039003800370036003500340033003200310030002f002e002d002c002b002a0029002800270026002500240023002200210020001f001e001d001c001b001a0019001800170016001500140013001200110010000f000e000d000c000b000a000900080007000600050004000300020001000029ff272054e882a7fc9c5453a20a9ff272054688297fc9c62d650caaff8318562832eafd865958a0cbadf6156562832abfd8c5958a0ca9ff2715162832a7fc9c46d8a0caaff8316562832eafd655ad8a0caaff8316b62832eb7d6556d8a0caaff5b15b62832abfe0c56d8a0caaff5b05b62832adfe0c6157a0cbb3f619655e832ed7d855957a0cab7f631655e832adfe0c5957a0ca9ff272055a832aefe0c6156a0cabbf5708b5a832aefd8c16d6a0ca9ff2718156832afbe0c6154a0cbbaf6196552832ef3d855954a0cabef6316552832afbe0c5954a0ca9ff2716546832a7fc9c8151a0cabfd8318546832eef5865951a0cbbdd6156546832aff58c5951a0cabfd8316546832affa0c6150a0cbbbe6196542832ef79855950a0cabfe6316542832adfe0c4c97a207bd75cd5356881ef6d725495a207beb5c95252881a7fc9c5493a207bf35cd324a8818ffe0c4ed2a2073fb6b12b20c51b7bd4c26d821469ff6b09b60851c7fd8a26d821465ff4f09b60851c7fc9b6ad821469ff271ab608518ffdac82d82147bf3609324e851afdd8c4c93a1469ff272084a851aefd6c20d2a146bdf570834a851afbd4c20d2a146bfb4b0834a851aff51c20d2a146bfe430834a8518ffdbc20d2a1469ff272034a851ebed836092a1479fb271824a851c7fc9c62d2a1463ff8318b4a851cfed824ed2a1463ff6313b4a8518ffe0c4ed2a1463ff6b20b60831a7fc9c61d8a0c7afb6095262831a7fc9c5498a0c69ff2717b62831eb7d876155a0c7bdb5c95256831a7fc9c8212a0c69ff271874a831ebed876092a0c63ff8318b4a83197fd8c2
          else
            0xd802d702d602d502d402d302d202d102d002cf02ce02cd02cc02cb02ca02c902c802c702c602c502c402c302c202c102c002bf02be02bd02bc02bb02ba02b902b802b702b602b502b402b302b202b102b002af02ae02ad02ac02ab02aa02a902a802a702a602a502a402a302a202a102a0029f029e029d029c029b029a0299029802970296029502940293029202910290028f028e028d028c028b028a0289028802870286028502840283028202810280027f027e027d027c027b027a0279027802770276027502740273027202710270026f026e026d026c026b026a0269026802670266026502640263026202610260025f025e025d025c025b025a0259025802570256025502540253025202510250024f024e024d024c024b024a0249024802470246024502440243024202410240023f023e023d023c023b023a0239023802370236023502340233023202310230022f022e022d022c022b022a0229022802270226022502240223022202210220021f021e021d021c021b021a0219021802170216021502140213021202110210020f020e020d020c020b020a020902080207020602050204020302020201020001ff01fe01fd01fc01fb01fa01f901f801f701f601f501f401f301f201f101f001ef01ee01ed01ec01eb01ea01e901e801e701e601e501e401e301e201e101e001df01de01dd01dc01db01da01d901d801d701d601d501d401d301d201d101d001cf01ce01cd01cc01cb01ca01c901c801c701c601c501c401c301c201c101c001bf01be01bd01bc01bb01ba01b901b801b701b601b501b401b301b201b101b001af01ae01ad01ac01ab01aa01a901a801a701a601a501a401a301a201a101a0019f019e019d019c019b019a0199019801970196019501940193019201910190018f018e018d018c018b018a0189018801870186018501840183018201810180017f017e017d017c017b017a0179017801770176017501740173017201710170016f016e016d016c016b016a0169016801670166016501640163016201610160015f015e015d015c015b015a0159015801570156015501540153015201510150014f014e014d014c014b014a0149014801470146014501440143014201410140013f013e013d013c013b013a0139013801370136013501340133013201310130012f012e012d012c012b012a0129012801270126012501240123012201210120011f011e011d011c011b011a0119011801170116011501140113011201110110010f010e010d010c010b010a010901080107010601050104010301020101010000ff00fe00fd00fc00fb00fa00f900f800f700f600f500f400f300f200f100f000ef00ee00ed00ec00eb00ea00e900e800e700e600e500e400e300e200e100e000df00de00dd00dc00db00da00d900
        else
          if i < 25 then
            0xd804d704d604d504d404d304d204d104d004cf04ce04cd04cc04cb04ca04c904c804c704c604c504c404c304c204c104c004bf04be04bd04bc04bb04ba04b904b804b704b604b504b404b304b204b104b004af04ae04ad04ac04ab04aa04a904a804a704a604a504a404a304a204a104a0049f049e049d049c049b049a0499049804970496049504940493049204910490048f048e048d048c048b048a0489048804870486048504840483048204810480047f047e047d047c047b047a0479047804770476047504740473047204710470046f046e046d046c046b046a0469046804670466046504640463046204610460045f045e045d045c045b045a0459045804570456045504540453045204510450044f044e044d044c044b044a0449044804470446044504440443044204410440043f043e043d043c043b043a0439043804370436043504340433043204310430042f042e042d042c042b042a0429042804270426042504240423042204210420041f041e041d041c041b041a0419041804170416041504140413041204110410040f040e040d040c040b040a040904080407040604050404040304020401040003ff03fe03fd03fc03fb03fa03f903f803f703f603f503f403f303f203f103f003ef03ee03ed03ec03eb03ea03e903e803e703e603e503e403e303e203e103e003df03de03dd03dc03db03da03d903d803d703d603d503d403d303d203d103d003cf03ce03cd03cc03cb03ca03c903c803c703c603c503c403c303c203c103c003bf03be03bd03bc03bb03ba03b903b803b703b603b503b403b303b203b103b003af03ae03ad03ac03ab03aa03a903a803a703a603a503a403a303a203a103a0039f039e039d039c039b039a0399039803970396039503940393039203910390038f038e038d038c038b038a0389038803870386038503840383038203810380037f037e037d037c037b037a0379037803770376037503740373037203710370036f036e036d036c036b036a0369036803670366036503640363036203610360035f035e035d035c035b035a0359035803570356035503540353035203510350034f034e034d034c034b034a0349034803470346034503440343034203410340033f033e033d033c033b033a0339033803370336033503340333033203310330032f032e032d032c032b032a0329032803270326032503240323032203210320031f031e031d031c031b031a0319031803170316031503140313031203110310030f030e030d030c030b030a030903080307030603050304030303020301030002ff02fe02fd02fc02fb02fa02f902f802f702f602f502f402f302f202f102f002ef02ee02ed02ec02eb02ea02e902e802e702e602e502e402e302e202e102e002df02de02dd02dc02db02da02d902
          else
            if i < 26 then
              0x640b570b4a0b3d0b300b230b190b090aff0af50aeb0adb0ad10ac70aba0aad0aa00a930a860a760a6c0a620a580a480a3e0a340a240a170a0a09fd09f009e309d309c309b909af09a5099b098b097e097109640957094a093a09300926091c0912090808fe08f408e408da08ca08c008b608ac08a2089208850878086b085b084e08410834082a08200816080c080207f807e807de07d407c707bd07b307a9079c078f077f076f0765075b07510747073d0736072c07220718070e070406f706ed06e306d906cf06c506b806b106a4069a06900686067c0672066b066a0669066806670666066506640663066206610660065f065e065d065c065b065a0659065806570656065506540653065206510650064f064e064d064c064b064a0649064806470646064506440643064206410640063f063e063d063c063b063a0639063806370636063506340633063206310630062f062e062d062c062b062a0629062806270626062506240623062206210620061f061e061d061c061b061a0619061806170616061506140613061206110610060f060e060d060c060b060a060906080607060606050604060306020601060005ff05fe05fd05fc05fb05fa05f905f805f705f605f505f405f305f205f105f005ef05ee05ed05ec05eb05ea05e905e805e705e605e505e405e305e205e105e005df05de05dd05dc05db05da05d905d805d705d605d505d405d305d205d105d005cf05ce05cd05cc05cb05ca05c905c805c705c605c505c405c305c205c105c005bf05be05bd05bc05bb05ba05b905b805b705b605b505b405b305b205b105b005af05ae05ad05ac05ab05aa05a905a805a705a605a505a405a305a205a105a0059f059e059d059c059b059a0599059805970596059505940593059205910590058f058e058d058c058b058a0589058805870586058505840583058205810580057f057e057d057c057b057a0579057805770576057505740573057205710570056f056e056d056c056b056a0569056805670566056505640563056205610560055f055e055d055c055b055a0559055805570556055505540553055205510550054f054e054d054c054b054a0549054805470546054505440543054205410540053f053e053d053c053b053a0539053805370536053505340533053205310530052f052e052d052c052b052a0529052805270526052505240523052205210520051f051e051d051c051b051a0519051805170516051505140513051205110510050f050e050d050c050b050a050905080507050605050504050305020501050004ff04fe04fd04fc04fb04fa04f904f804f704f604f504f404f304f204f104f004ef04ee04ed04ec04eb04ea04e904e804e704e604e504e404e304e204e104e004df04de04dd04dc04db04da04d904
            else
              0x82167e167a16761672166e166a1663165f165b16541650164c16481644163d1636162f162b16271623161f161b16141610160c16081604160015fc15f815f415f015ec15e815e415dd15d915d515d115cd15c915c515be15ba15b615b215ae15aa15a615a2159e159a1593158c158815841580157c157815741570156c15681564155d15591552154e15471543153f153b15371533152c152815241520151c151815141510150c15081504150014fc14f514f114ed14ec14e814e114dd14d914d514d114cd14c914c214b514b114ad14a914a514a1149d149914951491148a1486147c14751471146a1466145f145b1454144d144914451441143d14391435142e142a14261422141e141a14161412140e140a1406140213fe13fa13f613f213ee13ea13e613e213de13da13d613d213ce13ca13c613c213be13ba13b613b213ae13aa13a613a2139e139a13961392138e138a13861382137e13771373136f136513611354134d134913451341133d13391335132e132a13261322131e131a13161312130b12fe12fa12f612f212ee12ea12e612e212de12da12d612d212ce12ca12c912c512c112bd12b612b212ae12aa12a6129f129b12971293128f1288127e127a12761272126e12671260125912551251124a1243123f123b12371233122f122b12271223121f121b12171213120f1208120111fd11f611f211ee11ea11e611e211de11da11d611d211cb11c411c011bc11b811b411b011a911a2119e119a11961192118e118a11861182117e117a11761172116b11671163115f115b11571153114f114b11471143113f113b11371133112f112b11271123111f111b11171113110f110b1107110010fc10f810f410f010e910e510de10d710d010cc10c510c110bd10b910b510b110ad10a910a5109e109a10961092108b10871083107f107b10771073106f106b10671063105f105b10541050104c104810441040103c10381034102d10261022101e10171013100c100810010ffa0ff30fec0fe50fde0fda0fd60fd50fd10fcd0fc90fc50fc10fbd0fb90fb20fae0faa0fa60fa20f9e0f9a0f960f920f8b0f870f830f7f0f7b0f770f730f6f0f680f640f5d0f590f550f510f4d0f490f450f3e0f310f2d0f290f250f210f1d0f190f150f110f0a0f030eff0efb0ef40eed0ee90ee50ee10edd0ed90ed50ece0eca0ec60ec20ebe0eba0eb60eb20eae0eaa0ea60ea20e9e0e970e930e8f0e8b0e870e800e790e750e6e0e670e600e5c0e520e480e3e0e310e210e140e070dfd0df30de60dd90dcc0dbc0daf0da20d950d850d750d650d580d4e0d3e0d370d2a0d200d130d060cf90cec0cdf0cd20cc80cbb0cb10ca40c9a0c8d0c800c730c690c590c4c0c3f0c350c2b0c1b0c0e0c010bf40be70bd70bca0bbd0bb00ba60b9c0b920b880b7e0b740b
    else
      if i < 31 then
        if i < 29 then
          if i < 28 then
            0x32202e202a20262022201e201a20162012200b200720031fff1ff81ff11fed1fe91fe51fde1fd71fd01fcc1fc81fc11fbd1fb91fb51fb11fad1fa91fa51fa11f9a1f961f921f8e1f871f831f7f1f7b1f771f701f691f651f611f5d1f561f4f1f481f441f401f3c1f381f341f301f2c1f281f241f201f1c1f181f111f0a1f061f021efe1efa1ef31eef1eeb1ee71ee01edc1ed51ece1ec71ec31ebf1ebb1eb41ead1ea91ea51e9e1e971e901e891e851e811e7a1e731e6c1e681e641e5d1e561e4f1e481e441e401e3c1e351e311e2d1e291e251e1e1e171e131e0f1e0b1e071e001dfc1df81df41df01de91de51dde1dd71dd01dcc1dc81dc41dc01dbc1db51db11dad1da91da51d9e1d971d931d8f1d881d841d801d7c1d781d741d701d6c1d681d611d5d1d591d551d511d4a1d431d3c1d351d311d2a1d231d1f1d1b1d171d131d0f1d0b1d071d031cff1cfb1cf71cf31cef1ceb1ce71ce31cdf1cd81cd41ccd1cc91cc51cc11cbd1cb91cb51cb11cad1ca91ca21c9e1c9a1c931c8f1c8b1c841c7d1c761c6f1c6b1c671c631c5f1c581c541c4d1c491c451c411c3d1c391c351c311c2d1c291c221c1e1c1a1c131c0f1c0b1c071c031bff1bf81bf41bf01be91be51be11bda1bd61bcf1bcb1bc71bc01bb91bb51bb11bad1ba91ba51ba11b9d1b991b951b911b8d1b801b7c1b781b741b6d1b661b621b5e1b5a1b561b521b4e1b4a1b461b421b3b1b371b331b2f1b281b241b201b1c1b181b141b101b091b051b011afd1af91af51af11aed1ae91ae51ae11add1ad91ad51ace1aca1ac61ac21abe1aba1ab61ab21aae1aaa1aa61a9f1a9b1a971a931a8f1a881a811a7a1a761a721a6e1a6a1a661a5f1a5b1a541a501a4c1a451a3e1a3a1a361a2f1a2b1a271a231a1c1a181a141a101a091a051a0119fd19f919f219eb19e719e319df19d819d119ca19c619c219bb19b419b019ac19a819a419a0199919951991198d19891985197e197a19761972196e19671960195c19581951194a19461942193e193a19361932192e192a19261922191e191a1916190f190b1907190018fc18f818f418ed18e618df18db18d718d318cf18c818c418c018bc18b818b418b018ac18a518a1189d18961892188e188a1883187c18751871186d18691865185e185a18561852184e184a1843183c18381834182d182918251821181d1816180f180b1807180317fc17f517f117ed17e917e517e117dd17d617d217ce17ca17c317bf17bb17b717b317af17ab17a417a0179c1795178e17871783177f177b17771773176f176b17671763175f175b17571753174f174b1744173d173917351731172d172917251721171d17191712170e170a170616ff16f816f116ed16e916e516de16d716d016cc16c516be16ba16b616af16a816a1169d169916951691168d168916
          else
            0x92d022cfb2cf42cf02ce92ce22cd82cd42cd02cc92cc52cc12cbd2cb92cb52cae2ca42c9a2c902c892c822c7b2c742c732c662c5c2c552c512c4d2c492c452c412c3d2c302c232c192c0f2c052bfe2bfa2bf62bf22beb2bea2bda2bd62bc62bbf2bb52bae2baa2ba32b9f2b9b2b972b932b8f2b8b2b842b802b7c2b6f2b652b5b2b512b4a2b462b452b412b3d2b392b322b2e2b212b112b012af72ae42ae02ad92acf2ac82ac12aba2ab32aaf2aab2aa42a9d2a9c2a8f2a882a842a802a7c2a752a712a6a2a602a532a492a3f2a382a2e2a2a2a202a1c2a182a142a102a0f29ff29fb29eb29e129da29d029c929c529be29ba29b629b529b129ad29a929a5299e299a2996298f29852981297d29792972296e296a2966295f295b2957295029402936292f292829242923291f291b2917290d2909290528fb28f728f028ec28e828db28d428cd28c628bf28bb28ba28b628b228ae28a728a3289c288f28882881287a2873286f286b2864286028592852284b28442840283c283828342830282c2825281e281a28162812280e2807280327ff27f827f427f327e927e227de27da27d627cf27cb27c727c027bc27b527ae27aa279d278d2780277c2775277127672760275c274f274b27472743273f273b27372733272f272b2724271d271627122711270426fd26f626ef26eb26e726e326dc26d826d126cd26c326bf26bb26b426b026ac26a826a1269a269326862679266c26622658264e2644263d263926322631262426172613260c25ff25f525eb25e125d725cd25c325bc25b825b425ad25ac259f259b258e25812577256d25632559254f2548253e25342533252f252b252725202519250c24ff24f524eb24e124d724cd24c624bc24b224ab24aa24a624a2249e249a2493248c2485247e247a24762472246b246724602459244f2445243b2431242724202416240f240e240a240323ff23f823f423ed23e923e223d523c823c723c323bf23b523ab23a1239723902386237f23782374236d2369235f2352234523442340233c23322328231e2314230a230022f922ef22eb22e422dd22d922d222ce22c122b422aa22a02296228c22822278227122672260225f225b22572253224f22482241223d223922352231222d22292222221e221a2213220c22082204220021fc21f821f421f021ec21e521de21d721d321cf21c521c121bd21b921b521ae21a721a0219921952191218a2183217c21752171216d216921652161215d21592155214e214a21462142213b21372133212c212821242120211c21182111210a210320ff20fb20f420f020ec20e820e420e020dc20d820d420d020cc20c820c420bd20b620b220ae20aa20a6209f209b20972093208c20882081207a2073206f206b20672063205f205b20542050204c204820442040203920
        else
          if i < 30 then
            0x3061305a305330493042303b3034303030293025301e30173010300930052ffe2ff72ff02fe92fe22fde2fd72fd02fc92fbf2fb82fb12faa2fa32f9c2f982f912f8a2f832f7c2f752f6e2f6a2f632f5c2f582f512f4a2f432f3c2f382f342f2d2f292f222f1b2f172f132f0c2f052f042f002ef92ef82ef42eed2ee62edf2ed82ed12eca2ec32ebc2eb22eb12ead2eac2ea52ea12e9a2e932e8c2e852e812e7a2e732e6f2e6b2e642e5d2e5c2e552e482e412e3a2e332e2c2e252e212e1a2e162e0f2e082e042dfd2df92df22deb2de42ddd2dd62dcf2dc82dc42dbd2db62daf2da82da12d9a2d962d8f2d882d812d7a2d732d6c2d652d5e2d572d502d492d452d3e2d372d302d292d222d1e2d172d102d
          else
            0x2bc01032c2df22bc01323722bc02e01e0142d42c4e47c0102d42c4e47c0102d42c4e47c01323722bc02e01e01723722b402601601723722bc02e01e01432c2d42cbc01032f22bc00f23722bc02e01e01511c2d4832c2ab223c01032c277c00c32c2d42cbc01032c2d42cbc01032c2d42cbc01032c2d42c9c01032c2d42cbc01032c2d42cbc0102dc2cbc00c2cb22f221c0101102bf244c2cb22f223c0102dc2cbc00c32c2cb223c01032c2cb221c01032c2cb223c01111f220e00f22f223c02e01e014e3f22f22340120a322f221601032c277400c32f223400f22f22340260160150a322f222601211e0a3221601211e0a3221601211e0a322160102d82c82c0e2bc0142d82c0e2bc0102d82c0e2bc0102d82c0e29c01211f234e00c2d82c7c00c2d82c7c00c2d82c5c00c2d82c7c00c2d82c7c00c2d82c82c0e2bc0142d82c0e2bc0102d82c0e2bc0102d82c0e29c0102d82c0e2bc0102d82c0e2bc0102db23722cf23722fc02e01e01511f234e00c2d82c7c00c2d82c7c00f23722fc02e01e01611f234e00e11f234e00c2d82c0e2bc0102d82c0e2bc0102d82c0e29c0102d82c0e2bc0102d82c0e2bc0102d82c82c0e2bc0142d82c7c00c2d82c7c00c2d82c7c00f23722fc02e01e01611f234e00e11f234e00c2d82c82c0e2bc0142d82c0e2bc0102d82c0e29c0102d82c0e2bc0102d82c0e2bc0102d82c0e2bc01323722fc02e01e01723722fc02e01e01511f234e00c2d82c7c00c2d82c7c00e11f234e00c2d82c82c0e2bc0142d82c0e2bc0102d82c0e29c0102d82c0e2bc0102d82c0e2bc0102d82c0e2bc01323722fc02e01e01511f234e00c2d82c7c00c2d82c7c00c2d82c5c00c2d82c7c00c2d82c7c00c2d82c7c00f23722fc02e01e01511f234e00f23722fc02e01e0142d82c7400c2d82c7400c2d82c7400c2d82c7400f23722f40260160160a323722d601211e0a3235601211e0a323560102d82c82c062bc0142d82c062bc0102d82c062bc0102d82c0629c0102d82c7c00c2d82c7c00c2d82c5c00c2d82c7c00c2d82c7c00c2d82c7c00f23722fc02e01e01611f234e00e11f234e00c2d82c82c3c0102d82c3c00c2d82c3c00c2d82c1c00c2d82c062bc0102d82c062bc01323722fc02e01e01723722fc02e01e01511f234e00c2c4e47824c2c4e47824c2c4e47824c2c4e47824ce472348e44e3f214ce44e3f214ce44e3f214c2c4e44e3cce44e3f214f23780e6016013235e06600e0a3235600e0a3235600e0a3235600c32c2c8e20f23780e601601032de04b23780e60160110a3236600e0a3235600e0a3235600e0a3235600e0a3235600c2cf824800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
      else
        if i < 33 then
          if i < 32 then
            0xcb80c780c780c780c780c780c4261e04b80c5e04780c6e08780c780c780c780c780c4261e04821b80cb80c780c780c780c780c780c780c780c780c780c4223604b6044273604b6044263604b6047604780c780c780c421b80cb80c780c5e08780c780c780c40ec780c780c780c780c780c40a380cb80c780c4380c4222e08b80c780c780c780c4110780c426b80c826825824b80d00ec780c780c780c40ec780c780c462c780c7219e04862c421b80ce04c21780c9e04424f80cb80c422380cb80c40b780cb80c208b80c780c780c780c780c780c780c208b80c780c780c780c780c780c780c780c7604780c780c780c780c780c780c780c780c5e04780c780c780c780c780c780c780c780c780c780c780c780c780c780c780c780c780c780c780c780c780c780c780c780c780c780c4261e04b80c6e04427024ae04f80c427024c24b80d021780cb80c780c780c780c780c780c6211e04ae04780c780c40ec780c780c780c421780c826825824b80d00ec780c780c780c780c780c780c780c780c780c780c780c780c4380c780c780c4263604b80c780c4e44780c421780cb80c780c780c780c461f80c8e20215e04c0ec780c780c780c461f80c8215e04821780c80ec780c5e04204821b80cb80c780c780c780c4e444e446e046e04780c4e444e446e046e044e1b80c8e1f80cb80c4e21e04b80c4e2c5e04780c780c780c4e2c6e044e2c4e1f80cb80ce049e04780c780c780c4e2c4e1b80cb80ce049e04780c780c780c780c780c5e04780c780c780c780c780c421780cb80c780c780c780c40ec780c780c40ec780c780c780c780c780c780c780c780c780c780c4110780c780c780c780c780c780c421780cb80c4110780c5e04421b80c9e04424f80c9e04204b80c204b80c780c204b80c780c7608780c780c780c780c780c780c204b80c5e08780c780da04b80c780c780c780c780c780c780c780c780c780c780c780c42c9e089e08780c780c780c780c780c780c780c780f204b80c204b80c40ec780f204b80c780c204b80c42bb80cb80f204b80f204b80f204b80f204b80c204b80c780c436087608760876087608780c780c421380cb80c780c780c780c40ec780c780c5e087211e08b80c780c780c40ec780c780c780c424f80cb80c4222e08b80c780c4110780c780c780c426b80c826825824b80d00ec780c780c40ec780c780c780c780c421780c824f80cb80c6e08421780cb80c204b80c780c780c780c780c780c780c208b80c780c780c780c780c4110780c780c780c780c780c780c421380cb80c780c780c780c424f80c824380c9e08426b80cb80c204b80c208b80c42d42c7c00c2d42c7c00c2d42c7c00c32c2d42cbc01323722bc02e01e01432c2cf22bc01032c2d42cbc01032c2d7c00c32c2d7c00c2df23722bc0102dc2cb2
          else
            0x8e1fc008e07c00bc005c0c7c007c006c0c6c0ce04ac0c76086c0c7c00424ac0c9a13c00ac0c7c00426bc00ac0c7c00660856085608760876086c005c00e009c0c7c006c005c0c4e17c008e14c008e14c0082bec00ac005c00e0082bfc009c005c0c7c005c0c5c007c005c0c7c005c007c006c0c6c0c6c0c6c0c7c005c0c7c007213c009c0c4213c00bc007c007c0040ec5c007c007c006e086c0c6c0c208b40074004e0b400b40074004e174008e0b4008e174008e0b400b40074005c0c74004e0b400b4004e0b400b4005c005c0c7c007c005c0040ec7c005c004213c009c0c6e084217c009c0c7c006c0c6c0c6c0c4249c0cbc007c007213c009c0c7c004213c009c0c421bc00bc005c0c426bc00820bc009c0c7c006c0c6c0c6c0c6c0c6c0c6c0c7c006c0c7c0042c80a027bc0100ec7c007c005c00e008213c009c0c7c007c007c007c005c006c0c6c0c7c004249c0cbc007c005c004213c00bc007c007c005c0c5c0c7c004223c00bc005c0c7c006c0c6c0c76087c006c0c6c0c7c006c0c7c007c00425dc0cbc0040ec7c006c0c6c0c5c0c66087608760876084e0bc009c0c40ec7c007c004e0bc00826fc00b213c009c0c5c0c7c006e086c0c6c0c208bc00425dc0c9c0c7c004223c00820bc00bc005c0c426bc00ac0c6c0c41106c0c00cbc0041107c004092c0c9c0c5c0c7c006c004e1cc008212c009c0c7c007c004e1bc008e1fc008213c0081107c004e18c008212c00ac0c6c0c6c0c5c0c6c005c00e009c0c7c007c006c005c0c4e1bc009c0c7c005c007c004e1cc008e18c00ac006c004e1fc009c00e00bc005c005c0c7c007c006c0c6c0c6c0c5c0c5c0c5c0c7c006c004e1cc00ac006c005c00e009c0c7c007c004e1bc009c00e008e1fc00bc005c0c7c007c004e18c00ac006c005c0c5c0c5c0c7c006c004e1cc00ac006c005c00e009c0c7c007c004e1bc009c00e008e1fc00bc005c0c7c007c004e18c00ac006c005c0c5c0c7c00461cc008212c00ac007c00425bc009c007c007c007c00461fc008213c009c0c7c007c004212c00821bc009c0c7c006c0c6c0c5c0c6c005c00e009c0c7c007c004e18c00ac005c0c5c0c7c005c007c004e20c00ac006c004e23c008e1bc009c00e00bc005c005c0c7c007c006c0c6c0c74007400740074005c0c5c0c740074004e1b4008e1f400b40074007c007c005c0041107c007c007c005c00e009c0c7c007c00461bc009c00e008213c009c0c7c007c004618c008212c008212c009c0c5c00200821fc009c0c7c004223c009c002008223c00bc005c0c7c006c0c6c0c6c0c4249c0c9c0c5c0c7c005c007c006c004e1cc00ac006c005c00e009c0c7c007c005c004e23c009c00e008e1fc00bc005c0c7c007c005c004e20c00ac006c006c006c0c6c0c6c0c5c0c780c780c5e04780c780c425f80
        else
          if i < 34 then
            0x40db0c4c1c711c0ccc1c41900d8c1940e081107c007c00e00801e81a722f2151c0c41a40f4e4723501a40f50b723501970c4c44c1c711cc20c1970c4c44c1c711cc20c1c4190c44c1940e081c711cc20c1c41a722cc01107c0041107c00e00bc00e0081a40f42db23501a40f50b723501c711cc20c1c711cc20c1940db0c4c1c711cc20c1c41900d8c1940e081940db0c4c1c41a722cc1940e0801107c0041106e007c00e00bc00e0081a410c81a410c811041104110409bc00811041a410c81a418081c711cc20c1970c4c44c1970c4c44c1c711cc20c1c4190c44c1940e081c711cc20c1940e082e007c00e00811041a410c811041a410cbc007c00e0081a50a0e4723501a50a323722d00110740041c711cc20c1970c4c44c1c711cc20c1970c4c44c1940e081c41a722cc09bc00809bc00811041a410c9e00419407c048c1a408ce4723501a50b408f235001107c0041c711cc20c1970c4c44c1c711cc20c1970c4c44c1c711cc20c1c4190c44c1940e081c41a722cc1107c00e00bc00e009e00419408c9c0c41a40f4e4723501a40f50b723501c711cc20c1970c4c44c1c711cc20c1970c4c44c1c711cc20c1c4190c44c19407c81c41a722cc19407c801107c00411062007c00200bc00200ac0c6c0c44486c0c7c005c004217c00ac0c6c0c4249c0c8217c009c0c7c007c005c0c7c006c0c6c0c6c0c6c0c00c800f6049a17c0080ec7c00424f80fc00c0ec5c0c5c0c7c004e1fc008e07c008217c00a213c009c0c7c004e07c008217c008e1fc0082bbc00ac0c6c0c6c0c6c0c5c0c6e047c005c0c4e07c00bc005c0c7c004e1fc00ae047c004e07c00bc005c0c7c007c007c004e07c008e1fc008e07c00bc007c004e07c009c0c7c007c006c0c6c0c5e046c0c6c0c5c0c5c0c5c0c7c004e1fc008e07c00bc006e047c005c0c4e07c00bc005c0c7c004e07c00bc004e07c008e1fc008e07c00bc005c0c7c006604760456047604204b6045c0c5c0c7c005c0c4e1fc0082bbc009c0c7c005c0c7c005c0c7c007c006c0c6c0cc0cac0c5c0c7c00461fc008217c00ae047c005c0c461fc0082bbc008217c009c0c7c004207c009c0c7c006e046c0c6c0c6c0c5c0c5c0c4e07c00bc005c0c7c004e07c00bc005c0c7c007c004e23c008e07c00bc006e047c004e23c008e07c008e07c00bc005c0c7c007c006c0c6c0c5e046c0c5c0c5c0c5c0c74004e1f4008e07400b4006e0474005c0c4e07400b4005c0c74004e07400b4004e074008e1f4008e07400b4005c0c74004e07c00b217c009c0c7c004217c008e07c0082bbc008217c009c0c7c004207c008207c00821fc00bc005c0c424fc008207c008223c008207c009c0c7c006c0c6c0c204ac0c5c0c5c0c7c004e1fc008e07c00bc006e047c005c0c4e07c00bc005c0c7c007c004e07c00bc004e07c00
          else
            if i < 35 then
              0xc80e0c0c8c9cc748138e18815c40e0c0c80e0c0c80e0c0c80e0c0c8c9cc748138e18815c40e0c0c80e0c0c80e0c0c80e0c0c808c058808c058808cc0c849cc74813861880e0050808cc0c8108407c00c80e0c0c808cc0c8194c748138e20815c40e0c0c808cc0c807c40c807c40c849cc748138e188108407c40c807c40c8190148040fc007c00419007c840c7c0040ec40ec7c007c0020081d412c018c190148040c190148040c1904d88217c008217c0082bbc00801ec1a909f2150190148c40cc0fc0080ec40ec7c0040ec7c007c0070bb09c070c3d30bf09c070c65019014bc40f12ccb0070c190148c40cc0fc0080ec7c007c004e07c00801d80e4c4f235c0d5c0c41a813509cc672354190cd8819014812ccc0fc0080ec4c0fc0080ec7c0040ec7c007c0040ec4e07c00bc007c0042dd09c467235012ccb0070c1aa0d7c3cc19014812ccc0fc0080ec400ec7c0040ec42bbc00bc0041a80d426bc1d01a812c0d4278c75419011827bc3cc2141a80d7c3cc2dc0bd09c09c07b235bc0041d44648190148c40cc0fc008c0fc008217c008217c0080ec40ec400fc0081a410c801e01a72372190190cd880ec40ec7c004e07c00bc004c0fc0081d41c70b8c1d70bcc47019019014bc40c1d712f018cc0fc0081d412c018c0ec4190148c40c0ec7c007c007c00401d40e4c4f2372195c0c41a813509cc67235412c0d44b0c190cd88190148c40cc0f40080ec4c0f40080ec7400400ec7400740040ec4e07400b400740041904d88190148c40c0ec40ec40ec42bbc0080ec40ec40ec419007c80ec40ec419007c81a813509cc67235412ccb0070cc0fc008c0fc00bc0043c007c0040ec4190148c40c0ec40ec4190148c40c0ec4e07c00bc007c0041a413509f23501a44b0819007c819007c821fc0080ec400ec7c0040ec4207c00bc0041a416c81f01c01b004901a410c81a416c81940e081f41c081106e007c00e0080ec42bfc00bc00e0081a416c81a416cbc0041807c0041107c0040ec41a410c81a41808110740040ec74004e0b400811040ec41a416c81104019407c048c18005080ec40ec40ec41a410c840c41107c0020080ec420bc00bc00200a40c41f018fa3fa2d019818e0efa3fa2d41a48b408da3d0c0c409bc009e00419407c048c1b00c880ec41a50b408f23d040c7c007c007c005c007c007c007c007c007c0020081a416c81a410c80ec401e81a408722d01c016c81a416c810c06cbc0041107c00426fc00811041a410c9e0041d412c018c0ec40ec41a410c840c7c007c00420bc0081a410c81a410c81e41b019404901e81a722f21501a40f50b723501c711c0ccc1940db0c4c1c711c0ccc1940db0c4c1940e08110409bc00801e81a722f21501c41a413722d01107c00e0081a40f50b723501c711c0ccc1940db0c4c1c711c0ccc19
            else
              0x8c058808c0588080054810c07c24cc134c0c8444e1c814ce048088413407080ec4c4cc0c814ce1c8c4cc0c814ce048c0c4134c0c8c64c4c8134c0c8c44e1c8c44e048c0c4c4cc0c80b804c8134c0c81a80b8c74cc74c0c81500a88134c0c8c44e1c8c44e048c0c4c4cc0c81a805480800548134c0c8c44e1c8c44e048c0c4c4cc0c807c40c81084c44e04807c40c80e0c0c815dc088c34415c408c0709c08407c00c80f980cba104850418c0ec808c01080850407c00c800e04084054b05700cb05700cb05700c80f8090905700cb05500c80f800c81f0084054c32104007c00c8220407c00c807c00c807c00c8050c088138410c0708c0cc08815c415c408405481200848007c00c813410e0a0011007c00c80e0c0c80e0c0c8c9c4748138e18815c40e0050811040e0c0c8138e189c0c40e0c0c815c40e0c0c80e0c0c8184c9c80e0c0
def andLevel10 : Packing := (3425, 5, 7, 0, 0, 16, 0, andData10)
def andHash10 (i : Nat) : Nat :=
  if i < 6 then
    if i < 3 then
      if i < 1 then
        0xcf6a0390b01a1000e003072800800000e00700040000e000180a4004002000006400007100101300020016d9808c05a00000800cc08400b00700040080143ba81fd30636200000000060000008000000000000155c00e019026005c2c6e620320014008000668809c034035165000002c00501f800009603f0058010058019008001800202200001f8006000529000401c01600b003001002f003010c030000010808008a017000c0b884401d02e8014010001025000000200001b809003601d0391be0012000009001407c01700000241e206a003000001a032000802801601301980000060000030000002005023000000600c0040000014012006802001a004002807408201003c80ac0ce010000015804e04200a003800200600001200006ef439802805e00200501ac00002500001d000401d00b0004306000001808000001002600100a6000002001406602b009002c00a07a010001000000a00a80e402c02e00b0000030a2d0010120a4a012009800000200000080250ba02b005043000403101580cc00001b000003001c01c00300000360030099d5003a07b000801c01200600700d142088700180c403600a000018c02a0170a2810c0500060068008042000034002000c00d000801402e01f00005a400000000e005000800204a002c00004301c0020066e68000000c0000030000000014001000806c0b600200080180288b5006b22403c003000000010000200880e400c04f01a01a000c0000090039b0201a003802801600202600bc0020010020000026004000005c65c000000001005200d00000200a8001595806400e017001000002004c00300006a20150018060102000019bd1403e009000800c00a00e000800c00064e00680659b408600300e00140211f5800402c02a0000054024004007801115600c016000800a0034ce8001f4e00004300000320000090000000006645807c00011b0128000000004006803801401763a80040be02e000000800601c01580000740030000000002082029b79403c0000021c3800200b005af1800a016001009c006016000360c04c01a0000000002a29000004c02000100080000149cd0000038d6af5f00100fe0620200090010000000001000c00201d00e004005c007003006c88602d002003400000500000000000030258001f4200e001003c0020630070ccc0620000030000014004000803800000000780f404801f001003000201014c005c002008008ba4c002000016001c032006541801000003a00236d800000400e000000000502341e8008ba548700b405e0060028018024000003803802200200480100100000000004022001002807c014005000812c002004000001000000a004802800c01c000000400e0006e8803000000000c9a5c00200022b80159f80411830015ca002e
      else
        if i < 2 then
          0xb015007005c1c400201b00461020848394076c8e05b0178000ff801e003c62a4e10d600c008e00d00080dc18e03804083340b803100137100460b9000000000a07201980dc03000069a06380580f808b80000200070090ca8180086039002c00e07100080485cc02705d805d7d41ac01a0148172009309ad0401600a00114f0032034007002401227c000010182200302c817005e0c2003805c0f800000000dc000035028809401c04a005106413203101f802801c03200080100027830228178090933061003c4fa02752a80c400200156403ec0262ea0000cad86e00a00bc0800380005c200a84780006d3801009404800b060808e000002800007e0a3002802807e00103a002400019843c0070132e36009006402c148008800169401400b00001da14e00200e406e03400e0588bfa01b000031c4f4001024262807a06200a80b000005e0140100046000086001801c02400500040140fd00e000c1b001a095800c06c0020068b1c096f2f001003410c00a01180080f201200c000402800e11581046de00002c8100ba806957200380100bc011028c048009015001800e04000e00482e200201080d001a00000003900e400002500b801e013001804c036132619821c00e5d5003801400c00300d820800000a000819000000c01185f010203600101440980130000004004000049809c04600f00101792180210e087a801c03703c027000004b00101e879c002175802018001500480a400205305203900184f800000bc004003001800005400002d00002340ac04f806408600600000680080180020024abc00202481182d205f000800000c003027009c000bca000800400c930013003013007a02d002400003c061003001801503c0118046002021000002606b002000402408a027801c0000010018000122007001000135825f01b802800200145000ac020024056000005e004016000dafc005000004c08800002d866c00601f006021c06c000008800001019e00200080080000040021b5007f0033af00000240390004090000841406401200703080080e6017000803400409c014800001200000781dc096001001806c13600100e005c2a000e01100380ee0f50e7001c002527036004400c527045803c05e00006b8004006037001800006a00f00e001439e05800180d401001800000000b206900414c80520d1000002415200202e83a400002f76ba45800a0070030258672030718000000404b004001405c000044800805a02400b80b801c00100d802c05403180000a0064285006002973002e00001fc00214c004805400000900300f8000c3749401200000110002a9012800502700000080003bd80800aa00000003a0002001018804c000000001048007853a02e0360ae001503100500f200101f819009c0060010024000000010395
        else
          0x370381d8113680c5881a33830770633084503049b5822d282c3e534ea81189817a402f1402b1784360586850060c82d8d4a6548107c04c5400414825ce81c8482fa3421b6060d9033d283cda0349b833e205d1d8648f4b81d81da64acfd0482041e44ca6fb019c28448a025b40355a0667a063a9812940331682b0a03ff88070f03e6e85c3d82d1f0232a8659503335d2c754230b02d268660684817053e184d1102bdd80570825d2060cb8183e83fba05e770654a8481b0696b866a6025bf88753011ab8663a8275906aa3a289500f94809788615186a98836a20694e4368b066a831f2001ff203750013d1039484931a021aa0315d838458319801ffc0568c8551ed228b8570884d5e898fe8469d061ac027ed028a90c7d28230600dc602e6d8113e03411d91b40534e0689e059718000a8607c83d658618201e4e0379980846801598ce9a01c9384450833cf054ca0904003e4f80f9d047af856de0016c0265a80616027c30482c01eb58450c05401095f883a750471e85f600010203e5d069ea03f92ca920804f3060770669402f51842cc849a48298f0619e0695383f7b0610f8435a8686b8b50c423418ce8980c9c80a9805d45885ed01dc185f3f851bf8197b84573036c3520660362f01c330059e80b4485ddf04eaf0087c83add00d278236e829fd0464e0bc9752da5813a900b190164d81acd85ea44877a83d248091b0105f80c4130691012c7cabb7847108053980259c213f813018223d8266e8072a063e28e8e3807a281090021d3030c28675102411833f20635381966cac0b80fc10474700df28191105edd0182e520c301ef80673b0324e8943651fec02b928294d05a6d86624205564219485202033c2c1f65838b00634084ce500f3800b2582f2e821e780cddb1daa83174061fb81c5d06a45000f90170502e7883110014bf00889c1ba0019898057f80da582e2e02e1901e87017d9066dc82be2c2038028b48173f018bd0446b00390032da806f380e500245b044790209603ff7228590276e04ec981771868c30063b0614d4af0383345840de8287d4af6702569048ac038f884cdf05eb002fed80093042a601222a8585808a8095c101616851c1897de807c82269701506856b30958580e140138a018a18467682d0605b47097a6019098583984226cac310383b012c806a2f01fb3843a34a8c41af08039eb03f57815ba016ed054691b0f5824fe1ae3104873003f4b225e810f303f168034b043230363f05c358bc1402dab8655501539843f951a33069c604c848671d0582a849c905ee105fa184c070690085861847c48e6448523004400200000dabddf2e4aa00a063401a07700101b0002c11011800801404d00100381f20ae034174d87803b008b1f001603c0000001b5e018094001800278a3090175d14000015803014c02
    else
      if i < 4 then
        0xc37602fc2042728d9d7053310c269811ef0141c02bfc062938238e019b0824bd83568b1b638696300983010b80543704c6803c6a81b3e80bca85cdf8c59705fce811c900f62097fb065fc0c1a5ba734d1ee6893c806013032e504f21a4ee08531e8222101d000032582c6004a50040a68c162b218e89072861bc016470089783a3e0621e83fe10693a80b7703941039c484cff01b16522ba00785832f7054e480edd86652867a1a859e0101b03b7904249862202a2ef05f30092bb85423845218155405594031ee8296d01b7900302025fe01c0e2a4ce835ea0ce7981065d250185ecc843078220f057ad04a3c803c681f0881a5b04d4502b3f8585281e8a869ff81f2e02211043b40098a001e780467062b8840ab03ceec1bd785cac42339863fc84e23014b684b2c81c1dd1a5402b7084a248638b0290f82c1c04d9d0250d00c9100120085d284ab38540a057168013900a020078d80365027d780afc8176c808e1843d2014fb82b4201e2f8320a042858187680b0901b4705c628c421baabb000ae859ed04a904afad0683384ac741fb283aa285c788594dd1f548085082bbb89808862120dfb78644dd202d8ce86caec001d0d8c1698b4aa02294056e1baa1803dcd82dd7053dd053c002a5182b9d8525e060f502dbf052f8813a28685b830630157ed1edf052258348f4211502d6f80d5651ec7827fcd1d4b84f6581ab801f1281a6b0640880e7b0336682c4483da7807e6844b38029282c9700688c872c0549c02ca1894f986873d1fbe865ba8313b892e20075783b2c8451e04e0f064e58335c01d86034abd20954a844b34e30636e325920655f0567c8966381ec9800bb81d3483932812b38051c01afccaf9802f000087683449804cc84efb806d101a73060e881286038a780de7820c60462982c6b421ad03a2d03ee086a4a00be4cad81812d18104681cd382c508997985ded82d0c0137f81c4e02813820e8865a80457b8192e00e86066e584d7d81c790044704ea782cc384938818dd80fe30458802a2900a2583a4c05765039594aacb85a52863b085b320d9dcca8ea03f5e009120018184aa9a26d30bc4405575866b383e25064ed84067850d88002405e0f8246b31d50a27f8810e004f30821dc893f5848f289958867078068584e3f8518001aeacb1370b5a985d3ccab628975c8219383b95037f04a90701fa3a855e05aa0822bd039de0493504b5501a63003b980f85813cf0533e025724875e01df7053b8ba7ac0066e84bde81b1b03c9c00f6984e2ec9306829ba0093080bb8096330080783622a19acd1c1a041ed8553d857d281821005bf227e7002c7847b94864880b3a04291839b581fdc8a57d847d302a2280f5b097c00622b80f0582c3705d6200e9b02ae7850360286b82efa0626f042da83c53cb73b816a084f44a259983e
      else
        if i < 5 then
          0x23d0218982083857b081509027dd805df8603d863708258f018f00155805f85067d20646104385029534b817002fbc1c8401835856f58193c05ad30177900108897788522a05ce200efe0442d058d304dd60679302637866f9043e904ef1814c20287606878032af015c009425813488007601740018628382000d1d044b802e5905f9c0376302733d1ac6861750a56982286022c4010fe0323003baf0552f099b18b0ed83c36030cd854ae8094c8950203abd05e4d8577605b8bcaff78966d85296ba8bc8135e8666c84a590695e31ef803e5502960869e3844118578b01ca40c7c1002db0593404fc48323b80aea056c9854c405efe0516f864408558f849418486a419ee0423201266b25c58278000fb252448820f38632983451024aa01036827a60498141a4a09742846a40584b8416704e690058b854ef8202b4a720821760263b052a00509a00ad10b43c8339683e42837fe00d590147902f1bce32f84695039fe84fcb8492f016d8020abcaea651e9051ae38034200cce834778129b8367c80e344ac6081e0f016c600048802e184b4e8365b2a3d28bc2e0400301883818d3005d504d3c33517813f2aa4c5837d10678904abe03ab3826b7c1b95030e000dc88293b0342252f3e2257b039bb83c0c81a050347c804ed85013864bb851f00194981aa805fae02b2c855b080bed0322586853805f602a6e006a50612f01d4c039a60199fd2027863bc8022a850b48b44785d0c51ec806a7803c718145800a500413900a104ad94ba8fc0495941aee83fd3026d1007bc03c198342c844e081b84d22758181805f73823b18943c8415b0408b801c785dafd1f4d2a4a8022e70014180fc8cac56041f14342c0c17004eb20228882af8019aa84e1500c1903014000eb0554c0c83485fb1099450174c04b45061580354d828c28bc3884bc78518a80a1c0021e013900095f82a9f8536e066700590831e6e00f2104a4f846f2854fb84d1802a3f0944081439061118219f00bf28373003607011c002c7105b710c25a0214c867b4c1a2a00822864db00335021cc837b404550845e201ed90386083ed3014ce0c301ca6da0024482d2e846a980d6d809b78d04a03ccf03bbd8114582bd505da303b5703d4985f6d04d868360d02fd0046cc05c71035cb03b6301f950317ad34720666602e00285a302361813e285d6900fdc85d4c82f730628685c1c812ab8505c064cd064f1818fa8629bcad7c03913843c30213d034bf85aff8c47eb355e03cff05dd10099482133846848973d062cb8688382d37c1c70814a585fddd360f0a5d58398280373d1c7c01d2903190846c4832fb001a58048105bf70330b82abe55bb7065b7897ee82647caca48328f047924a4f38958b820ba8241b829c882a8b81727805e5335648665f0329c8502405f92844d7814d48c3c9
        else
          0xb842c18425284ee4d1b9885e91030190478981a450201080f2d005211b0da03fa00216e01a5084c4d0095685833860a082d3d80028035378237103e7c85f0f008d582ceb84ae5002ab004d3023d4026908550680fbf026ed0602c0251504fe303634809624b75985474801eb048040c45dca7bd99796055c5330e08126b01f32c206e00836831bd05b2c056698573b86b0102f8ac1f9505a7883a5a81a09a2565838853a9cd05310802c882f78850ff858de004288548205d2f82cf1017a88281e80c06812e8026138451503204a85b2018e4017158344481525049e8044cf061b351e4800cfe8c29e85088893ffce23c806788574c8390682ee181b2a0564884dc30308204db004bb38420903615810d2027144e1b2805c682c9f018a901d7402385037c5858b18318141c2981c538289702dc1826db227f6819598346184daf8593b81434b1f103ab2701c4505c130631f4208e860d15352681ada8188d8426882c4f809e0022ab0653a84a190047186a90838968387c0149e84b30001b680270007ea04602004b605a94034d68c2402a3cc850a60656f8117531d3e023fe0613a0599e00abc052dc8491eca32406ae282bf285ebca266c83b448b49851dbf816af0375d0185d1ad20809a202cbb04042d06560132682fcd01bdc890538951c0689685cce82034055f10278983163869ce8260883a008620d0203f01e3451b06039914a936028e7036568968380927022de856d282a5b0c1c1018cf0385684c38a23ef4205f0507b80bb385a02002a7035de031dd0967600079003fe8234031e5102667069a7caadb0299d852af41f8685e208307a03f4949be683dc0033a285b050c57506a8d018410967d02e34044f0068dd006428111f85d3080e7022a5a0692b03a8a84102020a281ee904a8e01635868e68bc258398d31cc751bac00b9f8680c83e95386dcd1d1f0311a00d2b00d7184fa001fc00c382b5cd00692384b3a82b82860040231c857c28246484f1385251008c60321400278098f7031a3096f603cbb51f8d05c2383ea104614899bd05a45805460326b80b4f05c8419032067a803154851100016201e95868f1086fb83b5a805a781587d2cd0047e70465105a88823308166d00a38807af81ec703b6d0623681f6a9afd90872783371c35f9c365a8325a0950a0daeb03348830a5d5cca034f0043e5051ec00503832bf01e15d5d57013b5487770460d8daf3046b0040848c1da80736029ea84345ca4d883e3e035a5032cd31e8d86416095120c4670c3b2835080541280ead05bb881c8e01ed3025e98c254008644e21d51d36011a08585880d338529a81657832d0829d6855138c18e0402c83f2401cf432001065cf223cd03c8e83e2f845cf84f0883338434d4856f8055238c19b82a03038c20592b83960061c9825050556b0026605
  else
    if i < 9 then
      if i < 7 then
        0x46fb0ce4c85c6c05370830b485a80025c6895210161d030aa811870048d02248802340124a803d282f3f229220563382fb202ac702259228b306afd8357381ab1000c5023bb82f0c05d8483cc5ca91985db604e438907f85ab18020641ea982e380096b0428e04c420652600fea02fd8824db836f5064a952de1826bb0483481bed8282d3aa0a0255801f40851aec1aab835bab920984cabb1d728049e85a3e81f1e838dc0468a80bddb35bf8480a8dfd085a1d023930541e0535586487053290559884ebb04867840150264f01e7b85b5884b0e04d7500ddb82651809048305b043dc81f8603b148062406454061da02ecc01d3b836be83595017c0040fc858f580725813ed837c882acb8166680f4680fa18299380c2a01b56861a38643a844608b6748420003c78b31c59ac9d037840674dcaf49037df8412e82487ba82883c4b1b0a7065f7813b8026c506aab04487023ce85f5d067dd841334b0b20673702ff003527c21bda27760577e05719b92af009a8864a6054b5016f30680101d25cb05901e990204ad23b98682fb5c118358a84eed82a4341acd01f9d05e3103df303de304d2341caf8036b814e180aad09094024230534580a620bc0e056b8b1f1880eb222b4fa289e80c64009f38494a04e9f006b684c9d0253e01f7a024c70212682b180553283a78010a9041d785e57819be840e981a1eba73a80ba201a8584a4605454806480443485ae55063a05bfa83a9681d14090380399e8332b05bad0636683f868206104aa30634a85b138046f83b8a8614785c5003c6600f4ed2f92812f603eb20156d0030a00d0e086920144983aca05f0251ce88657603b008684a82434d1aa284e598425881a8c81dde03c2685af381892836cd3a6cf816b655c0e0503f80b6004ccc025d8059dc84dc98658b06497864c1887460337c9af7201b648c46b9b02b03398819318c3be80ce1865a5086c988763867870009c421c7852ba436f4840f4ba6ec83d5a41b708462208582020d680e6782b4b02866ca90c013fd069430364304a8483101826e7c221402e86819978681a9b146849770291005272038af0550b065c3d1dcc023a3331128035d04e0605968842f90146e8377981ba006641834e805d900417b41bf283d7080bd685445c346f8165f8247f801ce015168515580b3701e25807d00876b4a4fe8975003b8184d9303323826750536504a6b02df58664b053fc09780803294af59baa8a836d8859bd816fb8476781021014260628c0c1840509481d63048a684ffb0669d021540243d833af84b168100341fd1067fc01dd5850684aad5841ab420a99978d059ac04b5c82ba6841fa03b2104ddc867c9aa3ea8431805cfd830218597a8270d812450029b325a902d5884cc405f2e848b081e63094d18322c0587c81e048455f84be1031f6069d
      else
        if i < 8 then
          0x9e02f4d03ba4850848652a01ca9850a906a870690b534df061c006b0a8650401e45062c28642c03ad1037480234d0581600713013188380a84037885de814db04b9c012df00e1c8419806b0a012a701b89006cb0128b80e3e03d3c06469854d2ca30c3aa6a05ef1050bf830b88092e065ec81cc30490c827ab04ca18579b819cf03c921ae9205b18031304e2ee84da2812bb03d468693481e5d829a18444c83f0c087910086d83726062fc85e414b72500d86d1c9304db9806e682c2302c0503272054918054bb1fff838e70001006b0b0208d03aff0239c8c57f85f8f019440370f0077604c650310e8561782d900061a8052c010710273b8249ac216f82fae0314a8376a01673015ab8a570b5fc78566485a2d0049485399036880340a8154782740062e802358b256e04c2a0982cbe02b04de7811f2c214d08749044208109b81f22017540e8bc83f3d80e46c21e58367685c2ad239385bdf06826041b101dc98406e05e9b00dd1017ba826028434d847ff52e8e02f6206307819dc0440b01ad301e6b85eab862f3865168668e80b2b808eb01199085f602ec4a28a2010ec03bef068ff06163849568563f03b382373a0532703ef581b9785c4a0075e00af7068b303044ba71105f12058a102806816cd854588066085578839d303a8500c6b85cb9842ad857230691d063ed84b8bca4ef848c152e440432f833ff069d0002540416a0409883d038625e83a9e84a7a058823ab0282e8a80f0805210852198433b015d00584684ced8473f5a5ba8368604e8f85ffa8c332814058006c84f1d85be302ca981ce2862d80240c85e0382bed8340405d71011bd03ec2053a7223c30386d0479e8c3788136b00383830e80169a0871d029700c4190256482a7402e4805389031408141182aec84706823ec007dd86118803a28438d0c6a5887378189985bb50970980e5c82a1a04d0482a0b059c5835868466fb2580cad4c83f71048980657f031fa85c4705a988605d848d2845fa4a2f1827750148c81fb84a762049070a5a286a34513388196e82cc882d7285bcf8c1c84ad15848848122d860548152904ba280c4e84e77053ed03a1f82933016e04a76d85a220679f84bf185b5205e828959000423cac8c046ee81bb60499300d4f82592028fd83d0981c6903837025290466300052808cf0230a862b1048930076e0341d8568781db406581806d9857cb042e68517c061f331d99896880018d807988686584f03c224d858ef8684605f57049c301bf5044732a47682236810a1819538502d0487e04de9866ccb1d8f8373d82d1382c8d035b604e7b82d9c8506782f9782d62020208484e84a2d01aa741af4020e58459482c870082bd1c0a04bd451bd98429c8233f83f1c03aad80d01860b7053d301466a2807028360158b0637d0659b8353fcac4c84c0b8
        else
          0x82005d2eb782c0e83efc808a70475a812e600add863c704239d1a79b1c4e039f3816d6851a28050b01106031b051b10806be8ce7380fad83b37898060220006b0bb5ca9066090560105de501c2683f6e51fe402dd88283c001ae80313803ee8295e520b981d9f81cb702fe1036af052790445d8592502c29845da8699782cfd00ceaba67085aa8029260676a0216181ccb8136205466015c986985b1da7028478555580f3341c8a855a80595205dc20572a065e300a35826f600e9201446834e0800b1825a7864b10530d05802008f002ea00c45605903028ddd1fa9001d400b100409582f9882a7905e3c8598a045d0801f6029c2846da832668674006b0d82d83d5e3004b9583121852c286a1a81270818b685699831d006b0a8253300433001108418c80c8604a01048cd85c5d045a681b4c059e7047b600cf602b67801290186e039ca0267c01a24026f8048de0121981b09029dac2183821a40e68703250036fa84cd486008849e78661c063c9033ec81e540008051c2203d2d0b615007f1838f30b5a2852f203f33008dd03188060e505e6e027e5cac1d00ec001486893288268583c800908382aa1d1b7e056198003782cb3042f451c4200283028e9855458385900c2384b7a02f5b0207d047c986033033df81c7084fb183eb9858893254e4873f83bfe81a7a844deaa3d8028cb04dfa810dd8979f81d7a04bb8005cc05a13015f90237a005120093b4af1004c1d83c068013584c2251fca03d1c03e0f0512b06422520a48412183fc484c88004c4847a5a28af027278112200c88aa4b2822b2803b581e3d8125380f720108e8661604241053ce818eb4a6ae019fb01a130470d02cd601cdf8640683a61021000262100a8100c5485f4705240841820575f0130c897e002e4603d1185390042b21ae10011960073d0580e05d9903710033818312b0384884bea4a87b01fec0528c03ae481dbe0316880c3a2a3a0050f2066f503e83042185246da23dd094ef058c98996d048388179c845b281a2f83bb58251d0526e0089a809cc03cf04acb18b74a00a6e8456204bf984cf4cacf10441c02eae0496700ebc852cf85a5c068a483ce50382f04889094020560800ace00406013dd021f1841a08080e0244a822982a3c50397904fe80369e805fb051d102b8c809be0606f062ad049fc03a558453780dfa06047824070321c4930c020cb8026900f1705e19838078056731ef5802b1809ec0044e0651c8114a063a38697505cb684f9d0c7ca82dfd04fd60402001d5e9905702bc684f92000dd8405803af50023e80cbb0520f8b504829f680da88c3a8006338257a02da152e2901029b1e7b0396a83ed80567202fba1adc7868ecd3607012fb02f6b861e90041c822f48630cd3667892f352fb882e08035678288900ab683242067eb813878472f051
    else
      if i < 11 then
        if i < 10 then
          0x6c024298110806b0d0608806b0c0279a01af30297da292f032c60259806b0983dd5067c2ca75006b0bba64006b0ed1ed0854a2c1fda0137204eda840b806b0883468021be84b26895a601c124216006b0f817e681de80c315855fa0647500ee684d4a856e952c2e8084d815e484ad00037a8624a8366806a1686ad2856208576e85fe15223304d09802edc1a9b85d8b837418306e846d006a618543c052b6804d9cad74aa2c03ab3800e09007c04aedb8dfbd82544069ab84c1182d4e015728134205df006b080c82d85abd04e328575006b0ed1c6900a4282d7800c720620181211850ea8548f0461f82f834201e03febb1e5e859d6814900254f85ff20d0ed80c0b82a4f82d410127d01fa884f6f810ca82bad83b1806b0c22a620217981cbe8c28f03e06069b80650a00de806b0f0670a066d484a0c02850062e686728821850014806714053ac0366006b09043ca8d9c6831ad8352e85ba5003508649d04afb059cd81ebb8227cb5a5381fd202c5d856c7803dd0449b043bc8392a81d4580a5e02ebb057dc06af4830dd822424ae74085e68090f05b3e227ea035ff0282200fd084cbec8663043ae035aa004fac1c16048580515f855d305fd70106d040d081c3a8277e8902485b79059a20465880a77034368505006b0a014f0836d68598181bc006b0d8020e03cd383ecb822710140d8478484350000f2d1dde056ab41f4404faacad3085bd006b0f06815034858403d000ce85b2404b1d8300c0414806b0a0437806b08850d2864f90463301d6d010b78349641b4084d6a0411105a0885c9231e82057e90211a862d4004a70245600b7e320eb03f8a8248d834a603fdc80bf9042648624151f3f0206d83ea984443009c4824e483bd5caf318081b02e668c3c04af1a8125806b098c47581b0200d8a0663500db00677e82add040718675dd208500977852d105e5903873011530065b83c15001978555a80b53863f503e1c04b0605cd005f7d03a4184314037880507685d590276006b0c050c00285cca9ae0639e8393853435cabf982deb815b085d22019ef03a378c7a806b0b00f51013579b103829a9820b28364c839544aeed83e60052640608685133023da026995201605ce8893c0838cf8504604c3081b6d035108271ab1f0e51cab01f528170da85adca2cf51de4853078151f04a10029450159286a6b04fdb837af8167e1904d55a4f0ce9602b5681d8c80b6f85be805cc55359b051cd8b4a6d1a610038d842d382e948427a82eb68511f065310361a0b4f50184b8436884ff701b7001c05014e804fb904aed8147205007a296880453a22c6010c5063df03051006913a74884e1804492cac1006274847740638302bb6066c38215f80b8f063100c3d582f420411f818530c48701fe0803cbd1b0e0472105db800e8bca2a6863d580c33
        else
          0x355081f3c8024841fc1050e283c5800f1b86131041d902cdd83bf60e65a802bb860fb02476869178039884846c1afd0b12006b0c039e651f6c0524d023f1825200bc3551bbd811b0ca20385285017280162083b4f1b053869b7861d683eee054d881bce09762836b501cfa8c81d02e7652042caef00b5338440685146835d0054b9055b80222f031e603dbc00c1002e9f2a4b8044fd85c9d00ff003db34871006b0a03d57028f1041e3055a5824ec06acc8591604f5701bd7029e283d7e85566057a006b09834d80df5a004088b61c0b13a85d5585ec003028866b80391e8359b05f4e858fe81561022cc8cf068225384f7c858258547c836e985b6a0071c0070006b0981039d1e1b8056b0475305dcc84e4cd061a82ad585747227dc0672600ef18dde004f5806b0d0dde9ba74704b74065dc00e2204d67097bf835f2811d3045414a34006b0b5347d05735025e700605cac4580d420868a84b6b847d80578006b0a032842251380a7c01ae503d8f856530581cc9f7006b0b05e780492483889815a72235b008b18587006b0c057f48c58006b08822fdd1d5b027b48327b00ac006b09040c3c219e05fbc02350819e09af6ab92b006b0806b0c0209a01f5e849168c2618697806b0e00762836e08c1d28514e02757caf78801728204481c299acbf3067ac34ed4afa1827ba823250c2af41bb00345ecacde8331980a8981ea831f2c8537d4ad8e007b200153005e9492f881f67cad3a838d08085c03bc4811fb0641c03bdc857e70210d8104e01330068c806b0b025a806b088459f840ce898198372a0c7b5007910139d03cac04f8905c8a042eb05ca100b5900ca90a5cc8b4fd84e96058bc849ddbb73505a765062b0979081986849ad867758c2fe83976865d60168ca2a778088500ecb045b80300083e9e8053703f06892a082b35803ae0458205e15017d40000182eed04f2d83d910699f824a0285920001c8163a00f8806b0d01e7581fcc83812837ef82b05ca3a902e50812025119103f46a37470612184d5006b0b03f298633e068af0005d845f280d1006b0f060a98501852bd3066ee51dd4017b1d1db705e8f838e9001db8274b4228806b0c052e78643282b584ad1c05eea0941f8212f86358860bb8cebb51bc006b08047e982146030fb855e003e8f048e90604e01c9806b0a861e5cb072815ec31b868957f0512000d7c8b0f683d6806b0806b0b814aa8105204bcb0591e8400e086e38499f867f431e6501762c20b103f9b02a170160b0c36806b0b02c1705797029048627e01da904cb08c3898153006b0c06a5200bc4833b381ac68639006b0981ef103ca006b09098130c1aa8513f0309006b080b48d8100806b0806b0e05c03860230477f0335151a0006b09c1a8b824f40b6a6058908b69951ad4815da00cd00601f851f931df24b
      else
        if i < 12 then
          0x1adf026a806b0e04e8782db203d9e846e4043710908b3aa3581f4806b0e84b8406191824d10047806b0902076d1ea0004af0171d8175f06a2200a0f85d0503774804bfb86a98982006b080289f815f605ae984af38187f01a990099f011110401a02aab0226305adb00b8300a4c024b106544842bc021b14a33806b0d8357e023c006b0882a9501b3102a31035c383fabbaa7881bfb05a4d01cec893d2844eb0476f81de68565c019f18589a80c7f05acc05fc6843f60303c80b94823e7829b0028ba859b00586e006c604969008fa021c705b9901680820580959e8291d05b49808b8d2d0d016950a287866854200c8596286478d1bf884e568379541f3355b2e0688a02ef3825f183c3e0261bb86d38031e51c9e83c460ce61011dc81f7702a87867bd856289ad2d057f88564600582016010c19006b0f83706cb045053b583a6b0c1b806b0d096ba05ac00336cb25cb0609c058a8041970329501ea24366db1d0d0474986094011e70330383a0a83a24827918d0420062d03cb2c1c0200651422470417385e2a002d006b0904c7f847f6321568931303ded85fe882b7d81975034b38351b85dfa0617f85cf70473682e2780cb401f01d2445800a7051708e8d6a25fa81d1a05b95ca8cf830d78004402ff8017ce028a3860c4806eab21fd819d781b5a04f4a0304841a714ac5a01f8f00ca483bcd0a60d04334849f30284a0498d832ef8389b013c58e9338570184c5d0698d80eeb00a9706a73cace300ea305991840560e8d9846bc827f085d1003be006b0806b080443d81ee40390a52d63041c402928422cfd2427b1e74859fc05d7904f3d868bd2a516845482a35d056970535883e1001a4b4a744ce9f806b0f00e6e04b678017984109045693aaf30544e001bf84228820da02f2106a0e0595983d3006b0d846785233106a5b867e10ceaf0309d821ef01ba8843998258181160821f802700ca04b83aef0028e849d106065851df009464a484812370011ecae798c5428b49603b0900b04897f0b5c0385bc0009fd0338c8645a0045806b0f0200806b0b80cc105383040e6835e6044a7848fe422a201548849b90623b8878c045e800ae5855dd02dc90120b845ae027cd03439828090500c010130272883543033b905b0f00439839ac05b66837a080d95a04d881e1d0ce6904a9b0226c80e0302c7a001fb861068262903dffba98a057be855ed024ca02a64028d28308c82688053f300e4f8616e02de30003c85191034c304a61036903a7ca022a20074383a1381a3d8081584079819250510e0558083dd984ec6d230103d85869f50618d2288c097ac034fd8516203506837e006565d1d8102e16806770159ac221d039218244082ed8841bd041ca048ba844c6034c84209b819010132a054f684ac8897cf04a3183ac501d5600a2b42251809d
        else
          0x286ae802b6d86a0006b0c8303306adb81c618b15304a748191d83c2884e6403e758430b01b988485201dfa84adb8181401158024948942806b0806b09cabe806b0d84df2816bb897d682555829804ab6f006fc031cc038ba045c70e652b1f01831c1022ed06ab5851e3002f40288280f7b02bce02ce6010848504881b2183b9a04ed4007f9cad57030f5820f806b0a05a318978d896df86ab982d563a6b984c9148642c1c62bab4806b0b068d482f320683d0145006b0c01bbe83b708221a8b0e482312850ca805940201f03f6280224841478131484f808006605b810019e8453b83fce0123e0542e85ed2837bb059f2000e48117805f1e8074f099518211302af0862a5018c20371905f2280d3881737023af83fb1b1d6484bae4b7fd05c0b058c3803e1335b7004e78463806b0a55eb900089058e085e640142d8662f03dad8676006b098994d8033c8083b819a101d90826a68162e04978062500116d0c82202ab40626585a60009de84d2906327064d70021002ed584d89048e604d308069c06ac3805b2020538452a892dfb35c68112f02b25a3718840b4044ae06a3d89335051b6046438c58806b0951b4d84f730510500aa68439006b0b01be0832a5052ea855cf00e2c84150c223b856a200ed12197f042100404b032b6800d280d64026ce805ae0594600baa00d9881a9380fff00dbc3a9fa04c744
def andIndex10 : Nat → Option (Nat × Nat) := lookupWord 1307 4268 13 20 12 4 andHash10
def andData11 (i : Nat) : Nat :=
  if i < 15 then
    if i < 7 then
      if i < 3 then
        if i < 1 then
          0x9510e7ff5010a21cfbfa0848439fbf40e90873fbe819210e7ff5012421cfbfa0808439f7f41100873f7e81e010e7ff5014021cfff18180439ffe2e300873ffc546010e7ff890c021cfff20880439ffe30f00873ffc61a010e7ff8bb4021cfff18580439ffe10b00873ffc5d6010e7ff8b2c021cfff20580439ffe30500873ffc20a010e7ff8b94021cfff16280439ffe2a500873ffc14a010e7ff9014021cfff08b80439f7f03704053efe821850a7f7d0330a14fbfa0859429f7f41102853fbe81a050a7fbcc2c0a14ff796581429fef41102853fde61a050a7fbc1dc0a14fbfa0860c29fdf40cc1853fde815830a7fbd0290614fbfa0858c29fef40ab1853efe821530a7f7d032a614ff7a0554c29f7f41029853fbe818530a7dfd0440614fefa0680c29fef40b01853ff660e030a7fecb1c0614ffd95380c29ffb41101853ff661a030a7fecc2c0614ffd88580c29ffb2cb01853ff6816030a7fec2dc0614ffd81b80c29f7f410c0853fbe819810a7fbd02b0214ffda0360429fef40a40853ff680c810a7dfd042c214ff7a0558429ffb406b0853efe821510a7f7d032a214ff7a0554429ffb406a8853efe820510a7fed018a214fbfa084c429fdf40c98853fde815310a7fed01a6214fbfa080c429fef40a18853efe822010a7fbd02c0214ffda0380429ffe30300853ffc546010a7ff898c0214fff20880429ffe30d00853ffc616010a7ff842c0214fff16580429ffe40b00853ffc60e010a7ff841c0214fff16380429ffe2a700853ffc14e010a7ff901c0214fff08b80429ffe0b700853ffc0ee010a7dfc1dc100cfbf82b82019f7f410c3833f7e82207067dfd0430a0cfdfa0761419f7f410ba833efe82205067fbcc2c0a0cff7a0881419fef30f02833fde22e05067fbc1dc0a0cff782b81419f7f410c1833f7e81d83067fbd02b060cfdfa0720c19fef40a41833efe82173067fbd02ae60cfbfa0854c19fbf40ea9833fde81553067dfd040a60cfbfa0880c19fbf40f01833fde81603067fecc1c060cffd97380c19ffb2a701833ff682203067fecc3c060cffd98580c19ffb10b01833ff65d603067fed02c060cffd88b80c19ffb0b701833ff60ae03067dfd043040cfdfa0760819fef40ac1033ff680d82067fbd029040cffda0320819f7f410b9033fde81572067fed01ae40cfbfa0854819fbf40ea9033fde81552067fed01aa40cfbfa0814819ffb40629033efe82132067efd03a640cff7a054c819ffb40699033efe82032067fbd028640cfbfa0880819fef40b01033ff680e02067ff4c14040cffe95280819ffd26501033ffa82202067ff4c3c040cffe98580819ffd10b01033ffa5d602067ff502c040cffe98380819ffd10701033ffa5ce02067ff4a9c040cffe85380819ffd40701033ffa22e02067ff42dc040cffe83b80819
        else
          if i < 2 then
            0xeb7a0856821de7408ad043bd680d5a0867bd05ab410ebba0852821de740aa5043be680d4a0867dd05a9410ebda084e821deb40a9d043be68113a0867ed05a7410ebba0852829dd740ca5053bce8154a0a77cd01a9414efb201528299f7416a5053fbe819800cbf7d032a0197efa0644032fbf40ea8103f7e81d30207efd03a4040fdfa0760031fbf40ea8063f7e81d200c7fdd022a2417fba044c482ffb40698905fee8120120bff8a8c02417ff14180482ffe26300905efe821850cbf7d0330a197efa0681432fef30b02865fde596050cbfbc4dc0a197bfa0860432fdf40cc0865fde815810cbfbd02ac2197efa0654432fef40aa8865fde816010cbff8c0c02197ff15180432fef40aba103f7e81d54207fbd02aa840ffb97581081ff740b02103fee81173207efd03aa640ff7a0554c81ff7408a9903f7e81d43207efd03c0640ffd97380c81ffb2a701903ff65d203207fec4dc0640ff7a055c881ff7408b9103ff680d72207efd03aa440ff7a0554881ff7408a9103ff680d52207fdd020a440ffda0314881fbf40ea1103fde81542207fed01a8440fdfa074c881fef40a99103fee81132207fed01a6440ff7a050c881fef40b01103fee81202207fed01c0440ffe95280881ffd28501103ffa4ca02207ff4ba40440ffe97380881ffd2a701103ffa50e02207ff501c0440ffd89b80c51ff7408c10a3ff680d82147fdd0210428ffda0320851ffb406a10a3fee81132147fed01a6428ffba0480851ffb407010a3ffa60a02147ff4a140428ffe93280851f7f13704063efe821870c7efd0440e18fbfa0861431fbf40ec2863efe821750c7dfd0440a18ff798581431fef41102863fde61e050c7dfd0430418fdfa0760831fef40ac1063fde814820c7dfd042e418ff7a055c831f7f410a9063f7e81d520c7fbd02aa418fbfa0814831f7f41101063fde816020c7ff4c140418ffe95280831ffd41101063ffa61e020c7ff4c2c0418ffe97580831ffd40b01063efe26e08087dfd0430a10fbfa0881421fef30b02843fde82205087dfd0430810ff7a0561021f7f410aa043fde81554087fdd0440810ffb98581021ff710b02043fee81604087dfd0430610ff7a0560c21ff7408c1843fde81483087dfd042a610ff7a0554c21ff7408a9843efe82053087dfd0428610ff7a0550c21f7f41101843fde81603087fecc1c0610ffd95380c21ffb30b01843ff621603087fed02c0610ffd95480c21ffb13701843fbe819820e7f7d032e41cfdfa0758839fdf40d01073ffa60a020e7ff4b14041cffea0880839ffd30f01073ffa61a020e7ff4bb4041cffe85b80839f7f410c0873f7e81d810e7f7d033021cffea0260439fbf40e40873ffa808810e7dfd042e21cfefa065c439ffd404b8873efe821610e7efd03ac21cffea0258439fdf40ca8873ffa80
          else
            0xcc5053bde8158a0a75fcc1b1414efda0362829dfd2a4c5053afe6058a0a77f900b1414cffa0b62829d7f410b5053bbe5956a0a77bd02ad414eef9635a829dfb406b5053bbe5856a0a77f490ad414eff2015a8299ff316b50533fe82d6a0a75fd042b414eefa0656829def10aad053bde5955a0a77bd02ab414ef795356829dfb406ad053bde5455a0a77f900ab414cff98b568299ff2d6ad0533fe82d5a0a77dd0429414efb98652829df730aa5053bee2154a0a77dcb2a9414efba0552829df7306a5053bee58d4a0a77dca9a9414efb98152829df7102a5053bee5854a0a77dca8a9414efb85152829df7262a5053bee8054a0a77dc45a9414efb85b52829df7036a5053afe8213a0a777d0327414ef7a054e829dfb4069d053bf64c53a0a77f900a7414cff98b4e8299ff2d69d0533fe56d3a0a67fd05a7414ebfa0846829ddf40c8d053bde8151a0a77ed01a3414eff13146829dfe4028d0533fe62d1a0a67fcb5a3414cff95b468299ff2768d0533fe82d1a0a7cfd0440e0cddf97b21419bdf2d6428337ee52c85066fec9d90a0cdfe92b21419bfe236428333fe6ac85067dbd0440a0cfd7a0781419bbf2f6418337be5ac83066fbcad9060cdfb94b20c19bfd256418337fc46c830667fcd59060cdff11b14c199ff35629833ef682203067eed03c060cff5a0580c199ff356410337be5ac52066fdca58a40cdff11b148199ff356290336fe62c32066efcbd8640cdef96b0c819bef2b6190337ee52c32066ff88d8640ccff9ab0c819f7d41101033f7a81e02067fb502c040cffca0380819f7e410a8833f7c81d51067fb902aa20cffd20354419fee2a4a8833ff880951066ff905aa20cebfa0862819dbf40ec5033bde8158a0677ed01b140cebf98262819dfd404c5033bfc5458a0667fd05b140cebfa085e819dbf30ebd033bde8157a0677ed01af40cedf9725e819dfd404bd033bfc5457a0667fcc5af40ccffa0b5e819d7f410ad033b7e81d5a0677bd02ab40cefda0356819def2a4ad033bfa8095a0667fcc5ab40ccff97b568199ff416ad033afe8213a0676fd03a740cef7a054e819dfb4069d033bf64c93a0677f5012740ccff98b4e8199ff2f69d0333fe56d3a0667fd05a740cebfa084a819dbf40e95033bde8152a0677ed01a540cefea024a8199ff316950333fe5ed2a0667fcada540ccff93b4a8199ff41695033abe8198a0ca5fd05b14196cfa065e832dcf40ab50653be82d6a0cb73d032b4194f7a0b56832dd740ca5065bce8154a0cb77903234196f7205468329fe4168d065b6e8117a2076ed01af440cdfa0b5e881db740ea5103bce8154a2077cd01a9440efaa02528819f7416a5103ade8158a0875dd0231410cbfa0b62821d3f410bd043b5e8157a0876dd022f410eafa085a821dcf40ab5043bae8116a08776d01ad410
      else
        if i < 5 then
          if i < 4 then
            0x76fd01af410eefa085a821ddf30ab5043bbe2156a08777d02ad410eef9845a821ddf2a8b5043bbe60d6a08777c41ad410eef9535a821ddf0a6b5043bbe50d6a08777d01ad410ebfa0856821def30aad043bde2155a0877bd02ab410ef795456821df7408ad043bde54d5a0877bc29ab410efda03568219ff316ad0433fe26d5a0867fd05ab410ef7a0856821def308ad043bde60d5a0877bc41ab410ef794356821def406ad043bde62d5a0877bc45ab410ef794b56821def276ad043bde0ed5a0877bc4dab410ef7a0b56821d7f410a5043bde8154a0877dd0429410efb98552821df710aa5043bee8154a0877dcc1a9410efb95352821d7f4109d043bde8153a0877dd0227410efd9834e821dfb1069d043bf654d3a0877ec29a7410efd9434e821dfb4069d0433fe62d3a0867fcada7410cff89b4e8219ff4169d043bf68213a0877ecc2a7410efd8854e821dfb40a9d043bf66113a0877ecaa27410efd98b4e821dfb1169d043bf656d3a0877ec2da7410efd94b4e821dfb1369d043bf682d3a087e7d03c0c1ccff9ab20839f7d41101073f7a81e020e7f75034041cddf97b20439bfb276408733fe6ac810e6fec9d8a21ccff9ab14439f7b41098873f7681d310e7f6d032621cffca024c439ffa302988737f656d310e6fed05a621cffd13148439b7f3161087377e5ec210e6f7cb58421cdf795b08439bfb276108733fe6ac210e7fe898c021cfbf20880439fbe40f00873fbc81a010e7fb902c021cffd15380439ffc40500873afe8216a0e76fd03ad41ceef9865a839def40ab5073bbe5896a0e77f5012d41cefd9315a839dfe402b50733fe5ed6a0e67fd05ad41cebfa084a839dbf40e95073bbe8192a0e77bd02a541cefe9824a839dfd40495073bf64c52a0e77f900a541ccff98b4a8399ff2f6950733fe5ad2a0e67fd05a541cebfa0846839dbf40e8d073bbe8191a0e77bd02a341cefea0246839dfe3028d073bfc4851a0e77f900a341ccff98b468399ff2f68d0733fe5ad1a0e67fcada341ccff92b468399ff4168d073ebe822060a6efcbd90a14def96b21429bf7296428537f64ec850a6ff49590a14dff11b214299ff35642853ede822050a7f3d0340a14ddf97b20c29bdf2d6418537de56c830a6fdca590614dfe92b20c29bfe236418533fe6ac830a6ff4958a614cff9ab14c29f7b41101853fb681a030a7fad02c0614fbea0854829fdd40ca9053fda815520a7fb4a9aa414ffca0354829bfd416a905377e5ec810a6fdca590214dfe92b204299ff35640853fda549510a6ff4958a214cff9ab14429bfd256188533fe6ac310a7df50424214feea0648429fed40a90853ff280d210a7ff098a4214dfe95b48429bfd41690853ff8486010a7df90440214fef20680429fee40b00853ff480e010a7ff0a940214ebfa0862829ddf40
          else
            0xb0c881bef2b6191037ee52c32206ff88d86440cff9ab0c881ff540901103ff280e022076fcbaaf440edf9745e881df7408bd103b7e5cd7a2077ed01af440edf9725e8819ff136bd1033fe82d7a2076fd02af440edf9545e881dbf2a6bd103b7e50d7a2076fd01af440edf9525e881dbf0a4bd103b7e5097a2076fc992f440edf8325e881dbf404bd103b7e56d7a2076fc2daf440edf94b5e881dbf276bd103b7e0ed7a2076fc95af440edf82b5e881dbf136bd103b7e82d7a2076fd03ab440ef7a0556881df7408ad103bde54d5a2077bca92b440cff97b568819ff136ad1033fe82d5a2076fd03a9440ef7a0552881dfd404a5103bee5d54a2077dd02a9440efb97352881df72a6a5103bee5c94a2077dca929440efb85252881df7264a5103bee8094a2076fd03a7440efba044e881dfb2a69d103bf680d3a2077ec9927440efea024e8819ff2f69d1033fe56d3a2067fc4da7440cffa0b4e881dbf40e95103bde8152a2077dd0225440efda034a881dfd2a495103bfa4c92a2077f50125440cff97b4a8819ff2b6951033fe4ed2a2067fc4da5440cffa0b4a881ff3409018a33fe6ac82146dfcc586428ddf97b0c851bdf2d6190a37de56c32146fdca586428dff11b0c8519ff356190a3bee8113a1477ed01a7428efd9324e8519ff1369d0a33fe82d3a1477dd0225428efda034a851dfd304950a3bfa8092a1467fcc5a5428cff93b4a8519ff136950a33fe82d2a147cfd0440e18fb7a0881431faf40f028633fe6ac820c6f7cb58a418cff9ab14831f7d41101063f7a81e020c7fb502c0418ebfa0862831dbf40ec5063bde8158a0c75fcc131418efea02628319ff136c50633fe82d8a0c75fd042f418edf9875e831def40abd063b7e5c97a0c77f5012f418cff98b5e8319ff136bd0633fe82d7a0c75fd042b418edfa0756831def30aad063bde8155a0c77bca92b418efea02568319ff316ad0633fe5ed5a0c67fc4dab418cffa0b56831d7f41095063b7e81d2a0c77bd02a5418efe9824a831dfd404950633fe62d2a0c67fcbda5418cff95b4a8319ff136950633fe82d2a0c67fcd590a10fb7a0881421f7741102043fce81604086efcbd90610def96b20c21bef2b6418437ee52c83086ff49590610dff11b20c219ff356418433fe6ac53087fad02c0610ff9a0480c21d7f410c5043afe6158a0875fc42b1410ef7a0562821d7f308c5043bee8118a0875fcc1b1410ebf883628219ff136c50433fe82d8a0875fd02b1410ebf95462821d7f2a6c5043afe14d8a0875fca1b1410ebfa0362821d7f2b6c5043afe16d8a0875fca5b1410ebf93b62821d7f076c5043afe26d8a0875fd05b1410edfa085e821dbf30abd043b7e2157a0876fd02af410edf9845e821dbf2a8bd043b7e60d7a0876fc41af410edf9535e821dbf0a6bd043b7e50d7a08
        else
          if i < 6 then
            0x5bfc5411a0cb7f885a34194ff60b46832ddf40c850653fe62d0a0ca7fcb5a14194ff95b428329ff23685065b7e5c17a2076fca82f440edf9305e881dbf240bd103b7e42d7a2066ff05af440ef795056881db7c0ea5103bee5c14a2077dca829440efb92052881dfb2609d103bfa4812a2076fd03a1440cff97b428819ff2b6851033fe4ed0a2067fc95a1440efd9304e8518ff9369d0a3bfa4812a1467fc9da1428cff92b42851d7f300c5063b7e5c17a0c77bca82b418c7fc9b56831dfd24095063b7e81d0a0c67fcc5a1418cff97b428319ff2b6850633fe4ad0a0c75fcc031410ebf95062821d7f260c5043afe42d8a0865ff05b1410edf9805e821dbf2a0bd043b7e4c17a08777cc02d410eef9505a821ddf260b5043bde5415a0877bcc02b410ef793056821def216ad0433df82d5a0877dcc029410efb95052821dfb2609d043bf66013a0877eca827410efd90b4e8219fbc169d0433fe62d0a0867fcada1410cff93b42821df74089d105bf680d3a20b7ec98a74414ff89b4e8829ff4169d105bee8111a20b7f8a8a34416ff13146882dfe4028d1053fe56d1a20a7fc9da34414ff89b468829ff4168d105f9e81a050cb5fd04314196bf98662832ddf40cc5065afe6158a0cb5fcc0b14194ff89b628329ff416c5065afe5958a0cb5fd02b14196bf96162832d7f2a2c5065afe8058a0cb5fcb5b14196bf95b62832d7f0b6c5065afe46d8a0cb5fc0db14196bf89b62832d7f416c5065b7e8217a0cb6fcc32f4196df9855e832dbf2cabd065b7e8157a0cb6fcc0af4196df9615e832dbf2a2bd065b7e8057a0cb77cc32d4196ef9655a832def40ab5065bbe5856a0ca7fcc5ad4194ff89b5a8329ff416b5065bbe8216a0cb77cc2ad4196efa055a832ddf302b5065bbe5456a0cb77d00ad4196ef98b5a832ddf116b5065bbe56d6a0cb77c2dad4196ef91b5a832ddf036b5065bbe26d6a0cb77d05ad4196efa0656832def30aad065bde5955a0cb7bd02ab4196f7951568329ff316ad0653fe5ad5a0ca7fc4dab4194ffa0b56832def410ad065bde6195a0cb7bcc0ab4196f796156832def402ad065bde62d5a0cb7bc45ab4196f796b56832def236ad065bde06d5a0cb7bc4dab4196f7a0b56832df7410a5065bee6194a0cb7dcc2a94196fb96552832df740aa5065bee6054a0cb7dcb0a94196fb95152832df7402a5065bbe8191a0cb7bd02a34196ff18146832dfe2c28d065bfc5451a0cb7f900a34194ff98b468329ff2d68d0653fe56d1a0ca7fc4da34194ffa0b46832dfe4108d065bfc6191a0cb7f8c2a34196ff16546832dfe40a8d065bfc62d1a0cb7f845a34196ff16b46832dfe2b68d065bfc16d1a0cb7f84da34196ff20b46832fb740f02103fce81604207eed03c0640ff9a0480c819ff356291036fe62c32206efcbd86440def96
          else
            0x3aea0cdff98b5d419dff356c18337fe82d83066ffcbd9060cdff95b20c19bff25641833f7e61d73066ffcc5ae60cdffa0b5cc19fef30aa9833ff660d53067fecb9aa60cdff98b54c19bff2f6a9833bfe6ad53066ffd05aa60cdff98b14c19bff25629833efe61d82067dfcc1b040ceff9ab60819bff416c10337fe56c82066ffc9d9040cfdf9735c819bff316b9033fde5d552067fbca9aa40cffe98254819ffd2e4a90337fe62d52066ffcbdaa40cfdf87b54819dff356a90337fe82d52066ffcc58a40cdff93b14819ffb2e699033ffa60932066ffcc5a640cdff97b4c819bff2b699033bfe6ad32066ffd05a640cdff98b0c819bff2b619033ffc82151067ff8c3aa20cfff18554419ffe306a8833ffc20d51067ff8b9aa20cfff15354419ffe406a8833ffc60951067ff8412a20cfff17254419ffe2a4a8833ffc4c951067ff8192a20cfff20254419ffe316a8833ffc5ed51067ff89daa20cfff12b54419dff30ec5033bfe6158a0677fcbab140ceffa0562819dff306c5033bfe5cd8a0677fca9b140ceff85362819dff406c5033bfe6098a0677fcb93140ceff95262819dff0a4c5033bfe4c98a0677fc193140ceffa0262819dff2f6c5033bfe56d8a0677fc9db140ceff92b62819dff410bd033bfe6157a0677fcc1af40ceff8835e819dff2a6bd033bfe80d7a0677fcc12f40ceff9325e819dff410ad033bfe61d5a0677fcc2ab40ceff98356819dff106ad033bfe5cd5a0677fca9ab40ceffa0356819dff304ad033bfe2095a0677fcb92b40ceff95256819dff264ad033bfe0c95a0677fd012b40ceff98b56819dff2f6ad033bfe4ed5a0677fc95ab40ceffa084e819dff30e9d033bfe6153a0677fc42a740ceff9754e819dff40a9d033bfe60d3a0677fcb9a740ceff9534e819dff3049d033bfe2093a0677fcb92740ceff9524e819dff0a49d033bfe4c93a0677fd012740ceff98b4e819dff1169d033bfe5ed3a0677fcada740ceff85b4e819dff2569d033bfe0ad3a0677fd05a740ceffa084a819dff30e95033bfe6152a0677fc42a540ceff9754a819dff40a95033bfe60d2a0677fc41a540ceff9734a819dff2a695033bfe14d2a0677fd01a540ceff9824a819dff2a495033bfe4c92a0677fcc5a540ceff95b4a819dff276950333fe4ed0a20a7fc8da14416bf98062832d5fc0cc5065afe5818a0cb5fca8314196bf91062832d7f216c50652ff82d8a0cb67f032f4196df9805e832dbf2c0bd065b7e5417a0cb6fc882f4196ef9605a832ddf300b5065bbe5416a0cb77c882d4196ef90b5a8329dfc16b5065bde5415a0cb73f032b4196f798056832def2c0ad065bde4415a0cb7bc85ab4194f7e0b56832dd7c0ca5065bee6014a0cb7dcb0294196fb95052832df7220a5065bfc4411a0cb77b03234196ff18046832dfe2c08d06
    else
      if i < 11 then
        if i < 9 then
          if i < 8 then
            0x9dff2d68d073bfe56d1a0e77fc2da341ceff92b46839dff0568d073bfe82d1a0e77fcd5b0a14dffa0b61429bff276428537fe46c850a7f7cc32ca14ff798559429bff316b28537fe82d650a77fcd5b0614dffa0b60c29bff2b6418537fe46c830a7f7cc32c614ffd98358c29bff316b18537fe82d630a7fbcc2aa614ffd98354c29bff316a98537fe5ad530a77fcd5aa614dffa0b54c29bff316298537fe5ac530a6ffc8d8a614ffea0854829ffd30ca9053ffa615520a7ff4b2aa414ffe98354829ffd106a9053ffa58d520a7ff4a9aa414ffea0354829ffd316a9053ffa5ad520a7ff49daa414ffe91b54829f7f30cc0853ffa549810a7f7c35b0214eff9ab60429bff416c0853ffa548810a6ffcad90214dff93b20429ffd2a4b0853ffc605610a6ffcc5ac214ff796554429ffd2a4a8853ffc605510a6ffcc5aa214dff96b54429ffd256a8853bfe6ad510a6ffd05aa214dff98b14429bff27628853ff658d310a7ff4a926214fff1814c429bff316988537fe5ad310a6ffcada6214eff9ab4c429bff41698853ffa548310a6ffcc586214dff95b0c429ffd41090853ffa619210a7ff4c2a4214ffe88548429ffd2ca90853ffa815210a7ff4c1a4214ffe88348429ffd2c690853ffa54d210a7ff429a4214ffea0348429ffd30290853ffa545210a7ff498a4214ffe98b48429ffd2b690853ffa4ed210a7ff4a940214eff98562829dff2cac5053bfe8158a0a77fcc1b1414eff96362829dff2a6c5053bfe14d8a0a77fd01b1414eff98162829dff2c2c5053bfe5458a0a77fc28b1414eff93162829dff062c5053bfe8058a0a77fcb5b1414eff95b62829dff0b6c5053bfe4ed8a0a77fc1db1414eff91b62829dff036c5053bfe82d8a0a77fcc2ad414effa055a829dff306b5053bfe54d6a0a77fc29ad414effa035a829dff2a2b5053bfe4c56a0a77fd042b414eff98656829dff30aad053bfe5955a0a77fcc1ab414eff88356829dff2c6ad053bfe54d5a0a77fd01ab414eff98156829dff102ad053bfe5855a0a77fca8ab414eff93156829dff062ad053bfe8055a0a77fcc5ab414eff96b56829dff276ad053bfe46d5a0a77fd0427414eff9864e829dff30a9d053bfe2153a0a77fcb2a7414effa054e829dff3069d053bfe58d3a0a77fca9a7414eff9814e829dff1029d053bfe5853a0a77fca8a7414eff8514e829dff2629d053bfe8053a0a77fcc5a7414eff96b4e829dff2b69d053bfe46d3a0a77fd0423414eff98646829dff30a8d053bfe2151a0a77fcb2a3414effa0546829dff3068d053bfe20d1a0a77fcb1a3414eff95346829dff0a68d053bfe80d1a0a77fcc0a3414eff95146829dff2628d053bfe62d1a0a77fcada3414eff93b46829bff416c3833efe61d850677fcd5b0a0cdffa0b61419bff276428337fe4ac85067efcc
          else
            0x1154086ffcc5aa810dffa0b55021f7f308c18437fe26d830877fcd5b0610dffa0b60c21bff2b641843fde61553087fbcaa2a610ffd98354c21bff316a98437fe26d530877fcd5aa610dffa0b54c21bff31629843fee61143086ffcc5a8610dff95b50c21bff13701843bfe6158a0877fd02b1410eff98462821dff2a8c5043bfe60d8a0877fca9b1410eff85362821dff286c5043bfe80d8a0877fcadb1410eff94b62821dff276c5043bfe8215a0877fcc2ab410eff98456821dff2a8ad043bfe60d5a0877fc41ab410eff95356821dff286ad043bfe80d5a0877fcc5ab410eff94b56821dff276ad043bfe8214a0877fcc2a9410eff88552821dff40aa5043bfe8213a0877fcc2a7410eff8854e821dff40a9d043bfe6113a0877fcaa27410eff9834e821dff2a69d043bfe62d3a0877fcada7410eff94b4e821dff356c10737fe82d820e6ffc8d9041cfef97658839ffd304b10737fe62d620e6ffcbdac41cdffa0b58839f7f30cc0873efe609810e7f7c35b021ceff9ab60439bff416c08737fe5ec810e6ffcad9021cdff92b20439fbf30eb8873f7e5d9710e7efcb92e21cdff98b5c439bff416b8873fbe589610e7ff8c0ac21cdff98b58439bff2f6b0873ffc605510e7ff8b8aa21cdff96b54439ffb276a8873bfe6ad510e6ffd05aa21cdff92b14439ffb41098873ff661d310e7fecc32621cffd9764c439ffb2ea98873ff6595310e7fecc12621cffd8824c439ffb2e498873ff6589310e7feca92621cffd8524c439ffb40498873ff6605310e7fecb8a621cffd9514c439ffb31698873ff622d310e7fecbda621cffd96b4c439ffb2b698873ff616d310e7fec95a621cffd82b4c439ffb41698873ff654d210e7ff4b12421cfff17148439ffb262908737fe62d210e6ffcbda421cdff96b48439bff2b690873bfe6ad210e6ffd05a421cffd95308439bff316108737fe56c210e7feca9c021ceff9875a839dff30ab5073bfe5d56a0e77fd02ad41ceff9825a839dff2e4b5073bfe5496a0e77fc292d41ceffa025a839dff2e2b5073bfe5456a0e77fc90ad41ceff85b5a839dff056b5073bfe8212a0e77fcc3a541ceff9864a839dff2ec95073bfe6152a0e77fc42a541ceff9754a839dff2ca95073bfe8152a0e77fcc12541ceff9624a839dff2a495073bfe6052a0e77fc40a541ceff9714a839dff2c295073bfe5452a0e77fc28a541ceff9214a839dff40295073bfe62d2a0e77fcb5a541ceff95b4a839dff23695073bfe8211a0e77fcc3a341ceff98646839dff2ec8d073bfe6151a0e77fc42a341ceff97546839dff2ca8d073bfe8151a0e77fcc12341ceff88246839dff2e48d073bfe5891a0e77fca92341ceff85246839dff4048d073bfe6051a0e77fcb8a341ceff95146839dff2428d073bfe62d1a0e77fc45a341ceff97b4683
        else
          if i < 10 then
            0xdff95b50c81bff13701903f7e5cd72207fbcbaaa440ff795354881ffd2e4a91037fe5ed52207efc3daa440dff89b54881dff356a91037fe82d52207fdcba28440ffb95450881ff7286a11037fe5ed42206ffcada8440dffa0b50881ffb2e699103ffa50932206ffcbda6440dff95b4c881bff296991037fe26d322077fcd5a6440dffa0b4c881bff2b619103bfe5517a2077fca9af440eff9435e881dff406bd103bfe5097a2077fc992f440eff97456881dff2a8ad103bfe5cd5a2077fca9ab440eff94356881dff406ad103bfe5c95a2077fca92b440eff94256881dff264ad103bfe0c95a2077fd012b440eff97b56881dff296ad103bfe4ed5a2077fc95ab440eff97552881dff40aa5103bfe5c94a2077fca929440eff85252881dff404a5103bfe5d53a2077fd02a7440eff9744e881dff2a89d103bfe5cd3a2077fca9a7440eff9724e881dff2a49d103bfe1493a2077fca127440eff9324e881dff4049d103bfe5ed3a2077fcada7440eff92b4e881dff2ea95103bfe8152a2077fcba25440eff9544a881dff2e695103bfe54d2a2077fca1a5440effa034a881dff2a495103bfe5092a2077fc9925440eff95b4a881dff29695103bfe4ed2a206ffc4dc0628dff89b60851dff356c10a37fe82d82146ffca590428dff93b20851ff7286a10a37fe62d42146ffd05a8428ffe9824c851ffd284990a37fe62d32146ffca5a6428dff89b4c851dff356990a37fe82d32146ffcc586428eff98252851dff104a50a3bfe8094a1477fcc127428eff8824e851dff2849d0a3bfe4c93a1477fd0127428eff94b4e851dff2569d0a3bfe0ad3a1477fc4da7428effa0b4e851dff410950a3bfe6112a1477fcc1a5428eff8834a851dff286950a3bfe80d2a1477fcc125428eff9424a851dff264950a3bfe62d2a1477fca5a5428eff93b4a851bff137040637fe26d870c6ffd05b0e18fbf98761431bff136c2863bfe6ad850c6ffd05b0a18fdf9875d431bff316ba863efe61d820c6ffc4db0418eff9ab60831bff416c10637fe56c820c6ffcc5ae418ff797554831ffd304a9063ffa5c9520c6ffcc5aa418dff97b54831fbf0f6a90637fe26d520c77fcd5aa418dffa0b54831bff31629063bfe61d8a0c77fcc2b1418eff97562831dff40ac5063bfe6098a0c77fcb931418eff95262831dff0a4c5063bfe8098a0c77fcbdb1418eff95b62831dff256c5063bfe8217a0c77fcc2af418eff9825e831dff410ad063bfe61d5a0c77fcc2ab418eff98256831dff104ad063bfe5c95a0c77fca92b418effa0256831dff316ad063bfe5ed5a0c77fc95ab418effa084a831dff30e95063bfe6152a0c77fcbaa5418effa054a831dff30495063bfe5492a0c77fcc5a5418eff95b4a831bff137040437fe26d850877fcd5b0a10dffa0b61421bff416c2043fee6
          else
            0x16950633ff5ed2a0c67feada5418effa0842831dff30e85063bfe6150a0c77fcbaa1418eff98242831dff2e485063bfe5490a0c6bfe4dc1010d7fc9b61421bbfaf6418437bf5ac83086fbead90610dfbd4b20c21bfda56418437fd46c83086ffc8590610cffdab20c21aff936a98435ff26e03087dfd0430010fbf98560021dff356c00437fe62d50087feca9a6010ffda034c021bff316980437fe56d300877fcd5a6010ebfe0862821d7fb0ac5043aff60d8a0875fe41b1410eff98062821dff2a0c5043bfe4c18a0877fc85b1410cffe0b62821d7faa6c5043aff56d8a0875fe9db1410ebfc3b62821d7fc16c5043b7f8217a0876fec2af410edfd835e821dbf906bd043b7f54d7a08777f042d410eefd855a821ddfb06b5043bbf20d6a08777ea9ad410eefe035a821defb0aad043bdf54d5a0877fcc02b410eff930568219ffb16ad043bdf8215a0877bec1ab410ef7c8356821defc06ad043bdf62d5a0877be9dab410efbe0852821df7b0aa5043bf760d3a0877ee41a7410efdd534e821dff3009d043bfe5413a0877fc9827410cffd8b4e8219ffab69d043bfe42d3a0867ff05a7410efde084e821dfbb0a9d043bf762d3a0877ee45a7410efdd5b4e821dfbc169d043bfe8210a0877fcc2a1410eff98342821dff10685043bfe54d0a0877fd01a1410dff89b80c82bff136a8905bfe6ad5120affd05aa2415ff95b50482bff416a0905ffc5053120affcada62415ff94b4c482bff13698905bfe6ad3120affd05a62416ff95152882dff402a5105bfe5453a20b7fca0a74416ff9314e882dff4029d105bfe46d3a20b7fd02a34416ff95446882dff2a68d105bfe50d1a20b7fd01a34416ff95146882dff2828d105bfe4c51a20b7fcada34416ff94b46882dff2768d1057fe26e080caffc4db0a196ff9ab61432bff416c2865fbe619650cbfbcc2aca195ff98b59432bff136b28657fe82d650caffc4dc0a197bf98660432fdf0d6c08657fe26d810cb7fcd5b02195ffa0b60432ffe302b08657fe62d610cbfbcb2aa2197ff18154432bff316a88657fe5ad510caffc4daa2196ff9ab54432bff416a8865bfe6158a0cb7fcb2b14196ffa0562832dff302c5065bfe5858a0cb7fca8b14196ffa0162832dff2d6c5065bfe56d8a0cb7fc8db14196ff9855a832dff40ab5065bfe5456a0cb7fd042b4196ff98656832dff30aad065bfe5955a0cb7fcc0ab4196ff96156832dff2a2ad065bfe8055a0cb7fcc5ab4196ff96b56832dff236ad065bfe8211a0cb7fcc3234196ff98546832dff2ca8d065bfe8151a0cb7fcc0a34196ff95146832dff3168d065bfe56d1a0cbfdcba2a840dff97b55081bff416aa103f7e5d173206ffc4dae640dffa0b5cc81fef2a8a9903ff65cd53206ffcbdaa640dff89b54c81dff356a99037fe82d53206ffcbda864
      else
        if i < 13 then
          if i < 12 then
            0xcb7fcc02b4196ff96056832dff2a0ad065bfe4415a0ca7fec5ab4194ffd6b56832dff216ad0653ff82d5a0cb7bec32b4196f7d8156832defac2ad065bdf62d5a0cb7be45ab4196f7d6b56832defa36ad065bdf82d5a0cb7dec3294196fbd8552832df7acaa5065bef8154a0cb7dec0a94196fbd6152832df7aa2a5065bbf8191a0cb7fac0a34196ff56146832dfeaa28d065bfe6011a0cb7fcb0234196ff950468329ffb168d0653ff5ad1a0ca7feada34196ff58646832dfeb0a8d065bfd5951a0cb7fb02a34196ff58b46832dfead68d065bfd56d1a0cb7fcc3214196ff98542832dff2ca85065bfe8150a0cb7fcc0a14196ff96142832dff2a2850655ff26d73206bfe4dc0640d7fc9b54881fbf2eab8103f7e5cd70206ffcbdaa040ffd9534c081ffb406981037fe5ed30206ffcada6040eff9ab4c081ffd2a4901037fe5ed20206ffcada4040dff93b48081dbfaeabd103b7f5cd7a2076feb92f440eff9505e881dff260bd103bfe4817a2067ff05af440edfd535e881dbfc06bd103b7f5497a2076fe992f440edfd5b5e881dbfa76bd103b7f0ed7a2076fe95af440edfe0b5e881dbfc0ead103bdf54d5a2077bea92b440eff97056881dff260ad103bfe4815a2067febdab440efbd7552881df7ae4a5103bef5494a2076ff03a7440efdd534e881dfba649d103bfe5c13a2077fca827440eff9304e881dff2409d1033ff5ed3a2067feada7440eff90b4e8819ffc169d103b7f81d2a2077f6a925440efed324a881dff2e095103bfe5412a2077fc9825440cffd7b4a8819ffab6951033ff4ed2a2077fcbaa1440eff97342881dff2a685103bfe80d0a2077fcb921440eff95242881dff26485103efe602081475fec541028d7fc9b82051bbfaf6418a37bf5ac83146fbead90628dfbd4b20c51bfda56418a37fd46c83146ffc8590628cffdab20c51aff937018a35ff26d82147fed01a6028eff9ab4c051bff316900a37fe4ed201477ef01a7428efdd324e851dff2609d0a3bfe4813a1477fc85a7428cffe0b4e851dfdb04950a3bfe6012a1477fc9825428cffd8b4a8519ffa76950a3bfe8210a1477fc41a1428effa0342851dff304850a3bfe4c90a146bfe4dc1018d7fc9b61c31aff936a9063efe821800c7dfcc2b0018eff9ab60031fbf2eab80637fe62d700c6ffcc5aa018dff97b54031ffd2a4900637fe62d200c6ffcbda4018dff95b48031dbfc0ec5063aff6098a0c77fcc031418eff97062831dff2a0c5063bfe4818a0c77fc85b1418cffe0b62831dbfb0ebd063b7f5c97a0c77fcc02f418eff9505e831dff240bd0633ff62d7a0c67ff05af418edfe0756831defb0aad063bdf5495a0c77fcc02b418eff97056831dff240ad0633ff62d5a0c67febdab418edfe074a831dfdb0495063bfe6012a0c77fcb825418eff9504a8319ffb
          else
            0x55a832dffb02ad065bff5855a0cb7fec3234196ffd8546832dffaca8d065bff8151a0cbfeeb9aa640ffed7254881ffbae699103bff6ad32206fff05a6440effd535e881dffc06bd103bff4c97a2077feb9ab440effd7256881dffa64ad103bff5d53a2077feb9a7440effd534e881dffae49d103bff5493a2077fe9927440effd7b4e881dffab69d103bff4ad3a2077febaa5440effd734a881dffaa695103bff80d2a206ffe9590628effd8a60851eff936c10a3bff6ad82146fff05b0428ffed824c851bffb16990a3bff6ad32146fff05a6428effe084e851dffb049d0a3bff4c93a1477fe95a7428effe084a851dffb06950a3bff20d2a1477ff01a5428fbfd8761431bffc16c2863eff61d820c77fed5b0418dffe0b60831fefaeaa9063ffb609520c7ff6b92a418dffd8b54831bffc16a9063bff61d8a0c77fec2b1418effd7562831dffb04c5063bff5c98a0c77fea931418effd7b62831dffab6c5063bff4ad8a0c77ff042f418effd855e831dffb04bd063bff61d5a0c77fec12b418effd7256831dffc1095063bff61d2a0c77fec2a5418effd754a831bffc16c2843bff6ad83086fff05b0610dffd5b20c21fefb0aa9843ff760d53086ffec5aa610dffe0b54c21dffb0ac5043bff60d8a0877fea9b1410effd5b62821dffa76c5043bff60d5a0877ff01ab410effe084e821dffb0a9d043bff60d3a0877fea9a7410effd8b4e821dffab69d043fde5420520b7bead40a4157fc9b81482bff216299053ff6ac5320abfe4daa2417fd9314c082dff35698105ffc5451020affcada20415ff93b44082dfba629d105bfe4c13a20b7fc88274416ff90b4e8829ffc169d105bfd5451a20b7fa98a34416ff95046882dff2608d1053ff56d1a20a7fe9da34416ffa0542882dff0a685105bfe5450a20b7fc98a14416ff95b42882dff276851055ff26d650cabfe4dc0a1957fc9b60432aff936a8865efe615800cbdfcc0b00196ff9ab60032fdf2cab0065fbe585600caffcc5ac0197f7a0554032fef2a2a80657fe62d500caffcb5aa0196ff9ab54032ffe2a2880657fe62d100caffcb5a20195ff95b44032d7fb0cc5065bbf8198a0cb5fec2b14196bfd8162832dff300c5065bfe5818a0cb7fca8314196ff91062832dff216c50653ff82d8a0cb5feb2b14196bfd6162832d7faa2c5065aff5ad8a0cb5feadb14196bfc5b62832d7fa36c5065aff82d8a0cb6fec32f4196dfd855e832dbfacabd065b7f6057a0cb6feb0af4196dfd515e832ddfb0cb5065bbf5956a0cb77eb0ad4196ff9805a832dff2a0b5065bfe4416a0ca7fec5ad4194ffe0b5a832ddfb0ab5065bbf8156a0cb77ec0ad4196efd515a832ddfb16b5065bbf22d6a0cb77eadad4196efc5b5a832ddfa36b5065bbf82d6a0cb77f032b4196f7d8556832defacaad065bdf5455a0
        else
          if i < 14 then
            0x2bae15a70aab0546c29aa148f0a248500c27bc138d09a384c8825b812b70938848ac23f611b508b20444c219a107c081583f681f120f38077383a581ca00e2b06f2836501a860ce7065b8316c18400bda05da82dbc16520ae3055f029e014640a0d04e38260412b809160468021fc105c080903f201e780eb0073e037c01af40cee06310306017440b5805a802d2016800b38059802ca016400b18058802c2016000af8057802ba015c00ad8056802b2015800ab8055802aa015400a98054802a2015000a780538029a014c00a5805280292014800a380518028a014400a18050802820140009f804f8027a013c009d804e802720138009b804d8026a01340099804c8026201300097804b8025a012c0095804a802520128009380498024a012400918048802420120008f80478023a011c008d8046802320118008b80458022a011400898044802220110008780438021a010c00858042802120108008380418020a010400818040802020100007f803f801fa00fc007d803e801f200f8007b803d801ea00f40079803c801e200f00077803b801da00ec0075803a801d200e800738039801ca00e400718038801c200e0006f8037801ba00dc006d8036801b200d8006b8035801aa00d400698034801a200d0006780338019a00cc006580328019200c8006380318018a00c4006180308018200c0005f802f8017a00bc005d802e8017200b8005b802d8016a00b40059802c8016200b00057802b8015a00ac0055802a8015200a8005380298014a00a4005180288014200a0004f80278013a009c004d8026801320098004b80258012a009400498024801220090004780238011a008c00458022801120088004380218010a008400418020801020080003f801f800fa007c003d801e800f20078003b801d800ea00740039801c800e200700037801b800da006c0035801a800d2006800338019800ca006400318018800c20060002f8017800ba005c002d8016800b20058002b8015800aa005400298014800a20050002780138009a004c00258012800920048002380118008a004400218010800820040001f800f8007a003c001d800e800720038001b800d8006a00340019800c8006200300017800b8005a002c0015800a800520028001380098004a002400118008800420020000f80078003a001c000d8006800320018000b80058002a001400098004800220010000780038001a000c00058002800120008000380018000a00040001800080002000037ff02a74416ffd514e882dffa629d105bff46d3a20b7ff02a34416ffd5346882dff8a68d1057ff82d850cbf7ec32ca197f7d8559432bffb16b28657ff82d650cb7fec2b14196ffd6562832dffb02c5065bff5858a0cb7fea8b14196ffd6b62832dffab6c5065bff46d8a0cb7fec2ad4196ffe
          else
            0xb3a04dd020e80cc404320101000a7fd53fbc9fd24fe1c7ec83f3b9f974fc2e7ddc3ecb1f4e8f9d27c8d3e341f0b4f7fa7ba13db89ec80f59e7a7e3d219e84cf36e795b3c959e3c0f18078903c301e0c0efea77c53bca9dd94ee5476ef3b499d960ec5075cc3ad39d558ea2074e03a4d1d124e85e73ff39d19cd48e61872e7395b9ca48e46c720638da9c614e27e70ee384e9c130e04e6ff737cd9bd54de1e6ed437521b978dc886e1436e19b5f4da586cf1364a9b0e4d7e66ba235b91acb0d5cc6ab6352d1a850d3c8699334b19a448d1f068bd343b9a06ccfc067b033b519cbccde866b9333f1990ccbfa65c232ad994acc9b46489322c99020c7b0639d31a098c18c5ac6290312a98894c3a861a430bf984b8c1ba60ad303e980b0bfe25fcc2fbd97ca8bdb25ea92f37178f8bc1c5dbd2ec1174c4ba025cdc2e45970e8b7d25bb92dbf16d38b63c5acd2d4916904b42259ec2ccd964fcb1dc58be2c3c16120b03057bc2bc615cc0ada856ba2b3f958b8abfc55ad2ab915534a9f854ab2a3d9512ca7f453ca29d814dd4a68a53152962149a0a47051e728d6145c4a22a50b9283f140b49fe44fa127b893d309df64e9f2721938a49bc64d9226a09344499964c9b26359306897d44b9925ba12d1096544ad92554929e494664a1924ef126e4933e497a24aa9246891be48ba2450121c09080481b23f591f188f58479223bc11d788e88472a238291b288d1e4675231d118288b9e459422ac914a489b0449d222b910f4880443c721c610d18864242db21451093c8454420520df905e482a84119207490234807840011fd28fd247e1c3ec81f410f8f07c023dd11ec58f51479d23cb91e4a0f1bc78943c251e000ef6c77563b701d9a8ec1475c03abb1d4b0e9c474983a271d068e7a0735a39671c908e3c4718238a71c410e148707038081bf18def86f1c37691ba78dcd46e3637011b630dab06cf8364c1b138d8086bd035ce1ac98d5e46a7c34f81a640d1dc686233eb19dd8cdd466a0332019678c9f86486320818db8c5f06256310618708c2f06102305c18058bee85f2a2f4f17950bb905d522e63170e8b75c5b382d6c16880b3ac59342c6a160c8af2057302b5215910ab1855422a7c15158a81853ac298514aa8a4ec524228db144a8a1685080280513df89e104e92270e136f09a344ce6262d12f3896b04b0e2541128e09384494c247612180902c47cc23c111ce08ddc468e2317116e08ab0450e226d1129888e4443e220510f0086c0430021451085083104128206f10250809440161ff10feb87ec83f301f7e0fb207d283e081eea0f57879d03c881e140ef2076d03b081d490e92073fc39881c7e0e1c06ff4376e1b7c0da606bec35801a850d14867e433a819a40cb48651031fc18b80c4406108300e17b60bbd85d002df416b40b3705874
  else
    if i < 23 then
      if i < 19 then
        if i < 17 then
          if i < 16 then
            0x342d97c6cabb64c9b230d8f36c6cb62fdb160d8966c3e361b5b0a6d8396c0a35fbdafaad7b06bc5b5d99ae82d7276b8135b75ad86d69e6b42359d5aca0d6366b0e35835abe6d5d96ada3563daaead55b6a9b35471aa04d4e86a61b52a5a934d4756a28350d9a838d40269f9b4f91a794d3b069cb34dc5a6c4d353699cb4c51a5f4d2d5695834a59a4f8d257691934835a3e6d1d968e5346c1a316d17c68b13454da288d12a6888343d9a1b8d0cd685f34291a0fed0656825b40c5a02ecffd67ec33ef99f48cf7f67b833d859e8ecf2d6789b3bb99da8cec5675033a459d04ce686727338fd9c60ce166703b37e19bd2cdda66e5b36c59b2ecd8866b7335519a74cd2b668e3340999d0ccc36649b31b99892cc1965fa32f699754cb8565b032cc19616cae6655b32a4594d8ca476511327f593b0c9b364c7325799272c9146472322fd9134c875642db2105904ec80263f431f0d8f52c79a63bab1d418e6cc71c638131ba18db2c6ca635831a598cf8c66263243188d8c28c5ef62eab16c18b42c59262b6b15218a5cc5096277b13558976c4ac624eb123988fec45a62203106d87d6c3d161dbb0e4986f0c35e61a230c7d860ac2f66168b0add8524c278612f30911846ac1e460da305e58266c0e26053b0209808ec0015fddafe017e5ebef45f67afa7d7cb2be1e5ef72f6f97adabd325e762f2c578c0bc3b5e002eee976e8bb395d742eab57510ba635d0eae7897322b9565c98ae3d9714ab85f5c17adfd16f88b7945bb22dc796ddcb6be5b3c2d94d6c04b5a65abb2d5196a2cb4f15a5b2d21968acb41059f02cec16700b35b59902cbed65acb2b159462c971646eb20758e62c67162d8b13c5880ac3716142b06658102bf955f80af8557a52bc955dd4aec557452b93d5c54adef56d4ab5e55a7cad03566f2b28d58baac2255feaaf09570eab4c55832ab855536aa60550d2a7515348a95354812a3755144a84653faa9ebd4ebca70d5353299d94c60a5df52cca95a54a30a4dd5246290ed4816a3af51bfa8d694628a2c35144288dd43cca1a050a2284514186a088502127ff13f2a9f5a4f8a27be93d949e844f19a77b53b649d614e8da7329391e9c3e4e01a6f4d371a9b734da1a6b9d352c9a454cffa668d328e98f64c68a622d307497ff4bd1a5dcd2e7096e74b562596d2c1495da4ae0255e92a5294ee4a4ea5131280c93aa49bd24ca525dc92be49312481923ac918548a5243b9217c906d4829a40611f8e8f8c479da3ba91d488e48470c237a11b2e8d6746a6a344919c48cb24630a30f118188bdc45d622df116988b1c457622af115028a3044f5226e912e8892e445e2220510b8882c43f8a1ed90eca8740437d21afd0d34865f43072174d0b308552428621371092c8466421b20fc10796839b41a520c3d05be82994129a080903a481974
          else
            0x70c3af21d5b0e888737439261c490dff86ed436d61b370d8186b3c35621a930d3a8690433ee19ad0cb18640c319e18850c1d8601c2f7a17730b9485b7c2d2a164b0b168578c2b3215650a98853f42992147f0a2585004276e136d099c84bbc254a125b091e8482423aa11b708cc8453c22621113086f842ac211a104307f183e641eca0f1b077383a741cfe0e61070b837e41b5e0d7b06988344c19ea0c95061a8300417c60bc505bd82d7416520adf054a82984142e09cd04c18253c126208fd046f823041146086f041d8201c0f7a079f03c081cdc0dda06a3032c818940c0e05d302da815ac0a4204ed0251811bc084a03f101e980e7c06aa0337017680a8c04b2022500ed80644028e00fd00648025400c2002cfff17fe63fe9dff04ff5d7fa1bfca5fe34fef57f683fad9fd4efe987f3f3f965fc52fe0f7ef53f741fb6cfd917ec13f5a1fa9cfd347e92bf3d5f9a0fcab7e433f185f878fc177e043ef61f766fb8e7db4bed11f63efb057d7b3eb45f56efa927d36be921f45cfa097cf7be781f376f9967cbe3e5b5f290f9237c84be3e9f1c0f8bb7c50be1f1f0daf8537c173e051efdef7ca7bddbdeb1ef3af7787ba9bdcb9ee12f6e47b653dac1ed2cf6717b263d89dec04f5e87ae73d6fdeb4af58b7abe3d589ea90f5237a7f3d365e97ef4a57a45bd1c5e898f4277a0c3d025e7c8f3d579ddbce2de6ccf34c79993cc35e5d0f2ce795fbca69e516f27c79313c94de472f22a79083c805e3e4f1e378ea3c715e36cf19c78c13c5a1e286f1297887bc3d5e1b6f0c178593c28de128f085783b3c145e058f01d7801bbfa5df9eefaa77c2bbd81de8cef37778ebbc0dddd2eeda7765bbac5dd18ee677726bb8cddc1cedde76d73b625dac8ed3f768d3b401d9ccecc17648bb1b1d88eec2d76043af8dd77ceb9975ba3ad69d66aeb10757b3ab45d558ea927541ba979d488ea2a750dba805d3cee9c274d43a60dd2bce94474953a415d1aae8c6745bba2a1d106e85e741cba07dd00ae7e073e339eb1cf0ee76d73a9b9d11ce6ae726738bb9c21cdc6e6c9735d39a55ccf6e66c7329398e1cc26e5ee72efb96e9cb40e58672b639549ca5ae513727cb937dc98ae4957243391b1c8a4e42d7209b8fe5c7d4e3d071db38e9dc704e37371acb8cfdc634e300717338b05c54ee28d7139b8965c468e21a7105b87f1c3dae1d370d738651c2f4e16070a338485c224e1037074b8369c196e0b1704bb81f5c0c6e03e701238055bff6dfec6fe937ee1bf52df9a6fc5b7dc5beaedf3d6f9737c51bdf4deeb6f6e37b09bd50de8e6f3a37969bc80de316f0bb77c9bb9adda86ec1b75a5bab4dd406e8db73d9b9a2dcb76e5437265b914dc706e30b7149b870dc296e0236fa9b7a0dbb66dc8b6db1b68edb226d7eb6b61b566da8e6d34b6911b43eda056cf5b6719b
        else
          if i < 18 then
            0x56d73b6b25b52ada616cdfb6525b1d2d85d6c09b5f7daf82d7616b8bb5addad32d6656b0db56edab3ad5696a8fb5355a942d3e969cfb4bf5a4e2d23d68e3b464da2ead1576865b3f9d9eb6ceb966f5b3525994ecc1b65bcb2b05943ec93b6457b208d8f02c6df6329b16c58acec51d6274b111d874ac2ed611ab06a5820ec0655fd6afc857d2abe095eb3af47578f6bbd95d9baec0d7572ba855d33ae76d729eb9315c52ae00d6eeeb6eb5b2fad69d6a0ab46359ebacc7d64fab1995865ac0fd5f66af115763ab8ed5b5ead0d5677ab295590eabfb55b7aab35542aa9735447a9f5d4e96a6bf530ea953d495aa42151bfa8bcd44faa20750c8a846d4176a0875013a7fcd3f7e9f8b4f95a7b853d5a9e794f22a77ed3b629d254e41a6f85375a9b634d97a69dd33d699334c53a5f652ec696c14b1aa56a529e294a74a23a4f9d2766937f49b0a4bad251691ff48b9a44a52166901147e3a3ea51eea8f57475aa38fd1c168d69468fa32a5183a8be945e5a2e5d16168a7f44e3a264d1292892b4470a22b510f2885b441ea1fcd0ece86c54311a160509be843d41cda0c3d0506820d40d6a05e5028a8111406ea024cffe27fbd3fcf9fdacfd927e533f1a9f804fabe7c913e239f04cf7927bab3dc69ec04f5427a2b3d069e764f37679873c9e9e47cf1d678b73c419e13cf03677d13b979dbeced6276933b3a9d95ceb9675293a439d0f4e81273d539999ca44e48e71d138ad9c49ce1e670d5382f9bfa4df3e6f13377a9bb04dd466dd536999b29cd8ba6c1335fa9af04d7466b6f359d9aabcd4466981346f9a0f4cf3666f9332b9972cca266487320898fccc77e63a131b698ce4c60a62bb3138988f4c33660e3302b97f2cbf2e5f792fa297c9cbd365dcd2e959727cb8265b712d67968b4b34259152c2395e94ae0656772af595474a89e53ad299094bb4a572521728ba9434ca0ba4fa52776939849b7e4d07263292f6496164ad7255c92a1493c649572491921ac8f924727234d9183c8aae449f21fe90d148572422d20af9029c80e64055201b8ffb47f463f591f878fb6c7d223e731f2a8f8847bae3d8d1eac8f43c798a3c911e2e8f04c77923b951da58ec04759a3a991d328e91c74523a0b1ceb8e63472de390f1c578e13c6fde37a51ba28dc446d6236671b0e8d7a46b1235291a648d1a4683e33d519ba8cd04664632d919478c91463f6319b18a88c47461d230b518408c0dc5fda2fa317ac8bc3c5d8a2e7b17188b79c5b3a2d53168f8b3ac596e2c83161c8afbc57762b45157d8aac454fa2a4915158a72c52d6292114608a1dc505a27e313cc89d3c4e3626fd1364899a44c3e25eb12d08955c4a4624d912478916c484e23f311d488d2445fe22b5112a8882c4382217710968838c415e206510188804c3f921f7f0f9a87bac3d421e570f0687
          else
            0x910e0985902c91b22f04c88700e09e46c8b91121c42309a91782442242c13423645e09910e01c238b113522f04a8b616522f04885100c11c4d08d91782444304716226a45e09110d09e47c8bc12221c030cbc1300cc5942711f22f04c88700e09e47c8bc13221c030cb077824c2389a11f22f0488661962cb04982713424245e09110c0b04d0909178244430cb16b82443a48d71722b81b81e00c27246c8ae07e07803807196e4646c8ae06e07803c8d914e1f81f00700c32c5bc8d915c0f803807196e4646c8ae06e078038b191b22b81f81e00e01dc8c8d71722b81b81a00f23645387e07e06801807196e4646c8ae06e07803c8d914e1f81f81e00e01c1dc8d915e0780380608ee2a4418b591722381f00700c2c857c8be132238038071970a248b8f908e0a80384485109a48b8f909400c04028917223c1203b851099c6c8b911400c0404716a0a244782508923645f80e00e01823c8d71462da46c8be13c01c0348d917c25c4700700c11246c8bf01c01c0304791ae28e46c8be12e2380380608923645f80e00e01823c8d714723645f0970dc01c0348d917c25c4700700c11e46b8a391b22f84b86e00e0182248d917e0380380685109a46c8b711400c0384485109a46c8ba00601c1448d916611c1448d391b22f84b88e00e0182248d917e0380380608f23484b48d917c27803806850e4646e03300a32e1439191b80dc0b42891ae1f01f81300c0a246f81345b0a246e03300a0a246f813000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c269e128f0913846fc2256103f07d583bac1c560d6b065582efc16560a1304a98219c0ef6071303558185c0a56046b01bf80a4c034e00baffe77fc3bfc9dfd8efe677f19bf74dfae6fd297e64bf0f5f7bafb7d7d8ebeaf5f512fa297ce4be655f296f9177c71be20df046f7c37bbcbdcbdedf6f6dd7b5fbd9d5ec56f5cb7acbbd535e9daf4a37a37bd0ede7e2f3917998bcb9de50ef22778e3bc64de292f0ff785abc155e016efab77a5bbc5ddd6eee837706bb65ddac6ed2f767dbb26dd876ebdb75bdbac6dd5a2ea877513ba71dd2fae9077469ba1cdd026e7b373a9b9b75ccfae63372f4b9625caaae5217255b912dc7d6e38b71a0b8c35c5b2e2a57143b88f5c362e17d706db81edc08edffd6fe4b7e55be96deeb6f50b7a0dbc9eddc36ea6b73b5b99edc9b6e12b6e0db672db
      else
        if i < 21 then
          if i < 20 then
            0x80491b82601b80412b237049c8dc1200cc65e09208e2bc85be8dc13601c028cbc12411346e09b00e01746e0950d212c0380651b82501d80488e64646e0990f21842b84732323704c8790cd11e46e0910f219c0348dc1221842a44791b82643886700c2c846e09313123704885408e26246e0990f219c0384712723446e0910e219c5bc8d91582643a8b791b82443885584c27646e0990d605c038b791b82443085584c27246e0990f605c038cb08e278c658b7c12632c5be09316e09c47c8dc12a32c4f609388e2784e48dc12e21c0384772323704c8890ce05c58b91c12723704b8810ae0440b0b1058e20c58c8dc12e2043085688e27246e09700a2c44c48dc12e2042b04716f23704c86700c11c4d89391b825c430b704f23704882516a2c445e0940822be1439191ae1dc36038050e464698cb0820a246b8870f80dc1439171f2150208af051235c4603702e10458c28716e21c360371960a246b87415e0a246b8870ee0586582891ae21065841051235c4387c06e06065828710632c1438131961041448d710e1f01b8cb058248c58828723235065841850e21c3b86c06e1041439191a82c41410cb050511c4f09d91b825c0304791b82644487702d11c4ec8dc12e01458027213025a46e0910aa11c5bc8dc1321dc0304712623e46e09516e0b246e09104a11c4f48dc1220945b0b005982521389e12323704c87700e32c23942792323704887700c09e48c8dc1321dc0309591b82443085508e0ee46984712623e46e0910cc32c4f609304e2784848dc12a0b04f09091b8254658b5c1221d345e0951120ac0380616c63f0498b631f824c5b02831e62d8c7e09316c63f04984432263f04a044058644c7a09dd17826c0380531e23f45e09416c09c4d18b604e42d81390b604e42d81390b604e42d81389a308863d4598a408863d4598a4139a2f04d80700a26f45e09b00e01745e0950f21ac03806197824c400341962dc1618cb05061cc65844c12632c1610cb04e432c1390cb16e09cc65827219609c865827219609cb45e09511216c0380619782485968bc13601c02896d17826c0380591782601b80431f22f04c03405863e45884491782601b8040882ca45e09416522f04c03700a11245e09316c2470498b184f22f04b8251642c613c8bc12e01813c8d91782643b80616c26a45e09108a2c61389a917825c0304416c2c845e09516c2c016609484e27645e0990b609c038b291782444084516522e45609910a09e45e0991121e42d82701032c59609108832c59609316463c45e09408e2ca45e0910ca32c59609384f23645e09110e01a1398f11b22f04c88608863e45e09404f23645e09910e0182209a917824422c2713423645e09910e01c238b013522f04a8b204e24645e0950882c04648bc12221a1648d91782444380685823645e09
          else
            0xa8b61622c246f03e00e01c238b11612350238b116123645b88e00e2d85838a607c01423c8d71462d8588b0916e2b81f00708e2c45848d916e238038b6162c0f802047161235c420471622c246c8b711c01c220b0916e290238b120882c5c8c8b714b11e1448d300911e1448d30082d85842804d235c3d00708e2c04948d916e21c3d00816c2c41450040882c61402672322dc338cb05123645b8751960a246c8b710b0a21309d91b22dc4700701111e1409d91b22dc3f00701011e4698a91121d4238b091b22c44387e00e2d85818a607c014238b091b22dc4087e00e1105848b314811e4698a316c2c24598a70f00f80384716024a46c8b71021f80404716024a46c8b110e1f80404716042d85802c917c0f8030b6161235c3f03e00e01c238b091b22dc4387e00e2d858b03e0081105889671922dc43047161235c3a047161235c4204716123645b8870fc01c5b0b0607c010238b091b22dc4387e00e1105848b308e2c646b88408e2c085b0b0916e1f81f00700e6404868ac0682c0c8e090069a2944485c07601c030b0c1248b74548570360145a82d134611c4e10b505a268c2398f50c611c5898f110a1945bc8ac0700dc02c8a806e08c23c86291580e01b80416f826430864c1321801982782922b01a60950c218c238b0208e2c08238b0208e2c08238b0208e2c0823a8610c62df45603b00e0160a68a704a0ac02847d0c411345603b00e0154560340760101de8ac07601c028b791b22a43d81515f244c848a90ea2df04c8610c82c858c8b915222c0b80716f8264308610aa2c857c91915605c0304716e411c5bc8d90f21945b8b2c120264328b713522ac0881585a27a47c8ac06e0185860980660b647c8a91180dc0b0b285a23e45488c06e01c4f096c132184328b0c1300cc4c014c1262dc16c8f91580dc0304713424c47e0990cc2c858609316e0b304c86104a2d85802cc1282784ec8d91722b01f8170102c645c8a91180dc1781708f2364448790ca2c858c8b91522301f8170102c44d48b91522301f8170102df04c8610ce0544d60990c21842b81608f2364448790c2198238b113424f04c86616a2cb04c86102a11c5889e90c811c4f09a11b82643302c13c2684860990cc2c41389a12624645603f03064448e8dc1282c4c8e0931626470498b1050644c58991c1262c41619131626470498b10580a0c8a09dd1b826c03805133a3704d80700a2c85802832282c01419131600a0c898b0050644c5802832262c01419131600a0c898b105042c0160933139a3704d80700ba3704c86503601c0368dc12a1e43580700d23704c03700923704c0370082c41610b191b824e46e09806e01058e0921962cb0498841960a0c4184715e620c6582804c621058a8dc12611c5890cb058432c1410cb04e42de46e09806e01465847291b82601b
        else
          if i < 22 then
            0x4d23e45f00508e2c647888408e2c44948f916223c0700808e2d647982712f23e45c88e00e01c4e89591f22c4270060762c61448b408e25e4788f917c0182389291e23e45888e00e32c1610cb0762d458a68bd14a2301c82e01601c0409dd17a2b01f00b00e01cc788fd17a2b01f0061960ec5a98cb0882df4520cb088a28f45e8a51121701f00b00e02065e8ac07c0105968bd1580f80580700e2d85ac03e0082c645c8a806e0b8030b216322e45403e00e01c4e09a12d22e45084e00e2c44d48b91500f80380716a26a4598b616a2c780209d91722a42c03b05c01c040b213922e45084e00c2ca45c8a91160b8030cb1652284270051962ca45700408e2ca45c8a10dc01865c8a21962ca45700409f23645c8af05c01c0384931f22e45488e00c1104dc8b91422042700708863e45c8a10ca1105809a91722842382e0102bc4d48b91522201f00701011c5809a91722b8030b231e23245c8a111c01c2209a9172290220b011922e45088609f23e45c8ae00e01865c8a807c0105908f91722a44403e00e0204b48b9142204270060762c245c8a408e26847c8b91421b8038cb16522b80204713826a45c8a105c01c65c8a21960ec5ac8a10ea2d85882810e21380368dd16a2243e03e01601c04447d1b02544180588e0b346980416c2c858028315c0185b0b005062b8028b61600a0c5700516c2c01418a600a2d858028315c0145b0b005062b8028b61600a0c5084e00c1105828b31421161468dd16a1e43603e01601c04a4704fa34c020b61610a246b87e00e01c238b616123645887e00e2d858b03e00911c58c2891b22f80380708e2c246b87408f235c548790ca11c5b0b012f23645b87e0102d85838a607c0145b02891ac2505b0b005923781f0060882d858c8b714a11c5b0b091a811c5b0b091b22dc3f0070882c245b8a408f235c518b616122dc5387e07c01c238b616123645b87e00e2d858b03e00811c5848d70e811c5b0b091b22dc3f00716c2c1c5303e00a2da46b09316c2c246b87e07c01c038b6161235c3f03e00e01c238b091b22dc4387e00e2d858b03e00811058b91916e294238b091ae1d0238b091ae210238b091b22dc4387e00e2d85838a607c014238b091b22dc4387e00e1105848b714811e46b8a316c2c245b8a70fc0f8038b6161235c3f03e00e01c238b091b22dc4387e00e2d858b03e0081105b0b1916e294238b091ae1d0238b091ae210238b091b22dc4387e00e2d85838a607c014238b091b22dc4387e00e1105848b714811e46b8a316c2c245b8a70fc0f803c2884c27246c8b711c01c040471622c246c8b111c01c5b0b1607c010220b1850e4645b8a608e2c246b88408e2d646b8a408e2c45809791b22dc470080882c245b8a488e25c4b48d91722380380808e2c04948d916e22c3f00808e2c48220b516322c4
          else
            0x8a710e078038cb16209e46c8a711c01c6583b163229058827216a2c5c5c8ae07c018658b5723235c3f03a00ee4646c8a60740146582791b229c4387a00e32c13c8d914e21c0d00716a2c5c5c8ae0740186582791b229c4387703402065c8a60740106582791b229c4387a00e32c1d8b5914e1d465c27915c01058c2792323645781e00e0206582713d23645387703c02065827915c0106582791b229c4087e00e32c1d8b5914e1d4238af13824e46c8a10fc0206589e915c0106582713d23645387e00e32c1390cb0762d64508751962d5c8c8d70fc0f803b9191b22981f00519609e46c8a710e1f8038cb04f23645388703c01c5a8b115d22b81f00619609e46c8a710e1dc0f0081962d414700419722981f00419609e46c8a710e1f8038cb077229c3a0cb04e432c1d8b5914e1d62388ed1060122382cd1060121468bd10a0b80580700e91c5aa8031960a04ef0041962d41470041962d41470041962d41470041962d41470041962d41430041962d41470041962d414700448fa2242a80300a8a345e8890bc02c0380716463e45c88109c018238b231d221023c8890f21a42d82608e2c84e48b911c01a2389712d24643b8690960b80380a1962ca44084e00a32d84c8831962ca4470040882d459491702a11c590af1392214238b215e27245c88e00e11c5a89a31962d645b87e07c0185948b910c0f8028cb089220c238b215e2724428471642bc4e48b911c01c658b5164c0f80283b16a2ca48b81516a2ca4588b911c018658b213ac0cc1700608e2c84e488416a2ca4588b911c018658b5607c010658b2911c010658b2910c0cc17006196c264418cb16522380242884e63c46c8b911c01c2242892263c44284791b22243209d12f24642084e00c2744d48b9102138030b231f22c45488103c01c2209a922c250220b0922230442c47851220c02447851220c02447851220c0202871f22e4450051961105ac28922e3d85702813b22e4438261960a245c88110a32c14488a00811c4e897917221c2b82a01032c1409da0082d81438f91722146583b16b0a24438768590a046c8b910e0b80384716a42c84e4919082138030b591621201f00513826a45c88109c01a1642813423645c88e00e0205a8b291622e44382e00e11c4d09211b22e44088e0102d44d48b31962d645887e00a32e14488e0082ca1442711f22e44700701011e47c8890c809c4bc8f9172238038071642744ac9190821380389712b24444484109c01c1dc289226344428cb16522380204713425e45c8811020b80404713424847c8b9102238040cb050c264420cb0762d644087548fa3e4318041960a04ef0041960ecc568741960ecc568741960ec5b98ad0ea32c1d8b1314832c1d98ad0e832c1d98ad0e832c1398a50fc01423c8f31522242a84491f22cc54099112178040b1
    else
      if i < 27 then
        if i < 25 then
          if i < 24 then
            0x380608e112441c4785107244707e0ae09c23828139221c3b85704c0a02384405122102383b05122102381c91022102383b910711e44408104e014238b213922102209a9234250238b103826a44088608e0ec4d488408e0964788740a411c1f48f408e0ee47984716209647888508e0ee47984704e070c238b204e611c2248630e21482381a408e0ee431c4784e209c020471642c00e486508e2c84e486408826a45c8a408e0ec4d486408e0cc5848d70ea11c2248d308e2d858c8d60ca11c198b091ae1d6238b686123783b80608e2c246b0870ea11c2248d308e2c646b8860ca11c5848d610e1d42384491a611c58c8d710c1942384491a611c588b091ac214238b191ae21832847089234e238448612378428471600a246b0870ec11c2202891a811c5881691ae214238b091ac21c3a847089234c238b102d235c42c4786225a46f08700c11c198b091a21d42384491a611c5881691a22145ac9191b00d8028b516124601f00513924646885109c0185849161262d45849111621f80302792323584c87513a25648c8d10bc0185b09792323442f0061962da14700419609c4949191a2238038cb05824a48c8d111c01c65b09910632c1d8b591021d746e8a90f80d40f00b00e020658b5323235c3c03e00e64646c8a60620780302d32323645487e07c01c6582713923645087e00e32c1389c13123645387703c0245a8281272350658b591a21f81f00619609c4e48d914e078038b5162e2e45703e00c32e45303e00832c1389c91b229c3f0071960ec5ac8a70ea2bc13c8d914e1dc0f00719609c4e48d914e1f8038b51620a38020cb04e27246c8a70ee078040cb16a0a38020b5051234c658b591ae1f81f0061962d5c8c8d70fc0f803b9191b22981f00519609e46c8a710e1f8038cb04f23645388703c01c5a8b171722b81f00619609e46c8a710e1dc0f00819722981f00419609e46c8a710e1f8038cb0762d645387516e64646c8a10bc0185b8b191b2284570060892364548870fc0ec0f00701232c4f48a109c0145b8b005923645700619609c86589e915c0105b8b516323781f00616e2c45702791b22b8038b51622ba45703e00c2de46c8a607c0145b8b115c09e46c8ae00e32c1d8b716b229c3b0b716123645387e00e01c658b50506078028b716123645387e00e01c65c8a70ec0f8028cb13d22b8020cb16e0a245181e00c32c1390cb13d22b8020cb84ee4646c8a910e078040cb16209c4f48d915c01c6582791b229c4381e00e2d458b8b91500f8030cb16209c4c48d914e2380404716024e46c8a71161f8040b716123645381e00201c5882712662d45888b915c0f8030cb16a2c5c8c8de07c01dc8c8d914c0f8028cb16209e46c8a710e078040cb914c0f8020cb0762d458c8a51962c413c8d914e238038b51620a1c8f00519609e46c
          else
            0x2076225a42e03307625884b6032702225b019096c064254446033126245c09895c0640ef019099126e04c22095212b80c81de03205a254499895c06411044a886c0662ba42e03307721481dc85215d80c81d883b113560885918f2c06a0484e884c066110422089a31e4268425823c06a0484e084c06626c4d382313b80c84b6032134618c1189a109608c4d884b04661b019187c06463c4426032134211c11e03110980c822084411346348c2e032c06a04842603207620ec44d18d2134212c1189a31a4617019187c0642c8c690afc064268423823d08e08b01a82216221301983b10762268c69186c06421301909a108e08c57e032c06225842603307620ec442603216463c8220e031c0680c9c108441c06380c70188b2704463c4216031c0680c8c3e032c06e049c10e031c06e08848382291621f01989a11ee0a40a0b613380cc5b48bc06626c4d38290282db01c81313380c85b086c07205245885c06632c4d382316380dc1481416e267019896c07204c5b8aec0680d05b0aec06722dc1381316d22f0198b691780cc5b48bc0662bc445823164274c7989c135608c4d08640760905789a31e62bc43582315e26842d82413425ac1184411180cc2209a31e611242109cc06411301909b134e08c22484208821b019844c0640ec44d08d704611242382312d80c81da0320880ec82238127042110422382211180c84d382213b80c822028213423dc11844111061a421b82104421cc34843c0620ec44d08d70462c701b8230760a0842c84c0660ecc3160370240a30193821c06380c701882810980cc42603212a22301989a12ae08412095c0640ef01909a11ee08c22095212b80c81de032134255c11895c06411044a886c0660ee4210af90980cc1dc84215d80c857e032076211c5881692323684888707724646d09419609c0e48d70eb0be13c1c91bc1dc0b0af04e27246b87702c05c6582713923583a83b91b228c65827039235c3ac4b84e27246f07700d0be13c8de11c1dc0b0cb04f23584387515e09e46b8870ee0580b8cb04f235c430750772364518b716209e46a0cb04e24e46b0870ec32c1389e91ac1d41d89391b22905b8b104f2352178ae84e07a46f07700e32c1502791ae21618c2f84f2378438161962c413c8d610a2c45782791ae21c0b0170772364518cb05409e46b8858962c613c8de10e01a17c2791bc2383b81619609e46b0870ea2bc13c8d710e1dc0b01719609e46b8860ea0ee46c8a307609e469c2f84f23784707702c32c13c8d610e1d45782791ae21c3b81602e32c13c8d710c1d41dc8d91460ee13f11e1f235617c2791bc2383b81102e32c1381c12723443b0b716209e46a0cb05409c4f48d507624e46c8a408e2c84e488408826a48b09408e2c857c88110c1981d89a922c250238b213922122383215f07244
        else
          if i < 26 then
            0x9260060984b092312d213801896909c00c4b700212dc009848a86c06421b01903b112663484f191212621ac0989310d604c57093b026260c59184c065a19c0960350242d8436033138269c1184410762268c218233162268c6909a10d608c0a0af10d608c4998b213c62c849886b02624c43581330f80c8c7889310ce04c220e03108821881d8984c064e0844c38127022e085c08e031c062e0844c3812c06e08814603210c61301998b10c4219c1104490c580dc09028c064e085c08e031c06380c414014c066050436033c062260c5909a31a4050431086c06604c4d086704624c43381313780cb01883b10c40a3019096c064110701889ab0242784ed81312623ec09887b02427ac0909311b604c5889370560501409310b605042d8130262bc4998b308824cc5989812a62cc49d81212760484b088c0662684b382104824c48b813126241c09896c0640a043e03313423dc11896126e04c4b087c06625a436033702204858486c06625b01b8130760a084d096704624c45b81312d80c81d889690d80cc1d896212d80c9c088b0c06425b01908830980cc4d3822126244c5989312062cc4ee0320880a084d08f70460b44c8937028110701883b1134235c118ae12662cc58e0370460ec14103b308462c4448637042088224862077218c21e0370240a30193821702380c7018e031050613019886c06580c44e885c066273019044112664484f1912126216c09899127604f01889c10b80cc140962050258849991213c644849885b02624ec09186c06461f019085c06424cc4085702980c442e03205021481409310a60a0429085c064e04442e03210ae04b0188b2c0680cdc08885c06461f01948dc06e08dc13812c06e08a46e037046260c59603b025a15c0960350242d842e03316580c81d883b1b022278c5909310b604c4c18b2088a148c3e03215d80c8498857026110701884410a40ec41d88983164217019186c0642bb01909310ae04c42e032c06221701960310502148140852c062e047018e034064261c09095c06580c701a032130e04b018e03130980c8c5885208921480a0852c06e04857e032c0622c701908790b80cc4c893322621c42e03331021a429893702580c443603231021b01999190a210c4988b702611301903b1c0620ec41d9882702380c4c46032c06262042e033c06e04842e03210b80c84f09d32262b843d81313c270c898ae127604c49886b0262b843581315c0b44c18ae131604c58b88110624dc88913111217019b8110242c70190b2c0680cc58893702621a42e03316221b0198b1c06e04c59603212622dc0984490a42c701903b10762c4858e03270222c70190b1c064258446033126245c09896c0640a043e03312c24dc0989610f80cc4b485c066e0440908790b80cc4b60370260ec141093116e04c4b603
          else
            0x1e004e078010b1e0042704af00312a24f801895e00425449b81103c01458895e0062ba42f003077214857700207622c849182200826849084a0080b049500313425d801804050212c1189b135c00c4bb0030062c8c170031342138018440505c0044270021342484250041242128018281384268c2f00313460b801985e0042c8c17003134213801e84e0042c9819282e0042c8427003134248c1100412461480189230a400c4d092109401057892a00610449500313460b801897600600c4d084e0062bf801092108c00c1d8282e0022584270031640a38018b215ec00c590afe0062bc4d300315e2738018af134c00c5789ae00624847300304c226c4d700308921084908a6006274437003134237801844908e08c4e892600625b80103b60640ec4e904416122110422382204c24a801844850098c13092a0060984918ea0080ec49103b850098c4d08fe0061104e109a11cc00c1309c1246e0841700313921380189a11bc00c4e382e0060ec44e09260062724270030762709c17002139c0084e700213423f80184412a424847300312a24980189a12bc00c4af00212422980189510dc00c57c84e00609841dc84215fc00984883b104821181983b1e00221380103b12440ec4491852006248c3084a00810449500330dc0084bb003006213801092108c00c1d8f00112c21380183b104c24a80183b12440ee140263e0020ec42089230cc010c3085909c0101d98626123c0040a186e006c0c442700212a223801895124c00c4af002164c0f801892114c00c4a886e0060ee421026107721081d8b091076213c4e1084b04426b8010b2305c00c220f00113a21380189a30fc00c4d084e006268c1700312ec0cb800884e0040ec44d084e006268c1700330fc00859182e00626f80109a109c00f4270020762a0b8010b1109c00c1d889c705c00c43c84e00626847f00308827084e484e00626846f003138e0b8018b7051c00c1d89c2705c0084e7002139c0084d888e0062c84df00313626b801844111c00c2209ae006112421044e0040ec45789ae0061124238230880ec82208441088e0884a888e0062684a882e00825780109a11fc00c220952077210857c84e0060ec457f00209e2d88222032e00227442603e0082d414500305061c801828109400c16028a0060a1801803050211819f00113821301f00405025b801986c07c00c14300300661f01f00310980f8018440505c00442603e00611014102830c400c14084a0060a042500305025885b484e0061105b1026116c2498018b6909c00c5b700208822d849300316c25b8018b6e004c2445b700216c2c780184490842c449300304c22c78010b2607c00c2248421622498018b112dc00c220b09108822da14026304c24a801826125400c2242804c62d84b700312dc00822303208825884b0
      else
        if i < 29 then
          if i < 28 then
            0x5814121018433414028220c4d014e00611042209a207620ec4d103b70441a42783d323a3402306907a8b48ee8d008d91c590b00600a08e98870ca1805b82823ba3706be470862c01802823a621c3286016e0a08ee8dc1ae183238b00600a08e98870ca1805b82823ba3706b86c0ca0a346988c08c19429843051c3d46a8b10901c434861051a2c0230790d819414004509e2112019036108900c8220282051600814026e0060a013700304c0588274470822db87b8f70cf11c220368602c08ec8d719013a23847163c3e46b0650a62c387c8b606c0cc0a1044116c098819884e88e2d858827e1ec18465c470890d85b03091ae0262384706d0c05848d60ee13a23847163c3e46b0650a62c387c8b606c13a2384116dc3dc7b86709d11c23c31160e21c3bc4708f0c05831d91ac21c2744708f0c458c8d60ca14e188b0916c0d8388cb88e1101848de10e21c0484e88e11c5870f710e1de238478602c18ec8d610e13a23847163c3e46b0650a62c387c8b606c1c465c470880c246f08710e024328b00610b416f08711c1dc3c8758962c016c8d611c19c3a83005b23446c0b616205082238020eb12c6582491ac2383387509c1245bc2f70dc0dc3004e88e11e188b191ae1e0328b0060c0d4328448622c018711723c0e03ac4b1972358470670cc0e03a8cb06123605b03609d11c208b6e1ee3dc33c4708f0c05842863b23584406009d11c238b1e1f235c32853161c3e45b0360e232e238440612378438870122580a1044104c05882744708e10c58f0f91ae1d46583091b02c01b016700419458030059c4448f07e07013a23847161c3dc4387788e11e180b063b23584384e88e11c58f0f91ac194298b0e1f22d81b07188e11c0b48d11bc21c440650882c018711723c1f81c04e88e1045b70f71ee19e238448602c18ec8d718c2202744708e2c787c8d60ca14c5870f91640d8388cb88e1101848de10e21c048650882c018711723c1e81c02412c40ec780084410bc00c49085a00609849500312ec00c01885e00424842b0030763c00442f00216a24a80183b16b0a0c4b700204c24980189690bc00c1d896212dc0084a887e00625449300312bc0084908a600625443700307721481db80207721481d8b091076213c4e108560680cf80089d10b80f80209330f80f80209ec0660780209310b80f802085407604c4c893c07c0105882c213180cc0f004d0b80f8018b760680cd40f00216e21701f00413d80cc0f00412621701f00413180cc0f00430f80f8018aec07c00c49885c07c0101da032e00211042f00313921780189c127c00c5889ce00627242b81e00827049f003139c0081d89c2703c0084e7002138e078018ae13dc00c588aee0062b84c70031622738018b1127c00c58c85e0062c5c0f003162e078018ae127c00c58c85e0060ec5890b
          else
            0xc1d882712a24cc1d886a06a09f8788f102c190230ae03c24f87b0750d426d87c06a0800dc3505384f055c8f0f91ac0e02a05289632e1382791ae1a8258af84e09d8cc8de10e21c0d0521650b99602412ae4781c06a06a09f87b8f702c190230aee1fc2181b06a86a09c0ab0f710e09c3505384e08849b91e1f2378248540a512c65c2704f235c3642704424e46b0160d212613b9160e21c43386a06a09f87b8f702c1902c822126c2d435057044c1d8228692600a34880450f21b032828008a1e03483226281104d102813440f8020441344110141028b0040a01309ae0080a013700304c07081dc032076268857c03e0060a01370030e01801789a02843d82d84b08e0d45909ce0ee16c25c351640c8c6884708826885789a61260ec4d10700b62bc4d01ae0600e8140750a512c658b2606c194270cb0890be1689ce0f01d45903205dc1981b07509c32e2383b1640be4470790e01801789a606a16c2584706a2c84e70770e019465b0660660982d84b86a2c8190af60e016c5782f13406b81b03883b00dc018750a512c422075097c18422044134427584903b10ea1c04d003604a1d43830f606816c25c3571bc1d81b0750960b783386704d07201b8030ea14a258b2108a18027447135c3e44088713826b801844104c07081d885b09611c1a8b2139c1dc3a85289632c01a81c61241942944b09227048887782b00dc018750962cb8308450c013a23f0f10a21181d89a207620984a905b0970d45903215ec1d425814121c184330780e413a2383b135c3e44404413442680a700308830500a086307626881db822076213c44e81d40661c83084f0742d8023052c8e2c8c4186e0b80dc328b7d1f83c84705c06e14b23a8fe1a620c360370ca2df47e0f211c1701b852c8e4c34798830d80dc328b7d1f83c84705c06e1942c89dd1f81101b06516e0900ea8fe1ac1942c824d1e01143905f0768b5012580204c09481dc03204dc0081298680661c62383e0762cb84380704c09481d8825612419424c31e2224443d0670a511c1dc8fe04a0ec44ab0920a511c2383191e23c43383e0762ca1609ee20233840829828050441814e00405043700307620ec43d06909e0eb4580460e016d2380440e21a426e8b008a13c422403203821104d1044135c00c22084413440ee01903b80640ec4d109be00507201b80309d11c1dc27135c3c43381c02842704d700308820ec40e085288e2d458c3005ac16c1a8b285c2238388670b62c81870ce11c1c43389b135c00c2209a207626882d8351650b813f07102e1c02d89b13406801d027a0f00dc018750a512c4338250ea12e03086704a1100a104413440ec43a85289632c1228750e026801b02582b00dc0186009d11c1dc27e1ec0ec41d89a2076213a2384708626b8788f90c21a42d8320602bc4d70ce10e1d42
        else
          if i < 30 then
            0x7641c027c1b60681e8380b280681c03709a806816c2b85208881802b85280681c42d844309e0ee0a984907626a0aa05209c10c1da0710860ecc2183813b81081a84e42840f61409c02881c432843050813821c2830c81802702830e810c1c42802981142183d85040d02203323a613a0a01430c217c218b640880cc82704d20c013822431828a1942b84486281305b41612c81382204312c813a0a01430e211082702320e208c816081d407600c3a92c059a47468056049c0083385416407548f0b006e1e032030d1a80ee019016a12a00c1dc03207700c85ac03e0061a81af0f1108059848033076205984906786c0b44e70f11ec1aa1a81561e215435035e1e21501d889561241d43543013600d43503e06a0b387888104e08843d033045c0081d883b104407482081620f61a826a27233a3402b8b205c4b01601c50c80dc9b68d40d419029043221a35a01903e0060ee01901c112700c81f00407624e01989310b00f80202c107700c842c03e00624c42c03e0080c441dc03215d00f80182d127c00c1dc0320d414e13822323c3e46f04884f071c018540a512c65c2704f235c3503504fc3dc7b81604e07081389c126e0440a82713840ec40e08528962d45882d84ec1a8258af84e09e0e09c633235c0d06d68e11a0e707606c1aa1a827138c3d8238270d414c57c2704fc3e46b87e0921502944b19709c13c8d70a81385932c051c2e43386a06a09f87b8f702c14a2583b16b09dc7b8170d414e17c2772323783b0380a814a258cb84e09e46b86a0962be138276332378438870341a81ac3116209dc0b06d68e11b84707606c1aa1a83104e235c4304716f0be1402232244783b8520961245bc2810cc1902301e127c3cc5884715d04c4998ae127c00c1d89320a614858c2f84e09c4c386a0962ba1381e127c1dc2a05289632e1382713d2360290b285c2b99609ce06c0e0350b706e0d787b0360d50d413b0f710c11c138530a42c617c2704e261c3504b05109c4f31d91a60602904b0922de1408660d509d87c8de10c0d83204615c07849f0f60d412c5742703c24f83bc3184ee00c3a8528960edc848d10ce1d42583b1372360338170ea1a818824836c11c138b104e42c449f00305409c81d88750a512c6582491ac1d42584913101843302a10ea2c815427e1600d83c06a85f09d88c8d606e1a81ac3116209dc0b06408d0c5c5f08606c1d42944b19609246b0750a82ca17028038e464340750962bc1248d80ce05c3a86a06306c4db04606e1d45902a84fc2d81b06a0a709dc8f0f91bc1181c0540a512c65c2704f235c3504b15f09c13b1991bc21c4381a1960c496428139c2f8438760721a81a827e1ee3dc0b06408dc3dc5f08606c1aa1a82761ee2182382784f055c0186a06a09f87b8f702c19023022e1e62f84306a86a09c0ab0f710e09
          else
            0xc01098198670a80f983a03e07640f811903b059054c2a05207c25601a85407c090c2684313a40d03005312661d02984313c60502182212781502d04322624c81a85284e088c3d84383827049b0360764d80e38140a84da0e09c606a1502909c608c0d42984d20a413481d81c70261a82942e13c07943542e82624d02a0521624b1c0a8548624b18588b50d509e0a895622a1502903b84f05543543b05d09c4aa83b16309e0aa0571648bc1420b205f80cc1202f050268c1203e42840ea1409602881e43806016481c03706530e00ec1789a40ae10e0e89b21f00d82b83b83a26902b84307707503804361ec0d037049606e0902904420aa1244d30d40ca1801f382407c0ec837023704614811903e04641801d82f61e81e42d93012a81802903e076817c1d82430ca0fb01983b03a485050a083a02980ccc3604c0660e00a604c0680f90a1067074050c328610a413d03285f0aa60f81d903e046413c1dc1530a40ee0ac03407c2c812303407c0904a985716581301a04d13a05301a09ac0980cc1204e42840e80a60330860bcc1186009c61cc5902fc06609038043074616c1d0b1c0682700e414606814822107a0e026981a04e07640ee0e09a61a235427043076271c1284d038414822104e0
def andLevel11 : Packing := (2498, 4, 7, 0, 0, 17, 0, andData11)
def andHash11 (i : Nat) : Nat :=
  if i < 5 then
    if i < 2 then
      if i < 1 then
        0x4b00600401703c00345600501b0145aa00500000000b00000100e03b06d002005bce0002e105a01805eb317f300969e3600020190120590fd06200302e02f00002a037a4f03900101302900800e00502708e0660020000000078ad00000067302c004008023b6500500b0e402f03400c00101500a00103b00003405700907700073c10e03a02701c00075258c00600001709c02102a07a0010010060005d000000104600600900a8df00200201700200800100000200904a01300000301200f0070020030740a200b02300200002a058a94bbc000003002000009bb382700502301302300001001200700000a00525934400c0c780e00002a00000200292903e00017a0056ab01087c00000000001100004574608e00d00270900000d00001900400872401624c00067400000000200000001100b0001d600500c00202d83400000001443b01400207a00900100008702f00400000505b00500000100402e00001f68b5d80010660171df00201301200300400001ac3a01602903c00c00e0c60000008690001da01700f0010010070648470010020024c500520f571008018000050000000004b8d6df0008de002016003bc480cbd8b9d00000501f0025c18bd000bbc53b0002c400001500000001370c00100000000900100c80e00e00206b00900029c00100701506043000f02400d0000010012b100d00102d0000000050000162bc000086000b1f00400401200077c00000201203902508500147700c02bba101502501d4f200000500e00100100800071400301f69e0020020021600050e5009bfc8da2ca00000000002000001600000004828f30500000001629b0070100006630010110070ee00000200005a00534301200305400c01128e00100000200201100904300c00503100002301700300a00101103a12e0010080d8019006022008480afb0039a500602c0000000000e417b07e00000200201900c75200b86957b01300100c00f5dd00b4ef02100000100000500000502200000d00001f0b400002d00000100002700900200400522ac3500501402700354300200700100002301f01e00600301100001100800201d04000e00b02c000ab600325000010300100600700700000100000000e006be701000001b00a00000400200e00f003004001001002405037008000004012c460144a700700a0020005a000f0000093b101100200076700000100000000300800300000700000003002600301e0010020130000000063ce00001200105121d01216a4bc7ed004794011024000086004004928043c4d00800400e00900002300000000a0200080000060055dfad500300903101700d4b700000000000000500100800700200b00000000000003403d7388cb00100f00000997b01f02800000001aa3900092a07600300100b000017005003
      else
        0x8b46004ca05deb0589a00d52037b80695c0936510392083c103a3d0973a001d802bdc0221f0731b0803d02fe615b42162e94001f05e2e078c90412b0845c0064a0225702a7e043c802c6ca068c037ee1931d067390031f07ce8049aa0137e0671005146055bb002cd37986039c108d25867f412633049ca065f1089660169a042a000aeba111005009074280870b05ca6068eb09ae211e89017be00200003aa98c2e00b7a092df0123e099da07e8e035d6087100915703ecc10b7f04f7701eec10bed185a908c9803f1f01131075a6091df01adf0800907cc807ad90355c0855f0385d004fa059ab02ca6064a107db51606001fa508d45029df062ef00b9b05e770250608e3102d520481a8318e128fe0460904cab0541c029f2099c703c7c0155d05dbd01bd9a112e1604533d1c077a407e2c011a800c0a0532d02d42084db0024a08e63010af006650521008a6c0575b06dc4045c9434dd07c93012f403e8c074e03059b092a303d33631d81654116db00878b0886e0670107940074a3049240922116ff4049902900109400502e04f47100301b00900e00800010900d00000005003800705500c0270049b400d1ad00302100700000000206600f08005397205800100005701b00304700002013701679900203102d0090e60ad13c0270220001d201d0000020231be06700202401400302303202200b38903100700c0270ef5c000900143d0b500f00000000e00000000500a03180a0a6000a35001090015001b1c04500000100002b00019200807e04d0025930001c02aa00200400200000f02204200704300b00ebfb13b0040047df00500d0f906f0580b500206b0da0050e017700400e00900003d77200200216008c00800a06900a00200100205d003050000002bc50000000040120005d400b00400400000110b00a00403f00b00301300707f00250b00200847e000057b6702e09100000509500102000042e36a04800400100607600485513d054000006549047000056087b3400e02b01300a01f0070020e401100703f0000170aa01801000c01901e00000f00000001700000100000244b00aa3400500002201600900704f8d0010000001010a6650f00000303d0000000030010511c000001d07101400cabf002bdfa830170094c487400101301a00803900600000000100400000001763200600205f00000602000400f0ca0015d801d0355ff0050029f80039f3000002000001ae300000000000000000700200002002208413500200a0013d900000032f02c00600801200d00300001204a01200a04501c02100a00e05e00400e00036c00c01100300203b35e09a75d01b00618800200200020902e01200200501417e00001b00800100013ec1003200c7b36c700700001601b00088a07001f006000005009b0e00480200a8e4098004a
    else
      if i < 3 then
        0x802f1b0444603c5b06d5d077e9910b408231099e60942200a7102b45063d2054bc08310030650288c0376c02fcd01d941658007beb0690908132142eb082c00177611ebe03e9d03d4f038dc01399015f20325010a7d07d8b05b5003ea30469706d1709a0d1651200bf77141d021ed0804101c69036fe02f6103007089bf05e8f010f9060cc0088904b4a06bb1152320006210d0309a7b0545d095f201ff605832111a40563507d0c06e98013330930605d1701e21018c6052cf05ff2069cd02a58018920384404a8150fd507552161a1036c3314db16746019d808fe70537407ec503bd40616806ea01612007e42080de015ec003d616fbb0124704de1040e910cfc05014087b703a0e09a360414a086a5037c403d80002220544a097a900db004fc403a690529f063f20397204bf74341e02c22798e1470a704dbc032c80998571407021f70462605b4c010d609c140937e082d3044c00314202d1505ef208b200452e02e9d074fe0455d02ab973a5805b2a030eba0f4703b84092f0095c398da5101cf05d8d126b603d74090d419bc40536217bfb05ad208fb707608098d4021c106892006ae86bce042800820d00f5905cc607359047ea047560319f027af0341304d5a07c040061f0905508fda06e3f048c0058d400c3a1603c075f7018db0766c0780900eee0828a006fe06ab462ed108be708a9c4116c00de7050d7a0e1a1861a04b671622d02c0102df207ab5197d107830024be0507d088df697d4007140379e028ef0599900dcb0207004c70036d5088ae0322f0779d040ce0752606fe30405c0976801acb037ad00e5500cfd0971b06eec96bcd018f900d3a05195013800401701c926432907ee70741e03404083720578aa31b2035440830a933110809503aab06d9d07bd3047b006923059510000f020a608b0c005130377d01355077460614e00359193f3045bb09bef00abb82f5701f41001c993dbb15ea607ddc8331f04741035f105bb00560f08b920418702daf05a32014d8058a610cbd712da0586801c7308876532f304d180940303568067e1a328000491050a60821a08f58a4122617d50329716a3200430056a401d7f011d71431b019c9817fa01b1316115049379192201f3908c19314cd7753c07c5f007f715317086590175807f2401db316fa10876f04a1f0606f02a9fa17c302e760089f0745008b3a0187301d5d066260510b00596018330463403239009171499c08e7507507378a00504507bc803fa50056d0980d615f9028d007a4a09543009c602e0a07df00338b03add080f247058061700152140c681620604ea5067fa01c1005d95b06eba802808ffa05777166f009aa5041e90284508511005d504f42059ce787e1707650318801fd907c270365707007024ec000a9162fc869db06ff11268706214045ad1600f
      else
        if i < 4 then
          0xe0406b06cbd03e4110aa402909126d5063e80952703f6a534840191b052ef00bbe03cd304a56036a50672f06bcc05a464128d903f7030b4668a807a8615d520592400115072f907ed802d8e1653402b7f069dd08cd207acd0030b00ebc095e50710b098a8a183a08198028a702d7e6869850f9c15cf61862705f8405d32025840642209a2c0945a0639306f51083df043b2073f1472fa05316063810993c0080d007d2020490906262e470508a08f8504e880810e08e9b0286104b01004d4008be05e6704c5a090b1017e88101a06ada036e6910100723705ee9004451672211f310154902919005b309ad4181f803fe737c30083e70223f033e31944a03fdd046aa0294201e8d0295d048b301bc7040d717118084900965f049521321c024a6031bd1621e06c830074d05f0f0121602a1f072d00036404f3a0534004ff6020f80416a67d58712955002109a9c093b9071b0033cf04b7411175033111269c03efc0882d064fc055710767f437c90100e07f1207362053070705b0229303bc40999502b9004be0075960734504ae30762ea7863097ff106d0045f802c3d0143005afb0635518667062cf0472b04c8204c9c093900838107a6e0232c03b7f10c1e012c809971003c205c9d01f8f089cc07148038c801e9a042fc02dee0513008c4691565163a70840a07d320387262c3180fe0012d90185f0785b0715212eaf90fe609329096370489202eff0145d99a6106fd980e8f0640e082ef023ff00b0c115f880eec02cb208357115da056c7036b701578010cb1935815a49a2ec10132308f710158b0007c1510909b2901a6a096f01274800c1b095b706c05055fc032d8081a808246a42580095b098bb079c6069f400f800453e73b2a06d2906aae05e410669702630094b1031d90641308a800336c0303f17c0204e1d05a691429c162a215d750112f0956a09ab103fc7079a8021bc12cfd13841000b4012550276b534e304cdf0097e01a0b08dbe06796910c806dfe080139782d10abe055ac05205043aa0634404b2004736072af102f90792207a38078d60880607ded0082103a7991589342b9015db80eac04b8e05fb10636c10a8d069a3100ba02ce0a2be305c160103b04f00053e502091a2e0001fc10060f04d260811405c43074c00863f053890659402b83021a5091bb0367382cae035b50559c0161b04c3d092cf0013606b6e0675e0834406dd98326302aff0523d067720571f04334029770426f04f80049d903dcf00e0e07217011e00582b07aa4165fa087dea174815fd193d5b1116e0988a026fe06a370037a07fa5094e30424a0666e066c5025e90404e9739f0817d096e707013067ce07fe5071ac03320051d233fde11f140923008e4d04baf08d5a00b1200c80027001319f027e3083fb0883304e6302b37057f9096c70016e09
        else
          0x63a077c4070fe0358e04108013ca0348207a1e04e5d05ba4092be00b860884f0364315a0c085c10776d07f6f03f7905c0a37c7c00122170aaa0edf0625f05c78056be06a2aa34cf04bcd039a3047c3934390126e072ce01986075764114d0588b02185083a7433858343319bfd0243e01a3b05e0e0957a08682053a6132200491f08998182080206908f6601a5702d65053900014301e5016f9d05f3e05e5000e170212f00b3f05e11000fc0722f051a8a327902ffd0390c062de06c7117c4d10a9f073c3033936119d065df055210511c069e640f8708ba2098c80360001f2808bfa07ba105731038290374a16527099f5315db11e600888d1260f0576f01caf01d1606a9603b0d0176d0555a071110046f0881309b35050ba008a20756f0234a11e900765d0890d669650092e01c531988c04a09097b20542906ba910e21014c601ef1014e70153770249051fc0969d003e501344094f507534914ff014ff0684e0372680e4e0955200cae1732101783016c602f57067420970703fb2076cd0021008144038fc0450205dc1016ef08ce1079bb0926f08a29b01ce08ec8027720681a06ced305290034d05cf201c8b0456100a3a056fa065230737c0833706edf00694a154000af70224006d8c0699809ba00554606a40039f908dd9014660430608cb000e600359a096240897d013b10228607b3515d690448700fed03cff078fd09bb7011c1056ea40fcb02e4f0454000c61000e2036940396608a011714d002a902f420860e058ea03301050c9060de05a9405fee340ab16e61a791b03b5505aca127f607a210771e9157806bfc08ac100236061100946e091ff03eb808734028be0311810ac4094d2028f40604108f1906a5e0388d08deb02c4c073d6075b40938607b2907d4811ddb05b30195c9029b2052420386604793021df02ec0044a4048350648904efd052bd04683019f308b6a00ef1161f00579d03ae200a6c017fd0335d00df908722067ba05404018690806306b920615108082065b708f0010a6b0744b08d02086e44122d04a2340f7d0408f08aec07d6201223006c6065ae17c13630c207ff704da10317002720071cd1650f0967d01b9308ad9685c501ab401f020136f031220688910bc0025c417c3aa304867bd705bc6095970788802cd700a8905b70032a80941503f3807693051ea06451017a006104077fc0164304d0007fd5070c10375804e7402d9601d2e16ab71288f0867302a07a3eb3089a1068770485402b540370d057e0042029104c059870432901ae481046035c80144633e7e027880104c56d2a087e1016b904a9c060340280601ebd0826f111b406a75017cc064bf1655e02f8f127b805672043f501c430285605a0809b940119b0738d06ccf08e0803bb5165d902ad660dce0052b061e0059d805f1c07f450195
  else
    if i < 7 then
      if i < 6 then
        0xaa04f5b06f76004b80693b432f50392f02224008c70916100f0a13255081d806552161d70008680f01020ba033d8912b804af8024f20847a09b59168480394a02355013f809a68029a603df7038ae015b201424070310256b1626c91073023d202ace979c362db7068370413f053f20162f07e7507cdd07d2e015924382902179088fd162d60564900fb1126100822a0220c08ed40526c09338079eb04bd907ebe0763609815025160654617029078a0094cc0718f04b9808af8023ae1360601da6473b1617a796d77078b3a0e27093a104a790629901052011b4108b7042b602c5107b5302e174745a173c200c2f16089060500623a091a903685042de07e9f9091e03240091c916021021450664300b59033ac412421673900bc5934ae067a80764206ef111eff10044438bf197f4003f9049e204848009b603b1405026412610471c022c70334902b1809943686da0231c02a4650fa70713405a2f08eed066db043e9060b80423804f2d110050551300ea607fbf0439d02897095df05cb707bbf08253534d0411860166c03d551619600f2e08d3402524002870457100bec02c75098f7151dd029e101e4d16fd307023001040627f0267608ea5060f4007eb0678411ea5070bf129000366f03e7b06e6f17171066190179703086072ee03d1f025f00073c03d2d02d2402f2e160ae034e10478307261105d6094a2000d701a2208898089300665e051540535202bc90110700d680910c98c9e0282507f8c01f7f02fa3a3cb711ded014b702cc40498d039330477d09031089fe0260e029800118407b71016010038f01df21536b0909b0307b03f8e411500853a0247804edf05c5b10a350732003738164de084e7012b506914007560313e0846c0242907958046c2055da041d603334166e9006bd08c3602a3c014a0a950661176071f30612f090290326f0141403c9b06b0509871092080754d06b7b0409c0482f03956062a206a0e06c3c00fdb086680528f0686e080e60773e013130712c023e6041c50708103ac6037db047a601bba0259d00b4b00cc2064ea1629308a79027f915e3e078690009b03e03075eb065e293c7904ac503b9506f2a05eae03a8807b620653408cf4015680584d066f207cad07f7a042ec0315201f620644705f6110d240517e009ff01dc201b2d048fb02ebf04c230273cb6ff00241482bbd17c794371e0266d099a5068c7a0f150630700d7130a609190703b4c0509204254611ee0966a111980958a06088153760986fb09fa0854901d4c05a7b03ce30446103a5309a5c011500908b0040c045e4159da052d4a7daa04c6b00edb774b4165c4088e715f828173e0778e67f8906f880607d053dd0079c08ab400bdc06cab073a3a4020027d103ed90812c012ab02e6c0083400a2605b1491328015a206eb0135d946c4f0
      else
        0x43b2200cd817c25016820440906a8f0697509acf073ec00cb40877b025b60620c010800421a181dc053c81607e127c080f3201ea9186ab00fc200f6a01d60085d7086150004706438093ef055ef081821705507f9f1666b05eb00173405d66038e80816408bd5a0ef05000b040fd06c5a02fbf06cda059b2057be08a430793a0943201b6a00fab01a8c020010140d15b3207cbc06ec212979060a50362505c3b015c807290024c90789305e9304472051690438608d79046181630302f0d07ef002fd90797c039e807874061f2016520053b031aa00785013a2086b7005ac07492097dc08b7504646164c11863a0048b02db910a260436404d9b913c9910ab82d2c084b60302a0506407e04022a802e8207f55601b812bc6033b001163080a207cfd161ee0470f04a699025a0283704e4b9793d09471033fd8683f08c6b101b004cfa01de15341d035720918e007b3185fe17c550844f09b7802e2006fa003c1f022e90407202bef135ba034bb315b008276093fba6ce8061be0975a081b3070dd0807100e780347f00ba008da008df806a6060dd1092570253f0488f051c517cc60546d126ac10b6c06e2d060e60163b030f205a19075d005434089de0572c01d0a0848d07b0404eee096111358c06604046be03e310990f07f3d03c390345c08d80087430637e6951400ac0412a71634607a9c03b3e027be00c51001980904e00d1b09c0e03db0a050404314160930346900a4c054a3439f883012008670983b00779069b108e260856907e520391001d3d0891806d6c0743b16675017210188b026da03d9c03cce10c2c06bed02e3f066ee016d21285f01ec300da80441100f7c0696b07c32a0dff01ce7019be152f508a1e43b3707b45a8194022660094907c6d0180b08c550709c0601b049fd08620088ce009a308ca6026c0a0e5f03e6c935300618d163720717c078e8040a890151039be4127308a3201701056d30434a04ab6040b40296702d0507d16940e90977e05bd804e9c08b8008bbb0490b0935800fff91389151110437480e0c097c30979b045d607a7004492915140852a087f8083bf12a6a06f0a14fd40099d11f20061c6005eb04dce04b56818260875a05dfd00274a15a30978f067d706e447080d04feb00e2004e2a0525705bfe058b000c7b0931305d4c06b1106e8e0184906db20350f005890429f0171a0953c5007d03f0704d3104581004e04188408ef8093d90843e0398fa3dffa0e9505d5e0950109bd606e0303992002e7034dc099b9017d9080c30292005f4808aad008f6066a206b3f02b201868c07d5203f2610c5130a25048dd08f3ca6cb905698a7fd0074ba0747b056620148c0667c1823607829090a60240106e7006947048a7034440265f05b990898501494057c3086cc194060057205abf702bf07c14044e0082
    else
      if i < 8 then
        0x33004ce512948070e906ae312ae501b3c01f1904113050ff039dd04f1d10cde06f6f03090161760587b08597029910466400a0b05fd604966032020995607258072b5009ec1059e018e20271e02a2c01fba01fe102277081fd02c1a0085909190972af050e200c95008e5a180a087a608d99315ec026260055608c871648f1320a06096030477724c001e4008750244c0562000e36026100730e07a0b00471025aa10b2c04fbc00b2e01a9417bde60d8b012870353f00f450321b050580748d08948034fb071e906311126ce0090b047660632c04869062b1181e01821408fa27131b0067806b2309b8703de102a8e0254d0593605e3e9376b0676a06d3f03f4403c6d079f8011750238110b090832403e1b037f310b8107b10046e403da5026e466fa904977022df035a200f16161c103c87315c10968205b0e13238068b201cb911f48084cc0600a06462150270657006c600901c05741059e7046fb09b0a08850081560054d163e0094420400c054d90181c082b70042104d8f02139019ec50fb7019ad0114d04fdc07d9c02f9005b6508d6009927093c816fc70928d001b50107a020370989609a131291e0065d06d7d0025c0070597c1e0062300b6300a18833a605d7a082ff01bec17bc4007af01ba203afc029cd04cb5032810836412845061d1032bd05858002b90111f054980001e09a4501e09023ce16572635cb06b4a063c600d89046510704f07274108a501af9052f7022f410402161b0166410602f054ec82ceb01b520553307249085b1065c5737460378c076b10658a94005098e60857405f700934615fc108c7a04c4f0337105c6293947002ff020d9198100728b9144409828086fa0790407586071d30912404c0360d9a8177400c460005606a1ba692f003980197e010eb0233e073bb16fe40202d02018058c606b8607b83038060167e1080c02a6d1707111f0717034193a305ec406de0053b401a1fa6828135c2076f209b1d00331412170895e0879e02dcb1938601a79062f1041f20706c0068c11e4f09493034a213a3804eb96024d05506076aa013e10216907e64077d306fb803433001fc00932142d70858f03c4507fce02d3a02bbb016a60150400a5da2cb20798110bf6031c40129208e5305b8108cc203d0801a450917007990085fd04d7a03a2d06338016f70246210aeb62f9ca7ecd054c6933ab095a3066b50381a072002054702798046d2129280215400ce90275a0651c035240192e8353610caf1351104df710d670951101c2a0018a0402905d05068aa04faf03caa0327604b190305906f3709117076d00199302f7b0249d0839d09072051b8032e508921026a510d40434ed02baa0527f091400591801cdc0781c00e86115ed075ca19be2068f006c9e09242341a215244098451264405da003c24043d300457
      else
        if i < 9 then
          0xd03612151e504f9a090e356c4009c250106f0239d0580407c7009c2a04a4207c85028140389e038b4034ce10bda08f9a04431a7f2040bd71287f084f909275044f36361b11dcf0522903eef125de0494c0841a092ee06c2604278088bd00e9002f350417a08e1803e5d0196f05c27a01688044300d0e00f97012e310cee01b0903f97076e31160710af3025d807af70127704dd0a110803ff900dda125fe03cb91530009c2106bda0268009c2b07e1501cce0568c006d10451107f08027c702aa403b2305be6070a212f6b001a80419503beb009d009c23024de01bf91262c0383d08429064d7077b009c2050f86097e99147c93a980656009c2009c2e07709013000211d1302309602020e901ed805d2902bf009c2303a9009c2f02dd900aa9160520442f05f240996208c2901cf41656902e5209b64026b806f18193d302ed0006e904c1304d4c028cb0342a1822009c2009c2f435a406fc793be401dda018a10518009c22044b7055c009c2705fa7091e0162c51675c0716009c2e08c0009c2a01b8d05c8c1601b01025048e502ead08a510174b00f3d059685004009c220733007ae717be3055681324009c2791490086df0594b80f2700323013d6611b808b1009c28063a009c2009c2b9389c06f4b008d802aed0208105ce80257009c2e011f009c250151407409084a009c2e04d6d67ef10626b03a1507dc009c2a1982505ed304ada0650805cd009c2203e2450fc80590009c2505ae70349009c220772508b5a82e9f074d009c2208d14165e509a8a06e5633d780269009c2105ddf030a009c2203711057de0301304e39918a203aba069850719009c23080b302b6c000280310709b4ca686600d2100a920777009c2893f181706a096bf023be05fc004456702ff058fa042cb030cf0205a713ad11e7b00e4009c26085a009c2009c210084a0287009c2009c2e09bc50921a01e3904e0009c2701c3a07ea50570009c2009c2c097451671f04cc20512307841832840685aa2d36087c008fc504f68097240182905f9806d0f08504076880076300506000c60415e04aa608bcc0237b02b07089e009c2f1631f02452063bc06248a6c00004180628c01e1c07bfa026400503b1937508296145820964a098540548ca109a06e1506ac910c71057a9096dc0647d052ad50f7f01f9b04b3f01aa30363c03bf4066880619105a5e04033005ce0029e03baf05619636b30210e0255304671914ee00d480435309292010b380de409af608ebf022baa81070422802c8706d4001f510248000ec10948f973f10098007d760597303d6a1273f06c4e01d85079d90805f0751e0558203518044dd1056807393096a50913b020cd938cc0680b0581a06c11018ba0026a099110081606da106cf207967a2f8f07e3e04a36085e8081e8080250746f05aaa059f705
        else
          0x9c24007cb9077c04bb009c270236b1942901e7801b490613216802086490230d0072009c2502196003b0066360109009c2c0682d00ad20775e941d7054f602ee009c21090fd03a4d061a59045001c090316604ecb10ad18311009c290274f0869009c2305a840101f737ec019015338009c2102cfc064c607da8713f0081ce031e203b61005f407b991279905f530293009c21041ad06f900459009bf009c2e076190791c01b7e08f211298f0096e12a7715ebf041b806afd08dcf8186f002dba2d1009c20166060003415e2009c2b1118a01e620547b032f009c2f0147701209a178e031fa047df0480009c290565009c2e03c0009c2b03ddb00d9910bbb0193009c2806b500707700176a82ce07c4c03f5009c2d047f50622b08e8009c20a7e0fa0f5b08f47090c70649009c2f02c9f04879068d3004a0035e907a550015d0194e030d7049b
def andIndex11 : Nat → Option (Nat × Nat) := lookupWord 1104 3155 12 20 12 4 andHash11
def andData12 (i : Nat) : Nat :=
  if i < 2 then
    if i < 1 then
      0xffe54032ffe44032bff62832bff5a832bff56832bff46832f7f81c81ffe5c081ffe54081ffe4c081ffe48081bff5e881bff56881bff4e881bff4a881ffe4c051ffe48051bff4e851bff4a851f7f81c31ffe60031ffe5c031ffe54031ffe48031bff62831bff5e831bff56831bff4a831ffe60021ffe54021ffe4c021bff62821bff56821bff4e821ffe50c82ffe80c82ffe54482ffe50482ffe4c482ffe80482ffe82032ffe61832ffe61432ffe59432ffe81432ffe60432ffe58432ffe54432ffe80432ffe5d481ffe81481ffe5d081ffe55081ffe5cc81ffe54c81ffe50c81ffe80c81ffe5c881ffe54881ffe14881ffe50881ffe4c881ffe0c881ffe80881ffe50c51ffe80c51ffe60851ffe20851ffe50851ffe4c851ffe0c851ffe80851ffe82031ffe61c31ffe61431ffe5d431ffe81431ffe60831ffe20831ffe5c831ffe54831ffe14831ffe80831ffe82021ffe61421ffe21421ffe81421ffe61021ffe55021ffe60c21ffe20c21ffe54c21ffe14c21ffe50c21ffe80c21ffe5d839ffe60839ffe20839ffe5c839ffe58839ffe80839ffe60439ffe20439ffe5c439ffe58439ffe54439ffe14439ffe48439ffe08439ffe80439ffe82029ffe61829ffe61429ffe21429ffe59429ffe81429ffe60c29ffe20c29ffe58c29ffe54c29ffe14c29ffe80c29ffe60429ffe20429ffe58429ffe54429ffe14429ffe4c429ffe0c429ffe80429ffe82019ffe61c19ffe61419ffe21419ffe5d419ffe81419ffe60c19ffe20c19ffe5cc19ffe54c19ffe14c19ffe80c19ffe60819ffe20819ffe5c819ffe54819ffe14819ffe4c819ffe0c819ffe80819bfe42882aff62832b7f5e832bbf5a832bdf56832bef52832bfd46832bfe42832b7f5e881bef52881bfe42881bfe42851bfe42831aff62821b7f5e821bbf5a821bdf56821bef52821bf74e821bfe42821fee81082bfe52882bfe4e882bfe46882fbe81832fde81432bfe62832bfe5a832bfe56832bfe46832f7e81c81fde81481fee81081ff680c81ffa80881bfe5e881bfe56881bfe52881bfe4e881bfe4a881fee81051ff680c51bfe52851bfe4e851bfe4a851efe82031f7e81c31fde81431ffa80831bfe62831bfe5e831bfe56831bfe4a831efe82021fde81421fee81021ff680c21bfe62821bfe56821bfe52821bfe4e821fbe81839ffa80839ff64c439ffc80439bfe5a839bfe4a839bfe46839efe82029fbe81829fde81429ff680c29ffa54829ffa48429ffc80429bfe62829bfe5a829bfe56829bfe4e829bfe46829efe82019f7e81c19fde81419ff680c19ffa80819ffc54419bfe62819bfe5e819bfe56819bfe4e819bfe4a819afe62832b7e5e832bbe5a832bde56832bee52832bfc46832b7e5e881bee52881afe62821b7e5e821bbe5a821bde56821bee52821bf64e821bee52829
    else
      0x407c0b88e469144410f01f05c0c32346c1244300a23b2346c12c0a85946c13c0b00a13d1b04f02c0296246c1201f02a6591b04806816d1b04b00823b2246c124390cc6596e1311b049104390cc0c9621611a45c124410dc0c08e4b11b0491043f02e6584e4891b0490ed45c12c4111c1300cc7b1b45c12c1104cc7d170490ec0284f45c13c1300ac6d170490ac0288e2231e45c12a5b04e469170490fc139965904e45c124410e42b05223888c791a45c124410d02391a45c124410ec370506584e4791704910c4691581f0380291a45607c0e00a4691581e0084691581f0380291a45607c0a00a4691581f038029178491180208e141224270480311a45e1380211a45e1380211a45e1380211a45e1380208e1411a45a00a4691784e0081411b01f029504a9df5360a6194a9292351caa2d9443a862505ca0253eaa7b04f029d5d39426f44d8a9a81336263d4c1c977d2d8257c4aae948d27ca4b148fa911120fa3f547788e211b1a34846328bbd16522aa44f6896d122a20c43a686910bfa150424c844107820da414281dd021a0193ffc7fa0fdf1f9e3ee87d50f951f193e067b3cf4b1e673c7a7874f039de73b7a7660eb71d4e3a3e73ace609c9238da70e4e0c9bef37806e58db11b47363a6be0d6c1ab3353a6a08d299a29343067b8ce9999f331265b8ca21929320863b8c5f989530fe617cc1a981a2fea5f18bcb976d2e9a5c8cb7c96e32d905a50b3f16592c545800af295c02b4a5628aad953b2a1853c4a6d94ac292c51c4a2d944a28404fec9e613bb27224e149b0134f26544c6497c92cf25684a3c93c924f245e48288fa11ca234a46508ba1145226844a088190f721a44318853108120ae40c880e10061fb83edc7d30f7c1eae3d047908efc1dcc3b547530e9a1cea399071f8e101bd637186d30d811ab834dc6890ced1986328c6468c7218a430c86090bf217a42ec85c90b7716b82cc85840ad9155429ec5238a1d13e627104cd097f12aa249847908c81164220c42f084d1050205c3f687c80f321da83a2871b0de21af434706690c7e18542ff85d00b5616182ba85460a4c141827804d5094c120422b843c084210181f583d007740e901c2035506560c1817302c6054c0a2c1380255047408540f301bc032405c80ab813c024c042c07800d5017e027c044807300ba011c01600160000fff81482fff14c82fff54482fff4c482fff61832fff61432fff59432fff81432fff60432fff58432fff54432fff5d481fff5cc81fff54c81fff80c81fff5c881fff54881fff4c881fff82051fff20c51fff80c51fff60851fff4c851fff82031fff61c31fff61431fff5d431fff60831fff5c831fff54831fff82021fff61421fff60c21fff20c21fff54c21fff80c21ffe4c082ffe44082bff4e882bff46882fbf81832ffe60032ffe58032
  else
    if i < 3 then
      0xac5d14c430f01b96013b2304a16013c12613926c7d14c430901b0302396104b10c390c42b88e5b96145310c390d01b032238504e184e4d3234530ec2c06c1408f43108e58514c430e43406e23b1f43188e58514c430e43406e2396014188e58310c3d0c4333234691ac54124430ec2432346c1242806a23d1a46c12c430ec339621632201a04c49d1a46c12c430cc0c16216316c430c42b08f4691b04b10c3b0ce58050c88068131274691b04b10c3b03023d1a46c12c430ec339601430e658050c5b10c390ac2396f4691b04b10c3b0cc0c9961331066588e423d1a46c12c430ec3399616108f4691b04b10c3b0ce6585046584cc430ec310ac5b31ac54124430e42388e4d51704b0ec330ac1408ec6d1704b10c3b0ce5b058c780680a31f45c12822058c7d1645b10c330b023b1b45c12c430ec3396c1380662393545c12c430ec2b05023b1b45c12c430ec3388813b1f45a19613d16c430e42308ec6d1704b10c3b0ce6582904b1086582904988e5951704b10c3b0cc2b05265858423b1b45c12c430ec3399613806665b1504b10c390a4238764891a452120410e029092258761383846e0fc0b8961d84e46e1183f02e258761391b8460ec258761884e46e11c0b8961d84e46e1183f02e258761391b8460fc0b8961d84e46e1183f02e238881d85e0e11183b88e220761403b86911c1408e2207644011c1308e1d91e03a08e2207613f04a238881b06046e0ec238881811b8460ec238881811b8460ec238881886046e10c238881885046e10c238881811b8460ec238881811b8460ed48d1ac521204a8504891a43908a5a850131224690f81e010658501392246e1243e01065b2346d1581c06c0903804d1b4530e43e0701f0380301216938c891a4510f81f038049965b828469144410f81b038051621691a4511181f03804196139224691443f0380431ec6d1784d1101b0441601222058c7d1784d118030102396b4470440296a1451744607c1600c04076c6d1784d1042c0780301223964578504890e42908c16014238504e922c791a426010238504470482396a1411a4591043f05804996238504791644600e23d1ec5185147d1784b0d80300e2385047988e1411e45b144410b804196238504791644600f45d14c411181c07c1600c04996c7d174560701b044160122205945d15c1600c0387745d1442c07c1600c0408e5b91a4591443f058041965905a459144410e42b0580508e2231e4691645111c160126588e4791645111803d1b45e12c411101e00c0408946d1643c07c0600c0408f46b1404a05146d1784b0c434078030125b0501311a4590f80388e588504691644600e2385046988e1412c46916c511043e01216b2345407c1302cc6d1442c07c0b00c23c1243704816d1501f04c0288e5b91a4511043c07c130325805a4791444
    else
      if i < 4 then
        0xc7d1ac3548e220865823b46c1ac62118340762748e239621461f46b8ca3016e180508ed1a81c0e265c8e220861805146e10c43016329601845a168518431183b0f46584e4ed2346a128338760a52346a12a1d86c180584b12246e1383c8761b1238791b84e0c01c09616c4f46e1183b02e6584f46a10c3806c5784e49d1ac430e01b0280c99613d1ac420e01b07613d1a01a0961d84e4e038c891b8390fc0903635196258885b84e46e104460ec0d8f01d8621392246e17847032258761391b8460fc0bc8f4441183e0d82c06c11052239384d510c3b0ac1205023889440068238504eb1b4420cc23877440068239645785e0e1118390e4310ac1588e220760ee1a4460dc1408e220764e0398691183f0441508e22076178384460fc1408e58d1ec420ca23877478068328a42387647e1a4420d0238761891f8460cd238618460f43406c11050239608430f43006c239344b310c3d0cc120502388943188e1dd0c01a08e220764e03986e0e4370441508e5905e13937841118390e42b0563c09622076139178420fc148881d85e1684f8460fc1408e5851a8430e01b08e2251a01a08e5885146b1083308e2216c1b06046e0e4340c0238881891b8460ce238881812c46e104460f05a85013d2346a12c5a96013d22c5b0e42e0780496f48d1a46a12c3b0d01b03805051489234691a84b0ec341965a85148d1ac390a81e012658765ad10c390a4239965ab2346910c390b81c0780504ec8d1b4540780319613d1b45310c3c0780415e1392746d14c4406c0e01258858c5d144531181e0106596e13d1b45310c3c06c0e0146585b4520780299613d1b45310c3c078041961d82945114c430ee0a31f45d1101e00c2252248b1ec510ec2b88e1431d44208e14138c6d10a238504e93545d10c2b0580488e14138c6d174430f80408e5a85066596a14516c390981e010658294440780288e5913945d10c3b0b01b058051962251042208e14138c7d10a238504e31b45d10c3e0106596a142078029961d96b4430e42908e2385147b1486584f47d16c531043e0780488e58d1f45b10c34078041961d93a42208e1451e47b10c3308e5885147d16c430d8041961d828c550ea658761631143b0c42b96c5ab1a4430e4260701e012239344b5174530f01b0580488e5851745310c3c07804028c7d1745407803088c8b1f45d144510ec2c08e5851745310c3c078041961d96a4221960a51501e00a239645851745310c3c06c16014658881451486587745114c430e42b96d4691ac5110c3e0701e0122396146d16c430f01e0105b1620a40780288e2216216516c430ce239601451ac3a88e5805146b10a239601451b45b10c3c0780496c58050c520780308e5805146d16c430f01e0122216014516c5288e1451ac5208e5805145b14c430f81e01213b2145406813b1
      else
        0x3a964160541152385e0d81c8ce2a1641103b48e1701c0ea350885805f46a0f832072368d42787c1a85183b0f03c0d429c4e1132387d1b8240742a0a52599621c4e13d1b01c8d42588657c4e13a3346e10c4406c0e164160551384f85b17843112368d41a84f84e0ec3c06c0c8c86588c1161f84406e368d432086188490e3108240743a8e00a21f45c0901b8b62588e1a8504ed1783b0ac150ea2949616850c6d16e3289c2245a1412387b1ac348b6658971a82984e0f01c0f03a8961d9658330d01b0523a8b62748e1d85187b1f4430342909f2396c1651f86b1ac348ca5b83a0a51f86c06e328a41dc5a123234791f86b0d4390a52387747c1ec3406c0c8e52387c1db2347c1f8440723009e2748e5a85b87b1ac3c8b72386a9915c13b0f01b0522d8a5238882196186b19434074380b72382887c0901b8b62748e1de1ec791543406c0d0b665c8e180298460f01c0fa2dc8e218765a964988618450d01b04c0f0c02789d238825b61e
def andLevel12 : Packing := (299, 3, 7, 0, 0, 15, 0, andData12)
def andHash12 (_ : Nat) : Nat :=
  0xc45320f64003581e1c051604ec063d80d0515a407ae019881f7c19a00e34086501db597d610750158019dc084005a7024f023c805ac0d8508818a680167012980050089c0256207ec031e8377c124408d6129302dc0256012b70350828b80f8e2a3b06ad04740256a2ede067c839b0528012b6079201840257c016f06a481cd808c012b0095c008180b0a0bf400580131802860b6300da08a3455d0001208db837ec1e6203d308010120c0cc00f760778b286c13a8104a06d503f745148273004f701a0c4dbe115304f9c2cf80c5c0607083502a281b9c00f7001c820e296e40fe601240461c12e809391474022745b12032b854b0346c19566d8502ab822b41dda8b8b070e80bbc11d88c080464036cc0a3411ac072580750058a086807cf0247d47282efc14dd041541a66082903a503e2064f20ecf06670284c01ac292f091181e6c1ae00d0f08b60a95408960ea108be8a4dc19c20a9e16d40aeb41002096b013402ab0210e0ac902f03103015a00a5b91d58ac6016860e7e0623017ec045406d7004382d64613e009204dc8a7159b8c087b087888b341f40011f0029826a256602983087101ec80b80119c01b9029f4193e0bc9021c08f4844d60a0da56782bb8020c0889001200c6c181e0a3f03b9049880002270107ad020780264065304a5804825a6c019c367e8152402f20fc9a6bc0255c0a6e0b9300f70aec81b240e8681d0803a4043a281205e9042941e32276808f30190400f52cdb01e58054403e00de1074d826001d7411ce02b182710606e04d4089f00eac21aa114e819c02eac039a04a9037783c2424a20e2f023f80a40073e1274088c809d410be035e057e84910572a10b407a602eec5b2e018513d3003180d3c2971089301c3c14840d2001f6aab4817ce0360763e00eec571a05bd062f83b580ae6004d081a8406c097804fe035c345840de20b8601c582c5c0ea00cb1015003214109207100182831940b3a041e022b01ff007e8121514cc0103003440c1a0178014b0117612a407da20e4c133c0b2605870c14c04a80e5206148a1c4204e0abf036101418186c128518a68380c24700900a1a508a9c0bb0072514ee84258047150cd090088ad014c80d6408fb03fc009daec6852ae07168001200000033c02800145700800001b00044ee0716874140100090000f200e814425882c4c0003818000c0400ece051281028680ba9c00001f8000000b28c0000201800d4010054804013280c06000e8399c070580e2c010004582820033000090680000f95d8040200001ddf21d2e809cb78000000007048058ef8ac0180000000001319893cce8050600000000032c250200002bc4500000012295dc40a000e049ea050340804047f84c007c0700c00d600004041bac822a42f8980c00cc128000014010341204
def andIndex12 : Nat → Option (Nat × Nat) := lookupWord 186 380 9 17 9 4 andHash12
def andData13 (_ : Nat) : Nat :=
  0x963b48a36120883c180724b1d89d1b08838140781923910770d440220f0601e0a88e3b4783e11068280e08e441d8c21107430100782a239111a0d8441e0c03848a361203802a35150301e0600c8b84a20078280323d170901c015168a8180f0500646a2e1203802a280782c0a2341381345827047a85f74eca2f9b4ebb278811a24b8cc1f03e007ff20bff865ffc81ffe28fff0c7ff843ff882ffc197fe207ff0a3ff831ffc10ffe0e7ff053ff819
def andLevel13 : Packing := (15, 2, 7, 0, 0, 10, 0, andData13)
def andHash13 (_ : Nat) : Nat :=
  0x50ef1190bb1ca0d90cf17d0140641d40500f41900f409008214f0360250af13004d00a1071a61650701006454104000a
def andIndex13 : Nat → Option (Nat × Nat) := lookupWord 12 27 5 12 4 4 andHash13

def andLevels : Nat → Packing
  | 9 => andLevel9
  | 10 => andLevel10
  | 11 => andLevel11
  | 12 => andLevel12
  | 13 => andLevel13
  | _ => emptyPacking

def andIndex : Nat → Nat → Option (Nat × Nat)
  | 10 => andIndex9
  | 11 => andIndex10
  | 12 => andIndex11
  | 13 => andIndex12
  | _ => fun _ => none

def andForest : Forest := ⟨1535, 13, dead.samples, searchColumns, deadautos.map List.reverse, andLevels, andIndex⟩
def andEarlyData9 (_ : Nat) : Nat :=
  0xc9148a051c9148a051c9148a051c80440203c900c8261c900c0221c900c0221c900c0221c80440203c80440263c120d0291c9269148bc100c0211c9068140bc100c0211c100c0211c100c0211c9068140bc100c0211c100c0211c9068140bc100c0211c9068140bc9068140bc100c0211c100c0211c9068140b320940a9dc9068140b0502c12ad89068148fc9068142f0500c02b14500c02111502c129d4502c123d450180403450180403450180403c900c0221c100c0211c100c0211c100c0211c100c0211c9068140bc100c0211c900c0221c900c0221c900c0221c900c0221c900c02214500c02114500c0331c100c0211c100c02114500c0331c900c0221c900c0221c900c0221c100c0211c100c0211c100c02114500c0331c900c0221c900c0221c900c0221c900c0221c9068140bc9068140b49068152b320940b1dc1428143bc100c0211c100c0211c9068140bc9068140bc900c0221320940b1dc9068140bc100c0211c9068140bc100c0211c9068140bc9068140bc100c0211c100c0211c9068140bc100c0211c9068140bc100c0211c9068140b4500c0331c900c0221c900c0221c900c0221c900c022149068152bc1428143bc9068140bc9068140b49068152bc100c0211c100c0211c100c0211c100c02114500c0331c900c0221c900c0221c900c0221c100c0211c9068140bc100c0211c100c0211c100c0211c100c0211c100c02114500c0331c100c0211c900c0221c100c0211c100c0211c900c0221c900c0221c100c0211c900c0221c900c0221c9068140bc9068140bc9068140bc9068140bc9068140b49068152b320940b1dc1428143bc92502011c92502011c92880403c90680403c90680403c9068140bc80440203c9068140bc9068140bc9068140bc80440203c80440203c80440203c9068140bc804402034900c036149068154bc9068140bc9068140bc9068140bc9068140b49068152bc9068146bc9068140b480440343c80440203c80440203c80440203c80440203680440323c8044026368044030bc8044024bc8044022b4500c0351c100c0211c100c0211c100c0211c100c0211c100c02114500c0331c100c0271c100c02113408403131408402536410804333a1548ac56814482613a1548a4d341a4924d4522d1285
def andEarlyData10 (i : Nat) : Nat :=
  if i < 4 then
    if i < 2 then
      if i < 1 then
        0x90483c900c0221192890483c900c02214542a05034542a050319068158bc9068140bc9068140bc9068140bc9068140bc9068140b49068152b8906814abc9068140bc900c0221c9068140bc9068140b4542a05034542a0503c9068140b4542a0503c9068140bc900c02214542a05034542a0503c900c0221c900c02214542a0503c900c02214542a0503c900c02214542a0503c900c02214542a0503c900c02211502c138d4502c120d4502c120d4502c120d4502c120d4502c120d4502c120d4502c132d0502c12ad4502c120d4502c120d4502c120d4502c120d4502c120d4502c120d4502c120d4502c120d49068150f89068148fc9068142f4502c120d4502c120d19289058349280412349068150b89068148bc9068142b4542a0503192890483c9068140bc928040231909848271909849271909848a74502c120d19098482fc909848276804403038a0440283c8044020bc80440203c804402071928905834900c02218900c02a1c900c022149068150b89068148bc9068142bc9068140b192890483c900c0221c9068140b4542a0503c945828154502c120d1502c128d4502c122dc9068140f4502c120d4502c120d4542a0503192890483c92804023c9068140b190984827c804402033a0540a856804402213a0540a0d3a4c22111340a4120d4542a05034562b05834900c032149068150bc9068140bc9068142bc9068140b4542a0503c9068140b4502c130dc9068140f4542a0503c9068140bc804402034542a0503c9068140b340a413098a0540a0d4542a050319289058349280412149068150b89068148bc9068142bc9068140b4542a0503192890483c9068140bc92804021190d828154502c130d1502c128d4502c120dc9068140f4502c120d4502c120d4542a0503192890483c92804021c9068140b4502c120d4542a0503c9068140b6854221118a0540a858a0540a0d8a0540a25c825028154542a05031928905834900c03218900c02a1c900c022149068150b89068148bc9068142b4542a0503192890483c900c0221c9068140b4502c120d4502c130d1502c128d4502c122dc9068140f4502c120d4502c120d4542a0503192890483c900c0221c9068140b4502c120d194c020114542a0503c9068140b4542a05031928904834502c1229c9068140b4502c120dc92c020114522d1285c925020114502c13098a0540a85c804402218a0540a0d4502c120d4542a05031928905834900c03218900c02a1c900c022149068150b89068148bc9068142bc9068140b490582915c90582835c9068140f4542a0503192890483c900c0221c9068140bc905828154542a0503c9068140b4542a05031928904838a0540a25c9068140bc905828154542a0503192890483c900c0221c9068140b4502c120d340a41309c804402218a0540a0d
      else
        0xbc900c0221c9068140bc901c0221c9068140dc80440223c8044020bc900c0221c9068140bc900c0221c9068140b4542a050349148a1514542a05038a48040214542a05038a48040614542a0503c9148a0518a480402119068140b49068150bc9068144bc9068140bc9068140bc9068140bc9068140bc9068140b4542a0503c9148a051c9068140b8a48040213a0980403680440303c80440243c80440203c80440203c80440203c80440203c8044020bc80440203c804402031542a0503c9148a051c92804021c9068140bc80440203682804021c9068140b4542a0503c9148a0516828040214502c1229c9068140bc92804021c804402034542a05034542a05031542a05038a550a8554542a05034542a05038a550a855c928040216828040214900c0221c900c0221c900c0221c900c02214542a05038a550a855c900c02214542a0503c900c02214542a05038a550a8554502c122949068140bc9068140bc9068140bc9068140bc9068140bc9068140b4542a05038a550a855c900c0221c9068140bc900c0221c9068140b4542a0503c900c0221c9068140b4542a05038a550a855c92804021c9068140b4542a0503c9068140b4542a05038a550a855c900c02214542a0503c80440221c9068140b8a05804033a0580403641080403680440203c80440203c80440203c80440203c80440203c80440203c80440203c80440203c80440203c80440203c80440203c80440203c900c0221c804402034542a05038a550a855c804402034542a0503c900c02214500c0211c100c0211c100c0211c100c0211c100c0211c100c0211c100c0211c100c0211c100c0211c100c0211c100c02113408402114542a050349148a1514900c0321c900c0261c900c02213a0b051291a0b05069c900c02214542a0503c9148a051c900c02213a0b05029641080403680440303c80440243c80440223c80440203c80440203c804402034542a0503c9148a051c900c0221c9068140bc80440203c900c02213a1548a4d4542a0503c9148a0514502c122919068140bc804402031948a0503c9148a051c900c0221c9068140bc804402034542a050349148a1514900c0321c900c0261c900c022149068150bc9068144bc9068142b8a038140bc9068140b4542a0503c9148a051c900c0221c9068140b8a01804033a01805038a01804238a018040b4542a0503c9148a051c900c0221c9068140b8a0180403c900c0221c9068140b4542a0503c9148a051c92804021c9068140b8a01804034542a0503c9148a051c900c0221c9068140b8a01804034542a0503c80440221c9068140b641080403c9068140b4502c120d0900c03a1c900c0221c900c0221192890483192890483c900c0221192890483c900c0221192890483c900c0221192890483c900c02214502c120d1928
    else
      if i < 3 then
        0x48a051c900c0221c90582815c804402036442a05034542a050319289058349148a15189148a0d14900c03218900c02a1c900c0261c900c02214502c130d1502c128d4502c124d4502c122d4502c120d4542a0503192890483c9148a051c900c02214502c120d6410804034542a0503192890483c9148a051c900c0221c905828156410804036410805033410804836410804236410804074542a0503192890483c9148a051c900c02214502c120d8a0180403194c02011194c020114542a0503c9148a051681080403192890483c900c02214502c120dc9148a0514502c120d3a0180403c92c020114542a0503192890483c9148a051c900c0221c905828158a0180403c92502011c925020114542a0503192890483c8540a051c80440221c825028158a01804038a01804034542a0503c9068140bc804402034900c0361c900c0221c900c0221c900c0221c900c0221c900c0221c80440203c900c02214542a0503151a8d06d4542a0503c9148a05149068154bc9068140bc9068140bc9068140bc9068140bc9068140b49068152bc9068146b151a8d16d2a0540b258a0540a654542a0503151a8d0658a0540a2519068140b49068150bc9068144bc9068140bc9068140b4502c130d4502c124d452884427c9068140fc9068140bc900c0221c900c0221c9068140bc900c0221c9068140b4542a0503151a8d06dc9068140bc928844258a0540a254542a0503c9068140b4542a0503c9068140b4542a0503c900c02214542a0503c900c022149148a1514901c0321c901c0261c901c022549068150dc9068144dc9068142dc901c0a0f4542a0507c9148a051c901c0221c9068140f8a01804074542a0507151a8d06dc901c0a25c9068140dc82450285340a4130dc80440225c9068140d6410804073a09804033a01805078a01804278a018040f8a0180407480440343c80440203c80440203c80440203c80440203c80440203c80440203680440323c80440263c80440203c80440203c80440203c80440203c80440203c80440203340340203c8044020368044030bc8044024bc8044022b340340303140340243c80440203340b40203c8044020b340340207c804402073403402034900c0221c900c0261c900c0221c9148a051c900c02213a4c22111c9068140b49068140bc9068144bc9068142bc9068140b3a4d22111151a8d06d8a0540a25c9068140b4502c120dc9148a051c900c0221c9068140b3a4c221118a4180403680440203c80440243c80440223c80440203c8044020b340340203c80440203c80440203c92880403c90680403c90680403c940e02033a108040349148a0514900c02214542a050349068140b4542a05036804402036828040214900c0321c900c0221c900c02213a1548a4d49068150bc9068140bc9068142bc9068140
      else
        0x214542a05034502c1229c9068140bc9068140bc9068140b4500c0211c100c0211c100c0211c100c02114542a05034900c0321c900c02214500c0311c100c02314542a0503c900c0221c100c0211c900c02214542a05034502c1229c100c02114542a05034542a0503c900c02211948a0503c900c02214542a0503c900c0221c100c0211c9068140b4542a05034502c1229c100c021119068140b4542a0503c900c02211948a0503c900c0221c100c0211c9068140b19068140bc9068140b4542a05034542a05031542a05034542a0503c928040214900c0221c900c02211948a0503c900c02214542a0503c928040214500c0211c100c0211c100c0211c100c02114542a0503c900c0221c100c0211c900c0221c100c02114542a05034502c1229c100c02114542a0503c100c02114542a0503c900c02214542a0503c900c02211948a0503c900c0221c100c0211c9068140b19068140bc9068140b49068140bc9068140bc9068140bc9068140bc9068140bc9068140bc9068140bc9068140bc9068140b4502c134d1502c12cd4502c120d192890483192890483c902c120d1928904834502c120d4502c120d8a0540a0d4502c120d4902c130b19289058949148a15189148a0d14902c130d8902c128dc902c124d4542a050b19289048bc9148a051c902c120d64108040b194c02011c9148a051c902c120d8a0540a0d3a0540b0d8a0540a8d8a0540a4dc8044020d8a018040b8a0540a0d4542a050919289048bc9148a051c90582815c925020118a018040b64108040b4542a05034542a05034542a05034542a0503c900c02214542a05034542a050364108050b34108048b64108040f3a018040b3a04403834804403438a04402c3c80440203c80440203c80440203c80440203c80440203c804402633a03403033a03402831a03402433a0340203c804402033a034020bc8044020bc804402033a0b40203c804402033a0340203c80440203680440307880440287c80440247c80440227c804402071928905831928904834900c03218900c02a1c900c0221c900c0221192890483c900c0221341a4924d4502c130d1502c128d4502c120d4502c122d4502c120d19289048bc902c0221c902c120d8a0540a0d8a0440283c80440223c80440207192890483c900c0221c905828154542a050319289058349148a15189148a0d14900c03218900c02a1c900c0261c900c02213a4c22111192890483c9148a051c900c0221150984825150984925150984865c900c02214542a050919289048bc9148a051c902c0221150b848258a0540a0d64108040b6804403038a0440283c80440243c80440223c80440203c80440203c80440203c9148a051c90582815c804402034542a0503c9148a051c80440203192890483c900c0221341a4924d1948a0503c91
  else
    if i < 6 then
      if i < 5 then
        0x28904834502c120d6854221118a0540a85c928040218a0540a25c905828151928905834900c03218900c02a1c900c02213a4c22111192890483c900c0221150984825150984925c900c02214542a0503192890483c900c0221c905828154542a05034542a05031928904838a0540a251905828154542a0503c900c02211948a0503c900c0221c90582815c100c02114500c0331c900c0221c900c02214542a0503c9068140b49068152bc1428143bc928040214900c0221c900c0221c900c02214500c0211c100c0211c100c0211c100c0231c900c0221c100c0211c900c0221c9068140bc900c02211542a05034900c02211948a05034500c02114542a0503c900c0221c92804021c100c02114502c1229c100c0211c900c0221c900c022119068140bc92804021c100c0211c100c0211c900c0221c900c0221c100c0211c9068140bc900c0221c900c02214900c02214500c02111542a05031948a05034542a05034542a05034542a05034542a05034542a05034542a05031948a05034542a05034542a05034542a05034542a05031542a05034542a0503c928040214900c02211948a0503c900c02214542a0503c928040214500c0211c100c0211c100c0211c100c02114542a0503c900c0221c100c0211c900c02214542a05034502c1229c100c02114542a05034542a0503c900c02211948a0503c900c0221c9068140b19068140b4542a05031542a05034542a0503c928040214900c02211948a0503c900c02214542a0503c928040214500c0211c100c0211c100c0211c100c02114542a0503c900c0221c100c0211c900c02214542a05034502c1229c100c02114542a05034542a0503c900c02211948a0503c900c0221c9068140b19068140b49068140bc9068140bc9068140bc9068140bc9068140bc9068140bc9068140b4542a05031542a05034542a05034542a05034500c0311c100c0211c100c0211c100c02114542a0503c100c02114542a050319068140b49068150bc9068140bc9068140bc9068140bc9068140bc1428141bc9068140b1542a0503c92804021c100c0211c9068140b4542a0503c9068140b4542a0503c92804021c92804021c100c02114502c1229c9068140b4542a05034542a05031948a05034500c02114542a0503c100c02114542a05031948a0503c9068140b49068140bc9068140bc9068140bc9068140b1542a0503c100c0211c9068140bc100c0211c9068140b4542a0503c9068140b4542a0503c100c021119068140b4542a05034542a0503c9068140b4542a0503c100c0211c9068140bc92804021c928040214502c12294900c0221c900c0221c900c0221c900c0221c900c0221c900c0221c900c0221c900c02214900c03214542a05031542a05034542a0503c928040214900c02214542a0503c900c02
      else
        0x211c9068140bc100c0211c9068140bc9068140bc100c02118a0540a0dc100c0211c9068140bc905828154502c120dc100c0211c100c0211c9068140bc100c0211c9068140bc900c0221c100c0211c9068140bc100c0211c9068140bc900c0221c9068140b1500c021119068140b1928904831928904831928904831928904831928904831928904838100c0291c100c0211192890483c100c0211c9280402119068140b192890483c100c0211c92804021190582815c100c02111928904838a0540a854500c02114502c12298a0540a258900c02a11502c128d4502c122dc900c02211928904834502c1229c900c0221c9068140b1928904838a0540a25c9068140bc9068140b192890483c900c0221c900c0221c9068140b1905828154502c120d4502c120d4502c120d4502c120d4502c120d4500c02114500c02114500c02114500c02114500c02114500c02118100c02911928904834502c1229c100c0211c9068140b89068148bc9068140b192890483c100c0211c9068140b4502c120d1502c128d4502c121d4502c120dc9068140f4502c120dc100c0211c9068140b1928904834502c1229c100c0211c9068140b4502c120d1928904834502c120d19289048319068140b8a0540a0d4502c120d8900c02a1c900c02218100c0291c100c023189068148bc9068142bc1428141bc9068140b1928904838a0540a25c100c0211c9068140bc90582815192890483c900c0221c100c02118a0540a0dc90582815c90582835c100c0211c9068140bc100c0211c9068140b1928904838a0540a25c100c0211c9068140bc90582815192890483c900c0221c100c0211c9068140b4502c120dc900c0221c9068140b4900c02214500c021149068140b1905828154502c120dc100c0211c9068140b4542a050319068140bc100c021119068140b4502c120d45018040345018040319068140bc100c02118a0540a0dc1428141bc9068140b3a4c22111c100c0211c9068140b190582815c100c0211c9068140bc100c0211c9068140bc90582815c100c021119068140b4502c120dc9068140bc100c0211c9068140bc905828150900c03a1c900c02214542a05031502c138d4502c132d0502c12ad4542a05031928904834900c02218900c02a1c900c0221192890483c900c02214542a0503c905828154502c120d1502c128d4502c122d4502c120d192890483c900c02214502c120d1928904834900c02213a4c22111340a4120d4562a05034900c03214542a05034502c130d4542a05034542a0503c900c02211948a0503192890583154aa05031928904834528040214528041214542a05031928904834528040211905828154502c130d1502c128d4502c120d4502c120d4502c120d4542a0503192890483c928040214502c120d4542a05034542a050319
    else
      if i < 7 then
        0x9068140b8a0540a853a0540a858a0540a854542a0503152a9148b152a9148b152a9148b1502c13094502c1309c900c02214500c02218a0540a0d190e8542bc100c02118a4560b0d641080403c9068140bc92804021c100c02118a0180403c100c0211c9068140b8a0180403820180413c100c02118a0180403c100c0211c9068140b8a01804033408402113a0180403641080403c9148a051c92804021c9148a0518a0180403c9148a051341a4934949148a0511542a05034542a0503c9148a051682804021c9148a051c928040213a0180403c9148a051c92804021c9148a051c9148a0518a0180403c9148a05149148a051341a493491542a05034542a05034542a05034542a05034542a05034542a05034542a05034542a05034542a05034542a05031542a0503c9148a051c9148a051c928040216828040214542a0503c9148a051c9148a051c928040218a01804033a0180403682804021c900c02214542a0503c900c0221c900c02211542a0503c92804021c900c0221c900c0221c92804021c804402213a01804036828040214542a0503c900c0221c900c02214542a0503c900c0221c900c0221c9148a051c9148a051c9148a0511542a0503c9148a051c9148a051c9148a0513a01804031542a0503c9148a051c92804021682804021c9148a051c9148a051c92804021682804021c928040214542a0503c9148a0518a01804031542a0503c9148a051c9148a0513a0180403c9148a051c9148a051c92804021682804021c928040214900c0221c900c0221c900c0221c900c0221c80440221c900c0221c900c0221c900c02211542a0503c9148a051c9148a051c928040216828040214900c0221c900c0221c900c02214542a0503c9148a051c900c0221c900c0221c9148a051c92804021c804402218a01804033a0180403c900c0261c900c02214542a0503c9148a051c900c0221c900c0221c9148a051c92804021c804402214542a0503c9148a051c900c02218a0180403c900c0221c9148a051c928040213a0180403c900c0221c804402218a01804033a01804031542a0503c9148a051c9148a051c928040216828040214900c0221c900c0221c900c0221c900c02214542a0503c9148a051c900c0221c900c0221c900c0221c9148a051c92804021c900c0221c804402218a01804033a0180403680440203c80440203c80440203c80440203c80440203c80440203c804402038100c02b181428149bc100c0211c9068140bc900c0221c900c0221c900c0221c900c0221c900c02211502c129d89068148fc9068142fc1428141fc100c0211c100c0211c9068140bc9068140bc1428141bc100c0211c9068140bc900c0221c9068140b1500c021119068140bc82804021c100c02114502c1229c100c021119068140bc9068140bc100c0
      else
        0x8a0440221c940e0341191c8e071c940e0341c940e0341491088140340a413091502c13094542a0503c940e0341191c8e071c940e0341c940e0341191c8e071c940e0341191c8e071c940e0341c940e0341191c8e071c0d048261c900c0221680440221c900c0221c940e0341191c8e071c940e0341c940e0341c940e0341191c8e071c940e03418a0180442c804402036804402033a0440203c940e0341191c8e071c940e03413a0540a85152a9148b8a0540a853a0540a853a0540a858a0540a85152a9148b8a0540a853a0540a85152a9148bc9068140b8a0540a851542a05031
def andEarlyData11 (i : Nat) : Nat :=
  if i < 1 then
    0xc02114542a05034542a0503c900c02211948a0503c900c0221c9068140b19068140bc9068140bc9068140bc9068140bc9068140bc9068140bc9148a051c9148a051192890483c9148a051c90582815341a4924d4502c120d4502c120d4502c120d4502c120d4502c120d4542a0503192890483c9148a0514502c120d1928904834502c120d4542a0503c9148a0514502c120d4542a05031928904834502c120dc9148a0514502c120d4502c120d4542a0503192890483c9148a051c905828154542a05034542a0503192890483340a4120d8a01804036810804033a01804038a0180403680440203c80440203c80440203c80440203c80440203c80440203c80440203c80440203c80440203c80440203c80440203c80440203c80440203c80440203c80440203c80440203c804402034542a05031542a0503c9148a0514542a05034542a0503c9148a051c928040216828040214900c0221c900c0221c900c02214542a0503c9148a051c900c0221c900c02214542a0503c900c02214542a0503c9148a0514502c12294542a0503c9148a0511948a0503c9148a051c900c0221c9068140b3a1548a4d19068140b49068140bc9068140bc9068140bc9068140bc9068140bc9068140bc9068140bc9068140b4542a0503c9148a051c900c0221c9068140bc900c0221c9068140b4542a0503c900c0221c9068140b4542a0503c9148a051c92804021c9068140b4542a0503c9068140b4542a0503c9148a051c900c0221c9068140b4542a0503c900c02214542a0503c80440221c9068140b8a01804033a0180403641080403680440203c80440203c80440203c80440203c80440203c80440203c80440203c80440203c80440203c80440203c80440203c80440203c80440203c80440203c804402034542a05034542a05034542a05031928904831542a05031928904834542a05034542a0503c928040214900c0221c900c0221c900c0221c900c0221c900c02214542a0503192890483c900c0221192890483c900c02214542a0503c900c02214542a05031928904834502c12294542a05031948a0503192890483c900c0221c9068140bc9068140b19068140b49068140bc9068140bc9068140bc9068140bc9068140bc9068140bc9068140bc9068140bc9068140b3a4c22111192890483c900c0221c9068140bc900c0221c9068140b4542a0503c900c0221c9068140b4542a05031928904838a0540a25c9068140b4542a0503c9068140b4542a0503192890483c900c02218a0540a0d4542a0503c900c02214542a0503c900c0221c9068140bc905828151905828154502c120d4502c120d4502c120d4502c120d4502c120d4502c120d4502c120d4502c120d4502c120d4502c120d4502c120d4502c120d4502c120d4502c120d4502c120d4502c120d
  else
    0xc940e0341191c8e071c940e03413a0540a85152a9148b8a0540a858a0540a853a0540a858a0540a85c100c0211c100c0211c9068140b3408402113a01804038a01804036410804031542a0503c9148a051c9148a051c92804021682804021c900c02214542a0503c9148a051c900c0221c900c0221c9148a051c92804021c804402218a01804033a0180403c900c0221192890483c92804021c100c0211c100c0211c100c02111928904834502c1229c100c0211192890483192890483c9068140b19068140bc9068140bc9068140bc900c0221c100c0211c9068140b1928904838a0540a25c100c0211c9068140bc100c0211c9068140b192890483c900c0221c9068140b192890483c900c0221c100c02118a0540a0dc900c0221c900c0221c100c0211c9068140b190582815c905828154502c120d4502c120d4502c120d4502c120d4502c120d4502c120dc9068140bc100c0211c9068140bc100c0211c9068140bc9068140bc100c02118a0540a0dc100c0211c9068140bc90582815c905828154502c120d4542a05034542a05031928904831542a05031928904834542a05034542a0503c928040214900c0221c900c02213a4c22111192890483c900c0221c900c02214542a0503c900c02214542a05031928904838a0540a254542a05034542a0503c900c0221c905828151905828154502c120d4502c120d4502c120d4502c120d4502c120d4542a05031542a05034542a0503c928040214900c02211948a0503c900c02214542a0503c928040214500c0211c100c0211c100c0211c100c02114542a0503c900c0221c100c0211c900c02214542a05034502c1229c100

def andWitnessData : Nat → Nat → Nat
  | 9 => andEarlyData9
  | 10 => andEarlyData10
  | 11 => andEarlyData11
  | _ => fun _ => 0

def andEarlyTest (k i : Nat) : Bool :=
  inversionWitness (targetOf andForest) k (stateSet andForest k i)
    (packedAt (andWitnessData k) (36 * i) 36)

def AndTableCheck : Prop :=
  ∀ k ≤ 13, ∀ i < (andForest.levels k).1, andEarlyTest k i = true ∨ nodeVerified andForest k i = true

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem andGeometry : graphValid andForest (boundsBefore known383) = true := by
  simp only [graphValid, Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel, by decide +kernel⟩, listPieces_all (d := 5) ?_⟩,
    listPieces_all (d := 3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

def firstAndLinks : List CheckedLink :=
  (List.range (andForest.levels 13).1).flatMap fun i =>
    [0, 1].filterMap (fun p =>
      (linkedSet andForest 13 (i, p)).map fun ws => (keySet ws, ws))

set_option maxRecDepth 8192 in
theorem firstAndLinks_valid (checks : AndTableCheck) :
    validLinks 13 firstAndLinks := by
  intro l hl
  obtain ⟨i, _, alt⟩ := List.mem_flatMap.mp hl
  obtain ⟨p, _, hit⟩ := List.mem_filterMap.mp alt
  obtain ⟨ws, hs, rfl⟩ := Option.map_eq_some_iff.mp hit
  have geom := andGeometry
  simp only [graphValid, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at geom
  have all := forest_all_cases andForest 13 (boundsBefore known383) andEarlyTest
    (before_sound known383 valid383) andGeometry (fun _ _ h => inversionWitness_sound h) checks
  have imp := linkedSet_sound andForest 13 geom.2 (all 13 (by omega)) hs
  have target : targetOf andForest = graph := by decide +kernel
  rwa [target] at imp
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_block_9_185 : block andForest 9 185 28 = true := by
  apply cellsBlock (ar := 9) (rows := 2) (d := 2)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_block_9_213 : block andForest 9 213 12 = true := by
  apply cellsBlock (ar := 10) (rows := 2) (d := 1)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem and_all_9 : block andForest 9 185 40 = true := (@block_merge andForest 9 185 28 12 and_block_9_185 and_block_9_213)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_block_10_1643 : block andForest 10 1643 170 = true := by
  apply cellsBlock (ar := 9) (rows := 2) (d := 5)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_block_10_1813 : block andForest 10 1813 240 = true := by
  apply cellsBlock (ar := 10) (rows := 2) (d := 5)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_block_10_2053 : block andForest 10 2053 240 = true := by
  apply cellsBlock (ar := 10) (rows := 2) (d := 5)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_block_10_2293 : block andForest 10 2293 240 = true := by
  apply cellsBlock (ar := 10) (rows := 2) (d := 5)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_block_10_2533 : block andForest 10 2533 240 = true := by
  apply cellsBlock (ar := 10) (rows := 2) (d := 5)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_block_10_2773 : block andForest 10 2773 240 = true := by
  apply cellsBlock (ar := 10) (rows := 2) (d := 5)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_block_10_3013 : block andForest 10 3013 240 = true := by
  apply cellsBlock (ar := 10) (rows := 2) (d := 5)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_block_10_3253 : block andForest 10 3253 29 = true := by
  apply cellsBlock (ar := 10) (rows := 2) (d := 2)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_block_10_3282 : block andForest 10 3282 143 = true := by
  apply cellsBlock (ar := 11) (rows := 2) (d := 4)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem and_all_10 : block andForest 10 1643 1782 = true := (@block_merge andForest 10 1643 890 892 (@block_merge andForest 10 1643 410 480 (@block_merge andForest 10 1643 170 240 and_block_10_1643 and_block_10_1813) (@block_merge andForest 10 2053 240 240 and_block_10_2053 and_block_10_2293)) (@block_merge andForest 10 2533 480 412 (@block_merge andForest 10 2533 240 240 and_block_10_2533 and_block_10_2773) (@block_merge andForest 10 3013 240 172 and_block_10_3013 (@block_merge andForest 10 3253 29 143 and_block_10_3253 and_block_10_3282))))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_block_11_363 : block andForest 11 363 48 = true := by
  apply cellsBlock (ar := 9) (rows := 2) (d := 3)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_block_11_411 : block andForest 11 411 240 = true := by
  apply cellsBlock (ar := 10) (rows := 2) (d := 5)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_block_11_651 : block andForest 11 651 240 = true := by
  apply cellsBlock (ar := 10) (rows := 2) (d := 5)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_block_11_891 : block andForest 11 891 240 = true := by
  apply cellsBlock (ar := 10) (rows := 2) (d := 5)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_block_11_1131 : block andForest 11 1131 48 = true := by
  apply cellsBlock (ar := 10) (rows := 2) (d := 3)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_block_11_1179 : block andForest 11 1179 240 = true := by
  apply cellsBlock (ar := 11) (rows := 2) (d := 5)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_block_11_1419 : block andForest 11 1419 240 = true := by
  apply cellsBlock (ar := 11) (rows := 2) (d := 5)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_block_11_1659 : block andForest 11 1659 240 = true := by
  apply cellsBlock (ar := 11) (rows := 2) (d := 5)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_block_11_1899 : block andForest 11 1899 240 = true := by
  apply cellsBlock (ar := 11) (rows := 2) (d := 5)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_block_11_2139 : block andForest 11 2139 240 = true := by
  apply cellsBlock (ar := 11) (rows := 2) (d := 5)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_block_11_2379 : block andForest 11 2379 119 = true := by
  apply cellsBlock (ar := 12) (rows := 2) (d := 4)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem and_all_11 : block andForest 11 363 2135 = true := (@block_merge andForest 11 363 816 1319 (@block_merge andForest 11 363 288 528 (@block_merge andForest 11 363 48 240 and_block_11_363 and_block_11_411) (@block_merge andForest 11 651 240 288 and_block_11_651 (@block_merge andForest 11 891 240 48 and_block_11_891 and_block_11_1131))) (@block_merge andForest 11 1179 720 599 (@block_merge andForest 11 1179 240 480 and_block_11_1179 (@block_merge andForest 11 1419 240 240 and_block_11_1419 and_block_11_1659)) (@block_merge andForest 11 1899 240 359 and_block_11_1899 (@block_merge andForest 11 2139 240 119 and_block_11_2139 and_block_11_2379))))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_block_12_0 : block andForest 12 0 15 = true := by
  apply cellsBlock (ar := 9) (rows := 2) (d := 1)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_block_12_15 : block andForest 12 15 91 = true := by
  apply cellsBlock (ar := 10) (rows := 2) (d := 4)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_block_12_106 : block andForest 12 106 157 = true := by
  apply cellsBlock (ar := 11) (rows := 2) (d := 4)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_block_12_263 : block andForest 12 263 36 = true := by
  apply cellsBlock (ar := 12) (rows := 2) (d := 2)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem and_all_12 : block andForest 12 0 299 = true := (@block_merge andForest 12 0 106 193 (@block_merge andForest 12 0 15 91 and_block_12_0 and_block_12_15) (@block_merge andForest 12 106 157 36 and_block_12_106 and_block_12_263))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_block_13_0 : block andForest 13 0 9 = true := by
  apply cellsBlock (ar := 10) (rows := 2) (d := 0)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_block_13_9 : block andForest 13 9 6 = true := by
  apply cellsBlock (ar := 11) (rows := 2) (d := 0)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem and_all_13 : block andForest 13 0 15 = true := (@block_merge andForest 13 0 9 6 and_block_13_0 and_block_13_9)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_early_9_0 : witnessBlock (andEarlyTest 9) 0 96 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_early_9_96 : witnessBlock (andEarlyTest 9) 96 89 = true := by decide +kernel

theorem and_early_9 (i : Nat) (hi : i < 185) : andEarlyTest 9 i = true := by
  by_cases h : i < 96
  ·
    exact witnessBlock_at and_early_9_0 (by omega) (by omega)
  ·
    exact witnessBlock_at and_early_9_96 (by omega) (by omega)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_early_10_0 : witnessBlock (andEarlyTest 10) 0 96 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_early_10_96 : witnessBlock (andEarlyTest 10) 96 96 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_early_10_192 : witnessBlock (andEarlyTest 10) 192 96 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_early_10_288 : witnessBlock (andEarlyTest 10) 288 96 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_early_10_384 : witnessBlock (andEarlyTest 10) 384 96 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_early_10_480 : witnessBlock (andEarlyTest 10) 480 96 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_early_10_576 : witnessBlock (andEarlyTest 10) 576 96 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_early_10_672 : witnessBlock (andEarlyTest 10) 672 96 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_early_10_768 : witnessBlock (andEarlyTest 10) 768 96 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_early_10_864 : witnessBlock (andEarlyTest 10) 864 96 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_early_10_960 : witnessBlock (andEarlyTest 10) 960 96 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_early_10_1056 : witnessBlock (andEarlyTest 10) 1056 96 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_early_10_1152 : witnessBlock (andEarlyTest 10) 1152 96 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_early_10_1248 : witnessBlock (andEarlyTest 10) 1248 96 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_early_10_1344 : witnessBlock (andEarlyTest 10) 1344 96 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_early_10_1440 : witnessBlock (andEarlyTest 10) 1440 96 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_early_10_1536 : witnessBlock (andEarlyTest 10) 1536 96 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_early_10_1632 : witnessBlock (andEarlyTest 10) 1632 11 = true := by decide +kernel

theorem and_early_10 (i : Nat) (hi : i < 1643) : andEarlyTest 10 i = true := by
  by_cases h : i < 864
  ·
    by_cases h : i < 384
    ·
      by_cases h : i < 192
      ·
        by_cases h : i < 96
        ·
          exact witnessBlock_at and_early_10_0 (by omega) (by omega)
        ·
          exact witnessBlock_at and_early_10_96 (by omega) (by omega)
      ·
        by_cases h : i < 288
        ·
          exact witnessBlock_at and_early_10_192 (by omega) (by omega)
        ·
          exact witnessBlock_at and_early_10_288 (by omega) (by omega)
    ·
      by_cases h : i < 576
      ·
        by_cases h : i < 480
        ·
          exact witnessBlock_at and_early_10_384 (by omega) (by omega)
        ·
          exact witnessBlock_at and_early_10_480 (by omega) (by omega)
      ·
        by_cases h : i < 672
        ·
          exact witnessBlock_at and_early_10_576 (by omega) (by omega)
        ·
          by_cases h : i < 768
          ·
            exact witnessBlock_at and_early_10_672 (by omega) (by omega)
          ·
            exact witnessBlock_at and_early_10_768 (by omega) (by omega)
  ·
    by_cases h : i < 1248
    ·
      by_cases h : i < 1056
      ·
        by_cases h : i < 960
        ·
          exact witnessBlock_at and_early_10_864 (by omega) (by omega)
        ·
          exact witnessBlock_at and_early_10_960 (by omega) (by omega)
      ·
        by_cases h : i < 1152
        ·
          exact witnessBlock_at and_early_10_1056 (by omega) (by omega)
        ·
          exact witnessBlock_at and_early_10_1152 (by omega) (by omega)
    ·
      by_cases h : i < 1440
      ·
        by_cases h : i < 1344
        ·
          exact witnessBlock_at and_early_10_1248 (by omega) (by omega)
        ·
          exact witnessBlock_at and_early_10_1344 (by omega) (by omega)
      ·
        by_cases h : i < 1536
        ·
          exact witnessBlock_at and_early_10_1440 (by omega) (by omega)
        ·
          by_cases h : i < 1632
          ·
            exact witnessBlock_at and_early_10_1536 (by omega) (by omega)
          ·
            exact witnessBlock_at and_early_10_1632 (by omega) (by omega)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_early_11_0 : witnessBlock (andEarlyTest 11) 0 96 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_early_11_96 : witnessBlock (andEarlyTest 11) 96 96 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_early_11_192 : witnessBlock (andEarlyTest 11) 192 96 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem and_early_11_288 : witnessBlock (andEarlyTest 11) 288 75 = true := by decide +kernel

theorem and_early_11 (i : Nat) (hi : i < 363) : andEarlyTest 11 i = true := by
  by_cases h : i < 192
  ·
    by_cases h : i < 96
    ·
      exact witnessBlock_at and_early_11_0 (by omega) (by omega)
    ·
      exact witnessBlock_at and_early_11_96 (by omega) (by omega)
  ·
    by_cases h : i < 288
    ·
      exact witnessBlock_at and_early_11_192 (by omega) (by omega)
    ·
      exact witnessBlock_at and_early_11_288 (by omega) (by omega)

theorem andTables : AndTableCheck := by
  intro k hk i hi
  interval_cases k
  · change i < 0 at hi; omega
  · change i < 0 at hi; omega
  · change i < 0 at hi; omega
  · change i < 0 at hi; omega
  · change i < 0 at hi; omega
  · change i < 0 at hi; omega
  · change i < 0 at hi; omega
  · change i < 0 at hi; omega
  · change i < 0 at hi; omega
  · change i < 225 at hi
    by_cases below : i < 185
    · exact Or.inl (and_early_9 i below)
    · exact Or.inr (block_at and_all_9 i (by omega) (by omega))
  · change i < 3425 at hi
    by_cases below : i < 1643
    · exact Or.inl (and_early_10 i below)
    · exact Or.inr (block_at and_all_10 i (by omega) (by omega))
  · change i < 2498 at hi
    by_cases below : i < 363
    · exact Or.inl (and_early_11 i below)
    · exact Or.inr (block_at and_all_11 i (by omega) (by omega))
  · change i < 299 at hi
    exact Or.inr (block_at and_all_12 i (by omega) (by omega))
  · change i < 15 at hi
    exact Or.inr (block_at and_all_13 i (by omega) (by omega))


set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem andBoth : AndCertified bothPolarities := by
  exact ⟨firstAndLinks, firstAndLinks_valid andTables, andMatrix_sound (by decide +kernel)⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem andNegative : AndCertified negPolarity := by
  exact ⟨firstAndLinks, firstAndLinks_valid andTables, andMatrix_sound (by decide +kernel)⟩

end PEqualNP.Outside.L_meta_1936

theorem PEqualNP.Outside.L_meta_1936 : ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro pins short D fan size
  exact PEqualNP.Outside.L_meta_1936.and_after_not pins short D fan size
    PEqualNP.Outside.L_meta_1936.andBoth PEqualNP.Outside.L_meta_1936.andNegative
