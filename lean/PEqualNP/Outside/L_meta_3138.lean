import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_3138
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
private lemma extract (gs : List Gate) (w : List Sig)
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
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]
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
def seed : Sig := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
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
    let large := decide (ws.length+(k+1) ≥ 17)
    let width := if large then 5 else 4
    let mask := if large then 31 else 15
    let a := ws.getD (bits &&& mask) defaultDecor
    let b := ws.getD ((bits >>> width) &&& mask) defaultDecor
    decodeBank k (bits >>> (if large then 20 else 10))
      (ws++[codeDecor ((bits >>> (2*width)) &&& 3) a b])
private theorem code_faithful {r s x y} (op : Nat) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (codeDecor op x y) := by
  by_cases h : op = 2
  · simpa only [codeDecor,if_pos h] using faithful_neg hx
  · simpa only [codeDecor,if_neg h] using faithful_bin (op == 1) hx hy
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
      exact code_faithful _ (faithful_get base _) (faithful_get base _)
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
def closeChild (pools : List BoundPool) (links : List Sig → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links ws).any (sameWords ws) || pools.any (fun p => scalarPoolCut p k rest op)
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
abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (List Sig → List (List Sig))
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
  let nonedge := dneg (dbin false (ws.getD 0 defaultDecor) (ws.getD 2 defaultDecor))
  if g.mask=1023 then ws.map (fun w => dbin false w nonedge) else ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  have base := raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  intro a ha
  unfold wiresOf at ha
  split at ha
  · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ha
    exact faithful_bin false (base w hw) (faithful_neg (faithful_bin false
      (faithful_get base 0) (faithful_get base 2)))
  · exact base _ ha
def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  if m=1023 then liftGoal m v &&& ~~~(v 0 &&& v 2) else liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  by_cases e : m=1023
  · have u := asRow_bit v i (0 : Fin 9)
    have w := asRow_bit v i (2 : Fin 9)
    have h := bit_liftGoal m v i
    change (inputs.getD 0 zero).getLsbD (asRow v i).val = (v 0).getLsbD i.val at u
    change (inputs.getD 2 zero).getLsbD (asRow v i).val = (v 2).getLsbD i.val at w
    have seedEq : seed = inputs.getD 0 zero &&& inputs.getD 2 zero := by decide +kernel
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
def storedDepth (g : Forest) (depth : Nat) := if (wiresOf g).length+depth ≥ 17 then 2*depth else depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,pw,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := packedAt data (i*width) width
  let stored := recp &&& ((1 <<< len)-1)
  let ops := if pw=250 then data (4*i) else stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (if pw=250 then data (4*i+1) else recp >>> len) bank)
def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let large := decide (bank.length ≥ 17)
    let width := if large then 5 else 4
    let more := chosenSteps bank (ops >>> (if large then 20 else 10)) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops (2*width) 2,(bank.getD (getFieldV ops 0 width) defaultDecor).1,
        (bank.getD (getFieldV ops width width) defaultDecor).1) :: more
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
def qOrbit (g : Forest) (ws : List Sig) : Nat × Nat :=
  let trans (i : Nat) := (((g.autos[i]?).getD []).map swapRows).reverse
  (List.range g.autos.size).foldl (fun best i =>
    let h := keySet (ws.map (movedWord (trans i)))
    if h<best.1 then (h,i) else best) (keySet ws,0)
def qCompose : List Nat := [0,1,2,8,4,11,6,7,3,9,10,5,1,0,3,9,5,10,7,6,2,8,11,4,2,8,0,1,3,9,5,10,4,11,7,6,3,9,1,0,2,8,4,11,5,10,6,7,4,11,8,2,0,1,3,9,6,7,5,10,5,10,9,3,1,0,2,8,7,6,4,11,6,7,11,4,8,2,0,1,10,5,3,9,7,6,10,5,9,3,1,0,11,4,2,8,8,2,4,11,6,7,10,5,0,1,9,3,9,3,5,10,7,6,11,4,1,0,8,2,10,5,7,6,11,4,8,2,9,3,0,1,11,4,6,7,10,5,9,3,8,2,1,0]
def qCandidate (g : Forest) (k : Nat) (ws : List Sig) : Option (Nat × Nat) :=
  let (_,_,_,_,mark,_,_,_) := g.levels k
  if mark=250 then
    let (h,p) := qOrbit g ws
    (g.index k h).map (fun (j,q) => (j,qCompose.getD (12*q+p) 0))
  else g.index k (keySet ws)
def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos (5+lw)
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let pairs := if pw=250 then getPairs (fun _ => data (4*i+3)) cw depth (data (4*i+2)) 0 else getPairs data cw depth nr st
  let rules := pairs.filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun ws => ((qCandidate g k ws).bind (linkedSet g (k-1))).toList
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
    have e : ((qCandidate g k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
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
  let nr := packedAt data pos (5+lw)
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let pairs := if pw=250 then getPairs (fun _ => data (4*i+3)) cw depth (data (4*i+2)) 0 else getPairs data cw depth nr st
  let rules := pairs.filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun ws => ((qCandidate g k ws).bind (linkedSet g (k-1))).toList
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
def seedB : Sig := inputs.getD 0 zero ||| inputs.getD 3 zero
theorem seedB_table : ∀ r : Row, bit r seedB = (sample r 0 || sample r 3) := by decide +kernel
theorem seedB_nonzero : seedB ≠ zero := by decide +kernel
def neighborB (i : Fin 9) : Nat := [5,2,1,2,3,0,1,2,3].getD i.val 0
def extraB (i : Fin 9) : Nat := [8,0,0,1,0,0,0,0,0].getD i.val 0
def absentB (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< neighborB i) ||| extraB i)
def presentB (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighborB i) ||| extraB i)
theorem seedB_witness : ∀ i : Fin 9,
    (bit (absentB i) graph != bit (presentB i) graph) &&
    ((inputs++[seedB]).all fun w => w == inputs.getD i.val zero ||
      bit (absentB i) w == bit (presentB i) w) = true := by decide +kernel
theorem all_rootsB {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ inputs++[seedB]) :
    S=inputs.toFinset ∨ S=(inputs++[seedB]).toFinset := by
  have all (i : Fin 9) : inputs.getD i.val zero ∈ S := by
    have cut := seedB_witness i
    simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne,List.all_eq_true,
      Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at cut
    apply raw_required h _ _ sub (absentB i) (presentB i) cut.1
    exact fun v hv hne => (cut.2 v hv).resolve_left hne
  have needed : inputs.toFinset ⊆ S := by
    intro v hv
    have hm := List.mem_toFinset.mp hv
    rw [←input_list,List.mem_ofFn] at hm
    obtain ⟨i,rfl⟩ := hm
    exact all i
  by_cases hseed : seedB ∈ S
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
theorem initial_liveB (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 3))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 15) :
    ∃ k t, k ≤ 14 ∧ (Live graph k t inputs.toFinset ∨ Live graph k t (inputs++[seedB]).toFinset) := by
  have headEq : (execute C.gates inputs).getD 9 zero = seedB := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal 9 r).trans ((first (sample r)).trans (seedB_table r).symm)
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
    exact False.elim (seedB_nonzero headEq.symm)
  | cons g gs =>
    have eq0 : gv inputs g = seedB := by
      rw [hgs] at headEq
      change (execute gs (inputs++[gv inputs g])).getD 9 zero = seedB at headEq
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
    rcases all_rootsB run hs with h | h
    · exact Or.inl (h ▸ run)
    · exact Or.inr (h ▸ run)
def qWiden : Nat → Nat → Nat
  | 0, _ => 0
  | t+1, r =>
    (r % 16) ||| (((r >>> 4)%16) <<< 5) ||| (((r >>> 8)%4) <<< 10) ||| ((qWiden t (r >>> 10)) <<< 20)
def q14r (i : Nat) : Nat := 0x0
def q14g (i : Nat) : Nat := 0xe
def q14p (i : Nat) : Nat := 0x5fc545b63629201a98180e060200
def orfd14 (p : Nat) : Nat :=
  let j := p/4
  let r := packedAt q14r (j*0) 0
  if p % 4=0 then (304 <<< 0) else if p % 4=1 then 1023 else
    let w := packedAt q14g (((r >>> 0) % 1)*4) 4
    let n := w >>> 0
    if p % 4=2 then n else packedAt q14p ((w % 1)*8) (n*8)
def orfl14 : Packing := (1,1,7,0,250,0,0,orfd14)
def q13pb (i : Nat) : Nat := 0x0
def q13r (i : Nat) : Nat := 0xe99d96d76d94d64d91c91d81c81d71d61d51c51d41d21c21e11d60d20d10299596266594894244591211940920200
def q13g (i : Nat) : Nat := 0x37
def q13p (i : Nat) : Nat := 0x1dcecf4afb7cbedd2eb549649647168ac522b00803a5c0e06fb69b2d86d29548a4462210c80401c8d06833988c26030108703813064301809024100a0000
def orfd13 (p : Nat) : Nat :=
  let j := p/4
  let r := packedAt q13r (j*12) 12
  let parent := packedAt q13pb (j*0) 0
  let op := ((r >>> 0) % 1024)
  let keep := ((r >>> 10) % 4)
  if p % 4=0 then (orfd14 (4*parent)) ||| (op <<< 10) else if p % 4=1 then
    let old := orfd14 (4*parent+1)
    let a := op % 16
    let b := (op >>> 4) % 16
    let rm := (if keep % 2=0 then 1 <<< a else 0) ||| (if keep/2=0 then 1 <<< b else 0)
    ((old ^^^ (old &&& rm)) ||| 1024)
  else
    let w := packedAt q13g (((r >>> 12) % 1)*6) 6
    let n := w >>> 0
    if p % 4=2 then n else packedAt q13p ((w % 1)*9) (n*9)
def orfl13 : Packing := (31,2,7,0,250,0,0,orfd13)
def q12pb (i : Nat) : Nat := 0x91a000a800fefef8e0fce0c080c0800000094a52fa50e0f080f0e08080fefe80c0ff90e940c0c0f0f8003dcd6b38e9548d22409400b51248ea509540c0a554f8000000a5
def q12ph (i : Nat) : Nat := 0x7620798206608577e0d9f0357a055e8157a0d1e014780cdd8137604dd83174045d03072041c810720bdc02e6e039b80e6e0b5b00d6c035b02c6a031a80c6a031a80c6a02da80b6a02da80b6a2ad80595c06570385a0dd6036560d55015540d148145204d4813520494831500c1382f4c0b9280e4a039280d4a035282c48031200c480ad180b4602d184842110f8043e08cf0033c00cf0033c088e8023a084e00138004e00138004e00138080d80036000d8a02c154a0712213c78691811850441008c38030e10428010a00428200820000
def q12r (i : Nat) : Nat := 0x3846cccc18332a738e69b2386708e09b23806f8de18d7666acd218873060ce71b0352684e21933666accf998306650e71cd3846fcd81be31e684c39cd386648e09c03546fcd49be34e6f4e2193378634d59a433e66ccc19439c734e19c2376700c89b137e6c0df18f35c684c39cd3826c8df9a937c63cdb1ae34e6f4d69c43266accf99b33060cca1ce39a6fcdf18f36c62cdd9ba3646c4d51b63166b8d39a130e6b4d01cd3826c8e01913726c4d51bf35268cde9ad340670e2193356690c419f328738e69c03226e4c61bf346734e1992398708dd9c03226e4c61b13926fcdc1b03466f8c79b63166b8d098733a718e19c2376700dc9b13926bcdf1b635c684c39c637a6d4d69a032e6f0d99a433070ce61c2376704dd1b23806e4c61b1354724d79a83446d8d39a137a6d4c51ad34c680c319932e714de18d3666acd2188336654c09ce386730e11bb3826e8d91c0372630d89aa3926dcd79a83446f8db18b35c69cd0987334718da9ad340664cb9bc366690cd99809a3084284e09a5106084a18412c268c318412c6084a1802fc8804817c214270c318412c600be2784cc92118096120a208909c1346104b17e440240be2884cc8c11409a30c9d8c1164128600bf2201205f0bd2884f02704d186308258c017e440240be14e5109e13309a304250bf2201205f0bd25a310a209325626c4004e09a2fc8804817c5108d91822830c6104b182128600be17a1346084a1802fc8804817a4b4621442564902704d1802fc880482884908a04d1861306104b1801245f9100902f82313d25a4808e11709a30c260c2096300550491502f8230bd14c1149613309c1346184c18412c6084a1801249112108c2f44c89708a4d0961251884f09992b508138268c3098308258c10943002492217c1189009908a4d0929161884f09992b24846c8c04e30260ce69c2364704d91c13646c8d81a9378634d99ab348620cf998306738e69c3324708dd9c13746c8e0191372630d89aa37e6e0d81a93466f8c79b63166b8d39a130e674c998d31060ce09b237c6d8c59ae34e718de9b53146b4d31a030c65cc11c539a70cc91cc3846ece09ba364700c89b93186c4d51c937e6e0d81a93466bcd41b634e674de98e36a628d69a6340618ce19738a64cde18d3666acd218833e66cca98139c704d91a837c6d8c59ae34e668e31bd36a628d69a6340618cc9973047150f8444821110821047a1100984406607d0a0440261102201308886d1ea44026110098440560900f81407a04d2212b93e47c8aa8509c1346104b09413826ac14941346084a62612c2524850a138268c3098308258c1094300248bf6201205f046126a1126a4a48ca7122a4d498b0925a4a492c412432263cc3d90b1d48caf54ca9748acf18fa8449c1346084a08e2f8232bd5321150fa13
def q12t0 (i : Nat) : Nat := 0x2aaa66889de66956448ce228459a6619765995651926458a61d866158460d82605805e9765d5745cd725c5705a96559163589615815a551535495152943509414e9324c52a485204690a26898254942489122885208811a85a148511283a0a8210680a
def q12g (i : Nat) : Nat := 0x35699de7e600
def q12p (i : Nat) : Nat := 0xf17b666010c3b001d6f47d0f41a06318adf97ddf57cdf17c59161d53544a126c8720c8f16c5915c55144530039ae1b82e037edab68d9b64d8360c82baa6296a5292a42988c238892208a2148421c8220480200731a8691a0689906798c62988619846098062104401003f0e8390e0380c02408a1a06619062180601282609022080200700801000007b1e8791e2775dcf71de765d8f61d8f51d6f47d1743d0741c8711bc6d1b06b5a8ea1a8691a0661946418c62184e01835fb7e5f77d5f37c5f3785eb75dd574dd1745b564d9165583605815c56b55d5554d5151d354cd314c52144505384e1344c92d4b32c4b12a49524c9126c8721483204811bc5d16c5915c5514c51144410d4230842106c0901c0500c01003f0f83d4f0bc0f03b8e83a2e439ae2386e1382e0384dcb70dfb6cdab68d9b64d8b60d8340cc320c42f0b82d0b02b0ab29aa6296a5292a4290a0270942488d2308e22488228852108720881200801f07a1c0701bc6a1a4681a8651926419e6318a6218661182601805c160541404c12046104401003f0e8390e0380d0300b02a09424890240801f06a1a0661906218060160401003c0a82809824088200801c020040000
def orfd12 (p : Nat) : Nat :=
  let j := p/4
  let r := packedAt q12r (j*11) 11
  let h := packedAt q12ph ((j/8)*18) 18
  let pw := h >>> 15
  let parent := ((h >>> 10)%32) + packedAt q12pb ((h % 1024)+(j % 8)*pw) pw
  let op := (packedAt q12t0 (((r >>> 0) % 128)*10) 10)
  let keep := ((r >>> 7) % 4)
  if p % 4=0 then (orfd13 (4*parent)) ||| (op <<< 20) else if p % 4=1 then
    let old := orfd13 (4*parent+1)
    let a := op % 16
    let b := (op >>> 4) % 16
    let rm := (if keep % 2=0 then 1 <<< a else 0) ||| (if keep/2=0 then 1 <<< b else 0)
    ((old ^^^ (old &&& rm)) ||| 2048)
  else
    let w := packedAt q12g (((r >>> 9) % 4)*17) 17
    let n := w >>> 9
    if p % 4=2 then n else packedAt q12p ((w % 512)*10) (n*10)
def orfl12 : Packing := (740,3,7,0,250,0,0,orfd12)
def q11pb (i : Nat) : Nat := (if i<1 then 0xf54088882220b12000aa50880000950080b1b2009400e0ea50c08d2200e0a554a550feaa50ffa0a940f0a900a5408080f880c080fcf0c0fe92484088822210ff94fcd9b690f0fcc0aa40b6a490ffa0e080a540f550a500aa422220ea80fcfaa8e0a400c0fea8f950fa5080ff00ba985520fd408000e940f400fef8c080fcaa949550a940fce9cc518820d2248090800080bb43111086643200e000fb68488d924080b64920d5409550a400f8c0fffcc000ff6b00e0b246c09540a800e0feaa94fc808c800086442220fa80ddd51100fa00c089224088888420aa0080aaa0aa80f0e0f0fcf8aa8088644000a800a000f8a000e0f8f08080fca500e0fffff220a699e69a4040f540e554a940fef8aa5480c3321100d500a950fca550aa509554f0a540aaa4809500f8fef89554fcf880f0f0a500f8c00000097a5d9765c96e5b9842100091a24895408da248a554b6d848fe908db440f23688b1b6c896644110ff50db6b608db6d08d1200a900809400ad2448a7544310fe94fa36d0cdb440b23488a550d64648d5b688b1a4889500924680e950a950e500b6491887663210b6d888eed775308097766430c0e540f900fea08d2490aa8610009999986092324088886100dad6c0fefa90c92240ea90fcaa5080923440a554e0eaa09554fca550e950a55480c0f8f0912248f88080809540c0e0fcaa54e9549554f8c0f08080f8fd50a954fcf09550f8f0fee0aa54e954fec0aa948da200f0c0e09400f8e0fef0fcc0f8a950e540e0a5509540fcf880c0c0c0fcfef0fcfcaaa8e9508080940080f0e0f0feff54f950e0fcc0fefefc80c0f0e08080e0fd5095409550f0fec080f8fcfe80c0f8f0f0c0f8f0f08db680ada4488880009554fcf8fcfcfce0fcaa809500e080f0c0f0c0f8c080f8f8e0fcf8fcfec0f0c0e0c0fcfef0e500f8e0e080fe80c0a954fcf0aaa0a954c0f8fca5549554fef8e0fcf8c0a954f080e0f0fcf0fec0f0f0fcfef0fcfc8080fcf8f8fe80e0f0fea5009554f0c0fc80c0f8fcc0c0fefcc0e0f8ffffd0feaaa4fca5008c92409550f0fc80f8f0a400c0f09400fefee099999920adb6d0b08000c09540fcfa8080f880e0fcc0fef0d000e0e0a540f954e0f8c0e0fcfcfef0fcf8e0f0fefcffd480f880fef8007479dcde3efb77b5877642109ca0e730609b12631420a89240eeb166184085432200db9542108607de3440c09636da1c4080eedc8610ad2248977211009248d091b248b646d095508d2248898c200000eedca92088888880fa46d092484087655550920000db5ad0fab640b1a448c0fe3488ea94e09500fe94ea94c0a940ea909554fefefcf8ff9200dad8d0fd40911240f0fef895409550a950f0fe808080e0f500f0fe94a550f0f0e09554fcf0c0c0f8fcf0f88080f8fa94c0e0c0f8aa40bec6d1407080d6a55440a000 else 0xffb77500c0a540e0c0f8bbbb544091a440a950fe90aa90)
def q11ph (i : Nat) : Nat := (if i<1 then 0x4a180264a181260a10125ca08025ca08025ca081258a000258a0012549f802549f812509f002509f0124c9e8024c9e8024c9e812489e002489e012449d812409d002409d0123c9c8023c9c8023c9c812389c002389c012349b802349b802349b802309b802309b8122c9b0022c9b0022c9b002289b002289b002289b012249a802249a802249a802249a802209a802209a8121c9a0021c9a012189980218998121499002149900214990121098802109880210988120c980020c980020c980020c9801208978220096821f895801f895811f095011ec94811e894001e894011e493811e093011dc92801dc92811d892001d892011d491801d491811d091001d091001cc91011c890811c490001c490001c490011c08f801c08f801c08f811bc8f011b88e801b88e8319c8d011988c821908b8118c8b0018c8b021848a001848a031748880174888216c87811688701164868016486801648681160860115c858115885001588502150840114c838114883001488302140820113c818013c818013c818113881001388101134808013480841107e830f47d030dc7b810d87b000d87b020d07a010cc79820bc78810b878010b477810b077000ac77010a876810a476000a476000a476010a0758109c750009c75010987480098748208c73810887300088730108472800847280084728207c7182070708106c700006c700006870010646f800646f810606f0105c6e8005c6e810546e000546e010506d8104c6d0004c6d0004c6d000486d000486d000486d010446c800446c810406c000406c000406c000406c000406c0103c6b8003c6b8003c6b8003c6b810386b000386b000386b010346a800346a810306a000306a000306a0102c698002c698002c698002c698002c698002c698202068810186801014678001467810106700010670100c668000c668000c668000c6681008660000866000086600008660900861846b85f8565c5d056045a835e059055685684540548450852864844f863ec4c843b44a8339449043684703358458334844033304282328418331840052d43d8429c3b8427c398325838032483684228348321033031f831831d830031c42e811bc2e0319c2c821902b8118c2b021842a02178290216c2801168278215c268215025821482481144240113c23811382301134228311821031001f820f01e830dc1d010d81c810d41c010d01b820c41a820b819820b018810ac18010a817800a817810a417010a0168109c1601098158208c14810841402078130206c12010681181064110106010820580f810540f010500e8104c0e010480d810440d010400c800400c8103c0c0003c0c010380b800380b810340b010300a8102c0a0002c0a0002c0a0201809010140881010080100c07810080700008070200006060d80306000000 else (if i<2 then 0x2915390390537828f936828ed35828e134838cd33048a531038912f848592d818552d048312b018252a82815298280928827f927837e926007e526047b92404795220378120847611e837451d0173d1c827311b837151a02709190170118826f917806f917816f517006f517036e515826d914816d514026c913026c112016bd11806bd11826b510826a50f8269d0e8069d0e816990e016950d806950d8168d0d016890c836750b016710a8166d0a016690981665090265d080065d08016590781655070065507016510682649058263d04826350381631030162d0281629020062902016250181621010161d0082610ff82604fe81600fe015fcfd805fcfd825f4fc805f4fc815ecfc005ecfc015e8fb815e4fb005e4fb015e0fa805e0fa825d8f9825c8f8815c4f8015c0f7825b8f6835a8f5015a0f481598f40158cf382584f28157cf201578f181574f101570f08156cf00056cf001568ef80568ef81564ef00564ef0255cee02550ed0054ced00548ed00548ed01540ec82538eb82530ea81528ea01524e981520e90151ce881518e801514e781510e700510e70150ce68050ce681508e600508e601504e581500e500500e5024f8e4024e8e3014e4e2814e0e2024d8e1014d4e0814d0e0014ccdf814c8df014c4de804c4de804c0de804bcde824b0dd824a4dc814a0dc01498db80498db80494db81490db0148cda81488da00488da00484da01480d980480d980480d98047cd98047cd980478d981474d900474d901470d880470d88146cd801468d780468d780464d780464d781460d700460d700460d70145cd681458d600458d600458d60244cd502444d402438d301434d281430d200430d20142cd181428d101424d080424d081420d00141ccf8041ccf81418cf00418cf01414ce80414ce80410ce80410ce8140cce01408cd80408cd80408cd80404cd80404cd81400cd00400cd013fccc813f8cc003f8cc013f4cb803f4cb803f4cb813f0cb003f0cb033e0c9833ccc8033bcc6823b4c5813b0c5013acc4813a8c4013a4c3813a0c3003a0c30139cc281398c200398c200398c202390c102388c001384bf81380bf01378be81374be01370bd8136cbd01368bc81364bc01360bb8135cbb01358ba81354ba0134cb981348b900348b901344b881340b800340b800340b80133cb781338b700338b700334b700334b701330b68132cb60032cb600328b601324b581320b500320b50131cb48031cb481318b400318b40230cb301304b2812fcb2012f8b1812f4b1002f0b1012e8b0802e8b0812e4b0012e0af822d8ae802d8ae812d4ae012d0ad822c8ac822c0ab812bcab012b4aa812b0aa022a8a9002a8a9022a0a80129ca781298a701294a681290a60128ca581288a50227ca401278a381274a301270a28126ca20026ca201264a18026 else 0xb820b84b260981b1e0902b120800b120801b0e0781b0a0701b060684ada0483aca0302abe0202ab20102aa60002a99ff04a75fd03a61fb82a55fa83a39f902a31f801a2df783a19f602a11f501a0df480a0df480a0df482a01f3819edf3039ddf1819d5f1029cdf0029c5ef019c1ee829b9ed829adec829a5eb819a1eb02999ea00995ea02989e900985e901981e88197de801979e781975e70196de681969e600969e601965e581961e50195de481959e403949e284929e082919df81915df038f9dd818f1dd018eddc818e9dc028dddb038c5d9828b9d8808b1d8818add8018a9d7828a1d682895d58288dd48088dd484865d282859d181855d102845d001841cf82839ce81835ce02829cd00829cd0281dcc02811cb0180dca82801c9847d1c7827c5c6827bdc5827b1c4827a5c38179dc30079dc300795c301791c28178dc201789c181785c100785c10277dc002775bf02769be01765bd80765bd856f1bb036d5b9836c1b8016bdb784691b584665b382659b28363db10362daf8062daf81625af03611ad82601ac825f9ab825f1aa815e9aa015e5a9825d5a8825c1a7835a5a6015a1a58358da40058da402585a30257da201579a181575a10256da00056da0015699f805699f805699f805699f815659f005659f035499d845259b825199a844e598824d197814cd97034bd958449d9382495928049592814919202489910048991004859100481910247990014758f814718f0146d8e814658e014618d824598c804598c844398a824318980431898042d89824258880425888142188024198700419870141586814118600411860140d8581409850040985014058481401840040184003fd84023f583003f583013f182843b580863097d822fd7c802fd7c822f17b802f17b802f17b822e97a812e57a012e179822d978802d978802d978802d978812d178042a176002a176002a17602295750228d7401285738227d7282275718226d7081269700225d6f0025d6f0025d6f0025d6f022556e002556e012516d8024d6d8024d6d822456c812416c002416c0123d6b812396b022316a0122d698122969012256881221680121d67822156681211660120d658a20d6084b515e83b3d5d02b355c03b115a82b095983af15802ae15703acd5583ab15403a9d5284a655082a554f83a3d4e03a2d4c83a194b02a0d4a01a094982a0148839e947049bd45029b14403995428397d41039693f829613e839493d039313b8391d3a))
def q11r (i : Nat) : Nat := (if i<7 then (if i<3 then (if i<1 then 0x14501c26326018602a60245f1e607a603a633060245d00890063126001251860145d0c890063006202d213180e5d00d1146304d50a6002d11c62206004d30918265d04d120631e5f1c5d014f01341c601c5d285f245d02890063125f0125145d0a89006318620d18205d04d120811c635c605c5f3c6324601e5f0c60014f01340125285f245d0289006301340c5d0e890063006202d602d304d217180e5d006202d604d213180e5d02d808a9166304d3006202d602d302d20b180e5d086320611e601e5e1a5d1e5b2289146316611660165e165b014f0334012518611860185e185b072200630125011f0b4536ae0f2e13250f211e8916630e621c60105f00630e6220d51a60249d10630c621ed50e6028d4225f246024601e5f4d1d3260325f014e0344053b01331c60145f145d014f013400ae7ca9012578a1989f011f134f0b45133444ae0f2e0f253a89211d1663126228611e891d1d16630e6228d616611a600e6222d6126122d512602260285f3a89211d16630e621ed4165f1e611860185f185e131d0e630e622ed6149a206128d51e6020d41e5f2ed31899205e086222d612611ed5106016d40e5f22d3165e271c2e612260285f285e225d30891d1d14630e621ed4165f28d31a5e1ad22118165d20611c601c5e145d1c5b1d4f15451d34152e1d25206242614260425e66d1425b4f3426624a6026624a614a604a5f206120601c5f205b20624a614a604a5f4a5e21324a5b62ae41212a62509d5a6124625a612a626c6148d55a602a626c614a606c5f4a875885266200d65a6108d53c605a5f0e994a5e26625a6148d54a605a5f4a5e5b1c4e624260625f0318425d5b1d2c625c615c605c5f5c5e0b4a64d65861585f585e51316b346b213661365f425d172c10902463586114d54260585f485e0f3124622a612a5f2a5e2518205d3331252c7e617e606c5f7e5e7e5d0b2b4e5b02896485009d4e636262505f765e0318625d551609470d2a5b1d2462426104d54260365f365e0d18505d0b311d2c06d0153e033424632a627e6158d55a606c5f6c5e5b18545d51315d2c59173530592b245b349c5487468540626e5f0318905d072c6a5b06c700a67a5a009c028778635a6142605a5f5a5e0531285b02a65a5a50625e6142605a5f5e5e6130245b50a35a5a4b4481346d212062426134d52660425f345e2718265d2531272c491735302b2b42d02aa634a3345a4f4f36a94c9d0a630a6218d5126016d40e5f1a601e5f0e630a621ed61a6116d512601ed4165f189c349d206120601a5f1a5c1c5b609d0c632c622c61346036d4265f4ed12c5b37475f34609d24630a621ed6166118d5146016d4125f20d31a5e35310e5c1ed1185b189c34870f831dc323bc23a12846361c2c1c1a2e262e221d261d222e262e261c4c313e2c5a26262e225f2c63 else (if i<2 then 0x139913cb0b9317c207ba0fde0fd219ca17c11db90bb20dc00fb803d005be05af0faa1fd80b9c0dcf0f950fc50fbc05b40f8d07ae0fa9039d0de361e27fd6899a9be161d59bcd7fd49bcc9bc37fd389999bcb89939bc29bba77de8fd28fca81c19bb97fb259c091b889c88fb78fab799c9b959b8d899d0be217d417c31bd21bb90bb80dc809b70fab1bd00f9609be0bb605af0f8a13aa0fa311da059c27bc13ae21a923a10d8311e317e111cd17cc17c317cb099311c20dba17de09c80fb711c7119109be11b607af178a0da317da9bd6abe19bd5abcd9bd4abccabc39bd3a7cba993abc2abba9bdea5c8abb79bd0a9c7abbeabb6abaf99ce8bbb8bb361e279d6a79aa7e16dd5a7cd7fd4a7cca7c37fd39999a7cba793a7c2a7ba89de8fd29fca93c1a7b99fb27fc0a1b873c8a1b775ab7fd09996a1c7a791a1bea7b6a7afa78a9faa8fa389da9dcfa9959bc5a9bc99b4a98d75ae9ba989a1a583898d898585d5a3c385c36bc085b885cfa1955fc575bc77b4a18d75a1a1835be385d685d58dcd8bd4a3cc97c361c987c097b88995a38d99838de18dcd85cc85c38dc985c085b89fc8759287bf85b78da775db75cfa19577c571bc89b4a18d75a5898565e34fd675e163d599cd43d499cc99c34fd399c299ba43d189c8899299bf89b789b0758b63db63c789be89af75cf619589c575bc89b4998d75a54f854fe385d673e185d5a1cd75d497cc97c389d3a1cb6193a3c289ba61c987c087b861b183d175c88992a3bf89b789b0758b61a775db8995a38d8985002e001f082e002e301c0018061802180418042904181e1c0057083c042e0c592c1c081804510058082e221c0218082e221c0418022e001d001d1e1c001d00189c1b8a570828102e10250058041f082e261c06180058042e1e1c00180058082e0e59261c081800530058042e0e21001d001d001d0e1c001d1e181e582658121c1e582658002e002e3e1d0c313e1d122608590229002e005800580058082d32292a1f0608222e065810589c4e0405a233000804088e240008002e001f262e7e562258181c7e5326580e1c0e581245123c082e0a2912250a1f2258121c5c5628580a1c325518585c5328580a1c30181c187e512658121c1658181f1e5826580e1c1658123c0a2e2029201f5c5128580e1c18182058321f20581a3c402920582a1f10450e290e291058104f1045103c10340e29142a022e6e56021d082506580c45083c0c2e0229042508210459041c5e1d321c102c081c02186417042504580445042e022902250459001d0858022906250a50082654502a262423041c0a030a3c0c2e022904236220044f0645063c0434062e02292c0608291258601d2058125818581e581651321d26581258124520291c581e582658781d125814292a1d362620580e58124f1045123c12340a29 else 0x39201bf01b0018b01c301cb01c201ba01b901b207be07af07aa29bc29b4058d29ae07e301cb01cb019301b209b4038d0dae03e305e20bd6099a0bd30d9901cb019311d201ca01b203e209d6079a11d201ca0bd8079c01cf019501ae01a9019f01e301cb019301e205d6039a05d3059901cb01930bd201ca01b201cf03b48de18dcd8dcb799385c28dde83ca83c183b29fc88d9287bf798b93ab75db8bcf999589c59fb4a18d91ae9fa5a7857de301e101cd01cb019301c201de01c8059203bf01b0038b01db03e101cd01cb019301c203de01c8059201bf01b0038b05db039517c517b4058d17a5078501e38b8599e201c31bc519a50d8519a107e3a1d5a185a3d59fc395c309c323ce079423c423bb23b3078c01c301c101b905cf059505c50bbc03b4098d0bae05a903a50b8503a1059f8b958b8d8b858d9d89c58bbc9fb4a18d9dae9fa5a785a59d97e399e2a39d97959b9d99e2a7d6a79a99e29dd699d5a9cd8dcd85cc85c39fcf999589c58bbc9dae89a5a785a59d8be399e29dd497c3899d8dcd95cc95c38dcb7b9395c295ba9fd6a1d59fcda1d4a1cc9fc39fd39fcb8d93a1c29fba9bd69bd5a9cda3d4a3cca3c39bd3a9cb8d93a9c2a3ba85cd85cc85c38dcb799385c285ba83ca71c183b971b29fcf999589c58bbc89b4a18d9daea59d81e399e29dd497c3a7d3a599a9cb7b9397c2a3baa7d293b9a7b29d9d97cd9bcb799397c29bc89b9297bf8bb08d8b9bcfa9c59bb49ba58dd699d5a9cd7bd3a5cb8b93a9c28dd19bc8a592a9bf9bb09b8b93d593d693d59fcd93d49fcc9fc38b958b8d8b830de109cd09cc09c309c207ba0dc8099209bf07b70db0078b09db07c703be03af93d695e193d59fcd93d49fcc9fc379d39fcb7b939fc29fba93d17bc88f929fbf9fb78fb08f8b95db8b958b8d8b85a395a38d9b8361e2919c9d8d9b839d9d15e151e261d6899a9be161e265d661d59bcd61e27fd6899a9be161d59bcd7fd49bcc9bc37f9c9d959b837f9d0bd611e109d509cd13d417cc13c313d311cb09930bc207ba0bde65d69be161d59bcd77d49bcc9bc377d39bcb8f939bc29bba77de07e205d515d419c307d20fc11db919d9039d19d61be10fd50bcd19d419cc19c315d311cb099319c20fba15dea7e1abccabcba993abba9bde13e10fcc13ca0dc11db90dc013b81fd80d9c09cf15950dc50fbc07ae0ba907e315e115cd1fcc1bc315cb0b9315c20fba0fde51e27dd6899a9be17dd49bcc7dd375999bcb8f939bba7dde7dd28fca9bb97db29bb81be10fcd0fcc17c313cb09930bc20bba17de13ca13c113b90db211c007b807c809b705ab1bcf09950bc529bc23b4058d2dae1fd9039d0be307e215d419c315d30b9913cb079317c209ba17de07d221b90fb209be05af07aa23d9059d09e209d6159a17e105d50fcd0fd415cc17c30fd3)) else (if i<5 then (if i<4 then 0x785f785e1718785d0f310f2c9d170b2b6a5b1ad02eaf12a60ea3785a031b194e1b44129c154f11451290153c9887046388628861765f0b18765d132ca9170b2b8e5b08d00aa608a3885a011b074e213b8ab3054f053c052903217e610ad57e607e5f7e5e073107306a5b12d004a60aa37e5a074e0f141144113b17330b0c8e628e618e5f8e5e14d012a38e5a154e1f3c00638e6288610ad58860785f885e1718885d09310f2ca7170730132b7c5b10d014a6885a051b194e233b172d154f0f45193c19340263766262610ad56260605e1118625d0b31152c9b170930132b8e5b3b471b23051b074e13441d0c092d8aa0014f0545013403298862766104d56260765f765e0b18505d0331052c8f170130032b605b06d00aa602a3625a011b074ea7149944993b8933990c092d912899208902074f0545053c0534012903215ad5969d5c6396628b5884d59660714073455e6368d656d5826054d4825f5863766292d4765f82d19ed88558989c74879063766283585f299121966276d676d4a25f7ec08358966270d66ad598608b4360b884d18f487558634f774584638cd666d5626076d4625f414077485f4f5f45733c5e6374628cd678618cd4785f83517548a137612766d68a6154d58a6054d4865f60d360d1825b8a9d4e63826278d692616ed592608ecc985f66d38e5c66d188c8925b82d092d88358968f8263606264d5626062d3625c62d1745b85586f458d344f297525966284d69861894d66d48ec3985f70d3985c84d188bf8c5b80d07f58654f8463966284d6966184d5a26084d3a25c84d188b7a25b8f477558774f77458a627cd4985f8c5c8ad1985b8cd089478b3e9ed88b58773c88a99c9d4e638c628c5c8cd19a5b7f584f2991258cd6626178d5626078d4505f8cd34f49634037384f318cd134a7505b61475f4f5f455f3c5f344e63906290d6986180d5986080d4985f90d39931985c8cd18f379c5b8cd08b3e60a661269ed87558654f7745773c79345f298063606262d6626162d37531625c6f584f4f83344f2978628cd67a618cd57a608cd37a5e99317c5c78d17a5b83509147a13ea12f41269d2305c39dcfab95a7c5a7b4ab8da7a5ab857de301c101b929c529ae29a505850de301b001c1038b0bc50fae0fa5078503e305e211d20bd10f97038b09d8079c01ae03a50185019f01e301b0038b05e20fd505d30b9919d207c107d10f9703b0098b0bc50fb405a501b901c201c101bf038b01c303b901c801bf01b707be29bc29ae29a5058509e301c303c801bf01b701be01c803920fae0fa5058505e305e211d205d1099701c8039201ae03a5078503e30fcd0fcc13c313c20fba09c8139215bf05b70f8b23cf0f9523c523bc29b4158d23a50d850be305cd03cc03c305c205ba03c8059203bf03b7058b05be05af01cd01c201c8 else 0x863a6629c619c603ab79c5b5d472758174f1b459262845f845b3f3e2758173c0cae20a908639e628c5b21580925a6629c619c609c5f0d325d379c5b4d3e06aa2758114f1745173c15340863906284610d321158014f0334786278617860785e0732785b93509f3e852f9f238e62128998850a9d026307450b3407250521a6627f56031d066210d6129a606110890063a6629a6109580b1d06638e621ed67e6110d57e601e89a485129d0263a6620ad59a601558a6629a61254d1158114f8e6226d67e6112d57e607e5f1a89a485109d02638861885f074f073c05250121a6629a613acd9a609a5f1958091d0463886205580129012501210759a6629a61314d9a5f0f58114fa6629a619a60294c3b434b4b1958114f1745051d046388627e617e5f7f539b4b9b3a0b1d8e610cd58e608e5f8e5e8c610ad58c608c5f8c5e0b1d7e617e5f7e5e9a610cd59a609a5e80618060805f6c5e051d4e625a610d4d5a5f5a5ea6629a6108d59a60294c9a5e19400945071d046390626c616c5f8e5e07186a5d072c1e8700639e628e613aba8e5e0d188e5d14b815310f2c0d48094f04638e618e5f8e5e093107480f37126216d60e9a7e6106d5646016d47e5f1ed30a997e5e14d20b18625d0b31132c03306a5b128998850c9d026388611cd58860885e15310f30765b034f0745013405259e6208d58e603ccc9a5f8e5e09188e5d09310d2ca51716c80d30112b8e5b11581c8f0b1d0463886212d58a609a5e13188e5d0931092ca9170930152b8e5b0558014501340129012505599e628e61294d28c38e5f8e5e07188e5d13310d2c072b08d005580d4f051d0463a6629a610cd59a609a5e0d189a5d0f31112cab1722b70b301b2b9a5b31471558114f1145a6629a619a609a5f253a9a5e07189a5d0331092cab17092b8e5b06d02947253e1558094f0d45093c18a90aa5189d011d00639e629a6117189a5d112cab17192b8e5b0758054f012903251359806106d58060805f805e09310d307c5b06d0051d8e628e618e5f8e5e03188e5d0731072c05480337032b04d000a6094f093c086388627e6112d57e607e5e1118645d1531152c8f170d30152b765b6550913e9b2f7f2a7d23091d06d6506106d4505f06d3505e0331033000d000a602a3505a054f113c113405219062886110d58860885f885e0f18885d05310d2ca7170330152b8e5b1ed01ec706a612a3885a011b169c22870663a66208d59a609a5e0b189a5d05310f2ca517a4c809300f2b9a5b06d008a608a39a5a8ace094505340b29052182627861785f785e13186c5d18c00f31112c112b10d01abe06a608a3785a0b4e0f4f02638e62886108d5886022ba885e1918885d22b80b31112ca7170930112b7e5b10d02eb608a608a3885a031b114e1b44169c154f1145a4871e830863826278618860) else (if i<6 then 0x94f074509340063006204d6906102d5906006d4905f0ad3905e0f3106d1905b12a6905a154627350b2216d8074f0345053c0b340b290063006200d6406100d5406002d3405e0b3102d1405b752f0b460922014f014501340125013472628a89726310d5026300621b5872d5706384629f58825f70609260905f945d228f2e8902639e60a65da4ce0345013401258a5f945d194e03143889388502639260945d194e1f4417452e8900639060985f9a5d1f4e011419441f3b388902639e5fa65d034e053ba4b3014f053c01259a609a5f1f4e03141f441f3b1f33050c8e60985f9a5d234e031417441f3b2333030c1f2d22882e890063a65fa65d054e053b0333092d0a88a4a4014f053c01348c607c5f7c5d034e01140344033b0333010c032d048803240104014f0345053c01341eae16a9012512a1169f071f86628a899b1d86638b458d347d25726252d6909a9a618a89791d7263a06280d68b58a69c8b1d8c63866258d6a0615ad5a06090895e63966284d596609f58966284d69661874d9f587d4f806264d6909a50d5a06054d4a65f8a899b1d86638ad68ad4a45f974f973c8f258c628cd678d58acda860a85f8cd39ed89f588d1d806364629f585f297525611f966284d6894d84d4a25f9f58734f966284d670d5a260894c8b4384d38f4b8b587d4f7d4584637ad6a6617ad5a66082d4a65f82d3a65e92d682d5a660a65f70d38d1d82d6a06182d4a05f70d370d6946182d5946082d3945e70d670d5a66082d4a65f92d38d1d746268d6909aa66156d5a06054d4a65f60d38899a65e7ed29d189a5d8a899b1d6a6390d6a66190d4a65f90d3a65e754f973c8b348e6276d68cd58acd9860985f9ed3985e92d29118985d82d19ed89f58989c9887989f751d74638c628cd39c5e8cd29d18a65d9f588d345f29511f966276d6a26176d4a25f76d3965e92d29f18a85d9f58614f966270d696616ad596608b437cd38eba965e92d29d18a25d84d18f489f58634f7d457c639a619a5f9a5d8b58614f73459690633c86637c628cd69c6176d48e5f8cd29d189c5d9f588d4f713c5f29511f92d6a66182d5a66092d4a65f82d3a65e92d18d1d9ad6a46198d5a4609ad3a45e9ad1a45b8b4f8b458b348b258c627ad5a2608cd3a25e8cd29f18a85d8cd19ac8a25b9b5887458d3475297525751f8c628cd6a2618cd29f18a85d8cd1a25b9b588d4f75297525751f8c628cd69c618cd39c5e8cd29d18a65d9b58754f7b345f29611f0663a662275826d59260925f02639062825f255818d908639e6217580921a6629c5f2158a6629c604d434b482558154f1b450c6392629261925f93517b489f378461846026d4845f26d1845b04639e6292605ccc9c5f925b27581e8f08639e6284608c5b1f58054505340525a6629c61474d58c39c5f3abf9c5b2758174f else 0x6200d65c6100d55c6002d374ba5c5e60b800d15c5b953d8a85049d00635062889c609d7e6150627ed660617e617e608885029d006350628ed6766176d562608e617e608e5f8a85069d006350628ed6766162607ed4765f769c88878885609d98620ed698618860985f0b4b985e0e9f049d886302620cd6626162600cd4625f0b4204b1153118d80690129f5e6350627cd640617cd4405f7cd3405e75318e617e608e5f8e5e0730605b7685049d00637662986176600ad4985f985e19304e5b05470734129f18d9069d8863026208d6626108d562600ad4625f0ed3625e1d3106d0033e12a6052616d805340e9f5e6350628ed6766176d562607ed4765f8ed3765e89316130405b4e9c748788854e9d886206d4485f485b0ad002c702a602a3585a04620ed63c611ad43c5f0ad302c23c5e00c00731033004d000be04a602a33c5a02637e6216d6526108d5526008ba525e10b809310730545b0ad018b608a60aa3525a0d450a638e618e5f8e5e10a60ea38e5a0063006204d4905f905b06d00ac708a6905a0d3510d8049c1c870063006204d6606104d4605f08d3605e0ac009310b3004d008be06a6605a0b461b350063006202d65e6102d55e6004d30aba5e5e06b80f315e5b04d008b608a608a3765a0946173d029c054f03459c87048300639861985f985e89308b468b35a54e993b99338934006200d6506100d5426000d4505f00d3505e0331733000d004a672a3425a03466f3d7735014f0145013c0134012901218a83089d00635262889c609d7a618c83029d006352628cd67661686052627ad662617ad5626074617460625f7483089d006352628cd676617ad5766068d4625f769c98878a83609d74621ed6746110d57460745f1b4b745e20d90c9d88638c618c607a5f8c5e8a83049d006352628cd676617ad5766068d4625f76d3765e7531749c609d066212d676610cd5766012d4765f0ed3133a765e1d310ed112b0765b1ed834a99063746274617460745e12d1745b1d2f11347263746278d6626178d5626078d3625e893178d1625b9a6264617a607a5f12d30acb7a5e133122d17a5b04c7192f06a6785a0e8764839a63066212d64e6118d54e6018d302ba4e5e02b8193118d14e5b0b2f1f4f04620ed64e6102d54e6016d4465f12d34e5e053101303a5b052f04a600a3385a0ad8114f0b3c528362638e618e608e5e8e5b192f07220063006208d608d58260905f0ad3825e153106d1825b0f2f14a6134609350f2212d8069c068f20870063006204d67a6104d47a5f04d37a5e0f3102d17a5b0b2f14a67a5a154621350322049c054f9a870063006204d67a6106d57a600ad37a5e0f310ad17a5b0d461522054f0345006206d4905f08d1905b14a6905a152216d8053c00630ad67a6108d57a600ed37a5e093104d17a5b15460322))) else (if i<10 then (if i<8 then 0x98639e5f9e5d233e22890263066210d49e5f1ad21f189e5d0ed1049726890263985f985d173e072e0125006202d600d5626002d302d20518765d00d11ab70b58029c0345128100639c62985f1d188a5d533e131b153b192d149c1c819c639862985f9ad0433e9ad72157193b20a80f2819240b040f25006200d4765f00d20318905d00d100d0993e0958009c013c01290e870125129f011f08ae012e03250263026278629b1c9a5d0c8910d9006302620ad219189e5d06d1069722890063006200d10063006200d600d203189c5d02d109480ad80958014f0063006204d1049d0063049d006370d6706070d684d5a0608460845f049d00637060705f049d006392600063013408ae032e01210959029d906280d5a2608e608e5f08891ad9069d0063905f0063006206d49e5f06d30299806290d4a85f9cd39d1c7e609a5d04899a85049d0063066214d6154d14d40cc3925f0ed314d21f189e5d0b3798639e5fa65d233e1a890263046210d49e5f16d304991ad21f189e5d26890063006204d600d5766002d302d20518945d06d10b5803450063006200d6766004d4625f02d20518765d04d0113e12d81158029c014f03450490013c1c810063006200d4805f00d300d201188e5d02d0993e0758069c013c0134011f033408ae012e088912d900630063006204d3049966628cd39b1c006206d3069908d217189e5d1e890063006200d600d305530519014b011300d2011800b2945d04d80958014f0ea90063006200d600d3034f034503340eae012e0325029d0a898aa10e9d00638c628c9c98818c610889069d00638c628cd68c618c618c600e899ea10e9d00638c628cd68c6176d58c608c9c9a878c618c608c5e0063026208d6029a7c6108d57c600ad302997c5e66629ad68c619ad58c609ad38c5e7d1c7a617a607a5e8c5d0e899ea10c9d00638c628cd68c6176d58c608cd38c5e8cd27d188c5d7a9c8881786254d6909a986160d5986054d38899985e82d29d18a25d54d19097985b90895463966282d6a2618b4d70d3965e92d29d18a85d82d18abf965b8f5874628ad6986184d5986062d38a5e92d28b18985d8ad1985b9ed89f58614588a99881606370d68c6182d58c6082d38c5e70d18c5b8e628ed69c6178d59c608ed39c5e90d29d18a65d78d19c5b9ed89f58734561347c6300636e62846100636e6280d68261846184600063026206d6766106d576600ad30b4b92636e6280d6826180d58260809c9c876e9d16d562608461846008ba845e14b800636e6280d6826180d5826080d374ba825e60b8909c869d6861686006ba685e0cb8685b006302620ad6766110d5766010d3765e10d1765b6e6280d6826180d5826080d374ba825e60b880d1825b746210b816d14a5b1ed010be14b64a5aa487006202d1825b06d008be825a9c870063 else (if i<9 then 0x1d00580045023c002900250021001f00590658001d8e53001d001d001d06310458001d0058004504290625001f0059001d065804300658001d005800290225001f0259001d08268e5088266023001d07220457085878460457984e04570a5808030858983004579833023c10290a58062302578a200a4f0845083c08340629032202578c5606580a5802580245023c002902250021001f0259045876530a580058001f005904580e3108580258003c04290421021f02598c5106260c570a580c570a580e570e5806570a5810d5114400d5034516ae01250121109f031f04ae012e012102621a890063006384d5a660006310898a830063786268d652600a890063786256d656d5a060565f7a607a5f1ad616d59e6012d49e5f1ad37ad668d5a26068d4a25f7ad3565f745d12d616d58a6012d4925f16d310d1194e1744193b193300d600d5746000d4565f00d300d20318685d00d1014f0145033c01341aae0ca90125129f0063006388d6886000638860006302d5926000d300d1006300d600d302d1006300d602d5766000d114a9006302d602d58e6002d30063a260a85f911c92609e5f925d168f2289026392600b189e5d1ad70d57091b054400628460705f0318945d0958029c01450ebc013c0125011f014508ae012e01250a89006368627a600063006204d58c6066627ad58c609b1c7a608c5d0a8910d90063026206d59e600ad219189e5d06d10897228900630062075500d2011800c1845d00d109580063006200d5906000d300d201189c5d00d11b510ad8095801340e9f0063006202d54e6002d300d1014f013408ae012e01250121029d068910d9049d006308620e9c086214d694627ad68b4d14c3705f06891ad9069d0063194d14c3925f0063006202d6009a1b4d02d41cc39e5f02d3826294d69b4d7ad4a0c3a85f86d39d1c154d14c3845f945d028910d9029d0063114d945d08890063046208d6029a08d48e5f10d312d21b188e5d08d1228922850263006214c37a5f0718845d1158029c088f0063006200d6994d00d498c3845f00d300d20318945d00d100d00958014f013c013401290125011f014f0145013404ae012e0125048912d9006304890063946282d6846008891ad9006392600063006202d602d59e6004d30299826294d694d5a86094d39f1c8460945d048910d90063046214d60ad58c600ad310d219189a5d10d19863046206d608d59e600ad3069910d21b189e5d08d106971a890063006202d5766002d20518945d0b580063006206d6114d02d302d20518945d02d110b70958034f006304ae012e012501210559029d886290d59860925f0063006204d48a5f7862a0d4985f8b1c9e609e5fa65d048910d9029d006362608a5d8e8d0489049d006304620cd6174d10d410c3925f153a10d225189e5d10d110bf else 0x5bcc67c35bcb4bba31cb49ba7fcb7fc26bde519959cb59ba49de59b931b261996dcb59de49ca5bb249cc43cb51ba31de45c353cb63e175cd89cb2be225d625d55bcd41d481c339d361996dc281ba47de47d245ca5bc181b94bb231c06db855b731ab25d03dd8a79c7fc57fbc7fb4818d7fae5ba959a559d98d9d67e33bc1659a6de17fcc5bcb4bba6dca81b94bb25bb849c791cd9dcb91c281ca6dc16bb259c0659a63e153cd91cc81c39bcb6dca5bc191b93dc06db849c855b73dab91cf9ba951a57b9a63e167ca3de15bcd5bcc67c36dcb5bc25bba29c73dbe2be235d6599a49e145d46bcc45d351997dcb6b936bba59de59d249ca6bb951b249d02faf479a61e153cd79cb3bca33c15be165cc51cb33c753cd55c379cb55ca55b953c791c265de6dc14bb281be7faf6daa899a7fe165cc65cb55ca65b93bc743cd77cb45ca43c7819a7fe153cd65cc67c365cb45ca65b945c78f9481954fe161cc51ca63b943b84fc861b743c76de143cd55cc55c365cb2dc765cb33c7899a7fe16dcd79cc7fc379cb55ca65b92dc743e143cd61cb43ca2dc143e151cd51cc51c363cb51ca51b925c70c080c08aa2410080008101f042e1058065812181e188a560418aa4e1e1826051e181e188a530418aa331e1818080a1898510808aa24081800080e1f0e570a57021c16570657040e001c0e57040e001c0857040ea8240058041f040e0457020e041c083c022e1255045804180418a85102590458021c0059022e021d001daa5604450059021d021d0843001c001d0218001d0c43001d0818101804180857001c9a4da84e0058081f021c021c022e0058001caa5302590e55025802180418aa510c3c04590058001c0058003c002e0629061f0059022e041d001d0218001d0418aa510a3412210059001d001d041818501018041808570e57041b021c0a571258001c061b0e57041b14280a58001c04570c28a8240058003c022e0629061f1c280a58025706280e00021c041f042e06180618aa5102590458061c00590258025800580058001f025800580058003c0229021f065004580c500658042e021d001d001daa530e210059001d001c001d1a530858001c04181e5028500858001c0a50085812180618085712570e570a58021c0457a83300580a2908570e58021c0e580657081c022ea85300590458041c005908530458001c042e061da6567821001d061d0658021c001d061da65340210a58001c001d02580245023c002e002900250021001f0a58001d16560a58001c16550a581a530a58001c0a18081d0618aa5178210858021c001d02588e21041f0a580a58001c0258023c002e0a297821061f1a510a58001c001d001d0658065806588053743a0658065808580258003c0829061f0059805104580658063a0a58063c0a588e56001d001d06580858)) else (if i<12 then (if i<11 then 0x3bca3bc15795658547cd798543cd2bcb4f8d43852fcd39cb39cd21cb4dc039c839bf21b063cd41cb77c051c877bf41b04fdb2fc82fc72fa339c82da339cd29cb3dc02bc839bf23b02bdb35e139cd51e145cd45cc45c3679541e14fcd61cc75c341cb4fcf2b9541c561bc61a54fa1899d35e341e14fcd4fcc4fc335c04fb827cf419541c52bbc41a927a12be335e135cd2bcc2bc341cb35c027b835b141c84f9541e14fcd41cc4fc361cb4fc835b035954fe14fcd4fcc4fc34fcb41c041b861b125cf41c535bc25b44fa925c325b825c81fb70fc721a619a331e12fcc25cb25b815b11bc71da639cd55cb3dc045b12bc82bb039c72ba62da36de167cc79cb37c72bc32bb82bb721c733a635a335e145cc39cb2bb825b11dc733a623cd1dcb31c02bb123c81db02ba623a32be139cd39cc3dc335cb31c02bb833b12bc82bb725b023c733a6658557e1679541e153cd45cc45c3679565854fe177cd89cc89c361cb75cf439561c54fbc61a5618589a153e341e147cd45cc45c353cb53c93bc047b841b167954fe151cd63cc77c363cb75c977c077b84fb161c8759277bf51b741b075a74fdb35cf75a935a54fe175cd51cb51c841b053cd69c345cb65c94fc029b833b133c865bf47b745b03fa757db33c73fa64da3698545cd2dcb33c957c02bb12bc853bf33b04fa73bdb29e12fcd27cc2fc341cb2bc921c01db81db121c82db71fb025a719c733a66be165cd79cb79c837b02fcd3dc339cb41c93bc031b82bb12fc839bf2fb72bb033a735db33a627a3558541e139cc39cb41c93db82bb12fc839b741a721c741a627a3679541cd35cb41c94bc035b135c845bf2bb041a735db5dc33db843c8539245bf4bb741a735db4fa635a345cb2db035e13dcd39cc4bc351cb41c94bc03db835b143c831b735b061a725c741a62be141cd2dcb35c93bc035b135c837bf2bb035a755c339b947b967c347b967c367c347b945c379c381c381bc5da179d679d4a1cc79d679d595cd79d149c891d89dcfa7c5a1b48f8da7a18fe37fcc67cd67cc67c367bf67b737d665d567cd65d495c347d345d18fbfa1b78fb059db33d05dd895c595bc87b4818d7fa57b857be38dbf67b071e19dcc87ba5fc8a1b795b069c7a1cfa7bca7a59dcd9dc281c89dbf95b06bdb87c34bc8599287bf67b73ddb71a555c8679255db79d687e179d5a1cd79d49dcca1c365d3a7cba1c295ba53d167c883b753d06bbe6baf93d87fcf9595a1c5a1bc87b4a18d79e37bcb67e167cd79cb3bc8559255bf55b067db51e251d667c363e189cc41e239d639d567cd65d481c341d37fd8a79ca7c5a7bca7ae7fa989a59da1a78389d9a79d8be3819a6de191cc81cd8fcba7cfa7c5a7ae9da99ba5519a6de155cc7fc363cb4bcd81c365cb81c26dba49de6de16dcc6dcb6dba91cd91cb91c265de31e14bcd else 0x25453e6344d4506250d640d440d375318a873e6344622cd644d36aba2ab875312b482b4f3e6335312b4f2b3c3e632c6220d546cc36d3413134c84130368f229f26d94e632529674d5ac32b4f66b75b47334f2b454f47334f3f4f252926d452d3434734622cd624d42cd36131254819373526214f333c2b347ed375314f303f3460c060b85914334f7747254f4462526244d6809c5263446244d5446246d6694d474f406252d644d58ccd34d364d836d954632b292b258d4d534f574c6943494b474f474544d544d6534d44d434d332632cd644d53b4c44d33b4033453e6340d62cd534d4554b214037383345213c3e63526244d652d57ccd62d3893144d162d8909ca287649f64d93e63346252d3893165343329446244d644d444d356c089313b4f52622cd636d57b4344d356ba2ab8893144d17d482b4f47453e63346236d62cd47d424eb141317d488d3f2cd83f4f53455690333c2cd96463414f2b2944d452d32c6242d642d442d361314ec83e63794d78bf334f34b0254f62d662d550d351402b3150d14f2f4f455f34346234d634d534d36131433e2b2f3526254f3f45253437c355c38bc337c38bc337c38b858b9577958b8583c563b46fa543cf35a55bcf43b455c371d571d285c187b06fd767c465d565d25dc179d159975fb053d0999c578529c147b051994bc15bb425b089e289e29fd65f954dba5dba2bba4db973957d9551e265d44fd23fb96fd153d0a99c5d9a5fba4db96b855dcd7f8573cd73c26fcd6fc24dcd4dc23fc189e28dd67bd569cd9bd3899969c29bd27bc17bd12fb061e255d565d24dc165d159975fbf5fb0598b61e265d665d365d265d16fc363c35dc34bc171b9739549cd3dc157c86b95739a73cc85b95fc85fb759cd59c36bb969c867c377c361b88bc877bf63b737cd37c1439727c837bf53cd77c377b953c8759ca3c389c897bf7bb79da889a44bc34bb9439733c83dbf33b7498541e17b9541e265d66f9a53d241d135c87dd86dcf6dae33e141c87f8587955dcd3fcc3fc35f957f8533cd3fcc3fc33fc233ba5f9539cd39c239c8658d939d5dc399cf999599c599bc8bae65a579a193d9ab9d8be36fc36fcb6fc25dba65d48bc365d393cb6fc26fba49cd69cb3dc249ca3bc131b26b95598d75e295d6919a73d473cc73d373cb73ba95d29fca85b993b279cb6bc249ba6bb969b28f8d67c355cb61e265d655d54dcd65d361995fcb4dc265d271ca4dc171b269d131c83dab41e251d6439a37d537cd41d42dcc2dc343d337d237ca2dc137b941d143d021be27aa71d8999c41cf739551c551bc41ae41a9359f57e351e279d479d351996dcb4bc25dba65d24bb96fb253d035af3baa9d9c698d69cb57cb55cb2b9a2fcb25ca5fcf35a933cb69857be17b9557cd6995698569e147cd57cb41e13bcd41cb69e13bcd53cb) else (if i<13 then 0x3ed67b4d3ed34a9a9b4da0c370623ed348ba72d28318569a9b4d6e9a9b4d734f726282d672d29318911b4129886270d672d2931882d668d47b14606284d646d4a46292d672d293187262729c4c635f4f592572623ed63ed35ad668d3314f5f3472623ed372d2731872905e633f4f352986625ad57ed67ed4334f373c2d342d215f59866266d25318726270d670d472d2531856622ed6534356d2531846d12b453663429a434d42bf4f257cb7633e41444f45433e273b74625cd48ed1513e2b3ba69c88812a637c627cd668d4373a68d253187cd1433e3757611b414e35442b3b272d27288e9c334f4f456a90413c88814863354e4f4f332975282b245128352460d6394f626266d257188c9c8c876cd9326354623ad65c634cd53ed6874d5d4f3ed69d4d3ed432d632d5874c874332d35d453e6348d65cd594cd5cd3246348d35f3449213ad63ed43ed33d4f28d630d595433ad368ba87482f4f47453e6330d45d458690393c5c634d4f1d3c30d68b4d30d328d166bf28633d3e2545526228d55289929d2e636e624558646252d638d546d464899e9d386376d676d4814f313c39252121415980626e625cd65cd445585c623cd6874c73434ad339584b453e6354d464d34ad64ad55ad33cd64ad44ad3346234d6569a34d534d3409944d242d11e6338622ed6554d28d32ed23b1857504758666266d642d366d2531834d159501f3e4358254590812a633cd63cd548d3313e68625ad450d3749990d26b3e22639cd35f347c6268d668d37cd26f18655759588e6278d65ad478d368d253183737433e37578b1b2b4e2d442d3b5358909c254f334556902b3c90813c63806280d680d26f4e53585f4f6cd47cd36b3e3d3b2b33870c7c6278d650d56cd478d33737573e254e3344333b253375286529686268d368d269573533492d554f546246d366d85ed9546339452f3423256662689a546246d6669c4663569a394f2f257a6254d664d568cd34d37ad854632b291f25694d4f4f3ad646d52ed356d646d33a9a52d652d3294f3934546246d654d556cd54d346d22f18569c56874063466242d354d2393446623ad63ad346d23b182f4f394f4745309054632f4f46d62ed53ad3526254d366d244626e9c4a9f32632e622ed572cd36d93263734d2b4f3cd374ba446238d586cd44d334ba2ed164d896876e9f44d93263446238d644d350ba50b8294f44621cd62aba34b81d4f33452c9020d9466340b82f4f3329446242d658d34eba2ab838622ed52ed326d1474d40b846bf2f4f34b8214f38622ed638d544d340ba34b82cd14d3e294f334525345a9f44d93263446240622cd66e9c3e63446236d5446238d65b4d2b4f406234d65acd44d434d350d8649f2cd9326325292b255b4d334f614c5b436d4b334f2b4548d6274d48d430d348d634d5374c52d32740 else 0x65347b2144623ad64734554f4525653458892663a14555254d57a51b3158809c488f28635f5759442b442b3b6a8e6f182f578f1b2144373b568e2b33252d43588e9c568f253490872e6357184133412d435873342b291d1f2544333b428e21334f2821244504368f432976871c6368625718535759443d2d3b244f1e3934489046634b3431252f217b4d4a9a94c34c629b4da0c3))))
def q11t0 (i : Nat) : Nat := 0xaee99a227799a559123388a116ad9b6699865d96655946499162d8a61d866158460d82605805ed7a5d9755d1735c9715c16b5a96559163589615815b5695454d525454b52943509414ed3a4c9314ad2a4852046d1a42d0a2ac9b26898254942489122c8a214822047b1ac6a16c5a1485112c4a0ec3a0ac2a06c1a02c0a
def q11g (i : Nat) : Nat := 0x13bf03a770084ec0109d4041398082710104de0209b404135808269017ccc23098c4613008c25d1184b423095c4612a08c25112049a2409244812289024112047a2408e44811a89023112045a2408a4481128942201284362508584a10889420c12840e2508084a0fe8941f81283e62607b44c0f38981e11303b62607544c0e78981c91303862606f44e0db09c1af1383502706844e0cd09c193138318280610500be0a01741402d8280590500ae0a41531482942905045209c0a7d2e2502484a046895e879ac10435f9f08c03b119c6fb340d2670188ce02d99e053b3c098680110d0d1de620334c80549980833400b66b20c0600000
def q11p (i : Nat) : Nat := (if i<7 then (if i<3 then (if i<1 then 0x2504808c108200500400f00c01402003004004000007c0f61e67b9771ee1de7b1761ec1da3a9751ebbd2fa4f47e8bd0fa1741e81d0398720e21bc3706d0d81adb50ea0d41a4b40680cc194320638c4588310611c0183afedfcbf77eafcdf8bef7dafadf3be57c6f85f1bc17a6ebdd1ba1766cc594b25646c8592b03602c0570adb56eacd57aab54ea9551aa1542a0530a413c2704c996b2c6584b09532624ac949252464849d9172264448790b20e40c809011be2f45d8b716a2cc588af15a2ac548a714a28c508a11021942184109e004007e0f81e8bc0780ee1d13a0748e49c8b9d716e25c3b85706e05c03886eadc9b8b706fedb9b6b6c6d6da9b4b686ced99b2b646c6d89b0b606c0d41a0330640c41802f05d0b41682c0560ab94ea9c536a694ca9852ea594aa94526a4948a90520a01382604a09291c2364688c91823c4548a113224444881142144248410f20c414821032024007c0f01d8380700df1ac3546a0d31a4344680d499832c648c899033e638c698c316624c418730c614c1982302600c01702c0540a01382404808c106208408801001fc3b0750e81cc390710e01c0340600b01522604a0911202404007e0da1b03586a0d21a0338660ca190318620c2180300580881002103007c0b41602b0520a01382604a090118220420801001e0180280400600800800000fa1f03d87a0f31dd3b9f71ee1de3b1761ec1da3a9f52ea3d43aef4be93d1fa2f43e81cc390710de1b83686c0d6da8b50ea0d41a4340670cc194320638c4588310e10c23803075fdbf97eefd5f9bf17defb5f5be97cef95f1be17c6f05edbb7766ec5d7bab74ee8dd0ba16e2cb594b25646ccd82b03602c0570adb56eacd57aab54ea9551aa1542a3d33a654c298520a213ca704e09a13265c4b59632c2584a99312564a4929232424ec8b91322243c85907206404808e11be2f45d8b916e2d4598b115e2b4558a914e294518a1142204328430821441083b02603c05803002003f07c0f61e0bc0780ef1d43a0750e51c9b92722e41ceb8c716e25c438770ae11c1b81700e21b9b726e2dc1bfb6e6dadb1b5b6a6d2da1b3b666cad91b1b626c2d81b0350680cc990320622bc1782e45a0b41602b055ca754e29b534a654c29752ca554a293524a45482905009c1302504988e91c2364688c91823c450899122224408a10b2124208790620a40c809001f03c0770e41c4380700df1ac3546a0d31a4344680d619832c648c899033e638c698c316628c498830e618c2983304604c01802e0580a814027048890120230418821022004007f0ec1d43a0730e41c4380700d01802c05489812a250488901202003f06d0d81ac350690d019c330650c818c310610c01802e0480801101803e05a0b01582a0520a01382604a090118220420801001e018028040060080080000 else (if i<2 then 0x4da9a532a614ba9652aa4d49291520a01382604a09211b2344648c11c226448889102284288490821e41882904206404800f81e03a0700df1ac3546a0d31a43406a4ca993324644c819f31c634c618b314624c418730c614c1982302600b81602a05009812022c410811002003f8760ea1d0398720e21c0380680c0148244480901001f83686c0d61a4340670cc194320630c2180300580881002003d0580ac1502905009c1302504808c110210400800f00c01402003004004000007b3ee5dc7bcf60ec7d4ba8f50ebbd2fa4f47e8bd0fa0f40e61c83806f0dc1ac349680cd194320638c458831061ebfb7eefd5f9bf17defb5f5be77caf8df0bd3742e85c0b73652c9d92b23642c8d80b015c2b6d5bab355ea9d50a8f4c2904d99632c2584a99312524949192127645c8990f21641c819011be2f45d8b716a2cc588af15a2ac538a5146284508810c6104207e0fa5e0bc0764e81d2393724e45c839d716e25c3b85706e05c03856e8dcdb93716e0dfdb736d6d8dadb53696d0d9db33656c8d8db13616c0d81a8340660c8188af05e0b81682c057ca754e29b534a654c29752ca554a293524a45482905009c1302484688c91823c450899122224408a90c2144248410f20c41482103204404801001f03c0740e01bc3546a0d31a4344680d499832a64cc919133e638c698b314624c418730c614c2183304604c01802e0580a81402604808b1042004007f0ec1d43a0730e41c4380700d01802a44a8911202404007e0da1b03586a0d21a0338660ca190318620c2180300500840c01f02d0580ac1502905009c1302504808c110210400800f00c01402003004004000007b0f29dcbb8f79ec3d8ba8f5de97d27a3f45e87d0398720e21bc3706d0d81ae7536a2d41a8349680cd194320630c418470060ebfb7f2fddf9bf17defb5f5be77caf8df0bf3786f6dd7bab742e05b8b2d652c9591b21666c0d80b015c2b6d5bab355eaad53aa1542a0520a213ca704d09932c6584b094d2564a4929232424ec8b91321e42c839032024046f8bd1762dc5a8b31622bc568ab14e294518a114220430849042083f07c0f65e0bc0780ed1d2b94722e41ceb8b712e15c1b81700e25bab726e2dc1bfb6e6dadadb53696d0d9db33656c6d89b0b606c0d0199320640c41802f05d0b51682d0580ac15729d536a694ca9852ea594aa94526a4948a90520a01382604948e11b2344648c11d22844c891112204508510921043c83105206404800f81e03b0710e01c037c6b0d51a834c680d5199330658ca992322640cf98e31a630c598a312620c398630a60cc1181300600b81602a05009812022c408801001fc3b0750e81cc390710e01c0340600b0152244480901001f83686c0d61a8348680ce198328640c6188308600c0160220400840c01f02d0580ac1502905009c13 else 0x90710e01c0340600a11202404007e0da1b0358690d019c330650c818c310610c01802c0420600f81682c0560a81482804e09812824046088108200400780600a01001802002000003d87a0f23dc7aef4be93d17a1f40e61bc3706d0d8da8349680cc194320631c2187afedfbbf57e6fc5f7bed7d6f9df2be37c6f1dd2ba3742e85b4b25646c8593b03602c0570adb566a9d50a8f4c290510a0538270cb09712524949192127645c8990f21641c819011c237c5d8b716a2cc588af15a2ac538a5146284508810e20dc007b2f01e03b4742e41ceb8b712e21c3b85702e21b93716fedb5b5b696d0d9db33656c6d89b0b606c0d41a0330640c45782f05c0b41602be53aa6d4d299530a5d4b295528a4d49291520a013826846c8d119230470899122224408a10b2144248410f20c41482103204404800f41c4380700de1a834c690d11a0352654c999132067cc718d31862cc518931061cc318530860cc1181300600b81602804c08b104204400800fe1d83a8740e61c8388700e01a0300580a8122240480800fa1b03586a0d21a0338660ca190318620c2180300580881002103007a0b01582905009c130250460841002003c0300500800c010007b0f25dc7b8772ec1d8ba8f5be93d1fa1f41e81cc3706b2d43a8349680d019a328632c418a7075fdbf77e6fc5f7bed7d6f9df2be37c2f8de0b6964ac8d90b33606c0580ae15aeacd57aa754aa8540a4140260cb09612a24a4929232424ec8b91322243c85907206404808df17a2ec5b8b51662bc568a714a28c508810c2103f07c0f45e03c0768e81d2392722e75c5b8970ee15c1b81700e21bb3746e4dc5b837f6dcdb5b5b6a6d2da1b3b666cad8db13616c0d81a0332640c41702d0580ac15729d536a654ba9652aa4d49291520a41402704a09211b2344648c11a2224408a90c2164288490f20c414819012004007c0f41c03806f0d51a834c690d01a832a64cc919133e638c698b31261cc3185306608c09802e0580a013024046083104204400800fe1d83a8740e61c8388700e01a0300580a11202404007e0da1b03586a0d21a0338660ca190318620c2180300580881002103007c0b41602b0520a01382604a090118220420801001e01802804004004000007b0f41e4bb8f71ec3d77a5f49e8fd0fa0730e21bc3706d0d8da8350692d0198328640c6188308e00c1d7f6fe5fbbf57e6fbdf6beb7cef95f1be37b6ecdd7ba7746e85d0b91652c9591b21646c0580ae15b6add59aaf54ea8d50a41442704d49632c2584a592924a48c9093b22e44c8790b21241c8190120237c5e8bb1722dc5a8b315e2b4558a714a28c508810ca10c20840fc1e8bc0780ec1d2392722e75c5b8970ae0dc1381710dc9b8b706fedb9b6b6c6d6da9b4b676ccd95b1b626c2d81b0350680cc1882f05c0b41602b055ca75)) else (if i<5 then (if i<4 then 0x2600c01602804c8901142004007f0ec1d43a0730e41c4380700d01802e04809e0d81a8348680ce198328640c4184300600b01002003d0580ac1502905009c12824046088108200400780600a01001802002000003da771ee1de3b1762ea3d6fa3f43e85d03906f0dc1b4349680d0198319620c5d7f6fddf9bf17defb5f5be77cafbdd0b71652c9591b2164ac0d80b015eeabd53aa555e9ad33a61482814b19712524949093321e42c849072064046f8bd1762dc598b115e2b4558a714a284508810ca13c007e0ed1c939073ae2dc4b85706e09c0b886ecdc9b8b706fedb9b6b6b6d4da5b43676ccd95b1b626c0d81a0338640c81702d0580ac15729d536a654c29752ca5549a92520a01302584688c918238448889102284288490e20a40c800f81e03a0700de1aa350698d21a832a648c899f31c634c598a312620c398630a60cc1181300580a81402604808b104204400800fe1d83a8740e61c8388700e01a0300508901202003f06d0d81a8348680ce198328640c6188308600b01001f02d0580ac1502905009c12824046088108200400780600a01001802002000003c8772ea3d77a2f43e81cc750698d05a0330650c818c30f5fdbf77e6fc5f7bed7d6f9df2be37cee95d1bb3662ca592b23642b856dab7566abd55aa7546a8524a014025cc9892924a48c9093b22e44c8790b20e4148190120237c5d8b716a2cc588af15a2ac538a514628450880fc1f03d0780ec1d1391720e75c5b8970ee15c1b81700e21b93716e0dfdb736d6d8dadb53696ced99b2b646c6d89b0b606c0ce190af05e0b81682c057ca754e29b534a654c29752ca554a293524a45482804c09211b2344648c11e22844c891112204508510921e41882903202400800f81e03806f0d51a834c688d01a8326644c819f31c634c618b314624c398630a60cc0980300580a01302003f8760ea1d0398720e21c0340600b01422404007e0da1b03586a0d21a0338660ca190318620c21802c04007a0b01582905009c1302504808c1102104007806008000003d87a0f23dc3b8f6be8fd0fa06e2d41a8349680d019c330640c6588310e00c1d7f6fe5fbbf57e6fc5f7bed7d6f9df2be37c6f05b8b2964ac8d90b3160ac0d80b015e6abd53aaf4ce985289632c2584a892924a48c9093b22643c8590720647c5e8bb16e2d4598af15a2ac528a1142204307e0f45e03c8740e91c939073ae2dc4b8870ee15c1b826fedb9b6b6b6d4da5b3b666cad91b1b626c0d81a8340664c81903105e0b81682c0560ab94ea9b534a654ba9652aa4d49291520a01382604908d119230470899122224408a10a21242087105206404800f81e03806f0d51a834c690d11a034a64cc919033e638c698c316628c498830e618c2983304604c01702c0540a01322404808c106208408801001fc3b0750e81cc3 else 0x8b51662bc568ab14e2945284f001f03b8728e4dc8b9073ae2dc4b83702e0db93716e0dfdb736d6d6da9b4b676ccd95b1b626c2d81a1320640b81602b055ca754e29b534a654ba9652aa4d492905108d119230468889102284288410e20a40c809002003c0700de1aa350698d21a035264cc819f31c634c618b314624c398630a60cc1181300580a0138240448801001fc3b0750e81cc388700c0160284480800fc1b43606a0d21a0338660ca190318620c2180280420600f81682c0560a81482804e098128240460841001e018003c8771ed1d4fadf49e8fd0fa06f0da1a0330640c7d7f6fddfabf37e2fbdf6beb7cef95f1be17dee85b2b23642bdd59aaf54ea8520a09382584a89252464849590720647c5e8b716a2cc588af15a2ac538a514228440860fc1ecbc8740ea1c9b92722e6dc4b85706e05c4b736e4dfdb736d6d6da9b4b686ced99b2b636c4d85b0340660b81682c057ca754da9a532a614ba9652aa5149a92520a41402644648c11c22444488112212438829032024007c0de1aa350698d419332467cc718d316628c498830e618c2983304600b0140264400800fe1d83a8740e61c8388700e01a0300580a41222404807d0d81ac350690d019c330650c818c310610c01802804007a0ac1502905009c1302504808c110210400800e00a01001802002000003ca772ee1dc7aef4be8fd17a1f40d31a0330640c658bafedfbbf57e6fc5f7bed7cef95f0bef74ac8d90af755eaad53aa3542a3d31a653825c4949252464849990f21641c808df17a2ec5b8b51662c4578ad15629c528a314228441843001f83e1780f01da3a0748e49c8b9073ae2dc4b8770ae0dc13716fedb9b6b6b6d4da5b43676ccd91b1b626c0d81a0332640c81782e05a0af94ea9c536a694ca9852ea594aa93524a45482905009a11a2324608e1122224408a10921c414819001f43806f0d51a834c690d01a8324644cf98e31a630c598a312620c398630a60cc1181300580a8140260498811002003f8760ea1d0398710e01a0300508901001f83686c0d61a8348680ce198328640c6188308600c01502103007c0b41602b0540a41402704c094120230440841002003c0300500800c003c8f70ee3d5fa1f41e81c8368690cdd7eefd5f9bf17defb5f5be77caf8df1bd3756ea5d0ba16e2ca592b23642c8d80af355ea9d51aa14a258cb09612aa4c4929232424cc8790323e2dc5a8b31622bc568a714a28c508810d2103e07a8ea1c839b712e21c2b84706e05c03886ecdc9b837f6dcdadb53696d0d9db33656c8d8db13616c0d81a0330622bc1782e05a0b015f29b534a654c29752ca4d49291520a013c2344648c11a2224408a90a21243c83105206408809001f03c8700e01bc3546a0d31a43406a0ca993324640cf98e31a630c598a312620c398630a610c198230) else (if i<6 then 0x50867006003f07a2f01dc3a0750e51c839d716e25c3b83710dc9b8b7f6dadadb53686ced99b1b626c0cc9903205c0ac156a9b534a654ba96526a49482804e0921192304688891022043482103204404800e81bc3546a0d31a43446a0c919033e638c698b314624c398630a60cc1181300580a8140270408801001fc3b0750e81cc388700d0180290480901001f43606b0d41a0338660ca190318620c21802903007a0ac1482804e090118210400800f00c003dcbb1750dc1b4b50650c818aafcdf8bef7dafadf3be57c6f958bab354ea85209612a24a4929232424cc8590720237c5a8af15a2ac538a514628447800e89c8b9970ae0dc23726e2dfdb6b6c6d6da9b43676ccd95b1b626c2d8199320620b81682c0576a694ca9852ea4d492984688c918238448889102284288490e20a410819022003e0730d51a834c690d4995324644cf98e31a62cc518931061cc318530860cc1181300580a8140264480901122004007f0ec1d43a0730e41c4380700dc0d61a8348680ce198328640c6188308600b01102004007a0b01482804e094120230440841002003c0300500800c01001000009dcbaef4be8fd0fa1740dc5a0340634c43876fe5fbbf57e6fc5f7bed7d6f9df2bf164ac8d91b015c2b5d57aa14a65cc9892924a4dc8990f21641c808df1762e45b8b51662c4578ad15629c528a10c5e03c0770e51c9391720e75c5b8970ae0dc0b826fedb5b5b6a6d2d9db33656c8d8db13606c0c81702c057aa714da9a532a614ba96526a49482804c09211a2324608f1142224408b105206404800f81bc3546a0d31a235064cc919033e638c698c316628c498830e618c2984306608c09802c05009c124240448801001fc3b0750e61c4380680b01402743606b0d41a4340670cc194320630c4184300500840c01e82c0540a41402704c094120230440841002003c03005000f41e47bc761ed1d47abf43e81bc368ea0ce18c3065fbbf57e6fc5f7be57c2fade7bab762c9590b25602bcd57aab54ea84d09512564949193722642c8f8bb16e2d4598b115e2a4538a51422844086508612417800fc1e83b8740e85cdb8970ae0dc0b886e4dc5bfb6d6d8dadb53686ced99b2b646c6d89b0b606a0d01882e05a0b015e29a532a614ba93524a45482684688c91823844888910228438821032003e07b0d51a834c690d4998324644c819f31c634c618b314624c418730c614c1181300600a81402604488010e1d83a8740e61c8388700e01a03004686c0d61a8340670ca190318620c01602004d0580ac1482804e094118220420801001e0180280400600800800008ee7d47a875de97d0fa06e1d41a4b40660c818c7075fdbf77eafcdf7bed7d6f9df7ba964ac8d90b1b56eabd55aa7542684a892b2524949192127645c8991121e42c84907206404808df17a2ec5b else 0x92915209d1182384488811121a410819012003e07b0d41a2344644c819e31a62cc498730c60cc09802e0540a01302003f8750e81cc390700e01a0300588901202003e0690ca190318620c2180300580801081803d0580a81482804a090118220420800f00c014020007d0f25d57a1f42e81c83686b2d4198320630c41836fb5f5be37daeadd2ba3746c8d80b112c65c4949252464849990b20e45c578ab14e28442840fa1d03a4722e65c1b826e2df5b636b6d4da5b43676ccd95b23636c2d81882f05c0b41602bd526a4948a944608e1122224408890821a40c800f51a435c62cc5187306600b81502804c0881001f83a8740e61c8388700e01a0320488901202003e86c0d61a8348680cc194320630c4184300600b01002003d0580a4140230420801001c01402003004004000007b0f43de3b0767e87d0378660ca19031d5f8bef7dafadf3be57c2dc592b23642bbd50a854c6584b892924a48c9092f21640c8f8b716a2cc588af15a29c528a3141e8bc0790e81d4394722e75c2b83702e09b8b7f6dadb1b5b6a6d0d9db33656c6d89b0b606c0b815d299530a5d4b293524a41442344648d1112204508510f20a410820e21c03806f0d51a83406a0ca19232267cc718d31862cc518931061cc318530860cc11813005009810e1d83a8740e41c4380680c01402743606a0d21a0338660ca190310600a01001e82c0520a01382504808c10820040047b9760ec3d77a3745e81a0328630c137e2f9df2be37c2c057dab7542704a49252464849d90b20e47c5d8b71662bc568a714a284407c0f41dc3a4722e75c4b85706e21ba3726e2dfdb6b6a6d2d9db33656c8d8db13616c0d01902c057aa654ba93524a414024c4688c9182384488891022843882903202400800f81e4380700de1a8348688d119033e638c698b314624c398630a610c1982302600a0134204400800fe1d83a8740e61c8388700e01a0310480800fa1b0350690d0194320630c41843005007a0b01502905009c128230440801001e01802804006008023b1751eb7d0fa0720da1a4330640c5b7f2fd5f8bed7cef95f1beb74eecd94b23642c8d80af354ea85209512524949192126e44c8590323e2ec5b8b51662c4578a914e28450880fc1e83a2736e25c2b83710dc9b8b706fedb5b636b6d0d9db33656c6d81a03105e0b815ea9c534a6149a91520a191a230470891112204448410e20a40c811001f8380730d51a63486a0c899033c634c618b31061cc3185306604c01802c04c0800fc1d43a0730e41c4380700d0190244480901001f4360690d0194320620c2180300500800f01502905008c1001c01402002002000003d87a2ee5d87b6f4be8fd0fa1680d019431edfbbf57e6fbdf6be77caf8df1bc964ac8d9dab355ea9d50a4924a48c9d90f21641c8f8bb16e2d4578ad14a28c))) else (if i<10 then (if i<8 then 0x412021040080087b2ee5d83b6f49e85d03916a0d21a0b00e09bef7cafbdd5ba7746ec594b23642cc582b0d4c6984a492325a42c8191f16e2cc578a314223401800f81e8bc0780ed1c939173ae25c2b83710dd1b93716fedb5b5b676ccd95b1b605c0b01582a7526a4948a984708891022c4007c0f01dc342678c698b31461cc31853005409910021c3a8740e61c8388700d01802a0490901202003e0680c818c310600b0110200400720a0120230440800f00c01402000721d4190318627bed7d6f9df2be37d2c8d94b015d2714e094924a4849990b20e4046b8af15a2ac538a5142183a2722e71c4b85706e05c13716f6da5b3b646c4d81882f05c0b41602b0554a5949a92522a413a23047089110228438690d718d316628c39863005c0a8140260480881001f43a0730e41c4380700d01802c0520911202404007c0d41a4340660ca190318620c2180300580801001d82a0520a012023044084100200380280400600800800790f03de3abf42d43aa340660ca185af9df2be37cacbd53a65382724929232424cc8790723e2bc538a514a10c29808f05e03a8728e65c2b83710dc9b8b7f6dadb1b5b6a6d2d9db2b636c4d85b43205c0b41602b25209e11a232470889102284288490e20a410710e61aa3486a0ca19e31a62cc498830a610c19823004c0901102003e8740e61c8388700e01b02484808c0d41a4340630c4180300500800f01482804808c108200400700400400400000781eebd0fa0730de1a4b40660c7b7eefb5f5be77c6f85c1b2560ea8520a1138a704e19612c25249292326642c8191f1762dc5a8b315e2b4558a714a28c508a1102183f07c0f01da39173ae25c2b83702e21b93716fedb5b5b686ced99b2b636c2d81a1320644bc57ea9b532a614ba935308d11923844888114214424859012003e07a0e21c038c690d11a8328648cf18d316628c498830e618c2984306608c01602604007e0ea1d0398710e01c0340588900fa1b0348680ca190318620c21802803d0580a4107b0f23de3b0761eb7d27a3743e85a8750698d05a0330650c818eefcdf7beb7cafb5d5ba1646c0570a412ca48c9093f1762dc5a8b315e29c528a316209c007c0f45e03c8748e81d4394722e55c1b846e4dc5bfb6d6d8dadb53696d0d9db2b646c4d85b0342640b81602b0554a5d4aa93524a41412384488891022a4007c0e51a4324644cf18d31862cc518930e618c11802c05009a102200430750e81cc390710e01a0300510911202703586a0d21a0338630c21802804007a0b01482804a09011821040080087b0f41e4bb8f71eadd07a0722d43ab6fbdf3bf375ae8dd1b25606c0563aa151a98d3096129248c999011be2ec5b8b315e2b4558a714a28c507a0f11c939d712e15c1b826e2dfdb6b6c6d6da9b4b676c8d8db13625e2bc1602b054ea554 else (if i<9 then 0x3a8740e41c4380690911201f0348680cc190318620c2180300580801341602905009412023040078007b1ec1c8348660c6181efadf3be37e2c9598b015d6a9d50a4129248c959032262bc558a7142183e07a0ee1d4b85702dfdb6b696d0d9db23636c2d81a83105c0b41602b0552a5549a984688c11c22444488114212434819001f03c0770d51ae31a62cc518730c60cc01402604808810a1d0398710e01a0300540901202003e0690d0190310610c016020039050090118210400800e00a01001800795e81b4b50ea0cc18c310617bed7d6f9df2be37c6c9d509e53825c49192126e2cc578ad14e283d0750e45ccb81704dc5bdb696ced99b23636c0b81602b5526a4948a904e48c11c224444881142103ac6b8c698b31461cc31802e04c090118204400800fc1d0398720e21c0380680c01422404d0690d0194320630c01802c0440801001e82c0520a0128240460841001c0140200300400400002755e85d0b50ea0cc37e6eadd2ba3642bcd55aa754aa95349612c2544949252464849990523e2bc548a7142204328430a20cc06805006003d8780f01da39c712e21c2b84702e21ba3726e2dfdb13616c6a4948a984688c918230450851092004007e0e21cc350650c9992322678c698c310618c2183304604c0110214390710e01c03004007c0d21a0300500800f0148280480841001c010000007b0f23dc7a8690cc190301df9bad74ee8dd4b23602bbd55aa555699530a41462714e094924a48c9092d21640c8b8b51662bc568a714a28c50865081f03b4726e21b93716fada9b4b686ced99b23636c2d81a0338644c81702d8526a45482884648e1122224408a10a212438829001f03d0700e61a8348688c899e31a630c598a31261cc3185306608c0980300580a01301f83a8740e61c4380700d01802a04a0901201f4360680ca190318610c0140187b1ec3d4ba0f40d29a0b40680cc182efbdf5be77c6fcdd3ba16c6c8573aa1516995309c1342604a49252464dc8990b20e4148f8b71662bc568ab14e29450780e85ccb83704dfdb53696ced8db13275209e11a23247088114214424871032003f0710e31a4324644cf18d31862cc518930e618c2984306608c09802c050098118208408801001f83a8740e61c8388700e01a0270348680cc18c310610c0160220400800f41602b0520a01382504808c107b0f21e07ab741e81cc3916a1d45a0330650c818cef95f9ba5746c8d8baab54aa84c19612c2544949252464849b91321a42c8390520647c5b8b315e2ac538a905e01c007a2f21d23a0748e45ca3726e2dfdb6b6b6d4da5b43656c8d8db13205c0aed4aa93524a45482444648c11c22444488112212420740e099f31c634c618b314620c3986306600a01302183a0730e41c4380510911202403e06a0d21a0328640c21802803d05809 else 0x5c0a21022004007e0ea1d0390710e01a02844808c0d41a4330640c6188308600b0110200400780a41402504808c1102003802800793e83a8348630c4b7cef95f1be7752c9591b2129248c9093522644c578ad14e29c007c8e41c9b81702de5b3b646c0b81582a3522a41222344408910921a40c800f718d316628c39863005c0b01502604007e0ea1d0398720e21c0380680c8122240480800f81a4340650c818c310610c0180280400760a8148200400700500800c010007b0f4dd03706d0cc18c310617bed7d6f9df6bab746cc4e49252424ac858a8e81d1391732e09bdb6a6d2da1b3b666cad85b02e05a0b015b293524a411c2244448811120c342678c6987300500901102003f0740e61c8388700e01a03004808c0d41a4330650c818c308600c0150200400780a814828046088108200380280400400400004752eb3d0ba16a1d41a4333df5ba1642c0576aa5546ab531a693a25a4b892924a48c9391f16e2cc578ab14e294518a10ca13405805006003e1780ec1d2392738e21c2b81710dc9b8b706fedb5b636b6d2da1b3b656c0d011c2224408a10a212438809001f4388688d4194324644cf98e31a630c518730c610c19823143844a021050000007b3e83a8348660c818d6f9df1bcd746ea591b21642bb555aa7546a8546a6b4ca98d309c32c25449592924a48c959151662bc568a714628c2980d00a00c007b0f05e2391728dc9b8b7d6d8dadb4b656c6d89b0348644c81902e054ea4d48a904f08d119238448889102284288490e20a40c830d41a2322678c698c316624c398630a60cc1180270400860ea1d0398720e21c03a04a09113a1b030791ee1d87a9f40da1a4b40660ca192afbdf3be9642c8d80aeb542944e29d12e24a4929232424cc8591715e2ac538a514219421782e65c13716f6da5b3b636c4d81a12f05c0b41602b852aa4d4c2344648e1122284288490d2003f0710e01c4324644cf18d31862cc518930e618c2183304604c01602804c0921001f43a0730e01a030058890120230348680cc194320630c41843005007a0b0107b1ea3a834c682d01a0330650c737cef95f1bf374ae8d92b03626995309812ca48c9990b20a45c598af1562945882f00e003d1788e81d2391732e15c1b826e2df5b636b6d0d9db2b636c4d81702b054ea4d4a23247089111220444871001f0384644cf18d31862cc518930e618c2983304600b81402183a8730e01802c05007c0d61a8348650c8188308600a81002602905009412023042080087b0f21e07b4f46e8bd0ba0f42d43a8349680c818e6f95f1bf375eeadd3ba5746c04c49252464849990d2164148191f16e2bc558a5141f03c8740e85ccb85708dc9b8b7f6dadadb53696ced91b1b626c0c81592904f089110224424878c698b314624c398630a60cc0170284400800fe1d8)) else (if i<12 then (if i<11 then 0x35308d118238448889102224207b8c698a30e618c1988250400860e81c4380600901001f43606a0d21a0300580980a81482804a090118220400800e00a010018007a0f2bd13135f09652424cc808f715e29c507c2dedb3b646c4d81702d0580ad949a915288c11a222454810d718d316628c39802a05009a120240440800fc1d43a0730e41c4380700d01842404808c0d2198328640c6188300600b01102602904a08c110200380280400600800804761ecbd03896a1d41a4b40650c818d6f9df1b25606c0570a112e24b48191b1662bc50883081f03c0748e41ceb8c702e21b8b7b6d4d8db1360680bc1702c0554a4d482784648e112222448869001fc342678c698c30e600a81202143a0730e1120268318620c00e41402c004000007b8ec7d0348631bed756e95d1ba364ac0570ad354aab531a632ca48c9092b216284328430a2083b8740e91cc385706e21ba3726e2df1b5b696d0d9db2b636c4d81a02d05108c9182384488811421443882904206408800fc1c4380730d51a8328648c899e31a630c598a312620c398630a610c19823004e0811002143a0730e41d0250487b0f23d4fa0660c8f7cef8dd0b71646c9d51aa150e9c4e19612a24a49193321640c8f8b715e2ac538b300a003d0768e45ccb85702e09b8b7f6d8dadb3b656c6d8191a984688c11c2204508510921a40c809001e03a0730d119f31c634c598730c60cc11802804c894104200430750e81cc388700d0180290488901202003e86c0d21a030f60ec7d0358660ca19031860abe77dee95d4b293924949193321645c578a314e003f07a2f01dc3a873ae0dc0b886e4dc5beb6b6ced91b1b62640bc1702d056ea5549a984688c11c2244448a10a212434819001f03b86a0d21ae31a630c598a30e618c19802804e082100214398720e01a02844808c0d21a0330650c818c310610c0140187b0f23de7b0f60ec3d0398712d45a0330641c2184304df5be57c6c0570ad34ca9852892524a4046d8b315e2b4558a7141f03c1732e15c0b826f4da5b3b60604bc5782e05b2a6149a904f08e112222440880fa19233c634c598a30e608c01602804c8860ea1cc390700d01502444d8690cc194318600b01102004007a0b01482804a090107b1ecfd0fa0712d43a8349680cc18e6f9df7bab74ee8dd2b0924a48c9391315e29c518af00e003d1780e85c9b816f4da5b3b636c2d81902e0566a494a2324608d11122045085109216408688cf18d31862cc498730c60cc01602804c0901102183a8740e61c8388700b0150270348660c818c310600a01341602905009011821040080087b0f21b4b50690cc190ef95f1be3642b85129232424dc8990d22e2bc538a0f45c93716f6da9b4b676c4d81882e05a0b015aa93524a4132230468881162003e0770d31a133c634c598a30e618c29833 else 0x9802183a8740e61c4380700dc0d0194320620c21802a04c04a0901001c014020006d3beb746c857193716a2cc50840fadb4b676c0b415ba935308d118234444880f61a6342678c698b31461cc19802a03f0730e41c4388480890cc188308600b0110200400740a4140250460801001c01402003004004000007b6e85a0338630c0d7d6f9df1ba3646c0572aa144a70cb09652464849b91320a46c5b8b314e294507e0f01d839d718e25c4385708e11beb6c6d6d8db12f0566a413923046888914194324678c698b30e6187206805800000790ec5a0701df0bc15ca984c89652c25c492921266414808d115e2b4538a514a14405805001f13c1780f01d93a8730dd1b937b6d4d9db33636c4d85b1320644a611b2344648e113220448840f81d8388700e61a4350650c919133c634c618a312620c398630a610c1982302600987b2ec7d0398712d4194320630c4381ef9df1bf3756e95d0ae15a6abd55aa554a48c909332262bc568a11021cbc077ae15c23726fadb1b5b696ced95b2360640ae9482704d0891102284207c0ee1a8324644cf18d31661cc31833005c094102200438760ea1d0398720e01b0250487c0f21e07a9f40de3a8349680cc185ef9df2be1722ca590ae754e984e197125248c9b8af14e284307e0f45e2393704dedb3b636c0c8171a904f08d11c2244408a10a21242c809001e0384678c598a30e618c19823005009e0ea1cc390700e01a0320488901202003e0690d019430791ea7d0351680cc190318617beb7caf8577aa55429049590322e2bc538a515e01c02800fc9e03cd706e09b9b60640c0161a904948d1192304508510921a4007d0d01a233c634c618b31461cc3183304600991202143a0710e01a03005089c0d21a0328640c6188308600c010018f50d65a8b4060abf37d6f9df2beb746eb551aa12ca48c9b8b315e2ac538a1041e239970ae05c13716fada5b43676cad8db13205aca4d4a230470891112203e0760e419233c634c618b31461cc3182302600b810c1d4398700a1120264340650c61802c04007a0b01482804a090107b2ecfd0fa1740d2190318620c2181afadf3be57dee9dd1ba52c6484939032262bc538a2e65c13716f6d8db02e05a0a812423444488114214424869041cc350690d219233c634c618b314624c3986304630750e61c03405009c0d2194320620c01401e82904808c1102104008008f61eafd0fa16a1d41a4338660cb57cef8de1b0128a48c9990b22e2bc53802f05beb6b6cad91b1b616c0a9549a925209c1222324608c910228424869001e03b8684cf18d316628c398630a60cc0170280430750e61c8388700a11202403e0690ca180300500980a4128240440800b740e61bcb50660ca190efbdd5bb1656a84e094b2262bc568a7141ccb85706e05c43726f0d9db02e05a0b015c29) else (if i<13 then 0x30640c1124e45c578b0f01e5b636c4c81903005aea55492204488410820e31a630c598a31261cc3183300430750e81282404808c0d41a4340650c818c310610c0180196a2be525629c5170ea5949a925248e112222450869041cc344678c698c316628c498730c614c19802c0430730e21c0370310680881341602a0520a01282404608810680c477deeaddb8af14e2bb62640c816c2935248e111224430700e61aa34c690d718d31862cc398630a60cc0130230408801001802303286904a0901082003802802f46be1796e8d909612824cc878a4e49b8b796c0b41602b35208d11022c35c634c59873183a8730e41c0300460690cc19432068088100248230580200300400400000791e81a4331628c03816f9df2bf374ee95d1ba5612724b492524249c8290f15a2a4538a10e2084107c0f0dc137d6d8d9db33656c6d89b0342642bc1702b6526a494828c4648d111228428840fe1a83486b8c698c316628c4762e8195310623be574aabd36a693a2594b097124a484999151662bc558a714a29426804f01cc382710dc9beb6b6d2da1b3b626c0b611b23844888114214430710e61a83486a0ca19e31a630c518931061cc318530860cc0792ec1ccb40642bf3742bc532a61412584b492524249c8091714a023846fadb1b5b696ced8db13205eca4d49238448881142103986a0c919e31a630c598931061cc3185306608c0150270490901202284088010c1d43a0707b2d4190b11df3ba364eac4949252464dc528a110219c03704df5b23636c0b8159a925209211a238448889102284288490e202404678c698c31661cc3183304600b8132240430750e61c0380680c81282484889012023031f40dc198320637be77cee9d509c12a248c9990b20e4148b8af141f83e075ae21ba3796ced818ba935308d119224424869032003f86a0d718d31862cc518730c614c1980280470750e61c0340600a01181a4340650c818c307b2d0b7c2b6c5b8a7141f03c4752e09b9b605c0b4159a924608e111220450851081d4384678c698b30e618c19823005c0981182084088010c1d4398710e01a0284480990d0190318620c2180300580881002003d0580a8116a1d41a4b40660c6d7d6f9df2bed4d25c4949252424bc558a716a003d8732e15c0b846e0b594aa92520a011c2244448a10a21a4007e0c919e31862cc518930e618c19802983a8740e61c61b41602a0520a01382504808c11f42d41a4311dd292722e29c53702df5b5b636c6a49482704888c91c224440880fe1a4342678c698c316628c498730c614c11802183a8710e01c0304480901181a8348650c6188300400720a0128240460881082004007003dd6ba574ac8d93aa128a4bc8690b20a44c578ad15e003d0760e61c43726eed99b1b60580ae54ba924608e11022c34c6b8c698b30e618c1 else 0x2af9df6aa326a43c5c70eda949a904708891718d31862cc518730c614c19802183a8730e81202303506096126e2cc5d6d6d903086904a08c1001c01401802006e83843055f3bef75aed556aa75625d48690f161e4394734e15c6b676d4a5949a984688c91823844488117187e87742bbd53ab54d24949390f14e2c4107c8f25c23726f6d9db2b636c4c91122103f86b8c698c316628c4988d1182efbdd0937226283cd70ae2db4b68656a454a2304508410b1a133a630c518930e618c298331040880103e877ee29b816fad9db02d3520778c618b30e614c1982200428730e41c438074094124244480901181ac35062d4326e2bc524608c91718b30e618c198220c390710ec0d0194320620c21801e82c0540a41402504808c10821ee3d8b40635be141e2c2224407f8c698b30e6008810c1d4398720e0180214318660400700500800c01001002eb5d1ba1742d45a0b10e12c077eaeb5d2ba565aa95509b12ca584b293521e414878a50a1e13c0790e51c939a704e09b8b7d6d6da9b3b666c6d897922435c634c07b8ec5d034a5d3ba5746e8572ab12d25c49493b16e2cc588af15a29c508650820d408730e11c1b886e8dedb3b656c6da948230448840fa1a233c630c598a31261cc4609bf37a6584b9929242494898af14e2b404730e15c13706f6da5b33616c88c91c222450841081f03b06a0c919e31a630c598931061cc3185306608c017029040880793e8190309df3aa92464cc53800f8dc237d6d6d9db0309524a51102284248590419233c634c598730c614c1980264400860ea1d0398700e01b025049091120270))))
def orfd11 (p : Nat) : Nat :=
  let j := p/4
  let r := packedAt q11r (j*16) 16
  let h := packedAt q11ph ((j/8)*28) 28
  let pw := h >>> 24
  let parent := ((h >>> 14)%1024) + packedAt q11pb ((h % 16384)+(j % 8)*pw) pw
  let op := (packedAt q11t0 (((r >>> 0) % 128)*10) 10)
  let keep := ((r >>> 7) % 4)
  if p % 4=0 then (orfd12 (4*parent)) ||| (op <<< 30) else if p % 4=1 then
    let old := orfd12 (4*parent+1)
    let a := op % 16
    let b := (op >>> 4) % 16
    let rm := (if keep % 2=0 then 1 <<< a else 0) ||| (if keep/2=0 then 1 <<< b else 0)
    if j=4543 then 4094 else if j=4567 then 4094 else ((old ^^^ (old &&& rm)) ||| 4096)
  else
    let w := packedAt q11g (((r >>> 9) % 128)*23) 23
    let n := w >>> 14
    if p % 4=2 then n else packedAt q11p ((w % 16384)*11) (n*11)
def orfl11 : Packing := (6730,4,7,0,250,0,0,orfd11)
def q10pb (i : Nat) : Nat := (if i<1 then 0x62b18800ee293942009d85c71c7180b1124081a6575cc240ffca972087765530cd9e829040e6ecb51840941ce2840083d6a48400e5e9079080eed95000a627995d7040d9987320cd1248edc82000fec51e739800c5ef7b4980b52938b9a0d59ac58840bad74f102080ad1ca29040dc66331091b648b97652109418720820996321108da440adb6d8aa96321094a5250c20bbbb4210d5a448ebbbbb30ce6d079800a510631860ff4448f540d12440c0922248db5640fea4e0009732200099875420b64000ffb600ad0000feb600ff588097776200d98500008000009000e94088742110ffead0daa95310ba999850aaaa5320fe96100000fa0000ff753100c89000f24000d9b000924900b5ad673580ba5294a400f540923240dca87620b4333300c00000d8000000b494800000fd8000ffc5431098886660b6da88fab000dddb760094a5294880ffff90bbbb8330a9864100c7432210daa24087754310800085332100fdc5331088865330f8c77777708358b50000842103080080008a4c418c40924840b1a490924800cbbb7200fec62110eddcb540876553208bca420000fb344886333300e89248f63240ada248924240b11248a954ff54f954a900d5b688e5408d2448c0e0a500922400ea40adb480924648a954f0fa94fef0f0e0c0e0eaa0a95488865420a950fa54a940fe9110009400fea4a954e954a954a95095409500fee0fcc0e080f0e0a554f0a950f0f8c0e0e0fcea54a55095009540892448b648d09400a954aa94c0a550c080c0f0c0f0fcc0c0c080e0f8f8fefcfef8fef0f8f0fec0f0fcf0a00091a200f0f0fcaa54a554fea550c0f0a550e0fcf8e08095222000f8b5b64895408d2248ffa0ea40a954fea8d5a240a554ffa4ea40f6488095008d2248aa949500fa40a550fa40a950fefcaa50955091b688a550f0e0ffd0e0fcffe4a550e099999700fd008654311087743310a950b24448a540aa94a540ffe48da200c08db640a54091b680ffa491b640a950feb636c89000ff50e540950095408db248aa54f8a540ffe49500809554fa909554f89554ffe4a540a5549554e09122409540e0da2200b236c8ea50c091b24091a240fa54fea8ea509550c0ada240a554ff949540b22448a5549232409000aaa4f080b5a248fe94e954f8c0faa8a550e0f8f0e0f8e500a550e0e08091a240c0fefcfcc0feff94e954f8f8f0fcf0c0809554fcaaa4e950fcf0f8955491a2409550c0eaa8a540c09540f0c080fcfe8da240c0fec0809554f8fcfcf8f8e0dad688d000d23240e0fc91a240aa94fe909554fe9554f8aaa0a950e554f8c0c080fcfcf0e080aa94d11000aa5400c0300c0300c03002e1b5a2a1945d430500e32e03d1414200ba99212ca1c0a944cf38a040c5a925a0e086f5e3a4874600eae5d6289180bd4041041040fa009500fff4 else (if i<2 then 0x344000a9f75d6db640dc221110ebb31110db5ad08913c30c2040cbb11100ae8a0e145140ae45550c30c0861644100000c71c71492380ffeedbb09a696384c240bd5e94a4068500a2328a208200c50a5294a0a552a8c09018080400b5ab5ad420fff440939894a480924000dd666000ff80a550c0c0d6b3941860cabacb28a040d638e17cc300ebde930800a4e51528e0ff522220a9522220909200f0def7bd8840ea54aaa99800d1a400aa00db5b40da1248a0008da490a550bca52920a0ffe4eda98000f2b6596124408433333080a500bdeef7bdc0def7bd51009647de48c080feee888000b5a69a641040fed63680aa408c4622f0381bf81000c626f739c0ba111100ad4821040091a20099662220dac900ca876520ccccb94083100000a40000ffb2008e30c2081000f900b7755200db6cc0b2b2ababa19d02008d24489000fff8ffffff082080ff50bdee500000c5533110eeeee64089220087321100c091b648ce73983520c9999940db46408da24088853100dac880fa54b24690e4f3cf38e28091b240921200892248c3c2c10c08010000fffff883111110e080fcfedbba8610ccaaaaa0a000839ac18400e781040c30408c1ee4a440921240a9977730924248f0b49200aa94aa80a950e0b2baebaaaa009ca5084200b648d8a999651083c2108400ffed88b0928f8a8a898700fcd6b5ad60f0ab9ce00000caa8330088888840aa00fcf8e0f0ce739c9040aa999760001000800400000000000012c4c41c920c40fe852100b8887320941ad210409d140b1860c0a4e528c60088777550deb59cd240ff79bc62e08b98828c20ffba9850cb97641087763210fb9e37de038081a307183040ffef7c38e240b69a0b041000dac6c887776520d5a0b31440dba94320eddc5310feed84308bda728c40814a5188208bd28388209c5cc51c408c1ee62c60fb5ac8ef39b93c209c9cd28c40b52725a060d66938ad0099887320bb6432209c5ee5a0a08c60b384209b9ab39c20fc911100fea96520a2d2841c80a2585d71a000e8766320997522109450720420839a620420fea642208777653083d0731840ed865500ffd4fb48c8a753211087322110d646d0dc765310baa88660d646d0939ab51ca0de6f672920b09248dc9ee624c08cd921b1e3c38095759448b28084f3450c2040e6b1068c00a1d61758c0c08c1c420800d525182c60eeb1894500c52725a9408985502070409f162284e6c0809c5c5284008554c91c7140e4dec10400a9360c0646018098765420830c510840fbaaa860a258d84881809460d50820ad10009316521000aea8df64e240a64747184100c62ea41c00feddb730fe94ad1ee6a820d3d8c31040f98766208396b18820bd9eb49ca0feca3210dd3e5aa523c1009a58144d2040b552a171418000ef7955a9208d9240887766608c else 0x24cb9965208390718820fb5b48b292829060cc92629000d9732110c51ea4a060cba98730feba6430c522a4a0e0a9854210f8521110df68e18102c098753200b568e6a4209e060e38e340ad1ad62c80c7666520deb35a8c40ecb54310a98765108766440092379854d240aaa9876089e75c64f040a678c50400008605944cd240eea87620c091c5100000e6f7ab51a083dab40820e8b24814300087655310ed987420a4e6e5a020a9655540aaa97510e6ab383560ebbb8610fdc41000fb52409ce6d52500995422209492618c00866621008c1ee08400a940f900aa8755309974440083147208209e275c68b040bba600009462f739809235534c4000cd60e7314081c6554c6080f4444200bad698186080c70aa764610096c52932444500ec987210b56b07b9c0c8643210d654731420a3dab39020ce6ee6b140c4e4e41040baaa872085221110a5273828408c60520c409080000000920795482080a95284d0c10000fd00b69248b5200094a4d29420b1b44883dab20c608c1c528c00aa999500f0909200adb600db6c88dc75542099c2108000ada488dca85550fffc8d8000c3d49398a0a6971740f240ecc54310bd671834609246808a94630000c646d7595000d1104050408100ddcbbb009420f7800099951100b2baeaa8c2408c6318800095509550d550966332109406308400945ee72c00dab6c0aaa99880e6a8c60400dad4888c631420609236c0f0ea40faa0fd5088a243082080d22248fd009cde00000090009990000099888710db66c8aaa4a28a27616480d6d918ff0091b600aa9111108c18210800fb6c90dcc11000d6c8909500a800ec711110b52440b6924091b6d091b6c0921248fce0a540f8fc88876610c62f7bb0c098886500820810289040f9f3be620343808e365549200089121428300800bb8888808e0811))
def q10ph (i : Nat) : Nat := (if i<2 then (if i<1 then 0x10f8df0010f8df0110f0de8110e8de0010e8de0110e0dd8110d8dd0210c8dc0310a0da811090da011088d9811078d9021068d8021058d7011050d6821040d5811038d5011030d4821020d3811018d3011008d2811000d2010ff8d1810ff0d1040fa8cf010f98ce830f70cd020f60cc030f38ca820f20c9820f08c8820ef0c7820ed8c6830ea0c5000e98c5020e80c4020e58c3020e40c2030e08c0820df8bf830dd8be020dc8bd020db0bc020d90bb020d80ba020d68b9020d50b8010d48b7810d40b7020d28b6020d10b5030cf0b3820ce0b2810cd8b2010cd0b1820cb8b0810ca8b0010c98af820c80ae820c70ad810c68ad040c20ab020c00aa040bc0a8040b78a6020b68a5030b40a3820b30a2820b20a1820b10a0820af89f830ad09e010ac09d830aa09c020a909b030a7099820a5898830a3897020a2896010a20958309f8940209e8930209c8920209b0910209a0900209908f0309708d8209588c8109488c0209388b0209208a02091089010908888208f8878008f8878208e0868208d0858108c8850208b8840208a0830208908202088081020870800108687f8308487e0208387d0108307c8308007b0307c8798207b0788107a878030770768307487502072874020710730206f8720206e8710106e0708306b86f0206a86e0206906d0206806c0306586a820648698306286802061867020600660105f0658105e8650005e0650305b8638205a0628205886181058061010578608205605f8205485e8105405e0105305d8105285d0105205c8105185c0005185c0205005b0204f05a0104e8598004e0598104d8590104d0588304a8570104a056800498568104885600048856010478558104705500047055010468548104605400046054020448530204305201042851810420510104185080041850810408500104004f8103f84f0103f04e8203e04d8103d84d0203c84c0203b04b0103a04a8103984a0003984a0003904a0103884982037848800378488303584702034846010340458203284482031043810308430202f8420102f0418102e8410102e0408102d8400102d03f8302b03e0102a83d8002a03d8102903d0002903d0102883c8102803c0202703b0102683a8102603a0002603a01025839800258398102503900025039010248388002483881024038030208368201f0358301c0340101b8338101a8330301883182017030800170308201482f8201382e8101302e0001302e0201202d0101182c8201082b8200f02a8200d8298100d0290000c8290100c0288100b8280100b0278100a8270100a0268100982601008025810078250200682403003822800030228200202180002021800018218a00001c88110818870d6015060bc812060a200f0508b80c8704000906022806060070030200300202002001020000000 else 0x5682a4c0667124907647a458563d2430662a2400561c23d875f1a3a045e6a38055dea35845d4233865bea30855b522e035b222c855a822a065922270657ca2405569a2184561a1f8255f21e85554a1c05546a198453ea1785535a1505529a1284520a10874e2a0d064cc20a0749ea06854902040348c202844872008547c9fe0546c9fb864581f8834551f7064449f40443c1f2044379f0054271ed854191eb0540b1e8854019e6053f21e3843e99e1863d51de843c51dc833c21db043b59d9013b31d8853a49d6053989d3853891d10537b1ce863641cb853569c90434a1c7033449c58433e1c3853351c1043309bf0332d9bd8332a9bc043251ba0531c1b7843161b5833131b40430c1b2052ff9af852f41ad032ef9ab822ee1aa832ea9a9012e99a8832e71a7032e39a5802e31a5822e09a4822de9a3842da1a1842d599f832d299e032cf19c832cc99b032c9199832c5998042c1196042b8994032b6992822b4991822b2190842ad98e832a998d042a298b0429d1890429818701297186842921848328e983042871810328397f8327f17e0327c17c8327517b052689788525d1760225a17503257973842511718424b16f8324716e0424096c05235969832321680422a96604226164032239628321f9610421915f0521015c8320a95b04205159041ff957001fe957041f7155031f3953841ef951821eb150841e314e841db94c841d714a811d614a041cf948051c7945851bf943021ba942051b213f831b013e031ad93c831ab93b041a41390419c1370419513504191133051881308318492f0418092d0317c12b8317612a03173928831709270316e1258216c9248216b1238216992282168921831659200216411f0316211d8116191d0116111c8016111c8216011b8315e11a0215c119031599178315711602156115011559148215411381153913011531128015291281150912011501118114f9110114f1108214d90f8214c90e8414890c8214790b8214610a821451098114490903142907821419068213f9058213d9048213c1038213a9028213910182138100821370ff811360ff011358fe811348fe011340fd811330fd011328fc811318fc011310fb821300fa8112f8fa0212e8f90112e0f88112d8f80112d0f78112c8f70112c0f68112b0f6021298f5021288f4021278f3021268f2031248f0831220ef021210ee0211f8ed0211e8ec0111e0eb8211d0ea8111c8ea0111c0e98111b8e90111b0e88111a8e80111a0e7811198e7001198e7001190e7001190e7011188e6811180e6011178e5801170e5801168e5811160e5011158e4811150e4001150e4011140e3801140e3811138e3001138e3011130e2811128e2001128e2011120e1811118e1001118e1011110e0801110e0811108e0001108e0011100df801100df8110f8df0) else (if i<3 then 0x47f0c3a847eb438837e3c37027e2c36007e2c36067cec33037cbc31827ca430837c842f047c242d057b842a807b842a837b4c29047ae427037ab425827aa424827a9423847a04218379dc200379b41e8379941d0379641b8379441a01793c19817934190279241801791c17817914170478bc150577fc12847794108676940d8772440a06712c07076e5403846dfc01866cdbfe866b8bfb846b23f9846aabf7836a7bf606696bf30468ebf106676bee0665fbeb0664f3e806636be50462f3e30661c3e0075e93dc865c93d9855babd709513bd2855083d003504bce854fbbcc034f93ca844f1bc8824ef3c7824ee3c6814edbc6014ed3c5854ddbc3064c4bc0064aa3bd0549bbba854903b8044853b6044803b40347dbb28047c3b28147b3b20546dbaf8246c3ae844663ac83462bab02461baa0345eba8834593a7024583a6034563a4824553a385446ba1024443a00443d39e0641eb9b0441ab990141a398824193978540db95053fdb92863eb38f803eb38f813ea38f043e2b8d063ca38a013c7389833c3b88003c3b88023c2b8709331b828531eb800431937e0530eb7b8330cb7a0430837803303376842fd374842f6372842f0370832ea36f032e3b6d862d236a822cfb69842c9b67832c6b660826cb620326ab6082269b5f82267b5e86247b5b8224635a8523ab5804234b560422db540322bb5284226b50812253500321834e8520bb4c0420534a03200b48831fdb47041f9b45031f6b43821f5342831f2341061d533e031d233c831d033b031ce3398816cb358316933404163b3201161b318116133101160b308115fb300415732e04150b2c0214fb2b05146b2886129325851203230311e3218411931f8011931f8311731e01116b1d8311431c00113b1c0211231b0211131a021103190110fb18860f9b15850e0b13030de311840d930f850ca30d030c6b0b8806eb078505f3050105eb04850543020404e3000004e30004049afe02048afd010482fc81047afc010472fb81046afb0503a2f8840352f68d0342f0059882ed84980aeb8497aae985971ae70695e2e405953ae18494d2df8593fadd0592e2da85925ad80491dad6049162d404911ad2068f1acf068e1acc068c22c9068ab2c6038a72c4848a32c285893ac00488cabe04881abc04879aba058702b785867ab50585e2b285854ab00584baad838482ac05838aa98582e2a705821aa485812aa20480e2a00480829e057fea9b857f4a99057eaa96847e2a94847daa92857d0a90067bc28d047b4a8b047afa89057a5a868579a284047922820478e28005784a7d8477d27b8277b27a83777a7904770a770476ca75037672738475fa718475926f8375526e0574b26b8573d269037392678572726507700261866ed25e866dc25b856cda59066b8a56056b0253856a22510569324e8 else 0x2d23d4e84d1cd4c85d1454a03d1054885d0554605cf854384cf154185ce3d3f04cddd3d04cd5d3b05cc9d3884cc3d3684cbc53486ca0d3184c9ad2f85c8f52d06c7752a05c6cd2784c6652585c58d2304c4dd2104c4651f04c41d1d06c2fd1a04c2751806c1251506bfbd1206bead0f04bd950d06bbf50a05bb0d0785ba5d0506b8750204b8350004b7acfe05b6f4fb84b68cf984b60cf785b524f504b48cf304b3fcf103b3bcef85b324ed04b2cceb05b23ce884b1fce685b174e402b15ce302b13ce204b0ece004b0a4de05b00cdb86aeccd884ae6cd685add4d406acacd105abdcce86aad4cb84aa54c986a8ccc686a734c387a43cc004a3bcbe05a304bb84a2a4b985a1bcb705a114b485a04cb2059ef4af849e8cad849e3cab859d7ca9059cf4a6859c4ca4069afca107984c9d8298349c83980c9b0397e4998597549703972c958596ac930595e49084958c8e8195848e0395648c83953c8b03950c8984949c878593ec850393c4838493548182931c808392fc7f0592247c8690dc7984906c77858f9475038f7473858eec71068d5c6e078a1c6a8489b46885891c660488cc6406876c6105868c5e8286745d8286645c82861c5b8485cc5985853c570584ac5483847c53048424510582ac4e83827c4d0581f44a8381d4490181b44882819c4782817c4682815c4586804c4283801c4102800440057f6c3d827f5c3c8))
def q10r (i : Nat) : Nat := (if i<7 then (if i<3 then (if i<1 then 0xd06cd06bd06ad138d14fd137d13dbcb6d127b86ed0a2d06db86ed06db86ed06dd0ded06cb86ed06dd06cd06bd087d085b86ebedfd06d96ded06cd06b869bd06ab86ed06dd0ded06cd06bd06ad11fd06ed06dd06cd06bd11bc153d06a891aa2bad069d06fc26ed06dd06cd06bd06abd52633dd0dfd06dd06bd06ad139d13dd127d165d06dd06bd069bf33c093d06fd06d7cded06cd06bd06a8739d06dd06cd06bd06ad069a332be8ad085b86fd06ed06dd06cd06bd06abf1ad069d119c138a332d118c14fa331c13da336d06fd06ed06dc0ded06cd06bd06abf1ad069c139bf33c0d9c145c0adc13dd06fb86ed06dd0ded06cd06bd06ad11ad069d139d133d119d138d132d09fd087d085d06ed06dd06cd06bd06acd1ad069cd39cd33d0d0cd38ccadd066ce91d06ed06dd06bd06abb38d06cd06ac13dc12cc26fd06ec06fbedec06cc06cc26cc26bc158c13dbeb6d0b0c127d122c26fd06ed06ebedfbe6dbe6cd0a1d122c26fd06ebedfc06dbedec06cd06dd06bd158d144d13dd127b86ed06dd06bd158d0a2c06dc06dc06cc06cc06bc06dc06cc06bd0a1d0a2d06dd06cc26dc26cc26bc068c267c158c13dbeb6c12cd06ed082d0a1d06eb46db66cd06eb46db46cb66db66cb66bd082a6a2d06fd06eb46db46cb6ddb46bd09fd082d0a1d06ed06dd06cc0d4d06b8edac0d0d067c091d06fd06eb46bb467c14fbca1d06fd06ed06dd06cbd4fbd3ccd58b46ed06dd06cd0ddd06bd0dad067d14fd13dd122c26fd06ed09fd0a1be6dd122c26fd06ebedfc06dbe6cd06ebedfc06dbedec06cbe6dbe6cbe6bd0a1d122c26fd06ebeddc06bd06ec2dfb46dc2deb46cb46bd153d0a1d122d06fbedfc06dbedec06cbeddc06bbedcc06abe6dbe6cbe6bbe6abe68d122c26fd06ebedfc06dbedec06cbeddc06bbedcc06ab539c068d09fd0a1d06dd06cd06ad067d158d14dd13dd12cd06dd06cd06ad0dad067d13d09580f4d093d0b2cd06cc14dc46fd06cd06bb757c543b72bc06f1fc91fea23c619b8158b23e719cd1fbd118e1fac238511ef0fb81d8b13d31394bf85c1ca17cabf97bf8ebf85b7a1d1d5d1d4d1cad1d3b794d1c9d1c1d1d8d1cdd1c4d1bdd1ac1bc82bc001a11bed11d51fd41fca1bd315941fc911c11bea0fee19dd25ca19dc179b15d315941fc90bc11bea11db41c025ba01a11dca00653a64022e002e3264321f3c1f161f022900296a6406363c1f0c36321f0636321f0236321f4a223c362c36663600644c210805463666362c3666366636463666365e224a2240225e225e22463666365c1f363904393e39102202093e2c342d32393e330c4f4e3840292c392c33342d5236523652365e6c5e6a58670b3c5e6f3c6c5c6c4a6b4c6c3e6b5c6d5c6c5c6b5c6a5c6f406b40695b213e6d3e6c3e6b3e6a486e3e6b486a031a5a695b215e6c5e6b else (if i<2 then 0x3952be6dbe6b171abe692d331b1e1d57d06ed06dd06cd06bbf49bf1ad069bf33c4cdb727a26dd06dd06da4ded06cd06dd06cd06bc0a2886c886bd0b6d127d06ed0a1d06eba6dd06eba6dba6bd087d06e86dfba6dba6b629bba6ad06eba6dba6bba6abb1fd06ed06bd11bd06a671a88bad069c0a1d06ed06dd06bd06abd52ba6dba6dba6cba6dba6cba6b9485ba6dba6cba6bba6ab522886d886c886b886aa922b86db86bb86ab869b522be6da26cbe6bbe6a96673957314cd06dd06bd06ad069d157b489d13dbe6dbe6bbe6abe691f572343233c23352289a46fd06dd06cd06bd06ad069a332d067b4b6b8b0b4acb4a7b4e4bcb6d06ed06cd06ed06dd06cd06bb885c2a2be6ebe6bbe6ad0a0d06ed06bd06ad0a0bd1fd06dd06cd06ad158d12cbe6ebe6c3cd4be6bbe6a2d1abe69d11927383c91be6f7a6d7a6c7a6b7a6a3738c0a0d06ed06dd06bd06ad138d14fd13dbcb6b527d06ebe6dd06ed06dd06ed06dbeded06cd06ed06dd06cd06bba87c2a2be6e20dfbe6d20debe6cbe6b2e9bbe6ad06ed06dbeded06cd06bd06abd1fbe6ebe6cbe6bd11b4353be6a271a38babe69be6ebe6dbe6cbe6bbe6a4352946d946c946a9469268ab6a1d0a2be6fbe6ebe6d33553ccabe6bbe6a1f1abe6943394d331921be6f886e886d886c886b271a88692f3342d93545d09f24931aa1be6fd06ed06dbeded06cd06bd06abf1ad069bf39bf3396d9bf45c33dd0b6d06ed0a1ba6dc922d06eba6dd06eba6db8deba6cd06eba6dba6cba6bd087d085d06e96dfbc6d96debc6cbc6b869bbc6ad06eba6db8deba6cba6bba6abd1fd06ed06dd06cd06bd11bc153d06a671a62bad069c0a1b722c26ed06dd06cd06bd06abd52d0dfd06dd06bd06ad139d13dd06dd06bd069bf33c093d06fd06da4ded06cd06bd06a8739bf22d06eba6dba6bba6abb1aba69d139d133d06dd06cd06ad069b738d067d06ed06dd06cd06ab738d067b73dd06ed06dd06abf1ad069b739a533b73db4b6d06ebc6cbe6e886bd06ebc6b8b1fbe6ebe6bd06ebc6dbc6b891abc69bf33be6cbe693f38be674091be6fbe6ebe6dbe6cbe6b271abe693738be67d1184b31273d1f22d06ebc6dbc6cbc6bbc6a891abc69bf39bf33bf38bc67b697b687be6bbe67be66be6fbe6ebe6bbe67be66234c2727ba6ed06bbf1ad069bf33becfbeadd066b4e2b4b0b4acc0a2bc6dbc6dbc6cbc6dbc6cbc6b786d786c786b35539c6abc6dbc6bbc6a7739886d886c886b886a8867354f373dbc6dbc6cbc6bbc6a7739bc67d06ed06ed06dd06ed06dd06cd06ed06dd06cd06bd085d06ed06dd06cd06bd149d093d06fd06ed06dd06bd06ad06ed06dd06cd06bd06ad145d13dd06ed06dd06cd06bd06ad138d06ed06dd06bd06ad138d0c5d066d06ed06dd06cd06bd153d06ad138d067d0b7d0a9d066d14bd06fd06ed06d else 0xb06fd0ded06cd06cd06cd06bd06ca26cbe6b4491086fbe6b3a85086fbe6c494d0a6fbe6cbe6b086fd06cbe6cbe6bbe6cbe6bbe69be6cbe6bbe69be6cbe6b03571516114c1543013c190dd06cb8b5be6cbe6bbe69d06cd06bb8afd06cd06bd069b4b5b8afbb2fb4a6b726be6cb721c921b721bf16bf0d8f21b721a54cbf43bf3cb73db72cd0d8c13dbeb6d0b0c130c12cd0a5d14dd0b6d136d12cd06dd06dc958b13dc92cd06dc158c130d158d13dd0b6d136d12cd08ad121d06fd06ed158d14dd13dd0b6d136d12cd08ad06fd06ebe6dd08ad06fd06ebedfc06dc06cd06cd06bbf57bf4ca543d06cb758b72cd06cd06bc158d0bdbeb6d0b0c12cd0a5c125d0b6d136d12cd122d06ebedec06cd06dd06dd06cd06bd06dd06cd06ac158c13dc12cd06dd06cd06bd06ac121be6fbf4dbf3d9d2cd06ed06dc121be6fd06ed0dfba9cd06dd06dd06cbe6fd06ed0dfd06dd0ded06cd06cd06bc121be6fb46bbf58bf44bf2cd06ed0ddd06bd121d0a2bc6fbe6ed06dd121d0a2bc6fbe6ed0dfd06dd06cbe6ed0dfd06dd0ded06cd06cd06bd121d0a2bc6fbe6ed0ddd06bd0dfd06dd0ded06cd0ddd06bd0dcd06ad0a2c06dc06dc06cc06cc06bd0a2d06dd06cd06bd06ad122d06dd06cd06bd06abf57bf4cbf43a53cd06dd06cd06ad069b758913dd06dd06cd06bd06abc69c158c13dbeb6d0b0d0acd0a5d13dd0b6d136d122d06ebedec06cbe6cbe6bd08ad121d122d06fd06ebedfc06dc06cbeddc06bd06bd06ad122d06fd06ed0ddd06bd0dcb49bd06abc6ed0ddd06bd0dcd06ad11fc6a2d06dd06dd06cbaa2d06dd06cd06ad06dd06cd06ad069d0a2d06cd06ad069d067b66fd06dd069d06dd06cd069d067b758b66fd06dd06cd06ad067d06dd06cd06ad069b758913db66fd06ed081d06ed06dd06ed06dd06cd06dd06cd06ad06fd06ed06dd06cd06ad09fd081d06ed06dd06cb753b6b8d067d06fd06ed06ed06ed06ec06dc06cbe6dbe6dbe6cbe6dbe6cbe6bd06ed06ec06dd06ec06dc06cd06ec06bbe6dbe6cbe6ba522d06ec06dc06cc06bc06abf3ad0b6d127d06eccc4d0b6d127d06ed0a1d0b6d127d06eba6dd06eba6dd0b6d127d06ed0a1d06eba6dd06eba6dba6cd06ed06dd06bbb27d06ed06dd06bb927b485be6fd06ec09fc0a1986dbe6fd06e96dfbc6dd06e96dfbc6d96debc6c886d886b2d581527d06e96dfbc6d96debc6cbc6bc085d06ed0a1ba6dd06eba6dd06eba6db8deba6cd06eba6dba6cba6bd085bc6d8adebc6cbc6bbc6abcb6d06ebea0d06ed06cbe6e2cde666c666bd06ed06cd06bbd1fd06ed06bc26ec0a1c26ed06dc26ed06dd06cc26ed06dd06cd06ba685bc6dbc6cbc6bbc6ad06fd0dfd06dd0dfd06dd06bd06bd0dfd06dd06bd06ad139d06fd0dfd06dd06bd06ad139d06fcaa1d06dd06dd06cd06bbd1fbe6dbe6cbe6b7f49)) else (if i<5 then (if i<4 then 0x986d3ade986c2d1a98693b33d1193b329067574f0d1d2b56234b2f342cb020ac2ca1986f906d3ade906c906a17391d38906723561f4b2f0cbe6e986d32de986c986a211a9869d119133827329067294f1929051d1b561b34213d986fd06ed06dd06bd06ad138d13dbe6ebe6dbe6bbe6a27383156d06dd06cd06abd39cf58bd2cbe6ba66fa66fbe6b906cbe6dbe6bc26fb86ed06dd06bbb58a46da46ca46ba468a467a691b4a1806fbe6cbe68be67a66fc06e8edcc0688edac067c06fd06eb46c8edc8edab467d06f966d966b9668be6cbe68be67be6bbe68be678ca1a66fba6ec06bc068c0678ad9b4b0bd2c386fbe68be67a66fd06e6ada8867c06fd06dd06cbd39cd58d06ed06dd06cc0ddd06b8edac13ed067d085d06fbe6dbe6cbe6bbe68be67a66fbe6da739be68a66fc06e8edc87398ee2c06fc06e8edfc06d8edc8739c06e8edfc06d8edc8739c068c06e8edfc06dc0688ee286b0c06fc06e6adf886d6adc873dc06fbe6dbe6cbe6abe68be67c26fd06eb46db46cb46ab4dab467b53dd06fd06cd06cd0a5c2e4a86ca86bb522a26cbe6b394c534352907a6c7a691eb6072cb4a5be6c0f3d006fc06cb522be6c194c986ca06918b6012c28b60336052c066f086e866ebd1fbe69248a046fbe6ebedbbf1ad0698eda2aa2086fa26c24a2066fc33db6b6b92cd06e906c428abe6fbe6e906c38dcd06eb66c8edc8b1f906c9069528abe6fb66ed06cbedcbeda986b006f006fc06cbe6cc06bb522be6b4543986ba0691eb6b4b0072cb4a7b4a51325b46cd139be6cbe6b35500f58006fb522a0691cb6032cb6a5b6b6b92c086ebc6e891f9069248abe6fd06eb46ebf1ad0698edabe6cd06cd06bc0a5d06ca06c14d0006f646c10b8006fa06c23500b580b3d006fbe6cc06bb522be6b5343553c986ba069033d1eb6b4a7b4a50b58026fb522193ca069013d18b60758073d22b60136248a046f2a8a066f066f066e14df0a9c18dc129b866ebedfbedcbd1f07581cb601360b651c8a046f066f086e14df089c866ebedfbd1fbe691e8a046fbe6e34df1d1a8869d11e2d5735352081be6fbe6e8edfbedbbf1ad069b69fb68724a2066f0358033d1cb601361c8a046f228a046f066f046e0edf069c18dc0a9b866e8edf8edc8b1f8e6e8edf8edcd0a2c06dc06dc06cd0a2d06dd06cd06ad122c06dc06cc06ad069d081d0a2d06dd06cd06ad067a157bf4cbf3cd06dd06cd06abc69d067c158c13dbeb6c12cd0a5d06dd06dd06cd06dd06cd06abe6dbe6cbe6abe67006fbe6dbe6cbe6abe671358006fbe6dbe6cbe6abe671758173d006fb4a2be6dbe6dbe6cb4a2be6dbe6cbe6ab4a2946d946c946a21389467986d986c986a9867bf280358033d18b6032cb4a5be6ac130c127d0b6d136d127d06c114d092c0127c0a50ce4be6fd06ec704c12cd0a1bc6fbe6e else 0xbe6cbe6bbe6ac069be8ab721a66fba6cba6bba6ac13dbe6ac069be8ab721a66fd06e70dc966a991aba69c06fbe6dbe6bc069c921a46da46ba869a28ab721806fd06dd06bc158be6dbe6bc069be8ab721a66fc06e8edfc06dbedbbf1ad069c06fa4dfd06da4ddd06bd06e94dfb46b891ab469b721d06fd06e94dfba6dba6b991aba69d06fbe6dbe6cbe6bbe6ad06fd06dd06cd06bd06ac1219c6d9c6c9c6b9c6a9c677758a13dd06dd06cd06abe6cbe6ac069be67be8a906fd06e9c6c6edc9c6a9d1aba699c67b687c06fbe6dc069be67be8a906fb66e8adfc06dbedbbf1ad0698adac067c06fd06e90dfb46d891ab469b467d081d06fbe6dbe6ac069be8a906fd06eba6dba6a991aba69d06fbe6e9867986fbe6ebe6cbe67be6e9867986fa06d1b3abe6fbe6e173a32e4986fbe6e986d173abe6e986d173abe6e986d16b626b0986fbe6e986d133a986fbe6dbe6cbe6abe67d138d0add085d06fbe6e3ec49e6d9e6b9e6f288ad085be6fbe6ebe6ebe6e986fbe6e906fbe6e3ce22eb01cac986fbe6ed087be6f646d646c646b2527d06ed06dd06cd06ad147d158d06ad127bc6dbc6bbc6abe6dbe6bbe6a2d391b502d3e1b382527966d966c966b966ad06dd06bd06ad13d9e6d2ede9e6c9e6a2739213d9e6f946c946a94692b3933329467228ad085be6fbe6e986a231a98691d393333d1192b329067986f3ade906c906a133917389067be6ebe6cbe6a2f1abe69d11917383732be67be6fbe6e36debe6cbe6a211abe6917392733253dbe6fbe6e9c6c9c6a3b1a9c69213933332b389c67be6f646e646d646c646b646a1d1a8869173921338867b4d9d14f37583ec40ab640b004ac9c6f946d94692d3294672c8ad08510a1be6fbe6ebe6d1d1abe69d1192732be67be6fbe6ebe6d211abe693733be6f886d886c886b886abe67c0852aa1886fbe6ebe6dbe6bbe6a331abe6905500b3e1532ba6dba6cba6aba69bf32b867be8ad085c0a1d06fd06ed06dd06cd06abf1ad069d119c138a332d067d06ed06dc0ded06cd06abf1ad069c139bf33873dd06fbe6dbe6cbe6a2738be67be6e986d2ade986c24c1986a2d1a98691ebf27392b33d1191d382b329067091d2956234bbe6e986d2d1a98693533d1192b32906734d936ad20a99866151d3f56986f906d906b72672ad916ad1ca990662b562342be6e986d986b1d1a9869d1192132906732d91aa998660f1d2756986fbe6ebe6d2adebe6cbe6a331abe6937395733be6fd06ed06dd06cd06ad11ad069d139d133d068d138d067d158d06fbe6e3ade986c986a2d1a986927393b33d11921383b3290670d1d234b2f0c2b34986fbe6e986d986a231a986937393b33d1192b3290671b29111d2b562b34986fbe6e986d3ade986c986a2d1a98692f393b33d11921383b329067474f111d2b56234b370c2b34be6e) else (if i<6 then 0x902c3836222224333258322c344f242252622630442c342dbe2d141e2e02281e2a4fd026324d22362030081ebe062c3040223c62324d32442030322c3227324d2e302c2226303c2dbe2dd062d04dd044d02cd027d064d065d038be36d05fca65c02cc062c04dc044be36c030c02cc027c265621fd01fbc33be1ad019c02cc062c04dbe36c030c02cb465b422c062c030c02c8659c02dd059d02dd029c01fca62ca4dca36ca30ca2cca27c262c230c22cba29b462b430b42cbc62d057a602b421b421d03cd026bc62d021bc62c04dbc628630bc62b430c022c022c022a065b421c022b421d057a605b4218c21d03cd02bbc20b4214c228e62c0278e628844c0278665b65ab421b821bc21d04f864d8605bc21bc218658864d8644863dbe5fd021a062bc62bc62c04dc0448630c02cbc62d021bc62bc62bc62d039a062bc62c044b430be5ad021bc62bc62c044b430bc62a06da06a27393b33d06cd06bbe6cbe6b1565be6c886c4adf3ede886cbe6fbe6cc66cd06ba8e49c6cbe69468a0a6f0e6e886c331abe69129f026e14de906cc66ca6e4186fbe6c906c9069468abe6fa06c9869308a046f14a1b755c4cad06b96e4126f966bd06cc0e4186fbe6c0ca10f30072c052cd06bc0e40e6fbe6cbe6bbe690158be6bd06bd141d069be6bd06fbe6ebe6bbe6fbe6ea06b3f452560154220ae072e192a0d03be6ebe6cbe6b4b41b6d93f451b6019560d15114b15421aae032e3abdbe6fa06b9869be6e786b151a9c6938d90a9f2e87c0e4186f9869288a066f0ea1d06bc0e4186fbe6b7c6b7c69448a0c6f006e14dc0e9ba6e4186f1e8a046f34ba9869208a046f06a1133d172cbe6d0b580f3d0f2cbe6dbe6c1358172cd06dd06cd06ad0a7206fbe6dbe6cbe6abe691358173dd06dd06cd06a966d9669be6dbe6cbe6ac069be67be8ab4a1a66fb46db46cb467c158c12cd06dd06cd06ad067be6dbe6cbe6ac069be67be8ab4a1a66fd06ed06dd06bd06abe6e1cdfbe6dbe6cbe6b0ea1be6fd06ed06dd06bd06ad138d14fd13dbe6ebe6dbe6c28ddbe6bbe6a16a5b8a1be6fbe6e3ccf26ad9c660a9f2887be6ea06da06ba06a274e7c6c7c6b7c673a91026fa06ba067a066026fa06ba06aa066026fb46fb46fbe6a086fd06cd069d08ad06fbe6bbe692956d06bd069d08ad06fbe6cbe6bbe6dbe6bbe6ad06bd069d08ad06fa26ca26ba06ca06b31560315234b2342313b050c312a0b03a06ca0694288d06fc921d06dd06ad14ec13dc12cd06bd06fbe6cbe6bbe8ab721a66fd06cd06bc12cbe8ab721a66fc06ec06ec06eb721c06fc06e8ee29ca5c06fc06ec06fbe6bc921d06dd06cc158c12cd06fd06cd06bc1219c6c9c6ba13d772cbe6dd06dd06bc121be6cbe6bd06fd06cd06bc121886c886ba158a12cd06dd06cd06bd06abc6dbc6bbc6ad06dd06bd06ad06f else 0x60928365227422506651809d02b020912361236121a0a1ad05a30622a221e6216251458144d1a44083612252e253c445830402532054425022224440a25006500440065d03c0609283642270465d03c020908360e36d05fd05c1862041f04620a4d0665325f1e62021f345c1e62021f0c36d05f325f1e62021f181a061ad0611862061f0462064d0a4406360030002534611e62021f0e628e61862f041f18620462044406270836d05fd05c1862021f0062044d044402360030042c00270265325f1e62021f2a5c1e62001f0e621462c022c022a64da644a2367e30a62c7e25a065c022c0227025a065a644a23694309425a065a022c022d057c005d03cbe09be09d02ba209a036064d06440630062c0627022504651a250465064446302e25066500220222144d14441030102c1027142512650022202512651044483046272e2512650222d0572205d03cd028d02b0e25be35d030d025bc36d02b4a251064b462d0563005d03b52570836ca30ca27ca25523c08440836c230082cc227c2251c3502351e35382b0c36b830b827b8251c35d030d025d030d025be35d030d025b635d025a60ed03cbe09be09d02bbe09a209a036a030bc36c044be09bc36d05fbc36a062d01fc022d0578e178809be09d02bbe09a209a036a025bc369c25be4dbe44a630be2ca625a662be62be62be62be62be4dbe448630be2c9c25a265be62a662a862c062c062d04dd044b430d02cba25c062c022a64da644a2367e307e2c7e25a065d057b421d03cbe09a209a036bc36d05cbc62d01fbc62c044d0369c25d01fbc5cd062861fb64db644b630b62cb6258c65b625b665b644b630b625b665b662b64db644b62cb625b665b662b625b662b644b625b6658e4d8e30c03018441630a0629c4d9c449c309c2c9c44be308e44c030ca30ca2cca64c230c22cc264b430b42cb4649e36c230c22c8e62b430b42c98449e36d05fc0219e369e36d05fc0219c648e628e4db430b42c965f2e2132622862224d22441630122c222722641e65c0219462984d98449830862c98279c6420363e44262134623e4d3e441a2c2e272e64d05fd062d04dd044d030d027d064d065402124390839d01f02390e39201f02391c12161f0239be12244d2c622c4d2c441a302c272c642c229836b422d05fc021b422b4229462984d98449836983098279c64b822621fd0213c4d3c443c363430202c322738643065d057242cbe09d00406204236382c20361a2c34622e441c36182720652c222838162134442036d022d05f2422d022d022242724652062284d28442836163012272c6420652422161f201a3c593259d0212059342d161a122dd01f0a2d0e2dd01f122dd03c2630062d201f0a2d0a2d9e36d05fc0219e2c9462984d984498369830862c9c64621fd01fbc33be1fbe1a90649044b630))) else (if i<10 then (if i<8 then 0xd022d022202da622d00622300c2786380636c039c02d284e3827be362827be36be363827be362e27be364236be36b422c822b422b4221e531422c022044f2a2230360441383604390438c022002dc2616a3d2836a62238222861381010443a302836d02228302836303630362a621636043410340a340a340408a236a03044251e64a025c6228c21284442304225c221b42130094230282c4225b4212805b42130053625c2212805b4210808c221d008000808080208a0210c0504080c081608020842350808522fbe084235522f5226a2369c25a236a030be36a622a0627625a062a236be36be36a236d039be3690626636be36be36be5fbe5fa0629c25be5ea0628630be36d01fbe1abe1a9c1a9c25be1abe1abe36a622c022c022d01fbe1abe61c03da236d01ec00690629025a0626230be36d01fbe1aa062be36d01fbe1abe36d01fbe1ac621c81f7a628e61864da2369665d01fbe1a945fa062a022a022a022a022a0629c25d01a901abe1abe1abe1ab636d01fbe1a6a629062b636d01fbe1a90629062b636d01fbe1a90626e622630c0225e44101f2635123ad009382c3e442836282cd0093009382cd0092209382c1a3016211630d021d02126631a3d1a361a273430d021063306334236202c8a1fd01b221a1c1a0439d022961ab422b41ab409141a1409be1ad019302c0e392a381a302421ba2206391633281ad01948442265d06508391a33221ad0190c33321a10391a33d03dd027d06510332c2126212c21362f2e2fd02b10362c441a302e64d0651a33381ad0191a391630d01f0633201f3c2dbe2dd0273a223222bc271a391a333a22b422981ad0196221ba2908390e2db4210c22003914332822324f1c22182d3830003912330e2d1639222d1433d0211e450c2dd021d021c421d0220c390c33d0220c2d8a22d006383038279822c4211033d0221e2d284d38301e65c23dd06512330e2d26022a59342d2430202c0c39102d1c023e44263008391a331e65c227d06508390e33c0273a4f18363a272a561e2920392c0c242c2c2114299465003906330c2dc002c044a236c030c029c058c04dc044c03dbe36c03030562a29be36c621be36a622c022be6168368627a0626230b421be36be36be36a065c621be36a622c022c022bc628e62a2368621c0228e618644a2368e5ca0628e5aa062be36be36be36a6218a61c42fbe36a0627a65a0658665b421c8218c21be36b421a0659c2d7a627a628c21d02d66366a5fa0626a5c8639a062be36a622c022c022c022c022d022c022a0629462bc62c021bc62d005c26430055409d02b060928364e2506651c09d02b020912361236181a121ad05a066208441a1a021a8261001f04620844043d0636003002251862066204442636d05c381ad05a52622e6220442036263020651a363a175409c82b else (if i<9 then 0x2460422e1e60262e121f2e2ed02a10360c2c322722644260202e001a006426252a300e620e640c621e270e642a6332272264d05c00640064d02d1e440a21c02712622e251221c0271c6202211c1f0a210a21a02704210a216227121abe1a1221c0271c62382504210a211221c0270421121f0a21a027166238250844064404443430064414601460d03830291860002910601860146006292a35302f2e363a27a2363027a2361c0530241c65a0248c1f3a5f001a161a101a445c001a2e35021a305abe1a3835402f0064026400640064041a021a021a081ac6228c1f12440065d01f2c1a061a021fd01f181ab627121e2a64123600647a36a8229264c0222a642209183600641836b41f021a0036185eca1f181a0236cc1f381a181a1662be5a16361435c830c825300904090c363c364836be36440906090c360c210421124d0a6404210221c022c022c022c0224c0902090836d022c022083638368a1f341a1c090c1a1c2c20360222a622c61f341a081e0e6210440c36ca1f181a48090e360c36be36440912360a64c022c022c022c0223a090c363a36b61f2836d039b41f0a1a2036d01f481a2036d01f481a1435b430b425be36a621c0210c210021a021c021c022c0223a09020906360e64a063c02228630c364c3630210c4ab01fc0220e362e273836b41f081a1636042200220022c61f0022481a06621e25d01ad01fd01fd01dbc645062384434300e2e0c030a360222c41f0422181ab627ba274e1e3e06c0222209183602641836b41f021a0e360636bc1f181a186212361435ba25be364409080912360e640c210021022124270a64c022c022a063c0222a63d0090e364a36c81f104ac022123628273836b41f081a2036d01f481a1c36042200229c220022c81f301a30623c61021ebe6126120e62144d2e250a3602220422bc1f181aba2722642209183600640064c02292640c36b41f021a023d00361862041f04620a4d0a44102c0a27185c0a1b1e62021f8e5cc41fd01b181a18628e5c0236042104211035a20916092036c027be36d027d02708091c36c027be36d027c021be0916092036c027be36d027c021c021d027d02706210e21be270a2112218627a021c021c022c021c022c021c022c022be0916092036c027be36d027c021c021c021d01fd027a236b421b421b421d01fb421d01abe1abe36d01f981abe36d01fb621be1abe61c02fc058a236c02c7625be36d01fb621be1a7a62be36be362636be36be362636be360447d0221c361e3014363a2cbe368644be36282cbe363a2cbe3642442e36b42118391239be39be36b422c622b422b422302c2038384d28442e360621162dbe2dbe36c039b4220c4f1a22082d303602490e392c2104450e2d302cd021d021c4210439142d202d203606220422184f1c223a301c361c391c36 else 0x7555bb5898d5a122ba6f8955bb588954994a9953bb58bb4d94c1cd3dad58c558d06fc354c74ac553d158d14db555753d854dd13d8f27ba9cce6fd0de9f55c958d15898d5d06f9f30c355d158c354994ac553d158d14dd0ded0de5d55bcde9d547b479b4dba9cb555bb337745bedfd139bb58c33dc539c31ed139c333c33dd139d1398939671eb516d158d139cd166739b9398f559ecad133d133bd4dbd39bc6f7955bd589ed5bc6f8955bd5889549f4a9f53bd58bd4d94c177399ed45d399e91bc6f8f559eca9f589f4fbd58bd4d794f7958bd589d39a5d3afca7bc889debfdba5c8bfda9d9987b88dd9d19f9785cd97b9855dc7afcaa9c87bc05dc785bfafcac3d5d1ca9bd0a5ca77d07fc657be9dae7daaadd5b3d4cbcaadd6bbae57d89b975dcd47c455bd95b077a759ef7dca7bc09dca79c0699953d09dc69dbe63858fd1c38eafca8dd35dc047d355d387d193ed8dd587b993ed6fd5add36fd2a9c865d587ca87a187ed87d587d487ca63d34f97a5d331b87dca69d355c0b1ca73d373c183ca69ca6db8c1acd1c6b1b8a1d3a7bda7d3a7d3a7d8a7d39fedbdd497ac65ed43d589d489ca97d397c173eabdd4a1d3bdc1bbca73d3bbedd1d5d1d3c3c84fed51d589d489ca89d389d289c889c065c789bf65d065bed1d8bb9cbbedd1d2c3d5abd4c3cac3d3c3c1639b97d397c197ea87c063bad1edd1d5d1d369d575d369d28bed99d273d05bcfbbd899b68bb095ac8bed91d459d073be3dcfd1c077cfcdedb3d5d1d3cdd2bdd1bdb975c891cd8bbd99b6bbb08bef8bedbbd399d26bed91d58bd399d275c86bed91d599d275c88bd875b08bed91d58bd399d35bc8d1d37bc08dca83caa9c04dd5afd4afcaafc17dc649b89f8543d52fd037c64dd57dc98dca8dd383ca83d3a9c055d383d3a9d357d36dd343d3b3c65bb88be7d18595d599d0b3c68be7d1859bed75d59bd3b9d383d353b885cab1ca6fd5afca8dca73ca89edb5d489cad1cad1d3d1c9cbc197eaa3edd1d5d1d4d1cac5c1699c85edcfd4abd2d1c0c3cac3c17fa1c3d5c3d4c3cac3d3c3c1c9cabdd38dd3d1cabdd3d1ca879bcbc9c7c18beac3c8c1c083bacf9fad8e89d565d489ca89d389c989c1d1ed9fed95d5cfd4d1cabdd3bb9ccbd5d1d4cbcac3d2a5c8d1c0b5a187e5d1a2bfedd1d5d1d4d1cad1d3d1c9d1c1d1edd1d5d1d3c3d2b7c8d1979d9cc7edc9d499d399c1d1d2d1c0c7babdbf899cb5ed89d5b5d489cab5d2b5c0799fcd97bdcad1cad1c8d1c0b99fd1cad1c8c3c08dcad1ca9dd59dd49dca9dd3c1d5c1d4c1cac1d3d05a3008d01a281ad01ad05ad01a1865381a3008244e000f020fd02d080f0e0f245824610a0f222722643c6018640c64001ad05a006430303a250e621a30021a0c621825181a0e1a121f36303625021a221a341a0a1a1862382512622c302863d02e)) else (if i<12 then (if i<11 then 0xbb2798d5994aba6f9958bb44753d7558994475588b3d649b7b3d9953869b96c1b8c1b8c196c198c1b8c1a539bb3d9958969c729fb4a1b8dec539bd38bc6f6d538b58bd3996de68df72de78d4649b391ac4d4af52c4d4ab33729382dec4d48339b8de6d1a9b39cf33cd38c1329f1ebb4cb73963388f448b3db8de8b1ad139d133d138d132bac4bb44bb3d8f559ecaaabacaa1b755c4cad152b755c4caa9398f55791ac533c532bb559958cb33aababca1d1529139d133a8dec33996de791aaf39c53372beaf38c532b8debd1ad139d133d138d132ba6fbd1ad133d132bb54994ac541c152c541ad3358d09d325a919941b133c93299415b1aa333c532ba91d0a18a6fc133a932c13394bed1328b588957b52f86a18957892f892bad58554f7558c152691ac533d132ba6fcb49995896dfbd53511aaaba86a1b6a2c352913970c1c5397d399739bd39bd39bb53c4a1c4a29752a953d15384a2a9526ca1cd4fc3338a93bb38d0ded139c333c945b53dcf32b2a9791ac539d133cd32b8d96cb7baadd0a9ba6fbd38bca9b8debb39d133d138c13259378b3dc953c2a19ea2d1529953d153d0c4d0a1c6a2d152554f8b58795378a1c9526b4f934f8b588b5266bf531aa933d132b8d954cf9aadb4a9bb42ba6f995490c074bfd13386bed132bb58bca9494f5558bb539ca17aa2bd4d9f3d9f279f58d153d0a1c4a2d152675350a1675272de591a8539ab334f38af329ce4a139594f794f9d4f894f8b58794f8a6db8de70d56ad3531a74d2ad3981334f38d132451d914b7734ba6fb1335553754f8b58b5538aa18b52a3399738474f613d5b3d4a93826f6f2c6f3d431a5693906fa74a7f4d8f55674a5150514d666f515566c6674f5158be6f7f55bf58a555a554a74abf4dbe6fa6d5bf3dbf58a74a72c1a5507f58a74dc14dc13dc158c144a72cc13d9f55a158c355ab54b14aa14dc74a94c1a94db755506f515542d5513d3958cd227f547f4a7f537f4d5d576d5585587e6f6158613d8558a86e56df58dcbee2806f45658358926e5cdfa8db571ad09f706f60dcc0e2aa6f473d5758aa6e42df42dc8ee2566f946fc6d5926f472cc3558d58c6d5926fad3d8d586d588d4d7493926f7158a6d57e6fa5557f58693d59497f507f4655587f4d4893686f833d8358592c8338833dab3d6d27ab3db358be6f7f55bf58a555a554a74abf4da6d57e6fbf3d8f279d58a74a6cc1a5506d588f4da46fa749a746bf4dbe936d44be6f7f588e6f8f556cc67f4f7758b8df7955bd586edf96de78d5d09f8a6f9f558b589f549f4a9f538b588b4dcaa0791ad0c4c5448f27c46f9f55d158c6d5d06fc355d158c354c74ac553d158d14dd06f8921cd219d547b479d58c5446d27ab1eab33bd30b727ab1eab16ce6fc8de9f55d158c6d5d06fc355d158c354c74ac553d158d14dd06f else 0x85587b36992cb86e96dcb8dbb91a94da6336952c8c6ea8db651abb2c6755632ca755a6ca8141c0c694bec14d866f814181453f58914d90937944906fa758a14177507b46473eb145736073565915734b9542592e7b588b2c77048b5679568b586f368c8acaa28a6f9b58746f68dfb66eb6db911a909f6e878a6ea8db691ad09fc087526f686e68df98db71045f4d592c7d165f58a9585f1671044b58592ca9584b58a958c30db557b54c8d43bf57cb16bf4cbf43d135d089892bbf26b358ad44b66f8b58b4b68b25d0e4bca19a6fd0a19a6f9b585b448b588b3dc958b13dc8b6c936c88ac86fc86ea4dfd06ea4dfb08a9e6fc755d0cac86fc86eb0df5c9cc755b0ddd0cab0dcd06e7cdcc0c1d0dbd11a7f558b3d7f58af58af3d8ab67b36ce8ad0a28c6fb48ad0a28c6f986f8c6eaedfaedeaedc649b8c6ea8db9f1a9e6e68dc98db8d1a6f5868b65f36c922c522c522c5226e6f4c6e4cdf50de66ddc86ea4dfa4ddc8dbb11ac945b35863368c6f526e60db371ad09f40915c81386f8c6e8edfa2dda8db651a926e6edf7cdd8cdb831a871e3757686e80db511a81455d614357914c90927b437b2fb3588a6e68df68dd92db8b1aa2e269586ecd68a58b3d6f368c8ac0a28a6f746f8cdd9adc933d686e7cdca8db686e8adfa8db8f585f585d5885586c6e46df806f6d5345538a6ea8db531ad09f686f8d308f168d586d166b586d4d553d8f588d58af2c5558af2cac6e5ede90d5666f7f5364bf555864bf55584ac74ebf7ec77cbf36bf64c78b58c4dfb0d596a54f4c4f43872b874463279d55a2dd42b9435770b98b58633869385158633d8b539d559ccaa2dd92dc689f474f54a1572d58df58dd615374a14ea23eb940c72ec74b2d995396df4ede5147c75386c498a162a24ebf76b94ebf714f62bf772d874f40bf78df78ddad5352b976c79cc776c74ebf46de56dc3d47915366c46b2d3cc756bfc55352dd44dc6539474f692c93588b588b2cd0dfd0ded0d5c2de872b872c9358a754c14ac46ea2dfa2dd9150c1468093c1446f5384a29eb854de54dc6147c7534ec456bf64bfa6b8b753b6a1baa246b972b8372dad5380b8632cad535cbf6958c553c55376bfc553746f826f5f3d7d42826f59567342706f952c7f3d81585f567542ab34aa88746f753d6158692c753dc06f5f55c0d5c14aa66f9d58c06fc158c14da73dc127c14cc14dc0c4c144c13dc12c8ec66cb86d38c14d813d8f588f5898cac091c06fc150c06f995594bec158c06fa755a6cac141c0c694bea74d8f509d58c06fc14a98c1a33a9955c0caa33ac13e7345793a993e5ab18091a66fbf3a9ab17758c06fbf3a9d58c14dc06f7d3a99455ab14b58a74da6938144a66fbf3a9ab1c158c14dc144c13d6cd35f3a6d53a758bc6fbc6f993d993d8f27bb44993dbc6f9f54bd58bb44bb44) else (if i<13 then 0xa6656435c065c022a622c022c022a622c022c022d030c022a622c022c022c022bc369e367822bc229661d01fd021b862d030d02cba63d01fd021d01fba22d02170584e1f7044861f6c2256369e2278229e22782c3e2748659854ba224e1f7454583392618e109a2170627630a02c8e1056106c63ba105444d0214e1f861f6c3d5a278a659a21904148339a219a218e659a2148279462984d9844983698307027621fba22ba22bc218e219a21ba2244229e219822bc21ba22706f452c4b4b7b425a8f5f0c312c4b1ac4d4594b9742728f593bab0c473d433b4b34448a526f391a373b3d34926ea11a6e6e611a8d606f4b4734472a5723593bd155bf3361585c9c8558ae6e8f55b3585358b755c4cad1555558d06eb755b755b3586d156f58af3d6cdc7cdcaf583758372c415890df90dd96df96dd8cdf8cdd686f5f5588be88b8894fb3586336952cb6b8854fc945ad4bb358932c514543424d2cc53fc7458943952c6741894585584f36c541b6b8974573568315974b974293583756375637564f564f56532c4d2e492a4f5673566cdf746e8d556e6e3f584d3d6e6e7cdfb5395b5896df72dd8cdf8cdd526f746e8b585358c0a1635875555145674b9b58c26fd139c53ead458556ab4bab429b586b566e6fc2df67567d457b42433ba50c4d3d633d55588a6e6c9c8d3d4d3d6c9c746e6ade532c553d6b586b3d373d8d583b58553d686e92db64bf4ebf64bf62c44cbf40bf64bf64bf4d3d4d3d72dd695848df5cdc653945584d3d4edd62a14edc4f39413d9d555358454f415846dc6b4f373d635050bf7d4f514f694f574f90dfc485b4a1a92767586758c297c2a2826f929792a2826f5a6f7cde7cdc74dac2a2706f706fc2a2706f70df70dc9edeb14d452c9f1ad09f806fa8de8c6e9f1a926ea91ac11e6a6e791a8a6e8b1a5b3d3f36713d686e451aac9f4893526fd155bed2712c6f30b6b6b7366f2cb727cd22cd36b727cc6fc758af3dc6b6c736c72cc68ac66faecabeba87168358ad44592caccab358cca2b755c4ca853d492cb66e6d55c46ec4dfaecab755c4cad15561588f55c4cab358b6a2b7558f55b3585b3d62b65f36592cc722c46e6a6eacddc4ca9136b46f9e6ec91ad11e9e6e8d1a9f586f36769caf30af586158af58af2caf589158b73db6b6b736928a8c6fb68ab66fb66fb66e92df90deb6dc649b7f58712c7f3daf4d8ab67b36af2cc88ad0a28c6f8c6eaede9e6e6ade98db8d1aaf589f3d8ab67b36732cce8ad0a28c6fcc6eb48ad0a28c6fcb55986f8c6eaedfcb55aedcb08a8c6fb86eb8dbb91a8c6ea8db9f1a9e6e98db8d1a835893589358c958c936c92cc26ea2dfca6e7cdfd06ec355cacad141769cc355cacad141a141d06ebedfbedda741d0dbd11a7f558b558aca6741b4c6b4b88b588945c541cb509745935895308a6f else 0x54085c086a36841ab21a7a1a54085e605860461d4a1e3c62b01f5c1a4a1f3e1f701dcc0f581e260f760f5010560f3c623630381a5e60600f5010443092368c1f441f8a1f3a646e4d8436ca36d04ad04a6a4db21a5e60c636c61ad036a0226a22a062ba25c836d036c636c6364a1ab01ac636a64dca368021a82194219421521a521ac436c836b221b2218a366621662168278c3d501a7260b41dd036b41dc83694229422501ab01f841f361f641db41d881d5012641d564d681fb6368e646e3690275664ba1ec00662306e22a8224c305627a64d54365c094864ca36683680215c21bedc780948648a218a21cc36ca36a036ac21aa21542c6636ba369a587636762c5625661a7460d036c83674229a22aa22661aa41dc93b62124862464d4225d064c21f76606262a022a022a06286308a1f5a1f9036b6366e366e218c36aa21ac21aa218e21682154216e216e21a821a821561a6c1a6e366c218a218c228a216a22563d4636562762306e3652216e4d6a3652366a36ae3d7c36ae27c406900686308c366a36804d98369822982252366836aa366a368c368c368c3688369c228a3d68368a2762308c368a39704d4236423990444c38d0397c607660586092368a368c368c368a368a3692228a227622cc3da4369a27b6069c1e68068630d0398c368a365236c439d039ba398439924d6222622262226e44921f5a1f60228c1a921f9643626292258e2e441a442c5a65741f9036a036ac4aac4a6a4d5236ac22821ad01ab01fae226c446c64ae229036b61f581a6236bc5eb01a9e1f7a628236b8256236b01a8e3d82276a6492229222ca3d80416e227e4156228a389e1f5a1f66415a226e1f6c64b44e542c5a65761f9a1fa0276e227a27a822aa2d8a649a21d04e8e2c8c64b0218c17ac219621d00988636a09b6208a36bc259a649a629a625a628a226836c84e602cc81fc81fa05fc8624a1fa05cb062401f62369e1f7a62ae1fbc5fa862481fbc5ca8624e1f383662229e4e382c36654c22681f6222661a8861aa1e9e1fca1e68627625d01eb01fc81e64127a1f5012401fc81ec81e8c1e561252005a62464d36258222742262629a1f9a1fbc5c92624c1f621f62626e4462303a3d44655c1f6a216a2292218a216a218c228c226a216a2264257a226a22484574228c224c218a226a224c21684d68444c2c68274021681740214021d128b4447021684d68228c229c22664d4c2c5821464f3a21702d2e47c621863f98217239403f864f702d42476647503f8c398a3992228a228a228a4d8a448a2c62276817b444862792229222c03d70416e53462290396e22364f642d4e3fc6396e39ac394c224c22c439bc39c439c022c022a622d030c0228022c0225422c0229c228010803076106c10c0107044704a9855c04a8e4d7027))))
def q10t0 (i : Nat) : Nat := 0xb3299a227799a559123388a116f1ac6ad9c66d9a6619765995651926458c62d8a61d866158460d82605805f17b5e9765d5745cd725c56c5ad6a5956458d625715b5695454d525454c52d4a50d425053c4ed3a4c52c4ad2a485204711b4310b428bc2b0ab2709b2689825494248912308b228851f07b1b06b1a85c16c5a1484c12c4a0f03b0b02b0a81c0300b
def q10g (i : Nat) : Nat := 0x1fe103ff6821fca087ee821faa087e6821f8a087de821f6a087d6821f4a087ce821f2a087c6821f0a0afbd441ed5107ad441e951079d441e551078d441e151077d441dd51076d441d951075d441d551074d441d151073d441cd51072d441c951071d441c551070d461c05186f5461ba5186dd461b45186c5461ae5186ad461a8518695461a251867d4619c5186654619651864d461905186354678a21fe18c81823205f8c817a3205d8c81723205b8c816a320598c8162328574c9f5842854d0a14e4285250a14442fcf94c1385304c94c12c5304994c1205384654e11253842d4e1045403f1500f45403b1500e454836d520d254fb21940be6502d1960a96582799809266021999a799681b25b25f0701441e0420780cc20023088048240000
def q10p (i : Nat) : Nat := (if i<6 then (if i<3 then (if i<1 then 0xa91a9129029028027026024c23823423223023322222122022c21d20b2072032001dc1c01ce1ad1ac1ab1a71a61ac19319119019f98f18e98d98b98798398318018017016015014013312012c1041011001000ff0ea0e90e80e70e60e40e30e20e00e00d00c00b00a209009008007f06e86e06c86c06a86a06986886786686606506486386306286206006005004003e82d82d02c82c02a02982882682482282182082002001e00c00a0090080070060050040030020000007c07b07a079277cf47f46f407307207106d36a066064063060f5fcdfc5fbdfadf9df8df85f7df75f3df35f2df25f05f8de05c0d90590d8058057056ed5cd5ad59d56d53d51d515504e04d04c8cb2cb0cb04b9498c92c90c9049cc8ac89c88c83c80c8046fc5f45ec5dc5cc5c45bc5ac59c59458c57c55c55453452c504504404303f03d8b9639039eb8db8cb8ab86b81b80388b72b7137037fb6f36db6cb6c36bb6ab69b68b67b67363362b60360343320300af02f02e82d02c02b02af29ea9ca9ba9aa99a99298a97a96a95293a93292a91a9029027026024323223123922422322222122821321f20e20d20b2072032001f01e01d81c01be1ad1ac1ab1aa1a91a71a61ac19919319099019f98f18e98d98c18b9899891879871839831819801801601441301301231021011001000ff0ed0ec0eb0ea0e90e80e70e30e20e00e00d80c00a809289089009008007c86c06b86a86a06986906886786606386306286006005c04a04604004003f02e82d82c82c02b82a82882802682602282202182002001e00d00c00b00a0090080070040030020010000007b07a0792771f70f60f5df49f46f44f43f407307206f06e06d06c16a06a0690660640630624e0060f5fedfddfcdfc5f9df8df85f7df6df3df35f2df1df05f05b8592590d92d81580d8057056ed5ad56d53d505505405104e04d2cb0cb9498c92c91c91490c9049cc8ac89c86c83c8248fc5f45ec5dc5cc5c45bc59c59458c57c53452c51c50450440430421c003f03d03b8b92b9239eb8db8cb8ab86b85b84b82b81b80388b7037fb6f36eb6db6cb6bb69b68b67b65b63362b61b60360340331320310af02f02e22d02d02c02b02af29ea9ca9aa99a99298a97a96a93a93292a91a9029027024c23823423323223123922822322222122c21821421321e20d20b2072062032001f01dc1c81c41c01c01be1ad1ac1ab1a91a71a61a31a319019f98f18e98d98c18b9899891879869839831829819801801601501401301241031021011001000ff0ed0ec0e90e80e70e50e30e20e00e00d00c00a889289089009008407007c86c06a86986906886786686606486386306286186006005604204004003e82d82c82c02a82882802782682482402382282202182082002001f00e00c00900800700600400300200100000 else (if i<2 then 0x859839831801801701501401301201181041000ff0ec0e90e80e70e30e20e00e00d00c00a809089009008007e86c86c06b86986906886786486386306286006005003e82d82c82c02a82982882682482382282182002001c00b00a009008007005004003002000000791770f71f5df49f46f43f407307206e06a069066064063edfddfcdfc5fbdfadf9df95f8df85f7df55f4df3df1df05f05a8d93592591d91590d94d80d8057cd5bd53d56d305234e4cb04a8c94c93491c91490c9049cc89c88c86c83c8046fc5f45ec5dc5bc5ac59c59458c57c56453c51c504304203b8b92b91b90b9eb8db8cb8ab86b83b88b73371b70b7037fb6eb6db6bb6ab69b68b67b63b63361b60360350310af02e02bf29ea9da9ca9c29ba9aa99a99298a97a97294a93a93291a9029027823423223123622422222022821121e20d2072052001d01be1ad1ac1ab1a71a919819119099019f98f18e98d98b98918798718698598398318018016015014013c1201181031021011000ff0ee0ec0ea0e90e80e70e50e30e00e00d00c00a889089008007e86e06c86a86986906886786706686606486386306186005c04003f02e82d82c82c02b82a82982882802602482382182002001f00e00d00c00a0090080070030010007b8f70f70f60f5cf49f43f407407306f06e06b069066063062f5fedfddfcdfc5fbdfadf7df6df3df35f2df15f05f0dec592590d98d80d8057cd53d50550cb04a3492c90c9049cc88c86c83c8046fc5f45ec5dc5cc5c45bc5b45ac57c56c53452c504504403b0b9cb86b85384b81b80380b7037fb6f36eb6db6cb6c36bb6ab68b67b66b63362b60b603603403333202f02e02c02b02af29da9d29ca9ba98a97a96a93a93292a9029027024c23823423323223123c22822422322222122022c21321121d2072052032012001e01d41c01c01be1ad1ab1aa1a91a71a41a31a21a11ac19319199119019f98f18d98c18b98b18798598398318298198018017016014013312c1031000ff0ee0ed0ec0eb0ea0e70e50e30e00e00d00b00a809009008407007e06c86c06b86a86886786686606486386306286206006005804604103003f02e82d82d02c82c02b82a82882682482402282182002001f00e00c00b00a0090070050030000007b07a0f78f68f54750f53f437407307207106d06b36a16a0660640633620e1f5fedfddfcdfc5fbdf9df8df7df3df35f2df15f05f05cc592591590d91580d80570567d53d53551d505205104e2cb04b04a8c91490c9049cc89c88c86c84c83c80c8fc5f45ec5dc5bc5ac59c58c57c55c55453452c504504404303f03e03a8b94390b9cb89b86b82b80b80385373372b70b7037fb6f36eb6db6bb6ab6a369b68b67b65b65363362b60360331320320af02f02e02d02c02b02af29ea9da9d29aa99a98a97a93a93292 else 0x9a98a97a97293a91a9029028024823423223023822622222022221e20d20a2092072052032012001f01e81c01be1ac1aa1a91a71a61a31a21a299199099f98f18e98d98c18a9899879871869859839829819801801601501401321001000ff0ee0ed0e70e50e00d00a809089008007f06e86d86c06a86986886786686606486386186006005a04604003e02d82c82c02a8298278268218200200107a079df4cf46f407206e0ea069066064063061edfe5fddfcdfbdf8df7df6df65f4df3df35f05f05b8590d90598580d8058057dd5cd51d505204d2c90c9049cc8ac89c88c86c83c8fc5ec5dc5cc5bc58c57c57456c53c53452c504504404314203d03beb8db8cb8ab86b83b88b7037fb6eb6db6cb6bb67b66b63b63362b603603403303102f02e02c02b02aea9da99a98a97a97296a93a93292a9029028026423223123422222122921821121d2092072052032081c01be1ad1ac1ab1a91a71a61a199119019f98f18d98b9899879871839831829801801601501401301281041031021001000ff0ee0ed0ec0e80e70e50e30e00e00d00c00a089009008007e86c86a86986906886706686606486386286006005003e82d82c82b82a82682602482282182002001f00e00c00a009008007006003002000001770f70f61f50f5df47f4072069066064063f5fedfddfcdf9df8df7df6df4df2df05f1dd15d8d92591590d9057056cd505244b2cb0cb04a8c95492c9149049ec8dc8cc88c87c86c83c8046fc5f45ec5dc5cc5bc59c57c56c55c52c50450440c203d03b8b91b90b9039eb8db8cb89b86b81b88b73372b71b7037fb6eb6db6d36cb69b68b67b66b63b62b603603403303102e02d02c02b02af29ea9da9ca9ba99a98a97a96a92a91a9029027024c23423223123023622022121d2072062052032012001e01d21c01c01be1ad1ac1a91a71a61a31a319199119099019f98f18e98d98b1879869859839831829819801801601501401301141031011001000ff0ee0ed0ec0ea0e70e50e10e00d00c00b00a289089008007f06e86e06d86c86986886786686606586386286186006005c04803003d82c82982682482282182002001f00e00d00c002f70f60768f52f5cf49f46f43f437406d06c06b069067066064062060cdfbdf9df8df7df3df35f2df05f2d94d80d80567d53d53551d51550510cb04a9498c93492c9149049cc8bc8ac89c87c84c83c8046fc5f45dc5cc5bc59c59458c57c53c53452c504504403d0bc03c2b9eb8cb8c38ab89b86b84b83b81b88b72b7037fb6f36eb6db6cb6bb69b68b67b63b63362b603603102f02e02d02b42a02aea9da9ca9ba99a99298a97a95a93a93292a9029027026823423223023322222022821f20e20d2072001f01e01d01be1ad1ac1ab1aa1a71a61a919819319019f98f18e98d98c18b9891879871)) else (if i<4 then 0x86606486386006005c04003e82d82c82982882682482182082002001e00c0006f06e069066064062cdfbdfadf9df8df7df3df05f7ddc598d96592590569d57d53d50528cb8c9049ec83c8fc5dc5cc5bc5ac59c58c57c50450448bc8b9cb8ab86b81b88b7fb6db6cb6bb6ab69b68b67b60360340332320320318af02e02d02c02ada9ca9ba9aa99a98a97a93a91a9029028027026823623423223023822622422222022821621421121021b2072062052032012001f01e01c01ba1a71a61a899699299199099019f98f18d98c98b9879869861859839801801601401381061021001000ff0ec0e70e60e30e10e00d80c00c889808008007e86e06c86c06a86986886786606486386005c04103c82a82982782682002001e00d00c00a008007006004003002000000778767f43f407407206e06c069067865063f5fddfcdfadf7df75f6df3df35f2df05f0d98d84d87d53d50550c9049cc8ac87c86c84c83c8046fc5ec5dc5cc5c45bc5ac57c57456c53450440438414c003bc3a03acb8ab89b86b84b81b8037fb6f36eb6db6cb6c36ab67b67366b653633603503403302e22d02c02b02aea9da9d29ca9c29ba9aa99a97a97296a93a9329029024823223023822622422222121e20d20b2092072032012001f01e81c01be1ac1a91a61a31a199f98f18e98d98c18b98b1899879871859839831829819801601501401301121001000fc0eb0ea0e80e70e50e00e00d00c00a609089208008e86e06c86c06a86886786686606486386286006005604003e82e02d82c82c02b82a8298278270268248228218200200107d07b0f5df43f406e06c0630e0edfddfcdfbdf9df8df3df2df05f8d96592d91592d8058057dd5cd5bd53d51d505204c0cb8c92c9149049cc89c83c8fc5ec5dc5cc5bc58c57c57452c504504403d0bc0b9eb8cb8ab86b80b7037fb6eb6db6cb6bb68b67b63362b603603402e82d02c02b02aea9da9ca9c29ba99a98a97a97293a9029026025c23823223123622222621221121d2092062032001fe1ad1aa1a91a71a899699199119099019f98f18d98b9879871869861839831809801801601401381031021011001000ff0ee0ed0ec0eb0e70e60e30e00d00a089008007e86c86c06b86986886706606486386286086006005c04103003e82d82c82c02b82a82982882682482282182002801001f00e00d00c00b00a0080070060030020000007b0f70778761f50f5df406b069067066063061f5fddfd5fc5fadf9df8df7df75f3df35f1df05f0de1dd15d2590d90590d8057056bd57d56d53d505205104c1c90c90496c84c83c82c8248046fc5f45ec5e45dc5c45bc5ac59c58c57c53c53451c504403f1b90b9db8cb8ab89b84b88b73371b70b7037fb6f36db6c36bb6ab69b68b67b67361b603403302f02e02d02c02b02af29da9ca9aa9 else (if i<5 then 0x1000fe0ed0ec0e90e40e30e10e00e00d00c889489009008807e86c86c06886606486406386286006005004103e82c82c02982382102082001e00c009008007006003002001000008760f5df47f406e0ea368064063ddf9df95f7df75f4df3df35f7dd0d9057bd57d55d53d50540528cb0cb8c90c9049cc8bc8ac89c86483c82c8048046fc5f45ec5dc5bc57c574534503e03d03b6390b9db8cb81b80380b7037fb6eb6db6bb67b67365b633603202f02e02b42a02af29da97a95a93a9329029826823423223123822222d2092072052032012001e01c01be1ad1ac1a21a319199099019f98f18e98d9899879869859839831809801801601501401301181041001000ff0ee0ec0ea0e70e50e30e00e00a007f06e86e06c86b86a86a06986786606386006005003c82a82a0298278268258218200200107306e066063edfcdfbdf9df8df7df3dfcdd7dd8d96590d98d8058056ed5cd5bd59d55d51d50528494490c9049cc8ac87c86c8fc5ec5dc5cc5bc57c5045cb8ab8fb6eb6db6cb6bb67b603603413203102f02e02c02bea9da9ca9ba99a98a97a93a91290a9029026c23a23823623c22a22622522121d20c20b2072032001e01be1ad1ac1a71a61a31a299199119019f98d98b9879839809801801601501401301181031021011001000ff0ee0ed0ec0eb0ea0e90e70e60e10e00e00d00c808008e86c86c06b86886786606386006005c04a04103e82c82a82982882782482382002001f00e00d00c00b00a008007006000f70690670660630e1ddfcdfc5f8df7df3df05f05cc598d92590d90d8057056dd5cd59d53d50547d30520cb8c94490c9cc88c84c83c82c8fc5dc5c45bc57c5043042db8cb84b81b8c37fb6eb6db6bb67b603503403303202e02d02c02bea9da9ca9c29ba99a97a93a9029028026823423223123622422222122022621121d2092062032012001f01e01cc1a91a61a699199099019f98f18d98c1899879869839819801801601501441301361001000ff0ec0ea0e90e70e60e50e30e10e00d00c089009008e06c86c06b86986686606486386286006005004d82c82c02982882782801c009008006004003002001000000791778768f507106f066063c62edfcdfbdf8df7df75f6df4df3df35f05f4d9057056ed5cd5bd57d51d50528cb0cb8c94c9349049ec8cc89c88c86c8046fc5ec5dc5cc5bc58c57c574534504504403b0b9eb8db8cb89b86b84b81b80388b7037fb6eb6db6d36cb6bb68b67b673633603602f02e02c02b42a02aea9da9ca9ba98a97a97293a9029c23423223023c22822622c21121c2092072001f01e21c01c01be1a91a71ac99319119099019f98f18d98c98c18b98b18798718398318198018017015014013c1221011001000fe0ed0ec0e70e50e10e00e00d00a889089008007e86c86c068867866 else 0x2682362322312302382292172001f01e21c01c01be1ac1a099f18d98b9899879859839831801801601441301301181011001000f70e00e00d00c00a009008c86686606206005004103c82a829827826823821824012010011770f7069068066063862262062ddfcdf9df6df4df3df35f0d9dd5cd59d56d53d51d304d8c91490c9049cc8ac85c84c8fc5dc5cc5bc59c57456c55c54c50411390b9cb81b8237fb6db6cb6bb67b66b64b603403102e02c02bda9ca9ba99a97a97293a9c2322332172001be1ac1a61a199f98f18e98d98b9889879871839819811809801801601401331021011000ff0ec0e70e50e00e00d00c00a008007e86e06c86c06986886706686486386286006005003c82982682182102001f00e00c0007c07306f06d069066064063062ddf9df3df659057dd59d55d53d505405204a0c9049ac86c89c57c5cb8db6bb603403323202e02c02bda9ba99a97a93a9026c2382342322312392282222202282142122112172052032001f01ee1ac1ab1a61a899199119099f18e98e18d9899889879869839809801801601401321011001000fc0eb0e90e80e50e40e30e00e00d00c889089009008c86a86986606386005004103003e82c82982382001e00d00c00b00a009008007006004003002001000000f606f168066064060cdfc5fbdf7df75f7dd6592590d9057cd53d50528cb8c9549049cc89c88c83c8fc5c45bc57c57455453c504304203acb8037fb6eb6bb67b65b63360340333320320af02f02e02d02c02bca9ba99a97a95293a92a9029026823223023822222122321d2032001f01e41c01cd1a91a21ac19199099f98d98b9879871851839801601501401381021001000ff0e40e00d00c00a089008e06c86c06b86a86a06986786606506386286086006005004103003c82b829822000008760f60f59f406d368168066862062061adf9df7df5df3df1df05f8d9bd5ad53d53d31d30530528c9049cc8ac89c87c86c8648fc5bc5ac57c50453c01c00408b90b9cb8ab86b8837137037fb6db6bb6ab67b603603203102e02d02bda9aa99a97a93a9029028823623223822122121021e20d20b2072032001f01e81c21c01c01be1a71a61a099019f98f18e98d9879839819811809801801601401381031021001000ff0ee0eb0e70e20e10e00e00d00c00a007e86c86a86986886786686386286006005004003c82a82982882782682582382182001f000f7073068066064edfcdf9df3df05f6592590570569d53d5052449049cc88c83c8fc5ec5dc5cc57c503a1390b9cb81b8c37337fb6eb6db6cb603403303102e02d02c02bea9ca9ba99a97a93a9028026623423223123822222122022c21421321121b2072052032001f01e01c01be1aa1a91a71a61a899199119099019f98d98c18b9879839801601401301181021011))) else (if i<9 then (if i<7 then 0x3402e02c9a97a97293a902802702682362322302302292182112101f01e01d399199099f98f18d98b9899891881879831819809801801601301000fa0e80e70e60e30e00e00d00c00a008906886206003a82982202082001d00c00a0080070060040030020010000006d06b0660630620e1bdf3df05f0d9ed59d53d50540528c9449cc8ac89c8bc57c504403f03b3b88b7837fb6bb68b603403303203102f02e02c02bba99a98a93a902632322382222282142112192072001f01e01be1ad1ab1a71a199d98b9879831801801601501401301101000f80e40e30e10e00d00c00b209089009008007c86c06a86986886606386005e00d000009f4073066edf9df3df8d96592d92590d92589d53d50548c96494492c91490c9049cc8ac86c8fc5bc53c5cb86b81b88b7fb603403302e02a9a97a93a9028026c23323223123222122c21621321e20d20b2092072032001f01c01be1a91a31a319199f98e98d98b98a98798318118018016014813013011210110c0ea0e60e00e00d00c00a889007c86c06986886686606406386286006005004103003e82d82c829826825823821820778f50f5068063162060ddfcdf8df7df0d9dd5cd5bd53d505204e8c9049ac89c86c82c8fc5ec5dc5cc5bc5b459c58c57c504503f03c0b9cb85b88b7037fb6eb6db6cb6bb6ab68b68367b603603202f02d02bca9aa97a93a902982322201e01be1ac1a31a899319199099019f98e98d98b9899889881879831819811809801801401321001000fc0e30e10e00d00a008007e86c86a86786686606386006005103003c825820020013f407306b066064262061cdf9df3dfcdd6590570567d505414e04e04a1490c93c82c8545cb8eb6bb6b3603402e02d02c02b02aca99a97a93a9029026823623222022921421221121b2072001f01e01be1a61a119099f18e98d98c18b98818798398118018016014013011810210110c0eb0ea0e70e60e50e40e00e00d009007c86986686386286006005a04003c82a82982682382002101001e00c00b00a0090080060040030020007906906606406305cc594d92591590d92580589d55d53d50cb04a1490c9cc88c86c84c8fc5dc5bc59457c50440430bc03bcb89b8eb6db67b603403303203102e02d02c02bda9ba99a95a93a9028026c23823623423323223123023622222022421121d2072032002001f01e01bc1a61a21a01a199099f18d98b9879869839819801601501301000fc0e90e30e10e00c00a208008e86e06c86c06b866862860060059820016000000f53680670660640620e1cdf9df7df6df4df05f959859659359259056dd5bd59d50529498496493492490c9049dc8cc8bc86c82c8fc57c56c54c50457c003a0b9cb86b83b8037fb6eb6db66b64b603603503403313203202e02d02c02bea9ca99a97a96a94a9028 else (if i<8 then 0x8698398016014013110a0e80e70e60e00d00ac09009808007e06c86986886606406386006005003e82e02c82a828826825020798f60f55740f407206e068066064063adf7df8d80535c8148fc5bc5ac58c57c503f03d2bc03bfb6ab68b61b602e02c02b02a3a902642362232272001d01c899099f18e98d9889879871831829811809801801401301131001000f30e00e00de06a8678638628618600600548238228218208200210100106e06635fc590d90590573d5052449049dc5bc57c53c504404303ecb8fb6db6b367b603402e02c02b5a93a9329027823223622222921321121e1a119f98f18c18918818798718598398198018014013110b0e90e70e30e10e00e00dc86986486406005103003c82682402001e00c00b00a0090080070060007c27707306f06d0660640627df3df0dd8590d9858049cc57c51457c003e03b03a3b8bb67b653633603603503102d02c7a982342322382202242192052001f01eb1a51a119f18e98d98b98b1891879849831801301060e40e30e00c008e06a06906686386286204003982282101001e006004003002000005f40f407306f0660640639df3dfc590d90590d86d55d505204b04a0c9dc5d457c53c514503f03e6b81b8fb6db67b63b60b603403303102f02e02d02c02bda99a95a93a91a9028c23823623223822222022821121d2092082072032022001f01e91a319019f18d98b98b1899879849839831819801601401301101000fe0ed0ec0e70e50e30e00e00d00c809008e060793f41f40640630620e0cdf75f3df0d99d53d504e0cb0c90499c8fc5bc57c574534504503d03b6390b9cb81b87b673603302e02bda99a97a97293a9027026c23123c2142132112152032001f01ce1ac1a31a319f18e98d98c18a98718698598398118016013810110010c0e40e10e00e00d00a008e86e06c86c06a86986906706686606406386006005103003e82c820f507206f06d16a068063061edfd5fadf9df6df659259bd50528c9649ac86c83c8fc5ec5dc5bc5ac504203ccb86b85b8fb6bb6ab603412f02e02c02baa93a91a902862322392192072001f01e01be1a91a899199099f98f18e98d98c98b9889879819811809801801601400f90e80e10e00d00c00b009007c86a06606286005004103003c829826825822820820020018f606f06a067066064063cdf0df0599d53d50c9cc5bc503e03bcb86b80b7db6cb67b603403202e02d02bca99a97a93a9223222321d2001e01d01c01be1ad1aa1a599319199099f18e98d98c18b9879871839831819811801801401301111001000fc0ea0e80e70e30e00e00d00c00a008e06c86986886786686386005103003c82a82982882482001e00d00c00b00a000795f40f407306f0640e12590d97d50528492490498c8048046dc58c50c503a8b67b66363b60b60 else 0x1d01a099d98c98918798618318018014013010e0e90e30e10e00e00d00c00a809289089009008007e06c868760720660644609df35f8d80560496c8bc53c52c51458b7db6cb6bb67b62b602f02e02b6a91a9823423023822221b2072001e01de1ae98c18798718298016014013d0e90e70e20e00d008e06a8698690688680678660658650648638628600507906d06b36a0668650630e1061d5fcdfadf3df0540c9046b4544103d03b03a1b8db64b613603403103002e02d02c02b329122f18e18b18798718098016013310e0e90e80e70e50e40e20e10e00d00b00ae06005003e82c82c02a029828826820f70740730704ea2ea066064063bdf7df1df0c9bc57c53c57c0140037bb68b67b61b613603602e02c02bba96a902702462382101d099019e18d98c18798718118018017014013810010e0e00d008e066864860050036826022821820820020010669df7df75f3df0d90c9fc5dc58c57c58bc03bc3a8b9cb88b7cb68b60b602e82d02b7a93a90a972001f01d819119f18b9879871869859839831801801301101000fd0e90e80e70e00e00a009007786586006005c04003c82682382002001e0007d07b06f06a06405714e4c9049dc58c57c56c54c56b88b78370379367b63b603102e82d02c02ac299296a95a93a92a9026821d1a71af18c18b1891831801401301101070e00e00d00ce06c86986686005003c82282e00d00c00b00a0090080006e9df4d9049dc5cc59455c543a03a037db6bb67b65364b633623613603602e02c02a1a9027223821121920b18918718598398318018016010d0e90e50e40e30e00a008a06906886606005804003882582001c00a0090080070060040030020007206d062adf0570540528c9049dc5cc5bc57c50c50450c2ab663603102e02d02c02baa902802742682302382162001e61a219099f18e98e18d1899881879849839831811801201060e10e00d00b009c06906286003001e00c003002001000001f507306f06d064063adf2df05705244e0c9049cc8dc5d45cc5bc59c55453451c514503b1b9cb88b86b88b7db6bb6a367b61b602c5a9028027c2322302222192052032001f91a51a31a01a819499119019f18e98e18b1891879859849831829819811801801601451000fd0e90e80e60e50e30e10e00d00b8f506c0648df3df0542cb2c93c8ac58c57c51c503a2b9cb88b7037e36db6cb68b65361b603603002f02e02cda9aa98a97a93a91a902982302382222201f01e01de1a199f18d98c1881879871831811801601401301000fe0e90e80e30e00d00c00a809009008007e06c86a8688680668638608600600507a06f06c36a0670660640630e1060cdf5df4df1df0df05f0d904e3c8fc50c50c003d0bc0b9cb81b8db69b67b63b633203002e02d02b02a9a93a9129123121e1af1899879871)) else (if i<10 then 0x490494c50455b63b61b602e02a9a93a93291290a9029623c2212101d119019b1879819801701601010e00c00a089009008007e06c86c06a0607307206606405d0560524c95c504303c03a4b9037db6cb6bb67b61b602b7a992212001ef18d98c18a18798718398017016014013d0e70e00bc8698690688668660658650648638607706d06a0646c81c503b0b99b61b683202332222222101f01df18e98e18d18c98a98998798718015014010009807007e06c86c06a8688680648638628620618610608600600580407b066063060d5fcdf4df15f0dd04b1490c9049cc8cc51450458b603603002d02b3a902901c119019f18718498118018017016013e0ea0e30e809009886686386003e82e02c82c0236a16a0691680663df05f8d80576c53c504503b6b85b82b8aa9028322a2101f319e18c18918798017014e0e70e30e00d009007e06386005003a829828828026824823822822021820f52ea06a168cdf6dfcdd4c9049dc5cc5ac56c54c5c3a03a0b94b8037cb67b633602e6a902742201d21c119f18e98d98d18918718118008e06d06005003c8218210208200280100106e06d06a0623df7dd057046cc58c5c3aa3a037db6ab65b613203102c0a901ff18c18818718698318017013010e0ed0e80e70e00d489009008007e06686286006005004003001e000660643dddc5cc5bc53c503d03c4b70377b65b603102dc299a99296a94a902642312171a199119698598398015013011c0ea0e30e00e889c86c82982282002e00d00c00b00a009000d98c9449bc59c5545a398b74b7037db6c369b68b653603603002b5a94a982382112102101ff18918818798698618598014010d0ec0e70e00e089886686c82582082b0080070060007a1620dfcb6bb65360b603102e2a9029223221f18e98d98c9899879859831811801301201000f50e00d00a009c86606486006005004003982282001e00d0060040030020010000007d0795f40f407307136a06a0660648e06df3df35f2df05f0d90540500cb44a0c9dc5cc5bc58c57450c503c03b0380b70379368b60b603202f02e02b02a3a902742392202201f01e41c019f1887606f16a0690670640619df6df4df3df2df05f6c8cc59c57c53c52c51c5cb68b67b67361b603402d02ba299a97a96a95a93a9329029822621221c2052032001f01bc1a51a31a119099019e98e18d98c98b18a9891889879871861849829807306635f05f0d905705414e04e04d04a4c90c9049cc58457c504504003aab88b8db6bb69b68b65363362b60b603602f02d02a12932242192032001fb1a91a31a819019f18d9899889879871829819801801601401301000fd0e80e70e40e30e07306f06d0ea0649df8df3df05f05404a649046bc59c57c53450432b92b70379b66b602f02e4a93a91a902902722312302302201e else (if i<11 then 0x60663df7c59b61367a9120119f18b9899891879871839829801370e50e00d489c86b0690688680670668660658648640607b04903c13702d027f18e98e18d98798718318014013112d0ec0e00880660658640638630628620618610608600600506a061060cdf05f05914e04e046dc5cb84b802f02d329822522322019f18718098112012686306005c04004003e02c8214503802b129122219119f1891879839831819811801601370e20e10ee06a06606586005c82c02a829829028828026820732ea168049123e98e18c18b9871831801400fe0ed0ec0e00de06c86a06206a82682582482402382302282202182102cf40710704ea168cdd7dd05c8c9049cc80458b74b7037db6cb603002401f01d01c61af18d98a18798003c8208200200106d0643dd14903102e6a92a9029199718118013010e0ec0e10e009008007e06c86686006c04004003c82001e00d00c005df0d9bc59c57c55c57b63a9823821221021099f18e9891879869859839800fc0e70ec06586e00c00b00a009008007007df05f0d90577c503a03402e02c5a9223422f18e98d98c98b98998318014606486005e00a0070060040030020010000007c07b5f407306d8ea36a2ea16a0ea06a066063cdf5df4df3df35f3dd0562c90c9dc5cc53c52c50432b9037cb6bb69b69367b63b633603603203112f0af02e02d02b9a99296a95a907306a8681680643df2df05f5dd05d0d93588c92490c97c54b9c37037db6cb6bb60b603483202f02e02b02a6a93a92a902902802702642322302342232212242101f01de1a71a81936a16a0690689df5df3df05d057056052349149bc59c58c57c53c52c51c504303b0b9137037eb6e367b63b61b602c02b0a9028322022e2001fa1a01a219199119019f18e98e18d9807d17807406a0690614df3df05e15d05d05805404d0497c80487c53c514503d037a368367b63b62b602d02b02a6a95a94a93a912902482312101a299099e98d98d18c98c18b98b180f70640630e19df3df05f8dd05d0d90550522490490489c59458457c554503d6398b82b8037eb68367b623603002c9a98a95a932922322101e019b98b18a9899891881879871861807606f0640e18d835314e04d3c8cc57c514504003c03a837037bb63b633613603402d9a982302382101b819319219019f18e98d9891879859849839831829811801801601401311207b0790712ea0690665df3df0578c9048dc53c51c574003b8b7db6bb69b67b65b63b61b602c8a93a902682172052001f01e61af18798718618598016013810010e0ec0eb0e90e80e0670649df8df4df35f4d94cb449048046dc5cc5043db6d36b367b63b63361b60b602e02dca96a962302342101ff18e98e18c98c18b18998718398118013b0e70e50e40e30e10e00d07106a0690663df1df05f05c8d914e6 else 0x7b07a0798f50f51f407307107006f0690670660640630e1061cdfadf9df8df6df5df4df3df1df15f05fcdd8dd7dd4dd05c05b8d90d9057cd505244a8c94491490c9049cc86c8046ec5dc5cc5bc59c58c57c56c55c54c53c504403b4390b9cb81370b7037eb6db6d36cb6bb6ab69b68b67b66b65b64b63b60330310300af02e02c02baa99a96a95293a93291a912902902682342322302382242282152112101f01e01d41c819299199119f18e98e18d98d18c98c18b98b18a98a1899891881879871869861859851839831821819811801701601401301131021001000fe0ed0ec0e90e80e70e50e30e10e00d00c089008e06c86c06a86a06906886806686606486386306286206186106086005a04204004403103003c82c02a82982902882682582502482402382282182102001e00d00c00b00a0090080070060030020010000007c07b07a7f45f41740730708ea0679df5df3df35f2df04d8cb04b0c90490488f60698de5dd3dd05d0d90570540524cb04b8c9dc5cc5bc59c58c57c56c55c53c53452c51450428c00404b92b98b88b74f607607406a0690640e14de05e6dd4dd2dd05d8c504404203f4bc03c03a2b80384b72b7037eb6db6cb6bb69b68b66b606f0ea06a9df3df7c52c54b7137cb6bb69b69368b67b66b65b64b62b60b603403203002f02e02d02c02b02a9a99296a907407207006d36a06acdf6df1d8bc5137db6bb69a99295a93a92a912902902802702602482362342322322212252122136a8e09df5df05e0534c924994504003c437c366b602b32922302332202212192012001f01e01c01b8193191991190190690643df05e3dd1dd3c50b9e380b7d360331326a95a93a912902842301be1a01a219119099f18e98e18d98d18c98c180f71680630e17dd7534492499c59458c57c503d1379363b613202b3a902942322301ec18b18a98a189989188187987180731681538496c89c5840140037db6bb69b67b613203002baa93a942322301e81c21c01c8191197186986185984983980698e00d9dc5cc5345043cb67b6336329024019e98d98c98b98b18a9881879869839831829821811801801701601351007906f0690663df35f8c9049dc5cc53c51c503b8b70375b63b602b3a91a901fe98d98798598014310210010e0ed0ec0e0660c99b8ab67b69a91a982302382142101ff18e98e18d98c98c18b18918798698598b0e90e80e70e40e30e20e10e00e06f06d16a06a0640e19df7df35f2df05f2c90422b7ca912901d099019618014d0eb0e00d00c00a48928908900900800707a0660619df1df0d90c93c51c5c3a037d363b61b61a9027623121819019e18d98798698598014007e06c86c06a8698))))
def orfd10 (p : Nat) : Nat :=
  let j := p/4
  let r := packedAt q10r (j*16) 16
  let h := packedAt q10ph ((j/8)*32) 32
  let pw := h >>> 28
  let parent := ((h >>> 15)%8192) + packedAt q10pb ((h % 32768)+(j % 8)*pw) pw
  let op := (packedAt q10t0 (((r >>> 0) % 128)*10) 10)
  let keep := ((r >>> 7) % 4)
  if p % 4=0 then (orfd11 (4*parent)) ||| (op <<< 40) else if p % 4=1 then
    let old := orfd11 (4*parent+1)
    let a := op % 16
    let b := (op >>> 4) % 16
    let rm := (if keep % 2=0 then 1 <<< a else 0) ||| (if keep/2=0 then 1 <<< b else 0)
    if j=6731 then 8182 else if j=7023 then 6655 else if j=7049 then 6655 else ((old ^^^ (old &&& rm)) ||| 8192)
  else
    let w := packedAt q10g (((r >>> 9) % 128)*22) 22
    let n := w >>> 13
    if p % 4=2 then n else packedAt q10p ((w % 8192)*12) (n*12)
def orfl10 : Packing := (7163,5,7,0,250,0,0,orfd10)
def q9pb (i : Nat) : Nat := 0xa87b705b000000baeb9e0820808f897a7931080200b5c69934a080d7af34c8aa4f80d98348206000fedba98093162bc6e64c80d57ebd0a0a4f00f7777a49a0ae7989206080c2078f38b040de7107b1208bd8b41880a266932c7000ad2317b480ce738a0820fdddb54081e51344e0c0f56928a8e09ca3071c60f7755a4d00a72a23f5c88280e6f1451440cd7ac525a58680b7624263050280f773794540deab4820808e281d54f10096140c305100a2565550d1c0c565150820f5ed161c80991a2ba506c480bac8d81810009d2c3860a10180ca85850c1000bdef6b39808a286081e440cb6b6a480f030100c2b5ae975b2c0800c45c80e080c180ffff7dae2280e2fb2b40b280bbd6920000a2a286841b0e0b008a415badd0d82406009999922095e79d48b2c0b698996591409b9c929020f1efec312e1b0300a2d15f2e46aae53c00cf185c700000ad9000ffe480892440e974ba1bfda4840000f24448af5a02f0a00000d981bb62244800d40000cba9887092468888876600fabdea9aa49ca7001400de4c4c4b45261700caa99980dc6b4000000000000081d75b697000fdb480ffffc899999420dad2409659645030c08a2896596200000488242f1ad8c546262ff17ddf1e1c24808000b552a4448882008564443a393829008b55282516160700b5f65840d300cf38143c60008d84786463565200d3e429d383a80c020095223a2263c200ddd9d4b7aa0502008b12095242448093938e8d6f1d1900d32b647543009b9a97936b413c00ae7e5f45241d09008ef9ebc7858580a638974c9180aa170f38a28089c45030a04089e756283040e738e9c202c300ac908a7573726f0091c6d438c280ba489a657200d2d2931860a70a1331424080a94dd284268880af566b13448880fb4f26120f0f0500a6755b3425201d00e0f552548884008617df796500a8c582f5c9928084edd2340746008f817365645d2000b75e63008080009cdce631808421081800aaa65300aaa31100a954a554fefe86421110bbb66630cd1200ea809540a940f09550c0fcf0f0fff4489236d8ad2200d24640fe50a550fea8
def q9ph (i : Nat) : Nat := 0x8d9e5f81b61b7b08d3f5dc1b4957407ceadc21b32d6d84cbf5ae1f25b6807c60d92171456206c36d7c1b0795c05c105661701b5706bf155016f915185bd5d3c12f374d06bbcd2816eb54785ba0d1416e454287b654fc16d473c87b164e41eb9d3585ad6ccc16b053086aaecb61aa672a86a82c9e169d32505a6548a1e8911f06a0a4701e78318869c4c56166e313069a7440224fb0c088db4201e2a704868844061a19afe8585abf022026f80977fbce11decf1867663ba19d3ceb85745ba421b34e5095a038219616dd835833700d5feda8357db6425250d48346834c1d0f2cf874063300d00cca843fd3220cfe4c7043f4b14287f4c00818daf01061eba09049ad6180e2b2830352c40c0c4af8402b2b60c0a0ac06015aa418008a60d00227e1e2169c078522622202294887aaa4219e0c8d8675ba2a21c4e86896362081d8447e885a09ea1d5f877085349cc1946270084ca9b0211c46807449992190a6618640d97a18ff05b863e91621ceb2550835314418d004e0632712c14bd848872cc9141ca8441872738f8207d43a081920d81c534328612d0be1c3a82c070bf8a2201de2487047084140f61e85035870100c21a0402b860080a817020280580409e158102705410088130401c8440c0660f8201803a0805a0d82015832040520c0201382c0404c0a810120280404609810108240c034078300b0180c01e048300480c0800a020200180408000000
def q9r (i : Nat) : Nat := (if i<1 then 0x67439ae23419aa27439ae2740650d540630e6c28cde3349cee68b7c5665a9c562a69c7272a8c7265a9aca132346205a4d0e7468b0e65a7d0e7467d0a33885067469cee65a9d1a65a7d0a33885067469cee72a9ee1fc39ee0dbe7f0e7b89f627c29f627c19f027bf9e9e7c19f067ad4e4e7c19eda7ad9e427b49f4e78298667b86704a3c98566140140050593d64f99466147145a0e9946614705a651994483210866519852651593e65170566506945c1f707dc1f98d401398f66517051a5170a9a25803a6509840646113844e987000e989c226107c01010500143052613684e61498526141074225089dc1a706a606384260360418109840827009c2271025c27089de119874e210862647983a61d987423d10f66137056025894262598426509940432108664d40ec4211079c1e989663208f664f99414139942650580a6509941a256895a256895a259941a25984162598404244080627208c027189c22711448310890831108081568114140144227088c823407461d080662a0142650989c227208c4252062618208dc1a089c82308f4225986082308f42200894227986023d0099c1a9899a25504e6326895a256895a25689541498c5c159895a2598426259895c1570566257055c159895a2598426259895c157055a259851c02693e21570ca65070726509941c179942632987261f9896625989662598966259895a506941a50694261498526149851413989662598966159855c26989c0511038027789dc145851414586262660604140862604182a61c989dc27989dc155899627991a61c30f421410f5c14709dc3d994262a989a626989a626989a61c989dc27989e6189871c269876627988e42798966259896625504e62598966259896625414060540ed01c406105038c8e5138c9818094663b98ca62198726179944232213483b20c8818213c8259852614313503238950503944832695da56995e65a6965a566969a59695da56696a65a99626566961a560269a520cbda596961a550439a54149cf236969a5969606cb695da550c39a54696a657996a65a996a65a99626579956658995e655994da586959a559962657995a658995e657995a658995e6569956658995e6569956656995665a9959a560439a54124e659995e6566c3a6549c4da581461a586959a559962657995665a99666569955b0e9952658995a654724d5149962657995a655695da540c99a530a21a5a9966658995e6569a2e65a9966658995e656995672a9962656995265a9962657995a6559966658995e6569955b0e995265a995e6579955a576955a53696a657995665374a6657995e6589962657995a658995e65699566579959910995a6589962657996265799598a599666579966658995e6566965a56695669299666569956692644265999626569956657 else 0x1c518899451689602a809601858a8c25506262658a9625506202a389661568c1630984661498246093801c3298ca63270c943250ca71918f583b98b26147850e1070c901360198325941021394445198866519894e518095e159840e10984122598966176946613985663b9946613985665098566216946632985660e2038e50714262598966258896425809660c980e2258096014989660e98956255896604989662598126259096604989662560966259895e25889662598e262a98e2625984de1428e1434609662528e0a5038edc5058ba63498ee62158acc1e989562530a86253062625986264f984e613984e63c98726179836603980e624994265088962259896225989663898e2604989660498966259896225505061450522259851225983e62598566159894a0e98422259894e3a989661558966254894a3560ed232483523150b0a2c18d4a0d08d601578960321836632710dc3270e1c389875c3270ed646209da27189c851309e623589e627989e623889a023489e023989e623988de23888e023981d832708e623607e6233055a1580ca032988e6279875827988de3298c4814988e61d980662338ca6329060850209e02398f66419900c27988de27989ce2778ed63b9852618989660e989662598edc3b7085c1870ecc32905622628ca027489d013409e614983a60e987661598766279875a1460ca60e984260e693561750ee218993d432993de442054c1e28a8c1868cd62e60bd81e993e63298ee627988e24178c9a1c9909a14687262a98c8a109d0e6596b2513d74f674382e27439d0d74382e15439c9665a996670e596a65a99666c09cf674464fa7469cf273c84ae25a996665a996a65a54966596b31aca9b2270e9d19b462ce4726450e2932a5173d9a4e6945ab949383096cb643a7279c8e7269c8954382e1a9384b9144446c93d7c9e09382520b2225173d649a6b29a4e0942ab18937252693825049344f67467a4d53d9d1a73d324db2a6d19b466ca9b46443a693951a7439c9e7239cf673b9b2e7259cc974382e114342e0b2e72d0cab74edc5a1cb91331d19d3b722d1327169d469d0a7387d0e2b884ba12e4cce688996a721950e1469d1a73b996a7329d1a72a9ab9f272d027239afa6889d15f3d751673d9d167459d016ae35067419aca6939d027409d067409d066939d027419a4e740332c90e349d323149a1223b3c93d3cf4f3d2cf67463cf67405b2cd0e7c8e72234f593d64f593d34f67457a4c73d54f67469d066939d189269caa7469caa7469cde740351a3374c38d269cde7469d0)
def q9t0 (i : Nat) : Nat := 0x2dda66889de669564488a11735bd6b5ab6759865d96655946458d6318b61d866158460d82605805f57c5ed765d5745cd725c56d5b16b5a965591635895d56d5454d525354c50d424f53c4ed3a4c52d4ad214811d4350c334bd2b4ac2ac9d270942348b1f47c1ec6d1b06b1744c12c2d0740b
def q9g (i : Nat) : Nat := 0x1350798c84a6424321199088c8426420320f99078ca39e81af40c7a05bd029ec11f6077c02be78c18000
def q9p (i : Nat) : Nat := 0xde066032737f3bf8df3efe374fbb0d946c83640a4049023731738b8c57e29f14d8a03b15cc2dfb6dcb6ddb6adb36d8b6bdb4ed9f6ceb66db1ed896c03601882bc05c02c015eaa73536a97549ea4852028c11a08c44601f80f0078036319f8c7a63c31d98e8c7063731b18d4c6662f31718b4c4c61f30f1874c3661930b983cc1c60d3039818c006002c014009e040620210088783b81d90ec075c3aa1c30e0068023c0dc06c434c19c0c8863c31c1890c3861430017905c02d41660b1056827413609904a823410608003e00e8070030016006001c00c0040000009b80cc7dfc6c815e3ab8c53e280ff36d8b6bdb4ed8f6c0af01700b00579a901401bc0ce7dd025032778afc53e2f6d9f6cbb601700b5d527a9013608cc47822411348003f01e10f007b234e1a2ccfc63631918b8c01c00de064470432778a03b25cc6e356d9b65db00d304601c2ccfc61f30f1838c0060028013c082040a20310108783b21d70e78701ec0de06dcefced8b6c0310171aa5046223b903c83831b1878c005802a0140099c3861c00d0047819c0c786002f20b504c823c101bc7bacd9024df15b8a945bdb48d9f6cd365db00b004cc234910267e31b18e037208d05e00e807003001700b00380180060000001b40cc0e19efb77c0a304902180ef76d3b65db00c405c02dcd49ea404d823411988c046222b903c80e4001f00f646ac34599ecc6660f300160098043c1d30e0068033c0d886a43381800b98294161d81ea06d12caf5409a649a645f15f8a7c5262d0ebb6d4b699b1ed805d9a93d48099047822b0d4667e31d98d8c4c61e30016009e04102070e2070034018606e414608505e00e00580260120020001cc0de46e0326755bab049de2bf1407603a1dc4ed886a03421880b805a02ced49ea4050623310f483640f2000f807803991ab0d3868c3519904cf663731b187cc3a6002c0140099840a20210e870034018489004661b10ce062430014008103cc1360b800e0000013dd3e806f03681988ca064cefe164cb24d912c9f540a404e8248127f8b3c55a280ed3703b8edb5ed9f6c03401980c806202f01710b405a02c015e6a4f52028013608d046623111c08b640b2000f706a332099f8c6e61f3079800b00500278108082040c2001020700340190892040021d0c486002f20b3051827c12608f0560003db3d00dc066eefeb7f3bf0d932c83661b005702b67553aa3d3028832e1920c9c644323f8bbc5be2d716a8abc5022010cb8004001db2e3f6ddb621a80c615e8af01740b405902b015f6a77539a98d480a004ca235111888442f20390007c039c1a70d1c68c35199fcc7c63730f983cc00580280138082040c203101080043e1db0e58700361128894047a1b70d886002ea0b304982800ec03400e00
def orfd9 (p : Nat) : Nat :=
  let j := p/4
  let r := packedAt q9r (j*14) 14
  let h := packedAt q9ph ((j/8)*30) 30
  let pw := h >>> 26
  let parent := ((h >>> 13)%8192) + packedAt q9pb ((h % 8192)+(j % 8)*pw) pw
  let op := (packedAt q9t0 (((r >>> 0) % 128)*10) 10)
  let keep := ((r >>> 7) % 4)
  if p % 4=0 then (orfd10 (4*parent)) ||| (op <<< 50) else if p % 4=1 then
    let old := orfd10 (4*parent+1)
    let a := op % 16
    let b := (op >>> 4) % 16
    let rm := (if keep % 2=0 then 1 <<< a else 0) ||| (if keep/2=0 then 1 <<< b else 0)
    if j=513 then 16338 else if j=1088 then 12214 else ((old ^^^ (old &&& rm)) ||| 16384)
  else
    let w := packedAt q9g (((r >>> 9) % 32)*17) 17
    let n := w >>> 10
    if p % 4=2 then n else packedAt q9p ((w % 1024)*13) (n*13)
def orfl9 : Packing := (1119,6,7,0,250,0,0,orfd9)
def q8pb (i : Nat) : Nat := 0xfefdc82e1600d30b2684b280caeae99e22c0beb717450040c36e8c65eb8680d588e1b2850180bbba373528280100a12793a8843a106800
def q8ph (i : Nat) : Nat := 0x86358865b358654b2864e0f87412c072c48881444890ea00
def q8r (i : Nat) : Nat := 0x2261302a2c0b0984c240b0984c2e108d46c311b0d434411c8f87436291080c30168888422208287c3c0a8d56b41a0d096c8e46d06848d552a91c1ea55145850040a082100014
def q8t0 (i : Nat) : Nat := 0x1ce6f985611815f9765b96d54d52539434811e378be2b8942381e
def q8g (i : Nat) : Nat := 0xb9effc0
def q8p (i : Nat) : Nat := 0x1c806f1f771d5812afc53f14044ced9bb600c601eee63b18d43807201b59d52f4c051ef15bc5cedafb610d50af00bb9a900a0026008cf201c8001f7868e1a0265f983e60016c040610cc3800dca08f82
def orfd8 (p : Nat) : Nat :=
  let j := p/4
  let r := packedAt q8r (j*9) 9
  let h := packedAt q8ph ((j/8)*24) 24
  let pw := h >>> 20
  let parent := ((h >>> 9)%2048) + packedAt q8pb ((h % 512)+(j % 8)*pw) pw
  let op := (packedAt q8t0 (((r >>> 0) % 32)*10) 10)
  let keep := ((r >>> 5) % 4)
  if p % 4=0 then (orfd9 (4*parent)) ||| (op <<< 60) else if p % 4=1 then
    let old := orfd9 (4*parent+1)
    let a := op % 16
    let b := (op >>> 4) % 16
    let rm := (if keep % 2=0 then 1 <<< a else 0) ||| (if keep/2=0 then 1 <<< b else 0)
    if j=10 then 24466 else ((old ^^^ (old &&& rm)) ||| 32768)
  else
    let w := packedAt q8g (((r >>> 7) % 4)*11) 11
    let n := w >>> 6
    if p % 4=2 then n else packedAt q8p ((w % 64)*14) (n*14)
def orfl8 : Packing := (62,7,7,0,250,0,0,orfd8)
def q7pb (i : Nat) : Nat := 0x8e27134850c1
def q7r (i : Nat) : Nat := 0x8e00e0883044
def q7t0 (i : Nat) : Nat := 0x5af58f4ce4a210f
def q7g (i : Nat) : Nat := 0xee0
def q7p (i : Nat) : Nat := 0x391bd3df6c00bbcd4802800483c8100f1e1a002cc040006880c
def orfd7 (p : Nat) : Nat :=
  let j := p/4
  let r := packedAt q7r (j*6) 6
  let parent := packedAt q7pb (j*6) 6
  let op := (packedAt q7t0 (((r >>> 0) % 8)*12) 12)
  let keep := ((r >>> 3) % 4)
  if p % 4=0 then (qWiden 7 (orfd8 (4*parent))) ||| (op <<< 140) else if p % 4=1 then
    let old := orfd8 (4*parent+1)
    let a := op % 32
    let b := (op >>> 5) % 32
    let rm := (if keep % 2=0 then 1 <<< a else 0) ||| (if keep/2=0 then 1 <<< b else 0)
    ((old ^^^ (old &&& rm)) ||| 65536)
  else
    let w := packedAt q7g (((r >>> 5) % 2)*8) 8
    let n := w >>> 4
    if p % 4=2 then n else packedAt q7p ((w % 16)*15) (n*15)
def orfl7 : Packing := (8,8,7,0,250,0,0,orfd7)
def q6pb (i : Nat) : Nat := 0x1a3
def q6r (i : Nat) : Nat := 0x48
def q6t0 (i : Nat) : Nat := 0x590110
def q6g (i : Nat) : Nat := 0x0
def q6p (i : Nat) : Nat := 0x0
def orfd6 (p : Nat) : Nat :=
  let j := p/4
  let r := packedAt q6r (j*3) 3
  let parent := packedAt q6pb (j*3) 3
  let op := (packedAt q6t0 (((r >>> 0) % 2)*12) 12)
  let keep := ((r >>> 1) % 4)
  if p % 4=0 then (orfd7 (4*parent)) ||| (op <<< 160) else if p % 4=1 then
    let old := orfd7 (4*parent+1)
    let a := op % 32
    let b := (op >>> 5) % 32
    let rm := (if keep % 2=0 then 1 <<< a else 0) ||| (if keep/2=0 then 1 <<< b else 0)
    ((old ^^^ (old &&& rm)) ||| 131072)
  else
    let w := packedAt q6g (((r >>> 3) % 1)*0) 0
    let n := w >>> 0
    if p % 4=2 then n else packedAt q6p ((w % 1)*9) (n*9)
def orfl6 : Packing := (3,9,0,0,250,0,0,orfd6)
def q5pb (i : Nat) : Nat := 0x0
def q5r (i : Nat) : Nat := 0x591
def q5g (i : Nat) : Nat := 0x0
def q5p (i : Nat) : Nat := 0x0
def orfd5 (p : Nat) : Nat :=
  let j := p/4
  let r := packedAt q5r (j*14) 14
  let parent := packedAt q5pb (j*0) 0
  let op := ((r >>> 0) % 4096)
  let keep := ((r >>> 12) % 4)
  if p % 4=0 then (orfd6 (4*parent)) ||| (op <<< 180) else if p % 4=1 then
    let old := orfd6 (4*parent+1)
    let a := op % 32
    let b := (op >>> 5) % 32
    let rm := (if keep % 2=0 then 1 <<< a else 0) ||| (if keep/2=0 then 1 <<< b else 0)
    ((old ^^^ (old &&& rm)) ||| 262144)
  else
    let w := packedAt q5g (((r >>> 14) % 1)*0) 0
    let n := w >>> 0
    if p % 4=2 then n else packedAt q5p ((w % 1)*10) (n*10)
def orfl5 : Packing := (1,10,0,0,250,0,0,orfd5)
def orflevels : Nat → Packing
  | 5 => orfl5
  | 6 => orfl6
  | 7 => orfl7
  | 8 => orfl8
  | 9 => orfl9
  | 10 => orfl10
  | 11 => orfl11
  | 12 => orfl12
  | 13 => orfl13
  | 14 => orfl14
  | _ => emptyPacking
def qix5s (i : Nat) : Nat := 0x0
def qix5v (i : Nat) : Nat := 0x2
def qix6s (i : Nat) : Nat := 0x0
def qix6v (i : Nat) : Nat := 0x1008000016
def qix7s (i : Nat) : Nat := 0x1c2
def qix7v (i : Nat) : Nat := 0x2b1801ea75c04138
def qix8s (i : Nat) : Nat := 0xa4c88c118005d0000004c000508004f
def qix8v (i : Nat) : Nat := 0x74ce8001ed9400a46054001cb08520299f010d3b0107466dec0026a3711e0150819032a7509b942b57e294c47d000f305dfa002552b9078300050ad60e0007d599719d20002f104f799c7c746b666acf5880018d0e7e58d
def qix9s (i : Nat) : Nat := 0x540c00900303f0001d800029000054000000246ac3c82c08280c078f50120205a00a00019c4600e0040b4000340286b40686774241400010036008348158140100900708201c000ca038184108000480b02882c00c11cf183102e030138000600080007f13e09c0f043074c6c190456443780c0da014040030030b6100150295940040080001807c210200067a40c8030144380c8544ae0080080171e0ec011320020003e80105a7c4010370160041601b0020d81080404205de28121360000000003e0040900304c0340000801a004030043f20d14801a06e070040030b60880f0017cc049f281200c3f0008080180080308400203c038120020042e8038d20280280a01a018120040000c80581b7f007406004000824048100240040290400600801000062068008000020000230401800000003040048038007d0010108030140080a034006005b60030088a806002002038038010020000080000405c040040020200080601002014173850119552d803e03a0e004000018090cb048000c500b0060000180000006c00001028018000590000a5ad17d002004008066f20200580600400400000010020038242fec480a001000bf96b02f022005e580502602c0301e34c0006d80379c01c060020020145f8010360395e0005286f00000000200c080160000000680056811400013000060e103800a02c020000120100e800
def qix9v (i : Nat) : Nat := (if i<1 then 0x9da488b916d806a84d6d94033162050cb4ca964396e33400f53b175792441d4bc8f70716e6348f8238e95c32d1a482b8c0534e844a522c9bf6610c66522a227c77248ba655228cb85f9222ed7a0bfe2658a0d4078b0e5a7ca6e8916c00ca44e64f700d3206d48806d6512f3867113ce03804dc054a6a0eaac5b9805a941662d00d2cba890d8b02400d4a9351a606bc15c308f13d08d45d53ab6f887c89e80433b5ca32b2cbe4a5c1d6342a8d7913ec45912582a02ca933ea433a80761ebbb4444d0ed821a1ca0db69a6ad1c90ac3292c48afdce90a8205aee16dccf41a2281d690411884022334c3a45aaab4135ef2230cc38c5500f82c521a7a36718b00d021d7cabb736227ea49f496ea1bee876545210000ea27fe840902202a0e4981aba1ef636965a021e031137d2e4884a788d1710ac23512c996c60468da4613bb721400eff5c12233942c88c15d6a82d943b72321d4d489a474eeecd8aaca434132e10981c4961b51a0c9dcd80bd172749124a294b4e164b66b0cc45a834138c0a64ad2074a3b32ac561eb3ce117ea7a4169a83401a42d485e2191911708ad9c7ca17d96e088a51a121cf083288fdda5ca10955e8e29866226514fd6922d8039a0278aeed6540b30a75d0639c521140a44c8f0e8d9ad99b952088941161af693c048184405186708703f95ada448854b0756e1c41a4766044a8cefa9c1735c63780fba217414730d90d9045b70ba6fe512e93c700e2f00202821d016d430a6435c9d14004d09816a33cb71242048cfa194ea1a004604fc19ed0461715e52020f055110bc81d6c1fe23d8916818daa8f039903fdc97d334444d6b9d1144b684010900d00ac846b77005041669c30780ae03d4f1cb6294b92e0113b390902da66ed1ba3acc00bc3129815933a857ae399038492972f6230d229d97142b807e6d5949aba757217248232a842bcc2124bd53f31896c0dd086497f95bc83ec01f1bc2489c813a4592279148943816059ac5837c2031475c90b067664d05d6187ba320047d91db90a088c8de0df84b6d470cb07a0a2c93017912121c9ec39987d6818a1d4ba47179a27ed11092c3a5f26ef507b0b0160642cfd16fcb1cb4dce87141d006041f8b0b9226d082039a8962620a1b6019282de9fab03ba1312c129eeca5292bb2769c33499435c56fe062b3117b3eaf00500c9b0c27cf4fb05119afab6312b049d001c992f81046d659bdf357410ade265b9a909364d8510495b605ee84d1c621a9b14964350023c2503748825816916a429811740ac93c66342074d0ac09eb97034fed1bad1d886b48f8a03fda5b720e8129004d8a712e80d299548417441460f187c1bfa129ae45021a205973bc710c03900ea8842c77404e84249872a750def1be634a6c8e9813a25f95bae9c643bc8f203e52455d48b811b52a4550607ca4f else (if i<2 then 0x3875d4ab0406801892668edc583dad1361a10a9870b18c282ac2ec0000a24031d2a80a16014394d6841a0e7018282c608b6899187a00014d6006718b0710eb07ed651820468e006c1171be090830a1e5af98785464855991cdbc3951d051d8f2cba34308c364e09319725132afa1f418c797dc6e565490a9412e724e1983183d96700162515308e08346a8e4ce493c90d12789d270000085f4f6a54d8b1601e6889d854caea42ae513c00020be37c707c5d6830d622a32ec06033bc0323744b6563d2b0000007700004b7a0000c479d911445b41d002a53113c9624600008c9000083c882d6dde000090e60070d894a98750801f91ec08c27166c6cd82ad45e6470abfd47d18e2436b2e09d26530b94940000d99c2ad000162a1c568a4d933f311de11d3b2932d2a7420a445c984400000000000800d2c7502f8000437b30dc9df22c84002c8ce19eb8e8421f29a90e05966840eed510c2a00746344ee981628ec163f67095cb800022568de6d08db37911481b95dd9c1075b464a2d4ca37675814fc60afb0ac430660fed620b0252340e3ed31ca6d646ac149c89822fb5b882f694f382836f8c0c286e237ea4b5683e55cd3f6024101441008383721d2d9917992fe45ca85e297aca0c288846601c2ca6f723aa355841dbcaa87e2c80012a326a1210f64e1aa26032720ff2538130eb66c49518ebc8eda7828cfa5ce323706ad4e7e9574a77100b249d6064b2314ff6c5c40b1bd575f6e19000020030000c0b903b20616432ce401993a1218380d9581c8313582ce958216914901a800000001c07948c0be046253ff17c88b265f0901f20a60002145c90376996e51ce2c89f43500f3e9f6b02a90880510023c3d200000b0845e4b71000124200b8323c91414625044992536566a1900bca9c365400011d0a2ee91e889eecbb9c4244f0cdfed33c9b740992bc08fe8000759ec36d81988fd73006a7dc4a4319b14c6eda1d220f514e4eb3ad33303603029034cb58813416c00011c8897595c602565968000442c84448a50c0435d8eb4819452f146480720d115b6e654cee1c525b3537122000190243efb678e2b9587a0b100008925c679ab575c10f404b94ba696c6ee4d86d4b96b5ac30c64f751246062e87d02b236447090e6d48e0b61377e812d98850e330f2e24d04bc84540ae431611f00af42c086e652bb15300df2b185edb1e691de425989d8a7516f625d8d50d93587a6b0cea0ecb779326ee351288b21a1c8c2a8463010137e52a140dc08107156079d17ec86973780ee65fbb0bab27eed22a1049c30080e02e897497ea043298586c3ae464688e22dfa3ab305dae195c8b298a94100adc0f50a18973c6644dceba1e14568718000518f90d41061dda02eba6520d15027c3d456d6868ca28902643c289a449b8a5094d8e220d9758a102cb272 else 0x4a142290c80800001fc028c2135dc490dd762b62954f9a2db92f3035dd0db23d95444cc4460cbaa67ac00011aea37d24ab4710a0da0637262b0ed0e3b428b4e8104ca04016744352a3187700000000c80e48123a5a61201f6de6496fb3ec02891733b98463cc8dad553aef48a0c8150a10b0))
def qix10s (i : Nat) : Nat := (if i<2 then (if i<1 then 0xb0a2002000805802c04b001812c0056ba007000c004001028801c02202001c0041a7aa388b40048004035002800800c0a61cdb9a007aa280020000004034000004c000cd6679803000200f0010008034000003803800a3ce0010018006001001800c00000800100de9da00002900000124dd38f80000100045e1800c0000005d8000403200a00c80000000170250050018008014001800200700800bc00400000a800004200e008003c00400200501c8a865dbe27000c0080400070078638000008001401a002004806c00201a036004c00eb4a00a8018014f08008006400000a01cd620000016001800401800000170d400001400e002c004004019000c01a00c005e7b40056cc0010014000000000802400001100e0000e0602000019d400207902f804c07e0040000000032ff2001807000201ad50800c04202b0000014000002001801c028006002008004a004714001801c0000078000000023008800401000200188bc00a000001002c00200600880f400400200200280c2000e186b8003402300a006f105646005000c0040140090000000000001000401457304280e80180009a0c0e400b32900a5da006e5ff000017000c00000200000840010020004000006000000a5e000a0010014022008da10028006004006171c0040050050000011b9f0005dac02000a000451c00a000006803400000e00b0000008001015802c0023d2000006c00c00000b80000020010000008008006000002c000003002009c03c23dbb1f0c40000020028000000032005800000200000000000000000020020018000022000000c0000070004076012003800f8dc0080018020007c4da7f000800e010008807c00000200000180020070000000010008c3180140000000185780055a760054b7970a00000480400000090028115a040000000608008072004801402400f019955400400000b007000000437d001800000000000bc00000c004c9bc00600b002801c0bc00101080192260030005db0006003004801c01e00600b000400000000523dc004018009800400200400700d000000000080000020010038001166000001002400000000080600240033cb097000600a96c0000002007000003c002012002800000001a0020045d380010000010022fcb01a8024f420000038044000005001000401e000001800403a003004007c001407001000800000600100480020000510000004009004000400a04000100080000270000004004009000001000000c00600200320005e98018000004001800400400001600ec00001300533e8012000003000c00000e0008010002031004003c0140000018000014024007000800000800100380000050012a3800e019010009401a01d001803800f7f0000004d68c0010018014012047001001dc2c00100080b006800e else 0x400d003400007800c00541200010009718979328000e46801a00d002007802a00001c000000401600180000e6003001801c00801300100440385f000a028400692bd39e9d001400900782b4008004002005400400e0174ef002200600d95f400a006004d65c0040000ec017c000c340018068012920c33804cb0201e02c0014000000015b2827b20011fac59c06200201000b80a6002000001400a00000400080e0000002000000d672008882000e10200f8000044038001371c01e03700080a142800d00001600000017d9000316401201e800002600000101f001383a1ec003c00000b009809010a01c000000400402f0000006d9600000280b4a620010176ee802e03e014446800007fac980940098ee000000c00200c13a003c00000000b800400a002000c94427001600100400360052abb81409c00000ab7300e00000110028022000000800c024020000800401400800812e8078ef700000b2fd4007ab6003400c00500200b801a04b00159300200010148008000009002ed8800ac8c002000c00417a00480e541402f0005e940020000000a30000ea400b003c06400b00001d000800802d801800000b000000003002e035005800939700548f4042e1d000800000a0000360029a108f40000004046cc701c81d809400c00d000001400000100600000000080000004000000003c01601c1318000058001001802401200000400b41e2005000267c036661003018c00400501d00040240080188024006009015e24802e00100b803c00201602e003c01183d00080e7706000156800c18c0020000080000001002007000400810b001000a00251c002802803000200a005e00100e802400600a000801c057c39015000806b76e005008800200000b803c06399c0038090002012d0b000001a03100000041300030003b9002600e00600c051600b008007802600200541dc00e00c0068139dc500c026dccc00200601880a400a019001002000400200c8030000012001004800000800846942bc000049804400c06500a002001400500780ac03202301200180007f800100080040149124aec00c00200400bc376005002007c01800400380000080030030ef508a000000000006600200301174fe00201c803c000010000000401000201743e8006001000000c0000000040000002000003000250a0010028220000062000003c00400500c02c400000000abd2801c004b83010002800200700b0006002195002400402d005800c0000010ef80040be04ebc4a524002000001005403a00301b808000e03500e803406356b003000001e001000807800c0110021d24003b23000002c0180500250080014001002008004400000001c953000f0040009c5a00b00d80000036e9002baf0024004016000003000300300435ce0080070008072c8c000000) else (if i<3 then 0xe40815470008029f5009e01980300000040bb01e800200f01a80680000010088074006016066000403a02100149e400000608f81100e800000082c0060000008e30801c08d45ed1a400004d000532403a0350031fac532006016003406402501b801c00788f00d806403a06f002c3700183d71518110742073916000000600002801540a0005000009810000000e8004090009039480ce52000029824000e05406007800c400a0000520010003009002c00000d005013c1b9c8f00380b800001c00501c80038170300048008017099802801405200d0004e8c03500a00300d3ab500080de49e07d997833414800000a2f3800c01db6b00680140dc000067400001600201a008200800580880040b2043800a1f403602102b801a056002805800000300101381a6031002808000401c000802400c00a00100640de9340168661c7c004001d19c11000500500dc0338e602680282e0024011004c00000c097000006800ad3b806003c02c00900480317670002db801b86d038803800000b00080040020069a23cbc020c8c030817c0742ad00150bc04e79700d00900000a969380282492dc001800c3860000032a1400e00200d24cc01608e00a017c0020314cb0004001bbc00d549837a000016000419006300880dc01a079000804c01200500000900160005738000008003001000194800000000b40700020f894440017df01a802802201ab62803000b74e66900c0030009015800012800201d800c00c06f00000002ea00200e00040000060188004072000046001c5a0012dd5013c0001260080000000dc577f000017400001d002806e029021800001800200c80907a800500580e807400d00401340d400a005805804183b00180000346b403800b41360060000010000004000001009c05b000542402a09b001801000213a00300000000020000004017bd3009006c00010e004805c00200202cc970004da8004832c01001d00300014d118d001004000c00100300b4000007002981c000f36001010c05a0e3650800c00201600ccd6801e00703501b000e03d00003dc0f400001a00000320000098000062b7d000000001c922031801001c00200580040000010158000000000004812c00800c003613c00400086a822c008566008806806a02e01c000004c006aa4004002400e00000b00320b000000db3ee01400b000c01c00b00067ac0dc051000800800000100380280000000208da403218d00a001001402505d003005558c50b816806e010008000400400500a800800601a000026802001d000007800600e2850c9401e0250050001ad600000b000401e006004958c000c27000000001a027891804003005e00067b0014dd001d80049cc023b36802001e00a000003c00000000f8034052040c5284bc00600800000b000e00200100000000d else 0x383cc058a1e00780d009800206b020c0a8000001804c0340388f2025c10201001001e4072b2f8eb06ad79c004004805c000000000804801a04402f06c000203c40d005035200305180005ca000007801006a08b002003400c0171ef000380325505c010c0ae0040ca632409a00c000586801c01a000003007430f88ccca4000000007005403000200180800133a600030a4004045014800400006c002a9e400a0280e58014003a7801581a401a00600687b40120470950b580000020218008022000008822c0180399310024020014000037c00001201437cc1ec000020800009b7ab02912b000e00a0b3013c00c0d400900a000001c005000400004101c004801200413140b80ca00400280cf4e4c0e00b800000400b000001405200004a051015e111008800a49009201902a000933704200dc0000480158144002013000107c02000d00504f009201c66700181260010f300103bc014008800363a0030000194004044000015400800003c800c000002001032ed060cf0030000010008660800805c0030003a0400004a006844c0a2004000406000000002c031400a00005f00005ce14f298c82c0019a900b84e00000930000f7401400e0128001ee8092050000823000c00a007c00806d01c81c408c0b20ca000003c01f00002ca51c29800a833003c015000003f81a00001900340035d502d864439600600001bc01c00a017800404c00000006ec30000500a800c5d600314c800000000f0000464fa2000008000002c04a002800c002014041aaa03300940200cf408a03f09d9da2518047000014c1e800a0210ce400000003200dc01e00100980f75d0039a59802809c00703682a41096e5066802400c8f1004e3101f000800280141340000008004018000d6100200174ba000000000015b002818c05e0090205ae000c000001806818400000600100de07600801f0000000061803002000401fd50c000033da8823000200001050cc00000b04882800bafe300068501ee05600180d001800900002d00d4013001044800411e00f800003c0073f88060033492000325c00005b00a000322c00e000806c000010026c5a407405c08c8398016004043804403c21250c000400e02100000))
def qix10v (i : Nat) : Nat := (if i<8 then (if i<4 then (if i<2 then (if i<1 then 0x2a13048b8888591e69ed0f40a88f9d659e521845c445360d311e863266c7b51ce65dd92871949ace4b2f54c0657d4a4cb53d7ef0f8653f71dfaadb95c8a3437799cc514956c077c79ca04c910af4d70714cc6c51566a95278a8651ba6d6a40d58f099b94b846146f57eb9cf4b95741838f22f1c74963190ffaad3b43f3bdb3242dc330e0726bbb8edd60f07d0712b86c8dd4cade260c754dfdc746e84752eaa64704acad767794395e9e727ac092bd94515c1a33d3a05bcde351c9c38c84244b4304a95c054ebe22888bd8624df4f4303ac6dc0dc65061720570e384e21a3266229adea6821ead535ce8ca64bafa11c640bf0707ba5bdcd8f306c37efdd6be6fbd36820c5f036e416324ac5ac1dd1a161cf1161a64aa349988cb1028e705602d10631375f4b5ec36a92543522c88d5b58f2ef194ae4137120827224654cff985fd2baa5a608e8c4d289bd02a27d645a2534a5a904d9d2c5e9d3bc226a56308b1411b20d30210992baa917813d69330234aa6ca15eefa9a5f354fa6e048bb0662060b6252adca806608c3983c61c8cd937baf450408a13de8b440385b9883c5bbcee02327c0c39cca602e50d89d40169dfcad94428a895ab244922158a6bc824dded090e52c08ba803b006d1096cd7137dfcd8ea9a14cb5c2c3a58c7e519c82a8abb7aad280c0f281216f23e9ee04b56822300fb6812817af7b58845aed1d1faf7790877720cb92018f83fbbcaa348d9aec2eb4998996b2665206f48938c8c9e2b0b881013274959b5a1be95fe91f1dc0a02e392a314df2044c5336119e0234f92b2132306fbb9aff9dd8cf72b161b4cc5a10ca170d72e42a484344682a8c391854205ea1d204b80309a85d6e24c20673343e94306e6b14820e9b13536b153a54e53613320cd22c2b1363571a481ae6ccc898b084c25296944ee60d0428ae4aa6650ab41902aaeb70669b035f18f4210cc270af23b13c9acaf581276944412532935df1852054d1a3af9e2a14956141654dabc5d5aa62a04ec24b5a550322d24a94bd9ee9b0c4569ac5551780aef67bc2461c31c3a616f585949704cd99a8a90ab0309a95056681e05b69cdbbb1bd054e9b293c27d65706f44f305481c4e02d0d894aac4b73837be193d23d07c4c158d25f4a95a94dcda57588c0a59f74106c9fce11c20fc360462a766dc3a98bdb20d487422468b6d8ac02ba4881b5f35e87a1a9e8b101521a3343f9565fe6a6e54859c0f3ce6d30ccc96d3cb9c1e41e7404b7a7cbe2caa029c722726179230808c856a0349c4bdbd0b5d91bc9bb9ed0302b0af2fae73edba3321d3486e2433fce6b1ec005778b70f4dc0ed40d5808b1c629e5a58a68ca897b649518aed312138402de37a9412b35e063a4092451948c04a073a293e54c6723f824ccc76ae9174152232f20d6e4d6728028799ce35935004f98 else 0xa44b8685c696236e9bd748ac4c31749774484c9039d47e8eb567c033356c82e6fc849dbd37fa64aaacbc8de00156aea2d715283c4a4eed097128666c3f53df19c84e9bb036bb39fae064ab81b891a27381a58022d07084dcb219ee0cc94993ce602ecf07b8956edb5378af8600377a2bbd9862730e6649a0c4541ea20282058dbcc5eed80ee28af2c5ac3928b5dd36be9268ccf0133f240806d20ccba14a4522b4785ec134268362fad763a986fea1aee240bad0d6e48516b232345af80a989a8a51324db61db74e97a3b5d52554a6748ed64b73a7d326129c08c12b16b041e98273a82b35ab5a24f0ed409240aa79d1e5c80bdd6f1c11b05b2bee915707e813a916f09a24cf2e86c541c0c46f912e74d865a07ee5fd0a66566338d5a46a0a51866cb0c9fd1da1244d0aae0628517ed4d3f27c34c8851bd80a43071e81cb2b76c0071214b0eaf5424c1185a39dac19d2d8968739644bbb49c35b65283d2a16d45e286c7bfbafbba3364f80318190cc23816c7c0e8fc5254bbe24b2af2a702dc025b3489be0218ba90542d9a0d3331d64b64d454c58b23943be444c2d2d3c57c28d3c9eadd42316a0193234e0110e5087d337bf4ad550da63281ac19ce642416522b993da25641b3a72ef36bc4dbace6c05193c4ca54481000b2f63e03b64d43ca3576874ab48a9e1133f68a8e12ff1e045c554b9202df00d5be55733b5ab4633255981beb0667d44d370c09da8ee887050e90c23fe78a23bf7b51c155b923ad8535b8ec9e7ed2320998884006eeca821ea86b25598e35a330f90baa1c925221151b9472526128d5f767cb2240d2a26c60ef3053b84a5fca0a840ff0b4d46ad6af3570359401dd70911ead62245f036256480b21bc9795c97c110888b0e19fea4ee0ce72474b89d451372f040902e827806aaa670c8d2a719c821360f833a06476b15d9952c0cd3d145b5ba041b7e92c071a9d1912c3f05087891e803da8a8004b317558d2c2e652321d5679a663215e00d6f02f696b86664578dc2d8cd48b171ea209b4d18c80aed9231b657261aaef50db0f9cb95271abfac8c497944aaf48eadb5d0659d2c3bb316e54944add70ded5a065b04959191ff3e539e514e7c744990d5ec8c51466ea86c9a90a73685ace91454377cf61441244afeb906e13e234c161c5d6e3ec7e69b143a1b1c4be6cfa91206065b0a5d93fb1b94010a1a0a095792cc5b21e434501482e5fb94f5837599a6f33e4a05d467d613dc1a9560f23e7aa58ac04298972bca2665a9612e670191c62662b023d058d516196ed64e6458e9b6db52aa8ca5098f09dd900c169be6b435b69b997a377b0532525cec89b62779957916111e75d28eaa89a0372adfac955b2846a9479cce63171b22f2343868f36ff3465b4259a42f4842570293e0fa6ba739de9c7e4d72ac7251519054d0d30a) else (if i<3 then 0x198cd293d34a1eba5278ed2b20515c66ece203788962c23079193ab0c9756adc165c87c95230119d3806c3d8accd2b2ba058cb7beb8fb948bc8e9245f2941e18b202c7118dcf3e0b8aecd725d1309a7322bf02ce4a37c5a144645199add293727b388d0e65addee712c52602ae013183023b01132ea6a466739d194f63ad995b2f66978533b98c26a78f964450582b699708770569d8a5aa92bbc44dd8643dcbdcd9fcf5f24db95851cd96f57c959a2091f16e160dc4252bdc6f436c2998a10ced054cde78cb58283a0462c9f32f91d963dbb1b2663c3085402b54306329678afbcb5c5162292425b27b699c2652a8c10b02c10bae2ac71e884a729731da25d7ad77da2a1c9259c8fd13a6494e9004ea20763d699e2221065dcc2d89acc1b03c46a84b709a884d1cf50d760e864082d3f5526fa47bb37a3bcd00cbcf701414364bb8a629b45e6007bbea2ac5ca301645e50c3025172a77cbc739df1966bb33191bfc2dbc86ffa411958ac21e905510838d5963c51449fe4b2ba931c20b5633e24706702f32eba6906a77552f782f4c188f070954ebb81d1c2fe786c4d8fb8b08515d572a8579a566665c6a7431a3756041109371297b3659a3e35672bacb436c1cbae98ec1d8794433cee6a02d50c4aa192c0d00d4ed989a30057be76b0e2c995c611d26271b5bb240cdc258446d8ef009628ca7bdd19667354ac7ce4329c9f133da4d10d0880eb7646e94a0cb68911d8d47c97dbb17ac043254624a7942c192dc727c39cee4095d4d8c65889b2c098b46430b1b6a8740c200763d72f574de2e801d14cef7295aed36bac906968554ed49f1a9465688153a13c2e6662f7883a29dcc12077a902f549058efaa735676b19aaad3708c9f76a7eb5719955415c8c044206d2933a73a45208891e38b98b2046d4b3282b2fe4df0b39a5732d4bdd1e9f6682a84b1cd5aed824f3d840c0b4a89c8f6697c238b9c64e95412f7866c7ba210ce68e05345493ab1d2a1ada0da2d55617ce6e2c7805ca94d60d31a26a050a2e195b4696eda99b22ec8e9e5c27172d306f335988e2d0a6880fa89b688a9d1672287134f44b2643ab2962c8ca0a9eccb0d3238f9b8e99807139cb1ea52db29cdc843600ac3d7ae02de82cc919f3c67c9ca8e9f2a2f15d44d4a891ba54a9a86d90eec46d7036b94b8b69aea0d439841935e65178c96b7a1920caddf0ea6b956c230635f07894073b43a4a6936e760a371e04a4d4225a85b8920a0847d0bb72fa2b75da12e40d2d353383409ec560d4b024433bf4bdad830e937e958951a1d332b23264bc71ab488a0e522991e354716d028ea490d5c4ba22cccb104b9a6e59bc1e8052af644d8305f521416c8d752ccb089c76717e8916a58da1060736569d78223c1658634ce0112a558e676b39c717feb07668976211e2be9307c69b82d7730 else 0x981aac4ca58538c84742389e95aec08f306448d15ee7f62327194050969f8c8377b63c13d112a7e5bcfa8cc20b3d80233676353c20b3a8ac287dd4af1d16262ebae0c14d58bc71cf0572f0424efb025a15db4cdf465daaa7dd18e0a0f42c589ac12a069b687ba93828604840a10287983649130b40814ad3c51592852c7b7ba954beb2f647193e6419a12da71656fe689be59a4ee06113214111aaa94f15d0254384b21ca8ad4f11418965362a4f2c40bda2b4e002e52dac8fe39a702ad2519990d289482ccdb8c15d2fa346ddae51185ce0113080d1b38e55f094d8980cc6b024738d79f26970c868daf010e98a424b07c5f8473562a699ae3d9822538b22a3d5a364942e895974abd42c4e26e3b52de40ddb116c6f16326922c46e51b34cec90fe9479561e2118c83820445adb5b6859b7ed9137aa34307ad94d0c09ae7795454937a58907ed63cc1881c26200091d3d6c9325244d44a5dd69b46761645a968d686030ab933859c9fda0b72467b31dfe112d34e877de4cfc646aa72ab066f017b1e3b20db4295c1bfa925ae87ea748db670d0876d3d41bd2353c247e14a4ca8e900882a22763dcb48224a7a3373669c235bb39a1a938177f37f49d1bc46ea072d157406c88a2ec8ba727283190e04e734403c359df7d934cc5e11bfda2c3e0b82c7be1dadac1894d1124694cd8ca6fecd3d74f7b4a6860f648c8cb93480818556a1c820984b8ccc03969ab22b6b7fbd01e0c18f7642612dc9f092c0d62dc49edb6a9d8af72f2a8d0759496cd9911082be080869eeb17b524a722c10c70acc1a8bde5d426d22cb4bf8624e9e8a5e5549262227091aa100e0574762239b4792e046f5374f520e0215b2dba39448a46d11c248b159cd4c5fa915b1095a5069ccde450ed18c86a64426ca538345b74cd9c5f41c904a51756745154ef13870be3554b1734776eaf9430dc58e219cbf144a671bc28a204fc474dbc6295886c5f70281bbec3a289cdf698ec4960cc976e0a48e181086c332eec0a0c6b3d8bb1590a82d16c584aea08e85d5cd43e47dc4b0cd0e3a6e5741805e7f0c36691220006268a1eda345e8465913de553a777dc9916a210a0dd207b04476d9108df64493d52c5213dc344244c70d0f52b4437e0aaa199ac487795cdeb4a09a2d4cf32e5788721b8f91624a6999702f08518c5eeeaf2a4f560f6bc9c5144c6d638d1d8a175206c629f8385a5a4e5d1ee62119f7b4c7c948f511834c748b065268795a77b24cf70e8e733249abc528925d3f24859621cc03ce2e55725920794160342ce39e4a7eb20460920907640ce255120a0caeec86a7391c6a3b8af9d1cd19a7eed2588f206aa6a1b64adb323b7301d282ae51b828b3a2d38087e435c9b0791fb24e858a38d8d310b285d810f4aa572638030d3d8dcf6f070dc244b2d2ab0187602a78525db)) else (if i<6 then (if i<5 then 0xbf28a3526a193ccc612e939b224a537d835464ee099f821390ff1324685be0c9f650bd5a406a5595de9e9b722e160cb3b5ae6b08165d004f4afea10e532f356e7335baaff46567471e05c6e04f52c5247665ea4e0f1c0d9c90bb2bf451e7d29c4a01d9a656501ad6197492b620acfdd1a8d3d62a2622e0d572e299275ecb2e9b4427bbde3b44e637234ab3bc0dd03a477b22eb9ac322170af662e3ec60fbb0c8874aa191f9768a1fa653d2daa22c3c20f088dda12f166695e3364fcc16df351f4e556efe371a49b3752788683b0bbab7ed04825d55e950030e248b6c37310d5c1b7bc989665226b098d33baf2d5696c0906b90a207555d2e2530c3e9a8a48a691b3c5d4a13fb92afcccd7bada33116586e45b367bfa8536b449314f56655e6aa050695fab6a40c3bac3ed71db744e2477464e4e9c3bc6ec2dd48e7510fdbb6da49a9c356cd478dbe95efe1a6a9b3e10200a1204f0ec5e5363e4ca3e81dc169071d105a6d020c47452ddcbca340cee85c03c161dfb2eb17239db2234c932462c0ab799d959e6e52282fe8194e11a81623922700d715b71e6d7ea75445a03a962696365cc9b639bfda33e1412b91d2ab8a10d4ed369bbf3cd4e88978450c68ebcd74457ad1a5e5082423964312e78cb741d8f4e52a0f2587dd31ca32ea427bba9146a55f48cc017b400243bb6d72ec78014640a6f5dd1652c189951a5aa51f560a1128d5360c5752ee1b02380ce720ca5a6ce748c323196eb6cad3a59581a660afaa0d4c75713d931cb0b37dabc5226c94c9c9458c1a5a8cc348e3851e9a8201c559eac0d5dd9636aa7563715356c96ad849829ec4e4562351b0064168c47228c92c8bcde558118e40e411f58d66e892e71fad91dde2d5244c682301b51803a9a4f9aa9284f5ec19360d47845d3b0225d515e473dd5fd20e1012ae5956a3716adf15b979ccf45f9aceb2470d6bc1245e1e4ac6d7b11c2dcd5e6886a61246624dcbe6b8ece3f24c5158a5db295b8744a44e7bce6d86b69b40dc3cda1d394b640dc84d9a1ee9e78ef38f331b98c2ae718d9b1c4cb4d5ff545a37788a2a514e2460ddb43ece75a59097b544103a9d4a6b1d4d7a48b5a0a8c60c2941f57aa424fe6638881579159a64846ca3bde91aba63f901c6a79e72d003e2896912ad4143c3818e498b40e140529e33d11f772e9499e55ee28c2b21d24c87d9fd9cd7f66b899f3a5705f23646007543a4c1d8129335c6c1921cad36273905717b5a03a9f263a4799324a66cf2c6838a6674912dea3414516536abad9c50d0b1e75c3811728dc335743420f59bccae908a93209e3044525df45d9a324536966dd4e04722b334c52edaa71452631d15b803ff2d174931965991d7116287d7b852319a709029827e4c92c231ee494bb5cae0765dd4e4674849163c4e15b17e48b534631eb05f06e8bd else 0x9227d80e1f45c80875141ee60f1233b93339a0ad167aed0968cc9e89eee2284af055c0d2b8f4af2bffb441519b4d77932eb8474bd6cac43a69911bd4bbc564bc92413a5fe829517334ba683cf99d1ddab036698948d13e3465296e8d91d85df6c2162e3e48225dca7e99860df049e4a093d70eb2c27225d0a2adc00a8bb8b232cb20a62a0456b1b5621081d95a2c3e53b901b450f521695461e2b3e8588479593ad9a9611541c0f03988cc8c6a49348ea99c6048b786aa361e59c890611a8a656d60461595dc643806b2b83fa9e04ef349240d539fb0592052949f9390e4ba4a43f6c0bb137bd5fa611ce8358085db4e4de7dc305a9b275658469a0d79382522e608ae8afb4a8bd6b6ae9644898b637f6409704418a73165d320b5ef272f41153a08294e432125f6778c5dd3a46293b59040e01f3d11529aca4d7c4d47e16106cdcbc0648ff5e80065c57493a3215ac254d3e74b724b6029266c3441978d2a5ef9c1b78b8f222c41e7d6c289699b8ba90c044e61f2a30ca44af69b297a8128d604993e9687f1d2c4d26617b830de19a5dd7e51c99286a139848feeebe2c264abfe182d4dfd6d39e57ea1b8a9c7cf21956b8b9e0aade177a25473bb2ed5ac222e3e718751a0ecead6bd76adbbd772519e87da974495c58a2ee67afa2dd146a55feb3b7743b149231d895681e8b2e4bbe899b2d57084adccb7c712e302d75d10d5f1ac0e34b6a6dba203c9baf19ba91515c06e585d00edab3cbbb11191f40f0382806445a34f2307b229a22298bb82a8ba8e10b79ac2d4193f7293b455481c13645508bc8ae162aef2504d16cb66647f0903b82c888d85d8a08764bbaac8ce8c32733cb6a38d480c2b2722bd11b8bca38042ac88341c1abd65811b26564cdd8e92119360d619996bcfe221648a9d42c7519d067f5676e8bd043824aed40115bad64e69e150533de6cf22a975d0a460dc9d42cd60aa8ec2ea103ac147012df6747890f83a3eae2dd2b0c917f4381dd206aaaa98fba5589af97710491f5cb0c10fc77aeaa505415f61a34f979441dd0336463af3f70862449000854acc2988fbe175a47d0c7749f8369b0218e87e27dae214faea301aac2bdf2052dc1cc95cdb3e55dd2666de501e77c714290a3391a8695cd9012db10acd22086aa6bccf49c5746a53020e0a8c2eb3166c53a37accaa86552a51ecd2866b41229a99b99e36036370816287811971163f49b8a0f9159685bcef3a713994d5dd81d8450f0d5049eda649b06dc94bea22aa04ff35498ca1a40ae4be4e8ff600845c7d04f0780f04fbb15d0348a4dcd16f1c5f4e5112d35f4a1021fac6694c7ab4d9932ee5f5ce02217a01951a1c363228b496f44de959672979332a0472269ea71d07a885c730669925de992938ef867fe006f32d0842cce440f5d59a8ec8e99a9b2f236abfad3f8a51) else (if i<7 then 0x123c7689c2611d668e32bbacb806d7e451804c94104dd0b42433110f6b8920a95548976e987612a9b9347562b2948ca46e8709689c795f5be23637f4d568b1f0d1b15112e2b895964358ae9fca79fa673b4afb2578f39ee0bce3a781014e70b507f8c64026c1d67b9691c81e52c5fa8e1b13f64a0220900b1eb766a469969a41680a98eac86e5e8213574b3abba786a5996e6067c248fd05d640a8ab22f810015c4522bf6a72a3050f051293a8dbdb0776f36ce0163c1c8bec1c4fb2907142818b1c569ce8a51a3d9b402f03f352743fdbd66e5854f5e20427a2032300f66e13c07065a1151ef3ba4b9b4eb6a2c2d2ec371a9332fa160b1759a007b411d4a37228f66a04a2e8caf9281349620eb2c8d340049491bb18fa2922e91f26ffba96ed959278d44200dfda4843326b1a360035a6bce06a194a9dc1ca4dc88008ad5e5dd467210101fa8381e9914d92cc3544539640657167125490daa8aee5bb57f9b71b5dd519d90cd9e3d78d58dec10cf3f958bfbcff0c9827bef3d1724076737ac34407dd5eced06b898d46a3d08fe8a29919d7451b4e82d53e6f05391924ba404c053a077480c3e5a24832492bc0b9025c68bd300619a4a400d1b464b117230c6dc596ec0a729b200ef4030c6c7928919cad5e13db2e9799975d8ec6532b9940d67d36d5107f6ee99a79aee6a1dce0d4f8699b621af29b25e34d954af36b0326748ac1a83add832e46a9476e215cde46a457f2d4713d8dd816113aa36f8c85e19911ba08092c4c18244b23cc3b383c39448c7325158a3c24f846300efc67a7a6465af2ce89f931ad84b0cb7ef25a3668915ea74146adb86e45a49aea1c18eb84b53c09ad8f29b4f53a211d192d3241362de9bd65e58426606372220dc936233bf4287bc2fbaafae33e9917d2e1c8d9a7160a8b223576e64db08e67042bb5f8a14b36bbabf0069c27012e05c2c112672921191b372d111c609ce7c2ee168f61ef6267a01938490fd91608c8336882c4a4b89a76f47148a85e23499e802d9ff91369eb09d1ef240cbab4baed20c5651d197dcd14bd83e763d8a34a300716ddcd62d709dc0a2248d6fbc3b8da8aa2652517afb90b9b1c151d0b6a08382b4e705429d230fa907380d617e940bcb80015c6157430b77a7fe24bc2ea22236a229aadc512dc273767a359187141e4cf3906fba63b6491e5b0853314a855c6172c28329ca072a9eef40ca4d824ddd6f1e414cf8766d6384d31a475a6cdab8ee9195768555da71ad691184c439a2d414316656f35bb68ad544dc36ed7ad7abf98e8fd35ff572232cd4e5048264d753b346995d904964b3e56ee11c54d5504a6d4850aae5493196a7c381216c0a6640790a62ac26e72803d4e7c5bc3d6b66d8c32ace4d3fc3812272d21c108fecaedc9bbd0f2179cec20054f51219229c5489a5a2b92e91bb9 else 0xa2dcf44d74483b6f1b362704a53926dc148ea9934af64622a408dbdc55d7bce034cc8cfcc1b139c9a73a1644d05a00f5e40e62109e5c8f51747ca2c1aac5bf5503d89d2c2fc48c1ec1620c2823f652ce7285c7cd90c256d25aaa864aa9c2f6e32dc88c3ac33c9f566aec95fb2522a033dc6f6c1a70d5a4e6fe0cab298622bc8142096449b6291044d530b0f251e328b9a5288d9c2b66099b0ab985227ed0d48411a30ee66e12c9a22fea497af3ba757a95e42c274ca99345bb438b8d06f14772f99567bc72a51180c734157819482a6329379a75bb06a6c96c59791f749820a11123423d7051e890fb06bafbdc339c462e3d1572421410585f13762e843b8ce7d2642945c69431a692c81f2c1f40c4b48b127034aa9e4c0108dcec7b2ef2cbc6ddcc0af550baa5ab9496ec647133586b97d46da69ccc16fc8c87223012beaccbf659044eb5c77a499a5291db96d53b8c63906a23d4ec54eb37ee70d1047c5554cd453bac418a85d84b7750b9918c0291e9aa76f9a7c81b4851583abf91cdacafe427c0a95467ccac0243f92be5b97b1935e12ca4abb94ab8086e9aca0a97937e16f58446175ba507986226b0c316179d1eb03ad1e3a790d386d4e3ba8dcb2a6253e258782a078e16661494bb610654c30685f0ab3a86db536c62a2fa4329ccece620b1ebcc9b89e86d792a273a938a809c327ab40c3d79a320c99214462b9066a225761c08c51465e46990e4b1030115b12f3a91e203e8160608b760dd04b9bbe5c54dea12f2a7fc9b955c618cc394d1e390110ffce3fc979ac5851a568c98135ada3c9a29a32199b050389b822fc0782abe251bae68588c13774380542ee9a73684736b3e0dd3bd3a762d478085981225772a31fa000e62802073188048d441e933be2090f4c5b2ccfcf4142a4aa30161e0a98e5ac054cb84c1ae20658413c589ef66d72f42cab228ba8d9b0c192be02496d8decb1fcb233223113616c9a98b6781bb1c49b453671cfa3b78ac92e017033c941be9e706f3f160b5d5c5d4a4a088a5cd46e88f406aa308586cd721ea70a7835731a555d200802344b4fc5352b70b33b33d5f1057dd1faf83868f012de2467a00411760220e65764412f7658951a6af7322b332b44c08d913af5c609a7c596e69005bb588873627e586ce67091d7b559001f534e289d4829e606ed581ca9a89ed79b53f0dee11bed3dc4472cd8d0286192cc5dab26b2f12c8283f0df628fd000193b49e2c212c0d4ce7b2fa6292ce54d4aa038c4db6ce49898be60dad8f114ce0b41264bbd0e0bc8b3b702f9395ae154b80652948d68a73e46b96923b4c128f5c84b5177002868e36cd097171f93d6fd1c42ed58b30cca0e1342b25b03c47cb232293d21dbbc132b389e7ae068a9c44515812e7946b13580da1f266844dd42bd1bae40e32207559556bb692cf9))) else (if i<12 then (if i<10 then (if i<9 then 0x23cd932bc8618b7ed037a6c8a146a122da6bc10d733c95e6624f4053460d16ad0d2a0fe4480b8c9cd927684f6993625b0c35d26f8297d03e26651b77b247b1e3dcea9580f6544b65c5b3ad404a6867855843b0c9d0cb8785fe0d08da19b14a34cf5a39c6f1f34690865cbbc3d25dafa87ba7f4a2219d00925f9603cb5341670e3f7b5e94a456d0a61a9613cf8ed8ec8a2a4ac021ba54bd085a47b341273164a4fe12c9540535b964234632753500193c90cf6e8877a024d05e476c03a9650ec8091b5df23c990c1a41dd716f32846c83927742362a4d5924f5b8c410ad35d433dc3bb193436b48d180c1a702a068e170889305dc1dcbb39c576390cd2255fb67cb9becb86d9e9033012599a03765d7865a309ac04c182667c89ca9308b4c690052fa837491c5251e1cc6f928b0ea929d5520629ebacd591bd4215585a186ecd4ca6c9e56b390fd4cf768c96508174794a0da9b57069b56c681f82622a210c06e4d9b00695b45d83ba23a6e87768c53066d006cba53d085ae3686b8fa5317138f700a8c67f9deed3ad3a82aaad850a292d852885d37191c2902473cbc48af88c4e804d91e421fe992d3637082498c9deb0a86c766028d91fd1362476d41af048002aac50e7a0a13d73dc68d0bf3366dd3d964be92c0222d1247ba666533bea96481298a2d27bf31d60937c42ee836636de892389c08af89a8da1c932ec87a58bb2844c53490862cac63b881160d75370d67bb05ca972e934d917258dc98585953203f94d68d2be5294929b60d358f3eac956c9923c0c3301544b65d43284cd540825a9a6b474edd0b9421c5bbb037a4bd326a0a82d67a1ca0268f4c66ac4011b5413a9a0ece482203464cc1752835d054c4b2226cd26b3606fa2b918f2eb39e705a39e4d10f0a2006506144e91831461b5257a25b9901a36bad00cd4af3c697f4666b38a312966826d0a8945d9abd652993536584bb3949e64c9395b593346745c709b4884ae5af55dc777783201c3ad94cc5ef59d9929a53e08b684b2137c7d335ad0c96f0aadab81d7ab70226ca9ad40a0b2529e45ff5d9ea161eec06940dab47ce712f37cf5cb4d7ca62e6d061302a44a5bcf56456018553a530b7d5c7627849555218611d2394d1596311c3e2a39c7bf1a3c31164eae80eb520c24558e5100034b3388301dea4732598406fc49f14dc5746751dfadd9d6c8315b351af2057ba2a108c5757a8b2a0d22f870a776123092267e5631ca2eb5a1a4c538d785b3160848695848cb5b34014450237714c6a26cbb1a11edc81cdb422ac88db10ef2a999492c3b65f54d86a16bbcbc314ea13247629bcd8d4445c6c7a914835eea18107acc5062139626cd7231e37a71da5d8a3529438791c99c934fa80430c21d653c254923f157075a182591c3a66528121ffe8a84e337a39e4a2f4de82a7a09a8d else 0x36c4268a5130ac71a5b04afa231906c65bc71a51b02367b6dd5e7565db40fe14102591c9d06f144503ae1e24d53a34f5c6d38aae0a0523361e34c83808c33448efba33458c865e1a58f4492e565825ddb353458d9aa78ed94b1bbd5bf84ea4192cee23c1d9c04b38db16121147563d8c51210516f6d4c20f054f434e5e8bde8003a0886c395b75d036fa8251468eb6994d6306f6d2ed59180cb65495d774f196550ca5d538c6d133099c6dae43ae2362286c1eef0f2eed2267992d6b8dac7f15ec9998162fe9078eb2a3bffb5a60a059661a55c2b02bee02a455f55af4b794259f60503d1b49ed644df368a86c1c80f153f0ec447df19d26e468f40ef534591e452784106d0043b66be61c00e99961338fb6f2a21013b43bba4818160cbe691efdbf9d4f3a8b7f229594e3e327735398bd5503a296e0452a777242995d9e1692b60d2bc9be345f2c6928532a57ae07d4fca5d4f4bcc5347c58baa7bdc8bde5e5a06369784ca866eeb7259c93f431d9a047d00649328beea1778325118bd63e310cb3e2c3d077b1dedd35b698c9a7be94016f34c1033a8f521c6c89c03706ac84863640c19295258eb302550541025d42164a234f24ed9ce955f23a2c8b0057e1b171c4e5e5f2039362c9d53579a612aa3c49f1c8631d02057e3918958e3a5916c95596d42685c23fc191a9311a485525b756507ae95e7b6f4321bdcacc7119310f4f24a2617049045c8f082173280ba6d900e506fd86e5dd65040c571bc4933bc340748cb95d5d508c9da513cfa0252e3bcf4e63f265037af4c4e89dd9711f42b37bd91d4e34aaa3825f3ee7a2075220065c90e33937ce3be82d86cdcb835866a2c47812470404c56444b41a232e0a35f40b3b3cca0339c0f4a4d379fa20cb01533360475cfc8c355a931b53a886dce38c5f8c0ad1bb69d2f9c8f4d44f79f62842511dc2061a7199a889108cef0159c24d2e24914287911c30e664b5e88eaa23a65bc9ec3cee0aa94491a7ea44392c54bc481870dc486456f84b110318932e98df4aae807e64608867a9adaba4908bf8630256f52b4c66490479789bc26f96eeb4e1a0762711d96f3b4b33a9ac4ca519201623633c11b317e02e35102960824cad9351089b890509de042c00d504a96c944ae9cf29e77a1dc8d22099f31c3712aca011b79a378d271c994e1294972f823574cce2b1cd0b0a9a25abd9ccc7b2634bd8b04abc4e5e64ff58dfb18cd09f45aeba7359049c957b3a4c899b3224069733245b97dc8adc898cc9cd94cf26959910d0c4991095b0c50fb2e475a2df43bc0c50d667d824e5ee9e81b775f0b437baf928aa256ff1a593b19ab5030db865e7228bea1e55a626d36cbc38f457695f7b9cd350617a0022289d7d915658ce474aac9ad605644bf24037360d8f69173ca74e99db10a65c4a571dfa054141d53669) else (if i<11 then 0x9ce631d86d05ef46a92d8c43be475c0000004fc0bb929f90260ac3045a88000000000000234b50f54000096d35d71221b930d1000058c6eced480e4600aa6cfc0000a6ba946a39024000000000000198b800002a740000262c00000d8d2a0ab000022d56f3d9000026c9c16480000000002ad1b4028a911a0e1057664d161e98478cafd637100e94a4c11eac1372cf4e9000055d861a2c88f3a28551c8db2208f245b86300d86a4844c8470b03c684238714b4df48867a9e7ab70e000046b5242f3582e0df7210baf02d50db99385d956b08122590107c8c94c82c1192000048842edf283780000467e1de4b63de4368253e86da400005c7d182e11d4a02cd606a5d0ce45750bea30a1ca16d6542cea842ebbd0e263b09b0091712871e02f108e0a05f1176955c28e7a99ba3cfee602284bd6a659e0021b9ee13a816f844d5d1fc967741b35ad40000134ee3b7f00002462e77b2259fcbef933becba09168a9b5a048a00009bab833752b5d7756716cabdbc0000d4499c7c228ed5f4e84b400002d99c18e336eb000043431d4b51442bc3d51850ad1c9b052ba15c1094a3b30b885ff0b1fd1cfe64ec93fa168d4cb3c88439220a934810ae8ba55d8eb8d3a5ad96ca1a30520b2d81085903b64938a90e6c12bbfa2cab834135e529a312010822672a6ce40646e9de61dae6948852efa25a1f250617ba7a542eede704853d4a140ab9ddda723f906fddc0c61ba258ab6ae1c614431aee0c94cce8846d2bec0e3085f45a501ae0864f96cf1ce51d6cd56fd83dd53cfa9820128d1030744d9534b2800d4dccb65f463016d4665be89b3caca638bc0c75141713556c2f84012d9ff1c5772cb47918a34d12470586e720e1eee266daf13c4d2521776650d5bac15cea480970c57300a68404750da0733e6364c2bd08ef8b36bc648b118a6666a6e1796324880e09fd25f74a150cd19e7547b4593272040aa1202d5565fb8dddc423ad8a8bc798c9d10e4ed153107a996054d130276613383340d053355f65d84c7c299b5304d8b19c32c1cbf575edac2c4c778d3f8aceeac70591501b7a4d5252d7b60c11be52d807a033863d278b7b1c74da182dd69ac91ef30c058f4a45de9a09327783b3e8aa163e274ffda150e87e8aca88373cf5a80677517534226356681c715f0c96d94852aca59a16154d1916a6a895457193c59469bf28a3560713918212b20d6a414dc43da45e9639089d5c4d928de4335a59538aedaae4f454a44c3b6282f7c2acfd2143dec9a6d434d1048fd4447659009b0f464e4a9459f2b23104489930e900cf79d897788ca56f65f33533275ce70aebc1575f9b65100f4e5852d5768954a91916d0802796079b576e2a24d4abdaaa3ada557e7ae52dd6c1ab583cd21e86132cdf75330aec2f5822468dee01a0ae50c93491a9f7f0208abaef8 else 0x7840000ab6b27161b47dae354b0776b4c0e04b3273ba1487ca50e905a72aef011bbc59e48d9286293904c9a529e84b332304982d08c4d36ba5b92430a612b12af90000216b00000711740905a1ea6aea823fbb5032bb9a99251b02b104993d0fbe1afa27100000066033265b9c448c450b334d0699e925b5056752d8c9c7f80000ca66000091c38157941fa465f1ccdb29fcb588ce499a1a48a4ccd84000027069a9dd30cad1b9000002a16c7aac1d600001e388ef430d906c425aaca73a122eb747c486b000015836abaf16f31224f0b7b54ed9622e6c4ad9e250845bf165c2b23a8b56638ef004572412976a3174800012285291132ca56efc28ad99e3542b95bc135d09b1904e011cb9107c6b61340e54ee6d2ea03e8c1a980001297e4d350000134a7647d000048f4400014b99000020168000096c09568000012bb14ccf8a22000009a0956928142305112ce374efa692a56ad70dec951a7c401aa92816f3415dc7443e9c051291100004c90d2b0a7027ab7b4c3f2092309b30dba20f0d5cf31447948edcbf2f380a4cdac1a14322529cc6fe02fc8284ef5103b601a750c16d80b00000b0b5b98110b9328d6000048c2a2d6e8bc4958124848df7a0ebc71d09a79131fb23ac3b3f30050a35c26eaad212c726689c8a1785f94d47a5f68a5f5b0ed0aa3647cb75e19b07a2f8d00d32d9d03e6914c6555c352bb40bc39b0724888f9445fb6e32586406de88e6c48ea40588ec747629ea498c76450d84df1399e462b70c2baed44ec00f11373100004cf94b6fe5958a69cd36ca1ce692dc0dedc2f7e6883768c3df9008d55f9a9598775119ac9a63708d3974b440851ce5111e3711ac7b5d2434a126a261b8a5c5d3163608bec3a6cf14ae97011ffa6e4cca1d025e4cf636aa661e8e0d91a10cd118969e1a3200000c2a4df16e1af5bc53260e44ad1aaf2dfb916d521fccd1b26481408153ad163d5672ccdd48cb76819b22740a083603339434cca96b6f6d562eaadcec865105b534e17131aa340a114d89e65ca492362878ed919999d424dd2307b4c551d0d6aa5b3533b45a6bccf3400003a5ba6d9b4ad66cb3504560a2c8d2983dca7405b852c841c77723087c95d191ea34a332c4c6d304a4ea916e82765d12bc480980c06011506b740001214060dd00001f6dee2e46c9100000000082ff333522d6468ca0000963500001125e000077d4ca428f6060000b43a80000000123dda5b124b14caf11bae406a8000095f60000460004612efacd6248b7981ab1de2e7ba922f521ef29a1ead7d00002aaad06b32172bacf2add0000076237a5652902a6ab743d000042fb400000000000013f481fb8ec2d57e700001d128000016fe80001910a58b100000000000016eaf909a00002d0f6000030189b6aa689b39db55a6547da47d040cc000000001a8b20)) else (if i<14 then (if i<13 then 0x109942a0cd40459288e74642c4d9c768e8a449c88d2d0b2172407a73554834c9d44f523069591146978fa8b1a3ac16912cf536adbd0c224c064fd34f61a62bd69257bc11f5965386bf975aacd6d4a8148ad6500e346494a3de0349355645cb4e452b80a8cec14123aec97ce093e93c77318985183488ab9c5db83bd15048c23845c29201ba5216655945ea5c508000008c972344527e4376118386fe1438e19c0796f919821b6ee2cc517925a2bb03a19820db6bdfccae915707615c000032f18b2532401a0092b7cd9c0d0f3490361a7414a4c6ce6bcd4001289fe0820a6c403151644d502399450a856dd1d669a419690a2d29756c1ef75354312e36f953591d2e0d26021ff6f1e420ea9d44e0a24b32209cd9164dfde1133acb2a6c4912e61bec5c38d26ad1686f3febbae1815c0c9ab2be9789a0de40000a4abb97ea27248c490964b734cb1718b9c8eb11df698a74562c709c0b86cabdef3b28f37341339ec6e36e67a699de4b2b9c37c000043ce000019cc56fd33b8a800026b8adaaeb438465241dc0fad822ab1acb8000021103600acced54f437081d2f8000208947684a324a9cdef10279303c148000252f12d640000000024817799297c89938d83d646ee00002a5c8cac732965cc42321aec1378f62b6ba074e521a000029174c92ae5fe0000952b4e6620e1400009ce3000002d16a682a7e38af151f496e1f9ad34aaea969b6ea303ef468e4967860e5abfb89660f09c0fdd3c461518d0fa904a32c34b819ab42133df440d41e2c35385bd262e78408aef1e64c290c8cccbeae68ec4d71aa40940cab64b34ac16b6a8d11e9244f55980e3086a4c8ce4a7b08551d5bdb5a120b3f80006521ea103acadce3a2ef0c12a67a17c58a8f11c0c83b81fba23e99f97280a8908c61e492a28800c560af6412005904426b499429bb0514a53bd862b5db36c0fe3c123857ad4fae40893f2800025a784707478d80001994845d0238f20819a257797a76bf99410f45490cbbc0a001d68d971bab00000a8606a282c4c38d13b1f440ba330ab410ccef5c0ed5a82469b21fb5c726000030e89df94d722a0ea996331745db26032d96d0a0f29e7b56470480e4d695279ef28b961195e9665dc2c40781282850551836d053ba128822484953e97652224dd83af15b75c75c539c9887a8c3de21cb34164af170000004efdaeec1a1aab44a5375e99aabcc5d7b2bffa743a02243163498dc0000000086e623c7c00002a7360d20000054c316432dea939d634eb4a38339b00000b49336415a4780000ee26d7919a044cbb2c3d486018b245655056fd407f0000516e5609926dd918cb95dc60fe3a50295925702956a3af51433916999f36d0cf43fbbdb714eef048447382541a73712fc14b64bed42cc308931a67a39878661966f80000201b4001420044537ce else 0x8a0d192ef23b91c873c9baa1b068240865b4d52d46e3268108db6241e3079a25fa5c3e8a273595664bc813ccdde87a3bba09c28a68fce14f12b8a9dd834df3acd79f9b273c6cca000048e24b5f00001364d0c98b06a5d26c614879dc9400aaf9b669243f20000000012f127679000022fc490d2095cbbdc155bee37f37e04d5b668fe9986945c128d000008c0a25bc8000000004ad300005dbc075bf719597649dbf61ca26a2d00002dbc51ff082619af50e579e734d95094a280002739b5a7a054d945ea491d686ea7b03b0310860f0ba9ad69ac8d19d68b6a778a512c2b3ec000000003d94a50b50c550000467f42418a0c599f0dd4945ad1679a10039dec68aaf2349000030ab504174fdebda2036c153eb4acb38e7aeb5881f763ce0348a28e525aadbc500003b17608e8846d000030962d160c28084d743fd1e606797b9208393d2d2530d6257ab20df8aef34d8163d601f8668daa0a4000005ba1e746466100000d30da90f28a03d5cb830cf04f2295a690bc659e7db4e5a367ac89c48c8002298120bd6c2067893318a0921f38afdaa79830da360e8375e000044951b180000144da201f2c3300b29614a9b9848d025270af5897db341cc8a8330b471f500001078ae1b740e72841c0001351c635b1db910b36c4a0b23980002d0be00003a15b00d1c0fa461b121ace976f4f000002c34396943341054b41e23a3d8b54d756e11b5a69ca6a7acae64004c2fee358d278f000049875554e99372098bbc6647348e1a4a4edde10d5fee582b64b09d3e709aec4f7ba65363ac040ec41000016c25eb2464d879ccce88c284c210f9a73266269a02705f000025a029586e2f1b0b4cd4b2f5bc5a1f824ba559d4a4069cc8b5a92c9dec58e9bd46fb2509e5792f5b19334b6e91811d70eb99e51ec689f96eced76d3b81f8effd304986f43a47a6bf005f8b9734209035fb75870000487540000a0f891f7b610a220b773e7a0d3b5462cc925961bc0968e05dbaacf11a5d208bd2dcb547d4d9583c5a593ec663a4cfc87fac3be952ea52fd99e12f3cf40cad68b18e8e13d2a4b474c13d75f41e6fcc441ecd84d70daa9757adcbcfd6f6400632b3fcd37764530876073d91a3bef5a4e099ba47304aa6b7971b8478300002d0caaf7300004c2111f3d7162011c55cd5d87e06e06418a3bd40000615991a6800025dcb242ba28fa5a74e2d0d97e25a9be47a1c11680629c853e5c8a2069b94ae659bc4d3e0cbb127ce0cca98a0145d3a68282e60ae0f2fb385c6c884468cc9a1c57fdbae22944695d7232ea2a709c057b33838121f5eef196fcf7a04d9ee8086936ae7aa7424ce55f92274ad063ea1091b52906075fccdaaccf8508e2585d4251cdf3354b2903a305cc105394852f8dcb659ae8e0396412abf248e18c01a703cb116d499834a717423b90cd41b2f) else (if i<15 then 0xe0000552ec000126bd3870800000001419f54ba000024557213f59adaaa8800000000507a24d48c3a8565fb417000000000042f99e43052642e8000041ba1264ecea7005b508b54106f2e931cb00001431983c60000055b38ca6c3c488999b5c00002b6208ac126a100002cbd25a9d2df5c8cc8000096e200e5a66451fc0000008c42c6c836308202b6ab2b31c087506c8125a8000204d8e343000000001b4265afc3832469f8a0f4653c43b1cca4e23f6e16899c0c4deee99525199d76ca34aa25176e091f343da694388738042c06e36ef5f45a9000004d3876ac64f8539326b20000141dc94e15e8441ba76e6592924a991e2b2c43f96f4b648c00012eff97d7da1f8f49a00004259444f6af36c0264b8ec41a245804123acb4800025f4200001458800025df2cbb345eea36f2e09f20680000381f0b33933ce9b0f8e7a00085644043f8c9f7190652488ac97000026ae684ad3dcfa3b7ca010000040e48d3fca292475f4405d3dd6728d592c250601098c0a8a98f0900a272d5a38021332deaab5a1e451abbadd804b41f3cc64fd958ba3b04b08b408371d000002135ecf5b4bde442192d7a9a524da4b6e0e73cb1b759a9451b0d377f6450834ecd659e78292613273489a10ecf22dd97d44e63e51bd36c830bf00002b2bf23b962e5d6179943edb7e358e8288621f684b118b0c9966c90f1b6e084fa942e26ce110c86e94ba29b0fe17689519cbd41194d39ad695980488000136ec00001661eb672ee32441d242448d452eef977c565a8e0c6cbc06564d15728224000029145d3b69eae78a686f0ccd0caedc0000829d257f217e0ef2885f7a1088ed2d2c1500002dbd4826eccefb73edab36656cf39f5717000000000ab54950dbceb242ef2cfb205883620242c2d18837f80000c38a6b6f00003367e93292331000022c4d423529a0bbc595a52907c0000b3e4a4b68d9f0c82d00004bbf6f1c893e8083295df00001724f82c6a31c000012d87535ab1ef549945b0e000003ed666d70c7e05d1b41ae5aa8e66f104e80001d1ab027c13ca9df3c444f058f77cd1451226ee8ed930e10c024c29850f572432a6706b3f70ceb22bcdbb4c2b48ea094f3255052d0695303c97926b26832235a4bd5d5ccd538b6b2c4a82012bad0c20000471a9b42e34e96a076309d145437b478b4919c0cc226afeec46aa3a01af9e4b311f80000259d000012f29941a822f800008e93a5b6b114848460000879946a44df88e80902541e1ee1454522a40175de0104f2a77d24c0561066ab216b2a7b538b0d0f9800006650180028ac400003857ded021f037a5abb17a57cc5ab5682083388ecb4f7164769357d5a9ec15d8817c9968993c4290d4498453b08062430a596c32728000245dae415a8d32645583c26b420000300855eda2a5e96244d20800010e8e9445ccd else 0x13674210b9329d45d5c57857389100ca85a5f3e9b2155cbb27fa6335290eade3088a1b58e0d1d971792b7aa0bb0a80b1edca5ece28c77ca35822d97a1c192ea754d39c4ee5750199f2b584c6b12ab476a84a911c26aa0af35a33885381ed001735be4797bcf8a6cc41bb375940c9e6936e83697d3e49fbd2f2e41306ba54e6bad65b063c3c59a645a5b53322744a1358b9d77d06a4421c0d092c2d885c34b00a614cf5a0ee4e4b7d5ed2d52ed583717674b02493ca000054ea14209de8c00009244c5e65872e000000004b57c28baf8918d56929c5ddaea725000000002a11e8231000033d54000051609af2d2dc52e0000009924cc95185587a6126a9ca35ea70f33189bd9c5d2d5bb40000000040c15e4606bc2a2b523ffc7683016d000048b610aeb202f71dc4b16a4305172b99c1d3339943d2277a3a3dd765e2a92ef))))
def qix11s (i : Nat) : Nat := (if i<2 then (if i<1 then 0x8002031c8f803000a00000d802c0000053fa80380000000022d9753600200a003000403488d0108006000000000801c00400080180052660064b2c006008002801b5fe00100069b800e00e000263401b0e6029007620400400000a000400000080000000010280004004023002a9e96d401700b8000008000002800802900c00c001800001c000cdd0026000014000c00c000002000760e000000010400200000b001c05c019000800c2e604e003000400400087c0001594000009000402e00001d000601e00e0018030020001d23806400a34f0030004006008d3a803400000d003001800000300048b400000b0010018002001001805000c0030050179b0937e00000280009a30018020136018003e7fc00000200580300300240290088008ad602a68b00000140008002ebe3f50000028018c0ec0e80680444690000025336000001503800a000011802403c001001001400400a001000000600479d8074038018000003002d5e90048000056b47006807000e00b0030000004000001800000e0174b0aa3c00401303a002c060000000801000166a0050098000006000000176a028000000c000000005800001800000d800c000029001000144c001028000005600102a254800c003002002000400102a6418000006001802112400e00d001400e0070018040000001002801c00e00001800023260050000050004007cb280140de11d016000000c005000002400002c00080651e802b003000000404e003005c00a00303100a8034001001001836800600400c401f087001805063202a008009406e00197100016c601b0058024000000000eb9401000000280000000030033cecb9400300000ec006016002001005e04e001001400400e00f012000c0010018000000000005000207c73e00488ac002000014086005602100080a800200c006802800e00362a0084004036001806c000007000333000002b0138030000000001152800856e004000000400101080f800200a9cd000001002500000c400800101f80140093f4000a76b5b951800339f000a00000a8000000012015b3d000d811000006c004000004000002040500e628c000003002002f350009001800004402cd5b0008000000000806800000a001800000002c004002000001f009cde00280244d9803401418700280940000000010ef8038000006672000f134005800c950000000804cdec00e0e60060002010001001400000200f0080000021009805800c0001e68030042097004803c02600000b80300020030098004000e19000599003203800a00b800000c0026098000004000801400b462d5480009d942e000004c06800b00066835043a54f184c000400501256dc000000000000c00400dc38804c01800b0000008000000000804400c001aed00180160450000134000000 else 0x70006ac0050017000b5c8006000000000401601700000000680060ec8014014000000000c008001028014805a03e0000094000014001df821f200d003260c00c00d00d804c03a00000000fc09c9ed000cd3803aa050310110002798003661804400a2b800c001600f00bb9bc0100160065fdc08a0200030184006000032000400002a026d554006000000800c006001a38000800800e0130074002fcb000800800202800023e400004a044807001e004000001001a000000005800000604f9954fde01000c000000c03400480480060080028010024000004005c00d6fd00f82340540520018044000159000a8d8004016004003800000b011003000601200380000083bf004822404c000653815402800a87c92c401a003003a74c00800f00e0010004095000002005c0007da001801e0130048010038039000000001a03203b0000006042004801c02a03f00100100d600000280e002e07400000400000000000020002cd86e080480095c103b801402126d0040c9c004049021a8640040380002e4800803a000004802e01201f000002000600300b80ba600003000c0110d1b1380ec002013004809c02c00737700040be023002806801a0e2b938058042000000007000000d001c6c8056000007008000401700000001c6003011800801400f63f0060002000001001c014018007a98002971f001002001e000006004c030008033802c0a0000004813c0017b2000d3640583f400080a40008fe00f0068000025001800c00201500380fc028017000201b572013000801d1fa05100d001403600c004c91000044700000000bc00000c80980055a70068015ff0005241005405c000002001400a00100002d400000b00014f400195075780f411e00300180013f8029000001000000200b8018008b1a68c81b4014000002800003a00401e006c00200f000b8bc024048009002400a0000005ad005a47d006021401400300f001000000300f813c00e0d08ef804b21d10ac3b005807e1df0052a1400000c2cc80680174b9000803002488b00300240140090018ce400075600800000580000000040000009000800d72803c0000004000d2600f35740000000008054002b5f0008000030007002800c00a01000a801003c00400100300374df002016000a0050018004004008000003000004e00cb26003e000004000800095879080c8006011008000c00604902a0034004728006c4cc010dfb011ab440472b900480e005586800a8000016010d548d9000c00400000e801c0000030038000d2a0030120000017001004c01600c004005800600101a800c04a00000b801c01a03200053740249630000028000000003806000400a000000001c009002b0b800202e004803400c00000380e800cb5a03d800000c001093164800e000001800a96c03600b000) else (if i<3 then 0x1c0020240008014a0e00203c80ec010000000001806600002b814016a014002816400e1316439e240aa01e04a80000ae2e700081e00ac0001d6339c02401201000781f806d004000402a05a2af800c02c05006e83040060130303d64282000da1802000a00000002080340000010058019a6400280200720df032004c02214000183ac014bfb00280100020cc002808807a05c03046541c800604d8002c9c057114006403e7d7007800000c03606d01340520030d700581b005500808b4006000b4204480000f402580066ea015002000802c07901303e000202900d002c0fedfd00080c803402f7ac00b40040060000001ad0027000e48c00c00f01d81b4000003002020404edd4002c22c0880c33c7000000bad9001800005000001500a761a007003000008606b00000036a000a007000002a000c16abb80a000303c80ac01efc114480000040270004c3c00603eb21807019b70800000181ae01d00035d80480a851482580306e2000003400002902d0064030022c7cd0013920010000150002034005004c010000ac5800c12c00c02f805800802a000004808e003003000402a004013003400c01b9fe80140191c303782400120000000038007837011800400602c011002c018008005008412eab200e8338003590015800010785d0218216208000015800002402ac16807c016000001004002c02500d804809000005100b004a0e900935e400e05f003005c01e00700101e0e78002001802404e003035800002ce31002531005c00a00480440060000150000000060000003a7ac389001a3d406000a00080000fe05900180200a001b004ec26bcc01800e00d4000000022d518022032a6c001a30a01f06e80046a400301982a8e8c01000182d001a53a0148010000024016009c01006b000ba4401e0010190060000027724002000003f002055008001a669809001202400a002c01e592030cef003001701080440000120000094018009000800000803d025039807c00b02180258c6002002019800205f01a80680120490058030008008000000000e01400b80a8044003000027803e16000000040060309f3009c0060568913d8800c00000debbd584011b8d800000001900501c002800e001001000a09700180240ba00100f01180d800db5a5f780fc007009003400407d00000440140040018018024001008000000e006006803407005b001017023e013232003401c0110002fc403c016000202c01c914003800000006e00300a800200700d000000401a00380dc06e053001801000065700301680ab54d03d606c00400601620500d203100083194d89e300c031425c026031004c00c0080c2e47c01800b014a12c01002c048802800a03b008815c00604701494e143e009000000c05600000e8018c5e02550b000334e04200980a40b400 else 0xd80c0150099028826c03685401800980000000004dbc028000af9028801a002006ebe83aa0b00010042020004056000400c0b80a20001df4094001806406a01a0028001142008002803c014002008834c13e008096004013e00ad70b54400a01f001e3ce48208800800380000830008010000051001a00401800301000bc01400a0000000368082007113400200400000b811e04d001004000006c00280c80ee02207c000000e5e1011dea871a02000c80300060d29c90db0002027000000f61c000009000000008e00004d4007ab9012c73806e044000809800607b002820405e03d00c800c00800000a80846ca01b024000004a013a2300e403261003e429005a00c0010284010000046809009e00c0012dd401401e7fd006e86a00000e005014005200081a0054006001000002e000c448219f4c06e00000fc00001584900ec04a00c0ac800000e00600300000436bf216b944022015000800073206e00400401e003600f0018000006d3e802808a097001046c00000001302f800eac4cfb805803cff000200b403a000016000000132300100c000401a08c829004a0090b242440261510738002d40012001800003c05801b0110078015a3a00141e2004cd9801e7eee460898a88028025008802c0000230008050006008005814c00402e1dfe74c01000000080c40660f9034c2940040310000004000132000002c03202e484828c000009005809c114005000003400013f04d805c00200001500e400172000200011b902f01000b400005d0208001c9000701860ac01000409a01))
def qix11v (i : Nat) : Nat := (if i<7 then (if i<3 then (if i<1 then 0x6878912499fba28fe690238313a6a9525651f46504b701c86882b2f345e3910d0546aa4454a94b0c8800e2da086654ad2ca471d8fc779094a29d2c6ed856936395f237cee5ec51e301c31c4b4840445b1a0903909a601d23c78b104ae204eaad239473450561e9422bb5a2b5162364440633f36e3d0668f39f0c0144303648e4520e40e71a30e05ef07a2e5643e708e3c64c25741b6abc65a9565916ba49eca1d71f2da193fa3a45a051d3f850449913d3b8ed7d133fd93f7d0bc64470471a64ee59e0d344b6ff2a28649d8c25ab68d748de9b1c08e2718d3a727491448bd4920e3871dd4bc694f748f20cc133890d1377d9a0b2496bedc7972d03aa51da789d3c41c2383cd8f48ae66e01d9a3e989903265513a46cc59c915fba91089466d04f282269a1838985e36cc0366ccc96aa21a6ae9e2a1d77473401b507d733fe63804aed11a307a2a2898a4a6dade722cab99b55bb0b3668b1938331e62ea9d891c194aa9de0c5010ed9db8824ca0c25952464950bd5262d3816c2495bc224ada88a501b8b1da8c828a7c5645219a1bada41f129219508d29b5e77865430aec0318c836f1998263b1de3ee38c122b875159ffa32c287c107bdb9d4ea1a3331733abca2f8d940954f48c6c97de954d12c4b40c5290e286ed9604ad6b3806a97d68a63ba4d4500d9aef418643f9b3526a0482dab4358b6b50fca552ba27d13259c14a91c818fa482a530b097b9ba19919e24b34e3fb70362154485a86cf6ab5a0e4429642a306844c8630a32e32049462ca086901416369a5feca54d0f13216f796dcd048dee316908b1c92eb10cb438b12b7a0b8fa1e6b18dd44a8db748ef177724796c529f2411a930706f5ad962d2bf6bd4bbdd23b968a688f18b3c9ab672e5be888248fdca1c9659728e8946195da4980f6a819a89104bac88f161d6ca493ec1efa3245db84b134c112fb12510424ca2505ae707a5b9978e5611cb366d028f2ca681747b7496912e4840e476683d15c78d168897f9452c7639021a2cc8c7132239d3135c1b344190ac27c81592a897a218c1b4cec09f245312b7f02803129a8d933238b82bb8980c6e7746e7c9e8650ae6ee9b4a324b19ac186ea52b97c82f0d5fd64a5a2762223097844aa5bb1693ef6959f597d49a31dea9283602251116dda24b212924e5297d83a45eff3523a79515c09b0e2c59e8b8f4a11e681b33250986cb3d2327b28a193c249fcc2ed6d4634bdac664003fb73a425dd18de296b6f4260cae43fb11cc1248b3aa5ccf092acae33346c452ac65ce6860228c1a3916271960b1462d11b026752c9ea9454d9db50716881642050c5089fb2e2b2a52cd5771029b23f30bf9d95bcddc50e6773dd9bdc0d4f367bf912bcd64d9cbf16542773443854611780299c01a2def3f6d8e593f80828acdf90836705c83db6da1e151c else (if i<2 then 0x9c95e77ed0db4adbb8f949e16addd67ba89c091ba4a5b24d2228bcc649eaa3d70ab951c153a430326bc08907ca34de68a41443bb9351c1608459ed4ba4016ba2bed70a193fdb1b88072e4b47bd0f9117a01f36b7024871b9a921f6f22c2bd31301694826a714a63460a2ce7a0ba45292d83781266e4ff911cb51aa950c925b33998dfb1311320952a63d09826788d0493ca2ca3c91b0c35b54a67aafc51aaa768d66b952a70495b22c2b07115a841bbb09d89aa815b4cde0c381606419de46cd33129a464da53fd3166a125295b461dae7aeabe5232ea12d573dc046d3963dc4095f3ec37491e7c97ccadeb519425d810b8ca45b294dbbfd5b09a51d675762973d45504c3d45d9b4db2990d5793663b0bb3a62c8ede44b20274a48925127cae3819b0aac9a67972bc17191592904386c0583766213a943822e184bbec34f082b77534724f1452423329107bbe25b781c69ac4e67387201709dc311d43883166f9e84e21564bbf95c4628b2d13b4448815dcf26b786b61a6204f40714867ab635933a0072276dc903cc829a331e41e03cd29acf584ea788783e3252b925732481a00f4cea8b22286625b7ba31603232ba0a4a263945ec928258ea2789abc9148f184849991d3c08e7177d311924613244d4e4a93812459dc9b86892f93b75c82486380ad7053310c0ee65c83e4bc08152c26742063d8c5bc83f6a598a5f116f69cbede46212548cf5db7892722c07d2a56461389a624af6210ada32527113368940325281746c6f8faa5d201f2a0ba945b06c1a68a24ee06ed22abc5c300e57b6f1a27dfd2aa249890e42b4a1b0d651346e0aba5634a25609b0432b23ac41f16ca30d499998f4c9101bbe187c7a38cd289597079ad610c0aefc83f28879286bd9bb119bb770d22da4be5cdd8f780a171dd1d0912d8d2e84a1ab3df6449b28e92989c03dccd0679704388239a53008a624911549318a63f039aacba985e41f3802b7b4588d7b85000eeb443ef8676a675728bc2a5eb8f9942f688cc25be359fd49de56a205d3943ce643d6811a0e285d7c6be4a299a7f3cce669669228022b6a2d0020a303bc7218d4458991d2a19722e25d8a5454f22490ce3a6b89d6f224749c6a3665e85096a44bce09cece228b61586cdb27765042ba2f81d65bea8a1cae91681d41045919828790a397d1870ec3e989758cc5a501d434a271b8e8a20359dba02a144dadc756e6ba967194fcd0bb8b48b63492cf348dda44ad764f609ba540dda86e22c2cfa18b3e2bc86b186786196b0994c514fb4078c3fce95b08bfa8af05ff51838ca310631529d48b70cf5b889ed53224161351fb8dfdc202adc56c35a7412559cdf3719034a44100b1941118e128854c589611e125f6865140f2a06c80d1182985eb5c18320726125a5c3a698a4a1e93b2a43f683eeb560aa68c6462 else 0x539682d3849a4cf2da34787b91b913364df724bf94d1248229a888ca22031f2085a28a4a512bc6b211d5820895aa04374a188ec200c8d33d612e1667a2502837c331328cd1519ab20a8389b4ddf8a2a532bf891f0181528221ad45d968008518d1445e8da7d18e66132528ab6250311f4be635e9a3889812f28b68209540c9c74d4ca2b072cd086f040419d3d1f967a6d28e8d4fa597d0598ea9035b95b751be0240a6d6931601868522936eb4bb8e19b4f4b38031117502929d22d2d67627759c971aefb0a04694b79c6f1643573d63a9b3c876145ed8ca0c8fca1542ceb34a44c1691bb613946ec03ce692f11074474af3529dc548e5ae30c678c09c7c554812988280fa2b2cd99a94fd91ff0a496076f4ab5ba4fdb8d0d7bd2bb31303968d171d097b2514bd32108cace7caa2b349732b4454f90528f262298f02ca154c1382f8289c6f082b7094ae40630c8fda99d325ce68e3c401ab6822947ceac704b6286fcb3bed7fd04de99b49e75000cb16a8b9b1318da4129029143d3cd2308b7969c4b9e1a463099432401ab6a9da6c85fb32a49678dd6028aa8a126265e25079d0a0e032111725c62d9742dbdb9bb154ed8d4c97b010f945185b2d6e92080f1106e5a8869509a27e5df1573c657304c83dd208e057287a2ba9c5b001e804c1061becc61129a0955d9527a880195794b13285b53a46a8d0b04ca9033a47a30af0feb4af81b08dd1e6d2b192575e1581f504b5e81da1846ce0ed4ae99634c58609928b14482e928c5a078406a8b2874aca19d9c7947b7234defe9c0514421987d66ea1e90e70684f254152ce6c20288160357884fbc4cc9a554989691aa163503b8a13ce864e459f99a080be91551a97388a86980f6a26c821d83e1ccee016e570a226200b7f26795236c6a2a4cdae722a26217124417701e9428134bfc3a3f19d1e15d9ba6fc97d48d1051d294f1b9ada5ac071b946e318bee682208259ca5d453a681488ee593503f52d165337849f2dcdb0832f63d0556116626e9ce0ed446c3953f0198f412cb2435b7e115776214944048f4dcf5728ab5934a941d2fd54bf796fa2db9025e9456397e793eea2cfa61963040a8c4ccdab21a7b46aa1e21441a6afdb0763b052d30b1223b2539b76ce0b8c8f406c105bc4ac93527e396a58e1e4b56a111434793c00d5aa18d07216504e9e83524a227e0b28089d03292949791c32424d82dbcb47bbb81a15a29125bbff89058a2ff75421b95a24ba86722e4b85269b2b4f4848cb516ba5a5fc85c4cf3d956012d9499a70548365544a26d8689286b735dd3acca886c8b62ab0d73cca5b771320d9a1eba522f72e164de2ac8c9a5d023394df4a7548d909872b102a6002b2f94abf9052229eae05a51581adf557b613d309e680d8db10a66db1631b3eba68b64fb291c5aa5c95ed244c498b84)) else (if i<5 then (if i<4 then 0xc1cdaee4b3231439593c29b0823e058206cb0190283aa020c2991836d51a9c59a8b4b9ad84d31746fe69ac5a6032d44a467d22cc02ac0f470600b22781ac2e576e81ef4b029914160265010b616ca2d1709695ff99d02555285be5908133a46715d5130ef055aa9a92e2a1967216c75b49d2a58279c2b1f1540d0b349236238bf5836ed88f45a7b5325a18ef3bb77f23cff247a932696db82291c5c244c414bf092e15ccd48b16ab00164a9c932b07f4abd356b41334827c806a920024348a656ea0eb9064d1f048d86eff46559ba6ad40c614eb8e5d14de15d90e65491d8ae95a1b2e43221024cfbc222ab72940ad52bead37eef32b06fd2d4e4b86aa5b100093b342f989a0f71a5a2facccf9668e1af9914f6d2cc633b3920543b6516127ea365b1ad42cf7045deb471d41bac7bb24b40ba61845ecf2f28f0a56e9e7cd899d29d3423b4640101a56fb63653db0a06d1528388a8b117a2e2aa8dd8a8272277ab3b2b61115cb25c30047c02be99b25c1ca8e7929a2a975db2e66fbe8090b4c0d66aa4fee81e8513fca26230c368c5757241a7a4b28c9646b821de588a84261d3746de3dc6bf6ef8b79f54b831665369a996b2c039cc2ff2873921c1c3148e9605bf0c7accdc942a66b04627bd888596b4ef98b0c30cc684ccf502e4bbdd5af82f67324d015add8d4502154cc99c49918eeda2306b27654cec50cb965dd27609af710fc752477130c2028da5932376468833622d73292a2d03c152e09a093b346e52dbf0b37b09efb7ae1dafca10897e1b2f08af19264d67d5bb2cddb10e043743294ccdc2a643297843b07080ace53e66a6a0b069c2ed1edf4c3f942028bea24ee51b5b24b94a4a5ad82b994b58c9126df59755f4be4cce716bd84d12235715c22db7e3956baa3a5444aae6995f8b401159c0c5a2d84843f4c966d1da8c5f3ce894c91a8b15754b6b459d35207d069d2164d29f5a89b4e15b2505923518306b3115d0859e99372e83a4af5ca12145f8005db3bf295d5551141159c4e58cfa48567a048b14045a5e174573b1336ae8b08647688375c1264bc8ad0f0d3999c193d1a892a75ea36ecb0a926960063b16e12f849d214a373137c940a6808c27727b61e6eceec7736eb22205d72f3e34635b9dd43b551e4cab2db6f553fe5a06a86908511818b085987023bb658ca0532f251718c334910e95574e1b319d4a1c650492b8c945d4d5e4f06e6f84bb149e82266ace9ccb250ac102c55a6cfb95b4db4726b8602e68c7e19c1e2d5ac7304c45da70e85e48109a00b165f84b4d1847239acb89e1334779b03ccdcd611189199e38c8c8ab91b1305fd38869c36899c12083bc1c225815544d46d8938c4c8230a53614585410584484891bb52f75d3be95e9284d55a1c67111226500225c09ba0c0516266a3d0321e58e0e2796200be2c2448 else 0xdf0e79b49d4477ac70341cea29513cfa543674ce29129a0fe434924c35977d389268ec0cd620b495cca133c271b9082bcd1c2cd875c1373e13afa5184b046b9a2259be5054990f2bd3dd60d708b4a72bbfe4a3d49ef9186e642e5db6a288e0d8f1b32de921318800d38a1eb244a58608d1d2577a0a82714460c452fc94a8a8d89240584f72018a332d4b0e2cfbc92665060263949a0a93bada4b0e704afe5a3fa48b12dbaa537dc9258ab894b6942b586bac4792904b80b1b1be28be4a5eb40e18434f3709832b307d13a6412477999d11b25a51e9a52c384ed4a28adbed245b911908abc2466cbf82c8720965293ce24551334816e524ec044ab695876dd2f1699132a7a020a54bf412db06b9679e2557207e40f4953cad26e978c9c0a2222c82e8cf8aba9f2072cdd5b3a003bc428c542ab04c9945eba9908a53b324fbbeed3fd8a538e9240bd8d4542cd66c99f67b44839268f16cee91baa36410f1d51a499b7a89b0110c44fd5b7ea5c704c2a753fb3cf35191316d698a297720724dd001939b40f1896ecff28e35710910796e39481ee944b95224d9345a0241ab24e19c78619165b2f155ecee9f6939b85603d66ce684cd102bd4d6388cf73813285e582d5962817b6b8453904cae782bbe4d1399b15260a87cf2815199bde7d0a6e76c8583b14d93b69612bd103d80cd197844bab916864ce300f6b300e55662e622d7279c4d225ed9a764e96610bdc77c023b228a52b8cce5c2251425e8cd38b89a0f666c7cbbe3d686831da002aa0b44c290465a6740a573a848a531e611a1c5840ea6509f527b48e39b9b5d69225eb8b1b2498ae1388f5db9dbd9104b1807056b97c211e8f126f602a17f9c1a60ca104d1218912f2c9624703f1c64db5245ef3199999cc4c21d01428cc695b7da06684fd4aa3580ab280d4046cf768c7724b089f40795b37ef94c2a306b32a39460a48610eb329a4b3fe51331565c501e25d8863b13219720144e44d0800c82cb3a554810c60ca8c91e1704b3918125f28c2555414c75d121ac6b7883541376cf804f029453ba7fd832b68587146c8309267b101825b9a1e712fcc35b8b369a11a6416c8c6a803badbe4e16176610784459c0ec0859f625de03b6648a96b7614d422d8534609126584ad31f6eadd4d7832e421e992b9a88e501a91c19d83bce23b9b961219e12ae4cb7bc16238725138432911c611a8a46cf084eb679ce26ca16720bb4731116c11798413891f29ca52cea2952a9121b9d7d26a46d42635fa5fdda0e04c15b01fdd026da8d186071a719429a10c91ec10e384671c1dee39d3b489e1f68bad166e531400ae89a5724b752f7a6189276d735b130ba48fde83379308640833fd6dac49f2b01f55ba1ca224d1387081df0d0fa40cb3943aa609a5c16c6aa81d2c8fd15cb94acc37e145129c15878aa20) else (if i<6 then 0xccd088cdca0f6601639b4ca66e2242142ac5d00269ba47289ce81e73955b92832856c21ec49fa064904381cc1d253163185b89cacb901b48e08053221dadaa9dc4e753b51a07341b660c398cc40229111ff09d78c5ddcb9a46fcc22938315cc502ec156ed6733585aaccbe727fb40bd1d15c80659af80771b3553436e4202c5ed8154f423427035ecc27a0d49903c410eb5bcc09e5095a18a28a10f95c3a5985ba7f5c7d65402c89a4c4319524ce1a0d7002d9539364b7d2fef0032268c955066e854bd223c80198a8aff1721a470a5b912c5674d925428e19d27d6b54b0446d312b343e1adb985d87078575bb9f8d0c00eaa6b8ada25fd2a755514802550f6cd22d4a7929ab9482d308a52a4929047a8365bece2493ebb3a90be389d1d76cda55d1e5a231b026054aa89bba91109756a99e6a3da8e3706ef8b6f244b70866323f28a27de0e896cf2296bbf6c01eae16a613f84e9153e09a6e8e1406b59c5e0ce7e6a46b7fe1e8ec303b209991b6a3d962083333e2324ae72cdef169448c67c3e65102550e93385ddfc68eac6341256d2485c4fd324aa9a0098a52ec82458870545cec824b4519ba0d18b3e4eaacb8bf1cb9931467141506845f9ddf708b6e8bf2a7fda848696374b71976f94c74830146e4269c2452cccd8f9e014ddca104e5d9025fb8e61b9ca6a26ceb191ddb0588dcf059a367611313298f6e0aa50e544a86455304c224e690c84978b162799eed3e9666d4573fb9fb35a48401c419fbd061d592e80b29030931d54965309680b3cd658685469079520aeb4e1ccaa504b03b89f1deac5b5768af0aaaa9490cd017a16404d1c478aa4c65528ac68b8aa96bf208b948d1b2fe1ca08d7e499d8060897b1199206ef43ed5a8d2eb8449a40e05648fd06ca94100567557de310b9a404a175303d20b3b41ad9a7d30de017757795d911573d77216946db54c9a7c110fa73b5821651f6c25d30c4a1c44e14c9110b3c3d2b1e0bfd73d516bacd626ea0023282825955b1c89c87cb950998a6d28ee98c5651913a2a9a0688923947ba56cad8f259cb61b9164eabbb2a2eb7aadccc232ee71ad47ec163fe67928d8d41413a1dcaeaf782426499acec2ce446c391dc13f021f8f785915bfa8c42601f2d66b7200373a0c8f67e1287746480e121236b4ae3915069c6566ef55425da821072239637f1c9729d4f6ab41b67e50581a4df77be449ec077e2b0f73f2943e2841a969c46ce99ded64f98e8c980ba274243d4dc8f2a10130932bc2522a6f37bb321ad7670680d928a1c1b926a9851215b56cc5b3a49bf257935f18312ad368e716104e43aa6319d2986081ecae3c1714eb1a4c19db0e9110a11e428095d0300390d926738ec4e0d07d890f83b5b907e08b150d160030aa9d8e36d59d81691c58f6144e9118280ccd07d4629064899fad47b98e else 0x4823d631a0575d0a03474772caca24cb35cea1c18bb44098eee36e3602c3434e98cc681eb9600021992e632aed20cf05d426b648f0f2b7dd98cd45f26bff1306254125211151b685552b1002202185acdaa44ac70348f77440d8076405c92a0bb3ffa63f6ce6ea31fb9bbb457695e24a2b3c443945ac795006f168ca5f48af31455b60382323c07264d444276d8dc518e870c7b244ac4e10b830f9da2e5a227a31c6760a468490ee9e453763291b21c1d46b5d01e3b51652ad253d697eb7260da3e4a006259b818208c7665057333b2ec1531062f8f174a0ae20278990158519ade945bd301b4b0693f94a836e7f0658152f95cefc85a49204ac26a1b2c862e0dd530fa5b7d561ef474f396b24bfe04a14e719a3accf72578627f4bac64212edba6e9b0992159ef4ed0968438c17c27b58d46ab228504929398b3e959b49c2d16a0858323cc733cb17e0100a724148c38871a526a5703942fa883e53bf07c4ba76a4970855472a6b9efd61516c942b93a569448f250576c27443851b62959d193ab404a5e96c18a56c856161e21631cea34596ab3630e514a6c11b62dd052a02b2940e95921c678d62d297194e58ade9ae4c6ea67129a0144d72f16bc9ac934312b3b680caba48a57392f0a6ed34cbd21aac83a7338a4bf2383002ee6e8d993f65c1eae6e09a0d352a447a4c508b09449a723f6ca02216769428da032e4c8eb32b6921ac5cac988c658c95a33715c7b6804323101d049f64d08ba001132d2686010deb4d34b591c8b498810b8790ad202041255155228cf4a018789d7255d09dac41c4fbb4315cc6b9e5c1735c8c8943dd2073941d1b87cda4c261720bd2235f52a32eb1160edbbed5b048dcd9065106888df9d80b54bed48ecb9de23204d803b804a0702675c87494330d14ad04121937b71fa50ec8618005f4bf1cd44202936db228ab0691a46b8ea6101c4a43f181d761b0023d9435ac1acafbcab314136d0fb7739691f3d3e86a28ec01f219823584c23974942b6d963c01e1d23fd3776d2b962d9e50be34f82947504211830912148d84ce1457c191f045c294bdb69955103a042ca2d87a0549c229bc22540e98d40685a385ce0b50528c5a140823492b5663528184a41aed24cb94bf59cb648814afca01e0002aa0be4f3b5293a367896fb6448714ad46cc32340f75382dccb16d1bc42b9b10d9bf94a0fb71ff48778ae614a7769b795b44baadcb092409870b5ce69c756c0e059642447d3043284ab6a6a893a308d245f91edd14002e5c6c1a8c80d924d05ab60dda5879864d5c1097355314dd5145b5ef00d48ed504d9c83ee906391f5bd6ac93a95b1a5645ab800199455f4aa482f3a31c9145394dc045a2f34412fd3bc24ba1096d44b7b92d69dd60ae7b44bc500bae7e8940e46da4ae905ede66c701e18c694e61a082e876861b))) else (if i<11 then (if i<9 then (if i<8 then 0x513014bf75974606cbcc566b8caac53b474859eb2aa6b948a30598209e066685b4e4b15322d0727f8a5fddaeda8ba2821f4bef527ecf0f23145284614506449446d736f75b0f4daf3328e8105b1356f1be62f35c3212b4ec1e417f0a098137099e286526aa61a620e993c576838163bad6d304847d9506195392a0f7582a757d9482ebbcc4e4452213aeec6e0ef2b6a43b9bfe8e4d23f0984bbba829688cf7a0aea55b51e85ac3afbb2dc23592f14cb3c462e1ba18ae8879a9aa6b935f52f0e89116044d52752608f2136539d976e21d656f63749da426f3fe771f820a52ace6a740d34711b59dda2c392f8d0984da65a67c0877b423fa0ba511216c31552b80b5923e605cda72623c34574d2f494b9d1c068af24267715c019811d0a771f818ee50cf0a56ee2352363d9452669e8da2b68f20cdde7bcd6731595811c04c34430a378eca2a16dc771c49aba52c7097d309db0c115c6f885ea11c922f1d1b8e8e56e332287a114b8eafc980789439194d33ac86a78c92264f0a1b128e79025bbcb4859aaa85b53183d30059d60e315e839128105328b8273f9c0742c4b2b872a9ba603a8077438040839d7ddc4d64fae3abe21ea9d246c9e58a2e349b6990c459748919af698c6504b991bf95df0aa613393a95631d6c99188e48559f98460c6ee2d5a15d549070179482442b6bc90198abd128b27a9289a008450b1140e816788a14a52798c630b69e95bd6def949351484e59f16ab6a2b23b41c9c57638750b5a6f6dc7324b828c40b6a58aae0723bbfb5c5690f2a81ec406a209f6a09e51f78c9103fe2d2b80394a703900d1c4740578330184372672811ab38618b5225236aa91b2eb94940715f63839a1735f404b236dec46f1dc05e2cf7709994fd144689d88a0277b809e85531fcd0c8250ede65131aa978602c1c63ce8045244fba01801815df56779377414115278b11349193ac48a491f290199d7b06a2e9c72a29494f255362cbf50303bdc08a3cc5ef34aa9221231d5db83283c3bcfda01cd60a0de93c3850d0894301164336148fd52d7b68614c0450c068ab56df0063fc19341542c3738c73367a253e84e98941d905ad4a357546299149246437cb6eba6f94ca29802a91eb195949372ec7c76ca370fa41cd74786998b1519b0c8993076e58b5494c851889359e46e4b440e62248a5ab233a2685c09b0e64bca11c388a32d2bb8b3a740fdc6c2f28d287b092f36287318c743a219bed0816402b9ac8209e8c4f80f121ad6220d2e52c504325ac1860642dd09d1b4aec2d82e34733d23c472684070ce4c5038d0107a918c24e9cb8ff0bfa253ee6ca32a35dd970d5f0e39f32a84e879c854e437b05943944977a95a68cdfb0132c91087b0b7165e1b25051677c05fa1e1dc8bcb72934b911064a329c517752ea40ed6dc1c57613bca0608c10d else 0x25b5911b8000082282d064d1b9670c000082230000000008333472946f2c19480000e0c89d058468570d06fe4000011894000000004239dd326518d3a0394ac059e24ecd5300277000000000113a86929dc57c0000f09f3846d176a5ad4020a36df495f698906aca558f4ad5ac1cd45a100005616d1a0a82d790cdcce8ed976a3057246145c1236e59b2b38fdc00587bc64c59053aaa5d019f472030a41a920a2b959832890348d8472109d099e328c44482b681f91fca52d24426c4f638bd59358ddfa00000c60a386607540c648b3355c2c24969457b510cd194eb8091b208be933a51494967e2b7f145668a6b6201860bbbca41878b6dfbccaad2e2078312aa274c8b450cd2ce9af25d9548aa50c8532db9781b2becf3a96af0aabddc8d4ca8911d43b991a1aa0da2df1b6adc0e6614674ce749c125d459dbc87ad45c6818e8d9f5337d803b59f91316a8d58539615e6ad0d270774be7235e9d2f4415723735c26a01fe83fcbab45b0ec863255f15b28cd43a480e00002a8bd4b34c03373da130b1429d55c355e35087cd1e8640e2dae3451da33930394a5cb688463ed2e360000b9600da300000000095053c225b21ac6bb5b2919a0986bce0ba2604a4c308637783916dd8000253fc000027ffa8b76679ce453741ecd38a50fb71fa1aa1800018f694b3e9078c5a9cdba2c1554d19cb0a51910ee87375eda75800007a41a543a577c41e022e04676907eeefea0000b400a10212aa44ca5825d5a64e1e4965d39043b595885c279ea5b09194e242a90c714d1751b34d986c222bb1ba106ec93f70d49a09b41910fba6f883746420fa337319131c8a10439111c51b043ee24974453f626e49a11179e684a66dc00001295af3a68f1c000024d42efc011f0895700000f38d6d17ab780000102110fee2978c3bda50ed33a70000145346f59635500068be260f1ae7cc9a3dbb79ad2048e6395c4c4840e91a78a730dc4b57c1a16d688947c5d398a4ad4b62a792c8900f2c746f72b56439baef78556d515113a5d0596cae619374d81a1f8d2b6b44b5c908c294c50af613c08c9565ca70cf367bdd784f2bc877499aca5f34e16eee95bbc0a4880d809006742a039af407093424360f1c695e7f9335a27f82685d2cd34dfb3a5d89819e15b0c1995c74177d06a64128b6ea21a84e49452da46c8dd4b90c4e000516b8b84d495f7166a8c24b853c9a6a703a81d6ccfe6f2a2a1fe49a4dceede939693c013959ff642e62e5828c9c6602d2832c6d9cda5b638af5e46bc46db9d56cea78a5fa25d6be2792e7c452827a2d90f129b611afbc2fccd5130dad8f974d3c518ae09a978d91b71de7a56cc27fab858a232ce254956bb8d303c6eae41144863b54a52531428f4f373f03126c53b42ed820c592a266cf4018acf293b692a814e1a068459ba1232122e58269) else (if i<10 then 0x45caced258ac6580939f4a474d9729b880073c23c4e39e75dcb281131480000000048ef6ee2414fab3ed19680d9120000a5745828d569015247213a53000001298c8a7415d0a513e712130f880002487e92fe92c7d4196e7a168dc232783656dbaca0403ba3de0490d2b6485b4b3d92c525a280cd8c3a9dd4a938c874a3bb83e7900000865b9269a13c8000160d53780dbce5564a97979457167b1b100508599b2980d90ccd76c531530313629ea91e602bf1b3f51ba0f1057b7fdb9049d92a1bda30da1dc931ae97d7235a1b341c11e2ce525c1942feee006d339ac88e06000000c6087e43c75a4170ed529411a0f566663039bb60b000028e54e1a6091a504e524af3725b3fab8a308dad31658872538e90f6569324c7b4b0ac9f8907a25c6cd2b40dd510beca021d9298e18537a9b1ec5b75e673a15d596b3ddb8247ec0efeb1261dd0ee3f916248ccfa499ad8964a2847e8a0f86ceff713712d2a468ae77d2360381c13ed0adf1669790462574ef01e42b04c2e4a2e424eb71cf528c9ca540c5f07d0512a99bfadea691d84ba6a3c8a85e1785eb85c2c65649c2c630a72505db526a3394d8899aae2d317d360f94e12c1691edd3414b25941032c3b928c089578c62497bf278b46bfa1a70861309d9b9af80002677255bab380d61a86c2d4aac22d1d307e00d1468d262ed04ac6b522e2b274424701cd02888d000025056a99a93370000000029fc27707478aa543e6914aa528b10a188800006878b2e805e3a1ab2920aa01c95456e9d44ed139195c2f64f1923c05141c907921e00000066fa6372ef908f674730d1d515fc50069b717da61ec1e8e14345e4257a8503a4b63974951b84000167f1529d5d91ee8de958a41875e36aecc1235f832620b9de8e410788b17260ad229120bd254ac96f5563f42eb902959e18da824a9912c6c8f5d21c162de0c529d364000130b244a453952de4f73c195c3132a2ed2ad47e99cfd9d9000014fa68c7a51324ab88001128b39302d65c74eefb0d64219573ae0fa305a6c81640577586907d394ad242e06e7aa31f96266673762273b5339616410d6da8b9f6152409750e434000048f69c65c0d0a9a541dace5c14000000005139eda0f737a878fcae80ab788bf527738e8a523591993b49dc4995c48c95ca22c94cd56270e6f9a63489cb4d30fe8254b1a2261f8e27ed450b99a5df5af0bb4bd5a7799593a0c94862a000052a4a52300000000028bb15c26000065ab8000025e731e0905fa46691604209f28cea1ed59ed200009880800008ce600003cd80000192984db9a7fa0d7bc00008660715380000ca0a00004671c0eba9a00f60095dd9322a40fec6f406235926e2cae9200b9f800001df86471c7a42be27ecb129260bbf78d76af2c906a99a7a55b999ee687610009224b0e2270f64b21d965d8eedf else 0x3ef25bb832c518ce35fa6104000009a732445337043e1ccc152a124cc0bcca09f9d2b9a91471ba91ce3303b62bb2c82450f1533c04356b28ed00285642333f4a716ce7d323500fb00002abd2598a4318c1e92324a97db43aeda368b32e879f015ed9b6e71204ccf15cf9e73120dea1239429491564130aa77ba0e85c641b00532c490b531e52f0523ff3aa638e9cd5f2aef949c7d9256523a6ca4539cda5895de33192ba0451d0d1b4c4a9a8a470b7e989f011db60121813acefa0d9400005da2d0219248e72294651210b62a68b782c58ac314c4b45b09258b42680486008039c3bd000002e33291edd8aa8e4ed9de94c718508864c4b39001c4a738cdd5339e921ca43e92eab660991f44d0b01a1a00009ac7a43c64cae0000a802b8e818e5d77d594b693d0699d8502720bc0b5eeda9575622696916e526988479214c5b4992a106caeab4e800015f5600007775898612d600000651a8ae8c4cea4ffd0bfa5925800017634501323c661449372a44449332ada8a783b00005a8e4a2f768e44064daf92dbb4903991e69814094e08cbe96794d3e5078b25c040a6256bdc15a00008c9b1683a85fc4e29924e3d6fccaca95a707d100001acf297932bab4e91e619b24af924d3211863a127ed7b35856691face41a1ad8100c6ce1314559226d88a2d97a4b9b746c30945b27032fa8c2821ab0ed82414122d51c8b993c378559acc999ba82a535e5000025119c1d5236549f4cb6289db08c66a5f724cfef28c79673917dd369d35a771a4487b48e247b3064e859b341b10f5331fdab7391b2662c34b4f336958a90a577218f4c954a276aa346b37905b8000000010fcc416cd83a0000164a3b1a1c0a784137282f46362465ecfd6f6874b112158ae81e8be74ac24a4645f067203453044888805e9214a175402214baa98a96933da60250f6000092bb4d08cddf775333ae2a126186b7596c82a6835b523db2f36374ddb95de875595d9a51cda71058d450f06f4237354c8b121f69464a0de52948c554477c3f48ac8c173757a252a8000016c2fb9a69156400010a3c4065906c8c28cede7337ec95ec8d0895c87a39ca1686b5738a83a9699ac832386aae4381054a6ea7054ca96941bafe31c518efaa4d058240000000091fd5e6c4ddea6c1d94441b32cec0e180116d8410345d3ad4064b1352c28d8a621da808090001d19026100000256702b67597b4708d14da538e974e06875388d7394886f87b9097b1c31c93393884d9f504eeb32a82ba2945d4eb976466a5eb58370861b6dfd57ac1455e67a70ed74d13000010d2456fa2690295ba5098668b000044a7c8ce5474c81d2000009f9ac37b15d4ba8ea957000003099be540dd748887a2a99b3788eb57505aaf33a6c448d6911c5283495f0f3a54aa730951c5b6028e78782851d52dca1a12aeb826a1)) else (if i<13 then (if i<12 then 0x14aea497e44af2d88a42bf26d08bb70000087c960e90000000004131bab7d3fa6cee3720b08870546242000000a598237f88e284e5b475600002a0ab342b25a65144002d8241d8b1d23ac80000000094751e8fa529f2844872d29be04c1c261f4ad1588989a800000bb61a364ee0f62010a54f3b6b2d2624533b49f962f083fe9a12aab4d1cc4d66a0000014d2862d461f569994b80d5c69c2f23c641018000000010f96482513b20000000008ccd80000989c97ca696933d58071a01b500d5cd1d22c36d55eb97b9b4fe31f134348b4784a45c866950b907b4d1e6499f363fa7dc29a6d9d55296e4c66ccf8c4cd683cba6948000212974b33b7bf2579d21ec45a92b64d0578c5d0058728da5dd98000088ad3b11a44641ade018a432cd81204c78552100000000294ba00003b4bd04ec0000af4b1afa268240001693841120000244e86ea700003912c703e00000000087cc000142bc15cea3c4d1b6314403a6c24c2000008bdb15a35a60e650a95d02761a49600000653183d1dbfdcca1341d40000166f00000921273d424bd4a0f8000036485a5a0cdbf2881b48a43e4c9a4e6b10a620b1576076505e21309a098d17d554f603cd48fc400007775ac29c06d8000046f59232b8d29707c4fcbba7980000000000008ca64a83c000179549cc6ccd0c0000856000005e644ca06c3e9286eb00e91f6e21f0000010ad89d5c2d01000013632f054862671ee4cf1c00016187b67f226492607238575bf24df108ef28b3ab709d2f2dbee532a57eac8fb647d4566d472a80198000087cd79fd264b11b469884a545d5466d2d49527383011a6229a53a43bcc758da9a19800003cad11ac400004fb100000000062d6cf0b94a700000230424366c850d296542920f5995393ebc8b660000140724814052739c957c0cc898000002db00002d7e09739513c8c4c152ae69c9145a945a9402e505ca20625c8c97c2d034c36343b5919c6cd61320db4dd0982e2b0a00008ce0805c41988823046cb94b88e6366bd135ae085fa66027a01bbe7800011b9779a141aa149f61c1f2950ba72d4ae9cde265c9000005cda51a8138e9cabc8ee69c0aca3d8c6a421150ecf006e2b635d4f666cc87989214916e8d9816a9f25eeaaa4e077c6037384ea10463334e95ab84f1bb2d4a60c70f0000458680000607b00005b3c2efdd4e3099ba4cfb94a6493f489bd90cb0e9668234b3c1063a82ee8977a8cc3c3ccdc2be83c9a53f8646d1115452980da4b83689f7007152e7000026b7650f2a27981a8253373706b7c8c96312dba0000266d180c1961110ea405748210c50d2a6201c9480d6cae693e128a31b1a0328309e25556b83ccd9586a588c204a16508dd29cf06bb967e23052924500000000266eaf0c19bd718bd08376b2a5a81893a7e9dc8192920f38000213eb2 else 0x5a382f504bc000071baa5fd455e8db80e5e947a19aa0267b0aa94000023c2acf6e79b72abe9a9541ec57098b4cba4ed2058a508187292c5812f8ca2652368c173ec18d09e708ad94020a5db282c000020da12e0a4ba26571224b4502a72b0bb21a469c2b2d33a29abbdb57422cc928000004a48ae8dc4f1749234c28010d80570389648f5834754725944b10be11ab9190684fc000028ea10a3ea8a55bcc509d64ea18325b015d0f234ff593f7100b416848a788a2e80000ca4400005311cd0a82ed84cb28abfdc2b800008e5e72643b811acba00001d20390be049e6bab38000000058107943b722099a4851294c1118f24c9e338f4b153bd1bd804199c0000a79180002498f7863338a80000319700fa08fb5b454ef1262b10000000000000954e451a4b5b8b3f933ac4880000019e6973db35a95c7a0000054b594c48000164040000000015d020f7368034baea5692a1cd7006b6da52aca86f866eb5af40000016a3616336580000251364f4250ec134a80000000091ad30020c37f68022bacb1b06288376cc1b430ca11071c0000a003000024bec977e735d52d65575ec14b4b575a58e1e12e2313d1028ce2b2b2000008c7db894a25d4561279e0000008e200004b8ec09050423700a43322d92e67a82d9f99e43519d1aa253184ae650aaca616c252924103035326337e20000000009e0f33ad50b6d1abc00008f1eacb2a06f2d1bec99d4bd080001ca3645a49534c0e84e22f76d9b3ec48d61b1f483982bad46415715cb2c9000003732f3e16f5722ba00aa0a29898f28c821a32a67e7237a719b21f22ef772d632300d95908b000547b80a1b13e517724843718aaa3d12ee4b1d6c492361640eb709b229f80000f2cd39c8377615dba2cd155f92cfab811c0001199cba6f403f8a0520000b4b2c1f092b3ee5b6a0a01e2ae50e8f21c01cac5a62804296b2b571834d8b30456503c51ca5ca271768f108d4984494caa35813aacc9845279f05e0907e13e52956e6c0248e69c4bd0f5f56ef9a4212db424d7670487880000281f675322009bb6a9c09e77c29a70a1fa2efd200004b6f5b57800bd0f9e50fe3c0bef2dc6ec63ca45b0b82e96266830fd50d0267994c77567c52af800016d4b37e5327d91fa700d84bc0233080000c00f723083d8ca044a513904705f2e4960c4fe46d05cde519a4b0db4d0e4a704a35490e700005921e800e02852584a64ec0000888fa272b57fa32d32a2dbbf42c1640001735799ffa57251a1890ec0000339bd05894ca99223000028aab33fb437cac4a534628c92000021b64680f38e00000412eef3b909d400004d481ac1d02c342084a2b244d34e002767c99606d0a611e2b554bb6cf3fb6a36906191b3c00006670131c15e5526fc00001710c30842fcb456c17f9891c8a9ef29344c20b3cfc00006ea39b6c00) else (if i<14 then 0xa12ebd6f2f00004637a12ecc2d137174d68118bd39f249c81c7766a72611990eec92ccd8716c3606709a1521e2235b67c03549e960ae9025198303c8419045a35353712a628604954125b65a5d146350a0032a55d071697e710c2a6e09b18e4860c783697d4822dbb2d278a5a552aa92eee0637627cc8f3a742658c8b4854c67e611112ad6a3fd4140035e242d067331675178f4adf4237dd98ea3cf29fd20b2ba6b1565200003377207d5c2e4aab6894459cca48080000377bcdf5112007173a566c86e8c268598c92e390cbd1af96e4f876b1c546657e7483475e13148d48a6f85a1444a641179eef5f00005a87d26a67248000019851d5eb4e20364e5b8dcf12ce435b6b108710ce1150e857ebca09c642334298c171acaaa0c677794014c3cb907f040339241da376412600000000000009f533492948fdc58e49b54af700001bf71c8ad36033169ca696f2a6516e264bc0e8e2cce933a20170b080e35133e7b24905da88341027b437b25e80000173ed447eca382c08a518abb1608cd6487a650d4b0f301d2a8cccce426e291ae6eb0ce009b4198b46c24e04fad97e283245206e19403675482face44518b25bc8b48516ea531699dab40cc8da96676ab74b90b80a8a4e8ba5103d0fd0f8e74d345f1449a23308127c573a31f44000096553893919fd8d0e01e68c4621ed8d4a319218ca780002d93e74b237f550576f02327d394214d782e0ff67a0a606344d6600f235da2e29bae00000c36fb54dadea00001007899bfcd0bc00008ac9280e1cb384fec00000b4142670a52f23c8b379226cc47056ad48c8f00e21611d749726429dc568502972800000983505240000ba49dbd52519f695e22cb2351c0000000000005815000014258bafa8000131040000a4f880002cfce97f978c7000012ff7372dba70210a0000059b6b4aa00000ed6ab84a2185891a2da98760b00001d4b08bcce45791f743d455d612ddc2533b91652681194aa959d33d48323040f000050bbe96a94f95b4859de76e6c1363000004a36e1e2c000099d29c6c50308e8a0582c00002e6e728c7a675800009d1200008b3a49db0dffd6f8252845d936343b72ea0000497d282140b383a4342782f0133865a143c90ea961a50042bbb25452ccbc822b20c69d5d6b2f090fe43bb9dc58000086a40939a942c9f677302b68fc1ad649c0155c4a0b8986527c9222f78c00000000006ac335d759e3c000135a34b8b915ae62a64f384ba541364e5ba706194ca000029fbce8ec000018621920f0c3e12c81424800000273a7f88000163a6afbe3823d29f80000e175515c2540496c800000000000000000000000000000123df61ad5560d3e312c1055310aca1b9eea0fcc3b043f0236040000531cb62bc486ecf7c834fb68102fd8d82686fa947b169114d700000000000000000178 else 0x294cc5a94e0768a4243f325ff9c559362fa2b95b10d3173006b73c94a6aa84f22de1591439b79c3c8869442e243f24a56b6b74472edcf8af0840cdb4ae8b28c114cac3573607d5ef6076360c7b2b4ca55af04ae97515c95a5084c5d20af50c600002c3521276905a264b45c5121a5495493d7a85ed7570b8fca243106cc31ceaa8ecaa38b456981b6513461d2149262d8298800b21460f1298acd00d6d0e996b30ea25f24866477f670c2c748e0150f364ffa2cf793c111220821e2ae118106ec8104ac4235202769ca6e8d03c3d2bd3ad81d09ec00001c949c6a297c0a777350590ef40000b7965b7fe40948c6e46c5d0080000168aaa5863cb785b4a6a6bbab0da564a1aa563399f35bfb6b3aa64f53c4899b30000175db8b1e1d4d4b22e000073de035a5d2f82b9550d520f8d323aaf467494185e800009778229cd4c66a46170cb49a509066b33b2219b6db116ed2e688e1e4a05a6332686250832b2421e51c8614ab90b3e13ae4e1696c1bb1a3a1a4e506341279704d8368d99014fb6974ca0982ab5335eb2454ce558f008c54123c217fead28d6819b5c4d41a47be0c7a2cd355a68000083d4a0a2b1d80a0914df992264565432ff3436119503710d5e7192e4002412f62ca6f9e1423a15d92d8667746b2f23513a50bc516a010e59202480481cc40672899d12f2ba39528e1b21debfae4254352bd1b0d55e46f355b75b8b50fc5223f492f4512c82fb14d657a3c17f2d1c54b07995c264))))
def qix12s (i : Nat) : Nat := 0x1cc01450001800200d000281c8f40ec0100048118d11e40040c00bcc000203900164096670282502c0000065030000093e3e01c074004640102c0e0786d0142000300c2c0001e8300c00034000700406c1d03c000000e010010a005018100440a06046470000240b028110000c00001088040a8f3044079d000096300a81c71407008c900000010170045b0280004c0000d4c01879034280800058c0501c070100704c484d00b05c1802433018200281d00405604000140458c0107408019480101a2d81801ccb000990000600005068060040502c1a01806a7401008000001001808008302b292090030080f09c0503c0b0080c040f553cbd0040200c390080601004000160092a004060028a04304000160080802c0d02000028000000004c0b02407001a20000a00035000070000b2fc0300001
def qix12v (i : Nat) : Nat := (if i<1 then 0xcd47baf0e8611650a59859da0889097f00009f294741172b6c05bb4a2879319a24fb4a8ec0210a25425c48670001447b7e2e220001c3092a9064a3f4c2f3af8aae1116567479248c3b24adfa38d09a89991f72a28ad9a8ad1d9455525d1194e0f3afec8e269084d2b44a890744a8890e4a049236c1bb2b89753b30ab2bac2e302b564a80000a9493b5026a62caa69265456498c000200ca91499d2c400008d9301400089c2492b7fc00028e626888e0ab589be25f13a8aaf85c083b4b068cd9245213a64520a47f0000b289070256d209405e17c2a4d2c660791548a3a678a0d24b10002e280000a442a2d85c25d11662010e6e36749e0b080ea2a3292512a0287d36a924bb280d0c11612c70002229b65e93b88a800006b2d8106cce9e896400046989bd391e277a0d4000a418d0a422282c49ee40f2754d6927700003370ae0b4d4dea27040000002ea4421c99b000000082d92180000000453cd0eb82ce9b215c9db2b5c000b2c2d5e82dca27751898300001cdb49a48bb8b6c1f21c48f600000000002e1b31b8000254e9b6bb08ea0278640bb8190c6351499a8994801b6d4c2821a11b041b1c5f991400027ce8d570249e223c484aa5f494cb46c9c0458925626e49ca352ee2c4750cf9b1fcc2ea6209c62a8ec7b47dae1fbadce32b4bae3435068c10000d502b389820001429239852b379cab6704a87eb29a421a09cd850000d499b628822b85250341e424a5c8dcc05949edb804d8e4844000b894000a64d9a22aaa15744c8e1244fac7744800000000000b6e248f5368e3a46c8e17b5a0d7b85e51a948f0cf846de615b8760d14574e7249aad9e44511a5a5b891913ae25ab834872b4b225e3ad10f536369302a119bb62ea8cf36868e227a65be21266cfa8d4de360c9255b07249eb871158480e5ee51781c8424194d73caebbb88687c47e513323f9105421241388f4573b30c5222aa6d382446cbf5378d0084c6d0b905249db1e89772ae0a81096ca4020eae143a61252b4624bcb22a8c2b869696426097685b0c3fa882ca1bab2261072e00e371004820cea9a43cc00c92d24a74b0eda8b26e287925ac5223b0986894ec8641bcad682f9205932249423d0ab304a51e5213c878234c1d2a350adeb405159b4becb318328e45630875898ac9c808898a2111d6b4b768e1253ade636aeca325e0dae89a5695ba3c8f0a394c3c21cee108312cafbab5018924e8d036c6c08246896f9042e993a7499839d68d789f11a72a35161b800a3f2492c955a9d26014f09c9b6d2423b4088df268d55c26014cb37c0e6d53309d62b412c5b48cdec27095d0a38006b23bc99c54dd1af914097e261cdf582d6e73a4e482d047ad99b22615a48985ad97bd27a261125c21b516492e508573e8d09017529c37d01128036cac9b4ce793a4126c47e89d3b7eecb2 else 0x2420e48458084e48d8ddd48ddcad1130c744624a433375156a33ae0e2b36c1a2144cd82654e4e2529202b7f84ee09accfc244e0c035080004b714d622f68c90002e71390a497277cd94a0aeea53b2cd90b45912140460b841d8836b182a9f14d2d1c447cc8093a0d5226e8e4a88bc903270c000a34959639240f7705486990dd23eb82112d4168ad44ae4ada363eaa12454000049ee33b064000b7f484115b4000b866d36218800013a400000020250002ca90000854a54400047c4e8ca0c56e2b20e82a51a8807375e053212c0008184000a00a276495c000967d1deb9d08e7664a13a9919dc537a123bb4fd24d0000110515483823ec2ba35a89da481cae327ae29245eac0629fc83e92acd48171d22e99311ce44108ff2436e1ea6f05bf00009d829fa80a00000003b2228342040009290e8292ecc46000083d331e49fb9f4d0f7314e972b482ca4905264310ec16473caab057d0633af4aa8b4f51254500944858d6312ac6285250c040000000049614db8074000488)
def qix13s (i : Nat) : Nat := 0xb484006008101807
def qix13v (i : Nat) : Nat := 0x940023800006829800000000584b60000000009ca0408134329000dc7700154b0962f23cb2714812ce800b69ead85d001188a44
def orfindex : Nat → Nat → Option (Nat × Nat)
  | 6 => fun h => let s := packedAt qix5s ((h % 1)*0) 0; let v := packedAt qix5v (((h/1+s)%1)*4) 4; some (v % 1,v >>> 0)
  | 7 => fun h => let s := packedAt qix6s ((h % 1)*0) 0; let v := packedAt qix6v (((h/1+s)%8)*6) 6; some (v % 4,v >>> 2)
  | 8 => fun h => let s := packedAt qix7s ((h % 3)*3) 3; let v := packedAt qix7v (((h/3+s)%9)*7) 7; some (v % 8,v >>> 3)
  | 9 => fun h => let s := packedAt qix8s ((h % 21)*6) 6; let v := packedAt qix8v (((h/21+s)%70)*10) 10; some (v % 64,v >>> 6)
  | 10 => fun h => let s := packedAt qix9s ((h % 373)*11) 11; let v := packedAt qix9v (((h/373+s)%1153)*15) 15; some (v % 2048,v >>> 11)
  | 11 => fun h => let s := packedAt qix10s ((h % 2388)*13) 13; let v := packedAt qix10v (((h/2388+s)%7378)*17) 17; some (v % 8192,v >>> 13)
  | 12 => fun h => let s := packedAt qix11s ((h % 2244)*13) 13; let v := packedAt qix11v (((h/2244+s)%7000)*17) 17; some (v % 8192,v >>> 13)
  | 13 => fun h => let s := packedAt qix12s ((h % 247)*10) 10; let v := packedAt qix12v (((h/247+s)%800)*14) 14; some (v % 1024,v >>> 10)
  | 14 => fun h => let s := packedAt qix13s ((h % 11)*6) 6; let v := packedAt qix13v (((h/11+s)%47)*9) 9; some (v % 32,v >>> 5)
  | _ => fun _ => none
def orf : Forest := ⟨511,15,fun j => deadsamples[j]?.getD (0,0),deadcolumns,deadautos,orflevels,orfindex⟩
theorem quickBlock {g : Forest} {k s n : Nat} (ar d : Nat)
    (h : cells g k s n ar 0 d := by
      simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
      repeat' apply And.intro
      all_goals decide +kernel) : block g k s n = true := cellsBlock h
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u5_0 : block orf 5 0 1=true := quickBlock 6 0
theorem allorf5 : block orf 5 0 1=true := u5_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u6_0 : block orf 6 0 3=true := quickBlock 7 0
theorem allorf6 : block orf 6 0 3=true := u6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u7_0 : block orf 7 0 3=true := quickBlock 7 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u7_3 : block orf 7 3 5=true := quickBlock 8 1
theorem allorf7 : block orf 7 0 8=true := (@block_merge orf 7 0 3 5 u7_0 u7_3)
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u8_0 : block orf 8 0 8=true := quickBlock 8 1
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u8_8 : block orf 8 8 54=true := quickBlock 9 4
theorem allorf8 : block orf 8 0 62=true := (@block_merge orf 8 0 8 54 u8_0 u8_8)
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u9_0 : block orf 9 0 128=true := quickBlock 9 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u9_128 : block orf 9 128 128=true := quickBlock 9 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u9_256 : block orf 9 256 128=true := quickBlock 9 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u9_384 : block orf 9 384 127=true := quickBlock 9 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u9_511 : block orf 9 511 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u9_639 : block orf 9 639 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u9_767 : block orf 9 767 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u9_895 : block orf 9 895 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u9_1023 : block orf 9 1023 96=true := quickBlock 10 5
theorem allorf9 : block orf 9 0 1119=true := (@block_merge orf 9 0 511 608 (@block_merge orf 9 0 256 255 (@block_merge orf 9 0 128 128 u9_0 u9_128) (@block_merge orf 9 256 128 127 u9_256 u9_384)) (@block_merge orf 9 511 256 352 (@block_merge orf 9 511 128 128 u9_511 u9_639) (@block_merge orf 9 767 128 224 u9_767 (@block_merge orf 9 895 128 96 u9_895 u9_1023))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_0 : block orf 10 0 89=true := quickBlock 9 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_89 : block orf 10 89 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_217 : block orf 10 217 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_345 : block orf 10 345 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_473 : block orf 10 473 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_601 : block orf 10 601 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_729 : block orf 10 729 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_857 : block orf 10 857 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_985 : block orf 10 985 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_1113 : block orf 10 1113 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_1241 : block orf 10 1241 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_1369 : block orf 10 1369 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_1497 : block orf 10 1497 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_1625 : block orf 10 1625 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_1753 : block orf 10 1753 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_1881 : block orf 10 1881 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_2009 : block orf 10 2009 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_2137 : block orf 10 2137 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_2265 : block orf 10 2265 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_2393 : block orf 10 2393 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_2521 : block orf 10 2521 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_2649 : block orf 10 2649 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_2777 : block orf 10 2777 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_2905 : block orf 10 2905 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_3033 : block orf 10 3033 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_3161 : block orf 10 3161 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_3289 : block orf 10 3289 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_3417 : block orf 10 3417 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_3545 : block orf 10 3545 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_3673 : block orf 10 3673 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_3801 : block orf 10 3801 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_3929 : block orf 10 3929 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_4057 : block orf 10 4057 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_4185 : block orf 10 4185 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_4313 : block orf 10 4313 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_4441 : block orf 10 4441 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_4569 : block orf 10 4569 88=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_4657 : block orf 10 4657 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_4785 : block orf 10 4785 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_4913 : block orf 10 4913 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_5041 : block orf 10 5041 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_5169 : block orf 10 5169 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_5297 : block orf 10 5297 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_5425 : block orf 10 5425 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_5553 : block orf 10 5553 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_5681 : block orf 10 5681 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_5809 : block orf 10 5809 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_5937 : block orf 10 5937 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_6065 : block orf 10 6065 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_6193 : block orf 10 6193 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_6321 : block orf 10 6321 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_6449 : block orf 10 6449 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_6577 : block orf 10 6577 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_6705 : block orf 10 6705 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_6833 : block orf 10 6833 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_6961 : block orf 10 6961 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u10_7089 : block orf 10 7089 74=true := quickBlock 11 5
theorem allorf10 : block orf 10 0 7163=true := (@block_merge orf 10 0 3545 3618 (@block_merge orf 10 0 1753 1792 (@block_merge orf 10 0 857 896 (@block_merge orf 10 0 345 512 (@block_merge orf 10 0 89 256 u10_0 (@block_merge orf 10 89 128 128 u10_89 u10_217)) (@block_merge orf 10 345 256 256 (@block_merge orf 10 345 128 128 u10_345 u10_473) (@block_merge orf 10 601 128 128 u10_601 u10_729))) (@block_merge orf 10 857 384 512 (@block_merge orf 10 857 128 256 u10_857 (@block_merge orf 10 985 128 128 u10_985 u10_1113)) (@block_merge orf 10 1241 256 256 (@block_merge orf 10 1241 128 128 u10_1241 u10_1369) (@block_merge orf 10 1497 128 128 u10_1497 u10_1625)))) (@block_merge orf 10 1753 896 896 (@block_merge orf 10 1753 384 512 (@block_merge orf 10 1753 128 256 u10_1753 (@block_merge orf 10 1881 128 128 u10_1881 u10_2009)) (@block_merge orf 10 2137 256 256 (@block_merge orf 10 2137 128 128 u10_2137 u10_2265) (@block_merge orf 10 2393 128 128 u10_2393 u10_2521))) (@block_merge orf 10 2649 384 512 (@block_merge orf 10 2649 128 256 u10_2649 (@block_merge orf 10 2777 128 128 u10_2777 u10_2905)) (@block_merge orf 10 3033 256 256 (@block_merge orf 10 3033 128 128 u10_3033 u10_3161) (@block_merge orf 10 3289 128 128 u10_3289 u10_3417))))) (@block_merge orf 10 3545 1752 1866 (@block_merge orf 10 3545 896 856 (@block_merge orf 10 3545 384 512 (@block_merge orf 10 3545 128 256 u10_3545 (@block_merge orf 10 3673 128 128 u10_3673 u10_3801)) (@block_merge orf 10 3929 256 256 (@block_merge orf 10 3929 128 128 u10_3929 u10_4057) (@block_merge orf 10 4185 128 128 u10_4185 u10_4313))) (@block_merge orf 10 4441 344 512 (@block_merge orf 10 4441 128 216 u10_4441 (@block_merge orf 10 4569 88 128 u10_4569 u10_4657)) (@block_merge orf 10 4785 256 256 (@block_merge orf 10 4785 128 128 u10_4785 u10_4913) (@block_merge orf 10 5041 128 128 u10_5041 u10_5169)))) (@block_merge orf 10 5297 896 970 (@block_merge orf 10 5297 384 512 (@block_merge orf 10 5297 128 256 u10_5297 (@block_merge orf 10 5425 128 128 u10_5425 u10_5553)) (@block_merge orf 10 5681 256 256 (@block_merge orf 10 5681 128 128 u10_5681 u10_5809) (@block_merge orf 10 5937 128 128 u10_5937 u10_6065))) (@block_merge orf 10 6193 512 458 (@block_merge orf 10 6193 256 256 (@block_merge orf 10 6193 128 128 u10_6193 u10_6321) (@block_merge orf 10 6449 128 128 u10_6449 u10_6577)) (@block_merge orf 10 6705 256 202 (@block_merge orf 10 6705 128 128 u10_6705 u10_6833) (@block_merge orf 10 6961 128 74 u10_6961 u10_7089))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_0 : block orf 11 0 16=true := quickBlock 9 2
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_16 : block orf 11 16 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_144 : block orf 11 144 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_272 : block orf 11 272 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_400 : block orf 11 400 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_528 : block orf 11 528 128=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_656 : block orf 11 656 87=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_743 : block orf 11 743 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_871 : block orf 11 871 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_999 : block orf 11 999 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_1127 : block orf 11 1127 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_1255 : block orf 11 1255 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_1383 : block orf 11 1383 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_1511 : block orf 11 1511 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_1639 : block orf 11 1639 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_1767 : block orf 11 1767 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_1895 : block orf 11 1895 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_2023 : block orf 11 2023 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_2151 : block orf 11 2151 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_2279 : block orf 11 2279 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_2407 : block orf 11 2407 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_2535 : block orf 11 2535 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_2663 : block orf 11 2663 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_2791 : block orf 11 2791 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_2919 : block orf 11 2919 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_3047 : block orf 11 3047 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_3175 : block orf 11 3175 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_3303 : block orf 11 3303 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_3431 : block orf 11 3431 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_3559 : block orf 11 3559 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_3687 : block orf 11 3687 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_3815 : block orf 11 3815 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_3943 : block orf 11 3943 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_4071 : block orf 11 4071 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_4199 : block orf 11 4199 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_4327 : block orf 11 4327 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_4455 : block orf 11 4455 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_4583 : block orf 11 4583 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_4711 : block orf 11 4711 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_4839 : block orf 11 4839 71=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_4910 : block orf 11 4910 128=true := quickBlock 12 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_5038 : block orf 11 5038 128=true := quickBlock 12 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_5166 : block orf 11 5166 128=true := quickBlock 12 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_5294 : block orf 11 5294 128=true := quickBlock 12 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_5422 : block orf 11 5422 128=true := quickBlock 12 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_5550 : block orf 11 5550 128=true := quickBlock 12 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_5678 : block orf 11 5678 128=true := quickBlock 12 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_5806 : block orf 11 5806 128=true := quickBlock 12 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_5934 : block orf 11 5934 128=true := quickBlock 12 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_6062 : block orf 11 6062 128=true := quickBlock 12 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_6190 : block orf 11 6190 128=true := quickBlock 12 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_6318 : block orf 11 6318 128=true := quickBlock 12 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_6446 : block orf 11 6446 128=true := quickBlock 12 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_6574 : block orf 11 6574 128=true := quickBlock 12 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u11_6702 : block orf 11 6702 28=true := quickBlock 12 3
theorem allorf11 : block orf 11 0 6730=true := (@block_merge orf 11 0 3303 3427 (@block_merge orf 11 0 1511 1792 (@block_merge orf 11 0 656 855 (@block_merge orf 11 0 272 384 (@block_merge orf 11 0 16 256 u11_0 (@block_merge orf 11 16 128 128 u11_16 u11_144)) (@block_merge orf 11 272 128 256 u11_272 (@block_merge orf 11 400 128 128 u11_400 u11_528))) (@block_merge orf 11 656 343 512 (@block_merge orf 11 656 87 256 u11_656 (@block_merge orf 11 743 128 128 u11_743 u11_871)) (@block_merge orf 11 999 256 256 (@block_merge orf 11 999 128 128 u11_999 u11_1127) (@block_merge orf 11 1255 128 128 u11_1255 u11_1383)))) (@block_merge orf 11 1511 896 896 (@block_merge orf 11 1511 384 512 (@block_merge orf 11 1511 128 256 u11_1511 (@block_merge orf 11 1639 128 128 u11_1639 u11_1767)) (@block_merge orf 11 1895 256 256 (@block_merge orf 11 1895 128 128 u11_1895 u11_2023) (@block_merge orf 11 2151 128 128 u11_2151 u11_2279))) (@block_merge orf 11 2407 384 512 (@block_merge orf 11 2407 128 256 u11_2407 (@block_merge orf 11 2535 128 128 u11_2535 u11_2663)) (@block_merge orf 11 2791 256 256 (@block_merge orf 11 2791 128 128 u11_2791 u11_2919) (@block_merge orf 11 3047 128 128 u11_3047 u11_3175))))) (@block_merge orf 11 3303 1735 1692 (@block_merge orf 11 3303 896 839 (@block_merge orf 11 3303 384 512 (@block_merge orf 11 3303 128 256 u11_3303 (@block_merge orf 11 3431 128 128 u11_3431 u11_3559)) (@block_merge orf 11 3687 256 256 (@block_merge orf 11 3687 128 128 u11_3687 u11_3815) (@block_merge orf 11 3943 128 128 u11_3943 u11_4071))) (@block_merge orf 11 4199 384 455 (@block_merge orf 11 4199 128 256 u11_4199 (@block_merge orf 11 4327 128 128 u11_4327 u11_4455)) (@block_merge orf 11 4583 256 199 (@block_merge orf 11 4583 128 128 u11_4583 u11_4711) (@block_merge orf 11 4839 71 128 u11_4839 u11_4910)))) (@block_merge orf 11 5038 896 796 (@block_merge orf 11 5038 384 512 (@block_merge orf 11 5038 128 256 u11_5038 (@block_merge orf 11 5166 128 128 u11_5166 u11_5294)) (@block_merge orf 11 5422 256 256 (@block_merge orf 11 5422 128 128 u11_5422 u11_5550) (@block_merge orf 11 5678 128 128 u11_5678 u11_5806))) (@block_merge orf 11 5934 384 412 (@block_merge orf 11 5934 128 256 u11_5934 (@block_merge orf 11 6062 128 128 u11_6062 u11_6190)) (@block_merge orf 11 6318 256 156 (@block_merge orf 11 6318 128 128 u11_6318 u11_6446) (@block_merge orf 11 6574 128 28 u11_6574 u11_6702))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u12_0 : block orf 12 0 2=true := quickBlock 9 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u12_2 : block orf 12 2 108=true := quickBlock 10 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u12_110 : block orf 12 110 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u12_238 : block orf 12 238 128=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u12_366 : block orf 12 366 102=true := quickBlock 11 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u12_468 : block orf 12 468 128=true := quickBlock 12 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u12_596 : block orf 12 596 128=true := quickBlock 12 5
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u12_724 : block orf 12 724 16=true := quickBlock 12 2
theorem allorf12 : block orf 12 0 740=true := (@block_merge orf 12 0 366 374 (@block_merge orf 12 0 110 256 (@block_merge orf 12 0 2 108 u12_0 u12_2) (@block_merge orf 12 110 128 128 u12_110 u12_238)) (@block_merge orf 12 366 230 144 (@block_merge orf 12 366 102 128 u12_366 u12_468) (@block_merge orf 12 596 128 16 u12_596 u12_724)))
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u13_0 : block orf 13 0 11=true := quickBlock 10 2
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u13_11 : block orf 13 11 20=true := quickBlock 11 3
theorem allorf13 : block orf 13 0 31=true := (@block_merge orf 13 0 11 20 u13_0 u13_11)
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem u14_0 : block orf 14 0 1=true := quickBlock 10 0
theorem allorf14 : block orf 14 0 1=true := u14_0
theorem tablesorf : checkedTables orf 15 := by
  intro k hk
  interval_cases k
  · exact (rfl : block orf 0 0 0 = true)
  · exact (rfl : block orf 1 0 0 = true)
  · exact (rfl : block orf 2 0 0 = true)
  · exact (rfl : block orf 3 0 0 = true)
  · exact (rfl : block orf 4 0 0 = true)
  · exact allorf5
  · exact allorf6
  · exact allorf7
  · exact allorf8
  · exact allorf9
  · exact allorf10
  · exact allorf11
  · exact allorf12
  · exact allorf13
  · exact allorf14
  · exact (rfl : block orf 15 0 0 = true)
theorem geomorf : graphValid orf (boundsBefore known383) = true := geomdead
theorem orf_start : Impossible graph 14 (inputs++[seedB]).toFinset := by
  have noRun := root_index (g:=orf) (before_sound known383 valid383) geomorf tablesorf (k:=14) (by decide)
    (i:=0) (ws:=inputs++[seedB]) (by decide +kernel)
  have tgt : targetOf orf=graph := by decide +kernel
  exact tgt ▸ noRun
theorem dead_only : Impossible graph 14 inputs.toFinset := by
  have noRun := root_index (g:=dead) (before_sound known383 valid383) geomdead tablesdead (k:=14) (by decide)
    (i:=0) (ws:=inputs) (by decide +kernel)
  have tgt : targetOf dead=graph := by decide +kernel
  exact tgt ▸ noRun
theorem boundB (C : PEqualNP.CircuitLowerBounds.Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 3))
    (h : PEqualNP.MetaComplexity.circuitFun 9 C = edge) : 16 ≤ C.size := by
  by_contra! small
  obtain ⟨k,t,hk,hdead | hlive⟩ := initial_liveB C legal first h (by omega)
  · exact dead_only k t hk hdead
  · exact orf_start k t hk hlive
end PEqualNP.Outside.L_meta_3138
set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.L_meta_3138 :
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ),   x1.length = (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false]) x1 ≤ (1 : ℕ) →         x2 ≤ (24 : ℕ) →           x3 ≤ (24 : ℕ) →             ∃ (x9 : Fin (9 : ℕ) → Bool),               have x10 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9 ++ [x9 (0 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ))]);               (x10.getD x2 Bool.false || x10.getD x3 Bool.false) ≠ (x9 (0 : Fin (9 : ℕ)) && x9 (1 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (2 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (3 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (4 : Fin (9 : ℕ)) || x9 (4 : Fin (9 : ℕ)) && x9 (0 : Fin (9 : ℕ)) || x9 (0 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (6 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (5 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (6 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (8 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ))) := by
  let Gate := PEqualNP.CircuitLowerBounds.Gate
  let Circuit := PEqualNP.CircuitLowerBounds.Circuit
  let FanInTwo := PEqualNP.MetaComplexity.FanInTwo
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let prefixOr : Gate := ⟨.or, [0, 3]⟩
  let mergeOr (p q : ℕ) : Gate := ⟨.or, [p, q]⟩
  let withAux (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [x 0 || x 3]
  let interim (gs : List Gate) (x : Fin 9 → Bool) : List Bool :=
    (⟨gs, 0⟩ : Circuit).wires (withAux x)
  let fanin (gs : List Gate) : Prop := FanInTwo ⟨gs, 0⟩
  have step_length (w : List Bool) (g : Gate) :
      (step w g).length = w.length + 1 := by simp [step]
  have fold_length (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => simp only [List.foldl_cons, ih, step_length, List.length_cons]; omega
  have prefix_length (gs : List Gate) (x : Fin 9 → Bool) :
      (interim gs x).length = 10 + gs.length := by
    change (gs.foldl step (withAux x)).length = _
    rw [fold_length]
    simp [withAux]
  have fold_getD (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (step w g) (by rw [step_length]; omega)]
      exact List.getD_append _ _ _ _ hi
  have prefix_eval (gs : List Gate) (x : Fin 9 → Bool) :
      (⟨prefixOr :: gs, 0⟩ : Circuit).wires (List.ofFn x) = interim gs x := by
    change gs.foldl step (step (List.ofFn x) prefixOr) = gs.foldl step (withAux x)
    simp [step, prefixOr, withAux, PEqualNP.CircuitLowerBounds.GateOp.eval]
  have single_fanin (gs : List Gate) (h : fanin gs) (o : ℕ) :
      FanInTwo ⟨prefixOr :: gs, o⟩ := by
    intro g hm
    simp only [List.mem_cons] at hm
    rcases hm with rfl | hm
    · simp [prefixOr]
    · exact h _ hm
  have merged_fanin (gs : List Gate) (h : fanin gs) (p q o : ℕ) :
      FanInTwo ⟨prefixOr :: (gs ++ [mergeOr p q]), o⟩ := by
    apply single_fanin
    intro g hm
    simp only [List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · exact h _ hm
    · simp [mergeOr]
  have append_eval (gs : List Gate) (g : Gate) (x : Fin 9 → Bool) :
      interim (gs ++ [g]) x = step (interim gs x) g := by
    simp [interim, PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_append, step]
  have merged_eval (gs : List Gate) (p q : ℕ) (x : Fin 9 → Bool) :
      (⟨prefixOr :: (gs ++ [mergeOr p q]), 10 + gs.length⟩ : Circuit).eval (List.ofFn x) =
        ((interim gs x).getD p false || (interim gs x).getD q false) := by
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval
    change ((⟨prefixOr :: (gs ++ [mergeOr p q]), 0⟩ : Circuit).wires
      (List.ofFn x)).getD (10 + gs.length) false = _
    rw [prefix_eval, append_eval, ← prefix_length gs x]
    simp [step, mergeOr, PEqualNP.CircuitLowerBounds.GateOp.eval]
  intro gs p q hlen hfanin _ _ _
  let C : Circuit := ⟨prefixOr :: (gs ++ [mergeOr p q]), 10 + gs.length⟩
  let F := PEqualNP.Outside.L_meta_3138.edge
  change ∃ x : Fin 9 → Bool,
    ((interim gs x).getD p false || (interim gs x).getD q false) ≠ F x
  classical
  by_contra hbad
  have hsame (x : Fin 9 → Bool) :
      ((interim gs x).getD p false || (interim gs x).getD q false) = F x :=
    Classical.byContradiction (fun hn => hbad ⟨x, hn⟩)
  have first (y : Fin 9 → Bool) :
      (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 3) := by
    change ((⟨prefixOr :: (gs ++ [mergeOr p q]), 0⟩ : Circuit).wires
      (List.ofFn y)).getD 9 false = _
    rw [prefix_eval]
    change ((gs ++ [mergeOr p q]).foldl step (withAux y)).getD 9 false = _
    rw [fold_getD _ _ _ (by simp [withAux])]
    have last (w : List Bool) (z : Bool) : (w ++ [z]).getD w.length false = z := by simp
    simpa only [withAux, List.length_ofFn] using last (List.ofFn y) (y 0 || y 3)
  have computes : PEqualNP.MetaComplexity.circuitFun 9 C = F := by
    funext x
    exact (merged_eval gs p q x).trans (hsame x)
  have lb := PEqualNP.Outside.L_meta_3138.boundB C (merged_fanin gs hfanin p q _)
    first computes
  have hs : C.size = 15 := by
    simp [C, PEqualNP.CircuitLowerBounds.Circuit.size, hlen]
  omega
